-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageSim — plan 0.146 B1.4a: the image simulates the run.
--
-- A16's `Machine.sim`, for the image: the image on the compiled code reaches
-- the code after it with the run's result, its events the run's (temporaries
-- erased) with balanced temporaries — its frames — woven in. Every state
-- carries the return stack; A16's `enter … leave` bracket is a call: the
-- block run to its `end` under the pushed continuation, then the return.
--
-- §1–§2 here: multi-step runs, and what a stretch of the image claims (the
-- records and their combinators, A16's §4–§5).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; _+_; _∸_; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (n∸n≡0)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym; cong; trans)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.LinCore.Free using (_≼_; ++-≼; Weave; w-[]; w-run; w-tmp; w-++; w-self; Along-++)

module Once.LinCore.ImageSim
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Temps fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_; fsz)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw

------------------------------------------------------------------------
-- 1. RUNS OF THE IMAGE.
------------------------------------------------------------------------

infixr 5 _⟫_
data StepsI {T : Sh} : ∀ {sh U sh′ U′} → Codeᴵ sh U → Ret U T → Cfg sh → ℕ → Trace
                     → Codeᴵ sh′ U′ → Ret U′ T → Cfg sh′ → ℕ → Set where
  done : ∀ {sh U} {c : Codeᴵ sh U} {r : Ret U T} {m n} → StepsI c r m n [] c r m n
  _⟫_  : ∀ {sh U sh′ U′ sh″ U″} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
           {c″ : Codeᴵ sh″ U″} {r″ : Ret U″ T} {m m′ m″ n n′ n″ t₁ t₂}
       → StepI c r m n t₁ c′ r′ m′ n′ → StepsI c′ r′ m′ n′ t₂ c″ r″ m″ n″ → StepsI c r m n (t₁ ++ t₂) c″ r″ m″ n″

stepsI-++ : ∀ {T sh U sh′ U′ sh″ U″} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
              {c″ : Codeᴵ sh″ U″} {r″ : Ret U″ T} {m m′ m″ n n′ n″ t₁ t₂}
          → StepsI c r m n t₁ c′ r′ m′ n′ → StepsI c′ r′ m′ n′ t₂ c″ r″ m″ n″ → StepsI c r m n (t₁ ++ t₂) c″ r″ m″ n″
stepsI-++ done st₂ = st₂
stepsI-++ {c = c} {r} {c″ = c″} {r″} {m = m} {m″ = m″} {n = n} {n″ = n″} {t₂ = t₂} (_⟫_ {t₁ = u₁} {t₂ = u₂} x st₁) st₂ =
  subst (λ z → StepsI c r m n z c″ r″ m″ n″) (sym (++-assoc u₁ u₂ t₂)) (x ⟫ stepsI-++ st₁ st₂)

oneI : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t}
     → StepI c r m n t c′ r′ m′ n′ → StepsI c r m n t c′ r′ m′ n′
oneI {c = c} {r} {c′} {r′} {m} {m′} {n} {n′} {t} x = subst (λ z → StepsI c r m n z c′ r′ m′ n′) (++-identityʳ t) (x ⟫ done)

------------------------------------------------------------------------
-- 2. WHAT A STRETCH OF THE IMAGE CLAIMS (A16's §4–§5, the return stack
-- threaded).
------------------------------------------------------------------------

-- to a configuration: the events are a run's (erased) with balanced
-- temporaries woven in
record OutI {T sh U sh′ U′} (c : Codeᴵ sh U) (r : Ret U T) (m : Cfg sh) (n : ℕ) (t : Trace)
            (c′ : Codeᴵ sh′ U′) (r′ : Ret U′ T) (m′ : Cfg sh′) (n′ : ℕ) : Set where
  constructor out
  field
    ts    : List TEv
    mt    : Trace
    steps : StepsI c r m n mt c′ r′ m′ n′
    woven : Weave tmp (erase t) ts mt
    bal   : TBal (tmps ts)

-- to some point: a cell trace the run's events (erased) are a prefix of,
-- with legal temporaries (a frame may be open)
record PausedI {T sh U} (c : Codeᴵ sh U) (r : Ret U T) (m : Cfg sh) (n : ℕ) (t : Trace) : Set where
  constructor paused
  field
    {sh′ U′} : Sh
    c′    : Codeᴵ sh′ U′
    r′    : Ret U′ T
    m′    : Cfg sh′
    n′    : ℕ
    ts    : List TEv
    mt t₀ : Trace
    steps : StepsI c r m n mt c′ r′ m′ n′
    woven : Weave tmp t₀ ts mt
    pref  : erase t ≼ t₀
    clean : NoT t₀
    leg   : TLeg (tmps ts)

-- by the run's outcome
SimRI : ∀ {T sh U E Es B S U′} → Outcome B → Codeᴵ sh U → Ret U T → Cfg sh → ℕ → Trace
      → Codeᴵ (E ∷ Es ∣ B ∷ S) U′ → Ret U′ T → Slots (E ∷ Es) → Stk S → Set
SimRI (gives w n′) c r m n t k r′ es os = OutI c r m n t k r′ (es ∥ w ∷ˢ os) n′
SimRI (stop y)     c r m n t k r′ es os = PausedI c r m n t

private
  δn-same : ∀ k → δn k k ≡ 1
  δn-same k with k ≟ k
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  bracket : ∀ k ts → TBal (tmps ts) → TBal (tmps (tnew k ∷ (ts ++ tdel k ∷ [])))
  bracket k ts (okX , zX) rewrite map-++ tmp ts (tdel k ∷ []) =
    ( (tt , Along-++ X (tmp (tdel k) ∷ []) L₁ okX′ (subst (1 ≤_) (sym (eqX k)) one≤ , tt))
    , λ j → trans (cong (λ M → M j) (tplay-++ X (tmp (tdel k) ∷ []) L₁))
                  (trans (cong (_∸ δn k j) (eqX j)) (n∸n≡0 (δn k j))) )
    where
      X  = tmps ts
      L₁ : TL
      L₁ j = 0 + δn k j
      w  = weave-ok (w-self X) none L₁ L₁ (λ j → refl) okX tt
      okX′ = fst w
      eqX : ∀ j → tplay X L₁ j ≡ L₁ j
      eqX j = trans (snd w j) (cong (_+ L₁ j) (zX j))
      one≤ : 1 ≤ L₁ k
      one≤ = subst (1 ≤_) (sym (δn-same k)) (s≤s z≤n)

  opened : ∀ k ts → TLeg (tmps ts) → TLeg (tmps (tnew k ∷ ts))
  opened k ts l = (tt , TOK-mono (tmps ts) (λ j → z≤n) l)

bal∅ : TBal (tmps [])
bal∅ = (tt , λ k → refl)

-- a silent step first
pre : ∀ {T sh U sh′ U′ sh″ U″} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
        {c″ : Codeᴵ sh″ U″} {r″ : Ret U″ T} {m m′ m″ n n′ n″ t}
    → StepI c r m n [] c′ r′ m′ n′ → OutI c′ r′ m′ n′ t c″ r″ m″ n″ → OutI c r m n t c″ r″ m″ n″
pre x (out ts mt st w b) = out ts mt (x ⟫ st) w b

preP : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t}
     → StepI c r m n [] c′ r′ m′ n′ → PausedI c′ r′ m′ n′ t → PausedI c r m n t
preP x (paused c′ r′ m′ n′ ts mt t₀ st w p cl l) = paused c′ r′ m′ n′ ts mt t₀ (x ⟫ st) w p cl l

preR : ∀ {T sh U sh′ U′ E Es B S V} (o : Outcome B) {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
         {m m′ n t} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V} {ρ : Ret V T} {es os}
     → StepI c r m n [] c′ r′ m′ n → SimRI o c′ r′ m′ n t k ρ es os → SimRI o c r m n t k ρ es os
preR (gives _ _) x s = pre x s
preR (stop _)    x s = preP x s

-- a silent step after
after : ∀ {T sh U sh′ U′ sh″ U″} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
          {c″ : Codeᴵ sh″ U″} {r″ : Ret U″ T} {m m′ m″ n n′ n″ t}
      → OutI c r m n t c′ r′ m′ n′ → StepI c′ r′ m′ n′ [] c″ r″ m″ n″ → OutI c r m n t c″ r″ m″ n″
after {t = t} (out ts mt st w b) x =
  out ts (mt ++ []) (stepsI-++ st (oneI x)) (subst (λ z → Weave tmp (erase t) ts z) (sym (++-identityʳ mt)) w) b

-- one step whose events hold no temporary
leaf : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t}
     → StepI c r m n t c′ r′ m′ n′ → NoT t → OutI c r m n t c′ r′ m′ n′
leaf {t = t} x nt = out [] t (oneI x) (subst (λ z → Weave tmp z [] t) (sym (erase-NoT t nt)) (w-self t)) bal∅

-- one stretch, then the next
then : ∀ {T sh U sh′ U′ sh″ U″} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
         {c″ : Codeᴵ sh″ U″} {r″ : Ret U″ T} {m m′ m″ n n′ n″ t₁ t₂}
     → OutI c r m n t₁ c′ r′ m′ n′ → OutI c′ r′ m′ n′ t₂ c″ r″ m″ n″ → OutI c r m n (t₁ ++ t₂) c″ r″ m″ n″
then {t₁ = t₁} {t₂} (out ts₁ m₁ st₁ w₁ b₁) (out ts₂ m₂ st₂ w₂ b₂) =
  out (ts₁ ++ ts₂) (m₁ ++ m₂) (stepsI-++ st₁ st₂)
      (subst (λ z → Weave tmp z (ts₁ ++ ts₂) (m₁ ++ m₂)) (sym (erase-++ t₁ t₂)) (w-++ w₁ w₂))
      (subst TBal (sym (map-++ tmp ts₁ ts₂)) (IsSubmonoid.∙-∈ balanced {tmps ts₁} {tmps ts₂} b₁ b₂))

thenP : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t₁ t₂}
      → OutI c r m n t₁ c′ r′ m′ n′ → PausedI c′ r′ m′ n′ t₂ → PausedI c r m n (t₁ ++ t₂)
thenP {t₁ = t₁} {t₂} (out ts₁ m₁ st₁ w₁ b₁) (paused c″ r″ m″ n″ ts₂ m₂ t₀ st₂ w₂ p cl l) =
  paused c″ r″ m″ n″ (ts₁ ++ ts₂) (m₁ ++ m₂) (erase t₁ ++ t₀) (stepsI-++ st₁ st₂) (w-++ w₁ w₂)
         (subst (_≼ erase t₁ ++ t₀) (sym (erase-++ t₁ t₂)) (++-≼ (erase t₁) p))
         (++⁺ (erase-clean t₁) cl)
         (subst TLeg (sym (map-++ tmp ts₁ ts₂)) (IsSubmonoid.∙-∈ legal {tmps ts₁} {tmps ts₂} (fst b₁) l))

thenR : ∀ {T sh U sh′ U′ E Es B S V} (o : Outcome B) {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
          {m m′ n n′ t₁ t₂} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V} {ρ : Ret V T} {es os}
      → OutI c r m n t₁ c′ r′ m′ n′ → SimRI o c′ r′ m′ n′ t₂ k ρ es os → SimRI o c r m n (t₁ ++ t₂) k ρ es os
thenR (gives _ _) a s = then a s
thenR (stop _)    a s = thenP a s

-- ★ A CALL: the block run to its end under the pushed continuation, then
-- the return (A16's `enter … leave`)
called : ∀ {T σ Es S U sh′ U′} {κ : Key σ} {k : Codeᴵ (top σ ⊳ Es ∣ cod σ ∷ S) U} {r : Ret U T}
           {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m₁ m′ n n₁ n′ t}
       → OutI (blockᴵ κ) (k ∷ᶜ r) m n t end (k ∷ᶜ r) m₁ n₁ → OutI k r m₁ n₁ [] c′ r′ m′ n′
       → OutI (call κ ⨾ k) r m n t c′ r′ m′ n′
called {t = t} (out ts mt st w b) (out ts₂ mt₂ st₂ w₂ b₂) =
  subst (λ z → OutI _ _ _ _ z _ _ _ _) (++-identityʳ t)
    (then {t₁ = t} {t₂ = []} (out (tnew fsz ∷ (ts ++ tdel fsz ∷ [])) (tmp (tnew fsz) ∷ (mt ++ tmp (tdel fsz) ∷ []))
               (i-call ⟫ stepsI-++ st (oneI i-ret))
               (w-tmp (subst (λ z → Weave tmp z (ts ++ tdel fsz ∷ []) (mt ++ tmp (tdel fsz) ∷ []))
                             (++-identityʳ (erase t)) (w-++ w (w-tmp w-[]))))
               (bracket fsz ts b))
          (out ts₂ mt₂ st₂ w₂ b₂))

calledP : ∀ {T σ Es S U} {κ : Key σ} {k : Codeᴵ (top σ ⊳ Es ∣ cod σ ∷ S) U} {r : Ret U T} {m n t}
        → PausedI (blockᴵ κ) (k ∷ᶜ r) m n t → PausedI (call κ ⨾ k) r m n t
calledP (paused c′ r′ m′ n′ ts mt t₀ st w p cl l) =
  paused c′ r′ m′ n′ (tnew fsz ∷ ts) (tmp (tnew fsz) ∷ mt) t₀ (i-call ⟫ st) (w-tmp w) p cl (opened fsz ts l)

-- a stretch whose trace gains `++ []`
P-[] : ∀ {T sh U} {c : Codeᴵ sh U} {r : Ret U T} {m n t} → PausedI c r m n t → PausedI c r m n (t ++ [])
P-[] {t = t} (paused c′ r′ m′ n′ ts mt t₀ st w p cl l) =
  paused c′ r′ m′ n′ ts mt t₀ st w (subst (_≼ t₀) (sym (trans (erase-++ t []) (++-identityʳ (erase t)))) p) cl l

O-[] : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t}
     → OutI c r m n t c′ r′ m′ n′ → OutI c r m n (t ++ []) c′ r′ m′ n′
O-[] {t = t} (out ts mt st w b) =
  out ts mt st (subst (λ z → Weave tmp z ts mt) (sym (trans (erase-++ t []) (++-identityʳ (erase t)))) w) b

------------------------------------------------------------------------
-- 3. ★ THE COPY BLOCK: `Events.copy` (post-order), by induction on the
-- value; each cell's contents copied by a call, then the cell built.
------------------------------------------------------------------------

doneO : ∀ {T sh U} {c : Codeᴵ sh U} {r : Ret U T} {m n} → OutI c r m n [] c r m n
doneO = out [] [] done w-[] bal∅

-- a stretch, then one whose trace is empty
thenL : ∀ {T sh U sh′ U′ sh″ U″} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
          {c″ : Codeᴵ sh″ U″} {r″ : Ret U″ T} {m m′ m″ n n′ n″ t}
      → OutI c r m n t c′ r′ m′ n′ → OutI c′ r′ m′ n′ [] c″ r″ m″ n″ → OutI c r m n t c″ r″ m″ n″
thenL {t = t} a b = subst (λ z → OutI _ _ _ _ z _ _ _ _) (++-identityʳ t) (then a b)

mutual
  copyS : ∀ {T A} (v : MV A) {Es S U} {es : Slots (A ∷ Es)} → see es ≡ v → (os : Stk S)
          {k : Codeᴵ (A ∷ Es ∣ A ∷ S) U} {r : Ret U T} (n : ℕ)
        → OutI (call (kcopy A) ⨾ k) r (es ∥ mone ∷ˢ os) n (snd (snd (copy v n)))
               k r (es ∥ fst (copy v n) ∷ˢ os) (fst (snd (copy v n)))
  copyS v e os n = called (copyB v e os n) doneO

  copyB : ∀ {T A} (v : MV A) {Es S U} {es : Slots (A ∷ Es)} → see es ≡ v → (os : Stk S)
          {k : Codeᴵ (A ∷ Es ∣ A ∷ S) U} {r : Ret U T} (n : ℕ)
        → OutI (blockᴵ (kcopy A)) (k ∷ᶜ r) (es ∥ mone ∷ˢ os) n (snd (snd (copy v n)))
               end (k ∷ᶜ r) (es ∥ fst (copy v n) ∷ˢ os) (fst (snd (copy v n)))
  copyB mone e os n = doneO
  copyB (mbase x) e os n = leaf (i-eword e) []
  copyB (mpair a b) e os n with copy a n | copyS a refl os n
  ... | (a′ , n₁ , t₁) | ca with copy b n₁ | copyS b refl (a′ ∷ˢ os) n₁
  ...   | (b′ , n₂ , t₂) | cb =
    pre (i-efst e) (then (after ca i-epop)
      (pre i-unit (pre (i-esnd e) (after (after (after cb i-epop) i-swap) i-pair))))
  copyB (minl a) e os n with copy a n | copyS a refl os n
  ... | (a′ , n₁ , t₁) | ca = pre (i-ecase₁ e) (thenL (after ca i-epop) (leaf (i-prim r-inl) []))
  copyB (minr b) e os n with copy b n | copyS b refl os n
  ... | (b′ , n₁ , t₁) | cb = pre (i-ecase₂ e) (thenL (after cb i-epop) (leaf (i-prim r-inr) []))
  copyB (mmu i v) e os n with copy v n | copyS v refl os n
  ... | (v′ , n₁ , t₁) | cv = pre (i-eoutq e) (then (after cv i-epop) (leaf (i-prim r-In) (k-alloc ∷ [])))
  copyB (mct x) e os n with copy x n | copyS x refl os n
  ... | (x′ , n₁ , t₁) | cx = pre (i-eapp e) (after (after cx i-epop) i-tag₁)
  copyB (mfn i (c1 ds b γ) x) e os n with copy x n | copyS x refl os n
  ... | (x′ , n₁ , t₁) | cx = pre (i-ccopy1 e) (then (after cx i-epop) (leaf (i-prim r-lam) (k-alloc ∷ [])))
  copyB (mfn i (cω ds b γ) x) e os n with copy x n | copyS x refl os n
  ... | (x′ , n₁ , t₁) | cx = pre (i-ccopyω e) (then (after cx i-epop) (leaf (i-prim r-lamω) (k-alloc ∷ [])))
  copyB (mnu i p) e os n with copy p n | copyS p refl os n
  ... | (p′ , n₁ , t₁) | cp = pre (i-ncopy e) (then (after cp i-epop) (leaf (i-prim r-unf) (k-alloc ∷ [])))
