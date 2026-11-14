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
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Unit using (tt)
open import Data.Product using (_×_)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst; sym; cong; trans)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.LinCore.Free using (_≼_; []≼; ≼-trans; ≼-refl; ++-≼; weave-pre; Weave; w-[]; w-run; w-tmp; w-++; w-self; Along-++)

module Once.LinCore.ImageSim
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Temps fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_; fsz; Plain; PlainM; op-NoT)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw
-- a ν is observed at the empty table (D423)
open import Once.LinCore.ObsTable fmt ans bw using (TF; tf-id; tf-∘; tf-⊗; tf-case; tf-inl; tf-inr; tf-lul; tf-lul⁻; tf-drop; tf-lend; tf-bsnd; tf-bcopy; tf-bev; tf-unf; rt; obsT-tf; rt-obsT)

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

-- ★ D429: a run that HALTED pauses the image at `halted`, having made exactly the run's events
HaltIf : ∀ {T sh U} {c : Codeᴵ sh U} {r : Ret U T} {m n t} → Why → PausedI c r m n t → Set
HaltIf         exhausted p = Data.Unit.⊤
HaltIf {t = t} halted    p = (PausedI.c′ p ≡ halted) × (PausedI.t₀ p ≡ erase t)

-- by the run's outcome
SimRI : ∀ {T sh U Es B S U′} → Outcome B → Codeᴵ sh U → Ret U T → Cfg sh → ℕ → Trace
      → Codeᴵ (Es ∣ B ∷ S) U′ → Ret U′ T → Slots Es → Stk S → Set
SimRI (gives w n′) c r m n t k r′ es os = OutI c r m n t k r′ (es ∥ w ∷ˢ os) n′
SimRI (stop y)     c r m n t k r′ es os = Σ (PausedI c r m n t) (HaltIf y)

-- a simulation of a code is one of an equal code
sim-code : ∀ {T sh U Es B S U′} {o : Outcome B} {c c′ : Codeᴵ sh U} {r : Ret U T} {m : Cfg sh} {n : ℕ} {t : Trace}
             {k : Codeᴵ (Es ∣ B ∷ S) U′} {r′ : Ret U′ T} {es : Slots Es} {os : Stk S}
         → c ≡ c′ → SimRI o c r m n t k r′ es os → SimRI o c′ r m n t k r′ es os
sim-code refl x = x

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

-- (a halt's pause carried along)
preH : ∀ {T sh U sh′ U′} (y : Why) {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t}
     → StepI c r m n [] c′ r′ m′ n′ → Σ (PausedI c′ r′ m′ n′ t) (HaltIf y) → Σ (PausedI c r m n t) (HaltIf y)
preH halted    x (p , h) = preP x p , h
preH exhausted x (p , h) = preP x p , tt

preR : ∀ {T sh U sh′ U′ Es B S V} (o : Outcome B) {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
         {m m′ n t} {k : Codeᴵ (Es ∣ B ∷ S) V} {ρ : Ret V T} {es os}
     → StepI c r m n [] c′ r′ m′ n → SimRI o c′ r′ m′ n t k ρ es os → SimRI o c r m n t k ρ es os
preR (gives _ _) x s = pre x s
preR (stop y)    x s = preH y x s

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

thenH : ∀ {T sh U sh′ U′} (y : Why) {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t₁ t₂}
      → OutI c r m n t₁ c′ r′ m′ n′ → Σ (PausedI c′ r′ m′ n′ t₂) (HaltIf y) → Σ (PausedI c r m n (t₁ ++ t₂)) (HaltIf y)
thenH halted {t₁ = t₁} {t₂} a (p , (hc , ht)) = thenP a p , (hc , trans (cong (erase t₁ ++_) ht) (sym (erase-++ t₁ t₂)))
thenH exhausted a (p , h) = thenP a p , tt

thenR : ∀ {T sh U sh′ U′ Es B S V} (o : Outcome B) {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T}
          {m m′ n n′ t₁ t₂} {k : Codeᴵ (Es ∣ B ∷ S) V} {ρ : Ret V T} {es os}
      → OutI c r m n t₁ c′ r′ m′ n′ → SimRI o c′ r′ m′ n′ t₂ k ρ es os → SimRI o c r m n (t₁ ++ t₂) k ρ es os
thenR (gives _ _) a s = then a s
thenR (stop y)    a s = thenH y a s

-- ★ A CALL: the block run to its end in a frame of its own (D415: the
-- caller's top view and the argument), the caller's configuration saved
-- below; then the return puts the result back on it (A16's `enter … leave`)
-- ★ ENTERED by a step that opens the frame: a call, or a dispatch through a
-- cell's code word into its trampoline (D417)
Enters : ∀ {T} t {Es A B S U} → Codeᴵ (t ⊳ Es ∣ A ∷ S) U → Codeᴵ (t ⊳ [] ∣ A ∷ []) (t ⊳ [] ∣ B ∷ [])
       → Codeᴵ (t ⊳ Es ∣ B ∷ S) U → Ret U T → Slots (t ⊳ Es) → MV A → Stk S → ℕ → Set
Enters t c₀ blk k r es a os n =
  StepI c₀ r (es ∥ a ∷ˢ os) n (tmp (tnew fsz) ∷ []) blk (frm {t = t} k es os r) (topv t es ∥ a ∷ˢ []ˢ) n

called′ : ∀ {T t Es A B S U sh′ U′} {c₀ : Codeᴵ (t ⊳ Es ∣ A ∷ S) U} {blk : Codeᴵ (t ⊳ [] ∣ A ∷ []) (t ⊳ [] ∣ B ∷ [])}
            {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) U} {r : Ret U T}
            {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {es : Slots (t ⊳ Es)} {a os} {e₁ b₁} {m′ n n₁ n′ tr}
        → Enters t c₀ blk k r es a os n
        → OutI blk (frm {t = t} k es os r) (topv t es ∥ a ∷ˢ []ˢ) n tr end (frm {t = t} k es os r) (e₁ ∥ b₁ ∷ˢ []ˢ) n₁
        → OutI k r (es ∥ b₁ ∷ˢ os) n₁ [] c′ r′ m′ n′
        → OutI c₀ r (es ∥ a ∷ˢ os) n tr c′ r′ m′ n′
called′ {tr = tr} x (out ts mt st w b) (out ts₂ mt₂ st₂ w₂ b₂) =
  subst (λ z → OutI _ _ _ _ z _ _ _ _) (++-identityʳ tr)
    (then {t₁ = tr} {t₂ = []} (out (tnew fsz ∷ (ts ++ tdel fsz ∷ [])) (tmp (tnew fsz) ∷ (mt ++ tmp (tdel fsz) ∷ []))
               (x ⟫ stepsI-++ st (oneI i-ret))
               (w-tmp (subst (λ z → Weave tmp z (ts ++ tdel fsz ∷ []) (mt ++ tmp (tdel fsz) ∷ []))
                             (++-identityʳ (erase tr)) (w-++ w (w-tmp w-[]))))
               (bracket fsz ts b))
          (out ts₂ mt₂ st₂ w₂ b₂))

calledP′ : ∀ {T t Es A B S U} {c₀ : Codeᴵ (t ⊳ Es ∣ A ∷ S) U} {blk : Codeᴵ (t ⊳ [] ∣ A ∷ []) (t ⊳ [] ∣ B ∷ [])}
             {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots (t ⊳ Es)} {a os n tr}
         → Enters t c₀ blk k r es a os n
         → PausedI blk (frm {t = t} k es os r) (topv t es ∥ a ∷ˢ []ˢ) n tr → PausedI c₀ r (es ∥ a ∷ˢ os) n tr
calledP′ x (paused c′ r′ m′ n′ ts mt t₀ st w p cl l) =
  paused c′ r′ m′ n′ (tnew fsz ∷ ts) (tmp (tnew fsz) ∷ mt) t₀ (x ⟫ st) (w-tmp w) p cl (opened fsz ts l)

calledH : ∀ {T t Es A B S U} (y : Why) {c₀ : Codeᴵ (t ⊳ Es ∣ A ∷ S) U} {blk : Codeᴵ (t ⊳ [] ∣ A ∷ []) (t ⊳ [] ∣ B ∷ [])}
            {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots (t ⊳ Es)} {a os n tr}
        → Enters t c₀ blk k r es a os n
        → Σ (PausedI blk (frm {t = t} k es os r) (topv t es ∥ a ∷ˢ []ˢ) n tr) (HaltIf y) → Σ (PausedI c₀ r (es ∥ a ∷ˢ os) n tr) (HaltIf y)
calledH halted    x (p , h) = calledP′ x p , h
calledH exhausted x (p , h) = calledP′ x p , tt

called : ∀ {T σ Es S U sh′ U′} {κ : Key σ} {k : Codeᴵ (top σ ⊳ Es ∣ cod σ ∷ S) U} {r : Ret U T}
           {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {es : Slots (top σ ⊳ Es)} {a os} {e₁ b₁} {m′ n n₁ n′ t}
       → OutI (blockᴵ κ) (frm {t = top σ} k es os r) (topv (top σ) es ∥ a ∷ˢ []ˢ) n t end (frm {t = top σ} k es os r) (e₁ ∥ b₁ ∷ˢ []ˢ) n₁
       → OutI k r (es ∥ b₁ ∷ˢ os) n₁ [] c′ r′ m′ n′
       → OutI (call κ ⨾ k) r (es ∥ a ∷ˢ os) n t c′ r′ m′ n′
called = called′ i-call

calledP : ∀ {T σ Es S U} {κ : Key σ} {k : Codeᴵ (top σ ⊳ Es ∣ cod σ ∷ S) U} {r : Ret U T}
            {es : Slots (top σ ⊳ Es)} {a os n t}
        → PausedI (blockᴵ κ) (frm {t = top σ} k es os r) (topv (top σ) es ∥ a ∷ˢ []ˢ) n t → PausedI (call κ ⨾ k) r (es ∥ a ∷ˢ os) n t
calledP = calledP′ i-call

-- a stretch whose trace gains `++ []`
P-[] : ∀ {T sh U} {c : Codeᴵ sh U} {r : Ret U T} {m n t} → PausedI c r m n t → PausedI c r m n (t ++ [])
P-[] {t = t} (paused c′ r′ m′ n′ ts mt t₀ st w p cl l) =
  paused c′ r′ m′ n′ ts mt t₀ st w (subst (_≼ t₀) (sym (trans (erase-++ t []) (++-identityʳ (erase t)))) p) cl l

P-[]H : ∀ {T sh U} (y : Why) {c : Codeᴵ sh U} {r : Ret U T} {m n t}
      → Σ (PausedI c r m n t) (HaltIf y) → Σ (PausedI c r m n (t ++ [])) (HaltIf y)
P-[]H halted {t = t} (p , (hc , ht)) = P-[] p , (hc , trans ht (sym (trans (erase-++ t []) (++-identityʳ (erase t)))))
P-[]H exhausted (p , h) = P-[] p , tt

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
  copyS v e os n = called (copyB v e n) doneO

  -- the copy block, in its own frame: the view, the unit it fills
  copyB : ∀ {T A} (v : MV A) {es : Slots (A ∷ [])} → see es ≡ v → {r : Ret (A ∷ [] ∣ A ∷ []) T} (n : ℕ)
        → OutI (blockᴵ (kcopy A)) r (es ∥ mone ∷ˢ []ˢ) n (snd (snd (copy v n)))
               end r (es ∥ fst (copy v n) ∷ˢ []ˢ) (fst (snd (copy v n)))
  copyB mone e n = doneO
  copyB (mbase x) e n = leaf (i-eword e) []
  copyB (mpair a b) e n with copy a n | copyS a refl []ˢ n
  ... | (a′ , n₁ , t₁) | ca with copy b n₁ | copyS b refl (a′ ∷ˢ []ˢ) n₁
  ...   | (b′ , n₂ , t₂) | cb =
    pre (i-efst e) (then (after ca i-epop)
      (pre i-unit (pre (i-esnd e) (after (after (after cb i-epop) i-swap) i-pair))))
  copyB (minl a) e n with copy a n | copyS a refl []ˢ n
  ... | (a′ , n₁ , t₁) | ca = pre (i-ecase₁ e) (thenL (after ca i-epop) (leaf (i-prim r-inl) []))
  copyB (minr b) e n with copy b n | copyS b refl []ˢ n
  ... | (b′ , n₁ , t₁) | cb = pre (i-ecase₂ e) (thenL (after cb i-epop) (leaf (i-prim r-inr) []))
  copyB (mmu i v) e n with copy v n | copyS v refl []ˢ n
  ... | (v′ , n₁ , t₁) | cv = pre (i-eoutq e) (then (after cv i-epop) (leaf (i-prim r-In) (k-alloc ∷ [])))
  copyB (mct x) e n with copy x n | copyS x refl []ˢ n
  ... | (x′ , n₁ , t₁) | cx = pre (i-eapp e) (after (after cx i-epop) i-tag₁)
  -- ★ a cell: its trampoline (D417) views the contents, copies them, and
  -- builds a cell with the same code words
  copyB (mfn i lam x) e n with copy x n | copyS x refl []ˢ n
  ... | (x′ , n₁ , t₁) | cx =
    called′ (i-ccopy e) (pre (i-copen e) (then (after cx i-epop) (leaf (i-reclose e) (k-alloc ∷ [])))) doneO
  copyB (mnu i p) e n with copy p n | copyS p refl []ˢ n
  ... | (p′ , n₁ , t₁) | cp =
    called′ (i-ncopy e) (pre (i-copenν e) (then (after cp i-epop) (leaf (i-recloseν e) (k-alloc ∷ [])))) doneO

------------------------------------------------------------------------
-- 4. ★ THE FREE BLOCK: `Events.freeAll`, by induction on the value; each
-- cell freed, then what it held by a call.
------------------------------------------------------------------------

mutual
  freeS : ∀ {T A} (v : MV A) {Es S U} {es : Slots Es} (os : Stk S) {k : Codeᴵ (Es ∣ One ∷ S) U} {r : Ret U T} (n : ℕ)
        → OutI (call (kfree A) ⨾ k) r (es ∥ v ∷ˢ os) n (freeAll v) k r (es ∥ mone ∷ˢ os) n
  freeS v os n = called (freeB v n) doneO

  -- the free block, in its own frame: no view, the operand
  freeB : ∀ {T A} (v : MV A) {r : Ret ([] ∣ One ∷ []) T} (n : ℕ)
        → OutI (blockᴵ (kfree A)) r ([]ᵉ ∥ v ∷ˢ []ˢ) n (freeAll v) end r ([]ᵉ ∥ mone ∷ˢ []ˢ) n
  freeB mone n = doneO
  freeB (mbase x) n = leaf (i-prim r-drop) []
  freeB (mpair a b) n =
    pre i-unpair (then (after (freeS a (b ∷ˢ []ˢ) n) i-swap)
                       (thenL (after (freeS b (mone ∷ˢ []ˢ) n) i-pair) (leaf (i-prim r-λ) [])))
  freeB (minl a) n = pre i-case₁ (freeS a []ˢ n)
  freeB (minr b) n = pre i-case₂ (freeS b []ˢ n)
  freeB (mmu i v) n = then (leaf (i-prim r-Outμ) (k-free ∷ [])) (freeS v []ˢ n)
  freeB (mct x) n = pre i-untag₁ (freeS x []ˢ n)
  -- ★ a cell: its trampoline (D417) frees it, then frees what it held
  freeB (mfn i lam x) n = called′ i-cfree (then (leaf i-fopen (k-free ∷ [])) (freeS x []ˢ n)) doneO
  freeB (mnu i p) n = called′ i-nfree (then (leaf i-fopenν (k-free ∷ [])) (freeS p []ˢ n)) doneO

------------------------------------------------------------------------
-- 5. MORE COMBINATORS: a view around, a call by outcome, a cut, the run's
-- own temporaries.
------------------------------------------------------------------------

-- a call by the run's outcome: a block that reads no view, and one that
-- reads the top view
calledR′ : ∀ {T t A Es B S U} (o : Outcome B) {c₀ : Codeᴵ (t ⊳ Es ∣ A ∷ S) U} {blk : Codeᴵ (t ⊳ [] ∣ A ∷ []) (t ⊳ [] ∣ B ∷ [])}
             {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) U} {ρ : Ret U T} {a n tr} {es : Slots (t ⊳ Es)} {os : Stk S}
         → Enters t c₀ blk k ρ es a os n
         → SimRI o blk (frm {t = t} k es os ρ) (topv t es ∥ a ∷ˢ []ˢ) n tr end (frm {t = t} k es os ρ) (topv t es) []ˢ
         → SimRI o c₀ ρ (es ∥ a ∷ˢ os) n tr k ρ es os
calledR′ (gives _ _) x s = called′ x s doneO
calledR′ (stop y)    x s = calledH y x s

calledR : ∀ {T A Es B S U} (o : Outcome B) {κ : Key (bsig nothing A B)} {k : Codeᴵ (Es ∣ B ∷ S) U} {ρ : Ret U T}
            {a n t} {es : Slots Es} {os : Stk S}
          → SimRI o (blockᴵ κ) (frm {t = nothing} k es os ρ) ([]ᵉ ∥ a ∷ˢ []ˢ) n t end (frm {t = nothing} k es os ρ) []ᵉ []ˢ
          → SimRI o (call κ ⨾ k) ρ (es ∥ a ∷ˢ os) n t k ρ es os
calledR o = calledR′ o i-call

calledRω : ∀ {T X A Es B S U} (o : Outcome B) {κ : Key (bsig (just X) A B)} {k : Codeᴵ (X ∷ Es ∣ B ∷ S) U} {ρ : Ret U T}
             {a n t} {es : Slots (X ∷ Es)} {os : Stk S}
           → SimRI o (blockᴵ κ) (frm {t = just X} k es os ρ) (vw (see es) []ᵉ ∥ a ∷ˢ []ˢ) n t end (frm {t = just X} k es os ρ) (vw (see es) []ᵉ) []ˢ
           → SimRI o (call κ ⨾ k) ρ (es ∥ a ∷ˢ os) n t k ρ es os
calledRω o = calledR′ o i-call

-- a view opened by a silent step, closed after
around : ∀ {T E′ Es B S S₀ U V} (o : Outcome B) {c₀ : Codeᴵ (Es ∣ S₀) U} {r₀ : Ret U T}
           {c₁ : Codeᴵ (E′ ∷ Es ∣ S₀) U} {e′ : MV E′} {es : Slots Es} {v : Stk S₀} {os : Stk S} {n t}
           {k : Codeᴵ (Es ∣ B ∷ S) V} {ρ : Ret V T}
       → StepI c₀ r₀ (es ∥ v) n [] c₁ r₀ (vw e′ es ∥ v) n
       → SimRI o c₁ r₀ (vw e′ es ∥ v) n t (epop ⨾ k) ρ (vw e′ es) os
       → SimRI o c₀ r₀ (es ∥ v) n t k ρ es os
around (gives _ _) x s = pre x (after s i-epop)
around (stop y)    x s = preH y x s

-- a run cut short: what the image did for the whole run covers the prefix
cutR : ∀ {T sh U Es B S V} (o : Outcome B) {c : Codeᴵ sh U} {r : Ret U T} {m n t t′}
         {k : Codeᴵ (Es ∣ B ∷ S) V} {ρ : Ret V T} {es os}
     → t′ ≼ t → SimRI o c r m n t k ρ es os → PausedI c r m n t′
cutR (gives _ _) {t = t} q (out ts mt st w b) = paused _ _ _ _ ts mt (erase t) st w (erase-≼ q) (erase-clean t) (fst b)
cutR (stop _) q (paused c′ r′ m′ n′ ts mt t₀ st w p cl l , _) = paused c′ r′ m′ n′ ts mt t₀ st w (≼-trans (erase-≼ q) p) cl l

-- the run's own temporaries: erased, the same events
tmpR : ∀ {T sh U Es B S V} (o : Outcome B) {c : Codeᴵ sh U} {r : Ret U T} {m n t t″ ts₀}
         {k : Codeᴵ (Es ∣ B ∷ S) V} {ρ : Ret V T} {es os}
     → Weave tmp t ts₀ t″ → SimRI o c r m n t k ρ es os → SimRI o c r m n t″ k ρ es os
tmpR (gives _ _) w (out ts mt st wv b) = out ts mt st (subst (λ z → Weave tmp z ts mt) (sym (erase-weave w)) wv) b
tmpR (stop halted) w (paused c′ r′ m′ n′ ts mt t₀ st wv p cl l , (hc , ht)) =
  paused c′ r′ m′ n′ ts mt t₀ st wv (subst (_≼ t₀) (sym (erase-weave w)) p) cl l , (hc , trans ht (sym (erase-weave w)))
tmpR (stop exhausted) w (paused c′ r′ m′ n′ ts mt t₀ st wv p cl l , _) =
  paused c′ r′ m′ n′ ts mt t₀ st wv (subst (_≼ t₀) (sym (erase-weave w)) p) cl l , tt

-- a label's key is its body's block
look-key1 : ∀ {Γ Δ l g X A B} {ds : Defs Γ} {p : Γ ∋[ l ] sg once g X A B} {ds′ : Defs Δ} {b : LTm Δ (X ⊗t A) B} {γ : Gd g b}
          → Look ds p ds′ (b1 b γ) → key1 ds p ≡ kbody1 ds′ b γ
look-key1 lk-here      = refl
look-key1 (lk-there q) = look-key1 q

look-keyω : ∀ {Γ Δ l g X A B} {ds : Defs Γ} {p : Γ ∋[ l ] sg many g X A B} {ds′ : Defs Δ} {b : Tm Δ X A B} {γ : Gd g b}
          → Look ds p ds′ (bω b γ) → keyω ds p ≡ kbodyω ds′ b γ
look-keyω lk-here      = refl
look-keyω (lk-there q) = look-keyω q

------------------------------------------------------------------------
-- 6. ★ THE SIMULATION: the image runs the compiled code as the term runs,
-- for every outcome (A16's `sim`, with calls).
------------------------------------------------------------------------

mutual
  simMI : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x o n t}
        → (rm : RunMap ds F alg e G x n o t) → PlainM rm
        → ∀ {Es S T U} (es : Slots (E ∷ Es)) → see es ≡ e → (os : Stk S) (k : Codeᴵ (E ∷ Es ∣ LF∙ G A ∷ S) U) (ρ : Ret U T)
        → SimRI o (travᴵ ds F alg G k) ρ (es ∥ x ∷ˢ os) n t k ρ es os
  simMI (m-id r) p es eq os k ρ = simI r p es eq os k ρ
  simMI m-one p es eq os k ρ = doneO
  simMI m-b p es eq os k ρ = doneO
  simMI m-μ p es eq os k ρ = doneO
  simMI (m-inl (fm-gives r)) p es eq os k ρ = pre i-case₁ (after (simMI r p es eq os _ ρ) (i-prim r-inl))
  simMI (m-inl (fm-stop r))  p es eq os k ρ = preH _ i-case₁ (simMI r p es eq os _ ρ)
  simMI (m-inr (fm-gives r)) p es eq os k ρ = pre i-case₂ (after (simMI r p es eq os _ ρ) (i-prim r-inr))
  simMI (m-inr (fm-stop r))  p es eq os k ρ = preH _ i-case₂ (simMI r p es eq os _ ρ)
  simMI (m-pair {x′ = x′} r (go-on {u = y} (fm-gives r′))) (p , p′) es eq os k ρ =
    pre i-unpair (then (simMI r p es eq (x′ ∷ˢ os) _ ρ)
                       (pre i-swap (after (after (simMI r′ p′ es eq (y ∷ˢ os) _ ρ) i-swap) i-pair)))
  simMI (m-pair {x′ = x′} r (go-on {u = y} (fm-stop r′))) (p , p′) es eq os k ρ =
    preH _ i-unpair (thenH _ (simMI r p es eq (x′ ∷ˢ os) _ ρ) (preH _ i-swap (simMI r′ p′ es eq (y ∷ˢ os) _ ρ)))
  simMI (m-pair {x′ = x′} r stopped) p es eq os k ρ = P-[]H _ (preH _ i-unpair (simMI r p es eq (x′ ∷ˢ os) _ ρ))

  simI : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v o n t}
       → (r : Run ds f e v n o t) → Plain r
       → ∀ {Es S T U} (es : Slots (E ∷ Es)) → see es ≡ e → (os : Stk S) (k : Codeᴵ (E ∷ Es ∣ B ∷ S) U) (ρ : Ret U T)
       → SimRI o (compᴵ ds f k) ρ (es ∥ v ∷ˢ os) n t k ρ es os
  simI r-id fr es eq os k ρ = doneO
  simI (r-∘ rg (go-on {o = o} rf)) (pg , pf) es eq os k ρ = thenR o (simI rg pg es eq os _ ρ) (simI rf pf es eq os k ρ)
  simI (r-∘ rg stopped) pg es eq os k ρ = P-[]H _ (simI rg pg es eq os _ ρ)
  simI (r-⊗ {c = c} rf (go-on {u = a′} (fm-gives rg))) (pf , pg) es eq os k ρ =
    pre i-unpair (then (simI rf pf es eq (c ∷ˢ os) _ ρ)
                       (pre i-swap (after (after (simI rg pg es eq (a′ ∷ˢ os) _ ρ) i-swap) i-pair)))
  simI (r-⊗ {c = c} rf (go-on {u = a′} (fm-stop rg))) (pf , pg) es eq os k ρ =
    preH _ i-unpair (thenH _ (simI rf pf es eq (c ∷ˢ os) _ ρ) (preH _ i-swap (simI rg pg es eq (a′ ∷ˢ os) _ ρ)))
  simI (r-⊗ {c = c} rf stopped) pf es eq os k ρ = P-[]H _ (preH _ i-unpair (simI rf pf es eq (c ∷ˢ os) _ ρ))
  simI r-ρ     fr es eq os k ρ = leaf (i-prim r-ρ) []
  simI r-ρ⁻    fr es eq os k ρ = leaf (i-prim r-ρ⁻) []
  simI r-λ     fr es eq os k ρ = leaf (i-prim r-λ) []
  simI r-λ⁻    fr es eq os k ρ = leaf (i-prim r-λ⁻) []
  simI r-α     fr es eq os k ρ = leaf (i-prim r-α) []
  simI r-α⁻    fr es eq os k ρ = leaf (i-prim r-α⁻) []
  simI r-swap  fr es eq os k ρ = leaf (i-prim r-swap) []
  -- ★ `dup`: the operand lent (a lend's slot owns it), the copy block called
  -- on it, taken back beside its copy
  simI (r-dup {v = v} {n}) fr es eq os k ρ =
    pre i-unit (pre i-swap (pre i-pair (pre i-elend (pre (i-esnd refl)
      (after (after (copyS v refl os n) i-epop) i-eunlend)))))
  -- ★ `drop`: the free block
  simI (r-drop {v = v} {n}) fr es eq os k ρ = freeS v os n
  simI r-inl   fr es eq os k ρ = leaf (i-prim r-inl) []
  simI r-inr   fr es eq os k ρ = leaf (i-prim r-inr) []
  simI (r-case₁ {o = o} r) p es eq os k ρ = preR o i-case₁ (simI r p es eq os k ρ)
  simI (r-case₂ {o = o} r) p es eq os k ρ = preR o i-case₂ (simI r p es eq os k ρ)
  simI r-In    fr es eq os k ρ = leaf (i-prim r-In) (k-alloc ∷ [])
  simI r-Outμ  fr es eq os k ρ = leaf (i-prim r-Outμ) (k-free ∷ [])
  simI r-clo   fr es eq os k ρ = leaf (i-prim r-clo) []
  -- ★ a label's body: a call into its block
  simI (r-app {o = o} q r) p es eq os k ρ rewrite look-key1 q =
    preR o i-untag (calledR o (around o i-elift (simI r p (vw mone []ᵉ) refl []ˢ _ (frm {t = nothing} k es os ρ))))
  -- ★ a fold: a call; the block frees the node, folds each child (calls),
  -- runs the algebra
  simI (r-cata rm (go-on {o = o} ra)) (pm , pa) es eq os k ρ =
    calledRω o (thenR o (leaf (i-prim r-Outμ) (k-free ∷ []))
                        (thenR o (simMI rm pm (vw (see es) []ᵉ) eq []ˢ _ (frm {t = just _} k es os ρ))
                                 (simI ra pa (vw (see es) []ᵉ) eq []ˢ end (frm {t = just _} k es os ρ))))
  simI (r-cata {e = e} rm stopped) pm es eq os k ρ =
    calledH _ i-call (thenH _ (leaf (i-prim r-Outμ) (k-free ∷ [])) (P-[]H _ (simMI rm pm (vw (see es) []ᵉ) eq []ˢ _ (frm {t = just _} k es os ρ))))
  simI (r-cata-reuse rm th) () es eq os k ρ
  simI (r-lend {x = x} (fm-gives r)) fr es refl os k ρ =
    pre i-elend (after (simI r fr (ln (see es) x es) refl os _ ρ) i-eunlend)
  simI (r-lend {x = x} (fm-stop r))  fr es refl os k ρ = preH _ i-elend (simI r fr (ln (see es) x es) refl os _ ρ)
  simI (r-lift {o = o} r) fr es eq os k ρ = around o i-elift (simI r fr (vw mone es) refl os _ ρ)
  simI (r-fst {e₁ = e₁} {o = o} r) fr es eq os k ρ = around o (i-efst eq) (simI r fr (vw e₁ es) refl os _ ρ)
  simI (r-snd {e₂ = e₂} {o = o} r) fr es eq os k ρ = around o (i-esnd eq) (simI r fr (vw e₂ es) refl os _ ρ)
  simI (r-caseE₁ {e = e} {o = o} r) fr es eq os k ρ = around o (i-ecase₁ eq) (simI r fr (vw e es) refl os _ ρ)
  simI (r-caseE₂ {e = e} {o = o} r) fr es eq os k ρ = around o (i-ecase₂ eq) (simI r fr (vw e es) refl os _ ρ)
  simI (r-out {B = B} {i = i} {v} {a} {o = o} {n} r) fr es eq os k ρ = outR o (simI r fr (vw v es) refl os _ ρ)
    where
      outR : (o : Outcome B) → ∀ {c₁ t} → SimRI o c₁ ρ (vw v es ∥ a ∷ˢ os) n t (epop ⨾ k) ρ (vw v es) os
           → SimRI o (eout ⨾ c₁) ρ (es ∥ a ∷ˢ os) n (peek i ∷ t) k ρ es os
      outR (gives _ _) r′ = then (leaf (i-eout eq) (k-peek ∷ [])) (after r′ i-epop)
      outR (stop _)    r′ = thenH _ (leaf (i-eout eq) (k-peek ∷ [])) r′
  -- ★ a lent copy: the copy block on the view
  simI (r-copy {n = n}) fr es refl os k ρ = copyS (see es) refl os n
  simI (r-bapp {x = x} {o = o} q r) fr es eq os k ρ rewrite look-keyω q =
    around o (i-eapp eq) (calledRω o (simI r fr (vw x []ᵉ) refl []ˢ end (frm {t = just _} (epop ⨾ k) (vw x es) os ρ)))
  simI r-lam   fr es eq os k ρ = leaf (i-prim r-lam) (k-alloc ∷ [])
  simI r-lamω  fr es eq os k ρ = leaf (i-prim r-lamω) (k-alloc ∷ [])
  simI r-unf   fr es eq os k ρ = leaf (i-prim r-unf) (k-alloc ∷ [])
  -- ★ through a cell's code word: its trampoline (D417), which does the
  -- cell's part and calls the block
  simI (r-nout {F = F} {S} {o = o} r) p es eq os k ρ =
    calledR′ o i-iobs (thenR o (leaf i-nopen (k-free ∷ []))
      (calledR o (around o i-elift
        (sim-code (cong (λ u → compᴵ ε u (epop ⨾ end)) (rt-obsT F S))
          (simTF r (obsT-tf F S) p (vw mone []ᵉ) refl []ˢ _ (frm {t = nothing} end []ᵉ []ˢ (frm {t = nothing} k es os ρ)))))))
  simI (r-ev {o = o} r) p es eq os k ρ =
    calledR′ o i-icall (thenR o (leaf i-open1 (k-free ∷ []))
      (calledR o (around o i-elift (simI r p (vw mone []ᵉ) refl []ˢ _ (frm {t = nothing} end []ᵉ []ˢ (frm {t = nothing} k es os ρ))))))
  simI (r-bev {B = B} {ds′ = ds′} {b = b} {γ = γ} {i = i} {x} {a} {o} {n} r) p es eq os k ρ =
    calledR′ o (i-icallω eq) (bevR o (calledRω o (simI r p (vw x []ᵉ) refl []ˢ end (frm {t = just _} (epop ⨾ end) (vw x E′) []ˢ R′))))
    where
      E′ = vw (see es) []ᵉ
      R′ = frm {t = just _} k es os ρ
      bevR : (o : Outcome B) → ∀ {t} → SimRI o (call (kbodyω ds′ b γ) ⨾ epop ⨾ end) R′ (vw x E′ ∥ a ∷ˢ []ˢ) n t (epop ⨾ end) R′ (vw x E′) []ˢ
           → SimRI o (openω ⨾ call (kbodyω ds′ b γ) ⨾ epop ⨾ end) R′ (E′ ∥ a ∷ˢ []ˢ) n (peek i ∷ t) end R′ E′ []ˢ
      bevR (gives _ _) r′ = then (leaf (i-openω eq) (k-peek ∷ [])) (after r′ i-epop)
      bevR (stop y)    r′ = thenH y (leaf (i-openω eq) (k-peek ∷ [])) r′
  simI r-const fr es eq os k ρ = leaf (i-prim r-const) []
  simI (r-op p) fr es eq os k ρ = leaf (i-prim (r-op p)) (op-NoT p)
  simI (r-opend {w = halted} p) fr es eq os k ρ =
    paused halted ρ _ _ [] _ _ (oneI (i-opend p)) (w-self _) (subst (_≼ _) (sym (erase-NoT _ (op-NoT p))) (≼-refl _)) (op-NoT p) tt
    , (refl , sym (erase-NoT _ (op-NoT p)))
  simI (r-opend {w = exhausted} p) () es eq os k ρ
  -- ★ the loop: its round with the branch pushed (no frame), then the branch
  simI (r-iter r (go-on done)) fr es eq os k ρ =
    O-[] (pre i-loop (after (after (simI r fr es eq os end _) i-reti) i-case₁))
  simI (r-iter r (go-on (again {o = o} rn))) (p , pn) es eq os k ρ =
    preR o i-loop (thenR o (simI r p es eq os end _) (preR o i-reti (preR o i-case₂ (simI rn pn es eq os k ρ))))
  simI (r-iter r stopped) fr es eq os k ρ = P-[]H _ (preH _ i-loop (simI r fr es eq os end _))
  simI r-exh fr es eq os k ρ = (paused _ ρ _ _ [] [] [] done w-[] []≼ [] tt , tt)
  simI (r-cut {o = o} r q) fr es eq os k ρ = (cutR o q (simI r fr es eq os k ρ) , tt)
  simI (r-tmp {o = o} r w p) fr es eq os k ρ = tmpR o w (simI r fr es eq os k ρ)

  -- ★ a TABLE-FREE term's run, on its code at the empty table (D423): as
  -- `simI`, by the run (the observation's block is `kobs ε`)
  simTF : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v o n t}
        → (r : Run ds f e v n o t) (w : TF f) → Plain r
        → ∀ {Es S T U} (es : Slots (E ∷ Es)) → see es ≡ e → (os : Stk S) (k : Codeᴵ (E ∷ Es ∣ B ∷ S) U) (ρ : Ret U T)
        → SimRI o (compᴵ ε (rt w) k) ρ (es ∥ v ∷ˢ os) n t k ρ es os
  simTF (r-tmp {o = o} r wv tp) w fr es eq os k ρ = tmpR o wv (simTF r w fr es eq os k ρ)
  simTF r-exh w fr es eq os k ρ = (paused _ ρ _ _ [] [] [] done w-[] []≼ [] tt , tt)
  simTF (r-cut {o = o} r q) w fr es eq os k ρ = (cutR o q (simTF r w fr es eq os k ρ) , tt)
  simTF r-id tf-id fr es eq os k ρ = doneO
  simTF (r-∘ rg (go-on {o = o} rf)) (tf-∘ wf wg) (pg , pf) es eq os k ρ =
    thenR o (simTF rg wg pg es eq os _ ρ) (simTF rf wf pf es eq os k ρ)
  simTF (r-∘ rg stopped) (tf-∘ wf wg) pg es eq os k ρ = P-[]H _ (simTF rg wg pg es eq os _ ρ)
  simTF (r-⊗ {c = c} rf (go-on {u = a′} (fm-gives rg))) (tf-⊗ wf wg) (pf , pg) es eq os k ρ =
    pre i-unpair (then (simTF rf wf pf es eq (c ∷ˢ os) _ ρ)
                       (pre i-swap (after (after (simTF rg wg pg es eq (a′ ∷ˢ os) _ ρ) i-swap) i-pair)))
  simTF (r-⊗ {c = c} rf (go-on {u = a′} (fm-stop rg))) (tf-⊗ wf wg) (pf , pg) es eq os k ρ =
    preH _ i-unpair (thenH _ (simTF rf wf pf es eq (c ∷ˢ os) _ ρ) (preH _ i-swap (simTF rg wg pg es eq (a′ ∷ˢ os) _ ρ)))
  simTF (r-⊗ {c = c} rf stopped) (tf-⊗ wf wg) pf es eq os k ρ = P-[]H _ (preH _ i-unpair (simTF rf wf pf es eq (c ∷ˢ os) _ ρ))
  simTF r-λ tf-lul fr es eq os k ρ = leaf (i-prim r-λ) []
  simTF r-λ⁻ tf-lul⁻ fr es eq os k ρ = leaf (i-prim r-λ⁻) []
  simTF (r-drop {v = v} {n}) tf-drop fr es eq os k ρ = freeS v os n
  simTF r-inl tf-inl fr es eq os k ρ = leaf (i-prim r-inl) []
  simTF r-inr tf-inr fr es eq os k ρ = leaf (i-prim r-inr) []
  simTF (r-case₁ {o = o} r) (tf-case wf wg) p es eq os k ρ = preR o i-case₁ (simTF r wf p es eq os k ρ)
  simTF (r-case₂ {o = o} r) (tf-case wf wg) p es eq os k ρ = preR o i-case₂ (simTF r wg p es eq os k ρ)
  simTF (r-lend {x = x} (fm-gives r)) (tf-lend wb) fr es refl os k ρ =
    pre i-elend (after (simTF r wb fr (ln (see es) x es) refl os _ ρ) i-eunlend)
  simTF (r-lend {x = x} (fm-stop r)) (tf-lend wb) fr es refl os k ρ = preH _ i-elend (simTF r wb fr (ln (see es) x es) refl os _ ρ)
  simTF (r-snd {e₂ = e₂} {o = o} r) (tf-bsnd wf) fr es eq os k ρ = around o (i-esnd eq) (simTF r wf fr (vw e₂ es) refl os _ ρ)
  simTF (r-copy {n = n}) tf-bcopy fr es refl os k ρ = copyS (see es) refl os n
  simTF r-unf tf-unf fr es eq os k ρ = leaf (i-prim r-unf) (k-alloc ∷ [])
  simTF (r-bev {B = B} {ds′ = ds′} {b = b} {γ = γ} {i = i} {x} {a} {o} {n} r) tf-bev p es eq os k ρ =
    calledR′ o (i-icallω eq) (bevR o (calledRω o (simI r p (vw x []ᵉ) refl []ˢ end (frm {t = just _} (epop ⨾ end) (vw x E′) []ˢ R′))))
    where
      E′ = vw (see es) []ᵉ
      R′ = frm {t = just _} k es os ρ
      bevR : (o : Outcome B) → ∀ {t} → SimRI o (call (kbodyω ds′ b γ) ⨾ epop ⨾ end) R′ (vw x E′ ∥ a ∷ˢ []ˢ) n t (epop ⨾ end) R′ (vw x E′) []ˢ
           → SimRI o (openω ⨾ call (kbodyω ds′ b γ) ⨾ epop ⨾ end) R′ (E′ ∥ a ∷ˢ []ˢ) n (peek i ∷ t) end R′ E′ []ˢ
      bevR (gives _ _) r′ = then (leaf (i-openω eq) (k-peek ∷ [])) (after r′ i-epop)
      bevR (stop y)    r′ = thenH y (leaf (i-openω eq) (k-peek ∷ [])) r′

------------------------------------------------------------------------
-- 7. ★ ON THE IMAGE (A16's §7).
------------------------------------------------------------------------

private
  pre₀ : Pre (λ _ → 0) 0 mone (λ _ → 0)
  pre₀ = record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }

-- a closed program starts with nothing lent and nothing given
start : Cfg (One ∷ [] ∣ One ∷ [])
start = vw mone []ᵉ ∥ mone ∷ˢ []ˢ

-- the world sees the same of a trace and of its erasure
ios-erase : ∀ t → ios (erase t) ≡ ios t
ios-erase []             = refl
ios-erase (alloc _ ∷ t)  = ios-erase t
ios-erase (free _ ∷ t)   = ios-erase t
ios-erase (peek _ ∷ t)   = ios-erase t
ios-erase (io s x y ∷ t) = cong (io-call s x y ∷_) (ios-erase t)
ios-erase (stp s x ∷ t)  = cong (io-halt s x ∷_) (ios-erase t)
ios-erase (tmp _ ∷ t)    = ios-erase t

-- ★ a finished run of a closed program: the image on its compiled code is
-- legal on the cell heap, leaves it empty, closes every frame it opened, and
-- shows the world what the run does (D429)
image-noleak : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {n′ t}
             → (run : Run ds f mone mone 0 (gives mone n′) t) → Plain run
             → Σ Trace λ mt → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 0 mt end []ʳ start n′
               × OK mt (λ _ → 0) × (∀ i → play mt (λ _ → 0) i ≡ 0) × TBal mt × ios mt ≡ ios t
image-noleak {t = t} run fr with simI run fr (vw mone []ᵉ) refl []ˢ end []ʳ | noleak (plain run)
... | out ts mt st w b | (ok , clean) =
  ( mt , st
  , OK-weave w (λ _ → 0) ok
  , (λ i → trans (cong (λ h → h i) (play-weave w (λ _ → 0))) (clean i))
  , weave-post (gives mone 0) w (NoT-Bal (erase t) (erase-clean t)) b
  , trans (ios-weave w) (ios-erase t) )

-- ★ A HALTING run of a closed program (D429): the image reaches `halted`, showing the world what the
-- run does
image-halts : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {t}
            → (run : Run ds f mone mone 0 (stop halted) t) → Plain run
            → Σ Trace λ mt → Σ Sh λ sh → Σ Sh λ U → Σ (Ret U (One ∷ [] ∣ One ∷ [])) λ r′ → Σ (Cfg sh) λ m′ → Σ ℕ λ n′
                → StepsI (compᴵ ds f end) []ʳ start 0 mt (halted {sh} {U}) r′ m′ n′ × ios mt ≡ ios t
image-halts {ds = ds} {f = f} {t = t} run fr = at (simI run fr (vw mone []ᵉ) refl []ˢ end []ʳ)
  where
    at : Σ (PausedI (compᴵ ds f end) []ʳ start 0 t) (HaltIf halted) → _
    at (paused {sh′} {U′} c′ r′ m′ n′ ts mt t₀ st w p cl l , (hc , ht)) =
      mt , sh′ , U′ , r′ , m′ , n′ , subst (λ c → StepsI (compᴵ ds f end) []ʳ start 0 mt c r′ m′ n′) hc st
         , trans (ios-weave w) (trans (cong ios ht) (ios-erase t))

-- ★ ANY stopped run of a closed program from nothing (a server cut after its
-- last round, a halt): the image runs at least as far, and what it did up to
-- the run's last event is legal on the cell heap, with legal frames
image-legal : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {y t}
            → (run : Run ds f mone mone 0 (stop y) t) → Plain run
            → Σ Trace λ mt′ → Σ (List TEv) λ ts′ → Weave tmp (erase t) ts′ mt′
               × OK mt′ (λ _ → 0) × TLeg mt′
               × Σ Trace λ mt → mt′ ≼ mt × Σ Sh λ sh → Σ Sh λ U → Σ (Codeᴵ sh U) λ c′ → Σ (Ret U (One ∷ [] ∣ One ∷ [])) λ r′
                 → Σ (Cfg sh) λ m′ → Σ ℕ λ n′ → StepsI (compᴵ ds f end) []ʳ start 0 mt c′ r′ m′ n′
image-legal {t = t} run fr with simI run fr (vw mone []ᵉ) refl []ˢ end []ʳ
... | (paused {sh′} {U′} c′ r′ m′ n′ ts mt t₀ st w p cl l , _) with weave-pre w p
...   | (ts′ , mt′ , w′ , q) =
  ( mt′ , ts′ , w′
  , OK-weave w′ (λ _ → 0) (fst (exchange (plain run) pre₀ lent₀))
  , TOK-≼ q (weave-post (stop {One} exhausted) w (fst (NoT-Bal t₀ cl)) l)
  , mt , q , sh′ , U′ , c′ , r′ , m′ , n′ , st )
