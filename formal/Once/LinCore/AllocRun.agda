-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.AllocRun — plan 0.146 A17: A LEGAL RUN NEVER MAKES THE ALLOCATOR
-- FAIL.
--
-- Each size class follows the run's events of its size (`ops`): a cell born
-- or freed, a temporary born or freed. If the run's events are legal — on the
-- cell heap (`OK`: a cell born is free, one freed is live) and on the
-- temporaries' ledger (`TOK`: a temporary freed is live) — the allocator
-- makes every step (`never-fails`), its invariant holding all along. The
-- link, kept event by event: a cell of size `k` is live in the pool exactly
-- when the heap holds it, and the pool's stack of temporaries is as long as
-- the ledger counts.
--
-- ★ §4 (D411 part 2): every size at once, in ONE region (`Once.LinCore.Region`):
-- a legal run drives the region from empty without a failed step, its blocks
-- of every size lie apart, and the words it uses are at most `Σ k · peakₖ`
-- over the program's sizes (`in-one-region`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂; subst; _≢_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (+-identityʳ; +-comm)
open import Data.List using (List; []; _∷_; _++_; length; concatMap)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base; FTy)
import Once.LinCore.Alloc as A
import Once.LinCore.Region as R
open import Data.Sum using (inj₁; inj₂)

module Once.LinCore.AllocRun
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw

------------------------------------------------------------------------
-- 1. A size class's operations, from the run's events.
------------------------------------------------------------------------

opOf : ℕ → Ev → List A.Op
opOf k (alloc (k′ , s)) with k′ ≟ k
... | yes _ = A.birth s ∷ []
... | no _  = []
opOf k (free (k′ , s)) with k′ ≟ k
... | yes _ = A.death s ∷ []
... | no _  = []
opOf k (tmp (tnew k′)) with k′ ≟ k
... | yes _ = A.tbirth ∷ []
... | no _  = []
opOf k (tmp (tdel k′)) with k′ ≟ k
... | yes _ = A.tdeath ∷ []
... | no _  = []
opOf k (peek _)     = []
opOf k (io _ _ _)   = []
opOf k (stp _ _)    = []

ops : ℕ → Trace → List A.Op
ops k = concatMap (opOf k)

steps-++ : ∀ {p p′ p″ os os′} → A.Steps p os p′ → A.Steps p′ os′ p″ → A.Steps p (os ++ os′) p″
steps-++ A.done        st = st
steps-++ (e A.⟫ st₁)   st = e A.⟫ steps-++ st₁ st

------------------------------------------------------------------------
-- 2. THE LINK between the run's heap and ledger and the pool of size `k`.
------------------------------------------------------------------------

record Link (k : ℕ) (h : Heap) (L : TL) (p : A.Pool) : Set where
  field
    live⇒ : ∀ s → A.Live p s → h (k , s) ≡ 1
    ⇒live : ∀ s → h (k , s) ≡ 1 → A.Live p s
    ntemp : length (A.temps p) ≡ L k
open Link

link₀ : ∀ k → Link k (λ _ → 0) none A.empty
link₀ k = record { live⇒ = λ s () ; ⇒live = λ s () ; ntemp = refl }


private
  δ-s : ∀ {k s s′} → s ≢ s′ → δ (k , s) (k , s′) ≡ 0
  δ-s ne = δ-≢ (λ e → ne (cong snd e))

  δ-k : ∀ {k k′ s s′} → k′ ≢ k → δ (k′ , s) (k , s′) ≡ 0
  δ-k ne = δ-≢ (λ e → ne (cong fst e))

  δn-same : ∀ k → δn k k ≡ 1
  δn-same k with k ≟ k
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne refl)

  δn-other : ∀ {k k′} → k′ ≢ k → δn k′ k ≡ 0
  δn-other {k} {k′} ne with k′ ≟ k
  ... | yes e = ⊥-elim (ne e)
  ... | no _  = refl

  1≢0 : 1 ≡ 0 → ⊥
  1≢0 ()

  sym≢ : ∀ {a b : ℕ} → a ≢ b → b ≢ a
  sym≢ ne e = ne (sym e)

-- an event of another size class asks nothing of this one
alloc-none : ∀ {k k′ s} → k′ ≢ k → opOf k (alloc (k′ , s)) ≡ []
alloc-none {k} {k′} ne with k′ ≟ k
... | yes e = ⊥-elim (ne e)
... | no _  = refl

free-none : ∀ {k k′ s} → k′ ≢ k → opOf k (free (k′ , s)) ≡ []
free-none {k} {k′} ne with k′ ≟ k
... | yes e = ⊥-elim (ne e)
... | no _  = refl

tnew-none : ∀ {k k′} → k′ ≢ k → opOf k (tmp (tnew k′)) ≡ []
tnew-none {k} {k′} ne with k′ ≟ k
... | yes e = ⊥-elim (ne e)
... | no _  = refl

tdel-none : ∀ {k k′} → k′ ≢ k → opOf k (tmp (tdel k′)) ≡ []
tdel-none {k} {k′} ne with k′ ≟ k
... | yes e = ⊥-elim (ne e)
... | no _  = refl

-- an event of this size class: its one operation
alloc-one : ∀ k s → opOf k (alloc (k , s)) ≡ A.birth s ∷ []
alloc-one k s with k ≟ k
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

free-one : ∀ k s → opOf k (free (k , s)) ≡ A.death s ∷ []
free-one k s with k ≟ k
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

tnew-one : ∀ k → opOf k (tmp (tnew k)) ≡ A.tbirth ∷ []
tnew-one k with k ≟ k
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

tdel-one : ∀ k → opOf k (tmp (tdel k)) ≡ A.tdeath ∷ []
tdel-one k with k ≟ k
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

-- one step, as the steps of that one operation
one : ∀ {p p′ os o} → os ≡ o ∷ [] → A.step o p ≡ just p′ → A.Steps p os p′
one refl e = e A.⟫ A.done

-- one event: the allocator's steps for it, its invariant, the link kept
record After (k : ℕ) (x : Ev) (h : Heap) (L : TL) (p : A.Pool) : Set where
  constructor after
  field
    p₁    : A.Pool
    steps : A.Steps p (opOf k x) p₁
    inv   : A.Inv p₁
    link  : Link k (step x h) (tstep x L) p₁

same : ∀ {k x h L p} → A.Inv p → Link k h L p → opOf k x ≡ [] → (∀ s → step x h (k , s) ≡ h (k , s))
     → tstep x L k ≡ L k → After k x h L p
same {k} {x} {h} {L} {p} iv lk e hs ls =
  after p (subst (λ os → A.Steps p os p) (sym e) A.done) iv
    (record { live⇒ = λ s l → trans (hs s) (live⇒ lk s l)
            ; ⇒live = λ s q → ⇒live lk s (trans (sym (hs s)) q)
            ; ntemp = trans (ntemp lk) (sym ls) })

event : ∀ k x {h L p} → okPre x h → tpre x L → A.Inv p → Link k h L p → After k x h L p
event k (alloc (k′ , s)) {h} {L} {p} ok _ iv lk with k′ ≟ k
... | no ne = same iv lk (alloc-none ne) (λ s′ → trans (cong (h (k , s′) +_) (δ-k {s = s} {s′ = s′} ne)) (+-identityʳ _)) refl
... | yes refl = after (A.bornP s p) (one (alloc-one k s) (A.born-ok s p nl)) (A.born-inv s p iv (A.born-ok s p nl))
                   (record { live⇒ = lv ; ⇒live = vl ; ntemp = ntemp lk })
  where
    nl : ¬ A.Live p s
    nl l = 1≢0 (trans (sym (live⇒ lk s l)) ok)
    lv′ : ∀ s′ → Dec (s ≡ s′) → A.Live (A.bornP s p) s′ → h (k , s′) + δ (k , s) (k , s′) ≡ 1
    lv′ s′ (yes refl) l = trans (cong (_+ δ (k , s) (k , s)) ok) (δ-same (k , s))
    lv′ s′ (no ne)    l = trans (cong (h (k , s′) +_) (δ-s ne)) (trans (+-identityʳ _) (live⇒ lk s′ (A.born-to s p (sym≢ ne) l)))
    lv : ∀ s′ → A.Live (A.bornP s p) s′ → h (k , s′) + δ (k , s) (k , s′) ≡ 1
    lv s′ = lv′ s′ (s ≟ s′)
    vl′ : ∀ s′ → Dec (s ≡ s′) → h (k , s′) + δ (k , s) (k , s′) ≡ 1 → A.Live (A.bornP s p) s′
    vl′ s′ (yes refl) q = A.born-live s p
    vl′ s′ (no ne)    q = A.born-from s p iv (sym≢ ne) (⇒live lk s′ (trans (sym (trans (cong (h (k , s′) +_) (δ-s ne)) (+-identityʳ _))) q))
    vl : ∀ s′ → h (k , s′) + δ (k , s) (k , s′) ≡ 1 → A.Live (A.bornP s p) s′
    vl s′ = vl′ s′ (s ≟ s′)
event k (free (k′ , s)) {h} {L} {p} ok _ iv lk with k′ ≟ k
... | no ne = same iv lk (free-none ne) (λ s′ → cong (h (k , s′) ∸_) (δ-k {s = s} {s′ = s′} ne)) refl
... | yes refl = after (A.diedP s p) (one (free-one k s) (A.died-ok s p ls)) (A.died-inv s p iv (A.died-ok s p ls))
                   (record { live⇒ = lv ; ⇒live = vl ; ntemp = ntemp lk })
  where
    ls : A.Live p s
    ls = ⇒live lk s ok
    lv′ : ∀ s′ → Dec (s ≡ s′) → A.Live (A.diedP s p) s′ → h (k , s′) ∸ δ (k , s) (k , s′) ≡ 1
    lv′ s′ (yes refl) l = ⊥-elim (A.died-dead s p l)
    lv′ s′ (no ne)    l = trans (cong (h (k , s′) ∸_) (δ-s ne)) (live⇒ lk s′ (A.died-to s p l))
    lv : ∀ s′ → A.Live (A.diedP s p) s′ → h (k , s′) ∸ δ (k , s) (k , s′) ≡ 1
    lv s′ = lv′ s′ (s ≟ s′)
    cong∸ : ∀ {a b c d : ℕ} → a ≡ c → b ≡ d → a ∸ b ≡ c ∸ d
    cong∸ refl refl = refl
    vl′ : ∀ s′ → Dec (s ≡ s′) → h (k , s′) ∸ δ (k , s) (k , s′) ≡ 1 → A.Live (A.diedP s p) s′
    vl′ s′ (yes refl) q = ⊥-elim (1≢0 (trans (sym q) (cong∸ ok (δ-same (k , s)))))
    vl′ s′ (no ne)    q = A.died-from s p ls (sym≢ ne) (⇒live lk s′ (trans (sym (cong (h (k , s′) ∸_) (δ-s ne))) q))
    vl : ∀ s′ → h (k , s′) ∸ δ (k , s) (k , s′) ≡ 1 → A.Live (A.diedP s p) s′
    vl s′ = vl′ s′ (s ≟ s′)
event k (peek _)   ok _ iv lk = same iv lk refl (λ _ → refl) refl
event k (io _ _ _) ok _ iv lk = same iv lk refl (λ _ → refl) refl
event k (stp _ _)  ok _ iv lk = same iv lk refl (λ _ → refl) refl
event k (tmp (tnew k′)) {h} {L} {p} _ _ iv lk with k′ ≟ k
... | no ne = same iv lk (tnew-none ne) (λ _ → refl) (trans (cong (L k +_) (δn-other ne)) (+-identityʳ _))
... | yes refl = after (A.tborn p) (one (tnew-one k) refl) (A.tborn-inv p iv)
                   (record { live⇒ = λ s l → live⇒ lk s (A.tborn-to p l)
                           ; ⇒live = λ s q → A.tborn-from p iv (⇒live lk s q)
                           ; ntemp = trans (cong suc (ntemp lk))
                                           (sym (trans (cong (L k +_) (δn-same k)) (+-comm (L k) 1))) })
event k (tmp (tdel k′)) {h} {L} {p} _ tp iv lk with k′ ≟ k
... | no ne = same iv lk (tdel-none ne) (λ _ → refl) (cong (L k ∸_) (δn-other ne))
... | yes refl with A.temps p in eq
...   | [] = ⊥-elim (z≰ (subst (1 ≤_) (trans (sym (ntemp lk)) (cong length eq)) tp))
  where z≰ : 1 ≤ 0 → ⊥
        z≰ ()
...   | (m , j) ∷ ts =
  after _ (one (tdel-one k) (A.tdied-ok p eq)) (A.tdied-inv p iv (A.tdied-ok p eq))
        (record { live⇒ = λ s l → live⇒ lk s (A.tdied-to p {j = j} {ts = ts} l)
                ; ⇒live = λ s q → A.tdied-from p iv eq (⇒live lk s q)
                ; ntemp = trans (cong (_∸ 1) (trans (sym (cong length eq)) (ntemp lk)))
                                (sym (cong (L k ∸_) (δn-same k))) })

------------------------------------------------------------------------
-- 3. ★ THE THEOREM.
------------------------------------------------------------------------

-- along a legal stretch, the allocator makes every step, its invariant and
-- the link holding
along : ∀ k t {h L p} → OK t h → TOK t L → A.Inv p → Link k h L p
      → Σ A.Pool λ p′ → A.Steps p (ops k t) p′ × A.Inv p′
along k []      _          _          iv lk = (_ , A.done , iv)
along k (x ∷ t) (ox , ot) (tx , tt′) iv lk with event k x ox tx iv lk
... | after p₁ st₁ iv₁ lk₁ with along k t ot tt′ iv₁ lk₁
...   | (p′ , st , iv′) = (p′ , steps-++ st₁ st , iv′)

-- ★ a legal run, from nothing: every size class's allocator makes every
-- step, from an empty region, its invariant holding — so the region grows
-- only when full (`A.grows-only-when-full`), and live blocks have distinct
-- addresses (`A.live-injective`)
never-fails : ∀ t → OK t (λ _ → 0) → TLeg t → ∀ k → Σ A.Pool λ p′ → A.Steps A.empty (ops k t) p′ × A.Inv p′
never-fails t ok tl k = along k t ok tl A.inv-empty (link₀ k)

------------------------------------------------------------------------
-- 4. ★ ONE REGION FOR EVERY SIZE (D411 part 2, `Once.LinCore.Region`).
------------------------------------------------------------------------

-- the run's events, as operations on the region: each on its own size
gopOf : Ev → List (ℕ × A.Op)
gopOf (alloc (k , s))  = (k , A.birth s) ∷ []
gopOf (free (k , s))   = (k , A.death s) ∷ []
gopOf (tmp (tnew k))   = (k , A.tbirth) ∷ []
gopOf (tmp (tdel k))   = (k , A.tdeath) ∷ []
gopOf (peek _)         = []
gopOf (io _ _ _)       = []
gopOf (stp _ _)        = []

gops : Trace → List (ℕ × A.Op)
gops = concatMap gopOf

-- every size's pool linked to the run
GLink : Heap → TL → R.Region → Set
GLink h L r = ∀ k → Link k h L (R.pools r k)

-- an event that asks nothing of size `k` leaves its pool as it was
after-none : ∀ {k x h L p} → opOf k x ≡ [] → After k x h L p → Link k (step x h) (tstep x L) p
after-none e (after p₁ st _ lk) with subst (λ os → A.Steps _ os p₁) e st
... | A.done = lk

-- an event of size `k`: its one operation is the pool's step
after-one : ∀ {k x h L p o} → opOf k x ≡ o ∷ [] → (a : After k x h L p) → A.step o p ≡ just (After.p₁ a)
after-one e (after p₁ st _ _) with subst (λ os → A.Steps _ os p₁) e st
... | e′ A.⟫ A.done = e′

GAfter : Ev → Heap → TL → R.Region → Set
GAfter x h L r = Σ R.Region λ r′ → R.GSteps r (gopOf x) r′ × R.RInv r′ × GLink (step x h) (tstep x L) r′

-- an event of one size: that pool steps, the others stay
gone : ∀ x {h L r} k₀ o → gopOf x ≡ (k₀ , o) ∷ [] → opOf k₀ x ≡ o ∷ [] → (∀ k → k₀ ≢ k → opOf k x ≡ [])
     → okPre x h → tpre x L → R.RInv r → GLink h L r → GAfter x h L r
gone x {h} {L} {r} k₀ o eg e₀ en ok tp iv lk =
  (R.place k₀ p₁ r , subst (λ gs → R.GSteps r gs (R.place k₀ p₁ r)) (sym eg) (R.gstep-ok {k₀} {o} {r} ep R.⟫ R.done)
  , R.rinv-place k₀ o r iv ep , lk′)
  where
    a  = event k₀ x ok tp (R.pinv iv k₀) (lk k₀)
    p₁ = After.p₁ a
    ep = after-one e₀ a
    lk′ : GLink (step x h) (tstep x L) (R.place k₀ p₁ r)
    lk′ k rewrite R.place-pools k₀ p₁ r with R.upd-view (R.pools r) k₀ p₁ k
    ... | inj₁ (refl , q) = subst (Link k _ _) (sym q) (After.link a)
    ... | inj₂ (ne , q)   = subst (Link k _ _) (sym q) (after-none (en k ne) (event k x ok tp (R.pinv iv k) (lk k)))

-- an event of no size: nothing steps
gzero : ∀ x {h L r} → gopOf x ≡ [] → (∀ k → opOf k x ≡ []) → okPre x h → tpre x L → R.RInv r → GLink h L r
      → GAfter x h L r
gzero x {r = r} eg en ok tp iv lk =
  (r , subst (λ gs → R.GSteps r gs r) (sym eg) R.done , iv
  , λ k → after-none (en k) (event k x ok tp (R.pinv iv k) (lk k)))

gevent : ∀ x {h L r} → okPre x h → tpre x L → R.RInv r → GLink h L r → GAfter x h L r
gevent (alloc (k , s))  = gone (alloc (k , s)) k (A.birth s) refl (alloc-one k s) (λ _ ne → alloc-none ne)
gevent (free (k , s))   = gone (free (k , s)) k (A.death s) refl (free-one k s) (λ _ ne → free-none ne)
gevent (tmp (tnew k))   = gone (tmp (tnew k)) k A.tbirth refl (tnew-one k) (λ _ ne → tnew-none ne)
gevent (tmp (tdel k))   = gone (tmp (tdel k)) k A.tdeath refl (tdel-one k) (λ _ ne → tdel-none ne)
gevent (peek i)         = gzero (peek i) refl (λ _ → refl)
gevent (io s x y)       = gzero (io s x y) refl (λ _ → refl)
gevent (stp s x)        = gzero (stp s x) refl (λ _ → refl)

galong : ∀ t {h L r} → OK t h → TOK t L → R.RInv r → GLink h L r
       → Σ R.Region λ r′ → R.GSteps r (gops t) r′ × R.RInv r′
galong []      _          _          iv lk = (_ , R.done , iv)
galong (x ∷ t) (ox , ot) (tx , tt′) iv lk with gevent x ox tx iv lk
... | (r₁ , st₁ , iv₁ , lk₁) with galong t ot tt′ iv₁ lk₁
...   | (r′ , st , iv′) = (r′ , R.gsteps-++ st₁ st , iv′)

-- ★ A LEGAL RUN IN ONE REGION, over the program's sizes `ks`:
--   * the region makes every step, from empty;
--   * the blocks of every size lie apart, below the top (`R.RInv`);
--   * the words in use are at most `Σ k · topₖ`;
--   * and every `topₖ` is a peak: at some moment of the run that many
--     blocks of size `k` were owned at once.
-- So the run runs out of a region of `M` words only if `Σ k · peakₖ > M`.
in-one-region : ∀ ks t → OK t (λ _ → 0) → TLeg t → R.Sizes ks (gops t)
              → Σ R.Region λ r → R.GSteps R.empty (gops t) r × R.RInv r
                               × R.wtop r ≤ R.Words ks r × (∀ k → R.Peak (gops t) k (R.tops r k))
in-one-region ks t ok tl sz with galong t ok tl R.rinv-empty (λ k → link₀ k)
... | (r , st , iv) = (r , st , iv , R.space ks sz z≤n st , R.peak st)
