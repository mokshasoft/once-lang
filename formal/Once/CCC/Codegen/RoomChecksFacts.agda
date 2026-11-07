-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.RoomChecksFacts — where the room-check pass puts things.
--
-- Plan 0.123 A.4 step 5 (D377). The pass (`RoomChecks.room-checks`) only ever
-- INSERTS `instr-room` instructions, so every instruction of the image keeps
-- its order and moves to a later index. This module names that index map and
-- proves what the transparency simulation needs of it:
--
--   * `ψ t i`: where instruction `i` of `t` sits in `checks E t`;
--     `φ t i = suc (ψ t i)` is its place in `room-checks t` (past the check at 0);
--   * `fetch-room`: the image with checks holds instruction `i` at `φ t i`.
--
-- `ψ` is defined by recursion on the trace, not as `i + (boundaries before i)`,
-- so the proofs follow `checks`' own recursion and need no arithmetic.
------------------------------------------------------------------------

module Once.CCC.Codegen.RoomChecksFacts where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; instr-room)
open import Once.CCC.Codegen.RoomChecks using (boundary?; stretch; checks; room-checks; max-entry)

-- one more index when the instruction just passed is a boundary (its check follows it)
bump : Bool → ℕ → ℕ
bump true  n = suc n
bump false n = n

-- where instruction `i` of `t` sits in `checks E t`
ψ : AbstractTrace → ℕ → ℕ
ψ []      i       = i
ψ (x ∷ t) zero    = zero
ψ (x ∷ t) (suc i) = suc (bump (boundary? x) (ψ t i))

-- …and in `room-checks t`, past the leading check
φ : AbstractTrace → ℕ → ℕ
φ t i = suc (ψ t i)

module RoomFacts {FS : FrameSemantics} where
  open FlatMachine {FS} using (fetch)

  -- what follows a boundary instruction in `checks`, read at a bumped index
  private
    fetch-after : ∀ (b : Bool) (k : ℕ) (C : AbstractTrace) (j : ℕ) {r : Maybe AbstractInstr}
                → fetch C j ≡ r
                → fetch (if b then instr-room k ∷ C else C) (bump b j) ≡ r
    fetch-after true  k C j e = e
    fetch-after false k C j e = e

  -- THE INSTRUCTIONS STAY: `checks E t` holds instruction `i` of `t` at `ψ t i`.
  fetch-checks : ∀ (E : ℕ) (t : AbstractTrace) (i : ℕ) → fetch (checks E t) (ψ t i) ≡ fetch t i
  fetch-checks E []      i       = refl
  fetch-checks E (x ∷ t) zero    = refl
  fetch-checks E (x ∷ t) (suc i) =
    fetch-after (boundary? x) (stretch E t) (checks E t) (ψ t i) (fetch-checks E t i)

  -- …and the whole pass, past its leading check.
  fetch-room : ∀ (t : AbstractTrace) (i : ℕ) → fetch (room-checks t) (φ t i) ≡ fetch t i
  fetch-room t i = fetch-checks (max-entry t) t i

  ------------------------------------------------------------------------
  -- THE SCANS COMMUTE with the map: a check is neither a label nor an entry, so
  -- `find-label` / `find-entry` on the image with checks find `φ` of what they
  -- find on the image without. (Jumps and calls are by NAME, which is why one
  -- index map serves the whole control flow.)
  ------------------------------------------------------------------------
  open FlatMachine {FS} using (fl-go; fl-at; fl-label-match; ft-go; ft-at; ft-match; find-label; find-entry; label-of?; entry-of?)
  open import Data.Maybe using () renaming (map to mmap)
  open import Data.Nat using (_+_)
  open import Data.Nat.Properties using (+-suc; +-identityʳ)
  open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
  open import Once.CCC.Label using (LabelId; _≡ᵇᴵ_; EntryId; _≡ᵇᴱ_)

  private
    mmap-ext : ∀ {f g : ℕ → ℕ} → (∀ i → f i ≡ g i) → ∀ (mx : Maybe ℕ) → mmap f mx ≡ mmap g mx
    mmap-ext e (just i) = cong just (e i)
    mmap-ext e nothing  = refl

    mmap-suc : ∀ (f : ℕ → ℕ) (mx : Maybe ℕ) → mmap f (mmap suc mx) ≡ mmap (λ i → f (suc i)) mx
    mmap-suc f (just i) = refl
    mmap-suc f nothing  = refl

    -- the index arithmetic of passing one instruction (and its check, if any)
    pass-eq : ∀ (b : Bool) (a y : ℕ) → (if b then suc (suc a) else suc a) + y ≡ a + suc (bump b y)
    pass-eq true  a y = sym (trans (+-suc a (suc y)) (cong suc (+-suc a y)))
    pass-eq false a y = sym (+-suc a y)

  -- starting a scan one later finds one later
  fl-go-suc : ∀ (xs : AbstractTrace) (m : LabelId) (b : ℕ) → fl-go xs m (suc b) ≡ mmap suc (fl-go xs m b)
  flm-suc   : ∀ (c : Bool) (xs : AbstractTrace) (m : LabelId) (b : ℕ)
            → fl-label-match c xs m (suc b) ≡ mmap suc (fl-label-match c xs m b)
  fl-go-suc []       m b = refl
  fl-go-suc (x ∷ xs) m b with label-of? x
  ... | just l  = flm-suc (l ≡ᵇᴵ m) xs m b
  ... | nothing = fl-go-suc xs m (suc b)
  flm-suc true  xs m b = refl
  flm-suc false xs m b = fl-go-suc xs m (suc b)

  private
    -- the label scan past one instruction of `t` and (if it is a boundary) its check
    fl-pass : ∀ (b : Bool) (k : ℕ) (C t : AbstractTrace) (m : LabelId) (a : ℕ)
            → (∀ a' → fl-go C m a' ≡ mmap (λ i → a' + ψ t i) (fl-go t m 0))
            → fl-go (if b then instr-room k ∷ C else C) m (suc a)
              ≡ mmap (λ i → a + suc (bump b (ψ t i))) (fl-go t m 0)
    fl-pass true  k C t m a ih =
      trans (ih (suc (suc a))) (mmap-ext (λ i → pass-eq true a (ψ t i)) (fl-go t m 0))
    fl-pass false k C t m a ih =
      trans (ih (suc a)) (mmap-ext (λ i → pass-eq false a (ψ t i)) (fl-go t m 0))

  fl-checks : ∀ (E : ℕ) (t : AbstractTrace) (m : LabelId) (a : ℕ)
            → fl-go (checks E t) m a ≡ mmap (λ i → a + ψ t i) (fl-go t m 0)
  fl-checks E []      m a = refl
  fl-checks E (x ∷ t) m a with label-of? x
  ... | nothing =
    trans (fl-pass (boundary? x) (stretch E t) (checks E t) t m a (fl-checks E t m))
          (sym (trans (cong (mmap (λ i → a + ψ (x ∷ t) i)) (fl-go-suc t m 0))
                      (mmap-suc (λ i → a + ψ (x ∷ t) i) (fl-go t m 0))))
  ... | just l with l ≡ᵇᴵ m
  ...   | true  = cong just (sym (+-identityʳ a))
  ...   | false =
    trans (fl-pass (boundary? x) (stretch E t) (checks E t) t m a (fl-checks E t m))
          (sym (trans (cong (mmap (λ i → a + ψ (x ∷ t) i)) (fl-go-suc t m 0))
                      (mmap-suc (λ i → a + ψ (x ∷ t) i) (fl-go t m 0))))

  -- JUMPS: the image with checks finds each label at `φ` of its old index.
  find-label-room : ∀ (t : AbstractTrace) (m : LabelId)
                  → find-label (room-checks t) m ≡ mmap (φ t) (find-label t m)
  find-label-room t m = fl-checks (max-entry t) t m 1

  -- …and the same for the entry scan (calls).
  ft-go-suc : ∀ (xs : AbstractTrace) (e : EntryId) (b : ℕ) → ft-go xs e (suc b) ≡ mmap suc (ft-go xs e b)
  ftm-suc   : ∀ (c : Bool) (xs : AbstractTrace) (e : EntryId) (b : ℕ)
            → ft-match c xs e (suc b) ≡ mmap suc (ft-match c xs e b)
  ft-go-suc []       e b = refl
  ft-go-suc (x ∷ xs) e b with entry-of? x
  ... | just e' = ftm-suc (e' ≡ᵇᴱ e) xs e b
  ... | nothing = ft-go-suc xs e (suc b)
  ftm-suc true  xs e b = refl
  ftm-suc false xs e b = ft-go-suc xs e (suc b)

  private
    ft-pass : ∀ (b : Bool) (k : ℕ) (C t : AbstractTrace) (e : EntryId) (a : ℕ)
            → (∀ a' → ft-go C e a' ≡ mmap (λ i → a' + ψ t i) (ft-go t e 0))
            → ft-go (if b then instr-room k ∷ C else C) e (suc a)
              ≡ mmap (λ i → a + suc (bump b (ψ t i))) (ft-go t e 0)
    ft-pass true  k C t e a ih =
      trans (ih (suc (suc a))) (mmap-ext (λ i → pass-eq true a (ψ t i)) (ft-go t e 0))
    ft-pass false k C t e a ih =
      trans (ih (suc a)) (mmap-ext (λ i → pass-eq false a (ψ t i)) (ft-go t e 0))

  ft-checks : ∀ (E : ℕ) (t : AbstractTrace) (e : EntryId) (a : ℕ)
            → ft-go (checks E t) e a ≡ mmap (λ i → a + ψ t i) (ft-go t e 0)
  ft-checks E []      e a = refl
  ft-checks E (x ∷ t) e a with entry-of? x
  ... | nothing =
    trans (ft-pass (boundary? x) (stretch E t) (checks E t) t e a (ft-checks E t e))
          (sym (trans (cong (mmap (λ i → a + ψ (x ∷ t) i)) (ft-go-suc t e 0))
                      (mmap-suc (λ i → a + ψ (x ∷ t) i) (ft-go t e 0))))
  ... | just e' with e' ≡ᵇᴱ e
  ...   | true  = cong just (sym (+-identityʳ a))
  ...   | false =
    trans (ft-pass (boundary? x) (stretch E t) (checks E t) t e a (ft-checks E t e))
          (sym (trans (cong (mmap (λ i → a + ψ (x ∷ t) i)) (ft-go-suc t e 0))
                      (mmap-suc (λ i → a + ψ (x ∷ t) i) (ft-go t e 0))))

  -- CALLS: the image with checks finds each entry at `φ` of its old index.
  find-entry-room : ∀ (t : AbstractTrace) (e : EntryId)
                  → find-entry (room-checks t) e ≡ mmap (φ t) (find-entry t e)
  find-entry-room t e = ft-checks (max-entry t) t e 1

  ------------------------------------------------------------------------
  -- ONE INSTRUCTION FURTHER: the map advances by one, or by two when the
  -- instruction is a boundary — and then its check sits in between.
  ------------------------------------------------------------------------
  open import Data.List using (drop)

  ψ-zero : ∀ (t : AbstractTrace) → ψ t 0 ≡ 0
  ψ-zero []      = refl
  ψ-zero (x ∷ t) = refl

  private
    bump-suc : ∀ (b : Bool) (n : ℕ) → bump b (suc n) ≡ suc (bump b n)
    bump-suc true  n = refl
    bump-suc false n = refl

    bump-comm : ∀ (b c : Bool) (n : ℕ) → bump b (bump c n) ≡ bump c (bump b n)
    bump-comm true  true  n = refl
    bump-comm true  false n = refl
    bump-comm false true  n = refl
    bump-comm false false n = refl

    -- `bump b (suc (bump c n)) ≡ suc (bump c (bump b n))`: the two orders agree
    bump-swap : ∀ (b c : Bool) (n : ℕ) → bump b (suc (bump c n)) ≡ suc (bump c (bump b n))
    bump-swap b c n = trans (bump-suc b (bump c n)) (cong suc (bump-comm b c n))

  ψ-next : ∀ (t : AbstractTrace) (i : ℕ) {x : AbstractInstr} → fetch t i ≡ just x
         → ψ t (suc i) ≡ suc (bump (boundary? x) (ψ t i))
  ψ-next (y ∷ t) zero    refl = cong (λ z → suc (bump (boundary? y) z)) (ψ-zero t)
  ψ-next (y ∷ t) (suc i) {x} e =
    trans (cong (λ z → suc (bump (boundary? y) z)) (ψ-next t i e))
          (cong suc (trans (bump-swap (boundary? y) (boundary? x) (ψ t i))
                           (sym (bump-suc (boundary? x) (bump (boundary? y) (ψ t i))))))

  private
    -- the place just after a bumped index, read through `checks`' branch
    fetch-after-suc : ∀ (b : Bool) (k : ℕ) (C : AbstractTrace) (j : ℕ) {r : Maybe AbstractInstr}
                    → fetch C (suc j) ≡ r
                    → fetch (if b then instr-room k ∷ C else C) (suc (bump b j)) ≡ r
    fetch-after-suc true  k C j e = e
    fetch-after-suc false k C j e = e

    -- …and right after a boundary instruction: its check
    check-here : ∀ (b : Bool) (k : ℕ) (C : AbstractTrace) → b ≡ true
               → fetch (if b then instr-room k ∷ C else C) zero ≡ just (instr-room k)
    check-here true k C refl = refl

  -- A BOUNDARY'S CHECK: right after a boundary instruction, `checks` holds the
  -- check for the stretch that follows it.
  check-at : ∀ (E : ℕ) (t : AbstractTrace) (i : ℕ) {x : AbstractInstr}
           → fetch t i ≡ just x → boundary? x ≡ true
           → fetch (checks E t) (suc (ψ t i)) ≡ just (instr-room (stretch E (drop (suc i) t)))
  check-at E (y ∷ t) zero    refl bnd = check-here (boundary? y) (stretch E t) (checks E t) bnd
  check-at E (y ∷ t) (suc i) e    bnd =
    fetch-after-suc (boundary? y) (stretch E t) (checks E t) (ψ t i) (check-at E t i e bnd)

  -- …and past the end of the image the map just counts on.
  ψ-next-nothing : ∀ (t : AbstractTrace) (i : ℕ) → fetch t i ≡ nothing → ψ t (suc i) ≡ suc (ψ t i)
  ψ-next-nothing []      i       e  = refl
  ψ-next-nothing (y ∷ t) (suc i) e  =
    cong suc (trans (cong (bump (boundary? y)) (ψ-next-nothing t i e)) (bump-suc (boundary? y) (ψ t i)))

------------------------------------------------------------------------
-- WHAT HOLDS OF EVERY INSTRUCTION, OR OF SOME: the pass only inserts checks,
-- so an `All` crosses it when the checks satisfy the predicate too, and an
-- `Any` crosses it unconditionally.
------------------------------------------------------------------------
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)

private
  all-after : ∀ {P : AbstractInstr → Set} (b : Bool) (k : ℕ) {C : AbstractTrace}
            → P (instr-room k) → All P C → All P (if b then instr-room k ∷ C else C)
  all-after true  k pk a = pk ∷ a
  all-after false k pk a = a

  any-after : ∀ {P : AbstractInstr → Set} (b : Bool) (k : ℕ) {C : AbstractTrace}
            → Any P C → Any P (if b then instr-room k ∷ C else C)
  any-after true  k a = there a
  any-after false k a = a

All-checks : ∀ {P : AbstractInstr → Set} (E : ℕ) (t : AbstractTrace)
           → (∀ k → P (instr-room k)) → All P t → All P (checks E t)
All-checks E []      pr []       = []
All-checks E (x ∷ t) pr (px ∷ a) = px ∷ all-after (boundary? x) (stretch E t) (pr _) (All-checks E t pr a)

All-room : ∀ {P : AbstractInstr → Set} (t : AbstractTrace)
         → (∀ k → P (instr-room k)) → All P t → All P (room-checks t)
All-room t pr a = pr _ ∷ All-checks (max-entry t) t pr a

Any-checks : ∀ {P : AbstractInstr → Set} (E : ℕ) (t : AbstractTrace) → Any P t → Any P (checks E t)
Any-checks E (x ∷ t) (here p)  = here p
Any-checks E (x ∷ t) (there a) = there (any-after (boundary? x) (stretch E t) (Any-checks E t a))

Any-room : ∀ {P : AbstractInstr → Set} (t : AbstractTrace) → Any P t → Any P (room-checks t)
Any-room t a = there (Any-checks (max-entry t) t a)

------------------------------------------------------------------------
-- WHAT A TRACE DEFINES: a fold to which a check contributes nothing (a check
-- defines no label, entry or symbol) folds the image with checks to the same.
------------------------------------------------------------------------
module _ {X : Set} (F : AbstractTrace → X) (g : AbstractInstr → X → X)
         (F-∷ : ∀ i is → F (i ∷ is) ≡ g i (F is)) (g-room : ∀ k x → g (instr-room k) x ≡ x) where
  open import Relation.Binary.PropositionalEquality using (trans; cong; sym)

  private
    fold-after : ∀ (b : Bool) (k : ℕ) (C : AbstractTrace) → F (if b then instr-room k ∷ C else C) ≡ F C
    fold-after true  k C = trans (F-∷ (instr-room k) C) (g-room k (F C))
    fold-after false k C = refl

  fold-checks : ∀ (E : ℕ) (t : AbstractTrace) → F (checks E t) ≡ F t
  fold-checks E []      = refl
  fold-checks E (x ∷ t) =
    trans (F-∷ x _) (trans (cong (g x) (trans (fold-after (boundary? x) (stretch E t) (checks E t)) (fold-checks E t)))
                           (sym (F-∷ x t)))

  fold-room : ∀ (t : AbstractTrace) → F (room-checks t) ≡ F t
  fold-room t = trans (F-∷ (instr-room _) (checks (max-entry t) t))
                      (trans (g-room _ _) (fold-checks (max-entry t) t))

------------------------------------------------------------------------
-- WHAT A TRACE REFERENCES: a check DOES reference something — the Host's
-- `once_exhausted`, which it calls when there is no room. So a property of every
-- reference crosses the pass when the check's references have it too.
------------------------------------------------------------------------
module _ {X : Set} {P : X → Set} (F : AbstractTrace → List X) (f : AbstractInstr → List X)
         (F-∷ : ∀ i is → F (i ∷ is) ≡ f i Data.List.++ F is) (f-room : ∀ k → All P (f (instr-room k))) where
  open import Data.List.Relation.Unary.All.Properties using (++⁺; ++⁻)
  open import Relation.Binary.PropositionalEquality using (subst; sym)
  open import Data.Product using (proj₁; proj₂)

  private
    all-fold-after : ∀ (b : Bool) (k : ℕ) (C : AbstractTrace) → All P (F C)
                   → All P (F (if b then instr-room k ∷ C else C))
    all-fold-after true  k C a = subst (All P) (sym (F-∷ (instr-room k) C)) (++⁺ (f-room k) a)
    all-fold-after false k C a = a

  All-fold-checks : ∀ (E : ℕ) (t : AbstractTrace) → All P (F t) → All P (F (checks E t))
  All-fold-checks E []      a = a
  All-fold-checks E (x ∷ t) a =
    subst (All P) (sym (F-∷ x _))
      (++⁺ (proj₁ split) (all-fold-after (boundary? x) (stretch E t) (checks E t) (All-fold-checks E t (proj₂ split))))
    where split = ++⁻ (f x) (subst (All P) (F-∷ x t) a)

  All-fold-room : ∀ (t : AbstractTrace) → All P (F t) → All P (F (room-checks t))
  All-fold-room t a =
    subst (All P) (sym (F-∷ (instr-room _) (checks (max-entry t) t)))
      (++⁺ (f-room _) (All-fold-checks (max-entry t) t a))

------------------------------------------------------------------------
-- THE BUDGET'S ARITHMETIC (plan 0.123 A.4 step 5): each check's `k` is what the
-- code spends after it up to the next check, and an ordinary instruction's
-- measure is its own spend plus its successor's.
------------------------------------------------------------------------
open import Once.CCC.Codegen.RoomChecks using (room?; till-check; need; spend; entry-frame)
open import Data.List using (drop)
open import Data.Nat using (_⊔_; _+_)

-- the program image has no checks of its own
NoRoom : AbstractTrace → Set
NoRoom = All (λ i → room? i ≡ false)

-- a check reserves no frame, so the largest entry frame is the same
max-entry-room : ∀ (t : AbstractTrace) → max-entry (room-checks t) ≡ max-entry t
max-entry-room = fold-room max-entry (λ i x → entry-frame i ⊔ x) (λ _ _ → refl) (λ _ _ → refl)

private
  till-after : ∀ (E : ℕ) (b : Bool) (k : ℕ) (C : AbstractTrace)
             → till-check E (if b then instr-room k ∷ C else C) ≡ (if b then 0 else till-check E C)
  till-after E true  k C = refl
  till-after E false k C = refl

  plus-if : ∀ (a : ℕ) (b : Bool) (x y : ℕ) → x ≡ y → a + (if b then 0 else x) ≡ a + (if b then 0 else y)
  plus-if a b x y e = cong (λ z → a + (if b then 0 else z)) e
    where open import Relation.Binary.PropositionalEquality using (cong)

-- WHAT FOLLOWS A CHECK SPENDS ITS STRETCH
till-checks : ∀ (E : ℕ) (t : AbstractTrace) → NoRoom t → till-check E (checks E t) ≡ stretch E t
till-checks E []      []        = refl
till-checks E (x ∷ t) (nr ∷ a) rewrite nr =
  trans (cong (spend E x +_) (till-after E (boundary? x) (stretch E t) (checks E t)))
        (plus-if (spend E x) (boundary? x) (till-check E (checks E t)) (stretch E t) (till-checks E t a))
  where open import Relation.Binary.PropositionalEquality using (trans; cong)

module CheckK {FS : FrameSemantics} where
  open FlatMachine {FS} using (fetch)
  open import Relation.Binary.PropositionalEquality using (trans; cong; sym)
  open import Data.Maybe.Properties using (just-injective)
  open import Data.Empty using (⊥; ⊥-elim)

  private
    room≢ : ∀ {x : AbstractInstr} {k : ℕ} → room? x ≡ false → x ≡ instr-room k → ⊥
    room≢ () refl

    -- in `checks`' branch after `x`: a check found there is the one just past `x`,
    -- or one further on
    k-after : ∀ (E : ℕ) (b : Bool) (t : AbstractTrace) (j k : ℕ) → NoRoom t
            → (∀ j′ → fetch (checks E t) j′ ≡ just (instr-room k) → k ≡ till-check E (drop (suc j′) (checks E t)))
            → fetch (if b then instr-room (stretch E t) ∷ checks E t else checks E t) j ≡ just (instr-room k)
            → k ≡ till-check E (drop (suc j) (if b then instr-room (stretch E t) ∷ checks E t else checks E t))
    k-after E true  t zero    k a ih refl = sym (till-checks E t a)
    k-after E true  t (suc j) k a ih f = ih j f
    k-after E false t j       k a ih f = ih j f

  -- EVERY CHECK OF `checks E t` HOLDS THE MEASURE OF WHAT FOLLOWS IT
  checks-k : ∀ (E : ℕ) (t : AbstractTrace) → NoRoom t → ∀ (j k : ℕ)
           → fetch (checks E t) j ≡ just (instr-room k) → k ≡ till-check E (drop (suc j) (checks E t))
  checks-k E (x ∷ t) (nr ∷ a) zero    k f = ⊥-elim (room≢ nr (just-injective f))
  checks-k E (x ∷ t) (nr ∷ a) (suc j) k f =
    k-after E (boundary? x) t j k a (λ j′ f′ → checks-k E t a j′ k f′) f

  -- …and so does every check of the pass's output
  check-k : ∀ (t : AbstractTrace) → NoRoom t → ∀ (pc k : ℕ)
          → fetch (room-checks t) pc ≡ just (instr-room k) → k ≡ till-check (max-entry t) (drop (suc pc) (room-checks t))
  check-k t a zero    k refl = sym (till-checks (max-entry t) t a)
  check-k t a (suc pc) k f = checks-k (max-entry t) t a pc k f

  -- what an ordinary instruction's measure is: its own spend, then its successor's
  drop-fetch : ∀ (P : AbstractTrace) (pc : ℕ) {i : AbstractInstr} → fetch P pc ≡ just i
             → drop pc P ≡ i ∷ drop (suc pc) P
  drop-fetch (x ∷ P) zero    refl = refl
  drop-fetch (x ∷ P) (suc pc) f   = drop-fetch P pc f

  till-step : ∀ (E : ℕ) (P : AbstractTrace) (pc : ℕ) {i : AbstractInstr} → fetch P pc ≡ just i → room? i ≡ false
            → till-check E (drop pc P) ≡ spend E i + till-check E (drop (suc pc) P)
  till-step E P pc {i} f nr rewrite drop-fetch P pc f | nr = refl

  -- …and at a check it is nothing
  till-room : ∀ (E : ℕ) (P : AbstractTrace) (pc k : ℕ) → fetch P pc ≡ just (instr-room k)
            → till-check E (drop pc P) ≡ 0
  till-room E P pc k f rewrite drop-fetch P pc f = refl

------------------------------------------------------------------------
-- A PROGRAM IMAGE HAS NO CHECKS OF ITS OWN: every image instruction is
-- `ImageI` (`ProgramImageFacts.image-frame-free`), and a check is not (D377:
-- the pass adds them after the image).
------------------------------------------------------------------------
open import Once.CCC.Machine.FrameFree using (ImageI)
open import Once.CCC.Machine.SMCore
  using ( mov-to-output; mov-to-input; load-indirect; load-indirect-suc; load-from-slot; store-at-slot
        ; store-indirect; store-indirect-suc; lea-slot; restore-input; instr-alloc-stack; instr-dealloc-stack
        ; instr-reclaim-to; instr-push-frame; instr-pop-frame; instr-call-closure; worklist-init
        ; worklist-push; worklist-pop; worklist-check; instr-sigop; instr-load-const; instr-load-code-addr
        ; instr-save-closure-reg; instr-load-tag-lit; instr-alloc-heap; instr-reg-op; instr-ctrl; instr-free-heap
        ; load-at; store-at; addr-at )

imageI-noroom : ∀ (i : AbstractInstr) → ImageI i → room? i ≡ false
imageI-noroom mov-to-output            _ = refl
imageI-noroom mov-to-input             _ = refl
imageI-noroom load-indirect            _ = refl
imageI-noroom load-indirect-suc        _ = refl
imageI-noroom (load-from-slot _)       _ = refl
imageI-noroom (store-at-slot _)        _ = refl
imageI-noroom store-indirect           _ = refl
imageI-noroom store-indirect-suc       _ = refl
imageI-noroom (lea-slot _)             _ = refl
imageI-noroom (restore-input _)        _ = refl
imageI-noroom (instr-alloc-stack _)    _ = refl
imageI-noroom (instr-dealloc-stack _)  _ = refl
imageI-noroom (instr-reclaim-to _)     _ = refl
imageI-noroom (instr-push-frame _)     _ = refl
imageI-noroom instr-pop-frame          _ = refl
imageI-noroom instr-call-closure       _ = refl
imageI-noroom (worklist-init _)        _ = refl
imageI-noroom (worklist-push _)        _ = refl
imageI-noroom (worklist-pop _)         _ = refl
imageI-noroom (worklist-check _)       _ = refl
imageI-noroom (instr-sigop _)          _ = refl
imageI-noroom (instr-load-const _ _)   _ = refl
imageI-noroom (instr-load-code-addr _) _ = refl
imageI-noroom instr-save-closure-reg   _ = refl
imageI-noroom (instr-load-tag-lit _)   _ = refl
imageI-noroom (instr-alloc-heap _)     _ = refl
imageI-noroom (instr-reg-op _)         _ = refl
imageI-noroom (instr-ctrl _)           _ = refl
imageI-noroom (instr-free-heap _)      _ = refl
imageI-noroom (load-at _)      _ = refl
imageI-noroom (store-at _)      _ = refl
imageI-noroom (addr-at _)      _ = refl
imageI-noroom (instr-room _)           ()

image-noroom : ∀ (t : AbstractTrace) → All ImageI t → NoRoom t
image-noroom []      []       = []
image-noroom (i ∷ t) (p ∷ a) = imageI-noroom i p ∷ image-noroom t a

------------------------------------------------------------------------
-- THE BUDGET'S LANDINGS (plan 0.123 A.4 step 5). Control that arrives other
-- than by falling through lands ON a boundary instruction (a jump on its label,
-- a call on its entry) or one past one (a return, past its call) — and the pass
-- puts a check right after every boundary instruction. So the measure at a
-- landing is the boundary's own spend, and one past it, 0.
------------------------------------------------------------------------
module NeedFacts {FS : FrameSemantics} where
  open FlatMachine {FS} using (fetch)
  open import Data.Product using (Σ; _,_)
  open import Data.Nat using (_≤_; _⊔_)
  open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
  open import Once.CCC.Machine.SMCore using (instr-ctrl; c-entry; EntryId)
  open import Once.CCC.Codegen.RoomChecks using (entry-frame)

  private
    next-in : ∀ (E : ℕ) (b : Bool) (t : AbstractTrace) (j : ℕ) {i : AbstractInstr}
            → (∀ (j′ : ℕ) {i′ : AbstractInstr} → fetch (checks E t) j′ ≡ just i′ → boundary? i′ ≡ true
               → Σ ℕ (λ k → fetch (checks E t) (suc j′) ≡ just (instr-room k)))
            → fetch (if b then instr-room (stretch E t) ∷ checks E t else checks E t) j ≡ just i
            → boundary? i ≡ true
            → Σ ℕ (λ k → fetch (if b then instr-room (stretch E t) ∷ checks E t else checks E t) (suc j)
                           ≡ just (instr-room k))
    next-in E true  t zero    ih refl ()
    next-in E true  t (suc j) ih f    bd = ih j f bd
    next-in E false t j       ih f    bd = ih j f bd

  checks-next : ∀ (E : ℕ) (t : AbstractTrace) (j : ℕ) {i : AbstractInstr}
              → fetch (checks E t) j ≡ just i → boundary? i ≡ true
              → Σ ℕ (λ k → fetch (checks E t) (suc j) ≡ just (instr-room k))
  checks-next E (x ∷ t) zero    refl bd rewrite bd = stretch E t , refl
  checks-next E (x ∷ t) (suc j) f    bd =
    next-in E (boundary? x) t j (λ j′ f′ bd′ → checks-next E t j′ f′ bd′) f bd

  -- RIGHT AFTER EVERY BOUNDARY INSTRUCTION OF THE PASS'S OUTPUT, A CHECK
  boundary-next : ∀ (t : AbstractTrace) (j : ℕ) {i : AbstractInstr}
                → fetch (room-checks t) j ≡ just i → boundary? i ≡ true
                → Σ ℕ (λ k → fetch (room-checks t) (suc j) ≡ just (instr-room k))
  boundary-next t zero    refl ()
  boundary-next t (suc j) f    bd = checks-next (max-entry t) t j f bd

  -- an entry reserves at most the largest frame (what a call's spend covers)
  entry-le : ∀ (P : AbstractTrace) (j : ℕ) (m : EntryId) (b : ℕ)
           → fetch P j ≡ just (instr-ctrl (c-entry m b)) → b ≤ max-entry P
  entry-le (x ∷ P) zero    m b refl = m≤m⊔n b (max-entry P)
  entry-le (x ∷ P) (suc j) m b f    = ≤-trans (entry-le P j m b f) (m≤n⊔m (entry-frame x) (max-entry P))

  -- a call is a boundary instruction (the pass checks past every one)
  open import Once.CCC.Machine.SMCore using (CallI; c-label; c-jmp; c-branch-tag-zero; c-ret; c-call-fn; c-start; c-leave)
  call-boundary : ∀ (c : AbstractInstr) → CallI c → boundary? c ≡ true
  call-boundary instr-call-closure                 _  = refl
  call-boundary (instr-ctrl (c-call-fn _))         _  = refl
  call-boundary (instr-ctrl (c-label _))           ()
  call-boundary (instr-ctrl (c-jmp _))             ()
  call-boundary (instr-ctrl (c-branch-tag-zero _)) ()
  call-boundary (instr-ctrl (c-entry _ _))         ()
  call-boundary (instr-ctrl (c-ret _))             ()
  call-boundary (instr-ctrl (c-start _))           ()
  call-boundary (instr-ctrl c-leave)               ()
  call-boundary mov-to-output            ()
  call-boundary mov-to-input             ()
  call-boundary load-indirect            ()
  call-boundary load-indirect-suc        ()
  call-boundary (load-from-slot _)       ()
  call-boundary (store-at-slot _)        ()
  call-boundary store-indirect           ()
  call-boundary store-indirect-suc       ()
  call-boundary (lea-slot _)             ()
  call-boundary (restore-input _)        ()
  call-boundary (instr-alloc-stack _)    ()
  call-boundary (instr-dealloc-stack _)  ()
  call-boundary (instr-reclaim-to _)     ()
  call-boundary (instr-push-frame _)     ()
  call-boundary instr-pop-frame          ()
  call-boundary (worklist-init _)        ()
  call-boundary (worklist-push _)        ()
  call-boundary (worklist-pop _)         ()
  call-boundary (worklist-check _)       ()
  call-boundary (instr-sigop _)          ()
  call-boundary (instr-load-const _ _)   ()
  call-boundary (instr-load-code-addr _) ()
  call-boundary instr-save-closure-reg   ()
  call-boundary (instr-load-tag-lit _)   ()
  call-boundary (instr-alloc-heap _)     ()
  call-boundary (instr-reg-op _)         ()
  call-boundary (instr-free-heap _)      ()
  call-boundary (load-at _)      ()
  call-boundary (store-at _)      ()
  call-boundary (addr-at _)      ()
  call-boundary (instr-room _)           ()
