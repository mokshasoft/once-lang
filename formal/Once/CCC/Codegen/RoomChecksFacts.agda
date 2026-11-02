-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.RoomChecksFacts — where the room-check pass puts things.
--
-- Plan 0.123 A.4 step 5 (D371). The pass (`RoomChecks.room-checks`) only ever
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
