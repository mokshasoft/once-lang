------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ A FOLD OVER AN INDEXED DESCRIPTION, at a
-- CONSTANT `Nat` motive, parametric in the ALGEBRA.
--
--     ifMeths D  :  the method tuple for `ielim D _ ifMeths _ ∷ Nat`
--
-- `Lib/ISz` is now this module at `z = 0`, `op = +`, `nd = suc`;
-- `Lib/IDepth` is it at `op = max`.
--
-- ⚠ THE MOTIVE STAYS `Nat`, deliberately.  An abstract constant motive
--   `A` would need `subTy σ A ≡ A` threaded as a parameter, where `Nat`
--   is stable DEFINITIONALLY.  Generalise the motive when something wants
--   a non-`Nat` fold, not before.
--
-- ★★ NOTHING HERE IS PER-CONSTRUCTOR.  The method is COMPUTED from the
--   `ICon` and the tuple from the `IDesc`, both by ONE induction with the
--   description a VARIABLE.  See `tools/gen-knot.py`'s step-3 note for the
--   measurement that forced this shape (enumerated 147s → computed 5s) and
--   for the two ways of half-doing it that are WORSE than either.
--
-- ⚠ NO TRAILING `op _ z`, and it is not cosmetic.  A constructor with `r`
--   recursive fields folds to `op xᵣ (… (op x₂ x₁))`, and one with a
--   SINGLE field folds to `x₁` itself rather than `op x₁ z`.  `plusTm a b`
--   recurses on `a`, so a trailing `+ 0` would cost `x₁` REDUCTION steps
--   at every node — which on a unary-recursive syntax (`lam`, `nsuc`, …)
--   turns an O(n) measure into O(n²).  This is the one place where the
--   object-level complexity of a generic fold can differ from the
--   hand-written measure it replaces, so it is worth stating.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IFold where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; RTy; RTm; Unit; Σ'; El; IMu; Nat; Π
        ; lam; pair; fst; snd; unit; nzero; nsuc
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; ipayTy; Sub; extS; subTm; subTy; renTy; isingle; iext
        ; sel; ilookupD; _∈ID_; hereID; thereID; ⌜Id⌝; Var
        ; εwkTy; εwk-ren; ipayTy-ren; ipayTy-cong )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢lam; ⊢pair; ⊢fst; ⊢snd; ⊢unit
        ; _⊢ty_; ty-Unit; ty-Σ; ty-Nat
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTyFrom; iihTy
        ; _⟶_; _⟶*_; done; step; βfst; βsnd; ξ-fst; ξ-snd )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; ren-ty; isingle-Sub⊢; iihTy-wf; iihTy-ren; iihTy-cong )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf; imethsTyFromNat-wf )

------------------------------------------------------------------------
-- ★ THE ALGEBRA.  `z` for a constructor with NO recursive fields, `op` to
--   absorb one child into the accumulator, `nd` to wrap the whole node.
--   ⚠ All three must be CONTEXT-POLYMORPHIC: they are used under the
--   method's three binders, at a depth the caller never names.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ⬜ SPIKE — CAN A FIELD BE CLASSIFIED SAME-SORT vs CROSS-SORT?
--
-- The `sz` agreement `szTm ⌈t⌉ ⟶* ⌜ sz t ⌝` fails because the meta-level
-- `szb` folds over `RTm` ALONE — the other sorts are separate Agda types
-- and it treats them as ATOMS — while this fold traverses all seven at
-- once.  ⚠ Measured 28/28: `szb`'s count is exactly the number of
-- SAME-SORT `iρ` fields, so the gap is precisely the CROSS-SORT ones.
--
-- ⇒ the question this section answers: is "same sort as the row" a
--   DECISION computable from the raw `ICon`, or does it need per-row data
--   (which would be the enumeration `Lib/IWk` exists to avoid)?
------------------------------------------------------------------------

data Maybeℕ : Set where
  noℕ   : Maybeℕ
  someℕ : ℕ → Maybeℕ

-- ★ THE MOVE THAT SIDESTEPS THE CONTEXT MISMATCH.  A field's sort lives
--   at depth `j` and the row's tag ford at depth `k`, so the two sort
--   literals inhabit DIFFERENT `RTm Δ`s and cannot be compared directly.
--   Both are closed numerals, so read their VALUES instead and compare
--   in `ℕ` — context-free, and no `RTm` equality is needed at all.
numVal : {Δ : Cx} → RTm Δ → Maybeℕ
numVal nzero    = someℕ zero
numVal (nsuc t) with numVal t
... | someℕ n = someℕ (suc n)
... | noℕ     = noℕ
numVal _        = noℕ

eqℕ : ℕ → ℕ → 𝔹
eqℕ zero    zero    = true
eqℕ (suc a) (suc b) = eqℕ a b
eqℕ _       _       = false

-- ★ the row's OWN sort, read off its tag ford.  ⚠ A SCAN, not per-row
--   data: the ford is `⌜Id⌝ c (fst ⟨i⟩) s`, the shape `Lib/IWk.decKa`
--   already recognises, and `s` is the row's sort literal.
rowSort : {Δ : Cx} → ICon Δ → Maybeℕ
rowSort iι                              = noℕ
rowSort (iρ j C)                        = rowSort C
rowSort (iκ (⌜Id⌝ c (fst (var a)) s) C) with numVal s
... | someℕ n = someℕ n
... | noℕ     = rowSort C
rowSort (iκ κ C)                        = rowSort C

-- …and a field's sort, from its `pair s d` index.
fieldSort : {Δ : Cx} → RTm Δ → Maybeℕ
fieldSort (pair s d) = numVal s
fieldSort _          = noℕ

-- the predicate, against an ALREADY-READ row sort.  ⚠ `Maybeℕ` is
-- context-free, so it threads through the telescope unchanged — which is
-- the whole reason the sorts were turned into `ℕ`s.
sameSortAt : {Δ : Cx} → Maybeℕ → RTm Δ → 𝔹
sameSortAt noℕ       j = false
sameSortAt (someℕ r) j with fieldSort j
... | someℕ f = eqℕ r f
... | noℕ     = false

-- ★★ HOW MANY CHILDREN A SAME-SORT MEASURE WOULD COUNT.
countSameAt : {Δ : Cx} → Maybeℕ → ICon Δ → ℕ
countSameAt r iι       = zero
countSameAt r (iκ κ C) = countSameAt r C
countSameAt r (iρ j C) with sameSortAt r j
... | true  = suc (countSameAt r C)
... | false = countSameAt r C

countSame : {Δ : Cx} → ICon Δ → ℕ
countSame C = countSameAt (rowSort C) C

module Fold
  ------------------------------------------------------------------------
  -- ★★★ WHICH RECURSIVE FIELDS THE FOLD COUNTS.
  --
  -- ⚠ WHY THIS IS A PARAMETER AND NOT A FIXED CHOICE.  The knot's seven
  --   sorts are ONE `IMu`, so a fold over it descends into all of them.
  --   `Metatheory/Canonicity`'s `szb`, being a function on `RTm` alone,
  --   treats the other six as ATOMS.  Neither is wrong — they are
  --   different measures — but `szTm ⌈t⌉ ⟶* ⌜ sz t ⌝` needs the encoded
  --   one to be the SAME measure as the meta-level one.
  --
  --   `R` is a per-row summary read off the constructor once; `pick`
  --   then decides each field against it.  ⚠ `R` MUST be context-free:
  --   it is carried down a telescope whose `Cx` grows at every field.
  --
  --   * COUNT EVERY CHILD (`Lib/ISz`, `Lib/IDepth` — unchanged):
  --       R = 𝔹, rsum _ = true, pick b _ = b
  --   * COUNT SAME-SORT CHILDREN ONLY (`Lib/ISzSort`):
  --       R = Maybeℕ, rsum = rowSort, pick = sameSortAt
  ------------------------------------------------------------------------
  (R    : Set)
  (rsum : {Δ : Cx} → ICon Δ → R)
  (pick : {Δ : Cx} → R → RTm Δ → 𝔹)
  (z   : {Γ : Cx} → RTm Γ)
  (op  : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ)
  (nd  : {Γ : Cx} → RTm Γ → RTm Γ)
  (⊢z  : {Γ : Ctx} → Γ ⊢ z ∷ Nat)
  (⊢op : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ op a b ∷ Nat)
  (⊢nd : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ Nat → Γ ⊢ nd a ∷ Nat)
  where

  -- ⚠ THE BOOLEAN IS CONSUMED HERE, BY A SEPARATE FUNCTION, NOT BY A
  --   `with` INSIDE `ifTail`.  A `with` would generate an auxiliary
  --   whose clauses `⊢ifTail` cannot see through, so every proof step
  --   would need its own `with` and the two abstractions would not line
  --   up.  Split out, `ifStep b` and `⊢ifStep b` are applied to the SAME
  --   `b`, and both reduce as soon as it does.
  ifStep : {Γ : Cx} → 𝔹 → RTm Γ → RTm Γ → RTm Γ
  ifStep true  h acc = op h acc
  ifStep false h acc = acc

  -- the accumulator pass: `acc` already holds at least one counted child.
  -- ⚠ A SKIPPED FIELD STILL STEPS THE TUPLE.  `ih` has a component for
  --   every `iρ`, counted or not — dropping the `snd` would silently
  --   read the next field's IH as this one's.
  ifTail : {Γ Δ : Cx} → R → ICon Δ → RTm Γ → RTm Γ → RTm Γ
  ifTail r iι       acc ih = acc
  ifTail r (iρ j C) acc ih = ifTail r C (ifStep (pick r j) (fst ih) acc) (snd ih)
  ifTail r (iκ κ C) acc ih = ifTail r C acc ih

  -- ★ the first COUNTED field seeds the accumulator, which is what
  --   removes the trailing `op _ z`.  With a `pick` that rejects, the
  --   search for that first field has to skip past fields — hence the
  --   mutual pair rather than one clause.
  ifSum     : {Γ Δ : Cx} → R → ICon Δ → RTm Γ → RTm Γ
  ifSumStep : {Γ Δ : Cx} → 𝔹 → R → ICon Δ → RTm Γ → RTm Γ

  ifSum r iι       ih = z
  ifSum r (iρ j C) ih = ifSumStep (pick r j) r C ih
  ifSum r (iκ κ C) ih = ifSum r C ih

  ifSumStep true  r C ih = ifTail r C (fst ih) (snd ih)
  ifSumStep false r C ih = ifSum r C (snd ih)

  -- ⚠ THE TELESCOPE IS A `Cx`, NOT A `Ctx`.  Indexed by a `Ctx Θ` the
  --   recursion cannot solve its own implicit: only `⌊ Θ ⌋` occurs, `⌊_⌋`
  --   is not injective, and `⌊ Θ ⌋ ∙ = ⌊ Θ' ⌋` does not determine `Θ'`.
  ⊢ifStep : {Γ : Ctx} (b : 𝔹) {h acc : RTm ⌊ Γ ⌋} →
            Γ ⊢ h ∷ Nat → Γ ⊢ acc ∷ Nat → Γ ⊢ ifStep b h acc ∷ Nat
  ⊢ifStep true  dh da = ⊢op dh da
  ⊢ifStep false dh da = da

  ⊢ifTail : {Γ : Ctx} {Δ : Cx} (D : IDesc) (I : RTy ε) (σ : Sub Δ ⌊ Γ ⌋)
            (r : R) (C : ICon Δ) (q acc ih : RTm ⌊ Γ ⌋) →
            Γ ⊢ acc ∷ Nat → Γ ⊢ ih ∷ iihTy D I σ C q Nat →
            Γ ⊢ ifTail r C acc ih ∷ Nat
  ⊢ifTail D I σ r iι       q acc ih da d = da
  ⊢ifTail D I σ r (iρ j C) q acc ih da d =
    ⊢ifTail D I (iext σ (fst q)) r C (snd q)
            (ifStep (pick r j) (fst ih) acc) (snd ih)
            (⊢ifStep (pick r j) (⊢fst d) da)
            (⊢-cast (wk-singleTy {v = fst ih}
                                 (iihTy D I (iext σ (fst q)) C (snd q) Nat))
                    (⊢snd d))
  ⊢ifTail D I σ r (iκ κ C) q acc ih da d =
    ⊢ifTail D I (iext σ (fst q)) r C (snd q) acc ih da d

  ⊢ifSum : {Γ : Ctx} {Δ : Cx} (D : IDesc) (I : RTy ε) (σ : Sub Δ ⌊ Γ ⌋)
           (r : R) (C : ICon Δ) (q ih : RTm ⌊ Γ ⌋) →
           Γ ⊢ ih ∷ iihTy D I σ C q Nat → Γ ⊢ ifSum r C ih ∷ Nat

  -- ⚠ `b` FIRST, and matched on FIRST: it is the argument that decides
  --   which clause of `ifSumStep` the goal reduces to.
  ⊢ifSumStep : {Γ : Ctx} {Δ : Cx} (b : 𝔹) (D : IDesc) (I : RTy ε)
               (σ : Sub Δ ⌊ Γ ⌋) (r : R) (j : RTm Δ) (C : ICon (Δ ∙))
               (q ih : RTm ⌊ Γ ⌋) →
               Γ ⊢ ih ∷ iihTy D I σ (iρ j C) q Nat →
               Γ ⊢ ifSumStep b r C ih ∷ Nat

  ⊢ifSum D I σ r iι       q ih d = ⊢z
  ⊢ifSum D I σ r (iρ j C) q ih d = ⊢ifSumStep (pick r j) D I σ r j C q ih d
  ⊢ifSum D I σ r (iκ κ C) q ih d =
    ⊢ifSum D I (iext σ (fst q)) r C (snd q) ih d

  ⊢ifSumStep true  D I σ r j C q ih d =
    ⊢ifTail D I (iext σ (fst q)) r C (snd q) (fst ih) (snd ih)
            (⊢fst d)
            (⊢-cast (wk-singleTy {v = fst ih}
                                 (iihTy D I (iext σ (fst q)) C (snd q) Nat))
                    (⊢snd d))
  ⊢ifSumStep false D I σ r j C q ih d =
    -- ⚠ the field is not COUNTED, but its IH slot is still THERE.
    ⊢ifSum D I (iext σ (fst q)) r C (snd q) (snd ih)
           (⊢-cast (wk-singleTy {v = fst ih}
                                (iihTy D I (iext σ (fst q)) C (snd q) Nat))
                   (⊢snd d))

  ------------------------------------------------------------------------
  -- THE METHOD, COMPUTED FROM THE CONSTRUCTOR.
  -- ⚠ CONTEXTS PINNED: `⊢lam`'s body lives one binder deeper, and left
  --   implicit those contexts are metas that never solve.
  ------------------------------------------------------------------------

  ifMethod : {Γ Δ : Cx} → ICon Δ → RTm Γ
  ifMethod C = lam (lam (lam (nd (ifSum (rsum C) C (var vz)))))

  ⊢ifMethod : {Γ : Ctx} (D : IDesc) (I : RTy ε) (k : ℕ) (C : ICon (ε ∙)) →
              IDescWf I D → IConWf D I (◇ ▹ εwkTy I) C →
              ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
              Γ ⊢ ifMethod C ∷ imethTy D I k C Nat
  ⊢ifMethod {Γ = Γ} D I k C wD wC tI =
    ⊢lam tI
      (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy I} D I (isingle (var vz)) C
                       wD wC (isingle-Sub⊢ (⊢-cast (εwk-ren vs I) (⊢var here))))
        (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy I) ▹ ipayTy D I (isingle (var vz)) C}
                        D I Nat (isingle (var (vs vz))) C (var vz) wC
                        (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs I))
                                                     (εwk-ren vs I))
                                              (⊢var (there here)))) ty-Nat
                        (⊢-cast (trans (ipayTy-ren vs D I (isingle (var vz)) C)
                                       (ipayTy-cong D I C (λ { vz → refl ; (vs ()) })))
                                (⊢var here)))
          -- ⚠ the IH-tuple variable, RETYPED: `⊢var here` hands back
          --   `renTy vs (iihTy …)` and the fold is stated one binder out.
          --   `iihTy-ren` moves the renaming inside, `iihTy-cong` then
          --   identifies the two environments — pointwise, not definitionally.
          (⊢nd (⊢ifSum D I (isingle (var (vs (vs vz)))) (rsum C) C (var (vs vz)) (var vz)
                 (⊢-cast (trans (iihTy-ren vs D I (isingle (var (vs vz))) C
                                           (var vz) Nat)
                                (iihTy-cong D I C (var (vs vz)) Nat
                                            (λ { vz → refl ; (vs ()) })))
                         (⊢var here))))))

  ------------------------------------------------------------------------
  -- ★★★ THE TUPLE, COMPUTED FROM THE DESCRIPTION.  ONE induction, and the
  --    description stays a VARIABLE — the condition a generic lemma needs
  --    in order to actually BE generic.
  ------------------------------------------------------------------------

  ifMeths : {Γ : Cx} → IDesc → RTm Γ
  ifMeths inil    = unit
  ifMeths (C ◂ E) = pair (ifMethod C) (ifMeths E)

  ⊢ifMeths : {Γ : Ctx} (D : IDesc) (I : RTy ε) (j : ℕ) (E : IDesc) →
             IDescWf I D → IDescWfFrom D I E →
             ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
             Γ ⊢ ifMeths E ∷ imethsTyFrom D I Nat j E
  ⊢ifMeths D I j inil    wD idwf-nil          tI = ⊢unit
  ⊢ifMeths D I j (C ◂ E) wD (idwf-cons wC wE) tI =
    ⊢pair (ren-ty (imethsTyFromNat-wf D I (suc j) E wD wE tI) there)
          (⊢ifMethod D I j C wD wC tI)
          (⊢-cast (sym (wk-singleTy {v = ifMethod C}
                                    (imethsTyFrom D I Nat (suc j) E)))
                  (⊢ifMeths D I (suc j) E wD wE tI))

  ------------------------------------------------------------------------
  -- ★★★ SELECTING A METHOD OUT OF THE TUPLE, IN **ONE** STEP PER ROW.
  --
  -- ⚠⚠ WHY THIS IS NOT COSMETIC.  `sel k ms` is `fst (sndᵏ ms)`, and
  --   `fst`/`snd` are TERM FORMERS stepping by `βfst`/`βsnd` — not
  --   meta-level projections.  So reaching row `k` of the tuple by hand
  --   costs `k+1` reduction steps, and the `sz` agreement
  --   (`szTm ⌈t⌉ ⟶* ⌜ sz t ⌝`) over 53 rows would be ~1400 selection steps
  --   alone: **O(n²)**, the shape `Knot/Tags` records for `∈ID`.
  --
  -- ★ ONE INDUCTION REMOVES IT.  Each row then costs ONE selection step
  --   plus the fixed tail (three βs for the method's binders, then the IH
  --   projections), so the agreement becomes O(n) chains of constant
  --   length.  ⇒ the 53 rows are bulk of a size worth doing, rather than a
  --   quadratic wall.
  ------------------------------------------------------------------------

  -- a reduction under `sel k`, i.e. under `fst (sndᵏ ⟨-⟩)`
  selCong : {Γ : Cx} (k : ℕ) {ms ms' : RTm Γ} → ms ⟶ ms' → sel k ms ⟶ sel k ms'
  selCong zero    r = ξ-fst r
  selCong (suc k) r = selCong k (ξ-snd r)

  -- ★ …and the selection itself.  ⚠ The `k ∈ID E` premise is what stops it
  --   falling off the end of the list, exactly as on `⊢icon`.
  ifMeths-sel : {Γ : Cx} (E : IDesc) (k : ℕ) → k ∈ID E →
                sel k (ifMeths {Γ = Γ} E) ⟶* ifMethod (ilookupD E k)
  ifMeths-sel (C ◂ E) zero    hereID      = step (βfst _ _) done
  ifMeths-sel (C ◂ E) (suc k) (thereID p) =
    step (selCong k (βsnd _ _)) (ifMeths-sel E k p)
