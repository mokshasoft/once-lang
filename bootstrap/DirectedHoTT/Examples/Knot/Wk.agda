------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ OBJECT-LEVEL WEAKENING OVER THE WHOLE KNOT.
--
--     wkK : K i → K (sh i)          i.e.  K (s, d) → K (s, suc d)
--
-- `PLAN-JUDGEMENT` step 2's first item, and the first FUNCTION OVER
-- SYNTAX the encoded knot has — everything before it was a MEASURE
-- (`Knot/Sz`) or a constructor.
--
-- ★★ 51 OF THE 53 METHODS ARE COMPUTED, 2 ARE GIVEN.  `Lib/IWk` derives
--   the method for every row whose fields ride the ambient depth or are
--   pinned at a closed index; the two DEPTH-FORDED `Var` rows are the
--   tail, hand-written in `Knot/WkRows` §5/§7 because their κ constrains
--   `snd ⟨i⟩` and so needs the witness re-proved under `nsuc`.
--
--   ⚠ That is the same split `Knot/Ctors` (51 generated) and
--     `Knot/Build` (2 hand-written) already use, for the same reason.
--
-- ⚠ AND NOTHING HERE ENUMERATES A ROW.  The classification, the leftover
--   description, its well-formedness and its position all come from ONE
--   recursion each over `decDesc KnotD` — `wkdRest`, `wfDrop`, `splDrop`.
--   `Knot/Tags` pays O(n²) to enumerate memberships; `Split` derives each
--   on the way past.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Wk where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; RTy; RTm; Nat; Σ'; IMu; pair; unit
        ; ielim; renTm; subTm; renTy; εwkTy; εwk-ren; IDesc; ICon; _◂_ )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; wk-single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢pair; ⊢unit
        ; IDescWfFrom; idwf-cons
        ; ty-IMu; imethsTy; imethsTyFrom; ⊢ielim )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast; ren-ty )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Lib.IWk
  using ( sh; Mot; decDesc; iwkMeths; ⊢iwkMethsFrom; wkdRest
        ; wfDrop; Split; spl-nil; imethsTyFromMot-wf )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import Agda.Builtin.Nat using ( suc )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz; tagVar-vs )
open import DirectedHoTT.Examples.Knot.WkProbe using ( ⊢shIPair )
open import DirectedHoTT.Examples.Knot.WkRows
  using ( wkVarVz; ⊢wkVarVz; wkVarVs; ⊢wkVarVs )

------------------------------------------------------------------------
-- 1. THE TAIL — the two rows `Lib/IWk` declines to classify.
--
-- ⚠ ITS TYPE IS COMPUTED, NOT WRITTEN.  `wkdRest (decDesc KnotD)` IS
--   `cVar-vz ◂ cVar-vs ◂ inil` (pinned by `Knot/WkProbe` §4) and
--   `wfDrop` peels the matching `IDescWfFrom`.  Nothing below names a
--   row number.
------------------------------------------------------------------------

-- ⚠ ONE STEP OF THE LEFTOVER'S WELL-FORMEDNESS.  `IDescWfFrom` is a
--   datatype, so its tail is reached by MATCHING, not projection — and
--   the two `⊢pair`s below each need one step further in.
wfStep : {D : IDesc} {I : RTy ε} {C : ICon (ε ∙)} {E : IDesc} →
         IDescWfFrom D I (C ◂ E) → IDescWfFrom D I E
wfStep (idwf-cons _ wE) = wE

wkTail : {Γ : Cx} → RTm Γ
wkTail = pair wkVarVz (pair wkVarVs unit)

⊢wkTail : {Γ : Ctx} →
          Γ ⊢ wkTail ∷ imethsTyFrom KnotD IPair (Mot KnotD IPair)
                         tagVar-vz (wkdRest (decDesc KnotD))
⊢wkTail =
  ⊢pair (ren-ty (imethsTyFromMot-wf KnotD IPair tagVar-vs _ KnotWf
                   (wfStep (wfDrop KnotWf (decDesc KnotD)))
                   ⊢IPair ⊢shIPair)
                there)
        ⊢wkVarVz
        (⊢-cast (sym (wk-singleTy {v = wkVarVz} _))
          (⊢pair (ren-ty (imethsTyFromMot-wf KnotD IPair (suc tagVar-vs) _ KnotWf
                            (wfStep (wfStep (wfDrop KnotWf (decDesc KnotD))))
                            ⊢IPair ⊢shIPair)
                         there)
                 ⊢wkVarVs
                 (⊢-cast (sym (wk-singleTy {v = wkVarVs} _)) ⊢unit)))

------------------------------------------------------------------------
-- 2. ★★★ THE METHOD TUPLE, AND `wkK`.
------------------------------------------------------------------------

wkMethsK : {Γ : Cx} → RTm Γ
wkMethsK = iwkMeths (decDesc KnotD) wkTail

⊢wkMethsK : {Γ : Ctx} →
            Γ ⊢ wkMethsK ∷ imethsTy KnotD IPair (Mot KnotD IPair) KnotD
⊢wkMethsK =
  ⊢iwkMethsFrom KnotD IPair (decDesc KnotD) spl-nil KnotWf KnotWf
                ⊢IPair ⊢shIPair wkTail ⊢wkTail

⊢MotK : {Γ : Ctx} →
        ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty Mot KnotD IPair
⊢MotK = ty-IMu KnotWf
          (⊢shIPair (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                   (εwk-ren vs IPair))
                            (⊢var (there here))))

-- ★★★ OBJECT-LEVEL WEAKENING FOR THE KNOT.
wkK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkK i t = ielim KnotD i wkMethsK t

⊢wkK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
       Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ wkK i t ∷ K (sh i)
⊢wkK {i = i} di dt =
  ⊢-cast (cong (λ z → K (sh z)) (wk-single i))
         (⊢ielim KnotWf ⊢MotK di ⊢wkMethsK dt)
