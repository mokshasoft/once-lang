------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ SPIKE: CAN AN `ielim` PRODUCE AN ELEMENT OF
-- ITS OWN FAMILY AT A **SHIFTED INDEX**?
--
-- HANDOFF-2026-08-26 step A, second half — the gate on the judgement
-- layer.  `_∋_∷_`'s `here` is
--
--     here : (Γ ▹ A) ∋ vz ∷ renTy vs A
--
-- so its index mentions `renTy`, a FUNCTION of an encoded term.  For the
-- judgement to be describable, weakening must EXIST object-level: an
-- `ielim` returning a KNOT ELEMENT at a different index.  `Lib/IFold`
-- does not reach it — that folds into a CONSTANT `Nat` motive, and this
-- needs a motive that MOVES THE INDEX.
--
-- ★ THE SMALLEST THING WITH BOTH FEATURES is `wkFin : Fin n → Fin (suc n)`
--   over `Examples/Scoped`'s `Fin`: two constructors, and
--
--     M(i, t) = Fin (suc ⟨i⟩)
--
--   is a motive that mentions the INDEX slot and lands in the family
--   being eliminated.
--
-- ⚠ AND THE SECOND CONSTRUCTOR IS WHERE IT SHOULD BITE.  `fsuc`'s index
--   is known only through a FORDING CONSTRAINT — `⟨i⟩ ≡ suc m` is an
--   `Id`, PROPOSITIONAL — so using the IH at the index the answer needs
--   is a TRANSPORT, not a conversion.  Fording made the description
--   cheap (§3); this is where that debt is called in.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.WkFin where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; U; El; Σ'; Unit; Nat; IMu
        ; RTm; var; lam; pair; fst; snd; unit; nzero; nsuc
        ; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; idrefl; icon; ielim; isingle
        ; ICon; IDesc; hereID; thereID; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢pair; ⊢fst; ⊢snd; ⊢unit
        ; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢idrefl; ⊢icon; ⊢lam
        ; _⊢ty_; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-IMu
        ; imethTy; IDescWf
        ; _≅ᵀ_; csymᵀ; credᵀ; El-⌜Id⌝ )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢-cast; isingle-Sub⊢; iihTy-wf )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf )
open import DirectedHoTT.Examples.Scoped
  using ( INat; FinD; FinWf; Fin; fzeroC; fsucC; fzeroWf; fsucWf; toI; fromI )

------------------------------------------------------------------------
-- 1. ★★★ THE MOTIVE THAT MOVES THE INDEX.
--
--     M(i, t) = Fin (suc i)
--
-- Every motive in the development so far has been CONSTANT (`Nat`) or a
-- `Π` into a constant.  This one lands in the family being eliminated,
-- at an index one greater than the scrutinee's.
------------------------------------------------------------------------

-- ⚠ CONTEXT-GENERIC: a method's motive lives at the METHOD's ambient,
--   not at `ε`.
wkMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
wkMot = IMu FinD INat (nsuc (var (vs vz)))

⊢wkMot : {Γ : Ctx} → ((Γ ▹ εwkTy INat) ▹ IMu FinD INat (var vz)) ⊢ty wkMot
⊢wkMot = ty-IMu FinWf (toI (⊢nsuc (fromI (⊢var (there here)))))

------------------------------------------------------------------------
-- 2. ⬜ THE METHODS — **NOT DONE**, and the state is recorded rather
--    than papered over.
--
-- `wkFzero`'s body was written and does not elaborate: `ipayTy-wf` /
-- `iihTy-wf` applied at `Scoped`'s `fzeroWf` leave an unsolved
--
--     subTm εsub _t  =  ⌜Nat⌝            (blocked on _t)
--
-- i.e. `icw-clo`'s closed code cannot be recovered — `εwkTm` is a DEFINED
-- function and so not injective, the third sighting of
-- `pin-implicits-on-defined-set-types` in this development.  Pinning the
-- two telescope implicits (`{Θ = ◇ ▹ INat}`) did NOT clear it, so the
-- cause is not yet understood.
--
-- ⚠ WHAT THIS DOES AND DOES NOT SAY.  It is an ELABORATION failure, not a
--   refutation: nothing here shows an index-shifting `ielim` is
--   impossible, and §1 shows its MOTIVE is fine.  ⇒ feasibility of
--   object-level weakening is **still open**, and the honest reading is
--   that the spike is unfinished, not that the answer is no.
--
-- ★ AND THE HARDER HALF IS STILL UNTOUCHED.  Even with `fzero` working,
--   `fsuc`'s index is known only through a FORDING CONSTRAINT — `⟨i⟩ ≡
--   suc m` is an `Id`, PROPOSITIONAL — so using the IH at the index the
--   answer needs is a TRANSPORT (`jsub` at a `⌜IMu⌝` motive), not a
--   conversion.  Fording bought a cheap description in §3; this is where
--   that debt is called in, and it is the part that decides the cost.
------------------------------------------------------------------------
