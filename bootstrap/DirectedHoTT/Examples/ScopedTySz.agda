------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — PROBE 2: THE FOLD, over a TYPE index.
--
-- `Examples/ScopedSz` applies `Lib/ISz`'s generic fold to `Scoped`'s
-- three-constructor syntax, and its header states the claim this file
-- tests:
--
--   > `szMeths : IDesc → RTm Γ` is generic in the description AND in
--   > the INDEX TYPE … whose index is `El ⌜Nat⌝` and NOT A PAIR.
--
-- ★ THIS FILE IS THE SAME LIBRARY AT `Examples/ScopedTy`, whose index
--   IS a pair — a CONTEXT and a TYPE, each an encoded datatype.
--
-- ⚠ THE QUESTION.  `KNOT-LESSONS` §2.1 says the Knot's pain is index
--   BOOKKEEPING inside folds: eight tower rungs, eight `natⁿ`
--   instances, `⟶*-wkTyKᵈ`'s four descents — all because a binder is
--   `+1` and the fold must count.  If a fold over a STRUCTURAL index
--   needs none of that, the bookkeeping was an artefact of the index
--   being a number, and §2.1's mechanism is confirmed.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.ScopedTySz where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; Nat; El; ielim )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ty-El; ty-Nat
        ; ⊢ielim; imethsTy )
open import DirectedHoTT.Lib.IPay using ( spl-nil )
open import DirectedHoTT.Lib.ISz using ( szMeths; ⊢szMeths )
open import DirectedHoTT.Examples.ScopedTy using ( TmD; TmWf; I; Tm; ⌜I⌝; ⊢⌜I⌝ )

szMethsTmTy : {Γ : Cx} → RTm Γ
szMethsTmTy = szMeths TmD

⊢szMethsTmTy : {Γ : Ctx} → Γ ⊢ szMethsTmTy ∷ imethsTy TmD I Nat TmD
⊢szMethsTmTy = ⊢szMeths TmD I zero TmD TmWf TmWf spl-nil (ty-El ⊢⌜I⌝)

-- ★ `size` for the TYPE-INDEXED λ-calculus, from the SAME library that
--   does the 53-constructor knot and the depth-indexed twin.
szTmTy : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
szTmTy i t = ielim TmD i szMethsTmTy t

⊢szTmTy : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
          Γ ⊢ i ∷ El ⌜I⌝ → Γ ⊢ t ∷ Tm i → Γ ⊢ szTmTy i t ∷ Nat
⊢szTmTy di dt = ⊢ielim TmWf ty-Nat di ⊢szMethsTmTy dt
