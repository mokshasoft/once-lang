------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `sz` OVER THE KNOT.
--
--     szsTm i t = ielim KnotD i szsMethsK t          -- ∷ Nat
--
-- ⚠⚠ `Knot/Sz` USED TO BE ~800 GENERATED LINES: 53 methods, 53 method
--   ⊢ty's, 53 tuple rungs.  It is now an INSTANTIATION, because
--   `Lib/ISz` computes all of them from the description.  See that
--   module's header for why the enumerated version could not be made
--   fast and this one is not slow.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SzS where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; Nat; Σ'; ielim )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ty-Nat; ⊢ielim; imethsTy )
open import DirectedHoTT.Lib.ISzSort using ( szsMeths; ⊢szsMeths )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )

szsMethsK : {Γ : Cx} → RTm Γ
szsMethsK = szsMeths KnotD

⊢szsMethsK : {Γ : Ctx} → Γ ⊢ szsMethsK ∷ imethsTy KnotD IPair Nat KnotD
⊢szsMethsK = ⊢szsMeths KnotD IPair zero KnotD KnotWf KnotWf ⊢IPair

-- ★★★ `sz` OVER THE WHOLE KNOT.
szsTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
szsTm i t = ielim KnotD i szsMethsK t

⊢szsTm : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
        Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ szsTm i t ∷ Nat
⊢szsTm di dt = ⊢ielim KnotWf ty-Nat di ⊢szsMethsK dt
