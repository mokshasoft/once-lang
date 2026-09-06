------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `sz` OVER THE KNOT.
--
--     szTm i t = ielim KnotD i szMethsK t          -- ∷ Nat
--
-- ⚠⚠ THIS FILE USED TO BE ~800 GENERATED LINES: 53 methods, 53 method
--   ⊢ty's, 53 tuple rungs.  It is now an INSTANTIATION, because
--   `Lib/ISz` computes all of them from the description.  See that
--   module's header for why the enumerated version could not be made
--   fast and this one is not slow.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Sz where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; Nat; Σ'; ielim )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ty-Nat; ⊢ielim; imethsTy )
open import DirectedHoTT.Lib.IPay using ( spl-nil )
open import DirectedHoTT.Lib.ISz using ( szMeths; ⊢szMeths )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )

szMethsK : {Γ : Cx} → RTm Γ
szMethsK = szMeths KnotD

-- ⚠ ONE ARGUMENT MORE: a `Split KnotD 0 KnotD`.  `Lib/IFold`'s
--   method-tuple lemma is motive-generic now, and its per-row
--   `imethTy-wf` needs `k ∈ID D` / `ilookupD D k ≡ C`, which the
--   split supplies.  At the hard-wired `Nat` motive the codomain
--   never mentioned the payload, so nobody had to say it.
⊢szMethsK : {Γ : Ctx} → Γ ⊢ szMethsK ∷ imethsTy KnotD IPair Nat KnotD
⊢szMethsK = ⊢szMeths KnotD IPair zero KnotD KnotWf KnotWf spl-nil ⊢IPair

-- ★★★ `sz` OVER THE WHOLE KNOT.
szTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
szTm i t = ielim KnotD i szMethsK t

⊢szTm : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
        Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ szTm i t ∷ Nat
⊢szTm di dt = ⊢ielim KnotWf ty-Nat di ⊢szMethsK dt
