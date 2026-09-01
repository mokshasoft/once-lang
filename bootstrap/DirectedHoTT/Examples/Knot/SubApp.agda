------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ APPLYING A SUBSTITUTION, OBJECT-LEVEL.
--
--     subAtK s dd m σ t  =  app (app (subTmK (pair s dd) t) m) σ
--
-- ⚠ THIS IS THE SHAPE THE JUDGEMENT ROWS ACTUALLY NEED.  `subTmK` is an
--   `ielim` and so takes an INDEX and an ELEMENT; a rule writes
--   `subTm σ t`, naming neither the index nor the target depth.  The
--   wrapper is where those two get supplied, which is what lets the
--   generator map a NAME to a NAME.
--
-- ★★★ AND THE PROOF IS `⊢motAppK ∘ ⊢subTmK` PLUS ONE CONVERSION.
--   `Knot/SubMot` already had to apply the motive to a depth and a
--   substitution — that is what the IH does at every row — so
--
--     ⊢motAppK : Γ ⊢ h ∷ iinst (pair s dd) u subMotK → Γ ⊢ m ∷ Nat →
--                Γ ⊢ sb ∷ SubTy dd m →
--                Γ ⊢ app (app h m) sb ∷ K (pair (sortMap s) m)
--
--   is exactly this wrapper's body, at an ABSTRACT head.  ⚠ I had begun
--   rebuilding it from `βsnd`/`βfst`/`sortMap-red` before looking.
--   ⇒ `judge-abstractions-at-the-use-site`, read in reverse: before
--     building the abstraction, check whether its CONSUMER exists.
--
-- ★ THE ONE THING LEFT TO PAY is that the motive returns at
--   `sortMap s`, not at `s`.  For a CONCRETE sort that is a reduction
--   and `decStableK` already decides it at every numeral — so the
--   caller passes the stability chain and nothing here cases on it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubApp where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; app; pair; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢conv )
open import DirectedHoTT.Spec.Typing using ( _⟶*_ )
open import DirectedHoTT.Metatheory.Injectivity using ( red→≅ᵀ; ⟶ᵀ*-IMu )
open import DirectedHoTT.Metatheory.Confluence using ( ⟶*-pairˡ )
open import DirectedHoTT.Examples.Knot.Desc using ( K )
open import DirectedHoTT.Examples.Knot.Sorts using ( ⊢ixP; sTy; sTm; ⊢sTy; ⊢sTm )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.SubMot
  using ( subTmK; ⊢subTmK; ⊢motAppK; sortMap; sortMap-ty; sortMap-tm )

------------------------------------------------------------------------
-- ★ THE TERM.  `t` sits at `dd`, the result at `m`, and the two are
--   INDEPENDENT — the index the eliminator is run at is not the index of
--   the answer, and which way they differ is the SUBSTITUTION's business.
--
-- ⚠⚠ IT USED TO READ `dd = nsuc m`, i.e. a substitution CONSUMES one
--   binder.  That is true of `single` and of `extS` and false in
--   general: `nrs : Sub (Γ ∙) ((Γ ∙) ∙)` RAISES, and `⊢natrec`'s
--   successor premise — `subTy nrs M` — is the row that says so.
--
-- ★ THE UNDERLYING LEMMA WAS ALREADY GENERAL.  `⊢motAppK` takes `dd` and
--   `m` as separate implicits; only this wrapper tied them together.
--   ⇒ the THIRD narrow twin found in one sitting, after `⊢Var-vzKv` and
--     `⊢Ctx-extKv`.  In each the general form cost nothing extra to
--     state — what it cost was noticing.
------------------------------------------------------------------------

subAtK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
subAtK s dd m σ t = app (app (subTmK (pair s dd) t) m) σ

⊢subAtK : {Γ : Ctx} {s dd m σ t : RTm ⌊ Γ ⌋} →
          -- ⚠ NOT `{Δ : Cx} → sortMap {Δ} s ⟶* s`.  `s` is a term IN
          --   `⌊ Γ ⌋`, so it cannot be read at another context; only the
          --   CONCRETE instances below are context-generic, and they
          --   instantiate here.
          Γ ⊢ s ∷ Nat → sortMap s ⟶* s →
          Γ ⊢ dd ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ σ ∷ SubTy dd m →
          Γ ⊢ t ∷ K (pair s dd) →
          Γ ⊢ subAtK s dd m σ t ∷ K (pair s m)
⊢subAtK ds st dd dm dσ dt =
  ⊢conv (⊢motAppK (⊢subTmK (⊢ixP ds dd) dt) dm dσ)
        (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairˡ st)))

------------------------------------------------------------------------
-- ★★ THE TWO INSTANCES THE RULES NAME.  A rule says `subTy σ A` or
--   `subTm σ t`; the sort is what tells them apart, and it is the only
--   thing that does.
------------------------------------------------------------------------

subTyAtK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
subTyAtK dd m σ A = subAtK sTy dd m σ A

subTmAtK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
subTmAtK dd m σ t = subAtK sTm dd m σ t

⊢subTyAtK : {Γ : Ctx} {dd m σ A : RTm ⌊ Γ ⌋} →
            Γ ⊢ dd ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ σ ∷ SubTy dd m →
            Γ ⊢ A ∷ K (pair sTy dd) →
            Γ ⊢ subTyAtK dd m σ A ∷ K (pair sTy m)
⊢subTyAtK = ⊢subAtK ⊢sTy sortMap-ty

⊢subTmAtK : {Γ : Ctx} {dd m σ t : RTm ⌊ Γ ⌋} →
            Γ ⊢ dd ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ σ ∷ SubTy dd m →
            Γ ⊢ t ∷ K (pair sTm dd) →
            Γ ⊢ subTmAtK dd m σ t ∷ K (pair sTm m)
⊢subTmAtK = ⊢subAtK ⊢sTm sortMap-tm
