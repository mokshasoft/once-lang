------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ APPLYING A SUBSTITUTION, OBJECT-LEVEL.
--
--     subAtK s n σ t  =  app (app (subTmK (pair s (nsuc n)) t) n) σ
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
  using ( Cx; RTm; app; pair; nsuc; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢nsuc; ⊢conv )
open import DirectedHoTT.Spec.Typing using ( _⟶*_ )
open import DirectedHoTT.Metatheory.Injectivity using ( red→≅ᵀ; ⟶ᵀ*-IMu )
open import DirectedHoTT.Metatheory.Confluence using ( ⟶*-pairˡ )
open import DirectedHoTT.Examples.Knot.Desc using ( K )
open import DirectedHoTT.Examples.Knot.Sorts using ( ⊢ixP; sTy; sTm; ⊢sTy; ⊢sTm )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.SubMot
  using ( subTmK; ⊢subTmK; ⊢motAppK; sortMap; sortMap-ty; sortMap-tm )

------------------------------------------------------------------------
-- ★ THE TERM.  `t` sits at `nsuc n` and the result at `n` — a
--   substitution CONSUMES one binder, which is why the index the
--   eliminator is run at is not the index of the answer.
------------------------------------------------------------------------

subAtK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
subAtK s n σ t = app (app (subTmK (pair s (nsuc n)) t) n) σ

⊢subAtK : {Γ : Ctx} {s n σ t : RTm ⌊ Γ ⌋} →
          -- ⚠ NOT `{Δ : Cx} → sortMap {Δ} s ⟶* s`.  `s` is a term IN
          --   `⌊ Γ ⌋`, so it cannot be read at another context; only the
          --   CONCRETE instances below are context-generic, and they
          --   instantiate here.
          Γ ⊢ s ∷ Nat → sortMap s ⟶* s →
          Γ ⊢ n ∷ Nat → Γ ⊢ σ ∷ SubTy (nsuc n) n →
          Γ ⊢ t ∷ K (pair s (nsuc n)) →
          Γ ⊢ subAtK s n σ t ∷ K (pair s n)
⊢subAtK ds st dn dσ dt =
  ⊢conv (⊢motAppK (⊢subTmK (⊢ixP ds (⊢nsuc dn)) dt) dn dσ)
        (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairˡ st)))

------------------------------------------------------------------------
-- ★★ THE TWO INSTANCES THE RULES NAME.  A rule says `subTy σ A` or
--   `subTm σ t`; the sort is what tells them apart, and it is the only
--   thing that does.
------------------------------------------------------------------------

subTyAtK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
subTyAtK n σ A = subAtK sTy n σ A

subTmAtK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
subTmAtK n σ t = subAtK sTm n σ t

⊢subTyAtK : {Γ : Ctx} {n σ A : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ σ ∷ SubTy (nsuc n) n →
            Γ ⊢ A ∷ K (pair sTy (nsuc n)) →
            Γ ⊢ subTyAtK n σ A ∷ K (pair sTy n)
⊢subTyAtK = ⊢subAtK ⊢sTy sortMap-ty

⊢subTmAtK : {Γ : Ctx} {n σ t : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ σ ∷ SubTy (nsuc n) n →
            Γ ⊢ t ∷ K (pair sTm (nsuc n)) →
            Γ ⊢ subTmAtK n σ t ∷ K (pair sTm n)
⊢subTmAtK = ⊢subAtK ⊢sTm sortMap-tm
