-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ViewNatural — plan 0.104 E.2: a view NATURAL in the rigid
-- substitution. At a substituted instance it finds the substituted instance
-- of the entry; ground and imported uses are fixed. (`viewOf` is, ElabInst.)
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

module Once.Adequacy.ViewNatural {s : ℕ} (S : Sig s) where

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤)
import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Type using (Ground)
open import Once.Type.Rigid using (KindedInstance)
open import Once.Spec.Core.PolyTy using (KCtx; GSub; Respects)
open import Once.TypeCheck.Classify using (Imports; PolyCtx; lookupPolyPrefix)
import Once.TypeCheck.RigidSubst as RS
open import Once.Spec.Elaboration S using (View; ImportAt; ffi; def)

module _ {m} (Δ : KCtx m) (τ : GSub m) (r : Respects Δ τ) where
  -- An imported definition is used at a ground instance, so it is fixed.
  NatImp : ∀ {T} → ImportAt T → Set
  NatImp (ffi _ _) = ⊤
  NatImp (def d i) = (λ j → RS.ρ̂ Δ τ r (proj₁ i j)) ≡ proj₁ i

  record Natural {imps : Imports} {polys : PolyCtx} (V : View imps polys) : Set where
    field
      nat-inst : ∀ {x sc body prefix T} (lp : lookupPolyPrefix polys x ≡ Data.Maybe.just (sc , body , prefix))
                   (ng : ¬ Ground sc) (ki : KindedInstance sc T)
               → proj₁ (View.inst V lp ng (RS.ρ̂-ki Δ τ r {sc} ki)) ≡ (λ i → RS.ρ̂ Δ τ r (proj₁ (View.inst V lp ng ki) i))
      nat-ground : ∀ {x sc body prefix} (lp : lookupPolyPrefix polys x ≡ Data.Maybe.just (sc , body , prefix)) (g : Ground sc)
                 → (λ i → RS.ρ̂ Δ τ r (proj₁ (View.ground V lp g) i)) ≡ proj₁ (View.ground V lp g)
      nat-imp : ∀ {x T} (lk : Once.TypeCheck.Classify.lookupImport imps x ≡ Data.Maybe.just T) → NatImp (View.imported V lk)

