-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.AnaBridge
--
-- D193: the `ana` case of `bridge-c` — `CataBridge`'s dual, and the last
-- site of D192.
--
-- WHY IT IS NOT `CataBridge`'s ARGUMENT. A fold runs over a value both sides
-- SHARE (`RelV (μ-type F) a b` is `a ≡ b`, so `cata-bridge` folds the same
-- `μS`), and only the per-layer step differs. An unfold shares nothing: it
-- BUILDS a coinductive value from two coalgebras the logical relation merely
-- RELATES, and the observational relation at a ν is propositional equality.
-- Relatedness is strictly weaker than equality, so no amount of structural
-- work closes that gap — the missing principle is coalgebraic extensionality,
-- which is why `Once.Denotation.ValueDomainLaws` exists.
--
-- With `_∼ᵈ_`, `anaᵈ-∼` and `bisimᵈ-to-eq` in hand the clause is short: push
-- the relation through the two coercions at the layer (`in-rel`, the mirror
-- of `CataBridge`'s `z-rel`), hand the result to `anaᵈ-rel-eq`, done.
--
-- Own module for `CataBridge`'s reason: minimal, distinct-suffix `⟦_⟧`
-- imports, clear of `MeaningBridge`'s mixfix soup.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.AnaBridge (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Once.Word using (Carrier)
open import Once.Type using (Type; Functor; ⟦_⟧T; ν-type; K; Id; _⊕_; _⊗_)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod; translateF;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum)
open import Once.Semantics.Machine using (coerce-ν-in; ⟦_⟧F)
open import Once.Semantics.Functor using (SFunctor; ⟦_⟧SF)
open import Once.Semantics.Functor.Laws using (⟦_⟧SF-rel)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; νᵈ; anaᵈ; anaFᵈ; coerce-functor-D)
open import Once.Denotation.ValueDomainLaws using (CoalgRel; anaᵈ-rel-eq)
open import Once.Denotation.TraceMonad using (T; projTrace; valueT; fmapT; _>>=T_)
open import Once.Adequacy.MeaningRelation fmt using (RelV; RelT)

------------------------------------------------------------------------
-- At a base type the observational relation IS equality
------------------------------------------------------------------------

-- The converse of `CataBridge.base-refl`, and the ana needs this direction:
-- a `K`-position's layer is a base constant, and `⟦ SK _ ⟧SF-rel` asks for
-- equality of the two constants, not merely relatedness.
base-eq : ∀ {A} (ib : IsBaseType A) {x y : ⟦ A ⟧ᴰ} → RelV A x y → x ≡ y
base-eq base-Unit   _  = refl
base-eq base-Int    eq = eq
base-eq base-Float  eq = eq
base-eq base-Str    eq = eq
base-eq base-Buffer eq = eq
base-eq (base-Prod ibA ibB) {a₁ , b₁} {a₂ , b₂} (rA , rB) =
  cong₂ _,_ (base-eq ibA rA) (base-eq ibB rB)
base-eq (base-Sum ibA ibB) {inj₁ _} {inj₁ _} r = cong inj₁ (base-eq ibA r)
base-eq (base-Sum ibA ibB) {inj₂ _} {inj₂ _} r = cong inj₂ (base-eq ibB r)
base-eq (base-Sum ibA ibB) {inj₁ _} {inj₂ _} r = ⊥-elim r
base-eq (base-Sum ibA ibB) {inj₂ _} {inj₁ _} r = ⊥-elim r

------------------------------------------------------------------------
-- The layer coercion, relationally
------------------------------------------------------------------------

-- The mirror of `CataBridge`'s `z-rel`: that one takes a functor-lifted
-- relation on a layer the fold produced and lands in `RelV (⟦ G ⟧T A)`; this
-- one starts from `RelV (⟦ G ⟧T A)` — what the coalgebra's own bridge gives —
-- and lands in the functor-lifted relation the unfold consumes. Induction on
-- `WellFormedF`, mirroring `coerce-functor-D` and `coerce-ν-in` together.
in-rel : ∀ {A : Type} {G : Functor} (wf : WellFormedF G) {l r : ⟦ ⟦ G ⟧T A ⟧ᴰ}
       → RelV (⟦ G ⟧T A) l r
       → ⟦ translateF Carrier Carrier G ⟧SF-rel (RelV A)
           (coerce-ν-in G ⟦ A ⟧ᴰ (coerce-functor-D G A l))
           (coerce-ν-in G ⟦ A ⟧ᴰ (coerce-functor-D G A r))
in-rel (wf-K ib) rel rewrite base-eq ib rel = refl
in-rel wf-Id     rel = rel
in-rel (wf-Sum wfF wfG) {inj₁ _} {inj₁ _} rel = in-rel wfF rel
in-rel (wf-Sum wfF wfG) {inj₂ _} {inj₂ _} rel = in-rel wfG rel
in-rel (wf-Sum wfF wfG) {inj₁ _} {inj₂ _} rel = ⊥-elim rel
in-rel (wf-Sum wfF wfG) {inj₂ _} {inj₁ _} rel = ⊥-elim rel
in-rel (wf-Prod wfF wfG) {_ , _} {_ , _} (rF , rG) =
  in-rel wfF rF , in-rel wfG rG

------------------------------------------------------------------------
-- The bridge
------------------------------------------------------------------------

-- Two `ana`s built from RELATED coalgebras, started from RELATED seeds, are
-- EQUAL. `kR` is what `bridge-c` has for the coalgebra derivation once the
-- closure is bound; `rab` is what `RelV` at the arrow supplies.
--
-- The two `fmapT`s are transparent: `fmapT` maps the value and leaves the
-- trace alone, both definitionally, so the `CoalgRel` obligations ARE the
-- relation's own two halves, with `in-rel` applied to the second.
ana-bridge : ∀ {A : Type} {F : Functor} (wfF : WellFormedF F)
             {k₁ k₂ : ⟦ A ⟧ᴰ → T ⟦ ⟦ F ⟧T A ⟧ᴰ}
           → (∀ {a b : ⟦ A ⟧ᴰ} → RelV A a b → RelT (⟦ F ⟧T A) (k₁ a) (k₂ b))
           → ∀ {a b : ⟦ A ⟧ᴰ} → RelV A a b
           → anaFᵈ F (λ a' → fmapT (coerce-functor-D F A) (k₁ a')) a
             ≡ anaFᵈ F (λ a' → fmapT (coerce-functor-D F A) (k₂ a')) b
ana-bridge {A} {F} wfF {k₁} {k₂} kR rab =
  anaᵈ-rel-eq (translateF Carrier Carrier F) cr rab
  where
    cr : CoalgRel (translateF Carrier Carrier F) (RelV A)
           (λ a → fmapT (coerce-ν-in F ⟦ A ⟧ᴰ)
                    (fmapT (coerce-functor-D F A) (k₁ a)))
           (λ b → fmapT (coerce-ν-in F ⟦ A ⟧ᴰ)
                    (fmapT (coerce-functor-D F A) (k₂ b)))
    cr r = (λ j → proj₁ (kR r j)) , (λ j → in-rel wfF (proj₂ (kR r j)))
