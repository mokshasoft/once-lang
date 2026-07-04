-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.MeaningBridge — the fundamental lemma of the observational
-- logical relation (Plan 0.58, OCP-0006): the DIRECT meaning `⟦_⟧ᶜ`/`⟦_⟧ᵢ`
-- and `SD.⟦realize _⟧ˢ` are `RelT`-related (and `⟦_⟧ᵐ`/`⟦_⟧ᵍ` relate to
-- `evalᴰ`/`eval` of the realized IR). Applied at `main : EffUU` / `tt`, this
-- discharges the apex `bridgeᵈ` postulate — funext-free (`MeaningRelation`).
--
-- Built strictly top-down: this module STATES the four-realm fundamental
-- lemma + the `RelEnv` it inducts over; the case discharges follow.
------------------------------------------------------------------------

module Once.Adequacy.MeaningBridge where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.Maybe using (just)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Once.Type using (Type; Purity; mk-kind; Many; _⇒[_]_; _+_; _*_; μ-type; ⟦_⟧T; Functor; Int)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; lookup)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; projTrace; valueT)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_; _⊢ᵍ_∶_; _⊢ᵐ_∶_⇨[_]_;
  m-id; m-fst; m-snd; m-terminal; m-initial; m-inl; m-inr; m-compose; m-case;
  m-pair; m-curry; m-cata; m-const; m-named; m-named-resolved;
  g-int; g-terminal; g-pair; g-inl; g-inr; g-In)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵍ; ⟦_⟧ᵐ; lookupᴰ; Env; cata-sem)
import Once.IR as IR
open import Once.Arith.SigOp.Builders using (value-info)
open import Once.CanonicalName using (CanonicalName; bare)
open import Once.Denotation.Realize using (realize; realize-infer; realize-morph; realize-global)
import Once.Denotation.SourceDenote as SD
open import Once.Adequacy.MeaningRelation
  using (RelV; RelT; RelT-return; RelT-bind)

------------------------------------------------------------------------
-- Related environments — pointwise `RelV` down the context.
------------------------------------------------------------------------

RelEnv : ∀ {n} (Γ : Ctx n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → Set
RelEnv ∅           _          _          = ⊤
RelEnv (Γ , A ^ q) (dγ₁ , a₁) (dγ₂ , a₂) = RelEnv Γ dγ₁ dγ₂ × RelV A a₁ a₂

-- A related environment yields related values at every de-Bruijn position.
rel-lookup : ∀ {n} (Γ : Ctx n) (i : Fin n) {dγ₁ dγ₂ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ}
           → RelEnv Γ dγ₁ dγ₂ → RelV (lookup Γ i) (lookupᴰ Γ i dγ₁) (lookupᴰ Γ i dγ₂)
rel-lookup (Γ , A ^ q) zero    {dγ₁ , a₁} {dγ₂ , a₂} (_  , ra) = ra
rel-lookup (Γ , A ^ q) (suc i) {dγ₁ , a₁} {dγ₂ , a₂} (re , _)  = rel-lookup Γ i re


------------------------------------------------------------------------
-- The fundamental lemma — four mutually-recursive realms. STATED here;
-- discharged case-by-case (structural: `RelT-bind`/`RelT-return` + IH).
-- SCAFFOLD: bodies are `postulate` pending the case discharges.
------------------------------------------------------------------------

postulate
  bridge-i : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ)
             {dγ₁ dγ₂ : Env ctx} (re : RelEnv (NamedCtx.debruijn ctx) dγ₁ dγ₂)
           → RelT A (⟦ d ⟧ᵢ dγ₁) (SD.⟦ realize-infer d ⟧ˢ dγ₂)
  bridge-c : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ)
             {dγ₁ dγ₂ : Env ctx} (re : RelEnv (NamedCtx.debruijn ctx) dγ₁ dγ₂)
           → RelT A (⟦ d ⟧ᶜ dγ₁) (SD.⟦ realize d ⟧ˢ dγ₂)
  -- m-named / m-named-resolved: a sigop preserves the relation. Its event drops
  -- non-`Int` (non-`FitsInReg`) args (`mkEvent`), and for `FitsInReg` domains
  -- `RelV = ≡` gives `forget`-equality by `cong` — funext-free (see plan 0.58).
  sigop-bridge : ∀ {A B} {cn : CanonicalName} {a b : ⟦ A ⟧ᴰ} → RelV A a b
               → RelT B (evalᴰ (IR.SigOp (value-info {A} {B} cn)) a)
                        (evalᴰ (IR.SigOp (value-info {A} {B} cn)) b)
  -- m-cata: the fold preserves the relation (`sem-cata` congruence over the
  -- direct algebra `cata-ev-algᴰ-D`, using the recursive `bridge-m` on `alg`).
  cata-bridge : ∀ {F} {A'} {wfF : WellFormedF F}
                (dalg : ⟦ ⟦ F ⟧T A' ⟧ᴰ → T ⟦ A' ⟧ᴰ) (mir : IR.IR (⟦ F ⟧T A') A')
                {a b : ⟦ μ-type F ⟧ᴰ} → RelV (μ-type F) a b
              → RelT A' (cata-sem wfF dalg a) (evalᴰ (IR.Cata wfF mir) b)
  -- Leaf `evalᴰ`-reduction facts (the `intLit` / `In` reductions of a global
  -- point). NOT the funext concern — plain equational leaves, discharged with
  -- the other leaves.
  int-bridge : ∀ {ctx : NamedCtx} {X : Type} (n : ℤ) (y : ⟦ X ⟧ᴰ)
             → RelT Int (returnT ⟦ g-int {ctx} n ⟧ᵍ) (evalᴰ (realize-global {X = X} (g-int {ctx} n)) y)
  in-bridge : ∀ {ctx arg} {F : Functor} {X : Type} {wfF : WellFormedF F}
              (dec : wellFormedF? F ≡ just wfF) (garg : ctx ⊢ᵍ arg ∶ (⟦ F ⟧T (μ-type F))) (y : ⟦ X ⟧ᴰ)
            → RelT (μ-type F) (returnT ⟦ g-In {wfF = wfF} dec garg ⟧ᵍ)
                             (evalᴰ (realize-global {X = X} (g-In {wfF = wfF} dec garg)) y)

-- The VALUE realm, DISCHARGED — structural (`RelT-bind`/`RelT-return`, using
-- `returnT x >>=T f ≡ f x` definitionally) + the two leaf facts above.
bridge-g : ∀ {ctx : NamedCtx} {e A} {X : Type} (d : ctx ⊢ᵍ e ∶ A) (y : ⟦ X ⟧ᴰ)
         → RelT A (returnT ⟦ d ⟧ᵍ) (evalᴰ (realize-global {X = X} d) y)
bridge-g {ctx = ctx} {X = X} (g-int n) y = int-bridge {ctx = ctx} {X = X} n y
bridge-g (g-terminal _ _) y n = refl , tt
-- Compound cases inline the `∀ n` reasoning (applying `bridge-g … n` gives a
-- concrete pair, so no `RelT`-type unification): the pure side's trace is `[]`,
-- the `evalᴰ` side's is `projTrace (sub) n ++ …`, equal by the sub-relation's
-- trace half; the value follows from the sub-relation's value half.
bridge-g (g-pair ga gb) y n =
    cong₂ (λ x z → x ++ (z ++ [])) (proj₁ (bridge-g ga y n)) (proj₁ (bridge-g gb y n))
  , (proj₂ (bridge-g ga y n) , proj₂ (bridge-g gb y n))
bridge-g (g-inl ga) y n = cong (_++ []) (proj₁ (bridge-g ga y n)) , proj₂ (bridge-g ga y n)
bridge-g (g-inr gb) y n = cong (_++ []) (proj₁ (bridge-g gb y n)) , proj₂ (bridge-g gb y n)
bridge-g (g-In dec garg) y = in-bridge dec garg y

------------------------------------------------------------------------
-- The MORPHISM realm, DISCHARGED — structural (`RelT-return`/`RelT-bind` +
-- direct `∀ n` for the constructor-wrapping cases); `m-const` routes to
-- `bridge-g`; `m-cata`/`m-named` via the leaves above.
------------------------------------------------------------------------

bridge-m : ∀ {ctx : NamedCtx} {e A B} {π : Purity} (d : ctx ⊢ᵐ e ∶ A ⇨[ π ] B)
         → RelV (A ⇒[ mk-kind Many π ] B) (⟦ d ⟧ᵐ) (evalᴰ (realize-morph d))
bridge-m (m-id _ _)          rv n = refl , rv
bridge-m (m-fst _ _)         rv n = refl , proj₁ rv
bridge-m (m-snd _ _)         rv n = refl , proj₂ rv
bridge-m (m-terminal _ _)    _ n = refl , tt
bridge-m (m-initial _ _) {a = ()}
bridge-m (m-inl _ _)         rv n = refl , rv
bridge-m (m-inr _ _)         rv n = refl , rv
bridge-m (m-compose _ df dg) rv n =
    cong₂ _++_ (proj₁ (bridge-m dg rv n)) (proj₁ (bridge-m df (proj₂ (bridge-m dg rv n)) n))
  , proj₂ (bridge-m df (proj₂ (bridge-m dg rv n)) n)
bridge-m (m-case df dg) {a = inj₁ _} {b = inj₁ _} rv = bridge-m df rv
bridge-m (m-case df dg) {a = inj₂ _} {b = inj₂ _} rv = bridge-m dg rv
bridge-m (m-case df dg) {a = inj₁ _} {b = inj₂ _} ()
bridge-m (m-case df dg) {a = inj₂ _} {b = inj₁ _} ()
bridge-m (m-pair df dg)      rv n =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-m df rv n)) (proj₁ (bridge-m dg rv n))
  , (proj₂ (bridge-m df rv n) , proj₂ (bridge-m dg rv n))
bridge-m (m-curry df)        rv n = refl , (λ rb → bridge-m df (rv , rb))
bridge-m (m-const gd) {b = b} _ = bridge-g gd b
bridge-m (m-cata {wfF = wfF} _ alg) {a = a} {b = b} rv =
  cata-bridge {wfF = wfF} ⟦ alg ⟧ᵐ (realize-morph alg) {a = a} {b = b} rv
bridge-m {A = A} {B = B} (m-named {x = x} _ _ _) {a = a} {b = b} rv =
  sigop-bridge {A = A} {B = B} {cn = bare x} {a = a} {b = b} rv
bridge-m {A = A} {B = B} (m-named-resolved {cn = cn} _) {a = a} {b = b} rv =
  sigop-bridge {A = A} {B = B} {cn = cn} {a = a} {b = b} rv
