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
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Once.Type using (Type; Purity; mk-kind; Many; _⇒[_]_; _+_; _*_; μ-type; ⟦_⟧T; Functor; Int; Unit)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; lookup; svar; SVar)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Surface.Syntax using (sigOp; poly)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; projTrace; valueT)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Raw using (BinOp;
  OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.SigOp.Info using (semM)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_; _⊢ᵍ_∶_; _⊢ᵐ_∶_⇨[_]_;
  m-id; m-fst; m-snd; m-terminal; m-initial; m-inl; m-inr; m-compose; m-case;
  m-pair; m-curry; m-cata; m-const; m-named; m-named-resolved;
  g-int; g-terminal; g-pair; g-inl; g-inr; g-In;
  t-int; t-str; t-unit; t-unit-var; t-var-local; t-var-qualified;
  t-var-resolved; t-var-import; t-annot; t-pair; t-neg; t-let; t-case;
  t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
  t-terminal-app; t-apply-app-infer; t-app; t-effApp;
  t-morph-lift; t-value-lift; t-embed; t-lam; t-pair-lit-check;
  t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
  t-initial-app-check; t-subsume; t-arg-driven-app-check; t-var-poly-instantiate)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵍ; ⟦_⟧ᵐ;
  lookupᴰ; Env; cata-sem; sigOpValᴰ; svarᴰ; in-value)
import Once.IR as IR
open import Once.Arith.SigOp.Builders using (value-info;
  add-info; sub-info; mul-info; div-info; mod-info; neg-info;
  lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
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
-- The RIGHT side uses `SD.lookupᴰ` (the SourceDenote env-lookup) so this feeds
-- the `t-var-local` bridge case directly: `Meaning.lookupᴰ` and `SD.lookupᴰ`
-- share every clause, so each leaf still reduces identically (`ra` / recurse).
rel-lookup : ∀ {n} (Γ : Ctx n) (i : Fin n) {dγ₁ dγ₂ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ}
           → RelEnv Γ dγ₁ dγ₂ → RelV (lookup Γ i) (lookupᴰ Γ i dγ₁) (SD.lookupᴰ Γ i dγ₂)
rel-lookup (Γ , A ^ q) zero    {dγ₁ , a₁} {dγ₂ , a₂} (_  , ra) = ra
rel-lookup (Γ , A ^ q) (suc i) {dγ₁ , a₁} {dγ₂ , a₂} (re , _)  = rel-lookup Γ i re


------------------------------------------------------------------------
-- The fundamental lemma — four mutually-recursive realms. STATED here;
-- discharged case-by-case (structural: `RelT-bind`/`RelT-return` + IH).
-- SCAFFOLD: bodies are `postulate` pending the case discharges.
------------------------------------------------------------------------

postulate
  -- t-var-qualified / t-var-resolved / t-var-import: a value-position named
  -- reference. LHS is the closed `value-info` sigop (`sigOpValᴰ`); RHS is
  -- `SD.⟦ sigOp cn ⟧ˢ`, which dispatches on whether `A` is an arrow. At a
  -- non-arrow `A` the two coincide definitionally; at an arrow the closed
  -- `value-info` value and SD's `arrow-info` closure agree by the same
  -- β/uncurry ABI iso as `sigop-bridge` (funext-free via `FitsInReg`).
  sigop-ref-bridge : ∀ {n} {Γ : Ctx n} {A : Type} (cn : CanonicalName) (dγ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ)
                   → RelT A (sigOpValᴰ (value-info {Unit} {A} cn)) (SD.⟦ sigOp {Γ = Γ} {A = A} cn ⟧ˢ dγ)
  -- t-var-poly-instantiate: same as `sigop-ref-bridge` but RHS is `poly x T`
  -- (SD's `poly` clause is the un-dispatched `value-info` form ⇒ LHS ≡ RHS
  -- definitionally; the remaining content is `RelV`-reflexivity at `T`).
  poly-ref-bridge : ∀ {n} {Γ : Ctx n} (name : String) (T : Type) (dγ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ)
                  → RelT T (sigOpValᴰ (value-info {Unit} {T} (bare name))) (SD.⟦ poly {Γ = Γ} name T ⟧ˢ dγ)
  -- t-In-app-check: the μ-introduction constructor `In` at the value level.
  -- `in-value` (LHS) vs `evalᴰ (IR.In wfF Heap)` (RHS) — both pure (empty
  -- trace), agreeing on the value by `eval (In)`/`inject`/`forget`.
  in-app-bridge : ∀ {F : Functor} {wfF : WellFormedF F} {vᴸ vᴿ : ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ}
                → RelV (⟦ F ⟧T (μ-type F)) vᴸ vᴿ
                → RelT (μ-type F) (returnT (in-value vᴸ)) (evalᴰ (IR.In wfF IR.Heap) vᴿ)
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
  -- Leaf `evalᴰ`-reduction fact for the `In` initial-algebra global point.
  in-bridge : ∀ {ctx arg} {F : Functor} {X : Type} {wfF : WellFormedF F}
              (dec : wellFormedF? F ≡ just wfF) (garg : ctx ⊢ᵍ arg ∶ (⟦ F ⟧T (μ-type F))) (y : ⟦ X ⟧ᴰ)
            → RelT (μ-type F) (returnT ⟦ g-In {wfF = wfF} dec garg ⟧ᵍ)
                             (evalᴰ (realize-global {X = X} (g-In {wfF = wfF} dec garg)) y)

-- `int-bridge` DISCHARGED: `realize-global (g-int n) = const fits-int ∣n∣ ∘ terminal`,
-- whose `evalᴰ` reduces (via the catch-all + `eval (const …) = ∣n∣`, `inject{Int}=id`,
-- `[]++[]=[]`) to `λ _ → ([] , ∣n∣) = returnT (absℤ n)` — definitionally the LHS.
int-bridge : ∀ {ctx : NamedCtx} {X : Type} (n : ℤ) (y : ⟦ X ⟧ᴰ)
           → RelT Int (returnT ⟦ g-int {ctx} n ⟧ᵍ) (evalᴰ (realize-global {X = X} (g-int {ctx} n)) y)
int-bridge n y k = refl , refl

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

------------------------------------------------------------------------
-- The CHECK / INFER realms, DISCHARGED — mutual structural induction on the
-- derivation, mirroring `Meaning.⟦_⟧ᵢ`/`⟦_⟧ᶜ` (LHS) vs `SD.⟦ realize(-infer) _ ⟧ˢ`
-- (RHS) clause-for-clause. Same technique as `bridge-g`/`bridge-m`: inline the
-- `∀ n`, `cong`/`cong₂` on the `++`-traces, project the value half. Genuinely
-- higher-order leaves route to the narrow postulates above.
------------------------------------------------------------------------

-- Propositional equality of a comparison result (`Unit + Unit`) lifts to `RelV`.
≡→RelV-⊎⊤ : ∀ {x y : ⟦ Unit + Unit ⟧ᴰ} → x ≡ y → RelV (Unit + Unit) x y
≡→RelV-⊎⊤ {inj₁ _} refl = tt
≡→RelV-⊎⊤ {inj₂ _} refl = tt

bridge-i : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ)
           {dγ₁ dγ₂ : Env ctx} (re : RelEnv (NamedCtx.debruijn ctx) dγ₁ dγ₂)
         → RelT A (⟦ d ⟧ᵢ dγ₁) (SD.⟦ realize-infer d ⟧ˢ dγ₂)
bridge-c : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ)
           {dγ₁ dγ₂ : Env ctx} (re : RelEnv (NamedCtx.debruijn ctx) dγ₁ dγ₂)
         → RelT A (⟦ d ⟧ᶜ dγ₁) (SD.⟦ realize d ⟧ˢ dγ₂)

-- Literals — pure `returnT`, identical values.
bridge-i (t-int _)   re k = refl , refl
bridge-i (t-str _)   re k = refl , refl
bridge-i t-unit      re k = refl , tt
bridge-i t-unit-var  re k = refl , tt

-- Local variable — `svarᴰ (svar i)` (LHS) and `SD.⟦ var i ⟧ˢ` (RHS) both peel to
-- the positional lookup; `rel-lookup` relates the two envs at position `i`.
bridge-i (t-var-local {eV = svar i} _ _) re k = refl , rel-lookup _ i re

-- Named value references — the sigop-reference leaf (dispatch on result type).
bridge-i {ctx = ctx} (t-var-qualified {T = A} _)   {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ dγ₂
bridge-i {ctx = ctx} (t-var-resolved {T = A} _)    {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ dγ₂
bridge-i {ctx = ctx} (t-var-import {T = A} _ _ _)  {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ dγ₂

-- Annotation switches to check mode.
bridge-i (t-annot d) re = bridge-c d re

-- Pair — two sequenced infers, product value.
bridge-i (t-pair da db) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i da re k)) (proj₁ (bridge-i db re k))
  , (proj₂ (bridge-i da re k) , proj₂ (bridge-i db re k))

-- Negation — bind then a pure `semM neg-info`.
bridge-i (t-neg d) re k =
    cong (_++ []) (proj₁ (bridge-i d re k))
  , cong (semM neg-info) (proj₂ (bridge-i d re k))

-- Let — thread the bound value into the extended related env.
bridge-i (t-let d₁ d₂) re k =
  let b1 = bridge-i d₁ re k
      b2 = bridge-i d₂ (re , proj₂ b1) k
  in cong₂ _++_ (proj₁ b1) (proj₁ b2) , proj₂ b2

-- Case — split on the (related) scrutinee's injection; recurse in the branch.
bridge-i (t-case ds dl dr) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re k
  with valueT (⟦ ds ⟧ᵢ dγ₁) k | valueT (SD.⟦ realize-infer ds ⟧ˢ dγ₂) k | bridge-i ds re k
... | inj₁ a | inj₁ a' | tr , rv =
      cong₂ _++_ tr (proj₁ (bridge-i dl (re , rv) k)) , proj₂ (bridge-i dl (re , rv) k)
... | inj₂ b | inj₂ b' | tr , rv =
      cong₂ _++_ tr (proj₁ (bridge-i dr (re , rv) k)) , proj₂ (bridge-i dr (re , rv) k)
... | inj₁ a | inj₂ b' | tr , ()
... | inj₂ b | inj₁ a' | tr , ()

-- Arithmetic binops — bind both, pure `semM <op>-info` (Int value = `≡`).
bridge-i (t-binop-arith {op = OpAdd} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM add-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpSub} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM sub-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpMul} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM mul-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpDiv} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM div-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpMod} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM mod-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpLt} () _ _)
bridge-i (t-binop-arith {op = OpLe} () _ _)
bridge-i (t-binop-arith {op = OpGt} () _ _)
bridge-i (t-binop-arith {op = OpGe} () _ _)
bridge-i (t-binop-arith {op = OpEq} () _ _)
bridge-i (t-binop-arith {op = OpNe} () _ _)

-- Comparison binops — bind both, pure `semM <op>-info` (Unit+Unit value).
bridge-i (t-binop-cmp {op = OpLt} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM lt-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpLe} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM le-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpGt} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM gt-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpGe} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM ge-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpEq} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM eq-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpNe} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM ne-info (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpAdd} () _ _)
bridge-i (t-binop-cmp {op = OpSub} () _ _)
bridge-i (t-binop-cmp {op = OpMul} () _ _)
bridge-i (t-binop-cmp {op = OpDiv} () _ _)
bridge-i (t-binop-cmp {op = OpMod} () _ _)

-- Polymorphic-builtin applications — RHS is `morph-app <ir> …`; each `evalᴰ <ir>`
-- reduces to the same pure post-op the LHS applies (modulo the `++ []` bookkeeping).
bridge-i (t-id-app d) re k =
    trans (proj₁ (bridge-i d re k)) (sym (++-identityʳ _)) , proj₂ (bridge-i d re k)
bridge-i (t-fst-app d) re k =
    cong (_++ []) (proj₁ (bridge-i d re k)) , proj₁ (proj₂ (bridge-i d re k))
bridge-i (t-snd-app d) re k =
    cong (_++ []) (proj₁ (bridge-i d re k)) , proj₂ (proj₂ (bridge-i d re k))
bridge-i (t-terminal-app d) re k =
    cong (_++ []) (proj₁ (bridge-i d re k)) , tt
bridge-i (t-apply-app-infer d) re k =
  let bd = bridge-i d re k
      inner = proj₁ (proj₂ bd) (proj₂ (proj₂ bd)) k
  in cong₂ _++_ (proj₁ bd) (proj₁ inner) , proj₂ inner

-- Application — infer the head, check the argument, apply the related closures.
bridge-i (t-app _ df dx) re k =
  let bf = bridge-i df re k
      bx = bridge-c dx re k
      inner = proj₂ bf (proj₂ bx) k
  in cong₂ _++_ (proj₁ bf) (cong₂ _++_ (proj₁ bx) (proj₁ inner)) , proj₂ inner

-- Effectful application — a suspended thunk; the value is the (arg-ignoring)
-- closure, related pointwise via the same application reasoning.
bridge-i (t-effApp _ df dx) re k = refl , λ {a} {b} _ k' →
  let bf = bridge-i df re k'
      bx = bridge-c dx re k'
      inner = proj₂ bf (proj₂ bx) k'
  in cong₂ _++_ (proj₁ bf) (cong₂ _++_ (proj₁ bx) (proj₁ inner)) , proj₂ inner

-- Morphism / value lift — `returnT` of the (bridge-m / bridge-g)-related arrow.
bridge-c (t-morph-lift d) re k = refl , bridge-m d
bridge-c (t-value-lift g) re k = refl , λ {a} {b} _ → bridge-g g b
bridge-c (t-embed d) re = bridge-i d re
bridge-c (t-lam _ d) re k = refl , λ {a} {b} rv → bridge-c d (re , rv)
bridge-c (t-pair-lit-check da db) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-c da re k)) (proj₁ (bridge-c db re k))
  , (proj₂ (bridge-c da re k) , proj₂ (bridge-c db re k))
bridge-c (t-In-app-check {wfF = wfF} _ d) re k =
  let bd = bridge-c d re k
      bi = in-app-bridge {wfF = wfF} (proj₂ bd) k
  in cong₂ _++_ (proj₁ bd) (proj₁ bi) , proj₂ bi
bridge-c (t-apply-check dp) re k =
  let bd = bridge-i dp re k
      inner = proj₁ (proj₂ bd) (proj₂ (proj₂ bd)) k
  in cong₂ _++_ (proj₁ bd) (proj₁ inner) , proj₂ inner
bridge-c (t-inl-app-check d) re k =
    cong (_++ []) (proj₁ (bridge-c d re k)) , proj₂ (bridge-c d re k)
bridge-c (t-inr-app-check d) re k =
    cong (_++ []) (proj₁ (bridge-c d re k)) , proj₂ (bridge-c d re k)
bridge-c (t-initial-app-check d) {dγ₁ = dγ₁} re k = ⊥-elim (valueT (⟦ d ⟧ᶜ dγ₁) k)
bridge-c (t-subsume d) re = bridge-c d re
bridge-c (t-arg-driven-app-check _ darg df) re k =
  let bf = bridge-c df re k
      bx = bridge-i darg re k
      inner = proj₂ bf (proj₂ bx) k
  in cong₂ _++_ (proj₁ bf) (cong₂ _++_ (proj₁ bx) (proj₁ inner)) , proj₂ inner
bridge-c {ctx = ctx} (t-var-poly-instantiate {x = x} {T = T} _ _ _ _ _ _) {dγ₂ = dγ₂} re = poly-ref-bridge {Γ = NamedCtx.debruijn ctx} x T dγ₂
