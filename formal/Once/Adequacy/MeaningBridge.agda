-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.MeaningBridge (fmt : TargetNum) where

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

open import Once.Type using (Type; Purity; mk-kind; Many; pure; _⇒[_]_; _+_; _*_; μ-type; ⟦_⟧T; Functor; Int; Unit)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum;
  IsConcrete; con-base; con-fun)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.Semantics.Machine using (sem-In; coerce-functor)
open import Once.IRTy using (eraseF; ⌊⟧T-commute; IRTy)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Adequacy.InErased fmt using (In-ir; liftFn-In)
open import Once.Postulates using (extensionality)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; lookup; svar; SVar)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Surface.Syntax using (sigOp; poly; Expr; Usage; morph-app; unit)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; projTrace; valueT)
open import Once.Denotation.DenotTrace using (evalᴰ; forget; liftFn; cohᴰ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Raw using (BinOp;
  OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.SigOp.Info using (semM)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_; _⊢ᵍ_∶_; _⊢ᵐ_∶_⇨[_]_;
  m-id; m-fst; m-snd; m-terminal; m-initial; m-inl; m-inr; m-compose; m-case;
  m-pair; m-curry; m-cata; m-const; m-named; m-named-resolved;
  g-int; g-float; g-neg-int; g-neg-float; g-terminal; g-pair; g-inl; g-inr; g-In;
  t-int; t-float; t-str; t-unit; t-unit-var; t-var-local; t-var-qualified;
  t-var-resolved; t-var-import; t-annot; t-pair; t-neg; t-neg-float; t-let; t-case;
  t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
  t-terminal-app; t-apply-app-infer; t-app; t-effApp;
  t-morph-lift; t-value-lift; t-embed; t-lam; t-pair-lit-check;
  t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
  t-initial-app-check; t-subsume; t-arg-driven-app-check; t-var-poly-instantiate;
  t-var-poly-instantiate-infer)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵍ; ⟦_⟧ᵐ;
  lookupᴰ; Env; cata-sem; sigOpValᴰ; sigOpRefᴰ; svarᴰ; in-value; named-sem)
open import Once.Adequacy.CataErased fmt using (liftFn-SigOp)
open import Once.Adequacy.LiftFnReduce fmt using
  (liftFn-id; liftFn-fst; liftFn-snd; liftFn-terminal; liftFn-inl; liftFn-inr;
   liftFn-∘; liftFn-pair; liftFn-curry; liftFn-case-inj₁; liftFn-case-inj₂; liftFn-apply)
import Once.IR as IR
open import Once.Arith.SigOp.Builders using (value-info;
  add-info; sub-info; mul-info; div-info; mod-info; neg-info;
  lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.CanonicalName using (CanonicalName; bare)
open import Once.Denotation.Realize using (realize; realize-infer; realize-morph; realize-global; poly-usage-eq)
open import Once.Adequacy.SourceFaithful fmt using (faithful)
open import Once.Surface.Elaborate using (elaborate)
import Once.Denotation.SourceDenote as SD
open import Once.Adequacy.MeaningRelation fmt
  using (RelV; RelT; RelT-return; RelT-bind)
open import Once.Adequacy.CataBridge fmt using (cata-bridge)

-- Move a codomain-subst on `f` across `g ∘_` into a domain-subst on `g`.
-- Match-to-refl.  (`realize-global (g-In) = In ∘ subst(⌊⟧T)(rg) = In-ir ∘ rg`.)
subst-∘-move : ∀ {A B B' C : IRTy} (eq : B ≡ B') (g : IR.IR B' C) (f : IR.IR A B)
  → g IR.∘ subst (λ o → IR.IR A o) eq f ≡ subst (λ o → IR.IR o C) (sym eq) g IR.∘ f
subst-∘-move refl g f = refl

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
-- ALL leaves are now DISCHARGED (Plan 0.58): `sigop-bridge`, `poly-ref-bridge`,
-- and every `sigop-ref-bridge` case via `concrete-rel→refl`/`RelT-refl` (the
-- arrow corner routes through the correctly-dispatching `sigOpRefᴰ`); and
-- `cata-bridge` (the fold congruence) in `Once.Adequacy.CataBridge`, applied at
-- the `m-cata` case via the recursive `bridge-m alg`. Every case is proved.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- `RelV → ≡` at ARROW-FREE types — the tool for the `In` value cases. A
-- WELL-FORMED functor layer `⟦ F ⟧T X` is polynomial (`WellFormedF`'s `K`
-- holds only `IsBaseType`), so `RelV` there collapses to propositional
-- equality (no funext) provided the recursive slot `X` is itself first-order.
------------------------------------------------------------------------

base-rel→eq : ∀ {A} (ib : IsBaseType A) {a b : ⟦ A ⟧ᴰ} → RelV A a b → a ≡ b
base-rel→eq base-Unit           _  = refl
base-rel→eq base-Void {a = ()}
base-rel→eq base-Int            rv = rv
base-rel→eq base-Float          rv = rv
base-rel→eq base-Str            rv = rv
base-rel→eq base-Buffer         rv = rv
base-rel→eq (base-Prod ibA ibB) {a₁ , b₁} {a₂ , b₂} rv =
  cong₂ _,_ (base-rel→eq ibA (proj₁ rv)) (base-rel→eq ibB (proj₂ rv))
base-rel→eq (base-Sum ibA ibB) {inj₁ a} {inj₁ a'} rv = cong inj₁ (base-rel→eq ibA rv)
base-rel→eq (base-Sum ibA ibB) {inj₂ b} {inj₂ b'} rv = cong inj₂ (base-rel→eq ibB rv)
base-rel→eq (base-Sum ibA ibB) {inj₁ a} {inj₂ b'} ()
base-rel→eq (base-Sum ibA ibB) {inj₂ b} {inj₁ a'} ()

wfF-layer-eq : ∀ {F} (wfF : WellFormedF F) {X : Type}
             → (∀ {x y : ⟦ X ⟧ᴰ} → RelV X x y → x ≡ y)
             → {a b : ⟦ ⟦ F ⟧T X ⟧ᴰ} → RelV (⟦ F ⟧T X) a b → a ≡ b
wfF-layer-eq (wf-K ib)       xeq rv = base-rel→eq ib rv
wfF-layer-eq wf-Id           xeq rv = xeq rv
wfF-layer-eq (wf-Sum wfF wfG) xeq {inj₁ a} {inj₁ a'} rv = cong inj₁ (wfF-layer-eq wfF xeq rv)
wfF-layer-eq (wf-Sum wfF wfG) xeq {inj₂ b} {inj₂ b'} rv = cong inj₂ (wfF-layer-eq wfG xeq rv)
wfF-layer-eq (wf-Sum wfF wfG) xeq {inj₁ a} {inj₂ b'} ()
wfF-layer-eq (wf-Sum wfF wfG) xeq {inj₂ b} {inj₁ a'} ()
wfF-layer-eq (wf-Prod wfF wfG) xeq {a₁ , b₁} {a₂ , b₂} rv =
  cong₂ _,_ (wfF-layer-eq wfF xeq (proj₁ rv)) (wfF-layer-eq wfG xeq (proj₂ rv))

-- Plan 0.58: reflexivity of the relation at CONCRETE types. A concrete type is
-- a base scalar or a first-order function pointer (base domain), so `RelV`
-- collapses to `≡` at the (base) domain, and the reflexive value/computation
-- relation is inhabited funext-free (the arrow case eats the domain `≡`).
base-rel→refl : ∀ {A} (ib : IsBaseType A) (v : ⟦ A ⟧ᴰ) → RelV A v v
base-rel→refl base-Unit   v = tt
base-rel→refl base-Void   ()
base-rel→refl base-Int    v = refl
base-rel→refl base-Float  v = refl
base-rel→refl base-Str    v = refl
base-rel→refl base-Buffer v = refl
base-rel→refl (base-Prod ibA ibB) (a , b) = base-rel→refl ibA a , base-rel→refl ibB b
base-rel→refl (base-Sum ibA ibB) (inj₁ a) = base-rel→refl ibA a
base-rel→refl (base-Sum ibA ibB) (inj₂ b) = base-rel→refl ibB b

mutual
  concrete-rel→refl : ∀ {A} (c : IsConcrete A) (v : ⟦ A ⟧ᴰ) → RelV A v v
  concrete-rel→refl (con-base ib) v = base-rel→refl ib v
  concrete-rel→refl (con-fun bA cB) v {a} {b} rv
    rewrite base-rel→eq bA rv = RelT-refl cB (v b)

  RelT-refl : ∀ {A} (c : IsConcrete A) (t : T ⟦ A ⟧ᴰ) → RelT A t t
  RelT-refl c t n = refl , concrete-rel→refl c (valueT t n)

-- m-named / m-named-resolved: a sigop preserves the relation. The SigOp domain
-- is a base type (`bA`), so `base-rel→eq` collapses the arg `RelV` to `a ≡ b`;
-- both event and value are then EQUAL by `cong`, and the result relation is
-- `concrete-rel→refl` (result is concrete). Funext-free.
sigop-bridge : ∀ {A B} {cn : CanonicalName} (bA : IsBaseType A) (cB : IsConcrete B) {a b : ⟦ A ⟧ᴰ} → RelV A a b
             → RelT B (named-sem {A} {B} fmt cn bA cB a)
                      (liftFn fmt (IR.SigOp (value-info {A} {B} cn bA cB)) b)
sigop-bridge {A} {B} {cn} bA cB {a} {b} rv
  rewrite base-rel→eq bA rv
  = subst (λ f → RelT B (named-sem fmt cn bA cB b) (f b))
          (sym (liftFn-SigOp (value-info {A} {B} cn bA cB) bA))
          (λ n → refl , concrete-rel→refl cB _)

-- Value-position named reference. SD's `sigOp` dispatches on `A`'s shape: at a
-- base (`con-base`) type the arrow clause can't fire, so SD's catch-all IS the
-- closed `value-info` form ⇒ LHS ≡ RHS definitionally and the relation is
-- reflexivity (`RelT-refl`). The arrow (`con-fun`) corner is likewise reflexivity
-- on the correctly-dispatching `sigOpRefᴰ`.
-- At a base (non-arrow) type SD's `sigOp` catch-all IS the closed `value-info`
-- form; casing the witness exposes the shape so each clause is `refl`.
sd-sigOp-base≡ : ∀ {n} {Γ : Ctx n} {A : Type} (cn : CanonicalName) (ib : IsBaseType A) (dγ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ)
               → (SD.⟦ sigOp {Γ = Γ} {A = A} cn (con-base ib) ⟧ˢ fmt) dγ ≡ sigOpValᴰ fmt (value-info {Unit} {A} cn base-Unit (con-base ib))
sd-sigOp-base≡ cn base-Unit          dγ = refl
sd-sigOp-base≡ cn base-Void          dγ = refl
sd-sigOp-base≡ cn base-Int           dγ = refl
sd-sigOp-base≡ cn base-Float         dγ = refl
sd-sigOp-base≡ cn base-Str           dγ = refl
sd-sigOp-base≡ cn base-Buffer        dγ = refl
sd-sigOp-base≡ cn (base-Prod ibA ibB) dγ = refl
sd-sigOp-base≡ cn (base-Sum ibA ibB)  dγ = refl

-- Now `refl`-shaped: `Meaning.sigOpRefᴰ` DISPATCHES exactly as SD's `sigOp`, so
-- LHS ≡ RHS. `con-base` still needs the type-shape reduction of SD's stuck
-- catch-all (`sd-sigOp-base≡`, `sigOpRefᴰ (con-base) = sigOpValᴰ fmt (value-info)`);
-- `con-fun` exposes `A` as an arrow so BOTH sides are the same `arrow-info`
-- closure ⇒ plain reflexivity.
sigop-ref-bridge : ∀ {n} {Γ : Ctx n} {A : Type} (cn : CanonicalName) (conc : IsConcrete A) (dγ : ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ)
                 → RelT A (sigOpRefᴰ fmt cn conc) ((SD.⟦ sigOp {Γ = Γ} {A = A} cn conc ⟧ˢ fmt) dγ)
sigop-ref-bridge {A = A} cn (con-base ib) dγ =
  subst (λ z → RelT A (sigOpRefᴰ fmt cn (con-base ib)) z)
        (sym (sd-sigOp-base≡ cn ib dγ))
        (RelT-refl (con-base ib) (sigOpRefᴰ fmt cn (con-base ib)))
sigop-ref-bridge {A = Dom ⇒[ k ] Cod} cn (con-fun bDom cCod) dγ =
  RelT-refl (con-fun {k = k} bDom cCod) (sigOpRefᴰ fmt cn (con-fun {k = k} bDom cCod))

-- Plan 0.58 / D071: `poly-ref-bridge` DELETED. The surface `poly` node is no
-- longer a concrete `value-info` leaf (it is an internal `internal-info`
-- reference at ANY type), and it was already dead here — the `t-var-poly-
-- instantiate` case of `bridge-c` recurses on `bodyD` directly (see below).

-- `in-app-bridge` DISCHARGED (t-In-app-check): both sides are the pure `In`
-- constructor (`sem-In ∘ coerce-functor ∘ forget`, `inject{μ}=id`, empty trace);
-- the argument's `RelV` collapses to `≡` via `wfF-layer-eq` (`RelV(μ)=≡` at the
-- recursive slot), so a `cong` finishes — no funext.
in-app-bridge : ∀ {F : Functor} {wfF : WellFormedF F} {vᴸ vᴿ : ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ}
              → RelV (⟦ F ⟧T (μ-type F)) vᴸ vᴿ
              → RelT (μ-type F) (returnT (in-value vᴸ)) (liftFn fmt (In-ir wfF) vᴿ)
in-app-bridge {F} {wfF} rv =
  subst (RelT (μ-type F) (returnT (in-value _))) (sym (liftFn-In wfF _))
        (λ k → refl , cong in-value (wfF-layer-eq wfF (λ r → r) rv))

-- `int-bridge` DISCHARGED: `realize-global (g-int n) = const fits-int ∣n∣ ∘ terminal`,
-- whose `evalᴰ` reduces (via the catch-all + `eval (const …) = ∣n∣`, `inject{Int}=id`,
-- `[]++[]=[]`) to `λ _ → ([] , ∣n∣) = returnT (absℤ n)` — definitionally the LHS.
int-bridge : ∀ {ctx : NamedCtx} {X : Type} (n : ℤ) (y : ⟦ X ⟧ᴰ)
           → RelT Int (returnT (⟦ g-int {ctx} n ⟧ᵍ fmt)) (liftFn fmt (realize-global {X = X} (g-int {ctx} n)) y)
int-bridge n y k = refl , refl

-- The VALUE realm, DISCHARGED — structural (`RelT-bind`/`RelT-return`, using
-- `returnT x >>=T f ≡ f x` definitionally) + the two leaf facts above.
bridge-g : ∀ {ctx : NamedCtx} {e A} {X : Type} (d : ctx ⊢ᵍ e ∶ A) (y : ⟦ X ⟧ᴰ)
         → RelT A (returnT (⟦ d ⟧ᵍ fmt)) (liftFn fmt (realize-global {X = X} d) y)
bridge-g {ctx = ctx} {X = X} (g-int n) y = int-bridge {ctx = ctx} {X = X} n y
-- The float leaf reduces the same way and even more directly: `⟦ g-float … ⟧ᵍ`
-- IS `d`, and `realize-global (g-float … d …) fits-float d ∘ terminal`,
-- whose `evalᴰ` is `d` — so both sides are `([] , d)` definitionally.
bridge-g (g-float i f l p) y k = refl , refl
-- PLAN 0.73 F3 / D120's other half. Both leaves reduce exactly as their
-- unnegated twins do — `⟦_⟧ᵍ` and `realize-global` name the SAME folded
-- payload (`- n`, `negate (decimalOf i f l)`), so neither side has anything
-- the other lacks and both are `([] , v)` definitionally.
bridge-g (g-neg-int n) y k = refl , refl
bridge-g (g-neg-float i f l p) y k = refl , refl
-- `liftFn (realize-global d) y` is APPLIED to `y`, so `liftFn` unfolds and a
-- `rewrite` of the (funext) reduction can't fire; convert with `subst (RelT …)`
-- over the reduction applied at `y` (`cong (λ h → h y)`).
bridge-g {X = X} (g-terminal a b) y =
  subst (RelT Unit (returnT tt))
        (cong (λ h → h y) (sym (liftFn-terminal {X})))
        (λ n → refl , tt)
-- Compound cases: the pure side's trace is `[]`, the `liftFn` side's is
-- `projTrace (sub) n ++ …`, equal by the sub-relation's trace half; the value
-- follows from the sub-relation's value half.
bridge-g {X = X} (g-pair {A = A₁} {B = A₂} ga gb) y =
  subst (RelT (A₁ * A₂) (returnT ((⟦ ga ⟧ᵍ fmt) , (⟦ gb ⟧ᵍ fmt))))
        (cong (λ h → h y) (sym (liftFn-pair {X} {A₁} {A₂} (realize-global ga) (realize-global gb))))
        (λ n → cong₂ (λ x z → x ++ (z ++ [])) (proj₁ (bridge-g ga y n)) (proj₁ (bridge-g gb y n))
             , (proj₂ (bridge-g ga y n) , proj₂ (bridge-g gb y n)))
bridge-g {X = X} (g-inl {A = A₁} {B = A₂} ga) y =
  subst (RelT (A₁ + A₂) (returnT (inj₁ (⟦ ga ⟧ᵍ fmt))))
        (cong (λ h → h y)
          (sym (trans (liftFn-∘ {A₁} {A₁ + A₂} {X} (IR.inl IR.Heap) (realize-global ga))
                      (cong (λ hh → λ a → liftFn fmt {X} {A₁} (realize-global ga) a >>=T hh) (liftFn-inl {A₁} {A₂})))))
        (λ n → cong (_++ []) (proj₁ (bridge-g ga y n)) , proj₂ (bridge-g ga y n))
bridge-g {X = X} (g-inr {A = A₁} {B = A₂} gb) y =
  subst (RelT (A₁ + A₂) (returnT (inj₂ (⟦ gb ⟧ᵍ fmt))))
        (cong (λ h → h y)
          (sym (trans (liftFn-∘ {A₂} {A₁ + A₂} {X} (IR.inr IR.Heap) (realize-global gb))
                      (cong (λ hh → λ a → liftFn fmt {X} {A₂} (realize-global gb) a >>=T hh) (liftFn-inr {A₂} {A₁})))))
        (λ n → cong (_++ []) (proj₁ (bridge-g gb y n)) , proj₂ (bridge-g gb y n))
-- g-In: `realize-global (g-In dec garg) = In wfF Heap ∘ realize-global garg`,
-- so the RHS binds the (recursively bridged) `garg` then applies the pure `In`.
-- Value via `wfF-layer-eq`+`cong` (as `in-app-bridge`); trace = the sub-trace
-- (`In` adds none) modulo `++ []`.
bridge-g {X = X} (g-In {F = F} {wfF = wfF} dec garg) y =
  subst (RelT (μ-type F) (returnT (in-value (⟦ garg ⟧ᵍ fmt))))
        (cong (λ h → h y) (sym g-In-reduce))
        (λ k → trans (proj₁ (bridge-g garg y k)) (sym (++-identityʳ _))
             , cong in-value (wfF-layer-eq wfF (λ r → r) (proj₂ (bridge-g garg y k))))
  where
    g-In-reduce : liftFn fmt {X} {μ-type F} (realize-global (g-In dec garg))
                ≡ (λ a → liftFn fmt {X} {⟦ F ⟧T (μ-type F)} (realize-global garg) a >>=T (λ w → returnT (in-value w)))
    g-In-reduce =
      trans (cong (liftFn fmt {X} {μ-type F}) (subst-∘-move (⌊⟧T-commute F (μ-type F))
                            (IR.In (wf-⌊⌋ wfF) IR.Heap) (realize-global garg)))
      (trans (liftFn-∘ {⟦ F ⟧T (μ-type F)} {μ-type F} {X} (In-ir wfF) (realize-global garg))
             (cong (λ h → λ a → liftFn fmt {X} {⟦ F ⟧T (μ-type F)} (realize-global garg) a >>=T h)
                   (extensionality (liftFn-In wfF))))

------------------------------------------------------------------------
-- The MORPHISM realm, DISCHARGED — structural (`RelT-return`/`RelT-bind` +
-- direct `∀ n` for the constructor-wrapping cases); `m-const` routes to
-- `bridge-g`; `m-cata`/`m-named` via the leaves above.
------------------------------------------------------------------------

-- `liftFn (realize-morph d)` is applied to `b` when `RelV (A⇒B) f g` unfolds
-- (`g b`), so `liftFn` reduces and a `rewrite` can't fire; convert with `subst`
-- over the (funext) reduction at the RelV level.
wrapM : ∀ {ctx : NamedCtx} {e A B} {π : Purity} (d : ctx ⊢ᵐ e ∶ A ⇨[ π ] B)
          {g : ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ}
      → liftFn fmt (realize-morph d) ≡ g
      → RelV (A ⇒[ mk-kind Many π ] B) ((⟦ d ⟧ᵐ fmt)) g
      → RelV (A ⇒[ mk-kind Many π ] B) ((⟦ d ⟧ᵐ fmt)) (liftFn fmt (realize-morph d))
wrapM {A = A} {B = B} {π = π} d eq body =
  subst (RelV (A ⇒[ mk-kind Many π ] B) ((⟦ d ⟧ᵐ fmt))) (sym eq) body

bridge-m : ∀ {ctx : NamedCtx} {e A B} {π : Purity} (d : ctx ⊢ᵐ e ∶ A ⇨[ π ] B)
         → RelV (A ⇒[ mk-kind Many π ] B) ((⟦ d ⟧ᵐ fmt)) (liftFn fmt (realize-morph d))
bridge-m d@(m-id {T = T} _ _)          = wrapM d (liftFn-id {T})       (λ rv n → refl , rv)
bridge-m d@(m-fst {A = A} {B = B} _ _) = wrapM d (liftFn-fst {A} {B})  (λ rv n → refl , proj₁ rv)
bridge-m d@(m-snd {A = A} {B = B} _ _) = wrapM d (liftFn-snd {A} {B})  (λ rv n → refl , proj₂ rv)
bridge-m d@(m-terminal {A = A} _ _)    = wrapM d (liftFn-terminal {A}) (λ _ n → refl , tt)
bridge-m (m-initial _ _) {a = ()}
bridge-m d@(m-inl {A = A} {B = B} _ _) = wrapM d (liftFn-inl {A} {B})  (λ rv n → refl , rv)
bridge-m d@(m-inr {A = A} {B = B} _ _) = wrapM d (liftFn-inr {B} {A})  (λ rv n → refl , rv)
bridge-m d@(m-compose {A = A} {B = B} {C = C} _ df dg) =
  wrapM d (liftFn-∘ {B} {C} {A} (realize-morph df) (realize-morph dg)) (λ rv n →
    cong₂ _++_ (proj₁ (bridge-m dg rv n)) (proj₁ (bridge-m df (proj₂ (bridge-m dg rv n)) n))
  , proj₂ (bridge-m df (proj₂ (bridge-m dg rv n)) n))
bridge-m (m-case {A = A} {B = B} {C = C} df dg) {a = inj₁ a} {b = inj₁ b} rv =
  subst (RelT C ((⟦ df ⟧ᵐ fmt) a))
        (sym (liftFn-case-inj₁ {A} {B} {C} (realize-morph df) (realize-morph dg) b)) (bridge-m df rv)
bridge-m (m-case {A = A} {B = B} {C = C} df dg) {a = inj₂ a} {b = inj₂ b} rv =
  subst (RelT C ((⟦ dg ⟧ᵐ fmt) a))
        (sym (liftFn-case-inj₂ {A} {B} {C} (realize-morph df) (realize-morph dg) b)) (bridge-m dg rv)
bridge-m (m-case df dg) {a = inj₁ _} {b = inj₂ _} ()
bridge-m (m-case df dg) {a = inj₂ _} {b = inj₁ _} ()
bridge-m d@(m-pair {A = A} {B = B} {C = C} df dg) =
  wrapM d (liftFn-pair {A} {B} {C} (realize-morph df) (realize-morph dg)) (λ rv n →
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-m df rv n)) (proj₁ (bridge-m dg rv n))
  , (proj₂ (bridge-m df rv n) , proj₂ (bridge-m dg rv n)))
bridge-m d@(m-curry {A = A} {B = B} {C = C} df) =
  wrapM d (liftFn-curry {A} {B} {C} {mk-kind Many pure} (realize-morph df))
          (λ rv n → refl , (λ rb → bridge-m df (rv , rb)))
bridge-m (m-const gd) {b = b} _ = bridge-g gd b
bridge-m (m-cata {wfF = wfF} _ alg) {a = a} {b = b} rv =
  cata-bridge {wfF = wfF} (⟦ alg ⟧ᵐ fmt) (realize-morph alg) (bridge-m alg) {a = a} {b = b} rv
bridge-m {A = A} {B = B} (m-named {x = x} _ _ _ bA cB) {a = a} {b = b} rv =
  sigop-bridge {A = A} {B = B} {cn = bare x} bA cB {a = a} {b = b} rv
bridge-m {A = A} {B = B} (m-named-resolved {cn = cn} _ bA cB) {a = a} {b = b} rv =
  sigop-bridge {A = A} {B = B} {cn = cn} bA cB {a = a} {b = b} rv

------------------------------------------------------------------------
-- The CHECK / INFER realms, DISCHARGED — mutual structural induction on the
-- derivation, mirroring `Meaning.⟦_⟧ᵢ`/`⟦_⟧ᶜ` (LHS) vs `SD.⟦ realize(-infer) _ ⟧ˢ`
-- (RHS) clause-for-clause. Same technique as `bridge-g`/`bridge-m`: inline the
-- `∀ n`, `cong`/`cong₂` on the `++`-traces, project the value half. Genuinely
-- higher-order leaves route to the discharged reflexivity/`cata-bridge` lemmas above.
------------------------------------------------------------------------

-- Propositional equality of a comparison result (`Unit + Unit`) lifts to `RelV`.
≡→RelV-⊎⊤ : ∀ {x y : ⟦ Unit + Unit ⟧ᴰ} → x ≡ y → RelV (Unit + Unit) x y
≡→RelV-⊎⊤ {inj₁ _} refl = tt
≡→RelV-⊎⊤ {inj₂ _} refl = tt

-- `SD.⟦_⟧ˢ` ignores the usage index, so a usage-coercing `subst` (as in
-- `realize`'s telescope poly clause) is invisible to the denotation. Lets the
-- poly bridge case see through `realize`'s `subst uEq (morph-app …)`.
SD-subst-usage : ∀ {n} {Γ : Ctx n} {A} {Ψ Ψ' : Usage n} {eq : Ψ ≡ Ψ'}
                   {e : Expr Γ Ψ A} {dγ}
  → (SD.⟦ subst (λ u → Expr Γ u A) eq e ⟧ˢ fmt) dγ ≡ (SD.⟦ e ⟧ˢ fmt) dγ
SD-subst-usage {eq = refl} = refl

bridge-i : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ)
           {dγ₁ dγ₂ : Env ctx} (re : RelEnv (NamedCtx.debruijn ctx) dγ₁ dγ₂)
         → RelT A ((⟦ d ⟧ᵢ fmt) dγ₁) ((SD.⟦ realize-infer d ⟧ˢ fmt) dγ₂)
bridge-c : ∀ {ctx : NamedCtx} {e A Ψ} (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ)
           {dγ₁ dγ₂ : Env ctx} (re : RelEnv (NamedCtx.debruijn ctx) dγ₁ dγ₂)
         → RelT A ((⟦ d ⟧ᶜ fmt) dγ₁) ((SD.⟦ realize d ⟧ˢ fmt) dγ₂)

-- Literals — pure `returnT`, identical values.
bridge-i (t-int _)   re k = refl , refl
bridge-i (t-float _ _ _ _) re k = refl , refl
-- PLAN 0.73 F3. A LEAF, like `t-float` above and unlike `t-neg` below: both
-- sides are the literal `round fmt (negate (decimalOf i f l))`, because
-- `realize-infer` had no float `neg` to keep (`Surface.neg` is Int-typed).
-- The `Int` fold could keep one and pays `⊝-fromℤ` for it in `RealizeAgrees`;
-- here there is nothing to reconcile.
bridge-i (t-neg-float _ _ _ _) re k = refl , refl
bridge-i (t-str _)   re k = refl , refl
bridge-i t-unit      re k = refl , tt
bridge-i t-unit-var  re k = refl , tt

-- Local variable — `svarᴰ (svar i)` (LHS) and `SD.⟦ var i ⟧ˢ` (RHS) both peel to
-- the positional lookup; `rel-lookup` relates the two envs at position `i`.
bridge-i (t-var-local {eV = svar i} _ _) re k = refl , rel-lookup _ i re

-- Named value references — the sigop-reference leaf (dispatch on result type).
bridge-i {ctx = ctx} (t-var-qualified {T = A} _ conc)   {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ conc dγ₂
bridge-i {ctx = ctx} (t-var-resolved {T = A} _ conc)    {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ conc dγ₂
bridge-i {ctx = ctx} (t-var-import {T = A} _ _ _ conc)  {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ conc dγ₂

-- Plan 0.58 / D071: infer-mode ground telescope reference — same shape as the
-- check-mode `t-var-poly-instantiate` case of `bridge-c` (below): both sides
-- δ-reduce to the closed body (⟦_⟧ᵢ = ⟦ bodyD ⟧ᶜ tt; realize-infer inlines
-- `morph-app (elaborate (realize bodyD)) unit`), so RECURSE on the body with
-- the empty related env; `faithful` closes the evalᴰ↔SD gap.
bridge-i {ctx = ctx} (t-var-poly-instantiate-infer _ _ _ _ _ _ _ bodyD) {dγ₂ = dγ₂} re k
  rewrite SD-subst-usage {Γ = NamedCtx.debruijn ctx} {eq = poly-usage-eq}
                         {e = morph-app (elaborate IR.Heap (realize bodyD)) unit} {dγ = dγ₂}
  rewrite faithful (realize bodyD) tt k = bridge-c bodyD {dγ₁ = tt} {dγ₂ = tt} tt k

-- Annotation switches to check mode.
bridge-i (t-annot d) re = bridge-c d re

-- Pair — two sequenced infers, product value.
bridge-i (t-pair da db) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i da re k)) (proj₁ (bridge-i db re k))
  , (proj₂ (bridge-i da re k) , proj₂ (bridge-i db re k))

-- Negation — bind then a pure `semM neg-info fmt`.
bridge-i (t-neg d) re k =
    cong (_++ []) (proj₁ (bridge-i d re k))
  , cong (semM neg-info fmt) (proj₂ (bridge-i d re k))

-- Let — thread the bound value into the extended related env.
bridge-i (t-let d₁ d₂) re k =
  let b1 = bridge-i d₁ re k
      b2 = bridge-i d₂ (re , proj₂ b1) k
  in cong₂ _++_ (proj₁ b1) (proj₁ b2) , proj₂ b2

-- Case — split on the (related) scrutinee's injection; recurse in the branch.
bridge-i (t-case ds dl dr) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re k
  with valueT ((⟦ ds ⟧ᵢ fmt) dγ₁) k | valueT ((SD.⟦ realize-infer ds ⟧ˢ fmt) dγ₂) k | bridge-i ds re k
... | inj₁ a | inj₁ a' | tr , rv =
      cong₂ _++_ tr (proj₁ (bridge-i dl (re , rv) k)) , proj₂ (bridge-i dl (re , rv) k)
... | inj₂ b | inj₂ b' | tr , rv =
      cong₂ _++_ tr (proj₁ (bridge-i dr (re , rv) k)) , proj₂ (bridge-i dr (re , rv) k)
... | inj₁ a | inj₂ b' | tr , ()
... | inj₂ b | inj₁ a' | tr , ()

-- Arithmetic binops — bind both, pure `semM <op>-info` (Int value = `≡`).
bridge-i (t-binop-arith {op = OpAdd} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM add-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpSub} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM sub-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpMul} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM mul-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpDiv} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM div-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpMod} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM mod-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith {op = OpLt} () _ _)
bridge-i (t-binop-arith {op = OpLe} () _ _)
bridge-i (t-binop-arith {op = OpGt} () _ _)
bridge-i (t-binop-arith {op = OpGe} () _ _)
bridge-i (t-binop-arith {op = OpEq} () _ _)
bridge-i (t-binop-arith {op = OpNe} () _ _)

-- Comparison binops — bind both, pure `semM <op>-info` (Unit+Unit value).
bridge-i (t-binop-cmp {op = OpLt} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM lt-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpLe} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM le-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpGt} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM gt-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpGe} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM ge-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpEq} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM eq-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpNe} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , ≡→RelV-⊎⊤ (cong₂ (λ a b → semM ne-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k)))
bridge-i (t-binop-cmp {op = OpAdd} () _ _)
bridge-i (t-binop-cmp {op = OpSub} () _ _)
bridge-i (t-binop-cmp {op = OpMul} () _ _)
bridge-i (t-binop-cmp {op = OpDiv} () _ _)
bridge-i (t-binop-cmp {op = OpMod} () _ _)

-- Polymorphic-builtin applications — RHS is `morph-app <ir> …`; each `evalᴰ <ir>`
-- reduces to the same pure post-op the LHS applies (modulo the `++ []` bookkeeping).
bridge-i {A = A} (t-id-app d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT A ((⟦ t-id-app d ⟧ᵢ fmt) dγ₁))
        (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) dγ₂ >>=T_) (liftFn-id {A})))
        (λ k → trans (proj₁ (bridge-i d re k)) (sym (++-identityʳ _)) , proj₂ (bridge-i d re k))
bridge-i (t-fst-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT A ((⟦ t-fst-app d ⟧ᵢ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) dγ₂ >>=T_) (liftFn-fst {A} {B})))
        (λ k → cong (_++ []) (proj₁ (bridge-i d re k)) , proj₁ (proj₂ (bridge-i d re k)))
bridge-i (t-snd-app {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT B ((⟦ t-snd-app d ⟧ᵢ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) dγ₂ >>=T_) (liftFn-snd {A} {B})))
        (λ k → cong (_++ []) (proj₁ (bridge-i d re k)) , proj₂ (proj₂ (bridge-i d re k)))
bridge-i (t-terminal-app {T = T} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT Unit ((⟦ t-terminal-app d ⟧ᵢ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) dγ₂ >>=T_) (liftFn-terminal {T})))
        (λ k → cong (_++ []) (proj₁ (bridge-i d re k)) , tt)
bridge-i (t-apply-app-infer {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT B ((⟦ t-apply-app-infer d ⟧ᵢ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer d ⟧ˢ fmt) dγ₂ >>=T_) (liftFn-apply {A} {B} {mk-kind Many pure})))
        (λ k → let bd = bridge-i d re k
                   inner = proj₁ (proj₂ bd) (proj₂ (proj₂ bd)) k
               in cong₂ _++_ (proj₁ bd) (proj₁ inner) , proj₂ inner)

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
bridge-c (t-apply-check {A = A} {B = B} dp) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT B ((⟦ t-apply-check dp ⟧ᶜ fmt) dγ₁)) (sym (cong ((SD.⟦ realize-infer dp ⟧ˢ fmt) dγ₂ >>=T_) (liftFn-apply {A} {B} {mk-kind Many pure})))
        (λ k → let bd = bridge-i dp re k
                   inner = proj₁ (proj₂ bd) (proj₂ (proj₂ bd)) k
               in cong₂ _++_ (proj₁ bd) (proj₁ inner) , proj₂ inner)
bridge-c (t-inl-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT (A + B) ((⟦ t-inl-app-check {A = A} {B = B} d ⟧ᶜ fmt) dγ₁)) (sym (cong ((SD.⟦ realize d ⟧ˢ fmt) dγ₂ >>=T_) (liftFn-inl {A} {B})))
        (λ k → cong (_++ []) (proj₁ (bridge-c d re k)) , proj₂ (bridge-c d re k))
bridge-c (t-inr-app-check {A = A} {B = B} d) {dγ₁ = dγ₁} {dγ₂ = dγ₂} re =
  subst (RelT (A + B) ((⟦ t-inr-app-check {A = A} {B = B} d ⟧ᶜ fmt) dγ₁)) (sym (cong ((SD.⟦ realize d ⟧ˢ fmt) dγ₂ >>=T_) (liftFn-inr {B} {A})))
        (λ k → cong (_++ []) (proj₁ (bridge-c d re k)) , proj₂ (bridge-c d re k))
bridge-c (t-initial-app-check d) {dγ₁ = dγ₁} re k = ⊥-elim (valueT ((⟦ d ⟧ᶜ fmt) dγ₁) k)
bridge-c (t-subsume d) re = bridge-c d re
bridge-c (t-arg-driven-app-check _ darg df) re k =
  let bf = bridge-c df re k
      bx = bridge-i darg re k
      inner = proj₂ bf (proj₂ bx) k
  in cong₂ _++_ (proj₁ bf) (cong₂ _++_ (proj₁ bx) (proj₁ inner)) , proj₂ inner
-- Plan 0.58 (telescope): ⟦ t-var-poly ⟧ᶜ dγ₁ = ⟦ bodyD ⟧ᶜ tt and
-- SD.⟦ realize d ⟧ˢ dγ₂ = evalᴰ (elaborate Heap (realize bodyD)) tt (morph-app+unit,
-- env-independent by def). So the bridge RECURSES on the body (bodyD is closed ⇒
-- empty RelEnv `tt`); `faithful (realize bodyD)` closes the evalᴰ↔SD gap.
bridge-c {ctx = ctx} (t-var-poly-instantiate _ _ _ _ _ _ bodyD) {dγ₂ = dγ₂} re k
  rewrite SD-subst-usage {Γ = NamedCtx.debruijn ctx} {eq = poly-usage-eq}
                         {e = morph-app (elaborate IR.Heap (realize bodyD)) unit} {dγ = dγ₂}
  rewrite faithful (realize bodyD) tt k = bridge-c bodyD {dγ₁ = tt} {dγ₂ = tt} tt k
