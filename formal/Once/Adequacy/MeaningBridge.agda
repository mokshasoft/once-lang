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
open import Data.Sum using (inj₁; inj₂; [_,_]′; _⊎_)
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

open import Once.Type using (Type; Purity; mk-kind; Many; pure; eff; _⇒[_]_; _+_; _*_; μ-type; ⟦_⟧T; Functor; Int; Unit)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Str; base-Buffer; base-Prod; base-Sum;
  IsConcrete; con-base; con-fun)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.Semantics.Machine using (sem-In; coerce-functor; sem-cata)
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
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_;
  t-id-check; t-fst-check; t-snd-check; t-terminal-morph-check;
  t-initial-morph-check; t-inl-morph-check; t-inr-morph-check;
  t-compose-check; t-case-copair-check; t-pair-morph-check;
  t-curry-check; t-cata-check;
  t-int; t-float; t-str; t-unit; t-unit-var; t-var-local; t-var-qualified;
  t-var-resolved; t-var-import; t-annot; t-pair; t-neg; t-neg-float; t-binop-arith-float; t-binop-arith-float-il; t-binop-arith-float-ir; t-let; t-case;
  t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
  t-terminal-app; t-apply-app-infer; t-app; t-effApp;
  t-embed; t-lam; t-pair-lit-check;
  t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
  t-initial-app-check; t-subsume; t-arg-driven-app-check; t-var-poly-instantiate;
  t-var-poly-instantiate-infer)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ;
  lookupᴰ; Env; cata-sem; sigOpValᴰ; sigOpRefᴰ; svarᴰ; in-value; named-sem)
open import Once.Adequacy.CataErased fmt using (liftFn-SigOp)
open import Once.Adequacy.LiftFnReduce fmt using
  (liftFn-id; liftFn-fst; liftFn-snd; liftFn-terminal; liftFn-inl; liftFn-inr;
   liftFn-∘; liftFn-pair; liftFn-curry; liftFn-case-inj₁; liftFn-case-inj₂; liftFn-apply)
import Once.IR as IR
open import Once.Arith.SigOp.Builders using (value-info;
  add-info; sub-info; mul-info; div-info; mod-info; neg-info;
  fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info;
  lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.CanonicalName using (CanonicalName; bare)
open import Once.Denotation.Realize using (realize; realize-infer; realize-morph; realize-global; poly-usage-eq)
open import Once.Adequacy.SourceFaithful fmt using (faithful)
open import Once.Surface.Elaborate using (elaborate)
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.ThinSound using (weaken-⟦⟧)
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

-- D127: `int-bridge`, `bridge-g`, `wrapM` and `bridge-m` are DELETED with the
-- two realms they bridged. Their content did not vanish — it moved into
-- `bridge-c`'s new clauses below, which relate the SAME meanings; the point-free
-- leaves reuse the old `bridge-m` bodies verbatim, and the combinators become
-- `RelT-bind`/`RelT-return` congruences now that both sides bind their arms.

-- D127: `case`'s value relation. `RelV (A + B)` is `⊥` on mismatched
-- injections, so the two absurd clauses are the whole of the disjointness.
-- D131: SD's cata fold IS `cata-sem` of the bound closure. `cata-ev-algˢ n
-- (returnT c)` collapses to `cata-ev-algᴰ-D n c` by the monad's left identity,
-- which is definitional here.
sd-fold-is-cata-sem : ∀ {F : Functor} {A : Type} (wf : WellFormedF F)
    (c : ⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ) (x : ⟦ μ-type F ⟧ᴰ)
  → (λ n → let r = sem-cata wf (SD.cata-ev-algˢ {F} {A} n (returnT c)) x
           in (proj₁ r , proj₂ r))
    ≡ cata-sem wf c x
sd-fold-is-cata-sem wf c x = refl

-- The scrutinees are EXPLICIT: as a term of the arrow relation's Π type Agda
-- cannot see which injection to split on, so the caller passes them.
copair-rel : ∀ {A B C : Type} {vf vf' : ⟦ A ⟧ᴰ → T ⟦ C ⟧ᴰ} {vg vg' : ⟦ B ⟧ᴰ → T ⟦ C ⟧ᴰ}
           → (∀ {a b} → RelV A a b → RelT C (vf a) (vf' b))
           → (∀ {a b} → RelV B a b → RelT C (vg a) (vg' b))
           → ∀ (ab ab' : ⟦ A ⟧ᴰ ⊎ ⟦ B ⟧ᴰ) → RelV (A + B) ab ab'
           → RelT C ([ vf , vg ]′ ab) ([ vf' , vg' ]′ ab')
copair-rel rf rg (inj₁ _) (inj₁ _) rv = rf rv
copair-rel rf rg (inj₂ _) (inj₂ _) rv = rg rv
copair-rel rf rg (inj₁ _) (inj₂ _) ()
copair-rel rf rg (inj₂ _) (inj₁ _) ()

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
bridge-i (t-var-local {eV = svar i} _) re k = refl , rel-lookup _ i re

-- Named value references — the sigop-reference leaf (dispatch on result type).
bridge-i {ctx = ctx} (t-var-qualified {T = A} _ conc)   {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ conc dγ₂
bridge-i {ctx = ctx} (t-var-resolved {T = A} _ conc)    {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ conc dγ₂
bridge-i {ctx = ctx} (t-var-import {T = A} _ _ conc)  {dγ₂ = dγ₂} re = sigop-ref-bridge {Γ = NamedCtx.debruijn ctx} {A = A} _ conc dγ₂

-- Plan 0.58 / D071: infer-mode ground telescope reference — same shape as the
-- check-mode `t-var-poly-instantiate` case of `bridge-c` (below): both sides
-- δ-reduce to the closed body (⟦_⟧ᵢ = ⟦ bodyD ⟧ᶜ tt; realize-infer inlines
-- `morph-app (elaborate (realize bodyD)) unit`), so RECURSE on the body with
-- the empty related env; `faithful` closes the evalᴰ↔SD gap.
bridge-i {ctx = ctx} (t-var-poly-instantiate-infer _ _ _ _ _ _ bodyD) {dγ₂ = dγ₂} re k
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
-- PLAN 0.75 F4: the float family, and the SAME two `cong₂`s — which is the
-- content: both realms sequence the operands identically and differ only in
-- which `semM` closes over them.
bridge-i (t-binop-arith-float {op = OpAdd} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fadd-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float {op = OpSub} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fsub-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float {op = OpMul} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fmul-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float {op = OpDiv} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fdiv-info fmt (a , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float {op = OpMod} () _ _)
bridge-i (t-binop-arith-float {op = OpLt} () _ _)
bridge-i (t-binop-arith-float {op = OpLe} () _ _)
bridge-i (t-binop-arith-float {op = OpGt} () _ _)
bridge-i (t-binop-arith-float {op = OpGe} () _ _)
bridge-i (t-binop-arith-float {op = OpEq} () _ _)
bridge-i (t-binop-arith-float {op = OpNe} () _ _)
-- D125: the mixed forms. The trace SHAPE differs from the unmixed clauses —
-- `i2f` is its own bind, so it contributes an `++ []` on whichever side widens
-- — and the `cong₂` says exactly where. It is still one `cong₂` and not a
-- `trans` chain, because `⟦_⟧ᵢ` was written to mirror the elaborated term's
-- binds rather than to inline the conversion.
bridge-i (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) re k =
    cong₂ (λ x y → (x ++ []) ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fadd-info fmt ((semM i2f-info fmt a) , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) re k =
    cong₂ (λ x y → (x ++ []) ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fsub-info fmt ((semM i2f-info fmt a) , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) re k =
    cong₂ (λ x y → (x ++ []) ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fmul-info fmt ((semM i2f-info fmt a) , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) re k =
    cong₂ (λ x y → (x ++ []) ++ (y ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fdiv-info fmt ((semM i2f-info fmt a) , b)) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float-il {op = OpMod} () _ _)
bridge-i (t-binop-arith-float-il {op = OpLt} () _ _)
bridge-i (t-binop-arith-float-il {op = OpLe} () _ _)
bridge-i (t-binop-arith-float-il {op = OpGt} () _ _)
bridge-i (t-binop-arith-float-il {op = OpGe} () _ _)
bridge-i (t-binop-arith-float-il {op = OpEq} () _ _)
bridge-i (t-binop-arith-float-il {op = OpNe} () _ _)
bridge-i (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ ((y ++ []) ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fadd-info fmt (a , (semM i2f-info fmt b))) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ ((y ++ []) ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fsub-info fmt (a , (semM i2f-info fmt b))) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ ((y ++ []) ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fmul-info fmt (a , (semM i2f-info fmt b))) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) re k =
    cong₂ (λ x y → x ++ ((y ++ []) ++ [])) (proj₁ (bridge-i d₁ re k)) (proj₁ (bridge-i d₂ re k))
  , cong₂ (λ a b → semM fdiv-info fmt (a , (semM i2f-info fmt b))) (proj₂ (bridge-i d₁ re k)) (proj₂ (bridge-i d₂ re k))
bridge-i (t-binop-arith-float-ir {op = OpMod} () _ _)
bridge-i (t-binop-arith-float-ir {op = OpLt} () _ _)
bridge-i (t-binop-arith-float-ir {op = OpLe} () _ _)
bridge-i (t-binop-arith-float-ir {op = OpGt} () _ _)
bridge-i (t-binop-arith-float-ir {op = OpGe} () _ _)
bridge-i (t-binop-arith-float-ir {op = OpEq} () _ _)
bridge-i (t-binop-arith-float-ir {op = OpNe} () _ _)
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

-- D127: the POINT-FREE LEAVES. `realize` sends each to `lift-morphism` of the
-- plain categorical generator, so these are the OLD `bridge-m` bodies verbatim,
-- re-aimed at `⊢ᶜ` — the `subst` moves `liftFn`'s funext-reduction out of the
-- way exactly as `wrapM` used to.
bridge-c (t-id-check {T = T} {π = π}) re k =
  refl , subst (RelV (T ⇒[ mk-kind Many π ] T) (λ a → returnT a))
               (sym (liftFn-id {T})) (λ rv n → refl , rv)
bridge-c (t-fst-check {A = A} {B = B} {π = π}) re k =
  refl , subst (RelV ((A * B) ⇒[ mk-kind Many π ] A) (λ ab → returnT (proj₁ ab)))
               (sym (liftFn-fst {A} {B})) (λ rv n → refl , proj₁ rv)
bridge-c (t-snd-check {A = A} {B = B} {π = π}) re k =
  refl , subst (RelV ((A * B) ⇒[ mk-kind Many π ] B) (λ ab → returnT (proj₂ ab)))
               (sym (liftFn-snd {A} {B})) (λ rv n → refl , proj₂ rv)
bridge-c (t-terminal-morph-check {A = A} {π = π}) re k =
  refl , subst (RelV (A ⇒[ mk-kind Many π ] Once.Type.Unit) (λ _ → returnT tt))
               (sym (liftFn-terminal {A})) (λ _ n → refl , tt)
bridge-c (t-initial-morph-check) re k = refl , (λ { {a = ()} })
bridge-c (t-inl-morph-check {A = A} {B = B} {π = π}) re k =
  refl , subst (RelV (A ⇒[ mk-kind Many π ] (A + B)) (λ a → returnT (inj₁ a)))
               (sym (liftFn-inl {A} {B})) (λ rv n → refl , rv)
bridge-c (t-inr-morph-check {A = A} {B = B} {π = π}) re k =
  refl , subst (RelV (B ⇒[ mk-kind Many π ] (A + B)) (λ b → returnT (inj₂ b)))
               (sym (liftFn-inr {B} {A})) (λ rv n → refl , rv)

-- D127: the COMBINATORS. Both sides now bind their arms and then build the
-- same function from the results, so each is a `RelT-bind`/`RelT-return`
-- congruence — no realm, no extraction, no per-shape reasoning.
bridge-c (t-compose-check {A = A} {B = B} {C = C} {π = π} _ df dg) re =
  RelT-bind {A = B ⇒[ mk-kind Many π ] C} {B = A ⇒[ mk-kind Many π ] C}
            (bridge-c df re) (λ {f₁} {f₂} rf →
  RelT-bind {A = A ⇒[ mk-kind Many π ] B} {B = A ⇒[ mk-kind Many π ] C}
            (bridge-c dg re) (λ {g₁} {g₂} rg →
  RelT-return {A = A ⇒[ mk-kind Many π ] C}
              {x = λ a → g₁ a >>=T f₁} {y = λ a → g₂ a >>=T f₂}
              (λ rv → RelT-bind {A = B} {B = C} (rg rv) rf)))
bridge-c (t-case-copair-check {A = A} {B = B} {C = C} {π = π} df dg) re =
  RelT-bind {A = A ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-c df re) (λ {c₁} {c₂} rf →
  RelT-bind {A = B ⇒[ mk-kind Many π ] C} {B = (A + B) ⇒[ mk-kind Many π ] C}
            (bridge-c dg re) (λ {d₁} {d₂} rg →
  RelT-return {A = (A + B) ⇒[ mk-kind Many π ] C}
              {x = λ ab → [ c₁ , d₁ ]′ ab} {y = λ ab → [ c₂ , d₂ ]′ ab}
              (λ {ab} {ab'} rv →
                 copair-rel {A} {B} {C} {vf = c₁} {vf' = c₂} {vg = d₁} {vg' = d₂}
                            rf rg ab ab' rv)))
bridge-c (t-pair-morph-check {A = A} {B = B} {C = C} df dg) re =
  RelT-bind {A = A ⇒[ mk-kind Many Once.Type.pure ] B}
            {B = A ⇒[ mk-kind Many Once.Type.pure ] (B * C)}
            (bridge-c df re) (λ {f₁} {f₂} rf →
  RelT-bind {A = A ⇒[ mk-kind Many Once.Type.pure ] C}
            {B = A ⇒[ mk-kind Many Once.Type.pure ] (B * C)}
            (bridge-c dg re) (λ {g₁} {g₂} rg →
  RelT-return {A = A ⇒[ mk-kind Many Once.Type.pure ] (B * C)}
              {x = λ a → f₁ a >>=T λ b → g₁ a >>=T λ c → returnT (b , c)}
              {y = λ a → f₂ a >>=T λ b → g₂ a >>=T λ c → returnT (b , c)}
              (λ rv → RelT-bind {A = B} {B = B * C} (rf rv) (λ {b₁} {b₂} rb →
                       RelT-bind {A = C} {B = B * C} (rg rv) (λ {e₁} {e₂} rc →
                         RelT-return {A = B * C} {x = b₁ , e₁} {y = b₂ , e₂} (rb , rc))))))
bridge-c (t-curry-check {A = A} {B = B} {C = C} df) re =
  RelT-bind {A = (A * B) ⇒[ mk-kind Many Once.Type.pure ] C}
            {B = A ⇒[ mk-kind Many Once.Type.pure ] (B ⇒[ mk-kind Many Once.Type.pure ] C)}
            (bridge-c df re) (λ {c₁} {c₂} rf →
  RelT-return {A = A ⇒[ mk-kind Many Once.Type.pure ] (B ⇒[ mk-kind Many Once.Type.pure ] C)}
              {x = λ a → returnT (λ b → c₁ (a , b))}
              {y = λ a → returnT (λ b → c₂ (a , b))}
              (λ {a} {b} rv →
                 RelT-return {A = B ⇒[ mk-kind Many Once.Type.pure ] C}
                             {x = λ z → c₁ (a , z)} {y = λ z → c₂ (b , z)}
                             (λ rv' → rf (rv , rv'))))
-- The cata: the algebra is BOUND on both sides (D131), so this is a bind over
-- the algebra followed by the fold congruence `cata-bridge` — which is exactly
-- why that lemma is now stated over two ALGEBRAS.
bridge-c (t-cata-check {F = F} {A = A} {π = π} wfF dalg) re =
  RelT-bind {A = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A}
            {B = μ-type F ⇒[ mk-kind Many π ] A}
            (bridge-c dalg tt) (λ {c₁} {c₂} ralg →
  RelT-return {A = μ-type F ⇒[ mk-kind Many π ] A}
              {x = cata-sem wfF c₁}
              {y = λ x → λ n → let r = sem-cata wfF (SD.cata-ev-algˢ {F} {A} n (returnT c₂)) x
                               in (proj₁ r , proj₂ r)}
              (λ {a} {b} rv → cata-bridge {A' = A} {wfF = wfF} c₁ c₂ ralg rv))
bridge-c (t-embed d) re = bridge-i d re
bridge-c (t-lam _ d) re k = refl , λ {a} {b} rv → bridge-c d (re , rv)
bridge-c (t-pair-lit-check da db) re k =
    cong₂ (λ x y → x ++ (y ++ [])) (proj₁ (bridge-c da re k)) (proj₁ (bridge-c db re k))
  , (proj₂ (bridge-c da re k) , proj₂ (bridge-c db re k))
bridge-c (t-In-app-check wfF d) re k =
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
bridge-c {ctx = ctx} (t-var-poly-instantiate _ _ _ _ _ bodyD) {dγ₂ = dγ₂} re k
  rewrite SD-subst-usage {Γ = NamedCtx.debruijn ctx} {eq = poly-usage-eq}
                         {e = morph-app (elaborate IR.Heap (realize bodyD)) unit} {dγ = dγ₂}
  rewrite faithful (realize bodyD) tt k = bridge-c bodyD {dγ₁ = tt} {dγ₂ = tt} tt k
