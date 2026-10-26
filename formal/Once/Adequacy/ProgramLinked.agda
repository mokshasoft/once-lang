-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ProgramLinked — THE COMPILED PROGRAM IS LINKED (plan 0.103
-- 6a‴): every call, in `main` and in every table entry, names an entry of the
-- table at its objects.
--
-- The calls are references. A definition's body is the realization of its
-- typing derivation (D254), and in `realize` every reference is one the rule
-- found in scope: an import at its type, or a telescope entry at a kinded
-- instance of its schema. The resolver splices the latter (its body checked
-- at the instance, D243, and realized), so after resolution every reference
-- is an import, i.e. an earlier entry of the table (D241: the telescope).
-- `main` is an entry like any other (D253); the program's `main` calls it.
--
-- The proof is a walk over the module telescope in lockstep with the compile
-- walk, carrying: the scope's imports are linked in the table so far, every
-- telescope entry's splice at every instance is linked, and so is every
-- entry so far.
------------------------------------------------------------------------

import Once.Spec.Type

import Once.Spec.Grade
module Once.Adequacy.ProgramLinked where

open import Once.Type.Instance using (kindsOf)
open import Once.TypeCheck.Classify using (ctxAt; baseKinds)
open import Once.Spec.Type using (Ty; KCtx; ∅ₖ)
open import Once.Type.Core using (wk₀)
open import Once.Spec.Type using (μ; ν)
open import Once.Weaken using (wk₀-id)
open import Once.TypeCheck.Classify using (TopCtx)
open import Data.Nat using (ℕ; _<_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit using (tt)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
import Data.String as Str
import Data.String.Properties as StrProp
import Data.List
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Spec.Type using (Type; Unit)
open import Once.Spec.Surface.Syntax using (PolyType)
open import Once.Type.Instance using (KindedInstance; rigidOf)
open import Once.Type.Concrete using (con-fun)
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.Name using (showCanonical)
open import Once.Contract using (ISig)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Once.IR using (IR)
open import Once.IRTy using (IRTy; ⌊_⌋)
open import Once.IR.Ref using (refIR)
import Once.Compile as C
import Once.IR as IR′
import Once.Parser as Parser
open Parser.FunInfo using (funName)
open Parser.PolyFunInfo using (pfunName; pfunType; pfunBody)
import Once.Parser.Module.Core as P
import Once.Surface.Context as Ctx
open import Once.Context hiding (_,_)
open import Once.Spec.Context using (Ctx; Usage; zeroUsage)
open import Once.Spec.Context using ([]; _∷_)
import Once.Spec.Context
open import Once.Surface.Context
open import Once.Surface.Syntax
import Once.Spec.Surface.Syntax as Syn
open import Once.TypeCheck.Scope using (NamedCtx; Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys)
open import Once.TypeCheck.Elaborate using (success; failure)
open import Once.TypeCheck.ElaborateSound using (VerifiedCheckResult; checkElabV)
open import Once.TypeCheck.Link using (resolveExpr; resolveExprWF)
open import Once.TypeCheck.Completeness using (check-completeS)
open import Once.TypeCheck.SpecWitness using (OkOf; OkSOf)
import Once.TypeCheck.WitnessSubst
open import Once.Type.Schema using (kinded-instance)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
import Once.Spec.Core.Syntax
import Once.Core.Translate as TR
import Once.Adequacy.ModuleProgram as MP
open import Once.Adequacy.ModuleSig using (sigOf; sig-in)
open import Data.Fin using (zero)
open import Once.Spec.Surface.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Type.Rigid using (ground-kinded)
open import Once.IRTy using (⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Denotation.Program using (IRFun; irProgram; LinkedAt; Linked; LinkedProgram)
open Once.Denotation.Program.IRFun using (fbody)
open import Once.Module using (ModTele; []; ffi; mono; poly; ModuleTyped-ef; EffUU; teleSig; moduleSig; moduleSig-ef)
open import Once.Adequacy.ModuleLaws using (teleSig≡entrySig)
open import Once.Compile using (moduleToIR; moduleToIR-aux; moduleTable; tableOfResult; tableOf-go; irFunOf; mainEntry; findMain-here)
open import Once.Spec.Sub using (_<:_; sub-arr; sub-unit; sub-void)
open import Once.Type.SubDecide using (_<:?_)
open import Once.CanonicalName using (_≟ᶜ_)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.FunBundle as FB
import Data.Maybe
open import Once.Adequacy.TelePosition
open import Once.Adequacy.ElaborateLinked
open import Once.Denotation.SurfaceRefs using (Refs; FFIRef; ImpRef; PolyRef; InScope)
open import Once.TypeCheck.ElaborateSound using (checkSoundOf; soundOf; inferElabV)

private variable σ : ISig

-- The resolver's splice of a telescope reference, read off the checker's
-- answer at the instance (`applySplice` without its termination bookkeeping).
spliceWith : ∀ {m} {n} {Γ : Ctx m n} (pre : PolyCtx) → Acc _<_ (length pre) → (String → TopCtx) → Imports → ℕ
           → (x : String) (A : Ty m) {Xs : TopCtx} {b : Syn.Expr}
           → VerifiedCheckResult (ctxAt baseKinds Xs pre) b A → Expr Γ zeroUsage A
spliceWith pre ac I uf fresh x A (failure _ , _)             = poly x A
spliceWith pre ac I uf fresh x A (success Once.Spec.Context.[] eE _ _ , _) = closed (resolveExprWF pre ac I uf fresh eE)

-- A telescope reference's splice is linked: at the entry's body, checked at
-- the instance in its declaration context.
SpliceOK : ∀ {m} → ISig → List IRFun → PolyCtx → (String → TopCtx) → String → Ty m → Set
SpliceOK σ tbl polys I x A =
  ∀ {s b pre} → lookupPolyPrefix polys x ≡ just (s , b , pre)
  → ∀ (ac : Acc _<_ (length pre)) (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx _ n}
  → Refs (DeclIn σ) (RefLinked σ tbl) (RefLinked σ tbl) (spliceWith {Γ = Γ} pre ac I uf fresh x A (checkElabV (ctxAt baseKinds (I x) pre) b A))

------------------------------------------------------------------------
-- (C′) The resolver turns each telescope reference into its splice.
------------------------------------------------------------------------

module _ {σ : ISig} (tbl : List IRFun) (polys : PolyCtx) (I : String → TopCtx) {m : ℕ} {Δ : KCtx m}
         (sp : ∀ {x} {A : Ty m} → PolyRef polys Δ x A → SpliceOK σ tbl polys I x A) where
  private
    L : String → Ty m → Set
    L = RefLinked σ tbl

    -- `applySplice` is `spliceWith` at the prefix's accessibility.
    as-case : ∀ (pAcc : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) (x : String) (A : Ty m) {n} {Γ : Ctx m n}
                {s b pre} (polyEq : lookupPolyPrefix polys x ≡ just (s , b , pre))
                (cr : VerifiedCheckResult (ctxAt baseKinds (I x) pre) b A)
            → (∀ ac → Refs (DeclIn σ) L L (spliceWith {Γ = Γ} pre ac I uf fresh x A cr))
            → Refs (DeclIn σ) L L (Once.TypeCheck.Link.applySplice {Γ = Γ} polys pAcc I uf fresh x A polyEq (proj₁ cr))
    as-case pAcc       uf fresh x A polyEq (failure e , w) h = h (<-wellFounded _)
    as-case (acc rec) uf fresh x A polyEq (success Once.Spec.Context.[] _ _ _ , w) h =
      h (rec (Once.TypeCheck.Classify.lookupPolyPrefix-decreases x polys polyEq))

    rp-case : ∀ (pAcc : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) (x : String) (A : Ty m) {n} {Γ : Ctx m n}
                (look : Maybe (PolyType × Syn.Expr × PolyCtx)) (lq : lookupPolyPrefix polys x ≡ look)
            → PolyRef polys Δ x A
            → Refs (DeclIn σ) L L (Once.TypeCheck.Link.resolvePolyCase {Γ = Γ} polys pAcc I uf fresh x A look lq)
    rp-case pAcc uf fresh x A nothing lq ((_ , eP , _)) = ⊥-elim (nothing≢just (trans (sym lq) eP))
      where nothing≢just : ∀ {X : Set} {v : X} → nothing ≢ just v
            nothing≢just ()
    rp-case pAcc uf fresh x A {Γ = Γ} (just (s , b , pre)) lq pr =
      as-case pAcc uf fresh x A lq (checkElabV (ctxAt baseKinds (I x) pre) b A)
              (λ ac → sp pr lq ac uf fresh {Γ = Γ})

  resolve-refs : ∀ (pAcc : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m}
                   (e : Expr Γ Ψ A)
               → Refs (DeclIn σ) L (PolyRef polys Δ) e → Refs (DeclIn σ) L L (resolveExprWF polys pAcc I uf fresh e)
  resolve-refs pAcc uf fresh (var _)           r = tt
  resolve-refs pAcc uf fresh (lam _ _ b)       r = resolve-refs pAcc uf fresh b r
  resolve-refs pAcc uf fresh (app f x)         (a , b) = resolve-refs pAcc uf fresh f a , resolve-refs pAcc uf fresh x b
  resolve-refs pAcc uf fresh (effApp f x)      (a , b) = resolve-refs pAcc uf fresh f a , resolve-refs pAcc uf fresh x b
  resolve-refs pAcc uf fresh (pair x y)        (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (fst' p)          r = resolve-refs pAcc uf fresh p r
  resolve-refs pAcc uf fresh (snd' p)          r = resolve-refs pAcc uf fresh p r
  resolve-refs pAcc uf fresh (inl' x)          r = resolve-refs pAcc uf fresh x r
  resolve-refs pAcc uf fresh (inr' x)          r = resolve-refs pAcc uf fresh x r
  resolve-refs pAcc uf fresh (case' s l r′)    (a , b , c) =
    resolve-refs pAcc uf fresh s a , resolve-refs pAcc uf fresh l b , resolve-refs pAcc uf fresh r′ c
  resolve-refs pAcc uf fresh unit              r = tt
  resolve-refs pAcc uf fresh (absurd e)        r = resolve-refs pAcc uf fresh e r
  resolve-refs pAcc uf fresh (let' e₁ e₂)      (a , b) = resolve-refs pAcc uf fresh e₁ a , resolve-refs pAcc uf fresh e₂ b
  resolve-refs pAcc uf fresh (int _)           r = tt
  resolve-refs pAcc uf fresh (float _)         r = tt
  resolve-refs pAcc uf fresh (add x y)         (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (sub x y)         (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (mul x y)         (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (fadd x y)        (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (fsub x y)        (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (fmul x y)        (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (fdiv x y)        (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (i2f x)           r = resolve-refs pAcc uf fresh x r
  resolve-refs pAcc uf fresh (div x y)         (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (mod' x y)        (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (neg x)           r = resolve-refs pAcc uf fresh x r
  resolve-refs pAcc uf fresh (lt x y)          (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (le x y)          (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (gt x y)          (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (ge x y)          (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (eq x y)          (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (ne x y)          (a , b) = resolve-refs pAcc uf fresh x a , resolve-refs pAcc uf fresh y b
  resolve-refs pAcc uf fresh (coerce _ e)      r = resolve-refs pAcc uf fresh e r
  resolve-refs pAcc uf fresh (sigOp _ _)       r = r
  resolve-refs pAcc uf fresh (closure x)       r = r
  resolve-refs pAcc uf fresh {A = A} (poly x T) r =
    rp-case pAcc uf fresh x A (lookupPolyPrefix polys x) refl r
  resolve-refs pAcc uf fresh (closed e)        r = resolve-refs pAcc uf fresh e r
  resolve-refs pAcc uf fresh (lift-morphism m) r = r
  resolve-refs pAcc uf fresh (morph-app m x)   (a , b) = a , resolve-refs pAcc uf fresh x b
  resolve-refs pAcc uf fresh (comp' f g)       (a , b) = resolve-refs pAcc uf fresh f a , resolve-refs pAcc uf fresh g b
  resolve-refs pAcc uf fresh (copair' f g)     (a , b) = resolve-refs pAcc uf fresh f a , resolve-refs pAcc uf fresh g b
  resolve-refs pAcc uf fresh (fork' f g)       (a , b) = resolve-refs pAcc uf fresh f a , resolve-refs pAcc uf fresh g b
  resolve-refs pAcc uf fresh (curry' f)        r = resolve-refs pAcc uf fresh f r
  resolve-refs pAcc uf fresh (cata _ alg)      r = resolve-refs pAcc uf fresh alg r
  resolve-refs pAcc uf fresh (ana _ coalg)     r = resolve-refs pAcc uf fresh coalg r
  resolve-refs pAcc uf fresh (loop round)      r = resolve-refs pAcc uf fresh round r

------------------------------------------------------------------------
-- (D) An entry's call and body.
------------------------------------------------------------------------

-- The direct-call form (`directCallIR`) of a linked body is linked.
dc-linked : ∀ (tbl : List IRFun) (ty : Type) (ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋)
          → Linked σ tbl ir → Linked σ tbl (proj₂ (proj₂ (C.directCallIR ty ir)))
dc-linked tbl (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero π ] B) ir l = tt , ((l , tt) , tt)
dc-linked tbl (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One  π ] B) ir l = tt , ((l , tt) , tt)
dc-linked tbl (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B) ir l = tt , ((l , tt) , tt)
dc-linked tbl Once.Spec.Type.Unit           ir l = l
dc-linked tbl Once.Spec.Type.Void           ir l = l
dc-linked tbl (A Once.Spec.Type.* B)        ir l = l
dc-linked tbl (A Once.Spec.Type.+ B)        ir l = l
dc-linked tbl (Once.Spec.Type.μ F)     ir l = l
dc-linked tbl (Once.Spec.Type.ν F π)   ir l = l
dc-linked tbl Once.Spec.Type.Int            ir l = l
dc-linked tbl Once.Spec.Type.Float          ir l = l
dc-linked tbl (Once.Spec.Type.var i)    ir l = l

-- A reference to an entry is linked once the entry is in the table: the
-- reference's call (`refIR`) is at the entry's direct-call objects (D245).
ref-entry : ∀ (tbl : List IRFun) (x : String) (ty : Type) (ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋)
          → RefLinked σ (irFunOf (C.mkCompiledFun (bare x) ty ir) ∷ tbl) x ty
ref-entry tbl x ty@(A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero π ] B) ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One  π ] B) ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B) ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@Once.Spec.Type.Unit         ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@Once.Spec.Type.Void         ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(A Once.Spec.Type.* B)      ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(A Once.Spec.Type.+ B)      ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(Once.Spec.Type.μ F)   ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(Once.Spec.Type.ν F π) ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@Once.Spec.Type.Int          ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@Once.Spec.Type.Float        ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(Once.Spec.Type.var i)  ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt

RefLinked-mono : ∀ {tbl tbl′ : List IRFun} → (∀ {f A B} → LinkedAt tbl f A B → LinkedAt tbl′ f A B)
               → ∀ {m} {x} {A : Ty m} → RefLinked σ tbl x A → RefLinked σ tbl′ x A
RefLinked-mono h {x = x} {A} = linked-mono h (refIR A (bare x))

------------------------------------------------------------------------
-- (E) THE WALK
------------------------------------------------------------------------

record LInv (σ : ISig) (csc : C.CScope) (pre : List IRFun) : Set where
  field
    iself  : IAgree (C.declImps (C.CScope.ctele csc)) (C.CScope.ctele csc)
    imp-ok : ∀ {x A} → lookupImport (C.CScope.cimps csc) x ≡ just A → RefLinked σ pre x A
    tel-ok : ∀ (I : String → TopCtx) → IAgree I (C.CScope.ctele csc)
           → ∀ {x} {A : Type} → PolyRef (C.cpolys csc) ∅ₖ x A → SpliceOK σ pre (C.cpolys csc) I x A
    ent-ok : All (λ e → Linked σ pre (fbody e)) pre
    -- plan 0.105 / D274: Σ in scope is among the signatures the program is
    -- compiled against.
    sig-ok : ∀ {x A} → lookupImport (C.CScope.csig csc) x ≡ just A → (x , A) ∈ σ

private
  -- moving the invariant's table forward
  SpliceOK-mono : ∀ {tbl tbl′ : List IRFun} → (∀ {f A B} → LinkedAt tbl f A B → LinkedAt tbl′ f A B)
                → ∀ {polys I x} {A : Type} → SpliceOK σ tbl polys I x A → SpliceOK σ tbl′ polys I x A
  SpliceOK-mono {σ = σ} {tbl = tbl} {tbl′ = tbl′} h {polys} {I} {x} {A} sp {s} {b} {pre} lk ac uf fresh {Γ = Γ} =
    Refs-map {Ps = DeclIn σ} {Ps′ = DeclIn σ} {Pc = RefLinked σ tbl} {Pp = RefLinked σ tbl} {Pc′ = RefLinked σ tbl′} {Pp′ = RefLinked σ tbl′}
             (λ r → r) (λ {A} {x} → RefLinked-mono h {x = x} {A}) (λ {A} {x} → RefLinked-mono h {x = x} {A})
             (spliceWith {Γ = Γ} pre ac I uf fresh x A (checkElabV (ctxAt baseKinds (I x) pre) b A))
             (sp lk ac uf fresh {Γ = Γ})

  ents-cons : ∀ (e : IRFun) (pre : List IRFun) → Linked σ pre (fbody e) → All (λ e′ → Linked σ pre (fbody e′)) pre
            → All (λ e′ → Linked σ (e ∷ pre) (fbody e′)) (e ∷ pre)
  ents-cons e pre lb ok = linked-mono (linkedAt-cons e pre) (fbody e) lb ∷ All.map (λ {e′} → linked-mono (linkedAt-cons e pre) (fbody e′)) ok

  imp-cons : ∀ {imps : Imports} {pre : List IRFun} (x : String) (ty : Type) (e : IRFun)
           → RefLinked σ (e ∷ pre) x ty → (∀ {y} {A : Type} → lookupImport imps y ≡ just A → RefLinked σ pre y A)
           → ∀ {y} {A : Type} → lookupImport ((x , ty) ∷ imps) y ≡ just A → RefLinked σ (e ∷ pre) y A
  imp-cons {σ = σ} {pre = pre} x ty e hr old {y} {A} lk with x Str.≟ y
  ... | yes refl = subst (RefLinked σ (e ∷ pre) x) (just-injective lk) hr
  ... | no _     = RefLinked-mono (linkedAt-cons e pre) {x = y} {A} (old lk)

  -- D324: a definition named `main` does not enter the context (`C.extendDefs`);
  -- the table still grows by its compiled form.
  imp-defs : ∀ (b : Bool) {imps : Imports} {pre : List IRFun} (x : String) (ty : Type) (e : IRFun)
           → RefLinked σ (e ∷ pre) x ty → (∀ {y} {A : Type} → lookupImport imps y ≡ just A → RefLinked σ pre y A)
           → ∀ {y} {A : Type} → lookupImport (C.extendDefs-at b imps x ty) y ≡ just A → RefLinked σ (e ∷ pre) y A
  imp-defs true  {pre = pre} x ty e hr old {y} {A} lk = RefLinked-mono (linkedAt-cons e pre) {x = y} {A} (old lk)
  imp-defs false x ty e hr old lk = imp-cons x ty e hr old lk

  sig-cons : ∀ {sg : Imports} (x : String) (ty : Type) → (x , ty) ∈ σ
           → (∀ {y} {A : Type} → lookupImport sg y ≡ just A → (y , A) ∈ σ)
           → ∀ {y} {A : Type} → lookupImport ((x , ty) ∷ sg) y ≡ just A → (y , A) ∈ σ
  sig-cons {σ = σ} x ty new old {y} {A} lk with x Str.≟ y
  ... | yes refl = subst (λ B → (x , B) ∈ σ) (just-injective lk) new
  ... | no _     = old lk

-- D274: an FFI declaration joins Σ — no table entry.
linv-sig : ∀ {csc pre} (x : String) (ty : Type) → (x , ty) ∈ σ
         → LInv σ csc pre → LInv σ (C.extendSig csc x ty) pre
linv-sig {σ = σ} {csc = csc} {pre = pre} x ty d inv = record
  { iself  = LInv.iself inv
  ; imp-ok = LInv.imp-ok inv
  ; tel-ok = LInv.tel-ok inv
  ; ent-ok = LInv.ent-ok inv
  ; sig-ok = sig-cons x ty d (LInv.sig-ok inv)
  }

-- A definition joins the scope, its compiled form the table.
linv-entry : ∀ {csc pre} (x : String) (ty : Type) (ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋)
           → Linked σ pre (fbody (irFunOf (C.mkCompiledFun (bare x) ty ir)))
           → LInv σ csc pre → LInv σ (C.extendScope csc x ty) (irFunOf (C.mkCompiledFun (bare x) ty ir) ∷ pre)
linv-entry {σ = σ} {csc = csc} {pre = pre} x ty ir lb inv = record
  { iself  = LInv.iself inv
  ; imp-ok = imp-defs (x Str.== "main") x ty e (ref-entry pre x ty ir) (LInv.imp-ok inv)
  ; tel-ok = λ I ia pr → SpliceOK-mono (linkedAt-cons e pre) {polys = C.cpolys csc} {I = I} (LInv.tel-ok inv I ia pr)
  ; ent-ok = ents-cons e pre lb (LInv.ent-ok inv)
  ; sig-ok = LInv.sig-ok inv
  }
  where e = irFunOf (C.mkCompiledFun (bare x) ty ir)

-- A reference to an import, at its ground type.
imp-ref : ∀ {csc pre} → LInv σ csc pre → ∀ {A : Type} {x} → ImpRef (C.CScope.cimps csc) x A → RefLinked σ pre x A
imp-ref {σ = σ} {pre = pre} inv {x = x} (T , lk , e) = subst (RefLinked σ pre x) (sym (trans e (wk₀-id T))) (LInv.imp-ok inv lk)

-- A definition's body, checked in its scope, compiles to linked IR.
body-linked : ∀ {csc pre} → LInv σ csc pre → (x : String) (ty : Type) {body : Syn.Expr} {irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋}
                {se : _} {d f : ℕ}
            → C.compileFun IR′.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body ≡ inj₂ irFun
            → (ce : Once.TypeCheck.Elaborate.checkElab (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body ty
                      ≡ success Once.Spec.Context.[] se d f)
            → Linked σ pre irFun
body-linked {σ = σ} {csc = csc} {pre = pre} inv x ty {body} {se = se} cf ce =
  subst (Linked σ pre) (sym (irFun-form (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body cf ce))
    (elaborate-linked pre IR′.Heap (resolveExpr (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 se)
      (resolve-refs pre (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
         (LInv.tel-ok inv (C.declImps (C.CScope.ctele csc)) (LInv.iself inv))
         (<-wellFounded (length (C.cpolys csc))) uf 0 se
         (Refs-map {Ps = FFIRef (C.CScope.csig csc)} {Ps′ = DeclIn σ} {Pc = ImpRef (C.CScope.cimps csc)} {Pp = PolyRef (C.cpolys csc) ∅ₖ} {Pc′ = RefLinked σ pre} {Pp′ = PolyRef (C.cpolys csc) ∅ₖ}
                   (LInv.sig-ok inv) (imp-ref inv) (λ r → r) se refs)))
  where -- the checker's term refers only into its scope (its witness says so)
        refs : InScope (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) se
        refs = proj₁ (subst (checkSoundOf (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body ty) ce
                                   (proj₂ (checkElabV (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body ty)))
        uf : Imports
        uf = (x , ty) ∷ C.CScope.cimps csc

-- R8: likewise a definition without a signature, compiled from its synthesis.
body-linkedI : ∀ {csc pre} → LInv σ csc pre → (x : String) (ty : Type) {body : Syn.Expr} {irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋}
                 {se : _} {d f : ℕ}
             → C.compileFunI IR′.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body ≡ inj₂ irFun
             → (ce : Once.TypeCheck.Elaborate.inferElab (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body
                       ≡ success ty Once.Spec.Context.[] se d f)
             → Linked σ pre irFun
body-linkedI {σ = σ} {csc = csc} {pre = pre} inv x ty {body} {se = se} cf ce =
  subst (Linked σ pre) (sym (irFun-formI (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body cf ce))
    (elaborate-linked pre IR′.Heap (resolveExpr (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 se)
      (resolve-refs pre (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
         (LInv.tel-ok inv (C.declImps (C.CScope.ctele csc)) (LInv.iself inv))
         (<-wellFounded (length (C.cpolys csc))) uf 0 se
         (Refs-map {Ps = FFIRef (C.CScope.csig csc)} {Ps′ = DeclIn σ} {Pc = ImpRef (C.CScope.cimps csc)} {Pp = PolyRef (C.cpolys csc) ∅ₖ} {Pc′ = RefLinked σ pre} {Pp′ = PolyRef (C.cpolys csc) ∅ₖ}
                   (LInv.sig-ok inv) (imp-ref inv) (λ r → r) se refs)))
  where refs : InScope (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) se
        refs = proj₁ (subst (soundOf (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body) ce
                                   (proj₂ (inferElabV (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body)))
        uf : Imports
        uf = (x , ty) ∷ C.CScope.cimps csc

-- A definition, in its own mode.
body-linkedM : ∀ {csc pre} → LInv σ csc pre → (ft : Data.Maybe.Maybe Type) (x : String) (ty : Type) {body : Syn.Expr}
                 {irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} {Ψ : Usage 0} {se : _} {d f : ℕ}
             → C.compileFunM ft IR′.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body ≡ inj₂ irFun
             → FB.ElabOK ft (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body ty Ψ se d f
             → Linked σ pre irFun
body-linkedM inv (Data.Maybe.just _) x ty {Ψ = Once.Spec.Context.[]} cf ce = body-linked inv x ty cf ce
body-linkedM inv Data.Maybe.nothing  x ty {Ψ = Once.Spec.Context.[]} cf ce = body-linkedI inv x ty cf ce

-- A telescope entry joins the scope. Its splice at a kinded instance is
-- linked: its body's witness, over the schema's parameters, instantiated, is
-- a Spec derivation at the instance (`WitnessSubst`), which the checker
-- accepts (`Completeness`, at the scope's Pack); the splice is that check's
-- term, whose references are the scope's (`InScope`), resolved
-- (`resolve-refs`).
private
  splice-at : ∀ (tbl : List IRFun) (pre : PolyCtx) (ac : Acc _<_ (length pre)) (I : String → TopCtx) (uf : Imports)
                (fresh : ℕ) (x : String) (A : Type) {n} {Γ : Ctx 0 n} {Xs : TopCtx} {b : Syn.Expr} {se : _} {d f : ℕ}
                (cr : VerifiedCheckResult (ctxAt baseKinds Xs pre) b A)
                (ce : proj₁ cr ≡ success Once.Spec.Context.[] se d f)
            → Refs (DeclIn σ) (RefLinked σ tbl) (RefLinked σ tbl) (resolveExprWF pre ac I uf fresh se)
            → Refs (DeclIn σ) (RefLinked σ tbl) (RefLinked σ tbl) (spliceWith {Γ = Γ} pre ac I uf fresh x A cr)
  splice-at tbl pre ac I uf fresh x A (success Once.Spec.Context.[] _ _ _ , w) refl r = r

linv-poly : ∀ {Σ : Signature} {s} {S : Defs s} {csc pre} {pfi : Parser.PolyFunInfo} {Ψ : Usage 0}
            (ss : TR.SigSig Σ (C.CScope.csig csc)) (is : TR.ImpSig Σ S (C.CScope.cimps csc))
            (ts : TR.TeleSig Σ S (C.telePolys (C.CScope.ctele csc))) (N : MP.Names Σ S is ts)
          → MP.PolyWit Σ (AS.scopeOf csc) pfi Ψ
          → All (pfunName pfi ≢_) (scopeNames csc)
          → LInv σ csc pre → LInv σ (C.addEntry csc pfi) pre
linv-poly {σ = σ} {Σ} {S = S} {csc} {pre} {pfi} {Once.Spec.Context.[]} ss is ts N W fr inv = record
  { iself  = declImps-head (pfi , C.ctop csc) (C.CScope.ctele csc) (pfunName pfi Str.≟ pfunName pfi)
             ∷ iself-step (pfi , C.ctop csc) (C.CScope.ctele csc) (C.CScope.ctele csc)
                          (++⁻ʳ (Data.List.map proj₁ (C.CScope.cimps csc)) fr) (LInv.iself inv)
  ; imp-ok = LInv.imp-ok inv
  ; tel-ok = tel′
  ; ent-ok = LInv.ent-ok inv
  ; sig-ok = LInv.sig-ok inv
  }
  where
    y     = pfunName pfi
    scT   = pfunType pfi
    bd    = pfunBody pfi
    polys = C.cpolys csc
    imps  = C.CScope.cimps csc
    top   = C.ctop csc

    -- the scope's Pack, and over the parameters
    P  = MP.packOf Σ {S = S} {sc = AS.scopeOf csc} ss is ts N
    κ  = kindsOf scT
    Pκ = MP.packOfAt Σ κ {S = S} {sc = AS.scopeOf csc} ss is ts N

    -- the head: its body at the instance, in its declaration scope
    head-ok : ∀ (I : String → TopCtx) → I y ≡ top → IAgree I (C.CScope.ctele csc) → ∀ {A : Type} → KindedInstance ∅ₖ scT A
            → ∀ (ac : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx 0 n}
            → Refs (DeclIn σ) (RefLinked σ pre) (RefLinked σ pre)
                   (spliceWith {Γ = Γ} polys ac I uf fresh y A (checkElabV (ctxWithImportsAndPolys (I y) polys) bd A))
    head-ok I iy ia {A} ki ac uf fresh {Γ = Γ} =
      subst (λ Xs → Refs (DeclIn σ) (RefLinked σ pre) (RefLinked σ pre)
                         (spliceWith {Γ = Γ} polys ac I uf fresh y A (checkElabV (ctxWithImportsAndPolys Xs polys) bd A)))
            (sym iy)
            (splice-at pre polys ac I uf fresh y A cr ce
              (resolve-refs pre polys I (LInv.tel-ok inv I ia) ac uf fresh se
                 (Refs-map {Ps = FFIRef (C.CScope.csig csc)} {Ps′ = DeclIn σ} {Pc = ImpRef imps} {Pp = PolyRef polys ∅ₖ} {Pc′ = RefLinked σ pre} {Pp′ = PolyRef polys ∅ₖ}
                           (LInv.sig-ok inv) (imp-ref inv) (λ r → r) se (proj₁ (wit-of cr ce)))))
      where
        K  = kinded-instance scT ki
        module WS = Once.TypeCheck.WitnessSubst Σ S (MP.Names.nm N) (OkOf P) (OkSOf P) κ ∅ₖ (proj₁ K) (proj₁ (proj₂ K))
        -- the witness over the parameters, at the instance
        wΔ = proj₁ (proj₂ (proj₂ (proj₂ W)))
        uΔ = proj₁ (proj₂ (proj₂ wΔ Pκ))
        su = WS.subW⇐ (proj₂ uΔ)
        cr = checkElabV (ctxWithImportsAndPolys top polys) bd A
        cc = subst (λ X → ∃[ se ] ∃[ d ] ∃[ f ] Once.TypeCheck.Elaborate.checkElab (ctxWithImportsAndPolys top polys) bd X
                                                  ≡ success Once.Spec.Context.[] se d f)
                   (proj₂ (proj₂ K)) (check-completeS P (proj₂ su))
        se = proj₁ cc
        ce = proj₂ (proj₂ (proj₂ cc))

    tel′ : ∀ (I : String → TopCtx) → IAgree I ((pfi , top) ∷ C.CScope.ctele csc)
         → ∀ {x} {A : Type} → PolyRef (C.cpolys (C.addEntry csc pfi)) ∅ₖ x A → SpliceOK σ pre (C.cpolys (C.addEntry csc pfi)) I x A
    tel′ I (iy ∷ ia) {x} {A} pr {s} {b} {pre′} lk ac uf fresh {Γ = Γ} with StrProp._≟_ y x
    tel′ I (iy ∷ ia) {x} {A} (r , eP , ki) {s} {b} {pre′} lk ac uf fresh {Γ = Γ} | yes refl
      with just-injective lk | just-injective eP
    ... | refl | refl = head-ok I iy ia ki ac uf fresh {Γ = Γ}
    tel′ I (iy ∷ ia) {x} {A} pr {s} {b} {pre′} lk ac uf fresh {Γ = Γ} | no _ =
      LInv.tel-ok inv I ia pr lk ac uf fresh {Γ = Γ}

-- plan 0.105: and the FFI declarations ahead are in the signatures `σ`. The
-- table and its names are built along (`ModuleProgram`), over a Spec
-- signature declaring the module's FFI declarations (`SigIn`).
link-walk : ∀ {Σ : Signature} {csc es} (mt : ModTele (AS.scopeOf csc) es) (b : FB.FunBundle csc es)
              {s} {S : Defs s} (ss : TR.SigSig Σ (C.CScope.csig csc)) (is : TR.ImpSig Σ S (C.CScope.cimps csc))
              (ts : TR.TeleSig Σ S (C.telePolys (C.CScope.ctele csc))) (N : MP.Names Σ S is ts) (pre : List IRFun)
          → LInv σ csc pre → Fresh csc es
          → (∀ {d} → d ∈ teleSig mt → d ∈ σ) → TR.SigIn Σ mt
          → All (λ e → Linked σ (tableOf-go (FB.bundle→compiled b) pre) (fbody e)) (tableOf-go (FB.bundle→compiled b) pre)
link-walk [] FB.bnil ss is ts N pre inv fr u uΣ = LInv.ent-ok inv
link-walk {csc = csc} {es = Parser.e-fun fi ∷ es} (ffi {ty = ty} ep et c h rest) (FB.bffi {ty = ty′} ep′ et′ ec eh rest-b) ss is ts N pre inv fr u uΣ
  with just-injective (trans (sym et) et′)
... | refl = link-walk rest rest-b (TR.s-ffi c h (uΣ (here refl)) ss) is ts N pre (linv-sig (funName fi) ty (u (here refl)) inv)
               (fresh-sig {csc = csc} {fi = fi} {ty = ty} {es = es} fr) (λ m → u (there m)) (λ m → uΣ (there m))
link-walk (ffi {fi = Parser.mkFunInfo x ft bd prim} refl et c h rest) (FB.bcons () rf fc ce cf rest-b) ss is ts N pre inv fr u uΣ
link-walk {Σ = Σ} {csc = csc} {es = Parser.e-poly pfi ∷ es} (poly pr W rest) (FB.bpoly fc ce rest-b) ss is ts N pre inv fr u uΣ =
  link-walk rest rest-b ss (TR.wkI Σ is) (TR.t-def zero refl (TR.wkT Σ ts)) (MP.names-poly Σ pfi N) pre
            (linv-poly ss is ts N W (fresh-head {csc = csc} {e = Parser.e-poly pfi} {es = es} fr) inv)
            (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr) u uΣ
link-walk {Σ = Σ} {csc = csc} {es = Parser.e-fun fi ∷ es} (mono {ty = ty} refl er pr _ rest)
          (FB.bcons {ty = ty′} {Ψ = Once.Spec.Context.[]} {irFun = irFun} refl rf fc ce cf rest-b) ss is ts N pre inv fr u uΣ
  with inj₂-injective (trans (sym er) rf)
... | refl = link-walk rest rest-b ss (TR.impDefs Σ (funName fi Str.== "main") is) (TR.wkT Σ ts) (MP.names-mono Σ (funName fi Str.== "main") (funName fi) ty N) _
               (linv-entry (funName fi) ty irFun
                  (dc-linked pre ty irFun (body-linkedM inv (Parser.FunInfo.funType fi) (funName fi) ty cf ce))
                  inv)
               (fresh-fun {csc = csc} {fi = fi} {ty = ty} {es = es} fr) u uΣ

-- The program's entry is linked: it calls `main`, which the table holds at its
-- own direct-call objects (D315: `main` at its type below `Eff Unit Unit`; a
-- `main` answering `Void` is called through `initial`).
private
  entry-linked : ∀ {σ : ISig} {tbl ty} (irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋) (p : ty <: EffUU)
               → LinkedAt tbl (bare "main")
                   (IRFun.fdom (irFunOf (C.mkCompiledFun (bare "main") ty irFun)))
                   (IRFun.fcod (irFunOf (C.mkCompiledFun (bare "main") ty irFun)))
               → Linked σ tbl (mainEntry p)
  entry-linked irFun (sub-arr sub-unit sub-unit g) lk = lk
  entry-linked irFun (sub-arr sub-unit sub-void g) lk = tt , lk
  entry-linked irFun sub-void                      lk = tt , lk

main-linked : ∀ {σ : ISig} {csc es} (b : FB.FunBundle csc es) (pre : List IRFun) {ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋}
            → FB.bundle-find b ≡ just ir → Linked σ (tableOf-go (FB.bundle→compiled b) pre) ir
main-linked FB.bnil pre ()
main-linked (FB.bffi _ _ _ _ rest) pre q₀ = main-linked rest pre q₀
main-linked (FB.bpoly _ _ rest) pre q₀ = main-linked rest pre q₀
main-linked {σ} (FB.bcons {fi = fi} {ty = ty} {irFun = irFun} _ _ _ _ _ rest) pre q₀ =
  atMain (funName fi) refl (bare (funName fi) ≟ᶜ bare "main") (ty <:? EffUU) q₀
  where
    T = FB.bundle→compiled rest
    atMain : ∀ x → x ≡ funName fi → ∀ nd td {ir}
         → findMain-here (C.mkCompiledFun (bare x) ty irFun) nd td (FB.bundle-find rest) ≡ just ir
         → Linked σ (tableOf-go T (irFunOf (C.mkCompiledFun (bare x) ty irFun) ∷ pre)) ir
    atMain x xe (yes n) (yes p) refl =
      entry-linked irFun p
        (subst (λ t → LinkedAt t (bare "main") _ _) (sym (tableOf-go-++ T [] (e′ ∷ pre)))
          (linkedAt-++ (tableOf-go T []) (e′ ∷ pre) (subst (λ y → LinkedAt (e′ ∷ pre) y (IRFun.fdom e′) (IRFun.fcod e′)) n′
                                                         (linkedAt-here e′ pre))))
      where
        n′ = n
        e′ = irFunOf (C.mkCompiledFun (bare x) ty irFun)
    atMain x xe (yes _) (no _)  {ir} q₀′ = subst (λ y → Linked σ (tableOf-go T (irFunOf (C.mkCompiledFun (bare y) ty irFun) ∷ pre)) ir) (sym xe) (main-linked rest _ q₀′)
    atMain x xe (no _)  _       {ir} q₀′ = subst (λ y → Linked σ (tableOf-go T (irFunOf (C.mkCompiledFun (bare y) ty irFun) ∷ pre)) ir) (sym xe) (main-linked rest _ q₀′)

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

-- The walk's start: the empty scope.
linv₀ : LInv σ C.emptyCScope []
linv₀ = record { iself = [] ; imp-ok = λ () ; tel-ok = λ _ _ {x} {A} pr _ → ⊥-elim (no-poly {x} {A} pr) ; ent-ok = [] ; sig-ok = λ () }
  where no-poly : ∀ {x} {A : Type} → PolyRef [] ∅ₖ x A → ⊥
        no-poly (_ , () , _)

private
  typed-ef : ∀ (m : P.Resolved) (ef : _) → ModuleTyped-ef m ef → ∀ {es} → ef ≡ inj₂ es → ModTele (AS.scopeOf C.emptyCScope) es
  typed-ef m .(inj₂ _) mt refl = mt

-- plan 0.105: linked against the interpretation signatures the module is
-- compiled against (`moduleSig`, its FFI declarations).
moduleToProgram-linked : ∀ (m : P.Resolved) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)
                       → moduleToIR m ≡ just ir → LinkedProgram (moduleSig m) (irProgram (moduleTable m) ir)
moduleToProgram-linked m ir mi with FB.program-node m ir mi
... | es , ef , b , ceq =
  subst (λ t → LinkedProgram (moduleSig m) (irProgram t ir)) (sym (cong tableOfResult ceq))
    ( main-linked b [] bf
    , link-walk mt₀ b {S = Once.Spec.Core.Syntax.[]} TR.[] TR.[] TR.[] (MP.names₀ (sigOf (teleSig mt₀))) [] linv₀
                (entries-distinct m ef , none-in-empty _) u (sig-in mt₀))
  where
    T  = tableOf-go (FB.bundle→compiled b) []
    bf = trans (sym (FB.find-agree b)) (trans (sym (cong moduleToIR-aux ceq)) mi)
    mt₀ = typed-ef m _ (AS.moduleToIR-typed m mi) ef
    -- the signatures the walk's typing reads are the module's
    u : ∀ {d} → d ∈ teleSig mt₀ → d ∈ moduleSig m
    u {d} k = subst (d ∈_) (trans (teleSig≡entrySig mt₀) (sym (cong moduleSig-ef ef))) k
