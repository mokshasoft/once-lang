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

import Once.Spec.Grade
module Once.Adequacy.ProgramLinked where

open import Once.Internal.Type.Instance using (kindsOf)
open import Once.TypeCheck.Classify using (ctxAt)
open import Once.Spec.Type using (Ty)
open import Once.TypeCheck.Classify using (TopCtx)
open import Data.Nat using (ℕ; _<_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
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
open import Once.Internal.Type.Poly using (PolyType)
open import Once.Internal.Type.Instance using (KindedInstance; rigidOf)
open import Once.Internal.Type.WellFormed using (RigidFree; con-fun)
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.Internal.Name using (showCanonical)
open import Once.Internal.Contract using (ISig)
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
open import Once.Internal.Context hiding (_,_)
open import Once.Spec.Context using ([]; _∷_)
open import Once.Surface.Context
open import Once.Surface.Syntax
open import Once.Internal.Syntax using (RawExpr)
open import Once.Internal.Typing.Scope using (NamedCtx; Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys)
open import Once.TypeCheck.Elaborate using (VerifiedCheckResult; checkElabV; success; failure)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr; resolveExprWF)
open import Once.TypeCheck.Instance using (inst-at)
open import Once.TypeCheck.Completeness using (check-complete)
open import Once.Denotation.Realize using (realize; realize-infer; realize-d)
open import Once.Internal.Typing
open import Once.Internal.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Type.Rigid using (ground-kinded)
open import Once.IRTy using (⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Internal.Type using (μ-type; ν-type)
open import Once.Denotation.Program using (IRFun; irProgram; LinkedAt; Linked; LinkedProgram)
open Once.Denotation.Program.IRFun using (fbody)
open import Once.Internal.Module using (ModTele; []; ffi; mono; poly; ModuleTyped-ef; EffUU; teleSig; moduleSig; moduleSig-ef)
open import Once.Adequacy.ModuleLaws using (teleSig≡entrySig)
open import Once.Compile using (moduleToIR; moduleToIR-aux; moduleTable; tableOfResult; tableOf-go; irFunOf; mainEntry; findMain-here)
open import Once.Spec.Sub using (_<:_; sub-arr; sub-unit; sub-void)
open import Once.Type.Sub using (_<:?_)
open import Once.CanonicalName using (_≟ᶜ_)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.FunBundle as FB
import Data.Maybe
open import Once.Adequacy.TelePosition
open import Once.Adequacy.ElaborateLinked

private variable σ : ISig

-- What a typing rule finds in scope at a reference.
ImpRef : ∀ {m} → Imports → String → Ty m → Set
ImpRef imps x A = lookupImport imps x ≡ just A

-- Plan 0.105 / D274: an FFI reference (`realize` emits one for a qualified or
-- resolved name): the generator of Σ it found.
FFIRef : ∀ {m} → Imports → CanonicalName → Ty m → Set
FFIRef sg c A = lookupImport sg (showCanonical c) ≡ just A

PolyRef : ∀ {m} → PolyCtx → String → Ty m → Set
PolyRef polys x A = Σ (PolyType × RawExpr × PolyCtx) (λ r → (lookupPolyPrefix polys x ≡ just r) × KindedInstance (proj₁ r) A)

-- The resolver's splice of a telescope reference, read off the checker's
-- answer at the instance (`applySplice` without its termination bookkeeping).
spliceWith : ∀ {m} {n} {Γ : Ctx n} (pre : PolyCtx) → Acc _<_ (length pre) → (String → TopCtx) → Imports → ℕ
           → (x : String) (A : Ty m) {Xs : TopCtx} {b : RawExpr}
           → VerifiedCheckResult (ctxWithImportsAndPolys Xs pre) b A → Expr Γ zeroUsage A
spliceWith pre ac I uf fresh x A (failure _ , _)             = poly x A
spliceWith pre ac I uf fresh x A (success Usage.[] _ _ _ , w) = closed (resolveExprWF pre ac I uf fresh (realize w))

-- A telescope reference's splice is linked: at the entry's body, checked at
-- the instance in its declaration context.
SpliceOK : ∀ {m} → ISig → List IRFun → PolyCtx → (String → TopCtx) → String → Ty m → Set
SpliceOK σ tbl polys I x A =
  ∀ {s b pre} → lookupPolyPrefix polys x ≡ just (s , b , pre)
  → ∀ (ac : Acc _<_ (length pre)) (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx n}
  → Refs (DeclIn σ) (RefLinked σ tbl) (RefLinked σ tbl) (spliceWith {Γ = Γ} pre ac I uf fresh x A (checkElabV (ctxWithImportsAndPolys (I x) pre) b A))

------------------------------------------------------------------------
-- (C) In `realize`, a reference is one its rule found in scope: an import
-- at its type (`t-var-import`, an own-module `t-var-resolved`), or a telescope
-- entry at a kinded instance of its schema (the `poly` rules).
------------------------------------------------------------------------

private
  Refs-substA : ∀ {m} {Ps : CanonicalName → Ty m → Set} {Pc Pp : String → Ty m → Set} {n} {Γ : Ctx n} {Ψ : Usage n} {A B : Ty m} (eq : A ≡ B) (e : Expr Γ Ψ A)
              → Refs Ps Pc Pp e → Refs Ps Pc Pp (subst (Expr Γ Ψ) eq e)
  Refs-substA refl e r = r

  Refs-substF : ∀ {m} {Ps : CanonicalName → Ty m → Set} {Pc Pp : String → Ty m → Set} {n} {Γ : Ctx n} {Ψ : Usage n} (G : Ty m → Ty m) {A B : Ty m} (eq : A ≡ B)
                (e : Expr Γ Ψ (G A)) → Refs Ps Pc Pp e → Refs Ps Pc Pp (subst (λ Z → Expr Γ Ψ (G Z)) eq e)
  Refs-substF G refl e r = r

  Linked-substˡ : ∀ {tbl : List IRFun} {X Y Z : IRTy} (eq : X ≡ Y) (ir : IR X Z)
                → Linked σ tbl ir → Linked σ tbl (subst (λ o → IR o Z) eq ir)
  Linked-substˡ refl ir l = l

  Linked-substʳ : ∀ {tbl : List IRFun} {X Y Z : IRTy} (eq : Y ≡ Z) (ir : IR X Y)
                → Linked σ tbl ir → Linked σ tbl (subst (λ o → IR X o) eq ir)
  Linked-substʳ refl ir l = l

RR : ∀ {m} → (ctx : NamedCtx m) → ∀ {Ψ : Usage (NamedCtx.size ctx)} {A : Ty m} → Expr (NamedCtx.debruijn ctx) Ψ A → Set
RR ctx = Refs (FFIRef (NamedCtx.sig ctx)) (ImpRef (NamedCtx.imports ctx)) (PolyRef (NamedCtx.polys ctx))

realize-refs   : ∀ {ctx e A} {Ψ : Usage (NamedCtx.size ctx)} (D : ctx ⊢ᶜ e ∶ A ⨾ Ψ) → RR ctx (realize D)
realize-refs-i : ∀ {m} {A : Ty m} {ctx e} {Ψ : Usage (NamedCtx.size ctx)} (D : Once.Internal.Typing._⊢ᵢ_∶_⨾_ ctx e A Ψ) → RR ctx (realize-infer D)
realize-refs-d : ∀ {m} {A B : Ty m} {ctx e π} {Ψ : Usage (NamedCtx.size ctx)} (D : Once.Internal.Typing._⊢ᵈ_∶_⇒[_]↦_⨾_ ctx e A π B Ψ)
               → RR ctx (realize-d D)

realize-refs t-id-check             = tt
realize-refs t-fst-check            = tt
realize-refs t-snd-check            = tt
realize-refs t-terminal-morph-check = tt
realize-refs t-initial-morph-check  = tt
realize-refs t-inl-morph-check      = tt
realize-refs t-inr-morph-check      = tt
realize-refs (t-compose-check-g dg df)   = realize-refs df , realize-refs-d dg
realize-refs (t-compose-check-f wf p dg) = realize-refs-i wf , realize-refs dg
realize-refs (t-case-copair-check df dg) = realize-refs df , realize-refs dg
realize-refs (t-pair-morph-check df dg)  = realize-refs df , realize-refs dg
realize-refs (t-curry-check df)          = realize-refs df
realize-refs (t-cata-check wfF dalg)     = realize-refs dalg
realize-refs (t-ana-check wfF dcoalg)    = realize-refs dcoalg
realize-refs (t-loop-check dround)       = realize-refs dround
realize-refs (t-sub d p)                 = realize-refs-i d
realize-refs (t-lam ≤p d)                = realize-refs d
realize-refs (t-pair-lit-check da db)    = realize-refs da , realize-refs db
realize-refs (t-In-app-check {F = F} wfF d) =
  Linked-substˡ (sym (⌊⟧T-commute F (μ-type F))) (IR.In (wf-⌊⌋ wfF)) tt , realize-refs d
realize-refs (t-apply-check dp)      = tt , realize-refs-i dp
realize-refs (t-inl-app-check d)     = tt , realize-refs d
realize-refs (t-inr-app-check d)     = tt , realize-refs d
realize-refs (t-initial-app-check d) = tt , realize-refs d
realize-refs (t-var-poly-instantiate eL eI eP ¬g ki) = _ , eP , ki

realize-refs-i (t-int n)         = tt
realize-refs-i (t-float i f l p) = tt
realize-refs-i t-unit            = tt
realize-refs-i t-unit-var        = tt
realize-refs-i (t-var-local {eV = svar i} _) = tt
realize-refs-i (t-var-resolved _ wn lk conc _) = lk
realize-refs-i (t-var-own _ lk _) = lk
realize-refs-i (t-var-import _ _ lk conc _) = lk
realize-refs-i (t-var-poly-instantiate-infer {schema = schema} {g = g} eL eI eP gr T≡) =
  _ , eP , subst (KindedInstance schema) (sym T≡) (ground-kinded schema g)
realize-refs-i (t-annot _ d _)     = realize-refs d
realize-refs-i (t-pair da db)    = realize-refs-i da , realize-refs-i db
realize-refs-i (t-neg d)         = realize-refs-i d
realize-refs-i (t-neg-float i f l p) = tt
realize-refs-i (t-let d₁ d₂)     = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-case ds dl dr _) = realize-refs-i ds , realize-refs-i dl , realize-refs-i dr
realize-refs-i (t-binop-arith {op = OpAdd} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith {op = OpSub} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith {op = OpMul} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith {op = OpDiv} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith {op = OpMod} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith {op = OpLt} () _ _)
realize-refs-i (t-binop-arith {op = OpLe} () _ _)
realize-refs-i (t-binop-arith {op = OpGt} () _ _)
realize-refs-i (t-binop-arith {op = OpGe} () _ _)
realize-refs-i (t-binop-arith {op = OpEq} () _ _)
realize-refs-i (t-binop-arith {op = OpNe} () _ _)
realize-refs-i (t-binop-arith-float {op = OpAdd} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float {op = OpSub} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float {op = OpMul} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float {op = OpDiv} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float {op = OpMod} () _ _)
realize-refs-i (t-binop-arith-float {op = OpLt} () _ _)
realize-refs-i (t-binop-arith-float {op = OpLe} () _ _)
realize-refs-i (t-binop-arith-float {op = OpGt} () _ _)
realize-refs-i (t-binop-arith-float {op = OpGe} () _ _)
realize-refs-i (t-binop-arith-float {op = OpEq} () _ _)
realize-refs-i (t-binop-arith-float {op = OpNe} () _ _)
realize-refs-i (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float-il {op = OpMod} () _ _)
realize-refs-i (t-binop-arith-float-il {op = OpLt} () _ _)
realize-refs-i (t-binop-arith-float-il {op = OpLe} () _ _)
realize-refs-i (t-binop-arith-float-il {op = OpGt} () _ _)
realize-refs-i (t-binop-arith-float-il {op = OpGe} () _ _)
realize-refs-i (t-binop-arith-float-il {op = OpEq} () _ _)
realize-refs-i (t-binop-arith-float-il {op = OpNe} () _ _)
realize-refs-i (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-arith-float-ir {op = OpMod} () _ _)
realize-refs-i (t-binop-arith-float-ir {op = OpLt} () _ _)
realize-refs-i (t-binop-arith-float-ir {op = OpLe} () _ _)
realize-refs-i (t-binop-arith-float-ir {op = OpGt} () _ _)
realize-refs-i (t-binop-arith-float-ir {op = OpGe} () _ _)
realize-refs-i (t-binop-arith-float-ir {op = OpEq} () _ _)
realize-refs-i (t-binop-arith-float-ir {op = OpNe} () _ _)
realize-refs-i (t-binop-cmp {op = OpLt} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-cmp {op = OpLe} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-cmp {op = OpGt} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-cmp {op = OpGe} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-cmp {op = OpEq} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-cmp {op = OpNe} _ d₁ d₂) = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-binop-cmp {op = OpAdd} () _ _)
realize-refs-i (t-binop-cmp {op = OpSub} () _ _)
realize-refs-i (t-binop-cmp {op = OpMul} () _ _)
realize-refs-i (t-binop-cmp {op = OpDiv} () _ _)
realize-refs-i (t-binop-cmp {op = OpMod} () _ _)
realize-refs-i (t-id-app d)       = tt , realize-refs-i d
realize-refs-i (t-fst-app d)      = tt , realize-refs-i d
realize-refs-i (t-snd-app d)      = tt , realize-refs-i d
realize-refs-i (t-Out-app-infer {F = F} wfF ceq d) =
  Refs-substA ceq _
    ( Linked-substʳ (sym (⌊⟧T-commute F (ν-type F Once.Spec.Grade.pureᶠ))) (IR.Out (wf-⌊⌋ wfF)) tt
    , realize-refs-i d)
realize-refs-i (t-Out-eff-app-infer {F = F} wfF ceq d) =
  Refs-substF (λ Z → Once.Spec.Type.Unit Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many Once.Spec.Grade.act ] Z) ceq _
    ( (Linked-substʳ (sym (⌊⟧T-commute F (ν-type F Once.Spec.Grade.actᶠ))) (IR.Out (wf-⌊⌋ wfF)) tt , tt)
    , realize-refs-i d)
realize-refs-i (t-terminal-app d) = tt , realize-refs-i d
realize-refs-i (t-apply-app-infer d) = tt , realize-refs-i d
realize-refs-i (t-apply-eff-app-infer d) = (tt , tt) , realize-refs-i d
realize-refs-i (t-app _ df dx)    = realize-refs-i df , realize-refs dx
realize-refs-i (t-effApp _ df dx) = realize-refs-i df , realize-refs dx
realize-refs-i (t-app-spine _ dx df) = realize-refs-d df , realize-refs-i dx

realize-refs-d (d-infer w a g) = realize-refs-i w
realize-refs-d (d-poly eL eI eP ¬g as inc ki g) = _ , eP , ki
realize-refs-d (d-lam d)         = realize-refs-i d
realize-refs-d (d-compose dg df) = realize-refs-d df , realize-refs-d dg
realize-refs-d d-id       = tt
realize-refs-d d-fst      = tt
realize-refs-d d-snd      = tt
realize-refs-d d-terminal = tt
realize-refs-d d-initial  = tt
realize-refs-d (d-case df dg _) = realize-refs-d df , realize-refs-d dg
realize-refs-d (d-pair df dg) = realize-refs-d df , realize-refs-d dg
realize-refs-d (d-cata wfF dalg) = realize-refs-i dalg

------------------------------------------------------------------------
-- (C′) The resolver turns each telescope reference into its splice.
------------------------------------------------------------------------

module _ {σ : ISig} (tbl : List IRFun) (polys : PolyCtx) (I : String → TopCtx)
         (sp : ∀ {x A} → PolyRef polys x A → SpliceOK σ tbl polys I x A) where
  private
    L = RefLinked σ tbl

    -- `applySplice` is `spliceWith` at the prefix's accessibility.
    as-case : ∀ {m} (pAcc : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) (x : String) (A : Ty m) {n} {Γ : Ctx n}
                {s b pre} (polyEq : lookupPolyPrefix polys x ≡ just (s , b , pre))
                (cr : VerifiedCheckResult (ctxWithImportsAndPolys (I x) pre) b A)
            → (∀ ac → Refs (DeclIn σ) L L (spliceWith {Γ = Γ} pre ac I uf fresh x A cr))
            → Refs (DeclIn σ) L L (Once.TypeCheck.ElaborateProofs.applySplice {Γ = Γ} polys pAcc I uf fresh x A polyEq cr)
    as-case pAcc       uf fresh x A polyEq (failure e , w) h = h (<-wellFounded _)
    as-case (acc rec) uf fresh x A polyEq (success Usage.[] _ _ _ , w) h =
      h (rec (Once.TypeCheck.Classify.lookupPolyPrefix-decreases x polys polyEq))

    rp-case : ∀ {m} (pAcc : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) (x : String) (A : Ty m) {n} {Γ : Ctx n}
                (look : Maybe (PolyType × RawExpr × PolyCtx)) (lq : lookupPolyPrefix polys x ≡ look)
            → PolyRef polys x A
            → Refs (DeclIn σ) L L (Once.TypeCheck.ElaborateProofs.resolvePolyCase {Γ = Γ} polys pAcc I uf fresh x A look lq)
    rp-case pAcc uf fresh x A nothing lq ((_ , eP , _)) = ⊥-elim (nothing≢just (trans (sym lq) eP))
      where nothing≢just : ∀ {X : Set} {v : X} → nothing ≢ just v
            nothing≢just ()
    rp-case pAcc uf fresh x A {Γ = Γ} (just (s , b , pre)) lq pr =
      as-case pAcc uf fresh x A lq (checkElabV (ctxWithImportsAndPolys (I x) pre) b A)
              (λ ac → sp pr lq ac uf fresh {Γ = Γ})

  resolve-refs : ∀ {m} (pAcc : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx n} {Ψ : Usage n} {A : Ty m}
                   (e : Expr Γ Ψ A)
               → Refs (DeclIn σ) L (PolyRef polys) e → Refs (DeclIn σ) L L (resolveExprWF polys pAcc I uf fresh e)
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
dc-linked : ∀ {m} (tbl : List IRFun) (ty : Ty m) (ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋)
          → Linked σ tbl ir → Linked σ tbl (proj₂ (proj₂ (C.directCallIR ty ir)))
dc-linked tbl (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero π ] B) ir l = tt , ((l , tt) , tt)
dc-linked tbl (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One  π ] B) ir l = tt , ((l , tt) , tt)
dc-linked tbl (A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B) ir l = tt , ((l , tt) , tt)
dc-linked tbl Once.Spec.Type.Unit           ir l = l
dc-linked tbl Once.Spec.Type.Void           ir l = l
dc-linked tbl (A Once.Spec.Type.* B)        ir l = l
dc-linked tbl (A Once.Spec.Type.+ B)        ir l = l
dc-linked tbl (Once.Internal.Type.μ-type F)     ir l = l
dc-linked tbl (Once.Internal.Type.ν-type F π)   ir l = l
dc-linked tbl Once.Spec.Type.Int            ir l = l
dc-linked tbl Once.Spec.Type.Float          ir l = l
dc-linked tbl (Once.Internal.Type.rigid k i)    ir l = l

-- A reference to an entry is linked once the entry is in the table: the
-- reference's call (`refIR`) is at the entry's direct-call objects (D245).
ref-entry : ∀ {m} (tbl : List IRFun) (x : String) (ty : Ty m) (ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋)
          → RefLinked σ (irFunOf (C.mkCompiledFun (bare x) ty ir) ∷ tbl) x ty
ref-entry tbl x ty@(A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Zero π ] B) ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.One  π ] B) ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(A Once.Spec.Type.⇒[ Once.Spec.Grade.mk-kind Once.Spec.Grade.Many π ] B) ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@Once.Spec.Type.Unit         ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@Once.Spec.Type.Void         ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(A Once.Spec.Type.* B)      ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(A Once.Spec.Type.+ B)      ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(Once.Internal.Type.μ-type F)   ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(Once.Internal.Type.ν-type F π) ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@Once.Spec.Type.Int          ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@Once.Spec.Type.Float        ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt
ref-entry tbl x ty@(Once.Internal.Type.rigid k i)  ir = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir)) tbl , tt

RefLinked-mono : ∀ {tbl tbl′ : List IRFun} → (∀ {f A B} → LinkedAt tbl f A B → LinkedAt tbl′ f A B)
               → ∀ {x A} → RefLinked σ tbl x A → RefLinked σ tbl′ x A
RefLinked-mono h {x} {A} = linked-mono h (refIR A (bare x))

------------------------------------------------------------------------
-- (E) THE WALK
------------------------------------------------------------------------

record LInv (σ : ISig) (csc : C.CScope) (pre : List IRFun) : Set where
  field
    irf    : ImportsRF (C.CScope.cimps csc)
    irs    : ImportsRF (C.CScope.csig csc)      -- D243: Σ is ground too
    iself  : IAgree (C.declImps (C.CScope.ctele csc)) (C.CScope.ctele csc)
    imp-ok : ∀ {x A} → lookupImport (C.CScope.cimps csc) x ≡ just A → RefLinked σ pre x A
    tel-ok : ∀ (I : String → TopCtx) → IAgree I (C.CScope.ctele csc)
           → ∀ {x A} → PolyRef (C.cpolys csc) x A → SpliceOK σ pre (C.cpolys csc) I x A
    ent-ok : All (λ e → Linked σ pre (fbody e)) pre
    -- plan 0.105 / D274: Σ in scope is among the signatures the program is
    -- compiled against.
    sig-ok : ∀ {x A} → lookupImport (C.CScope.csig csc) x ≡ just A → (x , A) ∈ σ

private
  -- moving the invariant's table forward
  SpliceOK-mono : ∀ {tbl tbl′ : List IRFun} → (∀ {f A B} → LinkedAt tbl f A B → LinkedAt tbl′ f A B)
                → ∀ {polys I x A} → SpliceOK σ tbl polys I x A → SpliceOK σ tbl′ polys I x A
  SpliceOK-mono {σ = σ} {tbl = tbl} {tbl′ = tbl′} h {polys} {I} {x} {A} sp {s} {b} {pre} lk ac uf fresh {Γ = Γ} =
    Refs-map {Ps = DeclIn σ} {Ps′ = DeclIn σ} {Pc = RefLinked σ tbl} {Pp = RefLinked σ tbl} {Pc′ = RefLinked σ tbl′} {Pp′ = RefLinked σ tbl′}
             (λ r → r) (λ {x} {A} → RefLinked-mono h {x} {A}) (λ {x} {A} → RefLinked-mono h {x} {A})
             (spliceWith {Γ = Γ} pre ac I uf fresh x A (checkElabV (ctxWithImportsAndPolys (I x) pre) b A))
             (sp lk ac uf fresh {Γ = Γ})

  ents-cons : ∀ (e : IRFun) (pre : List IRFun) → Linked σ pre (fbody e) → All (λ e′ → Linked σ pre (fbody e′)) pre
            → All (λ e′ → Linked σ (e ∷ pre) (fbody e′)) (e ∷ pre)
  ents-cons e pre lb ok = linked-mono (linkedAt-cons e pre) (fbody e) lb ∷ All.map (λ {e′} → linked-mono (linkedAt-cons e pre) (fbody e′)) ok

  imp-cons : ∀ {m} {imps : Imports} {pre : List IRFun} (x : String) (ty : Ty m) (e : IRFun)
           → RefLinked σ (e ∷ pre) x ty → (∀ {A : Ty m} {y} → lookupImport imps y ≡ just A → RefLinked σ pre y A)
           → ∀ {A : Ty m} {y} → lookupImport ((x , ty) ∷ imps) y ≡ just A → RefLinked σ (e ∷ pre) y A
  imp-cons {σ = σ} {pre = pre} x ty e hr old {y} {A} lk with x Str.≟ y
  ... | yes refl = subst (RefLinked σ (e ∷ pre) x) (just-injective lk) hr
  ... | no _     = RefLinked-mono (linkedAt-cons e pre) {y} {A} (old lk)

  -- D324: a definition named `main` does not enter the context (`C.extendDefs`);
  -- the table still grows by its compiled form.
  imp-defs : ∀ {m} (b : Bool) {imps : Imports} {pre : List IRFun} (x : String) (ty : Ty m) (e : IRFun)
           → RefLinked σ (e ∷ pre) x ty → (∀ {A : Ty m} {y} → lookupImport imps y ≡ just A → RefLinked σ pre y A)
           → ∀ {A : Ty m} {y} → lookupImport (C.extendDefs-at b imps x ty) y ≡ just A → RefLinked σ (e ∷ pre) y A
  imp-defs true  {pre = pre} x ty e hr old {y} {A} lk = RefLinked-mono (linkedAt-cons e pre) {y} {A} (old lk)
  imp-defs false x ty e hr old lk = imp-cons x ty e hr old lk

  sig-cons : ∀ {m} {sg : Imports} (x : String) (ty : Ty m) → (x , ty) ∈ σ
           → (∀ {A : Ty m} {y} → lookupImport sg y ≡ just A → (y , A) ∈ σ)
           → ∀ {A : Ty m} {y} → lookupImport ((x , ty) ∷ sg) y ≡ just A → (y , A) ∈ σ
  sig-cons {σ = σ} x ty new old {y} {A} lk with x Str.≟ y
  ... | yes refl = subst (λ B → (x , B) ∈ σ) (just-injective lk) new
  ... | no _     = old lk

-- D274: an FFI declaration joins Σ — no table entry.
linv-sig : ∀ {m} {csc pre} (x : String) (ty : Ty m) → RigidFree ty → (x , ty) ∈ σ
         → LInv σ csc pre → LInv σ (C.extendSig csc x ty) pre
linv-sig {σ = σ} {csc = csc} {pre = pre} x ty g d inv = record
  { irf    = LInv.irf inv
  ; irs    = irf-cons {imps = C.CScope.csig csc} {y = x} {ty = ty} g (LInv.irs inv)
  ; iself  = LInv.iself inv
  ; imp-ok = LInv.imp-ok inv
  ; tel-ok = LInv.tel-ok inv
  ; ent-ok = LInv.ent-ok inv
  ; sig-ok = sig-cons x ty d (LInv.sig-ok inv)
  }

-- A definition joins the scope, its compiled form the table.
linv-entry : ∀ {m} {csc pre} (x : String) (ty : Ty m) (ir : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋) → RigidFree ty
           → Linked σ pre (fbody (irFunOf (C.mkCompiledFun (bare x) ty ir)))
           → LInv σ csc pre → LInv σ (C.extendScope csc x ty) (irFunOf (C.mkCompiledFun (bare x) ty ir) ∷ pre)
linv-entry {σ = σ} {csc = csc} {pre = pre} x ty ir g lb inv = record
  { irf    = irf-defs (x Str.== "main") {imps = C.CScope.cimps csc} {y = x} {ty = ty} g (LInv.irf inv)
  ; irs    = LInv.irs inv
  ; iself  = LInv.iself inv
  ; imp-ok = imp-defs (x Str.== "main") x ty e (ref-entry pre x ty ir) (LInv.imp-ok inv)
  ; tel-ok = λ I ia pr → SpliceOK-mono (linkedAt-cons e pre) {polys = C.cpolys csc} {I = I} (LInv.tel-ok inv I ia pr)
  ; ent-ok = ents-cons e pre lb (LInv.ent-ok inv)
  ; sig-ok = LInv.sig-ok inv
  }
  where e = irFunOf (C.mkCompiledFun (bare x) ty ir)

-- A definition's body, checked in its scope, compiles to linked IR.
body-linked : ∀ {m} {csc pre} → LInv σ csc pre → (x : String) (ty : Ty m) {body : RawExpr} {irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋}
                {se : _} {d f : ℕ}
            → C.compileFun IR′.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body ≡ inj₂ irFun
            → (ce : Once.TypeCheck.Elaborate.checkElab (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body ty
                      ≡ success Usage.[] se d f)
            → Linked σ pre irFun
body-linked {σ = σ} {csc = csc} {pre = pre} inv x ty {body} cf ce =
  subst (Linked σ pre) (sym (irFun-form (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body cf ce))
    (elaborate-linked pre IR′.Heap (resolveExpr (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 (realize D′))
      (resolve-refs pre (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
         (LInv.tel-ok inv (C.declImps (C.CScope.ctele csc)) (LInv.iself inv))
         (<-wellFounded (length (C.cpolys csc))) uf 0 (realize D′)
         (Refs-map {Ps = FFIRef (C.CScope.csig csc)} {Ps′ = DeclIn σ} {Pc = ImpRef (C.CScope.cimps csc)} {Pp = PolyRef (C.cpolys csc)} {Pc′ = RefLinked σ pre} {Pp′ = PolyRef (C.cpolys csc)}
                   (LInv.sig-ok inv) (λ {x} {A} → LInv.imp-ok inv {x} {A}) (λ r → r) (realize D′) (realize-refs D′))))
  where D′ = sound-of (checkElabV (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body ty) ce
        uf : Imports
        uf = (x , ty) ∷ C.CScope.cimps csc

-- R8: likewise a definition without a signature, compiled from its synthesis.
body-linkedI : ∀ {m} {csc pre} → LInv σ csc pre → (x : String) (ty : Ty m) {body : RawExpr} {irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋}
                 {se : _} {d f : ℕ}
             → C.compileFunI IR′.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body ≡ inj₂ irFun
             → (ce : Once.TypeCheck.Elaborate.inferElab (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body
                       ≡ success ty Usage.[] se d f)
             → Linked σ pre irFun
body-linkedI {σ = σ} {csc = csc} {pre = pre} inv x ty {body} cf ce =
  subst (Linked σ pre) (sym (irFun-formI (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body cf ce))
    (elaborate-linked pre IR′.Heap (resolveExpr (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 (realize-infer D′))
      (resolve-refs pre (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
         (LInv.tel-ok inv (C.declImps (C.CScope.ctele csc)) (LInv.iself inv))
         (<-wellFounded (length (C.cpolys csc))) uf 0 (realize-infer D′)
         (Refs-map {Ps = FFIRef (C.CScope.csig csc)} {Ps′ = DeclIn σ} {Pc = ImpRef (C.CScope.cimps csc)} {Pp = PolyRef (C.cpolys csc)} {Pc′ = RefLinked σ pre} {Pp′ = PolyRef (C.cpolys csc)}
                   (LInv.sig-ok inv) (λ {x} {A} → LInv.imp-ok inv {x} {A}) (λ r → r) (realize-infer D′) (realize-refs-i D′))))
  where D′ = sound-of-i (Once.TypeCheck.Elaborate.inferElabV (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body) ce
        uf : Imports
        uf = (x , ty) ∷ C.CScope.cimps csc

-- A definition, in its own mode.
body-linkedM : ∀ {m} {csc pre} → LInv σ csc pre → (ft : Data.Maybe.Maybe (Ty m)) (x : String) (ty : Ty m) {body : RawExpr}
                 {irFun : IR ⌊ Unit {0} ⌋ ⌊ ty ⌋} {Ψ : Usage 0} {se : _} {d f : ℕ}
             → C.compileFunM ft IR′.Heap false (C.ctop csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body ≡ inj₂ irFun
             → FB.ElabOK ft (ctxWithImportsAndPolys (C.ctop csc) (C.cpolys csc)) body ty Ψ se d f
             → Linked σ pre irFun
body-linkedM inv (Data.Maybe.just _) x ty {Ψ = Usage.[]} cf ce = body-linked inv x ty cf ce
body-linkedM inv Data.Maybe.nothing  x ty {Ψ = Usage.[]} cf ce = body-linkedI inv x ty cf ce

-- A telescope entry joins the scope. Its splice at a kinded instance is
-- linked: its body, typed once at the rigid schema, types at the instance
-- (`inst-at`, D243/D252), so the checker succeeds there (completeness); the
-- splice is the realization of that derivation, whose references are the
-- scope's (`realize-refs`), resolved (`resolve-refs`).
private
  splice-at : ∀ {m} (tbl : List IRFun) (pre : PolyCtx) (ac : Acc _<_ (length pre)) (I : String → TopCtx) (uf : Imports)
                (fresh : ℕ) (x : String) (A : Ty m) {n} {Γ : Ctx n} {Xs : TopCtx} {b : RawExpr} {se : _} {d f : ℕ}
                (cr : VerifiedCheckResult (ctxWithImportsAndPolys Xs pre) b A)
                (ce : proj₁ cr ≡ success Usage.[] se d f)
            → Refs (DeclIn σ) (RefLinked σ tbl) (RefLinked σ tbl) (resolveExprWF pre ac I uf fresh (realize (sound-of cr ce)))
            → Refs (DeclIn σ) (RefLinked σ tbl) (RefLinked σ tbl) (spliceWith {Γ = Γ} pre ac I uf fresh x A cr)
  splice-at tbl pre ac I uf fresh x A (success Usage.[] _ _ _ , w) refl r = r

linv-poly : ∀ {csc pre} {pfi : Parser.PolyFunInfo} {Ψ : Usage 0}
          → ctxAt (kindsOf (pfunType pfi)) (C.ctop csc) (C.cpolys csc) ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ
          → All (pfunName pfi ≢_) (scopeNames csc)
          → LInv σ csc pre → LInv σ (C.addEntry csc pfi) pre
linv-poly {σ = σ} {csc} {pre} {pfi} {Usage.[]} D fr inv = record
  { irf    = LInv.irf inv
  ; irs    = LInv.irs inv
  ; iself  = declImps-head (pfi , C.ctop csc) (C.CScope.ctele csc) (pfunName pfi Str.≟ pfunName pfi)
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

    -- the head: its body at the instance, in its declaration scope
    head-ok : ∀ (I : String → TopCtx) → I y ≡ top → IAgree I (C.CScope.ctele csc) → ∀ {A : Ty _} → KindedInstance scT A
            → ∀ (ac : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx n}
            → Refs (DeclIn σ) (RefLinked σ pre) (RefLinked σ pre)
                   (spliceWith {Γ = Γ} polys ac I uf fresh y A (checkElabV (ctxWithImportsAndPolys (I y) polys) bd A))
    head-ok I iy ia {A} ki ac uf fresh {Γ = Γ} =
      subst (λ Xs → Refs (DeclIn σ) (RefLinked σ pre) (RefLinked σ pre)
                         (spliceWith {Γ = Γ} polys ac I uf fresh y A (checkElabV (ctxWithImportsAndPolys Xs polys) bd A)))
            (sym iy)
            (splice-at pre polys ac I uf fresh y A cr ce
              (resolve-refs pre polys I (LInv.tel-ok inv I ia) ac uf fresh (realize w)
                 (Refs-map {Ps = FFIRef (C.CScope.csig csc)} {Ps′ = DeclIn σ} {Pc = ImpRef imps} {Pp = PolyRef polys} {Pc′ = RefLinked σ pre} {Pp′ = PolyRef polys}
                           (LInv.sig-ok inv) (λ {x} {B} → LInv.imp-ok inv {x} {B}) (λ r → r) (realize w) (realize-refs w))))
      where
        D-A = inst-at scT (LInv.irf inv , LInv.irs inv) D ki
        cr  = checkElabV (ctxWithImportsAndPolys top polys) bd A
        ce  = proj₂ (proj₂ (proj₂ (check-complete D-A)))
        w   = sound-of cr ce

    tel′ : ∀ (I : String → TopCtx) → IAgree I ((pfi , top) ∷ C.CScope.ctele csc)
         → ∀ {A : Ty _} {x} → PolyRef (C.cpolys (C.addEntry csc pfi)) x A → SpliceOK σ pre (C.cpolys (C.addEntry csc pfi)) I x A
    tel′ I (iy ∷ ia) {x} {A} pr {s} {b} {pre′} lk ac uf fresh {Γ = Γ} with StrProp._≟_ y x
    tel′ I (iy ∷ ia) {x} {A} (r , eP , ki) {s} {b} {pre′} lk ac uf fresh {Γ = Γ} | yes refl
      with just-injective lk | just-injective eP
    ... | refl | refl = head-ok I iy ia ki ac uf fresh {Γ = Γ}
    tel′ I (iy ∷ ia) {x} {A} pr {s} {b} {pre′} lk ac uf fresh {Γ = Γ} | no _ =
      LInv.tel-ok inv I ia pr lk ac uf fresh {Γ = Γ}

-- plan 0.105: and the FFI declarations ahead are in the signatures `σ`.
link-walk : ∀ {csc es} (mt : ModTele (AS.scopeOf csc) es) (b : FB.FunBundle csc es) (pre : List IRFun)
          → LInv σ csc pre → Fresh csc es
          → (∀ {d} → d ∈ teleSig mt → d ∈ σ)
          → All (λ e → Linked σ (tableOf-go (FB.bundle→compiled b) pre) (fbody e)) (tableOf-go (FB.bundle→compiled b) pre)
link-walk [] FB.bnil pre inv fr u = LInv.ent-ok inv
link-walk {csc = csc} {es = Parser.e-fun fi ∷ es} (ffi {ty = ty} ep et c h g rest) (FB.bffi {ty = ty′} ep′ et′ ec eh eg rest-b) pre inv fr u
  with just-injective (trans (sym et) et′)
... | refl = link-walk rest rest-b pre (linv-sig (funName fi) ty g (u (here refl)) inv)
               (fresh-sig {csc = csc} {fi = fi} {ty = ty} {es = es} fr) (λ m → u (there m))
link-walk (ffi {fi = Parser.mkFunInfo x ft bd prim} refl et c h g rest) (FB.bcons () rf fc eg ce cf rest-b) pre inv fr u
link-walk {csc = csc} {es = Parser.e-poly pfi ∷ es} (poly pr D rest) (FB.bpoly fc ce rest-b) pre inv fr u =
  link-walk rest rest-b pre (linv-poly D (fresh-head {csc = csc} {e = Parser.e-poly pfi} {es = es} fr) inv)
            (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr) u
link-walk {csc = csc} {es = Parser.e-fun fi ∷ es} (mono {ty = ty} refl er pr g D rest)
          (FB.bcons {ty = ty′} {Ψ = Usage.[]} {irFun = irFun} refl rf fc eg ce cf rest-b) pre inv fr u
  with inj₂-injective (trans (sym er) rf)
... | refl = link-walk rest rest-b _
               (linv-entry (funName fi) ty irFun g
                  (dc-linked pre ty irFun (body-linkedM inv (Parser.FunInfo.funType fi) (funName fi) ty cf ce))
                  inv)
               (fresh-fun {csc = csc} {fi = fi} {ty = ty} {es = es} fr) u

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
main-linked (FB.bffi _ _ _ _ _ rest) pre q₀ = main-linked rest pre q₀
main-linked (FB.bpoly _ _ rest) pre q₀ = main-linked rest pre q₀
main-linked {σ} (FB.bcons {fi = fi} {ty = ty} {irFun = irFun} _ _ _ _ _ _ rest) pre q₀ =
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
linv₀ = record { irf = λ () ; irs = λ () ; iself = [] ; imp-ok = λ () ; tel-ok = λ _ _ {x} {A} pr _ → ⊥-elim (no-poly {x} {A} pr) ; ent-ok = [] ; sig-ok = λ () }
  where no-poly : ∀ {x A} → PolyRef [] x A → ⊥
        no-poly (_ , () , _)

private
  typed-ef : ∀ (m : P.Module) (ef : _) → ModuleTyped-ef m ef → ∀ {es} → ef ≡ inj₂ es → ModTele (AS.scopeOf C.emptyCScope) es
  typed-ef m .(inj₂ _) mt refl = mt

-- plan 0.105: linked against the interpretation signatures the module is
-- compiled against (`moduleSig`, its FFI declarations).
moduleToProgram-linked : ∀ (m : P.Module) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)
                       → moduleToIR m ≡ just ir → LinkedProgram (moduleSig m) (irProgram (moduleTable m) ir)
moduleToProgram-linked m ir mi with FB.program-node m ir mi
... | es , ef , b , ceq =
  subst (λ t → LinkedProgram (moduleSig m) (irProgram t ir)) (sym (cong tableOfResult ceq))
    ( main-linked b [] bf
    , link-walk mt₀ b [] linv₀ (entries-distinct m ef , none-in-empty _) u)
  where
    T  = tableOf-go (FB.bundle→compiled b) []
    bf = trans (sym (FB.find-agree b)) (trans (sym (cong moduleToIR-aux ceq)) mi)
    mt₀ = typed-ef m _ (AS.moduleToIR-typed m mi) ef
    -- the signatures the walk's typing reads are the module's
    u : ∀ {d} → d ∈ teleSig mt₀ → d ∈ moduleSig m
    u {d} k = subst (d ∈_) (trans (teleSig≡entrySig mt₀) (sym (cong moduleSig-ef ef))) k
