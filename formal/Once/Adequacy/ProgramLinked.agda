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

module Once.Adequacy.ProgramLinked where

open import Data.Nat using (ℕ; _<_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String) renaming (_≟_ to _≟str_)
import Data.String.Properties as StrProp
import Data.List
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Type using (Type; PolyType; Unit)
open import Once.Type.Rigid using (KindedInstance; RigidFree; rigidOf)
open import Once.CanonicalName using (CanonicalName; bare; _≟ᶜ_)
open import Once.IR using (IR)
open import Once.IRTy using (IRTy; ⌊_⌋; _≟IRTy_)
open import Once.IR.Ref using (refIR)
import Once.Compile as C
open C.FunInfo using (funName; funBody; funType; funIsPrimitive)
open C.PolyFunInfo using (pfunName; pfunType; pfunBody)
import Once.Parser.Module.Core as P
import Once.Surface.Context as Ctx
open import Once.Surface.Syntax hiding (_,_; _,_^_)
open import Once.Surface.Elaborate using (elaborateFull)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx; Imports; PolyCtx; lookupImport; lookupPolyPrefix; ctxWithImportsAndPolys)
open import Once.TypeCheck.Elaborate using (VerifiedCheckResult; checkElabV; success; failure)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr; resolveExprWF)
open import Once.TypeCheck.Instance using (inst-at)
open import Once.TypeCheck.Completeness using (check-complete)
open import Once.Denotation.Realize using (realize; realize-infer; realize-d)
open import Once.TypeCheck.Judgment
open import Once.TypeCheck.Raw using (BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Type.Rigid using (ground-kinded)
open import Once.IRTy using (⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Type using (μ-type; ν-type)
open import Once.CanonicalName using (canonical; own)
open import Once.Denotation.Program using (IRFun; fname; fdom; fcod; fbody; irProgram; table; main;
  LinkedAt; LinkedAt-at; Linked; LinkedProgram)
open import Once.Spec.Module using (ModTele; []; ffi; mono; poly; ModuleTyped; ModuleTyped-ef; EffUU)
open import Once.Adequacy.SourceTrace using (moduleToIR; moduleToIR-aux; moduleTable; tableOfResult; tableOf-go;
  irFunOf; mainCall)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.FunBundle as FB
open import Once.Adequacy.TelePosition
open import Once.Adequacy.ElaborateLinked

-- What a typing rule finds in scope at a reference.
ImpRef : Imports → String → Type → Set
ImpRef imps x A = lookupImport imps x ≡ just A

PolyRef : PolyCtx → String → Type → Set
PolyRef polys x A = Σ (PolyType × RawExpr × PolyCtx) (λ r → (lookupPolyPrefix polys x ≡ just r) × KindedInstance (proj₁ r) A)

-- The resolver's splice of a telescope reference, read off the checker's
-- answer at the instance (`applySplice` without its termination bookkeeping).
spliceWith : ∀ {n} {Γ : Ctx n} (pre : PolyCtx) → Acc _<_ (length pre) → (String → Imports) → Imports → ℕ
           → (x : String) (A : Type) {Xs : Imports} {b : RawExpr}
           → VerifiedCheckResult (ctxWithImportsAndPolys Xs pre) b A → Expr Γ zeroUsage A
spliceWith pre ac I uf fresh x A (failure _ , _)             = poly x A
spliceWith pre ac I uf fresh x A (success Usage.[] _ _ _ , w) = closed (resolveExprWF pre ac I uf fresh (realize w))

-- A telescope reference's splice is linked: at the entry's body, checked at
-- the instance in its declaration context.
SpliceOK : List IRFun → PolyCtx → (String → Imports) → String → Type → Set
SpliceOK tbl polys I x A =
  ∀ {s b pre} → lookupPolyPrefix polys x ≡ just (s , b , pre)
  → ∀ (ac : Acc _<_ (length pre)) (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx n}
  → Refs (RefLinked tbl) (RefLinked tbl) (spliceWith {Γ = Γ} pre ac I uf fresh x A (checkElabV (ctxWithImportsAndPolys (I x) pre) b A))

------------------------------------------------------------------------
-- (C) In `realize`, a reference is one its rule found in scope: an import
-- at its type (`t-var-import`, an own-module `t-var-resolved`), or a telescope
-- entry at a kinded instance of its schema (the `poly` rules).
------------------------------------------------------------------------

private
  Refs-substA : ∀ {Pc Pp : String → Type → Set} {n} {Γ : Ctx n} {Ψ : Usage n} {A B} (eq : A ≡ B) (e : Expr Γ Ψ A)
              → Refs Pc Pp e → Refs Pc Pp (subst (Expr Γ Ψ) eq e)
  Refs-substA refl e r = r

  Refs-substF : ∀ {Pc Pp : String → Type → Set} {n} {Γ : Ctx n} {Ψ : Usage n} (G : Type → Type) {A B} (eq : A ≡ B)
                (e : Expr Γ Ψ (G A)) → Refs Pc Pp e → Refs Pc Pp (subst (λ Z → Expr Γ Ψ (G Z)) eq e)
  Refs-substF G refl e r = r

  Linked-substˡ : ∀ {tbl : List IRFun} {X Y Z : IRTy} (eq : X ≡ Y) (ir : IR X Z)
                → Linked tbl ir → Linked tbl (subst (λ o → IR o Z) eq ir)
  Linked-substˡ refl ir l = l

  Linked-substʳ : ∀ {tbl : List IRFun} {X Y Z : IRTy} (eq : Y ≡ Z) (ir : IR X Y)
                → Linked tbl ir → Linked tbl (subst (λ o → IR X o) eq ir)
  Linked-substʳ refl ir l = l

RR : (ctx : NamedCtx) → ∀ {Ψ : Usage (NamedCtx.size ctx)} {A} → Expr (NamedCtx.debruijn ctx) Ψ A → Set
RR ctx = Refs (ImpRef (NamedCtx.imports ctx)) (PolyRef (NamedCtx.polys ctx))

realize-refs   : ∀ {ctx e A} {Ψ : Usage (NamedCtx.size ctx)} (D : ctx ⊢ᶜ e ∶ A ⨾ Ψ) → RR ctx (realize D)
realize-refs-i : ∀ {ctx e A} {Ψ : Usage (NamedCtx.size ctx)} (D : Once.TypeCheck.Judgment._⊢ᵢ_∶_⨾_ ctx e A Ψ) → RR ctx (realize-infer D)
realize-refs-d : ∀ {ctx e A B π} {Ψ : Usage (NamedCtx.size ctx)} (D : Once.TypeCheck.Judgment._⊢ᵈ_∶_⇒[_]↦_⨾_ ctx e A π B Ψ)
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
realize-refs-i (t-str s)         = tt
realize-refs-i t-unit            = tt
realize-refs-i t-unit-var        = tt
realize-refs-i (t-var-local {eV = svar i} _) = tt
realize-refs-i (t-var-qualified _ conc) = tt
realize-refs-i (t-var-resolved {cn = own x} _ lk conc) = lk
realize-refs-i (t-var-resolved {cn = canonical []} _ _ conc) = tt
realize-refs-i (t-var-resolved {cn = canonical (_ ∷ _ ∷ _)} _ _ conc) = tt
realize-refs-i (t-var-import _ _ lk conc) = lk
realize-refs-i (t-var-poly-instantiate-infer {schema = schema} {g = g} eL eI eP gr T≡) =
  _ , eP , subst (KindedInstance schema) (sym T≡) (ground-kinded schema g)
realize-refs-i (t-annot _ d)     = realize-refs d
realize-refs-i (t-pair da db)    = realize-refs-i da , realize-refs-i db
realize-refs-i (t-neg d)         = realize-refs-i d
realize-refs-i (t-neg-float i f l p) = tt
realize-refs-i (t-let d₁ d₂)     = realize-refs-i d₁ , realize-refs-i d₂
realize-refs-i (t-case ds dl dr) = realize-refs-i ds , realize-refs-i dl , realize-refs-i dr
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
    ( Linked-substʳ (sym (⌊⟧T-commute F (ν-type F Once.Type.pure))) (IR.Out (wf-⌊⌋ wfF)) tt
    , realize-refs-i d)
realize-refs-i (t-Out-eff-app-infer {F = F} wfF ceq d) =
  Refs-substF (λ Z → Once.Type.Unit Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many Once.Type.eff ] Z) ceq _
    ( (Linked-substʳ (sym (⌊⟧T-commute F (ν-type F Once.Type.eff))) (IR.Out (wf-⌊⌋ wfF)) tt , tt)
    , realize-refs-i d)
realize-refs-i (t-terminal-app d) = tt , realize-refs-i d
realize-refs-i (t-apply-app-infer d) = tt , realize-refs-i d
realize-refs-i (t-apply-eff-app-infer d) = (tt , tt) , realize-refs-i d
realize-refs-i (t-app _ df dx)    = realize-refs-i df , realize-refs dx
realize-refs-i (t-effApp _ df dx) = realize-refs-i df , realize-refs dx
realize-refs-i (t-app-spine _ dx df) = realize-refs-d df , realize-refs-i dx

realize-refs-d (d-infer w a g) = realize-refs-i w
realize-refs-d (d-poly eL eI eP ¬g as inc ki g) = _ , eP , ki
realize-refs-d (d-lam ≤p d)      = realize-refs-i d
realize-refs-d (d-compose dg df) = realize-refs-d df , realize-refs-d dg
realize-refs-d d-id       = tt
realize-refs-d d-fst      = tt
realize-refs-d d-snd      = tt
realize-refs-d d-terminal = tt
realize-refs-d d-initial  = tt
realize-refs-d (d-case df dg) = realize-refs-d df , realize-refs-d dg
realize-refs-d (d-pair df dg) = realize-refs-d df , realize-refs-d dg
realize-refs-d (d-cata wfF dalg) = realize-refs-i dalg

------------------------------------------------------------------------
-- (C′) The resolver turns each telescope reference into its splice.
------------------------------------------------------------------------

module _ (tbl : List IRFun) (polys : PolyCtx) (I : String → Imports)
         (sp : ∀ {x A} → PolyRef polys x A → SpliceOK tbl polys I x A) where
  private
    L = RefLinked tbl

    -- `applySplice` is `spliceWith` at the prefix's accessibility.
    as-case : ∀ (pAcc : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) (x : String) (A : Type) {n} {Γ : Ctx n}
                {s b pre} (polyEq : lookupPolyPrefix polys x ≡ just (s , b , pre))
                (cr : VerifiedCheckResult (ctxWithImportsAndPolys (I x) pre) b A)
            → (∀ ac → Refs L L (spliceWith {Γ = Γ} pre ac I uf fresh x A cr))
            → Refs L L (Once.TypeCheck.ElaborateProofs.applySplice {Γ = Γ} polys pAcc I uf fresh x A polyEq cr)
    as-case pAcc       uf fresh x A polyEq (failure e , w) h = h (<-wellFounded _)
    as-case (acc rec) uf fresh x A polyEq (success Usage.[] _ _ _ , w) h =
      h (rec (Once.TypeCheck.Classify.lookupPolyPrefix-decreases x polys polyEq))

    rp-case : ∀ (pAcc : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) (x : String) (A : Type) {n} {Γ : Ctx n}
                (look : Maybe (PolyType × RawExpr × PolyCtx)) (lq : lookupPolyPrefix polys x ≡ look)
            → PolyRef polys x A
            → Refs L L (Once.TypeCheck.ElaborateProofs.resolvePolyCase {Γ = Γ} polys pAcc I uf fresh x A look lq)
    rp-case pAcc uf fresh x A nothing lq ((_ , eP , _)) = ⊥-elim (nothing≢just (trans (sym lq) eP))
      where nothing≢just : ∀ {X : Set} {v : X} → nothing ≢ just v
            nothing≢just ()
    rp-case pAcc uf fresh x A {Γ = Γ} (just (s , b , pre)) lq pr =
      as-case pAcc uf fresh x A lq (checkElabV (ctxWithImportsAndPolys (I x) pre) b A)
              (λ ac → sp pr lq ac uf fresh {Γ = Γ})

  resolve-refs : ∀ (pAcc : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx n} {Ψ : Usage n} {A}
                   (e : Expr Γ Ψ A)
               → Refs L (PolyRef polys) e → Refs L L (resolveExprWF polys pAcc I uf fresh e)
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
  resolve-refs pAcc uf fresh (str _)           r = tt
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
  resolve-refs pAcc uf fresh (sigOp _ _)       r = tt
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

------------------------------------------------------------------------
-- (D) An entry's call and body.
------------------------------------------------------------------------

-- The direct-call form (`directCallIR`) of a linked body is linked.
dc-linked : ∀ (tbl : List IRFun) (ty : Type) (ir : IR ⌊ Unit ⌋ ⌊ ty ⌋)
          → Linked tbl ir → Linked tbl (proj₂ (proj₂ (C.directCallIR ty ir)))
dc-linked tbl (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero π ] B) ir l = tt , ((l , tt) , tt)
dc-linked tbl (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.One  π ] B) ir l = tt , ((l , tt) , tt)
dc-linked tbl (A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) ir l = tt , ((l , tt) , tt)
dc-linked tbl Once.Type.Unit           ir l = l
dc-linked tbl Once.Type.Void           ir l = l
dc-linked tbl (A Once.Type.* B)        ir l = l
dc-linked tbl (A Once.Type.+ B)        ir l = l
dc-linked tbl (Once.Type.μ-type F)     ir l = l
dc-linked tbl (Once.Type.ν-type F π)   ir l = l
dc-linked tbl Once.Type.Int            ir l = l
dc-linked tbl Once.Type.Float          ir l = l
dc-linked tbl Once.Type.Str            ir l = l
dc-linked tbl Once.Type.Buffer         ir l = l
dc-linked tbl (Once.Type.rigid k i)    ir l = l

-- A reference to an entry is linked once the entry is in the table: the
-- reference's call (`refIR`) is at the entry's direct-call objects (D245).
ref-entry : ∀ (tbl : List IRFun) (x : String) (ty : Type) (ir : IR ⌊ Unit ⌋ ⌊ ty ⌋) (p : _)
          → RefLinked (irFunOf (C.mkCompiledFun (bare x) ty ir p) ∷ tbl) x ty
ref-entry tbl x ty@(A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Zero π ] B) ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@(A Once.Type.⇒[ Once.Type.mk-kind Once.Type.One  π ] B) ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@(A Once.Type.⇒[ Once.Type.mk-kind Once.Type.Many π ] B) ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@Once.Type.Unit         ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@Once.Type.Void         ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@(A Once.Type.* B)      ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@(A Once.Type.+ B)      ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@(Once.Type.μ-type F)   ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@(Once.Type.ν-type F π) ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@Once.Type.Int          ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@Once.Type.Float        ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@Once.Type.Str          ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@Once.Type.Buffer       ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt
ref-entry tbl x ty@(Once.Type.rigid k i)  ir p = linkedAt-here (irFunOf (C.mkCompiledFun (bare x) ty ir p)) tbl , tt

RefLinked-mono : ∀ {tbl tbl′ : List IRFun} → (∀ {f A B} → LinkedAt tbl f A B → LinkedAt tbl′ f A B)
               → ∀ {x A} → RefLinked tbl x A → RefLinked tbl′ x A
RefLinked-mono h {x} {A} = linked-mono h (refIR A (bare x))

------------------------------------------------------------------------
-- (E) THE WALK
------------------------------------------------------------------------

record LInv (csc : C.CScope) (pre : List IRFun) : Set where
  field
    irf    : ImportsRF (C.CScope.cimps csc)
    iself  : IAgree (C.declImps (C.CScope.ctele csc)) (C.CScope.ctele csc)
    imp-ok : ∀ {x A} → lookupImport (C.CScope.cimps csc) x ≡ just A → RefLinked pre x A
    tel-ok : ∀ (I : String → Imports) → IAgree I (C.CScope.ctele csc)
           → ∀ {x A} → PolyRef (C.cpolys csc) x A → SpliceOK pre (C.cpolys csc) I x A
    ent-ok : All (λ e → Linked pre (fbody e)) pre

private
  -- moving the invariant's table forward
  SpliceOK-mono : ∀ {tbl tbl′ : List IRFun} → (∀ {f A B} → LinkedAt tbl f A B → LinkedAt tbl′ f A B)
                → ∀ {polys I x A} → SpliceOK tbl polys I x A → SpliceOK tbl′ polys I x A
  SpliceOK-mono {tbl} {tbl′} h {polys} {I} {x} {A} sp {s} {b} {pre} lk ac uf fresh {Γ = Γ} =
    Refs-map {Pc = RefLinked tbl} {Pp = RefLinked tbl} {Pc′ = RefLinked tbl′} {Pp′ = RefLinked tbl′}
             (λ {x} {A} → RefLinked-mono h {x} {A}) (λ {x} {A} → RefLinked-mono h {x} {A})
             (spliceWith {Γ = Γ} pre ac I uf fresh x A (checkElabV (ctxWithImportsAndPolys (I x) pre) b A))
             (sp lk ac uf fresh {Γ = Γ})

  ents-cons : ∀ (e : IRFun) (pre : List IRFun) → Linked pre (fbody e) → All (λ e′ → Linked pre (fbody e′)) pre
            → All (λ e′ → Linked (e ∷ pre) (fbody e′)) (e ∷ pre)
  ents-cons e pre lb ok = linked-mono (linkedAt-cons e pre) (fbody e) lb ∷ All.map (λ {e′} → linked-mono (linkedAt-cons e pre) (fbody e′)) ok

  imp-cons : ∀ {imps : Imports} {pre : List IRFun} (x : String) (ty : Type) (e : IRFun)
           → RefLinked (e ∷ pre) x ty → (∀ {y A} → lookupImport imps y ≡ just A → RefLinked pre y A)
           → ∀ {y A} → lookupImport ((x , ty) ∷ imps) y ≡ just A → RefLinked (e ∷ pre) y A
  imp-cons {pre = pre} x ty e here old {y} {A} lk with x ≟str y
  ... | yes refl = subst (RefLinked (e ∷ pre) x) (just-injective lk) here
  ... | no _     = RefLinked-mono (linkedAt-cons e pre) {y} {A} (old lk)

-- One entry joins the scope, its compiled form the table.
linv-entry : ∀ {csc pre} (x : String) (ty : Type) (ir : IR ⌊ Unit ⌋ ⌊ ty ⌋) (p : _) → RigidFree ty
           → Linked pre (fbody (irFunOf (C.mkCompiledFun (bare x) ty ir p)))
           → LInv csc pre → LInv (C.extendScope csc x ty) (irFunOf (C.mkCompiledFun (bare x) ty ir p) ∷ pre)
linv-entry {csc} {pre} x ty ir p g lb inv = record
  { irf    = irf-cons {imps = C.CScope.cimps csc} {y = x} {ty = ty} g (LInv.irf inv)
  ; iself  = LInv.iself inv
  ; imp-ok = imp-cons x ty e (ref-entry pre x ty ir p) (LInv.imp-ok inv)
  ; tel-ok = λ I ia pr → SpliceOK-mono (linkedAt-cons e pre) {polys = C.cpolys csc} {I = I} (LInv.tel-ok inv I ia pr)
  ; ent-ok = ents-cons e pre lb (LInv.ent-ok inv)
  }
  where e = irFunOf (C.mkCompiledFun (bare x) ty ir p)

-- A definition's body, checked in its scope, compiles to linked IR.
body-linked : ∀ {csc pre} → LInv csc pre → (x : String) (ty : Type) {body : RawExpr} {irFun : IR ⌊ Unit ⌋ ⌊ ty ⌋}
                {se : _} {d f : ℕ}
            → C.compileFun C.Heap false (C.CScope.cimps csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body ≡ inj₂ irFun
            → (ce : Once.TypeCheck.Elaborate.checkElab (ctxWithImportsAndPolys (C.CScope.cimps csc) (C.cpolys csc)) body ty
                      ≡ success Usage.[] se d f)
            → Linked pre irFun
body-linked {csc} {pre} inv x ty {body} cf ce =
  subst (Linked pre) (sym (irFun-form (C.CScope.cimps csc) (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) x ty body cf ce))
    (elaborate-linked pre C.Heap (resolveExpr (C.cpolys csc) (C.declImps (C.CScope.ctele csc)) uf 0 (realize D′))
      (resolve-refs pre (C.cpolys csc) (C.declImps (C.CScope.ctele csc))
         (LInv.tel-ok inv (C.declImps (C.CScope.ctele csc)) (LInv.iself inv))
         (<-wellFounded (length (C.cpolys csc))) uf 0 (realize D′)
         (Refs-map {Pc = ImpRef (C.CScope.cimps csc)} {Pp = PolyRef (C.cpolys csc)} {Pc′ = RefLinked pre} {Pp′ = PolyRef (C.cpolys csc)}
                   (λ {x} {A} → LInv.imp-ok inv {x} {A}) (λ r → r) (realize D′) (realize-refs D′))))
  where D′ = sound-of (checkElabV (ctxWithImportsAndPolys (C.CScope.cimps csc) (C.cpolys csc)) body ty) ce
        uf : Imports
        uf = (x , ty) ∷ C.CScope.cimps csc

-- An FFI declaration's compiled form is its SigOp wrapper: no calls.
prim-linked : ∀ (pre : List IRFun) (fi : C.FunInfo) (ty : Type) (c : _)
            → Linked pre (fbody (irFunOf (FB.primCF fi ty c)))
prim-linked pre fi ty c =
  dc-linked pre ty _ (elaborate-linked pre C.Heap (sigOp {Γ = ∅} (bare (funName fi)) c) tt)

-- A telescope entry joins the scope. Its splice at a kinded instance is
-- linked: its body, typed once at the rigid schema, types at the instance
-- (`inst-at`, D243/D252), so the checker succeeds there (completeness); the
-- splice is the realization of that derivation, whose references are the
-- scope's (`realize-refs`), resolved (`resolve-refs`).
private
  splice-at : ∀ (tbl : List IRFun) (pre : PolyCtx) (ac : Acc _<_ (length pre)) (I : String → Imports) (uf : Imports)
                (fresh : ℕ) (x : String) (A : Type) {n} {Γ : Ctx n} {Xs : Imports} {b : RawExpr} {se : _} {d f : ℕ}
                (cr : VerifiedCheckResult (ctxWithImportsAndPolys Xs pre) b A)
                (ce : proj₁ cr ≡ success Usage.[] se d f)
            → Refs (RefLinked tbl) (RefLinked tbl) (resolveExprWF pre ac I uf fresh (realize (sound-of cr ce)))
            → Refs (RefLinked tbl) (RefLinked tbl) (spliceWith {Γ = Γ} pre ac I uf fresh x A cr)
  splice-at tbl pre ac I uf fresh x A (success Usage.[] _ _ _ , w) refl r = r

linv-poly : ∀ {csc pre} {pfi : C.PolyFunInfo} {Ψ : Usage 0}
          → ctxWithImportsAndPolys (C.CScope.cimps csc) (C.cpolys csc) ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ
          → All (pfunName pfi ≢_) (scopeNames csc)
          → LInv csc pre → LInv (C.addEntry csc pfi) pre
linv-poly {csc} {pre} {pfi} {Usage.[]} D fr inv = record
  { irf    = LInv.irf inv
  ; iself  = declImps-head (pfi , C.CScope.cimps csc) (C.CScope.ctele csc) (pfunName pfi ≟str pfunName pfi)
             ∷ iself-step (pfi , C.CScope.cimps csc) (C.CScope.ctele csc) (C.CScope.ctele csc)
                          (++⁻ʳ (Data.List.map proj₁ (C.CScope.cimps csc)) fr) (LInv.iself inv)
  ; imp-ok = LInv.imp-ok inv
  ; tel-ok = tel′
  ; ent-ok = LInv.ent-ok inv
  }
  where
    y     = pfunName pfi
    scT   = pfunType pfi
    bd    = pfunBody pfi
    polys = C.cpolys csc
    imps  = C.CScope.cimps csc

    -- the head: its body at the instance, in its declaration scope
    head-ok : ∀ (I : String → Imports) → I y ≡ imps → IAgree I (C.CScope.ctele csc) → ∀ {A} → KindedInstance scT A
            → ∀ (ac : Acc _<_ (length polys)) (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx n}
            → Refs (RefLinked pre) (RefLinked pre)
                   (spliceWith {Γ = Γ} polys ac I uf fresh y A (checkElabV (ctxWithImportsAndPolys (I y) polys) bd A))
    head-ok I iy ia {A} ki ac uf fresh {Γ = Γ} =
      subst (λ Xs → Refs (RefLinked pre) (RefLinked pre)
                         (spliceWith {Γ = Γ} polys ac I uf fresh y A (checkElabV (ctxWithImportsAndPolys Xs polys) bd A)))
            (sym iy)
            (splice-at pre polys ac I uf fresh y A cr ce
              (resolve-refs pre polys I (LInv.tel-ok inv I ia) ac uf fresh (realize w)
                 (Refs-map {Pc = ImpRef imps} {Pp = PolyRef polys} {Pc′ = RefLinked pre} {Pp′ = PolyRef polys}
                           (λ {x} {B} → LInv.imp-ok inv {x} {B}) (λ r → r) (realize w) (realize-refs w))))
      where
        D-A = inst-at scT (LInv.irf inv) D ki
        cr  = checkElabV (ctxWithImportsAndPolys imps polys) bd A
        ce  = proj₂ (proj₂ (proj₂ (check-complete D-A)))
        w   = sound-of cr ce

    tel′ : ∀ (I : String → Imports) → IAgree I ((pfi , imps) ∷ C.CScope.ctele csc)
         → ∀ {x A} → PolyRef (C.cpolys (C.addEntry csc pfi)) x A → SpliceOK pre (C.cpolys (C.addEntry csc pfi)) I x A
    tel′ I (iy ∷ ia) {x} {A} pr {s} {b} {pre′} lk ac uf fresh {Γ = Γ} with StrProp._≟_ y x
    tel′ I (iy ∷ ia) {x} {A} (r , eP , ki) {s} {b} {pre′} lk ac uf fresh {Γ = Γ} | yes refl
      with just-injective lk | just-injective eP
    ... | refl | refl = head-ok I iy ia ki ac uf fresh {Γ = Γ}
    tel′ I (iy ∷ ia) {x} {A} pr {s} {b} {pre′} lk ac uf fresh {Γ = Γ} | no _ =
      LInv.tel-ok inv I ia pr lk ac uf fresh {Γ = Γ}

link-walk : ∀ {csc es} (mt : ModTele (AS.scopeOf csc) es) (b : FB.FunBundle csc es) (pre : List IRFun)
          → LInv csc pre → Fresh csc es
          → All (λ e → Linked (tableOf-go (FB.bundle→compiled b) pre) (fbody e)) (tableOf-go (FB.bundle→compiled b) pre)
link-walk [] FB.bnil pre inv fr = LInv.ent-ok inv
link-walk {csc} {C.e-fun fi ∷ es} (ffi {ty = ty} ep et c h g rest) (FB.bffi {ty = ty′} {c = c′} ep′ et′ ec eh eg rest-b) pre inv fr
  with just-injective (trans (sym et) et′)
... | refl = link-walk rest rest-b _ (linv-entry (funName fi) ty _ true g (prim-linked pre fi ty c′) inv)
               (fresh-fun {csc = csc} {fi = fi} {ty = ty} {es = es} fr)
link-walk (ffi {fi = C.mkFunInfo x ft bd prim} refl et c h g rest) (FB.bcons () rf eg ce cf rest-b) pre inv fr
link-walk {csc} {C.e-poly pfi ∷ es} (poly D rest) (FB.bpoly ce rest-b) pre inv fr =
  link-walk rest rest-b pre (linv-poly D (fresh-head {csc = csc} {e = C.e-poly pfi} {es = es} fr) inv)
            (fresh-poly {csc = csc} {pfi = pfi} {es = es} fr)
link-walk {csc} {C.e-fun fi ∷ es} (mono {ty = ty} refl er g D rest)
          (FB.bcons {ty = ty′} {Ψ = Usage.[]} {irFun = irFun} refl rf eg ce cf rest-b) pre inv fr
  with inj₂-injective (trans (sym er) rf)
... | refl = link-walk rest rest-b _
               (linv-entry (funName fi) ty irFun false g
                  (dc-linked pre ty irFun (body-linked inv (funName fi) ty cf ce)) inv)
               (fresh-fun {csc = csc} {fi = fi} {ty = ty} {es = es} fr)

-- The entry `main` is in the table, at `IO Unit`'s direct-call objects.
main-linked : ∀ {csc es} (b : FB.FunBundle csc es) (pre : List IRFun) → FB.BMainExists b
            → LinkedAt (tableOf-go (FB.bundle→compiled b) pre) (bare "main") ⌊ Unit ⌋ ⌊ Unit ⌋
main-linked FB.bnil pre ()
main-linked (FB.bffi {fi = fi} {ty = ty} {c = c} _ _ _ _ _ rest) pre w = main-linked rest (irFunOf (FB.primCF fi ty c) ∷ pre) w
main-linked (FB.bpoly _ rest) pre w = main-linked rest pre w
main-linked (FB.bcons {fi = fi} {ty = ty} {irFun = irFun} _ _ _ _ _ rest) pre (inj₂ w) =
  main-linked rest (irFunOf (C.mkCompiledFun (bare (funName fi)) ty irFun (funIsPrimitive fi)) ∷ pre) w
main-linked (FB.bcons {fi = fi} {ty = .EffUU} {irFun = irFun} _ _ _ _ _ rest) pre (inj₁ (refl , refl , refl)) =
  subst (λ t → LinkedAt t (bare "main") ⌊ Unit ⌋ ⌊ Unit ⌋) (sym (tableOf-go-++ (FB.bundle→compiled rest) [] (e ∷ pre)))
        (linkedAt-++ (tableOf-go (FB.bundle→compiled rest) []) (e ∷ pre) (linkedAt-here e pre))
  where e = irFunOf (C.mkCompiledFun (bare "main") EffUU irFun false)

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

private
  linv₀ : LInv C.emptyCScope []
  linv₀ = record { irf = λ () ; iself = [] ; imp-ok = λ () ; tel-ok = λ _ _ {x} {A} pr _ → ⊥-elim (no-poly {x} {A} pr) ; ent-ok = [] }
    where no-poly : ∀ {x A} → PolyRef [] x A → ⊥
          no-poly (_ , () , _)

  typed-ef : ∀ (m : P.Module) (ef : _) → ModuleTyped-ef m ef → ∀ {es} → ef ≡ inj₂ es → ModTele (AS.scopeOf C.emptyCScope) es
  typed-ef m .(inj₂ _) mt refl = mt

moduleToProgram-linked : ∀ (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋)
                       → moduleToIR m ≡ just ir → LinkedProgram (irProgram (moduleTable m) ir)
moduleToProgram-linked m ir mi with FB.program-node m ir mi
... | es , ef , b , ceq =
  subst (λ t → LinkedProgram (irProgram t ir)) (sym (cong tableOfResult ceq))
    (subst (λ x → LinkedProgram (irProgram T x)) (sym ir≡)
      ( main-linked b [] (FB.bundle-find-exists b bf)
      , link-walk (typed-ef m _ (AS.moduleToIR-typed m mi) ef) b [] linv₀ (entries-distinct m ef , none-in-empty _)))
  where
    T  = tableOf-go (FB.bundle→compiled b) []
    bf = trans (sym (FB.find-agree b)) (trans (sym (cong moduleToIR-aux ceq)) mi)
    ir≡ : ir ≡ mainCall
    ir≡ = FB.bundle-find-call b bf
