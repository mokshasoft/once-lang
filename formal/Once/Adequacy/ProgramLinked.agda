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
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.TypeCheck.Elaborate using (VerifiedCheckResult; checkElabV; success; failure)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr; resolveExprWF)
open import Once.TypeCheck.Instance using (inst-at)
open import Once.TypeCheck.Completeness using (check-complete)
open import Once.Denotation.Realize using (realize)
open import Once.Denotation.Program using (IRFun; fname; fdom; fcod; fbody; irProgram; table; main;
  LinkedAt; LinkedAt-at; Linked; LinkedProgram)
open import Once.Spec.Module using (ModTele; []; ffi; mono; poly; ModuleTyped; ModuleTyped-ef; EffUU)
open import Once.Adequacy.SourceTrace using (moduleToIR; moduleToIR-aux; moduleTable; tableOfResult; tableOf-go;
  irFunOf; mainCall)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.FunBundle as FB
open import Once.Adequacy.TelePosition

------------------------------------------------------------------------
-- (A) Linkedness grows with the table: a new entry is consed on, and the
-- lookup finds the first entry at the name and objects.
------------------------------------------------------------------------

linkedAt-cons : ∀ (e : IRFun) (tbl : List IRFun) {f A B} → LinkedAt tbl f A B → LinkedAt (e ∷ tbl) f A B
linkedAt-cons e tbl {f} {A} {B} lk = go (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B)
  where
    go : ∀ d₁ d₂ d₃ → LinkedAt-at e tbl f A B d₁ d₂ d₃
    go (yes _) (yes _) (yes _) = tt
    go (yes _) (yes _) (no _)  = lk
    go (yes _) (no _)  _       = lk
    go (no _)  _       _       = lk

linkedAt-here : ∀ (e : IRFun) (es : List IRFun) → LinkedAt (e ∷ es) (fname e) (fdom e) (fcod e)
linkedAt-here e es = go (fname e ≟ᶜ fname e) (fdom e ≟IRTy fdom e) (fcod e ≟IRTy fcod e)
  where
    go : ∀ d₁ d₂ d₃ → LinkedAt-at e es (fname e) (fdom e) (fcod e) d₁ d₂ d₃
    go (yes _) (yes _) (yes _) = tt
    go (yes _) (yes _) (no ¬p) = ⊥-elim (¬p refl)
    go (yes _) (no ¬p) _       = ⊥-elim (¬p refl)
    go (no ¬p) _       _       = ⊥-elim (¬p refl)

linked-mono : ∀ {tbl tbl′ : List IRFun} → (∀ {f A B} → LinkedAt tbl f A B → LinkedAt tbl′ f A B)
            → ∀ {A B} (ir : IR A B) → Linked tbl ir → Linked tbl′ ir
linked-mono h (g IR.∘ f)       (lg , lf) = linked-mono h g lg , linked-mono h f lf
linked-mono h IR.⟨ f , g ⟩     (lf , lg) = linked-mono h f lf , linked-mono h g lg
linked-mono h (IR.case f g)    (lf , lg) = linked-mono h f lf , linked-mono h g lg
linked-mono h (IR.curry f)     lf = linked-mono h f lf
linked-mono h (IR.Cata _ alg)  la = linked-mono h alg la
linked-mono h (IR.Ana _ coalg) lc = linked-mono h coalg lc
linked-mono h (IR.Call f)      lk = h lk
linked-mono h IR.id            _ = tt
linked-mono h IR.fst           _ = tt
linked-mono h IR.snd           _ = tt
linked-mono h IR.inl           _ = tt
linked-mono h IR.inr           _ = tt
linked-mono h IR.terminal      _ = tt
linked-mono h IR.initial       _ = tt
linked-mono h IR.apply         _ = tt
linked-mono h (IR.In _)        _ = tt
linked-mono h (IR.out-μ _)     _ = tt
linked-mono h (IR.Out _)       _ = tt
linked-mono h (IR.in-ν _)      _ = tt
linked-mono h (IR.SigOp _)     _ = tt
linked-mono h (IR.const _ _)   _ = tt

linkedAt-++ : ∀ (later tbl : List IRFun) {f A B} → LinkedAt tbl f A B → LinkedAt (later ++ tbl) f A B
linkedAt-++ []          tbl lk = lk
linkedAt-++ (e ∷ later) tbl lk = linkedAt-cons e (later ++ tbl) (linkedAt-++ later tbl lk)

-- A call-free IR (linked in the empty table) is linked in every table.
linkedAt-[] : ∀ {tbl : List IRFun} {f A B} → LinkedAt [] f A B → LinkedAt tbl f A B
linkedAt-[] ()

------------------------------------------------------------------------
-- (B) The references of a surface term.
------------------------------------------------------------------------

-- `Refs Pc Pp e`: every `closure x : A` in `e` satisfies `Pc x A`, every
-- `poly x A` satisfies `Pp x A`, and every embedded IR morphism is call-free.
Refs : (Pc Pp : String → Type → Set) → ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ A → Set
Refs Pc Pp (var _)             = ⊤
Refs Pc Pp (lam _ _ b)         = Refs Pc Pp b
Refs Pc Pp (app f x)           = Refs Pc Pp f × Refs Pc Pp x
Refs Pc Pp (effApp f x)        = Refs Pc Pp f × Refs Pc Pp x
Refs Pc Pp (pair a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fst' p)            = Refs Pc Pp p
Refs Pc Pp (snd' p)            = Refs Pc Pp p
Refs Pc Pp (inl' a)            = Refs Pc Pp a
Refs Pc Pp (inr' a)            = Refs Pc Pp a
Refs Pc Pp (case' s l r)       = Refs Pc Pp s × Refs Pc Pp l × Refs Pc Pp r
Refs Pc Pp unit                = ⊤
Refs Pc Pp (absurd e)          = Refs Pc Pp e
Refs Pc Pp (let' e₁ e₂)        = Refs Pc Pp e₁ × Refs Pc Pp e₂
Refs Pc Pp (int _)             = ⊤
Refs Pc Pp (str _)             = ⊤
Refs Pc Pp (float _)           = ⊤
Refs Pc Pp (add a b)           = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (sub a b)           = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (mul a b)           = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fadd a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fsub a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fmul a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fdiv a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (i2f a)             = Refs Pc Pp a
Refs Pc Pp (div a b)           = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (mod' a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (neg a)             = Refs Pc Pp a
Refs Pc Pp (lt a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (le a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (gt a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (ge a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (eq a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (ne a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (coerce _ e)        = Refs Pc Pp e
Refs Pc Pp (sigOp _ _)         = ⊤
Refs Pc Pp {A = A} (closure x) = Pc x A
Refs Pc Pp (poly x T)          = Pp x T
Refs Pc Pp (closed e)          = Refs Pc Pp e
Refs Pc Pp (lift-morphism m)   = Linked [] m
Refs Pc Pp (morph-app m a)     = Linked [] m × Refs Pc Pp a
Refs Pc Pp (comp' f g)         = Refs Pc Pp f × Refs Pc Pp g
Refs Pc Pp (copair' f g)       = Refs Pc Pp f × Refs Pc Pp g
Refs Pc Pp (fork' f g)         = Refs Pc Pp f × Refs Pc Pp g
Refs Pc Pp (curry' f)          = Refs Pc Pp f
Refs Pc Pp (cata _ alg)        = Refs Pc Pp alg
Refs Pc Pp (ana _ coalg)       = Refs Pc Pp coalg

-- A reference elaborates to a call (`refIR`); it is linked when the call is.
RefLinked : List IRFun → String → Type → Set
RefLinked tbl x A = Linked tbl (refIR A (bare x))

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
-- (C) The three structural facts. SCAFFOLD (plan 0.103 6a‴): stated, wired,
-- discharged next.
------------------------------------------------------------------------

postulate
  -- a term whose references are linked elaborates to linked IR
  elaborate-linked : ∀ (tbl : List IRFun) (m : C.AllocMode) {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
                   → Refs (RefLinked tbl) (RefLinked tbl) e → Linked tbl (elaborateFull m e)
  -- in `realize`, a reference is one its rule found in scope
  realize-refs : ∀ {ctx : NamedCtx} {e A} {Ψ : Usage (NamedCtx.size ctx)} (D : ctx ⊢ᶜ e ∶ A ⨾ Ψ)
               → Refs (ImpRef (NamedCtx.imports ctx)) (PolyRef (NamedCtx.polys ctx)) (realize D)
  -- the resolver turns telescope references into their splices
  resolve-refs : ∀ (tbl : List IRFun) (polys : PolyCtx) (pAcc : Acc _<_ (length polys)) (I : String → Imports)
                   (uf : Imports) (fresh : ℕ) {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
               → (∀ {x A} → PolyRef polys x A → SpliceOK tbl polys I x A)
               → Refs (RefLinked tbl) (PolyRef polys) e
               → Refs (RefLinked tbl) (RefLinked tbl) (resolveExprWF polys pAcc I uf fresh e)

Refs-map : ∀ {Pc Pp Pc′ Pp′ : String → Type → Set}
         → (∀ {x A} → Pc x A → Pc′ x A) → (∀ {x A} → Pp x A → Pp′ x A)
         → ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A) → Refs Pc Pp e → Refs Pc′ Pp′ e
Refs-map hc hp (var _)             r = tt
Refs-map hc hp (lam _ _ b)         r = Refs-map hc hp b r
Refs-map hc hp (app f x)           (a , b) = Refs-map hc hp f a , Refs-map hc hp x b
Refs-map hc hp (effApp f x)        (a , b) = Refs-map hc hp f a , Refs-map hc hp x b
Refs-map hc hp (pair x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fst' p)            r = Refs-map hc hp p r
Refs-map hc hp (snd' p)            r = Refs-map hc hp p r
Refs-map hc hp (inl' x)            r = Refs-map hc hp x r
Refs-map hc hp (inr' x)            r = Refs-map hc hp x r
Refs-map hc hp (case' s l r′)      (a , b , c) = Refs-map hc hp s a , Refs-map hc hp l b , Refs-map hc hp r′ c
Refs-map hc hp unit                r = tt
Refs-map hc hp (absurd e)          r = Refs-map hc hp e r
Refs-map hc hp (let' e₁ e₂)        (a , b) = Refs-map hc hp e₁ a , Refs-map hc hp e₂ b
Refs-map hc hp (int _)             r = tt
Refs-map hc hp (str _)             r = tt
Refs-map hc hp (float _)           r = tt
Refs-map hc hp (add x y)           (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (sub x y)           (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (mul x y)           (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fadd x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fsub x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fmul x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fdiv x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (i2f x)             r = Refs-map hc hp x r
Refs-map hc hp (div x y)           (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (mod' x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (neg x)             r = Refs-map hc hp x r
Refs-map hc hp (lt x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (le x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (gt x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (ge x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (eq x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (ne x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (coerce _ e)        r = Refs-map hc hp e r
Refs-map hc hp (sigOp _ _)         r = tt
Refs-map hc hp (closure x)         r = hc r
Refs-map hc hp (poly x T)          r = hp r
Refs-map hc hp (closed e)          r = Refs-map hc hp e r
Refs-map hc hp (lift-morphism m)   r = r
Refs-map hc hp (morph-app m x)     (a , b) = a , Refs-map hc hp x b
Refs-map hc hp (comp' f g)         (a , b) = Refs-map hc hp f a , Refs-map hc hp g b
Refs-map hc hp (copair' f g)       (a , b) = Refs-map hc hp f a , Refs-map hc hp g b
Refs-map hc hp (fork' f g)         (a , b) = Refs-map hc hp f a , Refs-map hc hp g b
Refs-map hc hp (curry' f)          r = Refs-map hc hp f r
Refs-map hc hp (cata _ alg)        r = Refs-map hc hp alg r
Refs-map hc hp (ana _ coalg)       r = Refs-map hc hp coalg r

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
      (resolve-refs pre (C.cpolys csc) (<-wellFounded (length (C.cpolys csc))) (C.declImps (C.CScope.ctele csc)) uf 0 (realize D′)
         (LInv.tel-ok inv (C.declImps (C.CScope.ctele csc)) (LInv.iself inv))
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

postulate
  -- SCAFFOLD (plan 0.103 6a‴): a telescope entry joins the scope; its splice
  -- at every instance is linked (its body checks there, D243, and the
  -- realization's references are the scope's). Discharged next.
  linv-poly : ∀ {csc pre} {pfi : C.PolyFunInfo} {Ψ : Usage 0}
            → ctxWithImportsAndPolys (C.CScope.cimps csc) (C.cpolys csc) ⊢ᶜ pfunBody pfi ∶ rigidOf (pfunType pfi) ⨾ Ψ
            → All (pfunName pfi ≢_) (scopeNames csc)
            → LInv csc pre → LInv (C.addEntry csc pfi) pre

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
