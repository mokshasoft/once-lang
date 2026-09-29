-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Elaboration — plan 0.103 phase 6b (plan 0.102 C): THE SURFACE
-- ELABORATES INTO THE CORE.
--
-- SPEC. Every surface derivation (`⊢ᶜ`/`⊢ᵢ`/`⊢ᵈ`) elaborates to a core term and
-- a core derivation of it at the SAME context, usage and type, at grade `pure`
-- (a surface expression's effects live on its arrows). Soundness is by
-- construction: the output IS a core derivation.
--
-- The shape is `realize`'s, clause by clause, so the meaning bridge is too:
--   * a combinator is its `Derived` definition (`DerivedTyping` types it at
--     the rule's exact usage);
--   * an applied builtin (`fst e`, `In e`, …) applies the closed definition,
--     `app Xᶜ e`, which is where the surface's `zeroUsage +ᵘ Many *ᵘ Ψ` comes from;
--   * arithmetic is the core's saturated `prim`;
--   * an FFI reference is `sigop`, a telescope reference `ref d τ`.
--
-- The module layer is an argument, not an assumption: a `View` says the
-- imports are honest (D231: checked at the FFI declaration) and names each
-- telescope entry's core index and the kind-respecting instance a use is at.
-- Phase 6c/6d construct it from the module.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)

module Once.Spec.Elaboration {s : ℕ} (S : Sig s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)

open import Once.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; mk-kind; Many; Purity; pure; eff;
  μ-type; ν-type; ⟦_⟧T; PolyType; Ground; extractGround; IsInstance)
open import Once.Type.Sub using (_<:_; sub-arr; <:-refl)
open import Once.Type.Honest using (HonestFFI)
open import Once.CanonicalName using (bare; showCanonical)
open import Once.Float.Decimal using (decimalOf; negate)
open import Once.Functor.Translate using (IsConcrete)
open import Once.Surface.Context using (Ctx; ∅; Usage; zeroUsage; _+ᵘ_; _*ᵘ_)
open import Once.Surface.Properties using (+ᵘ-identityʳ)
open import Once.TypeCheck.Raw using (RawExpr;
  OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.TypeCheck.Classify using (NamedCtx; Imports; PolyCtx; lookupImport; lookupPolyPrefix;
  ctxWithImportsAndPolys)
open import Once.TypeCheck.Judgment
open import Once.Spec.Core.PolyTy using (_!!_; arity; kinds; type; Respects; GSub; _⟪_⟫)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
open import Once.Spec.Core.Derived S
open import Once.Spec.Core.DerivedTyping S
open import Once.Spec.Core.Rename S using (close; ⊢close)

------------------------------------------------------------------------
-- The module layer, as seen by an expression
------------------------------------------------------------------------

-- `T` is a kind-respecting instance of the entry `d`.
InstanceOf : Fin s → Type → Set
InstanceOf d T = Σ[ τ ∈ GSub (arity (S !! d)) ] Respects (kinds (S !! d)) τ × (type (S !! d) ⟪ τ ⟫ ≡ T)

record View (imps : Imports) (polys : PolyCtx) : Set where
  field
    honest : ∀ {x T} → lookupImport imps x ≡ just T → HonestFFI T
    entry  : ∀ {x sc body prefix} → lookupPolyPrefix polys x ≡ just (sc , body , prefix) → Fin s
    ground : ∀ {x sc body prefix} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix)) (g : Ground sc)
           → InstanceOf (entry lp) (extractGround sc g)
    inst   : ∀ {x sc body prefix T} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
           → ¬ Ground sc → IsInstance sc T
           → ctxWithImportsAndPolys imps prefix ⊢ᶜ body ∶ T ⨾ zeroUsage
           → InstanceOf (entry lp) T
open View

Views : NamedCtx → Set
Views ctx = View (NamedCtx.imports ctx) (NamedCtx.polys ctx)

------------------------------------------------------------------------
-- Elaborated terms
------------------------------------------------------------------------

Elab : ∀ {n} → Ctx n → Usage n → Type → Set
Elab {n} Γ Ψ A = Σ[ t ∈ Tm n ] Γ ⊢[ Ψ ] t ∷ A ! pure

private
  variable
    n : ℕ
    Γ : Ctx n
    Ψ Ψ₁ Ψ₂ Ψ′ : Usage n
    A B : Type

  lift1 : (f : Tm n → Tm n) → (∀ {t} → Γ ⊢[ Ψ ] t ∷ A ! pure → Γ ⊢[ Ψ′ ] f t ∷ B ! pure)
        → Elab Γ Ψ A → Elab Γ Ψ′ B
  lift1 f h (t , d) = f t , h d

  lift2 : ∀ {C : Type} {Ψ₃ : Usage n} (f : Tm n → Tm n → Tm n)
        → (∀ {t u} → Γ ⊢[ Ψ₁ ] t ∷ A ! pure → Γ ⊢[ Ψ₂ ] u ∷ B ! pure → Γ ⊢[ Ψ₃ ] f t u ∷ C ! pure)
        → Elab Γ Ψ₁ A → Elab Γ Ψ₂ B → Elab Γ Ψ₃ C
  lift2 f h (t , d) (u , e) = f t u , h d e

  -- A closed combinator applied: the surface's `zeroUsage +ᵘ Many *ᵘ Ψ`.
  appC : ∀ {c} → Γ ⊢[ zeroUsage ] c ∷ A ⇒[ mk-kind Many pure ] B ! pure
       → Elab Γ Ψ A → Elab Γ (zeroUsage +ᵘ Many *ᵘ Ψ) B
  appC {c = c} dc = lift1 (app c) (⊢app dc)

  -- A binary operation: the saturated primitive on the pair of its operands.
  bin : (p : Prim) → primDom p ≡ A * B → Elab Γ Ψ₁ A → Elab Γ Ψ₂ B → Elab Γ (Ψ₁ +ᵘ Ψ₂) (primCod p)
  bin p eq = lift2 (λ t u → prim p (pair t u)) (λ d e → ⊢prim p (subst (λ D → _ ⊢[ _ ] _ ∷ D ! pure) (sym eq) (⊢pair d e)))

  i2f : Elab Γ Ψ Int → Elab Γ Ψ Float
  i2f = lift1 (prim p-i2f) (⊢prim p-i2f)

  coerceE : A <: B → Elab Γ Ψ A → Elab Γ Ψ B
  coerceE {A = A} {B = B} p = lift1 (coerce A B) (⊢coerce p)

  sigopE : ∀ {imps polys x} (c : Once.CanonicalName.CanonicalName) → View imps polys → lookupImport imps x ≡ just A → IsConcrete A
         → Elab Γ zeroUsage A
  sigopE {A = A} c V lk k = sigop c A , ⊢sigop c k (honest V lk)

  refE : (d : Fin s) → InstanceOf d A → Elab Γ zeroUsage A
  refE {Γ = Γ} d (τ , r , eq) = ref d τ , subst (λ T → Γ ⊢[ zeroUsage ] ref d τ ∷ T ! pure) eq (⊢ref d τ r)

  closeE : Elab ∅ zeroUsage A → Elab Γ zeroUsage A
  closeE (t , d) = close t , ⊢close d

  subE : Ψ ≡ Ψ′ → Elab Γ Ψ A → Elab Γ Ψ′ A
  subE refl e = e


------------------------------------------------------------------------
-- The elaboration
------------------------------------------------------------------------

elabᶜ : ∀ {ctx e A Ψ} → Views ctx → ctx ⊢ᶜ e ∶ A ⨾ Ψ → Elab (NamedCtx.debruijn ctx) Ψ A
elabᵢ : ∀ {ctx e A Ψ} → Views ctx → ctx ⊢ᵢ e ∶ A ⨾ Ψ → Elab (NamedCtx.debruijn ctx) Ψ A
elabᵈ : ∀ {ctx e A B π Ψ} → Views ctx → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ
      → Elab (NamedCtx.debruijn ctx) Ψ (A ⇒[ mk-kind Many π ] B)

elabᶜ V t-id-check             = idᶜ , ⊢idᶜ
elabᶜ V t-fst-check            = fstᶜ , ⊢fstᶜ
elabᶜ V t-snd-check            = sndᶜ , ⊢sndᶜ
elabᶜ V t-terminal-morph-check = terminalᶜ , ⊢terminalᶜ
elabᶜ V t-initial-morph-check  = initialᶜ , ⊢initialᶜ
elabᶜ V t-inl-morph-check      = inlᶜ , ⊢inlᶜ
elabᶜ V t-inr-morph-check      = inrᶜ , ⊢inrᶜ
elabᶜ V (t-compose-check-g dg df)   = lift2 composeᶜ ⊢composeᶜ (elabᶜ V df) (elabᵈ V dg)
elabᶜ V (t-compose-check-f wf p dg) = lift2 composeᶜ ⊢composeᶜ (coerceE p (elabᵢ V wf)) (elabᶜ V dg)
elabᶜ V (t-case-copair-check df dg) = lift2 caseᶜ ⊢caseᶜ (elabᶜ V df) (elabᶜ V dg)
elabᶜ V (t-pair-morph-check df dg)  = lift2 pairᶜ ⊢pairᶜ (elabᶜ V df) (elabᶜ V dg)
elabᶜ V (t-curry-check df)          = lift1 curryᶜ ⊢curryᶜ (elabᶜ V df)
elabᶜ V (t-cata-check wf dalg)      = lift1 cataᶜ (⊢cataᶜ wf) (closeE (elabᶜ V dalg))
elabᶜ V (t-ana-check wf dc)         = lift1 anaᶜ (⊢anaᶜ wf) (closeE (elabᶜ V dc))
elabᶜ V (t-sub d p)                 = coerceE p (elabᵢ V d)
elabᶜ V (t-lam {π = π} ≤p d)        = let (b , ⊢b) = elabᶜ V d in lam b , ⊢lam ≤p (⊢sub-eff (pure⊑ π) ⊢b)
elabᶜ V (t-pair-lit-check da db)    = lift2 pair ⊢pair (elabᶜ V da) (elabᶜ V db)
elabᶜ V (t-In-app-check wf d)       = appC (⊢inᶜ wf) (elabᶜ V d)
elabᶜ V (t-apply-check dp)          = appC ⊢applyᶜ (elabᵢ V dp)
elabᶜ V (t-inl-app-check d)         = appC ⊢inlᶜ (elabᶜ V d)
elabᶜ V (t-inr-app-check d)         = appC ⊢inrᶜ (elabᶜ V d)
elabᶜ V (t-initial-app-check d)     = appC ⊢initialᶜ (elabᶜ V d)
elabᶜ V (t-var-poly-instantiate _ _ lp ng ins bodyD) = refE (entry V lp) (inst V lp ng ins bodyD)

elabᵢ V (t-int n)         = lit (lit-int n) , ⊢lit-int
elabᵢ V (t-float i f l p) = lit (lit-float (decimalOf i f l)) , ⊢lit-float
elabᵢ V (t-str s)         = lit (lit-str s) , ⊢lit-str
elabᵢ V t-unit            = unit , ⊢unit
elabᵢ V t-unit-var        = unit , ⊢unit
elabᵢ V (t-var-local {eV = Once.Surface.Context.svar i} _) = var i , ⊢var i
elabᵢ V (t-var-qualified {name = name} {alias = alias} lk k) = sigopE (bare (alias ++ "." ++ name)) V lk k
elabᵢ V (t-var-resolved {cn = cn} _ lk k) = sigopE cn V lk k
elabᵢ V (t-var-import {x = x} _ _ lk k)    = sigopE (bare x) V lk k
elabᵢ V (t-var-poly-instantiate-infer {g = g} _ _ lp _ refl) = refE (entry V lp) (ground V lp g)
elabᵢ V (t-annot d)       = elabᶜ V d
elabᵢ V (t-pair da db)    = lift2 pair ⊢pair (elabᵢ V da) (elabᵢ V db)
elabᵢ V (t-neg d)         = lift1 (prim p-neg) (⊢prim p-neg) (elabᵢ V d)
elabᵢ V (t-neg-float i f l p) = lit (lit-float (negate (decimalOf i f l))) , ⊢lit-float
elabᵢ V (t-let d₁ d₂)     = let (e , ⊢e) = elabᵢ V d₁ ; (b , ⊢b) = elabᵢ V d₂ in let′ e b , ⊢let ⊢e ⊢b
elabᵢ V (t-case ds dl dr) =
  let (s , ⊢s) = elabᵢ V ds ; (l , ⊢l) = elabᵢ V dl ; (r , ⊢r) = elabᵢ V dr
  in case s l r , ⊢case ⊢s ⊢l ⊢r
elabᵢ V (t-binop-arith {op = OpAdd} _ d₁ d₂) = bin p-add refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-arith {op = OpSub} _ d₁ d₂) = bin p-sub refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-arith {op = OpMul} _ d₁ d₂) = bin p-mul refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-arith {op = OpDiv} _ d₁ d₂) = bin p-div refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-arith {op = OpMod} _ d₁ d₂) = bin p-mod refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-arith {op = OpLt} () _ _)
elabᵢ V (t-binop-arith {op = OpLe} () _ _)
elabᵢ V (t-binop-arith {op = OpGt} () _ _)
elabᵢ V (t-binop-arith {op = OpGe} () _ _)
elabᵢ V (t-binop-arith {op = OpEq} () _ _)
elabᵢ V (t-binop-arith {op = OpNe} () _ _)
elabᵢ V (t-binop-arith-float {op = OpAdd} _ d₁ d₂) = bin p-fadd refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-arith-float {op = OpSub} _ d₁ d₂) = bin p-fsub refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-arith-float {op = OpMul} _ d₁ d₂) = bin p-fmul refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-arith-float {op = OpDiv} _ d₁ d₂) = bin p-fdiv refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-arith-float {op = OpMod} () _ _)
elabᵢ V (t-binop-arith-float {op = OpLt} () _ _)
elabᵢ V (t-binop-arith-float {op = OpLe} () _ _)
elabᵢ V (t-binop-arith-float {op = OpGt} () _ _)
elabᵢ V (t-binop-arith-float {op = OpGe} () _ _)
elabᵢ V (t-binop-arith-float {op = OpEq} () _ _)
elabᵢ V (t-binop-arith-float {op = OpNe} () _ _)
elabᵢ V (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) = bin p-fadd refl (i2f (elabᵢ V d₁)) (elabᵢ V d₂)
elabᵢ V (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) = bin p-fsub refl (i2f (elabᵢ V d₁)) (elabᵢ V d₂)
elabᵢ V (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) = bin p-fmul refl (i2f (elabᵢ V d₁)) (elabᵢ V d₂)
elabᵢ V (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) = bin p-fdiv refl (i2f (elabᵢ V d₁)) (elabᵢ V d₂)
elabᵢ V (t-binop-arith-float-il {op = OpMod} () _ _)
elabᵢ V (t-binop-arith-float-il {op = OpLt} () _ _)
elabᵢ V (t-binop-arith-float-il {op = OpLe} () _ _)
elabᵢ V (t-binop-arith-float-il {op = OpGt} () _ _)
elabᵢ V (t-binop-arith-float-il {op = OpGe} () _ _)
elabᵢ V (t-binop-arith-float-il {op = OpEq} () _ _)
elabᵢ V (t-binop-arith-float-il {op = OpNe} () _ _)
elabᵢ V (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) = bin p-fadd refl (elabᵢ V d₁) (i2f (elabᵢ V d₂))
elabᵢ V (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) = bin p-fsub refl (elabᵢ V d₁) (i2f (elabᵢ V d₂))
elabᵢ V (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) = bin p-fmul refl (elabᵢ V d₁) (i2f (elabᵢ V d₂))
elabᵢ V (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) = bin p-fdiv refl (elabᵢ V d₁) (i2f (elabᵢ V d₂))
elabᵢ V (t-binop-arith-float-ir {op = OpMod} () _ _)
elabᵢ V (t-binop-arith-float-ir {op = OpLt} () _ _)
elabᵢ V (t-binop-arith-float-ir {op = OpLe} () _ _)
elabᵢ V (t-binop-arith-float-ir {op = OpGt} () _ _)
elabᵢ V (t-binop-arith-float-ir {op = OpGe} () _ _)
elabᵢ V (t-binop-arith-float-ir {op = OpEq} () _ _)
elabᵢ V (t-binop-arith-float-ir {op = OpNe} () _ _)
elabᵢ V (t-binop-cmp {op = OpLt} _ d₁ d₂) = bin p-lt refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-cmp {op = OpLe} _ d₁ d₂) = bin p-le refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-cmp {op = OpGt} _ d₁ d₂) = bin p-gt refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-cmp {op = OpGe} _ d₁ d₂) = bin p-ge refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-cmp {op = OpEq} _ d₁ d₂) = bin p-eq refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-cmp {op = OpNe} _ d₁ d₂) = bin p-ne refl (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-binop-cmp {op = OpAdd} () _ _)
elabᵢ V (t-binop-cmp {op = OpSub} () _ _)
elabᵢ V (t-binop-cmp {op = OpMul} () _ _)
elabᵢ V (t-binop-cmp {op = OpDiv} () _ _)
elabᵢ V (t-binop-cmp {op = OpMod} () _ _)
elabᵢ V (t-id-app d)       = appC ⊢idᶜ (elabᵢ V d)
elabᵢ V (t-fst-app d)      = appC ⊢fstᶜ (elabᵢ V d)
elabᵢ V (t-snd-app d)      = appC ⊢sndᶜ (elabᵢ V d)
elabᵢ V (t-terminal-app d) = appC ⊢terminalᶜ (elabᵢ V d)
elabᵢ V (t-apply-app-infer d)     = appC ⊢applyᶜ (elabᵢ V d)
elabᵢ V (t-apply-eff-app-infer d) = appC ⊢applyEffᶜ (elabᵢ V d)
elabᵢ V (t-Out-app-infer wf refl d)     = appC (⊢outᶜ wf) (elabᵢ V d)
elabᵢ V (t-Out-eff-app-infer wf refl d) = appC (⊢outEffᶜ wf) (elabᵢ V d)
elabᵢ V (t-app _ df dx)    = lift2 app ⊢app (elabᵢ V df) (elabᶜ V dx)
elabᵢ V (t-effApp _ df dx) = lift2 effAppᶜ ⊢effAppᶜ (elabᵢ V df) (elabᶜ V dx)
elabᵢ V (t-app-spine _ dx df) = lift2 app ⊢app (elabᵈ V df) (elabᵢ V dx)
elabᵢ V (t-neg-void d)           = elabᵢ V d
elabᵢ V (t-case-void dS _ _)     = elabᵢ V dS
elabᵢ V (t-binop-void-l d₁ _)    = elabᵢ V d₁
elabᵢ V (t-binop-void-r d₁ _ d₂) = lift2 seqᶜ ⊢seqᶜ (elabᵢ V d₁) (elabᵢ V d₂)
elabᵢ V (t-fst-app-void d)       = appC ⊢initialᶜ (elabᵢ V d)
elabᵢ V (t-snd-app-void d)       = appC ⊢initialᶜ (elabᵢ V d)
elabᵢ V (t-apply-app-void d)     = appC ⊢initialᶜ (elabᵢ V d)
elabᵢ V (t-Out-app-void d)       = appC ⊢initialᶜ (elabᵢ V d)
elabᵢ V (t-app-void _ dF _)      = elabᵢ V dF

elabᵈ V (d-infer {B = B} w a g) = coerceE (sub-arr a (<:-refl B) g) (elabᵢ V w)
elabᵈ V (d-poly {A = A} {B = B} _ _ lp ng _ _ ins g bodyD) =
  coerceE (sub-arr (<:-refl A) (<:-refl B) g) (refE (entry V lp) (inst V lp ng ins bodyD))
elabᵈ V (d-lam {π = π} ≤p d) = let (b , ⊢b) = elabᵢ V d in lam b , ⊢lam ≤p (⊢sub-eff (pure⊑ π) ⊢b)
elabᵈ V (d-compose dg df)    = lift2 composeᶜ ⊢composeᶜ (elabᵈ V df) (elabᵈ V dg)
elabᵈ V d-id       = idᶜ , ⊢idᶜ
elabᵈ V d-fst      = fstᶜ , ⊢fstᶜ
elabᵈ V d-snd      = sndᶜ , ⊢sndᶜ
elabᵈ V d-terminal = terminalᶜ , ⊢terminalᶜ
elabᵈ V d-initial  = initialᶜ , ⊢initialᶜ
elabᵈ V (d-case df dg) = lift2 caseᶜ ⊢caseᶜ (elabᵈ V df) (elabᵈ V dg)
elabᵈ V (d-pair df dg) = lift2 pairᶜ ⊢pairᶜ (elabᵈ V df) (elabᵈ V dg)
elabᵈ V (d-cata wf dalg) = lift1 cataᶜ (⊢cataᶜ wf) (closeE (elabᵢ V dalg))
elabᵈ V d-fst-void = initialᶜ , ⊢initialᶜ
elabᵈ V d-snd-void = initialᶜ , ⊢initialᶜ
elabᵈ V (d-case-void {Ψ₂ = Ψ₂} df dg) =
  subE (cong (_ +ᵘ_) (+ᵘ-identityʳ Ψ₂))
    (lift2 seqᶜ ⊢seqᶜ (elabᵈ V df) (lift1 (λ g → seqᶜ g initialᶜ) (λ d → ⊢seqᶜ d ⊢initialᶜ) (elabᵈ V dg)))
elabᵈ V (d-cata-void dalg) =
  subE (+ᵘ-identityʳ zeroUsage) (lift1 (λ a → seqᶜ a initialᶜ) (λ d → ⊢seqᶜ d ⊢initialᶜ) (closeE (elabᵢ V dalg)))
