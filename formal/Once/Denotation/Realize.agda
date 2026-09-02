-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Realize — the REFERENCE ELABORATION SEMANTICS (Plan 0.49
-- Phase 2 / route 2). This is part of the DENOTATIONAL SPEC, NOT the compiler.
--
-- `realize` turns a typing DERIVATION (`ctx ⊢ᶜ e ∶ A ⨾ Ψ`, which is term-free)
-- into the intrinsically-typed surface term it denotes. The *meaning* of a
-- source program is then `SD.⟦ realize D ⟧ˢ` — "elaborate (the reference way),
-- then denote". `realize` is the surface half of the authored semantics, the
-- companion to `SD.⟦_⟧ˢ` (term → trace).
--
-- ╔══════════════════════════════════════════════════════════════════╗
-- ║  ELABORATOR-FREE BY CONSTRUCTION — the no-cheat constraint.       ║
-- ║  This module MUST NOT import `Once.TypeCheck.Elaborate` (the       ║
-- ║  `checkElab`/`inferElab` algorithm). It reads the term off the    ║
-- ║  declarative derivation's STRUCTURE (built from the raw program +  ║
-- ║  deterministic lookups), never off `checkElab`'s output. If this   ║
-- ║  import line is ever added, the layering breaks and the agreement  ║
-- ║  bridge would cancel (proving the elaborator with the elaborator). ║
-- ║  The reviewer audits ONE thing: this import list excludes the      ║
-- ║  elaborator — exactly as 0.49 keeps the meaning free of the        ║
-- ║  compiler.                                                         ║
-- ╚══════════════════════════════════════════════════════════════════╝
--
-- `realize` is a DEFINITION (a total function); all PROOFS relating it to the
-- real `checkElab` (the agreement bridge) live in the proof layer
-- (`Once.Adequacy.*`), which is the only place allowed to import both.
------------------------------------------------------------------------

module Once.Denotation.Realize where

open import Data.Integer using (-_)   -- the folded payload of `g-neg-int` (plan 0.73 F3)
open import Data.String using (_++_)
open import Once.Type using (Type; Many; _*_; _+_; μ-type; ⟦_⟧T)
open import Once.IR as IR using (IR; _∘_; ⟨_,_⟩)
open import Once.IRTy using (⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.TypeCheck.Raw using (RawExpr;
  OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Judgment
  using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_;
         t-id-check; t-fst-check; t-snd-check; t-terminal-morph-check;
         t-initial-morph-check; t-inl-morph-check; t-inr-morph-check;
         t-compose-check; t-case-copair-check; t-pair-morph-check;
         t-curry-check; t-cata-check;
         m-compose; m-case; m-pair; m-curry; m-cata; m-const; m-named; m-named-resolved;
         t-int; t-float; t-str; t-unit; t-unit-var; t-var-local; t-var-qualified; t-var-resolved; t-var-import;
         t-annot; t-pair; t-neg; t-neg-float; t-let; t-case; t-binop-arith; t-binop-arith-float; t-binop-arith-float-il; t-binop-arith-float-ir; t-binop-cmp;
         t-id-app; t-fst-app; t-snd-app; t-terminal-app; t-apply-app-infer;
         t-app; t-effApp;
         t-embed; t-lam; t-value-lift; t-closed-lift; t-morph-lift; t-pair-lit-check; t-In-app-check;
         t-apply-check; t-inl-app-check; t-inr-app-check; t-initial-app-check;
         t-subsume; t-arg-driven-app-check; t-var-poly-instantiate;
         t-var-poly-instantiate-infer)
open import Once.Float.Decimal using (Decimal; decimalOf; negate)
open import Once.Surface.Thinning using (weaken)
open import Once.Surface.Syntax using (Expr; Usage; zeroUsage; var; svar; svar→expr;
  lam; app; effApp; pair; neg; let'; case'; int; float; str; unit;
  add; sub; mul; div; mod'; fadd; fsub; fmul; fdiv; i2f; lt; le; gt; ge; eq; ne; sigOp; poly;
  lift-morphism; morph-app; arr'; cata; comp'; copair'; fork'; curry')
open import Once.Surface.Elaborate using (intLit; floatLit; elaborate)
open import Once.Arith.SigOp.Builders using (value-info)
open import Once.CanonicalName using (bare)
open import Once.Surface.Syntax using (_+ᵘ_; _*ᵘ_)
open import Once.Surface.Properties using (+ᵘ-identityˡ; *ᵘ-zeroʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; trans; cong; sym)
import Relation.Binary.PropositionalEquality as PE

-- The reference elaboration (D063): a mutual block
--   realize       (⊢ᶜ → SExpr)   -- check-mode
--   realize-infer (⊢ᵢ → SExpr)   -- infer-mode
--   realize-morph (⊢ᵐ → IR)      -- morphism realm (below)
--   realize-global(⊢ᵍ → IR)      -- value realm (below)
-- Plan 0.58 (telescope): morph-app inflates the usage to
-- `zeroUsage +ᵘ Many *ᵘ zeroUsage`; a reference uses no local variables, so
-- this coerces it back to `zeroUsage`. TOP-LEVEL (not a `where`) so the bridge
-- can name it to see through `realize`'s poly `subst`.
poly-usage-eq : ∀ {n} → (zeroUsage {n}) +ᵘ (Many *ᵘ zeroUsage) ≡ zeroUsage
poly-usage-eq = trans (cong (zeroUsage +ᵘ_) (*ᵘ-zeroʳ Many)) (+ᵘ-identityˡ zeroUsage)

-- Forward signatures first (mutual recursion, no `mutual` keyword needed).
realize : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
            {Ψ : Usage (NamedCtx.size ctx)}
        → ctx ⊢ᶜ e ∶ A ⨾ Ψ → Expr (NamedCtx.debruijn ctx) Ψ A
realize-infer : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type}
                {Ψ : Usage (NamedCtx.size ctx)}
              → ctx ⊢ᵢ e ∶ A ⨾ Ψ → Expr (NamedCtx.debruijn ctx) Ψ A


------------------------------------------------------------------------
-- realize (⊢ᶜ) — check-mode reference elaboration.
-- The two bridge clauses route morphisms/values through the direct
-- categorical IR (forcing the laws); the rest are the genuinely
-- bidirectional / value-former rules kept in `⊢ᶜ`.
------------------------------------------------------------------------
-- D127: the combinators realize to the SURFACE term formers, not to a
-- separate morphism realm. The point-free leaves are still the plain
-- categorical generators — those were always closed and still are.
realize (t-id-check)             = lift-morphism IR.id
realize (t-fst-check)            = lift-morphism IR.fst
realize (t-snd-check)            = lift-morphism IR.snd
realize (t-terminal-morph-check) = lift-morphism IR.terminal
realize (t-initial-morph-check)  = lift-morphism IR.initial
realize (t-inl-morph-check)      = lift-morphism (IR.inl IR.Heap)
realize (t-inr-morph-check)      = lift-morphism (IR.inr IR.Heap)
realize (t-compose-check _ df dg)    = comp'   (realize df) (realize dg)
realize (t-case-copair-check df dg)  = copair' (realize df) (realize dg)
realize (t-pair-morph-check df dg)   = fork'   (realize df) (realize dg)
realize (t-curry-check df)           = curry'  (realize df)
realize (t-cata-check wfF dalg) = cata wfF (realize dalg)
realize (t-embed d)             = realize-infer d
realize (t-lam {q = q} ≤p d)    = lam q ≤p (realize d)
realize (t-pair-lit-check da db) = pair (realize da) (realize db)
realize (t-In-app-check {F = F} wfF d) =
  morph-app (subst (λ o → IR o ⌊ μ-type F ⌋) (sym (⌊⟧T-commute F (μ-type F))) (IR.In (wf-⌊⌋ wfF) IR.Heap)) (realize d)
realize (t-apply-check dp)      = morph-app IR.apply (realize-infer dp)
realize (t-inl-app-check d)     = morph-app (IR.inl IR.Heap) (realize d)
realize (t-inr-app-check d)     = morph-app (IR.inr IR.Heap) (realize d)
realize (t-initial-app-check d) = morph-app IR.initial (realize d)
realize (t-subsume d)           = arr' (realize d)
realize (t-arg-driven-app-check _ darg df) = app (realize df) (realize-infer darg)
-- Plan 0.58 (telescope / E1): a same-module def reference realizes to its
-- closed body's IR, wrapped as a closed morphism applied to `unit` — so its
-- denotation is env-independent BY DEFINITION (`⟦ morph-app ir unit ⟧ˢ dγ =
-- evalᴰ ir tt`), reusing existing combinators. No `poly` surface node (E1).
realize {ctx = ctx} {A = A} (t-var-poly-instantiate _ _ _ _ bodyD) =
  subst (λ u → Expr (NamedCtx.debruijn ctx) u A) poly-usage-eq
        (morph-app {Ψ = zeroUsage} (elaborate IR.Heap (realize bodyD)) unit)

------------------------------------------------------------------------
-- realize-infer (⊢ᵢ) — infer-mode reference elaboration.
------------------------------------------------------------------------
realize-infer (t-int n)         = int n
realize-infer (t-float i f l p) = float (decimalOf i f l)
realize-infer (t-str s)         = str s
realize-infer t-unit            = unit
realize-infer t-unit-var        = unit
realize-infer (t-var-local {eV = eV} _) = svar→expr eV
realize-infer (t-var-qualified {name = name} {alias = alias} _ conc) = sigOp (bare (alias ++ "." ++ name)) conc
-- Plan 0.50: a resolved ref carries its canonical identity directly — the
-- reference elaboration reads it with NO String render, so it agrees with
-- the elaborator's `SigOpInfo.name` by construction.
realize-infer (t-var-resolved {cn = cn} _ _ conc) = sigOp cn conc
realize-infer (t-var-import {x = x} _ _ _ conc) = sigOp (bare x) conc
-- Plan 0.58 / D071: infer-mode ground telescope reference — same closed-body
-- inline as the check-mode `t-var-poly-instantiate` clause above.
realize-infer {ctx = ctx} {A = A} (t-var-poly-instantiate-infer _ _ _ _ _ bodyD) =
  subst (λ u → Expr (NamedCtx.debruijn ctx) u A) poly-usage-eq
        (morph-app {Ψ = zeroUsage} (elaborate IR.Heap (realize bodyD)) unit)
realize-infer (t-annot d)       = realize d
realize-infer (t-pair da db)    = pair (realize-infer da) (realize-infer db)
realize-infer (t-neg d)         = neg (realize-infer d)
-- PLAN 0.73 F3. Unlike the `Int` fold — where `realize-infer` keeps
-- `neg (int n)` and `RealizeAgrees` spends `⊝-fromℤ` to reconcile it with the
-- elaborator's folded literal — there is nothing here to keep: `Surface.neg`
-- is `Expr Γ Ψ Int → Expr Γ Ψ Int`, so a float negation is not expressible in
-- the surface syntax at all. The reference elaboration folds because it has
-- no choice, and agreement with the elaborator is `refl`.
realize-infer (t-neg-float i f l p) = float (negate (decimalOf i f l))
realize-infer (t-let d₁ d₂)     = let' (realize-infer d₁) (realize-infer d₂)
realize-infer (t-case ds dl dr) = case' (realize-infer ds) (realize-infer dl) (realize-infer dr)
-- arithmetic binops: pick the SExpr ctor by `op`; comparison ops make the
-- `isArithmeticOp op ≡ true` premise absurd.
realize-infer (t-binop-arith {op = OpAdd} _ d₁ d₂) = add  (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-arith {op = OpSub} _ d₁ d₂) = sub  (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-arith {op = OpMul} _ d₁ d₂) = mul  (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-arith {op = OpDiv} _ d₁ d₂) = div  (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-arith {op = OpMod} _ d₁ d₂) = mod' (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-arith {op = OpLt} () _ _)
realize-infer (t-binop-arith {op = OpLe} () _ _)
realize-infer (t-binop-arith {op = OpGt} () _ _)
realize-infer (t-binop-arith {op = OpGe} () _ _)
realize-infer (t-binop-arith {op = OpEq} () _ _)
realize-infer (t-binop-arith {op = OpNe} () _ _)
-- PLAN 0.75 F4.
realize-infer (t-binop-arith-float {op = OpAdd} _ d₁ d₂) = fadd (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-arith-float {op = OpSub} _ d₁ d₂) = fsub (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-arith-float {op = OpMul} _ d₁ d₂) = fmul (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-arith-float {op = OpDiv} _ d₁ d₂) = fdiv (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-arith-float {op = OpMod} () _ _)
realize-infer (t-binop-arith-float {op = OpLt} () _ _)
realize-infer (t-binop-arith-float {op = OpLe} () _ _)
realize-infer (t-binop-arith-float {op = OpGt} () _ _)
realize-infer (t-binop-arith-float {op = OpGe} () _ _)
realize-infer (t-binop-arith-float {op = OpEq} () _ _)
realize-infer (t-binop-arith-float {op = OpNe} () _ _)
-- D125: the mixed forms wrap the Int side in `i2f`.
realize-infer (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) = fadd (i2f (realize-infer d₁)) (realize-infer d₂)
realize-infer (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) = fsub (i2f (realize-infer d₁)) (realize-infer d₂)
realize-infer (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) = fmul (i2f (realize-infer d₁)) (realize-infer d₂)
realize-infer (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) = fdiv (i2f (realize-infer d₁)) (realize-infer d₂)
realize-infer (t-binop-arith-float-il {op = OpMod} () _ _)
realize-infer (t-binop-arith-float-il {op = OpLt} () _ _)
realize-infer (t-binop-arith-float-il {op = OpLe} () _ _)
realize-infer (t-binop-arith-float-il {op = OpGt} () _ _)
realize-infer (t-binop-arith-float-il {op = OpGe} () _ _)
realize-infer (t-binop-arith-float-il {op = OpEq} () _ _)
realize-infer (t-binop-arith-float-il {op = OpNe} () _ _)
realize-infer (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) = fadd (realize-infer d₁) (i2f (realize-infer d₂))
realize-infer (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) = fsub (realize-infer d₁) (i2f (realize-infer d₂))
realize-infer (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) = fmul (realize-infer d₁) (i2f (realize-infer d₂))
realize-infer (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) = fdiv (realize-infer d₁) (i2f (realize-infer d₂))
realize-infer (t-binop-arith-float-ir {op = OpMod} () _ _)
realize-infer (t-binop-arith-float-ir {op = OpLt} () _ _)
realize-infer (t-binop-arith-float-ir {op = OpLe} () _ _)
realize-infer (t-binop-arith-float-ir {op = OpGt} () _ _)
realize-infer (t-binop-arith-float-ir {op = OpGe} () _ _)
realize-infer (t-binop-arith-float-ir {op = OpEq} () _ _)
realize-infer (t-binop-arith-float-ir {op = OpNe} () _ _)
-- comparison binops: dual.
realize-infer (t-binop-cmp {op = OpLt} _ d₁ d₂) = lt (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-cmp {op = OpLe} _ d₁ d₂) = le (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-cmp {op = OpGt} _ d₁ d₂) = gt (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-cmp {op = OpGe} _ d₁ d₂) = ge (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-cmp {op = OpEq} _ d₁ d₂) = eq (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-cmp {op = OpNe} _ d₁ d₂) = ne (realize-infer d₁) (realize-infer d₂)
realize-infer (t-binop-cmp {op = OpAdd} () _ _)
realize-infer (t-binop-cmp {op = OpSub} () _ _)
realize-infer (t-binop-cmp {op = OpMul} () _ _)
realize-infer (t-binop-cmp {op = OpDiv} () _ _)
realize-infer (t-binop-cmp {op = OpMod} () _ _)
realize-infer (t-id-app d)       = morph-app IR.id       (realize-infer d)
realize-infer (t-fst-app d)      = morph-app IR.fst      (realize-infer d)
realize-infer (t-snd-app d)      = morph-app IR.snd      (realize-infer d)
realize-infer (t-terminal-app d) = morph-app IR.terminal (realize-infer d)
realize-infer (t-apply-app-infer d) = morph-app IR.apply (realize-infer d)
realize-infer (t-app _ df dx)    = app    (realize-infer df) (realize dx)
realize-infer (t-effApp _ df dx) = effApp (realize-infer df) (realize dx)
