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
  using (_⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_; _⊢ᵍ_∶_; g-int; g-float; g-neg-int; g-neg-float; g-terminal; g-pair; g-inl; g-inr; g-In;
         _⊢ᵐ_∶_⇨[_]_; m-id; m-fst; m-snd; m-terminal; m-initial; m-inl; m-inr;
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
  add; sub; mul; div; mod'; fadd; fsub; fmul; i2f; lt; le; gt; ge; eq; ne; sigOp; poly;
  lift-morphism; morph-app; arr')
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
-- realize-global — the VALUE realm (⊢ᵍ) → its global-element IR.
--
-- The closed-value half of the CCC trichotomy (D063): a `⊢ᵍ` derivation
-- denotes a global element, read off the (term-free) derivation as the
-- direct IR — the elaborator-free mirror of `checkG`'s IR construction
-- (`Once.TypeCheck.Elaborate.checkG`, which `realize` must NOT import).
-- Parametric in the domain `X`: a global element `X → A` factors through
-- the terminal, so the constructors ignore `X`. Reused by `realize-morph`'s
-- `m-const` leaf (a value used where a morphism is expected = const morphism).
------------------------------------------------------------------------
realize-global : ∀ {ctx : NamedCtx} {e : RawExpr} {A X : Type}
               → ctx ⊢ᵍ e ∶ A → IR ⌊ X ⌋ ⌊ A ⌋
realize-global (g-int n)        = intLit n
-- PLAN 0.73 F3 / D120's other half: the FOLDED payload, so the value realm
-- and the infer realm produce the same IR object for the same source text.
realize-global (g-neg-int n)    = intLit (- n)
realize-global (g-neg-float i f l p) = floatLit (negate (decimalOf i f l))
-- The reference elaboration reads the DYADIC off the acceptance witness — the
-- same value the elaborator uses — so the two cannot disagree about what the
-- literal denotes.
realize-global (g-float i f l p) = floatLit (decimalOf i f l)
realize-global (g-terminal _ _) = IR.terminal
realize-global (g-pair ga gb)   = ⟨ realize-global ga , realize-global gb ⟩ IR.Heap
realize-global (g-inl ga)       = IR.inl IR.Heap ∘ realize-global ga
realize-global (g-inr gb)       = IR.inr IR.Heap ∘ realize-global gb
realize-global (g-In {F = F} {wfF = wfF} _ garg) =
  IR.In (wf-⌊⌋ wfF) IR.Heap ∘ subst (λ o → IR ⌊ _ ⌋ o) (⌊⟧T-commute F (μ-type F)) (realize-global garg)

------------------------------------------------------------------------
-- realize-morph — the MORPHISM realm (⊢ᵐ) → its categorical IR (D063).
--
-- The middle of the CCC trichotomy. STRUCTURAL on the combinators
-- (`m-compose`/`m-case`/`m-pair`/`m-curry`/`m-cata`) → the DIRECT
-- categorical IR (`IR.∘`/`IR.case`/`IR.⟨_,_⟩`/`IR.curry`/`IR.Cata`), so the
-- agreement bridge forces the categorical LAWS. EXTENSIONAL leaves:
--   • `m-const` → `realize-global` (a value is a constant morphism).
--   • `m-named` → `IR.SigOp (value-info x)` — the PRINCIPLED morphism form
--     (D064: a named def IS a morphism; the closure-returner ABI is corrected
--     separately, bridged meanwhile by `realize-agrees` via the β/uncurry iso).
--   • `m-lam`  → the closed lambda's body interpreted in the one-variable
--     context `(∅, x)` and supplied the unit: `elaborate (realize body) ∘
--     ⟨ terminal , id ⟩`. (Uses `realize` (the ⊢ᶜ reference) + `elaborate`
--     (row-2, verified by `faithful`) — NOT `checkElab`, so the elaborator-free
--     boundary holds.)
------------------------------------------------------------------------
realize-morph : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {π : Once.Type.Purity}
              → ctx ⊢ᵐ e ∶ A ⇨[ π ] B → IR ⌊ A ⌋ ⌊ B ⌋
realize-morph (m-id _ _)        = IR.id
realize-morph (m-fst _ _)       = IR.fst
realize-morph (m-snd _ _)       = IR.snd
realize-morph (m-terminal _ _)  = IR.terminal
realize-morph (m-initial _ _)   = IR.initial
realize-morph (m-inl _ _)       = IR.inl IR.Heap
realize-morph (m-inr _ _)       = IR.inr IR.Heap
realize-morph (m-compose _ df dg) = realize-morph df ∘ realize-morph dg
realize-morph (m-case df dg)    = IR.case (realize-morph df) (realize-morph dg)
realize-morph (m-pair df dg)    = ⟨ realize-morph df , realize-morph dg ⟩ IR.Heap
realize-morph (m-curry df)      = IR.curry (realize-morph df) IR.Heap
-- Plan 0.54: DIRECT — the algebra is a morphism (`⊢ᵐ`), read straight to its
-- categorical IR; no `elaborate` round-trip, uniform with the other combinators.
realize-morph (m-cata {F = F} {wfF = wfF} _ dalg) =
  IR.Cata (wf-⌊⌋ wfF) (subst (λ o → IR o ⌊ _ ⌋) (⌊⟧T-commute F _) (realize-morph dalg))
realize-morph (m-const gd)      = realize-global gd
realize-morph (m-named {x = x} _ _ _ bA cB) = IR.SigOp (value-info (bare x) bA cB)
realize-morph (m-named-resolved {cn = cn} _ bA cB) = IR.SigOp (value-info cn bA cB)

------------------------------------------------------------------------
-- realize (⊢ᶜ) — check-mode reference elaboration.
-- The two bridge clauses route morphisms/values through the direct
-- categorical IR (forcing the laws); the rest are the genuinely
-- bidirectional / value-former rules kept in `⊢ᶜ`.
------------------------------------------------------------------------
realize (t-morph-lift d)        = lift-morphism (realize-morph d)
realize (t-value-lift g)        = lift-morphism (realize-global g)
-- D126: a closed expression lifts by composing its own elaboration with
-- `terminal` — which is precisely what `t-value-lift` does for a value, with
-- `realize-global` in place of `realize-infer`. `zeroUsage` is what makes the
-- `terminal` legitimate: the body reads no local, so there is nothing to
-- capture and no closure to build.
-- D126: `λ _ → e`, built from the existing `weaken`. NOTE what `zeroUsage` does
-- and does not buy: it makes the lambda's own variable `Zero`-used, so the
-- abstraction is legitimate — but it does NOT say the body is independent of the
-- AMBIENT environment. `Zero *ᵘ Ψ` discards an argument's usage wholesale, so
-- `f x` at a `Zero`-quantity arrow is usage-closed while still reading a local.
-- That is fine here (`⊢ᶜ` is context-indexed and this is constant in its
-- ARGUMENT, not in `dγ`) and is exactly why the morphism realm needs a
-- different premise — see D126's entry.
realize (t-closed-lift {π = Once.Type.pure} _ d) = lam Many PE.refl (weaken (realize-infer d))
-- …and at `eff`, the same lambda through `arr'` — the pure→eff coercion
-- `t-subsume` uses. Grade-polymorphism is not free here the way it is for
-- `t-value-lift`, because `Surface.lam` is pure and `lift-morphism` is not
-- available without strengthening the body to the empty context.
realize (t-closed-lift {π = Once.Type.eff} _ d)  = arr' (lam Many PE.refl (weaken (realize-infer d)))
realize (t-embed d)             = realize-infer d
realize (t-lam {q = q} ≤p d)    = lam q ≤p (realize d)
realize (t-pair-lit-check da db) = pair (realize da) (realize db)
realize (t-In-app-check {F = F} {wfF = wfF} _ d) =
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
realize {ctx = ctx} {A = A} (t-var-poly-instantiate _ _ _ _ _ _ bodyD) =
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
realize-infer (t-var-local {eV = eV} _ _) = svar→expr eV
realize-infer (t-var-qualified {name = name} {alias = alias} _ conc) = sigOp (bare (alias ++ "." ++ name)) conc
-- Plan 0.50: a resolved ref carries its canonical identity directly — the
-- reference elaboration reads it with NO String render, so it agrees with
-- the elaborator's `SigOpInfo.name` by construction.
realize-infer (t-var-resolved {cn = cn} _ conc) = sigOp cn conc
realize-infer (t-var-import {x = x} _ _ _ conc) = sigOp (bare x) conc
-- Plan 0.58 / D071: infer-mode ground telescope reference — same closed-body
-- inline as the check-mode `t-var-poly-instantiate` clause above.
realize-infer {ctx = ctx} {A = A} (t-var-poly-instantiate-infer _ _ _ _ _ _ _ bodyD) =
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
realize-infer (t-binop-arith-float {op = OpDiv} () _ _)
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
realize-infer (t-binop-arith-float-il {op = OpDiv} () _ _)
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
realize-infer (t-binop-arith-float-ir {op = OpDiv} () _ _)
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
