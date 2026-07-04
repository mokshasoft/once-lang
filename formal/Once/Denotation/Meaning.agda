-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Denotation.Meaning — the reference meaning as a DIRECT denotation of
-- typing DERIVATIONS (Plan 0.58 north star, OCP-0006).
--
-- This is the IR-FREE reference semantics: recursion on the typing derivation,
-- landing in the value domain `⟦_⟧ᴰ` / trace monad `T`. It replaces the current
-- `SD.⟦ realize _ ⟧ˢ` route, whose only IR contact is `Surface.Expr`'s
-- `lift-morphism`/`morph-app` leaves (a morphism represented AS `IR`). Denoting
-- the morphism realm `⊢ᵐ` directly to a function `⟦A⟧ᴰ → T⟦B⟧ᴰ = ⟦A ⇒ B⟧ᴰ`
-- removes IR entirely — note the imports below contain NO `Once.IR`, NO `evalᴰ`.
--
-- P1 (this file): the VALUE realm `⟦_⟧ᵍ` and the MORPHISM realm `⟦_⟧ᵐ` — exactly
-- the two realms that leak IR today. Self-contained (⊢ᵐ recurses only into ⊢ᵐ/⊢ᵍ).
-- The three genuinely-hard cases (`m-cata` fold, `m-named` def-environment, `g-In`
-- initial algebra) are P1 SCAFFOLDS, discharged in P2. The `⊢ᶜ`/`⊢ᵢ` realms (the
-- mechanical mirror of `SD`) are added next.
------------------------------------------------------------------------

module Once.Denotation.Meaning where

open import Data.Integer using (ℤ) renaming (∣_∣ to absℤ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _++_)

open import Once.Type
  using (Type; Unit; Void; Int; _*_; _+_; _⇒[_]_; μ-type; Functor; ⟦_⟧T; Purity)
open import Once.CanonicalName using (CanonicalName; showCanonical; bare)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; emit-D; inject)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; svar; SVar) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ; lookup to lookupᵗ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Raw using (BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.SigOp.Info using (SigOpInfo; semM)
open import Once.Arith.SigOp.Builders
  using (value-info; str-lit-info;
         add-info; sub-info; mul-info; div-info; mod-info; neg-info;
         lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.TypeCheck.Judgment
  using (_⊢ᵍ_∶_; _⊢ᵐ_∶_⇨[_]_; _⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_;
         g-int; g-terminal; g-pair; g-inl; g-inr; g-In;
         m-id; m-fst; m-snd; m-terminal; m-initial; m-inl; m-inr;
         m-compose; m-case; m-pair; m-curry; m-cata; m-const;
         m-named; m-named-resolved;
         t-morph-lift; t-value-lift; t-embed; t-lam; t-pair-lit-check;
         t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
         t-initial-app-check; t-subsume; t-arg-driven-app-check; t-var-poly-instantiate;
         t-int; t-str; t-unit; t-unit-var; t-var-local; t-var-qualified;
         t-var-resolved; t-var-import; t-annot; t-pair; t-neg; t-let; t-case;
         t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
         t-terminal-app; t-apply-app-infer; t-app; t-effApp)

------------------------------------------------------------------------
-- P1 scaffolds (discharged in P2). NAMED and narrow — each is exactly one
-- rule's semantics that needs machinery this file does not yet set up.
------------------------------------------------------------------------

postulate
  -- g-In: the initial-algebra constructor `⟦F⟧T (μF) → μF` at the value level.
  in-value  : ∀ {F : Functor} → ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ → ⟦ μ-type F ⟧ᴰ
  -- m-cata: the structural fold of an algebra over `μF` (P2: reuse SD's cata-ev-algᴰ).
  cata-sem  : ∀ {F : Functor} {A : Type}
            → (⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ) → ⟦ μ-type F ⟧ᴰ → T ⟦ A ⟧ᴰ
  -- m-named / m-named-resolved: the named arrow's meaning (P2: the definition env).
  named-sem : ∀ {A B : Type} → String → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ

------------------------------------------------------------------------
-- The VALUE realm `⊢ᵍ` — a closed global element denotes a value `⟦A⟧ᴰ`.
------------------------------------------------------------------------

⟦_⟧ᵍ : ∀ {ctx e A} → ctx ⊢ᵍ e ∶ A → ⟦ A ⟧ᴰ
⟦ g-int n      ⟧ᵍ = absℤ n
⟦ g-terminal _ _ ⟧ᵍ = tt
⟦ g-pair ga gb ⟧ᵍ = ⟦ ga ⟧ᵍ , ⟦ gb ⟧ᵍ
⟦ g-inl ga     ⟧ᵍ = inj₁ ⟦ ga ⟧ᵍ
⟦ g-inr gb     ⟧ᵍ = inj₂ ⟦ gb ⟧ᵍ
⟦ g-In _ garg  ⟧ᵍ = in-value ⟦ garg ⟧ᵍ

------------------------------------------------------------------------
-- The MORPHISM realm `⊢ᵐ` — a categorical arrow denotes a Kleisli function
-- `⟦A⟧ᴰ → T⟦B⟧ᴰ = ⟦A ⇒ B⟧ᴰ`. Grade-erased (`π` ignored by the value domain).
------------------------------------------------------------------------

⟦_⟧ᵐ : ∀ {ctx e A π B} → ctx ⊢ᵐ e ∶ A ⇨[ π ] B → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
⟦ m-id _ _        ⟧ᵐ = λ a  → returnT a
⟦ m-fst _ _       ⟧ᵐ = λ ab → returnT (proj₁ ab)
⟦ m-snd _ _       ⟧ᵐ = λ ab → returnT (proj₂ ab)
⟦ m-terminal _ _  ⟧ᵐ = λ _  → returnT tt
⟦ m-initial _ _   ⟧ᵐ = λ v  → ⊥-elim v
⟦ m-inl _ _       ⟧ᵐ = λ a  → returnT (inj₁ a)
⟦ m-inr _ _       ⟧ᵐ = λ b  → returnT (inj₂ b)
⟦ m-compose _ f g ⟧ᵐ = λ a  → ⟦ g ⟧ᵐ a >>=T ⟦ f ⟧ᵐ
⟦ m-case f g      ⟧ᵐ = λ ab → [ ⟦ f ⟧ᵐ , ⟦ g ⟧ᵐ ]′ ab
⟦ m-pair f g      ⟧ᵐ = λ a  → ⟦ f ⟧ᵐ a >>=T λ b → ⟦ g ⟧ᵐ a >>=T λ c → returnT (b , c)
⟦ m-curry f       ⟧ᵐ = λ a  → returnT (λ b → ⟦ f ⟧ᵐ (a , b))
⟦ m-const gv      ⟧ᵐ = λ _  → returnT ⟦ gv ⟧ᵍ
⟦ m-cata _ alg    ⟧ᵐ = cata-sem ⟦ alg ⟧ᵐ
⟦_⟧ᵐ {A = A} {B = B} (m-named {x = x} _ _ _)        = named-sem {A} {B} x
⟦_⟧ᵐ {A = A} {B = B} (m-named-resolved {cn = cn} _) = named-sem {A} {B} (showCanonical cn)

------------------------------------------------------------------------
-- (P3) The env — IR-free positional lookup into `⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ`.
------------------------------------------------------------------------

lookupᴰ : ∀ {n} (Γ : Ctx n) (i : Fin n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ lookupᵗ Γ i ⟧ᴰ
lookupᴰ (Γ , A ^ q) zero    (dγ , a) = a
lookupᴰ (Γ , A ^ q) (suc i) (dγ , a) = lookupᴰ Γ i dγ

svarᴰ : ∀ {n} {Γ : Ctx n} {Ψ A} → SVar Γ Ψ A → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ A ⟧ᴰ
svarᴰ {Γ = Γ} (svar i) dγ = lookupᴰ Γ i dγ

-- A closed named/sigop value reference (matches SD's `sigOp`/`poly`), IR-free.
sigOpValᴰ : ∀ {B} → SigOpInfo Unit B → T ⟦ B ⟧ᴰ
sigOpValᴰ si = λ _ → (emit-D si tt , inject (semM si tt))

Env : NamedCtx → Set
Env ctx = ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜᵗ ⟧ᴰ

------------------------------------------------------------------------
-- (P3) The CHECK / INFER realms — the fusion of `realize` then `SD`, made
-- IR-free: morphisms via `⟦_⟧ᵐ`, values via `⟦_⟧ᵍ`, locals via `lookupᴰ`.
------------------------------------------------------------------------

⟦_⟧ᶜ : ∀ {ctx e A Ψ} → ctx ⊢ᶜ e ∶ A ⨾ Ψ → Env ctx → T ⟦ A ⟧ᴰ
⟦_⟧ᵢ : ∀ {ctx e A Ψ} → ctx ⊢ᵢ e ∶ A ⨾ Ψ → Env ctx → T ⟦ A ⟧ᴰ

⟦ t-morph-lift d ⟧ᶜ         dγ = returnT (⟦ d ⟧ᵐ)
⟦ t-value-lift g ⟧ᶜ         dγ = returnT (λ _ → returnT ⟦ g ⟧ᵍ)
⟦ t-embed d ⟧ᶜ              dγ = ⟦ d ⟧ᵢ dγ
⟦ t-lam _ d ⟧ᶜ              dγ = returnT (λ a → ⟦ d ⟧ᶜ (dγ , a))
⟦ t-pair-lit-check da db ⟧ᶜ dγ = ⟦ da ⟧ᶜ dγ >>=T λ a → ⟦ db ⟧ᶜ dγ >>=T λ b → returnT (a , b)
⟦ t-In-app-check _ d ⟧ᶜ     dγ = ⟦ d ⟧ᶜ dγ >>=T λ v → returnT (in-value v)
⟦ t-apply-check dp ⟧ᶜ       dγ = ⟦ dp ⟧ᵢ dγ >>=T λ fa → proj₁ fa (proj₂ fa)
⟦ t-inl-app-check d ⟧ᶜ      dγ = ⟦ d ⟧ᶜ dγ >>=T λ v → returnT (inj₁ v)
⟦ t-inr-app-check d ⟧ᶜ      dγ = ⟦ d ⟧ᶜ dγ >>=T λ v → returnT (inj₂ v)
⟦ t-initial-app-check d ⟧ᶜ  dγ = ⟦ d ⟧ᶜ dγ >>=T λ v → ⊥-elim v
⟦ t-subsume d ⟧ᶜ            dγ = ⟦ d ⟧ᶜ dγ
⟦ t-arg-driven-app-check _ darg df ⟧ᶜ dγ = ⟦ df ⟧ᶜ dγ >>=T λ vf → ⟦ darg ⟧ᵢ dγ >>=T λ vx → vf vx
⟦_⟧ᶜ {A = A} (t-var-poly-instantiate {x = x} _ _ _ _ _ _) dγ = sigOpValᴰ (value-info {Unit} {A} (bare x))

⟦ t-int n ⟧ᵢ                dγ = returnT (absℤ n)
⟦ t-str s ⟧ᵢ                dγ = returnT (semM (str-lit-info s) tt)
⟦ t-unit ⟧ᵢ                 dγ = returnT tt
⟦ t-unit-var ⟧ᵢ             dγ = returnT tt
⟦ t-var-local {eV = eV} _ _ ⟧ᵢ dγ = returnT (svarᴰ eV dγ)
⟦_⟧ᵢ {A = A} (t-var-qualified {name = name} {alias = alias} _) dγ = sigOpValᴰ (value-info {Unit} {A} (bare (alias ++ "." ++ name)))
⟦_⟧ᵢ {A = A} (t-var-resolved {cn = cn} _) dγ = sigOpValᴰ (value-info {Unit} {A} cn)
⟦_⟧ᵢ {A = A} (t-var-import {x = x} _ _ _) dγ = sigOpValᴰ (value-info {Unit} {A} (bare x))
⟦ t-annot d ⟧ᵢ              dγ = ⟦ d ⟧ᶜ dγ
⟦ t-pair da db ⟧ᵢ           dγ = ⟦ da ⟧ᵢ dγ >>=T λ a → ⟦ db ⟧ᵢ dγ >>=T λ b → returnT (a , b)
⟦ t-neg d ⟧ᵢ                dγ = ⟦ d ⟧ᵢ dγ >>=T λ v → returnT (semM neg-info v)
⟦ t-let d₁ d₂ ⟧ᵢ            dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ v → ⟦ d₂ ⟧ᵢ (dγ , v)
⟦ t-case ds dl dr ⟧ᵢ        dγ = ⟦ ds ⟧ᵢ dγ >>=T λ v →
                                   [ (λ a → ⟦ dl ⟧ᵢ (dγ , a)) , (λ b → ⟦ dr ⟧ᵢ (dγ , b)) ]′ v
⟦ t-binop-arith {op = OpAdd} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM add-info (a , b))
⟦ t-binop-arith {op = OpSub} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM sub-info (a , b))
⟦ t-binop-arith {op = OpMul} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM mul-info (a , b))
⟦ t-binop-arith {op = OpDiv} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM div-info (a , b))
⟦ t-binop-arith {op = OpMod} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM mod-info (a , b))
⟦_⟧ᵢ (t-binop-arith {op = OpLt} () _ _)
⟦_⟧ᵢ (t-binop-arith {op = OpLe} () _ _)
⟦_⟧ᵢ (t-binop-arith {op = OpGt} () _ _)
⟦_⟧ᵢ (t-binop-arith {op = OpGe} () _ _)
⟦_⟧ᵢ (t-binop-arith {op = OpEq} () _ _)
⟦_⟧ᵢ (t-binop-arith {op = OpNe} () _ _)
⟦ t-binop-cmp {op = OpLt} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM lt-info (a , b))
⟦ t-binop-cmp {op = OpLe} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM le-info (a , b))
⟦ t-binop-cmp {op = OpGt} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM gt-info (a , b))
⟦ t-binop-cmp {op = OpGe} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM ge-info (a , b))
⟦ t-binop-cmp {op = OpEq} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM eq-info (a , b))
⟦ t-binop-cmp {op = OpNe} _ d₁ d₂ ⟧ᵢ dγ = ⟦ d₁ ⟧ᵢ dγ >>=T λ a → ⟦ d₂ ⟧ᵢ dγ >>=T λ b → returnT (semM ne-info (a , b))
⟦_⟧ᵢ (t-binop-cmp {op = OpAdd} () _ _)
⟦_⟧ᵢ (t-binop-cmp {op = OpSub} () _ _)
⟦_⟧ᵢ (t-binop-cmp {op = OpMul} () _ _)
⟦_⟧ᵢ (t-binop-cmp {op = OpDiv} () _ _)
⟦_⟧ᵢ (t-binop-cmp {op = OpMod} () _ _)
⟦ t-id-app d ⟧ᵢ             dγ = ⟦ d ⟧ᵢ dγ
⟦ t-fst-app d ⟧ᵢ            dγ = ⟦ d ⟧ᵢ dγ >>=T λ v → returnT (proj₁ v)
⟦ t-snd-app d ⟧ᵢ            dγ = ⟦ d ⟧ᵢ dγ >>=T λ v → returnT (proj₂ v)
⟦ t-terminal-app d ⟧ᵢ       dγ = ⟦ d ⟧ᵢ dγ >>=T λ _ → returnT tt
⟦ t-apply-app-infer d ⟧ᵢ    dγ = ⟦ d ⟧ᵢ dγ >>=T λ fa → proj₁ fa (proj₂ fa)
⟦ t-app _ df dx ⟧ᵢ          dγ = ⟦ df ⟧ᵢ dγ >>=T λ vf → ⟦ dx ⟧ᶜ dγ >>=T λ vx → vf vx
⟦ t-effApp _ df dx ⟧ᵢ       dγ = returnT (λ _ → ⟦ df ⟧ᵢ dγ >>=T λ vf → ⟦ dx ⟧ᶜ dγ >>=T λ vx → vf vx)
