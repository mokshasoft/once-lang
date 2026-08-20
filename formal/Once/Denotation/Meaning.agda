-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Data.Integer using (ℤ)
import Once.Word as OnceWord
module IntW = OnceWord.Word64
open import Once.Float.Dyadic using (FloatFormat; encode)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; _++_)

open import Once.Type
  using (Type; Unit; Void; Int; _*_; _+_; _⇒[_]_; μ-type; Functor; ⟦_⟧T; Purity)
open import Once.CanonicalName using (CanonicalName; showCanonical; bare)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_; valueT; projTrace)
-- P5: the value-domain vocabulary comes from the IR-free `ValueDomain`
-- (NOT `DenotTrace`, whose `evalᴰ` is implementation).
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; emit-D; inject; forget; coerce-functor⁻¹-D)
open import Once.Semantics.Machine using (sem-In; coerce-functor; sem-cata; sem-fmap; coerce-functor⁻¹; ⟦_⟧F)
open import Once.Functor.Translate using (WellFormedF; IsBaseType; IsConcrete; base-Unit; con-base; con-fun)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.CCC.Eval as Val using ()
open import Data.List using (List) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ)
open import Once.Surface.Context using (Ctx; ∅; _,_^_; svar; SVar) renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ; lookup to lookupᵗ)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Raw using (BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.SigOp.Info using (SigOpInfo; semM)
open import Once.Arith.SigOp.Builders
  using (value-info; arrow-info; str-lit-info;
         add-info; sub-info; mul-info; div-info; mod-info; neg-info;
         lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.TypeCheck.Judgment
  using (_⊢ᵍ_∶_; _⊢ᵐ_∶_⇨[_]_; _⊢ᶜ_∶_⨾_; _⊢ᵢ_∶_⨾_;
         g-int; g-float; g-terminal; g-pair; g-inl; g-inr; g-In;
         m-id; m-fst; m-snd; m-terminal; m-initial; m-inl; m-inr;
         m-compose; m-case; m-pair; m-curry; m-cata; m-const;
         m-named; m-named-resolved;
         t-morph-lift; t-value-lift; t-embed; t-lam; t-pair-lit-check;
         t-In-app-check; t-apply-check; t-inl-app-check; t-inr-app-check;
         t-initial-app-check; t-subsume; t-arg-driven-app-check; t-var-poly-instantiate;
         t-var-poly-instantiate-infer;
         t-int; t-float; t-str; t-unit; t-unit-var; t-var-local; t-var-qualified;
         t-var-resolved; t-var-import; t-annot; t-pair; t-neg; t-let; t-case;
         t-binop-arith; t-binop-cmp; t-id-app; t-fst-app; t-snd-app;
         t-terminal-app; t-apply-app-infer; t-app; t-effApp)

------------------------------------------------------------------------
-- P1 scaffolds (discharged in P2). NAMED and narrow — each is exactly one
-- rule's semantics that needs machinery this file does not yet set up.
------------------------------------------------------------------------

-- m-cata: the event-tracking structural fold, IR-free — a direct-algebra mirror
-- of SD's `cata-ev-algᴰ` (`evalᴰ alg` replaced by the direct algebra `dalg`).
-- DEFINITIONALLY matches `evalᴰ (Cata wf alg)` when `dalg = evalᴰ alg`, so the
-- `bridgeᵈ` cata case reduces to the (recursive) morphism bridge.
cata-ev-algᴰ-D : ∀ {F : Functor} {A : Type} → ℕ → (⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ)
               → ⟦ F ⟧F (List SigOpEvent × ⟦ A ⟧ᴰ) → List SigOpEvent × ⟦ A ⟧ᴰ
cata-ev-algᴰ-D {F} {A} n dalg fc =
  ( events-F F proj₁ fc ++ₗ projTrace (dalg z) n
  , valueT (dalg z) n )
  where z = coerce-functor⁻¹-D F A (sem-fmap F proj₂ fc)

cata-sem : ∀ {F : Functor} {A : Type} → WellFormedF F
         → (⟦ ⟦ F ⟧T A ⟧ᴰ → T ⟦ A ⟧ᴰ) → ⟦ μ-type F ⟧ᴰ → T ⟦ A ⟧ᴰ
cata-sem {F} {A} wf dalg v = λ n →
  let r = sem-cata wf (cata-ev-algᴰ-D {F} {A} n dalg) (forget v)
  in (proj₁ r , proj₂ r)

-- g-In: the initial-algebra constructor `⟦F⟧T (μF) → μF` at the value level.
-- DEFINITIONALLY `eval (In wf Heap) ∘ forget` (first-order data is pure), so the
-- `bridgeᵈ` case for `g-In` is a `forget`-coercion step.
in-value : ∀ {F : Functor} → ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ → ⟦ μ-type F ⟧ᴰ
in-value {F} x = sem-In F (coerce-functor F (μ-type F) (forget x))

-- m-named / m-named-resolved: the named arrow's meaning, IR-free. This is
-- DEFINITIONALLY `evalᴰ (SigOp (value-info cn))` (same RHS), so the `bridgeᵈ`
-- case for a named morphism is `refl`.
named-sem : ∀ {A B : Type} → CanonicalName → IsBaseType A → IsConcrete B → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
named-sem {A} {B} cn bA cB a =
  λ _ → (emit-D (value-info {A} {B} cn bA cB) (forget a) , inject (semM (value-info {A} {B} cn bA cB) (forget a)))

------------------------------------------------------------------------
-- The VALUE realm `⊢ᵍ` — a closed global element denotes a value `⟦A⟧ᴰ`.
------------------------------------------------------------------------

⟦_⟧ᵍ : ∀ {ctx e A} → ctx ⊢ᵍ e ∶ A → FloatFormat → ⟦ A ⟧ᴰ
-- D054: an `Int` literal MEANS its two's-complement machine word, via
-- `Once.Word.fromℤ` — the same function the elaborator's `intLit` and the
-- blocked arith path use. It used to be `absℤ` (absolute value), so `-5` would
-- have meant 5; harmless only because no negative literal can be written yet,
-- and plan 0.73 F3 was about to change that.
⟦ g-int n      ⟧ᵍ fmt = IntW.fromℤ n
-- …and a float literal means ITS ENCODING AT THE TARGET'S FORMAT (D113).
-- `⟦ Float ⟧` is the target's representation, not an exact value, and `1.5`
-- has no target-free one — so the reference meaning takes the format. This
-- clause is the entire reason it does; every other clause just passes it on.
⟦ g-float _ _ _ d _ ⟧ᵍ fmt = encode fmt d
⟦ g-terminal _ _ ⟧ᵍ fmt = tt
⟦ g-pair ga gb ⟧ᵍ fmt = (⟦ ga ⟧ᵍ fmt) , (⟦ gb ⟧ᵍ fmt)
⟦ g-inl ga     ⟧ᵍ fmt = inj₁ (⟦ ga ⟧ᵍ fmt)
⟦ g-inr gb     ⟧ᵍ fmt = inj₂ (⟦ gb ⟧ᵍ fmt)
⟦ g-In _ garg  ⟧ᵍ fmt = in-value (⟦ garg ⟧ᵍ fmt)

------------------------------------------------------------------------
-- The MORPHISM realm `⊢ᵐ` — a categorical arrow denotes a Kleisli function
-- `⟦A⟧ᴰ → T⟦B⟧ᴰ = ⟦A ⇒ B⟧ᴰ`. Grade-erased (`π` ignored by the value domain).
------------------------------------------------------------------------

⟦_⟧ᵐ : ∀ {ctx e A π B} → ctx ⊢ᵐ e ∶ A ⇨[ π ] B → FloatFormat → ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ
⟦ m-id _ _        ⟧ᵐ fmt = λ a  → returnT a
⟦ m-fst _ _       ⟧ᵐ fmt = λ ab → returnT (proj₁ ab)
⟦ m-snd _ _       ⟧ᵐ fmt = λ ab → returnT (proj₂ ab)
⟦ m-terminal _ _  ⟧ᵐ fmt = λ _  → returnT tt
⟦ m-initial _ _   ⟧ᵐ fmt = λ v  → ⊥-elim v
⟦ m-inl _ _       ⟧ᵐ fmt = λ a  → returnT (inj₁ a)
⟦ m-inr _ _       ⟧ᵐ fmt = λ b  → returnT (inj₂ b)
⟦ m-compose _ f g ⟧ᵐ fmt = λ a  → (⟦ g ⟧ᵐ fmt) a >>=T (⟦ f ⟧ᵐ fmt)
⟦ m-case f g      ⟧ᵐ fmt = λ ab → [ (⟦ f ⟧ᵐ fmt) , (⟦ g ⟧ᵐ fmt) ]′ ab
⟦ m-pair f g      ⟧ᵐ fmt = λ a  → (⟦ f ⟧ᵐ fmt) a >>=T λ b → (⟦ g ⟧ᵐ fmt) a >>=T λ c → returnT (b , c)
⟦ m-curry f       ⟧ᵐ fmt = λ a  → returnT (λ b → (⟦ f ⟧ᵐ fmt) (a , b))
⟦ m-const gv      ⟧ᵐ fmt = λ _  → returnT (⟦ gv ⟧ᵍ fmt)
⟦ m-cata {wfF = wfF} _ alg ⟧ᵐ fmt = cata-sem wfF (⟦ alg ⟧ᵐ fmt)
⟦_⟧ᵐ {A = A} {B = B} (m-named {x = x} _ _ _ bA cB)        fmt = named-sem {A} {B} (bare x) bA cB
⟦_⟧ᵐ {A = A} {B = B} (m-named-resolved {cn = cn} _ bA cB) fmt = named-sem {A} {B} cn bA cB

------------------------------------------------------------------------
-- (P3) The env — IR-free positional lookup into `⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ`.
------------------------------------------------------------------------

lookupᴰ : ∀ {n} (Γ : Ctx n) (i : Fin n) → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ lookupᵗ Γ i ⟧ᴰ
lookupᴰ (Γ , A ^ q) zero    (dγ , a) = a
lookupᴰ (Γ , A ^ q) (suc i) (dγ , a) = lookupᴰ Γ i dγ

svarᴰ : ∀ {n} {Γ : Ctx n} {Ψ A} → SVar Γ Ψ A → ⟦ ⟦ Γ ⟧ᶜᵗ ⟧ᴰ → ⟦ A ⟧ᴰ
svarᴰ {Γ = Γ} (svar i) dγ = lookupᴰ Γ i dγ

-- A closed named/sigop value reference (matches SD's `poly`/`closure`), IR-free.
sigOpValᴰ : ∀ {B} → SigOpInfo Unit B → T ⟦ B ⟧ᴰ
sigOpValᴰ si = λ _ → (emit-D si tt , inject (semM si tt))

-- An EXTERNAL sigop reference (`t-var-qualified/resolved/import`, realized to
-- SD's `sigOp`). DISPATCHES ON RESULT-TYPE SHAPE exactly like SD's `sigOp`: at
-- an ARROW type the reference is a first-order function POINTER whose effect
-- fires on APPLICATION (`arrow-info` respects the arrow's `Purity`), NOT a pure
-- `value-info` value. This is the migration's headline case (a SigOp result may
-- be a first-order fn pointer); dispatching here keeps the direct meaning FAITHFUL
-- to SD (⇒ `sigop-ref-bridge`'s arrow case is `refl`), where an un-dispatched
-- `value-info` would wrongly drop the pointee's effect.
-- Split on the WITNESS (not `A`'s shape) so `con-base` reduces at an abstract
-- base `A` — `con-fun` forces the arrow shape for the closure form.
sigOpRefᴰ : ∀ {A} → CanonicalName → IsConcrete A → T ⟦ A ⟧ᴰ
sigOpRefᴰ {A = A} cn (con-base ib) = sigOpValᴰ (value-info {Unit} {A} cn base-Unit (con-base ib))
sigOpRefᴰ cn (con-fun {A = Dom} {B = Cod} {k = k} bDom cCod) =
  returnT (λ arg → λ n → ( emit-D (arrow-info {Dom} {Cod} k cn bDom cCod) (forget arg)
                         , inject (semM (arrow-info {Dom} {Cod} k cn bDom cCod) (forget arg)) ))

Env : NamedCtx → Set
Env ctx = ⟦ ⟦ NamedCtx.debruijn ctx ⟧ᶜᵗ ⟧ᴰ

------------------------------------------------------------------------
-- (P3) The CHECK / INFER realms — the fusion of `realize` then `SD`, made
-- IR-free: morphisms via `⟦_⟧ᵐ`, values via `⟦_⟧ᵍ`, locals via `lookupᴰ`.
------------------------------------------------------------------------

⟦_⟧ᶜ : ∀ {ctx e A Ψ} → ctx ⊢ᶜ e ∶ A ⨾ Ψ → FloatFormat → Env ctx → T ⟦ A ⟧ᴰ
⟦_⟧ᵢ : ∀ {ctx e A Ψ} → ctx ⊢ᵢ e ∶ A ⨾ Ψ → FloatFormat → Env ctx → T ⟦ A ⟧ᴰ

⟦ t-morph-lift d ⟧ᶜ fmt         dγ = returnT (⟦ d ⟧ᵐ fmt)
⟦ t-value-lift g ⟧ᶜ fmt         dγ = returnT (λ _ → returnT (⟦ g ⟧ᵍ fmt))
⟦ t-embed d ⟧ᶜ fmt              dγ = (⟦ d ⟧ᵢ fmt) dγ
⟦ t-lam _ d ⟧ᶜ fmt              dγ = returnT (λ a → (⟦ d ⟧ᶜ fmt) (dγ , a))
⟦ t-pair-lit-check da db ⟧ᶜ fmt dγ = (⟦ da ⟧ᶜ fmt) dγ >>=T λ a → (⟦ db ⟧ᶜ fmt) dγ >>=T λ b → returnT (a , b)
⟦ t-In-app-check _ d ⟧ᶜ fmt     dγ = (⟦ d ⟧ᶜ fmt) dγ >>=T λ v → returnT (in-value v)
⟦ t-apply-check dp ⟧ᶜ fmt       dγ = (⟦ dp ⟧ᵢ fmt) dγ >>=T λ fa → proj₁ fa (proj₂ fa)
⟦ t-inl-app-check d ⟧ᶜ fmt      dγ = (⟦ d ⟧ᶜ fmt) dγ >>=T λ v → returnT (inj₁ v)
⟦ t-inr-app-check d ⟧ᶜ fmt      dγ = (⟦ d ⟧ᶜ fmt) dγ >>=T λ v → returnT (inj₂ v)
⟦ t-initial-app-check d ⟧ᶜ fmt  dγ = (⟦ d ⟧ᶜ fmt) dγ >>=T λ v → ⊥-elim v
⟦ t-subsume d ⟧ᶜ fmt            dγ = (⟦ d ⟧ᶜ fmt) dγ
⟦ t-arg-driven-app-check _ darg df ⟧ᶜ fmt dγ = (⟦ df ⟧ᶜ fmt) dγ >>=T λ vf → (⟦ darg ⟧ᵢ fmt) dγ >>=T λ vx → vf vx
-- Plan 0.58 (telescope): a same-module def reference MEANS its closed body
-- (the body derivation is the rule's premise). Env-independent — the body is
-- typed in the empty local context (the prefix env), so discard `dγ` and feed
-- `tt`. Structural recursion (bodyD is a premise ⇒ a subterm).
⟦ t-var-poly-instantiate _ _ _ _ _ _ bodyD ⟧ᶜ fmt dγ = (⟦ bodyD ⟧ᶜ fmt) tt

⟦ t-int n ⟧ᵢ fmt                dγ = returnT (IntW.fromℤ n)
-- D113, in the INFER realm: same clause, same reason as `g-float` above.
⟦ t-float _ _ _ d _ ⟧ᵢ fmt      dγ = returnT (encode fmt d)
⟦ t-str s ⟧ᵢ fmt                dγ = returnT (semM (str-lit-info s) tt)
⟦ t-unit ⟧ᵢ fmt                 dγ = returnT tt
⟦ t-unit-var ⟧ᵢ fmt             dγ = returnT tt
⟦ t-var-local {eV = eV} _ _ ⟧ᵢ fmt dγ = returnT (svarᴰ eV dγ)
⟦_⟧ᵢ {A = A} (t-var-qualified {name = name} {alias = alias} _ conc) fmt dγ = sigOpRefᴰ {A = A} (bare (alias ++ "." ++ name)) conc
⟦_⟧ᵢ {A = A} (t-var-resolved {cn = cn} _ conc) fmt dγ = sigOpRefᴰ {A = A} cn conc
⟦_⟧ᵢ {A = A} (t-var-import {x = x} _ _ _ conc) fmt dγ = sigOpRefᴰ {A = A} (bare x) conc
-- Plan 0.58 / D071: an infer-mode ground telescope reference MEANS its body —
-- the context projection Γ(x). The body is closed (typed in the telescope
-- prefix over the empty local env), so its meaning runs on `tt`. Structural
-- recursion (bodyD is a premise ⇒ a subterm) — same as the check-mode rule.
⟦ t-var-poly-instantiate-infer _ _ _ _ _ _ _ bodyD ⟧ᵢ fmt dγ = (⟦ bodyD ⟧ᶜ fmt) tt
⟦ t-annot d ⟧ᵢ fmt              dγ = (⟦ d ⟧ᶜ fmt) dγ
⟦ t-pair da db ⟧ᵢ fmt           dγ = (⟦ da ⟧ᵢ fmt) dγ >>=T λ a → (⟦ db ⟧ᵢ fmt) dγ >>=T λ b → returnT (a , b)
⟦ t-neg d ⟧ᵢ fmt                dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ v → returnT (semM neg-info v)
⟦ t-let d₁ d₂ ⟧ᵢ fmt            dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ v → (⟦ d₂ ⟧ᵢ fmt) (dγ , v)
⟦ t-case ds dl dr ⟧ᵢ fmt        dγ = (⟦ ds ⟧ᵢ fmt) dγ >>=T λ v →
                                   [ (λ a → (⟦ dl ⟧ᵢ fmt) (dγ , a)) , (λ b → (⟦ dr ⟧ᵢ fmt) (dγ , b)) ]′ v
⟦ t-binop-arith {op = OpAdd} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM add-info (a , b))
⟦ t-binop-arith {op = OpSub} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM sub-info (a , b))
⟦ t-binop-arith {op = OpMul} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM mul-info (a , b))
⟦ t-binop-arith {op = OpDiv} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM div-info (a , b))
⟦ t-binop-arith {op = OpMod} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM mod-info (a , b))
⟦_⟧ᵢ (t-binop-arith {op = OpLt} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpLe} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpGt} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpGe} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpEq} () _ _) fmt
⟦_⟧ᵢ (t-binop-arith {op = OpNe} () _ _) fmt
⟦ t-binop-cmp {op = OpLt} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM lt-info (a , b))
⟦ t-binop-cmp {op = OpLe} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM le-info (a , b))
⟦ t-binop-cmp {op = OpGt} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM gt-info (a , b))
⟦ t-binop-cmp {op = OpGe} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM ge-info (a , b))
⟦ t-binop-cmp {op = OpEq} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM eq-info (a , b))
⟦ t-binop-cmp {op = OpNe} _ d₁ d₂ ⟧ᵢ fmt dγ = (⟦ d₁ ⟧ᵢ fmt) dγ >>=T λ a → (⟦ d₂ ⟧ᵢ fmt) dγ >>=T λ b → returnT (semM ne-info (a , b))
⟦_⟧ᵢ (t-binop-cmp {op = OpAdd} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpSub} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpMul} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpDiv} () _ _) fmt
⟦_⟧ᵢ (t-binop-cmp {op = OpMod} () _ _) fmt
⟦ t-id-app d ⟧ᵢ fmt             dγ = (⟦ d ⟧ᵢ fmt) dγ
⟦ t-fst-app d ⟧ᵢ fmt            dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ v → returnT (proj₁ v)
⟦ t-snd-app d ⟧ᵢ fmt            dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ v → returnT (proj₂ v)
⟦ t-terminal-app d ⟧ᵢ fmt       dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ _ → returnT tt
⟦ t-apply-app-infer d ⟧ᵢ fmt    dγ = (⟦ d ⟧ᵢ fmt) dγ >>=T λ fa → proj₁ fa (proj₂ fa)
⟦ t-app _ df dx ⟧ᵢ fmt          dγ = (⟦ df ⟧ᵢ fmt) dγ >>=T λ vf → (⟦ dx ⟧ᶜ fmt) dγ >>=T λ vx → vf vx
⟦ t-effApp _ df dx ⟧ᵢ fmt       dγ = returnT (λ _ → (⟦ df ⟧ᵢ fmt) dγ >>=T λ vf → (⟦ dx ⟧ᶜ fmt) dγ >>=T λ vx → vf vx)
