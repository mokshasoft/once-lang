-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Lang.Elaboration — plan 0.103 phase 6b (plan 0.102 C): THE SURFACE
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
--   * an FFI reference is `sigop`; a reference to one of the module's own
--     definitions (monomorphic or telescope) is `ref d τ`.
--
-- The module layer is an argument, not an assumption: a `View` resolves each
-- imported name to an honest, ground FFI declaration (D231, D243) or one of the module's own
-- definitions, and names each telescope entry's core index and the
-- kind-respecting instance a use is at.
-- Phase 6c/6d construct it from the module.
------------------------------------------------------------------------

import Once.Lang.Name
open import Data.Nat using (ℕ)
open import Once.Lang.Core.PolyTy using (Sig)

open import Once.Lang.Contract using (ISig)
module Once.Lang.Elaboration {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Fin using (Fin)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Product using () renaming (_,_ to _,ᵈ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Once.Lang.Type.Grade using (mk-kind; Many; pure; ≤q-Many; EffGrade)
open import Once.Lang.Type using (Type; Int; Float; _*_; _⇒[_]_)
open import Once.Lang.Type.Poly using (Ground; extractGround)
open import Once.Lang.Type.Instance using (KindedInstance)
open import Once.Lang.Type.WellFormed using (RigidFree)
open import Once.Lang.Type.Sub using (⊑-pure; _<:_; sub-arr; ·p-diag)
open import Once.Lang.Type.Sub using (<:-refl; ⊑π-refl; _⊔_≔_; <:ᶜ⇒<:)
open _⊔_≔_ using (left; right)
open import Once.Lang.Type.Honest using (HonestFFI)
open import Once.Spec.Name using (bare)
open import Once.Spec.Float.Decimal using (decimalOf; negate)
open import Once.Lang.Type.WellFormed using (IsConcrete)
open import Once.Lang.Context using (Ctx; ∅; Usage; zeroUsage; _+ᵘ_; _*ᵘ_)
open import Once.Lang.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Lang.Typing.Scope using (NamedCtx; Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Lang.Typing
open import Once.Lang.Core.PolyTy using (sigOf; _!!_; Respects; GSub; _⟪_⟫; module Schema)
open Schema using (arity; kinds; type)
open import Once.Lang.Core.Syntax S
open import Once.Lang.Core.Typing S
open import Once.Lang.Core.Derived S
open import Once.Lang.Core.DerivedTyping S
open import Once.Lang.Core.Rename S using (close; ⊢close)

------------------------------------------------------------------------
-- The module layer, as seen by an expression
------------------------------------------------------------------------

-- `T` is a kind-respecting instance of the entry `d`.
InstanceOf : Fin s → Type → Set
InstanceOf d T = Σ[ τ ∈ GSub (arity (S !! d)) ] Respects (kinds (S !! d)) τ × (type (S !! d) ⟪ τ ⟫ ≡ T)

-- D274: what a generator of the signature Σ in scope is: an FFI declaration of
-- the program, honest (D231) and ground (D243). Indexed by its key `x` (the
-- rendered path Σ is keyed by).
record Declared (x : String) (T : Type) : Set where
  constructor declared
  field
    honest : HonestFFI T
    rigid  : RigidFree T
    member : (x ,ᵈ T) ∈ sigOf S

-- What a name in the definitions table denotes: one of the module's own
-- definitions (D061/D071: an internal reference is a context projection,
-- never a SigOp), at a kind-respecting instance of its entry.
record ImportAt (x : String) (T : Type) : Set where
  constructor def
  field
    entryOf : Fin s
    instOf  : InstanceOf entryOf T

record View (imps : Imports) (sg : Imports) (polys : PolyCtx) : Set where
  field
    imported : ∀ {x T} → lookupImport imps x ≡ just T → ImportAt x T
    declares : ∀ {x T} → lookupImport sg x ≡ just T → Declared x T
    entry  : ∀ {x sc body prefix} → lookupPolyPrefix polys x ≡ just (sc , body , prefix) → Fin s
    ground : ∀ {x sc body prefix} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix)) (g : Ground sc)
           → InstanceOf (entry lp) (extractGround sc g)
    inst   : ∀ {x sc body prefix T} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
           → ¬ Ground sc → KindedInstance sc T
           → InstanceOf (entry lp) T
open View

Views : NamedCtx → Set
Views ctx = View (NamedCtx.imports ctx) (NamedCtx.sig ctx) (NamedCtx.polys ctx)

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

-- The elaboration's building blocks (public: the 6b bridge names the
-- transports they carry).
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

refE : (d : Fin s) → InstanceOf d A → Elab Γ zeroUsage A
refE {Γ = Γ} d (τ , r , eq) = ref d τ , subst (λ T → Γ ⊢[ zeroUsage ] ref d τ ∷ T ! pure) eq (⊢ref d τ r)

-- A generator's reference is the SigOp; its rendered path IS the key it was
-- looked up under in Σ (D274).
sigE : (c : Once.Spec.Name.CanonicalName) → IsConcrete A → Once.Lang.Name.WordName c → Declared (Once.Lang.Name.showCanonical c) A → Elab Γ zeroUsage A
sigE {A = A} c k w (declared h g m) = sigop c A , ⊢sigop c k h g w m

-- A definition's reference is the entry, at its instance.
importE : ∀ {x} → ImportAt x A → Elab Γ zeroUsage A
importE (def d i) = refE d i

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

elabᶜ V (t-id-check {u = u}) = idᶜ _ _ , ⊢idᶜ u
elabᶜ V (t-fst-check {u = u}) = fstᶜ _ _ _ , ⊢fstᶜ u
elabᶜ V (t-snd-check {u = u}) = sndᶜ _ _ _ , ⊢sndᶜ u
elabᶜ V (t-terminal-morph-check {u = u}) = terminalᶜ _ _ , ⊢terminalᶜ u
elabᶜ V (t-initial-morph-check {u = u}) = initialᶜ _ _ , ⊢initialᶜ u
elabᶜ V (t-inl-morph-check {u = u}) = inlᶜ _ _ _ , ⊢inlᶜ u
elabᶜ V (t-inr-morph-check {u = u}) = inrᶜ _ _ _ , ⊢inrᶜ u
elabᶜ V (t-compose-check-g dg df)   = lift2 (composeᶜ _ _) (⊢composeᶜ (·p-diag _)) (elabᶜ V df) (elabᵈ V dg)
elabᶜ V (t-compose-check-f wf p dg) = lift2 (composeᶜ _ _) (⊢composeᶜ (·p-diag _)) (coerceE p (elabᵢ V wf)) (elabᶜ V dg)
elabᶜ V (t-case-copair-check df dg) = lift2 (caseᶜ _ _ _) ⊢caseᶜ (elabᶜ V df) (elabᶜ V dg)
elabᶜ V (t-pair-morph-check df dg)  = lift2 (pairᶜ _ _) (⊢pairᶜ (·p-diag _)) (elabᶜ V df) (elabᶜ V dg)
elabᶜ V (t-curry-check {u = u} df)  = lift1 (curryᶜ _ _ _ _) (⊢curryᶜ u) (elabᶜ V df)
elabᶜ V (t-cata-check {u = u} wf dalg) = lift1 (cataᶜ _ _) (⊢cataᶜ u wf) (elabᶜ V dalg)
elabᶜ V (t-ana-check {u = u} wf dc) = lift1 (anaᶜ _ _ _) (⊢anaᶜ u wf) (elabᶜ V dc)
elabᶜ V (t-loop-check dc)          = lift1 (loopᶜ _) ⊢loopᶜ (elabᶜ V dc)
elabᶜ V (t-sub d p)                 = coerceE p (elabᵢ V d)
elabᶜ V (t-lam {u = u} ≤p d)        = let (b , ⊢b) = elabᶜ V d in lam _ _ _ b , ⊢lam ≤p (⊢sub-eff u ⊢b)
elabᶜ V (t-pair-lit-check da db)    = lift2 pair ⊢pair (elabᶜ V da) (elabᶜ V db)
elabᶜ V (t-In-app-check wf d)       = appC (⊢inᶜ wf) (elabᶜ V d)
elabᶜ V (t-apply-check dp)          = appC ⊢applyᶜ (elabᵢ V dp)
elabᶜ V (t-inl-app-check d)         = appC (⊢inlᶜ ⊑-pure) (elabᶜ V d)
elabᶜ V (t-inr-app-check d)         = appC (⊢inrᶜ ⊑-pure) (elabᶜ V d)
elabᶜ V (t-initial-app-check d)     = appC (⊢initialᶜ ⊑-pure) (elabᶜ V d)
elabᶜ V (t-var-poly-instantiate _ _ lp ng ins) = refE (entry V lp) (inst V lp ng ins)

elabᵢ V (t-int n)         = lit (lit-int n) , ⊢lit-int
elabᵢ V (t-float i f l p) = lit (lit-float (decimalOf i f l)) , ⊢lit-float
elabᵢ V t-unit            = unit , ⊢unit
elabᵢ V t-unit-var        = unit , ⊢unit
elabᵢ V (t-var-local {eV = Once.Lang.Context.svar i} _) = var i , ⊢var i
elabᵢ V (t-var-resolved {cn = cn} _ w lk k) = sigE cn k w (declares V lk)
elabᵢ V (t-var-own _ lk)                   = importE (imported V lk)
elabᵢ V (t-var-import _ _ lk k)            = importE (imported V lk)
elabᵢ V (t-var-poly-instantiate-infer {g = g} _ _ lp _ refl) = refE (entry V lp) (ground V lp g)
elabᵢ V (t-annot _ d)     = elabᶜ V d
elabᵢ V (t-pair da db)    = lift2 pair ⊢pair (elabᵢ V da) (elabᵢ V db)
elabᵢ V (t-neg d)         = lift1 (prim p-neg) (⊢prim p-neg) (elabᵢ V d)
elabᵢ V (t-neg-float i f l p) = lit (lit-float (negate (decimalOf i f l))) , ⊢lit-float
elabᵢ V (t-let d₁ d₂)     = let (e , ⊢e) = elabᵢ V d₁ ; (b , ⊢b) = elabᵢ V d₂ in let′ _ e b , ⊢let-pure _ ⊢e ⊢b
-- Each branch composed with its conversion into the join (D322).
elabᵢ V (t-case ds dl dr J) =
  let (s , ⊢s) = elabᵢ V ds ; (l , ⊢l) = elabᵢ V dl ; (r , ⊢r) = elabᵢ V dr
  in case _ _ s (coerce _ _ l) (coerce _ _ r) , ⊢case⊔ ⊢s (⊢coerce (<:ᶜ⇒<: (left J)) ⊢l) (⊢coerce (<:ᶜ⇒<: (right J)) ⊢r)
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
elabᵢ V (t-id-app d)       = appC (⊢idᶜ ⊑-pure) (elabᵢ V d)
elabᵢ V (t-fst-app d)      = appC (⊢fstᶜ ⊑-pure) (elabᵢ V d)
elabᵢ V (t-snd-app d)      = appC (⊢sndᶜ ⊑-pure) (elabᵢ V d)
elabᵢ V (t-terminal-app d) = appC (⊢terminalᶜ ⊑-pure) (elabᵢ V d)
elabᵢ V (t-apply-app-infer d)     = appC ⊢applyᶜ (elabᵢ V d)
elabᵢ V (t-apply-eff-app-infer d) = appC ⊢applyEffᶜ (elabᵢ V d)
elabᵢ V (t-Out-app-infer wf refl d)     = appC (⊢outᶜ wf) (elabᵢ V d)
elabᵢ V (t-Out-eff-app-infer wf refl d) = appC (⊢outEffᶜ wf) (elabᵢ V d)
elabᵢ V (t-app _ df dx)    = lift2 app (⊢app-pure _) (elabᵢ V df) (elabᶜ V dx)
elabᵢ V (t-effApp {π = π} _ df dx) = lift2 (effAppᶜ π) ⊢effAppᶜ (elabᵢ V df) (elabᶜ V dx)
elabᵢ V (t-app-spine _ dx df) = lift2 app ⊢app (elabᵈ V df) (elabᵢ V dx)

elabᵈ V (d-infer {B = B} w a g) = coerceE (sub-arr a (<:-refl B) g) (elabᵢ V w)
elabᵈ V (d-poly {A = A} {B = B} _ _ lp ng _ _ ins g) =
  coerceE (sub-arr (<:-refl A) (<:-refl B) g) (refE (entry V lp) (inst V lp ng ins))
elabᵈ V (d-lam {q' = q'} {u = u} d) = let (b , ⊢b) = elabᵢ V d in lam _ _ _ b , ⊢lam (≤q-Many q') (⊢sub-eff u ⊢b)
elabᵈ V (d-compose dg df)    = lift2 (composeᶜ _ _) (⊢composeᶜ (·p-diag _)) (elabᵈ V df) (elabᵈ V dg)
elabᵈ V (d-id {u = u}) = idᶜ _ _ , ⊢idᶜ u
elabᵈ V (d-fst {u = u}) = fstᶜ _ _ _ , ⊢fstᶜ u
elabᵈ V (d-snd {u = u}) = sndᶜ _ _ _ , ⊢sndᶜ u
elabᵈ V (d-terminal {u = u}) = terminalᶜ _ _ , ⊢terminalᶜ u
elabᵈ V (d-initial {u = u}) = initialᶜ _ _ , ⊢initialᶜ u
elabᵈ V (d-case df dg J) =
  lift2 (caseᶜ _ _ _) ⊢caseᶜ (coerceE (sub-arr (<:-refl _) (<:ᶜ⇒<: (left J)) (⊑π-refl _)) (elabᵈ V df))
                             (coerceE (sub-arr (<:-refl _) (<:ᶜ⇒<: (right J)) (⊑π-refl _)) (elabᵈ V dg))
elabᵈ V (d-pair df dg) = lift2 (pairᶜ _ _) (⊢pairᶜ (·p-diag _)) (elabᵈ V df) (elabᵈ V dg)
elabᵈ V (d-cata {u = u} wf dalg) = lift1 (cataᶜ _ _) (⊢cataᶜ u wf) (elabᵢ V dalg)
