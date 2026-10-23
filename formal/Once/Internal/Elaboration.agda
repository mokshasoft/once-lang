-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson
------------------------------------------------------------------------
-- Once.Internal.Elaboration — plan 0.103 phase 6b (plan 0.102 C): THE SURFACE
-- ELABORATES INTO THE CORE.
--
-- INTERNAL (D333). Every surface derivation (`⊢ᶜ`/`⊢ᵢ`/`⊢ᵈ`) elaborates to a core term and
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
-- imported name to an honest, ground FFI declaration of Σ (D231) or one of the
-- module's own definitions, and names each telescope entry's index in the
-- definitions table, whose schema is the entry's (`entryIs`); a use's instance
-- is computed from it (`kinded-instance`).
--
-- Plan 0.122: the target is the SPEC's core (`Spec.Core.Syntax`/`Typing`), at
-- the scope's kinds — a polymorphic body elaborates over its parameters.
-- Phase 6c/6d construct it from the module.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Internal.Elaboration (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Once.Spec.Grade using (mk-kind; Many; pure)
open import Once.Type.Grade using (≤q-Many; ≤qᵇ→≤q)
open import Once.Spec.Type using (Ty; Type; KCtx; TySub; Respects; ∅ₖ; Int; Float; _*_; _⇒[_]_; _⟨_⟩)
open import Once.Spec.Signature using (_∶_)
open import Once.Spec.Name using (CanonicalName)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Internal.Type using (wk₀; none)
open import Once.Internal.Type.Poly using (Ground; extractGround)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Internal.Type.Schema using (schemaOf; kinded-instance)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Spec.Sub using (_<:_; sub-arr)
open import Once.Internal.Type.Sub using (·p-diag)
open import Once.Spec.Grade using (⊑-pure)
open import Once.Spec.Sub using (_⊔_≔_)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open _⊔_≔_ using (left; right)
open import Once.Internal.Type.Honest using (HonestFFI)
open import Once.Spec.Float.Decimal using (decimalOf; negate)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Core.Decl using (declS; ⌜declS⌝)
open import Once.Spec.Context using (Ctx)
open import Once.Internal.Context using (Usage; zeroUsage; _+ᵘ_; _*ᵘ_; svar)
open import Once.Spec.Surface.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Internal.Typing.Scope using (NamedCtx; Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Internal.Typing
open import Once.Spec.Core.Syntax
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Derived
open import Once.Spec.Core.Typing Σ S
open import Once.TypeCheck.View Σ S
open View
open import Once.Internal.Core.DerivedTyping Σ S

------------------------------------------------------------------------
-- Elaborations and their combinators
------------------------------------------------------------------------

Elab : ∀ {m n} → KCtx m → Ctx m n → Usage n → Ty m → Set
Elab {m} {n} Δ Γ Ψ A = Σ[ t ∈ Tm S m n ] Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! pure

module _ {m : ℕ} {Δ : KCtx m} {n : ℕ} {Γ : Ctx m n} where

  lift1 : ∀ {Ψ Ψ′ : Usage n} {A B : Ty m} (f : Tm S m n → Tm S m n)
        → (∀ {t} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! pure → Δ ⊩ Γ ⊢[ Ψ′ ] f t ∷ B ! pure)
        → Elab Δ Γ Ψ A → Elab Δ Γ Ψ′ B
  lift1 f h (t , d) = f t , h d

  lift2 : ∀ {Ψ₁ Ψ₂ Ψ₃ : Usage n} {A B C : Ty m} (f : Tm S m n → Tm S m n → Tm S m n)
        → (∀ {t u} → Δ ⊩ Γ ⊢[ Ψ₁ ] t ∷ A ! pure → Δ ⊩ Γ ⊢[ Ψ₂ ] u ∷ B ! pure → Δ ⊩ Γ ⊢[ Ψ₃ ] f t u ∷ C ! pure)
        → Elab Δ Γ Ψ₁ A → Elab Δ Γ Ψ₂ B → Elab Δ Γ Ψ₃ C
  lift2 f h (t , d) (u , e) = f t u , h d e

  retypeD : ∀ {Ψ : Usage n} {t} {A B : Ty m} {π} → A ≡ B → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ B ! π
  retypeD refl d = d

  retypeE : ∀ {Ψ : Usage n} {A B : Ty m} → A ≡ B → Elab Δ Γ Ψ A → Elab Δ Γ Ψ B
  retypeE refl e = e

  appC : ∀ {Ψ : Usage n} {A B : Ty m} {c} → Δ ⊩ Γ ⊢[ zeroUsage ] c ∷ A ⇒[ mk-kind Many pure ] B ! pure
       → Elab Δ Γ Ψ A → Elab Δ Γ (zeroUsage +ᵘ Many *ᵘ Ψ) B
  appC {c = c} dc = lift1 (app c) (⊢app dc)

  bin : ∀ {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (p : Prim) → primDom p ≡ A * B
      → Elab Δ Γ Ψ₁ A → Elab Δ Γ Ψ₂ B → Elab Δ Γ (Ψ₁ +ᵘ Ψ₂) (primCod p)
  bin p eq = lift2 (λ t u → prim p (pair t u)) (λ d e → ⊢prim p (subst (λ D → Δ ⊩ Γ ⊢[ _ ] _ ∷ D ! pure) (sym eq) (⊢pair d e)))

  i2f : ∀ {Ψ : Usage n} → Elab Δ Γ Ψ Int → Elab Δ Γ Ψ Float
  i2f = lift1 (prim p-i2f) (⊢prim p-i2f)

  coerceE : ∀ {Ψ : Usage n} {A B : Ty m} → A <: B → Elab Δ Γ Ψ A → Elab Δ Γ Ψ B
  coerceE {A = A} {B = B} p = lift1 (coerce A B) (⊢coerce p)

  -- An entry of the table, at a kind-respecting instance of its schema.
  refAt : (d : Fin s) {sc : Schema} → S !! d ≡ sc → (τ : TySub (arity sc) m) → Respects (kinds sc) Δ τ
        → Elab Δ Γ zeroUsage (type sc ⟨ τ ⟩)
  refAt d refl τ r = ref d τ , ⊢ref d τ r

  -- An FFI reference is the declaration's `sigop`, at its type.
  sigE : ∀ {A : Ty m} (c : CanonicalName) {T : Type} → WordName c → IsConcrete T → Declared (showCanonical c) T → A ≡ wk₀ T
       → Elab Δ Γ zeroUsage A
  sigE c {T} wn k (declared h mem) eq = sigop c (declS T) , retypeD (trans (⌜declS⌝ k h) (sym eq)) (⊢sigop (mem wn refl))

  -- A monomorphic definition, at its ground type.
  importE : ∀ {A : Ty m} {x T} → ImportAt x T → A ≡ wk₀ T → Elab Δ Γ zeroUsage A
  importE (def d mono) eq = retypeE (sym eq) (refAt d mono none (λ ()))

  -- A telescope definition, at a kinded instance of its type.
  polyE : ∀ {imps sg polys} → View imps sg polys → ∀ {x sc body prefix} {U : Ty m}
        → (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix)) → KindedInstance Δ sc U
        → Elab Δ Γ zeroUsage U
  polyE V {sc = sc} lp ki =
    retypeE (proj₂ (proj₂ (kinded-instance sc ki)))
            (refAt (entry V lp) (entryIs V lp) (proj₁ (kinded-instance sc ki)) (proj₁ (proj₂ (kinded-instance sc ki))))

------------------------------------------------------------------------
-- The elaboration
------------------------------------------------------------------------

elabᶜ : ∀ {m} {A : Ty m} {ctx e Ψ} → Views ctx → ctx ⊢ᶜ e ∶ A ⨾ Ψ → Elab (NamedCtx.kinds ctx) (NamedCtx.debruijn ctx) Ψ A
elabᵢ : ∀ {m} {A : Ty m} {ctx e Ψ} → Views ctx → ctx ⊢ᵢ e ∶ A ⨾ Ψ → Elab (NamedCtx.kinds ctx) (NamedCtx.debruijn ctx) Ψ A
elabᵈ : ∀ {m} {A B : Ty m} {ctx e π Ψ} → Views ctx → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ
      → Elab (NamedCtx.kinds ctx) (NamedCtx.debruijn ctx) Ψ (A ⇒[ mk-kind Many π ] B)

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
elabᶜ V (t-cata-check wf dalg) = lift1 (cataᶜ _ _) (⊢cataᶜ wf) (elabᶜ V dalg)
elabᶜ V (t-ana-check {u = u} wf dc) = lift1 (anaᶜ _ _ _) (⊢anaᶜ u wf) (elabᶜ V dc)
elabᶜ V (t-loop-check dc)          = lift1 (loopᶜ _) ⊢loopᶜ (elabᶜ V dc)
elabᶜ V (t-sub d p)                 = coerceE p (elabᵢ V d)
elabᶜ V (t-lam {q = q} {q' = q'} {u = u} ≤p d) = let (b , ⊢b) = elabᶜ V d in lam _ _ _ b , ⊢lam (≤qᵇ→≤q q' q ≤p) (⊢sub-eff u ⊢b)
elabᶜ V (t-pair-lit-check da db)    = lift2 pair ⊢pair (elabᶜ V da) (elabᶜ V db)
elabᶜ V (t-In-app-check wf d)       = appC (⊢inᶜ wf) (elabᶜ V d)
elabᶜ V (t-apply-check dp)          = appC ⊢applyᶜ (elabᵢ V dp)
elabᶜ V (t-inl-app-check d)         = appC (⊢inlᶜ ⊑-pure) (elabᶜ V d)
elabᶜ V (t-inr-app-check d)         = appC (⊢inrᶜ ⊑-pure) (elabᶜ V d)
elabᶜ V (t-initial-app-check d)     = appC (⊢initialᶜ ⊑-pure) (elabᶜ V d)
elabᶜ V (t-var-poly-instantiate _ _ lp ng ins) = polyE V lp ins

elabᵢ V (t-int n)         = lit (lit-int n) , ⊢lit-int
elabᵢ V (t-float i f l) = lit (lit-float (decimalOf i f l)) , ⊢lit-float
elabᵢ V t-unit            = unit , ⊢unit
elabᵢ V t-unit-var        = unit , ⊢unit
elabᵢ V (t-var-local {eV = svar i} _) = var i , ⊢var i
elabᵢ V (t-var-resolved {cn = cn} _ w lk k eq) = sigE cn w k (declares V lk) eq
elabᵢ V (t-var-own _ lk eq)                  = importE (imported V lk) eq
elabᵢ V (t-var-import _ _ lk k eq)           = importE (imported V lk) eq
elabᵢ V (t-var-poly-instantiate-infer {schema = sc} {g = g} _ _ lp _ eq) = retypeE (sym eq) (polyE V lp (ground-kinded sc g))
elabᵢ V (t-annot d _)     = elabᶜ V d
elabᵢ V (t-pair da db)    = lift2 pair ⊢pair (elabᵢ V da) (elabᵢ V db)
elabᵢ V (t-neg d)         = lift1 (prim p-neg) (⊢prim p-neg) (elabᵢ V d)
elabᵢ V (t-neg-float i f l) = lit (lit-float (negate (decimalOf i f l))) , ⊢lit-float
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
elabᵢ V (t-Out-eff-app-infer wf refl d) = appC (⊢outActᶜ wf) (elabᵢ V d)
elabᵢ V (t-app _ df dx)    = lift2 app (⊢app-pure _) (elabᵢ V df) (elabᶜ V dx)
elabᵢ V (t-effApp {π = π} _ df dx) = lift2 (effAppᶜ π) ⊢effAppᶜ (elabᵢ V df) (elabᶜ V dx)
elabᵢ V (t-app-spine _ dx df) = lift2 app ⊢app (elabᵈ V df) (elabᵢ V dx)

elabᵈ V (d-infer {B = B} w a g) = coerceE (sub-arr a (<:-refl B) g) (elabᵢ V w)
elabᵈ V (d-poly {A = A} {B = B} _ _ lp ng _ _ ins g) =
  coerceE (sub-arr (<:-refl A) (<:-refl B) g) (polyE V lp ins)
elabᵈ V (d-lam {q' = q'} {u = u} d) = let (b , ⊢b) = elabᵢ V d in lam _ _ _ b , ⊢lam (≤qᵇ→≤q q' Many (≤q-Many q')) (⊢sub-eff u ⊢b)
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
elabᵈ V (d-cata wf dalg) = lift1 (cataᶜ _ _) (⊢cataᶜ wf) (elabᵢ V dalg)
