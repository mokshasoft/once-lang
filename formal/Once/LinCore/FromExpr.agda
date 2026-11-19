-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.FromExpr — plan 0.146 B1.7 (D458, D459): THE BRIDGE. The
-- elaborator's graded expression straight into the linear core.
--
-- OCP-0009's "architecture bug" was `elaborate : Expr Γ Ψ A → IR`: the usage
-- `Ψ` indexes the source and appears nowhere in the target. Here it indexes
-- the target's context object: `Co Γ Ψ` holds the variables `Ψ` uses, as
-- `elaborate`'s `⟦ Γ ↾ Ψ ⟧ᶜ` does, and
--
--   * CONTEXT ADDITION IS THE TENSOR'S SPLIT (`split`), not a pairing: a slot
--     goes to the side that uses it, and a `dup` appears only where both sides
--     do. `One +q One = Many`, so a variable used once is never copied.
--   * A restriction (`weak`) drops the slots a use leaves out (the core's
--     `drop` frees what it drops).
--
-- Every translation is a FINITE BLOCK (`Lq-blk`): `Expr`'s `app` applies
-- only pure arrows, and `effApp`, `loop`, `ana`, `lam` and the combinators
-- build closures, so nothing is checked and nothing fails (D459). The types
-- are the IR's, through FromIR's `⟪_⟫` (D459: the bridge is proved against
-- `elaborateFull`'s IR meaning, so it shares the IR's value relation): every
-- arrow is a many-use closure, applied owned by lending it to `bev`.
--
-- Clause for clause `Surface.Elaborate.elaborate`, where the IR splits its
-- context with `⟨ restrictEnv , restrictEnv ⟩` this splits it linearly.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.FromExpr (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)
open import Relation.Nullary using (yes; no)

import Once.Spec.Grade as G
open import Once.Spec.Type using (Ty; Unit; _⇒[_]_; μ; ν)
import Once.Spec.Type as ST
open import Once.Spec.Name using (CanonicalName; bare)
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_; zeroUsage; singleUse)
open import Once.Context
  using (⟦_⟧ᶜ; _↾_; _⊔ᵘ_; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ;
         z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.IRTy using (IRTy; ⌊_⌋; ⌊⟧T-commute; ⌊wk₀⌋)
import Once.IRTy as I
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Spec.Sub using (_<:_; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-*; sub-+; sub-μ; sub-ν)
open import Once.Surface.CoerceIR using (VoidFree; voidFree?; erase-eq)
open import Once.Surface.Properties using (erase-arg-usage)
open import Once.Surface.Map
  using (Map; mp-id; mp-fst; mp-snd; mp-terminal; mp-inl; mp-inr; mp-initial; mp-apply; mp-In; mp-Out; mp-toFloat)
open import Once.Surface.Syntax
open import Once.Type.Concrete using (IsConcrete; con-base; con-fun)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open import Once.Arith.SigOp.Builders using (numInfo; i2f-info; value-info; arrow-info)
open import Once.Arith.SigOp.AsBlock using (as-block)
open import Once.Spec.Theory using (Has; Sym)
import Once.Spec.Theory as Th
import Data.Fin

open import Once.LinCore.Core fmt
open import Once.LinCore.FromIR fmt using (⟪_⟫; lf; grade; ⟪⟫-TI; ⟪⌊⌋⟫-flat; unlinked-i)
open import Once.LinCore.PassTr fmt using (dropl; k-dropl; copyIn; k-copyIn)

------------------------------------------------------------------------
-- 1. THE OBJECTS: a type, and the context object of a usage.
------------------------------------------------------------------------

ty : ∀ {m} → Ty m → LTy
ty A = ⟪ ⌊ A ⌋ ⟫

-- the variables `Ψ` uses, as `elaborate`'s environment `⟦ Γ ↾ Ψ ⟧ᶜ`
Co : ∀ {m n} → Ctx m n → Usage n → LTy
Co Γ Ψ = ⟪ ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ ⟫

------------------------------------------------------------------------
-- 2. THE CONTEXT, LINEARLY: restriction, and the split.
------------------------------------------------------------------------

module _ {L : Cx} {E : LTy} where

  -- ★ restriction: the slots the smaller usage leaves out are dropped
  weak : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} → Ψ ⊑ᵘ Ψ′ → Tm L E (Co Γ Ψ′) (Co Γ Ψ)
  weak {Γ = SC.∅}       []           = lid
  weak {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) = weak {Γ = Γ} p
  weak {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) = ρl ∘l (weak {Γ = Γ} p ⊗l drop)
  weak {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) = ρl ∘l (weak {Γ = Γ} p ⊗l drop)
  weak {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) = weak {Γ = Γ} p ⊗l lid
  weak {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) = weak {Γ = Γ} p ⊗l lid
  weak {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) = weak {Γ = Γ} p ⊗l lid

  k-weak : ∀ {m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′) → Blk (weak {Γ = Γ} p)
  k-weak {Γ = SC.∅}       []           = k-id
  k-weak {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) = k-weak {Γ = Γ} p
  k-weak {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) = k-∘ k-ρ (k-⊗ (k-weak {Γ = Γ} p) k-drop)
  k-weak {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) = k-∘ k-ρ (k-⊗ (k-weak {Γ = Γ} p) k-drop)
  k-weak {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) = k-⊗ (k-weak {Γ = Γ} p) k-id
  k-weak {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) = k-⊗ (k-weak {Γ = Γ} p) k-id
  k-weak {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) = k-⊗ (k-weak {Γ = Γ} p) k-id

  -- carrying a slot into the left half (into the right half is `lassoc`)
  carryL : ∀ {X Y Z} → Tm L E ((X ⊗t Y) ⊗t Z) ((X ⊗t Z) ⊗t Y)
  carryL = lassoc⁻ ∘l (lid ⊗l lswap) ∘l lassoc

  k-carryL : ∀ {X Y Z} → Blk (carryL {X} {Y} {Z})
  k-carryL = k-∘ k-assoc⁻ (k-∘ (k-⊗ k-id k-swap) k-assoc)

  -- the middle-four interchange
  mixL : ∀ {X Y Z W} → Tm L E ((X ⊗t Y) ⊗t (Z ⊗t W)) ((X ⊗t Z) ⊗t (Y ⊗t W))
  mixL = lassoc⁻ ∘l (lid ⊗l (lassoc ∘l (lswap ⊗l lid) ∘l lassoc⁻)) ∘l lassoc

  k-mixL : ∀ {X Y Z W} → Blk (mixL {X} {Y} {Z} {W})
  k-mixL = k-∘ k-assoc⁻ (k-∘ (k-⊗ k-id (k-∘ k-assoc (k-∘ (k-⊗ k-swap k-id) k-assoc⁻))) k-assoc)

  -- ★ THE SPLIT: `_+ᵘ_` as a routing table. A slot used by one side goes to
  -- it; a `dup` only where both use it, and then the sum is `Many`.
  split : ∀ {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) → Tm L E (Co Γ (Ψ₁ +ᵘ Ψ₂)) (Co Γ Ψ₁ ⊗t Co Γ Ψ₂)
  split SC.∅          []          []          = ρl⁻
  split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) = split Γ Ψ₁ Ψ₂
  split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) = lassoc ∘l (split Γ Ψ₁ Ψ₂ ⊗l lid)
  split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) = lassoc ∘l (split Γ Ψ₁ Ψ₂ ⊗l lid)
  split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) = carryL ∘l (split Γ Ψ₁ Ψ₂ ⊗l lid)
  split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) = carryL ∘l (split Γ Ψ₁ Ψ₂ ⊗l lid)
  split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) = mixL ∘l (split Γ Ψ₁ Ψ₂ ⊗l dup)
  split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) = mixL ∘l (split Γ Ψ₁ Ψ₂ ⊗l dup)
  split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) = mixL ∘l (split Γ Ψ₁ Ψ₂ ⊗l dup)
  split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) = mixL ∘l (split Γ Ψ₁ Ψ₂ ⊗l dup)

  k-split : ∀ {m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) → Blk (split Γ Ψ₁ Ψ₂)
  k-split SC.∅          []          []          = k-ρ⁻
  k-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) = k-split Γ Ψ₁ Ψ₂
  k-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) = k-∘ k-assoc (k-⊗ (k-split Γ Ψ₁ Ψ₂) k-id)
  k-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) = k-∘ k-assoc (k-⊗ (k-split Γ Ψ₁ Ψ₂) k-id)
  k-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) = k-∘ k-carryL (k-⊗ (k-split Γ Ψ₁ Ψ₂) k-id)
  k-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) = k-∘ k-carryL (k-⊗ (k-split Γ Ψ₁ Ψ₂) k-id)
  k-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) = k-∘ k-mixL (k-⊗ (k-split Γ Ψ₁ Ψ₂) k-dup)
  k-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) = k-∘ k-mixL (k-⊗ (k-split Γ Ψ₁ Ψ₂) k-dup)
  k-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) = k-∘ k-mixL (k-⊗ (k-split Γ Ψ₁ Ψ₂) k-dup)
  k-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) = k-∘ k-mixL (k-⊗ (k-split Γ Ψ₁ Ψ₂) k-dup)

  -- a variable: its slot, the rest absent
  var-at : ∀ {m n} {Γ : Ctx m n} (i : Data.Fin.Fin n) → Tm L E (Co Γ (singleUse i G.One)) (ty (SC.lookup Γ i))
  var-at {Γ = Γ SC.▸ A} Data.Fin.zero    = dropl
  var-at {Γ = Γ SC.▸ A} (Data.Fin.suc i) = var-at {Γ = Γ} i

  k-var-at : ∀ {m n} {Γ : Ctx m n} (i : Data.Fin.Fin n) → Blk (var-at {Γ = Γ} i)
  k-var-at {Γ = Γ SC.▸ A} Data.Fin.zero    = k-dropl
  k-var-at {Γ = Γ SC.▸ A} (Data.Fin.suc i) = k-var-at {Γ = Γ} i

  -- a binder's slot, by its usage in the body (`elaborate`'s `bindEnv`)
  bindL : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (q : G.Quantity)
        → Tm L E (Co Γ Ψ ⊗t ty A) (Co (Γ SC.▸ A) (q ∷ Ψ))
  bindL G.Zero = ρl ∘l (lid ⊗l drop)
  bindL G.One  = lid
  bindL G.Many = lid

  k-bindL : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (q : G.Quantity) → Blk (bindL {Γ = Γ} {Ψ} {A} q)
  k-bindL G.Zero = k-∘ k-ρ (k-⊗ k-id k-drop)
  k-bindL G.One  = k-id
  k-bindL G.Many = k-id

------------------------------------------------------------------------
-- 3. CLOSURES: applied owned, and the grade of a body.
------------------------------------------------------------------------

module _ {L : Cx} {E : LTy} where

  -- a many-use closure applied OWNED: lent to its body, then dropped (the IR's
  -- `apply`; `Pass.tr apply`)
  apω : ∀ {g A B} → Tm L E (Fn many g A B ⊗t A) B
  apω = dropl ∘l lend (bsnd bev)

  k-apω : ∀ {A B} → Blk (apω {g = act} {A} {B})
  k-apω = k-∘ k-dropl (k-lend (k-snd k-bev))

  -- distributivity, by a one-shot closure per case (master's `distribute`)
  dist : ∀ {X A B} → Tm L E (X ⊗t (A ⊕t B)) ((X ⊗t A) ⊕t (X ⊗t B))
  dist = lev ∘l (lcase (llam (linl ∘l lswap) (k-∘ k-inl k-swap)) (llam (linr ∘l lswap) (k-∘ k-inr k-swap)) ⊗l lid) ∘l lswap

  k-dist : ∀ {X A B} → Blk (dist {X} {A} {B})
  k-dist = k-∘ k-ev (k-∘ (k-⊗ (k-case k-lam k-lam) k-id) k-swap)

-- a body's grade, when it is a block (D429: `pure` and `act` are blocks)
gdOf : ∀ {L X A B} (π : G.Purity) {b : LTm L (X ⊗t A) B} → Blk b → Gd (grade π) (copyIn b)
gdOf (G.fin _) β = k-copyIn β
gdOf G.eff     β = tt

-- a closure of the arrow's grade over a body
clo : ∀ {L E X A B} (π : G.Purity) (b : LTm L (X ⊗t A) B) → Blk b → Tm L E X (Fn many (grade π) A B)
clo π b β = llamω (copyIn b) (gdOf π β)

------------------------------------------------------------------------
-- 4. THE LEAVES: casts, SigOps, structure maps, calls, conversions.
------------------------------------------------------------------------

module _ {L : Cx} {E : LTy} where

  -- a term at equal types
  cast : ∀ {A A′ B B′} → A ≡ A′ → B ≡ B′ → Tm L E A B → Tm L E A′ B′
  cast p q t = subst₂ (Tm L E) p q t

  k-cast : ∀ {A A′ B B′} (p : A ≡ A′) (q : B ≡ B′) {t : Tm L E A B} → Blk t → Blk (cast p q t)
  k-cast refl refl β = β

  -- ★ a SigOp, at the IR's types of its base values; an arithmetic primitive
  -- as its block (D462: the arch layer runs blocks)
  opL : ∀ {A B} (si : SigOpInfo A B) → Tm L E (ty A) (ty B)
  opL si = cast (sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si))) (lop (sig (as-block si)))

  k-opL : ∀ {A B} (si : SigOpInfo A B) → Blk (opL si)
  k-opL si = k-cast (sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si))) (sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si))) k-op

-- a numeric operation (`elaborate`'s `numIR`, case for case)
numL : ∀ {L E m A U k} → Has A U → Sym U k → Tm L E (ty (Th.symDom {m} A k)) (ty (Th.symCod {m} A k))
numL {A = Th.int}   {k = Th.unary} h o = opL (numInfo h o)
numL {A = Th.int}   {k = Th.binary} h o = opL (numInfo h o)
numL {A = Th.int}   {k = Th.compare} h o = opL (numInfo h o)
numL {A = Th.float} {k = Th.unary} h o = opL (numInfo h o)
numL {A = Th.float} {k = Th.binary} h o = opL (numInfo h o)
numL {A = Th.float} {k = Th.compare} h o = opL (numInfo h o)

k-numL : ∀ {L E m A U k} (h : Has A U) (o : Sym U k) → Blk (numL {L} {E} {m} h o)
k-numL {A = Th.int}   {k = Th.unary} h o = k-opL (numInfo h o)
k-numL {A = Th.int}   {k = Th.binary} h o = k-opL (numInfo h o)
k-numL {A = Th.int}   {k = Th.compare} h o = k-opL (numInfo h o)
k-numL {A = Th.float} {k = Th.unary} h o = k-opL (numInfo h o)
k-numL {A = Th.float} {k = Th.binary} h o = k-opL (numInfo h o)
k-numL {A = Th.float} {k = Th.compare} h o = k-opL (numInfo h o)

-- a body's grade, when its blockness needs the grade to be finite (a body
-- that applies a closure of the same arrow's grade)
gdB : ∀ {L X A B} (π : G.Purity) {b : LTm L (X ⊗t A) B} → (∀ {φ} → π ≡ G.fin φ → Blk b) → Gd (grade π) (copyIn b)
gdB (G.fin φ) h = k-copyIn (h refl)
gdB G.eff     h = tt

-- a functor's layer, at the IR's types and at the core's code
layerEq : ∀ {m} {Δ : ST.KCtx m} (F : ST.Fun m) → ST.WFFun Δ F → ∀ (A : Ty m)
        → ty (ST.⟦ F ⟧F A) ≡ LF∙ (lf (I.eraseF F)) (ty A)
layerEq F w A = Relation.Binary.PropositionalEquality.trans (cong ⟪_⟫ (⌊⟧T-commute F A)) (⟪⟫-TI (wf-⌊⌋ w) ⌊ A ⌋)

module _ {L : Cx} where

  -- ★ D459: a structure map, by its table entry (`TypeCheck.Table.mapIR`, entry
  -- for entry)
  mapT : ∀ {m} {A B : Ty m} → Map A B → LTm L (ty A) (ty B)
  mapT mp-id                         = lid
  mapT mp-fst                        = ρl ∘l (lid ⊗l drop)
  mapT mp-snd                        = dropl
  mapT mp-terminal                   = drop
  mapT mp-inl                        = linl
  mapT mp-inr                        = linr
  mapT mp-initial                    = lzero
  mapT (mp-apply A B (G.fin G.pureᶠ)) = apω
  mapT (mp-apply A B (G.fin G.actᶠ))  = clo G.act (apω ∘l ρl) (k-∘ k-apω k-ρ)
  mapT (mp-apply A B G.eff)          = llamω (copyIn (apω ∘l ρl)) tt
  mapT (mp-In F w)                   = cast (sym (layerEq F w (μ F))) refl lIn
  mapT (mp-Out F G.pureᶠ w)          = cast refl (sym (layerEq F w (ν F G.pureᶠ))) lout
  mapT (mp-Out F G.actᶠ w)           =
    clo G.act (cast refl (sym (layerEq F w (ν F G.actᶠ))) lout ∘l ρl)
              (k-∘ (k-cast refl (sym (layerEq F w (ν F G.actᶠ))) k-nout) k-ρ)
  mapT mp-toFloat                    = opL i2f-info

  k-mapT : ∀ {m} {A B : Ty m} (mp : Map A B) → Blk (mapT {m} mp)
  k-mapT mp-id                         = k-id
  k-mapT mp-fst                        = k-∘ k-ρ (k-⊗ k-id k-drop)
  k-mapT mp-snd                        = k-dropl
  k-mapT mp-terminal                   = k-drop
  k-mapT mp-inl                        = k-inl
  k-mapT mp-inr                        = k-inr
  k-mapT mp-initial                    = k-zero
  k-mapT (mp-apply A B (G.fin G.pureᶠ)) = k-apω
  k-mapT (mp-apply A B (G.fin G.actᶠ))  = k-lamω
  k-mapT (mp-apply A B G.eff)          = k-lamω
  k-mapT (mp-In F w)                   = k-cast (sym (layerEq F w (μ F))) refl k-in
  k-mapT (mp-Out F G.pureᶠ w)          = k-cast refl (sym (layerEq F w (ν F G.pureᶠ))) k-nout
  k-mapT (mp-Out F G.actᶠ w)           = k-lamω
  k-mapT mp-toFloat                    = k-opL i2f-info

  -- ★ a SigOp named in the source (`elaborate`'s `sigOpIR`, case for case): an
  -- arrow is a closure whose body runs the op, a base value the op on `tt`
  sigL : (A : ST.Type) → CanonicalName → IsConcrete A → LTm L One (ty A)
  sigL (Dom ⇒[ G.mk-kind G.Zero (G.fin G.pureᶠ) ] Cod) name (con-fun bDom cCod) =
    clo G.pure (opL (value-info name ST.b-Unit cCod) ∘l dropl) (k-∘ (k-opL (value-info name ST.b-Unit cCod)) k-dropl)
  sigL (Dom ⇒[ G.mk-kind G.Zero G.eff ] Cod) name (con-fun bDom cCod) =
    clo G.eff (opL (arrow-info (G.mk-kind G.Zero G.eff) name ST.b-Unit cCod) ∘l dropl) (k-∘ (k-opL (arrow-info (G.mk-kind G.Zero G.eff) name ST.b-Unit cCod)) k-dropl)
  sigL (Dom ⇒[ G.mk-kind G.Zero (G.fin G.actᶠ) ] Cod) name (con-fun bDom cCod) =
    clo G.act (opL (arrow-info (G.mk-kind G.Zero G.act) name ST.b-Unit cCod) ∘l dropl) (k-∘ (k-opL (arrow-info (G.mk-kind G.Zero G.act) name ST.b-Unit cCod)) k-dropl)
  sigL (Dom ⇒[ G.mk-kind G.One π ] Cod) name (con-fun bDom cCod) =
    clo π (opL (arrow-info (G.mk-kind G.One π) name bDom cCod) ∘l dropl) (k-∘ (k-opL (arrow-info (G.mk-kind G.One π) name bDom cCod)) k-dropl)
  sigL (Dom ⇒[ G.mk-kind G.Many π ] Cod) name (con-fun bDom cCod) =
    clo π (opL (arrow-info (G.mk-kind G.Many π) name bDom cCod) ∘l dropl) (k-∘ (k-opL (arrow-info (G.mk-kind G.Many π) name bDom cCod)) k-dropl)
  {-# CATCHALL #-}
  sigL _ name (con-base ib) = opL (value-info name ST.b-Unit ib) ∘l drop

  k-sigL : (A : ST.Type) (name : CanonicalName) (c : IsConcrete A) → Blk (sigL A name c)
  k-sigL (Dom ⇒[ G.mk-kind G.Zero (G.fin G.pureᶠ) ] Cod) name (con-fun bDom cCod) = k-lamω
  k-sigL (Dom ⇒[ G.mk-kind G.Zero G.eff ] Cod) name (con-fun bDom cCod) = k-lamω
  k-sigL (Dom ⇒[ G.mk-kind G.Zero (G.fin G.actᶠ) ] Cod) name (con-fun bDom cCod) = k-lamω
  k-sigL (Dom ⇒[ G.mk-kind G.One π ] Cod) name (con-fun bDom cCod) = k-lamω
  k-sigL (Dom ⇒[ G.mk-kind G.Many π ] Cod) name (con-fun bDom cCod) = k-lamω
  -- (a base witness fixes the type's head, so `sigL`'s last clause fires)
  k-sigL _ name (con-base (ST.b-var {i = ()} _))
  k-sigL _ name (con-base ib@ST.b-Unit) = k-∘ (k-opL (value-info name ST.b-Unit ib)) k-drop
  k-sigL _ name (con-base ib@ST.b-Void) = k-∘ (k-opL (value-info name ST.b-Unit ib)) k-drop
  k-sigL _ name (con-base ib@ST.b-Int) = k-∘ (k-opL (value-info name ST.b-Unit ib)) k-drop
  k-sigL _ name (con-base ib@ST.b-Float) = k-∘ (k-opL (value-info name ST.b-Unit ib)) k-drop
  k-sigL _ name (con-base ib@(ST.b-* a b)) = k-∘ (k-opL (value-info name ST.b-Unit ib)) k-drop
  k-sigL _ name (con-base ib@(ST.b-+ a b)) = k-∘ (k-opL (value-info name ST.b-Unit ib)) k-drop

  -- ★ a conversion along a subtyping derivation (`CoerceIR.coeIR`): an arrow
  -- is re-wrapped, at the target's grade
  wrap : ∀ {π π′ X X′ Y Y′} → π G.⊑π π′ → (f : LTm L X′ X) → Blk f → (g : LTm L Y Y′) → Blk g
       → LTm L (Fn many (grade π) X Y) (Fn many (grade π′) X′ Y′)
  wrap r f φ g γ = llamω (copyIn (g ∘l apω ∘l (lid ⊗l f))) (gd r)
    where
      gd : ∀ {π π′} (r : π G.⊑π π′) → Gd (grade π′) (copyIn (g ∘l apω {g = grade π} ∘l (lid ⊗l f)))
      gd G.⊑-pure = k-copyIn (k-∘ γ (k-∘ k-apω (k-⊗ k-id φ)))
      gd G.⊑-pa   = k-copyIn (k-∘ γ (k-∘ k-apω (k-⊗ k-id φ)))
      gd G.⊑-act  = k-copyIn (k-∘ γ (k-∘ k-apω (k-⊗ k-id φ)))
      gd G.⊑-pe   = tt
      gd G.⊑-ae   = tt
      gd G.⊑-eff  = tt

  wrap₀ : ∀ {π π′ Y Y′} → π G.⊑π π′ → (g : LTm L Y Y′) → Blk g
        → LTm L (Fn many (grade π) One Y) (Fn many (grade π′) One Y′)
  wrap₀ r g γ = llamω (copyIn (g ∘l apω)) (gd r)
    where
      gd : ∀ {π π′} (r : π G.⊑π π′) → Gd (grade π′) (copyIn (g ∘l apω {g = grade π}))
      gd G.⊑-pure = k-copyIn (k-∘ γ k-apω)
      gd G.⊑-pa   = k-copyIn (k-∘ γ k-apω)
      gd G.⊑-act  = k-copyIn (k-∘ γ k-apω)
      gd G.⊑-pe   = tt
      gd G.⊑-ae   = tt
      gd G.⊑-eff  = tt

  coeL : ∀ {m} {A B : Ty m} → A <: B → LTm L (ty A) (ty B)
  k-coeL : ∀ {m} {A B : Ty m} (p : A <: B) → Blk (coeL p)

  coeL sub-void   = lzero
  coeL sub-unit   = lid
  coeL sub-int    = lid
  coeL sub-float  = lid
  coeL (sub-arr {q = G.Zero} a b r) = wrap₀ r (coeL b) (k-coeL b)
  coeL (sub-arr {q = G.One}  a b r) = wrap r (coeL a) (k-coeL a) (coeL b) (k-coeL b)
  coeL (sub-arr {q = G.Many} a b r) = wrap r (coeL a) (k-coeL a) (coeL b) (k-coeL b)
  coeL (sub-* a b) = coeL a ⊗l coeL b
  coeL (sub-+ a b) = lcase (linl ∘l coeL a) (linr ∘l coeL b)
  coeL sub-μ      = lid
  coeL (sub-ν _)  = lid
  coeL sub-var    = lid

  k-coeL sub-void   = k-zero
  k-coeL sub-unit   = k-id
  k-coeL sub-int    = k-id
  k-coeL sub-float  = k-id
  k-coeL (sub-arr {q = G.Zero} a b r) = k-lamω
  k-coeL (sub-arr {q = G.One}  a b r) = k-lamω
  k-coeL (sub-arr {q = G.Many} a b r) = k-lamω
  k-coeL (sub-* a b) = k-⊗ (k-coeL a) (k-coeL b)
  k-coeL (sub-+ a b) = k-case (k-∘ k-inl (k-coeL a)) (k-∘ k-inr (k-coeL b))
  k-coeL sub-μ      = k-id
  k-coeL (sub-ν _)  = k-id
  k-coeL sub-var    = k-id

  -- `runCoe`: a conversion that changes no representation is none
  coeR : ∀ {m Z} {A B : Ty m} (p : A <: B) → Relation.Nullary.Dec (VoidFree p) → LTm L Z (ty A) → LTm L Z (ty B)
  coeR p (yes vf) t = cast refl (cong ⟪_⟫ (erase-eq p vf)) t
  coeR p (no _)   t = coeL p ∘l t

  k-coeR : ∀ {m Z} {A B : Ty m} (p : A <: B) (d : Relation.Nullary.Dec (VoidFree p)) {t : LTm L Z (ty A)} → Blk t → Blk (coeR p d t)
  k-coeR p (yes vf) β = k-cast refl (cong ⟪_⟫ (erase-eq p vf)) β
  k-coeR p (no _)   β = k-∘ (k-coeL p) β

------------------------------------------------------------------------
-- 5. THE CALLS: a definition of the program, by its name, its call's types
-- and its grade; an unlinked one halts (`FromIR.unlinked`).
------------------------------------------------------------------------

Rs : Cx → Set
Rs L = CanonicalName → (A B : IRTy) (g : Gr) → Maybe (Σ ℕ λ l → L ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫)

module _ {L : Cx} where

  callM : ∀ {g A B} → Maybe (Σ ℕ λ l → L ∋[ l ] sg once g One A B) → LTm L A B
  callM (just (l , p)) = lapp p ∘l (lclo Idf p ⊗l lid) ∘l lul⁻
  callM nothing        = lzero ∘l (lop (sig unlinked-i) ∘l drop)

  k-callM : ∀ {A B} (r : Maybe (Σ ℕ λ l → L ∋[ l ] sg once act One A B)) → Blk (callM r)
  k-callM (just (l , p)) = k-∘ k-app (k-∘ (k-⊗ k-clo k-id) k-lul⁻)
  k-callM nothing        = k-∘ k-zero (k-∘ k-op k-drop)

  -- a reference to a definition (`IR.Ref.refIR`, case for case): an arrow is a
  -- closure whose body calls it, any other type its value, called on `tt`
  refL : Rs L → ∀ {m} (T : Ty m) → CanonicalName → LTm L One (ty T)
  refL rs (A ⇒[ G.mk-kind G.Zero π ] B) f = llamω (copyIn (callM (rs f I.Unit ⌊ B ⌋ (grade π)) ∘l dropl))
                                                  (gdB π (λ { refl → k-∘ (k-callM (rs f I.Unit ⌊ B ⌋ act)) k-dropl }))
  refL rs (A ⇒[ G.mk-kind G.One π ] B) f  = llamω (copyIn (callM (rs f ⌊ A ⌋ ⌊ B ⌋ (grade π)) ∘l dropl))
                                                  (gdB π (λ { refl → k-∘ (k-callM (rs f ⌊ A ⌋ ⌊ B ⌋ act)) k-dropl }))
  refL rs (A ⇒[ G.mk-kind G.Many π ] B) f = llamω (copyIn (callM (rs f ⌊ A ⌋ ⌊ B ⌋ (grade π)) ∘l dropl))
                                                  (gdB π (λ { refl → k-∘ (k-callM (rs f ⌊ A ⌋ ⌊ B ⌋ act)) k-dropl }))
  {-# CATCHALL #-}
  refL rs T f = callM (rs f I.Unit ⌊ T ⌋ act) ∘l drop

  k-refL : (rs : Rs L) → ∀ {m} (T : Ty m) (f : CanonicalName) → Blk (refL rs T f)
  k-refL rs (A ⇒[ G.mk-kind G.Zero π ] B) f = k-lamω
  k-refL rs (A ⇒[ G.mk-kind G.One π ] B) f  = k-lamω
  k-refL rs (A ⇒[ G.mk-kind G.Many π ] B) f = k-lamω
  k-refL rs T@ST.Unit      f = k-∘ (k-callM (rs f I.Unit ⌊ T ⌋ act)) k-drop
  k-refL rs T@ST.Void      f = k-∘ (k-callM (rs f I.Unit ⌊ T ⌋ act)) k-drop
  k-refL rs T@(_ ST.* _)   f = k-∘ (k-callM (rs f I.Unit ⌊ T ⌋ act)) k-drop
  k-refL rs T@(_ ST.+ _)   f = k-∘ (k-callM (rs f I.Unit ⌊ T ⌋ act)) k-drop
  k-refL rs T@(ST.μ _)     f = k-∘ (k-callM (rs f I.Unit ⌊ T ⌋ act)) k-drop
  k-refL rs T@(ST.ν _ _)   f = k-∘ (k-callM (rs f I.Unit ⌊ T ⌋ act)) k-drop
  k-refL rs T@ST.Int       f = k-∘ (k-callM (rs f I.Unit ⌊ T ⌋ act)) k-drop
  k-refL rs T@ST.Float     f = k-∘ (k-callM (rs f I.Unit ⌊ T ⌋ act)) k-drop
  k-refL rs T@(ST.var _)   f = k-∘ (k-callM (rs f I.Unit ⌊ T ⌋ act)) k-drop

------------------------------------------------------------------------
-- 6. ★★ THE BRIDGE: `Lq⟦_⟧`, clause for clause `elaborate`, a block.
------------------------------------------------------------------------

module _ {L : Cx} (rs : Rs L) where

  -- a usage relabelled along an equation (`elaborate`'s `subst` at an
  -- erased argument, `erase-arg-usage`)
  castΦ : ∀ {m n} {Γ : Ctx m n} {Φ Φ′ : Usage n} {B} → Φ ≡ Φ′ → LTm L (Co Γ Φ) B → LTm L (Co Γ Φ′) B
  castΦ {Γ = Γ} {B = B} e t = subst (λ Φ → LTm L (Co Γ Φ) B) e t

  k-castΦ : ∀ {m n} {Γ : Ctx m n} {Φ Φ′ : Usage n} {B} (e : Φ ≡ Φ′) {t : LTm L (Co Γ Φ) B} → Blk t → Blk (castΦ {Γ = Γ} e t)
  k-castΦ refl β = β

  Lq : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} → Expr Γ Ψ A → LTm L (Co Γ Ψ) (ty A)
  Lq-blk : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (e : Expr Γ Ψ A) → Blk (Lq e)

  Lq {Γ = Γ} (var i) = var-at {Γ = Γ} i
  -- a lambda: a closure over the variables its body uses; an unused argument
  -- is dropped on entry
  Lq (lam {q' = G.Zero} {π = π} G.Zero _ e) = clo π (Lq e ∘l ρl ∘l (lid ⊗l drop)) (k-∘ (Lq-blk e) (k-∘ k-ρ (k-⊗ k-id k-drop)))
  Lq (lam {q' = G.Zero} {π = π} G.One  _ e) = clo π (Lq e ∘l ρl ∘l (lid ⊗l drop)) (k-∘ (Lq-blk e) (k-∘ k-ρ (k-⊗ k-id k-drop)))
  Lq (lam {q' = G.Zero} {π = π} G.Many _ e) = clo π (Lq e ∘l ρl ∘l (lid ⊗l drop)) (k-∘ (Lq-blk e) (k-∘ k-ρ (k-⊗ k-id k-drop)))
  Lq (lam {q' = G.One}  {π = π} G.One  _ e) = clo π (Lq e) (Lq-blk e)
  Lq (lam {q' = G.One}  {π = π} G.Many _ e) = clo π (Lq e) (Lq-blk e)
  Lq (lam {q' = G.Many} {π = π} G.Many _ e) = clo π (Lq e) (Lq-blk e)
  -- an application: the context SPLIT between the function and the argument
  Lq {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} f x) =
    castΦ {Γ = Γ} (sym (erase-arg-usage Ψ₁ Ψ₂)) (apω ∘l (Lq f ⊗l lid) ∘l ρl⁻)
  Lq {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} f x) =
    apω ∘l (Lq f ⊗l (Lq x ∘l weak {Γ = Γ} (⊑ᵘ-*One Ψ₂))) ∘l split Γ Ψ₁ (G.One *ᵘ Ψ₂)
  Lq {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} f x) =
    apω ∘l (Lq f ⊗l (Lq x ∘l weak {Γ = Γ} (⊑ᵘ-*Many Ψ₂))) ∘l split Γ Ψ₁ (G.Many *ᵘ Ψ₂)
  -- an effectful application, suspended: a closure on `tt` that applies
  Lq {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} {π = π} f x) =
    castΦ {Γ = Γ} (sym (erase-arg-usage Ψ₁ Ψ₂))
      (llamω (copyIn ((apω ∘l (Lq f ⊗l lid) ∘l ρl⁻) ∘l ρl))
             (gdB π (λ { refl → k-∘ (k-∘ k-apω (k-∘ (k-⊗ (Lq-blk f) k-id) k-ρ⁻)) k-ρ })))
  Lq {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} {π = π} f x) =
    llamω (copyIn ((apω ∘l (Lq f ⊗l (Lq x ∘l weak {Γ = Γ} (⊑ᵘ-*One Ψ₂))) ∘l split Γ Ψ₁ (G.One *ᵘ Ψ₂)) ∘l ρl))
          (gdB π (λ { refl → k-∘ (k-∘ k-apω (k-∘ (k-⊗ (Lq-blk f) (k-∘ (Lq-blk x) (k-weak {Γ = Γ} (⊑ᵘ-*One Ψ₂))))
                                                    (k-split Γ Ψ₁ (G.One *ᵘ Ψ₂)))) k-ρ }))
  Lq {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} {π = π} f x) =
    llamω (copyIn ((apω ∘l (Lq f ⊗l (Lq x ∘l weak {Γ = Γ} (⊑ᵘ-*Many Ψ₂))) ∘l split Γ Ψ₁ (G.Many *ᵘ Ψ₂)) ∘l ρl))
          (gdB π (λ { refl → k-∘ (k-∘ k-apω (k-∘ (k-⊗ (Lq-blk f) (k-∘ (Lq-blk x) (k-weak {Γ = Γ} (⊑ᵘ-*Many Ψ₂))))
                                                    (k-split Γ Ψ₁ (G.Many *ᵘ Ψ₂)))) k-ρ }))
  Lq {Γ = Γ} (pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) = (Lq a ⊗l Lq b) ∘l split Γ Ψ₁ Ψ₂
  Lq (fst' p) = (ρl ∘l (lid ⊗l drop)) ∘l Lq p
  Lq (snd' p) = dropl ∘l Lq p
  Lq (inl' a) = linl ∘l Lq a
  Lq (inr' b) = linr ∘l Lq b
  -- a case: the scrutinee's share split off, the arms' context distributed
  Lq {Γ = Γ} (case' {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} s l r) =
    lcase (Lq l ∘l bindL {Γ = Γ} {A = A} qℓ ∘l (weak {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) ⊗l lid))
          (Lq r ∘l bindL {Γ = Γ} {A = B} qr ∘l (weak {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) ⊗l lid))
    ∘l dist ∘l (lid ⊗l Lq s) ∘l lswap ∘l split Γ Ψs (Ψₗ ⊔ᵘ Ψᵣ)
  Lq unit = drop
  Lq (absurd v) = lzero ∘l Lq v
  -- a let: an erased binding is never evaluated
  Lq {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} e1 e2) =
    castΦ {Γ = Γ} (sym (erase-arg-usage Ψ₂ Ψ₁)) (Lq e2)
  Lq {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} {A = A} e1 e2) =
    Lq e2 ∘l bindL {Γ = Γ} {A = A} G.One ∘l (lid ⊗l (Lq e1 ∘l weak {Γ = Γ} (⊑ᵘ-*One Ψ₁))) ∘l split Γ Ψ₂ (G.One *ᵘ Ψ₁)
  Lq {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} {A = A} e1 e2) =
    Lq e2 ∘l bindL {Γ = Γ} {A = A} G.Many ∘l (lid ⊗l (Lq e1 ∘l weak {Γ = Γ} (⊑ᵘ-*Many Ψ₁))) ∘l split Γ Ψ₂ (G.Many *ᵘ Ψ₁)
  Lq (int n) = lconst {b = int} n ∘l drop
  Lq (float d) = lconst {b = float} d ∘l drop
  Lq (num h o e) = numL h o ∘l Lq e
  Lq (coerce p f) = coeR p (voidFree? p) (Lq f)
  Lq (sigOp {A = A} name c) = cast refl (cong ⟪_⟫ (sym (⌊wk₀⌋ A))) (sigL A name c ∘l drop)
  Lq {A = A} (closure name) = refL rs A (bare name) ∘l drop
  Lq {A = A} (poly name _) = refL rs A (bare name) ∘l drop
  Lq (closed e) = Lq e ∘l drop
  Lq (lift-morphism {π = π} mp) = clo π (mapT mp ∘l dropl) (k-∘ (k-mapT mp) k-dropl)
  Lq {Γ = Γ} (morph-app {Ψ = Ψ} mp x) =
    mapT mp ∘l Lq x ∘l weak {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (G.Many *ᵘ Ψ)))
  -- the combinators: closures over the closures they combine
  Lq {Γ = Γ} (comp' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} f g) =
    llamω (copyIn (apω ∘l (lid ⊗l apω) ∘l lassoc))
          (gdB π (λ { refl → k-∘ k-apω (k-∘ (k-⊗ k-id k-apω) k-assoc) }))
    ∘l (Lq f ⊗l (Lq g ∘l weak {Γ = Γ} (⊑ᵘ-*Many Ψ₂))) ∘l split Γ Ψ₁ (G.Many *ᵘ Ψ₂)
  Lq {Γ = Γ} (copair' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} f g) =
    llamω (copyIn (lcase (apω ∘l ((ρl ∘l (lid ⊗l drop)) ⊗l lid)) (apω ∘l (dropl ⊗l lid)) ∘l dist))
          (gdB π (λ { refl → k-∘ (k-case (k-∘ k-apω (k-⊗ (k-∘ k-ρ (k-⊗ k-id k-drop)) k-id))
                                          (k-∘ k-apω (k-⊗ k-dropl k-id))) k-dist }))
    ∘l (Lq f ⊗l Lq g) ∘l split Γ Ψ₁ Ψ₂
  Lq {Γ = Γ} (fork' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} f g) =
    llamω (copyIn ((apω ⊗l apω) ∘l mixL ∘l (lid ⊗l dup)))
          (gdB π (λ { refl → k-∘ (k-⊗ k-apω k-apω) (k-∘ k-mixL (k-⊗ k-id k-dup)) }))
    ∘l (Lq f ⊗l Lq g) ∘l split Γ Ψ₁ Ψ₂
  Lq (curry' {π₀ = π₀} {π = π} f) =
    clo π₀ (llamω (copyIn (apω ∘l lassoc)) (gdB π (λ { refl → k-∘ k-apω k-assoc }))) k-lamω
    ∘l Lq f
  -- the fold: the algebra LENT to every layer, no copy per layer
  Lq {Γ = Γ} (cata {Ψ = Ψ} {F = F} {A = A} {π = π} wfF alg) =
    llamω (copyIn (dropl ∘l lend (lcata (lf (I.eraseF F)) (bsnd (cast (layerEq F wfF A) refl bev)))))
          (gdB π (λ { refl → k-∘ k-dropl (k-lend (k-cata (k-snd (k-cast (layerEq F wfF A) refl k-bev)))) }))
    ∘l Lq alg ∘l weak {Γ = Γ} (⊑ᵘ-*Many Ψ)
  -- the unfold: the coalgebra and the seed, a ν
  Lq {Γ = Γ} (ana {Ψ = Ψ} {F = F} {A = A} {π₀ = π₀} wfF coalg) =
    clo π₀ (lunf ∘l (cast refl (cong (Fn many act (ty A)) (layerEq F wfF A)) lid ⊗l lid))
           (k-∘ k-unf (k-⊗ (k-cast refl (cong (Fn many act (ty A)) (layerEq F wfF A)) k-id) k-id))
    ∘l Lq coalg ∘l weak {Γ = Γ} (⊑ᵘ-*Many Ψ)
  -- the loop: the round LENT to every round
  Lq {Γ = Γ} (loop {Ψ = Ψ} round) =
    llamω (copyIn (dropl ∘l lend (liter (bsnd bev) (k-snd k-bev)))) tt
    ∘l Lq round ∘l weak {Γ = Γ} (⊑ᵘ-*Many Ψ)

  Lq-blk {Γ = Γ} (var i) = k-var-at {Γ = Γ} i
  Lq-blk (lam {q' = G.Zero} G.Zero _ e) = k-lamω
  Lq-blk (lam {q' = G.Zero} G.One  _ e) = k-lamω
  Lq-blk (lam {q' = G.Zero} G.Many _ e) = k-lamω
  Lq-blk (lam {q' = G.One}  G.One  _ e) = k-lamω
  Lq-blk (lam {q' = G.One}  G.Many _ e) = k-lamω
  Lq-blk (lam {q' = G.Many} G.Many _ e) = k-lamω
  Lq-blk {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} f x) =
    k-castΦ {Γ = Γ} (sym (erase-arg-usage Ψ₁ Ψ₂)) (k-∘ k-apω (k-∘ (k-⊗ (Lq-blk f) k-id) k-ρ⁻))
  Lq-blk {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} f x) =
    k-∘ k-apω (k-∘ (k-⊗ (Lq-blk f) (k-∘ (Lq-blk x) (k-weak {Γ = Γ} (⊑ᵘ-*One Ψ₂)))) (k-split Γ Ψ₁ (G.One *ᵘ Ψ₂)))
  Lq-blk {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} f x) =
    k-∘ k-apω (k-∘ (k-⊗ (Lq-blk f) (k-∘ (Lq-blk x) (k-weak {Γ = Γ} (⊑ᵘ-*Many Ψ₂)))) (k-split Γ Ψ₁ (G.Many *ᵘ Ψ₂)))
  Lq-blk {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} f x) = k-castΦ {Γ = Γ} (sym (erase-arg-usage Ψ₁ Ψ₂)) k-lamω
  Lq-blk (effApp {q = G.One} f x) = k-lamω
  Lq-blk (effApp {q = G.Many} f x) = k-lamω
  Lq-blk {Γ = Γ} (pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) = k-∘ (k-⊗ (Lq-blk a) (Lq-blk b)) (k-split Γ Ψ₁ Ψ₂)
  Lq-blk (fst' p) = k-∘ (k-∘ k-ρ (k-⊗ k-id k-drop)) (Lq-blk p)
  Lq-blk (snd' p) = k-∘ k-dropl (Lq-blk p)
  Lq-blk (inl' a) = k-∘ k-inl (Lq-blk a)
  Lq-blk (inr' b) = k-∘ k-inr (Lq-blk b)
  Lq-blk {Γ = Γ} (case' {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} s l r) =
    k-∘ (k-case (k-∘ (Lq-blk l) (k-∘ (k-bindL {Γ = Γ} {A = A} qℓ) (k-⊗ (k-weak {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)) k-id)))
                (k-∘ (Lq-blk r) (k-∘ (k-bindL {Γ = Γ} {A = B} qr) (k-⊗ (k-weak {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)) k-id))))
        (k-∘ k-dist (k-∘ (k-⊗ k-id (Lq-blk s)) (k-∘ k-swap (k-split Γ Ψs (Ψₗ ⊔ᵘ Ψᵣ)))))
  Lq-blk unit = k-drop
  Lq-blk (absurd v) = k-∘ k-zero (Lq-blk v)
  Lq-blk {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} e1 e2) =
    k-castΦ {Γ = Γ} (sym (erase-arg-usage Ψ₂ Ψ₁)) (Lq-blk e2)
  Lq-blk {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} {A = A} e1 e2) =
    k-∘ (Lq-blk e2) (k-∘ (k-bindL {Γ = Γ} {A = A} G.One)
      (k-∘ (k-⊗ k-id (k-∘ (Lq-blk e1) (k-weak {Γ = Γ} (⊑ᵘ-*One Ψ₁)))) (k-split Γ Ψ₂ (G.One *ᵘ Ψ₁))))
  Lq-blk {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} {A = A} e1 e2) =
    k-∘ (Lq-blk e2) (k-∘ (k-bindL {Γ = Γ} {A = A} G.Many)
      (k-∘ (k-⊗ k-id (k-∘ (Lq-blk e1) (k-weak {Γ = Γ} (⊑ᵘ-*Many Ψ₁)))) (k-split Γ Ψ₂ (G.Many *ᵘ Ψ₁))))
  Lq-blk (int n) = k-∘ k-const k-drop
  Lq-blk (float d) = k-∘ k-const k-drop
  Lq-blk (num h o e) = k-∘ (k-numL h o) (Lq-blk e)
  Lq-blk (coerce p f) = k-coeR p (voidFree? p) (Lq-blk f)
  Lq-blk (sigOp {A = A} name c) = k-cast refl (cong ⟪_⟫ (sym (⌊wk₀⌋ A))) (k-∘ (k-sigL A name c) k-drop)
  Lq-blk {A = A} (closure name) = k-∘ (k-refL rs A (bare name)) k-drop
  Lq-blk {A = A} (poly name _) = k-∘ (k-refL rs A (bare name)) k-drop
  Lq-blk (closed e) = k-∘ (Lq-blk e) k-drop
  Lq-blk (lift-morphism mp) = k-lamω
  Lq-blk {Γ = Γ} (morph-app {Ψ = Ψ} mp x) =
    k-∘ (k-mapT mp) (k-∘ (Lq-blk x) (k-weak {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (G.Many *ᵘ Ψ)))))
  Lq-blk {Γ = Γ} (comp' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) =
    k-∘ k-lamω (k-∘ (k-⊗ (Lq-blk f) (k-∘ (Lq-blk g) (k-weak {Γ = Γ} (⊑ᵘ-*Many Ψ₂)))) (k-split Γ Ψ₁ (G.Many *ᵘ Ψ₂)))
  Lq-blk {Γ = Γ} (copair' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) = k-∘ k-lamω (k-∘ (k-⊗ (Lq-blk f) (Lq-blk g)) (k-split Γ Ψ₁ Ψ₂))
  Lq-blk {Γ = Γ} (fork' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) = k-∘ k-lamω (k-∘ (k-⊗ (Lq-blk f) (Lq-blk g)) (k-split Γ Ψ₁ Ψ₂))
  Lq-blk (curry' f) = k-∘ k-lamω (Lq-blk f)
  Lq-blk {Γ = Γ} (cata {Ψ = Ψ} wfF alg) = k-∘ k-lamω (k-∘ (Lq-blk alg) (k-weak {Γ = Γ} (⊑ᵘ-*Many Ψ)))
  Lq-blk {Γ = Γ} (ana {Ψ = Ψ} wfF coalg) = k-∘ k-lamω (k-∘ (Lq-blk coalg) (k-weak {Γ = Γ} (⊑ᵘ-*Many Ψ)))
  Lq-blk {Γ = Γ} (loop {Ψ = Ψ} round) = k-∘ k-lamω (k-∘ (Lq-blk round) (k-weak {Γ = Γ} (⊑ᵘ-*Many Ψ)))
