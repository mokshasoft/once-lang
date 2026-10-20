-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Back — the Spec's surface typing gives the
-- compiler's (plan 0.121 §3.6, F5).
--
-- The converse of `SpecFront.Check`. A Spec derivation of the related
-- expression (`RX`) in related locals (`LR`) gives the compiler's, at the
-- related type. Two things the Spec's surface rules do not say, the
-- compiler's do: how much each variable is used (linearity), and the type a
-- generator's application has in the core. Both are read from a core typing
-- of the Spec's term (`CoreInv`): the compiler's usage is below the one that
-- typing gives, so a lambda's body uses its variable within the arrow's
-- quantity; and the term's core type is the surface one.
--
-- What the compiler's rules ask of a reference — which table holds the name,
-- at what type, with what instance — is asked of the scope (the parameters
-- `h-…`), which the telescope walk discharges.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Lang.Name using (showCanonical)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
import Once.Lang.Type as LT
import Once.Lang.Type.WellFormed as LW
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
open import Once.Lang.Typing.Scope using (Imports; PolyCtx; lookupImport; lookupPolyPrefix)
open import Once.Adequacy.SpecCore.Type using (TyR)
import Once.Adequacy.SpecFront.Scope as Sc

module Once.Adequacy.SpecFront.Back
  (Σ : Signature) {s : ℕ} (S′ : SC.Defs s) (nm : Fin s → CanonicalName)
  {imps sg : Imports} {polys : PolyCtx} {ps : List String}
  {m : ℕ} (Δ : ST.KCtx m)
  -- every definition's name is an own name
  (h-name : ∀ d → Σ[ x ∈ String ] nm d ≡ canonical (x ∷ []))
  -- a declaration of Σ is the signature table's, at its type
  (h-sig : ∀ {c t} → NotGenerator c → (c ∶ t) ∈ Σ
         → Σ[ T ∈ LT.Type ] (lookupImport sg (showCanonical c) ≡ just T) × LW.IsConcrete T × TyR Δ T ⌜ t ⌝ᵈ)
  -- a definition with no type variables, not a polymorphic one: the definitions table's
  (h-mono : ∀ {d x} → nm d ≡ canonical (x ∷ []) → ¬ (x ∈ ps)
          → (lookupImport sg x ≡ nothing)
            × Σ[ T ∈ LT.Type ] (lookupImport imps x ≡ just T) × LW.IsConcrete T
              × (∀ τ → TyR Δ T (SC.Schema.type (S′ SC.!! d) ST.⟨ τ ⟩)))
  -- a definition with type variables is a polymorphic one
  (h-ps : ∀ {d x} → nm d ≡ canonical (x ∷ []) → 0 < SC.Schema.arity (S′ SC.!! d) → x ∈ ps)
  -- a polymorphic definition: the telescope's, with what its schema says
  (h-poly : ∀ {d x} → nm d ≡ canonical (x ∷ []) → x ∈ ps → Sc.PolyAt S′ imps polys Δ d x)
  -- a polymorphic definition's name is no declaration's
  (h-own-sig : ∀ {x t} → x ∈ ps → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σ))
  where

open import Data.Fin using (zero; suc)
open import Data.Nat using (suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (Dec; yes; no)
import Data.List.Relation.Unary.Any
import Data.List.Membership.Propositional.Properties
import Data.String
import Data.Fin
import Data.List

import Once.Lang.Type.Grade as LG
import Once.Lang.Type.Sub as LS
import Once.Spec.Grade as SG
import Once.Spec.Sub as SS
import Once.Spec.Context as SCx
import Once.Spec.Surface.Syntax as SX
import Once.Lang.Context as LC
open import Once.Lang.Context using (svar)
open import Once.Lang.Syntax using (RawExpr; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Lang.Typing
open import Once.Lang.Typing.Scope using (NamedCtx; mkCtx; classifyAppHead; classifyAppHeadView; viewToPba; AppHeadView;
  Binding; lookupLocal-go; lookupLocal-at; lookupLocal-next)
import Once.Lang.Typing.Scope as LTS
open Binding using (name)
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)
open import Once.Adequacy.SpecGrammar.Expr using (opS)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Context using (uS; uS-zero; uS-single; uS-+; uS-*; ≤q-L)
open import Once.Adequacy.SpecFront.Expr
open import Once.Adequacy.SpecFront.Types Δ
open import Once.Adequacy.SpecFront.Locals Σ S′ nm Δ
open import Once.Adequacy.SpecFront.CoreInv Σ S′ {Δ = Δ}
open import Once.Adequacy.SpecFront.GenInv Σ S′ {Δ = Δ}
import Once.Spec.Surface.Typing Σ S′ nm as SU
open import Once.Spec.Core.Typing Σ S′ using (_⊩_⊢[_]_∷_!_)
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-refl; ⊑ᵘ-+; ⊑ᵘ-*ʳ; ⊑ᵘ-*ˡ; +ᵘ-comm; One*ᵘ)

private
  C : ∀ (n : ℕ) → List Binding → LC.Ctx n → NamedCtx
  C n Γn Γd = mkCtx n Γn Γd imps polys sg

  -- the Spec's core context of its locals
  ctxL : ∀ {n} → SU.Locals m n → SCx.Ctx m n
  ctxL SU.∅           = SCx.∅
  ctxL (L SU.▹ x ∶ A) = ctxL L SCx.▸ A

------------------------------------------------------------------------
-- What a derivation read back gives
------------------------------------------------------------------------

record BSyn {n} (Γn : List Binding) (Γd : LC.Ctx n) (e : RawExpr) (A′ : ST.Ty m) (Φ : SCx.Usage n) : Set where
  constructor bsyn
  field
    {A} : LT.Type
    ra  : TyR Δ A A′
    {Ψ} : LC.Usage n
    der : C n Γn Γd ⊢ᵢ e ∶ A ⨾ Ψ
    use : uS Ψ SCx.⊑ᵘ Φ

record BChk {n} (Γn : List Binding) (Γd : LC.Ctx n) (e : RawExpr) (A : LT.Type) (Φ : SCx.Usage n) : Set where
  constructor bchk
  field
    {Ψ} : LC.Usage n
    der : C n Γn Γd ⊢ᶜ e ∶ A ⨾ Ψ
    use : uS Ψ SCx.⊑ᵘ Φ

record BDom {n} (Γn : List Binding) (Γd : LC.Ctx n) (e : RawExpr) (A : LT.Type) (π : LG.Purity) (B′ : ST.Ty m)
            (Φ : SCx.Usage n) : Set where
  constructor bdom
  field
    {B} : LT.Type
    rb  : TyR Δ B B′
    {Ψ} : LC.Usage n
    der : C n Γn Γd ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ
    use : uS Ψ SCx.⊑ᵘ Φ

------------------------------------------------------------------------
-- Locals, read back
------------------------------------------------------------------------

private
  at-name : ∀ {n} b {Γn} {Γd : LC.Ctx n} {B q} (d : Dec (name b ≡ name b))
          → lookupLocal-at (name b) b Γn Γd {B = B} {q = q} d ≡ just (LC.lookup (Γd LC., B ^ q) zero , LC.singleUse zero LG.One , svar zero)
  at-name b (yes _) = refl
  at-name b (no ¬e) = ⊥-elim (¬e refl)

  at-other : ∀ {n x} b {Γn} {Γd : LC.Ctx n} {B q} {i} → ¬ (x ≡ name b) → (d : Dec (x ≡ name b))
           → lookupLocal-go x Γn Γd ≡ just (LC.lookup Γd i , LC.singleUse i LG.One , svar i)
           → lookupLocal-at x b Γn Γd {B = B} {q = q} d ≡ just (LC.lookup (Γd LC., B ^ q) (suc i) , LC.singleUse (suc i) LG.One , svar (suc i))
  at-other b ne (yes e) _  = ⊥-elim (ne e)
  at-other b ne (no _)  eq = cong LTS.lookupLocal-next eq

  ctx-lookup : ∀ {n} {L : SU.Locals m n} {x A i} → SU._∋_⦂_at_ L x A i → SCx.lookup (ctxL L) i ≡ A
  ctx-lookup SU.here        = refl
  ctx-lookup (SU.there _ m) = ctx-lookup m

-- A Spec variable is the compiler's local, at a related type.
lk⁻ : ∀ {n x} {Γn} {Γd : LC.Ctx n} {L A′ i} → LR Γn Γd L → SU._∋_⦂_at_ L x A′ i
    → (lookupLocal-go x Γn Γd ≡ just (LC.lookup Γd i , LC.singleUse i LG.One , svar i)) × TyR Δ (LC.lookup Γd i) A′
lk⁻ (lr-▸ {b = b} lr ra) SU.here = at-name b (name b Data.String.≟ name b) , ra
lk⁻ {x = x} (lr-▸ {b = b} lr ra) (SU.there ne m) =
  let (e , r) = lk⁻ lr m in at-other b ne (x Data.String.≟ name b) e , r

-- A name bound by no enclosing binder is not found.
lk-none : ∀ {n x} Γn {Γd : LC.Ctx n} → ¬ (x ∈ names Γn) → lookupLocal-go x Γn Γd ≡ nothing
lk-none-at : ∀ {n x} b Γn {Γd : LC.Ctx n} {B q} → ¬ (x ∈ names (b ∷ Γn)) → (d : Dec (x ≡ name b))
           → lookupLocal-at x b Γn Γd {B = B} {q = q} d ≡ nothing
lk-none []       {LC.∅}         _ = refl
lk-none []       {Γd LC., _ ^ _} _ = refl
lk-none (b ∷ Γn) {LC.∅}         _ = refl
lk-none {x = x} (b ∷ Γn) {Γd LC., B ^ q} ∉ = lk-none-at b Γn ∉ (x Data.String.≟ name b)
lk-none-at b Γn ∉ (yes e) = ⊥-elim (∉ (Data.List.Relation.Unary.Any.here e))
lk-none-at b Γn {Γd} ∉ (no _) = cong LTS.lookupLocal-next (lk-none Γn (λ m → ∉ (Data.List.Relation.Unary.Any.there m)))

------------------------------------------------------------------------
-- Heads, read back
------------------------------------------------------------------------

private
  gen∈ : (k : Fin (Data.List.length SU.specialGenerators)) → Data.List.lookup SU.specialGenerators k ∈ SU.specialGenerators
  gen∈ k = Data.List.Membership.Propositional.Properties.∈-lookup {xs = SU.specialGenerators} k

special⁻ : ∀ {bound f f′} (v : AppHeadView f) → RX ps bound f f′ → ¬ SU.SpecialHead f′ → viewToPba v ≡ nothing
special⁻ LTS.ahv-id       (x-res _) ns = ⊥-elim (ns (SU.sh-gen (Data.List.Relation.Unary.Any.here refl)))
special⁻ LTS.ahv-fst      (x-res _) ns = ⊥-elim (ns (SU.sh-gen (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl))))
special⁻ LTS.ahv-snd      (x-res _) ns = ⊥-elim (ns (SU.sh-gen (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl)))))
special⁻ LTS.ahv-terminal (x-res _) ns = ⊥-elim (ns (SU.sh-gen (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.there (Data.List.Relation.Unary.Any.here refl))))))
special⁻ LTS.ahv-inl      (x-res _) ns = ⊥-elim (ns (SU.sh-gen (gen∈ (Data.Fin.# 4))))
special⁻ LTS.ahv-inr      (x-res _) ns = ⊥-elim (ns (SU.sh-gen (gen∈ (Data.Fin.# 5))))
special⁻ LTS.ahv-initial  (x-res _) ns = ⊥-elim (ns (SU.sh-gen (gen∈ (Data.Fin.# 6))))
special⁻ LTS.ahv-curry    (x-res _) ns = ⊥-elim (ns (SU.sh-gen (gen∈ (Data.Fin.# 7))))
special⁻ LTS.ahv-apply    (x-res _) ns = ⊥-elim (ns (SU.sh-gen (gen∈ (Data.Fin.# 8))))
special⁻ LTS.ahv-In       (x-res _) ns = ⊥-elim (ns (SU.sh-gen (gen∈ (Data.Fin.# 9))))
special⁻ LTS.ahv-cata     (x-res _) ns = ⊥-elim (ns (SU.sh-gen (gen∈ (Data.Fin.# 10))))
special⁻ LTS.ahv-ana      (x-res _) ns = ⊥-elim (ns (SU.sh-gen (gen∈ (Data.Fin.# 11))))
special⁻ LTS.ahv-Out      (x-res _) ns = ⊥-elim (ns (SU.sh-gen (gen∈ (Data.Fin.# 12))))
special⁻ LTS.ahv-pair-applied    (x-app (x-res _) _) ns = ⊥-elim (ns SU.sh-pair)
special⁻ LTS.ahv-compose-applied (x-app (x-res _) _) ns = ⊥-elim (ns SU.sh-compose)
special⁻ LTS.ahv-case-applied    (x-app (x-res _) _) ns = ⊥-elim (ns SU.sh-case)
special⁻ LTS.ahv-other x ns = refl

------------------------------------------------------------------------
-- Usage
------------------------------------------------------------------------

private
  ≤q-+ˡ : ∀ p q → p SG.≤q p SG.+q q
  ≤q-+ˡ SG.Zero q      = SG.0≤q
  ≤q-+ˡ SG.One  SG.Zero = SG.1≤1
  ≤q-+ˡ SG.One  SG.One  = SG.1≤ω
  ≤q-+ˡ SG.One  SG.Many = SG.1≤ω
  ≤q-+ˡ SG.Many q      = SG.ω≤ω

  ≤q-refl : ∀ q → q SG.≤q q
  ≤q-refl SG.Zero = SG.0≤q
  ≤q-refl SG.One  = SG.1≤1
  ≤q-refl SG.Many = SG.ω≤ω

  ≤q-+ʳ : ∀ p q → q SG.≤q p SG.+q q
  ≤q-+ʳ SG.Zero q       = ≤q-refl q
  ≤q-+ʳ SG.One  SG.Zero = SG.0≤q
  ≤q-+ʳ SG.One  SG.One  = SG.1≤ω
  ≤q-+ʳ SG.One  SG.Many = SG.ω≤ω
  ≤q-+ʳ SG.Many SG.Zero = SG.0≤q
  ≤q-+ʳ SG.Many SG.One  = SG.1≤ω
  ≤q-+ʳ SG.Many SG.Many = SG.ω≤ω

  z⊑ : ∀ {n} (Φ : SCx.Usage n) → SCx.zeroUsage SCx.⊑ᵘ Φ
  z⊑ SCx.[]      = SCx.[]
  z⊑ (q SCx.∷ Φ) = SG.0≤q SCx.⊑∷ z⊑ Φ

  ⊑-+ˡ : ∀ {n} (Ψ Φ : SCx.Usage n) → Ψ SCx.⊑ᵘ Ψ SCx.+ᵘ Φ
  ⊑-+ˡ SCx.[]      SCx.[]      = SCx.[]
  ⊑-+ˡ (p SCx.∷ Ψ) (q SCx.∷ Φ) = ≤q-+ˡ p q SCx.⊑∷ ⊑-+ˡ Ψ Φ

  ⊑-+ʳ : ∀ {n} (Ψ Φ : SCx.Usage n) → Φ SCx.⊑ᵘ Ψ SCx.+ᵘ Φ
  ⊑-+ʳ SCx.[]      SCx.[]      = SCx.[]
  ⊑-+ʳ (p SCx.∷ Ψ) (q SCx.∷ Φ) = ≤q-+ʳ p q SCx.⊑∷ ⊑-+ʳ Ψ Φ

  ⊑-head : ∀ {n p q} {Ψ Φ : SCx.Usage n} → (p SCx.∷ Ψ) SCx.⊑ᵘ (q SCx.∷ Φ) → p SG.≤q q
  ⊑-head (h SCx.⊑∷ _) = h

  ⊑-tail : ∀ {n p q} {Ψ Φ : SCx.Usage n} → (p SCx.∷ Ψ) SCx.⊑ᵘ (q SCx.∷ Φ) → Ψ SCx.⊑ᵘ Φ
  ⊑-tail (_ SCx.⊑∷ t) = t

  zero-use : ∀ {n} {Φ : SCx.Usage n} → uS (LC.zeroUsage {n}) SCx.⊑ᵘ Φ
  zero-use {Φ = Φ} = subst (SCx._⊑ᵘ Φ) (sym uS-zero) (z⊑ Φ)

  -- the usage of an application: the function's, and the argument's scaled
  app-use : ∀ {n} (Ψ₁ Ψ₂ : LC.Usage n) q {Φ₁ Φ₂ : SCx.Usage n} {q′}
          → uS Ψ₁ SCx.⊑ᵘ Φ₁ → uS Ψ₂ SCx.⊑ᵘ Φ₂ → qS q SG.≤q q′
          → uS (Ψ₁ LC.+ᵘ q LC.*ᵘ Ψ₂) SCx.⊑ᵘ Φ₁ SCx.+ᵘ q′ SCx.*ᵘ Φ₂
  app-use Ψ₁ Ψ₂ q {Φ₂ = Φ₂} u₁ u₂ le =
    subst (SCx._⊑ᵘ _) (sym (trans (uS-+ Ψ₁ (q LC.*ᵘ Ψ₂)) (cong (uS Ψ₁ SCx.+ᵘ_) (uS-* q Ψ₂))))
          (⊑ᵘ-+ u₁ (⊑ᵘ-trans (⊑ᵘ-*ʳ (qS q) u₂) (⊑ᵘ-*ˡ Φ₂ le)))

  sum-use : ∀ {n} (Ψ₁ Ψ₂ : LC.Usage n) {Φ₁ Φ₂ : SCx.Usage n}
          → uS Ψ₁ SCx.⊑ᵘ Φ₁ → uS Ψ₂ SCx.⊑ᵘ Φ₂ → uS (Ψ₁ LC.+ᵘ Ψ₂) SCx.⊑ᵘ Φ₁ SCx.+ᵘ Φ₂
  sum-use Ψ₁ Ψ₂ u₁ u₂ = subst (SCx._⊑ᵘ _) (sym (uS-+ Ψ₁ Ψ₂)) (⊑ᵘ-+ u₁ u₂)

  -- a join of usages below a bound
  ⊔q-least : ∀ p q {r} → qS p SG.≤q r → qS q SG.≤q r → qS (p LG.⊔q q) SG.≤q r
  ⊔q-least LG.Zero q    _  b = b
  ⊔q-least LG.One LG.Zero a _ = a
  ⊔q-least LG.One LG.One  a _ = a
  ⊔q-least LG.One LG.Many _ b = b
  ⊔q-least LG.Many q    a _ = a

  ⊔-use : ∀ {n} (Ψl Ψr : LC.Usage n) {Φ : SCx.Usage n} → uS Ψl SCx.⊑ᵘ Φ → uS Ψr SCx.⊑ᵘ Φ → uS (Ψl LC.⊔ᵘ Ψr) SCx.⊑ᵘ Φ
  ⊔-use LC.[]      LC.[]      SCx.[]       SCx.[]       = SCx.[]
  ⊔-use (p LC.∷ Ψl) (q LC.∷ Ψr) (a SCx.⊑∷ as) (b SCx.⊑∷ bs) = ⊔q-least p q a b SCx.⊑∷ ⊔-use Ψl Ψr as bs

  -- an arrow's parts, from an equation of arrows
  arr-inj : ∀ {A B A′ B′ : ST.Ty m} {q q′ π π′}
          → (A ST.⇒[ SG.mk-kind q π ] B) ≡ (A′ ST.⇒[ SG.mk-kind q′ π′ ] B′) → (A ≡ A′) × (q ≡ q′) × (π ≡ π′) × (B ≡ B′)
  arr-inj refl = refl , refl , refl , refl

  prod-inj : ∀ {A B A′ B′ : ST.Ty m} → (A ST.* B) ≡ (A′ ST.* B′) → (A ≡ A′) × (B ≡ B′)
  prod-inj refl = refl , refl

  sum-inj : ∀ {A B A′ B′ : ST.Ty m} → (A ST.+ B) ≡ (A′ ST.+ B′) → (A ≡ A′) × (B ≡ B′)
  sum-inj refl = refl , refl

  ν-inj : ∀ {F F′ : ST.Fun m} {f f′} → ST.ν F f ≡ ST.ν F′ f′ → (F ≡ F′) × (f ≡ f′)
  ν-inj refl = refl , refl

  ty-ctx : ∀ {n} {Γ : SCx.Ctx m n} {A A′ Ψ t B π} → A ≡ A′
         → Δ ⊩ (Γ SCx.▸ A) ⊢[ Ψ ] t ∷ B ! π → Δ ⊩ (Γ SCx.▸ A′) ⊢[ Ψ ] t ∷ B ! π
  ty-ctx refl d = d

  ty-at : ∀ {n} {Γ : SCx.Ctx m n} {Ψ t A A′ π} → A ≡ A′ → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A′ ! π
  ty-at refl d = d

  pure-⊑ : ∀ π → LG.pure LS.⊑π π
  pure-⊑ LG.pure = LS.⊑-pure
  pure-⊑ LG.act  = LS.⊑-pa
  pure-⊑ LG.eff  = LS.⊑-pe

  eff-L : ∀ {π} → SG.EffGrade (πS π) → LG.EffGrade π
  eff-L {LG.act} _ = LG.eg-act
  eff-L {LG.eff} _ = LG.eg-eff
  eff-L {LG.pure} ()

------------------------------------------------------------------------
-- The binary operators
------------------------------------------------------------------------

private
  ia-ok : ∀ {op p} → SU.IntArith (opS op) p
        → (Once.Lang.Syntax.isArithmeticOp op ≡ true) × (SC.primDom {m} p ≡ ST.Int ST.* ST.Int) × (SC.primCod {m} p ≡ ST.Int)
  ia-ok {OpAdd} SU.ia-add = refl , refl , refl
  ia-ok {OpSub} SU.ia-sub = refl , refl , refl
  ia-ok {OpMul} SU.ia-mul = refl , refl , refl
  ia-ok {OpDiv} SU.ia-div = refl , refl , refl
  ia-ok {OpMod} SU.ia-mod = refl , refl , refl
  ia-ok {OpLt} ()
  ia-ok {OpLe} ()
  ia-ok {OpGt} ()
  ia-ok {OpGe} ()
  ia-ok {OpEq} ()
  ia-ok {OpNe} ()

  fa-ok : ∀ {op p} → SU.FloatArith (opS op) p
        → (Once.Lang.Syntax.isFloatArithmeticOp op ≡ true) × (SC.primDom {m} p ≡ ST.Float ST.* ST.Float) × (SC.primCod {m} p ≡ ST.Float)
  fa-ok {OpAdd} SU.fa-add = refl , refl , refl
  fa-ok {OpSub} SU.fa-sub = refl , refl , refl
  fa-ok {OpMul} SU.fa-mul = refl , refl , refl
  fa-ok {OpDiv} SU.fa-div = refl , refl , refl
  fa-ok {OpMod} ()
  fa-ok {OpLt} ()
  fa-ok {OpLe} ()
  fa-ok {OpGt} ()
  fa-ok {OpGe} ()
  fa-ok {OpEq} ()
  fa-ok {OpNe} ()

  cmp-ok : ∀ {op p} → SU.Compare (opS op) p
         → (Once.Lang.Syntax.isComparisonOp op ≡ true) × (SC.primDom {m} p ≡ ST.Int ST.* ST.Int) × (SC.primCod {m} p ≡ ST.Unit ST.+ ST.Unit)
  cmp-ok {OpLt} SU.cmp-lt = refl , refl , refl
  cmp-ok {OpLe} SU.cmp-le = refl , refl , refl
  cmp-ok {OpGt} SU.cmp-gt = refl , refl , refl
  cmp-ok {OpGe} SU.cmp-ge = refl , refl , refl
  cmp-ok {OpEq} SU.cmp-eq = refl , refl , refl
  cmp-ok {OpNe} SU.cmp-ne = refl , refl , refl
  cmp-ok {OpAdd} ()
  cmp-ok {OpSub} ()
  cmp-ok {OpMul} ()
  cmp-ok {OpDiv} ()
  cmp-ok {OpMod} ()

  int-is : ∀ {A} → TyR Δ A ST.Int → A ≡ LT.Int
  int-is r-int = refl

  float-is : ∀ {A} → TyR Δ A ST.Float → A ≡ LT.Float
  float-is r-float = refl

------------------------------------------------------------------------
-- The rules' steps, given their parts read back
------------------------------------------------------------------------

private
  module _ {n} {Γn : List Binding} {Γd : LC.Ctx n} where

    pair-syn : ∀ {ea eb A′ B′ Φ₁ Φ₂ Φ} → Φ₁ SCx.+ᵘ Φ₂ SCx.⊑ᵘ Φ
             → BSyn Γn Γd ea A′ Φ₁ → BSyn Γn Γd eb B′ Φ₂ → BSyn Γn Γd (Once.Lang.Syntax.RPair ea eb) (A′ ST.* B′) Φ
    pair-syn u (bsyn ra {Ψa} da ua) (bsyn rb {Ψb} db ub) = bsyn (r-* ra rb) (t-pair da db) (⊑ᵘ-trans (sum-use Ψa Ψb ua ub) u)

    neg-syn : ∀ {e Φ₀ Φ} → Φ₀ SCx.⊑ᵘ Φ → BSyn Γn Γd e ST.Int Φ₀
            → BSyn Γn Γd (Once.Lang.Syntax.RUnaryOp Once.Lang.Syntax.OpNeg e) ST.Int Φ
    neg-syn u (bsyn r-int d u₀) = bsyn r-int (t-neg d) (⊑ᵘ-trans u₀ u)

    -- `x : A` in scope, then the body
    let-syn : ∀ {x e₁ e₂ A′ B′ q Φ₁ Φ₂ Φ} → Φ₂ SCx.+ᵘ q SCx.*ᵘ Φ₁ SCx.⊑ᵘ Φ
            → (s₁ : BSyn Γn Γd e₁ A′ Φ₁)
            → BSyn (LTS.mkBinding x (BSyn.A s₁) LG.Many ∷ Γn) (Γd LC., BSyn.A s₁ ^ LG.Many) e₂ B′ (q SCx.∷ Φ₂)
            → BSyn Γn Γd (Once.Lang.Syntax.RLet x e₁ e₂) B′ Φ
    let-syn u (bsyn r₁ {Ψ₁} d₁ u₁) (bsyn r₂ {q₀ LC.∷ Ψ₂} d₂ u₂) =
      bsyn r₂ (t-let d₁ d₂) (⊑ᵘ-trans (app-use Ψ₂ Ψ₁ q₀ (⊑-tail u₂) u₁ (⊑-head u₂)) u)

    -- the binary operators
    arith-syn : ∀ {op e₁ e₂ Φ₁ Φ₂ Φ} → Once.Lang.Syntax.isArithmeticOp op ≡ true → Φ₁ SCx.+ᵘ Φ₂ SCx.⊑ᵘ Φ
              → BSyn Γn Γd e₁ ST.Int Φ₁ → BSyn Γn Γd e₂ ST.Int Φ₂
              → BSyn Γn Γd (Once.Lang.Syntax.RBinOp op e₁ e₂) ST.Int Φ
    arith-syn ok u (bsyn r-int {Ψ₁} d₁ u₁) (bsyn r-int {Ψ₂} d₂ u₂) =
      bsyn r-int (t-binop-arith ok d₁ d₂) (⊑ᵘ-trans (sum-use Ψ₁ Ψ₂ u₁ u₂) u)

    farith-syn : ∀ {op e₁ e₂ Φ₁ Φ₂ Φ} → Once.Lang.Syntax.isFloatArithmeticOp op ≡ true → Φ₁ SCx.+ᵘ Φ₂ SCx.⊑ᵘ Φ
               → BSyn Γn Γd e₁ ST.Float Φ₁ → BSyn Γn Γd e₂ ST.Float Φ₂
               → BSyn Γn Γd (Once.Lang.Syntax.RBinOp op e₁ e₂) ST.Float Φ
    farith-syn ok u (bsyn r-float {Ψ₁} d₁ u₁) (bsyn r-float {Ψ₂} d₂ u₂) =
      bsyn r-float (t-binop-arith-float ok d₁ d₂) (⊑ᵘ-trans (sum-use Ψ₁ Ψ₂ u₁ u₂) u)

    farith-il-syn : ∀ {op e₁ e₂ Φ₁ Φ₂ Φ} → Once.Lang.Syntax.isFloatArithmeticOp op ≡ true → Φ₁ SCx.+ᵘ Φ₂ SCx.⊑ᵘ Φ
                  → BSyn Γn Γd e₁ ST.Int Φ₁ → BSyn Γn Γd e₂ ST.Float Φ₂
                  → BSyn Γn Γd (Once.Lang.Syntax.RBinOp op e₁ e₂) ST.Float Φ
    farith-il-syn ok u (bsyn r-int {Ψ₁} d₁ u₁) (bsyn r-float {Ψ₂} d₂ u₂) =
      bsyn r-float (t-binop-arith-float-il ok d₁ d₂) (⊑ᵘ-trans (sum-use Ψ₁ Ψ₂ u₁ u₂) u)

    farith-ir-syn : ∀ {op e₁ e₂ Φ₁ Φ₂ Φ} → Once.Lang.Syntax.isFloatArithmeticOp op ≡ true → Φ₁ SCx.+ᵘ Φ₂ SCx.⊑ᵘ Φ
                  → BSyn Γn Γd e₁ ST.Float Φ₁ → BSyn Γn Γd e₂ ST.Int Φ₂
                  → BSyn Γn Γd (Once.Lang.Syntax.RBinOp op e₁ e₂) ST.Float Φ
    farith-ir-syn ok u (bsyn r-float {Ψ₁} d₁ u₁) (bsyn r-int {Ψ₂} d₂ u₂) =
      bsyn r-float (t-binop-arith-float-ir ok d₁ d₂) (⊑ᵘ-trans (sum-use Ψ₁ Ψ₂ u₁ u₂) u)

    cmp-syn : ∀ {op e₁ e₂ Φ₁ Φ₂ Φ} → Once.Lang.Syntax.isComparisonOp op ≡ true → Φ₁ SCx.+ᵘ Φ₂ SCx.⊑ᵘ Φ
            → BSyn Γn Γd e₁ ST.Int Φ₁ → BSyn Γn Γd e₂ ST.Int Φ₂
            → BSyn Γn Γd (Once.Lang.Syntax.RBinOp op e₁ e₂) (ST.Unit ST.+ ST.Unit) Φ
    cmp-syn ok u (bsyn r-int {Ψ₁} d₁ u₁) (bsyn r-int {Ψ₂} d₂ u₂) =
      bsyn (r-+ r-unit r-unit) (t-binop-cmp ok d₁ d₂) (⊑ᵘ-trans (sum-use Ψ₁ Ψ₂ u₁ u₂) u)

    -- a reference to a definition with no type variables
    def-res : ∀ {c Φ} (d : Fin s) (τ : ST.TySub (SC.Schema.arity (S′ SC.!! d)) m) → nm d ≡ c → NotOwnPoly ps c
            → BSyn Γn Γd (Once.Lang.Syntax.RResolved c) (SC.Schema.type (S′ SC.!! d) ST.⟨ τ ⟩) Φ
    def-res d τ e nop = at (h-name d) e nop
      where
        at : ∀ {c Φ} → Σ[ x ∈ String ] nm d ≡ canonical (x ∷ []) → nm d ≡ c → NotOwnPoly ps c
           → BSyn Γn Γd (Once.Lang.Syntax.RResolved c) (SC.Schema.type (S′ SC.!! d) ST.⟨ τ ⟩) Φ
        at (x , ex) refl nop =
          let (lks , T , lki , k , rT) = h-mono ex (nop ex) in bsyn (rT τ) (subst (λ c → C _ Γn Γd ⊢ᵢ Once.Lang.Syntax.RResolved c ∶ T ⨾ _) (sym ex) (t-var-own lks lki k)) zero-use

    def-own : ∀ {x Φ} (d : Fin s) (τ : ST.TySub (SC.Schema.arity (S′ SC.!! d)) m) → ¬ (x ∈ names Γn) → x ∈ ps
            → nm d ≡ canonical (x ∷ []) → SC.Schema.arity (S′ SC.!! d) ≡ 0
            → BSyn Γn Γd (Once.Lang.Syntax.RVar x) (SC.Schema.type (S′ SC.!! d) ST.⟨ τ ⟩) Φ
    def-own d τ ∉ x∈ e ar =
      let pa = h-poly e x∈ ; (g , rT) = Sc.PolyAt.ground pa ar
      in bsyn (rT τ) (t-var-poly-instantiate-infer (lk-none Γn ∉) (Sc.PolyAt.lki pa) (Sc.PolyAt.lp pa) g refl) zero-use

  -- a compiler type related to a `Many` arrow is one
  record ArrMany (A : LT.Type) (X Y : ST.Ty m) (π : SG.Purity) : Set where
    field
      {πc}  : LG.Purity
      πeq   : πS πc ≡ π
      {A₁ A₂} : LT.Type
      eq    : A ≡ A₁ LT.⇒[ LG.mk-kind LG.Many πc ] A₂
      r₁    : TyR Δ A₁ X
      r₂    : TyR Δ A₂ Y

  arr-many : ∀ {A X Y π} → TyR Δ A (X SU.⇒⟨ π ⟩ Y) → ArrMany A X Y π
  arr-many {X = X} {Y} {π} (r-⇒ {A = A₀} {B = B₀} {k = LG.mk-kind q πc} e ra rb) = many q e ra rb
    where
      many : ∀ q′ → kS (LG.mk-kind q′ πc) ≡ SG.mk-kind SG.Many π → TyR Δ A₀ X → TyR Δ B₀ Y
           → ArrMany (A₀ LT.⇒[ LG.mk-kind q′ πc ] B₀) X Y π
      many LG.Many refl ra′ rb′ = record { πeq = refl ; eq = refl ; r₁ = ra′ ; r₂ = rb′ }
      many LG.Zero ()
      many LG.One  ()

  πL : SG.Purity → LG.Purity
  πL SG.pure = LG.pure
  πL SG.act  = LG.act
  πL SG.eff  = LG.eff

  πS-πL : ∀ π → πS (πL π) ≡ π
  πS-πL SG.pure = refl
  πS-πL SG.act  = refl
  πS-πL SG.eff  = refl

------------------------------------------------------------------------
-- The translation
------------------------------------------------------------------------

private
  -- usage of a generator's application `app g t`, `g` closed and `Many`
  gen-use : ∀ {n} (Ψ : LC.Usage n) {Φ Φ₁ Φ₂ : SCx.Usage n} {q} → uS Ψ SCx.⊑ᵘ Φ₂ → q ≡ SG.Many
          → Φ₁ SCx.+ᵘ q SCx.*ᵘ Φ₂ SCx.⊑ᵘ Φ → uS (LC.zeroUsage LC.+ᵘ LG.Many LC.*ᵘ Ψ) SCx.⊑ᵘ Φ
  gen-use Ψ u refl w = ⊑ᵘ-trans (app-use LC.zeroUsage Ψ LG.Many zero-use u SG.ω≤ω) w

  ≤q-≡ : ∀ {p q} → p ≡ q → p SG.≤q q
  ≤q-≡ {p} refl = ≤q-refl p

private
  pure-of : ∀ {π} → πS π ≡ SG.pure → π ≡ LG.pure
  pure-of {LG.pure} _ = refl
  pure-of {LG.act} ()
  pure-of {LG.eff} ()

  φ-pure : ∀ {φ} → φS φ ≡ SG.pureᶠ → φ ≡ LG.pure
  φ-pure {LG.pure} _ = refl
  φ-pure {LG.act} ()

  φ-act : ∀ {φ} → φS φ ≡ SG.actᶠ → φ ≡ LG.act
  φ-act {LG.act} _ = refl
  φ-act {LG.pure} ()

  module _ {n} {Γn : List Binding} {Γd : LC.Ctx n} {e : RawExpr} {Φ Φ₁ Φ₂ : SCx.Usage n} {q : SG.Quantity}
           (w : Φ₁ SCx.+ᵘ q SCx.*ᵘ Φ₂ SCx.⊑ᵘ Φ) (eq : q ≡ SG.Many) where

    G : String → RawExpr
    G g = Once.Lang.Syntax.RApp (Once.Lang.Syntax.RResolved (Once.Spec.Name.gen g)) e

    id-gen : ∀ {T} → BSyn Γn Γd e T Φ₂ → BSyn Γn Γd (G "id") T Φ
    id-gen (bsyn ra {Ψ} der u) = bsyn ra (t-id-app der) (gen-use Ψ u eq w)

    fst-gen : ∀ {A B} → BSyn Γn Γd e (A ST.* B) Φ₂ → BSyn Γn Γd (G "fst") A Φ
    fst-gen (bsyn (r-* ra rb) {Ψ} der u) = bsyn ra (t-fst-app der) (gen-use Ψ u eq w)

    snd-gen : ∀ {A B} → BSyn Γn Γd e (A ST.* B) Φ₂ → BSyn Γn Γd (G "snd") B Φ
    snd-gen (bsyn (r-* ra rb) {Ψ} der u) = bsyn rb (t-snd-app der) (gen-use Ψ u eq w)

    terminal-gen : ∀ {T} → BSyn Γn Γd e T Φ₂ → BSyn Γn Γd (G "terminal") ST.Unit Φ
    terminal-gen (bsyn ra {Ψ} der u) = bsyn r-unit (t-terminal-app der) (gen-use Ψ u eq w)

    -- the pair's two domains are one compiler type
    private
      one-dom : ∀ {Ψ} {A A′ : LT.Type} {X : ST.Ty m} {B : LT.Type} {π} → TyR Δ A X → TyR Δ A′ X
              → C _ Γn Γd ⊢ᵢ e ∶ ((A LT.⇒[ LG.mk-kind LG.Many π ] B) LT.* A′) ⨾ Ψ
              → C _ Γn Γd ⊢ᵢ e ∶ ((A LT.⇒[ LG.mk-kind LG.Many π ] B) LT.* A) ⨾ Ψ
      one-dom ra ra′ d = subst (λ Z → C _ Γn Γd ⊢ᵢ e ∶ (_ LT.* Z) ⨾ _) (TyR-uniqueˡ ra′ ra) d

    apply-gen : ∀ {A B} → BSyn Γn Γd e ((A SU.⇒⟨ SG.pure ⟩ B) ST.* A) Φ₂ → BSyn Γn Γd (G "apply") B Φ
    apply-gen (bsyn (r-* rf ra′) {Ψ} der u) = go (arr-many rf) ra′ der
      where
        go : ∀ {Af Aa A B} → ArrMany Af A B SG.pure → TyR Δ Aa A → C _ Γn Γd ⊢ᵢ e ∶ (Af LT.* Aa) ⨾ Ψ → BSyn Γn Γd (G "apply") B Φ
        go record { πc = πc ; πeq = pe ; eq = refl ; r₁ = r₁ ; r₂ = r₂ } ra″ d =
          bsyn r₂ (t-apply-app-infer (subst (λ π → C _ Γn Γd ⊢ᵢ e ∶ ((_ LT.⇒[ LG.mk-kind LG.Many π ] _) LT.* _) ⨾ Ψ) (pure-of pe)
                                            (one-dom r₁ ra″ d)))
               (gen-use Ψ u eq w)

    applyEff-gen : ∀ {A B π} → SG.EffGrade π → BSyn Γn Γd e ((A SU.⇒⟨ π ⟩ B) ST.* A) Φ₂
                 → BSyn Γn Γd (G "apply") (ST.Unit SU.⇒⟨ π ⟩ B) Φ
    applyEff-gen eg (bsyn (r-* rf ra′) {Ψ} der u) = go eg (arr-many rf) ra′ der
      where
        go : ∀ {Af Aa A B π} → SG.EffGrade π → ArrMany Af A B π → TyR Δ Aa A → C _ Γn Γd ⊢ᵢ e ∶ (Af LT.* Aa) ⨾ Ψ
           → BSyn Γn Γd (G "apply") (ST.Unit SU.⇒⟨ π ⟩ B) Φ
        go eg′ record { πc = πc ; πeq = refl ; eq = refl ; r₁ = r₁ ; r₂ = r₂ } ra″ d =
          bsyn (r-⇒ refl r-unit r₂) (t-apply-eff-app-infer {g = eff-L eg′} (one-dom r₁ ra″ d)) (gen-use Ψ u eq w)

    out-gen : ∀ {F} → ST.WFFun Δ F → BSyn Γn Γd e (ST.ν F SG.pureᶠ) Φ₂ → BSyn Γn Γd (G "Out") (ST.⟦ F ⟧F (ST.ν F SG.pureᶠ)) Φ
    out-gen {F} wf (bsyn (r-ν eφ f) {Ψ} der u) = go (φ-pure eφ) f der
      where
        go : ∀ {φ Fc} → φ ≡ LG.pure → FunR Δ Fc F → C _ Γn Γd ⊢ᵢ e ∶ LT.ν-type Fc φ ⨾ Ψ
           → BSyn Γn Γd (G "Out") (ST.⟦ F ⟧F (ST.ν F SG.pureᶠ)) Φ
        go refl f′ d = bsyn (⟦⟧-R f′ (r-ν refl f′)) (t-Out-app-infer (wf-L wf f′) refl d) (gen-use Ψ u eq w)

    outAct-gen : ∀ {F} → ST.WFFun Δ F → BSyn Γn Γd e (ST.ν F SG.actᶠ) Φ₂
               → BSyn Γn Γd (G "Out") (ST.Unit SU.⇒⟨ SG.act ⟩ ST.⟦ F ⟧F (ST.ν F SG.actᶠ)) Φ
    outAct-gen {F} wf (bsyn (r-ν eφ f) {Ψ} der u) = go (φ-act eφ) f der
      where
        go : ∀ {φ Fc} → φ ≡ LG.act → FunR Δ Fc F → C _ Γn Γd ⊢ᵢ e ∶ LT.ν-type Fc φ ⨾ Ψ
           → BSyn Γn Γd (G "Out") (ST.Unit SU.⇒⟨ SG.act ⟩ ST.⟦ F ⟧F (ST.ν F SG.actᶠ)) Φ
        go refl f′ d = bsyn (r-⇒ refl r-unit (⟦⟧-R f′ (r-ν refl f′))) (t-Out-eff-app-infer (wf-L wf f′) refl d) (gen-use Ψ u eq w)

private
  on-arr : ∀ {n} {Γn : List Binding} {Γd : LC.Ctx n} {e A X Y π Φ} {P : Set} → TyR Δ A (X SU.⇒⟨ π ⟩ Y)
         → (∀ {A₁ A₂ πc} → πS πc ≡ π → TyR Δ A₁ X → TyR Δ A₂ Y → P × BChk Γn Γd e (A₁ LT.⇒[ LG.mk-kind LG.Many πc ] A₂) Φ)
         → P × BChk Γn Γd e A Φ
  on-arr {Γn = Γn} {Γd} {e} {Φ = Φ} {P} rA k = go (arr-many rA) k
    where
      go : ∀ {A X Y π} → ArrMany A X Y π
         → (∀ {A₁ A₂ πc} → πS πc ≡ π → TyR Δ A₁ X → TyR Δ A₂ Y → P × BChk Γn Γd e (A₁ LT.⇒[ LG.mk-kind LG.Many πc ] A₂) Φ)
         → P × BChk Γn Γd e A Φ
      go record { πeq = pe ; eq = refl ; r₁ = r₁ ; r₂ = r₂ } k′ = k′ pe r₁ r₂

  eff-of : ∀ {π} → πS π ≡ SG.eff → π ≡ LG.eff
  eff-of {LG.eff} _ = refl
  eff-of {LG.pure} ()
  eff-of {LG.act} ()

  same-dom : ∀ {n} {Γn : List Binding} {Γd : LC.Ctx n} {e A₁ A₂ X Ψ k} → TyR Δ A₁ X → TyR Δ A₂ X
           → C n Γn Γd ⊢ᶜ e ∶ (A₁ LT.⇒[ k ] A₁) ⨾ Ψ → C n Γn Γd ⊢ᶜ e ∶ (A₁ LT.⇒[ k ] A₂) ⨾ Ψ
  same-dom r₁ r₂ d = subst (λ Z → C _ _ _ ⊢ᶜ _ ∶ (_ LT.⇒[ _ ] Z) ⨾ _) (TyR-uniqueˡ r₁ r₂) d

private
  ≡-chk : ∀ {n} {Γn : List Binding} {Γd : LC.Ctx n} {e A B Φ} → A ≡ B → BChk Γn Γd e A Φ → BChk Γn Γd e B Φ
  ≡-chk refl b = b

  kM : ∀ {πc π} → πS πc ≡ π → kS (LG.mk-kind LG.Many πc) ≡ SG.mk-kind SG.Many π
  kM = cong (SG.mk-kind SG.Many)

  -- an arrow's codomain and grade, from two equations of one type
  cod-eq : ∀ {Z A B A′ B′ : ST.Ty m} {q q′ π π′}
         → Z ≡ A ST.⇒[ SG.mk-kind q π ] B → Z ≡ A′ ST.⇒[ SG.mk-kind q′ π′ ] B′ → B ≡ B′
  cod-eq refl e = proj₂ (proj₂ (proj₂ (arr-inj e)))

  grd-eq : ∀ {A B A′ B′ : ST.Ty m} {q q′ π π′}
         → A ST.⇒[ SG.mk-kind q π ] B ≡ A′ ST.⇒[ SG.mk-kind q′ π′ ] B′ → π ≡ π′
  grd-eq e = proj₁ (proj₂ (proj₂ (arr-inj e)))

  cod-cong : ∀ {A B B′ : ST.Ty m} {k} → B ≡ B′ → (A ST.⇒[ k ] B) ≡ (A ST.⇒[ k ] B′)
  cod-cong refl = refl

  fin-inj : ∀ {f g} → SG.fin f ≡ SG.fin g → f ≡ g
  fin-inj refl = refl

  -- a compiler type related to an arrow is one
  split-k : ∀ {Ac A′ B′ k′} → TyR Δ Ac (A′ ST.⇒[ k′ ] B′)
          → Σ[ k ∈ LG.ArrowKind ] Σ[ A₁ ∈ LT.Type ] Σ[ A₂ ∈ LT.Type ]
              (kS k ≡ k′) × (Ac ≡ A₁ LT.⇒[ k ] A₂) × TyR Δ A₁ A′ × TyR Δ A₂ B′
  split-k (r-⇒ e ra rb) = _ , _ , _ , e , refl , ra , rb

  split-arr : ∀ {Ac X Y π} → TyR Δ Ac (X SU.⇒⟨ π ⟩ Y)
            → Σ[ πc ∈ LG.Purity ] Σ[ A₁ ∈ LT.Type ] Σ[ A₂ ∈ LT.Type ]
                (πS πc ≡ π) × (Ac ≡ A₁ LT.⇒[ LG.mk-kind LG.Many πc ] A₂) × TyR Δ A₁ X × TyR Δ A₂ Y
  split-arr rA = go (arr-many rA)
    where
      go : ∀ {Ac X Y π} → ArrMany Ac X Y π
         → Σ[ πc ∈ LG.Purity ] Σ[ A₁ ∈ LT.Type ] Σ[ A₂ ∈ LT.Type ]
             (πS πc ≡ π) × (Ac ≡ A₁ LT.⇒[ LG.mk-kind LG.Many πc ] A₂) × TyR Δ A₁ X × TyR Δ A₂ Y
      go record { πeq = pe ; eq = refl ; r₁ = r₁ ; r₂ = r₂ } = _ , _ , _ , pe , refl , r₁ , r₂

  many-use : ∀ {n} (Ψ : LC.Usage n) {Φ₁ Φ : SCx.Usage n} → uS Ψ SCx.⊑ᵘ Φ₁ → SG.Many SCx.*ᵘ Φ₁ SCx.⊑ᵘ Φ
           → uS (LG.Many LC.*ᵘ Ψ) SCx.⊑ᵘ Φ
  many-use Ψ u w = subst (SCx._⊑ᵘ _) (sym (uS-* LG.Many Ψ)) (⊑ᵘ-trans (⊑ᵘ-*ʳ SG.Many u) w)

  one-use : ∀ {n} (Ψ₁ Ψ₂ : LC.Usage n) {Φ₁ Φ₂ Φ : SCx.Usage n} → uS Ψ₁ SCx.⊑ᵘ Φ₁ → uS Ψ₂ SCx.⊑ᵘ Φ₂
          → Φ₁ SCx.+ᵘ SG.One SCx.*ᵘ Φ₂ SCx.⊑ᵘ Φ → uS (Ψ₁ LC.+ᵘ Ψ₂) SCx.⊑ᵘ Φ
  one-use Ψ₁ Ψ₂ {Φ₂ = Φ₂} u₁ u₂ w = ⊑ᵘ-trans (sum-use Ψ₁ Ψ₂ u₁ u₂) (subst (λ Z → _ SCx.+ᵘ Z SCx.⊑ᵘ _) (One*ᵘ Φ₂) w)

  one-use′ : ∀ {n} (Ψ : LC.Usage n) {Φ₁ Φ : SCx.Usage n} → uS Ψ SCx.⊑ᵘ Φ₁ → SG.One SCx.*ᵘ Φ₁ SCx.⊑ᵘ Φ → uS Ψ SCx.⊑ᵘ Φ
  one-use′ Ψ {Φ₁} u w = ⊑ᵘ-trans u (subst (SCx._⊑ᵘ _) (One*ᵘ Φ₁) w)

  poly-res : ∀ {c} (d : Fin s) → nm d ≡ c → 0 < SC.Schema.arity (S′ SC.!! d) → NotOwnPoly ps c → ⊥
  poly-res d e pos nop = let (x , ex) = h-name d in nop (trans (sym e) ex) (h-ps ex pos)

  module _ {n} {Γn : List Binding} {Γd : LC.Ctx n} where

    syn-arr : ∀ {e Af X Y π Ψ} → TyR Δ Af (X SU.⇒⟨ π ⟩ Y) → C n Γn Γd ⊢ᵢ e ∶ Af ⨾ Ψ
            → Σ[ πc ∈ LG.Purity ] Σ[ A₁ ∈ LT.Type ] Σ[ A₂ ∈ LT.Type ]
                (πS πc ≡ π) × TyR Δ A₁ X × TyR Δ A₂ Y × (C n Γn Γd ⊢ᵢ e ∶ (A₁ LT.⇒[ LG.mk-kind LG.Many πc ] A₂) ⨾ Ψ)
    syn-arr rf d = go (split-arr rf) d
      where
        go : ∀ {e Af X Y π Ψ} → Σ[ πc ∈ LG.Purity ] Σ[ A₁ ∈ LT.Type ] Σ[ A₂ ∈ LT.Type ]
                (πS πc ≡ π) × (Af ≡ A₁ LT.⇒[ LG.mk-kind LG.Many πc ] A₂) × TyR Δ A₁ X × TyR Δ A₂ Y
           → C n Γn Γd ⊢ᵢ e ∶ Af ⨾ Ψ
           → Σ[ πc ∈ LG.Purity ] Σ[ A₁ ∈ LT.Type ] Σ[ A₂ ∈ LT.Type ]
                (πS πc ≡ π) × TyR Δ A₁ X × TyR Δ A₂ Y × (C n Γn Γd ⊢ᵢ e ∶ (A₁ LT.⇒[ LG.mk-kind LG.Many πc ] A₂) ⨾ Ψ)
        go (_ , _ , _ , pe , refl , r₁ , r₂) d′ = _ , _ , _ , pe , r₁ , r₂ , d′

    -- `x : A` in scope, a body checked
    lam-chk : ∀ {x body A₁ A₂ q π q′} {Ψ Φ : SCx.Usage n} (k : LG.ArrowKind) → kS k ≡ SG.mk-kind q π
            → ∀ {Ψ₀ : LC.Usage (suc n)}
            → C (suc n) (LTS.mkBinding x A₁ LG.Many ∷ Γn) (Γd LC., A₁ ^ LG.Many) ⊢ᶜ body ∶ A₂ ⨾ Ψ₀
            → uS Ψ₀ SCx.⊑ᵘ (q′ SCx.∷ Ψ) → q′ SG.≤q q → Ψ SCx.⊑ᵘ Φ
            → BChk Γn Γd (Once.Lang.Syntax.RLam x body) (A₁ LT.⇒[ k ] A₂) Φ
    lam-chk k ek {q₀ LC.∷ Ψ₀} der u le w =
      bchk (t-lam {u = pure-⊑ _}
                  (≤q-L q₀ (LG.ArrowKind.quantity k)
                        (subst (λ z → qS q₀ SG.≤q z) (sym (cong SG.ArrowKind.quantity ek)) (≤q-trans (⊑-head u) le)))
                  der)
           (⊑ᵘ-trans (⊑-tail u) w)

    -- `x : A` in scope, a body synthesized
    lam-dom : ∀ {x body A₁ B′ π} {q′ : SG.Quantity} {Ψ Φ : SCx.Usage n}
            → BSyn (LTS.mkBinding x A₁ LG.Many ∷ Γn) (Γd LC., A₁ ^ LG.Many) body B′ (q′ SCx.∷ Ψ) → Ψ SCx.⊑ᵘ Φ
            → BDom Γn Γd (Once.Lang.Syntax.RLam x body) A₁ π B′ Φ
    lam-dom (bsyn rb {q₀ LC.∷ Ψ₀} der u) w = bdom rb (d-lam {u = pure-⊑ _} der) (⊑ᵘ-trans (⊑-tail u) w)

    -- `apply p` checked: `p`'s pair, its domain one type
    apply-chk : ∀ {e As Bs Bc Φ₁ Φ₂ Φ q} → BSyn Γn Γd e ((As SU.⇒⟨ SG.pure ⟩ Bs) ST.* As) Φ₂ → TyR Δ Bc Bs
              → q ≡ SG.Many → Φ₁ SCx.+ᵘ q SCx.*ᵘ Φ₂ SCx.⊑ᵘ Φ
              → BChk Γn Γd (Once.Lang.Syntax.RApp (Once.Lang.Syntax.RResolved (Once.Spec.Name.gen "apply")) e) Bc Φ
    apply-chk {e = e} {As} {Bs} (bsyn (r-* rf ra′) {Ψ} der u) rB eq w = go (split-arr rf) ra′ der
      where
        go : ∀ {Af Aa} → Σ[ πc ∈ LG.Purity ] Σ[ A₁ ∈ LT.Type ] Σ[ A₂ ∈ LT.Type ]
                (πS πc ≡ SG.pure) × (Af ≡ A₁ LT.⇒[ LG.mk-kind LG.Many πc ] A₂) × TyR Δ A₁ As × TyR Δ A₂ Bs
           → TyR Δ Aa As → C n Γn Γd ⊢ᵢ e ∶ (Af LT.* Aa) ⨾ Ψ → BChk Γn Γd _ _ _
        go (πc , A₁ , A₂ , pe , refl , r₁ , r₂) ra″ d =
          ≡-chk (TyR-uniqueˡ r₂ rB)
            (bchk (t-apply-check (subst (λ π → C n Γn Γd ⊢ᵢ e ∶ ((A₁ LT.⇒[ LG.mk-kind LG.Many π ] A₂) LT.* A₁) ⨾ Ψ) (pure-of pe)
                                        (subst (λ Z → C n Γn Γd ⊢ᵢ e ∶ (_ LT.* Z) ⨾ Ψ) (TyR-uniqueˡ ra″ r₁) d)))
                  (gen-use Ψ u eq w))

mutual
  bwdᵢ : ∀ {n Γn} {Γd : LC.Ctx n} {L : SU.Locals m n} {e e′ A′ t′}
       → SU._⊢_⇒_↝_ Δ L e′ A′ t′ → RX ps (names Γn) e e′ → LR Γn Γd L
       → ∀ {Φ X π} → Δ ⊩ ctxL L ⊢[ Φ ] t′ ∷ X ! π → (X ≡ A′) × BSyn Γn Γd e A′ Φ
  bwdᶜ : ∀ {n Γn} {Γd : LC.Ctx n} {L : SU.Locals m n} {e e′ A A′ t′}
       → SU._⊢_⇐_↝_ Δ L e′ A′ t′ → RX ps (names Γn) e e′ → LR Γn Γd L → TyR Δ A A′
       → ∀ {Φ X π} → Δ ⊩ ctxL L ⊢[ Φ ] t′ ∷ X ! π → (X ≡ A′) × BChk Γn Γd e A Φ
  bwdᵈ : ∀ {n Γn} {Γd : LC.Ctx n} {L : SU.Locals m n} {e e′ A A′ π′ B′ t′}
       → SU._⊢_⇐_⇒[_]↦_↝_ Δ L e′ A′ π′ B′ t′ → RX ps (names Γn) e e′ → LR Γn Γd L → TyR Δ A A′
       → ∀ π → πS π ≡ π′
       → ∀ {Φ X π₀} → Δ ⊩ ctxL L ⊢[ Φ ] t′ ∷ X ! π₀ → (X ≡ A′ SU.⇒⟨ π′ ⟩ B′) × BDom Γn Γd e A π B′ Φ

  ----------------------------------------------------------------------
  -- Synthesis
  ----------------------------------------------------------------------

  bwdᵢ (SU.s-int i) x-int lr T = inv-lit-int T , bsyn r-int (t-int i) zero-use
  bwdᵢ (SU.s-float i f l) (x-float {p = p}) lr T = inv-lit-float T , bsyn r-float (t-float i f l p) zero-use
  bwdᵢ SU.s-unit x-unit lr T = inv-unit T , bsyn r-unit t-unit zero-use
  bwdᵢ SU.s-unit-g (x-res _) lr T = inv-unit T , bsyn r-unit t-unit-var zero-use
  bwdᵢ (SU.s-var mem) (x-local _) lr T =
    trans (proj₁ (inv-var T)) (ctx-lookup mem)
    , bsyn (proj₂ (lk⁻ lr mem)) (t-var-local (proj₁ (lk⁻ lr mem))) (subst (SCx._⊑ᵘ _) (sym (uS-single _ LG.One)) (proj₂ (inv-var T)))
  bwdᵢ (SU.s-sigop ng mem) (x-res _) lr T =
    let (T₀ , lk , k , r) = h-sig ng mem in inv-sigop T , bsyn r (t-var-resolved ng lk k) zero-use
  bwdᵢ (SU.s-sigop ng mem) (x-own _ x∈) lr T = ⊥-elim (h-own-sig x∈ mem)
  bwdᵢ (SU.s-def d e τ ar) (x-res nop) lr T = inv-ref T , def-res d τ e nop
  bwdᵢ (SU.s-def d e τ ar) (x-own ∉ x∈) lr T = inv-ref T , def-own d τ ∉ x∈ e ar
  bwdᵢ (SU.s-annot d) (x-annot rf x) lr T =
    let (eq , bchk der u) = bwdᶜ d x lr (annot-R _ rf) T in eq , bsyn (annot-R _ rf) (t-annot rf der) u
  bwdᵢ (SU.s-pair da db) (x-pair xa xb) lr T =
    let r = inv-pair T ; (ea , sa) = bwdᵢ da xa lr (IPair.da r) ; (eb , sb) = bwdᵢ db xb lr (IPair.db r)
    in trans (IPair.ty r) (cong₂ ST._*_ ea eb) , pair-syn (IPair.use r) sa sb
  bwdᵢ (SU.s-neg d) (x-neg x) lr T =
    let r = inv-prim T ; (_ , sd) = bwdᵢ d x lr (IPrim.dt r) in IPrim.ty r , neg-syn (IPrim.use r) sd
  bwdᵢ (SU.s-neg-float i f l) (x-neg (x-float {p = p})) lr T = inv-lit-float T , bsyn r-float (t-neg-float i f l p) zero-use
  bwdᵢ (SU.s-let q d₁ d₂) (x-let x₁ x₂) lr T =
    let r = inv-let T ; (e₁ , s₁) = bwdᵢ d₁ x₁ lr (ILet.de r)
        (e₂ , s₂) = bwdᵢ d₂ x₂ (lr-▸ lr (BSyn.ra s₁)) (ty-ctx e₁ (ILet.db r))
    in e₂ , let-syn (ILet.use r) s₁ s₂
  bwdᵢ {Γn = Γn} {Γd} {L} (SU.s-case {Cl = Cl₀} {Cr = Cr₀} ql qr ds dl dr J) (x-destruct {xl = xl} {xr = xr} xs xl′ xr′) lr T =
    let r = inv-case T ; (es , ss) = bwdᵢ ds xs lr (ICase.ds r) in case-go r es ss
    where
      case-go : ∀ {Φ X} (r : ICase {Γ = ctxL L} Φ ql qr _ _ _ X) → ICase.A r ST.+ ICase.B r ≡ _ → BSyn Γn Γd _ _ (ICase.Φs r)
              → (X ≡ _) × BSyn Γn Γd _ _ Φ
      case-go r es (bsyn (r-+ ra rb) {Ψs} dS uS₀) =
        let (eA , eB) = sum-inj es
            cl = inv-coerce (ICase.dl r) ; cr = inv-coerce (ICase.dr r)
        in ICoerce.ty cl
           , branches (proj₂ (bwdᵢ dl xl′ (lr-▸ lr ra) (ty-ctx eA (ICoerce.dt cl))))
                      (proj₂ (bwdᵢ dr xr′ (lr-▸ lr rb) (ty-ctx eB (ICoerce.dt cr))))
                      (ICoerce.use cl) (ICoerce.use cr)
        where
          branches : ∀ {Φl Φr} → BSyn _ _ _ Cl₀ Φl → BSyn _ _ _ Cr₀ Φr
                   → Φl SCx.⊑ᵘ (ql SCx.∷ ICase.Ψ r) → Φr SCx.⊑ᵘ (qr SCx.∷ ICase.Ψ r) → BSyn Γn Γd _ _ _
          branches (bsyn rl {qL₀ LC.∷ Ψl} dL uL) (bsyn rr {qR₀ LC.∷ Ψr} dR uR) wl wr =
            let (C₀ , rc , J₀) = join-L J rl rr
            in bsyn rc (t-case dS dL dR J₀)
                 (⊑ᵘ-trans (sum-use Ψs (Ψl LC.⊔ᵘ Ψr) uS₀ (⊔-use Ψl Ψr (⊑-tail (⊑ᵘ-trans uL wl)) (⊑-tail (⊑ᵘ-trans uR wr))))
                           (ICase.use r))
  bwdᵢ (SU.s-arith ia d₁ d₂) (x-binop x₁ x₂) lr T =
    let (ok , dom , cod) = ia-ok ia ; r = inv-prim T ; p = inv-pair (ty-at dom (IPrim.dt r))
        (e₁ , e₂) = prod-inj (sym (IPair.ty p))
        (_ , s₁) = bwdᵢ d₁ x₁ lr (ty-at e₁ (IPair.da p)) ; (_ , s₂) = bwdᵢ d₂ x₂ lr (ty-at e₂ (IPair.db p))
    in trans (IPrim.ty r) cod , arith-syn ok (⊑ᵘ-trans (IPair.use p) (IPrim.use r)) s₁ s₂
  bwdᵢ (SU.s-arith-float fa d₁ d₂) (x-binop x₁ x₂) lr T =
    let (ok , dom , cod) = fa-ok fa ; r = inv-prim T ; p = inv-pair (ty-at dom (IPrim.dt r))
        (e₁ , e₂) = prod-inj (sym (IPair.ty p))
        (_ , s₁) = bwdᵢ d₁ x₁ lr (ty-at e₁ (IPair.da p)) ; (_ , s₂) = bwdᵢ d₂ x₂ lr (ty-at e₂ (IPair.db p))
    in trans (IPrim.ty r) cod , farith-syn ok (⊑ᵘ-trans (IPair.use p) (IPrim.use r)) s₁ s₂
  bwdᵢ (SU.s-arith-float-il fa d₁ d₂) (x-binop x₁ x₂) lr T =
    let (ok , dom , cod) = fa-ok fa ; r = inv-prim T ; p = inv-pair (ty-at dom (IPrim.dt r))
        (e₁ , e₂) = prod-inj (sym (IPair.ty p))
        w = inv-prim (ty-at e₁ (IPair.da p))
        (_ , s₁) = bwdᵢ d₁ x₁ lr (IPrim.dt w) ; (_ , s₂) = bwdᵢ d₂ x₂ lr (ty-at e₂ (IPair.db p))
    in trans (IPrim.ty r) cod
       , farith-il-syn ok (⊑ᵘ-trans (⊑ᵘ-trans (⊑ᵘ-+ (IPrim.use w) (⊑ᵘ-refl _)) (IPair.use p)) (IPrim.use r)) s₁ s₂
  bwdᵢ (SU.s-arith-float-ir fa d₁ d₂) (x-binop x₁ x₂) lr T =
    let (ok , dom , cod) = fa-ok fa ; r = inv-prim T ; p = inv-pair (ty-at dom (IPrim.dt r))
        (e₁ , e₂) = prod-inj (sym (IPair.ty p))
        w = inv-prim (ty-at e₂ (IPair.db p))
        (_ , s₁) = bwdᵢ d₁ x₁ lr (ty-at e₁ (IPair.da p)) ; (_ , s₂) = bwdᵢ d₂ x₂ lr (IPrim.dt w)
    in trans (IPrim.ty r) cod
       , farith-ir-syn ok (⊑ᵘ-trans (⊑ᵘ-trans (⊑ᵘ-+ (⊑ᵘ-refl _) (IPrim.use w)) (IPair.use p)) (IPrim.use r)) s₁ s₂
  bwdᵢ (SU.s-compare c d₁ d₂) (x-binop x₁ x₂) lr T =
    let (ok , dom , cod) = cmp-ok c ; r = inv-prim T ; p = inv-pair (ty-at dom (IPrim.dt r))
        (e₁ , e₂) = prod-inj (sym (IPair.ty p))
        (_ , s₁) = bwdᵢ d₁ x₁ lr (ty-at e₁ (IPair.da p)) ; (_ , s₂) = bwdᵢ d₂ x₂ lr (ty-at e₂ (IPair.db p))
    in trans (IPrim.ty r) cod , cmp-syn ok (⊑ᵘ-trans (IPair.use p) (IPrim.use r)) s₁ s₂
  bwdᵢ (SU.s-id-app d) (x-app (x-res _) x) lr T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (idᶜ-ty (IApp.df a)) ; (_ , s) = bwdᵢ d x lr (IApp.dx a)
    in eX , id-gen (IApp.use a) eq s
  bwdᵢ (SU.s-fst-app d) (x-app (x-res _) x) lr T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (fstᶜ-ty (IApp.df a)) ; (_ , s) = bwdᵢ d x lr (IApp.dx a)
    in eX , fst-gen (IApp.use a) eq s
  bwdᵢ (SU.s-snd-app d) (x-app (x-res _) x) lr T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (sndᶜ-ty (IApp.df a)) ; (_ , s) = bwdᵢ d x lr (IApp.dx a)
    in eX , snd-gen (IApp.use a) eq s
  bwdᵢ (SU.s-terminal-app d) (x-app (x-res _) x) lr T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (terminalᶜ-ty (IApp.df a)) ; (_ , s) = bwdᵢ d x lr (IApp.dx a)
    in eX , terminal-gen (IApp.use a) eq s
  bwdᵢ (SU.s-apply-app d) (x-app (x-res _) x) lr T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (applyᶜ-ty (IApp.df a)) ; (_ , s) = bwdᵢ d x lr (IApp.dx a)
    in eX , apply-gen (IApp.use a) eq s
  bwdᵢ (SU.s-apply-eff-app eg d) (x-app (x-res _) x) lr T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (applyEffᶜ-ty (IApp.df a)) ; (_ , s) = bwdᵢ d x lr (IApp.dx a)
    in eX , applyEff-gen (IApp.use a) eq eg s
  bwdᵢ (SU.s-Out-app wf d) (x-app (x-res _) x) lr T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (outᶜ-ty (IApp.df a)) ; (_ , s) = bwdᵢ d x lr (IApp.dx a)
    in eX , out-gen (IApp.use a) eq wf s
  bwdᵢ (SU.s-Out-act-app wf d) (x-app (x-res _) x) lr T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (outActᶜ-ty (IApp.df a)) ; (_ , s) = bwdᵢ d x lr (IApp.dx a)
    in eX , outAct-gen (IApp.use a) eq wf s
  bwdᵢ {Γn = Γn} {Γd} (SU.s-app {A = Ax} {B = Bx} {q = qx} nsh df dx) (x-app {f = f} xf xx) lr T =
    let a = inv-app T ; (ef , sf) = bwdᵢ df xf lr (IApp.df a) ; (eA , eq , _ , eX) = arr-inj ef
    in eX , app-go sf (ty-at eA (IApp.dx a)) eq (IApp.use a)
    where
      app-go : ∀ {Φ₁ Φ₂ q Φ π} → BSyn Γn Γd f (Ax ST.⇒[ SG.mk-kind qx SG.pure ] Bx) Φ₁
             → Δ ⊩ ctxL _ ⊢[ Φ₂ ] _ ∷ Ax ! π → q ≡ qx → Φ₁ SCx.+ᵘ q SCx.*ᵘ Φ₂ SCx.⊑ᵘ Φ → BSyn Γn Γd _ Bx Φ
      app-go (bsyn (r-⇒ {k = LG.mk-kind q₀ LG.pure} refl ra rb) {Ψ₁} derF uF) dx′ eqq w =
        let (_ , bchk derX uX) = bwdᶜ dx xx lr ra dx′
        in bsyn rb (t-app (special⁻ (classifyAppHeadView f) xf nsh) derF derX)
                (⊑ᵘ-trans (app-use Ψ₁ _ q₀ uF uX (≤q-≡ (sym eqq))) w)
      app-go (bsyn (r-⇒ {k = LG.mk-kind q₀ LG.act} () ra rb) derF uF) dx′ eqq w
      app-go (bsyn (r-⇒ {k = LG.mk-kind q₀ LG.eff} () ra rb) derF uF) dx′ eqq w
  bwdᵢ {Γn = Γn} {Γd} (SU.s-effApp {A = Ax} {B = Bx} {π = πx₀} nsh eg df dx) (x-app {f = f} xf xx) lr T =
    let (A₁ , q , πa , B₀ , πf , πx , Φf , Φx , dF , dX , use , eX) = effApp-inv T
        (ef , sf) = bwdᵢ df xf lr dF ; (eA , eq , _ , eB) = arr-inj ef
    in trans eX (cong (λ Z → ST.Unit SU.⇒⟨ _ ⟩ Z) eB) , effapp-go eg sf (ty-at eA dX) eq use
    where
      effapp-go : ∀ {q Φ₁ Φ₂ Φ πx} → SG.EffGrade πx₀ → BSyn Γn Γd f (Ax SU.⇒⟨ πx₀ ⟩ Bx) Φ₁
                → Δ ⊩ ctxL _ ⊢[ Φ₂ ] _ ∷ Ax ! πx → q ≡ SG.Many → Φ₁ SCx.+ᵘ q SCx.*ᵘ Φ₂ SCx.⊑ᵘ Φ
                → BSyn Γn Γd _ (ST.Unit SU.⇒⟨ πx₀ ⟩ Bx) Φ
      effapp-go eg′ (bsyn rf {Ψ₁} derF uF) dx′ eqq w = go eg′ (arr-many rf) derF
        where
          go : ∀ {Af} → SG.EffGrade πx₀ → ArrMany Af Ax Bx πx₀ → C _ Γn Γd ⊢ᵢ f ∶ Af ⨾ Ψ₁ → BSyn Γn Γd _ (ST.Unit SU.⇒⟨ πx₀ ⟩ Bx) _
          go eg″ record { πeq = refl ; eq = refl ; r₁ = r₁ ; r₂ = r₂ } d =
            let (_ , bchk derX uX) = bwdᶜ dx xx lr r₁ dx′
            in bsyn (r-⇒ refl r-unit r₂) (t-effApp {g = eff-L eg″} (special⁻ (classifyAppHeadView f) xf nsh) d derX)
                    (⊑ᵘ-trans (app-use Ψ₁ _ LG.Many uF uX (≤q-≡ (sym eqq))) w)
  bwdᵢ {Γn = Γn} {Γd} (SU.s-app-spine {X = Xs} {T = Ts} nsh dx df) (x-app {f = f} {a = a₀} xf xx) lr {X = X} T =
    let a = inv-app T ; (eX₀ , sx) = bwdᵢ dx xx lr (IApp.dx a)
        (ef , dF) = bwdᵈ df xf lr (BSyn.ra sx) LG.pure refl (ty-at (cong (λ Z → Z ST.⇒[ SG.mk-kind (IApp.q a) (IApp.πf a) ] X) eX₀) (IApp.df a))
        (_ , eq , _ , eT) = arr-inj ef
    in eT , spine-go sx dF eq (IApp.use a)
    where
      spine-go : ∀ {Φ₁ Φ₂ q Φ} → (sx : BSyn Γn Γd a₀ Xs Φ₂) → BDom Γn Γd f (BSyn.A sx) LG.pure Ts Φ₁
               → q ≡ SG.Many → Φ₁ SCx.+ᵘ q SCx.*ᵘ Φ₂ SCx.⊑ᵘ Φ → BSyn Γn Γd (Once.Lang.Syntax.RApp f a₀) Ts Φ
      spine-go (bsyn rx {Ψ₂} derX uX) (bdom rb {Ψ₁} derF uF) eqq w =
        bsyn rb (t-app-spine (special⁻ (classifyAppHeadView f) xf nsh) derX derF)
             (⊑ᵘ-trans (app-use Ψ₁ Ψ₂ LG.Many uF uX (≤q-≡ (sym eqq))) w)

  ----------------------------------------------------------------------
  -- Checking
  ----------------------------------------------------------------------

  bwdᶜ SU.c-id (x-res _) lr rA T =
    on-arr rA λ _ r₁ r₂ → idᶜ-ty T
      , ≡-chk (cong (λ Z → _ LT.⇒[ _ ] Z) (TyR-uniqueˡ r₁ r₂)) (bchk (t-id-check {u = pure-⊑ _}) zero-use)
  bwdᶜ SU.c-fst (x-res _) lr rA T =
    on-arr rA λ { _ (r-* ra rb) r₂ → fstᶜ-ty T
      , ≡-chk (cong (λ Z → _ LT.⇒[ _ ] Z) (TyR-uniqueˡ ra r₂)) (bchk (t-fst-check {u = pure-⊑ _}) zero-use) }
  bwdᶜ SU.c-snd (x-res _) lr rA T =
    on-arr rA λ { _ (r-* ra rb) r₂ → sndᶜ-ty T
      , ≡-chk (cong (λ Z → _ LT.⇒[ _ ] Z) (TyR-uniqueˡ rb r₂)) (bchk (t-snd-check {u = pure-⊑ _}) zero-use) }
  bwdᶜ SU.c-terminal (x-res _) lr rA T =
    on-arr rA λ { _ r₁ r-unit → terminalᶜ-ty T , bchk (t-terminal-morph-check {u = pure-⊑ _}) zero-use }
  bwdᶜ SU.c-initial (x-res _) lr rA T =
    on-arr rA λ { _ r-void r₂ → initialᶜ-ty T , bchk (t-initial-morph-check {u = pure-⊑ _}) zero-use }
  bwdᶜ SU.c-inl (x-res _) lr rA T =
    on-arr rA λ { _ r₁ (r-+ ra rb) → inlᶜ-ty T
      , ≡-chk (cong (λ Z → Z LT.⇒[ _ ] _) (TyR-uniqueˡ ra r₁)) (bchk (t-inl-morph-check {u = pure-⊑ _}) zero-use) }
  bwdᶜ SU.c-inr (x-res _) lr rA T =
    on-arr rA λ { _ r₁ (r-+ ra rb) → inrᶜ-ty T
      , ≡-chk (cong (λ Z → Z LT.⇒[ _ ] _) (TyR-uniqueˡ rb r₁)) (bchk (t-inr-morph-check {u = pure-⊑ _}) zero-use) }
  bwdᶜ (SU.c-compose-g dg df) (x-app (x-app (x-res _) xf) xg) lr rA T =
    let (r , M , q , πa , C₀ , eF , eX) = compose-inv T
    in on-arr rA λ pe r₁ r₂ →
         let (_ , bdom rb {Ψ₂} derG uG) = bwdᵈ dg xg lr r₁ _ pe (Two.dg r)
             (ef , bchk {Ψ₁} derF uF) = bwdᶜ df xf lr (r-⇒ (kM pe) rb r₂) (Two.df r)
         in trans eX (cod-cong (cod-eq eF ef))
            , bchk (t-compose-check-g derG derF) (⊑ᵘ-trans (app-use Ψ₁ Ψ₂ LG.Many uF uG SG.ω≤ω) (Two.use r))
  bwdᶜ (SU.c-compose-f df sub dg) (x-app (x-app (x-res _) xf) xg) lr rA T =
    let (r , M , q , πa , C₀ , eF , eX) = compose-inv T ; cf = inv-coerce (Two.df r)
        (_ , bsyn rf {Ψ₁} derF uF) = bwdᵢ df xf lr (ICoerce.dt cf)
        (π₁ , B₁ , C₁ , pe₁ , rB₁ , rC₁ , derF′) = syn-arr rf derF
    in on-arr rA λ pe r₁ r₂ →
         let (_ , bchk {Ψ₂} derG uG) = bwdᶜ dg xg lr (r-⇒ (kM pe) r₁ rB₁) (Two.dg r)
         in trans eX (cod-cong (cod-eq eF (ICoerce.ty cf)))
            , bchk (t-compose-check-f derF′ (sub-L sub (r-⇒ (kM pe₁) rB₁ rC₁) (r-⇒ (kM pe) rB₁ r₂)) derG)
                   (⊑ᵘ-trans (app-use Ψ₁ Ψ₂ LG.Many (⊑ᵘ-trans uF (ICoerce.use cf)) uG SG.ω≤ω) (Two.use r))
  bwdᶜ (SU.c-case df dg) (x-app (x-app (x-res _) xf) xg) lr rA T =
    let (r , C₀ , (_ , _ , _ , eF) , _ , eX) = case-inv T
    in on-arr rA λ { pe (r-+ ra rb) r₂ →
         let (ef , bchk {Ψ₁} derF uF) = bwdᶜ df xf lr (r-⇒ (kM pe) ra r₂) (Two.df r)
             (_ , bchk {Ψ₂} derG uG) = bwdᶜ dg xg lr (r-⇒ (kM pe) rb r₂) (Two.dg r)
         in trans eX (cod-cong (cod-eq eF ef))
            , bchk (t-case-copair-check derF derG) (one-use Ψ₁ Ψ₂ uF uG (Two.use r)) }
  bwdᶜ (SU.c-pair df dg) (x-app (x-app (x-res _) xf) xg) lr rA T =
    let (r , B₀ , C₀ , (_ , _ , _ , eF) , (_ , _ , _ , eG) , eX) = pair-inv T
    in on-arr rA λ { pe r₁ (r-* rb rc) →
         let (ef , bchk {Ψ₁} derF uF) = bwdᶜ df xf lr (r-⇒ (kM pe) r₁ rb) (Two.df r)
             (eg , bchk {Ψ₂} derG uG) = bwdᶜ dg xg lr (r-⇒ (kM pe) r₁ rc) (Two.dg r)
         in trans eX (cod-cong (cong₂ ST._*_ (cod-eq eF ef) (cod-eq eG eg)))
            , bchk (t-pair-morph-check derF derG) (one-use Ψ₁ Ψ₂ uF uG (Two.use r)) }
  bwdᶜ (SU.c-curry df) (x-app (x-res _) xf) lr rA T =
    let (r , M , q , πa , C₀ , eF , eX) = curry-inv T
    in on-arr rA λ pe₀ r₁ r₂ →
         let (πi , Bc , Cc , pei , eqi , rb , rc) = split-arr r₂
             (ef , bchk {Ψ} derF uF) = bwdᶜ df xf lr (r-⇒ (kM pei) (r-* r₁ rb) rc) (One′.df r)
         in trans eX (cong (λ Z → _ SU.⇒⟨ _ ⟩ (_ SU.⇒⟨ _ ⟩ Z)) (cod-eq eF ef))
            , ≡-chk (cong (λ Z → _ LT.⇒[ _ ] Z) (sym eqi)) (bchk (t-curry-check {u = pure-⊑ _} derF) (one-use′ Ψ uF (One′.use r)))
  bwdᶜ (SU.c-cata wf dalg) (x-app (x-res _) xa) lr rA T =
    let (r , A₀ , π₁ , eF , eX) = cata-inv T
    in on-arr rA λ { pe (r-μ fr) r₂ →
         let (ef , bchk {Ψ} derA uA) = bwdᶜ dalg xa lr (r-⇒ (kM pe) (⟦⟧-R fr r₂) r₂) (One′.df r)
         in trans eX (cod-cong (cod-eq eF ef))
            , bchk (t-cata-check {u = pure-⊑ _} (wf-L wf fr) derA) (many-use Ψ uA (One′.use r)) }
  bwdᶜ (SU.c-ana le wf dc) (x-app (x-res _) xc) lr rA T =
    let (f₀ , A₁ , πc , Φc , dc′ , use , eX) = ana-inv T
    in on-arr rA λ { pe r₁ (r-ν {φ = φ} eφ fr) →
         let (ec , bchk {Ψ} derC uC) = bwdᶜ dc xc lr (r-⇒ (kM (trans (πS-fin φ) (cong SG.fin eφ))) r₁ (⟦⟧-R fr r₁)) dc′
         in trans eX (cong (λ g → _ SU.⇒⟨ _ ⟩ ST.ν _ g) (fin-inj (grd-eq ec)))
            , bchk (t-ana-check {u = pure-⊑ _} {ua = ⊑π-L _ LG.act (subst (SG._⊑π SG.act) (sym pe) le)} (wf-L wf fr) derC)
                   (many-use Ψ uC use) }
  bwdᶜ (SU.c-loop dc) (x-app (x-res _) xc) lr rA T =
    let (r , A₁ , B₀ , eF , eX) = loop-inv T
    in on-arr rA λ pe r₁ r₂ →
         let (ef , bchk {Ψ} derC uC) = bwdᶜ dc xc lr (r-⇒ refl r₁ (r-+ r₂ r₁)) (One′.df r)
         in trans eX (cod-cong (proj₁ (sum-inj (cod-eq eF ef))))
            , ≡-chk (cong (λ π → _ LT.⇒[ LG.mk-kind LG.Many π ] _) (sym (eff-of pe)))
                    (bchk (t-loop-check derC) (many-use Ψ uC (One′.use r)))
  bwdᶜ (SU.c-sub ds sub) x lr rB T =
    let c = inv-coerce T ; (_ , bsyn ra {Ψ} der u) = bwdᵢ ds x lr (ICoerce.dt c)
    in ICoerce.ty c , bchk (t-sub der (sub-L sub ra rB)) (⊑ᵘ-trans u (ICoerce.use c))
  bwdᶜ (SU.c-lam db) (x-lam xb) lr rA T =
    let l = inv-lam T ; (k , A₁ , A₂ , ek , eA , ra , rb) = split-k rA
        (eB , bchk der u) = bwdᶜ db xb (lr-▸ lr ra) rb (ILam.body l)
    in trans (ILam.ty l) (cong (λ Z → _ ST.⇒[ _ ] Z) eB)
       , ≡-chk (sym eA) (lam-chk k ek der u (ILam.le l) (ILam.use l))
  bwdᶜ (SU.c-pair-lit da db) (x-pair xa xb) lr (r-* ra rb) T =
    let p = inv-pair T
        (ea , bchk {Ψ₁} dA uA) = bwdᶜ da xa lr ra (IPair.da p)
        (eb , bchk {Ψ₂} dB uB) = bwdᶜ db xb lr rb (IPair.db p)
    in trans (IPair.ty p) (cong₂ ST._*_ ea eb) , bchk (t-pair-lit-check dA dB) (⊑ᵘ-trans (sum-use Ψ₁ Ψ₂ uA uB) (IPair.use p))
  bwdᶜ (SU.c-In-app wf d) (x-app (x-res _) x) lr (r-μ fr) T =
    let a = inv-app T ; (eA , eq , _ , eX) = arr-inj (inᶜ-ty (IApp.df a))
        (_ , bchk {Ψ} der u) = bwdᶜ d x lr (⟦⟧-R fr (r-μ fr)) (ty-at eA (IApp.dx a))
    in eX , bchk (t-In-app-check (wf-L wf fr) der) (gen-use Ψ u eq (IApp.use a))
  bwdᶜ (SU.c-apply-app d) (x-app (x-res _) x) lr rB T =
    let a = inv-app T ; (eA , eq , _ , eX) = arr-inj (applyᶜ-ty (IApp.df a))
        (_ , s) = bwdᵢ d x lr (ty-at eA (IApp.dx a))
    in eX , apply-chk s rB eq (IApp.use a)
  bwdᶜ (SU.c-inl-app d) (x-app (x-res _) x) lr (r-+ ra rb) T =
    let a = inv-app T ; (eA , eq , _ , eX) = arr-inj (inlᶜ-ty (IApp.df a))
        (_ , bchk {Ψ} der u) = bwdᶜ d x lr ra (ty-at eA (IApp.dx a))
    in eX , bchk (t-inl-app-check der) (gen-use Ψ u eq (IApp.use a))
  bwdᶜ (SU.c-inr-app d) (x-app (x-res _) x) lr (r-+ ra rb) T =
    let a = inv-app T ; (eA , eq , _ , eX) = arr-inj (inrᶜ-ty (IApp.df a))
        (_ , bchk {Ψ} der u) = bwdᶜ d x lr rb (ty-at eA (IApp.dx a))
    in eX , bchk (t-inr-app-check der) (gen-use Ψ u eq (IApp.use a))
  bwdᶜ (SU.c-initial-app d) (x-app (x-res _) x) lr rA T =
    let a = inv-app T ; (eA , eq , _ , eX) = arr-inj (initialᶜ-ty (IApp.df a))
        (_ , bchk {Ψ} der u) = bwdᶜ d x lr r-void (ty-at eA (IApp.dx a))
    in eX , bchk (t-initial-app-check der) (gen-use Ψ u eq (IApp.use a))
  bwdᶜ {Γn = Γn} (SU.c-poly d e pos τ resp) (x-own ∉ x∈) lr rA T =
    let pa = h-poly e x∈
    in inv-ref T
       , bchk (t-var-poly-instantiate (lk-none Γn ∉) (Sc.PolyAt.lki pa) (Sc.PolyAt.lp pa) (Sc.PolyAt.open′ pa pos)
                                      (Sc.PolyAt.inst pa τ resp rA))
              zero-use
  bwdᶜ (SU.c-poly d e pos τ resp) (x-res nop) lr rA T = ⊥-elim (poly-res d e pos nop)

  ----------------------------------------------------------------------
  -- An arrow out of a given domain
  ----------------------------------------------------------------------

  bwdᵈ (SU.d-infer dg sub le) x lr rA π pe T =
    let c = inv-coerce T ; (_ , bsyn rf {Ψ} der u) = bwdᵢ dg x lr (ICoerce.dt c)
        (π₁ , A₁ , B₁ , pe₁ , r₁ , r₂ , der′) = syn-arr rf der
    in ICoerce.ty c
       , bdom r₂ (d-infer der′ (sub-L sub rA r₁) (⊑π-L π₁ π (subst₂ SG._⊑π_ (sym pe₁) (sym pe) le))) (⊑ᵘ-trans u (ICoerce.use c))
  bwdᵈ {Γn = Γn} (SU.d-poly d e pos {π′ = π₁} {B = B} eT occ τ resp eA eB le) (x-own ∉ x∈) lr rA π pe T =
    let pa = h-poly e x∈ ; (B₀ , rB) = back B
        (sd₀ , sc₀ , ar , cv) = Sc.PolyAt.arrow pa eT occ (πL π₁) (πS-πL π₁)
        rT = subst (λ Z → TyR Δ _ (Z ST.⟨ τ ⟩)) (sym eT)
                   (r-⇒ (kM (πS-πL π₁)) (subst (TyR Δ _) (sym eA) rA) (subst (TyR Δ _) (sym eB) rB))
    in ICoerce.ty (inv-coerce T)
       , bdom rB (d-poly (lk-none Γn ∉) (Sc.PolyAt.lki pa) (Sc.PolyAt.lp pa) (Sc.PolyAt.open′ pa pos) ar cv
                         (Sc.PolyAt.inst pa τ resp rT) (⊑π-L (πL π₁) π (subst₂ SG._⊑π_ (sym (πS-πL π₁)) (sym pe) le)))
              zero-use
  bwdᵈ (SU.d-poly d e pos eT occ τ resp eA eB le) (x-res nop) lr rA π pe T = ⊥-elim (poly-res d e pos nop)
  bwdᵈ (SU.d-lam db) (x-lam xb) lr rA π pe T =
    let l = inv-lam T ; (eB , sb) = bwdᵢ db xb (lr-▸ lr rA) (ILam.body l)
    in trans (ILam.ty l) (cong (λ Z → _ ST.⇒[ _ ] Z) eB) , lam-dom sb (ILam.use l)
  bwdᵈ (SU.d-compose dg df) (x-app (x-app (x-res _) xf) xg) lr rA π pe T =
    let (r , M , q , πa , C₀ , eF , eX) = compose-inv T
        (_ , bdom rM {Ψ₂} derG uG) = bwdᵈ dg xg lr rA π pe (Two.dg r)
        (ef , bdom rB {Ψ₁} derF uF) = bwdᵈ df xf lr rM π pe (Two.df r)
    in trans eX (cod-cong (cod-eq eF ef))
       , bdom rB (d-compose derG derF) (⊑ᵘ-trans (app-use Ψ₁ Ψ₂ LG.Many uF uG SG.ω≤ω) (Two.use r))
  bwdᵈ SU.d-id (x-res _) lr rA π pe T = idᶜ-ty T , bdom rA (d-id {u = pure-⊑ π}) zero-use
  bwdᵈ SU.d-fst (x-res _) lr (r-* ra rb) π pe T = fstᶜ-ty T , bdom ra (d-fst {u = pure-⊑ π}) zero-use
  bwdᵈ SU.d-snd (x-res _) lr (r-* ra rb) π pe T = sndᶜ-ty T , bdom rb (d-snd {u = pure-⊑ π}) zero-use
  bwdᵈ SU.d-terminal (x-res _) lr rA π pe T = terminalᶜ-ty T , bdom r-unit (d-terminal {u = pure-⊑ π}) zero-use
  bwdᵈ SU.d-initial (x-res _) lr r-void π pe T = initialᶜ-ty T , bdom r-void (d-initial {u = pure-⊑ π}) zero-use
  bwdᵈ (SU.d-case df dg J) (x-app (x-app (x-res _) xf) xg) lr (r-+ ra rb) π pe T =
    let (r , C₀ , (_ , _ , _ , eF) , _ , eX) = case-inv T
        cf = inv-coerce (Two.df r) ; cg = inv-coerce (Two.dg r)
        (_ , bdom rCf {Ψ₁} derF uF) = bwdᵈ df xf lr ra π pe (ICoerce.dt cf)
        (_ , bdom rCg {Ψ₂} derG uG) = bwdᵈ dg xg lr rb π pe (ICoerce.dt cg)
        (Cc , rC , J₀) = join-L J rCf rCg
    in trans eX (cod-cong (cod-eq eF (ICoerce.ty cf)))
       , bdom rC (d-case derF derG J₀)
              (one-use Ψ₁ Ψ₂ (⊑ᵘ-trans uF (ICoerce.use cf)) (⊑ᵘ-trans uG (ICoerce.use cg)) (Two.use r))
  bwdᵈ (SU.d-pair df dg) (x-app (x-app (x-res _) xf) xg) lr rA π pe T =
    let (r , B₀ , C₀ , (_ , _ , _ , eF) , (_ , _ , _ , eG) , eX) = pair-inv T
        (ef , bdom rB {Ψ₁} derF uF) = bwdᵈ df xf lr rA π pe (Two.df r)
        (eg , bdom rC {Ψ₂} derG uG) = bwdᵈ dg xg lr rA π pe (Two.dg r)
    in trans eX (cod-cong (cong₂ ST._*_ (cod-eq eF ef) (cod-eq eG eg)))
       , bdom (r-* rB rC) (d-pair derF derG) (one-use Ψ₁ Ψ₂ uF uG (Two.use r))
  bwdᵈ (SU.d-cata wf da) (x-app (x-res _) xa) lr (r-μ fr) π pe T =
    let (r , A₀ , π₁ , eF , eX) = cata-inv T
        (ef , bsyn ralg {Ψ} der u) = bwdᵢ da xa lr (One′.df r)
        (π₂ , A₁ , A₂ , pe₂ , r₁ , r₂ , der′) = syn-arr ralg der
    in trans eX (cod-cong (cod-eq eF ef))
       , bdom r₂ (d-cata {u = pure-⊑ π} (wf-L wf fr)
                         (subst₂ (λ Z π₃ → C _ _ _ ⊢ᵢ _ ∶ (Z LT.⇒[ LG.mk-kind LG.Many π₃ ] A₂) ⨾ Ψ)
                                 (TyR-uniqueˡ r₁ (⟦⟧-R fr r₂)) (πS-injective (trans pe₂ (sym pe))) der′))
              (many-use Ψ u (One′.use r))

