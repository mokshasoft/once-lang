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
  where

open import Data.Fin using (zero; suc)
open import Data.Nat using (suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst)
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

  ty-ctx : ∀ {n} {Γ : SCx.Ctx m n} {A A′ q Ψ t B π} → A ≡ A′
         → Δ ⊩ (Γ SCx.▸ A) ⊢[ q SCx.∷ Ψ ] t ∷ B ! π → Δ ⊩ (Γ SCx.▸ A′) ⊢[ q SCx.∷ Ψ ] t ∷ B ! π
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
