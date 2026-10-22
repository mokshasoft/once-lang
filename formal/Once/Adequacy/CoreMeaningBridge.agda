-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreMeaningBridge — plan 0.103 6b, step B.2: THE SURFACE
-- MEANING IS THE CORE MEANING OF THE ELABORATION.
--
--   ⟦ d ⟧ᶜ fmt ρ dγ ≡ GM.⟦ proj₂ (elabᶜ V d) ⟧ fmt δ dγ
--
-- clause by clause over the surface judgment, in an environment `ρ` that
-- AGREES with the core's `δ` at every reference the View resolves (`Agree`).
-- The derived combinators were written so their evaluation order is the
-- surface clause's (Spec.Core.Derived's header); what the proof spends is the
-- monad laws, the renaming lemma (B.1, `CoreRenameSem.ren-sem`) where a
-- combinator weakens or closes an arm, and the transports the typing proofs
-- carry.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Adequacy.CoreMeaningBridge (fmt : TargetNum) (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; trans-reflʳ)

open import Once.Spec.Type using (Ty; Type; Fun; KCtx; WFFun; TySub; Respects; _⟨_⟩; _*_; _+_; _⇒[_]_)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; pure; act; eff; Finite; fin; _⊑π_)
open import Once.Spec.Context using (Ctx; _▸_; _∷_; _⊑∷_; Usage)
open import Once.Spec.Signature using (⌜_⌝ᵈ)
open import Once.Spec.Core.Syntax using (Schema; schema; _!!_; ref)
open Schema using (arity; kinds; type)
open import Once.Internal.Type.Poly using (PolyType)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Internal.Type.Schema using (schemaOf; kinded-instance)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Type using (⟦_⟧T; wk₀; none)
open import Once.Internal.Weaken using (⟦wk₀⟧ᵛ)
open import Once.Internal.Name using (showCanonical)
open import Once.Spec.Name using (CanonicalName)
open import Once.Postulates using (extensionality)
open import Once.Internal.Graded using (⟦_⟧ᵛ; M; bindM; returnM; subM; _>>=ᵖ_; bindᵍ)
open import Once.Internal.Type.Sub using (·p-diag; ⊑π-irr; pure-⊑)
open import Once.Denotation.GradedDomainLaws using (>>=ᵖ-β; >>=ᵖ-assoc; >>=ᵖ-idʳ)
open import Once.Internal.Trace using (T; interp; module Interp)
open Interp using (sig; impl)
open import Once.Internal.Typing.Scope using (NamedCtx; lookupImport; lookupPolyPrefix; Imports; PolyCtx)
open import Once.Internal.Typing
open import Once.Denotation.DefEnv using (defAt; impAt)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵈ; MeaningsOf; Meanings; returnᵖ)
open Once.Denotation.Meaning.Meanings using (decl-res; defs; entries; world)
open import Once.Internal.GradedOps using (fmapM; sigOpRefᵛ; cata-semᵛ; ana-semᵛ; ⟦_⟧<:ᵛ)
open import Once.Internal.Core.Decl using (toISig; ∈-toISig; ⌜⌝ᵈ-concrete; declS; ⌜declS⌝)
import Once.Internal.Core.Meaning Σ S as GM
open import Once.Spec.Core.Typing Σ S
open import Once.Internal.Elaboration Σ S
  using (Views; View; ImportAt; Declared; declared; def; elabᶜ; elabᵢ; elabᵈ; Elab; refAt; sigE; importE; polyE; retypeD; retypeE)
open View

------------------------------------------------------------------------
-- The references' meanings
------------------------------------------------------------------------

-- An entry of the table at a kind-respecting instance of its schema.
refSemAt : (δ : GM.DefSem) (d : Fin s) {sc : Schema} → S !! d ≡ sc → (τ : TySub (arity sc) 0) {Δ : KCtx 0}
         → Respects (kinds sc) Δ τ → ⟦ type sc ⟨ τ ⟩ ⟧ᵛ
refSemAt δ d refl τ r = GM.defs δ d τ r

-- A telescope definition at a kinded instance (the instance `polyE` computes).
polySem : ∀ {imps sg polys} (δ : GM.DefSem) (V : View imps sg polys) {x sc body prefix} {Δ : KCtx 0} {U : Ty 0}
        → (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix)) → KindedInstance Δ sc U → ⟦ U ⟧ᵛ
polySem δ V {sc = sc} lp ki =
  subst (λ X → ⟦ X ⟧ᵛ) (proj₂ (proj₂ (kinded-instance sc ki)))
        (refSemAt δ (entry V lp) (entryIs V lp) (proj₁ (kinded-instance sc ki)) (proj₁ (proj₂ (kinded-instance sc ki))))

-- …a monomorphic definition, at its ground type…
impSem : (δ : GM.DefSem) {Δ : KCtx 0} {x : String} {T : Type} → ImportAt x T → ⟦ wk₀ {0} T ⟧ᵛ
impSem δ {Δ} (def d mono) = refSemAt δ d mono none {Δ = Δ} (λ ())

-- …and a generator of Σ (D274: an FFI declaration is not a definition).
sigSem : (δ : GM.DefSem) (c : CanonicalName) {T : Type} → IsConcrete T → Declared (showCanonical c) T → ⟦ wk₀ {0} T ⟧ᵛ
sigSem δ c {T} k (declared h mem) =
  subst (λ X → ⟦ X ⟧ᵛ) (⌜declS⌝ k h)
        (sigOpRefᵛ {A = ⌜ declS T ⌝ᵈ} fmt (toISig Σ) (GM.impl δ) c (⌜⌝ᵈ-concrete (declS T)) (∈-toISig (mem {c} refl)))

------------------------------------------------------------------------
-- The environment agreement
------------------------------------------------------------------------

-- `ρ` agrees with `δ` at every reference the View resolves.
record Agree {imps sg : Imports} {polys : PolyCtx} (V : View imps sg polys) (ρ : Meanings polys imps sg) (δ : GM.DefSem) : Set where
  field
    agree-inst : ∀ {Δ : KCtx 0} {x sc body prefix U} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
                   (ki : KindedInstance Δ sc U)
               → defAt polys x (defs ρ) lp U ki ≡ polySem δ V lp ki
    agree-import : ∀ {Δ : KCtx 0} {x T} (lk : lookupImport imps x ≡ just T)
                 → subst id (sym (⟦wk₀⟧ᵛ T)) (impAt imps x (entries ρ) lk) ≡ impSem δ {Δ} (imported V lk)
    -- a resolved reference names a generator of Σ: both meanings read the same
    -- declaration.
    agree-resolved : ∀ {cn T} (lk : lookupImport sg (showCanonical cn) ≡ just T) (k : IsConcrete T)
                   → subst id (sym (⟦wk₀⟧ᵛ T)) (sigOpRefᵛ {A = T} fmt (sig (world ρ)) (impl (world ρ)) cn k (decl-res ρ {cn = cn} lk))
                     ≡ sigSem δ cn k (declares V lk)

------------------------------------------------------------------------
-- The references' core meanings
------------------------------------------------------------------------

module _ {Δ : KCtx 0} {n} {Γ : Ctx 0 n} (δ : GM.DefSem) where

  ⟦⟧-retypeD : ∀ {Ψ t A B π} (e : A ≡ B) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (x : GM.Env Γ Ψ)
             → GM.⟦ retypeD e d ⟧ fmt δ x ≡ subst (λ X → M π ⟦ X ⟧ᵛ) e (GM.⟦ d ⟧ fmt δ x)
  ⟦⟧-retypeD refl d x = refl

  ⟦⟧-retypeE : ∀ {Ψ A B} (e : A ≡ B) (el : Elab Δ Γ Ψ A) (x : GM.Env Γ Ψ)
             → GM.⟦ proj₂ (retypeE e el) ⟧ fmt δ x ≡ subst (λ X → ⟦ X ⟧ᵛ) e (GM.⟦ proj₂ el ⟧ fmt δ x)
  ⟦⟧-retypeE refl el x = refl

  refAt-sem : (d : Fin s) {sc : Schema} (e : S !! d ≡ sc) (τ : TySub (arity sc) 0) (r : Respects (kinds sc) Δ τ) (x : GM.Env Γ _)
            → GM.⟦ proj₂ (refAt {Γ = Γ} d e τ r) ⟧ fmt δ x ≡ refSemAt δ d e τ r
  refAt-sem d refl τ r x = refl

  polyE-sem : ∀ {imps sg polys} (V : View imps sg polys) {x sc body prefix U}
                (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix)) (ki : KindedInstance Δ sc U) (y : GM.Env Γ _)
            → GM.⟦ proj₂ (polyE {Γ = Γ} V lp ki) ⟧ fmt δ y ≡ polySem δ V lp ki
  polyE-sem V {sc = sc} lp ki y =
    trans (⟦⟧-retypeE (proj₂ (proj₂ (kinded-instance sc ki))) _ y)
          (cong (subst (λ X → ⟦ X ⟧ᵛ) (proj₂ (proj₂ (kinded-instance sc ki))))
                (refAt-sem (entry V lp) (entryIs V lp) _ _ y))

  importE-sem : ∀ {x T} (i : ImportAt x T) (y : GM.Env Γ _) → GM.⟦ proj₂ (importE {Γ = Γ} i refl) ⟧ fmt δ y ≡ impSem δ {Δ} i
  importE-sem (def d mono) y = refAt-sem d mono none (λ ()) y

  sigE-sem : ∀ (c : CanonicalName) {T} (k : IsConcrete T) (D : Declared (showCanonical c) T) (y : GM.Env Γ _)
           → GM.⟦ proj₂ (sigE {Γ = Γ} c k D refl) ⟧ fmt δ y ≡ sigSem δ c k D
  sigE-sem c {T} k (declared h mem) y =
    trans (⟦⟧-retypeD (trans (⌜declS⌝ k h) refl) _ y)
          (cong (λ e → subst (λ X → ⟦ X ⟧ᵛ) e (sigOpRefᵛ {A = ⌜ declS T ⌝ᵈ} fmt (toISig Σ) (GM.impl δ) c (⌜⌝ᵈ-concrete (declS T)) (∈-toISig (mem {c} refl))))
                (trans-reflʳ (⌜declS⌝ k h)))

------------------------------------------------------------------------
-- The derived combinators' meanings (one lemma per combinator)
------------------------------------------------------------------------

open import Once.Internal.Context using (_+ᵘ_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*Many; zeroUsage; _⊑ᵘ_; _⊔ᵘ_; ⊑ᵘ-refl)
open import Once.Surface.Properties using (+ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-identityˡ; *ᵘ-zeroʳ)
open import Once.Internal.Environment using (bindᵛ; restrictᵛ)
open import Once.Internal.Iterative using (loop)
open import Once.Spec.Sub using (sub-arr)
open import Once.Spec.Sub using (_⊔_≔_)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open _⊔_≔_ using () renaming (left to ⊔-left; right to ⊔-right)
open import Once.Type.Grade using (≤qᵇ→≤q)
open import Once.Internal.Core.DerivedTyping Σ S
import Once.Internal.Laws.CoreRenameSem Σ S as RS
import Once.Denotation.EnvAlgebraV as EA

-- A usage transport on a derivation is a transport on its environment.
⟦⟧-substΨ : ∀ {Δ : KCtx 0} {n} {Γ : Ctx 0 n} {Ψ Ψ′ : Usage n} {A : Ty 0} {t π} (e : Ψ ≡ Ψ′)
              (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (δ : GM.DefSem) (x : GM.Env Γ Ψ′)
          → GM.⟦ subst (λ U → Δ ⊩ Γ ⊢[ U ] t ∷ A ! π) e d ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ (subst (GM.Env Γ) (sym e) x)
⟦⟧-substΨ refl d δ x = refl

-- A restriction of a transported environment is any restriction of the original.
env-subst : ∀ {n} {Γ : Ctx 0 n} {U U' Ψ' : Usage n} (e : U ≡ U') (u : Ψ' ⊑ᵘ U) (u' : Ψ' ⊑ᵘ U') (x : GM.Env Γ U')
          → restrictᵛ {Γ = Γ} u (subst (GM.Env Γ) (sym e) x) ≡ restrictᵛ {Γ = Γ} u' x
env-subst {Γ = Γ} refl u u' x = EA.restrict-irr {Γ = Γ} u u' x

-- Two restrictions of a transported environment: any restriction of the original.
env-subst₂ : ∀ {n} {Γ : Ctx 0 n} {Ψ' Um U U' : Usage n} (u : Ψ' ⊑ᵘ Um) (v : Um ⊑ᵘ U) (e : U ≡ U') (w : Ψ' ⊑ᵘ U')
               (x : GM.Env Γ U')
           → restrictᵛ {Γ = Γ} u (restrictᵛ {Γ = Γ} v (subst (GM.Env Γ) (sym e) x)) ≡ restrictᵛ {Γ = Γ} w x
env-subst₂ {Γ = Γ} u v refl w x = EA.restrict-≡ {Γ = Γ} u v w x

-- A shared grade read as the product of two (D311): the diagonal's bind.
diag-bind : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y) → subM (·p-diag π) (bindᵍ π π m k) ≡ bindM π m k
diag-bind Once.Spec.Grade.pure m k = refl
diag-bind Once.Spec.Grade.eff  m k = refl
diag-bind Once.Spec.Grade.act  m k = refl

module Comb {Δ : KCtx 0} {δ : GM.DefSem} where
  bindC : ∀ {X Y : Set} {a a' : X} {f g : X → Y} → a ≡ a' → (∀ v → f v ≡ g v) → (a >>=ᵖ f) ≡ (a' >>=ᵖ g)
  bindC {a = a} refl h = cong (a >>=ᵖ_) (extensionality h)

  compose-sem : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty 0} {π} {f g}
    (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ B ⇒[ mk-kind Many π ] C ! pure) (dg : Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π ] B ! pure)
    (x : GM.Env Γ (Ψ₁ +ᵘ Many *ᵘ Ψ₂))
    → GM.⟦ ⊢composeᶜ (·p-diag π) df dg ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x) >>=ᵖ λ vf →
         GM.⟦ dg ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x) >>=ᵖ λ vg →
         λ a → bindM π (vg a) vf)
  compose-sem {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} df dg x =
    trans (⟦⟧-substΨ E
                        (⊢let df (⊢let (wk-⊢′ _ dg)
                          (⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff (·p-diag π) (⊢app (⊢var (suc (suc zero))) (⊢app (⊢var (suc zero)) (⊢var zero)))))))
                        δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x))
                 (λ vf → bindC (trans (RS.wk-sem fmt δ _ dg _) (cong (GM.⟦ dg ⟧ fmt δ) (env-subst₂ {Γ = Γ} _ _ E (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x)))
                               (λ vg → extensionality λ a →
                                  trans (cong (subM (·p-diag π))
                                          (trans (>>=ᵖ-β vf _)
                                                 (cong (λ m → bindᵍ π π m (λ y → vf y))
                                                       (trans (>>=ᵖ-β vg _) (>>=ᵖ-β a _)))))
                                        (diag-bind π (vg a) vf))))
    where E = compose-use {Δ = Δ} Ψ₁ Ψ₂

  pair-sem : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty 0} {π} {f g}
    (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! pure) (dg : Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π ] C ! pure)
    (x : GM.Env Γ (Ψ₁ +ᵘ Ψ₂))
    → GM.⟦ ⊢pairᶜ (·p-diag π) df dg ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x) >>=ᵖ λ vf →
         GM.⟦ dg ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x) >>=ᵖ λ vg →
         λ a → bindM π (vf a) λ b → fmapM π (λ c → (b , c)) (vg a))
  pair-sem {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} df dg x =
    trans (⟦⟧-substΨ E
                        (⊢let df (⊢let (wk-⊢′ _ dg)
                          (⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff (·p-diag π) (⊢pair (⊢app (⊢var (suc (suc zero))) (⊢var zero))
                                                                 (⊢app (⊢var (suc zero)) (⊢var zero)))))))
                        δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x))
                 (λ vf → bindC (trans (RS.wk-sem fmt δ _ dg _)
                                      (cong (GM.⟦ dg ⟧ fmt δ) (env-subst₂ {Γ = Γ} _ _ E (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x)))
                               (λ vg → extensionality λ a →
                                  trans (cong (subM (·p-diag π))
                                          (cong₂ (λ m n → bindᵍ π π m λ b → fmapM π (λ c → (b , c)) n)
                                                 (trans (>>=ᵖ-β vf _) (>>=ᵖ-β a _))
                                                 (trans (>>=ᵖ-β vg _) (>>=ᵖ-β a _))))
                                        (diag-bind π (vf a) _))))
    where E = pair-use {Δ = Δ} Ψ₁ Ψ₂

  case-arm : ∀ {A B C : Ty 0} {π} (vf : ⟦ A ⟧ᵛ → M π ⟦ C ⟧ᵛ) (vg : ⟦ B ⟧ᵛ → M π ⟦ C ⟧ᵛ) (ab : ⟦ A ⟧ᵛ Data.Sum.⊎ ⟦ B ⟧ᵛ)
           → [ (λ a → vf >>=ᵖ λ f → a >>=ᵖ λ y → f y)
             , (λ b → vg >>=ᵖ λ g → b >>=ᵖ λ y → g y) ]′ ab
             ≡ [ vf , vg ]′ ab
  case-arm vf vg (inj₁ a) = trans (>>=ᵖ-β vf _) (>>=ᵖ-β a _)
  case-arm vf vg (inj₂ b) = trans (>>=ᵖ-β vg _) (>>=ᵖ-β b _)

  case-sem : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n} {A B C : Ty 0} {π} {f g}
    (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] C ! pure) (dg : Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ B ⇒[ mk-kind Many π ] C ! pure)
    (x : GM.Env Γ (Ψ₁ +ᵘ Ψ₂))
    → GM.⟦ ⊢caseᶜ df dg ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x) >>=ᵖ λ vf →
         GM.⟦ dg ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x) >>=ᵖ λ vg →
         returnᵖ (λ ab → [ vf , vg ]′ ab))
  case-sem {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} df dg x =
    trans (⟦⟧-substΨ E
                        (⊢let df (⊢let (wk-⊢′ _ dg)
                          (⊢lam (≤qᵇ→≤q _ _ refl) (⊢case⊔ (⊢var zero)
                                            (⊢app (⊢var (suc (suc (suc zero)))) (⊢var zero))
                                            (⊢app (⊢var (suc (suc zero))) (⊢var zero))))))
                        δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x))
                 (λ vf → bindC (trans (RS.wk-sem fmt δ _ dg _)
                                      (cong (GM.⟦ dg ⟧ fmt δ) (env-subst₂ {Γ = Γ} _ _ E (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x)))
                               (λ vg → extensionality λ ab →
                                  trans (>>=ᵖ-β ab _)
                                        (case-arm {A = A} {B = B} {C = C} {π = π} vf vg ab))))
    where E = case-use {Δ = Δ} Ψ₁ Ψ₂

  curry-sem : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A B C : Ty 0} {π₀ π} {f}
    (u₀ : pure ⊑π π₀) (df : Δ ⊩ Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many π ] C ! pure) (x : GM.Env Γ Ψ)
    → GM.⟦ ⊢curryᶜ u₀ df ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ x >>=ᵖ λ vf → λ a → returnM u₀ (λ b → vf (a , b)))
  curry-sem {Γ = Γ} {Ψ = Ψ} {π₀ = π₀} {π = π} u₀ df x =
    trans (⟦⟧-substΨ E
                        (⊢let df (⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff u₀
                          (⊢lam (≤qᵇ→≤q _ _ refl) (⊢app (⊢var (suc (suc zero))) (⊢pair (⊢var (suc zero)) (⊢var zero)))))))
                        δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-refl Ψ) x ∙ EA.restrict-refl {Γ = Γ} (⊑ᵘ-refl Ψ) x))
                 (λ vf → extensionality λ a → cong (subM u₀) (extensionality λ b →
                    trans (>>=ᵖ-β vf _)
                          (trans (cong (λ m → m >>=ᵖ (λ y → vf y))
                                       (>>=ᵖ-β a _))
                                 (>>=ᵖ-β (a , b) _)))))
    where E = curry-use {Δ = Δ} Ψ
          _∙_ = trans

  -- A closed combinator whose meaning is `returnᵖ F`, applied: its argument, bound into `F`.
  appC-sem : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A B : Ty 0} {c t} (F : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ)
    (dc : Δ ⊩ Γ ⊢[ zeroUsage ] c ∷ A ⇒[ mk-kind Many pure ] B ! pure)
    (hc : ∀ y → GM.⟦ dc ⟧ fmt δ y ≡ returnᵖ F)
    (dt : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! pure) (x : GM.Env Γ (zeroUsage +ᵘ Many *ᵘ Ψ))
    → GM.⟦ ⊢app dc dt ⟧ fmt δ x
      ≡ (GM.⟦ dt ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))) x) >>=ᵖ F)
  appC-sem {Γ = Γ} {Ψ = Ψ} F dc hc dt x rewrite hc (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ zeroUsage (Many *ᵘ Ψ)) x) = >>=ᵖ-β F _

  apply-sem : ∀ {n} {Γ : Ctx 0 n} {A B : Ty 0} (x : GM.Env Γ zeroUsage)
    → GM.⟦ ⊢applyᶜ {Δ = Δ} {Γ = Γ} {A = A} {B = B} ⟧ fmt δ x ≡ returnᵖ (λ fa → proj₁ fa (proj₂ fa))
  apply-sem {Γ = Γ} x =
    trans (⟦⟧-substΨ {Γ = Γ} (z+qz {Δ = Δ} Many) (⊢lam (≤qᵇ→≤q _ _ refl) (⊢app (⊢fst (⊢var zero)) (⊢snd (⊢var zero)))) δ x)
          (extensionality λ fa → trans (>>=ᵖ-β _ _) (>>=ᵖ-β _ _))

  -- The transport under a binder used once.
  substΨ1 : ∀ {n} {Γ : Ctx 0 n} {X : Ty 0} {U U' : Usage n} {B : Ty 0} {t π} (e : U ≡ U')
    (d : Δ ⊩ (Γ ▸ X) ⊢[ One ∷ U ] t ∷ B ! π) (x : GM.Env Γ U') (a : ⟦ X ⟧ᵛ)
    → GM.⟦ subst (λ V → Δ ⊩ (Γ ▸ X) ⊢[ One ∷ V ] t ∷ B ! π) e d ⟧ fmt δ (x , a)
      ≡ GM.⟦ d ⟧ fmt δ (subst (GM.Env Γ) (sym e) x , a)
  substΨ1 refl d x a = refl

  -- plan 0.113 B1: the coalgebra's usage is ω-scaled; it reads `x` restricted.
  ana-sem″ : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {F : Fun 0} {A : Ty 0} {π₀} {π : Finite} {c}
    (u₀ : pure ⊑π π₀) (wf : WFFun Δ F) (dc : Δ ⊩ Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many (fin π) ] ⟦ F ⟧T A ! pure) (x : GM.Env Γ (Many *ᵘ Ψ))
    → GM.⟦ ⊢anaᶜ u₀ wf dc ⟧ fmt δ x
      ≡ (λ a → returnM u₀ (ana-semᵛ π wf (GM.⟦ dc ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-*Many Ψ) x)) a))
  ana-sem″ {Γ = Γ} {Ψ = Ψ} {A = A} {π₀ = π₀} {π = π} u₀ wf dc x =
    extensionality λ a →
      trans (substΨ1 (+ᵘ-identityʳ (Many *ᵘ Ψ))
                     (⊢sub-eff u₀ (⊢unfold wf (wk-⊢′ A dc) (⊢var zero))) x a)
      (cong (subM u₀)
        (trans (>>=ᵖ-β _ _)
            (cong (λ C → ana-semᵛ π wf C a)
                  (trans (RS.wk-sem fmt δ A dc _)
                         (cong (GM.⟦ dc ⟧ fmt δ)
                               (env-subst {Γ = Γ} (+ᵘ-identityʳ (Many *ᵘ Ψ)) _ (⊑ᵘ-*Many Ψ) x))))))

  applyEff-sem : ∀ {n} {Γ : Ctx 0 n} {π} {A B : Ty 0} (x : GM.Env Γ zeroUsage)
    → GM.⟦ ⊢applyEffᶜ {Δ = Δ} {Γ = Γ} {π = π} {A = A} {B = B} ⟧ fmt δ x ≡ returnᵖ (λ fa → returnᵖ (λ _ → proj₁ fa (proj₂ fa)))
  applyEff-sem {Γ = Γ} x =
    trans (⟦⟧-substΨ {Γ = Γ} (z+qz {Δ = Δ} Many)
             (⊢lam (≤qᵇ→≤q _ _ refl) (⊢lam (≤qᵇ→≤q _ _ refl) (⊢app (⊢fst (⊢var (suc zero))) (⊢snd (⊢var (suc zero)))))) δ x)
          (extensionality λ fa → extensionality λ _ → trans (>>=ᵖ-β _ _) (>>=ᵖ-β _ _))

  effApp-sem : ∀ {n} {Γ : Ctx 0 n} {Ψ₁ Ψ₂ : Usage n} {π} {A B : Ty 0} {f t}
    (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! pure) (dx : Δ ⊩ Γ ⊢[ Ψ₂ ] t ∷ A ! pure)
    (x : GM.Env Γ (Ψ₁ +ᵘ Many *ᵘ Ψ₂))
    → GM.⟦ ⊢effAppᶜ df dx ⟧ fmt δ x
      ≡ returnᵖ (λ _ → GM.⟦ df ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x) >>=ᵖ λ vf →
                       GM.⟦ dx ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x) >>=ᵖ λ vx → vf vx)
  effApp-sem {Γ = Γ} df dx x =
    extensionality λ _ →
      cong₂ (λ F X → F >>=ᵖ λ vf → X >>=ᵖ λ vx → vf vx) (RS.wk-sem fmt δ _ df _) (RS.wk-sem fmt δ _ dx _)

  cata-sem′ : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {F : Fun 0} {A : Ty 0} {π} {alg}
    (u : pure ⊑π π) (wf : WFFun Δ F) (da : Δ ⊩ Γ ⊢[ Ψ ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ! pure) (x : GM.Env Γ (Many *ᵘ Ψ))
    → GM.⟦ ⊢cataᶜ wf da ⟧ fmt δ x
      ≡ (GM.⟦ da ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-*Many Ψ) x) >>=ᵖ λ valg → λ v → cata-semᵛ u wf valg v)
  cata-sem′ {Γ = Γ} {Ψ = Ψ} {π = π} u wf da x =
    trans (⟦⟧-substΨ E (⊢let da (⊢lam (≤qᵇ→≤q _ _ refl) (⊢fold wf (⊢var (suc zero)) (⊢var zero)))) δ x)
          (bindC (cong (GM.⟦ da ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-*Many Ψ) x))
                 (λ valg → extensionality λ v → trans (>>=ᵖ-β valg _) (trans (>>=ᵖ-β v _) (cong (λ w → cata-semᵛ w wf valg v) (⊑π-irr (pure-⊑ π) u)))))
    where E = cata-use {Δ = Δ} Ψ

  -- the loop: the round's closure, bound once, then iterated (`Lang.Iterative.loop`).
  loop-sem : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A B : Ty 0} {c}
    (dc : Δ ⊩ Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many act ] (B + A) ! pure) (x : GM.Env Γ (Many *ᵘ Ψ))
    → GM.⟦ ⊢loopᶜ dc ⟧ fmt δ x ≡ (λ a → loop (GM.⟦ dc ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-*Many Ψ) x)) a)
  loop-sem {Γ = Γ} {Ψ = Ψ} dc x =
    trans (⟦⟧-substΨ E (⊢let dc (⊢lam (≤qᵇ→≤q _ _ refl) (⊢iter (⊢var (suc zero)) (⊢var zero)))) δ x)
          (trans (bindC (cong (GM.⟦ dc ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-*Many Ψ) x))
                        (λ vr → extensionality λ a → trans (>>=ᵖ-β vr _) (>>=ᵖ-β a _)))
                 (>>=ᵖ-β _ _))
    where E = loop-use {Δ = Δ} Ψ

------------------------------------------------------------------------
-- The bridge
------------------------------------------------------------------------

open import Once.Internal.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Denotation.Meaning using (EnvRun)

module _ {δ : GM.DefSem} where
  bindC : ∀ {X Y : Set} {a a' : X} {f g : X → Y} → a ≡ a' → (∀ v → f v ≡ g v) → (a >>=ᵖ f) ≡ (a' >>=ᵖ g)
  bindC {a = a} refl h = cong (a >>=ᵖ_) (extensionality h)

  -- A pure bind against the core's map (D311 C2: unary core rules map).
  fmapC : ∀ {X Y : Set} {a a' : X} (f : X → Y) → a ≡ a' → (a >>=ᵖ f) ≡ f a'
  fmapC {a = a} f refl = >>=ᵖ-β a f

  -- A closed pure combinator applied to an argument: the surface binds the
  -- argument into `F`; the core applies the combinator's value `c`, which agrees
  -- with `F` pointwise — one β-step of the pure bind.
  app-comb : ∀ {X Y : Set} {m m' : X} {F : X → Y} (c : X → Y) → (∀ v → c v ≡ F v) → m ≡ m'
           → (m >>=ᵖ F) ≡ (c >>=ᵖ λ vf → m' >>=ᵖ λ vx → vf vx)
  app-comb c hc refl = trans (bindC refl (λ v → sym (hc v))) (sym (>>=ᵖ-β c _))

  -- A binary operation: the surface binds the operands and applies `K`; the
  -- core builds the pair and binds it into `K` — associativity, twice.
  binK : ∀ {X Y Z : Set} {m₁ m₁' : X} {m₂ m₂' : Y} {K : X × Y → Z}
       → m₁ ≡ m₁' → m₂ ≡ m₂'
       → (m₁ >>=ᵖ λ a → m₂ >>=ᵖ λ b → K (a , b))
         ≡ K (m₁' >>=ᵖ λ a → (a , m₂'))
  binK {m₁' = m₁'} {m₂' = m₂'} {K = K} refl refl =
    trans (>>=ᵖ-β m₁' _) (trans (>>=ᵖ-β m₂' _) (sym (cong K (>>=ᵖ-β m₁' _))))

  bridge-d : ∀ {A B : Ty 0} {ctx : NamedCtx 0} {e π Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
             (d : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) (dγ : EnvRun ctx Ψ)
           → ⟦ d ⟧ᵈ fmt ρ dγ ≡ GM.⟦ proj₂ (elabᵈ V d) ⟧ fmt δ dγ

  bridge-i : ∀ {A : Ty 0} {ctx : NamedCtx 0} {e Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
             (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ) (dγ : EnvRun ctx Ψ)
           → ⟦ d ⟧ᵢ fmt ρ dγ ≡ GM.⟦ proj₂ (elabᵢ V d) ⟧ fmt δ dγ

  bridge-c : ∀ {A : Ty 0} {ctx : NamedCtx 0} {e Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
             (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ) (dγ : EnvRun ctx Ψ)
           → ⟦ d ⟧ᶜ fmt ρ dγ ≡ GM.⟦ proj₂ (elabᶜ V d) ⟧ fmt δ dγ

  bridge-c V ag t-id-check             dγ = refl
  bridge-c V ag (t-fst-check {u = u}) dγ = refl
  bridge-c V ag (t-snd-check {u = u}) dγ = refl
  bridge-c V ag t-terminal-morph-check dγ = refl
  bridge-c V ag (t-initial-morph-check {π = π}) dγ = extensionality λ ()
  bridge-c V ag (t-inl-morph-check {u = u}) dγ = refl
  bridge-c V ag (t-inr-morph-check {u = u}) dγ = refl
  bridge-c V ag (t-compose-check-g dg df) dγ =
    trans (bindC (bridge-c V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.compose-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-c V ag (t-compose-check-f wf p dg) dγ =
    trans (bindC (cong ⟦ p ⟧<:ᵛ (bridge-i V ag wf _)) (λ vf → bindC (bridge-c V ag dg _) (λ vg → refl)))
          (sym (Comb.compose-sem {δ = δ} (⊢coerce p (proj₂ (elabᵢ V wf))) (proj₂ (elabᶜ V dg)) dγ))
  bridge-c V ag (t-case-copair-check df dg) dγ =
    trans (bindC (bridge-c V ag df _) (λ vf → bindC (bridge-c V ag dg _) (λ vg → refl)))
          (sym (Comb.case-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg)) dγ))
  bridge-c V ag (t-pair-morph-check df dg) dγ =
    trans (bindC (bridge-c V ag df _) (λ vf → bindC (bridge-c V ag dg _) (λ vg → refl)))
          (sym (Comb.pair-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg)) dγ))
  bridge-c V ag (t-curry-check {u = u} df) dγ =
    trans (bindC (bridge-c V ag df dγ) (λ vf → refl))
          (sym (Comb.curry-sem {δ = δ} u (proj₂ (elabᶜ V df)) dγ))
  bridge-c V ag (t-cata-check {u = u} wf dalg) dγ =
    trans (bindC (bridge-c V ag dalg _) (λ valg → refl))
          (sym (Comb.cata-sem′ {δ = δ} u wf (proj₂ (elabᶜ V dalg)) dγ))
  bridge-c V ag (t-sub d p) dγ = cong ⟦ p ⟧<:ᵛ (bridge-i V ag d dγ)
  bridge-c V ag (t-lam {q = Zero} {q' = Zero} {u = u} le d) dγ = extensionality λ a → cong (subM u) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = One}  {q' = Zero} {u = u} le d) dγ = extensionality λ a → cong (subM u) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Many} {q' = Zero} {u = u} le d) dγ = extensionality λ a → cong (subM u) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = One}  {q' = One} {u = u} le d) dγ = extensionality λ a → cong (subM u) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Many} {q' = One} {u = u} le d) dγ = extensionality λ a → cong (subM u) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Many} {q' = Many} {u = u} le d) dγ = extensionality λ a → cong (subM u) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Zero} {q' = One}  () d) dγ
  bridge-c V ag (t-lam {q = Zero} {q' = Many} () d) dγ
  bridge-c V ag (t-lam {q = One}  {q' = Many} () d) dγ
  bridge-c V ag (t-pair-lit-check da db) dγ =
    bindC (bridge-c V ag da _) (λ a → trans (>>=ᵖ-β _ _) (cong (a ,_) (bridge-c V ag db _)))
  bridge-c V ag (t-In-app-check wf d) dγ = app-comb _ (λ v → refl) (bridge-c V ag d _)
  bridge-c V ag (t-inl-app-check d) dγ = app-comb _ (λ v → refl) (bridge-c V ag d _)
  bridge-c V ag (t-inr-app-check d) dγ = app-comb _ (λ v → refl) (bridge-c V ag d _)
  bridge-c {ctx = ctx} V ag (t-initial-app-check d) dγ = app-comb {F = λ w → ⊥-elim w} _ (λ v → >>=ᵖ-β v (λ w → ⊥-elim w)) (bridge-c V ag d (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ))
  -- D273: the coalgebra lives in the context — no `close`, read at `dγ`.
  bridge-c {ctx = ctx} V ag (t-ana-check {π₀ = π₀} {φ = π} {u = u} wf dcoalg) dγ =
    trans (cong (λ C → λ a → returnM u (ana-semᵛ π wf C a)) (bridge-c V ag dcoalg _))
          (sym (Comb.ana-sem″ {δ = δ} u wf (proj₂ (elabᶜ V dcoalg)) dγ))
  bridge-c {ctx = ctx} V ag (t-loop-check dround) dγ =
    trans (cong (λ C → λ a → loop C a) (bridge-c V ag dround _))
          (sym (Comb.loop-sem {δ = δ} (proj₂ (elabᶜ V dround)) dγ))
  bridge-c {ctx = ctx} V ag (t-apply-check {A = A} {B = B} dp) dγ =
    trans (bindC (bridge-i V ag dp _) (λ fa → refl))
          (sym (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                 (λ y → Comb.apply-sem {δ = δ} {Γ = NamedCtx.debruijn ctx} {A = A} {B = B} y) (proj₂ (elabᵢ V dp)) dγ))
  bridge-c V ag (t-var-poly-instantiate _ _ lp ng ki) dγ =
    trans (Agree.agree-inst ag lp ki) (sym (polyE-sem δ V lp ki dγ))


  bridge-i V ag (t-int n) dγ = refl
  bridge-i V ag (t-float i f l p) dγ = refl
  bridge-i V ag t-unit dγ = refl
  bridge-i V ag t-unit-var dγ = refl
  bridge-i V ag (t-var-local {eV = Once.Internal.Context.svar i} _) dγ = refl
  bridge-i V ag (t-var-resolved {cn = cn} _ wn lk k refl) dγ =
    trans (Agree.agree-resolved ag {cn = cn} lk k) (sym (sigE-sem δ cn k (declares V lk) dγ))
  bridge-i V ag (t-var-own _ lk refl) dγ = trans (Agree.agree-import ag lk) (sym (importE-sem δ (imported V lk) dγ))
  bridge-i V ag (t-var-import _ _ lk k refl) dγ = trans (Agree.agree-import ag lk) (sym (importE-sem δ (imported V lk) dγ))
  bridge-i V ag (t-var-poly-instantiate-infer {schema = sc} {g = g} _ _ lp _ refl) dγ =
    trans (Agree.agree-inst ag lp (ground-kinded sc g)) (sym (polyE-sem δ V lp (ground-kinded sc g) dγ))
  bridge-i V ag (t-annot _ d refl) dγ = bridge-c V ag d dγ
  bridge-i V ag (t-pair da db) dγ = bindC (bridge-i V ag da _) (λ a → trans (>>=ᵖ-β _ _) (cong (a ,_) (bridge-i V ag db _)))
  bridge-i V ag (t-neg d) dγ = fmapC _ (bridge-i V ag d dγ)
  bridge-i V ag (t-neg-float i f l p) dγ = refl
  bridge-i V ag (t-let {q = Zero} d₁ d₂) dγ = bridge-i V ag d₂ _
  bridge-i V ag (t-let {q = One} d₁ d₂) dγ = bindC (bridge-i V ag d₁ _) (λ v → bridge-i V ag d₂ _)
  bridge-i V ag (t-let {q = Many} d₁ d₂) dγ = bindC (bridge-i V ag d₁ _) (λ v → bridge-i V ag d₂ _)
  -- D276: the core arm runs at the join through `⊢sub-use`, i.e. restricted
  -- after binding; the surface binds after restricting. Same environment.
  -- D322: each arm converted into the join, on both sides.
  bridge-i V ag (t-case {ctx = ctx} {A = A} {B = B} {qL = qL} {qR = qR} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} ds dl dr J) dγ =
    bindC (bridge-i V ag ds _)
      (λ { (inj₁ a) → cong ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ
                        (trans (bridge-i V ag dl _)
                            (cong (GM.⟦ proj₂ (elabᵢ V dl) ⟧ fmt δ)
                                  (sym (EA.restrict-bind {Γ = Γc} {A = A} qL qL (⊑ᵘ-keep {Δ = NamedCtx.kinds ctx} qL (Once.Internal.Context.⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)) (Once.Internal.Context.⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) x a))))
         ; (inj₂ b) → cong ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ
                        (trans (bridge-i V ag dr _)
                            (cong (GM.⟦ proj₂ (elabᵢ V dr) ⟧ fmt δ)
                                  (sym (EA.restrict-bind {Γ = Γc} {A = B} qR qR (⊑ᵘ-keep {Δ = NamedCtx.kinds ctx} qR (Once.Internal.Context.⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)) (Once.Internal.Context.⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) x b)))) })
    where Γc = NamedCtx.debruijn ctx
          x  = restrictᵛ {Γ = Γc} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) dγ
  bridge-i V ag (t-binop-arith {op = OpAdd} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith {op = OpSub} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith {op = OpMul} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith {op = OpDiv} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith {op = OpMod} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith {op = OpLt} () _ _) dγ
  bridge-i V ag (t-binop-arith {op = OpLe} () _ _) dγ
  bridge-i V ag (t-binop-arith {op = OpGt} () _ _) dγ
  bridge-i V ag (t-binop-arith {op = OpGe} () _ _) dγ
  bridge-i V ag (t-binop-arith {op = OpEq} () _ _) dγ
  bridge-i V ag (t-binop-arith {op = OpNe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float {op = OpAdd} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float {op = OpSub} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float {op = OpMul} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float {op = OpDiv} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float {op = OpMod} () _ _) dγ
  bridge-i V ag (t-binop-arith-float {op = OpLt} () _ _) dγ
  bridge-i V ag (t-binop-arith-float {op = OpLe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float {op = OpGt} () _ _) dγ
  bridge-i V ag (t-binop-arith-float {op = OpGe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float {op = OpEq} () _ _) dγ
  bridge-i V ag (t-binop-arith-float {op = OpNe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) dγ = binK (fmapC _ (bridge-i V ag d₁ _)) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) dγ = binK (fmapC _ (bridge-i V ag d₁ _)) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) dγ = binK (fmapC _ (bridge-i V ag d₁ _)) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) dγ = binK (fmapC _ (bridge-i V ag d₁ _)) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float-il {op = OpMod} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpLt} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpLe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpGt} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpGe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpEq} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpNe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (fmapC _ (bridge-i V ag d₂ _))
  bridge-i V ag (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (fmapC _ (bridge-i V ag d₂ _))
  bridge-i V ag (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (fmapC _ (bridge-i V ag d₂ _))
  bridge-i V ag (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (fmapC _ (bridge-i V ag d₂ _))
  bridge-i V ag (t-binop-arith-float-ir {op = OpMod} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-ir {op = OpLt} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-ir {op = OpLe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-ir {op = OpGt} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-ir {op = OpGe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-ir {op = OpEq} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-ir {op = OpNe} () _ _) dγ
  bridge-i V ag (t-binop-cmp {op = OpLt} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-cmp {op = OpLe} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-cmp {op = OpGt} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-cmp {op = OpGe} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-cmp {op = OpEq} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-cmp {op = OpNe} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-cmp {op = OpAdd} () _ _) dγ
  bridge-i V ag (t-binop-cmp {op = OpSub} () _ _) dγ
  bridge-i V ag (t-binop-cmp {op = OpMul} () _ _) dγ
  bridge-i V ag (t-binop-cmp {op = OpDiv} () _ _) dγ
  bridge-i V ag (t-binop-cmp {op = OpMod} () _ _) dγ
  bridge-i V ag (t-id-app d) dγ = trans (bridge-i V ag d _) (sym (trans (>>=ᵖ-β _ _) (>>=ᵖ-idʳ _)))
  bridge-i V ag (t-fst-app d) dγ = app-comb _ (λ v → refl) (bridge-i V ag d _)
  bridge-i V ag (t-snd-app d) dγ = app-comb _ (λ v → refl) (bridge-i V ag d _)
  bridge-i {ctx = ctx} V ag (t-terminal-app d) dγ = bindC (bridge-i V ag d (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ)) (λ v → refl)
  bridge-i V ag (t-Out-app-infer wf refl d) dγ = app-comb _ (λ v → >>=ᵖ-β v _) (bridge-i V ag d _)
  bridge-i V ag (t-Out-eff-app-infer wf refl d) dγ = app-comb _ (λ v → cong returnᵖ (extensionality λ _ → >>=ᵖ-β v _)) (bridge-i V ag d _)
  bridge-i {ctx = ctx} V ag (t-apply-app-infer {A = A} {B = B} d) dγ =
    trans (bindC (bridge-i V ag d _) (λ fa → refl))
          (sym (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                 (λ y → Comb.apply-sem {δ = δ} {Γ = NamedCtx.debruijn ctx} {A = A} {B = B} y) (proj₂ (elabᵢ V d)) dγ))
  bridge-i {ctx = ctx} V ag (t-apply-eff-app-infer {A = A} {B = B} {π = π} d) dγ =
    trans (bindC (bridge-i V ag d _) (λ fa → refl))
          (sym (Comb.appC-sem {δ = δ} (λ fa → returnᵖ (λ _ → proj₁ fa (proj₂ fa)))
                 (⊢applyEffᶜ {Γ = NamedCtx.debruijn ctx} {π = π} {A = A} {B = B})
                 (λ y → Comb.applyEff-sem {δ = δ} {Γ = NamedCtx.debruijn ctx} {π = π} {A = A} {B = B} y) (proj₂ (elabᵢ V d)) dγ))
  bridge-i V ag (t-app {q = Zero} _ df dx) dγ = bindC (bridge-i V ag df _) (λ vf → refl)
  bridge-i V ag (t-app {q = One} _ df dx) dγ = bindC (bridge-i V ag df _) (λ vf → bindC (bridge-c V ag dx _) (λ vx → refl))
  bridge-i V ag (t-app {q = Many} _ df dx) dγ = bindC (bridge-i V ag df _) (λ vf → bindC (bridge-c V ag dx _) (λ vx → refl))
  bridge-i V ag (t-effApp _ df dx) dγ =
    trans (cong returnᵖ (extensionality λ _ → bindC (bridge-i V ag df _) (λ vf → bindC (bridge-c V ag dx _) (λ vx → refl))))
          (sym (Comb.effApp-sem {δ = δ} (proj₂ (elabᵢ V df)) (proj₂ (elabᶜ V dx)) dγ))
  bridge-i V ag (t-app-spine _ dx df) dγ = bindC (bridge-d V ag df _) (λ vf → bindC (bridge-i V ag dx _) (λ vx → refl))

  bridge-d V ag (d-infer {B = B} w a g) dγ = cong ⟦ sub-arr {q = Many} a (<:-refl B) g ⟧<:ᵛ (bridge-i V ag w dγ)
  bridge-d V ag (d-poly {A = A} {B = B} _ _ lp ng _ _ ki g) dγ =
    cong ⟦ sub-arr {q = Many} (<:-refl A) (<:-refl B) g ⟧<:ᵛ (trans (Agree.agree-inst ag lp ki) (sym (polyE-sem δ V lp ki dγ)))
  bridge-d V ag (d-lam {q' = Zero} {u = u} d) dγ = extensionality λ a → cong (subM u) (bridge-i V ag d _)
  bridge-d V ag (d-lam {q' = One} {u = u} d) dγ = extensionality λ a → cong (subM u) (bridge-i V ag d _)
  bridge-d V ag (d-lam {q' = Many} {u = u} d) dγ = extensionality λ a → cong (subM u) (bridge-i V ag d _)
  bridge-d V ag (d-compose dg df) dγ =
    trans (bindC (bridge-d V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.compose-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-d V ag d-id dγ = refl
  bridge-d V ag (d-fst {u = u}) dγ = refl
  bridge-d V ag (d-snd {u = u}) dγ = refl
  bridge-d V ag d-terminal dγ = refl
  bridge-d V ag (d-initial {π = π}) dγ = extensionality λ ()
  bridge-d V ag (d-case {A = A} {B = B} {π = π} df dg J) dγ =
    trans (bindC (cong ⟦ pf ⟧<:ᵛ (bridge-d V ag df _)) (λ vf → bindC (cong ⟦ pg ⟧<:ᵛ (bridge-d V ag dg _)) (λ vg → refl)))
          (sym (Comb.case-sem {δ = δ} (⊢coerce pf (proj₂ (elabᵈ V df))) (⊢coerce pg (proj₂ (elabᵈ V dg))) dγ))
    where pf = sub-arr {q = Many} (<:-refl A) (<:ᶜ⇒<: (⊔-left J)) (⊑π-refl π)
          pg = sub-arr {q = Many} (<:-refl B) (<:ᶜ⇒<: (⊔-right J)) (⊑π-refl π)
  bridge-d V ag (d-pair df dg) dγ =
    trans (bindC (bridge-d V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.pair-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-d V ag (d-cata {u = u} wf dalg) dγ =
    trans (bindC (bridge-i V ag dalg _) (λ valg → refl))
          (sym (Comb.cata-sem′ {δ = δ} u wf (proj₂ (elabᵢ V dalg)) dγ))

