-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreMeaningBridge — plan 0.103 6b, step B.2: THE SURFACE
-- MEANING IS THE CORE MEANING OF THE ELABORATION (plan 0.122 §5.5 M4: the
-- Spec's core meaning).
--
--   ⟦ d ⟧ᶜ fmt ρ x ≡ SM.⟦ proj₂ (elabᶜ V d) ⟧ δ σ₀ noResp γ
--
-- clause by clause over the surface judgment, at related environments
-- (`SurfaceEnv.EnvR`: the surface's product of the used values against the
-- Spec's slots), in a surface environment `ρ` that AGREES with the core's
-- `δ` at every reference the View resolves (`Agree`). The derived combinators
-- were written so their evaluation order is the surface clause's
-- (Spec.Core.Derived's header); what the proof spends is the pure bind's
-- β-law, the renaming lemma (`SpecRenameSem.wk-sem`) where a combinator
-- weakens an arm, each of the Spec's environment splits being a restriction
-- (`Coherence.Env`), and the transports the typing proofs carry.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (TySub)

module Once.Adequacy.CoreMeaningBridge (fmt : TargetNum) (Σ : Signature) {s : ℕ} (S : Defs s) (σ₀ : TySub 0 0) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; trans-reflʳ)
open import Once.Spec.Type using (Ty; Type; Fun; KCtx; ∅ₖ; WFFun; Respects; _⟨_⟩; _*_; _+_; _⇒[_]_)
open import Once.Spec.Type.Substitution using (respects-∘; ⟨⟩-∘)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; mk-kind; pure; act; eff; Finite; fin; _⊑π_; ⊑-pure; pureᶠ; actᶠ)
open import Once.Spec.Context using (Ctx; _▸_; _∷_; _⊑∷_; Usage)
open import Once.Spec.Signature using (⌜_⌝ᵈ)
open import Once.Spec.Core.Syntax using (Schema; schema; _!!_; ref)
open Schema using (arity; kinds; type)
open import Once.Internal.Type.Poly using (PolyType)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Internal.Type.Schema using (schemaOf; kinded-instance)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Type using (wk₀; none; noResp)
open import Once.Spec.Type using (⟦_⟧F)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Spec.Name using (CanonicalName)
open import Once.Postulates using (extensionality)
open import Once.Functor.Translate using (Base-irrelevant)
open import Once.Internal.Type.Sub using (·p-diag)
open import Once.Denotation.PureBind using (_>>=ᵖ_; >>=ᵖ-β; >>=ᵖ-idʳ)
open import Once.Internal.Typing.Scope using (NamedCtx; lookupImport; lookupPolyPrefix; Imports; PolyCtx)
open import Once.Internal.Typing
open import Once.Denotation.DefEnv using (defAt; impAt)
import Once.Denotation.Meaning Σ σ₀ as DM
open DM using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵈ; MeaningsOf; Meanings; returnᵖ)
open DM.Meanings using (sigs; defs; entries)
open import Once.Denotation.SpecDomain Σ σ₀
  using (⟦_⟧ᵛ; ⟦wk₀⟧ᵛ; M; bindM; returnM; subM; fmapM; cata-semᵛ; ana-semᵛ; ⟦_⟧<:ᵛ; loop; restrictᵛ; bindᵛ)
open import Once.Internal.Core.Decl using (declS; ⌜declS⌝)
import Once.Spec.Domain Σ as SD
import Once.Spec.Effect Σ as SE
import Once.Spec.Core.Meaning Σ fmt S as SM
open SM using (DefSem; Env; envˡ; envʳ; env*One; env*Many; restrict; slot)
open import Once.Metatheory.Coherence.Env Σ fmt S
  using (envˡ-restrict; envʳ-restrict; env*One-envʳ-restrict; env*Many-envʳ-restrict; env*Many-envˡ-restrict)
open import Once.Spec.Core.Typing Σ S
open import Once.Internal.Elaboration Σ S
  using (Views; View; ImportAt; Declared; declared; def; elabᶜ; elabᵢ; elabᵈ; Elab; refAt; sigE; importE; polyE; retypeD; retypeE)
open View
open import Once.Adequacy.SurfaceEnv Σ fmt S σ₀
import Once.Adequacy.SpecRenameSem Σ fmt S as RS
import Once.Denotation.EnvAlgebraV Σ σ₀ as EA

------------------------------------------------------------------------
-- The core meaning at the instance
------------------------------------------------------------------------

⟦_⟧ₛ : ∀ {Δ : KCtx 0} {n} {Γ : Ctx 0 n} {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → DefSem → Env σ₀ Γ Ψ → M π ⟦ A ⟧ᵛ
⟦ D ⟧ₛ δ γ = SM.⟦ D ⟧ δ σ₀ noResp γ

------------------------------------------------------------------------
-- The references' meanings
------------------------------------------------------------------------

-- An entry of the table at a kind-respecting instance of its schema: the
-- Spec's reference, at the instance.
refSemAt : (δ : DefSem) (d : Fin s) {sc : Schema} → S !! d ≡ sc → (τ : TySub (arity sc) 0) {Δ : KCtx 0}
         → Respects (kinds sc) Δ τ → ⟦ type sc ⟨ τ ⟩ ⟧ᵛ
refSemAt δ d refl τ {Δ} r =
  subst SD.⟦_⟧ᵛ (sym (⟨⟩-∘ (type (S !! d)) τ σ₀)) (SM.DefSem.defs δ d (λ i → τ i ⟨ σ₀ ⟩) (respects-∘ r (noResp {σ₀} {Δ})))

-- The meaning of an entry does not depend on the kinds it is read at: over
-- no variable there is one kind context, and `Respects` is a proposition.
refSemAt-Δ : (δ : DefSem) (d : Fin s) {sc : Schema} (e : S !! d ≡ sc) (τ : TySub (arity sc) 0) {Δ Δ′ : KCtx 0}
             (r : Respects (kinds sc) Δ τ) (r′ : Respects (kinds sc) Δ′ τ) → refSemAt δ d e τ r ≡ refSemAt δ d e τ r′
refSemAt-Δ δ d refl τ r r′ =
  cong (λ q → subst SD.⟦_⟧ᵛ (sym (⟨⟩-∘ (type (S !! d)) τ σ₀)) (SM.DefSem.defs δ d (λ i → τ i ⟨ σ₀ ⟩) q))
       (extensionality λ i → extensionality λ e → Base-irrelevant _ _)

-- An entry at a kinded instance of a telescope definition's schema.
entrySem : (δ : DefSem) (d : Fin s) {sc : PolyType} → S !! d ≡ schemaOf sc → {Δ : KCtx 0} {U : Ty 0}
         → KindedInstance Δ sc U → ⟦ U ⟧ᵛ
entrySem δ d {sc} e ki =
  subst (λ X → ⟦ X ⟧ᵛ) (proj₂ (proj₂ (kinded-instance sc ki)))
        (refSemAt δ d e (proj₁ (kinded-instance sc ki)) (proj₁ (proj₂ (kinded-instance sc ki))))

-- A telescope definition at a kinded instance (the instance `polyE` computes).
polySem : ∀ {imps sg polys} (δ : DefSem) (V : View imps sg polys) {x sc body prefix} {Δ : KCtx 0} {U : Ty 0}
        → (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix)) → KindedInstance Δ sc U → ⟦ U ⟧ᵛ
polySem δ V {sc = sc} lp ki = entrySem δ (entry V lp) {sc} (entryIs V lp) ki

-- …a monomorphic definition, at its ground type…
impSem : (δ : DefSem) {Δ : KCtx 0} {x : String} {T : Type} → ImportAt x T → ⟦ wk₀ {0} T ⟧ᵛ
impSem δ {Δ} (def d mono) = refSemAt δ d mono none {Δ = Δ} (λ ())

-- …and a generator of Σ (D274: an FFI declaration is not a definition): the
-- Spec's reference to its declaration, read in the world's model or the
-- Spec's call.
sigSem : (δ : DefSem) (c : CanonicalName) {T : Type} → WordName c → IsConcrete T → Declared (showCanonical c) T → ⟦ wk₀ {0} T ⟧ᵛ
sigSem δ c {T} wn k (declared h mem) =
  subst (λ X → ⟦ X ⟧ᵛ) (⌜declS⌝ k h) (SM.sigopᵛ σ₀ c (declS T) (mem {c} wn refl) (SM.DefSem.model δ))

------------------------------------------------------------------------
-- The environment agreement
------------------------------------------------------------------------

-- `ρ` agrees with `δ` at every reference the View resolves.
record Agree {imps sg : Imports} {polys : PolyCtx} (V : View imps sg polys) (ρ : Meanings polys imps sg) (δ : DefSem) : Set where
  field
    agree-inst : ∀ {Δ : KCtx 0} {x sc body prefix U} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
                   (ki : KindedInstance Δ sc U)
               → defAt polys x (defs ρ) lp U ki ≡ polySem δ V lp ki
    agree-import : ∀ {Δ : KCtx 0} {x T} (lk : lookupImport imps x ≡ just T)
                 → subst id (sym (⟦wk₀⟧ᵛ T)) (impAt imps x (entries ρ) lk) ≡ impSem δ {Δ} (imported V lk)
    -- a resolved reference names a generator of Σ: both meanings read the same
    -- declaration.
    agree-resolved : ∀ {cn T} (wn : WordName cn) (lk : lookupImport sg (showCanonical cn) ≡ just T) (k : IsConcrete T)
                   → subst id (sym (⟦wk₀⟧ᵛ T)) (sigs ρ {cn = cn} wn lk k) ≡ sigSem δ cn wn k (declares V lk)

------------------------------------------------------------------------
-- The references' core meanings
------------------------------------------------------------------------

module _ {Δ : KCtx 0} {n} {Γ : Ctx 0 n} (δ : DefSem) where

  ⟦⟧-retypeD : ∀ {Ψ t A B π} (e : A ≡ B) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (γ : Env σ₀ Γ Ψ)
             → ⟦ retypeD e d ⟧ₛ δ γ ≡ subst (λ X → M π ⟦ X ⟧ᵛ) e (⟦ d ⟧ₛ δ γ)
  ⟦⟧-retypeD refl d γ = refl

  ⟦⟧-retypeE : ∀ {Ψ A B} (e : A ≡ B) (el : Elab Δ Γ Ψ A) (γ : Env σ₀ Γ Ψ)
             → ⟦ proj₂ (retypeE e el) ⟧ₛ δ γ ≡ subst (λ X → ⟦ X ⟧ᵛ) e (⟦ proj₂ el ⟧ₛ δ γ)
  ⟦⟧-retypeE refl el γ = refl

  refAt-sem : (d : Fin s) {sc : Schema} (e : S !! d ≡ sc) (τ : TySub (arity sc) 0) (r : Respects (kinds sc) Δ τ) (γ : Env σ₀ Γ _)
            → ⟦ proj₂ (refAt {Γ = Γ} d e τ r) ⟧ₛ δ γ ≡ refSemAt δ d e τ r
  refAt-sem d refl τ r γ = refl

  polyE-sem : ∀ {imps sg polys} (V : View imps sg polys) {x sc body prefix U}
                (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix)) (ki : KindedInstance Δ sc U) (γ : Env σ₀ Γ _)
            → ⟦ proj₂ (polyE {Γ = Γ} V lp ki) ⟧ₛ δ γ ≡ polySem δ V lp ki
  polyE-sem V {sc = sc} lp ki γ =
    trans (⟦⟧-retypeE (proj₂ (proj₂ (kinded-instance sc ki))) _ γ)
          (cong (subst (λ X → ⟦ X ⟧ᵛ) (proj₂ (proj₂ (kinded-instance sc ki))))
                (refAt-sem (entry V lp) (entryIs V lp) _ _ γ))

  importE-sem : ∀ {x T} (i : ImportAt x T) (γ : Env σ₀ Γ _) → ⟦ proj₂ (importE {Γ = Γ} i refl) ⟧ₛ δ γ ≡ impSem δ {Δ} i
  importE-sem (def d mono) γ = refAt-sem d mono none (λ ()) γ

  sigE-sem : ∀ (c : CanonicalName) {T} (wn : WordName c) (k : IsConcrete T) (D : Declared (showCanonical c) T) (γ : Env σ₀ Γ _)
           → ⟦ proj₂ (sigE {Γ = Γ} c wn k D refl) ⟧ₛ δ γ ≡ sigSem δ c wn k D
  sigE-sem c {T} wn k (declared h mem) γ =
    trans (⟦⟧-retypeD (trans (⌜declS⌝ k h) refl) _ γ)
          (cong (λ e → subst (λ X → ⟦ X ⟧ᵛ) e (SM.sigopᵛ σ₀ c (declS T) (mem {c} wn refl) (SM.DefSem.model δ)))
                (trans-reflʳ (⌜declS⌝ k h)))

------------------------------------------------------------------------
-- The pure bind
------------------------------------------------------------------------

β2 : ∀ {X Y Z : Set} (m : X) (n : Y) (k : X → Y → Z) → (m >>=ᵖ λ a → n >>=ᵖ λ b → k a b) ≡ k m n
β2 m n k = trans (>>=ᵖ-β m _) (>>=ᵖ-β n _)

-- A binary operation: the surface binds the operands and applies `K`; the
-- core applies it to the pair.
binK : ∀ {X Y Z : Set} {m₁ m₁' : X} {m₂ m₂' : Y} {K : X × Y → Z}
     → m₁ ≡ m₁' → m₂ ≡ m₂' → (m₁ >>=ᵖ λ a → m₂ >>=ᵖ λ b → K (a , b)) ≡ K (m₁' , m₂')
binK {m₁' = m₁'} {m₂' = m₂'} {K = K} refl refl = β2 m₁' m₂' (λ a b → K (a , b))

-- A unary operation.
fmapC : ∀ {X Y : Set} {a a' : X} (f : X → Y) → a ≡ a' → (a >>=ᵖ f) ≡ f a'
fmapC {a = a} f refl = >>=ᵖ-β a f

-- An application.
appC : ∀ {X Y : Set} {f f′ : X → Y} {a a′ : X} → f ≡ f′ → a ≡ a′ → (f >>=ᵖ λ vf → a >>=ᵖ λ vx → vf vx) ≡ f′ a′
appC {f = f} {a = a} refl refl = β2 f a (λ vf vx → vf vx)

-- A shared grade read as the product of two (D311): the diagonal's bind.
diag-bind : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y) → subM (·p-diag π) (SE.bindᵍ π π m k) ≡ bindM π m k
diag-bind pure m k = refl
diag-bind eff  m k = refl
diag-bind act  m k = refl

------------------------------------------------------------------------
-- The derived combinators' meanings (one lemma per combinator), over related
-- environments, given their arms' bridges.
------------------------------------------------------------------------

open import Once.Internal.Context using (_+ᵘ_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*Many; ⊑ᵘ-*One; zeroUsage; _⊑ᵘ_; _⊔ᵘ_; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-refl)
open import Once.Spec.Sub using (sub-arr; _⊔_≔_)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open _⊔_≔_ using () renaming (left to ⊔-left; right to ⊔-right)
open import Once.Internal.Core.DerivedTyping Σ S
open import Once.Type.Grade using (≤qᵇ→≤q)
open import Once.Surface.Properties using (+ᵘ-identityʳ)

-- A usage transport on a derivation is a transport on its environment.
⟦⟧-substΨ : ∀ {Δ : KCtx 0} {n} {Γ : Ctx 0 n} {Ψ Ψ′ : Usage n} {A : Ty 0} {t π} (e : Ψ ≡ Ψ′)
              (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (δ : DefSem) (γ : Env σ₀ Γ Ψ′)
          → ⟦ subst (λ U → Δ ⊩ Γ ⊢[ U ] t ∷ A ! π) e d ⟧ₛ δ γ ≡ ⟦ d ⟧ₛ δ (subst (Env σ₀ Γ) (sym e) γ)
⟦⟧-substΨ refl d δ γ = refl

module Comb {Δ : KCtx 0} {δ : DefSem} {n} {Γ : Ctx 0 n} where

  -- An arm's bridge: related environments give equal meanings.
  Arm : ∀ {Ψ : Usage n} {X : Set} → (EA.Env Γ Ψ → X) → (Env σ₀ Γ Ψ → X) → Set
  Arm {Ψ} F G = ∀ {x γ} → EnvR Γ Ψ x γ → F x ≡ G γ

  -- A closed combinator whose meaning is `F`, applied: its argument, bound into `F`.
  appC-sem : ∀ {Ψ : Usage n} {A B : Ty 0} {c t} (F : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ)
    (dc : Δ ⊩ Γ ⊢[ zeroUsage ] c ∷ A ⇒[ mk-kind Many pure ] B ! pure)
    (hc : ∀ y → ⟦ dc ⟧ₛ δ y ≡ F)
    (dt : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! pure) (T : EA.Env Γ Ψ → ⟦ A ⟧ᵛ) → Arm T (⟦ dt ⟧ₛ δ)
    → Arm {zeroUsage +ᵘ Many *ᵘ Ψ}
          (λ x → T (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))) x) >>=ᵖ F)
          (⟦ ⊢app dc dt ⟧ₛ δ)
  appC-sem {Ψ = Ψ} F dc hc dt T hT {x} {γ} r =
    trans (>>=ᵖ-β _ F)
          (cong₂ (λ f v → f v) (sym (hc _))
                 (hT (split-R′ {Γ = Γ} _ _ (λ y → env*Many σ₀ Ψ (envʳ σ₀ zeroUsage (Many *ᵘ Ψ) y))
                               (env*Many-envʳ-restrict σ₀ zeroUsage Ψ) r)))

  compose-sem : ∀ {Ψ₁ Ψ₂ : Usage n} {A B C : Ty 0} {π} {f g}
    (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ B ⇒[ mk-kind Many π ] C ! pure) (dg : Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π ] B ! pure)
    (F : EA.Env Γ Ψ₁ → ⟦ B ⇒[ mk-kind Many π ] C ⟧ᵛ) (G : EA.Env Γ Ψ₂ → ⟦ A ⇒[ mk-kind Many π ] B ⟧ᵛ)
    → Arm F (⟦ df ⟧ₛ δ) → Arm G (⟦ dg ⟧ₛ δ)
    → Arm {Ψ₁ +ᵘ Many *ᵘ Ψ₂}
          (λ x → F (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x) >>=ᵖ λ vf →
                 G (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x) >>=ᵖ λ vg →
                 λ a → bindM π (vg a) vf)
          (⟦ ⊢composeᶜ (·p-diag π) df dg ⟧ₛ δ)
  compose-sem {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} df dg F G hF hG {x} {γ} r =
    trans (β2 _ _ (λ vf vg → λ a → bindM π (vg a) vf))
      (trans (cong₂ (λ vf vg → λ a → bindM π (vg a) vf)
                    (hF (split-R {Γ = Γ} E (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) _ fX (env*One-envʳ-restrict σ₀ ZΨ Ψ₁) r))
                    (hG (split-R {Γ = Γ} E (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) _ fY eY r)))
             (sym (trans (⟦⟧-substΨ E D δ γ)
                         (extensionality λ a →
                            trans (cong (λ W → SE.sub (·p-diag π) (SE.bindᵍ π π (W a) (λ y → ⟦ df ⟧ₛ δ (fX γ′) y)))
                                        (RS.wk-sem σ₀ δ noResp (B ⇒[ mk-kind Many π ] C) dg _))
                                  (diag-bind π _ _)))))
    where
      E  = compose-use {Δ = Δ} Ψ₁ Ψ₂
      Z  = zeroUsage {n} +ᵘ Many *ᵘ (zeroUsage +ᵘ Many *ᵘ zeroUsage)
      ZΨ = Z +ᵘ Many *ᵘ Ψ₂
      γ′ = subst (Env σ₀ Γ) (sym E) γ
      fX : Env σ₀ Γ (ZΨ +ᵘ One *ᵘ Ψ₁) → Env σ₀ Γ Ψ₁
      fX y = env*One σ₀ Ψ₁ (envʳ σ₀ ZΨ (One *ᵘ Ψ₁) y)
      fY : Env σ₀ Γ (ZΨ +ᵘ One *ᵘ Ψ₁) → Env σ₀ Γ Ψ₂
      fY y = env*Many σ₀ Ψ₂ (envʳ σ₀ Z (Many *ᵘ Ψ₂) (envˡ σ₀ ZΨ (One *ᵘ Ψ₁) y))
      eY : ∀ y → fY y ≡ restrict σ₀ _ y
      eY y = trans (cong (λ w → env*Many σ₀ Ψ₂ (envʳ σ₀ Z (Many *ᵘ Ψ₂) w)) (envˡ-restrict σ₀ ZΨ (One *ᵘ Ψ₁) y))
                   (trans (env*Many-envʳ-restrict σ₀ Z Ψ₂ _) (RS.restrict-∘ σ₀ _ _ y))
      D = ⊢let df (⊢let (wk-⊢′ (B ⇒[ mk-kind Many π ] C) dg)
            (⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff (·p-diag π) (⊢app (⊢var (suc (suc zero))) (⊢app (⊢var (suc zero)) (⊢var zero))))))

  pair-sem : ∀ {Ψ₁ Ψ₂ : Usage n} {A B C : Ty 0} {π} {f g}
    (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! pure) (dg : Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π ] C ! pure)
    (F : EA.Env Γ Ψ₁ → ⟦ A ⇒[ mk-kind Many π ] B ⟧ᵛ) (G : EA.Env Γ Ψ₂ → ⟦ A ⇒[ mk-kind Many π ] C ⟧ᵛ)
    → Arm F (⟦ df ⟧ₛ δ) → Arm G (⟦ dg ⟧ₛ δ)
    → Arm {Ψ₁ +ᵘ Ψ₂}
          (λ x → F (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x) >>=ᵖ λ vf →
                 G (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x) >>=ᵖ λ vg →
                 λ a → bindM π (vf a) λ b → fmapM π (λ c → (b , c)) (vg a))
          (⟦ ⊢pairᶜ (·p-diag π) df dg ⟧ₛ δ)
  pair-sem {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} df dg F G hF hG {x} {γ} r =
    trans (β2 _ _ (λ vf vg → λ a → bindM π (vf a) λ b → fmapM π (λ c → (b , c)) (vg a)))
      (trans (cong₂ (λ vf vg → λ a → bindM π (vf a) λ b → fmapM π (λ c → (b , c)) (vg a))
                    (hF (split-R {Γ = Γ} E (⊑ᵘ-+ˡ Ψ₁ Ψ₂) _ fX (env*One-envʳ-restrict σ₀ ZΨ Ψ₁) r))
                    (hG (split-R {Γ = Γ} E (⊑ᵘ-+ʳ Ψ₁ Ψ₂) _ fY eY r)))
             (sym (trans (⟦⟧-substΨ E D δ γ)
                         (extensionality λ a →
                            trans (cong (λ W → SE.sub (·p-diag π) (SE.bindᵍ π π (⟦ df ⟧ₛ δ (fX γ′) a) (λ b → SE.fmap π (λ c → (b , c)) (W a))))
                                        (RS.wk-sem σ₀ δ noResp (A ⇒[ mk-kind Many π ] B) dg _))
                                  (diag-bind π _ _)))))
    where
      E  = pair-use {Δ = Δ} Ψ₁ Ψ₂
      Z  = (zeroUsage {n} +ᵘ Many *ᵘ zeroUsage) +ᵘ (zeroUsage +ᵘ Many *ᵘ zeroUsage)
      ZΨ = Z +ᵘ One *ᵘ Ψ₂
      γ′ = subst (Env σ₀ Γ) (sym E) γ
      fX : Env σ₀ Γ (ZΨ +ᵘ One *ᵘ Ψ₁) → Env σ₀ Γ Ψ₁
      fX y = env*One σ₀ Ψ₁ (envʳ σ₀ ZΨ (One *ᵘ Ψ₁) y)
      fY : Env σ₀ Γ (ZΨ +ᵘ One *ᵘ Ψ₁) → Env σ₀ Γ Ψ₂
      fY y = env*One σ₀ Ψ₂ (envʳ σ₀ Z (One *ᵘ Ψ₂) (envˡ σ₀ ZΨ (One *ᵘ Ψ₁) y))
      eY : ∀ y → fY y ≡ restrict σ₀ _ y
      eY y = trans (cong (λ w → env*One σ₀ Ψ₂ (envʳ σ₀ Z (One *ᵘ Ψ₂) w)) (envˡ-restrict σ₀ ZΨ (One *ᵘ Ψ₁) y))
                   (trans (env*One-envʳ-restrict σ₀ Z Ψ₂ _) (RS.restrict-∘ σ₀ _ _ y))
      D = ⊢let df (⊢let (wk-⊢′ (A ⇒[ mk-kind Many π ] B) dg)
            (⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff (·p-diag π) (⊢pair (⊢app (⊢var (suc (suc zero))) (⊢var zero))
                                                                    (⊢app (⊢var (suc zero)) (⊢var zero))))))

  case-sem : ∀ {Ψ₁ Ψ₂ : Usage n} {A B C : Ty 0} {π} {f g}
    (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] C ! pure) (dg : Δ ⊩ Γ ⊢[ Ψ₂ ] g ∷ B ⇒[ mk-kind Many π ] C ! pure)
    (F : EA.Env Γ Ψ₁ → ⟦ A ⇒[ mk-kind Many π ] C ⟧ᵛ) (G : EA.Env Γ Ψ₂ → ⟦ B ⇒[ mk-kind Many π ] C ⟧ᵛ)
    → Arm F (⟦ df ⟧ₛ δ) → Arm G (⟦ dg ⟧ₛ δ)
    → Arm {Ψ₁ +ᵘ Ψ₂}
          (λ x → F (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x) >>=ᵖ λ vf →
                 G (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x) >>=ᵖ λ vg →
                 returnᵖ (λ ab → [ vf , vg ]′ ab))
          (⟦ ⊢caseᶜ df dg ⟧ₛ δ)
  case-sem {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} df dg F G hF hG {x} {γ} r =
    trans (β2 _ _ (λ vf vg → λ ab → [ vf , vg ]′ ab))
      (trans (cong₂ (λ vf vg → λ ab → [ vf , vg ]′ ab)
                    (hF (split-R {Γ = Γ} E (⊑ᵘ-+ˡ Ψ₁ Ψ₂) _ fX (env*One-envʳ-restrict σ₀ ZΨ Ψ₁) r))
                    (hG (split-R {Γ = Γ} E (⊑ᵘ-+ʳ Ψ₁ Ψ₂) _ fY eY r)))
             (sym (trans (⟦⟧-substΨ E D δ γ)
                         (cong (λ W → λ ab → [ (λ a → ⟦ df ⟧ₛ δ (fX γ′) a) , (λ b → W b) ]′ ab)
                               (RS.wk-sem σ₀ δ noResp (A ⇒[ mk-kind Many π ] C) dg _)))))
    where
      E  = case-use {Δ = Δ} Ψ₁ Ψ₂
      Z  = zeroUsage {n} +ᵘ ((zeroUsage +ᵘ Many *ᵘ zeroUsage) ⊔ᵘ (zeroUsage +ᵘ Many *ᵘ zeroUsage))
      ZΨ = Z +ᵘ One *ᵘ Ψ₂
      γ′ = subst (Env σ₀ Γ) (sym E) γ
      fX : Env σ₀ Γ (ZΨ +ᵘ One *ᵘ Ψ₁) → Env σ₀ Γ Ψ₁
      fX y = env*One σ₀ Ψ₁ (envʳ σ₀ ZΨ (One *ᵘ Ψ₁) y)
      fY : Env σ₀ Γ (ZΨ +ᵘ One *ᵘ Ψ₁) → Env σ₀ Γ Ψ₂
      fY y = env*One σ₀ Ψ₂ (envʳ σ₀ Z (One *ᵘ Ψ₂) (envˡ σ₀ ZΨ (One *ᵘ Ψ₁) y))
      eY : ∀ y → fY y ≡ restrict σ₀ _ y
      eY y = trans (cong (λ w → env*One σ₀ Ψ₂ (envʳ σ₀ Z (One *ᵘ Ψ₂) w)) (envˡ-restrict σ₀ ZΨ (One *ᵘ Ψ₁) y))
                   (trans (env*One-envʳ-restrict σ₀ Z Ψ₂ _) (RS.restrict-∘ σ₀ _ _ y))
      D = ⊢let df (⊢let (wk-⊢′ (A ⇒[ mk-kind Many π ] C) dg)
            (⊢lam (≤qᵇ→≤q _ _ refl) (⊢case⊔ (⊢var zero)
                              (⊢app (⊢var (suc (suc (suc zero)))) (⊢var zero))
                              (⊢app (⊢var (suc (suc zero))) (⊢var zero)))))

  curry-sem : ∀ {Ψ : Usage n} {A B C : Ty 0} {π₀ π} {f}
    (u₀ : pure ⊑π π₀) (df : Δ ⊩ Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many π ] C ! pure)
    (F : EA.Env Γ Ψ → ⟦ (A * B) ⇒[ mk-kind Many π ] C ⟧ᵛ) → Arm F (⟦ df ⟧ₛ δ)
    → Arm {Ψ} (λ x → F x >>=ᵖ λ vf → λ a → returnM u₀ (λ b → vf (a , b))) (⟦ ⊢curryᶜ u₀ df ⟧ₛ δ)
  curry-sem {Ψ = Ψ} {A = A} {B = B} {C = C} {π₀ = π₀} {π = π} u₀ df F hF {x} {γ} r =
    trans (>>=ᵖ-β _ _)
      (trans (cong (λ vf → λ a → returnM u₀ (λ b → vf (a , b)))
                   (hF (subst (λ z → EnvR Γ Ψ z (fX γ′)) (EA.restrict-refl {Γ = Γ} (⊑ᵘ-refl Ψ) x)
                              (split-R {Γ = Γ} E (⊑ᵘ-refl Ψ) _ fX (env*One-envʳ-restrict σ₀ Z Ψ) r))))
             (sym (⟦⟧-substΨ E D δ γ)))
    where
      E  = curry-use {Δ = Δ} Ψ
      Z  = zeroUsage {n} +ᵘ Many *ᵘ (zeroUsage +ᵘ zeroUsage)
      γ′ = subst (Env σ₀ Γ) (sym E) γ
      fX : Env σ₀ Γ (Z +ᵘ One *ᵘ Ψ) → Env σ₀ Γ Ψ
      fX y = env*One σ₀ Ψ (envʳ σ₀ Z (One *ᵘ Ψ) y)
      D = ⊢let df (⊢lam (≤qᵇ→≤q _ _ refl) (⊢sub-eff u₀
            (⊢lam (≤qᵇ→≤q _ _ refl) (⊢app (⊢var (suc (suc zero))) (⊢pair (⊢var (suc zero)) (⊢var zero))))))

  cata-sem′ : ∀ {Ψ : Usage n} {F : Fun 0} {A : Ty 0} {π} {alg}
    (u : pure ⊑π π) (wf : WFFun Δ F) (da : Δ ⊩ Γ ⊢[ Ψ ] alg ∷ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ! pure)
    (Alg : EA.Env Γ Ψ → ⟦ ⟦ F ⟧F A ⇒[ mk-kind Many π ] A ⟧ᵛ) → Arm Alg (⟦ da ⟧ₛ δ)
    → Arm {Many *ᵘ Ψ} (λ x → Alg (restrictᵛ {Γ = Γ} (⊑ᵘ-*Many Ψ) x) >>=ᵖ λ valg → λ v → cata-semᵛ u wf valg v)
          (⟦ ⊢cataᶜ wf da ⟧ₛ δ)
  cata-sem′ {Ψ = Ψ} {π = π} u wf da Alg hA {x} {γ} r =
    trans (>>=ᵖ-β _ _)
      (trans (cong (λ C → λ v → cata-semᵛ u wf C v)
                   (hA (split-R {Γ = Γ} E (⊑ᵘ-*Many Ψ) _ fX (env*Many-envʳ-restrict σ₀ Z Ψ) r)))
             (sym (⟦⟧-substΨ E D δ γ)))
    where
      E  = cata-use {Δ = Δ} Ψ
      Z  = Many *ᵘ zeroUsage {n} +ᵘ zeroUsage
      fX : Env σ₀ Γ (Z +ᵘ Many *ᵘ Ψ) → Env σ₀ Γ Ψ
      fX y = env*Many σ₀ Ψ (envʳ σ₀ Z (Many *ᵘ Ψ) y)
      D = ⊢let da (⊢lam (≤qᵇ→≤q _ _ refl) (⊢fold wf (⊢var (suc zero)) (⊢var zero)))

  ana-sem″ : ∀ {Ψ : Usage n} {F : Fun 0} {A : Ty 0} {π₀} {π : Finite} {c}
    (u₀ : pure ⊑π π₀) (wf : WFFun Δ F) (dc : Δ ⊩ Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many (fin π) ] ⟦ F ⟧F A ! pure)
    (Co : EA.Env Γ Ψ → ⟦ A ⇒[ mk-kind Many (fin π) ] ⟦ F ⟧F A ⟧ᵛ) → Arm Co (⟦ dc ⟧ₛ δ)
    → Arm {Many *ᵘ Ψ} (λ x → λ a → returnM u₀ (ana-semᵛ π wf (Co (restrictᵛ {Γ = Γ} (⊑ᵘ-*Many Ψ) x)) a))
          (⟦ ⊢anaᶜ u₀ wf dc ⟧ₛ δ)
  ana-sem″ {Ψ = Ψ} {F = F} {A = A} {π = π} u₀ wf dc Co hC {γ = γ} r =
    extensionality λ a →
      trans (cong (λ C → SE.sub u₀ (ana-semᵛ π wf C a))
                  (hC (split-R {Γ = Γ} (+ᵘ-identityʳ (Many *ᵘ Ψ)) (⊑ᵘ-*Many Ψ) _ (λ y → env*Many σ₀ Ψ (envˡ σ₀ (Many *ᵘ Ψ) zeroUsage y))
                               (env*Many-envˡ-restrict σ₀ Ψ zeroUsage) r)))
            (sym (trans (substΨ1 (+ᵘ-identityʳ (Many *ᵘ Ψ)) _ γ a)
                        (cong (λ C → SE.sub u₀ (ana-semᵛ π wf C a)) (RS.wk-sem σ₀ δ noResp A dc _))))
    where
      substΨ1 : ∀ {U U′ : Usage n} {X B : Ty 0} {t π′} (e : U ≡ U′) (d : Δ ⊩ (Γ ▸ X) ⊢[ One ∷ U ] t ∷ B ! π′)
                (γ′ : Env σ₀ Γ U′) (v : ⟦ X ⟧ᵛ)
              → ⟦ subst (λ V → Δ ⊩ (Γ ▸ X) ⊢[ One ∷ V ] t ∷ B ! π′) e d ⟧ₛ δ (γ′ , v) ≡ ⟦ d ⟧ₛ δ (subst (Env σ₀ Γ) (sym e) γ′ , v)
      substΨ1 refl d γ′ v = refl

  loop-sem : ∀ {Ψ : Usage n} {A B : Ty 0} {c}
    (dc : Δ ⊩ Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many act ] (B + A) ! pure)
    (R : EA.Env Γ Ψ → ⟦ A ⇒[ mk-kind Many act ] (B + A) ⟧ᵛ) → Arm R (⟦ dc ⟧ₛ δ)
    → Arm {Many *ᵘ Ψ} (λ x → λ a → loop (R (restrictᵛ {Γ = Γ} (⊑ᵘ-*Many Ψ) x)) a) (⟦ ⊢loopᶜ dc ⟧ₛ δ)
  loop-sem {Ψ = Ψ} dc R hR {γ = γ} r =
    trans (cong (λ C → λ a → loop C a)
                (hR (split-R {Γ = Γ} (loop-use {Δ = Δ} Ψ) (⊑ᵘ-*Many Ψ) _ (λ y → env*Many σ₀ Ψ (envʳ σ₀ _ (Many *ᵘ Ψ) y))
                             (env*Many-envʳ-restrict σ₀ _ Ψ) r)))
          (sym (⟦⟧-substΨ (loop-use {Δ = Δ} Ψ) _ δ γ))

  effApp-sem : ∀ {Ψ₁ Ψ₂ : Usage n} {π} {A B : Ty 0} {f t}
    (df : Δ ⊩ Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! pure) (dx : Δ ⊩ Γ ⊢[ Ψ₂ ] t ∷ A ! pure)
    (F : EA.Env Γ Ψ₁ → ⟦ A ⇒[ mk-kind Many π ] B ⟧ᵛ) (X : EA.Env Γ Ψ₂ → ⟦ A ⟧ᵛ)
    → Arm F (⟦ df ⟧ₛ δ) → Arm X (⟦ dx ⟧ₛ δ)
    → Arm {Ψ₁ +ᵘ Many *ᵘ Ψ₂}
          (λ x → returnᵖ (λ _ → F (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x) >>=ᵖ λ vf →
                                X (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x) >>=ᵖ λ vx → vf vx))
          (⟦ ⊢effAppᶜ df dx ⟧ₛ δ)
  effApp-sem {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} df dx F X hF hX r =
    extensionality λ _ →
      trans (appC (hF (envˡ-R {Γ = Γ} Ψ₁ (Many *ᵘ Ψ₂) r)) (hX (env*Many-envʳ-R {Γ = Γ} Ψ₁ Ψ₂ r)))
            (sym (cong₂ (λ f a → f a) (RS.wk-sem σ₀ δ noResp Once.Spec.Type.Unit df _) (RS.wk-sem σ₀ δ noResp Once.Spec.Type.Unit dx _)))

------------------------------------------------------------------------
-- The bridge
------------------------------------------------------------------------

open import Once.Spec.Surface.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Denotation.Meaning Σ σ₀ using (EnvRun)

module _ {δ : DefSem} where

  bridge-d : ∀ {A B : Ty 0} {ctx : NamedCtx 0} {e π Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
             (d : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) {x γ} → EnvR (NamedCtx.debruijn ctx) Ψ x γ
           → ⟦ d ⟧ᵈ fmt ρ x ≡ ⟦ proj₂ (elabᵈ V d) ⟧ₛ δ γ

  bridge-i : ∀ {A : Ty 0} {ctx : NamedCtx 0} {e Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
             (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ) {x γ} → EnvR (NamedCtx.debruijn ctx) Ψ x γ
           → ⟦ d ⟧ᵢ fmt ρ x ≡ ⟦ proj₂ (elabᵢ V d) ⟧ₛ δ γ

  bridge-c : ∀ {A : Ty 0} {ctx : NamedCtx 0} {e Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
             (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ) {x γ} → EnvR (NamedCtx.debruijn ctx) Ψ x γ
           → ⟦ d ⟧ᶜ fmt ρ x ≡ ⟦ proj₂ (elabᶜ V d) ⟧ₛ δ γ

  bridge-c V ag t-id-check             r = refl
  bridge-c V ag (t-fst-check {u = u}) r = refl
  bridge-c V ag (t-snd-check {u = u}) r = refl
  bridge-c V ag t-terminal-morph-check r = refl
  bridge-c V ag (t-initial-morph-check {π = π}) r = extensionality λ ()
  bridge-c V ag (t-inl-morph-check {u = u}) r = refl
  bridge-c V ag (t-inr-morph-check {u = u}) r = refl
  bridge-c V ag (t-compose-check-g dg df) r =
    Comb.compose-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᵈ V dg)) _ _ (bridge-c V ag df) (bridge-d V ag dg) r
  bridge-c V ag (t-compose-check-f wf p dg) r =
    Comb.compose-sem {δ = δ} (⊢coerce p (proj₂ (elabᵢ V wf))) (proj₂ (elabᶜ V dg)) _ _
                     (λ e → cong ⟦ p ⟧<:ᵛ (bridge-i V ag wf e)) (bridge-c V ag dg) r
  bridge-c V ag (t-case-copair-check df dg) r =
    Comb.case-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg)) _ _ (bridge-c V ag df) (bridge-c V ag dg) r
  bridge-c V ag (t-pair-morph-check df dg) r =
    Comb.pair-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᶜ V dg)) _ _ (bridge-c V ag df) (bridge-c V ag dg) r
  bridge-c V ag (t-curry-check {u = u} df) r =
    Comb.curry-sem {δ = δ} u (proj₂ (elabᶜ V df)) _ (bridge-c V ag df) r
  bridge-c V ag (t-cata-check {u = u} wf dalg) r =
    Comb.cata-sem′ {δ = δ} u wf (proj₂ (elabᶜ V dalg)) _ (bridge-c V ag dalg) r
  bridge-c V ag (t-sub d p) r = cong ⟦ p ⟧<:ᵛ (bridge-i V ag d r)
  bridge-c {ctx = ctx} V ag (t-lam {A = A} {q = Zero} {q' = Zero} {u = u} le d) r = extensionality λ a → cong (subM u) (bridge-c V ag d (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt r))
  bridge-c {ctx = ctx} V ag (t-lam {A = A} {q = One} {q' = Zero} {u = u} le d) r = extensionality λ a → cong (subM u) (bridge-c V ag d (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt r))
  bridge-c {ctx = ctx} V ag (t-lam {A = A} {q = Many} {q' = Zero} {u = u} le d) r = extensionality λ a → cong (subM u) (bridge-c V ag d (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt r))
  bridge-c {ctx = ctx} V ag (t-lam {A = A} {q = One} {q' = One} {u = u} le d) r = extensionality λ a → cong (subM u) (bridge-c V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} One a r))
  bridge-c {ctx = ctx} V ag (t-lam {A = A} {q = Many} {q' = One} {u = u} le d) r = extensionality λ a → cong (subM u) (bridge-c V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} One a r))
  bridge-c {ctx = ctx} V ag (t-lam {A = A} {q = Many} {q' = Many} {u = u} le d) r = extensionality λ a → cong (subM u) (bridge-c V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} Many a r))
  bridge-c V ag (t-lam {q = Zero} {q' = One}  () d) r
  bridge-c V ag (t-lam {q = Zero} {q' = Many} () d) r
  bridge-c V ag (t-lam {q = One}  {q' = Many} () d) r
  bridge-c {ctx = ctx} V ag (t-pair-lit-check {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} da db) r =
    binK {K = λ ab → ab}
         (bridge-c V ag da (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (bridge-c V ag db (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envʳ σ₀ _ _) (envʳ-restrict σ₀ _ _) r))
  bridge-c V ag (t-In-app-check {F = F} wf d) r =
    Comb.appC-sem {δ = δ} {A = ⟦ F ⟧F (Once.Spec.Type.μ F)} {B = Once.Spec.Type.μ F} _ (⊢inᶜ wf) (λ y → refl) (proj₂ (elabᶜ V d)) _ (bridge-c V ag d) r
  bridge-c V ag (t-inl-app-check {A = A} {B = B} d) r =
    Comb.appC-sem {δ = δ} {A = A} {B = A + B} _ (⊢inlᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᶜ V d)) _ (bridge-c V ag d) r
  bridge-c V ag (t-inr-app-check {A = A} {B = B} d) r =
    Comb.appC-sem {δ = δ} {A = B} {B = A + B} _ (⊢inrᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᶜ V d)) _ (bridge-c V ag d) r
  bridge-c V ag (t-initial-app-check {T = T} d) r =
    Comb.appC-sem {δ = δ} {A = Once.Spec.Type.Void} {B = T} (λ w → ⊥-elim w) (⊢initialᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᶜ V d)) _ (bridge-c V ag d) r
  -- D273: the coalgebra lives in the context — no `close`, read at `x`.
  bridge-c V ag (t-ana-check {π₀ = π₀} {φ = π} {u = u} wf dcoalg) r =
    Comb.ana-sem″ {δ = δ} u wf (proj₂ (elabᶜ V dcoalg)) _ (bridge-c V ag dcoalg) r
  bridge-c V ag (t-loop-check dround) r =
    Comb.loop-sem {δ = δ} (proj₂ (elabᶜ V dround)) _ (bridge-c V ag dround) r
  bridge-c {ctx = ctx} V ag (t-apply-check {A = A} {B = B} dp) r =
    Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                  (λ y → ⟦⟧-substΨ (z+qz {Δ = NamedCtx.kinds ctx} Many) _ δ y) (proj₂ (elabᵢ V dp)) _ (bridge-i V ag dp) r
  bridge-c V ag (t-var-poly-instantiate _ _ lp ng ki) {γ = γ} r =
    trans (Agree.agree-inst ag lp ki) (sym (polyE-sem δ V lp ki γ))

  bridge-i V ag (t-int n) r = refl
  bridge-i V ag (t-float i f l) r = refl
  bridge-i V ag t-unit r = refl
  bridge-i V ag t-unit-var r = refl
  bridge-i {ctx = ctx} V ag (t-var-local {eV = Once.Internal.Context.svar i} _) r = lookup-R (NamedCtx.debruijn ctx) i r
  bridge-i V ag (t-var-resolved {cn = cn} _ wn lk k refl) {γ = γ} r =
    trans (Agree.agree-resolved ag {cn = cn} wn lk k) (sym (sigE-sem δ cn wn k (declares V lk) γ))
  bridge-i V ag (t-var-own _ lk refl) {γ = γ} r = trans (Agree.agree-import ag lk) (sym (importE-sem δ (imported V lk) γ))
  bridge-i V ag (t-var-import _ _ lk k refl) {γ = γ} r = trans (Agree.agree-import ag lk) (sym (importE-sem δ (imported V lk) γ))
  bridge-i V ag (t-var-poly-instantiate-infer {schema = sc} {g = g} _ _ lp _ refl) {γ = γ} r =
    trans (Agree.agree-inst ag lp (ground-kinded sc g)) (sym (polyE-sem δ V lp (ground-kinded sc g) γ))
  bridge-i V ag (t-annot _ d refl) r = bridge-c V ag d r
  bridge-i {ctx = ctx} V ag (t-pair da db) r =
    binK {K = λ ab → ab}
         (bridge-i V ag da (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (bridge-i V ag db (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envʳ σ₀ _ _) (envʳ-restrict σ₀ _ _) r))
  bridge-i V ag (t-neg d) r = fmapC _ (bridge-i V ag d r)
  bridge-i V ag (t-neg-float i f l) r = refl
  bridge-i {ctx = ctx} V ag (t-let {A = A} {q = Zero} d₁ d₂) r =
    bridge-i V ag d₂ (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
  bridge-i {ctx = ctx} V {ρ = ρ} ag (t-let {A = A} {q = One} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) {x = x} r =
    trans (>>=ᵖ-β _ _)
          (trans (cong (λ v → ⟦ d₂ ⟧ᵢ fmt ρ (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} One (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) x) v))
                       (bridge-i V ag d₁ (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (λ y → env*One σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (One *ᵘ Ψ₁) y))
                                                     (env*One-envʳ-restrict σ₀ Ψ₂ Ψ₁) r)))
                 (bridge-i V ag d₂ (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} One _ (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))))
  bridge-i {ctx = ctx} V {ρ = ρ} ag (t-let {A = A} {q = Many} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} d₁ d₂) {x = x} r =
    trans (>>=ᵖ-β _ _)
          (trans (cong (λ v → ⟦ d₂ ⟧ᵢ fmt ρ (bindᵛ {Γ = NamedCtx.debruijn ctx} {A = A} Many (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) x) v))
                       (bridge-i V ag d₁ (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (λ y → env*Many σ₀ Ψ₁ (envʳ σ₀ Ψ₂ (Many *ᵘ Ψ₁) y))
                                                     (env*Many-envʳ-restrict σ₀ Ψ₂ Ψ₁) r)))
                 (bridge-i V ag d₂ (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} Many _ (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))))
  -- D276: the core arm runs at the join through `⊢sub-use`, i.e. restricted
  -- after binding; the surface binds after restricting. Same environment.
  -- D322: each arm converted into the join, on both sides.
  bridge-i V ag (t-case {ctx = ctx} {A = A} {B = B} {C = C} {qL = qL} {qR = qR} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} ds dl dr J) {x = x} {γ = γ} r =
    trans (>>=ᵖ-β _ _)
      (trans (cong (λ v → [ L , R ]′ v) (bridge-i V ag ds (envˡ-R {Γ = Γc} Ψs (Ψₗ ⊔ᵘ Ψᵣ) r)))
             (go (⟦ proj₂ (elabᵢ V ds) ⟧ₛ δ (envˡ σ₀ Ψs (Ψₗ ⊔ᵘ Ψᵣ) γ))))
    where
      Γc = NamedCtx.debruijn ctx
      xr = restrictᵛ {Γ = Γc} (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) x
      γr = envʳ σ₀ Ψs (Ψₗ ⊔ᵘ Ψᵣ) γ
      rr : EnvR Γc (Ψₗ ⊔ᵘ Ψᵣ) xr γr
      rr = envʳ-R {Γ = Γc} Ψs (Ψₗ ⊔ᵘ Ψᵣ) r
      kl = ⊑ᵘ-keep {Δ = NamedCtx.kinds ctx} qL (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)
      kr = ⊑ᵘ-keep {Δ = NamedCtx.kinds ctx} qR (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)
      L : ⟦ A ⟧ᵛ → ⟦ C ⟧ᵛ
      L = λ a → ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ (⟦ dl ⟧ᵢ fmt _ (bindᵛ {Γ = Γc} {A = A} qL (restrictᵛ {Γ = Γc} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) xr) a))
      R : ⟦ B ⟧ᵛ → ⟦ C ⟧ᵛ
      R = λ b → ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ (⟦ dr ⟧ᵢ fmt _ (bindᵛ {Γ = Γc} {A = B} qR (restrictᵛ {Γ = Γc} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) xr) b))
      L′ : ⟦ A ⟧ᵛ → ⟦ C ⟧ᵛ
      L′ = λ a → ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ (⟦ proj₂ (elabᵢ V dl) ⟧ₛ δ (restrict σ₀ {Γ = Γc ▸ A} kl (γr , slot qL a)))
      R′ : ⟦ B ⟧ᵛ → ⟦ C ⟧ᵛ
      R′ = λ b → ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ (⟦ proj₂ (elabᵢ V dr) ⟧ₛ δ (restrict σ₀ {Γ = Γc ▸ B} kr (γr , slot qR b)))
      go : ∀ v → [ L , R ]′ v ≡ [ L′ , R′ ]′ v
      go (inj₁ a) =
        cong ⟦ <:ᶜ⇒<: (⊔-left J) ⟧<:ᵛ
          (bridge-i V ag dl (subst (λ z → EnvR (Γc ▸ A) (qL ∷ Ψₗ) z (restrict σ₀ {Γ = Γc ▸ A} kl (γr , slot qL a)))
                                   (EA.restrict-bind {Γ = Γc} {A = A} qL qL kl (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) xr a)
                                   (restrict-R {Γ = Γc ▸ A} kl kl (bind-R {Γ = Γc} {A = A} qL a rr))))
      go (inj₂ b) =
        cong ⟦ <:ᶜ⇒<: (⊔-right J) ⟧<:ᵛ
          (bridge-i V ag dr (subst (λ z → EnvR (Γc ▸ B) (qR ∷ Ψᵣ) z (restrict σ₀ {Γ = Γc ▸ B} kr (γr , slot qR b)))
                                   (EA.restrict-bind {Γ = Γc} {A = B} qR qR kr (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) xr b)
                                   (restrict-R {Γ = Γc ▸ B} kr kr (bind-R {Γ = Γc} {A = B} qR b rr))))
  bridge-i {ctx = ctx} V ag (t-binop-arith {op = OpAdd} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith {op = OpSub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith {op = OpMul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith {op = OpDiv} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith {op = OpMod} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i V ag (t-binop-arith {op = OpLt} () _ _) r
  bridge-i V ag (t-binop-arith {op = OpLe} () _ _) r
  bridge-i V ag (t-binop-arith {op = OpGt} () _ _) r
  bridge-i V ag (t-binop-arith {op = OpGe} () _ _) r
  bridge-i V ag (t-binop-arith {op = OpEq} () _ _) r
  bridge-i V ag (t-binop-arith {op = OpNe} () _ _) r
  bridge-i {ctx = ctx} V ag (t-binop-arith-float {op = OpAdd} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith-float {op = OpSub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith-float {op = OpMul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith-float {op = OpDiv} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i V ag (t-binop-arith-float {op = OpMod} () _ _) r
  bridge-i V ag (t-binop-arith-float {op = OpLt} () _ _) r
  bridge-i V ag (t-binop-arith-float {op = OpLe} () _ _) r
  bridge-i V ag (t-binop-arith-float {op = OpGt} () _ _) r
  bridge-i V ag (t-binop-arith-float {op = OpGe} () _ _) r
  bridge-i V ag (t-binop-arith-float {op = OpEq} () _ _) r
  bridge-i V ag (t-binop-arith-float {op = OpNe} () _ _) r
  bridge-i {ctx = ctx} V ag (t-binop-arith-float-il {op = OpAdd} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (fmapC _ (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith-float-il {op = OpSub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (fmapC _ (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith-float-il {op = OpMul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (fmapC _ (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-arith-float-il {op = OpDiv} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (fmapC _ (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i V ag (t-binop-arith-float-il {op = OpMod} () _ _) r
  bridge-i V ag (t-binop-arith-float-il {op = OpLt} () _ _) r
  bridge-i V ag (t-binop-arith-float-il {op = OpLe} () _ _) r
  bridge-i V ag (t-binop-arith-float-il {op = OpGt} () _ _) r
  bridge-i V ag (t-binop-arith-float-il {op = OpGe} () _ _) r
  bridge-i V ag (t-binop-arith-float-il {op = OpEq} () _ _) r
  bridge-i V ag (t-binop-arith-float-il {op = OpNe} () _ _) r
  bridge-i {ctx = ctx} V ag (t-binop-arith-float-ir {op = OpAdd} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (fmapC _ (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
  bridge-i {ctx = ctx} V ag (t-binop-arith-float-ir {op = OpSub} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (fmapC _ (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
  bridge-i {ctx = ctx} V ag (t-binop-arith-float-ir {op = OpMul} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (fmapC _ (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
  bridge-i {ctx = ctx} V ag (t-binop-arith-float-ir {op = OpDiv} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (fmapC _ (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)))
  bridge-i V ag (t-binop-arith-float-ir {op = OpMod} () _ _) r
  bridge-i V ag (t-binop-arith-float-ir {op = OpLt} () _ _) r
  bridge-i V ag (t-binop-arith-float-ir {op = OpLe} () _ _) r
  bridge-i V ag (t-binop-arith-float-ir {op = OpGt} () _ _) r
  bridge-i V ag (t-binop-arith-float-ir {op = OpGe} () _ _) r
  bridge-i V ag (t-binop-arith-float-ir {op = OpEq} () _ _) r
  bridge-i V ag (t-binop-arith-float-ir {op = OpNe} () _ _) r
  bridge-i {ctx = ctx} V ag (t-binop-cmp {op = OpLt} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-cmp {op = OpLe} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-cmp {op = OpGt} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-cmp {op = OpGe} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-cmp {op = OpEq} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i {ctx = ctx} V ag (t-binop-cmp {op = OpNe} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ d₁ d₂) r = binK (bridge-i V ag d₁ (envˡ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r)) (bridge-i V ag d₂ (envʳ-R {Γ = NamedCtx.debruijn ctx} Ψ₁ Ψ₂ r))
  bridge-i V ag (t-binop-cmp {op = OpAdd} () _ _) r
  bridge-i V ag (t-binop-cmp {op = OpSub} () _ _) r
  bridge-i V ag (t-binop-cmp {op = OpMul} () _ _) r
  bridge-i V ag (t-binop-cmp {op = OpDiv} () _ _) r
  bridge-i V ag (t-binop-cmp {op = OpMod} () _ _) r
  bridge-i V ag (t-id-app {T = T} d) r =
    trans (sym (>>=ᵖ-idʳ _)) (Comb.appC-sem {δ = δ} {A = T} {B = T} (λ v → v) (⊢idᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᵢ V d)) _ (bridge-i V ag d) r)
  bridge-i V ag (t-fst-app {A = A} {B = B} d) r = Comb.appC-sem {δ = δ} {A = A * B} {B = A} _ (⊢fstᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᵢ V d)) _ (bridge-i V ag d) r
  bridge-i V ag (t-snd-app {A = A} {B = B} d) r = Comb.appC-sem {δ = δ} {A = A * B} {B = B} _ (⊢sndᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᵢ V d)) _ (bridge-i V ag d) r
  bridge-i V ag (t-terminal-app {T = T} d) r = Comb.appC-sem {δ = δ} {A = T} {B = Once.Spec.Type.Unit} _ (⊢terminalᶜ ⊑-pure) (λ y → refl) (proj₂ (elabᵢ V d)) _ (bridge-i V ag d) r
  bridge-i V ag (t-Out-app-infer {F = F} wf refl d) r = Comb.appC-sem {δ = δ} {A = Once.Spec.Type.ν F pureᶠ} {B = ⟦ F ⟧F (Once.Spec.Type.ν F pureᶠ)} _ (⊢outᶜ wf) (λ y → refl) (proj₂ (elabᵢ V d)) _ (bridge-i V ag d) r
  bridge-i V ag (t-Out-eff-app-infer {F = F} wf refl d) r = Comb.appC-sem {δ = δ} {A = Once.Spec.Type.ν F actᶠ} {B = Once.Spec.Type.Unit ⇒[ mk-kind Many act ] ⟦ F ⟧F (Once.Spec.Type.ν F actᶠ)} _ (⊢outActᶜ wf) (λ y → refl) (proj₂ (elabᵢ V d)) _ (bridge-i V ag d) r
  bridge-i {ctx = ctx} V ag (t-apply-app-infer {A = A} {B = B} d) r =
    Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                  (λ y → ⟦⟧-substΨ (z+qz {Δ = NamedCtx.kinds ctx} Many) _ δ y) (proj₂ (elabᵢ V d)) _ (bridge-i V ag d) r
  bridge-i {ctx = ctx} V ag (t-apply-eff-app-infer {A = A} {B = B} {π = π} d) r =
    Comb.appC-sem {δ = δ} (λ fa → returnᵖ (λ _ → proj₁ fa (proj₂ fa)))
                  (⊢applyEffᶜ {Γ = NamedCtx.debruijn ctx} {π = π} {A = A} {B = B})
                  (λ y → ⟦⟧-substΨ (z+qz {Δ = NamedCtx.kinds ctx} Many) _ δ y) (proj₂ (elabᵢ V d)) _ (bridge-i V ag d) r
  bridge-i {ctx = ctx} V ag (t-app {q = Zero} _ df dx) r =
    trans (>>=ᵖ-β _ _) (cong (λ f → f tt) (bridge-i V ag df (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r)))
  bridge-i {ctx = ctx} V ag (t-app {q = One} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ df dx) r =
    appC (bridge-i V ag df (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (bridge-c V ag dx (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (λ y → env*One σ₀ Ψ₂ (envʳ σ₀ Ψ₁ (One *ᵘ Ψ₂) y))
                                     (env*One-envʳ-restrict σ₀ Ψ₁ Ψ₂) r))
  bridge-i {ctx = ctx} V ag (t-app {q = Many} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ df dx) r =
    appC (bridge-i V ag df (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (bridge-c V ag dx (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (λ y → env*Many σ₀ Ψ₂ (envʳ σ₀ Ψ₁ (Many *ᵘ Ψ₂) y))
                                     (env*Many-envʳ-restrict σ₀ Ψ₁ Ψ₂) r))
  bridge-i V ag (t-effApp _ df dx) r =
    Comb.effApp-sem {δ = δ} (proj₂ (elabᵢ V df)) (proj₂ (elabᶜ V dx)) _ _ (bridge-i V ag df) (bridge-c V ag dx) r
  bridge-i {ctx = ctx} V ag (t-app-spine {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} _ dx df) r =
    appC (bridge-d V ag df (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (envˡ σ₀ _ _) (envˡ-restrict σ₀ _ _) r))
         (bridge-i V ag dx (split-R′ {Γ = NamedCtx.debruijn ctx} _ _ (λ y → env*Many σ₀ _ (envʳ σ₀ _ (Many *ᵘ _) y))
                                     (env*Many-envʳ-restrict σ₀ _ _) r))

  bridge-d V ag (d-infer {B = B} w a g) r = cong ⟦ sub-arr {q = Many} a (<:-refl B) g ⟧<:ᵛ (bridge-i V ag w r)
  bridge-d V ag (d-poly {A = A} {B = B} _ _ lp ng _ _ ki g) {γ = γ} r =
    cong ⟦ sub-arr {q = Many} (<:-refl A) (<:-refl B) g ⟧<:ᵛ (trans (Agree.agree-inst ag lp ki) (sym (polyE-sem δ V lp ki γ)))
  bridge-d {ctx = ctx} V ag (d-lam {A = A} {q' = Zero} {u = u} d) r = extensionality λ a → cong (subM u) (bridge-i V ag d (bind0-R {Γ = NamedCtx.debruijn ctx} {A = A} tt r))
  bridge-d {ctx = ctx} V ag (d-lam {A = A} {q' = One} {u = u} d) r = extensionality λ a → cong (subM u) (bridge-i V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} One a r))
  bridge-d {ctx = ctx} V ag (d-lam {A = A} {q' = Many} {u = u} d) r = extensionality λ a → cong (subM u) (bridge-i V ag d (bind-R {Γ = NamedCtx.debruijn ctx} {A = A} Many a r))
  bridge-d V ag (d-compose dg df) r =
    Comb.compose-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) _ _ (bridge-d V ag df) (bridge-d V ag dg) r
  bridge-d V ag d-id r = refl
  bridge-d V ag (d-fst {u = u}) r = refl
  bridge-d V ag (d-snd {u = u}) r = refl
  bridge-d V ag d-terminal r = refl
  bridge-d V ag (d-initial {π = π}) r = extensionality λ ()
  bridge-d V ag (d-case {A = A} {B = B} {π = π} df dg J) r =
    Comb.case-sem {δ = δ} (⊢coerce pf (proj₂ (elabᵈ V df))) (⊢coerce pg (proj₂ (elabᵈ V dg))) _ _
                  (λ e → cong ⟦ pf ⟧<:ᵛ (bridge-d V ag df e)) (λ e → cong ⟦ pg ⟧<:ᵛ (bridge-d V ag dg e)) r
    where pf = sub-arr {q = Many} (<:-refl A) (<:ᶜ⇒<: (⊔-left J)) (⊑π-refl π)
          pg = sub-arr {q = Many} (<:-refl B) (<:ᶜ⇒<: (⊔-right J)) (⊑π-refl π)
  bridge-d V ag (d-pair df dg) r =
    Comb.pair-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) _ _ (bridge-d V ag df) (bridge-d V ag dg) r
  bridge-d V ag (d-cata {u = u} wf dalg) r =
    Comb.cata-sem′ {δ = δ} u wf (proj₂ (elabᵢ V dalg)) _ (bridge-i V ag dalg) r
