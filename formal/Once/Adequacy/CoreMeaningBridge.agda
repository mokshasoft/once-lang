-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreMeaningBridge — the Spec's core meaning of a term, as
-- the bridge to the implementation reads it (plan 0.103 6b; plan 0.122 §2b-3:
-- the Spec's core meaning is the only meaning of a derivation).
--
-- The references' meanings (an entry at an instance, an import, a generator
-- of Σ), the agreement of a scope's reference tables with the core's `δ`
-- (`Agree`), and one lemma per derived combinator: its core meaning, at a
-- Spec environment related to a surface one (`SurfaceEnv.EnvR`: the product
-- of the used values against the Spec's slots), is its arms' meanings
-- composed as the implementation composes them. The derived combinators were
-- written so their evaluation order is the implementation's (Spec.Core.Derived's
-- header); what the proofs spend is the pure bind's β-law, the renaming lemma
-- (`SpecRenameSem.wk-sem`) where a combinator weakens an arm, each of the
-- Spec's environment splits being a restriction (`Coherence.Env`), and the
-- transports the typing proofs carry.
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
open import Once.Spec.Surface.Syntax using (PolyType)
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
open import Once.Denotation.DefEnv using (defAt; impAt)
import Once.Denotation.RefMeanings Σ σ₀ as RM
open RM using (MeaningsOf; Meanings)
open RM.Meanings using (sigs; defs; entries)
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
open import Once.TypeCheck.View Σ S using (Views; View; ImportAt; Declared; declared; def)
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
-- The pure bind
------------------------------------------------------------------------

-- A pure return.
returnᵖ : ∀ {X : Set} → X → X
returnᵖ x = x

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

  -- A derivation's own arm: its meaning, read at the surface environment's values.
  arm : ∀ {Ψ : Usage n} {A : Ty 0} {t π} (D : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Arm (λ x → ⟦ D ⟧ₛ δ (fromSurf {Γ = Γ} x)) (⟦ D ⟧ₛ δ)
  arm D r = cong (⟦ D ⟧ₛ δ) (fromR≡ {Γ = Γ} r)

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
