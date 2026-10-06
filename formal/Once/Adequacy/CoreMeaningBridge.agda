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

open import Once.Target.Arch using (TargetNum)
open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig; sigOf; _!!_; arity; kinds; type; Respects; _⟪_⟫; GSub)

open import Once.Spec.Contract using (ISig)
module Once.Adequacy.CoreMeaningBridge (fmt : TargetNum) {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import Once.Type using (Type; PolyType; Ground; extractGround)
open import Once.Type.Rigid using (KindedInstance; ground-kinded)
open import Once.Functor.Translate using (IsConcrete)
open import Once.CanonicalName using (CanonicalName; canonical; own; bare; showCanonical; NotOwn)
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.String using (_++_)
open import Once.Postulates using (extensionality)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ; M; bindM; returnM; subM; _>>=ᵖ_; >>=ᵖ-β; >>=ᵖ-assoc; >>=ᵖ-idʳ; bindM-idˡ)
open import Once.Denotation.TraceMonad using (T; interp; sig; impl)
open import Once.TypeCheck.Classify using (NamedCtx; lookupImport; lookupPolyPrefix; ctxWithImportsAndPolys; Imports; PolyCtx)
open import Data.String using (String)
open import Once.TypeCheck.Judgment
open import Once.Denotation.DefEnv using (defAt; impAt)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵈ; MeaningsOf; Meanings; returnᵖ)
open Once.Denotation.Meaning.Meanings using (decl-qual; decl-res; defs; entries; world)
open import Once.Denotation.GradedOps using (sigOpRefᵛ; cata-semᵛ; ana-semᵛ; ⟦_⟧<:ᵛ)
import Once.Spec.Core.Meaning S as GM
open import Once.Spec.Elaboration S using (Views; View; ImportAt; Declared; def; InstanceOf; elabᶜ; elabᵢ; elabᵈ; Elab; subE; lift1; closeE)
open View

------------------------------------------------------------------------
-- The environment agreement
------------------------------------------------------------------------

-- The core meaning of a reference to entry `d` at an instance.
refSem : ∀ (δ : GM.DefSem) {d : Fin s} {U : Type} → InstanceOf d U → ⟦ U ⟧ᵛ
refSem δ {d} (τ , r , eq) = subst (λ X → ⟦ X ⟧ᵛ) eq (GM.defs δ d τ r)

-- …and of a definition in scope (D274: an FFI declaration is not one — it is
-- in Σ, and its reference is the SigOp).
impSem : ∀ (δ : GM.DefSem) {x : String} {U : Type} → ImportAt x U → ⟦ U ⟧ᵛ
impSem δ (def d i) = refSem δ i

-- `ρ` agrees with `δ` at every reference the View resolves.
record Agree {imps sg : Imports} {polys : PolyCtx} (V : View imps sg polys) (ρ : Meanings polys imps sg) (δ : GM.DefSem) : Set where
  field
    agree-inst : ∀ {x sc body prefix U} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
                   (ng : ¬ Ground sc) (ki : KindedInstance sc U)
               → defAt polys x (defs ρ) lp U ki ≡ refSem δ (inst V lp ng ki)
    agree-ground : ∀ {x sc body prefix} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
                     (g : Ground sc)
                 → defAt polys x (defs ρ) lp (extractGround sc g) (ground-kinded sc g)
                   ≡ refSem δ (ground V lp g)
    agree-import : ∀ {x U} (lk : lookupImport imps x ≡ just U)
                 → impAt imps x (entries ρ) lk ≡ impSem δ (imported V lk)
    -- a qualified or resolved reference names a generator of Σ: both meanings
    -- read the same declaration in the same world.
    agree-qualified : ∀ {name alias U} (lk : lookupImport sg (alias ++ "." ++ name) ≡ just U) (k : IsConcrete U)
                    → sigOpRefᵛ fmt (sigOf S) (GM.impl δ) (bare (alias ++ "." ++ name)) k (Declared.member (declares V lk))
                      ≡ sigOpRefᵛ fmt (sig (world ρ)) (impl (world ρ)) (bare (alias ++ "." ++ name)) k (decl-qual ρ {name = name} {alias = alias} lk)
    agree-resolved : ∀ {cn U} (lk : lookupImport sg (showCanonical cn) ≡ just U) (k : IsConcrete U)
                   → sigOpRefᵛ fmt (sigOf S) (GM.impl δ) cn k (Declared.member (declares V lk))
                     ≡ sigOpRefᵛ fmt (sig (world ρ)) (impl (world ρ)) cn k (decl-res ρ {cn = cn} lk)
    -- Plan 0.105: both meanings run in the same world — the core's signatures
    -- with its implementation.
    agree-world : world ρ ≡ interp (sigOf S) (GM.impl δ)

------------------------------------------------------------------------
-- The derived combinators' meanings (one lemma per combinator)
------------------------------------------------------------------------

open import Once.Surface.Context using (Ctx; Usage; _+ᵘ_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*Many; zeroUsage; _⊑ᵘ_; _⊑∷_; _∷_; _,_^_)
open import Once.Type using (Quantity; Zero; One; _*_; _+_; Functor; ⟦_⟧T; μ-type; ν-type)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Surface.Context using (_⊔ᵘ_; ⊑ᵘ-refl)
open import Once.Surface.Properties using (+ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-identityˡ)
open import Once.Denotation.PhaseV using (bindᵛ)
open import Data.Fin using (zero; suc)
open import Once.Type using (Many; mk-kind; _⇒[_]_; pure; eff)
open import Once.Denotation.PhaseV using (restrictᵛ)
open import Once.Spec.Core.Syntax S
open import Once.Type.Sub using (pure⊑; sub-arr; <:-refl)
open import Once.Spec.Core.Typing S
open import Once.Spec.Core.DerivedTyping S
open import Once.Spec.Core.Derived S using (seqᶜ; initialᶜ)
import Once.Adequacy.CoreRenameSem S as RS
open import Once.Spec.Core.Rename S using (⊢close)
import Once.Denotation.EnvAlgebraV as EA

-- A restriction of a transported environment is any restriction of the original.
env-subst : ∀ {n} {Γ : Ctx n} {U U' Ψ' : Usage n} (e : U ≡ U') (u : Ψ' ⊑ᵘ U) (u' : Ψ' ⊑ᵘ U') (x : RS.Env Γ U')
          → restrictᵛ {Γ = Γ} u (subst (RS.Env Γ) (sym e) x) ≡ restrictᵛ {Γ = Γ} u' x
env-subst {Γ = Γ} refl u u' x = EA.restrict-irr {Γ = Γ} u u' x

-- Restrict, bind a value the restricted usage does not use, restrict again:
-- a restriction of the original (the pipeline `let′` builds for a weakened arm).
drop-bind : ∀ {n} {Γ : Ctx n} {A : Type} {Ψ' Ψm U U' : Usage n} {q : Quantity}
              (W3 : (Zero ∷ Ψ') ⊑ᵘ (q ∷ Ψm)) (W2 : Ψm ⊑ᵘ U) (e : U ≡ U') (w : Ψ' ⊑ᵘ U')
              (x : RS.Env Γ U') (a : ⟦ A ⟧ᵛ)
          → restrictᵛ {Γ = Γ , A ^ Many} W3 (bindᵛ {Γ = Γ} {A = A} q (restrictᵛ {Γ = Γ} W2 (subst (RS.Env Γ) (sym e) x)) a)
            ≡ restrictᵛ {Γ = Γ} w x
drop-bind {Γ = Γ} {q = q} (c ⊑∷ u) W2 refl w x a =
  trans (EA.restrict-bind {Γ = Γ} Zero q (c ⊑∷ u) u (restrictᵛ {Γ = Γ} W2 x) a)
        (EA.restrict-≡ {Γ = Γ} u W2 w x)

-- Two restrictions of a transported environment: any restriction of the original.
env-subst₂ : ∀ {n} {Γ : Ctx n} {Ψ' Um U U' : Usage n} (u : Ψ' ⊑ᵘ Um) (v : Um ⊑ᵘ U) (e : U ≡ U') (w : Ψ' ⊑ᵘ U')
               (x : RS.Env Γ U')
           → restrictᵛ {Γ = Γ} u (restrictᵛ {Γ = Γ} v (subst (RS.Env Γ) (sym e) x)) ≡ restrictᵛ {Γ = Γ} w x
env-subst₂ {Γ = Γ} u v refl w x = EA.restrict-≡ {Γ = Γ} u v w x

module Comb {δ : GM.DefSem} where
  bindC : ∀ {X Y : Set} {a a' : X} {f g : X → Y} → a ≡ a' → (∀ v → f v ≡ g v) → (a >>=ᵖ f) ≡ (a' >>=ᵖ g)
  bindC {a = a} refl h = cong (a >>=ᵖ_) (extensionality h)

  compose-sem : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type} {π} {f g}
    (df : Γ ⊢[ Ψ₁ ] f ∷ B ⇒[ mk-kind Many π ] C ! pure) (dg : Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π ] B ! pure)
    (x : RS.Env Γ (Ψ₁ +ᵘ Many *ᵘ Ψ₂))
    → GM.⟦ ⊢composeᶜ df dg ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x) >>=ᵖ λ vf →
         GM.⟦ dg ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x) >>=ᵖ λ vg →
         λ a → bindM π (vg a) vf)
  compose-sem {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} df dg x =
    trans (RS.⟦⟧-substΨ (arms Many Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (z+qz Many))) (z+qz Many)))
                        (⊢let df (⊢let (wk-⊢′ _ dg)
                          (⊢lam refl (⊢app (⊢var′ (suc (suc zero)) π) (⊢app (⊢var′ (suc zero) π) (⊢var′ zero π))))))
                        fmt δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x))
                 (λ vf → bindC (trans (RS.wk-sem _ dg fmt δ _) (cong (GM.⟦ dg ⟧ fmt δ) (env-subst₂ {Γ = Γ} _ _ E (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x)))
                               (λ vg → extensionality λ a →
                                  trans (bindM-idˡ π vf _)
                                        (cong (λ m → bindM π m (λ y → vf y))
                                              (trans (bindM-idˡ π vg _) (bindM-idˡ π a _))))))
    where E = arms Many Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (z+qz Many))) (z+qz Many))

  pair-sem : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type} {π} {f g}
    (df : Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! pure) (dg : Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π ] C ! pure)
    (x : RS.Env Γ (Ψ₁ +ᵘ Ψ₂))
    → GM.⟦ ⊢pairᶜ df dg ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x) >>=ᵖ λ vf →
         GM.⟦ dg ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x) >>=ᵖ λ vg →
         λ a → bindM π (vf a) λ b → bindM π (vg a) λ c → returnM π (b , c))
  pair-sem {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} df dg x =
    trans (RS.⟦⟧-substΨ E
                        (⊢let df (⊢let (wk-⊢′ _ dg)
                          (⊢lam refl (⊢pair (⊢app (⊢var′ (suc (suc zero)) π) (⊢var′ zero π))
                                            (⊢app (⊢var′ (suc zero) π) (⊢var′ zero π))))))
                        fmt δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x))
                 (λ vf → bindC (trans (RS.wk-sem _ dg fmt δ _)
                                      (cong (GM.⟦ dg ⟧ fmt δ) (env-subst₂ {Γ = Γ} _ _ E (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x)))
                               (λ vg → extensionality λ a →
                                  cong₂ (λ m n → bindM π m λ b → bindM π n λ c → returnM π (b , c))
                                        (trans (bindM-idˡ π vf _) (bindM-idˡ π a _))
                                        (trans (bindM-idˡ π vg _) (bindM-idˡ π a _)))))
    where E = trans (arms One Ψ₁ Ψ₂ (trans (cong₂ _+ᵘ_ (z+qz Many) (z+qz Many)) (+ᵘ-identityˡ zeroUsage)))
                    (cong (Ψ₁ +ᵘ_) (*ᵘ-identityˡ Ψ₂))

  case-arm : ∀ {A B C : Type} {π} (vf : ⟦ A ⟧ᵛ → M π ⟦ C ⟧ᵛ) (vg : ⟦ B ⟧ᵛ → M π ⟦ C ⟧ᵛ) (ab : ⟦ A ⟧ᵛ Data.Sum.⊎ ⟦ B ⟧ᵛ)
           → [ (λ a → bindM π (returnM π vf) λ f → bindM π (returnM π a) λ y → f y)
             , (λ b → bindM π (returnM π vg) λ g → bindM π (returnM π b) λ y → g y) ]′ ab
             ≡ [ vf , vg ]′ ab
  case-arm {π = π} vf vg (inj₁ a) = trans (bindM-idˡ π vf _) (bindM-idˡ π a _)
  case-arm {π = π} vf vg (inj₂ b) = trans (bindM-idˡ π vg _) (bindM-idˡ π b _)

  case-sem : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type} {π} {f g}
    (df : Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] C ! pure) (dg : Γ ⊢[ Ψ₂ ] g ∷ B ⇒[ mk-kind Many π ] C ! pure)
    (x : RS.Env Γ (Ψ₁ +ᵘ Ψ₂))
    → GM.⟦ ⊢caseᶜ df dg ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x) >>=ᵖ λ vf →
         GM.⟦ dg ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x) >>=ᵖ λ vg →
         returnᵖ (λ ab → [ vf , vg ]′ ab))
  case-sem {Γ = Γ} {Ψ₁} {Ψ₂} {A} {B} {C} {π} df dg x =
    trans (RS.⟦⟧-substΨ E
                        (⊢let df (⊢let (wk-⊢′ _ dg)
                          (⊢lam refl (⊢case⊔ (⊢var′ zero π)
                                            (⊢app (⊢var′ (suc (suc (suc zero))) π) (⊢var′ zero π))
                                            (⊢app (⊢var′ (suc (suc zero)) π) (⊢var′ zero π))))))
                        fmt δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x))
                 (λ vf → bindC (trans (RS.wk-sem _ dg fmt δ _)
                                      (cong (GM.⟦ dg ⟧ fmt δ) (env-subst₂ {Γ = Γ} _ _ E (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x)))
                               (λ vg → extensionality λ ab →
                                  trans (bindM-idˡ π ab _)
                                        (case-arm {A = A} {B = B} {C = C} {π = π} vf vg ab))))
    where E = trans (arms One Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (trans (cong₂ _⊔ᵘ_ (z+qz Many) (z+qz Many)) z⊔z))
                                           (+ᵘ-identityˡ zeroUsage)))
                    (cong (Ψ₁ +ᵘ_) (*ᵘ-identityˡ Ψ₂))

  curry-sem : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B C : Type} {π₀ π} {f}
    (df : Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many π ] C ! pure) (x : RS.Env Γ Ψ)
    → GM.⟦ ⊢curryᶜ {π₀ = π₀} df ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ x >>=ᵖ λ vf → λ a → returnM π₀ (λ b → vf (a , b)))
  curry-sem {Γ = Γ} {Ψ} {π₀ = π₀} {π} df x =
    trans (RS.⟦⟧-substΨ E
                        (⊢let df (⊢lam refl (⊢sub-eff (pure⊑ π₀)
                          (⊢lam refl (⊢app (⊢var′ (suc (suc zero)) π) (⊢pair (⊢var′ (suc zero) π) (⊢var′ zero π)))))))
                        fmt δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-refl Ψ) x ∙ EA.restrict-refl {Γ = Γ} (⊑ᵘ-refl Ψ) x))
                 (λ vf → extensionality λ a → cong (subM (pure⊑ π₀)) (extensionality λ b →
                    trans (bindM-idˡ π vf _)
                          (trans (cong (λ m → bindM π m (λ y → vf y))
                                       (trans (bindM-idˡ π a _) (bindM-idˡ π b _)))
                                 (bindM-idˡ π (a , b) _)))))
    where E = trans (cong₂ _+ᵘ_ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (+ᵘ-identityˡ zeroUsage))) (z+qz Many))
                                (*ᵘ-identityˡ Ψ))
                    (+ᵘ-identityˡ Ψ)
          _∙_ = trans

  -- A closed combinator whose meaning is `returnᵖ F`, applied: its argument, bound into `F`.
  appC-sem : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B : Type} {c t} (F : ⟦ A ⟧ᵛ → ⟦ B ⟧ᵛ)
    (dc : Γ ⊢[ zeroUsage ] c ∷ A ⇒[ mk-kind Many pure ] B ! pure)
    (hc : ∀ y → GM.⟦ dc ⟧ fmt δ y ≡ returnᵖ F)
    (dt : Γ ⊢[ Ψ ] t ∷ A ! pure) (x : RS.Env Γ (zeroUsage +ᵘ Many *ᵘ Ψ))
    → GM.⟦ ⊢app dc dt ⟧ fmt δ x
      ≡ (GM.⟦ dt ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))) x) >>=ᵖ F)
  appC-sem {Γ = Γ} {Ψ} F dc hc dt x rewrite hc (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ zeroUsage (Many *ᵘ Ψ)) x) = >>=ᵖ-β F _

  -- Two pure binds, each of a projection, feeding a binary continuation.
  bind2β : ∀ {X Y Z W : Set} (m : X) (f : X → Y) (n : X) (g : X → Z) (h : Y → Z → W)
         → ((m >>=ᵖ f) >>=ᵖ λ vf → (n >>=ᵖ g) >>=ᵖ λ vx → h vf vx) ≡ h (f m) (g n)
  bind2β m f n g h =
    trans (cong (_>>=ᵖ (λ vf → (n >>=ᵖ g) >>=ᵖ λ vx → h vf vx)) (>>=ᵖ-β m f))
          (trans (>>=ᵖ-β (f m) _)
                 (trans (cong (_>>=ᵖ (λ vx → h (f m) vx)) (>>=ᵖ-β n g)) (>>=ᵖ-β (g n) _)))

  apply-sem : ∀ {n} {Γ : Ctx n} {A B : Type} (x : RS.Env Γ zeroUsage)
    → GM.⟦ ⊢applyᶜ {Γ = Γ} {A = A} {B = B} ⟧ fmt δ x ≡ returnᵖ (λ fa → proj₁ fa (proj₂ fa))
  apply-sem {Γ = Γ} x =
    trans (RS.⟦⟧-substΨ {Γ = Γ} (z+qz Many) (⊢lam refl (⊢app (⊢fst (⊢var zero)) (⊢snd (⊢var zero)))) fmt δ x)
          (extensionality λ fa → bind2β _ proj₁ _ proj₂ (λ f a → f a))

  -- The transport under a binder used once.
  substΨ1 : ∀ {n} {Γ : Ctx n} {X : Type} {U U' : Usage n} {t B π} (e : U ≡ U')
    (d : (Γ , X ^ Many) ⊢[ One ∷ U ] t ∷ B ! π) (x : RS.Env Γ U') (a : ⟦ X ⟧ᵛ)
    → GM.⟦ subst (λ V → (Γ , X ^ Many) ⊢[ One ∷ V ] t ∷ B ! π) e d ⟧ fmt δ (x , a)
      ≡ GM.⟦ d ⟧ fmt δ (subst (RS.Env Γ) (sym e) x , a)
  substΨ1 refl d x a = refl

  ana-sem″ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {F : Functor} {A : Type} {π₀ π} {c}
    (wf : WellFormedF F) (dc : Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ! pure) (x : RS.Env Γ Ψ)
    → GM.⟦ ⊢anaᶜ {π₀ = π₀} wf dc ⟧ fmt δ x ≡ (λ a → ana-semᵛ π π₀ wf (returnM π₀ (GM.⟦ dc ⟧ fmt δ x)) a)
  ana-sem″ {Γ = Γ} {Ψ} {A = A} {π₀ = π₀} {π} wf dc x =
    extensionality λ a →
      trans (substΨ1 (+ᵘ-identityʳ Ψ)
                     (⊢unfold wf (⊢sub-eff (pure⊑ π₀) (wk-⊢′ A dc)) (⊢var′ zero π₀)) x a)
      (trans (bindM-idˡ π₀ a _)
            (cong (λ C → ana-semᵛ π π₀ wf (returnM π₀ C) a)
                  (trans (RS.wk-sem A dc fmt δ _)
                         (cong (GM.⟦ dc ⟧ fmt δ)
                               (trans (env-subst {Γ = Γ} (+ᵘ-identityʳ Ψ) _ (⊑ᵘ-refl Ψ) x)
                                      (EA.restrict-refl {Γ = Γ} (⊑ᵘ-refl Ψ) x))))))

  applyEff-sem : ∀ {n} {Γ : Ctx n} {A B : Type} (x : RS.Env Γ zeroUsage)
    → GM.⟦ ⊢applyEffᶜ {Γ = Γ} {A = A} {B = B} ⟧ fmt δ x ≡ returnᵖ (λ fa → returnᵖ (λ _ → proj₁ fa (proj₂ fa)))
  applyEff-sem {Γ = Γ} x =
    trans (RS.⟦⟧-substΨ {Γ = Γ} (z+qz Many)
             (⊢lam refl (⊢lam refl (⊢app (⊢fst (⊢var′ (suc zero) eff)) (⊢snd (⊢var′ (suc zero) eff))))) fmt δ x) refl

  effApp-sem : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B : Type} {f t}
    (df : Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many eff ] B ! pure) (dx : Γ ⊢[ Ψ₂ ] t ∷ A ! pure)
    (x : RS.Env Γ (Ψ₁ +ᵘ Many *ᵘ Ψ₂))
    → GM.⟦ ⊢effAppᶜ df dx ⟧ fmt δ x
      ≡ returnᵖ (λ _ → GM.⟦ df ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x) >>=ᵖ λ vf →
                       GM.⟦ dx ⟧ fmt δ (restrictᵛ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x) >>=ᵖ λ vx → vf vx)
  effApp-sem {Γ = Γ} df dx x =
    extensionality λ _ →
      trans (cong₂ (λ f a → f a) (RS.wk-sem _ df fmt δ _) (RS.wk-sem _ dx fmt δ _))
            (sym (trans (>>=ᵖ-β _ _) (>>=ᵖ-β _ _)))

  cata-sem′ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {F : Functor} {A : Type} {π} {alg}
    (wf : WellFormedF F) (da : Γ ⊢[ Ψ ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ! pure) (x : RS.Env Γ Ψ)
    → GM.⟦ ⊢cataᶜ wf da ⟧ fmt δ x ≡ (GM.⟦ da ⟧ fmt δ x >>=ᵖ λ valg → λ v → cata-semᵛ π wf valg v)
  cata-sem′ {Γ = Γ} {Ψ} {π = π} wf da x =
    trans (RS.⟦⟧-substΨ E (⊢let da (⊢lam refl (⊢fold wf (⊢var′ (suc zero) π) (⊢var′ zero π)))) fmt δ x)
          (bindC (cong (GM.⟦ da ⟧ fmt δ) (trans (env-subst {Γ = Γ} E _ (⊑ᵘ-refl Ψ) x) (EA.restrict-refl {Γ = Γ} (⊑ᵘ-refl Ψ) x)))
                 (λ valg → extensionality λ v → trans (bindM-idˡ π valg _) (bindM-idˡ π v _)))
    where E = trans (cong₂ _+ᵘ_ (+ᵘ-identityˡ zeroUsage) (*ᵘ-identityˡ Ψ)) (+ᵘ-identityˡ Ψ)

------------------------------------------------------------------------
-- The bridge
------------------------------------------------------------------------

open import Once.Denotation.Meaning using (EnvRun; seqᴰ)
open import Once.TypeCheck.Raw using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Denotation.TraceMonad using (fmapT)
open import Once.Surface.Context using (zeroUsage)

-- The monad laws are equalities of trees (plan 0.105).
open import Once.Denotation.TraceMonad using (returnT; _>>=T_; >>=T-assoc; >>=T-identityʳ)

assocT : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z) → ((m >>=T f) >>=T g) ≡ (m >>=T (λ x → f x >>=T g))
assocT m f g = >>=T-assoc m f g

idʳT : ∀ {X : Set} (m : T X) → (m >>=T returnT) ≡ m
idʳT m = >>=T-identityʳ m

-- `subE`'s usage transport moves onto the environment.
subE-sem : ∀ {δ : GM.DefSem} {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A : Type} (eq : Ψ ≡ Ψ′) (e : Elab Γ Ψ A) (x : RS.Env Γ Ψ′)
         → GM.⟦ proj₂ (subE eq e) ⟧ fmt δ x ≡ GM.⟦ proj₂ e ⟧ fmt δ (subst (RS.Env Γ) (sym eq) x)
subE-sem refl e x = refl

-- A resolved reference means its entry at the instance (refE's typing).
refSem-⊢ : ∀ {δ : GM.DefSem} {n} {Γ : Ctx n} {d : Fin s} {U : Type} (i : InstanceOf d U) (x : RS.Env Γ zeroUsage)
         → refSem δ i ≡ GM.⟦ subst (λ X → Γ ⊢[ zeroUsage ] ref d (proj₁ i) ∷ X ! pure) (proj₂ (proj₂ i))
                                  (⊢ref d (proj₁ i) (proj₁ (proj₂ i))) ⟧ fmt δ x
refSem-⊢ {δ} {d = d} (τ , r , eq) x = sym (RS.⟦⟧-substA eq (⊢ref d τ r) fmt δ x)

module _ {δ : GM.DefSem} where
  bindC : ∀ {X Y : Set} {a a' : X} {f g : X → Y} → a ≡ a' → (∀ v → f v ≡ g v) → (a >>=ᵖ f) ≡ (a' >>=ᵖ g)
  bindC {a = a} refl h = cong (a >>=ᵖ_) (extensionality h)

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
         ≡ ((m₁' >>=ᵖ λ a → m₂' >>=ᵖ λ b → returnᵖ (a , b)) >>=ᵖ K)
  binK {m₁' = m₁'} {m₂' = m₂'} {K = K} refl refl =
    sym (trans (>>=ᵖ-assoc m₁' _ K) (bindC refl (λ a → trans (>>=ᵖ-assoc m₂' _ K) (bindC refl (λ b → >>=ᵖ-β (a , b) K)))))

  bridge-d : ∀ {ctx e A B π Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
             (d : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) (dγ : EnvRun ctx Ψ)
           → ⟦ d ⟧ᵈ fmt ρ dγ ≡ GM.⟦ proj₂ (elabᵈ V d) ⟧ fmt δ dγ

  bridge-i : ∀ {ctx e A Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
             (d : ctx ⊢ᵢ e ∶ A ⨾ Ψ) (dγ : EnvRun ctx Ψ)
           → ⟦ d ⟧ᵢ fmt ρ dγ ≡ GM.⟦ proj₂ (elabᵢ V d) ⟧ fmt δ dγ

  bridge-c : ∀ {ctx e A Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree V ρ δ)
             (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ) (dγ : EnvRun ctx Ψ)
           → ⟦ d ⟧ᶜ fmt ρ dγ ≡ GM.⟦ proj₂ (elabᶜ V d) ⟧ fmt δ dγ

  bridge-c V ag t-id-check             dγ = refl
  bridge-c V ag (t-fst-check {π = π}) dγ = extensionality λ v → sym (bindM-idˡ π v _)
  bridge-c V ag (t-snd-check {π = π}) dγ = extensionality λ v → sym (bindM-idˡ π v _)
  bridge-c V ag t-terminal-morph-check dγ = refl
  bridge-c V ag (t-initial-morph-check {π = π}) dγ = extensionality λ v → sym (bindM-idˡ π v _)
  bridge-c V ag (t-inl-morph-check {π = π}) dγ = extensionality λ v → sym (bindM-idˡ π v _)
  bridge-c V ag (t-inr-morph-check {π = π}) dγ = extensionality λ v → sym (bindM-idˡ π v _)
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
  bridge-c V ag (t-curry-check df) dγ =
    trans (bindC (bridge-c V ag df dγ) (λ vf → refl))
          (sym (Comb.curry-sem {δ = δ} (proj₂ (elabᶜ V df)) dγ))
  bridge-c V ag (t-cata-check wf dalg) dγ =
    trans (bindC (bridge-c V ag dalg dγ) (λ valg → refl))
          (sym (Comb.cata-sem′ {δ = δ} wf (proj₂ (elabᶜ V dalg)) dγ))
  bridge-c V ag (t-sub d p) dγ = cong ⟦ p ⟧<:ᵛ (bridge-i V ag d dγ)
  bridge-c V ag (t-lam {q = Zero} {q' = Zero} {π = π} le d) dγ = extensionality λ a → cong (subM (pure⊑ π)) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = One}  {q' = Zero} {π = π} le d) dγ = extensionality λ a → cong (subM (pure⊑ π)) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Many} {q' = Zero} {π = π} le d) dγ = extensionality λ a → cong (subM (pure⊑ π)) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = One}  {q' = One} {π = π} le d) dγ = extensionality λ a → cong (subM (pure⊑ π)) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Many} {q' = One} {π = π} le d) dγ = extensionality λ a → cong (subM (pure⊑ π)) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Many} {q' = Many} {π = π} le d) dγ = extensionality λ a → cong (subM (pure⊑ π)) (bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Zero} {q' = One}  () d) dγ
  bridge-c V ag (t-lam {q = Zero} {q' = Many} () d) dγ
  bridge-c V ag (t-lam {q = One}  {q' = Many} () d) dγ
  bridge-c V ag (t-pair-lit-check da db) dγ =
    bindC (bridge-c V ag da _) (λ a → bindC (bridge-c V ag db _) (λ b → refl))
  bridge-c V ag (t-In-app-check wf d) dγ = app-comb _ (λ v → >>=ᵖ-β v _) (bridge-c V ag d _)
  bridge-c V ag (t-inl-app-check d) dγ = app-comb _ (λ v → >>=ᵖ-β v _) (bridge-c V ag d _)
  bridge-c V ag (t-inr-app-check d) dγ = app-comb _ (λ v → >>=ᵖ-β v _) (bridge-c V ag d _)
  bridge-c {ctx = ctx} V ag (t-initial-app-check d) dγ = app-comb {F = λ w → ⊥-elim w} _ (λ v → >>=ᵖ-β v (λ w → ⊥-elim w)) (bridge-c V ag d (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ))
  -- D273: the coalgebra lives in the context — no `close`, read at `dγ`.
  bridge-c {ctx = ctx} V ag (t-ana-check {π₀ = π₀} {π = π} wf dcoalg) dγ =
    trans (cong (λ C → λ a → ana-semᵛ π π₀ wf (returnM π₀ C) a) (bridge-c V ag dcoalg dγ))
          (sym (Comb.ana-sem″ {δ = δ} wf (proj₂ (elabᶜ V dcoalg)) dγ))
  bridge-c {ctx = ctx} V ag (t-apply-check {A = A} {B = B} dp) dγ =
    trans (bindC (bridge-i V ag dp _) (λ fa → refl))
          (sym (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                 (λ y → Comb.apply-sem {δ = δ} {Γ = NamedCtx.debruijn ctx} {A = A} {B = B} y) (proj₂ (elabᵢ V dp)) dγ))
  bridge-c V ag (t-var-poly-instantiate _ _ lp ng ki) dγ =
    trans (Agree.agree-inst ag lp ng ki) (refSem-⊢ (inst V lp ng ki) dγ)



  bridge-i V ag (t-int n) dγ = refl
  bridge-i V ag (t-float i f l p) dγ = refl
  bridge-i V ag t-unit dγ = refl
  bridge-i V ag t-unit-var dγ = refl
  bridge-i V ag (t-var-local {eV = Once.Surface.Context.svar i} _) dγ = refl
  bridge-i V ag (t-var-qualified {name = name} {alias = alias} lk k) dγ = sym (Agree.agree-qualified ag {name = name} {alias = alias} lk k)
  bridge-i V ag (t-var-resolved {cn = cn} _ lk k) dγ = sym (Agree.agree-resolved ag {cn = cn} lk k)
  bridge-i V ag (t-var-own _ lk k) dγ = trans (Agree.agree-import ag lk) (refSem-⊢ (ImportAt.instOf (imported V lk)) dγ)
  bridge-i V ag (t-var-import _ _ lk k) dγ = trans (Agree.agree-import ag lk) (refSem-⊢ (ImportAt.instOf (imported V lk)) dγ)
  bridge-i V ag (t-var-poly-instantiate-infer {g = g} _ _ lp _ refl) dγ =
    trans (Agree.agree-ground ag lp g) (refSem-⊢ (ground V lp g) dγ)
  bridge-i V ag (t-annot _ d) dγ = bridge-c V ag d dγ
  bridge-i V ag (t-pair da db) dγ = bindC (bridge-i V ag da _) (λ a → bindC (bridge-i V ag db _) (λ b → refl))
  bridge-i V ag (t-neg d) dγ = bindC (bridge-i V ag d dγ) (λ v → refl)
  bridge-i V ag (t-neg-float i f l p) dγ = refl
  bridge-i V ag (t-let {q = Zero} d₁ d₂) dγ = bridge-i V ag d₂ _
  bridge-i V ag (t-let {q = One} d₁ d₂) dγ = bindC (bridge-i V ag d₁ _) (λ v → bridge-i V ag d₂ _)
  bridge-i V ag (t-let {q = Many} d₁ d₂) dγ = bindC (bridge-i V ag d₁ _) (λ v → bridge-i V ag d₂ _)
  -- D276: the core arm runs at the join through `⊢sub-use`, i.e. restricted
  -- after binding; the surface binds after restricting. Same environment.
  bridge-i V ag (t-case {ctx = ctx} {A = A} {B = B} {qL = qL} {qR = qR} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} ds dl dr) dγ =
    bindC (bridge-i V ag ds _)
      (λ { (inj₁ a) → trans (bridge-i V ag dl _)
                            (cong (GM.⟦ proj₂ (elabᵢ V dl) ⟧ fmt δ)
                                  (sym (EA.restrict-bind {Γ = Γc} {A = A} qL qL (⊑ᵘ-keep qL (Once.Surface.Context.⊑ᵘ-⊔ˡ Ψₗ Ψᵣ)) (Once.Surface.Context.⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) x a)))
         ; (inj₂ b) → trans (bridge-i V ag dr _)
                            (cong (GM.⟦ proj₂ (elabᵢ V dr) ⟧ fmt δ)
                                  (sym (EA.restrict-bind {Γ = Γc} {A = B} qR qR (⊑ᵘ-keep qR (Once.Surface.Context.⊑ᵘ-⊔ʳ Ψₗ Ψᵣ)) (Once.Surface.Context.⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) x b))) })
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
  bridge-i V ag (t-binop-arith-float-il {op = OpAdd} _ d₁ d₂) dγ = binK (bindC (bridge-i V ag d₁ _) (λ _ → refl)) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float-il {op = OpSub} _ d₁ d₂) dγ = binK (bindC (bridge-i V ag d₁ _) (λ _ → refl)) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float-il {op = OpMul} _ d₁ d₂) dγ = binK (bindC (bridge-i V ag d₁ _) (λ _ → refl)) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float-il {op = OpDiv} _ d₁ d₂) dγ = binK (bindC (bridge-i V ag d₁ _) (λ _ → refl)) (bridge-i V ag d₂ _)
  bridge-i V ag (t-binop-arith-float-il {op = OpMod} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpLt} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpLe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpGt} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpGe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpEq} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-il {op = OpNe} () _ _) dγ
  bridge-i V ag (t-binop-arith-float-ir {op = OpAdd} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bindC (bridge-i V ag d₂ _) (λ _ → refl))
  bridge-i V ag (t-binop-arith-float-ir {op = OpSub} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bindC (bridge-i V ag d₂ _) (λ _ → refl))
  bridge-i V ag (t-binop-arith-float-ir {op = OpMul} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bindC (bridge-i V ag d₂ _) (λ _ → refl))
  bridge-i V ag (t-binop-arith-float-ir {op = OpDiv} _ d₁ d₂) dγ = binK (bridge-i V ag d₁ _) (bindC (bridge-i V ag d₂ _) (λ _ → refl))
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
  bridge-i V ag (t-fst-app d) dγ = app-comb _ (λ v → >>=ᵖ-β v _) (bridge-i V ag d _)
  bridge-i V ag (t-snd-app d) dγ = app-comb _ (λ v → >>=ᵖ-β v _) (bridge-i V ag d _)
  bridge-i {ctx = ctx} V ag (t-terminal-app d) dγ = bindC (bridge-i V ag d (restrictᵛ {Γ = NamedCtx.debruijn ctx} (⊑ᵘ-trans (⊑ᵘ-*Many _) (⊑ᵘ-+ʳ zeroUsage _)) dγ)) (λ v → refl)
  bridge-i V ag (t-Out-app-infer wf refl d) dγ = app-comb _ (λ v → >>=ᵖ-β v _) (bridge-i V ag d _)
  bridge-i V ag (t-Out-eff-app-infer wf refl d) dγ = app-comb _ (λ v → refl) (bridge-i V ag d _)
  bridge-i {ctx = ctx} V ag (t-apply-app-infer {A = A} {B = B} d) dγ =
    trans (bindC (bridge-i V ag d _) (λ fa → refl))
          (sym (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                 (λ y → Comb.apply-sem {δ = δ} {Γ = NamedCtx.debruijn ctx} {A = A} {B = B} y) (proj₂ (elabᵢ V d)) dγ))
  bridge-i {ctx = ctx} V ag (t-apply-eff-app-infer {A = A} {B = B} d) dγ =
    trans (bindC (bridge-i V ag d _) (λ fa → refl))
          (sym (Comb.appC-sem {δ = δ} (λ fa → returnᵖ (λ _ → proj₁ fa (proj₂ fa)))
                 (⊢applyEffᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                 (λ y → Comb.applyEff-sem {δ = δ} {Γ = NamedCtx.debruijn ctx} {A = A} {B = B} y) (proj₂ (elabᵢ V d)) dγ))
  bridge-i V ag (t-app {q = Zero} _ df dx) dγ = bindC (bridge-i V ag df _) (λ vf → refl)
  bridge-i V ag (t-app {q = One} _ df dx) dγ = bindC (bridge-i V ag df _) (λ vf → bindC (bridge-c V ag dx _) (λ vx → refl))
  bridge-i V ag (t-app {q = Many} _ df dx) dγ = bindC (bridge-i V ag df _) (λ vf → bindC (bridge-c V ag dx _) (λ vx → refl))
  bridge-i V ag (t-effApp _ df dx) dγ =
    trans (cong returnᵖ (extensionality λ _ → bindC (bridge-i V ag df _) (λ vf → bindC (bridge-c V ag dx _) (λ vx → refl))))
          (sym (Comb.effApp-sem {δ = δ} (proj₂ (elabᵢ V df)) (proj₂ (elabᶜ V dx)) dγ))
  bridge-i V ag (t-app-spine _ dx df) dγ = bindC (bridge-d V ag df _) (λ vf → bindC (bridge-i V ag dx _) (λ vx → refl))

  bridge-d V ag (d-infer {B = B} w a g) dγ = cong ⟦ sub-arr {q = Many} a (<:-refl B) g ⟧<:ᵛ (bridge-i V ag w dγ)
  bridge-d V ag (d-poly {A = A} {B = B} _ _ lp ng _ _ ki g) dγ =
    cong ⟦ sub-arr {q = Many} (<:-refl A) (<:-refl B) g ⟧<:ᵛ (trans (Agree.agree-inst ag lp ng ki) (refSem-⊢ (inst V lp ng ki) dγ))
  bridge-d V ag (d-lam {q' = Zero} {π = π} le d) dγ = extensionality λ a → cong (subM (pure⊑ π)) (bridge-i V ag d _)
  bridge-d V ag (d-lam {q' = One} {π = π} le d) dγ = extensionality λ a → cong (subM (pure⊑ π)) (bridge-i V ag d _)
  bridge-d V ag (d-lam {q' = Many} {π = π} le d) dγ = extensionality λ a → cong (subM (pure⊑ π)) (bridge-i V ag d _)
  bridge-d V ag (d-compose dg df) dγ =
    trans (bindC (bridge-d V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.compose-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-d V ag d-id dγ = refl
  bridge-d V ag (d-fst {π = π}) dγ = extensionality λ v → sym (bindM-idˡ π v _)
  bridge-d V ag (d-snd {π = π}) dγ = extensionality λ v → sym (bindM-idˡ π v _)
  bridge-d V ag d-terminal dγ = refl
  bridge-d V ag (d-initial {π = π}) dγ = extensionality λ v → sym (bindM-idˡ π v _)
  bridge-d V ag (d-case df dg) dγ =
    trans (bindC (bridge-d V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.case-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-d V ag (d-pair df dg) dγ =
    trans (bindC (bridge-d V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.pair-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-d V ag (d-cata wf dalg) dγ =
    trans (bindC (bridge-i V ag dalg dγ) (λ valg → refl))
          (sym (Comb.cata-sem′ {δ = δ} wf (proj₂ (elabᵢ V dalg)) dγ))

