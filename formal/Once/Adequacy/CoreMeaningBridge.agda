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
open import Once.Spec.Core.PolyTy using (Sig; _!!_; arity; kinds; type; Respects; _⟪_⟫; GSub)

module Once.Adequacy.CoreMeaningBridge (fmt : TargetNum) {s : ℕ} (S : Sig s) where

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
open import Once.CanonicalName using (CanonicalName; bare)
open import Once.Postulates using (extensionality)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.TypeCheck.Classify using (NamedCtx; lookupImport; lookupPolyPrefix)
open import Once.TypeCheck.Judgment
open import Once.Denotation.DefEnv using (defAt; impAt)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵈ; MeaningsOf; defs; entries; sigOpRefᴰ)
import Once.Spec.Core.Meaning S as GM
open import Once.Spec.Elaboration S using (Views; View; ImportAt; ffi; def; InstanceOf; elabᶜ; elabᵢ; elabᵈ)
open View

------------------------------------------------------------------------
-- The environment agreement
------------------------------------------------------------------------

-- The core meaning of a reference to entry `d` at an instance.
refSem : ∀ (δ : GM.DefSem) {d : Fin s} {U : Type} → InstanceOf d U → T ⟦ U ⟧ᴰ
refSem δ {d} (τ , r , eq) = subst (λ X → T ⟦ X ⟧ᴰ) eq (δ d τ r)

-- …and of an import (an FFI declaration is its contract).
impSem : ∀ (δ : GM.DefSem) {U : Type} → CanonicalName → IsConcrete U → ImportAt U → T ⟦ U ⟧ᴰ
impSem δ c k (ffi _ _) = sigOpRefᴰ fmt c k
impSem δ c k (def d i) = refSem δ i

-- `ρ` agrees with `δ` at every reference the View resolves.
record Agree {ctx : NamedCtx} (V : Views ctx) (ρ : MeaningsOf ctx) (δ : GM.DefSem) : Set where
  field
    agree-inst : ∀ {x sc body prefix U} (lp : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (sc , body , prefix))
                   (ng : ¬ Ground sc) (ki : KindedInstance sc U)
               → defAt (NamedCtx.polys ctx) x (defs ρ) lp U ki ≡ refSem δ (inst V lp ng ki)
    agree-ground : ∀ {x sc body prefix} (lp : lookupPolyPrefix (NamedCtx.polys ctx) x ≡ just (sc , body , prefix))
                     (g : Ground sc)
                 → defAt (NamedCtx.polys ctx) x (defs ρ) lp (extractGround sc g) (ground-kinded sc g)
                   ≡ refSem δ (ground V lp g)
    agree-import : ∀ {x U} (lk : lookupImport (NamedCtx.imports ctx) x ≡ just U) (k : IsConcrete U)
                 → impAt (NamedCtx.imports ctx) x (entries ρ) lk ≡ impSem δ (bare x) k (imported V lk)

------------------------------------------------------------------------
-- The derived combinators' meanings (one lemma per combinator)
------------------------------------------------------------------------

open import Once.Surface.Context using (Ctx; Usage; _+ᵘ_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*Many; zeroUsage; _⊑ᵘ_; _⊑∷_; _∷_; _,_^_)
open import Once.Type using (Quantity; Zero; One; _*_; _+_; Functor; ⟦_⟧T; μ-type)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Denotation.Meaning using (cata-sem)
open import Once.Surface.Context using (_⊔ᵘ_; ⊑ᵘ-refl)
open import Once.Surface.Properties using (+ᵘ-identityˡ; *ᵘ-identityˡ)
open import Once.Denotation.Phase using (bindᴰ)
open import Data.Fin using (zero; suc)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Type using (Many; mk-kind; _⇒[_]_; pure)
open import Once.Denotation.Phase using (restrictᴰ)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
open import Once.Spec.Core.DerivedTyping S
import Once.Adequacy.CoreRenameSem S as RS
import Once.Denotation.EnvAlgebra as EA

-- A restriction of a transported environment is any restriction of the original.
env-subst : ∀ {n} {Γ : Ctx n} {U U' Ψ' : Usage n} (e : U ≡ U') (u : Ψ' ⊑ᵘ U) (u' : Ψ' ⊑ᵘ U') (x : RS.Env Γ U')
          → restrictᴰ {Γ = Γ} u (subst (RS.Env Γ) (sym e) x) ≡ restrictᴰ {Γ = Γ} u' x
env-subst {Γ = Γ} refl u u' x = EA.restrict-irr {Γ = Γ} u u' x

-- Restrict, bind a value the restricted usage does not use, restrict again:
-- a restriction of the original (the pipeline `let′` builds for a weakened arm).
drop-bind : ∀ {n} {Γ : Ctx n} {A : Type} {Ψ' Ψm U U' : Usage n} {q : Quantity}
              (W3 : (Zero ∷ Ψ') ⊑ᵘ (q ∷ Ψm)) (W2 : Ψm ⊑ᵘ U) (e : U ≡ U') (w : Ψ' ⊑ᵘ U')
              (x : RS.Env Γ U') (a : ⟦ A ⟧ᴰ)
          → restrictᴰ {Γ = Γ , A ^ Many} W3 (bindᴰ {Γ = Γ} {A = A} q (restrictᴰ {Γ = Γ} W2 (subst (RS.Env Γ) (sym e) x)) a)
            ≡ restrictᴰ {Γ = Γ} w x
drop-bind {Γ = Γ} {q = q} (c ⊑∷ u) W2 refl w x a =
  trans (EA.restrict-bind {Γ = Γ} Zero q (c ⊑∷ u) u (restrictᴰ {Γ = Γ} W2 x) a)
        (EA.restrict-≡ {Γ = Γ} u W2 w x)

-- Two restrictions of a transported environment: any restriction of the original.
env-subst₂ : ∀ {n} {Γ : Ctx n} {Ψ' Um U U' : Usage n} (u : Ψ' ⊑ᵘ Um) (v : Um ⊑ᵘ U) (e : U ≡ U') (w : Ψ' ⊑ᵘ U')
               (x : RS.Env Γ U')
           → restrictᴰ {Γ = Γ} u (restrictᴰ {Γ = Γ} v (subst (RS.Env Γ) (sym e) x)) ≡ restrictᴰ {Γ = Γ} w x
env-subst₂ {Γ = Γ} u v refl w x = EA.restrict-≡ {Γ = Γ} u v w x

module Comb {δ : GM.DefSem} where
  bindC : ∀ {X Y : Set} {a a' : T X} {f g : X → T Y} → a ≡ a' → (∀ v → f v ≡ g v) → (a >>=T f) ≡ (a' >>=T g)
  bindC {a = a} refl h = cong (a >>=T_) (extensionality h)

  compose-sem : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type} {π} {f g}
    (df : Γ ⊢[ Ψ₁ ] f ∷ B ⇒[ mk-kind Many π ] C ! pure) (dg : Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π ] B ! pure)
    (x : RS.Env Γ (Ψ₁ +ᵘ Many *ᵘ Ψ₂))
    → GM.⟦ ⊢composeᶜ df dg ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x) >>=T λ vf →
         GM.⟦ dg ⟧ fmt δ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x) >>=T λ vg →
         returnT (λ a → vg a >>=T vf))
  compose-sem {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} df dg x =
    trans (RS.⟦⟧-substΨ (arms Many Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (z+qz Many))) (z+qz Many)))
                        (⊢let df (⊢let (wk-⊢′ _ dg)
                          (⊢lam refl (⊢app (⊢var′ (suc (suc zero)) π) (⊢app (⊢var′ (suc zero) π) (⊢var′ zero π))))))
                        fmt δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x))
                 (λ vf → bindC (trans (RS.wk-sem _ dg fmt δ _) (cong (GM.⟦ dg ⟧ fmt δ) (env-subst₂ {Γ = Γ} _ _ E (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x)))
                               (λ vg → refl)))
    where E = arms Many Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (z+qz Many))) (z+qz Many))

  pair-sem : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type} {π} {f g}
    (df : Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] B ! pure) (dg : Γ ⊢[ Ψ₂ ] g ∷ A ⇒[ mk-kind Many π ] C ! pure)
    (x : RS.Env Γ (Ψ₁ +ᵘ Ψ₂))
    → GM.⟦ ⊢pairᶜ df dg ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x) >>=T λ vf →
         GM.⟦ dg ⟧ fmt δ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x) >>=T λ vg →
         returnT (λ a → vf a >>=T λ b → vg a >>=T λ c → returnT (b , c)))
  pair-sem {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} df dg x =
    trans (RS.⟦⟧-substΨ E
                        (⊢let df (⊢let (wk-⊢′ _ dg)
                          (⊢lam refl (⊢pair (⊢app (⊢var′ (suc (suc zero)) π) (⊢var′ zero π))
                                            (⊢app (⊢var′ (suc zero) π) (⊢var′ zero π))))))
                        fmt δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x))
                 (λ vf → bindC (trans (RS.wk-sem _ dg fmt δ _)
                                      (cong (GM.⟦ dg ⟧ fmt δ) (env-subst₂ {Γ = Γ} _ _ E (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x)))
                               (λ vg → refl)))
    where E = trans (arms One Ψ₁ Ψ₂ (trans (cong₂ _+ᵘ_ (z+qz Many) (z+qz Many)) (+ᵘ-identityˡ zeroUsage)))
                    (cong (Ψ₁ +ᵘ_) (*ᵘ-identityˡ Ψ₂))

  case-sem : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B C : Type} {π} {f g}
    (df : Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many π ] C ! pure) (dg : Γ ⊢[ Ψ₂ ] g ∷ B ⇒[ mk-kind Many π ] C ! pure)
    (x : RS.Env Γ (Ψ₁ +ᵘ Ψ₂))
    → GM.⟦ ⊢caseᶜ df dg ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x) >>=T λ vf →
         GM.⟦ dg ⟧ fmt δ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x) >>=T λ vg →
         returnT (λ ab → [ vf , vg ]′ ab))
  case-sem {Γ = Γ} {Ψ₁} {Ψ₂} {π = π} df dg x =
    trans (RS.⟦⟧-substΨ E
                        (⊢let df (⊢let (wk-⊢′ _ dg)
                          (⊢lam refl (⊢case (⊢var′ zero π)
                                            (⊢app (⊢var′ (suc (suc (suc zero))) π) (⊢var′ zero π))
                                            (⊢app (⊢var′ (suc (suc zero)) π) (⊢var′ zero π))))))
                        fmt δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-+ˡ Ψ₁ Ψ₂) x))
                 (λ vf → bindC (trans (RS.wk-sem _ dg fmt δ _)
                                      (cong (GM.⟦ dg ⟧ fmt δ) (env-subst₂ {Γ = Γ} _ _ E (⊑ᵘ-+ʳ Ψ₁ Ψ₂) x)))
                               (λ vg → cong returnT (extensionality λ { (inj₁ a) → refl ; (inj₂ b) → refl }))))
    where E = trans (arms One Ψ₁ Ψ₂ (trans (cong (zeroUsage +ᵘ_) (trans (cong₂ _⊔ᵘ_ (z+qz Many) (z+qz Many)) z⊔z))
                                           (+ᵘ-identityˡ zeroUsage)))
                    (cong (Ψ₁ +ᵘ_) (*ᵘ-identityˡ Ψ₂))

  curry-sem : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B C : Type} {π₀ π} {f}
    (df : Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many π ] C ! pure) (x : RS.Env Γ Ψ)
    → GM.⟦ ⊢curryᶜ {π₀ = π₀} df ⟧ fmt δ x
      ≡ (GM.⟦ df ⟧ fmt δ x >>=T λ vf → returnT (λ a → returnT (λ b → vf (a , b))))
  curry-sem {Γ = Γ} {Ψ} {π₀ = π₀} {π} df x =
    trans (RS.⟦⟧-substΨ E
                        (⊢let df (⊢lam refl (⊢sub-eff (pure⊑ π₀)
                          (⊢lam refl (⊢app (⊢var′ (suc (suc zero)) π) (⊢pair (⊢var′ (suc zero) π) (⊢var′ zero π)))))))
                        fmt δ x)
          (bindC (cong (GM.⟦ df ⟧ fmt δ) (env-subst {Γ = Γ} E _ (⊑ᵘ-refl Ψ) x ∙ EA.restrict-refl {Γ = Γ} (⊑ᵘ-refl Ψ) x))
                 (λ vf → refl))
    where E = trans (cong₂ _+ᵘ_ (trans (cong (zeroUsage +ᵘ_) (cong (Many *ᵘ_) (+ᵘ-identityˡ zeroUsage))) (z+qz Many))
                                (*ᵘ-identityˡ Ψ))
                    (+ᵘ-identityˡ Ψ)
          _∙_ = trans

  cata-sem′ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {F : Functor} {A : Type} {π} {alg}
    (wf : WellFormedF F) (da : Γ ⊢[ Ψ ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ! pure) (x : RS.Env Γ Ψ)
    → GM.⟦ ⊢cataᶜ wf da ⟧ fmt δ x ≡ (GM.⟦ da ⟧ fmt δ x >>=T λ valg → returnT (cata-sem wf valg))
  cata-sem′ {Γ = Γ} {Ψ} {π = π} wf da x =
    trans (RS.⟦⟧-substΨ E (⊢let da (⊢lam refl (⊢fold wf (⊢var′ (suc zero) π) (⊢var′ zero π)))) fmt δ x)
          (bindC (cong (GM.⟦ da ⟧ fmt δ) (trans (env-subst {Γ = Γ} E _ (⊑ᵘ-refl Ψ) x) (EA.restrict-refl {Γ = Γ} (⊑ᵘ-refl Ψ) x)))
                 (λ valg → refl))
    where E = trans (cong₂ _+ᵘ_ (+ᵘ-identityˡ zeroUsage) (*ᵘ-identityˡ Ψ)) (+ᵘ-identityˡ Ψ)

------------------------------------------------------------------------
-- The bridge
------------------------------------------------------------------------

open import Once.Denotation.Meaning using (EnvRun)

module _ {δ : GM.DefSem} where
  bindC : ∀ {X Y : Set} {a a' : T X} {f g : X → T Y} → a ≡ a' → (∀ v → f v ≡ g v) → (a >>=T f) ≡ (a' >>=T g)
  bindC {a = a} refl h = cong (a >>=T_) (extensionality h)

  bridge-d : ∀ {ctx e A B π Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree {ctx} V ρ δ)
             (d : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) (dγ : EnvRun ctx Ψ)
           → ⟦ d ⟧ᵈ fmt ρ dγ ≡ GM.⟦ proj₂ (elabᵈ V d) ⟧ fmt δ dγ

  bridge-c : ∀ {ctx e A Ψ} (V : Views ctx) {ρ : MeaningsOf ctx} (ag : Agree {ctx} V ρ δ)
             (d : ctx ⊢ᶜ e ∶ A ⨾ Ψ) (dγ : EnvRun ctx Ψ)
           → ⟦ d ⟧ᶜ fmt ρ dγ ≡ GM.⟦ proj₂ (elabᶜ V d) ⟧ fmt δ dγ

  bridge-c V ag t-id-check             dγ = refl
  bridge-c V ag t-fst-check            dγ = refl
  bridge-c V ag t-snd-check            dγ = refl
  bridge-c V ag t-terminal-morph-check dγ = refl
  bridge-c V ag t-initial-morph-check  dγ = refl
  bridge-c V ag t-inl-morph-check      dγ = refl
  bridge-c V ag t-inr-morph-check      dγ = refl
  bridge-c V ag (t-compose-check-g dg df) dγ =
    trans (bindC (bridge-c V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.compose-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-c V ag _ dγ = {!!}

  bridge-d V ag d dγ = {!!}
