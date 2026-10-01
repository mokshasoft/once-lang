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
open import Once.CanonicalName using (CanonicalName; canonical; own; bare; showCanonical)
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.String using (_++_)
open import Once.Postulates using (extensionality)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.TypeCheck.Classify using (NamedCtx; lookupImport; lookupPolyPrefix; ctxWithImportsAndPolys; Imports; PolyCtx)
open import Once.TypeCheck.Judgment
open import Once.Denotation.DefEnv using (defAt; impAt)
open import Once.Denotation.Meaning using (⟦_⟧ᶜ; ⟦_⟧ᵢ; ⟦_⟧ᵈ; MeaningsOf; Meanings; defs; entries; sigOpRefᴰ)
import Once.Spec.Core.Meaning S as GM
open import Once.Spec.Elaboration S using (Views; View; ImportAt; ffi; def; InstanceOf; elabᶜ; elabᵢ; elabᵈ; Elab; subE; lift1; closeE)
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

-- D248: a canonical name that is not an own-module entry's (`own x`).
NotOwn : CanonicalName → Set
NotOwn (own _) = ⊥
NotOwn _       = ⊤

-- `ρ` agrees with `δ` at every reference the View resolves.
record Agree {imps : Imports} {polys : PolyCtx} (V : View imps polys) (ρ : Meanings polys imps) (δ : GM.DefSem) : Set where
  field
    agree-inst : ∀ {x sc body prefix U} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
                   (ng : ¬ Ground sc) (ki : KindedInstance sc U)
               → defAt polys x (defs ρ) lp U ki ≡ refSem δ (inst V lp ng ki)
    agree-ground : ∀ {x sc body prefix} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
                     (g : Ground sc)
                 → defAt polys x (defs ρ) lp (extractGround sc g) (ground-kinded sc g)
                   ≡ refSem δ (ground V lp g)
    agree-import : ∀ {x U} (lk : lookupImport imps x ≡ just U) (k : IsConcrete U)
                 → impAt imps x (entries ρ) lk ≡ impSem δ (bare x) k (imported V lk)
    -- a qualified or resolved reference names another module's FFI entry: the
    -- View classifies it as FFI, so it means the contract.
    agree-qualified : ∀ {name alias U} (lk : lookupImport imps (alias ++ "." ++ name) ≡ just U) (k : IsConcrete U)
                    → impSem δ (bare (alias ++ "." ++ name)) k (imported V lk) ≡ sigOpRefᴰ fmt (bare (alias ++ "." ++ name)) k
    -- D248: only a path of two or more parts (another module's inlined FFI
    -- signature); an own-module name is a call (`agree-import`).
    agree-resolved : ∀ {cn U} → NotOwn cn → (lk : lookupImport imps (showCanonical cn) ≡ just U) (k : IsConcrete U)
                   → impSem δ cn k (imported V lk) ≡ sigOpRefᴰ fmt cn k

------------------------------------------------------------------------
-- The derived combinators' meanings (one lemma per combinator)
------------------------------------------------------------------------

open import Once.Surface.Context using (Ctx; Usage; _+ᵘ_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*Many; zeroUsage; _⊑ᵘ_; _⊑∷_; _∷_; _,_^_)
open import Once.Type using (Quantity; Zero; One; _*_; _+_; Functor; ⟦_⟧T; μ-type; ν-type)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Denotation.Meaning using (cata-sem; ana-sem)
open import Once.Surface.Context using (_⊔ᵘ_; ⊑ᵘ-refl)
open import Once.Surface.Properties using (+ᵘ-identityˡ; +ᵘ-identityʳ; *ᵘ-identityˡ)
open import Once.Denotation.Phase using (bindᴰ)
open import Data.Fin using (zero; suc)
  renaming (⟦_⟧ᶜ to ⟦_⟧ᶜᵗ)
open import Once.Type using (Many; mk-kind; _⇒[_]_; pure; eff)
open import Once.Denotation.Phase using (restrictᴰ)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
open import Once.Spec.Core.DerivedTyping S
open import Once.Spec.Core.Derived S using (seqᶜ; initialᶜ)
import Once.Adequacy.CoreRenameSem S as RS
open import Once.Spec.Core.Rename S using (⊢close)
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

  -- A closed combinator whose meaning is `returnT F`, applied: its argument, bound into `F`.
  appC-sem : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B : Type} {c t} (F : ⟦ A ⟧ᴰ → T ⟦ B ⟧ᴰ)
    (dc : Γ ⊢[ zeroUsage ] c ∷ A ⇒[ mk-kind Many pure ] B ! pure)
    (hc : ∀ y → GM.⟦ dc ⟧ fmt δ y ≡ returnT F)
    (dt : Γ ⊢[ Ψ ] t ∷ A ! pure) (x : RS.Env Γ (zeroUsage +ᵘ Many *ᵘ Ψ))
    → GM.⟦ ⊢app dc dt ⟧ fmt δ x
      ≡ (GM.⟦ dt ⟧ fmt δ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))) x) >>=T F)
  appC-sem {Γ = Γ} {Ψ} F dc hc dt x rewrite hc (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ zeroUsage (Many *ᵘ Ψ)) x) = refl

  apply-sem : ∀ {n} {Γ : Ctx n} {A B : Type} (x : RS.Env Γ zeroUsage)
    → GM.⟦ ⊢applyᶜ {Γ = Γ} {A = A} {B = B} ⟧ fmt δ x ≡ returnT (λ fa → proj₁ fa (proj₂ fa))
  apply-sem {Γ = Γ} x = trans (RS.⟦⟧-substΨ {Γ = Γ} (z+qz Many) (⊢lam refl (⊢app (⊢fst (⊢var zero)) (⊢snd (⊢var zero)))) fmt δ x) refl

  -- The transport under a binder used once.
  substΨ1 : ∀ {n} {Γ : Ctx n} {X : Type} {U U' : Usage n} {t B π} (e : U ≡ U')
    (d : (Γ , X ^ Many) ⊢[ One ∷ U ] t ∷ B ! π) (x : RS.Env Γ U') (a : ⟦ X ⟧ᴰ)
    → GM.⟦ subst (λ V → (Γ , X ^ Many) ⊢[ One ∷ V ] t ∷ B ! π) e d ⟧ fmt δ (x , a)
      ≡ GM.⟦ d ⟧ fmt δ (subst (RS.Env Γ) (sym e) x , a)
  substΨ1 refl d x a = refl

  ana-sem″ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {F : Functor} {A : Type} {π₀ π} {c}
    (wf : WellFormedF F) (dc : Γ ⊢[ Ψ ] c ∷ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ! pure) (x : RS.Env Γ Ψ)
    → GM.⟦ ⊢anaᶜ {π₀ = π₀} wf dc ⟧ fmt δ x ≡ returnT (λ a → ana-sem {π = π} wf (GM.⟦ dc ⟧ fmt δ x) a)
  ana-sem″ {Γ = Γ} {Ψ} {A = A} {π₀ = π₀} {π} wf dc x =
    cong returnT (extensionality λ a →
      trans (substΨ1 (+ᵘ-identityʳ Ψ)
                     (⊢unfold wf (⊢sub-eff (pure⊑ π₀) (wk-⊢′ A dc)) (⊢var′ zero π₀)) x a)
            (cong (λ C → ana-sem {π = π} wf C a)
                  (trans (RS.wk-sem A dc fmt δ _)
                         (cong (GM.⟦ dc ⟧ fmt δ)
                               (trans (env-subst {Γ = Γ} (+ᵘ-identityʳ Ψ) _ (⊑ᵘ-refl Ψ) x)
                                      (EA.restrict-refl {Γ = Γ} (⊑ᵘ-refl Ψ) x))))))

  applyEff-sem : ∀ {n} {Γ : Ctx n} {A B : Type} (x : RS.Env Γ zeroUsage)
    → GM.⟦ ⊢applyEffᶜ {Γ = Γ} {A = A} {B = B} ⟧ fmt δ x ≡ returnT (λ fa → returnT (λ _ → proj₁ fa (proj₂ fa)))
  applyEff-sem {Γ = Γ} x =
    trans (RS.⟦⟧-substΨ {Γ = Γ} (z+qz Many)
             (⊢lam refl (⊢lam refl (⊢app (⊢fst (⊢var′ (suc zero) eff)) (⊢snd (⊢var′ (suc zero) eff))))) fmt δ x) refl

  effApp-sem : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ : Usage n} {A B : Type} {f t}
    (df : Γ ⊢[ Ψ₁ ] f ∷ A ⇒[ mk-kind Many eff ] B ! pure) (dx : Γ ⊢[ Ψ₂ ] t ∷ A ! pure)
    (x : RS.Env Γ (Ψ₁ +ᵘ Many *ᵘ Ψ₂))
    → GM.⟦ ⊢effAppᶜ df dx ⟧ fmt δ x
      ≡ returnT (λ _ → GM.⟦ df ⟧ fmt δ (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) x) >>=T λ vf →
                       GM.⟦ dx ⟧ fmt δ (restrictᴰ {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) x) >>=T λ vx → vf vx)
  effApp-sem {Γ = Γ} df dx x =
    cong returnT (extensionality λ _ →
      bindC (RS.wk-sem _ df fmt δ _) (λ vf → bindC (RS.wk-sem _ dx fmt δ _) (λ vx → refl)))

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

open import Once.Denotation.Meaning using (EnvRun; seqᴰ)
open import Once.TypeCheck.Raw using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe)
open import Once.Denotation.TraceMonad using (fmapT)
open import Once.Surface.Context using (zeroUsage)

-- The monad laws as equalities (T is a record: its two fields agree).
open import Once.Denotation.TraceMonad using (mkT; projTrace; atT; >>=T-assoc; >>=T-identityʳ)
T-ext : ∀ {X : Set} {l r : T X} → (∀ n → projTrace l n ≡ projTrace r n) → T.resT l ≡ T.resT r → l ≡ r
T-ext {l = mkT t₁ r₁} {r = mkT t₂ .r₁} tr refl = cong (λ t → mkT t r₁) (extensionality tr)

T-at : ∀ {X : Set} {l r : T X} → (∀ n → atT l n ≡ atT r n) → l ≡ r
T-at h = T-ext (λ n → cong proj₁ (h n)) (cong proj₂ (h 0))

assocT : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z) → ((m >>=T f) >>=T g) ≡ (m >>=T (λ x → f x >>=T g))
assocT m f g = T-at (>>=T-assoc m f g)

idʳT : ∀ {X : Set} (m : T X) → (m >>=T returnT) ≡ m
idʳT m = T-at (>>=T-identityʳ m)

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
  bindC : ∀ {X Y : Set} {a a' : T X} {f g : X → T Y} → a ≡ a' → (∀ v → f v ≡ g v) → (a >>=T f) ≡ (a' >>=T g)
  bindC {a = a} refl h = cong (a >>=T_) (extensionality h)

  -- A binary operation: the surface binds the operands and applies `K`; the
  -- core builds the pair and binds it into `K` — associativity, twice.
  binK : ∀ {X Y Z : Set} {m₁ m₁' : T X} {m₂ m₂' : T Y} {K : X × Y → T Z}
       → m₁ ≡ m₁' → m₂ ≡ m₂'
       → (m₁ >>=T λ a → m₂ >>=T λ b → K (a , b))
         ≡ ((m₁' >>=T λ a → m₂' >>=T λ b → returnT (a , b)) >>=T K)
  binK {m₁' = m₁'} {m₂' = m₂'} {K = K} refl refl =
    sym (trans (assocT m₁' _ K) (bindC refl (λ a → assocT m₂' _ K)))

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
  bridge-c V ag t-fst-check            dγ = refl
  bridge-c V ag t-snd-check            dγ = refl
  bridge-c V ag t-terminal-morph-check dγ = refl
  bridge-c V ag t-initial-morph-check  dγ = refl
  bridge-c V ag t-inl-morph-check      dγ = refl
  bridge-c V ag t-inr-morph-check      dγ = refl
  bridge-c V ag (t-compose-check-g dg df) dγ =
    trans (bindC (bridge-c V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.compose-sem {δ = δ} (proj₂ (elabᶜ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-c V ag (t-compose-check-f wf p dg) dγ =
    trans (bindC (cong (fmapT _) (bridge-i V ag wf _)) (λ vf → bindC (bridge-c V ag dg _) (λ vg → refl)))
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
  bridge-c {ctx = ctx} V ag (t-cata-check wf dalg) dγ =
    trans (bindC (trans (bridge-c {ctx = ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)} V ag dalg tt) (sym (RS.close-sem {Γ = NamedCtx.debruijn ctx} (proj₂ (elabᶜ V dalg)) fmt δ dγ))) (λ valg → refl))
          (sym (Comb.cata-sem′ {δ = δ} wf (⊢close {Γ = NamedCtx.debruijn ctx} (proj₂ (elabᶜ V dalg))) dγ))
  bridge-c V ag (t-sub d p) dγ = cong (fmapT _) (bridge-i V ag d dγ)
  bridge-c V ag (t-lam {q = Zero} {q' = Zero} le d) dγ = cong returnT (extensionality λ a → bridge-c V ag d _)
  bridge-c V ag (t-lam {q = One}  {q' = Zero} le d) dγ = cong returnT (extensionality λ a → bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Many} {q' = Zero} le d) dγ = cong returnT (extensionality λ a → bridge-c V ag d _)
  bridge-c V ag (t-lam {q = One}  {q' = One}  le d) dγ = cong returnT (extensionality λ a → bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Many} {q' = One}  le d) dγ = cong returnT (extensionality λ a → bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Many} {q' = Many} le d) dγ = cong returnT (extensionality λ a → bridge-c V ag d _)
  bridge-c V ag (t-lam {q = Zero} {q' = One}  () d) dγ
  bridge-c V ag (t-lam {q = Zero} {q' = Many} () d) dγ
  bridge-c V ag (t-lam {q = One}  {q' = Many} () d) dγ
  bridge-c V ag (t-pair-lit-check da db) dγ =
    bindC (bridge-c V ag da _) (λ a → bindC (bridge-c V ag db _) (λ b → refl))
  bridge-c V ag (t-In-app-check wf d) dγ = bindC (bridge-c V ag d _) (λ v → refl)
  bridge-c V ag (t-inl-app-check d) dγ = bindC (bridge-c V ag d _) (λ v → refl)
  bridge-c V ag (t-inr-app-check d) dγ = bindC (bridge-c V ag d _) (λ v → refl)
  bridge-c V ag (t-initial-app-check d) dγ = bindC (bridge-c V ag d _) (λ v → refl)
  bridge-c {ctx = ctx} V ag (t-ana-check {π = π} wf dcoalg) dγ =
    trans (cong (λ C → returnT (ana-sem {π = π} wf C))
                (trans (bridge-c {ctx = ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)} V ag dcoalg tt)
                       (sym (RS.close-sem {Γ = NamedCtx.debruijn ctx} (proj₂ (elabᶜ V dcoalg)) fmt δ dγ))))
          (sym (Comb.ana-sem″ {δ = δ} wf (⊢close {Γ = NamedCtx.debruijn ctx} (proj₂ (elabᶜ V dcoalg))) dγ))
  bridge-c {ctx = ctx} V ag (t-apply-check {A = A} {B = B} dp) dγ =
    trans (bindC (bridge-i V ag dp _) (λ fa → refl))
          (sym (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                 (λ y → Comb.apply-sem {δ = δ} {Γ = NamedCtx.debruijn ctx} {A = A} {B = B} y) (proj₂ (elabᵢ V dp)) dγ))
  bridge-c V ag (t-var-poly-instantiate _ _ lp ng ki) dγ =
    trans (Agree.agree-inst ag lp ng ki) (refSem-⊢ (inst V lp ng ki) dγ)



  bridge-i V ag (t-int n) dγ = refl
  bridge-i V ag (t-float i f l p) dγ = refl
  bridge-i V ag (t-str s′) dγ = refl
  bridge-i V ag t-unit dγ = refl
  bridge-i V ag t-unit-var dγ = refl
  bridge-i V ag (t-var-local {eV = Once.Surface.Context.svar i} _) dγ = refl
  bridge-i V ag (t-var-qualified {name = name} {alias = alias} lk k) dγ with imported V lk | Agree.agree-qualified ag {name = name} {alias = alias} lk k
  ... | ffi h g   | eq = refl
  ... | def d′ i′ | eq = trans (sym eq) (refSem-⊢ i′ dγ)
  bridge-i V ag (t-var-resolved {cn = own x} _ lk k) dγ with imported V lk | Agree.agree-import ag {x = x} lk k
  ... | ffi h g   | eq = eq
  ... | def d′ i′ | eq = trans eq (refSem-⊢ i′ dγ)
  bridge-i V ag (t-var-resolved {cn = canonical []} _ lk k) dγ
    with imported V lk | Agree.agree-resolved ag {cn = canonical []} tt lk k
  ... | ffi h g   | eq = refl
  ... | def d′ i′ | eq = trans (sym eq) (refSem-⊢ i′ dγ)
  bridge-i V ag (t-var-resolved {cn = canonical (a ∷ b ∷ rest)} _ lk k) dγ
    with imported V lk | Agree.agree-resolved ag {cn = canonical (a ∷ b ∷ rest)} tt lk k
  ... | ffi h g   | eq = refl
  ... | def d′ i′ | eq = trans (sym eq) (refSem-⊢ i′ dγ)
  bridge-i V ag (t-var-import {x = x} _ _ lk k) dγ with imported V lk | Agree.agree-import ag {x = x} lk k
  ... | ffi h g   | eq = eq
  ... | def d′ i′ | eq = trans eq (refSem-⊢ i′ dγ)
  bridge-i V ag (t-var-poly-instantiate-infer {g = g} _ _ lp _ refl) dγ =
    trans (Agree.agree-ground ag lp g) (refSem-⊢ (ground V lp g) dγ)
  bridge-i V ag (t-annot d) dγ = bridge-c V ag d dγ
  bridge-i V ag (t-pair da db) dγ = bindC (bridge-i V ag da _) (λ a → bindC (bridge-i V ag db _) (λ b → refl))
  bridge-i V ag (t-neg d) dγ = bindC (bridge-i V ag d dγ) (λ v → refl)
  bridge-i V ag (t-neg-float i f l p) dγ = refl
  bridge-i V ag (t-let {q = Zero} d₁ d₂) dγ = bridge-i V ag d₂ _
  bridge-i V ag (t-let {q = One} d₁ d₂) dγ = bindC (bridge-i V ag d₁ _) (λ v → bridge-i V ag d₂ _)
  bridge-i V ag (t-let {q = Many} d₁ d₂) dγ = bindC (bridge-i V ag d₁ _) (λ v → bridge-i V ag d₂ _)
  bridge-i V ag (t-case ds dl dr) dγ =
    bindC (bridge-i V ag ds _) (λ { (inj₁ a) → bridge-i V ag dl _ ; (inj₂ b) → bridge-i V ag dr _ })
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
  bridge-i V ag (t-id-app d) dγ = trans (bridge-i V ag d _) (sym (idʳT _))
  bridge-i V ag (t-fst-app d) dγ = bindC (bridge-i V ag d _) (λ v → refl)
  bridge-i V ag (t-snd-app d) dγ = bindC (bridge-i V ag d _) (λ v → refl)
  bridge-i V ag (t-terminal-app d) dγ = bindC (bridge-i V ag d _) (λ v → refl)
  bridge-i V ag (t-Out-app-infer wf refl d) dγ = bindC (bridge-i V ag d _) (λ v → refl)
  bridge-i V ag (t-Out-eff-app-infer wf refl d) dγ = bindC (bridge-i V ag d _) (λ v → refl)
  bridge-i {ctx = ctx} V ag (t-apply-app-infer {A = A} {B = B} d) dγ =
    trans (bindC (bridge-i V ag d _) (λ fa → refl))
          (sym (Comb.appC-sem {δ = δ} (λ fa → proj₁ fa (proj₂ fa)) (⊢applyᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                 (λ y → Comb.apply-sem {δ = δ} {Γ = NamedCtx.debruijn ctx} {A = A} {B = B} y) (proj₂ (elabᵢ V d)) dγ))
  bridge-i {ctx = ctx} V ag (t-apply-eff-app-infer {A = A} {B = B} d) dγ =
    trans (bindC (bridge-i V ag d _) (λ fa → refl))
          (sym (Comb.appC-sem {δ = δ} (λ fa → returnT (λ _ → proj₁ fa (proj₂ fa)))
                 (⊢applyEffᶜ {Γ = NamedCtx.debruijn ctx} {A = A} {B = B})
                 (λ y → Comb.applyEff-sem {δ = δ} {Γ = NamedCtx.debruijn ctx} {A = A} {B = B} y) (proj₂ (elabᵢ V d)) dγ))
  bridge-i V ag (t-app {q = Zero} _ df dx) dγ = bindC (bridge-i V ag df _) (λ vf → refl)
  bridge-i V ag (t-app {q = One} _ df dx) dγ = bindC (bridge-i V ag df _) (λ vf → bindC (bridge-c V ag dx _) (λ vx → refl))
  bridge-i V ag (t-app {q = Many} _ df dx) dγ = bindC (bridge-i V ag df _) (λ vf → bindC (bridge-c V ag dx _) (λ vx → refl))
  bridge-i V ag (t-effApp _ df dx) dγ =
    trans (cong returnT (extensionality λ _ → bindC (bridge-i V ag df _) (λ vf → bindC (bridge-c V ag dx _) (λ vx → refl))))
          (sym (Comb.effApp-sem {δ = δ} (proj₂ (elabᵢ V df)) (proj₂ (elabᶜ V dx)) dγ))
  bridge-i V ag (t-app-spine _ dx df) dγ = bindC (bridge-d V ag df _) (λ vf → bindC (bridge-i V ag dx _) (λ vx → refl))

  bridge-d V ag (d-infer w a g) dγ = cong (fmapT _) (bridge-i V ag w dγ)
  bridge-d V ag (d-poly _ _ lp ng _ _ ki g) dγ =
    cong (fmapT _) (trans (Agree.agree-inst ag lp ng ki) (refSem-⊢ (inst V lp ng ki) dγ))
  bridge-d V ag (d-lam {q' = Zero} le d) dγ = cong returnT (extensionality λ a → bridge-i V ag d _)
  bridge-d V ag (d-lam {q' = One}  le d) dγ = cong returnT (extensionality λ a → bridge-i V ag d _)
  bridge-d V ag (d-lam {q' = Many} le d) dγ = cong returnT (extensionality λ a → bridge-i V ag d _)
  bridge-d V ag (d-compose dg df) dγ =
    trans (bindC (bridge-d V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.compose-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-d V ag d-id dγ = refl
  bridge-d V ag d-fst dγ = refl
  bridge-d V ag d-snd dγ = refl
  bridge-d V ag d-terminal dγ = refl
  bridge-d V ag d-initial dγ = refl
  bridge-d V ag (d-case df dg) dγ =
    trans (bindC (bridge-d V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.case-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-d V ag (d-pair df dg) dγ =
    trans (bindC (bridge-d V ag df _) (λ vf → bindC (bridge-d V ag dg _) (λ vg → refl)))
          (sym (Comb.pair-sem {δ = δ} (proj₂ (elabᵈ V df)) (proj₂ (elabᵈ V dg)) dγ))
  bridge-d {ctx = ctx} V ag (d-cata wf dalg) dγ =
    trans (bindC (trans (bridge-i {ctx = ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)} V ag dalg tt)
                        (sym (RS.close-sem {Γ = NamedCtx.debruijn ctx} (proj₂ (elabᵢ V dalg)) fmt δ dγ))) (λ valg → refl))
          (sym (Comb.cata-sem′ {δ = δ} wf (⊢close {Γ = NamedCtx.debruijn ctx} (proj₂ (elabᵢ V dalg))) dγ))

