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
-- The bridge
------------------------------------------------------------------------

open import Once.Denotation.Meaning using (EnvRun)

module _ {δ : GM.DefSem} where

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
  bridge-c V ag (t-compose-check-g dg df) dγ = refl
  bridge-c V ag _ dγ = {!!}
