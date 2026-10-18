{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Sigop — the leaves of the meaning: a reference
-- to the signature, a primitive, a literal. Each is the same as itself; and
-- when every operation of Σ is declared once (`OneName`), two derivations
-- of one reference read the same declaration.
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature; call)

module Once.Metatheory.Coherence.Sigop (Σ : Signature) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Once.Spec.Grade using (pure; act; eff; mk-kind; Zero; One; Many)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Type
  using (Ty; Type; TySub; Base; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; ∅ₖ; Unit; Int; Float; _*_; _+_; _⟨_⟩)
open import Once.Spec.Signature
  using (BTy; unit; void; int; float; ⌜_⌝; ⌜_⌝ᵈ; DeclType; constant; value; operation; Decl; _∶_; Op; op; NotEmpty; notEmpty?)
import Once.Spec.Signature as S
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; toB; fromB)
open import Once.Spec.Equivalence Σ
open import Once.Spec.Observation Σ using (World)
open import Once.Spec.Trace using (returned; halted; EndRel; returned≈; halted≈)
open import Once.Metatheory.Trace using (MaybeEnd; cut≈; end≈)
open import Relation.Nullary using (Dec; yes; no)
open import Once.Metatheory.Run Σ
open import Once.Spec.Signature using (OneName)
import Once.Metatheory.OneName as ON
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ


------------------------------------------------------------------------
-- One declaration per name
------------------------------------------------------------------------

module Names (u : OneName Σ) where
  decl-unique : ∀ {c t t′} → (c ∶ t) ∈ Σ → (c ∶ t′) ∈ Σ → t ≡ t′
  decl-unique = ON.decl-unique u

  mem-unique : ∀ {d} (p q : d ∈ Σ) → p ≡ q
  mem-unique = ON.mem-unique u

------------------------------------------------------------------------
-- Base values of the signature's types
------------------------------------------------------------------------

module _ {m : ℕ} (σ : TySub m 0) where

  baseB : ∀ b → Base ∅ₖ (⌜ b ⌝ ⟨ σ ⟩)
  baseB unit    = b-Unit
  baseB void    = b-Void
  baseB int     = b-Int
  baseB float   = b-Float
  baseB (a S.* b) = b-* (baseB a) (baseB b)
  baseB (a S.+ b) = b-+ (baseB a) (baseB b)

  argEq : ∀ a {x x′} → Same (⌜ a ⌝ ⟨ σ ⟩) x x′ → toB σ a x ≡ toB σ a x′
  argEq a s = cong (toB σ a) (sameBase (baseB a) s)

  fromB-same : ∀ b v → Same (⌜ b ⌝ ⟨ σ ⟩) (fromB σ b v) (fromB σ b v)
  fromB-same b v = reflBase (baseB b) (fromB σ b v)

  private
    -- One call's runs end the same as themselves, when its answers do.
    selfA : ∀ {X : Set} {R : X → X → Set} {w h o v n d e} {k : S.⟦ S.Op.ans o ⟧ᵇ → X} {D : Dec (NotEmpty (S.Op.ans o))}
          → (∀ r → R (k r) (k r)) → RunA w h o v (λ r → roll (done (inj₁ (k r)))) D n d e → MaybeEnd R e e
    selfA hk (ra-go rb-cut) = cut≈
    selfA hk (ra-go rb-ret) = end≈ (returned≈ (hk _))
    selfA hk ra-halt = end≈ halted≈
    selfA hk ra-cut  = cut≈

    selfCall : ∀ {X : Set} {R : X → X → Set} {o v} {k : S.⟦ S.Op.ans o ⟧ᵇ → X} → (∀ r → R (k r) (k r))
             → ∀ {w h n d e} → Run w h (embed (performT (call o v k))) n d e → MaybeEnd R e e
    selfCall hk (run rb-cut) = cut≈
    selfCall hk (run (rb-call r)) = selfA hk r

  -- One call of an operation, answered with a base value: a block.
  module _ {c a q b} (mem : (c ∶ operation a q b) ∈ Σ) where
    callT : ∀ {v v′} → v ≡ v′
          → Rel act act (⌜ b ⌝ ⟨ σ ⟩) (performT (call (op mem) v (fromB σ b))) (performT (call (op mem) v′ (fromB σ b)))
    callT refl = rel (Related-self (selfCall (fromB-same b)))

