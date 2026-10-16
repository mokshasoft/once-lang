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
  using (BTy; unit; void; int; float; ⌜_⌝; ⌜_⌝ᵈ; DeclType; constant; arrow; Decl; _∶_; Op; op; e-act; e-eff)
import Once.Spec.Signature as S
open import Once.Spec.Effect Σ
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ; toB; fromB)
open import Once.Spec.Equivalence Σ
open import Once.Spec.Observation Σ using (Interp; module Interp; Answer; resume; returned; halted; cut)
open import Once.Metatheory.Run Σ
open import Once.Spec.Metatheory using (OneName)
open import Once.Metatheory.Coherence.Relation Σ
open import Once.Metatheory.Coherence.Layer Σ

open T∞ using (force)

------------------------------------------------------------------------
-- One declaration per name
------------------------------------------------------------------------

module Names (u : OneName Σ) where
  private
    go-decl : ∀ {Σ′ : Signature} → OneName Σ′ → ∀ {c t t′} → (c ∶ t) ∈ Σ′ → (c ∶ t′) ∈ Σ′ → t ≡ t′
    go-decl (_ ∷ _) (here refl) (here refl) = refl
    go-decl (all ∷ _) (here refl) (there q) = ⊥-elim (All.lookup all (∈-map⁺ S.Decl.name q) refl)
    go-decl (all ∷ _) (there p) (here refl) = ⊥-elim (All.lookup all (∈-map⁺ S.Decl.name p) refl)
    go-decl (_ ∷ rest) (there p) (there q) = go-decl rest p q

    go-mem : ∀ {Σ′ : Signature} → OneName Σ′ → ∀ {d} (p q : d ∈ Σ′) → p ≡ q
    go-mem (_ ∷ _) (here refl) (here refl) = refl
    go-mem (all ∷ _) (here refl) (there q) = ⊥-elim (All.lookup all (∈-map⁺ S.Decl.name q) refl)
    go-mem (all ∷ _) (there p) (here refl) = ⊥-elim (All.lookup all (∈-map⁺ S.Decl.name p) refl)
    go-mem (_ ∷ rest) (there p) (there q) = cong there (go-mem rest p q)

  decl-unique : ∀ {c t t′} → (c ∶ t) ∈ Σ → (c ∶ t′) ∈ Σ → t ≡ t′
  decl-unique = go-decl u

  mem-unique : ∀ {d} (p q : d ∈ Σ) → p ≡ q
  mem-unique = go-mem u

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
    selfRes : ∀ {X : Set} {R : X → X → Set} {ι h n d e} (β : BTy) (v : Answer β) (k : S.⟦ β ⟧ᵇ → X)
            → (∀ r → R (k r) (k r)) → RunA ι h (resume β v (λ r → roll (done (inj₁ (k r))))) n d e → EndRel R e e
    selfRes void    v k hk ra-halt = halted≈
    selfRes unit    v k hk (ra-go rb-cut) = cut≈
    selfRes unit    v k hk (ra-go rb-ret) = returned≈ (hk v)
    selfRes int     v k hk (ra-go rb-cut) = cut≈
    selfRes int     v k hk (ra-go rb-ret) = returned≈ (hk v)
    selfRes float   v k hk (ra-go rb-cut) = cut≈
    selfRes float   v k hk (ra-go rb-ret) = returned≈ (hk v)
    selfRes (p S.* q) v k hk (ra-go rb-cut) = cut≈
    selfRes (p S.* q) v k hk (ra-go rb-ret) = returned≈ (hk v)
    selfRes (p S.+ q) v k hk (ra-go rb-cut) = cut≈
    selfRes (p S.+ q) v k hk (ra-go rb-ret) = returned≈ (hk v)

    selfCall : ∀ {X : Set} {R : X → X → Set} {o v} {k : S.⟦ S.Op.ans o ⟧ᵇ → X} → (∀ r → R (k r) (k r))
             → ∀ {ι h n d e} → Run ι h (embed (performT (call o v k))) n d e → EndRel R e e
    selfCall hk (run rb-cut) = cut≈
    selfCall {o = o} {v} {k} hk {ι} {h} (run (rb-call r)) = selfRes (S.Op.ans o) (Interp.answer ι o h v) k hk r

  -- One call of an operation, answered with a base value, at each grade.
  module _ {c a q π b} (mem : (c ∶ arrow a (mk-kind q π) b) ∈ Σ) (ef : S.Effectful π) where
    callT : ∀ {v v′} → v ≡ v′
          → Rel act act (⌜ b ⌝ ⟨ σ ⟩) (performT (call (op mem ef) v (fromB σ b))) (performT (call (op mem ef) v′ (fromB σ b)))
    callT refl = rel (Related-self (selfCall (fromB-same b)))

    call∞ : ∀ {v v′} → v ≡ v′
          → Rel eff eff (⌜ b ⌝ ⟨ σ ⟩) (perform (call (op mem ef) v (fromB σ b))) (perform (call (op mem ef) v′ (fromB σ b)))
    call∞ refl = rel (Related-self (selfCall (fromB-same b)))
