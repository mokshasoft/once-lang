-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.FillOk   (plan 0.135 S3, cata M4 stage D2)
--
-- EVERY FILL ON THE FOLD LOOP'S OWN RUN SUCCEEDS. Stage A's `PO.runPO`
-- returns junk when `PO.fill` finds the value stack too short; this module
-- shows that never happens on the run the machine performs (eval =
-- `PO.FI [ root ] []`, val = `[]`).
--
-- `fill` succeeds exactly when the stack holds at least as many entries as
-- the node's layer has `Id` positions (`idc`; values are irrelevant,
-- `fill-ok`). `Ok ns m` says: processing the nodes `ns` from a stack of
-- height `m`, every node finds its `Id` count on the stack (and pushes one
-- result). A subtree's post-order consumes nothing it did not push and
-- leaves one entry (`po-ok`, by tree induction mirroring `PO.po-run`), so
-- the root's post-order is `Ok` from the empty stack (`root-ok`).
------------------------------------------------------------------------

module Once.CCC.Codegen.IRObsCorrect.CataBr.FillOk where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm; suc-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Type using (Fun; K; Id; _⊕_; _⊗_)
open import Once.Spec.Type using (WFFun; ∅ₖ; wf-K; wf-Id) renaming (wf-⊕ to wf-Sum; wf-⊗ to wf-Prod)
open import Once.Spec.Polynomial using (⟦_⟧SF) renaming (inS to ⟨_⟩)
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using (⟦_⟧F; sem-Out; coerce-μ-out)
open import Once.IR.Semantics.Iterative using (T∞)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning using (module PO)

module FillOk {G : Fun 0} (w : WFFun ∅ₖ G) {C : Set} (alg : ⟦ G ⟧F C → T∞ C) where

  open PO w alg using (N; TF; fill; po; poL; FI)

  -- the number of `Id` positions in a layer
  idc : ∀ (H : Fun 0) → ⟦ H ⟧F N → ℕ
  idc (K A)     _        = 0
  idc Id        _        = 1
  idc (H₁ ⊕ H₂) (inj₁ x) = idc H₁ x
  idc (H₁ ⊕ H₂) (inj₂ y) = idc H₂ y
  idc (H₁ ⊗ H₂) (x , y)  = idc H₁ x + idc H₂ y

  private
    swap3 : ∀ (a b m : ℕ) → (a + b) + m ≡ b + (a + m)
    swap3 a b m = trans (cong (_+ m) (+-comm a b)) (+-assoc b a m)

  -- a stack holding the layer's `Id` count (and `m` more) fills it, leaving `m`
  fill-ok : ∀ (H : Fun 0) (x : ⟦ H ⟧F N) (vs : List C) (m : ℕ) → length vs ≡ idc H x + m
          → Σ (⟦ H ⟧F C) λ l → Σ (List C) λ rest → (fill H x vs ≡ just (l , rest)) × (length rest ≡ m)
  fill-ok (K A)     x        vs       m e = x , vs , refl , e
  fill-ok Id        x        []       m ()
  fill-ok Id        x        (c ∷ vs) m e = c , vs , refl , suc-injective e
  fill-ok (H₁ ⊕ H₂) (inj₁ x) vs       m e with fill-ok H₁ x vs m e
  ... | a , r , q , le rewrite q = inj₁ a , r , refl , le
  fill-ok (H₁ ⊕ H₂) (inj₂ y) vs       m e with fill-ok H₂ y vs m e
  ... | b , r , q , le rewrite q = inj₂ b , r , refl , le
  fill-ok (H₁ ⊗ H₂) (x , y)  vs       m e with fill-ok H₂ y vs (idc H₁ x + m) (trans e (swap3 (idc H₁ x) (idc H₂ y) m))
  ... | b , r₂ , q₂ , le₂ with fill-ok H₁ x r₂ m le₂
  ...   | a , r₁ , q₁ , le₁ rewrite q₂ | q₁ = (a , b) , r₁ , refl , le₁

  -- the nodes `ns`, processed from a stack of height `m`, each find their fill
  Ok : List N → ℕ → Set
  Ok []       m = ⊤
  Ok (t ∷ ns) m = Σ ℕ λ m′ → (m ≡ idc G (sem-Out w t) + m′) × Ok ns (suc m′)

  -- one round: the fill succeeds, and the rest is `Ok` with the result pushed
  step-ok : ∀ (t : N) (ns : List N) (vs : List C) → Ok (t ∷ ns) (length vs)
          → Σ (⟦ G ⟧F C) λ l → Σ (List C) λ rest → (fill G (sem-Out w t) vs ≡ just (l , rest)) × Ok ns (suc (length rest))
  step-ok t ns vs (m′ , e , ok) with fill-ok G (sem-Out w t) vs m′ e
  ... | l , rest , q , le = l , rest , q , subst (λ z → Ok ns (suc z)) (sym le) ok

  -- a subtree's post-order leaves one more entry than it found
  mutual
    po-ok : ∀ (t : N) (xs : List N) (m : ℕ) → Ok xs (suc m) → Ok (po t ++ xs) m
    po-ok ⟨ y ⟩ xs m ok =
      subst (λ L → Ok L m) (sym (++-assoc (poL w y) [ ⟨ y ⟩ ] xs))
            (poL-ok w y (⟨ y ⟩ ∷ xs) m (m , refl , ok))

    poL-ok : ∀ {H} (a : WFFun ∅ₖ H) (y : ⟦ TF H ⟧SF N) (xs : List N) (m : ℕ)
           → Ok xs (idc H (coerce-μ-out a N y) + m) → Ok (poL a y ++ xs) m
    poL-ok (wf-K _)      y        xs m ok = ok
    poL-ok wf-Id         t        xs m ok = po-ok t xs m ok
    poL-ok (wf-Sum a b)  (inj₁ x) xs m ok = poL-ok a x xs m ok
    poL-ok (wf-Sum a b)  (inj₂ y) xs m ok = poL-ok b y xs m ok
    poL-ok {H₁ ⊗ H₂} (wf-Prod a b) (x , y) xs m ok =
      subst (λ L → Ok L m) (sym (++-assoc (poL a x) (poL b y) xs))
            (poL-ok a x (poL b y ++ xs) m
               (poL-ok b y xs (idc H₁ (coerce-μ-out a N x) + m)
                  (subst (Ok xs) (swap3 (idc H₁ (coerce-μ-out a N x)) (idc H₂ (coerce-μ-out b N y)) m) ok)))

  -- the machine's fold starts from the root's post-order and an empty stack
  root-ok : ∀ (t : N) → Ok (FI [ t ] []) 0
  root-ok t = po-ok t [] 0 tt
