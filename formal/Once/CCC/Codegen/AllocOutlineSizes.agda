-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocOutlineSizes — the call mode's sizes (D482).
--
-- The routines are made for the program's distinct sizes (`dsizes P`): each is
-- one of the outlined program's sizes (its routine's), each is one word at
-- least (a size is an allocation's or a free's, `AllocMinI`), and every size of
-- the program is among them.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocOutlineSizes {FS : FrameSemantics} where

open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-deduplicate⁺; ∈-deduplicate⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.AllocMin using (AllocMinI)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (fetch)
open import Once.CCC.Codegen.AllocExpand using (prim-routines; skip; skip-label; outline; site-call)
open import Once.CCC.Codegen.AllocExpandClasses using (size-of; sizes; dsizes; Sz)
open import Once.CCC.Codegen.AllocExpandClasses using (module Fetch)

------------------------------------------------------------------------
-- An instruction's size, viewed
------------------------------------------------------------------------

data SizeV : AbstractInstr → Set where
  szv-a    : ∀ k → SizeV (instr-alloc-heap k)
  szv-f    : ∀ k → SizeV (instr-free-heap k)
  szv-none : ∀ {i} → size-of i ≡ [] → SizeV i

size-view : ∀ i → SizeV i
size-view mov-to-output                      = szv-none refl
size-view mov-to-input                       = szv-none refl
size-view load-indirect                      = szv-none refl
size-view load-indirect-suc                  = szv-none refl
size-view (load-from-slot x)                 = szv-none refl
size-view (store-at-slot x)                  = szv-none refl
size-view store-indirect                     = szv-none refl
size-view store-indirect-suc                 = szv-none refl
size-view (lea-slot x)                       = szv-none refl
size-view (restore-input x)                  = szv-none refl
size-view (instr-alloc-stack x)              = szv-none refl
size-view (instr-dealloc-stack x)            = szv-none refl
size-view (instr-reclaim-to x)               = szv-none refl
size-view (instr-push-frame x)               = szv-none refl
size-view instr-pop-frame                    = szv-none refl
size-view instr-call-closure                 = szv-none refl
size-view (worklist-init x)                  = szv-none refl
size-view (worklist-push x)                  = szv-none refl
size-view (worklist-pop x)                   = szv-none refl
size-view (worklist-check x)                 = szv-none refl
size-view (instr-sigop si)                   = szv-none refl
size-view (instr-load-const p v)             = szv-none refl
size-view (instr-load-code-addr l)           = szv-none refl
size-view instr-save-closure-reg             = szv-none refl
size-view (instr-load-tag-lit n)             = szv-none refl
size-view (instr-alloc-heap k)               = szv-a k
size-view (instr-reg-op op)                  = szv-none refl
size-view (instr-free-heap k)                = szv-f k
size-view (instr-room k)                     = szv-none refl
size-view (load-at k)                        = szv-none refl
size-view (store-at k)                       = szv-none refl
size-view (addr-at k)                        = szv-none refl
size-view (load-rec k)                       = szv-none refl
size-view (store-rec k)                      = szv-none refl
size-view (instr-ctrl (c-label l))           = szv-none refl
size-view (instr-ctrl (c-jmp l))             = szv-none refl
size-view (instr-ctrl (c-branch-tag-zero l)) = szv-none refl
size-view (instr-ctrl (c-entry e b))         = szv-none refl
size-view (instr-ctrl (c-call-fn f))         = szv-none refl
size-view (instr-ctrl (c-ret b))             = szv-none refl
size-view (instr-ctrl (c-start b rsv))           = szv-none refl
size-view (instr-ctrl c-leave)               = szv-none refl

sizes-++ : ∀ xs ys → sizes (xs ++ ys) ≡ sizes xs ++ sizes ys
sizes-++ []       ys = refl
sizes-++ (x ∷ xs) ys = trans (cong (size-of x ++_) (sizes-++ xs ys)) (sym (Data.List.Properties.++-assoc (size-of x) (sizes xs) (sizes ys)))
  where import Data.List.Properties

-- a size of the program: an allocation's or a free's, somewhere
size-at : ∀ P k → k ∈ sizes P → Σ ℕ λ n → (fetch P n ≡ just (instr-alloc-heap k)) ⊎ (fetch P n ≡ just (instr-free-heap k))
size-at []      k ()
size-at (x ∷ P) k m = at (size-view x) m
  where
    up : (Σ ℕ λ n → (fetch P n ≡ just (instr-alloc-heap k)) ⊎ (fetch P n ≡ just (instr-free-heap k)))
       → Σ ℕ λ n → (fetch (x ∷ P) n ≡ just (instr-alloc-heap k)) ⊎ (fetch (x ∷ P) n ≡ just (instr-free-heap k))
    up (n , e) = suc n , e
    at : ∀ {y} → SizeV y → k ∈ size-of y ++ sizes P → Σ ℕ λ n → (fetch (y ∷ P) n ≡ just (instr-alloc-heap k)) ⊎ (fetch (y ∷ P) n ≡ just (instr-free-heap k))
    at (szv-a k′) (here refl) = 0 , inj₁ refl
    at (szv-a k′) (there m′)  = let (n , e) = size-at P k m′ in suc n , e
    at (szv-f k′) (here refl) = 0 , inj₂ refl
    at (szv-f k′) (there m′)  = let (n , e) = size-at P k m′ in suc n , e
    at {y} (szv-none e) m′    = let (n , e′) = size-at P k (subst (λ z → k ∈ z ++ sizes P) e m′) in suc n , e′

-- ★ the routines' sizes are the outlined program's
routine-sizes : ∀ ks k → k ∈ ks → k ∈ sizes (prim-routines ks)
routine-sizes (k′ ∷ ks) k (here refl) = here refl
routine-sizes (k′ ∷ ks) k (there m)   = there (there (routine-sizes ks k m))

outline-sz : ∀ ks b rsv T k → k ∈ ks → Sz (outline ks (instr-ctrl (c-start b rsv) ∷ T)) k
outline-sz ks b rsv T k m =
  subst (k ∈_) (sym (sizes-++ (skip ks) (map site-call T)))
    (∈-++⁺ˡ (subst (k ∈_) (sym (sizes-++ (prim-routines ks) (instr-ctrl (c-label skip-label) ∷ []))) (∈-++⁺ˡ (routine-sizes ks k m))))

-- ★ the program's distinct sizes: one word at least
dsizes-pos : ∀ P → All AllocMinI P → ∀ k → k ∈ dsizes P → 1 ≤ k
dsizes-pos P am k m = pos (size-at P k (∈-deduplicate⁻ Data.Nat.Properties._≟_ (sizes P) m))
  where
    lk : ∀ n {i} → fetch P n ≡ just i → AllocMinI i
    lk n {i} f = Data.List.Relation.Unary.All.lookup am (fetch-∈ P n f)
      where
        fetch-∈ : ∀ (xs : AbstractTrace) n′ {j} → fetch xs n′ ≡ just j → j ∈ xs
        fetch-∈ (x ∷ xs) zero    refl = here refl
        fetch-∈ (x ∷ xs) (suc n′) e   = there (fetch-∈ xs n′ e)
    pos : (Σ ℕ λ n → (fetch P n ≡ just (instr-alloc-heap k)) ⊎ (fetch P n ≡ just (instr-free-heap k))) → 1 ≤ k
    pos (n , inj₁ f) = lk n f
    pos (n , inj₂ f) = lk n f

-- ★ every size of the program is among them
in-dsizes : ∀ P n k → (fetch P n ≡ just (instr-alloc-heap k)) ⊎ (fetch P n ≡ just (instr-free-heap k)) → k ∈ dsizes P
in-dsizes P n k (inj₁ f) = ∈-deduplicate⁺ Data.Nat.Properties._≟_ (Fetch.sz-alloc {FS} P n k f)
in-dsizes P n k (inj₂ f) = ∈-deduplicate⁺ Data.Nat.Properties._≟_ (Fetch.sz-free {FS} P n k f)
