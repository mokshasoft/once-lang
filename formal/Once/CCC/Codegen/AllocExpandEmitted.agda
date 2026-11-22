-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandEmitted — the expansion of an image is an image
-- the arch layer runs (D468/D470, plan 0.146 B1.6 item 3c4).
--
-- What the arch layer reads of a program (`RunContext.Emitted`) holds of the
-- expansion when it holds of the primitive program: everything the expansion
-- fetches is a primitive instruction's own, or of an alloc's, a free's or the
-- start's code (`fetch-inv`), and that code is the arch layer's (record words
-- below `rec-size`: a class's head word is `3 + c`, `c < count C ≤ 61`), has
-- no start, no call, no entry and no code word; the entries, the functions
-- and the code words are found where the pc map puts them (`ft-exp`).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandEmitted {FS : FrameSemantics} where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (fetch)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off)

------------------------------------------------------------------------
-- A fetch from an append: from its left part, or past it
------------------------------------------------------------------------

fetch-split : ∀ (xs ys : AbstractTrace) k {j} → fetch (xs ++ ys) k ≡ just j
            → (fetch xs k ≡ just j) ⊎ (Σ ℕ λ k′ → (k ≡ length xs + k′) × (fetch ys k′ ≡ just j))
fetch-split []       ys k       e = inj₂ (k , refl , e)
fetch-split (x ∷ xs) ys zero    e = inj₁ e
fetch-split (x ∷ xs) ys (suc k) e = up (fetch-split xs ys k e)
  where
    up : ∀ {j} → (fetch xs k ≡ just j) ⊎ (Σ ℕ λ k′ → (k ≡ length xs + k′) × (fetch ys k′ ≡ just j))
       → (fetch (x ∷ xs) (suc k) ≡ just j) ⊎ (Σ ℕ λ k′ → (suc k ≡ length (x ∷ xs) + k′) × (fetch ys k′ ≡ just j))
    up (inj₁ f)             = inj₁ f
    up (inj₂ (k′ , eq , f)) = inj₂ (k′ , cong suc eq , f)

------------------------------------------------------------------------
-- ★ What the expansion fetches: an instruction of some primitive one's expansion
------------------------------------------------------------------------

module _ (C : Classes) where

  record From (s : ℕ) (P : AbstractTrace) (k : ℕ) (j : AbstractInstr) : Set where
    constructor from
    field
      n   : ℕ
      i   : AbstractInstr
      r   : ℕ
      f-P : fetch P n ≡ just i
      f-k : k ≡ off C s P n + r
      f-e : fetch (expand-at C (n + s) i) r ≡ just j

  fetch-inv : ∀ s P k {j} → fetch (expand-from C s P) k ≡ just j → From s P k j
  fetch-inv s []      k ()
  fetch-inv s (x ∷ P) k {j} e = by (fetch-split (expand-at C s x) (expand-from C (suc s) P) k e)
    where
      by : (fetch (expand-at C s x) k ≡ just j)
           ⊎ (Σ ℕ λ k′ → (k ≡ length (expand-at C s x) + k′) × (fetch (expand-from C (suc s) P) k′ ≡ just j))
         → From s (x ∷ P) k j
      by (inj₁ f) = from 0 x k refl refl f
      by (inj₂ (k′ , eq , f)) = shift (fetch-inv (suc s) P k′ f)
        where
          shift : From (suc s) P k′ j → From s (x ∷ P) k j
          shift (from n i r fP fk fe) =
            from (suc n) i r fP
              (trans eq (trans (cong (length (expand-at C s x) +_) fk)
                               (sym (Data.Nat.Properties.+-assoc (length (expand-at C s x)) (off C (suc s) P n) r))))
              (subst (λ z → fetch (expand-at C z i) r ≡ just j) (Data.Nat.Properties.+-suc n s) fe)
