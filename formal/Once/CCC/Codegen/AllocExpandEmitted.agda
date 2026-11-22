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
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; exp-view; ExpView; ev-alloc; ev-free; ev-start; ev-same)

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

------------------------------------------------------------------------
-- The expansion's own code: its instructions' kinds
------------------------------------------------------------------------

open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Maybe.Properties using (just-injective)
open import Once.CCC.Label using (LabelId)

all-fetch : ∀ {Q : AbstractInstr → Set} (xs : AbstractTrace) r {j} → All Q xs → fetch xs r ≡ just j → Q j
all-fetch []       r       []       ()
all-fetch (x ∷ xs) zero    (q ∷ _)  refl = q
all-fetch (x ∷ xs) (suc r) (_ ∷ qs) e    = all-fetch xs r qs e

data GenCtrl : FlatCtrl → Set where
  gc-br  : ∀ s → GenCtrl (c-branch-tag-zero (lb-bump s))
  gc-jmp : ∀ s → GenCtrl (c-jmp (lb-done s))
  gc-lbl : ∀ l → GenCtrl (c-label l)

data Gen : AbstractInstr → Set where
  g-out   : Gen mov-to-output
  g-in    : Gen mov-to-input
  g-srec  : ∀ w → w < rec-size → Gen (store-rec w)
  g-lrec  : ∀ w → w < rec-size → Gen (load-rec w)
  g-lat0  : Gen (load-at 0)
  g-sat0  : Gen (store-at 0)
  g-tag0  : Gen (instr-load-tag-lit 0)
  g-alloc : ∀ n → 1 ≤ n → Gen (instr-alloc-heap n)
  g-ctrl  : ∀ c → GenCtrl c → Gen (instr-ctrl c)

module Code (C : Classes) (small : 3 + count C ≤ rec-size) (in-range : ∀ k → cls C k < count C) (fits : ∀ k → k ≤ bsz C k) where
  open import Data.Nat.Properties using (<-≤-trans; ≤-trans; +-monoʳ-<; ≤-<-trans; m≤m+n)

  head< : ∀ c → c < count C → head-word c < rec-size
  head< c lt = <-≤-trans (+-monoʳ-< 3 lt) small

  w1 : w-s1 < rec-size
  w1 = s≤s (s≤s z≤n)
  w2 : w-s2 < rec-size
  w2 = s≤s (s≤s (s≤s z≤n))

  alloc-gen : ∀ site k → 1 ≤ k → All Gen (alloc-code C site k)
  alloc-gen site k one =
    g-out ∷ g-srec _ w1 ∷ g-lrec _ hl ∷ g-in ∷ g-ctrl _ (gc-br site) ∷ g-lat0 ∷ g-srec _ hl
    ∷ g-out ∷ g-srec _ w2 ∷ g-lrec _ w1 ∷ g-in ∷ g-lrec _ w2 ∷ g-ctrl _ (gc-jmp site) ∷ g-ctrl _ (gc-lbl _)
    ∷ g-lrec _ w1 ∷ g-in ∷ g-alloc _ (≤-trans one (fits k)) ∷ g-ctrl _ (gc-lbl _) ∷ []
    where hl = head< (cls C k) (in-range k)

  free-gen : ∀ k → All Gen (free-code C k)
  free-gen k = g-srec _ w1 ∷ g-lrec _ hl ∷ g-sat0 ∷ g-out ∷ g-srec _ hl ∷ g-lrec _ w1 ∷ []
    where hl = head< (cls C k) (in-range k)

  heads-gen : ∀ c → c ≤ count C → All Gen (heads C c)
  heads-gen zero    _  = []
  heads-gen (suc c) le = g-srec _ (head< c le) ∷ heads-gen c (≤-trans (m≤m+n c 1′) (sub le))
    where
      1′ = 1
      sub : suc c ≤ count C → c + 1 ≤ count C
      sub le′ = subst (_≤ count C) (sym (Data.Nat.Properties.+-comm c 1)) le′

  setup-gen : All Gen (setup C)
  setup-gen = g-srec _ w1 ∷ g-out ∷ g-srec _ w2 ∷ g-alloc 1 (s≤s z≤n)
            ∷ ++⁺ (heads-gen (count C) Data.Nat.Properties.≤-refl)
                  (g-in ∷ g-tag0 ∷ g-sat0 ∷ g-lrec _ w2 ∷ g-in ∷ g-lrec _ w1 ∷ [])

  -- ★ an instruction of one primitive instruction's expansion: that one itself
  -- (kept, or the start, at its offset 0), or of the expansion's own code
  Kept : ℕ → AbstractInstr → Set
  Kept s i = (expand-at C s i ≡ i ∷ []) ⊎ (Σ ℕ λ b → i ≡ instr-ctrl (c-start b))

  gen-of : ∀ s i r {j} → (∀ n → i ≡ instr-alloc-heap n → 1 ≤ n) → fetch (expand-at C s i) r ≡ just j
         → ((r ≡ 0) × (j ≡ i) × Kept s i) ⊎ Gen j
  gen-of s i r {j} am e = by (exp-view C s i) e
    where
      by : ExpView C s i → fetch (expand-at C s i) r ≡ just j → ((r ≡ 0) × (j ≡ i) × Kept s i) ⊎ Gen j
      by (ev-alloc k) f = inj₂ (all-fetch (alloc-code C s k) r (alloc-gen s k (am k refl)) f)
      by (ev-free k)  f = inj₂ (all-fetch (free-code C k) r (free-gen k) f)
      by (ev-start b) f = st r f
        where
          st : ∀ r′ → fetch (instr-ctrl (c-start b) ∷ setup C) r′ ≡ just j → ((r′ ≡ 0) × (j ≡ instr-ctrl (c-start b)) × Kept s (instr-ctrl (c-start b))) ⊎ Gen j
          st zero    f′ = inj₁ (refl , sym (just-injective f′) , inj₂ (b , refl))
          st (suc r′) f′ = inj₂ (all-fetch (setup C) r′ setup-gen f′)
      by (ev-same eq) f = sm r (subst (λ xs → fetch xs r ≡ just j) eq f)
        where
          sm : ∀ r′ → fetch (i ∷ []) r′ ≡ just j → ((r′ ≡ 0) × (j ≡ i) × Kept s i) ⊎ Gen j
          sm zero    f′ = inj₁ (refl , sym (just-injective f′) , inj₁ eq)
          sm (suc r′) ()
