-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandStep — the renaming through memory (D468, 3c3b).
--
-- The memory half of the expansion's simulation, below the instructions: the
-- renaming commutes with offsets and fixes every non-pointer value; a write at a
-- live cell, done at its renamed cell, keeps the live cells related (the
-- renaming is injective on the live blocks) and leaves every other expanded word
-- — the record, the sentinel, the free blocks — as it was.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandStep {FS : FrameSemantics} where

open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef; offsetHL; _≟HL_)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Codegen.AllocExpandRel {FS} using (ref-of; rhl; rloc; rv; blk)
open MemOps {FS} using (writeHeapMem; writeHeapMem-aux)

------------------------------------------------------------------------
-- The renaming on addresses and values
------------------------------------------------------------------------

rhl-off : ∀ ρ (hl : HeapLocation) k → rhl ρ (offsetHL hl k) ≡ offsetHL (rhl ρ hl) k
rhl-off ρ (heap-loc r o) k = refl

ref-off : ∀ (hl : HeapLocation) k → ref-of (offsetHL hl k) ≡ ref-of hl
ref-off (heap-loc r o) k = refl

-- the renamed cell of a block is the block's renamed ref at the same offset
rhl-at : ∀ ρ r o → rhl ρ (heap-loc (mkHeapRef r) o) ≡ heap-loc (mkHeapRef (ρ r)) o
rhl-at ρ r o = refl

-- distinct live cells stay distinct (the renaming injective on their refs)
rhl-apart : ∀ ρ (hl hl′ : HeapLocation) → (ref-of hl ≡ ref-of hl′ → ¬ HeapLocation.heap-offset hl ≡ HeapLocation.heap-offset hl′)
          → (ρ (ref-of hl) ≡ ρ (ref-of hl′) → ref-of hl ≡ ref-of hl′)
          → ¬ rhl ρ hl ≡ rhl ρ hl′
rhl-apart ρ (heap-loc (mkHeapRef r) o) (heap-loc (mkHeapRef r′) o′) off inj e =
  off (inj (cong (λ x → HeapRef.ref-id (HeapLocation.heap-ref x)) e)) (cong HeapLocation.heap-offset e)

-- cells are equal when their refs and offsets are
hl-eq : ∀ (hl hl′ : HeapLocation) → ref-of hl ≡ ref-of hl′ → HeapLocation.heap-offset hl ≡ HeapLocation.heap-offset hl′ → hl ≡ hl′
hl-eq (heap-loc (mkHeapRef r) o) (heap-loc (mkHeapRef .r) .o) refl refl = refl

------------------------------------------------------------------------
-- A write, done on both sides
------------------------------------------------------------------------

module _ (ρ : ℕ → ℕ) (Lv : ℕ → Set)
         (inj : ∀ r r′ → Lv r → Lv r′ → ρ r ≡ ρ r′ → r ≡ r′) where

  -- the live cells of `h` are `g`'s at their renamed cells
  HeapR : HeapMem FS → HeapMem FS → Set
  HeapR h g = ∀ hl v → Lv (ref-of hl) → h hl ≡ just v → g (rhl ρ hl) ≡ just (rv ρ v)

  private
    w-same : ∀ (h : HeapMem FS) hl v → writeHeapMem h hl v hl ≡ just v
    w-same h hl v = w-same-aux (hl ≟HL hl)
      where
        w-same-aux : ∀ (d : Relation.Nullary.Dec (hl ≡ hl)) → writeHeapMem-aux {hl = hl} {hl' = hl} d (h hl) v ≡ just v
        w-same-aux (yes _) = refl
        w-same-aux (no ne) = Data.Empty.⊥-elim (ne refl)
          where import Data.Empty

    w-other : ∀ (h : HeapMem FS) hl hl′ v → ¬ hl ≡ hl′ → writeHeapMem h hl v hl′ ≡ h hl′
    w-other h hl hl′ v ne = w-other-aux (hl ≟HL hl′)
      where
        w-other-aux : ∀ (d : Relation.Nullary.Dec (hl ≡ hl′)) → writeHeapMem-aux {hl = hl} {hl' = hl′} d (h hl′) v ≡ h hl′
        w-other-aux (yes e) = Data.Empty.⊥-elim (ne e)
          where import Data.Empty
        w-other-aux (no _)  = refl

  -- ★ a write at a live cell, and at its renamed cell, keeps the live cells related
  heap-write : ∀ {h g} hl₀ v → Lv (ref-of hl₀) → HeapR h g
             → HeapR (writeHeapMem h hl₀ v) (writeHeapMem g (rhl ρ hl₀) (rv ρ v))
  heap-write {h} {g} hl₀ v₀ lv₀ R hl v lv e = go (hl₀ ≟HL hl)
    where
      go : Relation.Nullary.Dec (hl₀ ≡ hl) → writeHeapMem g (rhl ρ hl₀) (rv ρ v₀) (rhl ρ hl) ≡ just (rv ρ v)
      go (yes refl) = trans (w-same g (rhl ρ hl₀) (rv ρ v₀)) (cong (λ z → just (rv ρ z)) (just-inj (trans (sym (w-same h hl₀ v₀)) e)))
        where
          just-inj : ∀ {a b : StoredValue FS} → just a ≡ just b → a ≡ b
          just-inj refl = refl
      go (no ne) =
        trans (w-other g (rhl ρ hl₀) (rhl ρ hl) (rv ρ v₀)
                 (rhl-apart ρ hl₀ hl (λ er eo → ne (hl-eq hl₀ hl er eo)) (inj (ref-of hl₀) (ref-of hl) lv₀ lv)))
              (R hl v lv (trans (sym (w-other h hl₀ hl v₀ ne)) e))

  -- ★ a write at a renamed live cell leaves an expanded word no live block is renamed to
  heap-write-off : ∀ (g : HeapMem FS) hl₀ v (q : HeapLocation) → Lv (ref-of hl₀)
                 → (∀ r → Lv r → ¬ ρ r ≡ ref-of q)
                 → writeHeapMem g (rhl ρ hl₀) v q ≡ g q
  heap-write-off g hl₀ v q lv₀ miss = w-other g (rhl ρ hl₀) q v (λ e → miss (ref-of hl₀) lv₀ (cong ref-of e))
