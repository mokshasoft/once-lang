-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageSymsX — the allocator's expansion of an image keeps its
-- file's symbols well formed (D468/D470, plan 0.146 B1.6 item 3c4).
--
-- What the expansion holds is a kept instruction of the image's, or of an
-- alloc's, a free's or the start's code (`in-exp`). Its labels are the image's
-- and each alloc site's two (`alloc-label`), told apart by owner and index;
-- its entries are the image's.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Data.Nat using (ℕ)

module Once.LinCore.ImageSymsX
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Data.Nat using (zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (LabelId; EntryId; module LabelId)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.LinCore.LabelsC fmt ans bw using (module LabsC)

module X {FS : FrameSemantics} (C : Classes) where
  open FlatMachine {FS} using (fetch; label-of?; entry-of?)
  open LabsC {FS} using (Labs; lab; Labs-++; Ents; ent; Ents-++)
  open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; exp-view; ExpView; ev-alloc; ev-free; ev-start; ev-same)

  ------------------------------------------------------------------------
  -- ★ What the expansion holds
  ------------------------------------------------------------------------

  data InExp (s : ℕ) (P : AbstractTrace) (i : AbstractInstr) : Set where
    in-kept  : i ∈ P → (∀ k → i ≡ instr-alloc-heap k → ⊥) → (∀ k → i ≡ instr-free-heap k → ⊥) → InExp s P i
    in-alloc : ∀ n k → fetch P n ≡ just (instr-alloc-heap k) → i ∈ alloc-code C (n + s) k → InExp s P i
    in-free  : ∀ k → i ∈ free-code C k → InExp s P i
    in-setup : i ∈ setup C → InExp s P i

  in-exp : ∀ s P {i} → i ∈ expand-from C s P → InExp s P i
  in-exp s []      ()
  in-exp s (x ∷ P) {i} m = by (∈-++⁻ (expand-at C s x) m)
    where
      at : ExpView C s x → i ∈ expand-at C s x → InExp s (x ∷ P) i
      at (ev-alloc k) m′ = in-alloc 0 k refl m′
      at (ev-free k)  m′ = in-free k m′
      at (ev-start b) (here refl) = in-kept (here refl) (λ _ ()) (λ _ ())
      at (ev-start b) (there m′)  = in-setup m′
      at (ev-same eq) m′ = one (subst (i ∈_) eq m′)
        where
          one : i ∈ (x ∷ []) → InExp s (x ∷ P) i
          one (here refl) = in-kept (here refl) (λ k e → not-alloc k e) (λ k e → not-free k e)
            where
              not-alloc : ∀ k → x ≡ instr-alloc-heap k → ⊥
              not-alloc k refl = len (cong Data.List.length eq)
                where len : 18 ≡ 1 → ⊥
                      len ()
              not-free : ∀ k → x ≡ instr-free-heap k → ⊥
              not-free k refl = len (cong Data.List.length eq)
                where len : 6 ≡ 1 → ⊥
                      len ()
          one (there ())
      up : InExp (suc s) P i → InExp s (x ∷ P) i
      up (in-kept m′ na nf) = in-kept (there m′) na nf
      up (in-alloc n k f m′) = in-alloc (suc n) k f (subst (λ z → i ∈ alloc-code C z k) (Data.Nat.Properties.+-suc n s) m′)
      up (in-free k m′) = in-free k m′
      up (in-setup m′) = in-setup m′
      by : (i ∈ expand-at C s x) ⊎ (i ∈ expand-from C (suc s) P) → InExp s (x ∷ P) i
      by (inj₁ m′) = at (exp-view C s x) m′
      by (inj₂ m′) = up (in-exp (suc s) P m′)

  -- …and an alloc's code is in it, whole
  alloc-in : ∀ s P n k → fetch P n ≡ just (instr-alloc-heap k) → ∀ {i} → i ∈ alloc-code C (n + s) k → i ∈ expand-from C s P
  alloc-in s []      n       k () m
  alloc-in s (x ∷ P) zero    k refl m = ∈-++⁺ˡ m
  alloc-in s (x ∷ P) (suc n) k f {i} m =
    ∈-++⁺ʳ (expand-at C s x) (alloc-in (suc s) P n k f (subst (λ z → i ∈ alloc-code C z k) (sym (Data.Nat.Properties.+-suc n s)) m))

  -- …and so is every kept instruction
  kept-in : ∀ s P {i} → i ∈ P → (∀ k → i ≡ instr-alloc-heap k → ⊥) → (∀ k → i ≡ instr-free-heap k → ⊥) → i ∈ expand-from C s P
  kept-in s (x ∷ P) (here refl) na nf = ∈-++⁺ˡ (head-in (exp-view C s x))
    where
      head-in : ExpView C s x → x ∈ expand-at C s x
      head-in (ev-alloc k) = ⊥-elim (na k refl)
      head-in (ev-free k)  = ⊥-elim (nf k refl)
      head-in (ev-start b) = here refl
      head-in (ev-same eq) = subst (x ∈_) (sym eq) (here refl)
  kept-in s (x ∷ P) (there m) na nf = ∈-++⁺ʳ (expand-at C s x) (kept-in (suc s) P m na nf)
