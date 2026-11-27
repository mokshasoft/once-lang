-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageSyms — plan 0.146 B1.7 step 3 (D466): ★ THE NEW IMAGE'S
-- FILE IS WELL-FORMED, as symbols: what `AsmWF` reads of it.
--
--   * every symbol the file defines is defined once: the image's labels and
--     entries are distinct (`LabelsI.image-dst`, `EntriesI.image-edst`), each
--     owned by a block (`once-lincore.b<j>`, D466), so their symbols are
--     (`LabelSymInj.sym-inj`); they start with `.` or name a block, the arith
--     blocks' a digest, `once_main` neither;
--   * every symbol it references is defined or an extern: a jump's label
--     (`Jumps`: the code jumps only to labels it defines), a call's block and
--     a code word's trampoline (`EntriesI.image-fn`/`image-tramp`), an op's
--     block (`ImageOwned`) or, external, an extern (`ImageExterns`), the
--     Host's `leave` and `exhausted`.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to AP-++⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any
import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import Once.Postulates using (toList-++; toList∘fromList)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Name using (CanonicalName; canonical; bare; module CanonicalName)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.Type using (FitsInReg)
open import Once.Semantics.Machine using (LitPayload)
open import Once.SigOp.Info using (SigOpInfo; sigop-owner; module SigOpInfo)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (Label; once; callee; LabelId; EntryId; e-thunk; e-fn; labelSym; thunkSym)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.CCC.Codegen.RoomChecksFacts using (fold-room; All-fold-room)
open import Once.CCC.Codegen.ImageSymbols using (instr-defs; instr-refs; adefs; arefs; entry-symbol; part-refs; stack-refs)
open import Once.CCC.Codegen.ImageExterns using (image-externs; ext-in; ImageWF; image-externs-valid)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Target.SymbolFresh using (host-leave-symbol; host-exhausted-symbol; alloc-record-symbol; record≢osp)
open import Once.Target.SymbolInjective using (Peel; PeelS; once-symbol-path-injective-peel)
open import Once.Arith.Machine.IR using (ArithBlock; module ArithBlock)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Arith.SigOp.AsBlock using (Canonical)
open import Once.Compile.Emit using (block-symbol; block-syms)
import Once.Adequacy.BlockTable as BT
open import Once.Adequacy.LabelSymbols using (DefL; head-of; once-head; thunk-head; fn-head)
open import Once.Adequacy.LabelSymInj using (GoodId; GoodL; syms-dst)
open import Once.Adequacy.ImageUnique using (ilab; dlabs; adefs-labs; dlabs-def; entry≢osp; BlockSym; blocks-unique; blocks-sym)

module Once.LinCore.ImageSyms
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; Lit)
open Sig using (info)
open import Once.LinCore.Image fmt bw
open import Once.LinCore.Keys fmt bw
open Univ using (ops)
open import Once.LinCore.Layout fmt bw
open import Once.LinCore.Values fmt bw using (wsz)
open import Once.LinCore.Lower fmt bw
open import Once.LinCore.MoveCode using (mvPS; mvSP)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.LabelsC fmt ans bw using (module LabsC)
import Once.LinCore.LabelsC
import Once.LinCore.LabelsI
import Once.LinCore.EntriesI
import Once.LinCore.ImageAll
import Once.LinCore.ImageOwned
import Once.LinCore.ImageBlocks
open import Once.LinCore.Jumps fmt ans bw using (jump-of; jmp; Jmps; Jmps-nj; mvPS-nj; mvSP-nj; module Closed; module Free)

import Once.CCC.Codegen.AllocExpand
import Once.CCC.Codegen.AllocExpandClasses
import Once.LinCore.ImageSymsX
-- D488 (a3): a check's references, per part: the record (its limit), then `once_exhausted`
-- (D491: the stack part first — the record, `once_exhausted`, the record)
room-refs-G : ∀ {G : String → Set} → G alloc-record-symbol → G host-exhausted-symbol
            → ∀ (k : Room) → All G (instr-refs (instr-room k))
room-refs-G {G} rg eg k = ++⁺ (sr (Room.room-s k)) (pr (Room.room-h k))
  where
    pr : ∀ n → All G (part-refs n)
    pr zero    = []
    pr (suc _) = rg ∷ eg ∷ []
    sr : ∀ n → All G (stack-refs n)
    sr zero    = []
    sr (suc _) = rg ∷ eg ∷ rg ∷ []

module LI = Once.LinCore.LabelsI fmt ans bw
module EI = Once.LinCore.EntriesI fmt ans bw
module IAll = Once.LinCore.ImageAll fmt ans bw

------------------------------------------------------------------------
-- 1. ★ A BLOCK'S NAME READS BACK (D466), and is no arith block's.
------------------------------------------------------------------------

opaque
  unfolding nameOf

  nameOf-good : ∀ j → All PeelS (CanonicalName.parts (nameOf j))
  nameOf-good j = (_ , _ , refl , refl)
                ∷ subst Peel (sym (toList∘fromList ('b' ∷ Data.Nat.Show.charsInBase 10 j))) (_ , _ , refl , refl) ∷ []
    where import Data.Nat.Show

  nameOf-two : ∀ j → length (CanonicalName.parts (nameOf j)) ≡ 2
  nameOf-two j = refl

  -- D482: a block's name leads with `once-lincore`
  nameOf-lead : ∀ j → Data.List.take 1 (CanonicalName.parts (nameOf j)) ≡ "once-lincore" ∷ []
  nameOf-lead j = refl

-- an arith block's name reads back too
block-good : ∀ d → All PeelS (CanonicalName.parts (bare ("arith.block." ++ˢ d)))
block-good d = subst Peel (sym (toList-++ "arith.block." d)) (_ , _ , refl , refl) ∷ []

-- ★ a block's symbol is no arith block's
name≢block : ∀ j d → once-symbol-path (nameOf j) ≢ once-symbol-path (bare ("arith.block." ++ˢ d))
name≢block j d e = two≢one (trans (sym (nameOf-two j)) (cong (λ c → length (CanonicalName.parts c))
                     (once-symbol-path-injective-peel (nameOf j) (bare ("arith.block." ++ˢ d)) (nameOf-good j) (block-good d) e)))
  where two≢one : 2 ≡ 1 → ⊥
        two≢one ()

-- D482: the call mode's routines, their names read back too
alloc-good : ∀ k → All PeelS (CanonicalName.parts (Once.CCC.Codegen.AllocExpand.alloc-fn k))
alloc-good k = (_ , _ , refl , refl) ∷ subst Peel (sym (toList-++ "a" (Once.Target.Symbol.showNat k))) (_ , _ , refl , refl) ∷ []

free-good : ∀ k → All PeelS (CanonicalName.parts (Once.CCC.Codegen.AllocExpand.free-fn k))
free-good k = (_ , _ , refl , refl) ∷ subst Peel (sym (toList-++ "f" (Once.Target.Symbol.showNat k))) (_ , _ , refl , refl) ∷ []

-- a routine's symbol is no arith block's (two parts, theirs one)
routine≢block : ∀ (cn : CanonicalName) → All PeelS (CanonicalName.parts cn) → length (CanonicalName.parts cn) ≡ 2
              → ∀ d → once-symbol-path cn ≢ once-symbol-path (bare ("arith.block." ++ˢ d))
routine≢block cn g two d e = two≢one (trans (sym two) (cong (λ c → length (CanonicalName.parts c))
                               (once-symbol-path-injective-peel cn (bare ("arith.block." ++ˢ d)) g (block-good d) e)))
  where two≢one : 2 ≡ 1 → ⊥
        two≢one ()

-- the labels and entries of the image (D482: and of the outlined image's skip and routines)
data ShapeL : Label → Set where
  s-jl : ∀ j k → ShapeL (once (jl j k))
  s-fn : ∀ j → ShapeL (callee (e-fn (nameOf j)))
  s-tl : ∀ j → ShapeL (callee (e-thunk (tl j)))
  s-sk : ShapeL (once Once.CCC.Codegen.AllocExpand.skip-label)
  s-ra : ∀ k → ShapeL (callee (e-fn (Once.CCC.Codegen.AllocExpand.alloc-fn k)))
  s-rf : ∀ k → ShapeL (callee (e-fn (Once.CCC.Codegen.AllocExpand.free-fn k)))

shape-lab : ∀ {y l} → y ≡ once l → (Σ ℕ λ j → Σ ℕ λ k → l ≡ jl j k) → ShapeL y
shape-lab refl (j , k , refl) = s-jl j k

shape-ent : ∀ {y e} → y ≡ callee e → (Σ ℕ λ j → e ≡ e-fn (nameOf j) ⊎ e ≡ e-thunk (tl j)) → ShapeL y
shape-ent refl (j , inj₁ refl) = s-fn j
shape-ent refl (j , inj₂ refl) = s-tl j

shape-good : ∀ {y} → ShapeL y → GoodL y
shape-good (s-jl j k) = refl , nameOf-good j
shape-good (s-fn j)   = nameOf-good j
shape-good (s-tl j)   = refl , nameOf-good j
shape-good s-sk       = refl , ((_ , _ , refl , refl) ∷ [])
shape-good (s-ra k)   = alloc-good k
shape-good (s-rf k)   = free-good k

shape-def : ∀ {y} → ShapeL y → DefL y
shape-def (s-jl j k) = Once.Adequacy.LabelSymbols.d-once
shape-def (s-fn j)   = Once.Adequacy.LabelSymbols.d-callee
shape-def (s-tl j)   = Once.Adequacy.LabelSymbols.d-callee
shape-def s-sk       = Once.Adequacy.LabelSymbols.d-once
shape-def (s-ra k)   = Once.Adequacy.LabelSymbols.d-callee
shape-def (s-rf k)   = Once.Adequacy.LabelSymbols.d-callee

private
  head≢ : ∀ {s t : String} → head-of (toList s) ≡ '.' → head-of (toList t) ≡ 'o' → s ≢ t
  head≢ hs ht e = case trans (sym hs) (trans (cong (λ z → head-of (toList z)) e) ht) of λ ()

-- ★ a label's symbol is no arith block's, and not the entry's
shape≢block : ∀ {y t} → ShapeL y → BlockSym t → labelSym y ≢ t
shape≢block (s-jl j k) (d , refl) = head≢ (once-head (jl j k)) (fn-head (bare ("arith.block." ++ˢ d)))
shape≢block (s-fn j)   (d , refl) = name≢block j d
shape≢block (s-tl j)   (d , refl) = head≢ (thunk-head (tl j)) (fn-head (bare ("arith.block." ++ˢ d)))
shape≢block s-sk       (d , refl) = head≢ (once-head Once.CCC.Codegen.AllocExpand.skip-label) (fn-head (bare ("arith.block." ++ˢ d)))
shape≢block (s-ra k)   (d , refl) = routine≢block (Once.CCC.Codegen.AllocExpand.alloc-fn k) (alloc-good k) refl d
shape≢block (s-rf k)   (d , refl) = routine≢block (Once.CCC.Codegen.AllocExpand.free-fn k) (free-good k) refl d

entry≢shape : ∀ {y} → ShapeL y → entry-symbol ≢ labelSym y
entry≢shape (s-jl j k) e = head≢ (once-head (jl j k)) refl (sym e)
entry≢shape (s-fn j)   e = entry≢osp (nameOf j) e
entry≢shape (s-tl j)   e = head≢ (thunk-head (tl j)) refl (sym e)
entry≢shape s-sk       e = head≢ (once-head Once.CCC.Codegen.AllocExpand.skip-label) refl (sym e)
entry≢shape (s-ra k)   e = entry≢osp (Once.CCC.Codegen.AllocExpand.alloc-fn k) e
entry≢shape (s-rf k)   e = entry≢osp (Once.CCC.Codegen.AllocExpand.free-fn k) e

entry≢block : ∀ {t} → BlockSym t → entry-symbol ≢ t
entry≢block (d , refl) = entry≢osp (bare ("arith.block." ++ˢ d))

-- D472: the allocator record's symbol is no label's, no block's, not the entry's
record≢shape : ∀ {y} → ShapeL y → alloc-record-symbol ≢ labelSym y
record≢shape (s-jl j k) e = head≢ (once-head (jl j k)) refl (sym e)
record≢shape (s-fn j)   e = record≢osp (nameOf j) e
record≢shape (s-tl j)   e = head≢ (thunk-head (tl j)) refl (sym e)
record≢shape s-sk       e = head≢ (once-head Once.CCC.Codegen.AllocExpand.skip-label) refl (sym e)
record≢shape (s-ra k)   e = record≢osp (Once.CCC.Codegen.AllocExpand.alloc-fn k) e
record≢shape (s-rf k)   e = record≢osp (Once.CCC.Codegen.AllocExpand.free-fn k) e

record≢block : ∀ {t} → BlockSym t → alloc-record-symbol ≢ t
record≢block (d , refl) = record≢osp (bare ("arith.block." ++ˢ d))

entry≢record : entry-symbol ≢ alloc-record-symbol
entry≢record ()

------------------------------------------------------------------------
-- 2. A TRACE'S DEFINED LABELS: its jump labels and its entries.
------------------------------------------------------------------------

module DL {FS : FrameSemantics} where
  open FlatMachine {FS} using (label-of?; entry-of?; fetch)
  open LabsC {FS} using (Labs; lab; Ents; ent)

  lo : Maybe LabelId → List Label
  lo (just l) = once l ∷ []
  lo nothing  = []

  le : Maybe EntryId → List Label
  le (just e) = callee e ∷ []
  le nothing  = []

  ilab-sv : ∀ (i : AbstractInstr) → ilab i ≡ lo (label-of? i) ++ le (entry-of? i)
  ilab-sv (instr-ctrl (c-label m)) = refl
  ilab-sv (instr-ctrl (c-entry (e-thunk m) _)) = refl
  ilab-sv (instr-ctrl (c-entry (e-fn f) _)) = refl
  ilab-sv (instr-ctrl (c-jmp _)) = refl
  ilab-sv (instr-ctrl (c-branch-tag-zero _)) = refl
  ilab-sv (instr-ctrl (c-ret _)) = refl
  ilab-sv (instr-ctrl (c-call-fn _)) = refl
  ilab-sv (instr-ctrl (c-start _ _)) = refl
  ilab-sv (instr-ctrl c-leave) = refl
  ilab-sv mov-to-output = refl
  ilab-sv mov-to-input = refl
  ilab-sv load-indirect = refl
  ilab-sv load-indirect-suc = refl
  ilab-sv (load-from-slot _) = refl
  ilab-sv (store-at-slot _) = refl
  ilab-sv store-indirect = refl
  ilab-sv store-indirect-suc = refl
  ilab-sv (lea-slot _) = refl
  ilab-sv (restore-input _) = refl
  ilab-sv (instr-alloc-stack _) = refl
  ilab-sv (instr-dealloc-stack _) = refl
  ilab-sv (instr-reclaim-to _) = refl
  ilab-sv (instr-free-heap _) = refl
  ilab-sv (load-at _) = refl
  ilab-sv (store-at _) = refl
  ilab-sv (addr-at _) = refl
  ilab-sv (load-rec _) = refl
  ilab-sv (store-rec _) = refl
  ilab-sv (instr-room _) = refl
  ilab-sv (instr-push-frame _) = refl
  ilab-sv instr-pop-frame = refl
  ilab-sv instr-call-closure = refl
  ilab-sv (worklist-init _) = refl
  ilab-sv (worklist-push _) = refl
  ilab-sv (worklist-pop _) = refl
  ilab-sv (worklist-check _) = refl
  ilab-sv (instr-sigop _) = refl
  ilab-sv (instr-load-const _ _) = refl
  ilab-sv (instr-load-code-addr _) = refl
  ilab-sv instr-save-closure-reg = refl
  ilab-sv (instr-load-tag-lit _) = refl
  ilab-sv (instr-alloc-heap _) = refl
  ilab-sv (instr-reg-op _) = refl
  private
    -- a jump label apart from a trace's is no defined label of it
    not-once : ∀ {xs l y} → All (l ≢_) (Labs xs) → once l ≡ y
             → (Σ LabelId λ l′ → y ≡ once l′ × l′ ∈ Labs xs) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents xs) → ⊥
    not-once a refl (inj₁ (l′ , refl , m′)) = Data.List.Relation.Unary.All.lookup a m′ refl
    not-once a refl (inj₂ (e′ , () , _))

    not-callee : ∀ {xs e y} → All (e ≢_) (Ents xs) → callee e ≡ y
               → (Σ LabelId λ l′ → y ≡ once l′ × l′ ∈ Labs xs) ⊎ (Σ EntryId λ e′ → y ≡ callee e′ × e′ ∈ Ents xs) → ⊥
    not-callee a refl (inj₁ (l′ , () , _))
    not-callee a refl (inj₂ (e′ , refl , m′)) = Data.List.Relation.Unary.All.lookup a m′ refl

  -- a defined label is a jump label or an entry
  dl-in : ∀ xs {y} → y ∈ dlabs xs → (Σ LabelId λ l → y ≡ once l × l ∈ Labs xs) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents xs)
  dl-in (x ∷ xs) {y} p = go (label-of? x) refl (entry-of? x) refl (subst (λ z → y ∈ z ++ dlabs xs) (ilab-sv x) p)
    where
      rest : y ∈ dlabs xs → ∀ ml → label-of? x ≡ ml → ∀ me → entry-of? x ≡ me
           → (Σ LabelId λ l → y ≡ once l × l ∈ Labs (x ∷ xs)) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents (x ∷ xs))
      rest q ml el me ee = up′ (dl-in xs q)
        where
          up′ : (Σ LabelId λ l → y ≡ once l × l ∈ Labs xs) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents xs)
             → (Σ LabelId λ l → y ≡ once l × l ∈ Labs (x ∷ xs)) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents (x ∷ xs))
          up′ (inj₁ (l , e , m)) = inj₁ (l , e , lab-up (label-of? x) m)
            where lab-up : ∀ mo {l} → l ∈ Labs xs → l ∈ lab mo (Labs xs)
                  lab-up (just _) m′ = there m′
                  lab-up nothing  m′ = m′
          up′ (inj₂ (e′ , e , m)) = inj₂ (e′ , e , ent-up (entry-of? x) m)
            where ent-up : ∀ mo {e} → e ∈ Ents xs → e ∈ ent mo (Ents xs)
                  ent-up (just _) m′ = there m′
                  ent-up nothing  m′ = m′
      go : ∀ ml → label-of? x ≡ ml → ∀ me → entry-of? x ≡ me → y ∈ (lo ml ++ le me) ++ dlabs xs
         → (Σ LabelId λ l → y ≡ once l × l ∈ Labs (x ∷ xs)) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents (x ∷ xs))
      go (just l) el me ee (here e) = inj₁ (l , e , subst (λ z → l ∈ lab z (Labs xs)) (sym el) (here refl))
      go (just l) el (just e′) ee (there (here e)) = inj₂ (e′ , e , subst (λ z → e′ ∈ ent z (Ents xs)) (sym ee) (here refl))
      go (just l) el (just e′) ee (there (there q)) = rest q (just l) el (just e′) ee
      go (just l) el nothing ee (there q) = rest q (just l) el nothing ee
      go nothing el (just e′) ee (here e) = inj₂ (e′ , e , subst (λ z → e′ ∈ ent z (Ents xs)) (sym ee) (here refl))
      go nothing el (just e′) ee (there q) = rest q nothing el (just e′) ee
      go nothing el nothing ee q = rest q nothing el nothing ee

  -- a jump label and an entry are defined labels
  lab-dl : ∀ xs {l} → l ∈ Labs xs → once l ∈ dlabs xs
  lab-dl (x ∷ xs) {l} p = subst (λ z → once l ∈ z ++ dlabs xs) (sym (ilab-sv x)) (go (label-of? x) (entry-of? x) p)
    where
      go : ∀ ml me → l ∈ lab ml (Labs xs) → once l ∈ (lo ml ++ le me) ++ dlabs xs
      go (just m) me (here refl) = here refl
      go (just m) me (there q)   = there (∈-++⁺ʳ (le me) (lab-dl xs q))
      go nothing  me q           = ∈-++⁺ʳ (le me) (lab-dl xs q)

  ent-dl : ∀ xs {e} → e ∈ Ents xs → callee e ∈ dlabs xs
  ent-dl (x ∷ xs) {e} p = subst (λ z → callee e ∈ z ++ dlabs xs) (sym (ilab-sv x)) (go (label-of? x) (entry-of? x) p)
    where
      go : ∀ ml me → e ∈ ent me (Ents xs) → callee e ∈ (lo ml ++ le me) ++ dlabs xs
      go (just l) (just e′) (here refl) = there (here refl)
      go nothing  (just e′) (here refl) = here refl
      go (just l) (just e′) (there q)   = there (there (ent-dl xs q))
      go nothing  (just e′) (there q)   = there (ent-dl xs q)
      go (just l) nothing   q           = there (ent-dl xs q)
      go nothing  nothing   q           = ent-dl xs q

  -- ★ distinct jump labels and distinct entries: distinct defined labels
  dl-dst : ∀ xs → AllPairs _≢_ (Labs xs) → AllPairs _≢_ (Ents xs) → AllPairs _≢_ (dlabs xs)
  dl-dst []       _  _  = []
  dl-dst (x ∷ xs) dl de =
    subst (λ z → AllPairs _≢_ (z ++ dlabs xs)) (sym (ilab-sv x))
      (go (label-of? x) refl (entry-of? x) refl dl de)
    where
      apart-l : ∀ {l} → All (l ≢_) (Labs xs) → All (once l ≢_) (dlabs xs)
      apart-l {l} a = Data.List.Relation.Unary.All.tabulate λ {y} m e → not-once {xs} a e (dl-in xs m)
      apart-e : ∀ {e} → All (e ≢_) (Ents xs) → All (callee e ≢_) (dlabs xs)
      apart-e {e} a = Data.List.Relation.Unary.All.tabulate λ {y} m q → not-callee {xs} a q (dl-in xs m)
      go : ∀ ml → label-of? x ≡ ml → ∀ me → entry-of? x ≡ me
         → AllPairs _≢_ (lab ml (Labs xs)) → AllPairs _≢_ (ent me (Ents xs))
         → AllPairs _≢_ ((lo ml ++ le me) ++ dlabs xs)
      go (just l) el (just e) ee (al ∷ dl′) (ae ∷ de′) = ((λ ()) ∷ apart-l al) ∷ apart-e ae ∷ dl-dst xs dl′ de′
      go (just l) el nothing  ee (al ∷ dl′) de′        = apart-l al ∷ dl-dst xs dl′ de′
      go nothing  el (just e) ee dl′ (ae ∷ de′)        = apart-e ae ∷ dl-dst xs dl′ de′
      go nothing  el nothing  ee dl′ de′               = dl-dst xs dl′ de′

private
  fetch-∈ : ∀ {FS : FrameSemantics} (xs : AbstractTrace) k {i} → FlatMachine.fetch {FS} xs k ≡ just i → i ∈ xs
  fetch-∈ {FS} (x ∷ xs) zero    refl = here refl
  fetch-∈ {FS} (x ∷ xs) (suc k) e    = there (fetch-∈ {FS} xs k e)

  arefs-of : ∀ {G : String → Set} (t : AbstractTrace) → All (λ i → All G (instr-refs i)) t → All G (arefs t)
  arefs-of []       []       = []
  arefs-of (i ∷ is) (a ∷ as) = ++⁺ a (arefs-of is as)

  -- a jump's label, instruction by instruction
  jmp-pt : ∀ {P : LabelId → Set} (xs : AbstractTrace) → All P (Jmps xs) → All (λ i → ∀ l → jump-of i ≡ just l → P l) xs
  jmp-pt {P} []       _ = []
  jmp-pt {P} (x ∷ xs) a = go (jump-of x) refl a
    where
      go : ∀ mo → jump-of x ≡ mo → All P (jmp mo (Jmps xs)) → All (λ i → ∀ l → jump-of i ≡ just l → P l) (x ∷ xs)
      go (just l) e (pl ∷ a′) = (λ l′ e′ → subst P (just-inj (trans (sym e) e′)) pl) ∷ jmp-pt xs a′
        where just-inj : ∀ {a b : LabelId} → just a ≡ just b → a ≡ b
              just-inj refl = refl
      go nothing e a′ = (λ l′ e′ → ⊥-elim (nj (trans (sym e) e′))) ∷ jmp-pt xs a′
        where nj : ∀ {b : LabelId} → nothing ≢ just b
              nj ()

  -- a block's symbol is in the table's list
  syms-has : ∀ (bs : List ArithBlock) {b} → b ∈ bs → block-symbol b ∈ block-syms bs
  syms-has bs m =
    Data.List.Relation.Unary.Any.Properties.map⁺
      (Data.List.Relation.Unary.Any.map sym
        (Data.List.Relation.Unary.Any.Properties.map⁻ (BT.table-has block-symbol (λ x → x) bs m)))

------------------------------------------------------------------------
-- 3. ★ THE IMAGE.
------------------------------------------------------------------------

module Img (nm : CanonicalName) {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → Lit b → AbstractInstr) (ld-is : IAll.LoadConst ldConst)
           (canon : ∀ {s} → s ∈ ops (Program.U ds f) → Canonical (info s))
           {FS : FrameSemantics} where
  open Program ds f using (U; blocks-in; start-in; ncty)
  open In U
  open _⊑[_] using (go)
  open Program′ ds f ldConst
  open Lowering U ncty ldConst
  open FlatMachine {FS} using (fetch; find-entry-sound; find-thunk-sound)
  open LabsC {FS} using (Labs; Labs-++; Ents; Ents-++; module C; module Ok)
  open DL {FS}
  open Closed {FS} using (Cov; cov-nj; cov-++)
  module IA = IAll.Img nm ds f ldConst ld-is
  module IOk = IAll.Ok nm U ncty ldConst
  ld-nl = IA.ld-nl {FS}
  module LIm = LI.Img {FS} ds f ldConst ld-nl
  module EIm = EI.ImgE {FS} ds f ldConst ld-nl

  ld-nj : ∀ {b} (v : Lit b) → jump-of (ldConst v) ≡ nothing
  ld-nj v = nj-go (ld-is v)
    where nj-go : (Σ _ λ A → Σ (FitsInReg A) λ p → Σ (LitPayload p) λ x → ldConst v ≡ instr-load-const p x)
             → jump-of (ldConst v) ≡ nothing
          nj-go (_ , p , x , e) = subst (λ i → jump-of i ≡ nothing) (sym e) refl

  module JC = Closed.C {FS} U ncty ldConst ld-nj
  open Free U ncty ldConst ld-nj using (tramp-nj; view-nj)

  -- the file's parts: the room-checked image, its blocks, its externs
  P′ : AbstractTrace
  P′ = room-checks image

  bs : List ArithBlock
  bs = Once.LinCore.ImageBlocks.imageBlocks fmt bw U

  D : List String
  D = entry-symbol ∷ alloc-record-symbol ∷ adefs P′ ++ block-syms bs

  ex : List String
  ex = image-externs image

  ----------------------------------------------------------------------
  -- the image's labels and entries: each a block's
  ----------------------------------------------------------------------

  private
    main₀ = compᴵ ds f {[]} {[]} end
    φ₀ = frameOf main₀
    code₀ = proj₁ (lowC φ₀ j₀ 0 (instr-ctrl c-leave ∷ []) main₀ (start-in {[]} {[]} tt))
    bl = blocksOf (allK U) blocks-in 0

    o₀ = proj₂ (C.lowC-ok U ncty ldConst ld-nl φ₀ j₀ 0 (instr-ctrl c-leave ∷ []) (refl ∷ []) main₀ (start-in {[]} {[]} tt))

  labs-shape : All (λ l → Σ ℕ λ j → Σ ℕ λ k → l ≡ jl j k) (Labs image)
  labs-shape =
    subst (All (λ l → Σ ℕ λ j → Σ ℕ λ k → l ≡ jl j k)) (sym (Labs-++ code₀ bl))
      (++⁺ (subst (All (λ l → Σ ℕ λ j → Σ ℕ λ k → l ≡ jl j k)) (sym (Ok.eq o₀))
             (Data.List.Relation.Unary.All.Properties.map⁺ (Data.List.Relation.Unary.All.tabulate (λ {k} _ → j₀ , k , refl))))
           (Data.List.Relation.Unary.All.map (λ { (j , k , _ , _ , e) → j , k , e }) (proj₂ (LIm.blocks-lab (allK U) blocks-in 0))))
    where import Data.List.Relation.Unary.All.Properties

  ents-shape : All (λ e → Σ ℕ λ j → e ≡ e-fn (nameOf j) ⊎ e ≡ e-thunk (tl j)) (Ents image)
  ents-shape =
    subst (All (λ e → Σ ℕ λ j → e ≡ e-fn (nameOf j) ⊎ e ≡ e-thunk (tl j))) (sym (trans (Ents-++ code₀ bl) (cong (_++ Ents bl) EIm.code₀-ne)))
      (Data.List.Relation.Unary.All.map (λ { (j , _ , _ , o) → j , o }) (proj₂ (EIm.blocks-ent (allK U) blocks-in 0)))

  private
    shape-in : ∀ {y} → (Σ LabelId λ l → y ≡ once l × l ∈ Labs image) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents image) → ShapeL y
    shape-in (inj₁ (l , e , m′)) = shape-lab e (Data.List.Relation.Unary.All.lookup labs-shape m′)
    shape-in (inj₂ (x , e , m′)) = shape-ent e (Data.List.Relation.Unary.All.lookup ents-shape m′)

  dl-shape : All ShapeL (dlabs image)
  dl-shape = Data.List.Relation.Unary.All.tabulate λ m → shape-in (dl-in image m)

  ----------------------------------------------------------------------
  -- ★ EVERY SYMBOL THE FILE DEFINES, ONCE
  ----------------------------------------------------------------------

  adefs-eq : adefs P′ ≡ adefs image
  adefs-eq = fold-room adefs (λ i xs → instr-defs i ++ xs) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ _ → refl) image

  adefs-dst : AllPairs _≢_ (adefs image)
  adefs-dst = subst (AllPairs _≢_) (sym (adefs-labs image))
                (syms-dst (dlabs-def image) (Data.List.Relation.Unary.All.map shape-good dl-shape)
                          (dl-dst image LIm.image-dst EIm.image-edst))

  adefs-shape : All (λ s → Σ Label λ y → ShapeL y × s ≡ labelSym y) (adefs image)
  adefs-shape = subst (All (λ s → Σ Label λ y → ShapeL y × s ≡ labelSym y)) (sym (adefs-labs image))
                  (Data.List.Relation.Unary.All.Properties.map⁺ (Data.List.Relation.Unary.All.map (λ {y} sh → y , sh , refl) dl-shape))
    where import Data.List.Relation.Unary.All.Properties

  defined-once : Unique D
  defined-once =
    subst (λ A → Unique (entry-symbol ∷ alloc-record-symbol ∷ A ++ block-syms bs)) (sym adefs-eq)
      ( (entry≢record ∷ ++⁺ (Data.List.Relation.Unary.All.map (λ { {s} (y , sh , refl) → entry≢shape sh }) adefs-shape)
            (Data.List.Relation.Unary.All.map entry≢block (blocks-sym bs)))
      ∷ ++⁺ (Data.List.Relation.Unary.All.map (λ { {s} (y , sh , refl) → record≢shape sh }) adefs-shape)
            (Data.List.Relation.Unary.All.map record≢block (blocks-sym bs))
      ∷ AP-++⁺ adefs-dst (blocks-unique bs)
          (Data.List.Relation.Unary.All.map (λ { {s} (y , sh , refl) → Data.List.Relation.Unary.All.map (shape≢block sh) (blocks-sym bs) }) adefs-shape))

  ----------------------------------------------------------------------
  -- ★ EVERY SYMBOL IT REFERENCES, DEFINED OR AN EXTERN
  ----------------------------------------------------------------------

  G : String → Set
  G s = s ∈ D ⊎ s ∈ ex

  private
    inD : ∀ {s} → s ∈ adefs image → G s
    inD {s} m = inj₁ (there (there (∈-++⁺ˡ (subst (s ∈_) (sym adefs-eq) m))))

    inB : ∀ {s} → s ∈ block-syms bs → G s
    inB m = inj₁ (there (there (∈-++⁺ʳ (adefs P′) m)))

    dl-G : ∀ {y} → y ∈ dlabs image → G (labelSym y)
    dl-G m = inD (subst (_ ∈_) (sym (adefs-labs image)) (∈-map⁺ labelSym m))

    lab-G : ∀ {l} → l ∈ Labs image → G (labelSym (once l))
    lab-G m = dl-G (lab-dl image m)

    ent-G : ∀ {e b} k → fetch image k ≡ just (instr-ctrl (c-entry e b)) → G (labelSym (callee e))
    ent-G k e = dl-G (ent-dl image (ent-∈ image (fetch-∈ {FS} image k e)))
      where
        ent-∈ : ∀ xs {e b} → instr-ctrl (c-entry e b) ∈ xs → e ∈ Ents xs
        ent-∈ (x ∷ xs) (here refl) = here refl
        ent-∈ (x ∷ xs) (there m)   = ent-up (FlatMachine.entry-of? {FS} x) (ent-∈ xs m)
          where ent-up : ∀ mo {e} → e ∈ Ents xs → e ∈ LabsC.ent {FS} mo (Ents xs)
                ent-up (just _) m′ = there m′
                ent-up nothing  m′ = m′

    -- an entry the image finds is one it defines
    ent-from : ∀ (e : EntryId) {j} → FlatMachine.find-entry {FS} image e ≡ just j → G (labelSym (callee e))
    ent-from e {j} fe = let (b , x) = find-entry-sound image e j fe in ent-G j x

    -- a call lands on its block's entry
    fn-G : ∀ {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) → G (labelSym (callee (e-fn (nameOf (idx p)))))
    fn-G p = ent-from (e-fn (nameOf (idx p))) (EIm.image-fn p)

    -- a code word lands on its trampoline's entry
    tr-G : ∀ {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) {b r}
         → tramp (idx p) κ ≡ instr-ctrl (c-entry (e-thunk (tl (idx p))) b) ∷ r → G (thunkSym (tl (idx p)))
    tr-G p te = ent-from (e-thunk (tl (idx p))) (EIm.image-tramp p te)

    -- an op: a block of the image's, or an extern
    sig-G : ∀ {A B} (si : SigOpInfo A B) → IOk.Ref (instr-sigop si) → instr-sigop si ∈ image → G (once-symbol-path (SigOpInfo.name si))
    sig-G si r m = case sigop-owner (SigOpInfo.sem si) of λ where
      (inj₁ isI) → case Once.LinCore.ImageOwned.named-call fmt bw U canon si r isI of λ where
        (b , b∈ , nm≡ , _) → inB (subst (_∈ block-syms bs) (sym (cong once-symbol-path nm≡)) (syms-has bs b∈))
      (inj₂ isE) → inj₂ (ext-in image si m isE)

  -- ★ the image's code jumps only to labels it defines
  private
    block-cov : ∀ {σ} j (κ : Key σ) (ev : CIn (blockᴵ κ)) → Cov (Labs (lowBlock j κ ev)) [] (lowBlock j κ ev)
    block-cov {bsig t A B} j κ ev =
      let φ = frameOf (blockᴵ κ) ; M = wsz A ⊔ wsz B ; b = fbudget φ
          fin = restore-input (sv₁ φ) ∷ mvSP (Tp φ (B ∷ [])) (M ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret b) ∷ []
          code = proj₁ (lowC φ j 0 fin (blockᴵ κ) ev)
          pre = instr-ctrl (c-entry (e-fn (nameOf j)) b) ∷ store-at-slot (sv₂ φ) ∷ mov-to-output ∷ store-at-slot (sv₁ φ)
                ∷ mvPS (M ∸ wsz A) (Tp φ (A ∷ [])) (wsz A)
      in cov-++ pre (view-in t φ ++ code)
           (cov-nj {xs = pre} (refl ∷ refl ∷ refl ∷ refl ∷ mvPS-nj (M ∸ wsz A) (Tp φ (A ∷ [])) (wsz A)))
           (cov-++ (view-in t φ) code (cov-nj (view-nj t φ))
             (subst (λ E → Cov (Labs code) E code)
                    (Jmps-nj {fin} (refl ∷ ++⁺ (mvSP-nj (Tp φ (B ∷ [])) (M ∸ wsz B) (wsz B)) (refl ∷ [])))
                    (JC.lowC-cov φ j 0 fin (blockᴵ κ) ev)))

    blocks-cov : ∀ (ks : List AKey) (ev : ∀ {κ} → κ ∈ ks → BIn κ) j → Cov (Labs (blocksOf ks ev j)) [] (blocksOf ks ev j)
    blocks-cov []             ev j = []
    blocks-cov ((σ , κ) ∷ ks) ev j =
      cov-++ (lowBlock j κ (ev (here refl))) (tramp j κ ++ blocksOf ks (λ q → ev (there q)) (suc j))
        (block-cov j κ (ev (here refl)))
        (cov-++ (tramp j κ) (blocksOf ks (λ q → ev (there q)) (suc j)) (cov-nj (tramp-nj j κ)) (blocks-cov ks (λ q → ev (there q)) (suc j)))

  jumps-in : All (λ l → l ∈ Labs image) (Jmps image)
  jumps-in = Data.List.Relation.Unary.All.map (λ { (inj₁ p) → p ; (inj₂ ()) })
               (cov-++ code₀ bl (JC.lowC-cov φ₀ j₀ 0 (instr-ctrl c-leave ∷ []) main₀ (start-in {[]} {[]} tt)) (blocks-cov (allK U) blocks-in 0))

  ----------------------------------------------------------------------
  -- D470: THE IMAGE'S LABELS HAVE AN EMPTY PATH (its own: `jl`, `tl`), apart
  -- from the allocator expansion's (`AllocExpand.lb-bump`/`lb-done`)
  ----------------------------------------------------------------------

  private
    lab-in : ∀ xs {m} → instr-ctrl (c-label m) ∈ xs → m ∈ Labs xs
    lab-in (x ∷ xs) (here refl) = here refl
    lab-in (x ∷ xs) {m} (there p) = lab-up (FlatMachine.label-of? {FS} x) (lab-in xs p)
      where lab-up : ∀ mo → m ∈ Labs xs → m ∈ LabsC.lab {FS} mo (Labs xs)
            lab-up (just _) q = there q
            lab-up nothing  q = q

    path-of : ∀ {m} → m ∈ Labs image → Once.CCC.Codegen.AllocExpand.ImgL m
    path-of p = path-jl (Data.List.Relation.Unary.All.lookup labs-shape p)
      where path-jl : ∀ {m} → (Σ ℕ λ j → Σ ℕ λ k → m ≡ jl j k) → Once.CCC.Codegen.AllocExpand.ImgL m
            path-jl (j , _ , refl) e = two≢one (trans (sym (nameOf-two j)) (cong (λ c → length (CanonicalName.parts c)) e))
              where two≢one : 2 ≡ 1 → ⊥
                    two≢one ()

  img-path : ∀ n m → fetch image n ≡ just (instr-ctrl (c-label m)) → Once.CCC.Codegen.AllocExpand.ImgL m
  img-path n m f = path-of (lab-in image (fetch-∈ {FS} image n f))

  jmp-path : ∀ n m → fetch image n ≡ just (instr-ctrl (c-jmp m)) → Once.CCC.Codegen.AllocExpand.ImgL m
  jmp-path n m f = path-of (Data.List.Relation.Unary.All.lookup (jmp-pt image jumps-in) (fetch-∈ {FS} image n f) m refl)

  br-path : ∀ n m → fetch image n ≡ just (instr-ctrl (c-branch-tag-zero m)) → Once.CCC.Codegen.AllocExpand.ImgL m
  br-path n m f = path-of (Data.List.Relation.Unary.All.lookup (jmp-pt image jumps-in) (fetch-∈ {FS} image n f) m refl)

  ----------------------------------------------------------------------
  -- D482: THE OUTLINED IMAGE'S NAMES — no jump of the image's targets the
  -- skip label (its owner one part, a block's two), and no call of the image's
  -- names a routine (a block's first part is `once-lincore`, theirs `once-alloc`)
  ----------------------------------------------------------------------

  private
    skip-of : ∀ {m} → m ∈ Labs image → ¬ Once.CCC.Codegen.AllocExpand.skip-label ≡ m
    skip-of p = sk (Data.List.Relation.Unary.All.lookup labs-shape p)
      where sk : ∀ {m} → (Σ ℕ λ j → Σ ℕ λ k → m ≡ jl j k) → ¬ Once.CCC.Codegen.AllocExpand.skip-label ≡ m
            sk (j , _ , refl) e = one≢two (trans (cong (λ l → length (CanonicalName.parts (LabelId.owner l))) e) (nameOf-two j))
              where one≢two : 1 ≡ 2 → ⊥
                    one≢two ()

    first : CanonicalName → List String
    first c = Data.List.take 1 (CanonicalName.parts c)

  skip-apart : ∀ q i m → fetch IA.tail q ≡ just i → (i ≡ instr-ctrl (c-jmp m)) ⊎ (i ≡ instr-ctrl (c-branch-tag-zero m))
             → ¬ Once.CCC.Codegen.AllocExpand.skip-label ≡ m
  skip-apart q i m f (inj₁ refl) = skip-of (Data.List.Relation.Unary.All.lookup (jmp-pt image jumps-in) (fetch-∈ {FS} image (suc q) f) m refl)
  skip-apart q i m f (inj₂ refl) = skip-of (Data.List.Relation.Unary.All.lookup (jmp-pt image jumps-in) (fetch-∈ {FS} image (suc q) f) m refl)

  calls-apart : ∀ q i f → fetch IA.tail q ≡ just i → i ≡ instr-ctrl (c-call-fn f)
              → ∀ k → (¬ e-fn (Once.CCC.Codegen.AllocExpand.alloc-fn k) ≡ e-fn f) × (¬ e-fn (Once.CCC.Codegen.AllocExpand.free-fn k) ≡ e-fn f)
  calls-apart q i f ft refl k = ap (proj₂ (proj₂ (Data.List.Relation.Unary.All.lookup IA.tail-ok (fetch-∈ {FS} IA.tail q ft))))
    where
      e-fn-inj : ∀ {x y} → e-fn x ≡ e-fn y → x ≡ y
      e-fn-inj refl = refl
      ap : IOk.Ref (instr-ctrl (c-call-fn f))
         → (¬ e-fn (Once.CCC.Codegen.AllocExpand.alloc-fn k) ≡ e-fn f) × (¬ e-fn (Once.CCC.Codegen.AllocExpand.free-fn k) ≡ e-fn f)
      ap (_ , p , refl) = (λ e → a≢l (trans (cong first (e-fn-inj e)) (nameOf-lead (idx p))))
                        , (λ e → a≢l (trans (cong first (e-fn-inj e)) (nameOf-lead (idx p))))
        where a≢l : ¬ ("once-alloc" ∷ []) ≡ ("once-lincore" ∷ [])
              a≢l ()

  ----------------------------------------------------------------------
  -- D482: THE OUTLINED IMAGE'S LABELS AND ENTRIES — the skip label then the
  -- image's; the routines' (two a size) then the image's; each once
  ----------------------------------------------------------------------

  module Ol where
    open import Once.CCC.Codegen.AllocExpand using (alloc-fn; free-fn; site-call; prim-routines; skip; skip-label; outline)
    open import Once.CCC.Codegen.AllocOutline {FS} using (label-site; entry-site; alloc-fn-inj; free-fn-inj; alloc≢free)
    import Data.List.Relation.Unary.Unique.DecPropositional.Properties
    import Data.Nat.Properties

    ksᵒ : List ℕ
    ksᵒ = Once.CCC.Codegen.AllocExpandClasses.dsizes image

    imageᵒ : AbstractTrace
    imageᵒ = outline ksᵒ image

    rents : List ℕ → List EntryId
    rents []       = []
    rents (k ∷ ks) = e-fn (alloc-fn k) ∷ e-fn (free-fn k) ∷ rents ks

    private
      labs-map : ∀ (xs : AbstractTrace) → Labs (map site-call xs) ≡ Labs xs
      labs-map []       = refl
      labs-map (x ∷ xs) = trans (cong (λ mo → LabsC.lab {FS} mo (Labs (map site-call xs))) (label-site x))
                                (cong (LabsC.lab {FS} (FlatMachine.label-of? {FS} x)) (labs-map xs))

      ents-map : ∀ (xs : AbstractTrace) → Ents (map site-call xs) ≡ Ents xs
      ents-map []       = refl
      ents-map (x ∷ xs) = trans (cong (λ mo → LabsC.ent {FS} mo (Ents (map site-call xs))) (entry-site x))
                                (cong (LabsC.ent {FS} (FlatMachine.entry-of? {FS} x)) (ents-map xs))

      labs-rou : ∀ ks → Labs (prim-routines ks) ≡ []
      labs-rou []       = refl
      labs-rou (k ∷ ks) = labs-rou ks

      ents-rou : ∀ ks → Ents (prim-routines ks) ≡ rents ks
      ents-rou []       = refl
      ents-rou (k ∷ ks) = cong (λ r → e-fn (alloc-fn k) ∷ e-fn (free-fn k) ∷ r) (ents-rou ks)

    labs-out : Labs imageᵒ ≡ skip-label ∷ Labs image
    labs-out =
      trans (Labs-++ (skip ksᵒ) (map site-call IA.tail))
        (trans (cong (_++ Labs (map site-call IA.tail))
                     (trans (Labs-++ (prim-routines ksᵒ) (instr-ctrl (c-label skip-label) ∷ [])) (cong (_++ (skip-label ∷ [])) (labs-rou ksᵒ))))
               (cong (skip-label ∷_) (labs-map IA.tail)))

    ents-out : Ents imageᵒ ≡ rents ksᵒ ++ Ents image
    ents-out =
      trans (Ents-++ (skip ksᵒ) (map site-call IA.tail))
        (Relation.Binary.PropositionalEquality.cong₂ _++_ (trans (Ents-++ (prim-routines ksᵒ) (instr-ctrl (c-label skip-label) ∷ []))
                           (trans (Data.List.Properties.++-identityʳ _) (ents-rou ksᵒ)))
                    (ents-map IA.tail))
      where import Data.List.Properties

    private
      e-fn-inj : ∀ {x y} → e-fn x ≡ e-fn y → x ≡ y
      e-fn-inj refl = refl

      skip≢img : ∀ {l} → (Σ ℕ λ j → Σ ℕ λ k → l ≡ jl j k) → skip-label ≢ l
      skip≢img (j , _ , refl) e = one≢two (trans (cong (λ l → length (CanonicalName.parts (LabelId.owner l))) e) (nameOf-two j))
        where one≢two : 1 ≡ 2 → ⊥
              one≢two ()

      -- a routine's name is no block's (first parts) and no thunk's
      rou≢img : ∀ (f : CanonicalName) → first f ≡ "once-alloc" ∷ [] → ∀ {e} → (Σ ℕ λ j → e ≡ e-fn (nameOf j) ⊎ e ≡ e-thunk (tl j)) → e-fn f ≢ e
      rou≢img f lead (j , inj₁ refl) e = a≢l (trans (sym lead) (trans (cong first (e-fn-inj e)) (nameOf-lead j)))
        where a≢l : ¬ ("once-alloc" ∷ []) ≡ ("once-lincore" ∷ [])
              a≢l ()
      rou≢img f lead (j , inj₂ refl) ()

      -- the routines' names: apart by size and kind
      rents-dst : ∀ ks → AllPairs _≢_ ks → AllPairs _≢_ (rents ks)
      rents-dst []       _          = []
      rents-dst (k ∷ ks) (nk ∷ uks) =
          ((λ e → alloc≢free k k (e-fn-inj e)) ∷ apart-a nk) ∷ apart-f nk ∷ rents-dst ks uks
        where
          apart-a : ∀ {ks′} → All (k ≢_) ks′ → All (e-fn (alloc-fn k) ≢_) (rents ks′)
          apart-a []          = []
          apart-a {k′ ∷ _} (n ∷ ns) = (λ e → n (alloc-fn-inj {k} {k′} (e-fn-inj e))) ∷ (λ e → alloc≢free k k′ (e-fn-inj e)) ∷ apart-a ns
          apart-f : ∀ {ks′} → All (k ≢_) ks′ → All (e-fn (free-fn k) ≢_) (rents ks′)
          apart-f []          = []
          apart-f {k′ ∷ _} (n ∷ ns) = (λ e → alloc≢free k′ k (sym (e-fn-inj e))) ∷ (λ e → n (free-fn-inj {k} {k′} (e-fn-inj e))) ∷ apart-f ns

      rents-lead : ∀ ks → All (λ e → Σ CanonicalName λ f → (e ≡ e-fn f) × (first f ≡ "once-alloc" ∷ [])) (rents ks)
      rents-lead []       = []
      rents-lead (k ∷ ks) = (alloc-fn k , refl , refl) ∷ (free-fn k , refl , refl) ∷ rents-lead ks

    labs-dstᵒ : AllPairs _≢_ (Labs imageᵒ)
    labs-dstᵒ = subst (AllPairs _≢_) (sym labs-out)
                  (Data.List.Relation.Unary.All.map skip≢img labs-shape ∷ LIm.image-dst)

    ents-dstᵒ : AllPairs _≢_ (Ents imageᵒ)
    ents-dstᵒ = subst (AllPairs _≢_) (sym ents-out)
                  (AP-++⁺ (rents-dst ksᵒ (Data.List.Relation.Unary.Unique.DecPropositional.Properties.deduplicate-! Data.Nat.Properties._≟_ (Once.CCC.Codegen.AllocExpandClasses.sizes image)))
                          EIm.image-edst
                          (Data.List.Relation.Unary.All.map (λ { (f , refl , lead) → Data.List.Relation.Unary.All.map (rou≢img f lead) ents-shape }) (rents-lead ksᵒ)))

  private
    refs-ok : ∀ (i : AbstractInstr) → IOk.Ref i → (∀ l → jump-of i ≡ just l → l ∈ Labs image) → i ∈ image → All G (instr-refs i)
    refs-ok (instr-ctrl (c-label _)) r jin m = []
    refs-ok (instr-ctrl (c-entry (e-thunk _) _)) r jin m = []
    refs-ok (instr-ctrl (c-entry (e-fn _) _)) r jin m = []
    refs-ok (instr-ctrl (c-jmp n)) r jin m = lab-G (jin n refl) ∷ []
    refs-ok (instr-ctrl (c-branch-tag-zero n)) r jin m = lab-G (jin n refl) ∷ []
    refs-ok (instr-ctrl (c-ret _)) r jin m = []
    refs-ok (instr-ctrl (c-call-fn _)) ((σ , κ) , p , refl) jin m = fn-G p ∷ []
    refs-ok (instr-ctrl (c-start _ _)) r jin m = inj₂ (there (here refl)) ∷ inj₁ (there (here refl)) ∷ []
    refs-ok (instr-ctrl c-leave) r jin m = inj₂ (here refl) ∷ []
    refs-ok mov-to-output r jin m = []
    refs-ok mov-to-input r jin m = []
    refs-ok load-indirect r jin m = []
    refs-ok load-indirect-suc r jin m = []
    refs-ok (load-from-slot _) r jin m = []
    refs-ok (store-at-slot _) r jin m = []
    refs-ok store-indirect r jin m = []
    refs-ok store-indirect-suc r jin m = []
    refs-ok (lea-slot _) r jin m = []
    refs-ok (restore-input _) r jin m = []
    refs-ok (instr-alloc-stack _) r jin m = []
    refs-ok (instr-dealloc-stack _) r jin m = []
    refs-ok (instr-reclaim-to _) r jin m = []
    refs-ok (instr-free-heap _) r jin m = []
    refs-ok (load-at _) r jin m = []
    refs-ok (store-at _) r jin m = []
    refs-ok (addr-at _) r jin m = []
    refs-ok (load-rec _) r jin m = inj₁ (there (here refl)) ∷ []
    refs-ok (store-rec _) r jin m = inj₁ (there (here refl)) ∷ []
    refs-ok (instr-room q) r jin m = room-refs-G (inj₁ (there (here refl))) (inj₂ (there (here refl))) q
    refs-ok (instr-push-frame _) r jin m = []
    refs-ok instr-pop-frame r jin m = []
    refs-ok instr-call-closure r jin m = []
    refs-ok (worklist-init _) r jin m = []
    refs-ok (worklist-push _) r jin m = []
    refs-ok (worklist-pop _) r jin m = []
    refs-ok (worklist-check _) r jin m = []
    refs-ok (instr-sigop si) r jin m = sig-G si r m ∷ []
    refs-ok (instr-load-const _ _) r jin m = []
    refs-ok (instr-load-code-addr _) ((σ , κ) , p , refl , (b , r , te)) jin m = tr-G p te ∷ []
    refs-ok instr-save-closure-reg r jin m = []
    refs-ok (instr-load-tag-lit _) r jin m = []
    refs-ok (instr-alloc-heap _) r jin m = []
    refs-ok (instr-reg-op _) r jin m = []
  -- ★★ the file's references resolve
  resolved : All G (arefs P′)
  resolved =
    All-fold-room arefs instr-refs (λ _ _ → refl) (room-refs-G (inj₁ (there (here refl))) (inj₂ (there (here refl)))) (λ _ _ _ → refl) image
      (arefs-of image (refs-ok _ tt (λ l ()) (here refl)
        ∷ Data.List.Relation.Unary.All.tabulate (λ {i} m →
            refs-ok i (proj₂ (proj₂ (Data.List.Relation.Unary.All.lookup IA.tail-ok m)))
                      (Data.List.Relation.Unary.All.lookup jtail m) (there m))))
    where
      jtail : All (λ i → ∀ l → jump-of i ≡ just l → l ∈ Labs image) IA.tail
      jtail = Data.List.Relation.Unary.All.tail (jmp-pt image jumps-in)

  -- ★★ THE IMAGE'S FILE IS WELL-FORMED, as symbols (`ImageExterns.ImageWF`)
  image-wf : ImageWF P′ bs ex
  image-wf = defined-once , resolved , image-externs-valid image

  ----------------------------------------------------------------------
  -- ★★ THE ALLOCATOR'S EXPANSION OF THE IMAGE (D470/D472): its file's
  -- symbols are well-formed too — its labels the image's and each alloc
  -- site's two (once each: `ImageSymsX.labs-dst`), its entries the image's,
  -- every reference defined or an extern (a site's jumps its own labels, the
  -- record's words the file's record)
  ----------------------------------------------------------------------

  module Xp (C : Once.CCC.Codegen.AllocExpand.Classes) where
    open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-map⁻)
    module XX = Once.LinCore.ImageSymsX.X fmt ans bw {FS} C
    module DLX = DL {FS}

    imageˣ : AbstractTrace
    imageˣ = Once.CCC.Codegen.AllocExpand.expand C image

    P″ : AbstractTrace
    P″ = room-checks imageˣ

    Dˣ : List String
    Dˣ = entry-symbol ∷ alloc-record-symbol ∷ adefs P″ ++ block-syms bs

    adefs-eqˣ : adefs P″ ≡ adefs imageˣ
    adefs-eqˣ = fold-room adefs (λ i xs → instr-defs i ++ xs) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ _ → refl) imageˣ

    -- what the expansion defines: the image's labels and entries, and the sites' labels
    data ShapeX : Label → Set where
      sx : ∀ {y} → ShapeL y → ShapeX y
      sa : ∀ s b → ShapeX (once (Once.CCC.Codegen.AllocExpand.alloc-label s b))

    private
      img-L : ∀ {m} → m ∈ Labs image → Once.CCC.Codegen.AllocExpand.ImgL m
      img-L = path-of

      shape-x : ∀ {y} → y ∈ dlabs imageˣ → ShapeX y
      shape-x m = by (dl-in imageˣ m)
        where
          by : ∀ {y} → (Σ LabelId λ l → y ≡ once l × l ∈ Labs imageˣ) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents imageˣ) → ShapeX y
          by (inj₁ (l , refl , ml)) = lab (XX.labs-in 0 image ml)
            where
              lab : (l ∈ Labs image) ⊎ (Σ ℕ λ s′ → (0 Data.Nat.≤ s′) × Once.CCC.Codegen.AllocExpand.SiteL l s′) → ShapeX (once l)
              lab (inj₁ q) = sx (shape-lab refl (Data.List.Relation.Unary.All.lookup labs-shape q))
              lab (inj₂ (s′ , _ , (b , _ , refl))) = sa s′ b
          by (inj₂ (e , refl , me)) = sx (shape-ent refl (Data.List.Relation.Unary.All.lookup ents-shape (subst (e ∈_) (XX.ents-exp 0 image) me)))

      good-x : ∀ {y} → ShapeX y → GoodL y
      good-x (sx sh) = shape-good sh
      good-x (sa s b) = refl , ((_ , _ , refl , refl) ∷ [])

      shapes-x : All ShapeX (dlabs imageˣ)
      shapes-x = Data.List.Relation.Unary.All.tabulate shape-x

      adefs-shape-x : All (λ s → Σ Label λ y → ShapeX y × s ≡ labelSym y) (adefs imageˣ)
      adefs-shape-x = subst (All (λ s → Σ Label λ y → ShapeX y × s ≡ labelSym y)) (sym (adefs-labs imageˣ))
                        (Data.List.Relation.Unary.All.Properties.map⁺ (Data.List.Relation.Unary.All.map (λ {y} sh → y , sh , refl) shapes-x))
        where import Data.List.Relation.Unary.All.Properties

      adefs-dst-x : AllPairs _≢_ (adefs imageˣ)
      adefs-dst-x = subst (AllPairs _≢_) (sym (adefs-labs imageˣ))
                      (syms-dst (dlabs-def imageˣ) (Data.List.Relation.Unary.All.map good-x shapes-x)
                                (dl-dst imageˣ (XX.labs-dst 0 image LIm.image-dst img-L)
                                               (subst (AllPairs _≢_) (sym (XX.ents-exp 0 image)) EIm.image-edst)))

      entry≢x : ∀ {y} → ShapeX y → entry-symbol ≢ labelSym y
      entry≢x (sx sh) = entry≢shape sh
      entry≢x (sa s b) e = head≢ (once-head (Once.CCC.Codegen.AllocExpand.alloc-label s b)) refl (sym e)

      record≢x : ∀ {y} → ShapeX y → alloc-record-symbol ≢ labelSym y
      record≢x (sx sh) = record≢shape sh
      record≢x (sa s b) e = head≢ (once-head (Once.CCC.Codegen.AllocExpand.alloc-label s b)) refl (sym e)

      x≢block : ∀ {y t} → ShapeX y → BlockSym t → labelSym y ≢ t
      x≢block (sx sh) b = shape≢block sh b
      x≢block (sa s b′) (d , refl) = head≢ (once-head (Once.CCC.Codegen.AllocExpand.alloc-label s b′)) (fn-head (bare ("arith.block." ++ˢ d)))

    defined-onceˣ : Unique Dˣ
    defined-onceˣ =
      subst (λ A → Unique (entry-symbol ∷ alloc-record-symbol ∷ A ++ block-syms bs)) (sym adefs-eqˣ)
        ( (entry≢record ∷ ++⁺ (Data.List.Relation.Unary.All.map (λ { {s} (y , sh , refl) → entry≢x sh }) adefs-shape-x)
                              (Data.List.Relation.Unary.All.map entry≢block (blocks-sym bs)))
        ∷ ++⁺ (Data.List.Relation.Unary.All.map (λ { {s} (y , sh , refl) → record≢x sh }) adefs-shape-x)
              (Data.List.Relation.Unary.All.map record≢block (blocks-sym bs))
        ∷ AP-++⁺ adefs-dst-x (blocks-unique bs)
            (Data.List.Relation.Unary.All.map (λ { {s} (y , sh , refl) → Data.List.Relation.Unary.All.map (x≢block sh) (blocks-sym bs) }) adefs-shape-x))

    ----------------------------------------------------------------------
    -- …and every symbol it references is defined or an extern
    ----------------------------------------------------------------------

    Gˣ : String → Set
    Gˣ s = s ∈ Dˣ ⊎ s ∈ ex

    private
      inDˣ : ∀ {y} → y ∈ dlabs imageˣ → labelSym y ∈ Dˣ
      inDˣ {y} ym = there (there (∈-++⁺ˡ (subst (labelSym y ∈_) (sym adefs-eqˣ)
                      (subst (labelSym y ∈_) (sym (adefs-labs imageˣ)) (∈-map⁺ labelSym ym)))))

      lab-Gˣ : ∀ {l} → instr-ctrl (c-label l) ∈ imageˣ → Gˣ (labelSym (once l))
      lab-Gˣ m = inj₁ (inDˣ (lab-dl imageˣ (XX.mem-lab imageˣ m)))

      rec-G : Gˣ alloc-record-symbol
      rec-G = inj₁ (there (here refl))

      -- what the image's file resolves, the expansion's does
      toˣ : ∀ {s} → G s → Gˣ s
      toˣ (inj₂ q) = inj₂ q
      toˣ (inj₁ (here e)) = inj₁ (here e)
      toˣ (inj₁ (there (here e))) = inj₁ (there (here e))
      toˣ {s} (inj₁ (there (there q))) = by (∈-++⁻ (adefs P′) q)
        where
          from-dl : ∀ {y} → y ∈ dlabs image → Gˣ (labelSym y)
          from-dl ym = pick (dl-in image ym)
            where
              pick : ∀ {y} → (Σ LabelId λ l → y ≡ once l × l ∈ Labs image) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents image) → Gˣ (labelSym y)
              pick (inj₁ (l , refl , ml)) = lab-Gˣ (XX.kept-in 0 image (XX.lab-mem image ml) (λ k ()) (λ k ()))
              pick (inj₂ (e , refl , me)) = inj₁ (inDˣ (ent-dl imageˣ (subst (e ∈_) (sym (XX.ents-exp 0 image)) me)))
          by : (s ∈ adefs P′) ⊎ (s ∈ block-syms bs) → Gˣ s
          by (inj₂ b) = inj₁ (there (there (∈-++⁺ʳ (adefs P″) b)))
          by (inj₁ a) = at-def (∈-map⁻ labelSym (subst (s ∈_) (adefs-labs image) (subst (s ∈_) adefs-eq a)))
            where
              at-def : (Σ Label λ y → y ∈ dlabs image × s ≡ labelSym y) → Gˣ s
              at-def (y , ym , refl) = from-dl ym

      ref-of : ∀ {i} → i ∈ image → IOk.Ref i
      ref-of (here refl) = tt
      ref-of (there m) = proj₂ (proj₂ (Data.List.Relation.Unary.All.lookup IA.tail-ok m))

      AllR : AbstractInstr → Set
      AllR i = All Gˣ (instr-refs i)

      alloc-refs : ∀ n k → fetch image n ≡ just (instr-alloc-heap k) → All AllR (Once.CCC.Codegen.AllocExpand.alloc-code C (n + 0) k)
      alloc-refs n k f =
          [] ∷ (rec-G ∷ []) ∷ (rec-G ∷ []) ∷ [] ∷ (bump ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ (rec-G ∷ []) ∷ []
        ∷ (rec-G ∷ []) ∷ (done ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ [] ∷ [] ∷ [] ∷ []
        where
          bump = lab-Gˣ (XX.alloc-in 0 image n k f (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))
          done = lab-Gˣ (XX.alloc-in 0 image n k f (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))))))

      free-refs : ∀ k → All AllR (Once.CCC.Codegen.AllocExpand.free-code C k)
      free-refs k = (rec-G ∷ []) ∷ (rec-G ∷ []) ∷ [] ∷ [] ∷ (rec-G ∷ []) ∷ (rec-G ∷ []) ∷ []

      heads-refs : ∀ c → All AllR (Once.CCC.Codegen.AllocExpand.heads C c)
      heads-refs zero    = []
      heads-refs (suc c) = (rec-G ∷ []) ∷ heads-refs c

      setup-refs : All AllR (Once.CCC.Codegen.AllocExpand.setup C)
      setup-refs = (rec-G ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ []
                 ∷ ++⁺ (heads-refs (Once.CCC.Codegen.AllocExpand.Classes.count C))
                       ([] ∷ [] ∷ [] ∷ (rec-G ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ [])

      refs-x : ∀ i → i ∈ imageˣ → AllR i
      refs-x i m = by (XX.in-exp 0 image m)
        where
          by : XX.InExp 0 image i → AllR i
          by (XX.in-kept q _ _) = Data.List.Relation.Unary.All.map toˣ (refs-ok i (ref-of q) (Data.List.Relation.Unary.All.lookup (jmp-pt image jumps-in) q) q)
          by (XX.in-alloc n k f q) = Data.List.Relation.Unary.All.lookup (alloc-refs n k f) q
          by (XX.in-free k q) = Data.List.Relation.Unary.All.lookup (free-refs k) q
          by (XX.in-setup q) = Data.List.Relation.Unary.All.lookup setup-refs q

    resolvedˣ : All Gˣ (arefs P″)
    resolvedˣ =
      All-fold-room arefs instr-refs (λ _ _ → refl) (room-refs-G (inj₁ (there (here refl))) (inj₂ (there (here refl)))) (λ _ _ _ → refl) imageˣ
        (arefs-of imageˣ (Data.List.Relation.Unary.All.tabulate (λ {i} m → refs-x i m)))

    -- ★★ THE EXPANSION'S FILE IS WELL-FORMED, as symbols
    image-wfˣ : ImageWF P″ bs ex
    image-wfˣ = defined-onceˣ , resolvedˣ , image-externs-valid image

  ----------------------------------------------------------------------
  -- ★★ D482: THE CALL MODE'S FILE IS WELL-FORMED, as symbols: the expansion of
  -- the outlined image (`Ol.imageᵒ`) defines the image's labels and entries, the
  -- skip label, the routines' entries and the sites' labels, each once; every
  -- symbol it references is defined (a site's call its routine, the jump the skip
  -- label) or an extern
  ----------------------------------------------------------------------

  module Xc (C : Once.CCC.Codegen.AllocExpand.Classes) where
    open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-map⁻)
    open import Once.CCC.Codegen.AllocExpand using (site-call; prim-routines; skip; skip-label; alloc-fn; free-fn)
    open import Once.CCC.Codegen.AllocOutline {FS} using (RouI; ri-ae; ri-a; ri-r; ri-fe; ri-f; rou; SiteView; sv-alloc; sv-free; sv-same; site-view)
    import Once.CCC.Codegen.AllocOutlineSizes
    module XX = Once.LinCore.ImageSymsX.X fmt ans bw {FS} C
    module DLX = DL {FS}
    open Ol

    imageᶜ : AbstractTrace
    imageᶜ = Once.CCC.Codegen.AllocExpand.expand C imageᵒ

    Pᶜ : AbstractTrace
    Pᶜ = room-checks imageᶜ

    Dᶜ : List String
    Dᶜ = entry-symbol ∷ alloc-record-symbol ∷ adefs Pᶜ ++ block-syms bs

    adefs-eqᶜ : adefs Pᶜ ≡ adefs imageᶜ
    adefs-eqᶜ = fold-room adefs (λ i xs → instr-defs i ++ xs) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ _ → refl) imageᶜ

    data ShapeC : Label → Set where
      cx : ∀ {y} → ShapeL y → ShapeC y
      ca : ∀ s b → ShapeC (once (Once.CCC.Codegen.AllocExpand.alloc-label s b))

    private
      rents-shape : ∀ ks {e} → e ∈ rents ks → ShapeL (callee e)
      rents-shape (k ∷ ks) (here refl)         = s-ra k
      rents-shape (k ∷ ks) (there (here refl)) = s-rf k
      rents-shape (k ∷ ks) (there (there m))   = rents-shape ks m

      lab-shapeᵒ : ∀ {l} → l ∈ Labs imageᵒ → ShapeL (once l)
      lab-shapeᵒ {l} m = by (subst (l ∈_) labs-out m)
        where by : ∀ {l} → l ∈ skip-label ∷ Labs image → ShapeL (once l)
              by (here refl) = s-sk
              by (there q)   = shape-lab refl (Data.List.Relation.Unary.All.lookup labs-shape q)

      ent-shapeᵒ : ∀ {e} → e ∈ Ents imageᵒ → ShapeL (callee e)
      ent-shapeᵒ {e} m = by (∈-++⁻ (rents ksᵒ) (subst (e ∈_) ents-out m))
        where by : ∀ {e} → (e ∈ rents ksᵒ) ⊎ (e ∈ Ents image) → ShapeL (callee e)
              by (inj₁ r) = rents-shape ksᵒ r
              by (inj₂ q) = shape-ent refl (Data.List.Relation.Unary.All.lookup ents-shape q)

      img-Lᵒ : ∀ {m} → m ∈ Labs imageᵒ → Once.CCC.Codegen.AllocExpand.ImgL m
      img-Lᵒ {l} m = by (subst (l ∈_) labs-out m)
        where by : ∀ {m} → m ∈ skip-label ∷ Labs image → Once.CCC.Codegen.AllocExpand.ImgL m
              by (here refl) ()
              by (there q)   = path-of q

      shape-c : ∀ {y} → y ∈ dlabs imageᶜ → ShapeC y
      shape-c m = by (dl-in imageᶜ m)
        where
          by : ∀ {y} → (Σ LabelId λ l → y ≡ once l × l ∈ Labs imageᶜ) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents imageᶜ) → ShapeC y
          by (inj₁ (l , refl , ml)) = lab (XX.labs-in 0 imageᵒ ml)
            where
              lab : (l ∈ Labs imageᵒ) ⊎ (Σ ℕ λ s′ → (0 Data.Nat.≤ s′) × Once.CCC.Codegen.AllocExpand.SiteL l s′) → ShapeC (once l)
              lab (inj₁ q) = cx (lab-shapeᵒ q)
              lab (inj₂ (s′ , _ , (b , _ , refl))) = ca s′ b
          by (inj₂ (e , refl , me)) = cx (ent-shapeᵒ (subst (e ∈_) (XX.ents-exp 0 imageᵒ) me))

      good-c : ∀ {y} → ShapeC y → GoodL y
      good-c (cx sh) = shape-good sh
      good-c (ca s b) = refl , ((_ , _ , refl , refl) ∷ [])

      shapes-c : All ShapeC (dlabs imageᶜ)
      shapes-c = Data.List.Relation.Unary.All.tabulate shape-c

      adefs-shape-c : All (λ s → Σ Label λ y → ShapeC y × s ≡ labelSym y) (adefs imageᶜ)
      adefs-shape-c = subst (All (λ s → Σ Label λ y → ShapeC y × s ≡ labelSym y)) (sym (adefs-labs imageᶜ))
                        (Data.List.Relation.Unary.All.Properties.map⁺ (Data.List.Relation.Unary.All.map (λ {y} sh → y , sh , refl) shapes-c))
        where import Data.List.Relation.Unary.All.Properties

      adefs-dst-c : AllPairs _≢_ (adefs imageᶜ)
      adefs-dst-c = subst (AllPairs _≢_) (sym (adefs-labs imageᶜ))
                      (syms-dst (dlabs-def imageᶜ) (Data.List.Relation.Unary.All.map good-c shapes-c)
                                (dl-dst imageᶜ (XX.labs-dst 0 imageᵒ labs-dstᵒ img-Lᵒ)
                                               (subst (AllPairs _≢_) (sym (XX.ents-exp 0 imageᵒ)) ents-dstᵒ)))

      entry≢c : ∀ {y} → ShapeC y → entry-symbol ≢ labelSym y
      entry≢c (cx sh) = entry≢shape sh
      entry≢c (ca s b) e = head≢ (once-head (Once.CCC.Codegen.AllocExpand.alloc-label s b)) refl (sym e)

      record≢c : ∀ {y} → ShapeC y → alloc-record-symbol ≢ labelSym y
      record≢c (cx sh) = record≢shape sh
      record≢c (ca s b) e = head≢ (once-head (Once.CCC.Codegen.AllocExpand.alloc-label s b)) refl (sym e)

      c≢block : ∀ {y t} → ShapeC y → BlockSym t → labelSym y ≢ t
      c≢block (cx sh) b = shape≢block sh b
      c≢block (ca s b′) (d , refl) = head≢ (once-head (Once.CCC.Codegen.AllocExpand.alloc-label s b′)) (fn-head (bare ("arith.block." ++ˢ d)))

    defined-onceᶜ : Unique Dᶜ
    defined-onceᶜ =
      subst (λ A → Unique (entry-symbol ∷ alloc-record-symbol ∷ A ++ block-syms bs)) (sym adefs-eqᶜ)
        ( (entry≢record ∷ ++⁺ (Data.List.Relation.Unary.All.map (λ { {s} (y , sh , refl) → entry≢c sh }) adefs-shape-c)
                              (Data.List.Relation.Unary.All.map entry≢block (blocks-sym bs)))
        ∷ ++⁺ (Data.List.Relation.Unary.All.map (λ { {s} (y , sh , refl) → record≢c sh }) adefs-shape-c)
              (Data.List.Relation.Unary.All.map record≢block (blocks-sym bs))
        ∷ AP-++⁺ adefs-dst-c (blocks-unique bs)
            (Data.List.Relation.Unary.All.map (λ { {s} (y , sh , refl) → Data.List.Relation.Unary.All.map (c≢block sh) (blocks-sym bs) }) adefs-shape-c))

    ----------------------------------------------------------------------
    -- …and every symbol it references is defined or an extern
    ----------------------------------------------------------------------

    Gᶜ : String → Set
    Gᶜ s = s ∈ Dᶜ ⊎ s ∈ ex

    private
      inDᶜ : ∀ {y} → y ∈ dlabs imageᶜ → labelSym y ∈ Dᶜ
      inDᶜ {y} ym = there (there (∈-++⁺ˡ (subst (labelSym y ∈_) (sym adefs-eqᶜ)
                      (subst (labelSym y ∈_) (sym (adefs-labs imageᶜ)) (∈-map⁺ labelSym ym)))))

      lab-Gᶜ : ∀ {l} → instr-ctrl (c-label l) ∈ imageᶜ → Gᶜ (labelSym (once l))
      lab-Gᶜ m = inj₁ (inDᶜ (lab-dl imageᶜ (XX.mem-lab imageᶜ m)))

      -- a label of the outlined image's, kept
      labᵒ-Gᶜ : ∀ {l} → l ∈ Labs imageᵒ → Gᶜ (labelSym (once l))
      labᵒ-Gᶜ ml = lab-Gᶜ (XX.kept-in 0 imageᵒ (XX.lab-mem imageᵒ ml) (λ k ()) (λ k ()))

      -- an entry of the outlined image's
      entᵒ-Gᶜ : ∀ {e} → e ∈ Ents imageᵒ → Gᶜ (labelSym (callee e))
      entᵒ-Gᶜ {e} me = inj₁ (inDᶜ (ent-dl imageᶜ (subst (e ∈_) (sym (XX.ents-exp 0 imageᵒ)) me)))

      rec-G : Gᶜ alloc-record-symbol
      rec-G = inj₁ (there (here refl))

      -- what the image's file resolves, the call mode's does
      toᶜ : ∀ {s} → G s → Gᶜ s
      toᶜ (inj₂ q) = inj₂ q
      toᶜ (inj₁ (here e)) = inj₁ (here e)
      toᶜ (inj₁ (there (here e))) = inj₁ (there (here e))
      toᶜ {s} (inj₁ (there (there q))) = by (∈-++⁻ (adefs P′) q)
        where
          from-dl : ∀ {y} → y ∈ dlabs image → Gᶜ (labelSym y)
          from-dl ym = pick (dl-in image ym)
            where
              pick : ∀ {y} → (Σ LabelId λ l → y ≡ once l × l ∈ Labs image) ⊎ (Σ EntryId λ e → y ≡ callee e × e ∈ Ents image) → Gᶜ (labelSym y)
              pick (inj₁ (l , refl , ml)) = labᵒ-Gᶜ (subst (l ∈_) (sym labs-out) (there ml))
              pick (inj₂ (e , refl , me)) = entᵒ-Gᶜ (subst (e ∈_) (sym ents-out) (∈-++⁺ʳ (rents ksᵒ) me))
          by : (s ∈ adefs P′) ⊎ (s ∈ block-syms bs) → Gᶜ s
          by (inj₂ b) = inj₁ (there (there (∈-++⁺ʳ (adefs Pᶜ) b)))
          by (inj₁ a) = at-def (∈-map⁻ labelSym (subst (s ∈_) (adefs-labs image) (subst (s ∈_) adefs-eq a)))
            where
              at-def : (Σ Label λ y → y ∈ dlabs image × s ≡ labelSym y) → Gᶜ s
              at-def (y , ym , refl) = from-dl ym

      ref-of : ∀ {i} → i ∈ image → IOk.Ref i
      ref-of (here refl) = tt
      ref-of (there m) = proj₂ (proj₂ (Data.List.Relation.Unary.All.lookup IA.tail-ok m))

      AllR : AbstractInstr → Set
      AllR i = All Gᶜ (instr-refs i)

      alloc-refs : ∀ n k → fetch imageᵒ n ≡ just (instr-alloc-heap k) → All AllR (Once.CCC.Codegen.AllocExpand.alloc-code C (n + 0) k)
      alloc-refs n k f =
          [] ∷ (rec-G ∷ []) ∷ (rec-G ∷ []) ∷ [] ∷ (bump ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ (rec-G ∷ []) ∷ []
        ∷ (rec-G ∷ []) ∷ (done ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ [] ∷ [] ∷ [] ∷ []
        where
          bump = lab-Gᶜ (XX.alloc-in 0 imageᵒ n k f (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))
          done = lab-Gᶜ (XX.alloc-in 0 imageᵒ n k f (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))))))))

      free-refs : ∀ k → All AllR (Once.CCC.Codegen.AllocExpand.free-code C k)
      free-refs k = (rec-G ∷ []) ∷ (rec-G ∷ []) ∷ [] ∷ [] ∷ (rec-G ∷ []) ∷ (rec-G ∷ []) ∷ []

      heads-refs : ∀ c → All AllR (Once.CCC.Codegen.AllocExpand.heads C c)
      heads-refs zero    = []
      heads-refs (suc c) = (rec-G ∷ []) ∷ heads-refs c

      setup-refs : All AllR (Once.CCC.Codegen.AllocExpand.setup C)
      setup-refs = (rec-G ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ []
                 ∷ ++⁺ (heads-refs (Once.CCC.Codegen.AllocExpand.Classes.count C))
                       ([] ∷ [] ∷ [] ∷ (rec-G ∷ []) ∷ [] ∷ (rec-G ∷ []) ∷ [])

      -- a size of the image's has its routines
      rents-in : ∀ k → k ∈ ksᵒ → (e-fn (alloc-fn k) ∈ Ents imageᵒ) × (e-fn (free-fn k) ∈ Ents imageᵒ)
      rents-in k m = subst (e-fn (alloc-fn k) ∈_) (sym ents-out) (∈-++⁺ˡ (ra ksᵒ m)) , subst (e-fn (free-fn k) ∈_) (sym ents-out) (∈-++⁺ˡ (rf ksᵒ m))
        where
          ra : ∀ ks → k ∈ ks → e-fn (alloc-fn k) ∈ rents ks
          ra (k′ ∷ ks) (here refl) = here refl
          ra (k′ ∷ ks) (there q)   = there (there (ra ks q))
          rf : ∀ ks → k ∈ ks → e-fn (free-fn k) ∈ rents ks
          rf (k′ ∷ ks) (here refl) = there (here refl)
          rf (k′ ∷ ks) (there q)   = there (there (rf ks q))

      -- what a kept instruction of the outlined image references
      kept-refs : ∀ i → i ∈ imageᵒ → (∀ k → i ≡ instr-alloc-heap k → ⊥) → (∀ k → i ≡ instr-free-heap k → ⊥) → AllR i
      kept-refs i (here refl) _ _ = inj₂ (there (here refl)) ∷ rec-G ∷ []
      kept-refs i (there q) nA nF = by (∈-++⁻ (skip ksᵒ) q)
        where
          rou-refs : ∀ {j} → RouI ksᵒ j → (∀ k → j ≡ instr-alloc-heap k → ⊥) → (∀ k → j ≡ instr-free-heap k → ⊥) → AllR j
          rou-refs (ri-ae k _) _ _ = []
          rou-refs (ri-a k _) nA′ _ = ⊥-elim (nA′ k refl)
          rou-refs ri-r _ _ = []
          rou-refs (ri-fe k _) _ _ = []
          rou-refs (ri-f k _) _ nF′ = ⊥-elim (nF′ k refl)
          in-rou : ∀ ks {j} → j ∈ prim-routines ks → RouI ks j
          in-rou ks {j} r = let (n , f) = ∈-fetch′ (prim-routines ks) r in rou ks n j f
            where
              ∈-fetch′ : ∀ (xs : AbstractTrace) {x} → x ∈ xs → Σ ℕ λ n → fetch xs n ≡ just x
              ∈-fetch′ (x ∷ xs) (here refl) = 0 , refl
              ∈-fetch′ (x ∷ xs) (there m′)  = let (n , f′) = ∈-fetch′ xs m′ in suc n , f′
          by : (i ∈ skip ksᵒ) ⊎ (i ∈ map site-call IA.tail) → AllR i
          by (inj₁ (here refl)) = labᵒ-Gᶜ (subst (skip-label ∈_) (sym labs-out) (here refl)) ∷ []
          by (inj₁ (there r)) = in-skip (∈-++⁻ (prim-routines ksᵒ) r)
            where in-skip : (i ∈ prim-routines ksᵒ) ⊎ (i ∈ instr-ctrl (c-label skip-label) ∷ []) → AllR i
                  in-skip (inj₁ r′) = rou-refs (in-rou ksᵒ r′) nA nF
                  in-skip (inj₂ (here refl)) = []
                  in-skip (inj₂ (there ()))
          by (inj₂ r) = let (x , mx , e) = ∈-map⁻ site-call r in subst AllR (sym e) (site (site-view x) mx)
            where
              sz-of : ∀ {x k} → x ∈ IA.tail → (x ≡ instr-alloc-heap k) ⊎ (x ≡ instr-free-heap k) → k ∈ ksᵒ
              sz-of {x} {k} mx e = let (n , f) = ∈-fetchᵗ IA.tail mx in
                Once.CCC.Codegen.AllocOutlineSizes.in-dsizes {FS} image (suc n) k (cases e f)
                where
                  ∈-fetchᵗ : ∀ (xs : AbstractTrace) {y} → y ∈ xs → Σ ℕ λ n → fetch xs n ≡ just y
                  ∈-fetchᵗ (y ∷ xs) (here refl) = 0 , refl
                  ∈-fetchᵗ (y ∷ xs) (there m′)  = let (n , f′) = ∈-fetchᵗ xs m′ in suc n , f′
                  cases : ∀ {n} → (x ≡ instr-alloc-heap k) ⊎ (x ≡ instr-free-heap k) → fetch IA.tail n ≡ just x
                        → (fetch image (suc n) ≡ just (instr-alloc-heap k)) ⊎ (fetch image (suc n) ≡ just (instr-free-heap k))
                  cases (inj₁ refl) f′ = inj₁ f′
                  cases (inj₂ refl) f′ = inj₂ f′

              site : ∀ {x} → SiteView x → x ∈ IA.tail → AllR (site-call x)
              site (sv-alloc k) mx = entᵒ-Gᶜ (proj₁ (rents-in k (sz-of mx (inj₁ refl)))) ∷ []
              site (sv-free k) mx  = entᵒ-Gᶜ (proj₂ (rents-in k (sz-of mx (inj₂ refl)))) ∷ []
              site {x} (sv-same s) mx = subst AllR (sym s)
                (Data.List.Relation.Unary.All.map toᶜ (refs-ok x (ref-of (there mx)) (Data.List.Relation.Unary.All.lookup (jmp-pt image jumps-in) (there mx)) (there mx)))
      refs-c : ∀ i → i ∈ imageᶜ → AllR i
      refs-c i m = by (XX.in-exp 0 imageᵒ m)
        where
          by : XX.InExp 0 imageᵒ i → AllR i
          by (XX.in-kept q nA nF) = kept-refs i q nA nF
          by (XX.in-alloc n k f q) = Data.List.Relation.Unary.All.lookup (alloc-refs n k f) q
          by (XX.in-free k q) = Data.List.Relation.Unary.All.lookup (free-refs k) q
          by (XX.in-setup q) = Data.List.Relation.Unary.All.lookup setup-refs q

    resolvedᶜ : All Gᶜ (arefs Pᶜ)
    resolvedᶜ =
      All-fold-room arefs instr-refs (λ _ _ → refl) (room-refs-G (inj₁ (there (here refl))) (inj₂ (there (here refl)))) (λ _ _ _ → refl) imageᶜ
        (arefs-of imageᶜ (Data.List.Relation.Unary.All.tabulate (λ {i} m → refs-c i m)))

    -- ★★ THE CALL MODE'S FILE IS WELL-FORMED, as symbols
    image-wfᶜ : ImageWF Pᶜ bs ex
    image-wfᶜ = defined-onceᶜ , resolvedᶜ , image-externs-valid image
