-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageSyms — plan 0.146 B1.7 step 3 (D464): ★ THE NEW IMAGE'S
-- FILE IS WELL-FORMED, as symbols: what `AsmWF` reads of it.
--
--   * every symbol the file defines is defined once: the image's labels and
--     entries are distinct (`LabelsI.image-dst`, `EntriesI.image-edst`), each
--     owned by a block (`once-lincore.b<j>`, D464), so their symbols are
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
open import Once.CCC.Codegen.ImageSymbols using (instr-defs; instr-refs; adefs; arefs; entry-symbol)
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

module LI = Once.LinCore.LabelsI fmt ans bw
module EI = Once.LinCore.EntriesI fmt ans bw
module IAll = Once.LinCore.ImageAll fmt ans bw

------------------------------------------------------------------------
-- 1. ★ A BLOCK'S NAME READS BACK (D464), and is no arith block's.
------------------------------------------------------------------------

opaque
  unfolding nameOf

  nameOf-good : ∀ j → All PeelS (CanonicalName.parts (nameOf j))
  nameOf-good j = (_ , _ , refl , refl)
                ∷ subst Peel (sym (toList∘fromList ('b' ∷ Data.Nat.Show.charsInBase 10 j))) (_ , _ , refl , refl) ∷ []
    where import Data.Nat.Show

  nameOf-two : ∀ j → length (CanonicalName.parts (nameOf j)) ≡ 2
  nameOf-two j = refl

-- an arith block's name reads back too
block-good : ∀ d → All PeelS (CanonicalName.parts (bare ("arith.block." ++ˢ d)))
block-good d = subst Peel (sym (toList-++ "arith.block." d)) (_ , _ , refl , refl) ∷ []

-- ★ a block's symbol is no arith block's
name≢block : ∀ j d → once-symbol-path (nameOf j) ≢ once-symbol-path (bare ("arith.block." ++ˢ d))
name≢block j d e = two≢one (trans (sym (nameOf-two j)) (cong (λ c → length (CanonicalName.parts c))
                     (once-symbol-path-injective-peel (nameOf j) (bare ("arith.block." ++ˢ d)) (nameOf-good j) (block-good d) e)))
  where two≢one : 2 ≡ 1 → ⊥
        two≢one ()

-- the labels and entries of the image
data ShapeL : Label → Set where
  s-jl : ∀ j k → ShapeL (once (jl j k))
  s-fn : ∀ j → ShapeL (callee (e-fn (nameOf j)))
  s-tl : ∀ j → ShapeL (callee (e-thunk (tl j)))

shape-lab : ∀ {y l} → y ≡ once l → (Σ ℕ λ j → Σ ℕ λ k → l ≡ jl j k) → ShapeL y
shape-lab refl (j , k , refl) = s-jl j k

shape-ent : ∀ {y e} → y ≡ callee e → (Σ ℕ λ j → e ≡ e-fn (nameOf j) ⊎ e ≡ e-thunk (tl j)) → ShapeL y
shape-ent refl (j , inj₁ refl) = s-fn j
shape-ent refl (j , inj₂ refl) = s-tl j

shape-good : ∀ {y} → ShapeL y → GoodL y
shape-good (s-jl j k) = refl , nameOf-good j
shape-good (s-fn j)   = nameOf-good j
shape-good (s-tl j)   = refl , nameOf-good j

shape-def : ∀ {y} → ShapeL y → DefL y
shape-def (s-jl j k) = Once.Adequacy.LabelSymbols.d-once
shape-def (s-fn j)   = Once.Adequacy.LabelSymbols.d-callee
shape-def (s-tl j)   = Once.Adequacy.LabelSymbols.d-callee

private
  head≢ : ∀ {s t : String} → head-of (toList s) ≡ '.' → head-of (toList t) ≡ 'o' → s ≢ t
  head≢ hs ht e = case trans (sym hs) (trans (cong (λ z → head-of (toList z)) e) ht) of λ ()

-- ★ a label's symbol is no arith block's, and not the entry's
shape≢block : ∀ {y t} → ShapeL y → BlockSym t → labelSym y ≢ t
shape≢block (s-jl j k) (d , refl) = head≢ (once-head (jl j k)) (fn-head (bare ("arith.block." ++ˢ d)))
shape≢block (s-fn j)   (d , refl) = name≢block j d
shape≢block (s-tl j)   (d , refl) = head≢ (thunk-head (tl j)) (fn-head (bare ("arith.block." ++ˢ d)))

entry≢shape : ∀ {y} → ShapeL y → entry-symbol ≢ labelSym y
entry≢shape (s-jl j k) e = head≢ (once-head (jl j k)) refl (sym e)
entry≢shape (s-fn j)   e = entry≢osp (nameOf j) e
entry≢shape (s-tl j)   e = head≢ (thunk-head (tl j)) refl (sym e)

entry≢block : ∀ {t} → BlockSym t → entry-symbol ≢ t
entry≢block (d , refl) = entry≢osp (bare ("arith.block." ++ˢ d))

-- D470: the allocator record's symbol is no label's, no block's, not the entry's
record≢shape : ∀ {y} → ShapeL y → alloc-record-symbol ≢ labelSym y
record≢shape (s-jl j k) e = head≢ (once-head (jl j k)) refl (sym e)
record≢shape (s-fn j)   e = record≢osp (nameOf j) e
record≢shape (s-tl j)   e = head≢ (thunk-head (tl j)) refl (sym e)

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
  ilab-sv (instr-ctrl (c-start _)) = refl
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
  open _⊑U using (go)
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
  adefs-eq = fold-room adefs (λ i xs → instr-defs i ++ xs) (λ _ _ → refl) (λ _ _ → refl) image

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
  -- D468: THE IMAGE'S LABELS HAVE AN EMPTY PATH (its own: `jl`, `tl`), apart
  -- from the allocator expansion's (`AllocExpand.lb-bump`/`lb-done`)
  ----------------------------------------------------------------------

  private
    lab-in : ∀ xs {m} → instr-ctrl (c-label m) ∈ xs → m ∈ Labs xs
    lab-in (x ∷ xs) (here refl) = here refl
    lab-in (x ∷ xs) {m} (there p) = lab-up (FlatMachine.label-of? {FS} x) (lab-in xs p)
      where lab-up : ∀ mo → m ∈ Labs xs → m ∈ LabsC.lab {FS} mo (Labs xs)
            lab-up (just _) q = there q
            lab-up nothing  q = q

    path-of : ∀ {m} → m ∈ Labs image → LabelId.path m ≡ []
    path-of p = path-jl (Data.List.Relation.Unary.All.lookup labs-shape p)
      where path-jl : ∀ {m} → (Σ ℕ λ j → Σ ℕ λ k → m ≡ jl j k) → LabelId.path m ≡ []
            path-jl (_ , _ , refl) = refl

  img-path : ∀ n m → fetch image n ≡ just (instr-ctrl (c-label m)) → LabelId.path m ≡ []
  img-path n m f = path-of (lab-in image (fetch-∈ {FS} image n f))

  jmp-path : ∀ n m → fetch image n ≡ just (instr-ctrl (c-jmp m)) → LabelId.path m ≡ []
  jmp-path n m f = path-of (Data.List.Relation.Unary.All.lookup (jmp-pt image jumps-in) (fetch-∈ {FS} image n f) m refl)

  br-path : ∀ n m → fetch image n ≡ just (instr-ctrl (c-branch-tag-zero m)) → LabelId.path m ≡ []
  br-path n m f = path-of (Data.List.Relation.Unary.All.lookup (jmp-pt image jumps-in) (fetch-∈ {FS} image n f) m refl)

  private
    refs-ok : ∀ (i : AbstractInstr) → IOk.Ref i → (∀ l → jump-of i ≡ just l → l ∈ Labs image) → i ∈ image → All G (instr-refs i)
    refs-ok (instr-ctrl (c-label _)) r jin m = []
    refs-ok (instr-ctrl (c-entry (e-thunk _) _)) r jin m = []
    refs-ok (instr-ctrl (c-entry (e-fn _) _)) r jin m = []
    refs-ok (instr-ctrl (c-jmp n)) r jin m = lab-G (jin n refl) ∷ []
    refs-ok (instr-ctrl (c-branch-tag-zero n)) r jin m = lab-G (jin n refl) ∷ []
    refs-ok (instr-ctrl (c-ret _)) r jin m = []
    refs-ok (instr-ctrl (c-call-fn _)) ((σ , κ) , p , refl) jin m = fn-G p ∷ []
    refs-ok (instr-ctrl (c-start _)) r jin m = []
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
    refs-ok (instr-room _) r jin m = inj₂ (there (here refl)) ∷ []
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
    All-fold-room arefs instr-refs (λ _ _ → refl) (λ _ → inj₂ (there (here refl)) ∷ []) image
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
