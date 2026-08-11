-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition
--
-- Plan 0.32 Phase D (composition, Stage 1): the BLOCK-OFFSET machinery
-- for the abstract↔x86 plus-simulation. Each abstract instruction lowers
-- to a contiguous x86 BLOCK (1 instr for most, 2 for alloc-heap, …), so
-- the x86 pc is NOT the flat pc — it is `x86-off prog (flat-pc)`, the sum
-- of block lengths before it. This module proves the load-bearing
-- `find-label` preservation: a jump that lands at flat index `j` lands at
-- x86 index `x86-off prog j` in the compiled program. (Injective encodings
-- + a non-lockstep simulation — see the plus-simulation design.)
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.Adequacy.ArchCorrectness.X86-64.FlatComposition (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; length; drop)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (Label; once; thunk; _≡ᵇᴸ_; LabelId; _≡ᵇᴵ_; ≡ᵇᴵ-true; ≢⇒≡ᵇᴵfalse)
open import Once.Type using (FitsInReg; fits-int; fits-float)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X
import Once.CCC.Target.X86-64.Syntax as XS
open import Once.CCC.Target.X86-64.Syntax
  using ( Instr; Program
        ; mov; lea; add; sub; cmp; test; jmp; je; jne; call; call-sym
        ; ret; push; pop; nop; ud2; syscall; label
        ; Operand; reg; imm; rsp; slots)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-abstract; compile-trace)

------------------------------------------------------------------------
-- Plan 0.65 G1b: THE BLOCK-OFFSET MACHINERY IS ARCH-GENERIC and lives in
-- `…FlatCore.FlatComposition`. What x86-64 supplies is its instruction type,
-- its emitter, its fetch — and the two things only an ISA can say: which
-- instructions are labels, and that the label scan steps past the ones that
-- are not. That second one is `skip-law`, and its 22-clause case split is the
-- enumeration this module used to carry inside `find-label-go-skip`. It is the
-- same evidence; it now lives where the constructors do, and the correspondence
-- gets a three-line induction instead.
------------------------------------------------------------------------
is-label? : XS.Instr → Bool
is-label? (label _) = true
is-label? (mov _ _) = false
is-label? (lea _ _) = false
is-label? (add _ _) = false
is-label? (sub _ _) = false
is-label? (cmp _ _) = false
is-label? (test _ _) = false
is-label? (jmp _) = false
is-label? (je _) = false
is-label? (jne _) = false
is-label? (call _) = false
is-label? (call-sym _) = false
is-label? ret = false
is-label? (push _) = false
is-label? (pop _) = false
is-label? nop = false
is-label? ud2 = false
is-label? syscall = false

-- The scan steps past a non-label. One `refl` per constructor: the case split
-- is what makes `X.find-label-go`'s catch-all reduce.
skip-law : ∀ (t : Label) (i : XS.Instr) (rest : Program) (xi : ℕ)
         → is-label? i ≡ false
         → X.find-label-go t (i ∷ rest) xi ≡ X.find-label-go t rest (suc xi)
skip-law t (label _) rest xi ()
skip-law t (mov _ _) rest xi _ = refl
skip-law t (lea _ _) rest xi _ = refl
skip-law t (add _ _) rest xi _ = refl
skip-law t (sub _ _) rest xi _ = refl
skip-law t (cmp _ _) rest xi _ = refl
skip-law t (test _ _) rest xi _ = refl
skip-law t (jmp _) rest xi _ = refl
skip-law t (je _) rest xi _ = refl
skip-law t (jne _) rest xi _ = refl
skip-law t (call _) rest xi _ = refl
skip-law t (call-sym _) rest xi _ = refl
skip-law t ret rest xi _ = refl
skip-law t (push _) rest xi _ = refl
skip-law t (pop _) rest xi _ = refl
skip-law t nop rest xi _ = refl
skip-law t ud2 rest xi _ = refl
skip-law t syscall rest xi _ = refl

open import Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition FS XS.Instr
       compile-abstract compile-trace (λ _ _ → refl)
       X.fetch (λ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl)
       is-label? X.find-label-go skip-law
  public
  -- the block-offset names this arch's downstream modules already use
  renaming (blk-len to x86-len; blk-off to x86-off; blk-off-suc to x86-off-suc)

-- Plan 0.63 (D082): a block that IS a single label, but in a FOREIGN
-- provenance. The scan does not match it and steps past it, costing one
-- index — the whole content of the premise is that `_≡ᵇᴸ_` says `false`,
-- which for a `thunk` label against a `once` target is its catch-all.
find-label-go-skip-other : ∀ (target ℓ : Label) (rest : Program) (xi : ℕ)
  → (ℓ ≡ᵇᴸ target) ≡ false
  → X.find-label-go target (label ℓ ∷ rest) xi ≡ X.find-label-go target rest (suc xi)
find-label-go-skip-other target ℓ rest xi ne rewrite ne = refl

------------------------------------------------------------------------
-- HeadView: per-instruction evidence that confines the constructor
-- enumeration to `headView`, so `find-label-pres` stays structural.
-- Either the head is `instr-ctrl (c-label m)` (compiles to a single
-- `label (once m)`) or its x86 block is label-free; in both cases we
-- record how flat `fl-go` reduces on the head.
------------------------------------------------------------------------
-- Plan 0.63: each constructor now records how BOTH scans reduce on the head —
-- the `once` scan (`fl-go`, jumps) and the `thunk` scan (`ft-go`, calls). One
-- enumeration serves both; a parallel `headView` would duplicate 40 clauses to
-- say the mirror-image thing.
data HeadView (i : AbstractInstr) : Set where
  hv-clabel : (m : LabelId)
    → compile-abstract i ≡ label (once m) ∷ []
    → (∀ rest tgt acc → fl-go (i ∷ rest) tgt acc ≡ fl-label-match (m ≡ᵇᴵ tgt) rest tgt acc)
    -- a `once` label is INVISIBLE to the call scan: `thunk-of?` misses it, and
    -- concretely `once m ≡ᵇᴸ thunk tgt` is the catch-all `false` (D082).
    → (∀ rest tgt acc → ft-go (i ∷ rest) tgt acc ≡ ft-go rest tgt (suc acc))
    → HeadView i
  hv-plain : has-label (compile-abstract i) ≡ false
    → (∀ rest tgt acc → fl-go (i ∷ rest) tgt acc ≡ fl-go rest tgt (suc acc))
    → (∀ rest tgt acc → ft-go (i ∷ rest) tgt acc ≡ ft-go rest tgt (suc acc))
    → HeadView i
  -- Plan 0.63 (D082): a block that OPENS WITH A FOREIGN-PROVENANCE LABEL.
  -- `c-thunk` fits neither case above — it IS a label instruction (so it
  -- occupies an index on both sides, which `hv-plain` would deny) but it is
  -- not a `once` label (so `hv-clabel`'s matching scan must not fire).
  -- Both scans therefore step over the whole block. Step 2a made the block
  -- LONGER than one instruction (the label is followed by the body's frame
  -- reservation), so the tail is carried explicitly and only has to be
  -- label-free — `hv-clabel`'s single-instruction shape would not do.
  -- The provenance premise is `refl` at every producer precisely because
  -- provenances are definitionally disjoint — what D082 bought.
  -- …and it is the THUNK label specifically (the only producer is `c-thunk`),
  -- which is what lets the same view drive the call scan: there this head is
  -- the MATCH decision, exactly as `hv-clabel` is for the jump scan.
  hv-otherlabel : (m : LabelId) (tail : Program)
    → compile-abstract i ≡ label (thunk m) ∷ tail
    → has-label tail ≡ false
    → (∀ rest tgt acc → fl-go (i ∷ rest) tgt acc ≡ fl-go rest tgt (suc acc))
    → (∀ rest tgt acc → ft-go (i ∷ rest) tgt acc ≡ ft-match (m ≡ᵇᴵ tgt) rest tgt acc)
    → HeadView i

reg-op-no-label : ∀ (op : RegOp) → has-label (compile-abstract (instr-reg-op op)) ≡ false
reg-op-no-label scratch-one = refl
reg-op-no-label scratch-zero = refl
reg-op-no-label scratch-dec = refl
reg-op-no-label scratch-load-count = refl
reg-op-no-label count-zero = refl
reg-op-no-label count-inc = refl

const-no-label : ∀ {A} (p : FitsInReg A) (v : _) → has-label (compile-abstract (instr-load-const p v)) ≡ false
const-no-label fits-int   v = refl
const-no-label fits-float v = refl

headView : ∀ (i : AbstractInstr) → HeadView i
headView mov-to-output = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView mov-to-input = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView mov-output-to-input2 = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView mov-input2-to-output = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView load-indirect = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView load-indirect-suc = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView store-indirect = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView store-indirect-suc = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView instr-pop-frame = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView instr-call-closure = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView instr-save-closure-reg = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (load-from-slot _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (store-at-slot _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (lea-slot _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (lea-indexed _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (restore-input _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-alloc-stack _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-dealloc-stack _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-reclaim-to _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-push-frame _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (worklist-init _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (worklist-push _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (worklist-pop _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (worklist-check _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-load-code-addr _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-load-tag-lit _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-alloc-heap _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-loop _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-sigop si) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-load-const p v) = hv-plain (const-no-label p v) (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-case-on-tag f g) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-reg-op op) = hv-plain (reg-op-no-label op) (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-label m)) = hv-clabel m refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-thunk m b)) =
  hv-otherlabel m (sub (reg rsp) (imm (slots b)) ∷ []) refl refl
                (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-ret b)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-jmp m)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-branch-scratch-zero m)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-branch-tag-zero m)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)

------------------------------------------------------------------------
-- THE CALL SCAN (Plan 0.63). `find-thunk` is `find-label`'s mirror over the
-- OTHER provenance: a closure call resolves its body by scanning for
-- `c-thunk n`, and the emitted `call` resolves `.L_thunk_n` — which after
-- D081 is `X.find-label … (thunk n)`. The two agree modulo `x86-off`, by the
-- same structural induction over `All HeadView`, with the roles of the two
-- label cases EXCHANGED: `hv-clabel` steps past (a jump label is invisible to
-- the call scan) and `hv-otherlabel` is the match.
--
-- That exchange is exactly what D082 bought. Both "steps past" premises are
-- the catch-all of `_≡ᵇᴸ_` on mismatched provenances, so they are `refl` at
-- every producer — no label-uniqueness argument anywhere.
------------------------------------------------------------------------
find-thunk-pres : ∀ (prog : AbstractTrace) (target : LabelId) (acc xi j : ℕ)
  → All HeadView prog
  → ft-go prog target acc ≡ just j
  → Σ ℕ (λ d → (j ≡ acc + d)
        × (X.find-label-go (thunk target) (compile-trace prog) xi ≡ just (xi + x86-off prog d)))
find-thunk-pres [] target acc xi j _ ()
find-thunk-pres (i ∷ rest) target acc xi j (hv-plain hl _ ft-p ∷ all-rest) ft-eq =
  let ih = find-thunk-pres rest target (suc acc) (xi + x86-len i) j all-rest
             (trans (sym (ft-p rest target acc)) ft-eq)
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , trans (find-label-go-skip (thunk target) (compile-abstract i) (compile-trace rest) xi hl)
           (trans (proj₂ (proj₂ ih)) (cong just (+-assoc xi (x86-len i) (x86-off rest d'))))
-- a JUMP label: the call scan misses it, and so does the compiled scan
-- (`once m ≡ᵇᴸ thunk target` is the catch-all).
find-thunk-pres (i ∷ rest) target acc xi j (hv-clabel m ca-eq _ ft-p ∷ all-rest) ft-eq
  rewrite ca-eq =
  let ih = find-thunk-pres rest target (suc acc) (suc xi) j all-rest
             (trans (sym (ft-p rest target acc)) ft-eq)
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , trans (proj₂ (proj₂ ih))
           (cong just (trans (sym (+-suc xi (x86-off rest d')))
                             (cong (λ L → xi + (L + x86-off rest d')) (sym (cong length ca-eq)))))
-- THE MATCH CASE: a `c-thunk m` block. Both scans decide on `m ≡ᵇ target`.
find-thunk-pres (i ∷ rest) target acc xi j (hv-otherlabel m tl ca-eq nl _ ft-m ∷ all-rest) ft-eq
  with m ≡ᵇᴵ target in meq
... | true rewrite ca-eq | meq = 0 , comp1 , cong just (sym (+-identityʳ xi))
  where
    jinj : ∀ {a b : ℕ} → (just a) ≡ (just b) → a ≡ b
    jinj refl = refl
    acc≡j : acc ≡ j
    acc≡j = jinj (trans (sym (cong (λ b → ft-match b rest target acc) meq))
                        (trans (sym (ft-m rest target acc)) ft-eq))
    comp1 : j ≡ acc + 0
    comp1 = trans (sym acc≡j) (sym (+-identityʳ acc))
... | false rewrite ca-eq | meq =
  let ih = find-thunk-pres rest target (suc acc) (suc xi + length tl) j all-rest
             (trans (sym (cong (λ b → ft-match b rest target acc) meq))
                    (trans (sym (ft-m rest target acc)) ft-eq))
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , trans (find-label-go-skip (thunk target) tl (compile-trace rest) (suc xi) nl)
           (trans (proj₂ (proj₂ ih))
                  (cong just (trans (trans (cong suc (+-assoc xi (length tl) (x86-off rest d')))
                                           (sym (+-suc xi (length tl + x86-off rest d'))))
                                    (cong (λ L → xi + (L + x86-off rest d')) (sym (cong length ca-eq))))))

------------------------------------------------------------------------
-- find-label preservation: a flat jump landing at flat index j lands at
-- x86 index `x86-off prog j` in the compiled program. The flat target is
-- a ℕ; the x86 target is `once target` (compiler provenance), so SigOp
-- labels (sigop _ _) never interfere — definitional via `_≡ᵇᴸ_`.
-- Structural over `All HeadView prog` (enumeration lives in headView).
------------------------------------------------------------------------
just-inj : ∀ {a b : ℕ} → (just a) ≡ (just b) → a ≡ b
just-inj refl = refl

find-label-pres : ∀ (prog : AbstractTrace) (target : LabelId) (acc xi j : ℕ)
  → All HeadView prog
  → fl-go prog target acc ≡ just j
  → Σ ℕ (λ d → (j ≡ acc + d)
        × (X.find-label-go (once target) (compile-trace prog) xi ≡ just (xi + x86-off prog d)))
find-label-pres [] target acc xi j _ ()
find-label-pres (i ∷ rest) target acc xi j (hv-plain hl fl-p _ ∷ all-rest) fl-eq =
  let ih = find-label-pres rest target (suc acc) (xi + x86-len i) j all-rest
             (trans (sym (fl-p rest target acc)) fl-eq)
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , trans (find-label-go-skip (once target) (compile-abstract i) (compile-trace rest) xi hl)
           (trans (proj₂ (proj₂ ih)) (cong just (+-assoc xi (x86-len i) (x86-off rest d'))))
find-label-pres (i ∷ rest) target acc xi j (hv-otherlabel m tl ca-eq nl fl-p _ ∷ all-rest) fl-eq
  rewrite ca-eq =
  let ih = find-label-pres rest target (suc acc) (suc xi + length tl) j all-rest
             (trans (sym (fl-p rest target acc)) fl-eq)
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , trans (find-label-go-skip (once target) tl (compile-trace rest) (suc xi) nl)
           (trans (proj₂ (proj₂ ih))
                  (cong just (trans (trans (cong suc (+-assoc xi (length tl) (x86-off rest d')))
                                           (sym (+-suc xi (length tl + x86-off rest d'))))
                                    (cong (λ L → xi + (L + x86-off rest d')) (sym (cong length ca-eq))))))
find-label-pres (i ∷ rest) target acc xi j (hv-clabel m ca-eq fl-c _ ∷ all-rest) fl-eq
  with m ≡ᵇᴵ target in meq
... | true rewrite ca-eq | meq = 0 , comp1 , cong just (sym (+-identityʳ xi))
  where
    acc≡j : acc ≡ j
    acc≡j = just-inj (trans (sym (cong (λ b → fl-label-match b rest target acc) meq))
                            (trans (sym (fl-c rest target acc)) fl-eq))
    comp1 : j ≡ acc + 0
    comp1 = trans (sym acc≡j) (sym (+-identityʳ acc))
... | false rewrite ca-eq | meq =
  let ih = find-label-pres rest target (suc acc) (suc xi) j all-rest
             (trans (sym (cong (λ b → fl-label-match b rest target acc) meq))
                    (trans (sym (fl-c rest target acc)) fl-eq))
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , trans (proj₂ (proj₂ ih))
           (cong just (trans (sym (+-suc xi (x86-off rest d')))
                             (cong (λ L → xi + (L + x86-off rest d')) (sym (cong length ca-eq)))))

-- headView is total (every current instruction is a c-label, a
-- foreign-provenance label — `c-thunk` — or a label-free block;
-- `compile-sigOp` = call-sym, no labels), so the
-- All-HeadView side-condition is always dischargeable. (Plan 0.33 S2 will
-- generalize the hv-plain evidence to `no once-label` so this stays total
-- when label-using SigOps are inlined; today it holds outright.)
all-headView : ∀ (prog : AbstractTrace) → All HeadView prog
all-headView []         = []
all-headView (i ∷ rest) = headView i ∷ all-headView rest

-- find-label preservation, side-condition discharged: a flat jump to flat
-- index j corresponds to the x86 jump to block-offset index x86-off prog j.
find-label-corr : ∀ (prog : AbstractTrace) (target : LabelId) (xi j : ℕ)
  → fl-go prog target 0 ≡ just j
  → X.find-label-go (once target) (compile-trace prog) xi ≡ just (xi + x86-off prog j)
find-label-corr prog target xi j fl-eq with find-label-pres prog target 0 xi j (all-headView prog) fl-eq
... | (d , j≡0+d , x86-eq) rewrite j≡0+d = x86-eq

-- …and the CALL's, the same statement over the `thunk` provenance: the flat
-- machine's `find-thunk` and the emitted `call`'s label resolution land on the
-- same block. This is what `instr-call-closure`'s block-step will consume.
find-thunk-corr : ∀ (prog : AbstractTrace) (target : LabelId) (xi j : ℕ)
  → ft-go prog target 0 ≡ just j
  → X.find-label-go (thunk target) (compile-trace prog) xi ≡ just (xi + x86-off prog j)
find-thunk-corr prog target xi j ft-eq with find-thunk-pres prog target 0 xi j (all-headView prog) ft-eq
... | (d , j≡0+d , x86-eq) rewrite j≡0+d = x86-eq

------------------------------------------------------------------------
-- Fetch preservation (Plan 0.32 Stage 2): the x86 program, viewed from a
-- block offset, is the compiled tail of the flat program. So fetching the
-- compiled program at `x86-off prog k` gives the start of block k.
------------------------------------------------------------------------
-- These all come from `FlatCore.FlatComposition` now (opened above):
--   drop-[] / drop-len-++ / drop-+ / drop-compile / fetch-drop /
--   fetch-at-offset / x86-off-suc (blk-off-suc) / drop-fetch
-- — list and offset arithmetic with no instruction set in it.

-- The x86 instruction at block offset k is the head of compile-abstract i
-- (where i is the flat instruction at flat index k).
fetch-block-head : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → X.fetch (compile-trace prog) (x86-off prog k)
    ≡ X.fetch (compile-abstract i ++ compile-trace (drop (suc k) prog)) 0
fetch-block-head prog k i ft =
  trans (fetch-at-offset prog k)
        (cong (λ p → X.fetch (compile-trace p) 0) (drop-fetch prog k i ft))

-- The SECOND x86 instruction of block k (for 2-instr blocks: c-branch's je,
-- alloc-heap's add). At offset x86-off prog k + 1.
fetch-block-2nd : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → X.fetch (compile-trace prog) (x86-off prog k + 1)
    ≡ X.fetch (drop 1 (compile-abstract i ++ compile-trace (drop (suc k) prog))) 0
fetch-block-2nd prog k i ft =
  trans (fetch-drop (compile-trace prog) (x86-off prog k + 1))
        (cong (λ xs → X.fetch xs 0)
              (trans (drop-+ (x86-off prog k) 1 (compile-trace prog))
                     (trans (cong (drop 1) (drop-compile prog k))
                            (cong (λ p → drop 1 (compile-trace p)) (drop-fetch prog k i ft)))))

-- The THIRD x86 instruction of the block at flat index k (offset +2). Same shape
-- as fetch-block-2nd; needed by 3-instruction blocks (e.g. push-frame).
fetch-block-3rd : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → X.fetch (compile-trace prog) (x86-off prog k + 2)
    ≡ X.fetch (drop 2 (compile-abstract i ++ compile-trace (drop (suc k) prog))) 0
fetch-block-3rd prog k i ft =
  trans (fetch-drop (compile-trace prog) (x86-off prog k + 2))
        (cong (λ xs → X.fetch xs 0)
              (trans (drop-+ (x86-off prog k) 2 (compile-trace prog))
                     (trans (cong (drop 2) (drop-compile prog k))
                            (cong (λ p → drop 2 (compile-trace p)) (drop-fetch prog k i ft)))))

-- The FOURTH x86 instruction of the block at flat index k (offset +3) — the
-- 6-instruction `lea-indexed` block needs these.
fetch-block-4th : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → X.fetch (compile-trace prog) (x86-off prog k + 3)
    ≡ X.fetch (drop 3 (compile-abstract i ++ compile-trace (drop (suc k) prog))) 0
fetch-block-4th prog k i ft =
  trans (fetch-drop (compile-trace prog) (x86-off prog k + 3))
        (cong (λ xs → X.fetch xs 0)
              (trans (drop-+ (x86-off prog k) 3 (compile-trace prog))
                     (trans (cong (drop 3) (drop-compile prog k))
                            (cong (λ p → drop 3 (compile-trace p)) (drop-fetch prog k i ft)))))

-- The FIFTH x86 instruction of the block at flat index k (offset +4) — the
-- 6-instruction `lea-indexed` block needs these.
fetch-block-5th : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → X.fetch (compile-trace prog) (x86-off prog k + 4)
    ≡ X.fetch (drop 4 (compile-abstract i ++ compile-trace (drop (suc k) prog))) 0
fetch-block-5th prog k i ft =
  trans (fetch-drop (compile-trace prog) (x86-off prog k + 4))
        (cong (λ xs → X.fetch xs 0)
              (trans (drop-+ (x86-off prog k) 4 (compile-trace prog))
                     (trans (cong (drop 4) (drop-compile prog k))
                            (cong (λ p → drop 4 (compile-trace p)) (drop-fetch prog k i ft)))))

-- The SIXTH x86 instruction of the block at flat index k (offset +5) — the
-- 6-instruction `lea-indexed` block needs these.
fetch-block-6th : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → X.fetch (compile-trace prog) (x86-off prog k + 5)
    ≡ X.fetch (drop 5 (compile-abstract i ++ compile-trace (drop (suc k) prog))) 0
fetch-block-6th prog k i ft =
  trans (fetch-drop (compile-trace prog) (x86-off prog k + 5))
        (cong (λ xs → X.fetch xs 0)
              (trans (drop-+ (x86-off prog k) 5 (compile-trace prog))
                     (trans (cong (drop 5) (drop-compile prog k))
                            (cong (λ p → drop 5 (compile-trace p)) (drop-fetch prog k i ft)))))

------------------------------------------------------------------------
-- find-label, NEGATIVE direction: if the flat scan finds no `c-label m`,
-- the compiled scan finds no `label (once m)` either.
--
-- The invariant this needs is PROVENANCE, not disjointness: `compile-abstract`
-- emits a `label` only for `instr-ctrl (c-label m)`, and then exactly
-- `label (once m)` — which is what `HeadView` already enumerates (`hv-clabel` /
-- `hv-plain`'s `has-label ≡ false`). Label UNIQUENESS is never needed: both
-- scanners return their first match, so duplicates align rather than conflict.
------------------------------------------------------------------------
find-label-none-go : ∀ (prog : AbstractTrace) (target : LabelId) (acc xi : ℕ)
  → All HeadView prog
  → fl-go prog target acc ≡ nothing
  → X.find-label-go (once target) (compile-trace prog) xi ≡ nothing
find-label-none-go [] target acc xi _ _ = refl
find-label-none-go (i ∷ rest) target acc xi (hv-plain nl fl-p _ ∷ all-rest) fl-eq =
  trans (find-label-go-skip (once target) (compile-abstract i)
                            (compile-trace rest) xi nl)
        (find-label-none-go rest target (suc acc) (xi + length (compile-abstract i))
                            all-rest (trans (sym (fl-p rest target acc)) fl-eq))
-- Plan 0.63: a foreign-provenance label never matches a `once` target, so
-- the compiled scan just steps past it — one index, like the flat scan.
find-label-none-go (i ∷ rest) target acc xi (hv-otherlabel m tl ca-eq nl fl-p _ ∷ all-rest) fl-eq
  rewrite ca-eq =
  trans (find-label-go-skip (once target) tl (compile-trace rest) (suc xi) nl)
        (find-label-none-go rest target (suc acc) (suc xi + length tl) all-rest
                            (trans (sym (fl-p rest target acc)) fl-eq))
find-label-none-go (i ∷ rest) target acc xi (hv-clabel m ca-eq fl-c _ ∷ all-rest) fl-eq
  with m ≡ᵇᴵ target in meq
-- a MATCH contradicts the flat scan's `nothing`
... | true  = absurd (trans (sym fl-eq)
                (trans (fl-c rest target acc)
                       (cong (λ b → fl-label-match b rest target acc) meq)))
  where absurd : ∀ {A : Set} {x : A} → (nothing ≡ just x)
               → X.find-label-go (once target) (compile-trace (i ∷ rest)) xi ≡ nothing
        absurd ()
... | false rewrite ca-eq | meq =
  find-label-none-go rest target (suc acc) (suc xi) all-rest
    (trans (sym (cong (λ b → fl-label-match b rest target acc) meq))
           (trans (sym (fl-c rest target acc)) fl-eq))

find-label-none-corr : ∀ (prog : AbstractTrace) (target : LabelId)
  → fl-go prog target 0 ≡ nothing
  → X.find-label (compile-trace prog) (once target) ≡ nothing
find-label-none-corr prog target fl-eq =
  find-label-none-go prog target 0 0 (all-headView prog) fl-eq
