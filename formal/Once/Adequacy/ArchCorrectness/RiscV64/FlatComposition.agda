-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition
--
-- THE SECOND INSTANCE OF `FlatCore.{HeadView,FlatComposition}`
-- (plan 0.65, 2026-08-12).
--
-- Written now, and not at G2, for one reason: a core with a single instance
-- is not known to be generic, only known to typecheck. Everything below is
-- what riscv64 has to say for itself — which instructions are labels, that the
-- scan steps past the ones that are not and decides on the ones that are, and
-- how THIS emitter lowers each abstract instruction. The 500 lines of
-- block-offset arithmetic and scan preservation come back by instantiation,
-- unchanged, and every law is discharged exactly as x86-64 discharges it.
--
-- TWO PLACES WHERE riscv64 IS GENUINELY DIFFERENT, and they are the test:
--
--   * `c-thunk n b` lowers to THREE instructions (`label ; addi sp ; sd ra`)
--     where x86-64's is two. `hv-otherlabel` carries its tail explicitly, so
--     the difference is one longer list in one clause — nothing in the core
--     moves. That field was introduced for x86-64's two-instruction block and
--     this is the first evidence it was the right shape rather than a shape
--     that happened to fit.
--   * `c-branch-scratch-zero` is ONE instruction (`beq s3 zero`) against
--     x86-64's `cmp ; je`. That difference does not surface here — block
--     LENGTH is data, not structure — which is precisely why it belongs to the
--     branch-block law of G1d step 3 and not to this layer.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.Adequacy.ArchCorrectness.RiscV64.FlatComposition (FS : FrameSemantics) where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just)
open import Data.Integer using (+_) renaming (-_ to ℤ-)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (Label; once; thunk; _≡ᵇᴸ_)
open import Once.Type using (FitsInReg; fits-int; fits-float)
import Once.CCC.Target.RiscV64.Semantics as R
import Once.CCC.Target.RiscV64.Syntax as RS
open import Once.CCC.Target.RiscV64.Syntax
  using ( Instr; Program
        ; ld; sd; add; sub; addi; li; auipc; lla; mv; beq; bne; jal; jalr
        ; j; ret; call; call-sym; nop; unimp; label
        ; sp; ra; t1; s3; slots )
open import Once.CCC.Target.RiscV64.AbstractToRiscV using (compile-abstract; compile-trace)

------------------------------------------------------------------------
-- WHICH INSTRUCTIONS ARE LABELS, and the three scan equations that follow.
-- One `refl` per constructor, exactly as on x86-64: the case split is what
-- makes `R.find-label-go`'s catch-all reduce.
------------------------------------------------------------------------
is-label? : RS.Instr → Bool
is-label? (label _) = true
is-label? (ld _ _ _) = false
is-label? (sd _ _ _) = false
is-label? (add _ _ _) = false
is-label? (sub _ _ _) = false
is-label? (addi _ _ _) = false
is-label? (li _ _) = false
is-label? (auipc _ _) = false
is-label? (lla _ _) = false
is-label? (mv _ _) = false
is-label? (beq _ _ _) = false
is-label? (bne _ _ _) = false
is-label? (jal _ _) = false
is-label? (jalr _ _ _) = false
is-label? (j _) = false
is-label? ret = false
is-label? (call _) = false
is-label? (call-sym _) = false
is-label? nop = false
is-label? unimp = false

skip-law : ∀ (t : Label) (i : RS.Instr) (rest : Program) (xi : ℕ)
         → is-label? i ≡ false
         → R.find-label-go t (i ∷ rest) xi ≡ R.find-label-go t rest (suc xi)
skip-law t (label _) rest xi ()
skip-law t (ld _ _ _) rest xi _ = refl
skip-law t (sd _ _ _) rest xi _ = refl
skip-law t (add _ _ _) rest xi _ = refl
skip-law t (sub _ _ _) rest xi _ = refl
skip-law t (addi _ _ _) rest xi _ = refl
skip-law t (li _ _) rest xi _ = refl
skip-law t (auipc _ _) rest xi _ = refl
skip-law t (lla _ _) rest xi _ = refl
skip-law t (mv _ _) rest xi _ = refl
skip-law t (beq _ _ _) rest xi _ = refl
skip-law t (bne _ _ _) rest xi _ = refl
skip-law t (jal _ _) rest xi _ = refl
skip-law t (jalr _ _ _) rest xi _ = refl
skip-law t (j _) rest xi _ = refl
skip-law t ret rest xi _ = refl
skip-law t (call _) rest xi _ = refl
skip-law t (call-sym _) rest xi _ = refl
skip-law t nop rest xi _ = refl
skip-law t unimp rest xi _ = refl

label-hit : ∀ (ℓ t : Label) (rest : Program) (xi : ℕ)
          → (ℓ ≡ᵇᴸ t) ≡ true
          → R.find-label-go t (label ℓ ∷ rest) xi ≡ just xi
label-hit ℓ t rest xi eq rewrite eq = refl

label-miss : ∀ (ℓ t : Label) (rest : Program) (xi : ℕ)
           → (ℓ ≡ᵇᴸ t) ≡ false
           → R.find-label-go t (label ℓ ∷ rest) xi ≡ R.find-label-go t rest (suc xi)
label-miss ℓ t rest xi eq rewrite eq = refl

open import Once.Adequacy.ArchCorrectness.FlatCore.HeadView
       FS RS.Instr compile-abstract is-label? label
  public

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

------------------------------------------------------------------------
-- How THIS emitter lowers each abstract instruction, as far as the scans can
-- see it. The one interesting clause is `c-thunk`, whose block is three
-- instructions long — the label, the frame reservation, and the `ra` spill
-- D102 restored.
------------------------------------------------------------------------
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
-- THREE instructions, where x86-64's is two: the entry label, the frame
-- reservation, and the `ra` spill (D102). `hv-otherlabel`'s explicit tail
-- absorbs the difference — no core change, one longer list here.
headView (instr-ctrl (c-thunk m b)) =
  hv-otherlabel m (addi sp sp (ℤ- (+ (slots b))) ∷ sd ra sp (slots b) ∷ []) refl refl
                (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-ret b)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-jmp m)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-branch-scratch-zero m)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-branch-tag-zero m)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)

------------------------------------------------------------------------
-- …and the whole block-offset and scan-preservation development comes back.
-- Every equation riscv64 supplies below the line is `refl`, exactly as on
-- x86-64 — which is the evidence the parameterisation is over facts the two
-- arches genuinely share.
------------------------------------------------------------------------
open import Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition FS RS.Instr
       compile-abstract compile-trace refl (λ _ _ → refl)
       R.fetch (λ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl)
       is-label? label R.find-label-go (λ _ _ → refl) skip-law
       label-hit label-miss headView
  public
