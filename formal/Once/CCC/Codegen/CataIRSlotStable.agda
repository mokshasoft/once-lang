-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataIRSlotStable — the codegen-image half of the
-- frame-discipline invariant (Plan 0.36 task #8): every trace
-- `ir-to-trace` emits is slot-stable (`AllSlotStable`).
--
-- Combined with `CataNextSlot.exec-flat-keeps-next-slot` (exec-flat over
-- a slot-stable trace preserves next-slot), this discharges the algebra's
-- frame discipline: the compiled algebra leaves `next-slot` fixed, so the
-- algebra IH's `next-slot ≡ 0` precondition holds at every cata layer.
--
-- Structural induction on the IR. Almost every constructor emits a list
-- of slot-stable instructions (control / reg-ops / loads / stores / mov /
-- alloc-heap) plus recursively-compiled sub-traces; `case` wraps its
-- branches in `instr-case-on-tag` (slot-stable iff the branches are —
-- `AllI`, via `All→AllI`); `Cata` routes through `cata-dispatch`
-- (`cata-dispatch-slot-stable`).
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.CataIRSlotStable (o : CanonicalName) where

open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-assoc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.IR
open import Once.IRTy using (⌈_⌉F)
open import Once.Type using (Functor; K; Id; _⊕_; _⊗_; fits-int; fits-float)
open import Once.CCC.Machine.SMCore using (AbstractTrace; AbstractInstr;
         mov-to-output; mov-to-input; mov-output-to-input2; mov-input2-to-output;
         load-indirect; load-indirect-suc; load-from-slot; store-at-slot;
         store-indirect; store-indirect-suc; lea-slot; restore-input;
         instr-alloc-stack; instr-dealloc-stack; instr-reclaim-to;
         instr-push-frame; instr-pop-frame; instr-call-closure;
         worklist-init; worklist-push; worklist-pop; worklist-check;
         instr-sigop; instr-load-const; instr-load-code-addr; instr-save-closure-reg;
         instr-load-tag-lit; instr-case-on-tag; instr-alloc-heap; instr-loop;
         instr-reg-op; instr-ctrl; lea-indexed;
         module AbstractExec)
open import Once.CCC.Codegen.IRToTrace o
  using (ir-to-trace; ir-to-trace'; cata-strategy; cata-dispatch;
         CataStrategy; strat-const; strat-nat; strat-linear; strat-branching;
         cata-trace-nat; cata-trace-linear; cata-trace-branching;
         visit-walk; rebuild-walk; lsize; cata-br-I₁; cata-br-I₂;
         -- D099 / C1: the called-algebra blocks.
         cata-body; cata-call-setup; cata-call; cata-trace-const; fsize;
         cata-nat-I₁; cata-nat-I₂; cata-nat-I₃; cata-lin-I₁; cata-lin-I₂; cata-lin-I₃)

module CataIRSlotStable {FS : FrameSemantics} where
  open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot)
  open CataNextSlot {FS} using (SlotStable; SlotStableT; AllSlotStable)
  open AbstractExec {FS} using (AllI)

  -- the trace component of `ir-to-trace'`'s 4-tuple (proj-trace is private
  -- in IRToTrace; this is the same extraction, definitionally).
  trc : ℕ × ℕ × AbstractTrace × List (ℕ × ℕ × AbstractTrace) → AbstractTrace
  trc (_ , _ , t , _) = t

  -- stdlib `All SlotStable` → the spelled-out `SlotStableT` that
  -- `SlotStable (instr-case-on-tag …)` now asks for. (It used to target
  -- SMCore's `AllI SlotStable`; the predicate moved to a mutual definition so
  -- that its recursion is structural — see CataNextSlot, 2026-07-31.)
  All→AllI : ∀ {t} → All SlotStable t → SlotStableT t
  All→AllI []ᴬ        = tt
  All→AllI (px ∷ᴬ ps) = px , All→AllI ps

  ----------------------------------------------------------------------
  -- A boolean decider mirroring `SlotStable` (mutually with `all-stable?`
  -- over traces) + its soundness. This centralises the per-instruction
  -- enumeration ONCE: every fully-concrete trace `ir-to-trace` emits then
  -- discharges via `all-stable?-sound refl` (the decider computes to
  -- `true`), instead of a hand-written `All`-of-`tt`s per trace.
  ----------------------------------------------------------------------
  stable?     : AbstractInstr → Bool
  all-stable? : AbstractTrace → Bool
  stable? (instr-alloc-stack _)   = false
  stable? (instr-reclaim-to _)    = false
  stable? (instr-loop _)          = false
  stable? (instr-case-on-tag f g) = all-stable? f ∧ all-stable? g
  stable? _                       = true
  all-stable? []       = true
  all-stable? (i ∷ is) = stable? i ∧ all-stable? is

  -- split a `_∧_ ≡ true` (no `with` — pattern on the left bool).
  ∧-split : ∀ {a b} → (a ∧ b) ≡ true → (a ≡ true) × (b ≡ true)
  ∧-split {true}  {true}  _  = refl , refl
  ∧-split {false}         ()
  ∧-split {true}  {false} ()

  stable?-sound     : ∀ i → stable? i ≡ true → SlotStable i
  all-stable?-sound : ∀ t → all-stable? t ≡ true → AllSlotStable t
  -- the only non-`true` instructions (alloc-stack/reclaim-to/loop) get an
  -- absurd `()`; case-on-tag recurses through the sub-traces; the catch-all
  -- maps `true → tt` for the slot-stable instructions.
  stable?-sound (instr-alloc-stack _)   ()
  stable?-sound (instr-reclaim-to _)    ()
  stable?-sound (instr-loop _)          ()
  stable?-sound (instr-case-on-tag f g) eq =
    let (ef , eg) = ∧-split eq
    in All→AllI (all-stable?-sound f ef) , All→AllI (all-stable?-sound g eg)
  stable?-sound mov-to-output           _ = tt
  stable?-sound mov-to-input            _ = tt
  stable?-sound mov-output-to-input2    _ = tt
  stable?-sound mov-input2-to-output    _ = tt
  stable?-sound load-indirect           _ = tt
  stable?-sound load-indirect-suc       _ = tt
  stable?-sound (load-from-slot _)      _ = tt
  stable?-sound (store-at-slot _)       _ = tt
  stable?-sound store-indirect          _ = tt
  stable?-sound store-indirect-suc      _ = tt
  stable?-sound (lea-slot _)            _ = tt
  stable?-sound (restore-input _)       _ = tt
  stable?-sound (instr-dealloc-stack _) _ = tt
  stable?-sound (instr-push-frame _)    _ = tt
  stable?-sound instr-pop-frame         _ = tt
  stable?-sound instr-call-closure      _ = tt
  stable?-sound (worklist-init _)       _ = tt
  stable?-sound (worklist-push _)       _ = tt
  stable?-sound (worklist-pop _)        _ = tt
  stable?-sound (worklist-check _)      _ = tt
  stable?-sound (instr-sigop _)         _ = tt
  stable?-sound (instr-load-const _ _)  _ = tt
  stable?-sound (instr-load-code-addr _) _ = tt
  stable?-sound instr-save-closure-reg  _ = tt
  stable?-sound (instr-load-tag-lit _)  _ = tt
  stable?-sound (instr-alloc-heap _)    _ = tt
  stable?-sound (instr-reg-op _)        _ = tt
  stable?-sound (instr-ctrl _)          _ = tt
  stable?-sound (lea-indexed _)         _ = tt
  all-stable?-sound []       _  = []ᴬ
  all-stable?-sound (i ∷ is) eq =
    let (ei , eis) = ∧-split eq
    in stable?-sound i ei ∷ᴬ all-stable?-sound is eis

  ----------------------------------------------------------------------
  -- Completeness (the converse) + `all-stable?` distributes over `++`.
  -- Needed for the Tier-2 branching trace, whose `(rebuild-walk F ++
  -- Rest) ++ final-read` shape is a NEUTRAL `++` that `++⁺` cannot split;
  -- the boolean equation navigates associativity cleanly instead.
  ----------------------------------------------------------------------
  AllI→All : ∀ {t} → SlotStableT t → All SlotStable t
  AllI→All {[]}     _        = []ᴬ
  AllI→All {_ ∷ _} (px , ps) = px ∷ᴬ AllI→All ps

  ∧-intro : ∀ {a b} → a ≡ true → b ≡ true → a ∧ b ≡ true
  ∧-intro {a} {b} pa pb = trans (cong (_∧ b) pa) pb

  all-stable?-++ : ∀ xs ys → all-stable? (xs ++ ys) ≡ all-stable? xs ∧ all-stable? ys
  all-stable?-++ []       ys = refl
  all-stable?-++ (i ∷ is) ys =
    trans (cong (stable? i ∧_) (all-stable?-++ is ys))
          (sym (∧-assoc (stable? i) (all-stable? is) (all-stable? ys)))

  stable?-complete     : ∀ i → SlotStable i → stable? i ≡ true
  all-stable?-complete : ∀ t → AllSlotStable t → all-stable? t ≡ true
  stable?-complete (instr-alloc-stack _)   ()
  stable?-complete (instr-reclaim-to _)    ()
  stable?-complete (instr-loop _)          ()
  stable?-complete (instr-case-on-tag f g) (af , ag) =
    ∧-intro (all-stable?-complete f (AllI→All af)) (all-stable?-complete g (AllI→All ag))
  stable?-complete mov-to-output           _ = refl
  stable?-complete mov-to-input            _ = refl
  stable?-complete mov-output-to-input2    _ = refl
  stable?-complete mov-input2-to-output    _ = refl
  stable?-complete load-indirect           _ = refl
  stable?-complete load-indirect-suc       _ = refl
  stable?-complete (load-from-slot _)      _ = refl
  stable?-complete (store-at-slot _)       _ = refl
  stable?-complete store-indirect          _ = refl
  stable?-complete store-indirect-suc      _ = refl
  stable?-complete (lea-slot _)            _ = refl
  stable?-complete (restore-input _)       _ = refl
  stable?-complete (instr-dealloc-stack _) _ = refl
  stable?-complete (instr-push-frame _)    _ = refl
  stable?-complete instr-pop-frame         _ = refl
  stable?-complete instr-call-closure      _ = refl
  stable?-complete (worklist-init _)       _ = refl
  stable?-complete (worklist-push _)       _ = refl
  stable?-complete (worklist-pop _)        _ = refl
  stable?-complete (worklist-check _)      _ = refl
  stable?-complete (instr-sigop _)         _ = refl
  stable?-complete (instr-load-const _ _)  _ = refl
  stable?-complete (instr-load-code-addr _) _ = refl
  stable?-complete instr-save-closure-reg  _ = refl
  stable?-complete (instr-load-tag-lit _)  _ = refl
  stable?-complete (instr-alloc-heap _)    _ = refl
  stable?-complete (instr-reg-op _)        _ = refl
  stable?-complete (instr-ctrl _)          _ = refl
  stable?-complete (lea-indexed _)         _ = refl
  all-stable?-complete []       _          = refl
  all-stable?-complete (i ∷ is) (px ∷ᴬ ps) =
    ∧-intro (stable?-complete i px) (all-stable?-complete is ps)

  ----------------------------------------------------------------------
  -- Tier-2 structural walks (`visit-walk` / `rebuild-walk`): since item 6
  -- the ⊕ dispatch is FLAT control, so every clause is a plain splice of
  -- concrete chunks (ctrl/prologue instructions, `all-stable?`-sound) and
  -- the recursive walks.
  ----------------------------------------------------------------------
  visit-walk-stable : ∀ td tv tb F s lb → AllSlotStable (visit-walk td tv tb F s lb)
  visit-walk-stable td tv tb (K _)   s lb = []ᴬ
  visit-walk-stable td tv tb Id      s lb = all-stable?-sound _ refl
  visit-walk-stable td tv tb (F ⊕ G) s lb =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (visit-walk-stable td tv tb G _ _)
      (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
       ++⁺ (visit-walk-stable td tv tb F _ _) (tt ∷ᴬ []ᴬ))
  visit-walk-stable td tv tb (F ⊗ G) s lb =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (visit-walk-stable td tv tb G _ _)
      (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ visit-walk-stable td tv tb F _ _)

  rebuild-walk-stable : ∀ vs tv tb F s lb → AllSlotStable (rebuild-walk vs tv tb F s lb)
  rebuild-walk-stable vs tv tb (K _)   s lb = all-stable?-sound _ refl
  rebuild-walk-stable vs tv tb Id      s lb = all-stable?-sound _ refl
  rebuild-walk-stable vs tv tb (F ⊕ G) s lb =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (rebuild-walk-stable vs tv tb G _ _)
      (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ   -- wrap-sum 1 s
       tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ                                   -- jmp, label, prologue
       ++⁺ (rebuild-walk-stable vs tv tb F _ _)
         (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ -- wrap-sum 0 s
          tt ∷ᴬ []ᴬ))
  rebuild-walk-stable vs tv tb (F ⊗ G) s lb =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (rebuild-walk-stable vs tv tb F _ _)
      (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
       ++⁺ (rebuild-walk-stable vs tv tb G _ _) (all-stable?-sound _ refl))

  ----------------------------------------------------------------------
  -- The three non-degenerate cata strategy traces. Concrete scaffold
  -- chunks (descend/ascend control, build-layer, push2/pop2/wrap-sum)
  -- discharge via `all-stable?-sound refl`; the spliced algebra trace
  -- `at` uses the hypothesis `sat`; `++⁺` mirrors each concatenation.
  ----------------------------------------------------------------------
  -- NatF (Tier-0): scratch-one ∷ count-zero ∷ descend-flat(12) ∷
  -- scratch-load-count ∷ load-tag ∷ mov ∷ build-layer-0(10) ∷ mov ∷
  -- (at ++ ascend-flat); ascend-flat = la-top ∷ la-end ∷ mov ∷
  -- build-layer-1(10) ∷ mov ∷ ((at ++ [scratch-dec]) ++ [jmp,label]).
  -- D099 / C1: the algebra is a CALLED BODY now, so every strategy's trace is
  -- `cata-body ++ <all concrete>` — and that makes these four witnesses
  -- collapse. The body is the only place `at` appears, so it is the only place
  -- the hypothesis is needed; everything after it settles by the decider.
  --
  -- `instr-call-closure` is slot-stable (the predicate is ⊥ only for
  -- `instr-alloc-stack`/`instr-reclaim-to`/`instr-loop`), which is the same
  -- reason `ir-stable apply` is `all-stable?-sound refl`.
  cata-body-stable : ∀ b e bb at → AllSlotStable at
                   → AllSlotStable (cata-body b e bb at)
  cata-body-stable b e bb at sat = tt ∷ᴬ tt ∷ᴬ ++⁺ sat (tt ∷ᴬ tt ∷ᴬ []ᴬ)

  cata-trace-const-stable : ∀ bb n1 l1 at → AllSlotStable at
                          → AllSlotStable (proj₂ (proj₂ (cata-trace-const bb n1 l1 at)))
  cata-trace-const-stable bb n1 l1 at sat =
    ++⁺ (all-stable?-sound (cata-call-setup n1 (n1 +ℕ 1) l1 ++ cata-call n1 (n1 +ℕ 1)) refl)
        (cata-body-stable l1 (l1 +ℕ 1) bb at sat)

  cata-trace-nat-stable : ∀ bb n1 l1 at → AllSlotStable at
                        → AllSlotStable (proj₂ (proj₂ (cata-trace-nat bb n1 l1 at)))
  cata-trace-nat-stable bb n1 l1 at sat =
    ++⁺ (all-stable?-sound
           (cata-call-setup (suc (suc n1)) (suc (suc (suc n1)))
                            (suc (suc (suc (suc (suc (suc l1)))))) ++
            (cata-nat-I₁ n1 l1 ++
             (cata-call (suc (suc n1)) (suc (suc (suc n1))) ++
              (cata-nat-I₂ n1 l1 ++
               (cata-call (suc (suc n1)) (suc (suc (suc n1))) ++ cata-nat-I₃ l1))))) refl)
        (cata-body-stable (suc (suc (suc (suc (suc (suc l1)))))) (suc (suc (suc (suc (suc (suc (suc l1))))))) bb at sat)

  cata-trace-linear-stable : ∀ bb n1 l1 at → AllSlotStable at
                           → AllSlotStable (proj₂ (proj₂ (cata-trace-linear bb n1 l1 at)))
  cata-trace-linear-stable bb n1 l1 at sat =
    ++⁺ (all-stable?-sound
           (cata-call-setup (suc (suc (suc (suc (suc (suc n1))))))
                            (suc (suc (suc (suc (suc (suc (suc n1)))))))
                            (suc (suc (suc (suc l1)))) ++
            (cata-lin-I₁ n1 l1 ++
             (cata-call (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) ++
              (cata-lin-I₂ n1 l1 ++
               (cata-call (suc (suc (suc (suc (suc (suc n1)))))) (suc (suc (suc (suc (suc (suc (suc n1))))))) ++ cata-lin-I₃ l1))))) refl)
        (cata-body-stable (suc (suc (suc (suc l1)))) (suc (suc (suc (suc (suc l1))))) bb at sat)

  -- Tier 2 is the one exception: its skeleton splices the two COMPILE-TIME
  -- functor walks, which are stuck on `F`, so the tail still needs the boolean
  -- route with those two peels (the algebra's peel is gone — it is in the body).
  cata-trace-branching-stable : ∀ F bb n1 l1 at → AllSlotStable at
                              → AllSlotStable (proj₂ (proj₂ (cata-trace-branching F bb n1 l1 at)))
  -- Nested `++⁺` mirroring the emitter's own nesting, NOT a two-way
  -- prefix/body split: `cata-br-I₁` contains the functor walks, which are stuck
  -- on `F`, so the concrete blocks around them do not reduce and the
  -- association is not definitional (nat/linear get away with the flat split
  -- precisely because every block there IS concrete).
  cata-trace-branching-stable F bb n1 l1 at sat =
    ++⁺ (all-stable?-sound (cata-call-setup cl (cl +ℕ 1) bodyL) refl)
        (++⁺ (all-stable?-sound (cata-br-I₁ F n1 l1) I₁-true)
             (++⁺ (all-stable?-sound (cata-call cl (cl +ℕ 1)) refl)
                  (++⁺ (all-stable?-sound (cata-br-I₂ n1 l1) refl)
                       (cata-body-stable bodyL (bodyL +ℕ 1) bb at sat))))
    where
      bodyL = l1 +ℕ 4 +ℕ lsize F +ℕ lsize F
      cl    = n1 +ℕ 7 +ℕ (4 *ℕ fsize F) +ℕ 4
      I₁-true : all-stable? (cata-br-I₁ F n1 l1) ≡ true
      I₁-true =
        trans (all-stable?-++ (visit-walk n1 (n1 +ℕ 4) (n1 +ℕ 5) F (n1 +ℕ 7) (l1 +ℕ 4)) _)
          (∧-intro (all-stable?-complete _ (visit-walk-stable n1 (n1 +ℕ 4) (n1 +ℕ 5) F (n1 +ℕ 7) (l1 +ℕ 4)))
            (trans (all-stable?-++ (rebuild-walk (n1 +ℕ 2) (n1 +ℕ 4) (n1 +ℕ 5) F (n1 +ℕ 7) (l1 +ℕ 4 +ℕ lsize F)) _)
              (∧-intro (all-stable?-complete _ (rebuild-walk-stable (n1 +ℕ 2) (n1 +ℕ 4) (n1 +ℕ 5) F (n1 +ℕ 7) (l1 +ℕ 4 +ℕ lsize F)))
                       refl)))

  cata-dispatch-slot-stable : ∀ (strat : CataStrategy) (bb n l : ℕ) (at : AbstractTrace)
                            → AllSlotStable at
                            → AllSlotStable (proj₂ (proj₂ (cata-dispatch strat bb n l at)))
  cata-dispatch-slot-stable strat-const         bb n l at sat = cata-trace-const-stable bb n l at sat
  cata-dispatch-slot-stable strat-nat           bb n l at sat = cata-trace-nat-stable bb n l at sat
  cata-dispatch-slot-stable strat-linear        bb n l at sat = cata-trace-linear-stable bb n l at sat
  cata-dispatch-slot-stable (strat-branching F) bb n l at sat = cata-trace-branching-stable F bb n l at sat

  ----------------------------------------------------------------------
  -- The theorem: every trace `ir-to-trace` emits is slot-stable.
  -- Concrete-trace constructors discharge uniformly via `all-stable?-sound
  -- refl`; the four sub-trace-carrying constructors (∘ / pair / case /
  -- Cata) recurse + `++⁺` / `All→AllI` / `cata-dispatch-slot-stable`.
  ----------------------------------------------------------------------
  ir-stable : ∀ {A B} (ir : IR A B) (n l : ℕ) → AllSlotStable (trc (ir-to-trace' n l ir))
  ir-stable id              n l = all-stable?-sound _ refl
  ir-stable fst             n l = all-stable?-sound _ refl
  ir-stable snd             n l = all-stable?-sound _ refl
  ir-stable terminal        n l = all-stable?-sound _ refl
  ir-stable initial         n l = all-stable?-sound _ refl
  ir-stable apply           n l = all-stable?-sound _ refl
  -- the flip: the body is inline, so the decider cannot settle the whole
  -- fragment by itself — the prefix/suffix compute, the body recurses.
  ir-stable (curry b Stack) n l =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (ir-stable b _ _) (tt ∷ᴬ tt ∷ᴬ []ᴬ)
  ir-stable (curry b Heap)  n l =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (ir-stable b _ _) (tt ∷ᴬ tt ∷ᴬ []ᴬ)
  ir-stable (SigOp _)       n l = all-stable?-sound _ refl
  ir-stable (const fits-int _)   n l = all-stable?-sound _ refl
  ir-stable (const fits-float _) n l = all-stable?-sound _ refl
  ir-stable (inl Stack)     n l = all-stable?-sound _ refl
  ir-stable (inr Stack)     n l = all-stable?-sound _ refl
  ir-stable (inl Heap)      n l = all-stable?-sound _ refl
  ir-stable (inr Heap)      n l = all-stable?-sound _ refl
  ir-stable (In _ _)        n l = all-stable?-sound _ refl
  ir-stable (out-μ _)       n l = all-stable?-sound _ refl
  ir-stable (Para _ _)      n l = all-stable?-sound _ refl
  ir-stable (Out _)         n l = all-stable?-sound _ refl
  ir-stable (in-ν _ _)      n l = all-stable?-sound _ refl
  ir-stable (Ana _ _)       n l = all-stable?-sound _ refl
  ir-stable (Hylo _ _ _ _)  n l = all-stable?-sound _ refl
  ir-stable (Fuse _ _ _ _)  n l = all-stable?-sound _ refl
  ir-stable (free-heap _)   n l = all-stable?-sound _ refl
  ir-stable (g ∘ f)         n l = ++⁺ (ir-stable f n l) (tt ∷ᴬ ir-stable g _ _)
  ir-stable (⟨ f , g ⟩ Stack) n l =
    tt ∷ᴬ tt ∷ᴬ ++⁺ (ir-stable f _ _) (tt ∷ᴬ tt ∷ᴬ ++⁺ (ir-stable g _ _) (tt ∷ᴬ tt ∷ᴬ []ᴬ))
  ir-stable (⟨ f , g ⟩ Heap) n l =
    tt ∷ᴬ tt ∷ᴬ ++⁺ (ir-stable f _ _) (tt ∷ᴬ tt ∷ᴬ ++⁺ (ir-stable g _ _) (all-stable?-sound _ refl))
  -- item 6: case is FLAT CONTROL — plain splices.
  ir-stable (case f g)      n l =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (ir-stable g _ _)
      (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
       ++⁺ (ir-stable f n (suc (suc l))) (tt ∷ᴬ []ᴬ))
  -- C1: the algebra is generated at frontier 0 (its own frame).
  ir-stable (Cata {F} _ alg) n l =
    cata-dispatch-slot-stable (cata-strategy ⌈ F ⌉F) _ _ _ _ (ir-stable alg 0 l)

  -- top-level: the trace `ir-to-trace ir` (= `trc (ir-to-trace' 0 0 ir)`).
  ir-to-trace-slot-stable : ∀ {A B} (ir : IR A B) → AllSlotStable (ir-to-trace ir)
  ir-to-trace-slot-stable ir = ir-stable ir 0 0
