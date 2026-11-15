-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
-- alloc-heap) plus recursively-compiled sub-traces; `Cata` routes through
-- `cata-dispatch`
-- (`cata-dispatch-slot-stable`).
------------------------------------------------------------------------

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys
-- its labels. `o` is constant for a whole definition, so it belongs on the
-- module rather than on every lemma — which is exactly what keeps the
-- statements below UNCHANGED under D089: `IRToTrace` is imported APPLIED,
-- so each `ir-to-trace' n l ir` reads as it always did.
open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.CataIRSlotStable (o : CanonicalName) where

open import Data.Nat using (ℕ; suc)
import Data.Nat as ℕ
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-assoc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.IR
open import Once.IRTy using (K; Id; _⊕_; _⊗_; fits-int; fits-float; ⌈_⌉F; WellFormedFI; wf-K; wf-Id; wf-Prod; wf-Sum)
open import Once.CCC.Label using (ℓ)
open import Once.Spec.Type using (K; Id; _⊕_; _⊗_)
open import Once.Type using (fits-int; fits-float)
open import Once.CCC.Machine.SMCore using (blocks-layout; link-top)
open import Once.CCC.Machine.SMCore using (LabelId; AbstractTrace; AbstractInstr; mov-to-output; mov-to-input; load-indirect; load-indirect-suc; load-from-slot; store-at-slot; store-indirect; store-indirect-suc; lea-slot; restore-input; instr-alloc-stack; instr-dealloc-stack; instr-reclaim-to; instr-push-frame; instr-pop-frame; instr-call-closure; worklist-init; worklist-push; worklist-pop; worklist-check; instr-sigop; instr-load-const; instr-load-code-addr; instr-save-closure-reg; instr-load-tag-lit; instr-alloc-heap; instr-reg-op; instr-free-heap; instr-room; load-at; store-at; addr-at; instr-ctrl)
open import Data.Maybe using (Maybe; just; nothing)
open import Once.SigOp.Info using (module SigOpInfo; SigOpInfo)
open SigOpInfo using (sem)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (CmpAt; cmp-of)
open import Once.CCC.Machine.MuRep using (MuRep; mu-box; mu-unit; mu-ptr; mu-rep)
open import Once.CCC.Codegen.IRToTrace o
  using (sigop-code; ir-to-trace; ir-to-trace-lab; ir-to-unit; ir-to-trace'; cata-strategy; cata-dispatch; resuspend-layer; CataStrategy; strat-const; strat-box; strat-branching; cata-trace-branching; cata-trace-box; cata-call-box; in-trace; with-copy; two-cell; out-trace; visit-walk; rebuild-walk; lsize; cata-br-I₁; cata-br-I₂; -- D099 / C1: the called-algebra blocks.
         cata-body; cata-call-setup; cata-call; cata-trace-const; fsize;
         cata-call-from; inj-trace; env-entry; getμ; wrap-sum; push2)
open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; put; put-k; get; get-k; kind; lkind; lsz;
  put-All; put-k-All; get-All; get-k-All; fill; fill-All)
open import Once.CCC.Codegen.Size using (size)
open import Once.IRTy using (IRTy; IRFunctor; ⟦_⟧TI; ν-type) renaming (_+_ to _+ᵀ_)
open import Once.Spec.Type using (Fun)

module CataIRSlotStable {FS : FrameSemantics} where
  open import Once.CCC.Codegen.CataNextSlot using (module CataNextSlot)
  open CataNextSlot {FS} using (SlotStable; AllSlotStable)

  -- the trace component of `ir-to-trace'`'s 4-tuple (proj-trace is private
  -- in IRToTrace; this is the same extraction, definitionally).
  trc : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace) → AbstractTrace
  trc (_ , _ , t , _) = t


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
  {-# CATCHALL #-}
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
  -- the only non-`true` instructions (alloc-stack/reclaim-to) get an
  -- absurd `()`; the catch-all
  -- maps `true → tt` for the slot-stable instructions.
  stable?-sound (instr-alloc-stack _)   ()
  stable?-sound (instr-reclaim-to _)    ()
  stable?-sound mov-to-output           _ = tt
  stable?-sound mov-to-input            _ = tt
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
  stable?-sound (instr-free-heap _)     _ = tt
  stable?-sound (load-at _)     _ = tt
  stable?-sound (store-at _)     _ = tt
  stable?-sound (addr-at _)     _ = tt
  stable?-sound (instr-room _)     _ = tt
  stable?-sound (instr-ctrl _)          _ = tt
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
  stable?-complete mov-to-output           _ = refl
  stable?-complete mov-to-input            _ = refl
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
  stable?-complete (instr-free-heap _)     _ = refl
  stable?-complete (load-at _)     _ = refl
  stable?-complete (store-at _)     _ = refl
  stable?-complete (addr-at _)     _ = refl
  stable?-complete (instr-room _)     _ = refl
  stable?-complete (instr-ctrl _)          _ = refl
  all-stable?-complete []       _          = refl
  all-stable?-complete (i ∷ is) (px ∷ᴬ ps) =
    ∧-intro (stable?-complete i px) (all-stable?-complete is ps)

  ----------------------------------------------------------------------
  -- Tier-2 structural walks (`visit-walk` / `rebuild-walk`): since item 6
  -- the ⊕ dispatch is FLAT control, so every clause is a plain splice of
  -- concrete chunks (ctrl/prologue instructions, `all-stable?`-sound) and
  -- the recursive walks.
  ----------------------------------------------------------------------
  -- plan 0.123 B.4 α: the layout code is slot-stable, whatever the type.
  put-st : ∀ X s b o′ → AllSlotStable (put X s b o′)
  put-st X s b o′ = put-All X s b o′ tt tt tt (λ _ → tt) (λ _ → tt)

  put-k-st : ∀ kd n s b o′ → AllSlotStable (put-k kd n s b o′)
  put-k-st kd n s b o′ = put-k-All kd n s b o′ tt tt tt (λ _ → tt) (λ _ → tt)

  get-st : ∀ X k → AllSlotStable (get X k)
  get-st X k = get-All X k (λ _ → tt) (λ _ → tt) tt

  getμ-st : ∀ G k → AllSlotStable (getμ G k)
  getμ-st G k = get-k-All (lkind G word) (lsz G 1) k (λ _ → tt) (λ _ → tt) tt

  fill-st : ∀ from c → AllSlotStable (fill from c)
  fill-st from c = fill-All from c tt (λ _ → tt)

  wrap-st : ∀ tag pk ps ss s → AllSlotStable (wrap-sum tag pk ps ss s)
  wrap-st tag pk ps ss s =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ ++⁺ (fill-st _ (ss ℕ.∸ suc ps)) (++⁺ (put-k-st pk ps s (suc s) 1) (tt ∷ᴬ []ᴬ))

  inj-st : ∀ t P S n → AllSlotStable (inj-trace t P S n)
  inj-st t P S n =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ ++⁺ (fill-st _ (size S ℕ.∸ suc (size P))) (++⁺ (put-st P n (suc n) 1) (tt ∷ᴬ []ᴬ))

  call-st : ∀ i0 E lk ls cl k ev pr → SlotStable i0 → AllSlotStable (cata-call-from i0 E lk ls cl k ev pr)
  call-st i0 E lk ls cl k ev pr s0 =
    s0 ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (put-st E ev pr 0)
        (++⁺ (put-k-st lk ls k pr (size E)) (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ []ᴬ))

  setup-st : ∀ E cl k ev bl → AllSlotStable (cata-call-setup E cl k ev bl)
  setup-st E cl k ev bl = ++⁺ (get-st E 0) (all-stable?-sound _ refl)

  entry-st : ∀ kd E A → AllSlotStable (proj₂ (env-entry kd E A))
  entry-st word E A = []ᴬ
  entry-st flat E A =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (get-st A 1)
        (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ ++⁺ (put-st E 1 3 0) (++⁺ (put-st A 2 3 (size E)) (tt ∷ᴬ tt ∷ᴬ []ᴬ)))

  visit-walk-stable : ∀ td tv tb F s lb → AllSlotStable (visit-walk td tv tb F s lb)
  visit-walk-stable td tv tb (K _)   s lb = []ᴬ
  visit-walk-stable td tv tb Id      s lb = all-stable?-sound _ refl
  visit-walk-stable td tv tb (F ⊕ G) s lb =
    tt ∷ᴬ ++⁺ (getμ-st G 1)
      (tt ∷ᴬ ++⁺ (visit-walk-stable td tv tb G _ _)
        (tt ∷ᴬ tt ∷ᴬ ++⁺ (getμ-st F 1)
          (tt ∷ᴬ ++⁺ (visit-walk-stable td tv tb F _ _) (tt ∷ᴬ []ᴬ))))
  visit-walk-stable td tv tb (F ⊗ G) s lb =
    tt ∷ᴬ tt ∷ᴬ ++⁺ (getμ-st F 0)
      (tt ∷ᴬ ++⁺ (visit-walk-stable td tv tb F _ _)
        (tt ∷ᴬ ++⁺ (getμ-st G (lsz F 1)) (tt ∷ᴬ visit-walk-stable td tv tb G _ _)))

  rebuild-walk-stable : ∀ vs tv tb (ck : Kind) (cs : ℕ) F s lb → AllSlotStable (rebuild-walk vs tv tb ck cs F s lb)
  rebuild-walk-stable vs tv tb ck cs (K _)   s lb = all-stable?-sound _ refl
  rebuild-walk-stable vs tv tb ck cs Id      s lb = all-stable?-sound _ refl
  rebuild-walk-stable vs tv tb ck cs (F ⊕ G) s lb =
    tt ∷ᴬ ++⁺ (getμ-st G 1)
      (tt ∷ᴬ ++⁺ (rebuild-walk-stable vs tv tb ck cs G _ _)
        (++⁺ (wrap-st 1 (lkind G ck) (lsz G cs) (lsz (F ⊕ G) cs) s)
          (tt ∷ᴬ tt ∷ᴬ ++⁺ (getμ-st F 1)
            (tt ∷ᴬ ++⁺ (rebuild-walk-stable vs tv tb ck cs F _ _)
              (++⁺ (wrap-st 0 (lkind F ck) (lsz F cs) (lsz (F ⊕ G) cs) s) (tt ∷ᴬ []ᴬ))))))
  rebuild-walk-stable vs tv tb ck cs (F ⊗ G) s lb =
    tt ∷ᴬ tt ∷ᴬ ++⁺ (getμ-st G (lsz F 1))
      (tt ∷ᴬ ++⁺ (rebuild-walk-stable vs tv tb ck cs G _ _)
        (tt ∷ᴬ tt ∷ᴬ ++⁺ (getμ-st F 0)
          (tt ∷ᴬ ++⁺ (rebuild-walk-stable vs tv tb ck cs F _ _)
            (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
             ++⁺ (put-k-st (lkind F ck) (lsz F cs) (suc s) (s ℕ.+ 3) 0)
                 (++⁺ (put-k-st (lkind G ck) (lsz G cs) (s ℕ.+ 2) (s ℕ.+ 3) (lsz F cs)) (tt ∷ᴬ []ᴬ))))))

  ----------------------------------------------------------------------
  -- The three non-degenerate cata strategy traces. Concrete scaffold
  -- chunks (descend/ascend control, build-layer, push2/pop2/wrap-sum)
  -- discharge via `all-stable?-sound refl`; the spliced algebra trace
  -- `at` uses the hypothesis `sat`; `++⁺` mirrors each concatenation.
  ----------------------------------------------------------------------
  -- D099 / C1: the algebra is a CALLED BODY now, so every strategy's trace is
  -- `cata-body ++ <all concrete>` — and that makes these four witnesses
  -- collapse. The body is the only place `at` appears, so it is the only place
  -- the hypothesis is needed; everything after it settles by the decider.
  --
  -- `instr-call-closure` is slot-stable (the predicate is ⊥ only for
  -- `instr-alloc-stack`/`instr-reclaim-to`), which is the same
  -- reason `ir-stable apply` is `all-stable?-sound refl`.
  cata-body-stable : ∀ b e bb at → AllSlotStable at
                   → AllSlotStable (cata-body b e bb at)
  cata-body-stable b e bb at sat = tt ∷ᴬ tt ∷ᴬ ++⁺ sat (tt ∷ᴬ tt ∷ᴬ []ᴬ)

  cata-trace-const-stable : ∀ E G bb n1 l1 at → AllSlotStable at
                          → AllSlotStable (proj₂ (proj₂ (cata-trace-const E G bb n1 l1 at)))
  cata-trace-const-stable E G bb n1 l1 at sat =
    ++⁺ (setup-st E n1 (n1 ℕ.+ 1) (n1 ℕ.+ 2) l1)
        (++⁺ (call-st mov-to-output E (lkind G word) (lsz G 1) n1 (n1 ℕ.+ 1) (n1 ℕ.+ 2) (n1 ℕ.+ 3) tt)
             (cata-body-stable l1 (l1 ℕ.+ 1) bb at sat))

  cata-trace-box-stable : ∀ E G bb n1 l1 at → AllSlotStable at
                          → AllSlotStable (proj₂ (proj₂ (cata-trace-box E G bb n1 l1 at)))
  cata-trace-box-stable E G bb n1 l1 at sat =
    ++⁺ (setup-st E n1 (n1 ℕ.+ 1) (n1 ℕ.+ 2) l1)
        (++⁺ (call-st (load-at 0) E (lkind G word) (lsz G 1) n1 (n1 ℕ.+ 1) (n1 ℕ.+ 2) (n1 ℕ.+ 3) tt)
             (cata-body-stable l1 (l1 ℕ.+ 1) bb at sat))

  -- Tier 2 is the one exception: its skeleton splices the two COMPILE-TIME
  -- functor walks, which are stuck on `F`, so the tail still needs the boolean
  -- route with those two peels (the algebra's peel is gone — it is in the body).
  cata-trace-branching-stable : ∀ E A F bb n1 l1 at → AllSlotStable at
                              → AllSlotStable (proj₂ (proj₂ (cata-trace-branching E A F bb n1 l1 at)))
  -- Nested `++⁺` mirroring the emitter's own nesting, NOT a two-way
  -- prefix/body split: `cata-br-I₁` contains the functor walks, which are stuck
  -- on `F`, so the concrete blocks around them do not reduce and the
  -- association is not definitional (nat/linear get away with the flat split
  -- precisely because every block there IS concrete).
  cata-trace-branching-stable E A F bb n1 l1 at sat =
    ++⁺ (setup-st E cl (cl ℕ.+ 1) (cl ℕ.+ 2) bodyL)
        (++⁺ I₁-st
             (++⁺ (call-st mov-to-output E (lkind F (kind A)) (lsz F (size A)) cl (cl ℕ.+ 1) (cl ℕ.+ 2) (cl ℕ.+ 3) tt)
                  (++⁺ (all-stable?-sound (cata-br-I₂ n1 l1) refl)
                       (cata-body-stable bodyL (bodyL ℕ.+ 1) bb at sat))))
    where
      bodyL = l1 ℕ.+ 4 ℕ.+ lsize F ℕ.+ lsize F
      cl    = n1 ℕ.+ 7 ℕ.+ (4 ℕ.* fsize F) ℕ.+ 4
      -- the init, flatten and fold rows are concrete; the two walks are stuck on `F`
      I₁-st : AllSlotStable (cata-br-I₁ (kind A) (size A) F n1 l1)
      I₁-st =
        tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
        ++⁺ (all-stable?-sound (push2 n1 (n1 ℕ.+ 4) (n1 ℕ.+ 5)) refl)
            (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
             ++⁺ (all-stable?-sound (push2 (suc n1) (n1 ℕ.+ 4) (n1 ℕ.+ 5)) refl)
                 (tt ∷ᴬ tt ∷ᴬ
                  ++⁺ (visit-walk-stable n1 (n1 ℕ.+ 4) (n1 ℕ.+ 5) F (n1 ℕ.+ 7) (l1 ℕ.+ 4))
                      (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
                       ++⁺ (rebuild-walk-stable (n1 ℕ.+ 2) (n1 ℕ.+ 4) (n1 ℕ.+ 5) (kind A) (size A) F (n1 ℕ.+ 7)
                                                (l1 ℕ.+ 4 ℕ.+ lsize F))
                           (tt ∷ᴬ []ᴬ))))

  -- D366: `In`'s three shapes and `out-μ`'s.
  in-stable : ∀ (r : MuRep) kd L (n : ℕ) → AllSlotStable (in-trace r kd L n)
  in-stable mu-box  kd L n = all-stable?-sound _ refl
  in-stable mu-unit kd L n = all-stable?-sound _ refl
  in-stable mu-ptr  word L n = all-stable?-sound _ refl
  in-stable mu-ptr  flat L n = tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ ++⁺ (put-st L n (suc n) 0) (tt ∷ᴬ []ᴬ)

  out-stable : ∀ (r : MuRep) → AllSlotStable (out-trace r)
  out-stable mu-box  = all-stable?-sound _ refl
  out-stable mu-unit = all-stable?-sound _ refl
  out-stable mu-ptr  = all-stable?-sound _ refl

  cata-dispatch-slot-stable : ∀ (E A : IRTy) (G : Fun 0) (strat : CataStrategy) (bb n l : ℕ) (at : AbstractTrace)
                            → AllSlotStable at
                            → AllSlotStable (proj₂ (proj₂ (cata-dispatch E A G strat bb n l at)))
  cata-dispatch-slot-stable E A G strat-const         bb n l at sat = cata-trace-const-stable E G bb n l at sat
  cata-dispatch-slot-stable E A G strat-box           bb n l at sat = cata-trace-box-stable E G bb n l at sat
  cata-dispatch-slot-stable E A G (strat-branching F) bb n l at sat = cata-trace-branching-stable E A F bb n l at sat

  ----------------------------------------------------------------------
  -- The theorem: every trace `ir-to-trace` emits is slot-stable.
  -- Concrete-trace constructors discharge uniformly via `all-stable?-sound
  -- refl`; the four sub-trace-carrying constructors (∘ / pair / case /
  -- Cata) recurse + `++⁺` / `All→AllI` / `cata-dispatch-slot-stable`.
  ----------------------------------------------------------------------
  -- Plan 0.108: a SigOp is one call, or a comparison's straight-line
  -- lowering; the decider settles either once the choice is known.
  sigop-stable : ∀ {A B} (si : SigOpInfo A B) (m : Maybe (CmpAt A)) (n l : ℕ)
               → AllSlotStable (sigop-code si n m)
  sigop-stable si nothing  n l = all-stable?-sound _ refl
  sigop-stable si (just c) n l = all-stable?-sound _ refl

  -- D399: a kept value's copy, then the two-cell build
  wc-st : ∀ kd E n c → AllSlotStable (with-copy kd E n (λ m → two-cell m c))
  wc-st word E n c = tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ []ᴬ
  wc-st flat E n c = ++⁺ (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ ++⁺ (put-st E n (suc n) 0) (tt ∷ᴬ []ᴬ)) (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ []ᴬ)

  ir-stable : ∀ {A B} (ir : IR A B) (n l : ℕ) → AllSlotStable (trc (ir-to-trace' n l ir))
  ir-stable id              n l = all-stable?-sound _ refl
  ir-stable (fst {A} {B})   n l = get-st A 0
  ir-stable (snd {A} {B})   n l = get-st B (size A)
  ir-stable terminal        n l = all-stable?-sound _ refl
  ir-stable initial         n l = all-stable?-sound _ refl
  ir-stable (apply {A} {B}) n l =
    ++⁺ (get-st A 1)
        (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
         ++⁺ (put-st A n (suc (suc n)) 1) (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ []ᴬ))
  -- D159: the body is a NAMED BLOCK now, so the entry block is closed
  -- straight-line code and the decider settles it — the recursion into the
  -- body moved to `ir-blocks-stable`, where the body actually lives.
  ir-stable (curry {E} b)  n l = wc-st (kind E) E n _
  ir-stable (SigOp si)      n l = sigop-stable si (cmp-of (sem si)) n l
  ir-stable (Call _)       n l = all-stable?-sound _ refl
  ir-stable (const fits-int _)   n l = all-stable?-sound _ refl
  ir-stable (const fits-float _) n l = all-stable?-sound _ refl
  ir-stable (inl {A} {B})   n l = inj-st 0 A (A +ᵀ B) n
  ir-stable (inr {A} {B})   n l = inj-st 1 B (A +ᵀ B) n
  ir-stable (In {F} _)      n l = in-stable (mu-rep F) _ _ n
  ir-stable (out-μ {F} _)   n l = out-stable (mu-rep F)
  ir-stable (Out _)         n l = all-stable?-sound _ refl
  ir-stable (in-ν {F} _)      n l = wc-st (kind (⟦ F ⟧TI (ν-type F))) _ n _
  ir-stable (Ana {F} _ {E} {A} c)       n l = wc-st flat (Once.IRTy._*_ E A) n _
  -- the loop: a straight-line prefix and suffix around the round.
  ir-stable (Iter {E} {A} {B} b) n l =
    ++⁺ (get-st E 0)
        (tt ∷ᴬ tt ∷ᴬ
         ++⁺ (ir-stable b _ _)
             (tt ∷ᴬ tt ∷ᴬ
              ++⁺ (get-st A 1)
                  (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
                   ++⁺ (put-st E (suc n) (suc (suc (suc n))) 0)
                       (++⁺ (put-st A (suc (suc n)) (suc (suc (suc n))) (size E))
                            (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ get-st B 1)))))
  ir-stable (g ∘ f)         n l = ++⁺ (ir-stable f n l) (tt ∷ᴬ ir-stable g _ _)
  -- Stage G: one clause, the heap shape. (The stack-shape clause that stood
  -- here collapsed onto the same LHS when the mode was dropped, and shadowed
  -- this one.)
  ir-stable (⟨_,_⟩ {A} {B} {C} f g) n l =
    tt ∷ᴬ tt ∷ᴬ ++⁺ (ir-stable f _ _)
      (tt ∷ᴬ tt ∷ᴬ ++⁺ (ir-stable g _ _)
        (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
         ++⁺ (put-st B (suc n) (suc (suc (suc n))) 0)
             (++⁺ (put-st C (suc (suc n)) (suc (suc (suc n))) (size B)) (tt ∷ᴬ []ᴬ))))
  -- item 6: case is FLAT CONTROL — plain splices.
  ir-stable (case {A} {B} f g) n l =
    tt ∷ᴬ ++⁺ (get-st B 1)
      (tt ∷ᴬ ++⁺ (ir-stable g _ _)
        (tt ∷ᴬ tt ∷ᴬ ++⁺ (get-st A 1)
          (tt ∷ᴬ ++⁺ (ir-stable f n (suc (suc l))) (tt ∷ᴬ []ᴬ))))
  -- C1: the algebra is generated at frontier 0 (its own frame).
  ir-stable (Cata {F} _ {E} {A} alg) n l =
    cata-dispatch-slot-stable E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F) _ _ _ _ (ir-stable alg 0 l)

  ----------------------------------------------------------------------
  -- D159: …and the BLOCKS. `AllSlotStable` is a plain `All`, so `link`
  -- preservation is `++⁺` — no index to thread, unlike `SegOK`.
  ----------------------------------------------------------------------
  bds : ℕ × ℕ × AbstractTrace × List (LabelId × ℕ × AbstractTrace)
      → List (LabelId × ℕ × AbstractTrace)
  bds (_ , _ , _ , bs) = bs

  BlockStable : LabelId × ℕ × AbstractTrace → Set
  BlockStable (_ , _ , t) = AllSlotStable t

  blocks-stable : ∀ (bs : List (LabelId × ℕ × AbstractTrace))
                → All BlockStable bs → AllSlotStable (blocks-layout bs)
  blocks-stable []                   []ᴬ       = []ᴬ
  blocks-stable ((lb , bb , t) ∷ bs) (q ∷ᴬ qs) =
    ++⁺ (tt ∷ᴬ ++⁺ q (tt ∷ᴬ []ᴬ)) (blocks-stable bs qs)

  -- D199: the re-suspension pass emits only slot-stable instructions —
  -- register moves, indirect loads/stores, a heap allocation and flat control,
  -- none of which touch `next-slot`. It cannot go through `all-stable?-sound`
  -- like `in-ν`'s literal stub does: the trace is not concrete, it is generated
  -- from the functor witness, so the induction mirrors `resuspend-layer`'s own.
  resuspend-stable : ∀ (H : IRFunctor) (E A : IRTy) (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
                   → AllSlotStable (proj₂ (proj₂ (resuspend-layer H E A n l lbl env wf)))
  resuspend-stable H E A n l lbl env (wf-K _) = []ᴬ
  resuspend-stable H E A n l lbl env wf-Id =
    tt ∷ᴬ tt ∷ᴬ
    ++⁺ (get-st E 0)
        (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
         ++⁺ (put-st E (suc n) (suc (suc n)) 0)
             (++⁺ (put-st A n (suc (suc n)) (size E))
                  (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ []ᴬ)))
  resuspend-stable H E A n l lbl env (wf-Prod {F} {G} wfF wfG) =
    tt ∷ᴬ tt ∷ᴬ
    ++⁺ (get-st (⟦ F ⟧TI A) 0)
        (++⁺ (resuspend-stable H E A (suc (suc (suc (suc n)))) l lbl env wfF)
             (tt ∷ᴬ tt ∷ᴬ
              ++⁺ (get-st (⟦ G ⟧TI A) (size (⟦ F ⟧TI A)))
                  (++⁺ (resuspend-stable H E A n2 l2 lbl env wfG)
                       (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
                        ++⁺ (put-st (⟦ F ⟧TI (ν-type H)) (suc (suc n)) (suc n) 0)
                            (++⁺ (put-st (⟦ G ⟧TI (ν-type H)) (suc (suc (suc n))) (suc n) (size (⟦ F ⟧TI (ν-type H))))
                                 (tt ∷ᴬ []ᴬ))))))
    where
      n2 = proj₁ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF)
      l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF))
  -- each arm reads the payload at word 1, transforms it, and builds a fresh node
  resuspend-stable H E A n l lbl env (wf-Sum {F} {G} wfF wfG) =
    tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
    ++⁺ (tt ∷ᴬ ++⁺ (get-st (⟦ G ⟧TI A) 1)
                   (++⁺ (resuspend-stable H E A n2 l2 lbl env wfG)
                        (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
                         ++⁺ (fill-st _ (c-of G)) (++⁺ (put-st (⟦ G ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1) (tt ∷ᴬ []ᴬ)))))
        (tt ∷ᴬ tt ∷ᴬ
         ++⁺ (tt ∷ᴬ ++⁺ (get-st (⟦ F ⟧TI A) 1)
                        (++⁺ (resuspend-stable H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
                             (tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ tt ∷ᴬ
                              ++⁺ (fill-st _ (c-of F)) (++⁺ (put-st (⟦ F ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1) (tt ∷ᴬ []ᴬ)))))
             (tt ∷ᴬ []ᴬ))
    where
      n2 = proj₁ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
      l2 = proj₁ (proj₂ (resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF))
      c-of : IRFunctor → ℕ
      c-of P = size (⟦ F ⟧TI (ν-type H) +ᵀ ⟦ G ⟧TI (ν-type H)) ℕ.∸ suc (size (⟦ P ⟧TI (ν-type H)))

  ir-blocks-stable : ∀ {A B} (ir : IR A B) (n l : ℕ)
                   → All BlockStable (bds (ir-to-trace' n l ir))
  ir-blocks-stable id                   n l = []ᴬ
  ir-blocks-stable fst                  n l = []ᴬ
  ir-blocks-stable snd                  n l = []ᴬ
  ir-blocks-stable terminal             n l = []ᴬ
  ir-blocks-stable initial              n l = []ᴬ
  ir-blocks-stable apply                n l = []ᴬ
  ir-blocks-stable (curry {E} {A} b) n l =
    ++⁺ (entry-st (kind E) E A) (ir-stable b _ (suc (suc l)))
    ∷ᴬ ir-blocks-stable b _ (suc (suc l))
  ir-blocks-stable (SigOp _)            n l = []ᴬ
  ir-blocks-stable (Call _)            n l = []ᴬ
  ir-blocks-stable (const fits-int _)   n l = []ᴬ
  ir-blocks-stable (const fits-float _) n l = []ᴬ
  ir-blocks-stable inl                  n l = []ᴬ
  ir-blocks-stable inr                  n l = []ᴬ
  ir-blocks-stable (In _)             n l = []ᴬ
  ir-blocks-stable (out-μ _)            n l = []ᴬ
  ir-blocks-stable (Out _)              n l = []ᴬ
  ir-blocks-stable (in-ν _)           n l = all-stable?-sound _ refl ∷ᴬ []ᴬ
  -- D199: the block is `coalg ++ re-suspension`, so its stability is theirs.
  ir-blocks-stable (Ana {F} wf {E} {A} c) n l =
    (tt ∷ᴬ tt ∷ᴬ
     ++⁺ (ir-stable c 1 (suc l))
         (resuspend-stable F E A (proj₁ (ir-to-trace' 1 (suc l) c))
                           (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c))) (ℓ o l) 0 wf))
      ∷ᴬ ir-blocks-stable c 1 (suc l)
  ir-blocks-stable (g ∘ f)              n l = ++⁺ (ir-blocks-stable f n l)
                                                  (ir-blocks-stable g _ _)
  ir-blocks-stable ⟨ f , g ⟩            n l = ++⁺ (ir-blocks-stable f _ l)
                                                  (ir-blocks-stable g _ _)
  ir-blocks-stable (case f g)           n l = ++⁺ (ir-blocks-stable f n (suc (suc l)))
                                                  (ir-blocks-stable g _ _)
  ir-blocks-stable (Cata {F} _ alg)     n l = ir-blocks-stable alg 0 l
  ir-blocks-stable (Iter b)             n l = ir-blocks-stable b _ _

  -- top-level: the LINKED program — entry, its terminator, then the blocks.
  ir-to-trace-slot-stable : ∀ {A B} (ir : IR A B) → AllSlotStable (ir-to-trace ir)
  ir-to-trace-slot-stable ir =
    ++⁺ (ir-stable ir 0 0)
        (tt ∷ᴬ blocks-stable _ (ir-blocks-stable ir 0 0))

  -- D244/D245: …and a program's unit placed at label counter `l`.
  ir-to-trace-lab-slot-stable : ∀ {A B} (ir : IR A B) (l : ℕ) → AllSlotStable (ir-to-trace-lab l ir)
  ir-to-trace-lab-slot-stable ir l =
    ++⁺ (ir-stable ir 0 l)
        (tt ∷ᴬ blocks-stable _ (ir-blocks-stable ir 0 l))

  -- …and the OUTERMOST unit, linked with the program's leave (D320).
  ir-to-trace-top-slot-stable : ∀ {A B} (ir : IR A B) → AllSlotStable (link-top (ir-to-unit ir))
  ir-to-trace-top-slot-stable ir =
    ++⁺ (ir-stable ir 0 0)
        (tt ∷ᴬ blocks-stable _ (ir-blocks-stable ir 0 0))
