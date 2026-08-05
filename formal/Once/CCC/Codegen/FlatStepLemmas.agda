-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Codegen.FlatStepLemmas — opaque-state step API for the flat
-- abstract machine `exec-flat` (Plan 0.36, task #8 foundation).
--
-- This is the `exec-flat` analogue of the X86-64 `StepLemmas` API that
-- the deleted `CataIsEvenInduction` POC used to prove the cata loop↔fold
-- ∀-n. The technique (per the prior POCs + `feedback_fuel_cpu_induction
-- _technique`): reason over OPAQUE states, peel a FIXED number of steps
-- off SYMBOLIC fuel via a chain combinator, then μ-induct on the input.
--
-- The peel primitive already exists: `FlatMachine.exec-flat-step` (the
-- `exec-1` analogue). Here we add `FlatSteps`/`exec-flat-steps` — the
-- chain combinator (mirrors `StepLemmas.Steps`/`exec-steps`) — over
-- which the descend/base/ascend phases of the cata loop are reasoned
-- once each (not unrolled per input). `flat-exec-instr` is itself the
-- abstract per-instruction semantics, so each step's "next state" is
-- forced (no free `s'`, unlike the real-CPU `step-not-halted ≡ just s'`).
------------------------------------------------------------------------

module Once.CCC.Codegen.FlatStepLemmas where

open import Once.CCC.Label using (LabelId; ≢⇒≡ᵇᴵfalse; _≡ᵇᴵ_)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (halted; regs; readReg; Scratch; AbstractInstr; AbstractTrace;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero)
open import Once.CCC.Machine.Flat using (module FlatMachine)

-- `m ≢ n` ⇒ the boolean `m ≡ᵇ n` is `false` (induction on m,n, matching `≡ᵇ`).
≢⇒≡ᵇfalse : ∀ (m n : ℕ) → ¬ (m ≡ n) → (m ≡ᵇ n) ≡ false
≢⇒≡ᵇfalse zero    zero    ne = ⊥-elim (ne refl)
≢⇒≡ᵇfalse zero    (suc n) ne = refl
≢⇒≡ᵇfalse (suc m) zero    ne = refl
≢⇒≡ᵇfalse (suc m) (suc n) ne = ≢⇒≡ᵇfalse m n (λ eq → ne (cong suc eq))

module FlatStepsAPI {FS : FrameSemantics} where
  open FlatMachine {FS}

  -- A chain of `k` non-halted `exec-flat` steps from `fs` to `fs'`. Each
  -- link carries its halted+fetch evidence; the next state is forced by
  -- `flat-exec-instr i prog fs` (opaque — never destructured).
  data FlatSteps (prog : AbstractTrace) : ℕ → FlatState → FlatState → Set where
    []  : ∀ {fs} → FlatSteps prog 0 fs fs
    _∷_ : ∀ {fs k fs'} {i : AbstractInstr}
        → (halted (floc fs) ≡ false × fetch prog (fpc fs) ≡ just i)
        → FlatSteps prog k (flat-exec-instr i prog fs) fs'
        → FlatSteps prog (suc k) fs fs'

  infixr 5 _∷_

  -- Peel a whole chain off the fuel (mirrors `StepLemmas.exec-steps`):
  -- a `k`-step chain reduces `exec-flat (k + b)` from `fs` to
  -- `exec-flat b` from `fs'`.
  exec-flat-steps : ∀ {prog k fs fs'} → FlatSteps prog k fs fs'
                  → ∀ b → exec-flat (k + b) prog fs ≡ exec-flat b prog fs'
  exec-flat-steps []                           b = refl
  exec-flat-steps (_∷_ {k = k} {i = i} (h , f) rest) b =
    trans (exec-flat-step (k + b) _ _ i h f) (exec-flat-steps rest b)

  -- A single step whose RESULT state is named via a step-lemma equation,
  -- rather than left as the (possibly stuck) `flat-exec-instr i prog fs`.
  -- This is the abstraction that makes a BRANCH step first-class: its
  -- result `flat-exec-instr (c-branch…) prog fs` reduces to a stuck
  -- `do-branch …`, but the control-flow lemmas (`flat-scratch-branch-not`
  -- etc.) prove it equals the clean `record fs { fpc = … }`. `flat-step1`
  -- lets that proof name the chain link's result, so branches compose with
  -- straight steps via `FlatSteps-++` without per-site `rewrite`/`subst`.
  flat-step1 : ∀ {prog fs fs'} {i : AbstractInstr}
             → halted (floc fs) ≡ false
             → fetch prog (fpc fs) ≡ just i
             → flat-exec-instr i prog fs ≡ fs'
             → FlatSteps prog 1 fs fs'
  flat-step1 {prog} {fs} {fs'} h f eq =
    subst (FlatSteps prog 1 fs) eq ((h , f) ∷ [])

  ----------------------------------------------------------------------
  -- Control-flow step-lemmas: name `flat-exec-instr`'s reductions for the
  -- jumps/branches the cata loop uses. The descend/ascend `FlatSteps`
  -- chains compose these (the straight instrs reduce definitionally via
  -- `flat-step-straight`, so they need no lemma). All over OPAQUE `fs`;
  -- the branch condition is read off the (opaque) register/tag.
  ----------------------------------------------------------------------

  -- label: pc passes through.
  flat-label : ∀ (prog : AbstractTrace) (fs : FlatState) (n : LabelId)
             → flat-exec-instr (instr-ctrl (c-label n)) prog fs
                 ≡ record fs { fpc = suc (fpc fs) }
  flat-label prog fs n = refl

  -- unconditional jump: pc ← find-label target.
  flat-jmp : ∀ (prog : AbstractTrace) (fs : FlatState) (n : LabelId)
           → flat-exec-instr (instr-ctrl (c-jmp n)) prog fs
               ≡ do-jump (find-label prog n) fs
  flat-jmp prog fs n = refl

  -- scratch-branch NOT taken (Scratch ≠ 0, the descend-continue path): fall through.
  flat-scratch-branch-not : ∀ (prog : AbstractTrace) (fs : FlatState) (n : LabelId)
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ false
    → flat-exec-instr (instr-ctrl (c-branch-scratch-zero n)) prog fs
        ≡ record fs { fpc = suc (fpc fs) }
  flat-scratch-branch-not prog fs n cond rewrite cond = refl

  -- scratch-branch taken (Scratch = 0, exit): pc ← find-label target.
  flat-scratch-branch-yes : ∀ (prog : AbstractTrace) (fs : FlatState) (n : LabelId)
    → sv-is-zero (readReg (regs (floc fs)) Scratch) ≡ true
    → flat-exec-instr (instr-ctrl (c-branch-scratch-zero n)) prog fs
        ≡ do-jump (find-label prog n) fs
  flat-scratch-branch-yes prog fs n cond rewrite cond = refl

  -- tag-branch NOT taken (tag ≠ 0, the inr/cons path): fall through.
  flat-tag-branch-not : ∀ (prog : AbstractTrace) (fs : FlatState) (n : LabelId)
    → tag-zf (flat-read-tag (floc fs)) ≡ false
    → flat-exec-instr (instr-ctrl (c-branch-tag-zero n)) prog fs
        ≡ record fs { fpc = suc (fpc fs) }
  flat-tag-branch-not prog fs n cond rewrite cond = refl

  -- tag-branch taken (tag = 0, the inl/base path): pc ← find-label target.
  flat-tag-branch-yes : ∀ (prog : AbstractTrace) (fs : FlatState) (n : LabelId)
    → tag-zf (flat-read-tag (floc fs)) ≡ true
    → flat-exec-instr (instr-ctrl (c-branch-tag-zero n)) prog fs
        ≡ do-jump (find-label prog n) fs
  flat-tag-branch-yes prog fs n cond rewrite cond = refl

  ----------------------------------------------------------------------
  -- `fetch` distributes over `++` (the clean half of label/position
  -- reasoning over a concatenated trace — `fetch` indexes the list, it
  -- does NOT inspect instructions, so no AbstractInstr catchall). This
  -- lets the ASCEND phase fetch its instructions relative to the
  -- abstract base offset `length prefix` (prefix = descend+base+`at`,
  -- `at` abstract): `fetch (prefix ++ ascend) (length prefix + j)`
  -- reduces to `fetch ascend j` (concrete). Reusable; mirrors the
  -- intent of the X86 `StepLemmas` fetch reasoning.
  --
  -- (The `find-label` distribution — its dual — DOES hit the catchall,
  -- since `fl-go` inspects `c-label`; that's the ascend-only decision
  -- deferred to the ascend build. The descend phase needs neither: its
  -- labels sit in the concrete prefix, so `find-label`/`fetch` reduce
  -- directly there.)
  ----------------------------------------------------------------------
  fetch-++ : ∀ (xs ys : AbstractTrace) (j : ℕ)
           → fetch (xs ++ ys) (length xs + j) ≡ fetch ys j
  fetch-++ []        ys j = refl
  fetch-++ (i ∷ xs') ys j = fetch-++ xs' ys j

  ----------------------------------------------------------------------
  -- `find-label`-skip: `fl-go` scans PAST a prefix `xs` containing no
  -- matching label, continuing into `ys` with the accumulator advanced
  -- by `length xs`. The refactor pays off here — we case on `label-of?
  -- x`'s 2-valued result, NOT AbstractInstr's ~30 constructors, so the
  -- abstract algebra trace `at` (in the ascend prefix) is handled
  -- uniformly. (Hypothesis: every element's label, if any, differs from
  -- the target — `All`.)
  ----------------------------------------------------------------------
  fl-go-skip : ∀ (xs ys : AbstractTrace) (target : LabelId) (i : ℕ)
             → All (λ x → ¬ (label-of? x ≡ just target)) xs
             → fl-go (xs ++ ys) target i ≡ fl-go ys target (i + length xs)
  fl-go-skip []        ys target i []          =
          cong (fl-go ys target) (sym (+-identityʳ i))
  fl-go-skip (x ∷ xs') ys target i (px ∷ pxs) with label-of? x
  ... | just m  rewrite ≢⇒≡ᵇᴵfalse m target (λ m≡t → px (cong just m≡t)) =
          trans (fl-go-skip xs' ys target (suc i) pxs)
                (cong (fl-go ys target) (sym (+-suc i (length xs'))))
  ... | nothing =
          trans (fl-go-skip xs' ys target (suc i) pxs)
                (cong (fl-go ys target) (sym (+-suc i (length xs'))))

  ----------------------------------------------------------------------
  -- `find-label` RELOCATION foundation (toward embedding `at = ir-to-trace
  -- alg` at an offset inside the cata program). Dual of `fl-go-skip`: where
  -- skip handles labels SCANNED PAST, shift handles a label FOUND within a
  -- segment whose scan started at a shifted index.
  --
  -- `fl-go`'s accumulator is a pure offset: starting the scan at `b + a`
  -- instead of `b` shifts the found position by `a`. No arithmetic lemmas
  -- needed — the recursion uses `suc (b + a) = suc b + a` definitionally
  -- and the match case is `refl` (`b + a` on both sides).
  ----------------------------------------------------------------------
  fl-go-shift : ∀ (xs : AbstractTrace) (target : LabelId) (a b : ℕ)
              → fl-go xs target (b + a) ≡ map (_+ a) (fl-go xs target b)
  flm-shift   : ∀ (cmp : Bool) (xs : AbstractTrace) (target : LabelId) (a b : ℕ)
              → fl-label-match cmp xs target (b + a) ≡ map (_+ a) (fl-label-match cmp xs target b)
  fl-go-shift []       target a b = refl
  fl-go-shift (x ∷ xs) target a b with label-of? x
  ... | just m  = flm-shift (m ≡ᵇᴵ target) xs target a b
  ... | nothing = fl-go-shift xs target a (suc b)
  flm-shift true  xs target a b = refl
  flm-shift false xs target a b = fl-go-shift xs target a (suc b)

  -- A label found in a prefix segment is found at the same index in the
  -- segment extended by any suffix (the scan stops before reaching it).
  -- The dual fact the relocation needs alongside `fl-go-shift`/`fl-go-skip`.
  fl-go-prefix : ∀ (seg post : AbstractTrace) (target : LabelId) (i p : ℕ)
               → fl-go seg target i ≡ just p → fl-go (seg ++ post) target i ≡ just p
  flm-prefix   : ∀ (cmp : Bool) (seg post : AbstractTrace) (target : LabelId) (i p : ℕ)
               → fl-label-match cmp seg target i ≡ just p → fl-label-match cmp (seg ++ post) target i ≡ just p
  fl-go-prefix []        post target i p ()
  fl-go-prefix (x ∷ seg) post target i p h with label-of? x
  ... | just m  = flm-prefix (m ≡ᵇᴵ target) seg post target i p h
  ... | nothing = fl-go-prefix seg post target (suc i) p h
  flm-prefix true  seg post target i p h = h
  flm-prefix false seg post target i p h = fl-go-prefix seg post target (suc i) p h

  -- `find-label` distribution: a label found at relative index `p` in a
  -- segment `seg` embedded after a label-free prefix `pre` (and before any
  -- suffix `post`) resolves to absolute index `p + length pre` in the full
  -- program. This is what relocates `at = ir-to-trace alg`'s internal jump
  -- targets when `at` is embedded in the cata program: skip past `pre`
  -- (`fl-go-skip`), the accumulator becomes the offset (`fl-go-shift`), and
  -- the suffix is unreached (`fl-go-prefix`).
  find-label-distrib : ∀ (pre seg post : AbstractTrace) (target : LabelId) (p : ℕ)
                     → All (λ x → ¬ (label-of? x ≡ just target)) pre
                     → fl-go seg target 0 ≡ just p
                     → find-label (pre ++ seg ++ post) target ≡ just (p + length pre)
  find-label-distrib pre seg post target p pre-no h =
    trans (fl-go-skip pre (seg ++ post) target 0 pre-no)
          (trans (fl-go-shift (seg ++ post) target (length pre) 0)
                 (cong (map (_+ length pre)) (fl-go-prefix seg post target 0 p h)))

  ----------------------------------------------------------------------
  -- Compose two step-chains (so a phase = pre ++ body ++ post reuses
  -- sub-chains like `descend-body-flat`). Induction on the first chain.
  ----------------------------------------------------------------------
  ----------------------------------------------------------------------
  -- REIFY a halting `exec-flat` run as a `FlatSteps` chain (the bridge
  -- from `IRObsCorrectF`'s `exec-flat`/`flat-events` level to the
  -- relocation machinery, which consumes `FlatSteps`). A run that halts
  -- within fuel `n` decomposes into its instruction-steps (a `FlatSteps`
  -- chain to a SETTLED state — halted, or nothing left to fetch) plus the
  -- leftover fuel. `n ≡ steps-len + rest-fuel` lets downstream rewrite the
  -- original fuel as `steps-len + b` to peel the chain off `flat-events`/
  -- `exec-flat`. Settling by fetch-nothing is `at`'s case (a morphism
  -- trace runs off its end); settling by `halted` covers explicit halts.
  ----------------------------------------------------------------------
  record RunReified (prog : AbstractTrace) (fs : FlatState) (n : ℕ) : Set where
    constructor reified
    field
      steps-len  : ℕ
      rest-fuel  : ℕ
      settle     : FlatState
      chain      : FlatSteps prog steps-len fs settle
      settled    : (halted (floc settle) ≡ true) ⊎ (fetch prog (fpc settle) ≡ nothing)
      fuel-split : n ≡ steps-len + rest-fuel

  reify-run : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState)
            → halted (floc (exec-flat n prog fs)) ≡ true
            → RunReified prog fs n
  reify-run zero    prog fs h = reified 0 0 fs [] (inj₁ h) refl
  reify-run (suc n) prog fs h with halted (floc fs) in heq
  ... | true  = reified 0 (suc n) fs [] (inj₁ heq) refl
  ... | false with fetch prog (fpc fs) in feq
  ...   | nothing = reified 0 (suc n) fs [] (inj₂ feq) refl
  ...   | just i  with reify-run n prog (flat-exec-instr i prog fs) h
  ...     | reified N r fs' ch st fsp =
              reified (suc N) r fs' ((heq , feq) ∷ ch) st (cong suc fsp)

  FlatSteps-++ : ∀ {prog k₁ k₂ fs₁ fs₂ fs₃}
               → FlatSteps prog k₁ fs₁ fs₂ → FlatSteps prog k₂ fs₂ fs₃
               → FlatSteps prog (k₁ + k₂) fs₁ fs₃
  FlatSteps-++ []       ys = ys
  FlatSteps-++ (x ∷ xs) ys = x ∷ FlatSteps-++ xs ys

  ----------------------------------------------------------------------
  -- Chain a UNIFORM FAMILY of `k`-step blocks indexed by depth: given a
  -- block from state `st d` to `st (suc d)` at every `d`, compose `n` of
  -- them into one `k*n`-step chain from `st 0` to `st n`. Induction on `n`.
  -- This is the inductive backbone of the cata descend/ascend loops: the
  -- per-depth block is `descend-iter-flat` (resp. an ascend iteration)
  -- applied with depth `d`'s heap facts, and `st` is the loop-head state at
  -- each depth. The heap model supplies `st`/the family; `chain-steps` is
  -- where the combinators compose over the recursion.
  ----------------------------------------------------------------------
  chain-steps : ∀ {prog : AbstractTrace} (k n : ℕ) (st : ℕ → FlatState)
              → (∀ d → FlatSteps prog k (st d) (st (suc d)))
              → FlatSteps prog (n * k) (st 0) (st n)
  chain-steps k zero    st f = []
  chain-steps k (suc m) st f =
    FlatSteps-++ (f 0) (chain-steps k m (λ d → st (suc d)) (λ d → f (suc d)))

  -- `chain-steps` at depth 0 is the empty chain. `refl` HERE (inside
  -- `FlatStepsAPI`, where `chain-steps` reduces); exported so downstream
  -- callers under `open FlatStepsAPI` can rewrite the depth-0 chain to `[]`.
  chain-steps-nil : ∀ {prog : AbstractTrace} (k : ℕ) (st : ℕ → FlatState)
                      (f : ∀ d → FlatSteps prog k (st d) (st (suc d)))
                  → chain-steps k zero st f ≡ []
  chain-steps-nil k st f = refl
