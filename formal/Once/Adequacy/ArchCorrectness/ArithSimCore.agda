-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimCore  (Plan 0.54 rung B / B2.3)
--
-- The ARCH-GENERIC arith concrete↔abstract simulation — R/R-scratch/R-input,
-- all per-instruction R-step cases, the block composition (R-sim/Rf-sim), the
-- Rf assembly, the endpoints (result-correct/R-init), and the
-- `arith-block-correct` capstone, written ONCE.
--
-- CLOBBER-AGNOSTIC design (rule of three, x86-64 + riscv64): the proof only
-- ever needs two facts per instruction, and both are arch-neutral —
--   * `rt-<i>` (READ-TARGET): after `i`, reading its arith target back yields
--     the value (in op-form over the pre-state register reads);
--   * `rf-other` (READ-FRAME, one generic param): after ANY `i`, reading a
--     NON-target arith register is unchanged.
-- The core makes NO assumption about the concrete write shape (how many io
-- registers `i` clobbers, or which). Each arch DISCHARGES `rt`/`rf-other` from
-- its own frame lemmas: x86-64 peels its rax/rdx idiv clobbers; riscv64's native
-- div/rem clobber nothing, so it discharges them directly. That difference —
-- which broke a writeReg-shape parameterisation — lives entirely in the arch
-- instances, not here.
--
-- What is ARCH-NEUTRAL and imported directly: the WHOLE abstract side
-- (`exec-xinstr`/`exec-xprog`/`xreg-idx`, the store, `bin-op`/`un-op`,
-- `block-value-semM`, `block-semM`/`toWord`, the Word64 ops).
--
-- What is a PARAMETER: the concrete machine (`St`, `rr`=read-register,
-- `mem`, `arith-reg`, `out-reg`, `def`, `sa`=scratch-addr, `pl`=path-load),
-- the opaque step/block-fold (`e1`/`eb`) with their `eb-nil`/`eb-cons`
-- reductions, and the read-back facts (`rt-*` + `rf-other`).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimCore where

open import Data.Nat using (ℕ; _≟_)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Empty using (⊥; ⊥-elim)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch; mk-scratch)
open XI using (XR0; XR1)
open import Once.Arith.Machine.Shape using (InputShape; ⟦_⟧S; InputPath; project)
open import Once.Arith.Machine.AbsState
  using (ArithAbsState; Store; _[_]; _[_↦_]; init; store-write-same; store-write-other; output-of)
open import Once.Arith.Machine.AbsInstr using (bin-op; un-op; maybe-zero; move-to-out)
import Once.Arith.Backend.Correct as Correct
open Correct 64 using (exec-xinstr; exec-xprog; exec-xprog-++; xreg-idx)
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Backend.XInstr.CodeGen using (_≟x_; emit; emit-program)
open import Once.Arith.Machine.Compile using (compile-abs; compile-go)
open import Once.Arith.SigOp.Block using (block-semM)
open import Once.Arith.SigOp.BlockSemBridge using (toWord)
open import Once.Arith.Backend.BlockValueSemM using (block-value-semM)

import Once.Word as OnceWord
open OnceWord.Word64 using (_⊕_; _⊖_; _⊗_; _/ˢ_; _%ˢ_; ⊝_; shlᵂ; sdiv2ᵏ; fromℤ)

------------------------------------------------------------------------
-- `tgt` — each XInstr's primary arith target (arch-neutral). `nothing` for
-- the instructions that write no arith register (spill, mov-out). Drives the
-- generic frame `rf-other`.
------------------------------------------------------------------------

tgt : XInstr → Maybe XReg
tgt (XI.Xmov-imm d _)         = just d
tgt (XI.Xmov-rr d _)          = just d
tgt (XI.Xmov-m-r d _)         = just d
tgt (XI.Xmov-arg d _)         = just d
tgt (XI.Xadd-rr d _)          = just d
tgt (XI.Xsub-rr d _)          = just d
tgt (XI.Ximul-rr d _)         = just d
tgt (XI.Xneg-r d)             = just d
tgt (XI.Xshl-rri d _ _)       = just d
tgt (XI.Xdiv-rrr d _ _)       = just d
tgt (XI.Xrem-rrr d _ _)       = just d
tgt (XI.Xdiv-safe-rrr d _ _)  = just d
tgt (XI.Xrem-safe-rrr d _ _)  = just d
tgt (XI.Xsdiv-pow2-rri d _ _) = just d
tgt (XI.Xmov-r-m _ _)         = nothing
tgt (XI.Xmov-out _)           = nothing

------------------------------------------------------------------------
-- Block structure (arch-neutral). The compiled arith block ENDS with
-- `Xmov-out XR0`: `compile-abs e = compile-go 0 e ++ [move-to-out 0]`, and
-- `emit (move-to-out 0) = [Xmov-out XR0]` (abs-reg 0 = just XR0). Used to
-- discharge `output-extract` (the block's result is the final Xmov-out).
------------------------------------------------------------------------

emit-program-++ : ∀ (xs ys : List _) → emit-program (xs ++ ys) ≡ emit-program xs ++ emit-program ys
emit-program-++ []       ys = refl
emit-program-++ (i ∷ is) ys =
  trans (cong (emit i ++_) (emit-program-++ is ys))
        (sym (++-assoc (emit i) (emit-program is) (emit-program ys)))

block-shape : ∀ {sh} (e : MArithIR sh)
            → emit-program (compile-abs e) ≡ emit-program (compile-go 0 e) ++ (XI.Xmov-out XR0 ∷ [])
block-shape e = emit-program-++ (compile-go 0 e) (move-to-out 0 ∷ [])

------------------------------------------------------------------------
-- Spill is the ONLY instruction that writes the abstract scratch store (and,
-- concretely, memory). `NonSpill` marks the other 15; `scratch-unchanged` is
-- their (arch-neutral) abstract-scratch invariance, feeding `scratch-frame`.
------------------------------------------------------------------------

NonSpill : XInstr → Set
NonSpill (XI.Xmov-r-m _ _) = ⊥
NonSpill _                 = ⊤

scratch-unchanged : ∀ i → NonSpill i → ∀ {sh} (s : ArithAbsState sh)
                  → ArithAbsState.scratch (exec-xinstr i s) ≡ ArithAbsState.scratch s
scratch-unchanged (XI.Xmov-imm _ _)         _ s = refl
scratch-unchanged (XI.Xmov-rr _ _)          _ s = refl
scratch-unchanged (XI.Xmov-m-r _ _)         _ s = refl
scratch-unchanged (XI.Xmov-arg _ _)         _ s = refl
scratch-unchanged (XI.Xadd-rr _ _)          _ s = refl
scratch-unchanged (XI.Xsub-rr _ _)          _ s = refl
scratch-unchanged (XI.Ximul-rr _ _)         _ s = refl
scratch-unchanged (XI.Xneg-r _)             _ s = refl
scratch-unchanged (XI.Xshl-rri _ _ _)       _ s = refl
scratch-unchanged (XI.Xdiv-rrr _ _ _)       _ s = refl
scratch-unchanged (XI.Xrem-rrr _ _ _)       _ s = refl
scratch-unchanged (XI.Xdiv-safe-rrr _ _ _)  _ s = refl
scratch-unchanged (XI.Xrem-safe-rrr _ _ _)  _ s = refl
scratch-unchanged (XI.Xsdiv-pow2-rri _ _ _) _ s = refl
scratch-unchanged (XI.Xmov-out _)           _ s = refl

module Core
  (St Reg  : Set)
  (rr       : St → Reg → ℕ)                    -- read a register (= readReg ∘ regs)
  (mem      : St → ℕ → Maybe ℕ)                -- read memory (= readMem ∘ memory)
  (arith-reg : XReg → Reg)
  (out-reg  : Reg)                             -- where Xmov-out writes (rax / a0)
  (def      : Maybe ℕ → ℕ)
  (def-just : ∀ w → def (just w) ≡ w)
  (sa       : St → XScratch → ℕ)               -- scratch-addr
  (pl       : St → InputPath → ℕ)              -- path-load
  (e1       : XInstr → St → St)                -- concrete step (opaque)
  (eb       : List XInstr → St → St)           -- concrete block fold (opaque)
  (eb-nil   : ∀ s → eb [] s ≡ s)
  (eb-cons  : ∀ i is s → eb (i ∷ is) s ≡ eb is (e1 i s))
  -- MEMORY-EFFECT primitives (drive scratch-frame). Only spill writes memory;
  -- the scratch address is step-invariant (sp is never written), and injective
  -- in the slot (riscv `sp+8·slot` unconditionally; x86-64 needs its frontier).
  (sa-inv       : ∀ i s sc → sa (e1 i s) sc ≡ sa s sc)
  (sa-inj       : ∀ s sc sc' → ¬ (XScratch.slot sc ≡ XScratch.slot sc') → ¬ (sa s sc ≡ sa s sc'))
  (mem-keep     : ∀ i s addr → NonSpill i → mem (e1 i s) addr ≡ mem s addr)
  (mem-spill-hit  : ∀ sc' src s → mem (e1 (XI.Xmov-r-m sc' src) s) (sa s sc') ≡ just (rr s (arith-reg src)))
  (mem-spill-miss : ∀ sc' src s addr → ¬ (addr ≡ sa s sc') → mem (e1 (XI.Xmov-r-m sc' src) s) addr ≡ mem s addr)
  -- READ-FRAME: reading a non-target arith register is unchanged by `i`.
  (rf-other : ∀ i s x → (∀ d → tgt i ≡ just d → ¬ (x ≡ d))
            → rr (e1 i s) (arith-reg x) ≡ rr s (arith-reg x))
  -- READ-TARGET: reading `i`'s arith target back yields its value (op-form).
  (rt-mov-imm : ∀ d z s   → rr (e1 (XI.Xmov-imm d z) s)   (arith-reg d) ≡ fromℤ z)
  (rt-mov-rr  : ∀ d src s  → rr (e1 (XI.Xmov-rr d src) s)  (arith-reg d) ≡ rr s (arith-reg src))
  (rt-reload  : ∀ d sc s   → rr (e1 (XI.Xmov-m-r d sc) s)  (arith-reg d) ≡ def (mem s (sa s sc)))
  (rt-arg     : ∀ d p s    → rr (e1 (XI.Xmov-arg d p) s)   (arith-reg d) ≡ pl s p)
  (rt-add     : ∀ d src s  → rr (e1 (XI.Xadd-rr d src) s)  (arith-reg d) ≡ rr s (arith-reg d) ⊕ rr s (arith-reg src))
  (rt-sub     : ∀ d src s  → rr (e1 (XI.Xsub-rr d src) s)  (arith-reg d) ≡ rr s (arith-reg d) ⊖ rr s (arith-reg src))
  (rt-imul    : ∀ d src s  → rr (e1 (XI.Ximul-rr d src) s) (arith-reg d) ≡ rr s (arith-reg d) ⊗ rr s (arith-reg src))
  (rt-neg     : ∀ d s      → rr (e1 (XI.Xneg-r d) s)       (arith-reg d) ≡ ⊝ rr s (arith-reg d))
  (rt-shl     : ∀ d src imm s → rr (e1 (XI.Xshl-rri d src imm) s) (arith-reg d) ≡ shlᵂ (rr s (arith-reg src)) imm)
  (rt-div     : ∀ d a b s  → rr (e1 (XI.Xdiv-rrr d a b) s)      (arith-reg d) ≡ rr s (arith-reg a) /ˢ rr s (arith-reg b))
  (rt-rem     : ∀ d a b s  → rr (e1 (XI.Xrem-rrr d a b) s)      (arith-reg d) ≡ rr s (arith-reg a) %ˢ rr s (arith-reg b))
  (rt-div-safe : ∀ d a b s → rr (e1 (XI.Xdiv-safe-rrr d a b) s) (arith-reg d) ≡ rr s (arith-reg a) /ˢ rr s (arith-reg b))
  (rt-rem-safe : ∀ d a b s → rr (e1 (XI.Xrem-safe-rrr d a b) s) (arith-reg d) ≡ rr s (arith-reg a) %ˢ rr s (arith-reg b))
  (rt-sdiv    : ∀ d src imm s → rr (e1 (XI.Xsdiv-pow2-rri d src imm) s) (arith-reg d) ≡ sdiv2ᵏ (rr s (arith-reg src)) imm)
  (rt-out     : ∀ src s    → rr (e1 (XI.Xmov-out src) s) out-reg ≡ rr s (arith-reg src))
  where

  ----------------------------------------------------------------------
  -- xreg-idx is arch-neutral, so its injectivity is proved here.
  ----------------------------------------------------------------------
  xreg-idx-inj : ∀ {x y} → xreg-idx x ≡ xreg-idx y → x ≡ y
  xreg-idx-inj {XR0} {XR0} refl = refl
  xreg-idx-inj {XR1} {XR1} refl = refl

  -- From a target `just d` and `x ≢ d`, the `rf-other` frame hypothesis.
  frame-hyp : ∀ {i d x} → tgt i ≡ just d → ¬ (x ≡ d)
            → (∀ d' → tgt i ≡ just d' → ¬ (x ≡ d'))
  frame-hyp ti≡ ¬x≡d d' ti≡' x≡d' = ¬x≡d (trans x≡d' (just-injective (trans (sym ti≡') ti≡)))

  -- The vacuous frame hypothesis for a no-arith-target instruction.
  no-tgt-hyp : ∀ (i : XInstr) {x} → tgt i ≡ nothing → (∀ d → tgt i ≡ just d → ¬ (x ≡ d))
  no-tgt-hyp i ti≡ d ti≡' with trans (sym ti≡) ti≡'
  ... | ()

  ----------------------------------------------------------------------
  -- R — the register correspondence.
  ----------------------------------------------------------------------
  R : ∀ {sh} → ArithAbsState sh → St → Set
  R s-abs s-conc =
    ∀ (x : XReg) (w : ℕ)
    → (ArithAbsState.regs s-abs [ xreg-idx x ]) ≡ just w
    → w ≡ rr s-conc (arith-reg x)

  n≢j : ∀ {w : ℕ} → nothing ≡ just w → ⊥
  n≢j ()

  -- Inversion: a defined `bin-op`/`un-op` result is the op of the register reads.
  bin-value : ∀ {sh} (f : ℕ → ℕ → ℕ) (dr sr : XReg)
                (s-abs : ArithAbsState sh) (s-conc : St) (w : ℕ)
            → R s-abs s-conc
            → bin-op f (ArithAbsState.regs s-abs [ xreg-idx dr ])
                       (ArithAbsState.regs s-abs [ xreg-idx sr ]) ≡ just w
            → w ≡ f (rr s-conc (arith-reg dr)) (rr s-conc (arith-reg sr))
  bin-value f dr sr s-abs s-conc w r eq
    with ArithAbsState.regs s-abs [ xreg-idx dr ] in ed | ArithAbsState.regs s-abs [ xreg-idx sr ] in es
  ... | just a | just b = trans (sym (just-injective eq)) (cong₂ f (r dr a ed) (r sr b es))
  ... | just a | nothing = ⊥-elim (n≢j eq)
  ... | nothing | just b = ⊥-elim (n≢j eq)
  ... | nothing | nothing = ⊥-elim (n≢j eq)

  un-value : ∀ {sh} (f : ℕ → ℕ) (sr : XReg)
               (s-abs : ArithAbsState sh) (s-conc : St) (w : ℕ)
           → R s-abs s-conc
           → un-op f (ArithAbsState.regs s-abs [ xreg-idx sr ]) ≡ just w
           → w ≡ f (rr s-conc (arith-reg sr))
  un-value f sr s-abs s-conc w r eq
    with ArithAbsState.regs s-abs [ xreg-idx sr ] in es
  ... | just a  = trans (sym (just-injective eq)) (cong f (r sr a es))
  ... | nothing = ⊥-elim (n≢j eq)

  ----------------------------------------------------------------------
  -- The per-instruction step. UNIFORM: the `yes` branch combines the abstract
  -- value inversion with `rt-<i>`; the `no` branch rides `r` through the
  -- abstract frame and `rf-other`. Reload/arg need R-scratch/R-input (below).
  ----------------------------------------------------------------------

  -- The `no` (x ≢ target) half, shared by every value instruction. `vₐ` is the
  -- abstract value written to the target (inferred from `eq` at each call).
  step-other : ∀ {sh} {vₐ : Maybe ℕ} (i : XInstr) (d x : XReg) (w : ℕ)
                 (s-abs : ArithAbsState sh) (s-conc : St)
             → tgt i ≡ just d → R s-abs s-conc → ¬ (x ≡ d)
             → (ArithAbsState.regs s-abs [ xreg-idx d ↦ vₐ ]) [ xreg-idx x ] ≡ just w
             → w ≡ rr (e1 i s-conc) (arith-reg x)
  step-other i d x w s-abs s-conc ti≡ r ¬eq eq =
    trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
          (sym (rf-other i s-conc x (frame-hyp ti≡ ¬eq)))

  ----------------------------------------------------------------------
  -- Piece 4 — the output/result endpoint.
  ----------------------------------------------------------------------
  result-correct : ∀ {sh} (src : XReg) (s-abs : ArithAbsState sh) (s-conc : St) (v : ℕ)
                 → R s-abs s-conc
                 → ArithAbsState.regs s-abs [ xreg-idx src ] ≡ just v
                 → rr (e1 (XI.Xmov-out src) s-conc) out-reg ≡ v
  result-correct src s-abs s-conc v r eq = trans (rt-out src s-conc) (sym (r src v eq))

  ----------------------------------------------------------------------
  -- Piece 3 — init correspondence (register part), vacuous.
  ----------------------------------------------------------------------
  R-init : ∀ {sh} (env : ⟦ sh ⟧S) (s-conc : St) → R (init env) s-conc
  R-init env s-conc x w eq = ⊥-elim (n≢j eq)

  ----------------------------------------------------------------------
  -- R-scratch — the scratch correspondence (for reload).
  ----------------------------------------------------------------------
  R-scratch : ∀ {sh} → ArithAbsState sh → St → Set
  R-scratch s-abs s-conc =
    ∀ (sc : XScratch) (w : ℕ)
    → (ArithAbsState.scratch s-abs [ XScratch.slot sc ]) ≡ just w
    → mem s-conc (sa s-conc sc) ≡ just w

  R-step-reload : ∀ {sh} (d : XReg) (sc : XScratch) (s-abs : ArithAbsState sh) (s-conc : St)
                → R s-abs s-conc → R-scratch s-abs s-conc
                → R (exec-xinstr (XI.Xmov-m-r d sc) s-abs) (e1 (XI.Xmov-m-r d sc) s-conc)
  R-step-reload d sc s-abs s-conc r rs x w eq with x ≟x d
  ... | yes refl =
        sym (trans (rt-reload d sc s-conc)
                   (trans (cong def (rs sc w (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq)))
                          (def-just w)))
  ... | no ¬eq = step-other (XI.Xmov-m-r d sc) d x w s-abs s-conc refl r ¬eq eq

  ----------------------------------------------------------------------
  -- R-input — the input correspondence (for arg).
  ----------------------------------------------------------------------
  R-input : ∀ {sh} → ArithAbsState sh → St → Set
  R-input {sh} s-abs s-conc =
    ∀ (p : InputPath)
    → pl s-conc p ≡ fromℤ (maybe-zero (project sh p (ArithAbsState.input s-abs)))

  R-step-arg : ∀ {sh} (d : XReg) (p : InputPath) (s-abs : ArithAbsState sh) (s-conc : St)
             → R s-abs s-conc → R-input s-abs s-conc
             → R (exec-xinstr (XI.Xmov-arg d p) s-abs) (e1 (XI.Xmov-arg d p) s-conc)
  R-step-arg d p s-abs s-conc r ri x w eq with x ≟x d
  ... | yes refl =
        sym (trans (rt-arg d p s-conc)
                   (trans (ri p)
                          (just-injective (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))))
  ... | no ¬eq = step-other (XI.Xmov-arg d p) d x w s-abs s-conc refl r ¬eq eq

  ----------------------------------------------------------------------
  -- Rf = R × R-scratch × R-input — the FULL relation and block simulation.
  ----------------------------------------------------------------------
  Rf : ∀ {sh} → ArithAbsState sh → St → Set
  Rf s-abs s-conc = R s-abs s-conc × R-scratch s-abs s-conc × R-input s-abs s-conc

  -- The per-instruction step, TOTAL over XInstr. UNIFORM: the `yes` (x ≡ target)
  -- branch combines the abstract value inversion with `rt-<i>`; the `no` branch
  -- rides `r` through the abstract frame and `rf-other`. Reload/arg consume the
  -- R-scratch/R-input components; spill/out write no arith register (rf-other).
  R-step-full : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
              → Rf s-abs s-conc → R (exec-xinstr i s-abs) (e1 i s-conc)
  R-step-full (XI.Xmov-m-r d sc) s-abs s-conc (r , rsc , _) = R-step-reload d sc s-abs s-conc r rsc
  R-step-full (XI.Xmov-arg d p)  s-abs s-conc (r , _ , rin) = R-step-arg d p s-abs s-conc r rin
  R-step-full (XI.Xmov-r-m sc src) s-abs s-conc (r , _ , _) x w eq =
    trans (r x w eq) (sym (rf-other (XI.Xmov-r-m sc src) s-conc x (no-tgt-hyp (XI.Xmov-r-m sc src) refl)))
  R-step-full (XI.Xmov-out src) s-abs s-conc (r , _ , _) x w eq =
    trans (r x w eq) (sym (rf-other (XI.Xmov-out src) s-conc x (no-tgt-hyp (XI.Xmov-out src) refl)))
  R-step-full (XI.Xmov-imm d z) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (sym (just-injective (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq)))
                         (sym (rt-mov-imm d z s-conc))
  ... | no ¬eq = step-other (XI.Xmov-imm d z) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xmov-rr d src) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (r src w (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-mov-rr d src s-conc))
  ... | no ¬eq = step-other (XI.Xmov-rr d src) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xadd-rr d src) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (bin-value _⊕_ d src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-add d src s-conc))
  ... | no ¬eq = step-other (XI.Xadd-rr d src) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xsub-rr d src) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (bin-value _⊖_ d src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-sub d src s-conc))
  ... | no ¬eq = step-other (XI.Xsub-rr d src) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Ximul-rr d src) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (bin-value _⊗_ d src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-imul d src s-conc))
  ... | no ¬eq = step-other (XI.Ximul-rr d src) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xneg-r d) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (un-value ⊝_ d s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-neg d s-conc))
  ... | no ¬eq = step-other (XI.Xneg-r d) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xshl-rri d src imm) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (un-value (λ q → shlᵂ q imm) src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-shl d src imm s-conc))
  ... | no ¬eq = step-other (XI.Xshl-rri d src imm) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xdiv-rrr d a b) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (bin-value _/ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-div d a b s-conc))
  ... | no ¬eq = step-other (XI.Xdiv-rrr d a b) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xrem-rrr d a b) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (bin-value _%ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-rem d a b s-conc))
  ... | no ¬eq = step-other (XI.Xrem-rrr d a b) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xdiv-safe-rrr d a b) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (bin-value _/ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-div-safe d a b s-conc))
  ... | no ¬eq = step-other (XI.Xdiv-safe-rrr d a b) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xrem-safe-rrr d a b) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (bin-value _%ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-rem-safe d a b s-conc))
  ... | no ¬eq = step-other (XI.Xrem-safe-rrr d a b) d x w s-abs s-conc refl r ¬eq eq
  R-step-full (XI.Xsdiv-pow2-rri d src imm) s-abs s-conc (r , _ , _) x w eq with x ≟x d
  ... | yes refl = trans (un-value (λ q → sdiv2ᵏ q imm) src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
                         (sym (rt-sdiv d src imm s-conc))
  ... | no ¬eq = step-other (XI.Xsdiv-pow2-rri d src imm) d x w s-abs s-conc refl r ¬eq eq

  -- The INPUT frame — R-input preservation. Memory-layout obligation: no
  -- instruction changes the input pointer, and spill's write is disjoint from
  -- the input region (input ≥ frontier > scratch). Named residual.
  postulate
    input-frame : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
                → R-input s-abs s-conc → R-input (exec-xinstr i s-abs) (e1 i s-conc)

  -- Same slot ⇒ same scratch address (XScratch eta: `sc = mk-scratch (slot sc)`).
  sa-slot-eq : ∀ s sc sc' → XScratch.slot sc ≡ XScratch.slot sc' → sa s sc ≡ sa s sc'
  sa-slot-eq s sc sc' slot≡ = cong (λ n → sa s (mk-scratch n)) slot≡

  -- The 15 NON-spill instructions leave both abstract scratch and concrete
  -- memory@scratch-addr untouched (scratch-unchanged + mem-keep), and the
  -- address is step-invariant (sa-inv) ⇒ R-scratch rides through unchanged.
  nonspill-sf : ∀ i (nsp : NonSpill i) {sh} (s-abs : ArithAbsState sh) (s-conc : St)
              → R-scratch s-abs s-conc → R-scratch (exec-xinstr i s-abs) (e1 i s-conc)
  nonspill-sf i nsp s-abs s-conc rsc sc w eq =
    trans (cong (λ a → mem (e1 i s-conc) a) (sa-inv i s-conc sc))
          (trans (mem-keep i s-conc (sa s-conc sc) nsp)
                 (rsc sc w (trans (sym (cong (λ σ → σ [ XScratch.slot sc ]) (scratch-unchanged i nsp s-abs))) eq)))

  -- The SCRATCH frame — R-scratch preservation. PROVED from the memory-effect
  -- primitives (+ R for the spill hit, whose new cell = the spilled register).
  scratch-frame : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
                → R s-abs s-conc → R-scratch s-abs s-conc
                → R-scratch (exec-xinstr i s-abs) (e1 i s-conc)
  scratch-frame (XI.Xmov-r-m sc' src) s-abs s-conc r rsc sc w eq with XScratch.slot sc ≟ XScratch.slot sc'
  ... | yes slot≡ =
        trans (cong (λ a → mem (e1 (XI.Xmov-r-m sc' src) s-conc) a)
                    (trans (sa-inv (XI.Xmov-r-m sc' src) s-conc sc) (sa-slot-eq s-conc sc sc' slot≡)))
              (trans (mem-spill-hit sc' src s-conc)
                     (cong just (sym (r src w
                       (trans (sym (store-write-same (ArithAbsState.scratch s-abs) (XScratch.slot sc')
                                     (ArithAbsState.regs s-abs [ xreg-idx src ])))
                              (subst (λ n → (ArithAbsState.scratch s-abs [ XScratch.slot sc' ↦ ArithAbsState.regs s-abs [ xreg-idx src ] ]) [ n ] ≡ just w)
                                     slot≡ eq))))))
  ... | no slot≢ =
        trans (cong (λ a → mem (e1 (XI.Xmov-r-m sc' src) s-conc) a) (sa-inv (XI.Xmov-r-m sc' src) s-conc sc))
              (trans (mem-spill-miss sc' src s-conc (sa s-conc sc) (sa-inj s-conc sc sc' slot≢))
                     (rsc sc w (trans (sym (store-write-other (ArithAbsState.scratch s-abs) (XScratch.slot sc') (XScratch.slot sc)
                                             (ArithAbsState.regs s-abs [ xreg-idx src ]) (λ e → slot≢ (sym e)))) eq)))
  scratch-frame (XI.Xmov-imm d z) s-abs s-conc r rsc = nonspill-sf (XI.Xmov-imm d z) tt s-abs s-conc rsc
  scratch-frame (XI.Xmov-rr d src) s-abs s-conc r rsc = nonspill-sf (XI.Xmov-rr d src) tt s-abs s-conc rsc
  scratch-frame (XI.Xmov-m-r d sc) s-abs s-conc r rsc = nonspill-sf (XI.Xmov-m-r d sc) tt s-abs s-conc rsc
  scratch-frame (XI.Xmov-arg d p) s-abs s-conc r rsc = nonspill-sf (XI.Xmov-arg d p) tt s-abs s-conc rsc
  scratch-frame (XI.Xadd-rr d src) s-abs s-conc r rsc = nonspill-sf (XI.Xadd-rr d src) tt s-abs s-conc rsc
  scratch-frame (XI.Xsub-rr d src) s-abs s-conc r rsc = nonspill-sf (XI.Xsub-rr d src) tt s-abs s-conc rsc
  scratch-frame (XI.Ximul-rr d src) s-abs s-conc r rsc = nonspill-sf (XI.Ximul-rr d src) tt s-abs s-conc rsc
  scratch-frame (XI.Xneg-r d) s-abs s-conc r rsc = nonspill-sf (XI.Xneg-r d) tt s-abs s-conc rsc
  scratch-frame (XI.Xshl-rri d src imm) s-abs s-conc r rsc = nonspill-sf (XI.Xshl-rri d src imm) tt s-abs s-conc rsc
  scratch-frame (XI.Xdiv-rrr d a b) s-abs s-conc r rsc = nonspill-sf (XI.Xdiv-rrr d a b) tt s-abs s-conc rsc
  scratch-frame (XI.Xrem-rrr d a b) s-abs s-conc r rsc = nonspill-sf (XI.Xrem-rrr d a b) tt s-abs s-conc rsc
  scratch-frame (XI.Xdiv-safe-rrr d a b) s-abs s-conc r rsc = nonspill-sf (XI.Xdiv-safe-rrr d a b) tt s-abs s-conc rsc
  scratch-frame (XI.Xrem-safe-rrr d a b) s-abs s-conc r rsc = nonspill-sf (XI.Xrem-safe-rrr d a b) tt s-abs s-conc rsc
  scratch-frame (XI.Xsdiv-pow2-rri d src imm) s-abs s-conc r rsc = nonspill-sf (XI.Xsdiv-pow2-rri d src imm) tt s-abs s-conc rsc
  scratch-frame (XI.Xmov-out src) s-abs s-conc r rsc = nonspill-sf (XI.Xmov-out src) tt s-abs s-conc rsc

  Rf-step : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
          → Rf s-abs s-conc → Rf (exec-xinstr i s-abs) (e1 i s-conc)
  Rf-step i s-abs s-conc rf@(rr₀ , rsc , rin) =
    R-step-full i s-abs s-conc rf , scratch-frame i s-abs s-conc rr₀ rsc , input-frame i s-abs s-conc rin

  Rf-sim : ∀ {sh} (xs : List XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
         → Rf s-abs s-conc
         → Rf (exec-xprog xs s-abs) (eb xs s-conc)
  Rf-sim []       s-abs s-conc rf rewrite eb-nil s-conc = rf
  Rf-sim (i ∷ is) s-abs s-conc rf rewrite eb-cons i is s-conc =
    Rf-sim is (exec-xinstr i s-abs) (e1 i s-conc) (Rf-step i s-abs s-conc rf)

  ----------------------------------------------------------------------
  -- Rf at block entry (`init env`).
  ----------------------------------------------------------------------
  R-scratch-init : ∀ {sh} (env : ⟦ sh ⟧S) (s-conc : St) → R-scratch (init env) s-conc
  R-scratch-init env s-conc sc w eq = ⊥-elim (n≢j eq)

  Rf-init : ∀ {sh} (env : ⟦ sh ⟧S) (s-conc : St)
          → R-input (init env) s-conc → Rf (init env) s-conc
  Rf-init env s-conc ri = R-init env s-conc , R-scratch-init env s-conc , ri

  ----------------------------------------------------------------------
  -- THE ARITH-BLOCK VALUE THEOREM (top-down capstone).
  ----------------------------------------------------------------------
  -- `eb` over a concatenation (derived from the opaque `eb-nil`/`eb-cons`).
  eb-++ : ∀ xs ys s → eb (xs ++ ys) s ≡ eb ys (eb xs s)
  eb-++ []       ys s = cong (eb ys) (sym (eb-nil s))
  eb-++ (i ∷ is) ys s =
    trans (eb-cons i (is ++ ys) s)
          (trans (eb-++ is ys (e1 i s)) (cong (eb ys) (sym (eb-cons i is s))))

  -- The block ENDS with `Xmov-out XR0` (block-shape). Running it, the concrete
  -- result register holds the abstract output — PROVED: the final Xmov-out's
  -- concrete out-reg = arith-reg XR0's read (rt-out), which R ties to the
  -- abstract reg 0 = the block output (block-value-semM makes it defined).
  output-extract : ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) (s-conc : St)
    → R (exec-xprog (emit-program (compile-abs e)) (init env))
        (eb (emit-program (compile-abs e)) s-conc)
    → output-of (exec-xprog (emit-program (compile-abs e)) (init env))
        ≡ just (rr (eb (emit-program (compile-abs e)) s-conc) out-reg)
  output-extract {sh} e env s-conc R-end = trans (block-value-semM e env) (cong just body)
    where
      pre = emit-program (compile-go 0 e)
      aPre  = exec-xprog pre (init env)
      cPre  = eb pre s-conc
      blk≡ : exec-xprog (emit-program (compile-abs e)) (init env) ≡ exec-xinstr (XI.Xmov-out XR0) aPre
      blk≡ = trans (cong (λ p → exec-xprog p (init env)) (block-shape e))
                   (exec-xprog-++ pre (XI.Xmov-out XR0 ∷ []) (init env))
      ebk≡ : eb (emit-program (compile-abs e)) s-conc ≡ e1 (XI.Xmov-out XR0) cPre
      ebk≡ = trans (cong (λ p → eb p s-conc) (block-shape e))
                   (trans (eb-++ pre (XI.Xmov-out XR0 ∷ []) s-conc)
                          (trans (eb-cons (XI.Xmov-out XR0) [] cPre) (eb-nil (e1 (XI.Xmov-out XR0) cPre))))
      R' : R (exec-xinstr (XI.Xmov-out XR0) aPre) (e1 (XI.Xmov-out XR0) cPre)
      R' = subst₂ (λ a b → R a b) blk≡ ebk≡ R-end
      bvs' : ArithAbsState.regs aPre [ xreg-idx XR0 ] ≡ just (block-semM e (toWord sh env))
      bvs' = subst (λ t → output-of t ≡ just (block-semM e (toWord sh env))) blk≡ (block-value-semM e env)
      rr-eq : block-semM e (toWord sh env) ≡ rr (e1 (XI.Xmov-out XR0) cPre) (arith-reg XR0)
      rr-eq = R' XR0 (block-semM e (toWord sh env)) bvs'
      body : block-semM e (toWord sh env) ≡ rr (eb (emit-program (compile-abs e)) s-conc) out-reg
      body = trans (trans rr-eq (rf-other (XI.Xmov-out XR0) cPre XR0 (no-tgt-hyp (XI.Xmov-out XR0) refl)))
                   (sym (trans (cong (λ t → rr t out-reg) ebk≡) (rt-out XR0 cPre)))

  arith-block-correct : ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) (s-conc : St)
    → R-input (init env) s-conc
    → rr (eb (emit-program (compile-abs e)) s-conc) out-reg
        ≡ block-semM e (toWord sh env)
  arith-block-correct e env s-conc ri =
    just-injective
      (trans (sym (output-extract e env s-conc
                     (proj₁ (Rf-sim (emit-program (compile-abs e)) (init env) s-conc (Rf-init env s-conc ri)))))
             (block-value-semM e env))
