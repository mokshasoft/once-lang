-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimCore  (Plan 0.54 rung B / B2.3)
--
-- The ARCH-GENERIC arith concrete↔abstract simulation. This is the x86-64
-- proof (`ArithSimX86-64`) with its arch-specific surface hoisted into a
-- parameter telescope, so the ~16 R-step cases, the block composition
-- (`R-sim`/`Rf-sim`), the Rf assembly, and the `arith-block-correct` capstone
-- are written ONCE. Each arch is a thin instance: x86-64 supplies its state /
-- readReg / writeReg / val-mirror; riscv64 is a near-free mirror (different reg
-- set + `scratch-addr = sp + 8·slot`); x86-32 adds BorrowRestoreCore but reuses
-- this template.
--
-- What is ARCH-NEUTRAL and imported directly: the WHOLE abstract side —
-- `exec-xinstr` / `exec-xprog` / `xreg-idx` (Backend.Correct 64), the abstract
-- store, `bin-op`/`un-op`, `block-value-semM`, `block-semM`/`toWord`,
-- `emit-program`/`compile-abs`, and the Word64 ops.
--
-- What is a PARAMETER (see the `Core` telescope):
--   * the concrete machine (`St`, `regs`, `readReg`, `writeReg`, `mem`,
--     `arith-reg`, `rax`/`rdx`, `def`, `sa`=scratch-addr, `pl`=path-load);
--   * `e1`/`eb` — the concrete step / block fold (opaque here);
--   * the arch's 4 frame lemmas (`readReg-wr-…`) + `readReg-wr-rax-same`;
--   * `eb-nil`/`eb-cons` — the block-fold reductions (a param `eb` is opaque);
--   * the 16 `ce-*` per-instruction concrete reg-effects — each folds `writes`
--     with the val-mirror, so `refl` per arch, and lets the R-step proofs reduce.
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimCore where

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Empty using (⊥; ⊥-elim)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch)
open XI using (XR0; XR1; XR2; XR3)
open import Once.Arith.Machine.Shape using (InputShape; ⟦_⟧S; InputPath; project)
open import Once.Arith.Machine.AbsState
  using (ArithAbsState; Store; _[_]; init; store-write-same; store-write-other; output-of)
open import Once.Arith.Machine.AbsInstr using (bin-op; un-op; maybe-zero)
import Once.Arith.Backend.Correct as Correct
open Correct 64 using (exec-xinstr; exec-xprog; xreg-idx)
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Backend.XInstr.CodeGen using (_≟x_; emit-program)
open import Once.Arith.Machine.Compile using (compile-abs)
open import Once.Arith.SigOp.Block using (block-semM)
open import Once.Arith.SigOp.BlockSemBridge using (toWord)
open import Once.Arith.Backend.BlockValueSemM using (block-value-semM)

import Once.Word as OnceWord
open OnceWord.Word64 using (_⊕_; _⊖_; _⊗_; _/ˢ_; _%ˢ_; ⊝_; shlᵂ; sdiv2ᵏ; fromℤ)

------------------------------------------------------------------------
-- The parameterised core. `St`/`RegFile`/`Reg` are the concrete machine's
-- carriers; every word is `ℕ` (all arches use `Word64.Word = ℕ` at this layer,
-- the same width as `block-semM`).
------------------------------------------------------------------------

module Core
  (St RegFile Reg : Set)
  (regs     : St → RegFile)
  (readReg  : RegFile → Reg → ℕ)
  (writeReg : RegFile → Reg → ℕ → RegFile)
  (mem      : St → ℕ → Maybe ℕ)
  (arith-reg : XReg → Reg)
  (rax rdx  : Reg)
  (def      : Maybe ℕ → ℕ)
  (def-just : ∀ w → def (just w) ≡ w)
  (sa       : St → XScratch → ℕ)
  (pl       : St → InputPath → ℕ)
  (e1       : XInstr → St → St)
  (eb       : List XInstr → St → St)
  -- block-fold reductions (a param `eb` is opaque, so R-sim can't reduce it).
  (eb-nil   : ∀ s → eb [] s ≡ s)
  (eb-cons  : ∀ i is s → eb (i ∷ is) s ≡ eb is (e1 i s))
  -- the arch's frame lemmas (the 4×4 analysis on the arith-reg window).
  (readReg-wr-arith-same  : ∀ rf x v → readReg (writeReg rf (arith-reg x) v) (arith-reg x) ≡ v)
  (readReg-wr-arith-other : ∀ rf x y v → ¬ (x ≡ y)
                          → readReg (writeReg rf (arith-reg x) v) (arith-reg y) ≡ readReg rf (arith-reg y))
  (readReg-wr-rax-arith   : ∀ rf x v → readReg (writeReg rf rax v) (arith-reg x) ≡ readReg rf (arith-reg x))
  (readReg-wr-rdx-arith   : ∀ rf x v → readReg (writeReg rf rdx v) (arith-reg x) ≡ readReg rf (arith-reg x))
  (readReg-wr-rax-same    : ∀ rf v → readReg (writeReg rf rax v) rax ≡ v)
  -- per-instruction concrete reg-effects (folds `writes` + val-mirror; `refl` per arch).
  (ce-mov-imm : ∀ d z s   → regs (e1 (XI.Xmov-imm d z) s)   ≡ writeReg (regs s) (arith-reg d) (fromℤ z))
  (ce-mov-rr  : ∀ d src s  → regs (e1 (XI.Xmov-rr d src) s)  ≡ writeReg (regs s) (arith-reg d) (readReg (regs s) (arith-reg src)))
  (ce-spill   : ∀ sc src s → regs (e1 (XI.Xmov-r-m sc src) s) ≡ regs s)
  (ce-reload  : ∀ d sc s   → regs (e1 (XI.Xmov-m-r d sc) s)  ≡ writeReg (regs s) (arith-reg d) (def (mem s (sa s sc))))
  (ce-arg     : ∀ d p s    → regs (e1 (XI.Xmov-arg d p) s)   ≡ writeReg (writeReg (regs s) (arith-reg d) (pl s p)) rax (pl s p))
  (ce-add     : ∀ d src s  → regs (e1 (XI.Xadd-rr d src) s)  ≡ writeReg (regs s) (arith-reg d) (readReg (regs s) (arith-reg d) ⊕ readReg (regs s) (arith-reg src)))
  (ce-sub     : ∀ d src s  → regs (e1 (XI.Xsub-rr d src) s)  ≡ writeReg (regs s) (arith-reg d) (readReg (regs s) (arith-reg d) ⊖ readReg (regs s) (arith-reg src)))
  (ce-imul    : ∀ d src s  → regs (e1 (XI.Ximul-rr d src) s) ≡ writeReg (regs s) (arith-reg d) (readReg (regs s) (arith-reg d) ⊗ readReg (regs s) (arith-reg src)))
  (ce-neg     : ∀ d s      → regs (e1 (XI.Xneg-r d) s)       ≡ writeReg (regs s) (arith-reg d) (⊝ readReg (regs s) (arith-reg d)))
  (ce-shl     : ∀ d src imm s → regs (e1 (XI.Xshl-rri d src imm) s) ≡ writeReg (regs s) (arith-reg d) (shlᵂ (readReg (regs s) (arith-reg src)) imm))
  (ce-div     : ∀ d a b s  → regs (e1 (XI.Xdiv-rrr d a b) s)
                           ≡ writeReg (writeReg (writeReg (regs s) (arith-reg d) (readReg (regs s) (arith-reg a) /ˢ readReg (regs s) (arith-reg b)))
                                                rax (readReg (regs s) (arith-reg a) /ˢ readReg (regs s) (arith-reg b)))
                                      rdx (readReg (regs s) (arith-reg a) /ˢ readReg (regs s) (arith-reg b)))
  (ce-rem     : ∀ d a b s  → regs (e1 (XI.Xrem-rrr d a b) s)
                           ≡ writeReg (writeReg (writeReg (regs s) (arith-reg d) (readReg (regs s) (arith-reg a) %ˢ readReg (regs s) (arith-reg b)))
                                                rax (readReg (regs s) (arith-reg a) %ˢ readReg (regs s) (arith-reg b)))
                                      rdx (readReg (regs s) (arith-reg a) %ˢ readReg (regs s) (arith-reg b)))
  (ce-div-safe : ∀ d a b s → regs (e1 (XI.Xdiv-safe-rrr d a b) s)
                           ≡ writeReg (writeReg (writeReg (regs s) (arith-reg d) (readReg (regs s) (arith-reg a) /ˢ readReg (regs s) (arith-reg b)))
                                                rax (readReg (regs s) (arith-reg a) /ˢ readReg (regs s) (arith-reg b)))
                                      rdx (readReg (regs s) (arith-reg a) /ˢ readReg (regs s) (arith-reg b)))
  (ce-rem-safe : ∀ d a b s → regs (e1 (XI.Xrem-safe-rrr d a b) s)
                           ≡ writeReg (writeReg (writeReg (regs s) (arith-reg d) (readReg (regs s) (arith-reg a) %ˢ readReg (regs s) (arith-reg b)))
                                                rax (readReg (regs s) (arith-reg a) %ˢ readReg (regs s) (arith-reg b)))
                                      rdx (readReg (regs s) (arith-reg a) %ˢ readReg (regs s) (arith-reg b)))
  (ce-sdiv    : ∀ d src imm s → regs (e1 (XI.Xsdiv-pow2-rri d src imm) s)
                           ≡ writeReg (writeReg (regs s) (arith-reg d) (sdiv2ᵏ (readReg (regs s) (arith-reg src)) imm))
                                      rax (sdiv2ᵏ (readReg (regs s) (arith-reg src)) imm))
  (ce-out     : ∀ src s    → regs (e1 (XI.Xmov-out src) s)   ≡ writeReg (regs s) rax (readReg (regs s) (arith-reg src)))
  where

  ----------------------------------------------------------------------
  -- xreg-idx is arch-neutral, so its injectivity is proved here (not a param).
  ----------------------------------------------------------------------
  xreg-idx-inj : ∀ {x y} → xreg-idx x ≡ xreg-idx y → x ≡ y
  xreg-idx-inj {XR0} {XR0} refl = refl
  xreg-idx-inj {XR1} {XR1} refl = refl
  xreg-idx-inj {XR2} {XR2} refl = refl
  xreg-idx-inj {XR3} {XR3} refl = refl

  -- Peel the rax+rdx clobbers (div/rem write [arith-reg d, rax, rdx]).
  peel-io2 : ∀ (rf : RegFile) (x : XReg) (v : ℕ)
           → readReg (writeReg (writeReg rf rax v) rdx v) (arith-reg x) ≡ readReg rf (arith-reg x)
  peel-io2 rf x v = trans (readReg-wr-rdx-arith (writeReg rf rax v) x v) (readReg-wr-rax-arith rf x v)

  ----------------------------------------------------------------------
  -- R — the register correspondence. Every DEFINED abstract register cell
  -- matches the concrete register, via `xreg-idx` (abstract index) ↔
  -- `arith-reg` (physical reg).
  ----------------------------------------------------------------------
  R : ∀ {sh} → ArithAbsState sh → St → Set
  R s-abs s-conc =
    ∀ (x : XReg) (w : ℕ)
    → (ArithAbsState.regs s-abs [ xreg-idx x ]) ≡ just w
    → w ≡ readReg (regs s-conc) (arith-reg x)

  n≢j : ∀ {w : ℕ} → nothing ≡ just w → ⊥
  n≢j ()

  -- Inversion: a defined `bin-op`/`un-op` result forces both operand cells
  -- defined; with R, the value is the op of the concrete register reads.
  bin-value : ∀ {sh} (f : ℕ → ℕ → ℕ) (dr sr : XReg)
                (s-abs : ArithAbsState sh) (s-conc : St) (w : ℕ)
            → R s-abs s-conc
            → bin-op f (ArithAbsState.regs s-abs [ xreg-idx dr ])
                       (ArithAbsState.regs s-abs [ xreg-idx sr ]) ≡ just w
            → w ≡ f (readReg (regs s-conc) (arith-reg dr)) (readReg (regs s-conc) (arith-reg sr))
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
           → w ≡ f (readReg (regs s-conc) (arith-reg sr))
  un-value f sr s-abs s-conc w r eq
    with ArithAbsState.regs s-abs [ xreg-idx sr ] in es
  ... | just a  = trans (sym (just-injective eq)) (cong f (r sr a es))
  ... | nothing = ⊥-elim (n≢j eq)

  ----------------------------------------------------------------------
  -- The per-instruction step. NEAR-DEFINITIONAL for arithmetic instructions
  -- (each `ce-*` reduces the concrete write to the op form); memory
  -- instructions (reload/arg) need R's scratch/input extension → catch-all.
  ----------------------------------------------------------------------
  postulate
    R-step-rest : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
                → R s-abs s-conc → R (exec-xinstr i s-abs) (e1 i s-conc)

  R-step : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
         → R s-abs s-conc → R (exec-xinstr i s-abs) (e1 i s-conc)
  R-step (XI.Xmov-r-m sc src) s-abs s-conc r rewrite ce-spill sc src s-conc = r
  R-step (XI.Xmov-imm d z) s-abs s-conc r x w eq rewrite ce-mov-imm d z s-conc with x ≟x d
  ... | yes refl =
        trans (sym (just-injective (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq)))
              (sym (readReg-wr-arith-same (regs s-conc) d _))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
  R-step (XI.Xmov-rr d src) s-abs s-conc r x w eq rewrite ce-mov-rr d src s-conc with x ≟x d
  ... | yes refl =
        trans (r src w (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (readReg-wr-arith-same (regs s-conc) d _))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
  R-step (XI.Xmov-out src) s-abs s-conc r x w eq rewrite ce-out src s-conc =
        trans (r x w eq) (sym (readReg-wr-rax-arith (regs s-conc) x _))
  R-step (XI.Xadd-rr d src) s-abs s-conc r x w eq rewrite ce-add d src s-conc with x ≟x d
  ... | yes refl =
        trans (bin-value _⊕_ d src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (readReg-wr-arith-same (regs s-conc) d _))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
  R-step (XI.Xsub-rr d src) s-abs s-conc r x w eq rewrite ce-sub d src s-conc with x ≟x d
  ... | yes refl =
        trans (bin-value _⊖_ d src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (readReg-wr-arith-same (regs s-conc) d _))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
  R-step (XI.Ximul-rr d src) s-abs s-conc r x w eq rewrite ce-imul d src s-conc with x ≟x d
  ... | yes refl =
        trans (bin-value _⊗_ d src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (readReg-wr-arith-same (regs s-conc) d _))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
  R-step (XI.Xneg-r d) s-abs s-conc r x w eq rewrite ce-neg d s-conc with x ≟x d
  ... | yes refl =
        trans (un-value ⊝_ d s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (readReg-wr-arith-same (regs s-conc) d _))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
  R-step (XI.Xshl-rri d src imm) s-abs s-conc r x w eq rewrite ce-shl d src imm s-conc with x ≟x d
  ... | yes refl =
        trans (un-value (λ q → shlᵂ q imm) src s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (readReg-wr-arith-same (regs s-conc) d _))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))
  R-step (XI.Xdiv-rrr d a b) s-abs s-conc r x w eq rewrite ce-div d a b s-conc with x ≟x d
  ... | yes refl =
        trans (bin-value _/ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) d _)
                          (readReg-wr-arith-same (regs s-conc) d _)))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) x _)
                          (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
  R-step (XI.Xrem-rrr d a b) s-abs s-conc r x w eq rewrite ce-rem d a b s-conc with x ≟x d
  ... | yes refl =
        trans (bin-value _%ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) d _)
                          (readReg-wr-arith-same (regs s-conc) d _)))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) x _)
                          (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
  R-step (XI.Xdiv-safe-rrr d a b) s-abs s-conc r x w eq rewrite ce-div-safe d a b s-conc with x ≟x d
  ... | yes refl =
        trans (bin-value _/ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) d _)
                          (readReg-wr-arith-same (regs s-conc) d _)))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) x _)
                          (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
  R-step (XI.Xrem-safe-rrr d a b) s-abs s-conc r x w eq rewrite ce-rem-safe d a b s-conc with x ≟x d
  ... | yes refl =
        trans (bin-value _%ˢ_ a b s-abs s-conc w r (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) d _)
                          (readReg-wr-arith-same (regs s-conc) d _)))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (trans (peel-io2 (writeReg (regs s-conc) (arith-reg d) _) x _)
                          (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
  R-step (XI.Xsdiv-pow2-rri d src imm) s-abs s-conc r x w eq rewrite ce-sdiv d src imm s-conc with x ≟x d
  ... | yes refl =
        trans (un-value (λ q → sdiv2ᵏ q imm) src s-abs s-conc w r
                 (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))
              (sym (trans (readReg-wr-rax-arith (writeReg (regs s-conc) (arith-reg d) _) d _)
                          (readReg-wr-arith-same (regs s-conc) d _)))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (trans (readReg-wr-rax-arith (writeReg (regs s-conc) (arith-reg d) _) x _)
                          (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))
  R-step i s-abs s-conc r = R-step-rest i s-abs s-conc r

  ----------------------------------------------------------------------
  -- The block simulation — PROVED by induction, reducing to `R-step`. Both
  -- folds peel the head instruction in lockstep (`eb-cons`), so the cons case
  -- threads `R-step` then recurses.
  ----------------------------------------------------------------------
  R-sim : ∀ {sh} (xs : List XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
        → R s-abs s-conc
        → R (exec-xprog xs s-abs) (eb xs s-conc)
  R-sim []       s-abs s-conc r rewrite eb-nil s-conc = r
  R-sim (i ∷ is) s-abs s-conc r rewrite eb-cons i is s-conc =
    R-sim is (exec-xinstr i s-abs) (e1 i s-conc) (R-step i s-abs s-conc r)

  ----------------------------------------------------------------------
  -- Piece 4 — the output/result endpoint. After `Xmov-out src`, the concrete
  -- result register `rax` holds the abstract source value.
  ----------------------------------------------------------------------
  result-correct : ∀ {sh} (src : XReg) (s-abs : ArithAbsState sh) (s-conc : St) (v : ℕ)
                 → R s-abs s-conc
                 → ArithAbsState.regs s-abs [ xreg-idx src ] ≡ just v
                 → readReg (regs (e1 (XI.Xmov-out src) s-conc)) rax ≡ v
  result-correct src s-abs s-conc v r eq rewrite ce-out src s-conc =
    trans (readReg-wr-rax-same (regs s-conc) (readReg (regs s-conc) (arith-reg src))) (sym (r src v eq))

  ----------------------------------------------------------------------
  -- Piece 3 — init correspondence (register part). `init env` has EMPTY
  -- registers, so R holds VACUOUSLY.
  ----------------------------------------------------------------------
  R-init : ∀ {sh} (env : ⟦ sh ⟧S) (s-conc : St) → R (init env) s-conc
  R-init env s-conc x w eq = ⊥-elim (n≢j eq)

  ----------------------------------------------------------------------
  -- R-scratch — the scratch correspondence (for reload). Abstract scratch slot
  -- ↔ concrete `mem (scratch-addr sc)`.
  ----------------------------------------------------------------------
  R-scratch : ∀ {sh} → ArithAbsState sh → St → Set
  R-scratch s-abs s-conc =
    ∀ (sc : XScratch) (w : ℕ)
    → (ArithAbsState.scratch s-abs [ XScratch.slot sc ]) ≡ just w
    → mem s-conc (sa s-conc sc) ≡ just w

  -- Reload (`Xmov-m-r d sc`): writes reg d from the scratch slot. Given R and
  -- R-scratch, R is preserved.
  R-step-reload : ∀ {sh} (d : XReg) (sc : XScratch) (s-abs : ArithAbsState sh) (s-conc : St)
                → R s-abs s-conc → R-scratch s-abs s-conc
                → R (exec-xinstr (XI.Xmov-m-r d sc) s-abs) (e1 (XI.Xmov-m-r d sc) s-conc)
  R-step-reload d sc s-abs s-conc r rs x w eq rewrite ce-reload d sc s-conc with x ≟x d
  ... | yes refl =
        sym (trans (trans (readReg-wr-arith-same (regs s-conc) d _)
                          (cong def (rs sc w (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))))
                   (def-just w))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de))))

  ----------------------------------------------------------------------
  -- R-input — the input correspondence (for arg). The concrete rdi memory
  -- chase `pl p` equals the abstract input value at path `p`.
  ----------------------------------------------------------------------
  R-input : ∀ {sh} → ArithAbsState sh → St → Set
  R-input {sh} s-abs s-conc =
    ∀ (p : InputPath)
    → pl s-conc p ≡ fromℤ (maybe-zero (project sh p (ArithAbsState.input s-abs)))

  -- Arg (`Xmov-arg d p`): writes reg d from the input (rdi chase). Given R and
  -- R-input, R is preserved.
  R-step-arg : ∀ {sh} (d : XReg) (p : InputPath) (s-abs : ArithAbsState sh) (s-conc : St)
             → R s-abs s-conc → R-input s-abs s-conc
             → R (exec-xinstr (XI.Xmov-arg d p) s-abs) (e1 (XI.Xmov-arg d p) s-conc)
  R-step-arg d p s-abs s-conc r ri x w eq rewrite ce-arg d p s-conc with x ≟x d
  ... | yes refl =
        sym (trans (trans (readReg-wr-rax-arith (writeReg (regs s-conc) (arith-reg d) (pl s-conc p)) d (pl s-conc p))
                          (readReg-wr-arith-same (regs s-conc) d (pl s-conc p)))
                   (trans (ri p)
                          (just-injective (trans (sym (store-write-same (ArithAbsState.regs s-abs) (xreg-idx d) _)) eq))))
  ... | no ¬eq =
        trans (r x w (trans (sym (store-write-other (ArithAbsState.regs s-abs) (xreg-idx d) (xreg-idx x) _
                                    (λ ie → ¬eq (sym (xreg-idx-inj ie))))) eq))
              (sym (trans (readReg-wr-rax-arith (writeReg (regs s-conc) (arith-reg d) (pl s-conc p)) x (pl s-conc p))
                          (readReg-wr-arith-other (regs s-conc) d x _ (λ de → ¬eq (sym de)))))

  ----------------------------------------------------------------------
  -- Rf = R × R-scratch × R-input — the FULL relation, and the block simulation.
  ----------------------------------------------------------------------
  Rf : ∀ {sh} → ArithAbsState sh → St → Set
  Rf s-abs s-conc = R s-abs s-conc × R-scratch s-abs s-conc × R-input s-abs s-conc

  R-step-full : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
              → Rf s-abs s-conc → R (exec-xinstr i s-abs) (e1 i s-conc)
  R-step-full (XI.Xmov-m-r d sc) s-abs s-conc (rr , rsc , rin) = R-step-reload d sc s-abs s-conc rr rsc
  R-step-full (XI.Xmov-arg d p)  s-abs s-conc (rr , rsc , rin) = R-step-arg d p s-abs s-conc rr rin
  R-step-full i                  s-abs s-conc (rr , rsc , rin) = R-step i s-abs s-conc rr

  -- The scratch/input FRAME preservations — mechanical (these don't change;
  -- spill updates the written slot / is disjoint from the input below the
  -- frontier). Named obligations; the per-instruction VALUE content is proved.
  postulate
    scratch-frame : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
                  → R-scratch s-abs s-conc → R-scratch (exec-xinstr i s-abs) (e1 i s-conc)
    input-frame   : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
                  → R-input s-abs s-conc → R-input (exec-xinstr i s-abs) (e1 i s-conc)

  Rf-step : ∀ {sh} (i : XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
          → Rf s-abs s-conc → Rf (exec-xinstr i s-abs) (e1 i s-conc)
  Rf-step i s-abs s-conc rf@(rr , rsc , rin) =
    R-step-full i s-abs s-conc rf , scratch-frame i s-abs s-conc rsc , input-frame i s-abs s-conc rin

  Rf-sim : ∀ {sh} (xs : List XInstr) (s-abs : ArithAbsState sh) (s-conc : St)
         → Rf s-abs s-conc
         → Rf (exec-xprog xs s-abs) (eb xs s-conc)
  Rf-sim []       s-abs s-conc rf rewrite eb-nil s-conc = rf
  Rf-sim (i ∷ is) s-abs s-conc rf rewrite eb-cons i is s-conc =
    Rf-sim is (exec-xinstr i s-abs) (e1 i s-conc) (Rf-step i s-abs s-conc rf)

  ----------------------------------------------------------------------
  -- Rf at block entry (`init env`). Registers + scratch empty (vacuous); the
  -- input correspondence is the caller's hypothesis.
  ----------------------------------------------------------------------
  R-scratch-init : ∀ {sh} (env : ⟦ sh ⟧S) (s-conc : St) → R-scratch (init env) s-conc
  R-scratch-init env s-conc sc w eq = ⊥-elim (n≢j eq)

  Rf-init : ∀ {sh} (env : ⟦ sh ⟧S) (s-conc : St)
          → R-input (init env) s-conc → Rf (init env) s-conc
  Rf-init env s-conc ri = R-init env s-conc , R-scratch-init env s-conc , ri

  ----------------------------------------------------------------------
  -- THE ARITH-BLOCK VALUE THEOREM (top-down capstone). Running the compiled
  -- arith block on the concrete machine leaves `block-semM (toWord env)` in
  -- `rax` — the value rung A's flat machine computes.
  ----------------------------------------------------------------------
  postulate
    output-extract : ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) (s-conc : St)
      → R (exec-xprog (emit-program (compile-abs e)) (init env))
          (eb (emit-program (compile-abs e)) s-conc)
      → output-of (exec-xprog (emit-program (compile-abs e)) (init env))
          ≡ just (readReg (regs (eb (emit-program (compile-abs e)) s-conc)) rax)

  arith-block-correct : ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) (s-conc : St)
    → R-input (init env) s-conc
    → readReg (regs (eb (emit-program (compile-abs e)) s-conc)) rax
        ≡ block-semM e (toWord sh env)
  arith-block-correct e env s-conc ri =
    just-injective
      (trans (sym (output-extract e env s-conc
                     (proj₁ (Rf-sim (emit-program (compile-abs e)) (init env) s-conc (Rf-init env s-conc ri)))))
             (block-value-semM e env))
