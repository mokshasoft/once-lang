-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ArithSimRiscV64  (Plan 0.54 rung B / B2.3)
--
-- The riscv64 INSTANCE of the arch-generic arith concrete↔abstract simulation
-- (`ArithSimCore.Core`) — the near-free mirror the genericization was built for.
-- All the content (R / R-scratch / R-input, the per-instruction step, Rf-sim,
-- the capstone) is re-exported from the core; this module supplies only the
-- riscv64 surface:
--   * `val-riscv64` — the concrete XInstr interpreter over `RV.State` (mirrors
--     `val-x86-64`: registers via readReg∘regs∘arith-reg, reload via readMem at
--     `sp + 8·slot`, arg via the InputPath chase from `t0`);
--   * the frame lemmas (the 2×2 arith window a3/a4, plus the io reg `a0`);
--   * `rf-other` / the 14 `rt-*` facts.
--
-- Contrast with x86-64, made trivial by the clobber-agnostic core: RV64's native
-- `div`/`rem` clobber NOTHING beyond the target (single write — no rax/rdx peel),
-- and the io scratch/output reg is `a0` (there is no `rdx` analogue). The proof
-- bodies are otherwise identical to x86-64's.
--
-- Parameterised by `N` — the reserved scratch-frame size riscv's `exec1` threads
-- (x86-64's subtract-addressing needs none; riscv's `sp + offset` does).
------------------------------------------------------------------------

module Once.Adequacy.ArchCorrectness.ArithSimRiscV64 where

open import Data.Nat using (ℕ; _+_; _*_; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Once.Arith.Backend.XInstr.Syntax as XI using (XInstr; XReg; XScratch)
open XI using (XR0; XR1)
open import Once.Arith.Machine.Shape using (⟦_⟧S; InputPath; Side; Fst; Snd)
open import Once.Target.RiscV64.PhysReg using (Reg; a0; a3; a4; sp; t0)
open import Once.Arith.Backend.RiscV64.Emit using (arith-reg)
import Once.CCC.Target.RiscV64.Semantics as RV
open RV using (State; readReg; writeReg; readMem; RegFile; Word)
open RV.State using (regs; memory)
import Once.Arith.Backend.RiscV64.ExecArith as EA
import Once.Word as OnceWord
module W = OnceWord.Word64
open import Once.Adequacy.ArchCorrectness.ArithSimCore using (tgt; module Core)

------------------------------------------------------------------------
-- val-riscv64 — the concrete XInstr arith interpreter over RV.State.
------------------------------------------------------------------------

rd : State → XReg → Word
rd s x = readReg (regs s) (arith-reg x)

def : Maybe Word → Word
def (just w) = w
def nothing  = 0

scratch-addr : State → XScratch → Word
scratch-addr s sc = readReg (regs s) sp + (8 * XScratch.slot sc)

side-off : Side → Word
side-off Fst = 0
side-off Snd = 8

path-load-go : State → Word → InputPath → Word
path-load-go s addr []          = def (readMem (memory s) addr)
path-load-go s addr (sd ∷ rest) =
  path-load-go s (def (readMem (memory s) (addr + side-off sd))) rest

path-load : State → InputPath → Word
path-load s p = path-load-go s (readReg (regs s) t0) p

val-riscv64 : XInstr → State → Reg → Word
val-riscv64 (XI.Xmov-imm d z)          s _ = W.fromℤ z
val-riscv64 (XI.Xmov-rr d src)         s _ = rd s src
val-riscv64 (XI.Xmov-r-m sc src)       s _ = rd s src
val-riscv64 (XI.Xmov-m-r d sc)         s _ = def (readMem (memory s) (scratch-addr s sc))
val-riscv64 (XI.Xmov-arg d p)          s _ = path-load s p
val-riscv64 (XI.Xadd-rr d src)         s _ = rd s d W.⊕ rd s src
val-riscv64 (XI.Xsub-rr d src)         s _ = rd s d W.⊖ rd s src
val-riscv64 (XI.Ximul-rr d src)        s _ = rd s d W.⊗ rd s src
val-riscv64 (XI.Xdiv-rrr d a b)        s _ = rd s a W./ˢ rd s b
val-riscv64 (XI.Xrem-rrr d a b)        s _ = rd s a W.%ˢ rd s b
val-riscv64 (XI.Xdiv-safe-rrr d a b)   s _ = rd s a W./ˢ rd s b
val-riscv64 (XI.Xrem-safe-rrr d a b)   s _ = rd s a W.%ˢ rd s b
val-riscv64 (XI.Xshl-rri d src imm)    s _ = W.shlᵂ (rd s src) imm
val-riscv64 (XI.Xsdiv-pow2-rri d src imm) s _ = W.sdiv2ᵏ (rd s src) imm
val-riscv64 (XI.Xneg-r d)              s _ = W.⊝ (rd s d)
val-riscv64 (XI.Xmov-out src)          s _ = rd s src

------------------------------------------------------------------------
-- Frame lemmas — the 2×2 arith window (a3/a4) plus the io reg `a0`. RV64 has
-- no rdx analogue, and native div/rem clobber only the target.
------------------------------------------------------------------------

readReg-wr-arith-other : ∀ (rf : RegFile) (x y : XReg) (v : Word)
                       → ¬ (x ≡ y)
                       → readReg (writeReg rf (arith-reg x) v) (arith-reg y) ≡ readReg rf (arith-reg y)
readReg-wr-arith-other rf XR0 XR0 v ¬eq = ⊥-elim (¬eq refl)
readReg-wr-arith-other rf XR0 XR1 v _ = refl
readReg-wr-arith-other rf XR1 XR0 v _ = refl
readReg-wr-arith-other rf XR1 XR1 v ¬eq = ⊥-elim (¬eq refl)

readReg-wr-arith-same : ∀ (rf : RegFile) (x : XReg) (v : Word)
                      → readReg (writeReg rf (arith-reg x) v) (arith-reg x) ≡ v
readReg-wr-arith-same rf XR0 v = refl
readReg-wr-arith-same rf XR1 v = refl

readReg-wr-a0-arith : ∀ (rf : RegFile) (x : XReg) (v : Word)
                    → readReg (writeReg rf a0 v) (arith-reg x) ≡ readReg rf (arith-reg x)
readReg-wr-a0-arith rf XR0 v = refl
readReg-wr-a0-arith rf XR1 v = refl

readReg-wr-a0-same : ∀ (rf : RegFile) (v : Word) → readReg (writeReg rf a0 v) a0 ≡ v
readReg-wr-a0-same rf v = refl

rr : State → Reg → ℕ
rr s r = readReg (regs s) r

mem : State → ℕ → Maybe ℕ
mem s a = readMem (memory s) a

¬d≡x : ∀ (d x : XReg) → (∀ d' → just d ≡ just d' → ¬ (x ≡ d')) → ¬ (d ≡ x)
¬d≡x d x h d≡x = h d refl (sym d≡x)

------------------------------------------------------------------------
-- The instance, parameterised by the scratch-frame size `N`.
------------------------------------------------------------------------

module _ (N : ℕ) where

  -- The value instruction `i` writes to its target (val ignores the reg arg).
  V : XInstr → State → Word
  V i s = val-riscv64 i s a0

  -- rf-other — non-target arith registers unchanged. Single-write div/rem need
  -- no peel; arg/sdiv/out peel the single io write `a0`.
  rf-other : ∀ i s x → (∀ d → tgt i ≡ just d → ¬ (x ≡ d))
           → rr (EA.exec1 val-riscv64 N i s) (arith-reg x) ≡ rr s (arith-reg x)
  rf-other (XI.Xmov-imm d z) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-imm d z) s) (¬d≡x d x h)
  rf-other (XI.Xmov-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xmov-m-r d sc) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xmov-m-r d sc) s) (¬d≡x d x h)
  rf-other (XI.Xmov-arg d p) s x h =
    trans (readReg-wr-a0-arith (writeReg (regs s) (arith-reg d) (V (XI.Xmov-arg d p) s)) x (V (XI.Xmov-arg d p) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xmov-arg d p) s) (¬d≡x d x h))
  rf-other (XI.Xadd-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xadd-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xsub-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xsub-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Ximul-rr d src) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Ximul-rr d src) s) (¬d≡x d x h)
  rf-other (XI.Xneg-r d) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xneg-r d) s) (¬d≡x d x h)
  rf-other (XI.Xshl-rri d src imm) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xshl-rri d src imm) s) (¬d≡x d x h)
  rf-other (XI.Xdiv-rrr d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-rrr d a b) s) (¬d≡x d x h)
  rf-other (XI.Xrem-rrr d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xrem-rrr d a b) s) (¬d≡x d x h)
  rf-other (XI.Xdiv-safe-rrr d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xdiv-safe-rrr d a b) s) (¬d≡x d x h)
  rf-other (XI.Xrem-safe-rrr d a b) s x h = readReg-wr-arith-other (regs s) d x (V (XI.Xrem-safe-rrr d a b) s) (¬d≡x d x h)
  rf-other (XI.Xsdiv-pow2-rri d src imm) s x h =
    trans (readReg-wr-a0-arith (writeReg (regs s) (arith-reg d) (V (XI.Xsdiv-pow2-rri d src imm) s)) x (V (XI.Xsdiv-pow2-rri d src imm) s))
          (readReg-wr-arith-other (regs s) d x (V (XI.Xsdiv-pow2-rri d src imm) s) (¬d≡x d x h))
  rf-other (XI.Xmov-r-m sc src) s x h = refl
  rf-other (XI.Xmov-out src) s x h = readReg-wr-a0-arith (regs s) x (V (XI.Xmov-out src) s)

  open Core
    State Reg
    rr mem
    arith-reg a0
    def (λ _ → refl)
    scratch-addr path-load
    (EA.exec1 val-riscv64 N) (EA.exec-arith-block val-riscv64 N)
    (λ _ → refl) (λ _ _ _ → refl)
    rf-other
    -- rt-mov-imm rt-mov-rr rt-reload
    (λ d z s   → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d sc s   → readReg-wr-arith-same (regs s) d _)
    -- rt-arg (peel a0)
    (λ d p s    → trans (readReg-wr-a0-arith (writeReg (regs s) (arith-reg d) _) d _)
                        (readReg-wr-arith-same (regs s) d _))
    -- rt-add rt-sub rt-imul
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    (λ d src s  → readReg-wr-arith-same (regs s) d _)
    -- rt-neg rt-shl
    (λ d s      → readReg-wr-arith-same (regs s) d _)
    (λ d src imm s → readReg-wr-arith-same (regs s) d _)
    -- rt-div rt-rem rt-div-safe rt-rem-safe (single write — no peel)
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)
    (λ d a b s  → readReg-wr-arith-same (regs s) d _)
    -- rt-sdiv (peel a0)
    (λ d src imm s → trans (readReg-wr-a0-arith (writeReg (regs s) (arith-reg d) _) d _)
                           (readReg-wr-arith-same (regs s) d _))
    -- rt-out
    (λ src s    → readReg-wr-a0-same (regs s) _)
    public
