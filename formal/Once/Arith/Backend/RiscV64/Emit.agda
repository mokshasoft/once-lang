-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.Emit
--
-- Plan 0.53 — RISC-V 64 arith-block emitter. Mirrors
-- `Once.Arith.Backend.X86-64.Emit`: translate the arch-independent arith
-- `XInstr` IR to RV64 assembly text and assemble a leaf block subroutine
-- (prologue + body + epilogue).
--
-- Calling convention (matching the rest of Once's RV64 codegen):
--   - `t0` holds the block input value pointer (Input1). A primitive Int
--     lives at `0(t0)`; a nested pair's `Fst`/`Snd` map to byte offsets
--     `0` / `8`.
--   - The Int result is returned in `a0` (Output).
--   - The abstract reg file XR0..XR3 maps to a3/a4/a5 (CCC-free; see arith-reg
--     + Once.Target.RiscV64.PhysReg). `a0` doubles as
--     the path-walk scratch. All are caller-saved at the SigOp call site.
--   - Scratch stack slots live at `8*slot(sp)` after the prologue reserves
--     `8 * required-scratch` bytes. The block is a leaf (no calls), so it
--     needs no `ra` save.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.Emit where

open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat using (ℕ; suc; _*_; _∸_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Once.Float.Decimal using (round)
open import Once.Float.Dyadic using (binary64)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.AbsState using (InputPath; Side; Fst; Snd)
open import Once.Arith.Machine.Compile using (compile-abs; required-scratch; normalize)
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR using (MArithIR; ArithBlock; mk-block)
open Once.Arith.Machine.IR.ArithBlock using (block-shape; block-kind; block-body)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Target.Symbol using (once-symbol-own)

------------------------------------------------------------------------
-- Register / scratch text
------------------------------------------------------------------------

open import Once.Target.RiscV64.PhysReg using (Reg; a3; a4; a5; showReg; owner; RegClass; arith)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- XR0..XR3 acquire the CCC-free caller-saved argument registers a3/a4/a5 from
-- the single shared `Once.Target.RiscV64.PhysReg` declaration (Plan 0.55).
-- Only 3 registers are CCC-free on RV64, and `compile-go` emits only XR0/XR1
-- (compile-abs-bound), so the dead XR2/XR3 alias a5 — never actually emitted.
-- `arith-disjoint` is a `refl`, so non-clobbering is definitional (replacing the
-- old — false — comment that t1-t4 were free: CCC emits t1 ~45×).
arith-reg : XReg → Reg
arith-reg XR0 = a3
arith-reg XR1 = a4

arith-disjoint : ∀ x → owner (arith-reg x) ≡ arith
arith-disjoint XR0 = refl
arith-disjoint XR1 = refl

reg-text : XReg → String
reg-text x = showReg (arith-reg x)

-- | A scratch slot lives at `8*slot(sp)` within the reserved frame.
scratch-text : XScratch → String
scratch-text record { slot = s } =
  showℕ (8 * s) ++ "(sp)"

------------------------------------------------------------------------
-- Per-instruction text
------------------------------------------------------------------------

instr-text : XInstr → String
instr-text (Xmov-imm dst z)   = "    li " ++ reg-text dst ++ ", " ++ showℤ z ++ "\n"
instr-text (Xmov-rr dst src)  = "    mv " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"

------------------------------------------------------------------------
-- PLAN 0.75 F4: the float instructions.
--
-- Values live in GPRs between operations and move to `ft*` only for the
-- operation, so spill/reload stay the `sd`/`ld` they already are. RISC-V is
-- NATIVE for D055's NaN rule: `fadd.d` already produces the canonical NaN and
-- never propagates a payload, so nothing has to be fixed up here — the cost
-- lands on x86, exactly as the div guard does.
------------------------------------------------------------------------
instr-text (Xfadd-rr dst src) =
  "    fmv.d.x ft0, " ++ reg-text dst ++ "\n" ++
  "    fmv.d.x ft1, " ++ reg-text src ++ "\n" ++
  "    fadd.d ft0, ft0, ft1\n" ++
  "    fmv.x.d " ++ reg-text dst ++ ", ft0\n"
instr-text (Xfsub-rr dst src) =
  "    fmv.d.x ft0, " ++ reg-text dst ++ "\n" ++
  "    fmv.d.x ft1, " ++ reg-text src ++ "\n" ++
  "    fsub.d ft0, ft0, ft1\n" ++
  "    fmv.x.d " ++ reg-text dst ++ ", ft0\n"
instr-text (Xfsubr-rr dst src) =
  "    fmv.d.x ft0, " ++ reg-text src ++ "\n" ++
  "    fmv.d.x ft1, " ++ reg-text dst ++ "\n" ++
  "    fsub.d ft0, ft0, ft1\n" ++
  "    fmv.x.d " ++ reg-text dst ++ ", ft0\n"
instr-text (Xfmul-rr dst src) =
  "    fmv.d.x ft0, " ++ reg-text dst ++ "\n" ++
  "    fmv.d.x ft1, " ++ reg-text src ++ "\n" ++
  "    fmul.d ft0, ft0, ft1\n" ++
  "    fmv.x.d " ++ reg-text dst ++ ", ft0\n"
instr-text (Xfneg-r dst) =
  "    fmv.d.x ft0, " ++ reg-text dst ++ "\n" ++
  "    fneg.d ft0, ft0\n" ++
  "    fmv.x.d " ++ reg-text dst ++ ", ft0\n"
instr-text (Xi2f-r dst src) =
  "    fcvt.d.l ft0, " ++ reg-text src ++ "\n" ++
  "    fmv.x.d " ++ reg-text dst ++ ", ft0\n"
instr-text (Xmov-fimm dst dc) =
  "    li " ++ reg-text dst ++ ", " ++ showℕ (round binary64 dc) ++ "\n"
instr-text (Xmov-r-m s src)   = "    sd " ++ reg-text src ++ ", " ++ scratch-text s ++ "\n"
instr-text (Xmov-m-r dst s)   = "    ld " ++ reg-text dst ++ ", " ++ scratch-text s ++ "\n"
-- A float leaf is loaded exactly as an integer one is.
instr-text (Xmov-farg dst path) = instr-text (Xmov-arg dst path)
instr-text (Xmov-arg dst path) = path-load-text dst path
  where
    -- Byte offset for one path step (matches CCC's pair layout).
    side-offset : Side → String
    side-offset Fst = "0"
    side-offset Snd = "8"

    -- Walk intermediate steps using a0 as base; final step lands in dst.
    walk-a0-rest : XReg → InputPath → String
    walk-a0-rest dst (s ∷ []) =
      "    ld " ++ reg-text dst ++ ", " ++ side-offset s ++ "(a0)\n"
    walk-a0-rest dst (s ∷ ss) =
      "    ld a0, " ++ side-offset s ++ "(a0)\n" ++ walk-a0-rest dst ss
    walk-a0-rest dst []       = ""

    -- Top-level path walker. `[]` = the input pointer t0 IS the value.
    path-load-text : XReg → InputPath → String
    path-load-text dst []         =
      "    mv " ++ reg-text dst ++ ", t0\n"
    path-load-text dst (s ∷ [])   =
      "    ld " ++ reg-text dst ++ ", " ++ side-offset s ++ "(t0)\n"
    path-load-text dst (s ∷ rest) =
      "    ld a0, " ++ side-offset s ++ "(t0)\n" ++
      walk-a0-rest dst rest
instr-text (Xadd-rr dst src)  = "    add " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
instr-text (Xsub-rr dst src)  = "    sub " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
instr-text (Ximul-rr dst src) = "    mul " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
-- RV64M `div`/`rem` are signed and TOTAL by spec (D055): div-by-zero → -1
-- (quotient) / dividend (remainder); INT_MIN/-1 → INT_MIN / 0. Clean 1-1.
instr-text (Xdiv-rrr dst a b) = "    div " ++ reg-text dst ++ ", " ++ reg-text a ++ ", " ++ reg-text b ++ "\n"
instr-text (Xrem-rrr dst a b) = "    rem " ++ reg-text dst ++ ", " ++ reg-text a ++ ", " ++ reg-text b ++ "\n"
-- `-safe` variants: RV64 `div`/`rem` are already total (no #DE trap), so the
-- guard-elided form is IDENTICAL to the guarded one — a clean 1-1 map.
instr-text (Xdiv-safe-rrr dst a b) = "    div " ++ reg-text dst ++ ", " ++ reg-text a ++ ", " ++ reg-text b ++ "\n"
instr-text (Xrem-safe-rrr dst a b) = "    rem " ++ reg-text dst ++ ", " ++ reg-text a ++ ", " ++ reg-text b ++ "\n"
-- Strength-reduced multiply by a power-of-two literal: `slli` left shift by
-- `imm` (`imm ≤ 30 < 64`, so the shift count is in range).
instr-text (Xshl-rri dst src imm) =
     "    slli " ++ reg-text dst ++ ", " ++ reg-text src ++ ", " ++ showℕ imm ++ "\n"
-- Strength-reduced signed divide by `2^imm` (truncate toward zero) — the
-- sign-bias idiom realising `sdiv2ᵏ`. `a0` is the path-walk scratch (caller-
-- saved, never an arith register). bias = (src<0 ? 2^imm−1 : 0) via
-- `srai a0,src,63` (sign mask) then logical `srli a0,a0,64−imm`; then arithmetic
-- `srai` of (src + bias) by imm. `src` read twice before `dst` is written, so
-- correct even when `dst ≡ src`.
instr-text (Xsdiv-pow2-rri dst src imm) =
     "    srai a0, " ++ reg-text src ++ ", 63\n" ++             -- a0 = src<0 ? -1 : 0
     "    srli a0, a0, " ++ showℕ (64 ∸ imm) ++ "\n" ++         -- a0 = src<0 ? 2^imm−1 : 0
     "    add a0, " ++ reg-text src ++ ", a0\n" ++              -- a0 = src + bias
     "    srai " ++ reg-text dst ++ ", a0, " ++ showℕ imm ++ "\n"  -- dst = quotient
instr-text (Xneg-r dst)       = "    neg " ++ reg-text dst ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-out src)     = "    mv a0, " ++ reg-text src ++ "\n"

program-text : XProgram → String
program-text []       = ""
program-text (i ∷ is) = instr-text i ++ program-text is

------------------------------------------------------------------------
-- Block subroutine emission
------------------------------------------------------------------------

-- | A complete arith-block subroutine. Leaf (no calls) ⇒ no ra save.
--
--   <sym>:
--       addi sp, sp, -N      ; reserve scratch (N = 8 * required-scratch)
--       <emitted instructions>
--       addi sp, sp, N
--       ret
emit-arith-block : (sym : String) → ArithBlock → String
-- DESTRUCTURED, not `with block-kind blk`: with-abstraction on one
-- projection of a record does not refine another projection's TYPE, so
-- `body` would stay at the abstract kind. The pattern refines both.
emit-arith-block sym (mk-block sh NInt body) =
    let nbody = normalize body   -- div-guard elision + degenerate folds
        n     = required-scratch nbody
        pad   = showℕ (8 * n)
        instr = emit-program (compile-abs nbody)
    in sym ++ ":\n" ++
       "    addi sp, sp, -" ++ pad ++ "\n" ++
       program-text instr ++
       "    addi sp, sp, " ++ pad ++ "\n" ++
       "    ret\n\n"
emit-arith-block sym (mk-block sh NFloat body) =
    let nbody = body             -- no `normalize`: it is the div-guard /
        --                           degenerate-divisor pre-pass, and both are
        --                           Int-only by type — a float tree has no
        --                           `adiv`/`amod` to fold.
        n     = required-scratch nbody
        pad   = showℕ (8 * n)
        instr = emit-program (compile-abs nbody)
    in sym ++ ":\n" ++
       "    addi sp, sp, -" ++ pad ++ "\n" ++
       program-text instr ++
       "    addi sp, sp, " ++ pad ++ "\n" ++
       "    ret\n\n"

------------------------------------------------------------------------
-- Block-list emission
------------------------------------------------------------------------

arith-block-symbol : ArithBlock → String
arith-block-symbol blk = once-symbol-own (block-name (block-body blk))

emit-arith-blocks : List ArithBlock → String
emit-arith-blocks []       = ""
emit-arith-blocks (b ∷ bs) =
  ".globl " ++ arith-block-symbol b ++ "\n" ++
  emit-arith-block (arith-block-symbol b) b ++
  emit-arith-blocks bs
