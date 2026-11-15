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

open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat using (ℕ; _*_; _∸_; _<ᵇ_)
open import Data.Bool using (true; false)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Once.Float.Word using (round)
open import Once.Spec.Float.Dyadic using (binary64)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.CmpOp using (c-lt; c-le; c-gt; c-ge; c-eq; c-ne; FCmpOp; fcmp)
open import Once.Spec.Theory
  using (float-rounded; float-order; float-equality; ‵==ᵈ; ‵!=ᵈ; ‵<ᵈ; ‵<=ᵈ; ‵>ᵈ; ‵>=ᵈ; ‵<; ‵<=; ‵>; ‵>=; ‵==; ‵!=)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.Shape using (InputPath; Side; Fst; Snd)
open import Once.Arith.Machine.Compile using (compile-abs; required-scratch; normalize)
open import Once.Arith.Type using (NInt; NFloat)
open import Once.Arith.Machine.IR using (ArithBlock; mk-block)
open Once.Arith.Machine.IR.ArithBlock using (block-body)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Target.Symbol using (once-symbol-own)

------------------------------------------------------------------------
-- Register / scratch text
------------------------------------------------------------------------

open import Once.Target.RiscV64.PhysReg using (Reg; a3; a4; showReg; owner)
open import Once.Target.RegConvention using (arith)
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

-- D391: a leaf of the flat input (D381) is ONE doubleword at its offset `k` from
-- the input pointer `t0`; a whole-input scalar (`[]`) is `t0` itself. An offset
-- past the 12-bit immediate is formed in `dst` (no other register written).
------------------------------------------------------------------------
-- plan 0.150: the FLOAT COMPARISONS (`Xfcmp-rrr`), at binary64.
--
-- Both operands go to `ft0`/`ft1` FIRST; after that `a`/`b` are never read,
-- so `dst` is free scratch even when it aliases one of them. The only other
-- register written is the io scratch `a0` (the `Xsdiv-pow2-rri` footprint,
-- `Confine.writes`); the IEEE row writes `dst` alone.
--
-- IEEE row: `flt.d`/`fle.d`/`feq.d` (0 on NaN), operands swapped for `>.`/
-- `>=.`, `!=.` the negated `feq.d`.
--
-- Order row (totalOrder: −∞ < … < −0 < +0 < … < +∞ < NaN): each operand's
-- pattern, NaN replaced by THE canonical NaN `0x7ff8000000000000` (`feq.d
-- f, f` is 0 exactly on NaN), is mapped to a SIGNED-sortable key
-- `w xor ((w srai 63) srli 1)` — a non-negative pattern is unchanged, a
-- negative one keeps its sign and complements the rest. (This is the
-- unsigned key `w xor ((w srai 63) or 1<<63)` with bit 63 flipped, so `slt`
-- on it IS `sltu` on that one; it needs no second scratch for the constant.)
-- `b`'s key is computed in `a0` (temp `dst`) and parked bit-exactly in `ft1`
-- (`fmv` is a raw move), `a`'s key then lands in `a0`, `b`'s back in `dst`.
-- Identity row (NaN == NaN, −0 ≠ +0): the same with no key, then `xor` and
-- `seqz`/`snez`.
------------------------------------------------------------------------

-- | The NaN-canonical pattern of `ft` into `a0`, testing through `dst`,
-- labels `l1`/`l2`.
fcanon-rv : String → String → String → String → String
fcanon-rv d ft l1 l2 =
  "    feq.d " ++ d ++ ", " ++ ft ++ ", " ++ ft ++ "\n" ++
  "    bnez " ++ d ++ ", " ++ l1 ++ "f\n" ++
  "    li a0, 0x7ff8000000000000\n" ++
  "    j " ++ l2 ++ "f\n" ++
  l1 ++ ":\n" ++
  "    fmv.x.d a0, " ++ ft ++ "\n" ++
  l2 ++ ":\n"

-- | The signed-sortable key of `a0`, in place (temp `dst`).
fkey-rv : String → String
fkey-rv d =
  "    srai " ++ d ++ ", a0, 63\n" ++
  "    srli " ++ d ++ ", " ++ d ++ ", 1\n" ++
  "    xor a0, a0, " ++ d ++ "\n"

fload-rv : String → String → String
fload-rv a b =
  "    fmv.d.x ft0, " ++ a ++ "\n" ++
  "    fmv.d.x ft1, " ++ b ++ "\n"

-- | Keys: `a`'s in `a0`, `b`'s in `dst`.
fkeys-rv : String → String → String → String
fkeys-rv d a b =
  fload-rv a b ++
  fcanon-rv d "ft1" "1" "2" ++ fkey-rv d ++
  "    fmv.d.x ft1, a0\n" ++
  fcanon-rv d "ft0" "3" "4" ++ fkey-rv d ++
  "    fmv.x.d " ++ d ++ ", ft1\n"

-- | Canonical patterns: `a`'s in `a0`, `b`'s in `dst`.
fcanons-rv : String → String → String → String
fcanons-rv d a b =
  fload-rv a b ++
  fcanon-rv d "ft1" "1" "2" ++
  "    fmv.d.x ft1, a0\n" ++
  fcanon-rv d "ft0" "3" "4" ++
  "    fmv.x.d " ++ d ++ ", ft1\n"

fcmp-text-rv : FCmpOp → (dst a b : String) → String
fcmp-text-rv (fcmp float-rounded ‵<ᵈ) d a b =
  fload-rv a b ++ "    flt.d " ++ d ++ ", ft0, ft1\n"
fcmp-text-rv (fcmp float-rounded ‵<=ᵈ) d a b =
  fload-rv a b ++ "    fle.d " ++ d ++ ", ft0, ft1\n"
fcmp-text-rv (fcmp float-rounded ‵>ᵈ) d a b =
  fload-rv a b ++ "    flt.d " ++ d ++ ", ft1, ft0\n"
fcmp-text-rv (fcmp float-rounded ‵>=ᵈ) d a b =
  fload-rv a b ++ "    fle.d " ++ d ++ ", ft1, ft0\n"
fcmp-text-rv (fcmp float-rounded ‵==ᵈ) d a b =
  fload-rv a b ++ "    feq.d " ++ d ++ ", ft0, ft1\n"
fcmp-text-rv (fcmp float-rounded ‵!=ᵈ) d a b =
  fload-rv a b ++ "    feq.d " ++ d ++ ", ft0, ft1\n" ++
  "    xori " ++ d ++ ", " ++ d ++ ", 1\n"
fcmp-text-rv (fcmp float-order ‵<) d a b =
  fkeys-rv d a b ++ "    slt " ++ d ++ ", a0, " ++ d ++ "\n"
fcmp-text-rv (fcmp float-order ‵>) d a b =
  fkeys-rv d a b ++ "    slt " ++ d ++ ", " ++ d ++ ", a0\n"
fcmp-text-rv (fcmp float-order ‵<=) d a b =
  fkeys-rv d a b ++ "    slt " ++ d ++ ", " ++ d ++ ", a0\n" ++
  "    xori " ++ d ++ ", " ++ d ++ ", 1\n"
fcmp-text-rv (fcmp float-order ‵>=) d a b =
  fkeys-rv d a b ++ "    slt " ++ d ++ ", a0, " ++ d ++ "\n" ++
  "    xori " ++ d ++ ", " ++ d ++ ", 1\n"
fcmp-text-rv (fcmp float-equality ‵==) d a b =
  fcanons-rv d a b ++ "    xor " ++ d ++ ", a0, " ++ d ++ "\n" ++
  "    seqz " ++ d ++ ", " ++ d ++ "\n"
fcmp-text-rv (fcmp float-equality ‵!=) d a b =
  fcanons-rv d a b ++ "    xor " ++ d ++ ", a0, " ++ d ++ "\n" ++
  "    snez " ++ d ++ ", " ++ d ++ "\n"

arg-load-text : XReg → InputPath → ℕ → String
arg-load-text dst [] _ = "    mv " ++ reg-text dst ++ ", t0\n"
arg-load-text dst (_ ∷ _) k with (8 * k) <ᵇ 2048
... | true  = "    ld " ++ reg-text dst ++ ", " ++ showℕ (8 * k) ++ "(t0)\n"
... | false = "    li " ++ reg-text dst ++ ", " ++ showℕ (8 * k) ++ "\n" ++
              "    add " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", t0\n" ++
              "    ld " ++ reg-text dst ++ ", 0(" ++ reg-text dst ++ ")\n"

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
-- Three-address, so both sources are read into the FP scratch pair BEFORE
-- the destination is written — which is what lets `dst` alias `b`.
instr-text (Xfdiv-rrr dst a b) =
  "    fmv.d.x ft0, " ++ reg-text a ++ "\n" ++
  "    fmv.d.x ft1, " ++ reg-text b ++ "\n" ++
  "    fdiv.d ft0, ft0, ft1\n" ++
  "    fmv.x.d " ++ reg-text dst ++ ", ft0\n"
instr-text (Xfcmp-rrr o dst a b) = fcmp-text-rv o (reg-text dst) (reg-text a) (reg-text b)
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
instr-text (Xmov-farg dst path k) = arg-load-text dst path k
instr-text (Xmov-arg dst path k)  = arg-load-text dst path k
instr-text (Xadd-rr dst src)  = "    add " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
instr-text (Xsub-rr dst src)  = "    sub " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
instr-text (Ximul-rr dst src) = "    mul " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
-- RV64M `div`/`rem` are signed and TOTAL by spec (D055): div-by-zero → -1
-- (quotient) / dividend (remainder); INT_MIN/-1 → INT_MIN / 0. Clean 1-1.
-- plan 0.108: a SIGNED comparison into a 0/1 word. `slt` reads both operands
-- before it writes, so `dst` may alias either; `≤`/`≥` are the negated `slt`,
-- `=`/`≠` the zero test of the difference.
instr-text (Xcmp-rrr c-lt dst a b) = "    slt " ++ reg-text dst ++ ", " ++ reg-text a ++ ", " ++ reg-text b ++ "\n"
instr-text (Xcmp-rrr c-gt dst a b) = "    slt " ++ reg-text dst ++ ", " ++ reg-text b ++ ", " ++ reg-text a ++ "\n"
instr-text (Xcmp-rrr c-le dst a b) =
  "    slt " ++ reg-text dst ++ ", " ++ reg-text b ++ ", " ++ reg-text a ++ "\n" ++
  "    xori " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", 1\n"
instr-text (Xcmp-rrr c-ge dst a b) =
  "    slt " ++ reg-text dst ++ ", " ++ reg-text a ++ ", " ++ reg-text b ++ "\n" ++
  "    xori " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", 1\n"
instr-text (Xcmp-rrr c-eq dst a b) =
  "    sub " ++ reg-text dst ++ ", " ++ reg-text a ++ ", " ++ reg-text b ++ "\n" ++
  "    seqz " ++ reg-text dst ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xcmp-rrr c-ne dst a b) =
  "    sub " ++ reg-text dst ++ ", " ++ reg-text a ++ ", " ++ reg-text b ++ "\n" ++
  "    snez " ++ reg-text dst ++ ", " ++ reg-text dst ++ "\n"
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
-- Plan 0.107: THE BLOCK'S PAYLOAD — its instructions and its scratch need. The
-- one definition both the printer (`emit-payload`) and the decoded file's block
-- table (`Target.RiscV64.File`) read, so the text and the model cannot differ.
-- DESTRUCTURED, not `with block-kind blk`: with-abstraction on one projection of
-- a record does not refine another projection's TYPE, so `body` would stay at
-- the abstract kind. The pattern refines both.
block-payload : ArithBlock → XProgram × ℕ
block-payload (mk-block sh NInt body) =
  let nbody = normalize body   -- div-guard elision + degenerate folds
  in emit-program (compile-abs nbody) , required-scratch nbody
block-payload (mk-block sh NFloat body) =
  -- no `normalize`: it is the div-guard / degenerate-divisor pre-pass, and both
  -- are Int-only by type — a float tree has no `adiv`/`amod` to fold.
  emit-program (compile-abs body) , required-scratch body

emit-payload : (sym : String) → XProgram × ℕ → String
emit-payload sym (instr , n) =
  let pad = showℕ (8 * n)
  in sym ++ ":\n" ++
     "    addi sp, sp, -" ++ pad ++ "\n" ++
     program-text instr ++
     "    addi sp, sp, " ++ pad ++ "\n" ++
     "    ret\n\n"

emit-arith-block : (sym : String) → ArithBlock → String
emit-arith-block sym blk = emit-payload sym (block-payload blk)

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
