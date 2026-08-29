-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-32.Emit
--
-- Plan 0.53 — x86-32 arith-block emitter. Mirrors
-- `Once.Arith.Backend.X86-64.Emit` (x86-64) with i386 conventions.
--
-- Calling convention (matching the rest of Once's x86-32 codegen):
--   - `%ecx` holds the block input value pointer (Input1). A primitive Int
--     lives at `0(%ecx)`; a nested pair's `Fst`/`Snd` map to byte offsets
--     `0` / `4` (4-byte i386 words).
--   - The Int result is returned in `%eax` (Output); `%eax` also doubles as
--     the path-walk scratch.
--   - The 4 abstract arith registers (`AbsReg 0..3`) map to `%edx`, `%edi`,
--     `%ebx`, `%esi`. `%ebx` (closure) and `%esi` (heap) are GLOBAL in the
--     wider codegen, so the block saves/restores them (push/pop). `%edx` and
--     `%edi` are free (Scratch / Count, dead across a SigOp call).
--   - Scratch stack slots live at `4*slot(%esp)` within a reserved frame.
--     The block is a leaf (no calls), so it needs no return-address save
--     beyond what `ret` already handles.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-32.Emit where

open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat using (ℕ; suc; _*_; _∸_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Once.Float.Decimal using (round)
open import Once.Float.Dyadic using (binary32)
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

open import Once.Target.X86-32.PhysReg using (Reg; edx; edi; ebx; esi; showReg; owner; RegClass; ccc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ia32 is register-POOR: CCC live-uses all 8 GPRs, so there are NO CCC-free
-- registers. The arith block BORROWS edx/edi/ebx/esi (all `ccc`-owned) from the
-- single shared `Once.Target.X86-32.PhysReg` and PRESERVES them by save/restore
-- (the push/pop in the block framing below). So — unlike x86-64/riscv — the
-- honest fact is `arith-borrows : owner (arith-reg x) ≡ ccc`, marking that
-- PreservesCCC here is restore-correctness, not disjointness.
arith-reg : XReg → Reg
arith-reg XR0 = edx
arith-reg XR1 = edi

arith-borrows : ∀ x → owner (arith-reg x) ≡ ccc
arith-borrows XR0 = refl
arith-borrows XR1 = refl

reg-text : XReg → String
reg-text x = showReg (arith-reg x)

-- | A scratch slot lives at `4*slot(%esp)` within the reserved frame.
scratch-text : XScratch → String
scratch-text record { slot = s } =
  showℕ (4 * s) ++ "(%esp)"

------------------------------------------------------------------------
-- Per-instruction text
------------------------------------------------------------------------

instr-text : XInstr → String
instr-text (Xmov-imm dst z)   = "    movl $" ++ showℤ z ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-rr dst src)  = "    movl " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-r-m s src)   = "    movl " ++ reg-text src ++ ", " ++ scratch-text s ++ "\n"
instr-text (Xmov-m-r dst s)   = "    movl " ++ scratch-text s ++ ", " ++ reg-text dst ++ "\n"
-- A float leaf is loaded exactly as an integer one is.
instr-text (Xmov-farg dst path) = instr-text (Xmov-arg dst path)
instr-text (Xmov-arg dst path) = path-load-text dst path
  where
    side-offset : Side → String
    side-offset Fst = "0"
    side-offset Snd = "4"

    walk-eax-rest : XReg → InputPath → String
    walk-eax-rest dst (s ∷ []) =
      "    movl " ++ side-offset s ++ "(%eax), " ++ reg-text dst ++ "\n"
    walk-eax-rest dst (s ∷ ss) =
      "    movl " ++ side-offset s ++ "(%eax), %eax\n" ++ walk-eax-rest dst ss
    walk-eax-rest dst []       = ""

    path-load-text : XReg → InputPath → String
    path-load-text dst []         =
      "    movl %ecx, " ++ reg-text dst ++ "\n"
    path-load-text dst (s ∷ [])   =
      "    movl " ++ side-offset s ++ "(%ecx), " ++ reg-text dst ++ "\n"
    path-load-text dst (s ∷ rest) =
      "    movl " ++ side-offset s ++ "(%ecx), %eax\n" ++
      walk-eax-rest dst rest
instr-text (Xadd-rr dst src)  = "    addl " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xsub-rr dst src)  = "    subl " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Ximul-rr dst src) = "    imull " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
-- D055 total signed division. `idivl` uses edx:eax implicitly; since %edx is
-- an arith register (XR0) here, the divisor is stashed on the stack so
-- `cltd`/`idivl` can freely clobber %edx, and both operands are read before
-- any clobber. Result in %eax. Guards div-by-0 and INT_MIN/-1 (both #DE).
instr-text (Xdiv-rrr dst a b) =
     "    pushl " ++ reg-text b ++ "\n" ++
     "    movl " ++ reg-text a ++ ", %eax\n" ++
     "    cmpl $0, (%esp)\n" ++
     "    jne 1f\n" ++
     "    movl $-1, %eax\n" ++            -- a / 0 = -1
     "    jmp 3f\n" ++
     "1:\n" ++
     "    cmpl $-1, (%esp)\n" ++
     "    jne 2f\n" ++
     "    cmpl $0x80000000, %eax\n" ++
     "    jne 2f\n" ++
     "    movl $0x80000000, %eax\n" ++    -- INT_MIN / -1 = INT_MIN
     "    jmp 3f\n" ++
     "2:\n" ++
     "    cltd\n" ++
     "    idivl (%esp)\n" ++
     "3:\n" ++
     "    addl $4, %esp\n" ++
     "    movl %eax, " ++ reg-text dst ++ "\n"
instr-text (Xrem-rrr dst a b) =
     "    pushl " ++ reg-text b ++ "\n" ++
     "    movl " ++ reg-text a ++ ", %eax\n" ++
     "    cmpl $0, (%esp)\n" ++
     "    jne 1f\n" ++
     "    jmp 3f\n" ++                    -- a % 0 = a  (a already in %eax)
     "1:\n" ++
     "    cmpl $-1, (%esp)\n" ++
     "    jne 2f\n" ++
     "    cmpl $0x80000000, %eax\n" ++
     "    jne 2f\n" ++
     "    xorl %eax, %eax\n" ++           -- INT_MIN % -1 = 0
     "    jmp 3f\n" ++
     "2:\n" ++
     "    cltd\n" ++
     "    idivl (%esp)\n" ++
     "    movl %edx, %eax\n" ++           -- remainder is in %edx
     "3:\n" ++
     "    addl $4, %esp\n" ++
     "    movl %eax, " ++ reg-text dst ++ "\n"
-- Guard-ELIDED div/rem (divisor a compile-time-safe literal, ≠ 0, ≠ −1 — see
-- `compile-go`'s `safe-divisor?`). BARE cltd/idivl, no #DE guard. The divisor
-- is still stashed on the stack so cltd/idivl may freely clobber %edx (an arith
-- register), and both operands are read before any clobber.
instr-text (Xdiv-safe-rrr dst a b) =
     "    pushl " ++ reg-text b ++ "\n" ++
     "    movl " ++ reg-text a ++ ", %eax\n" ++
     "    cltd\n" ++
     "    idivl (%esp)\n" ++
     "    addl $4, %esp\n" ++
     "    movl %eax, " ++ reg-text dst ++ "\n"
instr-text (Xrem-safe-rrr dst a b) =
     "    pushl " ++ reg-text b ++ "\n" ++
     "    movl " ++ reg-text a ++ ", %eax\n" ++
     "    cltd\n" ++
     "    idivl (%esp)\n" ++
     "    movl %edx, %eax\n" ++           -- remainder is in %edx
     "    addl $4, %esp\n" ++
     "    movl %eax, " ++ reg-text dst ++ "\n"
-- Strength-reduced multiply by a power-of-two literal: left shift by `imm`
-- (32-bit widths; `imm ≤ 30 < 32`, so the shift count is in range).
instr-text (Xshl-rri dst src imm) =
     "    movl " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n" ++
     "    sall $" ++ showℕ imm ++ ", " ++ reg-text dst ++ "\n"
-- Strength-reduced signed divide by `2^imm` (truncate toward zero) — the
-- branchless sign-bias idiom realising `sdiv2ᵏ` at 32-bit width. `%eax` is
-- the path-walk scratch (never an arith register). bias = (src<0 ? 2^imm−1 :
-- 0), then arithmetic-shift-right (src + bias) by imm. `src` read twice
-- before `dst` is written, so correct even when `dst ≡ src`.
instr-text (Xsdiv-pow2-rri dst src imm) =
     "    movl " ++ reg-text src ++ ", %eax\n" ++
     "    sarl $31, %eax\n" ++                                  -- eax = src<0 ? -1 : 0
     "    shrl $" ++ showℕ (32 ∸ imm) ++ ", %eax\n" ++          -- eax = src<0 ? 2^imm−1 : 0
     "    addl " ++ reg-text src ++ ", %eax\n" ++               -- eax = src + bias
     "    sarl $" ++ showℕ imm ++ ", %eax\n" ++                 -- eax = quotient
     "    movl %eax, " ++ reg-text dst ++ "\n"
instr-text (Xneg-r dst)       = "    negl " ++ reg-text dst ++ "\n"

------------------------------------------------------------------------
-- PLAN 0.75 F4: the float instructions, at BINARY32.
--
-- The format is the target's, and here it is the narrow one — which is the
-- whole point of D113's parameterisation: the same `Decimal` payload rounds
-- to four bytes here and eight on x86-64, from one `round`.
--
-- STILL OWED (D055's rule): the NaN canonicalising fixup, as on x86-64.
------------------------------------------------------------------------
instr-text (Xfadd-rr dst src) =
  "    movd " ++ reg-text dst ++ ", %xmm0\n" ++
  "    movd " ++ reg-text src ++ ", %xmm1\n" ++
  "    addss %xmm1, %xmm0\n" ++
  "    movd %xmm0, " ++ reg-text dst ++ "\n"
instr-text (Xfsub-rr dst src) =
  "    movd " ++ reg-text dst ++ ", %xmm0\n" ++
  "    movd " ++ reg-text src ++ ", %xmm1\n" ++
  "    subss %xmm1, %xmm0\n" ++
  "    movd %xmm0, " ++ reg-text dst ++ "\n"
instr-text (Xfsubr-rr dst src) =
  "    movd " ++ reg-text src ++ ", %xmm0\n" ++
  "    movd " ++ reg-text dst ++ ", %xmm1\n" ++
  "    subss %xmm1, %xmm0\n" ++
  "    movd %xmm0, " ++ reg-text dst ++ "\n"
instr-text (Xfmul-rr dst src) =
  "    movd " ++ reg-text dst ++ ", %xmm0\n" ++
  "    movd " ++ reg-text src ++ ", %xmm1\n" ++
  "    mulss %xmm1, %xmm0\n" ++
  "    movd %xmm0, " ++ reg-text dst ++ "\n"
-- Three-address, so both sources are read into the FP scratch pair BEFORE
-- the destination is written — which is what lets `dst` alias `b`.
instr-text (Xfdiv-rrr dst a b) =
  "    movd " ++ reg-text a ++ ", %xmm0\n" ++
  "    movd " ++ reg-text b ++ ", %xmm1\n" ++
  "    divss %xmm1, %xmm0\n" ++
  "    movd %xmm0, " ++ reg-text dst ++ "\n"
instr-text (Xfneg-r dst) =
  "    xorl $-2147483648, " ++ reg-text dst ++ "\n"
instr-text (Xi2f-r dst src) =
  "    cvtsi2ssl " ++ reg-text src ++ ", %xmm0\n" ++
  "    movd %xmm0, " ++ reg-text dst ++ "\n"
instr-text (Xmov-fimm dst dc) =
  "    movl $" ++ showℕ (round binary32 dc) ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-out src)     = "    movl " ++ reg-text src ++ ", %eax\n"

program-text : XProgram → String
program-text []       = ""
program-text (i ∷ is) = instr-text i ++ program-text is

------------------------------------------------------------------------
-- Block subroutine emission
------------------------------------------------------------------------

-- | A complete arith-block subroutine. Saves/restores the two borrowed
-- global registers (%ebx = closure, %esi = heap) around the body, and
-- reserves `4 * required-scratch` bytes of scratch below them.
--
--   <sym>:
--       pushl %ebx ; pushl %esi        ; save borrowed abstract regs
--       subl $N, %esp                  ; reserve scratch
--       <emitted instructions>
--       addl $N, %esp
--       popl %esi ; popl %ebx
--       ret
emit-arith-block : (sym : String) → ArithBlock → String
-- DESTRUCTURED, not `with block-kind blk`: with-abstraction on one
-- projection of a record does not refine another projection's TYPE, so
-- `body` would stay at the abstract kind. The pattern refines both.
emit-arith-block sym (mk-block sh NInt body) =
    let nbody = normalize body   -- div-guard elision + degenerate folds
        n     = required-scratch nbody
        pad   = showℕ (4 * n)
        instr = emit-program (compile-abs nbody)
    in sym ++ ":\n" ++
       -- Save ALL four borrowed abstract-reg registers: %ebx (closure) and
       -- %esi (heap) are global; %edx (Scratch) and %edi (Count) are the
       -- CCC reg-op registers, live across a cata loop whose algebra calls
       -- this block. Clobbering %edx would corrupt the loop counter.
       "    pushl %ebx\n" ++
       "    pushl %esi\n" ++
       "    pushl %edx\n" ++
       "    pushl %edi\n" ++
       "    subl $" ++ pad ++ ", %esp\n" ++
       program-text instr ++
       "    addl $" ++ pad ++ ", %esp\n" ++
       "    popl %edi\n" ++
       "    popl %edx\n" ++
       "    popl %esi\n" ++
       "    popl %ebx\n" ++
       "    ret\n\n"
emit-arith-block sym (mk-block sh NFloat body) =
    let nbody = body             -- no `normalize`: it is the div-guard /
        --                           degenerate-divisor pre-pass, and both are
        --                           Int-only by type — a float tree has no
        --                           `adiv`/`amod` to fold.
        n     = required-scratch nbody
        pad   = showℕ (4 * n)
        instr = emit-program (compile-abs nbody)
    in sym ++ ":\n" ++
       -- Save ALL four borrowed abstract-reg registers: %ebx (closure) and
       -- %esi (heap) are global; %edx (Scratch) and %edi (Count) are the
       -- CCC reg-op registers, live across a cata loop whose algebra calls
       -- this block. Clobbering %edx would corrupt the loop counter.
       "    pushl %ebx\n" ++
       "    pushl %esi\n" ++
       "    pushl %edx\n" ++
       "    pushl %edi\n" ++
       "    subl $" ++ pad ++ ", %esp\n" ++
       program-text instr ++
       "    addl $" ++ pad ++ ", %esp\n" ++
       "    popl %edi\n" ++
       "    popl %edx\n" ++
       "    popl %esi\n" ++
       "    popl %ebx\n" ++
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
