-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.Emit
--
-- Plan 0.20 Phase G — translate the arith subsystem's `XInstr`
-- subset to AT&T-syntax x86-64 assembly text, and assemble a full
-- block subroutine (prologue + body + epilogue) ready to concatenate
-- after the main program text.
--
-- Calling convention (SysV / matching the rest of Once's codegen):
--   - `%rdi` holds the *block input value pointer*. For a primitive
--     `Int` input the value lives at `0(%rdi)`; for a nested pair the
--     `Fst`/`Snd` walk maps to byte offsets `0` and `+8`.
--   - The block's `Int` result is returned in `%rax` per the SysV
--     return-value convention. The wrapping `SigOp arith.block.*`
--     call site treats the result the same way `compile-const`
--     emits its integer literals.
--   - The abstract reg file `XR0..XR3` maps to `%r8-%r11` — acquired
--     from the single shared `Once.Target.X86-64.PhysReg` declaration
--     via `arith-reg`. These are chosen to be BOTH caller-saved (so the
--     frameless block owes no callee-save across the `call`) AND in the
--     set CCC never emits. The latter makes non-clobbering DEFINITIONAL:
--     `arith-disjoint : owner (arith-reg x) ≡ arith` is a `refl` (Plan
--     0.55), replacing the old — and, for `r12`/`r15`, false — comment
--     that claimed `r12-r15` were CCC scratch (they are CCC's closure and
--     heap-top pointers).
--   - Scratch stack slots are addressed via `[%rsp - 8*(slot+1)]`
--     after the prologue subtracts `8 * required-scratch` from
--     `%rsp`. The reservation matches `Once.Arith.Backend.XInstr.Syntax`'s
--     comment.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.Emit where

open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat using (ℕ; suc; _*_; _∸_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.AbsState using (InputPath; Side; Fst; Snd)
open import Once.Arith.Machine.Compile using (compile-abs; required-scratch; normalize)
open import Once.Arith.Machine.IR using (MArithIR; ArithBlock)
open Once.Arith.Machine.IR.ArithBlock using (block-shape; block-body)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Target.X86-64.PhysReg using (Reg; r8; r9; r10; r11; showReg; owner; RegClass; arith)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Register / scratch text
--
-- The arith block acquires its 4 working registers from the SINGLE shared
-- `Once.Target.X86-64.PhysReg` declaration (Plan 0.55), choosing registers
-- CCC never emits — so `arith-disjoint` below is a `refl`, and the
-- "does-not-clobber-CCC" property is definitional rather than assumed.
------------------------------------------------------------------------

arith-reg : XReg → Reg
arith-reg XR0 = r8
arith-reg XR1 = r9

-- Every arith working register is `arith`-owned, hence never a CCC-live
-- register (`owner`'s `ccc`/`io` classes are distinct constructors).
arith-disjoint : ∀ x → owner (arith-reg x) ≡ arith
arith-disjoint XR0 = refl
arith-disjoint XR1 = refl

reg-text : XReg → String
reg-text x = showReg (arith-reg x)

-- | A scratch slot lives at `8*slot(%rsp)` — ADDITIVE from the reserved frame
-- base, exactly like riscv64/x86-32's `8*slot(sp)`. The prologue reserves
-- `8 * required-scratch` bytes (`sub $N, %rsp`); addressing UP from the lowered
-- %rsp keeps every slot inside the reserved frame [%rsp, %rsp+N).
scratch-text : XScratch → String
scratch-text record { slot = s } =
  showℕ (8 * s) ++ "(%rsp)"

------------------------------------------------------------------------
-- Per-instruction text
------------------------------------------------------------------------

instr-text : XInstr → String
instr-text (Xmov-imm dst z)   = "    movq $" ++ showℤ z ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-rr dst src)  = "    movq " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-r-m s src)   = "    movq " ++ reg-text src ++ ", " ++ scratch-text s ++ "\n"
instr-text (Xmov-m-r dst s)   = "    movq " ++ scratch-text s ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-arg dst path) = path-load-text dst path
  where
    -- | Byte offset for one path step. `Fst` is offset 0, `Snd` is
    -- offset 8 — matching CCC's pair layout (compose `fst`/`snd`
    -- compile to `mov rax, [rdi]` / `mov rax, [rdi+8]`).
    side-offset : Side → String
    side-offset Fst = "0"
    side-offset Snd = "8"

    -- | Walk an intermediate path step using `%rax` as scratch.
    -- After the first step `%rax` holds the current "base"; each
    -- intermediate step reads `offset(%rax)` back into `%rax`. The
    -- final step lands in `dst`.
    walk-rax-rest : XReg → InputPath → String
    walk-rax-rest dst (s ∷ []) =
      "    movq " ++ side-offset s ++ "(%rax), " ++ reg-text dst ++ "\n"
    walk-rax-rest dst (s ∷ ss) =
      "    movq " ++ side-offset s ++ "(%rax), %rax\n" ++ walk-rax-rest dst ss
    -- Path [] inside an intermediate walk is unreachable for shapes
    -- that the recogniser produces; treat as a no-op fallback.
    walk-rax-rest dst []       = ""

    -- | Top-level path walker.
    --
    -- - `[]` (whole input): the block's `%rdi` IS the value (Int
    --   passed by-value through the SigOp call site). Move it to
    --   `dst`.
    -- - `[s]` (one hop): direct `mov dst, offset(%rdi)`.
    -- - `s :: rest` (chained): bootstrap into `%rax`, then walk the
    --   rest. Each `s :: rest` step does one memory dereference,
    --   matching CCC's `fst`/`snd` compose chain exactly.
    path-load-text : XReg → InputPath → String
    path-load-text dst []         =
      "    movq %rdi, " ++ reg-text dst ++ "\n"
    path-load-text dst (s ∷ [])   =
      "    movq " ++ side-offset s ++ "(%rdi), " ++ reg-text dst ++ "\n"
    path-load-text dst (s ∷ rest) =
      "    movq " ++ side-offset s ++ "(%rdi), %rax\n" ++
      walk-rax-rest dst rest
instr-text (Xadd-rr dst src)  = "    addq " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xsub-rr dst src)  = "    subq " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Ximul-rr dst src) = "    imulq " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
-- D055 total signed division. x86 `idiv` traps (#DE) on divisor 0 AND on
-- INT_MIN/-1, so we guard both cases before ever executing `idivq`.
-- Result computed in %rax; %rdx is caller-saved scratch (never an arith
-- register). GNU-as numeric local labels (`1f`/`2f`/`3f`) are per-emission
-- reusable, so multiple div/rem sequences never collide.
instr-text (Xdiv-rrr dst a b) =
     "    movq " ++ reg-text a ++ ", %rax\n" ++
     "    testq " ++ reg-text b ++ ", " ++ reg-text b ++ "\n" ++
     "    jne 1f\n" ++
     "    movq $-1, %rax\n" ++            -- a / 0 = -1
     "    jmp 3f\n" ++
     "1:\n" ++
     "    cmpq $-1, " ++ reg-text b ++ "\n" ++
     "    jne 2f\n" ++
     "    movabsq $0x8000000000000000, %rdx\n" ++
     "    cmpq %rdx, %rax\n" ++
     "    jne 2f\n" ++
     "    movq %rdx, %rax\n" ++           -- INT_MIN / -1 = INT_MIN
     "    jmp 3f\n" ++
     "2:\n" ++
     "    cqto\n" ++
     "    idivq " ++ reg-text b ++ "\n" ++
     "3:\n" ++
     "    movq %rax, " ++ reg-text dst ++ "\n"
instr-text (Xrem-rrr dst a b) =
     "    movq " ++ reg-text a ++ ", %rax\n" ++
     "    testq " ++ reg-text b ++ ", " ++ reg-text b ++ "\n" ++
     "    jne 1f\n" ++
     "    jmp 3f\n" ++                    -- a % 0 = a  (a already in %rax)
     "1:\n" ++
     "    cmpq $-1, " ++ reg-text b ++ "\n" ++
     "    jne 2f\n" ++
     "    movabsq $0x8000000000000000, %rdx\n" ++
     "    cmpq %rdx, %rax\n" ++
     "    jne 2f\n" ++
     "    xorl %eax, %eax\n" ++           -- INT_MIN % -1 = 0
     "    jmp 3f\n" ++
     "2:\n" ++
     "    cqto\n" ++
     "    idivq " ++ reg-text b ++ "\n" ++
     "    movq %rdx, %rax\n" ++           -- remainder is in %rdx
     "3:\n" ++
     "    movq %rax, " ++ reg-text dst ++ "\n"
-- Guard-ELIDED div/rem. The divisor is a compile-time-safe literal (nonzero,
-- ≠ −1, verified by `compile-go`'s `safe-divisor?`), so neither #DE case can
-- arise: BARE cqto/idivq, no test/cmp/jmp guard. Same trusted-printer seam as
-- the guarded idivq — safety is guaranteed by construction at the call site.
instr-text (Xdiv-safe-rrr dst a b) =
     "    movq " ++ reg-text a ++ ", %rax\n" ++
     "    cqto\n" ++
     "    idivq " ++ reg-text b ++ "\n" ++
     "    movq %rax, " ++ reg-text dst ++ "\n"
instr-text (Xrem-safe-rrr dst a b) =
     "    movq " ++ reg-text a ++ ", %rax\n" ++
     "    cqto\n" ++
     "    idivq " ++ reg-text b ++ "\n" ++
     "    movq %rdx, " ++ reg-text dst ++ "\n"   -- remainder is in %rdx
-- Strength-reduced multiply by a power-of-two literal: left shift by `imm`.
-- `imm ≤ 30 < 64`, so the shift count is always in range.
instr-text (Xshl-rri dst src imm) =
     "    movq " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n" ++
     "    salq $" ++ showℕ imm ++ ", " ++ reg-text dst ++ "\n"
-- Strength-reduced signed divide by `2^imm` (truncate toward zero) — the
-- branchless GCC sign-bias idiom realising `sdiv2ᵏ`. `%rax` is caller-saved
-- scratch (never an arith register). Computes bias = (src<0 ? 2^imm−1 : 0),
-- then arithmetic-shift-right (src + bias) by imm. `src` is read twice before
-- `dst` is written, so it is correct even when `dst ≡ src`.
instr-text (Xsdiv-pow2-rri dst src imm) =
     "    movq " ++ reg-text src ++ ", %rax\n" ++
     "    sarq $63, %rax\n" ++                                  -- rax = src<0 ? -1 : 0
     "    shrq $" ++ showℕ (64 ∸ imm) ++ ", %rax\n" ++          -- rax = src<0 ? 2^imm−1 : 0
     "    addq " ++ reg-text src ++ ", %rax\n" ++               -- rax = src + bias
     "    sarq $" ++ showℕ imm ++ ", %rax\n" ++                 -- rax = quotient
     "    movq %rax, " ++ reg-text dst ++ "\n"
instr-text (Xneg-r dst)       = "    negq " ++ reg-text dst ++ "\n"
instr-text (Xmov-out src)     = "    movq " ++ reg-text src ++ ", %rax\n"

program-text : XProgram → String
program-text []       = ""
program-text (i ∷ is) = instr-text i ++ program-text is

------------------------------------------------------------------------
-- Block subroutine emission
------------------------------------------------------------------------

-- | Emit a complete arith-block subroutine. The symbol must match
-- the one the call site emits (`once_arith.block.<digest>`); the
-- caller passes that pre-mangled symbol in.
--
-- Layout:
--
--   <sym>:
--       subq $N, %rsp        ; reserve scratch (N = 8 * required-scratch)
--       <emitted instructions>
--       addq $N, %rsp
--       ret
--
-- The block is frameless w.r.t. `%rbp` — like the rest of Once's
-- codegen post-Plan 0.2.4.5 D1. `%rsp` is the only stack pointer
-- the block touches; the prologue's `subq` and epilogue's `addq`
-- are perfectly balanced so the call site sees no stack drift.
emit-arith-block : (sym : String) → ArithBlock → String
emit-arith-block sym blk =
  let body  = normalize (block-body blk)   -- div-guard elision + degenerate folds
      n     = required-scratch body
      pad   = showℕ (8 * n)
      instr = emit-program (compile-abs body)
  in sym ++ ":\n" ++
     "    subq $" ++ pad ++ ", %rsp\n" ++
     program-text instr ++
     "    addq $" ++ pad ++ ", %rsp\n" ++
     "    ret\n\n"

------------------------------------------------------------------------
-- Block-list emission
------------------------------------------------------------------------

-- | The canonical assembly symbol for an `ArithBlock`. Mirrors the
-- name `block-info` puts in the `SigOpInfo` (`bare (block-name …)` =
-- `canonical [block-name]`), mangled through `once-symbol-own` =
-- `once-symbol-path ∘ canonical ∘ [_]` to match `compile-sigOp`'s
-- `once-symbol-path` call-site emission (Plan 0.50 — legacy `once-symbol`
-- left the dots un-encoded, mismatching the call).
arith-block-symbol : ArithBlock → String
arith-block-symbol blk = once-symbol-own (block-name (block-body blk))

-- | Emit a list of arith blocks as concatenated assembly text. Each
-- block becomes a `<once_arith.block.<digest>>:` subroutine; dedup
-- by symbol is the caller's responsibility (the rewrite pass may
-- discover the same block at multiple call sites).
emit-arith-blocks : List ArithBlock → String
emit-arith-blocks []       = ""
emit-arith-blocks (b ∷ bs) =
  ".globl " ++ arith-block-symbol b ++ "\n" ++
  emit-arith-block (arith-block-symbol b) b ++
  emit-arith-blocks bs
