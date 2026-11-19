-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Compile.Emit — what the back end shares with the IR's arith lifting:
-- the arith-lifted program (`rewrite-program`) and its arith blocks by symbol
-- (`program-blocks`, `dedup-blocks`, `block-symbol`), the entry unit's owner,
-- and each target's file type (`FileOf`, `printFile`). Master's lowering of the
-- IR program to a file is deleted (D465); the file is the linear core's
-- (`LinCore.Emit`).
------------------------------------------------------------------------

module Once.Compile.Emit where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
import Data.List as DL
import Data.Bool.ListAction as BLA
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _==_)
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.Target.Arch
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Arith.Machine.IR using (ArithBlock)
open Once.Arith.Machine.IR.ArithBlock using (block-body)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Arith.Machine.Rewrite using (rewrite-ir)
open import Once.Denotation.Program using (IRFun; irFun; IRProgram; irProgram)
open Once.Denotation.Program.IRProgram using (main; table)
open Once.Denotation.Program.IRFun using (fbody; fcod; fdom; fname)
import Once.CCC.Target.X86-64.File as X64F
import Once.CCC.Target.X86-32.File as X32F
import Once.CCC.Target.RiscV64.File as RVF

-- D165/D244: THE PROGRAM THE BACKEND COMPILES — every definition arith-lifted.
rewrite-fun : IRFun → IRFun
rewrite-fun e = irFun (fname e) (fdom e) (fcod e) (proj₁ (rewrite-ir (fbody e)))

rewrite-table : List IRFun → List IRFun
rewrite-table []       = []
rewrite-table (e ∷ es) = rewrite-fun e ∷ rewrite-table es

rewrite-program : IRProgram → IRProgram
rewrite-program p = irProgram (rewrite-table (table p)) (proj₁ (rewrite-ir (main p)))

-- …and the arith blocks that lifting minted, from the SAME `rewrite-ir` calls.
table-blocks : List IRFun → List ArithBlock
table-blocks []       = []
table-blocks (e ∷ es) = proj₂ (rewrite-ir (fbody e)) DL.++ table-blocks es

program-blocks : IRProgram → List ArithBlock
program-blocks p = proj₂ (rewrite-ir (main p)) DL.++ table-blocks (table p)

-- One block per symbol (the first): two definitions lifting the same
-- arithmetic mint the same digest, and a symbol is defined once.
dedup-go : List String → List (String × ArithBlock) → List (String × ArithBlock)
dedup-go seen []             = []
dedup-go seen ((s , b) ∷ bs) =
  if BLA.any (λ x → x == s) seen then dedup-go seen bs
                                 else (s , b) ∷ dedup-go (s ∷ seen) bs

dedup-blocks : List (String × ArithBlock) → List (String × ArithBlock)
dedup-blocks = dedup-go []

-- An arith block's symbol — what every arch's `arith-block-symbol` is.
block-symbol : ArithBlock → String
block-symbol b = once-symbol-own (block-name (block-body b))

-- The file's block table, by symbol, once each (`blocks-<arch>`).
block-syms : List ArithBlock → List String
block-syms bs = DL.map proj₁ (dedup-blocks (DL.map (λ b → block-symbol b , b) bs))

-- The entry unit's owner: a name no definition can have (an identifier cannot
-- start with a digit), so its labels and symbol cannot clash.
entry-owner : CanonicalName
entry-owner = bare "0entry"

------------------------------------------------------------------------
-- The per-arch file: `code` IS the lowered program image, and `_start` is its
-- first instruction — the image's `c-start` (the heap register, the outermost
-- frame); `main`'s unit ends where the program leaves — a call of the Host's
-- `leave` (D320). No syscall, no hand-written runtime: what ending a run means
-- is the Host's, linked beside the program, on bare metal as under an OS.
------------------------------------------------------------------------

FileOf : Arch → Set
FileOf x86-64  = X64F.Image
FileOf x86-32  = X32F.Image
FileOf riscv64 = RVF.Image

printFile : (arch : Arch) → FileOf arch → String
printFile x86-64  = X64F.print
printFile x86-32  = X32F.print
printFile riscv64 = RVF.print

