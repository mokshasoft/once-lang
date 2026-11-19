-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Compile.Emit — the back end of the pipeline: from an IR program to
-- the file of each target.
--
-- The program the back end compiles is the arith-lifted one (`rewrite-program`);
-- its image is the program image with its room checks (`image-of`); each
-- target's file is that image, lowered, with the program's arith blocks by
-- symbol (`blocks-<arch>`) and the symbols it calls outside itself
-- (`prog-externs`). A library is its functions only (`emitLibrary`).
------------------------------------------------------------------------

module Once.Compile.Emit where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
import Data.List as DL
import Data.Bool.ListAction as BLA
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _==_)
open import Data.List.Membership.DecPropositional Data.String._≟_ using () renaming (_∈?_ to _∈ˢ?_; _∈_ to _∈ˢ_)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable.Core using (¬?)
open import Relation.Nullary.Negation.Core using (¬_)
open import Once.IR using (id)
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.Target.Arch
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Target.SymbolFresh using (host-leave-symbol; host-exhausted-symbol)
open import Once.CCC.Codegen.NodesOK using (leaf-syms)
open import Once.Arith.Machine.IR using (ArithBlock)
open Once.Arith.Machine.IR.ArithBlock using (block-body)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Arith.Machine.Rewrite using (rewrite-ir)
open import Once.Denotation.Program using (IRFun; irFun; IRProgram; irProgram)
open Once.Denotation.Program.IRProgram using (main; table)
open Once.Denotation.Program.IRFun using (fbody; fcod; fdom; fname)
open import Once.CCC.Machine.SMCore using (AbstractTrace)
open import Once.CCC.Codegen.ProgramImage using (program-image; fns-image)
open import Once.CCC.Codegen.RoomChecks using (room-checks)
import Once.CCC.Target.X86-64.File as X64F
import Once.CCC.Target.X86-32.File as X32F
import Once.CCC.Target.RiscV64.File as RVF
import Once.CCC.Target.X86-64.AbstractToX86 as X64L
import Once.CCC.Target.X86-32.AbstractToX86-32 as X32L
import Once.CCC.Target.RiscV64.AbstractToRiscV as RVL
import Once.Arith.Backend.X86-64.Emit as X64A
import Once.Arith.Backend.X86-32.Emit as X32A
import Once.Arith.Backend.RiscV64.Emit as RVA

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

-- The symbols the program's SigOps call (`NodesOK.leaf-syms`, leaf by leaf).
calls-of : IRProgram → List String
calls-of p = leaf-syms (main p) DL.++ DL.concatMap (λ e → leaf-syms (fbody e)) (table p)

-- plan 0.107 §9 2D / D274: the interpretation symbols the file calls and `ld`
-- resolves are EXACTLY the SigOp symbols the (rewritten) program calls that are
-- not its own arith blocks — the names the code actually calls, never a
-- declaration's spelling. A call to anything else is defined in the file.
is-extern? : (p : IRProgram) (s : String) → Dec (¬ (s ∈ˢ block-syms (program-blocks p)))
is-extern? p s = ¬? (s ∈ˢ? block-syms (program-blocks p))

externs-of : IRProgram → List String
externs-of p = DL.filter (is-extern? p) (calls-of (rewrite-program p))

-- D320: a PROGRAM also calls the Host's `leave` (`c-leave`); a library does not.
-- D377: …and its `exhausted` (every room check calls it when there is no room).
prog-externs : IRProgram → List String
prog-externs p = host-leave-symbol ∷ host-exhausted-symbol ∷ externs-of p

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

-- D377 (plan 0.123 A.4 step 5): the image the backends lower is the program image
-- with its room checks (`RoomChecks.room-checks`): a check at the start and after
-- every label, entry and call, each for what its stretch spends.
image-of : IRProgram → AbstractTrace
image-of p = room-checks (program-image entry-owner (rewrite-program p))

-- the file's arith blocks: the program's, by symbol, once each
blocks-x86-64 : IRProgram → List (String × X64F.Payload)
blocks-x86-64 p =
  DL.map (λ sb → proj₁ sb , X64A.block-payload (proj₂ sb))
    (dedup-blocks (DL.map (λ b → X64A.arith-block-symbol b , b) (program-blocks p)))

emit-x86-64 : IRProgram → X64F.Image
emit-x86-64 p =
  X64F.mkImage (proj₂ (X64L.compile-trace-cnt entry-owner 0 (image-of p))) (just 0) (blocks-x86-64 p) (prog-externs p)

-- the file's arith blocks: the program's, by symbol, once each
blocks-x86-32 : IRProgram → List (String × X32F.Payload)
blocks-x86-32 p =
  DL.map (λ sb → proj₁ sb , X32A.block-payload (proj₂ sb))
    (dedup-blocks (DL.map (λ b → X32A.arith-block-symbol b , b) (program-blocks p)))

emit-x86-32 : IRProgram → X32F.Image
emit-x86-32 p =
  X32F.mkImage (proj₂ (X32L.compile-trace-cnt entry-owner 0 (image-of p))) (just 0) (blocks-x86-32 p) (prog-externs p)

-- the file's arith blocks: the program's, by symbol, once each
blocks-riscv64 : IRProgram → List (String × RVF.Payload)
blocks-riscv64 p =
  DL.map (λ sb → proj₁ sb , RVA.block-payload (proj₂ sb))
    (dedup-blocks (DL.map (λ b → RVA.arith-block-symbol b , b) (program-blocks p)))

emit-riscv64 : IRProgram → RVF.Image
emit-riscv64 p =
  RVF.mkImage (proj₂ (RVL.compile-trace-cnt entry-owner 0 (image-of p))) (just 0) (blocks-riscv64 p) (prog-externs p)

emitProgram : (arch : Arch) → IRProgram → FileOf arch
emitProgram x86-64  = emit-x86-64
emitProgram x86-32  = emit-x86-32
emitProgram riscv64 = emit-riscv64

-- A LIBRARY (no `main`): its functions only — no entry unit, no `_start`. The
-- verified compiler never assembles one (it has no behaviour); the CLI emits it.
lib-image : List IRFun → AbstractTrace
lib-image tbl = fns-image 0 (rewrite-table tbl)

-- A library as a program whose `main` does nothing: its blocks and externs
-- are the table's.
lib-program : List IRFun → IRProgram
lib-program tbl = irProgram tbl id

lib-blocks : List IRFun → List ArithBlock
lib-blocks tbl = program-blocks (lib-program tbl)

emitLibrary : (arch : Arch) → List IRFun → FileOf arch
emitLibrary x86-64 tbl =
  X64F.mkImage (proj₂ (X64L.compile-trace-cnt entry-owner 0 (lib-image tbl))) nothing
    (DL.map (λ sb → proj₁ sb , X64A.block-payload (proj₂ sb))
      (dedup-blocks (DL.map (λ b → X64A.arith-block-symbol b , b) (lib-blocks tbl)))) (externs-of (lib-program tbl))
emitLibrary x86-32 tbl =
  X32F.mkImage (proj₂ (X32L.compile-trace-cnt entry-owner 0 (lib-image tbl))) nothing
    (DL.map (λ sb → proj₁ sb , X32A.block-payload (proj₂ sb))
      (dedup-blocks (DL.map (λ b → X32A.arith-block-symbol b , b) (lib-blocks tbl)))) (externs-of (lib-program tbl))
emitLibrary riscv64 tbl =
  RVF.mkImage (proj₂ (RVL.compile-trace-cnt entry-owner 0 (lib-image tbl))) nothing
    (DL.map (λ sb → proj₁ sb , RVA.block-payload (proj₂ sb))
      (dedup-blocks (DL.map (λ b → RVA.arith-block-symbol b , b) (lib-blocks tbl)))) (externs-of (lib-program tbl))
