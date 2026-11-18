-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.X86-32.Backend — plan 0.146 B1.7c (D460): x86-32's code
-- generator (`Target.Backend`): its file (`CCC.Target.X86-32.File`), the
-- abstract trace lowered (`AbstractToX86-32.compile-trace-cnt`), an arith
-- block's code (`Arith.Backend.X86-32.Emit.block-payload`).
------------------------------------------------------------------------

module Once.Target.X86-32.Backend where

open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Once.Target.Backend using (Backend)
open import Once.Compile using (entry-owner)
import Once.CCC.Target.X86-32.File as F
import Once.CCC.Target.X86-32.AbstractToX86-32 as L
import Once.Arith.Backend.X86-32.Emit as A

backend : Backend
backend = record
  { File = F.Image ; print = F.print
  ; Payload = F.Payload ; payload = A.block-payload
  ; file = λ t bs ex → F.mkImage (proj₂ (L.compile-trace-cnt entry-owner 0 t)) (just 0) bs ex
  }
