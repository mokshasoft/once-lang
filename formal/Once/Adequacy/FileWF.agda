-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FileWF — plan 0.107 phase d: THE FILE IS WHAT `as`/`ld` ACCEPT.
--
-- `as-faithful` (`Once.Adequacy.CPU.Interface`) is the ONLY trust about turning
-- a program into bytes, and it is preconditioned on `AsmWF`: every symbol the
-- file defines is defined once, every symbol it references is defined in it or
-- is an interpretation's, and the entry point is an instruction of it.
--
-- A THEOREM per arch, over the image (plan 0.107 §6): the file's code is the
-- lowering of the program image (one walk; nested-free, so the counter-threaded
-- lowering is the plain one), the lowering is symbol-faithful
-- (`Target.<arch>.FileSymbols`, layer 1), so the file's definitions and
-- references ARE the image's — and those are `Adequacy.ImageWF`'s (layers 2–3).
-- `_start` is instruction 0, and the image's first instruction (`c-start`)
-- lowers to code, so the entry is inside it.
------------------------------------------------------------------------

module Once.Adequacy.FileWF where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming (map to All-map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Once.Target.AsmSymbol using (AsmSym)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₂)
open import Data.Unit using (tt)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Target.Arch using (Arch; x86-64; x86-32; riscv64)
open import Once.Parser.Module.Core using (Module)
import Once.Compile as C
open import Once.Adequacy.Compile using (AsmWF-of)
open import Once.Adequacy.EmitFile using (file-is-emit; file-is-lib)
open import Once.Adequacy.ImageWF
  using (prog-defs; lib-defs; Resolved)
open import Once.Adequacy.ImageUnique using (prog-unique; lib-unique)
open import Once.Adequacy.ImageValid using (prog-defs-valid; lib-defs-valid; externs-valid)
open import Once.Adequacy.ImageResolved using (prog-resolved; lib-resolved)
open import Once.CCC.Codegen.ImageSymbols using (arefs)
open import Once.CCC.Machine.NoNested using (NoNested; no-nested-of-all)
open import Once.CCC.Machine.FrameFree using (emittable-image)
open import Once.CCC.Codegen.ProgramImageFacts C.entry-owner using (image-frame-free; fns-frame-free)
open import Once.Denotation.Program using (irProgram)
open import Once.Arith.Machine.Rewrite using (rewrite-ir)

private
  -- the file's block table keeps the symbols it was built from
  map-fst : ∀ {A B C : Set} (f : A × B → C) (xs : List (A × B))
          → map proj₁ (map (λ sb → proj₁ sb , f sb) xs) ≡ map proj₁ xs
  map-fst f []       = refl
  map-fst f (x ∷ xs) = cong (proj₁ x ∷_) (map-fst f xs)

  -- the program image and the library image are nested-free
  prog-nn : ∀ (m : Module) ir → NoNested (C.image-of (irProgram (C.moduleTable m) ir))
  prog-nn m ir = no-nested-of-all _ (image-frame-free (C.rewrite-table (C.moduleTable m)) (proj₁ (rewrite-ir ir)))

  lib-nn : ∀ (m : Module) → NoNested (C.lib-image (C.moduleTable m))
  lib-nn m = no-nested-of-all _ (All-map (λ {i} → emittable-image i) (fns-frame-free 0 (C.rewrite-table (C.moduleTable m))))

  -- an `AsmWF`-shaped conclusion, transported along the two equations
  resolved-at : ∀ {ds ds′ ext rs rs′ : List String} → ds ≡ ds′ → rs ≡ rs′
              → Resolved ds′ ext rs′ → All (λ s → s ∈ ds ⊎ s ∈ ext) rs
  resolved-at refl refl r = r

------------------------------------------------------------------------
-- X86-64
------------------------------------------------------------------------
module X8664W where
  import Once.CCC.Target.X86-64.File as F
  import Once.CCC.Target.X86-64.AbstractToX86 as L
  open import Once.CCC.Target.X86-64.FileSymbols using (defs-lower; refs-lower)

  prog-wf : ∀ (m : Module) ir → C.moduleToIR m ≡ just ir
          → F.AsmWF (C.emitProgram x86-64 (irProgram (C.moduleTable m) ir))
  prog-wf m ir mi = record
    { defined-once = subst Unique (sym defs≡) (prog-unique m ir)
    ; resolved     = resolved-at defs≡ refs≡ (prog-resolved m ir mi)
    ; entry-in     = s≤s z≤n
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (prog-defs-valid (irProgram (C.moduleTable m) ir))
    ; externs-valid = externs-valid (irProgram (C.moduleTable m) ir)
    }
    where
      p = irProgram (C.moduleTable m) ir
      G = C.emitProgram x86-64 p
      code≡ : F.code G ≡ L.compile-trace (C.image-of p)
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.image-of p) (prog-nn m ir))
      defs≡ : F.defs G ≡ prog-defs p
      defs≡ = cong (λ z → F.heap-sym ∷ "_start" ∷ z)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.image-of p))) (map-fst _ _))
      refs≡ : F.refs (F.code G) ≡ arefs (C.image-of p)
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.image-of p))

  lib-wf : ∀ (m : Module) → C.moduleToIR m ≡ nothing
         → F.AsmWF (C.emitLibrary x86-64 (C.moduleTable m))
  lib-wf m mi = record
    { defined-once = subst Unique (sym defs≡) (lib-unique m)
    ; resolved     = resolved-at defs≡ refs≡ (lib-resolved m)
    ; entry-in     = tt
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (lib-defs-valid m)
    ; externs-valid = externs-valid (C.lib-program (C.moduleTable m))
    }
    where
      G = C.emitLibrary x86-64 (C.moduleTable m)
      code≡ : F.code G ≡ L.compile-trace (C.lib-image (C.moduleTable m))
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.lib-image (C.moduleTable m)) (lib-nn m))
      defs≡ : F.defs G ≡ lib-defs m
      defs≡ = cong (F.heap-sym ∷_)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.lib-image (C.moduleTable m))))
                            (map-fst _ _))
      refs≡ : F.refs (F.code G) ≡ arefs (C.lib-image (C.moduleTable m))
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.lib-image (C.moduleTable m)))

  file-wf : ∀ (m : Module) (G : C.FileOf x86-64) → C.compileFileFromModule C.Heap false x86-64 m ≡ inj₂ G
          → AsmWF-of x86-64 G
  file-wf m G eq = by (C.moduleToIR m) refl
    where
      by : ∀ (r : Maybe _) → C.moduleToIR m ≡ r → AsmWF-of x86-64 G
      by (just ir) mi = subst F.AsmWF (sym (file-is-emit x86-64 m G ir eq mi)) (prog-wf m ir mi)
      by nothing   mi = subst F.AsmWF (sym (file-is-lib x86-64 m G eq mi)) (lib-wf m mi)

------------------------------------------------------------------------
-- X86-32
------------------------------------------------------------------------
module X8632W where
  import Once.CCC.Target.X86-32.File as F
  import Once.CCC.Target.X86-32.AbstractToX86-32 as L
  open import Once.CCC.Target.X86-32.FileSymbols using (defs-lower; refs-lower)

  prog-wf : ∀ (m : Module) ir → C.moduleToIR m ≡ just ir
          → F.AsmWF (C.emitProgram x86-32 (irProgram (C.moduleTable m) ir))
  prog-wf m ir mi = record
    { defined-once = subst Unique (sym defs≡) (prog-unique m ir)
    ; resolved     = resolved-at defs≡ refs≡ (prog-resolved m ir mi)
    ; entry-in     = s≤s z≤n
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (prog-defs-valid (irProgram (C.moduleTable m) ir))
    ; externs-valid = externs-valid (irProgram (C.moduleTable m) ir)
    }
    where
      p = irProgram (C.moduleTable m) ir
      G = C.emitProgram x86-32 p
      code≡ : F.code G ≡ L.compile-trace (C.image-of p)
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.image-of p) (prog-nn m ir))
      defs≡ : F.defs G ≡ prog-defs p
      defs≡ = cong (λ z → F.heap-sym ∷ "_start" ∷ z)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.image-of p))) (map-fst _ _))
      refs≡ : F.refs (F.code G) ≡ arefs (C.image-of p)
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.image-of p))

  lib-wf : ∀ (m : Module) → C.moduleToIR m ≡ nothing
         → F.AsmWF (C.emitLibrary x86-32 (C.moduleTable m))
  lib-wf m mi = record
    { defined-once = subst Unique (sym defs≡) (lib-unique m)
    ; resolved     = resolved-at defs≡ refs≡ (lib-resolved m)
    ; entry-in     = tt
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (lib-defs-valid m)
    ; externs-valid = externs-valid (C.lib-program (C.moduleTable m))
    }
    where
      G = C.emitLibrary x86-32 (C.moduleTable m)
      code≡ : F.code G ≡ L.compile-trace (C.lib-image (C.moduleTable m))
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.lib-image (C.moduleTable m)) (lib-nn m))
      defs≡ : F.defs G ≡ lib-defs m
      defs≡ = cong (F.heap-sym ∷_)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.lib-image (C.moduleTable m))))
                            (map-fst _ _))
      refs≡ : F.refs (F.code G) ≡ arefs (C.lib-image (C.moduleTable m))
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.lib-image (C.moduleTable m)))

  file-wf : ∀ (m : Module) (G : C.FileOf x86-32) → C.compileFileFromModule C.Heap false x86-32 m ≡ inj₂ G
          → AsmWF-of x86-32 G
  file-wf m G eq = by (C.moduleToIR m) refl
    where
      by : ∀ (r : Maybe _) → C.moduleToIR m ≡ r → AsmWF-of x86-32 G
      by (just ir) mi = subst F.AsmWF (sym (file-is-emit x86-32 m G ir eq mi)) (prog-wf m ir mi)
      by nothing   mi = subst F.AsmWF (sym (file-is-lib x86-32 m G eq mi)) (lib-wf m mi)

------------------------------------------------------------------------
-- RiscV64
------------------------------------------------------------------------
module RiscV64W where
  import Once.CCC.Target.RiscV64.File as F
  import Once.CCC.Target.RiscV64.AbstractToRiscV as L
  open import Once.CCC.Target.RiscV64.FileSymbols using (defs-lower; refs-lower)

  prog-wf : ∀ (m : Module) ir → C.moduleToIR m ≡ just ir
          → F.AsmWF (C.emitProgram riscv64 (irProgram (C.moduleTable m) ir))
  prog-wf m ir mi = record
    { defined-once = subst Unique (sym defs≡) (prog-unique m ir)
    ; resolved     = resolved-at defs≡ refs≡ (prog-resolved m ir mi)
    ; entry-in     = s≤s z≤n
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (prog-defs-valid (irProgram (C.moduleTable m) ir))
    ; externs-valid = externs-valid (irProgram (C.moduleTable m) ir)
    }
    where
      p = irProgram (C.moduleTable m) ir
      G = C.emitProgram riscv64 p
      code≡ : F.code G ≡ L.compile-trace (C.image-of p)
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.image-of p) (prog-nn m ir))
      defs≡ : F.defs G ≡ prog-defs p
      defs≡ = cong (λ z → F.heap-sym ∷ "_start" ∷ z)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.image-of p))) (map-fst _ _))
      refs≡ : F.refs (F.code G) ≡ arefs (C.image-of p)
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.image-of p))

  lib-wf : ∀ (m : Module) → C.moduleToIR m ≡ nothing
         → F.AsmWF (C.emitLibrary riscv64 (C.moduleTable m))
  lib-wf m mi = record
    { defined-once = subst Unique (sym defs≡) (lib-unique m)
    ; resolved     = resolved-at defs≡ refs≡ (lib-resolved m)
    ; entry-in     = tt
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (lib-defs-valid m)
    ; externs-valid = externs-valid (C.lib-program (C.moduleTable m))
    }
    where
      G = C.emitLibrary riscv64 (C.moduleTable m)
      code≡ : F.code G ≡ L.compile-trace (C.lib-image (C.moduleTable m))
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.lib-image (C.moduleTable m)) (lib-nn m))
      defs≡ : F.defs G ≡ lib-defs m
      defs≡ = cong (F.heap-sym ∷_)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.lib-image (C.moduleTable m))))
                            (map-fst _ _))
      refs≡ : F.refs (F.code G) ≡ arefs (C.lib-image (C.moduleTable m))
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.lib-image (C.moduleTable m)))

  file-wf : ∀ (m : Module) (G : C.FileOf riscv64) → C.compileFileFromModule C.Heap false riscv64 m ≡ inj₂ G
          → AsmWF-of riscv64 G
  file-wf m G eq = by (C.moduleToIR m) refl
    where
      by : ∀ (r : Maybe _) → C.moduleToIR m ≡ r → AsmWF-of riscv64 G
      by (just ir) mi = subst F.AsmWF (sym (file-is-emit riscv64 m G ir eq mi)) (prog-wf m ir mi)
      by nothing   mi = subst F.AsmWF (sym (file-is-lib riscv64 m G eq mi)) (lib-wf m mi)

------------------------------------------------------------------------
-- THE THEOREM (was a postulate, D262).
------------------------------------------------------------------------
file-wf : ∀ (arch : Arch) (m : Module) (F : C.FileOf arch)
        → C.compileFileFromModule C.Heap false arch m ≡ inj₂ F
        → AsmWF-of arch F
file-wf x86-64  = X8664W.file-wf
file-wf x86-32  = X8632W.file-wf
file-wf riscv64 = RiscV64W.file-wf
