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
open import Data.Bool using (Bool; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Target.Arch using (Arch; x86-64; x86-32; riscv64)
import Once.Parser.Module.Core as Core
import Once.Compile as C
import Once.IR as IR
open import Once.Adequacy.Compile using (AsmWF-of)
open import Once.Adequacy.EmitFile using (file-is-emit-at; file-is-lib-at)
open import Once.Adequacy.ImageWF
  using (prog-defs; lib-defs; Resolved)
open import Once.Adequacy.ImageUnique using (TableNames; table-names-at; prog-unique-at; lib-unique-at)
open import Once.Adequacy.ImageValid using (prog-defs-valid; lib-defs-valid; externs-valid; prog-externs-valid)
open import Once.Adequacy.ImageResolved using (prog-resolved-at; lib-resolved-at)
open import Once.CCC.Codegen.ImageSymbols using (arefs)
open import Once.CCC.Machine.NoNested using (NoNested; no-nested-of-all)
open import Once.CCC.Machine.FrameFree using (emittable-image)
open import Once.CCC.Codegen.ProgramImageFacts C.entry-owner using (image-frame-free; fns-frame-free)
open import Once.Denotation.Program using (irProgram; IRFun; Linked; LinkedProgram)
open Once.Denotation.Program.IRFun using (fbody)
open import Once.Contract using (ISig)
open import Once.Adequacy.OptimizedLinked using (build-linked; build-table-linked)
open import Once.Arith.Machine.Rewrite using (rewrite-ir)

private
  -- the file's block table keeps the symbols it was built from
  map-fst : ∀ {A B C : Set} (f : A × B → C) (xs : List (A × B))
          → map proj₁ (map (λ sb → proj₁ sb , f sb) xs) ≡ map proj₁ xs
  map-fst f []       = refl
  map-fst f (x ∷ xs) = cong (proj₁ x ∷_) (map-fst f xs)

  -- the program image and the library image are nested-free
  prog-nn : ∀ (T : List IRFun) ir → NoNested (C.image-of (irProgram T ir))
  prog-nn T ir = no-nested-of-all _ (image-frame-free (C.rewrite-table T) (proj₁ (rewrite-ir ir)))

  lib-nn : ∀ (T : List IRFun) → NoNested (C.lib-image T)
  lib-nn T = no-nested-of-all _ (All-map (λ {i} → emittable-image i) (fns-frame-free 0 (C.rewrite-table T)))

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

  prog-wf : ∀ (T : List IRFun) (tn : TableNames T) ir {σ : ISig} → LinkedProgram σ (irProgram T ir)
          → F.AsmWF (C.emitProgram x86-64 (irProgram T ir))
  prog-wf T tn ir lk = record
    { defined-once = subst Unique (sym defs≡) (prog-unique-at T tn ir)
    ; resolved     = resolved-at defs≡ refs≡ (prog-resolved-at _ (irProgram T ir) lk)
    ; entry-in     = s≤s z≤n
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (prog-defs-valid (irProgram T ir))
    ; externs-valid = prog-externs-valid (irProgram T ir)
    }
    where
      p = irProgram T ir
      G = C.emitProgram x86-64 p
      code≡ : F.Image.code G ≡ L.compile-trace (C.image-of p)
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.image-of p) (prog-nn T ir))
      defs≡ : F.defs G ≡ prog-defs p
      defs≡ = cong (λ z → F.heap-sym ∷ "_start" ∷ z)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.image-of p))) (map-fst _ _))
      refs≡ : F.refs (F.Image.code G) ≡ arefs (C.image-of p)
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.image-of p))

  lib-wf : ∀ (T : List IRFun) (tn : TableNames T) {σ : ISig} → All (λ e → Linked σ T (fbody e)) T
         → F.AsmWF (C.emitLibrary x86-64 T)
  lib-wf T tn tl = record
    { defined-once = subst Unique (sym defs≡) (lib-unique-at T tn)
    ; resolved     = resolved-at defs≡ refs≡ (lib-resolved-at _ T tl)
    ; entry-in     = tt
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (lib-defs-valid T)
    ; externs-valid = externs-valid (C.lib-program T)
    }
    where
      G = C.emitLibrary x86-64 T
      code≡ : F.Image.code G ≡ L.compile-trace (C.lib-image T)
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.lib-image T) (lib-nn T))
      defs≡ : F.defs G ≡ lib-defs T
      defs≡ = cong (F.heap-sym ∷_)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.lib-image T)))
                            (map-fst _ _))
      refs≡ : F.refs (F.Image.code G) ≡ arefs (C.lib-image T)
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.lib-image T))

  file-wf : ∀ (doOpt : Bool) (m : Core.Resolved) (G : C.FileOf x86-64) → C.compileFileFromModule IR.Heap doOpt x86-64 m ≡ inj₂ G
          → AsmWF-of x86-64 G
  file-wf doOpt m G eq = by (C.moduleToIR-aux (C.compileResolvedModule IR.Heap doOpt m)) refl
    where
      T = C.tableOfResult (C.compileResolvedModule IR.Heap doOpt m)
      by : ∀ (r : Maybe _) → C.moduleToIR-aux (C.compileResolvedModule IR.Heap doOpt m) ≡ r → AsmWF-of x86-64 G
      by (just ir) mi = subst F.AsmWF (sym (file-is-emit-at doOpt x86-64 m G ir eq mi))
                          (prog-wf T (table-names-at doOpt m) ir (build-linked doOpt m ir mi))
      by nothing   mi = subst F.AsmWF (sym (file-is-lib-at doOpt x86-64 m G eq mi))
                          (lib-wf T (table-names-at doOpt m) (build-table-linked doOpt m))

------------------------------------------------------------------------
-- X86-32
------------------------------------------------------------------------
module X8632W where
  import Once.CCC.Target.X86-32.File as F
  import Once.CCC.Target.X86-32.AbstractToX86-32 as L
  open import Once.CCC.Target.X86-32.FileSymbols using (defs-lower; refs-lower)

  prog-wf : ∀ (T : List IRFun) (tn : TableNames T) ir {σ : ISig} → LinkedProgram σ (irProgram T ir)
          → F.AsmWF (C.emitProgram x86-32 (irProgram T ir))
  prog-wf T tn ir lk = record
    { defined-once = subst Unique (sym defs≡) (prog-unique-at T tn ir)
    ; resolved     = resolved-at defs≡ refs≡ (prog-resolved-at _ (irProgram T ir) lk)
    ; entry-in     = s≤s z≤n
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (prog-defs-valid (irProgram T ir))
    ; externs-valid = prog-externs-valid (irProgram T ir)
    }
    where
      p = irProgram T ir
      G = C.emitProgram x86-32 p
      code≡ : F.Image.code G ≡ L.compile-trace (C.image-of p)
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.image-of p) (prog-nn T ir))
      defs≡ : F.defs G ≡ prog-defs p
      defs≡ = cong (λ z → F.heap-sym ∷ "_start" ∷ z)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.image-of p))) (map-fst _ _))
      refs≡ : F.refs (F.Image.code G) ≡ arefs (C.image-of p)
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.image-of p))

  lib-wf : ∀ (T : List IRFun) (tn : TableNames T) {σ : ISig} → All (λ e → Linked σ T (fbody e)) T
         → F.AsmWF (C.emitLibrary x86-32 T)
  lib-wf T tn tl = record
    { defined-once = subst Unique (sym defs≡) (lib-unique-at T tn)
    ; resolved     = resolved-at defs≡ refs≡ (lib-resolved-at _ T tl)
    ; entry-in     = tt
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (lib-defs-valid T)
    ; externs-valid = externs-valid (C.lib-program T)
    }
    where
      G = C.emitLibrary x86-32 T
      code≡ : F.Image.code G ≡ L.compile-trace (C.lib-image T)
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.lib-image T) (lib-nn T))
      defs≡ : F.defs G ≡ lib-defs T
      defs≡ = cong (F.heap-sym ∷_)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.lib-image T)))
                            (map-fst _ _))
      refs≡ : F.refs (F.Image.code G) ≡ arefs (C.lib-image T)
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.lib-image T))

  file-wf : ∀ (doOpt : Bool) (m : Core.Resolved) (G : C.FileOf x86-32) → C.compileFileFromModule IR.Heap doOpt x86-32 m ≡ inj₂ G
          → AsmWF-of x86-32 G
  file-wf doOpt m G eq = by (C.moduleToIR-aux (C.compileResolvedModule IR.Heap doOpt m)) refl
    where
      T = C.tableOfResult (C.compileResolvedModule IR.Heap doOpt m)
      by : ∀ (r : Maybe _) → C.moduleToIR-aux (C.compileResolvedModule IR.Heap doOpt m) ≡ r → AsmWF-of x86-32 G
      by (just ir) mi = subst F.AsmWF (sym (file-is-emit-at doOpt x86-32 m G ir eq mi))
                          (prog-wf T (table-names-at doOpt m) ir (build-linked doOpt m ir mi))
      by nothing   mi = subst F.AsmWF (sym (file-is-lib-at doOpt x86-32 m G eq mi))
                          (lib-wf T (table-names-at doOpt m) (build-table-linked doOpt m))

------------------------------------------------------------------------
-- RiscV64
------------------------------------------------------------------------
module RiscV64W where
  import Once.CCC.Target.RiscV64.File as F
  import Once.CCC.Target.RiscV64.AbstractToRiscV as L
  open import Once.CCC.Target.RiscV64.FileSymbols using (defs-lower; refs-lower)

  prog-wf : ∀ (T : List IRFun) (tn : TableNames T) ir {σ : ISig} → LinkedProgram σ (irProgram T ir)
          → F.AsmWF (C.emitProgram riscv64 (irProgram T ir))
  prog-wf T tn ir lk = record
    { defined-once = subst Unique (sym defs≡) (prog-unique-at T tn ir)
    ; resolved     = resolved-at defs≡ refs≡ (prog-resolved-at _ (irProgram T ir) lk)
    ; entry-in     = s≤s z≤n
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (prog-defs-valid (irProgram T ir))
    ; externs-valid = prog-externs-valid (irProgram T ir)
    }
    where
      p = irProgram T ir
      G = C.emitProgram riscv64 p
      code≡ : F.Image.code G ≡ L.compile-trace (C.image-of p)
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.image-of p) (prog-nn T ir))
      defs≡ : F.defs G ≡ prog-defs p
      defs≡ = cong (λ z → F.heap-sym ∷ "_start" ∷ z)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.image-of p))) (map-fst _ _))
      refs≡ : F.refs (F.Image.code G) ≡ arefs (C.image-of p)
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.image-of p))

  lib-wf : ∀ (T : List IRFun) (tn : TableNames T) {σ : ISig} → All (λ e → Linked σ T (fbody e)) T
         → F.AsmWF (C.emitLibrary riscv64 T)
  lib-wf T tn tl = record
    { defined-once = subst Unique (sym defs≡) (lib-unique-at T tn)
    ; resolved     = resolved-at defs≡ refs≡ (lib-resolved-at _ T tl)
    ; entry-in     = tt
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (lib-defs-valid T)
    ; externs-valid = externs-valid (C.lib-program T)
    }
    where
      G = C.emitLibrary riscv64 T
      code≡ : F.Image.code G ≡ L.compile-trace (C.lib-image T)
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 (C.lib-image T) (lib-nn T))
      defs≡ : F.defs G ≡ lib-defs T
      defs≡ = cong (F.heap-sym ∷_)
                (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower (C.lib-image T)))
                            (map-fst _ _))
      refs≡ : F.refs (F.Image.code G) ≡ arefs (C.lib-image T)
      refs≡ = trans (cong F.refs code≡) (refs-lower (C.lib-image T))

  file-wf : ∀ (doOpt : Bool) (m : Core.Resolved) (G : C.FileOf riscv64) → C.compileFileFromModule IR.Heap doOpt riscv64 m ≡ inj₂ G
          → AsmWF-of riscv64 G
  file-wf doOpt m G eq = by (C.moduleToIR-aux (C.compileResolvedModule IR.Heap doOpt m)) refl
    where
      T = C.tableOfResult (C.compileResolvedModule IR.Heap doOpt m)
      by : ∀ (r : Maybe _) → C.moduleToIR-aux (C.compileResolvedModule IR.Heap doOpt m) ≡ r → AsmWF-of riscv64 G
      by (just ir) mi = subst F.AsmWF (sym (file-is-emit-at doOpt riscv64 m G ir eq mi))
                          (prog-wf T (table-names-at doOpt m) ir (build-linked doOpt m ir mi))
      by nothing   mi = subst F.AsmWF (sym (file-is-lib-at doOpt riscv64 m G eq mi))
                          (lib-wf T (table-names-at doOpt m) (build-table-linked doOpt m))

------------------------------------------------------------------------
-- THE THEOREM (was a postulate, D262).
------------------------------------------------------------------------
file-wf : ∀ (arch : Arch) (doOpt : Bool) (m : Core.Resolved) (F : C.FileOf arch)
        → C.compileFileFromModule IR.Heap doOpt arch m ≡ inj₂ F
        → AsmWF-of arch F
file-wf x86-64  = X8664W.file-wf
file-wf x86-32  = X8632W.file-wf
file-wf riscv64 = RiscV64W.file-wf
