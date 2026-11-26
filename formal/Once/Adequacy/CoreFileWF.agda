-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreFileWF — plan 0.146 B1.7 step 3 (D466): ★ A BACKEND'S
-- FILE OF AN IMAGE IS WELL-FORMED when the image's symbols are.
--
-- Each arch's file of an image (`Target.<Arch>.Backend.file`: the image's
-- code from its entry, its blocks' table, its externs) defines `once_main`,
-- the image's labels and the blocks' symbols, and references the image's
-- (`<Arch>.FileSymbols`). So `AsmWF` is the image's facts: its definitions
-- once each, its references among them or the externs, every symbol one `as`
-- reads (`ImageValid`). The linear core's image meets them (`ImageSyms`).
------------------------------------------------------------------------

module Once.Adequacy.CoreFileWF where

import Data.Nat
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.CCC.Codegen.ImageSymbols using (adefs; arefs; entry-symbol)
open import Once.CCC.Label using (e-thunk; e-fn)
open import Once.CCC.Codegen.ImageExterns using (image-externs; ext-syms; ext-sym; ext-at; Defs; ImageWF)
open import Once.Target.AsmSymbol using (AsmSym)
open import Once.Target.SymbolValid using (once-symbol-path-asm)
open import Once.Target.Backend using (file-table)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.SigOp.Info using (SigOpInfo; SigOpSem; blockV; primV; ffiV; callsV; emitsV; haltsV; module SigOpInfo)
open import Once.CCC.Machine.SMCore
import Once.Compile.Emit as C
open import Once.Adequacy.ImageValid using (adefs-asm; block-syms-asm; entry-asm)

private
  map-fst : ∀ {A B D : Set} (f : A × B → D) (xs : List (A × B))
          → map proj₁ (map (λ sb → proj₁ sb , f sb) xs) ≡ map proj₁ xs
  map-fst f []       = refl
  map-fst f (x ∷ xs) = cong (proj₁ x ∷_) (map-fst f xs)


-- the defined symbols are `as`'s
defs-asm : ∀ (t : AbstractTrace) (bs : List ArithBlock) → All AsmSym (Defs t bs)
defs-asm t bs = entry-asm ∷ record-asm ∷ ++⁺ (adefs-asm t) (block-syms-asm bs)
  where
    -- D472: `once_alloc_record`, the program's allocator record
    record-asm : AsmSym "once_alloc_record"
    record-asm = (tt , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])

module X8664 where
  import Once.CCC.Target.X86-64.File as F
  import Once.CCC.Target.X86-64.AbstractToX86 as L
  import Once.Arith.Backend.X86-64.Emit as A
  open import Once.CCC.Target.X86-64.FileSymbols using (defs-lower; refs-lower)

  -- ★ x86-64's file of a room-checked image (it starts with its start, D488)
  -- a library's file: no code, no entry, nothing to define or resolve (D467)
  empty-wf : F.AsmWF (F.mkImage [] nothing [] [])
  empty-wf = record { defined-once = [] ; resolved = [] ; entry-in = tt ; defs-valid = [] ; externs-valid = [] }

  core-wf : ∀ b rsv (t″ : AbstractTrace) (bs : List ArithBlock) (ex : List String)
          → ImageWF (instr-ctrl (c-start b rsv) ∷ t″) bs ex
          → F.AsmWF (F.mkImage (proj₂ (L.compile-trace-cnt C.entry-owner 0 (instr-ctrl (c-start b rsv) ∷ t″))) (just 0) (file-table A.block-payload bs) ex)
  core-wf b rsv t″ bs ex (u , r , ev) = record
    { defined-once  = subst Unique (sym defs≡) u
    ; resolved      = subst₂′ r
    ; entry-in      = s≤s z≤n
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (defs-asm t bs)
    ; externs-valid = ev
    }
    where
      t = instr-ctrl (c-start b rsv) ∷ t″
      -- D488: the image starts with its start, whose code makes the file's entry
      G = F.mkImage (proj₂ (L.compile-trace-cnt C.entry-owner 0 t)) (just 0) (file-table A.block-payload bs) ex
      code≡ : F.Image.code G ≡ L.compile-trace t
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 t)
      defs≡ : F.defs G ≡ Defs t bs
      defs≡ = cong (λ z → "once_main" ∷ "once_alloc_record" ∷ z) (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower t)) (map-fst _ _))
      refs≡ : F.refs (F.Image.code G) ≡ arefs t
      refs≡ = trans (cong F.refs code≡) (refs-lower t)
      subst₂′ : All (λ s → s ∈ Defs t bs ⊎ s ∈ ex) (arefs t) → All (λ s → s ∈ F.defs G ⊎ s ∈ ex) (F.refs (F.Image.code G))
      subst₂′ a = subst (λ rs → All (λ s → s ∈ F.defs G ⊎ s ∈ ex) rs) (sym refs≡)
                    (subst (λ ds → All (λ s → s ∈ ds ⊎ s ∈ ex) (arefs t)) (sym defs≡) a)

module X8632 where
  import Once.CCC.Target.X86-32.File as F
  import Once.CCC.Target.X86-32.AbstractToX86-32 as L
  import Once.Arith.Backend.X86-32.Emit as A
  open import Once.CCC.Target.X86-32.FileSymbols using (defs-lower; refs-lower)

  -- a library's file: no code, no entry, nothing to define or resolve (D467)
  empty-wf : F.AsmWF (F.mkImage [] nothing [] [])
  empty-wf = record { defined-once = [] ; resolved = [] ; entry-in = tt ; defs-valid = [] ; externs-valid = [] }

  core-wf : ∀ b rsv (t″ : AbstractTrace) (bs : List ArithBlock) (ex : List String)
          → ImageWF (instr-ctrl (c-start b rsv) ∷ t″) bs ex
          → F.AsmWF (F.mkImage (proj₂ (L.compile-trace-cnt C.entry-owner 0 (instr-ctrl (c-start b rsv) ∷ t″))) (just 0) (file-table A.block-payload bs) ex)
  core-wf b rsv t″ bs ex (u , r , ev) = record
    { defined-once  = subst Unique (sym defs≡) u
    ; resolved      = subst₂′ r
    ; entry-in      = ent (L.room-fits? (rsv Data.Nat.+ b))
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (defs-asm t bs)
    ; externs-valid = ev
    }
    where
      t = instr-ctrl (c-start b rsv) ∷ t″
      -- D488: the image starts with its start, whose code (its check or its call) makes the file's entry
      ent : ∀ c → 1 Data.Nat.≤ Data.List.length ((L.fits-or-out c (L.room-code (rsv Data.Nat.+ b)) ++ L.start-tail b rsv)
                                                   ++ proj₂ (L.compile-trace-cnt C.entry-owner 0 t″))
      ent true  = s≤s z≤n
      ent false = s≤s z≤n
      G = F.mkImage (proj₂ (L.compile-trace-cnt C.entry-owner 0 t)) (just 0) (file-table A.block-payload bs) ex
      code≡ : F.Image.code G ≡ L.compile-trace t
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 t)
      defs≡ : F.defs G ≡ Defs t bs
      defs≡ = cong (λ z → "once_main" ∷ "once_alloc_record" ∷ z) (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower t)) (map-fst _ _))
      refs≡ : F.refs (F.Image.code G) ≡ arefs t
      refs≡ = trans (cong F.refs code≡) (refs-lower t)
      subst₂′ : All (λ s → s ∈ Defs t bs ⊎ s ∈ ex) (arefs t) → All (λ s → s ∈ F.defs G ⊎ s ∈ ex) (F.refs (F.Image.code G))
      subst₂′ a = subst (λ rs → All (λ s → s ∈ F.defs G ⊎ s ∈ ex) rs) (sym refs≡)
                    (subst (λ ds → All (λ s → s ∈ ds ⊎ s ∈ ex) (arefs t)) (sym defs≡) a)

module RiscV64 where
  import Once.CCC.Target.RiscV64.File as F
  import Once.CCC.Target.RiscV64.AbstractToRiscV as L
  import Once.Arith.Backend.RiscV64.Emit as A
  open import Once.CCC.Target.RiscV64.FileSymbols using (defs-lower; refs-lower)

  -- a library's file: no code, no entry, nothing to define or resolve (D467)
  empty-wf : F.AsmWF (F.mkImage [] nothing [] [])
  empty-wf = record { defined-once = [] ; resolved = [] ; entry-in = tt ; defs-valid = [] ; externs-valid = [] }

  core-wf : ∀ b rsv (t″ : AbstractTrace) (bs : List ArithBlock) (ex : List String)
          → ImageWF (instr-ctrl (c-start b rsv) ∷ t″) bs ex
          → F.AsmWF (F.mkImage (proj₂ (L.compile-trace-cnt C.entry-owner 0 (instr-ctrl (c-start b rsv) ∷ t″))) (just 0) (file-table A.block-payload bs) ex)
  core-wf b rsv t″ bs ex (u , r , ev) = record
    { defined-once  = subst Unique (sym defs≡) u
    ; resolved      = subst₂′ r
    ; entry-in      = ent (L.room-fits? (rsv Data.Nat.+ b))
    ; defs-valid    = subst (All AsmSym) (sym defs≡) (defs-asm t bs)
    ; externs-valid = ev
    }
    where
      t = instr-ctrl (c-start b rsv) ∷ t″
      -- D488: the image starts with its start, whose code (its check or its call) makes the file's entry
      ent : ∀ c → 1 Data.Nat.≤ Data.List.length ((L.fits-or-out c (L.room-code (rsv Data.Nat.+ b)) ++ L.start-tail b rsv)
                                                   ++ proj₂ (L.compile-trace-cnt C.entry-owner 0 t″))
      ent true  = s≤s z≤n
      ent false = s≤s z≤n
      G = F.mkImage (proj₂ (L.compile-trace-cnt C.entry-owner 0 t)) (just 0) (file-table A.block-payload bs) ex
      code≡ : F.Image.code G ≡ L.compile-trace t
      code≡ = cong proj₂ (L.compile-trace-cnt-agrees C.entry-owner 0 t)
      defs≡ : F.defs G ≡ Defs t bs
      defs≡ = cong (λ z → "once_main" ∷ "once_alloc_record" ∷ z) (cong₂ _++_ (trans (cong F.label-defs code≡) (defs-lower t)) (map-fst _ _))
      refs≡ : F.refs (F.Image.code G) ≡ arefs t
      refs≡ = trans (cong F.refs code≡) (refs-lower t)
      subst₂′ : All (λ s → s ∈ Defs t bs ⊎ s ∈ ex) (arefs t) → All (λ s → s ∈ F.defs G ⊎ s ∈ ex) (F.refs (F.Image.code G))
      subst₂′ a = subst (λ rs → All (λ s → s ∈ F.defs G ⊎ s ∈ ex) rs) (sym refs≡)
                    (subst (λ ds → All (λ s → s ∈ ds ⊎ s ∈ ex) (arefs t)) (sym defs≡) a)
