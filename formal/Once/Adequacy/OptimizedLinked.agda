-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.OptimizedLinked — THE OPTIMIZED BUILD'S PROGRAM IS LINKED
-- (plan 0.39 C).
--
-- The optimized build's table has the source build's entries, name for name
-- and type for type (`OptimizedModule.crm-opt`), each body the direct-call
-- form of an optimized body. A call that names an entry of one table names
-- the same entry of the other, and the optimizer calls nothing new
-- (`OptimizeLinked.optimize-linked`), so the source program's linkedness
-- (`ProgramLinked.moduleToProgram-linked`) carries over.
------------------------------------------------------------------------

module Once.Adequacy.OptimizedLinked where

import Data.Bool
open import Data.Bool using (Bool; true; false)
open import Once.Adequacy.ImageResolved using (module LibLinked)
import Once.CanonicalName
import Once.IRTy
import Once.Module
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (var; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; μ; ν)
open import Once.IR
open import Once.IRTy using (⌊_⌋; _⇛_)
open import Once.Contract using (ISig)
open import Once.Denotation.Program using (IRFun; irFun; irProgram; Linked; LinkedAt; LinkedProgram)
open import Once.Adequacy.ElaborateLinked using (linked-mono)
open import Once.Optimize using (optimize)
import Once.Compile as C
open C using (CompiledFun; mkCompiledFun)
import Once.Parser.Module.Core as P
open import Once.Adequacy.OptimizeLinked using (optimize-linked)
open import Once.Adequacy.OptimizedModule using (optCF; optCFs; optRes; crm-opt; moduleToIR-opt)
open import Once.Adequacy.ProgramLinked using (moduleToProgram-linked)
open import Once.Contract using () renaming (ISig to Sig)

-- | Two entries with the same name and types, the first's body linked
-- wherever the second's is (against tables that link the same calls).
data EntrySame : IRFun → IRFun → Set where
  same : ∀ n D C {b′ b : IR D C}
       → (∀ {σ : ISig} {t t′ : List IRFun} → (∀ {f A B} → LinkedAt t f A B → LinkedAt t′ f A B)
            → Linked σ t b → Linked σ t′ b′)
       → EntrySame (irFun n D C b′) (irFun n D C b)

data Same : List IRFun → List IRFun → Set where
  s-nil  : Same [] []
  s-cons : ∀ {e′ e t′ t} → EntrySame e′ e → Same t′ t → Same (e′ ∷ t′) (e ∷ t)

-- a call that names an entry of one table names the same entry of the other
linkedAt-same : ∀ {t′ t} → Same t′ t → ∀ {f A B} → LinkedAt t f A B → LinkedAt t′ f A B
linkedAt-same s-nil ()
linkedAt-same (s-cons {t′ = t′} {t = t} (same n D C _) s) {f} {A} {B} l = at (n Once.CanonicalName.≟ᶜ f) (D Once.IRTy.≟IRTy A) (C Once.IRTy.≟IRTy B) l
  where
    at : ∀ d₁ d₂ d₃ → Once.Denotation.Program.LinkedAt-at (irFun n D C _) t f A B d₁ d₂ d₃
       → Once.Denotation.Program.LinkedAt-at (irFun n D C _) t′ f A B d₁ d₂ d₃
    at (yes _) (yes _) (yes _) l = tt
    at (yes _) (yes _) (no _)  l = linkedAt-same s l
    at (yes _) (no _)  _       l = linkedAt-same s l
    at (no _)  _       _       l = linkedAt-same s l

all-same : ∀ {σ : ISig} {T′ T : List IRFun} (h : ∀ {f A B} → LinkedAt T f A B → LinkedAt T′ f A B) {t′ t} → Same t′ t
         → All (λ e → Linked σ T (IRFun.fbody e)) t → All (λ e → Linked σ T′ (IRFun.fbody e)) t′
all-same h s-nil [] = []
all-same h (s-cons (same n D C bl) s) (l ∷ ls) = bl h l ∷ all-same h s ls

-- | A program whose table is the same as a linked one's is linked.
linked-same : ∀ {σ : ISig} {t′ t} → Same t′ t → ∀ ir → LinkedProgram σ (irProgram t ir) → LinkedProgram σ (irProgram t′ ir)
linked-same s ir (lm , lt) = linked-mono (linkedAt-same s) ir lm , all-same (linkedAt-same s) s lt

------------------------------------------------------------------------
-- The optimized build's table
------------------------------------------------------------------------

private
  opt-l : ∀ {σ : ISig} {t t′ : List IRFun} (h : ∀ {f A B} → LinkedAt t f A B → LinkedAt t′ f A B) {X Y} (ir : IR X Y)
        → Linked σ t ir → Linked σ t′ (optimize ir)
  opt-l {σ} {t} {t′} h ir l = optimize-linked σ t′ ir (linked-mono h ir l)

  -- the direct-call form: `apply ∘ ⟨ ir ∘ terminal , id ⟩`
  dc-l : ∀ {σ : ISig} {t t′ : List IRFun} (h : ∀ {f A B} → LinkedAt t f A B → LinkedAt t′ f A B) {X Z} (ir : IR Once.IRTy.Unit (X ⇛ Z))
       → Linked σ t (apply ∘ ⟨ ir ∘ terminal , id ⟩) → Linked σ t′ (apply ∘ ⟨ optimize ir ∘ terminal , id ⟩)
  dc-l h ir (_ , ((l , _) , _)) = tt , ((opt-l h ir l , tt) , tt)

entry-same : ∀ (cf : CompiledFun) → EntrySame (C.irFunOf (optCF cf)) (C.irFunOf cf)
entry-same (mkCompiledFun n (A ⇒[ mk-kind Zero π ] B) ir) = same n _ _ (λ h → dc-l h ir)
entry-same (mkCompiledFun n (A ⇒[ mk-kind One  π ] B) ir) = same n _ _ (λ h → dc-l h ir)
entry-same (mkCompiledFun n (A ⇒[ mk-kind Many π ] B) ir) = same n _ _ (λ h → dc-l h ir)
entry-same (mkCompiledFun n Unit    ir) = same n _ _ (λ h → opt-l h ir)
entry-same (mkCompiledFun n Void    ir) = same n _ _ (λ h → opt-l h ir)
entry-same (mkCompiledFun n (A * B) ir) = same n _ _ (λ h → opt-l h ir)
entry-same (mkCompiledFun n (A + B) ir) = same n _ _ (λ h → opt-l h ir)
entry-same (mkCompiledFun n Int     ir) = same n _ _ (λ h → opt-l h ir)
entry-same (mkCompiledFun n Float   ir) = same n _ _ (λ h → opt-l h ir)
entry-same (mkCompiledFun n (μ F)   ir) = same n _ _ (λ h → opt-l h ir)
entry-same (mkCompiledFun n (ν F f) ir) = same n _ _ (λ h → opt-l h ir)
entry-same (mkCompiledFun n (var x) ir) = same n _ _ (λ h → opt-l h ir)

private
  same-go : ∀ cfs {s′ s} → Same s′ s → Same (C.tableOf-go (optCFs cfs) s′) (C.tableOf-go cfs s)
  same-go []         sm = sm
  same-go (cf ∷ cfs) sm = same-go cfs (s-cons (entry-same cf) sm)

table-same : ∀ r → Same (C.tableOfResult (optRes r)) (C.tableOfResult r)
table-same (inj₁ _)   = s-nil
table-same (inj₂ cfs) = same-go cfs s-nil

-- | The optimized build's program is linked against the module's signatures.
optimized-linked : ∀ (m : P.Resolved) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) → C.moduleToIR m ≡ just ir
                 → LinkedProgram (Once.Module.moduleSig m)
                     (irProgram (C.tableOfResult (C.compileResolvedModule Heap Data.Bool.true m)) ir)
optimized-linked m ir mi =
  subst (λ r → LinkedProgram (Once.Module.moduleSig m) (irProgram (C.tableOfResult r) ir))
        (sym (crm-opt Heap m))
        (linked-same (table-same (C.compileResolvedModule Heap Data.Bool.false m)) ir (moduleToProgram-linked m ir mi))

------------------------------------------------------------------------
-- Either build: what the file's proofs need of the table
------------------------------------------------------------------------

private
  T : Bool → P.Resolved → List IRFun
  T doOpt m = C.tableOfResult (C.compileResolvedModule Heap doOpt m)

build-linked : ∀ (doOpt : Bool) (m : P.Resolved) (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)
             → C.moduleToIR-aux (C.compileResolvedModule Heap doOpt m) ≡ just ir
             → LinkedProgram (Once.Module.moduleSig m) (irProgram (T doOpt m) ir)
build-linked false m ir mi = moduleToProgram-linked m ir mi
build-linked true  m ir mi = optimized-linked m ir (trans (sym (moduleToIR-opt m)) mi)

build-table-linked : ∀ (doOpt : Bool) (m : P.Resolved)
                   → All (λ e → Linked (Once.Module.moduleSig m) (T doOpt m) (IRFun.fbody e)) (T doOpt m)
build-table-linked false m = LibLinked.lib-table-linked m
build-table-linked true  m =
  subst (λ r → All (λ e → Linked (Once.Module.moduleSig m) (C.tableOfResult r) (IRFun.fbody e)) (C.tableOfResult r))
        (sym (crm-opt Heap m))
        (all-same (linkedAt-same s) s (LibLinked.lib-table-linked m))
  where s = table-same (C.compileResolvedModule Heap false m)
