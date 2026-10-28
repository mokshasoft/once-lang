-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.OptimizedTable — THE OPTIMIZED BUILD'S PROGRAM HAS THE
-- SOURCE PROGRAM'S TRACE (plan 0.39 A + B).
--
-- The optimized build's table is the table of the optimized functions
-- (`OptimizedModule.crm-opt`): each entry the direct-call form
-- (`directCallIR`) of an optimized body. The direct-call form is a
-- congruence (`apply ∘ ⟨ ir ∘ terminal , id ⟩` at an arrow, the body itself
-- otherwise), and the optimizer keeps each body's run
-- (`OptimizePreserves.optimize-rel`), so the two tables are related entry by
-- entry, and the programs, with the same `main` (`moduleToIR-opt`), have the
-- same trace.
------------------------------------------------------------------------

module Once.Adequacy.OptimizedTable where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import Relation.Binary.PropositionalEquality

open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.Spec.Type using (Ty; var; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float; μ; ν)
open import Once.IR
import Once.IRTy as II
open import Once.IR.Semantics.Trace using (Interp; pureHalf)
open import Once.Denotation.Program using (IRFun; irFun; IRProgram; irProgram; runIR)
open import Once.Denotation.TraceMonadInfLaws using (RelS-bind; relS-ret)
open import Once.Denotation.TraceTr using (trT∞)
open import Once.Denotation.EvalRel using (RelEnv)
open import Once.Spec.Trace using (_≈ᵗ⟨_⟩_)
open import Once.Optimize using (optimize)
import Once.Compile as C
open C using (CompiledFun; mkCompiledFun)
import Once.Parser.Module.Core as P
open import Once.Adequacy.OptimizePreserves using (Rel; optimize-rel; EntryRel; e-rel; TblRel; t-nil; t-cons; table-trace)
open import Once.Adequacy.OptimizedModule using (optCF; optCFs; optRes; crm-opt)

module _ (fmt : TargetNum) where

  -- the direct-call form at an arrow keeps the relation
  dc-rel : ∀ {ρ ρ′} (re : RelEnv fmt ρ ρ′) {X Y : II.IRTy} (x′ x : IR II.Unit (X II.⇛ Y))
         → Rel fmt re x′ x → Rel fmt re (apply ∘ ⟨ x′ ∘ terminal , id ⟩) (apply ∘ ⟨ x ∘ terminal , id ⟩)
  dc-rel re x′ x rx r =
    RelS-bind (RelS-bind (RelS-bind (relS-ret tt) (λ _ → rx tt)) (λ r₁ → RelS-bind (relS-ret r) (λ r₂ → relS-ret (r₁ , r₂))))
              (λ q → proj₁ q (proj₂ q))

  -- | Each optimized entry is related to the source's.
  entry-opt : ∀ (cf : CompiledFun) → EntryRel fmt (C.irFunOf (optCF cf)) (C.irFunOf cf)
  entry-opt (mkCompiledFun n (A ⇒[ mk-kind Zero π ] B) ir) = e-rel n _ _ (λ re → dc-rel re (optimize ir) ir (optimize-rel fmt re ir))
  entry-opt (mkCompiledFun n (A ⇒[ mk-kind One  π ] B) ir) = e-rel n _ _ (λ re → dc-rel re (optimize ir) ir (optimize-rel fmt re ir))
  entry-opt (mkCompiledFun n (A ⇒[ mk-kind Many π ] B) ir) = e-rel n _ _ (λ re → dc-rel re (optimize ir) ir (optimize-rel fmt re ir))
  entry-opt (mkCompiledFun n Unit    ir) = e-rel n _ _ (λ re → optimize-rel fmt re ir)
  entry-opt (mkCompiledFun n Void    ir) = e-rel n _ _ (λ re → optimize-rel fmt re ir)
  entry-opt (mkCompiledFun n (A * B) ir) = e-rel n _ _ (λ re → optimize-rel fmt re ir)
  entry-opt (mkCompiledFun n (A + B) ir) = e-rel n _ _ (λ re → optimize-rel fmt re ir)
  entry-opt (mkCompiledFun n Int     ir) = e-rel n _ _ (λ re → optimize-rel fmt re ir)
  entry-opt (mkCompiledFun n Float   ir) = e-rel n _ _ (λ re → optimize-rel fmt re ir)
  entry-opt (mkCompiledFun n (μ F)   ir) = e-rel n _ _ (λ re → optimize-rel fmt re ir)
  entry-opt (mkCompiledFun n (ν F f) ir) = e-rel n _ _ (λ re → optimize-rel fmt re ir)
  entry-opt (mkCompiledFun n (var x) ir) = e-rel n _ _ (λ re → optimize-rel fmt re ir)

  private
    tbl-go : ∀ cfs {s′ s} → TblRel fmt s′ s → TblRel fmt (C.tableOf-go (optCFs cfs) s′) (C.tableOf-go cfs s)
    tbl-go []         tr = tr
    tbl-go (cf ∷ cfs) tr = tbl-go cfs (t-cons (entry-opt cf) tr)

  table-opt : ∀ r → TblRel fmt (C.tableOfResult (optRes r)) (C.tableOfResult r)
  table-opt (inj₁ _)   = t-nil
  table-opt (inj₂ cfs) = tbl-go cfs t-nil

-- | The optimized build's program, run with the same `main`, has the trace of
-- the source program.
optimized-trace : ∀ (fmt : TargetNum) (ι : Interp) (mod : P.Resolved) (main : IR II.Unit II.Unit)
                → trT∞ ι [] (runIR fmt (pureHalf ι) (irProgram (C.tableOfResult (C.compileResolvedModule Heap true mod)) main))
                  ≈ᵗ⟨ _≡_ ⟩ trT∞ ι [] (runIR fmt (pureHalf ι) (irProgram (C.moduleTable mod) main))
optimized-trace fmt ι mod main =
  subst (λ r → trT∞ ι [] (runIR fmt (pureHalf ι) (irProgram (C.tableOfResult r) main))
               ≈ᵗ⟨ _≡_ ⟩ trT∞ ι [] (runIR fmt (pureHalf ι) (irProgram (C.moduleTable mod) main)))
        (Relation.Binary.PropositionalEquality.sym (crm-opt Heap mod))
        (table-trace fmt ι (table-opt fmt (C.compileResolvedModule Heap false mod)) main)
