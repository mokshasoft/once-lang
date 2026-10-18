{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Source — what a source text denotes (what `Spec.Correct` is
-- instantiated with).
--
-- A SOURCE is a complete compilation unit: the program's text and the texts
-- of the modules it imports, by path. It denotes a TYPED program when its
-- texts parse (`Spec.Surface.Grammar`) and the program's module denotes a
-- program over its signature (`Spec.Surface.Program`). What the program does
-- is its behaviour against an Interpretation of that signature
-- (`Spec.Core.Program.behaviour`): its trace — the calls it makes, in a run
-- that may go on forever. Two behaviours are the same when their traces are
-- weakly bisimilar (D317); that is the equivalence a correct compiler
-- preserves (`Spec.Correct`).
--
-- A target owes an answer only for the programs it can express
-- (ADMISSIBLE): every integer literal, a negated one read as negative, fits
-- the target's signed range. (Arithmetic is not checked: it wraps.)
------------------------------------------------------------------------

module Once.Spec.Source where

open import Data.Integer using (ℤ; -_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Unit using (⊤)
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
import Once.Spec.Word as Word
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Surface.Grammar using (Parses)
open import Once.Spec.Surface.Resolution using (ModuleMap)
open import Once.Spec.Surface.Program using (Denotes)
import Once.Spec.Core.Program as CoreProgram
import Once.Spec.Observation as Observation
open import Once.Spec.Trace using (Tr; _≈ᵗ⟨_⟩_)

record Source : Set where
  field
    text    : String                          -- the program
    modules : List (List String × String)     -- the modules it may import, by path
open Source

record Typed : Set where
  field
    module′   : Module
    signature : Signature
    program   : CoreProgram.Program signature
open Typed

-- Each module text parses, at its path.
ParsesModules : List (List String × String) → ModuleMap → Set
ParsesModules = Pointwise (λ { (p , txt) (p′ , m) → p ≡ p′ × Parses txt m })

_⊢_ : Source → Typed → Set
src ⊢ tp = Σ[ mm ∈ ModuleMap ]
             Parses (text src) (module′ tp) × ParsesModules (modules src) mm
           × Denotes mm (module′ tp) (signature tp) (program tp)

------------------------------------------------------------------------
-- What a target can express
------------------------------------------------------------------------

intLits  : Expr → List ℤ
negLits : Expr → List ℤ   -- under a negation: a literal there is negative
intLits (RInt i)              = i ∷ []
intLits (RNeg e)              = negLits e
intLits (RVar _)              = []
intLits (RQualified _ _)      = []
intLits (RResolved _)         = []
intLits (RApp f x)            = intLits f ++ intLits x
intLits (RLam _ b)            = intLits b
intLits (RLet _ e b)          = intLits e ++ intLits b
intLits (RPair a b)           = intLits a ++ intLits b
intLits (RDestruct e _ l _ r) = intLits e ++ intLits l ++ intLits r
intLits RUnit                 = []
intLits (RFloat _ _ _)        = []
intLits (RAnnot e _)          = intLits e
intLits (RBinOp _ a b)        = intLits a ++ intLits b
negLits (RInt i) = (- i) ∷ []
{-# CATCHALL #-}
negLits e        = intLits e

declLits : List Decl → List ℤ
declLits []                     = []
declLits (DFunDef _ e ∷ ds)     = intLits e ++ declLits ds
declLits (DTypeSig _ _ ∷ ds)    = declLits ds
declLits (DSignature _ _ ∷ ds)  = declLits ds
declLits (DTypeAlias _ _ _ ∷ ds) = declLits ds
declLits (DImport _ ∷ ds)       = declLits ds

Admissible : TargetNum → Typed → Set
Admissible fmt tp = All (Word.Width.InRange (TargetNum.int-bits fmt)) (declLits (Module.decls (module′ tp)))

-- What the program does, against an Interpretation of its signature.
behaviour : TargetNum → (tp : Typed) → Observation.Interp (signature tp) → Tr ⊤
behaviour fmt tp = CoreProgram.behaviour (signature tp) fmt (program tp)

-- The same behaviour: weakly bisimilar traces.
SameBehaviour : Tr ⊤ → Tr ⊤ → Set
SameBehaviour t t′ = t ≈ᵗ⟨ _≡_ ⟩ t′
