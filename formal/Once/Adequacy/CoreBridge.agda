-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreBridge — plan 0.103 phase 6a: THE APEX MEANS THE CORE.
--
-- A typed module IS a core program (6c, `Spec.Core.Translate.toProgram`), and
-- its meaning is the core's (`Telescope.runProgram`): every definition typed
-- once, a reference meaning the entry (D239, D243, D246), and the program
-- running its `main` entry (D253). This module proves the link between it and
-- the compiled chain:
--
--   exec ≋ IR program (codegen)                      — proved (backend)
--        ≋ core `runProgram (typedProgram tp)`         — `program-core` (below)
--
-- `program-core` is the telescope walk (`TeleWalk` over `ModTele`): each
-- compiled table entry means its core entry, by induction on the telescope
-- (the 6b meaning bridge, clause by clause, at the telescope's environments;
-- each linked telescope reference means the entry's instance, 6e). `main` is
-- an entry like any other, and the compiled program's `main` is the call of it.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.CoreBridge (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
import Once.Compile as C
import Once.Parser.Module.Core as P
open import Once.Spec.Module using (ModuleTyped; ModuleTyped-ef; HasValidMain; HasValidMain-ef)
open import Once.Spec.Program using (Typed)
open import Once.Spec.Core.Telescope using (Program; program; runProgram; IOUnit; noVars)
open import Once.Spec.Core.Translate using (toProgram)
import Once.Spec.Core.Translate as TR
import Once.Spec.Core.Telescope as Tele
import Once.Spec.Core.PolyTyping as PT
import Once.Spec.Core.Meaning as GM
open import Once.Denotation.Behavior using (Behavior; mkBehavior)
open import Once.Denotation.TraceMonad using (T; _>>=T_; PrefixFamily; bnd; sat; coh)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Adequacy.SourceTrace using (moduleToIR; moduleToIR-aux; mainCall; tableOf-go; moduleTable; ⟦_⟧IR)
import Once.Adequacy.FunBundle as FB
open import Once.Denotation.Behavior using (at)
open import Once.Denotation.Program using (irProgram)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.TraceMonad using (projTrace)
open import Data.Maybe using (just)
import Once.Adequacy.TeleWalk fmt as TW
import Once.Spec.Core.Translate as TR
open import Once.Adequacy.SourceTrace using (tableOfResult)
open import Once.Denotation.Program using (tableEnv)
open import Once.Spec.Module using (EffUU)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
import Once.Parser
open import Function using (case_of_)
import Once.Adequacy.NameClash as NC
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans; cong; cong₂)

------------------------------------------------------------------------
-- The typed module as a core program (6c).
------------------------------------------------------------------------

typedProgram-ef : ∀ (m : P.Module) ef (mt : ModuleTyped-ef m ef) → HasValidMain-ef m ef mt → Program
typedProgram-ef m (inj₁ _)  () _
typedProgram-ef m (inj₂ es) mt (_ , mi) = toProgram Tele.[] TR.[] TR.[] (λ ()) mt mi

typedProgram : Typed → Program
typedProgram (m , mt , hvm) = typedProgram-ef m (C.extractFunctions (C.extractAliases m) m) mt hvm

-- The walk's premises at the start: the empty scope, and the entries' names
-- (D249: the extractor's guard).
entries-distinct : ∀ (m : P.Module) {es : List C.Entry}
  → C.extractFunctions (C.extractAliases m) m ≡ inj₂ es → AllPairs _≢_ (map TW.entryName es)
entries-distinct (P.mkModule ds) eq = NC.guard-entries (C.extractFunctions-go (C.extractAliases (P.mkModule ds)) ds C.nothing) eq

private
  none-in-empty : ∀ (xs : List String) → All (λ x → All (x ≢_) (TW.scopeNames C.emptyCScope)) xs
  none-in-empty []       = []
  none-in-empty (x ∷ xs) = [] ∷ none-in-empty xs

  inv₀ : TW.Inv C.emptyCScope Tele.[] TR.[] TR.[] []
  inv₀ = record { valid = tt ; irf = λ () ; iself = [] ; rel = λ _ _ _ _ _ → tt , tt }

  -- Every definition's name is an identifier: the extractor's guard.
  valid-of : ∀ (es : List C.Entry) → Once.Parser.allValidIdentB (Once.Parser.emittedNames (Once.Parser.funsOf es)) ≡ true
           → All TW.MonoValid es
  valid-of []                   eq = []
  valid-of (C.e-poly pfi ∷ es) eq = tt ∷ valid-of es eq
  valid-of (C.e-fun fi ∷ es)   eq with C.FunInfo.funIsPrimitive fi in ep
  ... | true  = (λ p → case trans (sym ep) p of λ ()) ∷ valid-of es eq
  ... | false = (λ _ → NC.∧-elimˡ eq) ∷ valid-of es (NC.∧-elimʳ eq)

  valid-mod : ∀ (m : P.Module) {es} → C.extractFunctions (C.extractAliases m) m ≡ inj₂ es → All TW.MonoValid es
  valid-mod (P.mkModule ds) {es} eq = valid-of es (NC.∧-elimʳ (NC.guard-true (C.extractFunctions-go (C.extractAliases (P.mkModule ds)) ds C.nothing) eq))

  core-ef : ∀ (m : P.Module) (ef : String ⊎ List C.Entry) (mt : ModuleTyped-ef m ef) (hvm : HasValidMain-ef m ef mt)
              {es} → ef ≡ inj₂ es → AllPairs _≢_ (map TW.entryName es) → All TW.MonoValid es
            → (b : FB.FunBundle C.emptyCScope es) (n : ℕ)
            → TW.RunAt (tableOf-go (FB.bundle→compiled b) []) n ≡ runProgram fmt (typedProgram-ef m ef mt hvm) n
  core-ef m .(inj₂ _) mt (_ , mi) refl dist vd b n =
    TW.walk mt b mi Tele.[] TR.[] TR.[] _ [] inv₀ (dist , none-in-empty _) vd n

------------------------------------------------------------------------
-- The compiled program, from `moduleToIR m ≡ just ir`: the entries, their
-- compile bundle, and the compile result it is.
------------------------------------------------------------------------

ProgramNode : P.Module → Set
ProgramNode m =
  Σ-syntax (List C.Entry) (λ es →
  Σ-syntax (C.extractFunctions (C.extractAliases m) m ≡ inj₂ es) (λ _ →
  Σ-syntax (FB.FunBundle C.emptyCScope es) (λ b →
    C.compileResolvedModule C.Heap false m ≡ inj₂ (FB.bundle→compiled b))))

private
  node-ce : ∀ (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (es : List C.Entry) (cv : String ⊎ List C.CompiledFun)
          → C.compileEntries C.Heap false C.emptyCScope es ≡ cv → moduleToIR-aux cv ≡ just ir
          → C.extractFunctions (C.extractAliases m) m ≡ inj₂ es → ProgramNode m
  node-ce m ir es (inj₁ _) ce mi ef = case mi of λ ()
  node-ce m ir es (inj₂ compiled) ce mi ef =
    es , ef , FB.ce-bundle C.emptyCScope es ce
       , trans (cong (C.compileResolvedModule-aux C.Heap false m) ef)
               (trans ce (cong inj₂ (sym (FB.bundle→compiled≡compiled C.emptyCScope es compiled ce))))

  node-ef : ∀ (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (efv : String ⊎ List C.Entry)
          → C.extractFunctions (C.extractAliases m) m ≡ efv
          → moduleToIR-aux (C.compileResolvedModule-aux C.Heap false m efv) ≡ just ir → ProgramNode m
  node-ef m ir (inj₁ _)  ef mi = case mi of λ ()
  node-ef m ir (inj₂ es) ef mi = node-ce m ir es (C.compileEntries C.Heap false C.emptyCScope es) refl mi ef

program-node : ∀ (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir → ProgramNode m
program-node m ir mi = node-ef m ir (C.extractFunctions (C.extractAliases m) m) refl mi

------------------------------------------------------------------------
-- THE LINK: the compiled program means the core program.
------------------------------------------------------------------------

program-core :
  ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : HasValidMain m mt) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir) (n : ℕ)
  → at (⟦ just (irProgram (moduleTable m) ir) ⟧IR fmt) n ≡ runProgram fmt (typedProgram (m , mt , hvm)) n
program-core m mt hvm ir mi n with program-node m ir mi
... | es , ef , b , ceq =
  trans (cong₂ (λ tbl x → projTrace (evalᴰ fmt (tableEnv fmt tbl) x tt) n) (cong tableOfResult ceq) ir≡)
        (core-ef m (C.extractFunctions (C.extractAliases m) m) mt hvm ef (entries-distinct m ef) (valid-mod m ef) b n)
  where
    ir≡ : ir ≡ mainCall
    ir≡ = FB.bundle-find-call b (trans (sym (FB.find-agree b)) (trans (sym (cong moduleToIR-aux ceq)) mi))
