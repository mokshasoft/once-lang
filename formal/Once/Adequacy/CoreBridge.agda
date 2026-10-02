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

open import Once.Denotation.TraceMonad using (Interp)

-- Plan 0.105: at an interpretation `ι`.
module Once.Adequacy.CoreBridge (fmt : TargetNum) (ι : Interp) where

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
import Once.Adequacy.TeleWalk fmt ι as TW
import Once.Adequacy.TeleWalk.Invariant fmt ι as TWI
import Once.Adequacy.TelePosition as TP
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

private
  inv₀ : TWI.Inv C.emptyCScope Tele.[] TR.[] TR.[] []
  inv₀ = record { valid = tt ; irf = λ () ; iself = [] ; rel = λ _ _ _ _ _ → tt , tt , refl }

  -- Every definition's name is an identifier: the extractor's guard.
  valid-of : ∀ (es : List C.Entry) → Once.Parser.allValidIdentB (Once.Parser.emittedNames (Once.Parser.funsOf es)) ≡ true
           → All TWI.MonoValid es
  valid-of []                   eq = []
  valid-of (C.e-poly pfi ∷ es) eq = tt ∷ valid-of es eq
  valid-of (C.e-fun fi ∷ es)   eq with C.FunInfo.funIsPrimitive fi in ep
  ... | true  = (λ p → case trans (sym ep) p of λ ()) ∷ valid-of es eq
  ... | false = (λ _ → NC.∧-elimˡ eq) ∷ valid-of es (NC.∧-elimʳ eq)

  valid-mod : ∀ (m : P.Module) {es} → C.extractFunctions (C.extractAliases m) m ≡ inj₂ es → All TWI.MonoValid es
  valid-mod (P.mkModule ds) {es} eq = valid-of es (NC.∧-elimʳ (NC.guard-true (C.extractFunctions-go (C.extractAliases (P.mkModule ds)) ds C.nothing) eq))

  core-ef : ∀ (m : P.Module) (ef : String ⊎ List C.Entry) (mt : ModuleTyped-ef m ef) (hvm : HasValidMain-ef m ef mt)
              {es} → ef ≡ inj₂ es → AllPairs _≢_ (map TP.entryName es) → All TWI.MonoValid es
            → (b : FB.FunBundle C.emptyCScope es) (n : ℕ)
            → TW.RunAt (tableOf-go (FB.bundle→compiled b) []) n ≡ runProgram fmt ι (typedProgram-ef m ef mt hvm) n
  core-ef m .(inj₂ _) mt (_ , mi) refl dist vd b n =
    TW.walk mt b mi Tele.[] TR.[] TR.[] _ [] inv₀ (dist , TP.none-in-empty _) vd n

------------------------------------------------------------------------
-- THE LINK: the compiled program means the core program.
------------------------------------------------------------------------

program-core :
  ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : HasValidMain m mt) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir) (n : ℕ)
  → at (⟦ just (irProgram (moduleTable m) ir) ⟧IR fmt ι) n ≡ runProgram fmt ι (typedProgram (m , mt , hvm)) n
program-core m mt hvm ir mi n with FB.program-node m ir mi
... | es , ef , b , ceq =
  trans (cong₂ (λ tbl x → projTrace ι (evalᴰ fmt (tableEnv fmt (Interp.pure ι) tbl) x tt) n) (cong tableOfResult ceq) ir≡)
        (core-ef m (C.extractFunctions (C.extractAliases m) m) mt hvm ef (TP.entries-distinct m ef) (valid-mod m ef) b n)
  where
    ir≡ : ir ≡ mainCall
    ir≡ = FB.bundle-find-call b (trans (sym (FB.find-agree b)) (trans (sym (cong moduleToIR-aux ceq)) mi))
