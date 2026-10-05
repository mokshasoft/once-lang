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

open import Once.Denotation.TraceMonad using (Interp; pureHalf)

-- Plan 0.105: at an interpretation `ι`.
-- Plan 0.105 (D257, D061): no fixed world — a typed module's meaning is
-- relative to an implementation of the signatures it is compiled against.
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
open import Once.Spec.Module using (ModuleTyped; ModuleTyped-ef; HasValidMain; HasValidMain-ef; moduleSig; moduleSig-ef; teleSig; teleSig≡entrySig)
open import Once.Spec.Contract using (ISig; Impl)
open import Once.Denotation.TraceMonad using (Interp; interp; pureHalf)
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
open import Once.Adequacy.SourceTrace using (⟦_⟧IR)
open import Once.Compile using (moduleToIR; moduleToIR-aux; mainCall; tableOf-go; moduleTable; tableOfResult)
import Once.Adequacy.FunBundle as FB
open import Once.Denotation.Behavior using (at)
open import Once.Denotation.Program using (irProgram)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Denotation.TraceMonad using (projTrace)
open import Data.Maybe using (just)
import Once.Adequacy.TeleWalk as TW
import Once.Adequacy.TeleWalk.Invariant as TWI
import Once.Adequacy.EntriesValid as EV
open EV using (valid-mod)
import Once.Adequacy.TelePosition as TP
import Once.Spec.Core.Translate as TR
open import Once.Denotation.Program using (tableEnv; IRFun)
open import Once.Denotation.Trace using (SigOpEvent)
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
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans; cong; cong₂; subst)

------------------------------------------------------------------------
-- The typed module as a core program (6c).
------------------------------------------------------------------------

-- The interpretation signatures the core program is compiled against: the
-- module's FFI declarations, as its typing fixes them.
typedSig-ef : ∀ (m : P.Module) ef (mt : ModuleTyped-ef m ef) → ISig
typedSig-ef m (inj₁ _)  ()
typedSig-ef m (inj₂ es) mt = teleSig mt

typedSig : Typed → ISig
typedSig (m , mt , hvm) = typedSig-ef m (C.extractFunctions (C.extractAliases m) m) mt

typedProgram-ef : ∀ (m : P.Module) ef (mt : ModuleTyped-ef m ef) → HasValidMain-ef m ef mt → Program (typedSig-ef m ef mt)
typedProgram-ef m (inj₁ _)  () _
typedProgram-ef m (inj₂ es) mt (_ , mi) = TR.toProgram₀ mt mi

typedProgram : (tp : Typed) → Program (typedSig tp)
typedProgram (m , mt , hvm) = typedProgram-ef m (C.extractFunctions (C.extractAliases m) m) mt hvm

-- …which are the module's signatures, read off its entries.
typed-sig-ef : ∀ (m : P.Module) ef (mt : ModuleTyped-ef m ef) → typedSig-ef m ef mt ≡ moduleSig-ef ef
typed-sig-ef m (inj₁ _)  ()
typed-sig-ef m (inj₂ es) mt = teleSig≡entrySig mt

typed-sig : ∀ (tp : Typed) → typedSig tp ≡ moduleSig (proj₁ tp)
typed-sig (m , mt , hvm) = typed-sig-ef m (C.extractFunctions (C.extractAliases m) m) mt

-- An implementation of the module's signatures implements the core program's.
implFor : ∀ (tp : Typed) → Impl (moduleSig (proj₁ tp)) → Impl (typedSig tp)
implFor tp I = subst Impl (sym (typed-sig tp)) I

-- A world built from a transported implementation is the same world.
interp-subst : ∀ {Σ₁ Σ₂ : ISig} (e : Σ₁ ≡ Σ₂) (I : Impl Σ₂) → interp Σ₁ (subst Impl (sym e) I) ≡ interp Σ₂ I
interp-subst refl I = refl

private
  -- The compiled program's run, in a world.
  runIRAt : Interp → List IRFun → ℕ → List SigOpEvent
  runIRAt ι′ tbl n = projTrace ι′ (evalᴰ fmt (tableEnv fmt (pureHalf ι′) tbl) mainCall tt) n

  core-ef : ∀ (m : P.Module) (ef : String ⊎ List C.Entry) (mt : ModuleTyped-ef m ef) (hvm : HasValidMain-ef m ef mt)
              {es} → ef ≡ inj₂ es → AllPairs _≢_ (map TP.entryName es) → All EV.MonoValid es
            → (b : FB.FunBundle C.emptyCScope es) (I : Impl (moduleSig-ef ef)) (n : ℕ)
            → runIRAt (interp (moduleSig-ef ef) I) (tableOf-go (FB.bundle→compiled b) []) n
              ≡ runProgram fmt (typedProgram-ef m ef mt hvm) (subst Impl (sym (typed-sig-ef m ef mt)) I) n
  core-ef m .(inj₂ _) mt (_ , mi) refl dist vd b I n =
    trans (cong (λ ι′ → runIRAt ι′ (tableOf-go (FB.bundle→compiled b) []) n) (sym (interp-subst (teleSig≡entrySig mt) I)))
          (TWm.walk mt b mi Tele.[] TR.[] TR.[] (λ ()) [] inv₀ (λ k → k) (dist , TP.none-in-empty _) vd n)
    where
      I′ = subst Impl (sym (teleSig≡entrySig mt)) I
      module TWm = TW fmt (teleSig mt) I′
      inv₀ : TWI.Inv fmt (teleSig mt) I′ C.emptyCScope Tele.[] TR.[] TR.[] []
      inv₀ = record { valid = tt ; irf = λ () ; iself = [] ; rel = λ _ _ _ _ _ → tt , tt , refl }

------------------------------------------------------------------------
-- THE LINK: the compiled program means the core program.
------------------------------------------------------------------------

-- Plan 0.105: for EVERY implementation `I` of the module's signatures: the
-- compiled program run in the world they make, and the core program run with `I`.
program-core :
  ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : HasValidMain m mt) (I : Impl (moduleSig m))
    (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir) (n : ℕ)
  → at (⟦ just (irProgram (moduleTable m) ir) ⟧IR fmt (interp (moduleSig m) I)) n
    ≡ runProgram fmt (typedProgram (m , mt , hvm)) (implFor (m , mt , hvm) I) n
program-core m mt hvm I ir mi n with FB.program-node m ir mi
... | es , ef , b , ceq =
  trans (cong₂ (λ tbl x → projTrace ι (evalᴰ fmt (tableEnv fmt (pureHalf ι) tbl) x tt) n) (cong tableOfResult ceq) ir≡)
        (core-ef m (C.extractFunctions (C.extractAliases m) m) mt hvm ef (TP.entries-distinct m ef) (valid-mod m ef) b I n)
  where
    ι = interp (moduleSig m) I
    ir≡ : ir ≡ mainCall
    ir≡ = FB.bundle-find-call b (trans (sym (FB.find-agree b)) (trans (sym (cong moduleToIR-aux ceq)) mi))
