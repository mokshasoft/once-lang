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

open import Once.Spec.Numerics using (TargetNum)


-- Plan 0.105: at an interpretation `ι`.
-- Plan 0.105 (D257, D061): no fixed world — a typed module's meaning is
-- relative to an implementation of the signatures it is compiled against.
module Once.Adequacy.CoreBridge (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Lang.Type using (Unit)
import Once.Compile as C
import Once.Parser as Parser
import Once.Parser.Module.Core as P
open import Once.Lang.Module using (ModuleTyped; ModuleTyped-ef; HasValidMain; HasValidMain-ef; moduleSig; moduleSig-ef; teleSig)
open import Once.Adequacy.ModuleLaws using (teleSig≡entrySig)
open import Once.Lang.Contract using (ISig; Impl)
open import Once.Lang.Trace using (Interp; interp; pureHalf)
open import Once.Lang.Program using (Typed)
open import Once.Lang.Core.Telescope using (Program; runProgram; runCore)
import Once.Lang.Core.Translate as TR
import Once.Lang.Core.Telescope as Tele
import Once.Lang.Core.PolyTyping as PT
import Once.Lang.Core.Meaning as GM
import Once.Denotation.Behavior
open import Once.Adequacy.SourceTrace using (⟦_⟧IR; ⟦_⟧IRᵗ)
open import Once.Spec.Trace using (Tr; _≈ᵗ⟨_⟩_)
open import Once.Denotation.TraceTr using (runTr; trT∞; RelT∞′-tr)
open import Once.Metatheory.Trace using (WB-sym)
open import Once.Compile using (moduleToIR; moduleToIR-aux; mainCall; tableOf-go; moduleTable; tableOfResult)
import Once.Adequacy.FunBundle as FB
import Once.Denotation.Behavior
open Once.Denotation.Behavior.Behavior using (at)
open import Once.Denotation.Program using (irProgram)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Once.Lang.Trace using (projTrace)
open import Data.Maybe using (just)
import Once.Adequacy.TeleWalk as TW
import Once.Adequacy.TeleWalk.Invariant as TWI
import Once.Adequacy.TelePosition as TP
import Once.Lang.Core.Translate as TR
open import Once.Denotation.Program using (tableEnv; IRFun)
open import Once.Lang.Event using (SigOpEvent)
open import Data.List using (List; []; map)
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
import Once.Parser
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
typedSig (m , mt , hvm) = typedSig-ef m (Parser.extractFunctions (Parser.extractAliases m) m) mt

typedProgram-ef : ∀ (m : P.Module) ef (mt : ModuleTyped-ef m ef) → HasValidMain-ef m ef mt → Program (typedSig-ef m ef mt)
typedProgram-ef m (inj₁ _)  () _
typedProgram-ef m (inj₂ es) mt (_ , mi) = TR.toProgram₀ mt mi

typedProgram : (tp : Typed) → Program (typedSig tp)
typedProgram (m , mt , hvm) = typedProgram-ef m (Parser.extractFunctions (Parser.extractAliases m) m) mt hvm

-- …which are the module's signatures, read off its entries.
typed-sig-ef : ∀ (m : P.Module) ef (mt : ModuleTyped-ef m ef) → typedSig-ef m ef mt ≡ moduleSig-ef ef
typed-sig-ef m (inj₁ _)  ()
typed-sig-ef m (inj₂ es) mt = teleSig≡entrySig mt

typed-sig : ∀ (tp : Typed) → typedSig tp ≡ moduleSig (proj₁ tp)
typed-sig (m , mt , hvm) = typed-sig-ef m (Parser.extractFunctions (Parser.extractAliases m) m) mt

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

  core-ef : ∀ (m : P.Module) (ef : String ⊎ List Parser.Entry) (mt : ModuleTyped-ef m ef) (hvm : HasValidMain-ef m ef mt)
              {es} → ef ≡ inj₂ es → AllPairs _≢_ (map TP.entryName es)
            → (b : FB.FunBundle C.emptyCScope es) (I : Impl (moduleSig-ef ef)) (n : ℕ)
            → runIRAt (interp (moduleSig-ef ef) I) (tableOf-go (FB.bundle→compiled b) []) n
              ≡ runProgram fmt (typedProgram-ef m ef mt hvm) (subst Impl (sym (typed-sig-ef m ef mt)) I) n
  core-ef m .(inj₂ _) mt (_ , mi) refl dist b I n =
    trans (cong (λ ι′ → runIRAt ι′ (tableOf-go (FB.bundle→compiled b) []) n) (sym (interp-subst (teleSig≡entrySig mt) I)))
          (TWm.agree-events (tableOf-go (FB.bundle→compiled b) []) (TR.toProgram Tele.[] TR.[] TR.[] TR.[] (λ ()) mt mi (λ k → k))
             (TWm.walk mt b mi Tele.[] TR.[] TR.[] TR.[] (λ ()) [] inv₀ (λ k → k) (dist , TP.none-in-empty _)) n)
    where
      I′ = subst Impl (sym (teleSig≡entrySig mt)) I
      module TWm = TW fmt (teleSig mt) I′
      inv₀ : TWI.Inv fmt (teleSig mt) I′ C.emptyCScope Tele.[] TR.[] TR.[] TR.[] []
      inv₀ = record { irf = λ () ; irs = λ () ; iself = [] ; rel = λ _ _ _ _ _ → tt , tt , refl }

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
        (core-ef m (Parser.extractFunctions (Parser.extractAliases m) m) mt hvm ef (TP.entries-distinct m ef) b I n)
  where
    ι = interp (moduleSig m) I
    ir≡ : ir ≡ mainCall
    ir≡ = FB.bundle-find-call b (trans (sym (FB.find-agree b)) (trans (sym (cong moduleToIR-aux ceq)) mi))

------------------------------------------------------------------------
-- D320: THE SAME LINK, AS TRACES — calls and how each run ended. The walk's
-- relation (`TeleWalk.Agree`) relates the core run to the compiled tree node
-- by node, so their traces are weakly bisimilar (`TraceTr.RelT∞′-tr`).
------------------------------------------------------------------------

private
  -- the compiled program's trace, in a world
  trIRAt : Interp → List IRFun → Tr ⊤
  trIRAt ι′ tbl = runTr ι′ [] (evalᴰ fmt (tableEnv fmt (pureHalf ι′) tbl) mainCall tt)

  core-ef-tr : ∀ (m : P.Module) (ef : String ⊎ List Parser.Entry) (mt : ModuleTyped-ef m ef) (hvm : HasValidMain-ef m ef mt)
                 {es} → ef ≡ inj₂ es → AllPairs _≢_ (map TP.entryName es)
               → (b : FB.FunBundle C.emptyCScope es) (I : Impl (moduleSig-ef ef))
               → trIRAt (interp (moduleSig-ef ef) I) (tableOf-go (FB.bundle→compiled b) [])
                 ≈ᵗ⟨ _≡_ ⟩ trT∞ (interp (moduleSig-ef ef) I) [] (runCore fmt (typedProgram-ef m ef mt hvm) (subst Impl (sym (typed-sig-ef m ef mt)) I))
  core-ef-tr m .(inj₂ _) mt (_ , mi) refl dist b I =
    subst (λ ι′ → trIRAt ι′ (tableOf-go (FB.bundle→compiled b) []) ≈ᵗ⟨ _≡_ ⟩ trT∞ ι′ [] (runCore fmt P I′))
          (interp-subst (teleSig≡entrySig mt) I)
          (WB-sym sym (RelT∞′-tr (interp (teleSig mt) I′) []
             (TWm.walk mt b mi Tele.[] TR.[] TR.[] TR.[] (λ ()) [] inv₀ (λ k → k) (dist , TP.none-in-empty _))))
    where
      I′ = subst Impl (sym (teleSig≡entrySig mt)) I
      P  = TR.toProgram Tele.[] TR.[] TR.[] TR.[] (λ ()) mt mi (λ k → k)
      module TWm = TW fmt (teleSig mt) I′
      inv₀ : TWI.Inv fmt (teleSig mt) I′ C.emptyCScope Tele.[] TR.[] TR.[] TR.[] []
      inv₀ = record { irf = λ () ; irs = λ () ; iself = [] ; rel = λ _ _ _ _ _ → tt , tt , refl }

-- For EVERY implementation `I`: the compiled program's trace in the world it
-- makes is the core program's.
program-core-tr :
  ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : HasValidMain m mt) (I : Impl (moduleSig m))
    (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir)
  → ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ fmt (interp (moduleSig m) I)
    ≈ᵗ⟨ _≡_ ⟩ trT∞ (interp (moduleSig m) I) [] (runCore fmt (typedProgram (m , mt , hvm)) (implFor (m , mt , hvm) I))
program-core-tr m mt hvm I ir mi with FB.program-node m ir mi
... | es , ef , b , ceq =
  subst (λ t → runTr ι [] t ≈ᵗ⟨ _≡_ ⟩ trT∞ ι [] (runCore fmt (typedProgram (m , mt , hvm)) (implFor (m , mt , hvm) I)))
        (sym (cong₂ (λ tbl x → evalᴰ fmt (tableEnv fmt (pureHalf ι) tbl) x tt) (cong tableOfResult ceq) ir≡))
        (core-ef-tr m (Parser.extractFunctions (Parser.extractAliases m) m) mt hvm ef (TP.entries-distinct m ef) b I)
  where
    ι = interp (moduleSig m) I
    ir≡ : ir ≡ mainCall
    ir≡ = FB.bundle-find-call b (trans (sym (FB.find-agree b)) (trans (sym (cong moduleToIR-aux ceq)) mi))
