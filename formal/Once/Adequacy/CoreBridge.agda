-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreBridge — plan 0.103 phase 6a: THE APEX MEANS THE CORE.
--
-- A typed module IS a core program (6c, `Spec.Core.Translate.toProgram`), and
-- its meaning is the core's (`Telescope.runCore`): every definition typed
-- once, a reference meaning the entry (D239, D243, D246), and the program
-- running its `main` entry (D253). This module proves the link between it and
-- the compiled chain:
--
--   exec ≋ IR program (codegen)                      — proved (backend)
--        ≋ core `runCore (typedProgram tp)`            — `program-core-tr` (below)
--
-- `program-core-tr` is the telescope walk (`TeleWalk` over `ModTele`): each
-- compiled table entry means its core entry, by induction on the telescope
-- (the 6b meaning bridge, clause by clause, at the telescope's environments;
-- each linked telescope reference means the entry's instance, 6e). `main` is
-- an entry like any other, and the compiled program's `main` is the call of it.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)


-- Plan 0.105: at an interpretation `ι`.
-- Plan 0.105 (D257, D061): no fixed world — a typed module's meaning is
-- relative to an implementation of the signatures it is compiled against.
module Once.Adequacy.CoreBridge where

open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Spec.Type using (Unit)
open import Once.Spec.Signature using (Signature; WellFormed; Decl)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Once.Internal.Name using (showCanonical)
import Once.Spec.Observation as Obs
open import Once.Adequacy.SpecInterp using (toInterp)
import Once.Adequacy.SpecObserve as SO
import Once.Adequacy.SpecSig as SSg
import Once.Compile as C
import Once.Parser as Parser
import Once.Parser.Module.Core as P
open import Once.Internal.Module using (ModuleTyped; ModuleTyped-ef; HasValidMain; HasValidMain-ef)
open import Once.Internal.Trace using (Interp; pureHalf)
open import Once.Internal.Program using (Typed)
import Once.Internal.Core.Telescope as TL
import Once.Internal.Core.Translate as TR
import Once.Spec.Core.Program as SP
open import Once.Adequacy.SourceTrace using (⟦_⟧IRᵗ)
open import Once.Spec.Trace using (Tr; _≈ᵗ⟨_⟩_)
open import Once.Denotation.TraceTr using (trT∞)
open import Once.Compile using (moduleToIR; moduleToIR-aux; tableOf-go; moduleTable; tableOfResult)
import Once.Adequacy.FunBundle as FB
open import Once.Denotation.Program using (irProgram)
open import Once.Denotation.DenotTrace using (evalᴰ)
open import Data.Maybe using (Maybe; just)
import Once.Adequacy.TeleWalk as TW
import Once.Adequacy.TeleWalk.Invariant as TWI
import Once.Adequacy.TelePosition as TP
open import Once.Denotation.Program using (tableEnv; IRFun)
open import Data.List using (List; []; map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.All using ([])
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- The typed module as a core program (6c), over a signature Σ that declares
-- its FFI words (plan 0.122: the core is the Spec's, over a Spec signature).
------------------------------------------------------------------------

-- Σ declares the module's FFI declarations, each under its word names.
SigView-ef : ∀ (m : P.Module) ef (mt : ModuleTyped-ef m ef) → Signature → Set
SigView-ef m (inj₁ _)  ()
SigView-ef m (inj₂ es) mt Σ = TR.SigIn Σ mt

SigView : Typed → Signature → Set
SigView (m , mt , hvm) = SigView-ef m (Parser.extractFunctions m) mt

typedProgram-ef : ∀ (m : P.Module) ef (mt : ModuleTyped-ef m ef) → HasValidMain-ef m ef mt
                → (Σ : Signature) → SigView-ef m ef mt Σ → TL.Program Σ
typedProgram-ef m (inj₁ _)  () _
typedProgram-ef m (inj₂ es) mt (_ , mi) Σ u = TR.toProgram₀ Σ mt mi u

typedProgram : (tp : Typed) (Σ : Signature) → SigView tp Σ → TL.Program Σ
typedProgram (m , mt , hvm) = typedProgram-ef m (Parser.extractFunctions m) mt hvm

module _ (fmt : TargetNum) where

  ------------------------------------------------------------------------
  -- D320: THE LINK, AS TRACES — calls and how each run ended. The walk's
  -- relation (`TeleWalk.Agree`) relates the core run to the compiled tree
  -- step for step, so their traces are weakly bisimilar
  -- (`SpecObserve.observe-R`, the interpretation agreeing with `J`'s world,
  -- `SpecSig.agree`). Plan 0.122: the core run is the Spec's, in `J`'s world.
  ------------------------------------------------------------------------

  -- The core program's trace in `J`'s world.
  coreTr : ∀ (Σ : Signature) → TL.Program Σ → Obs.Interp Σ → Tr ⊤
  coreTr Σ P J = Obs.trace Σ (Obs.Interp.world J) [] (TL.runCore Σ fmt P (Obs.Interp.model J))

  private
    -- the compiled program's trace, in a world
    trIRAt : Interp → List IRFun → IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋ → Tr ⊤
    trIRAt ι′ tbl ir = trT∞ ι′ [] (evalᴰ fmt (tableEnv fmt (pureHalf ι′) tbl) ir tt)

    -- the walk's agreement at the entry the bundle finds
    agree-at : ∀ {Σ wf J uniq tbl P} {m : Maybe (IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋)} {ir} → m ≡ just ir
             → TW.AgreeM fmt Σ wf J uniq tbl m P → TW.Agree fmt Σ wf J uniq tbl ir P
    agree-at refl a = a

    core-ef-tr : ∀ (m : P.Module) (ef : String ⊎ List Parser.Entry) (mt : ModuleTyped-ef m ef) (hvm : HasValidMain-ef m ef mt)
                   {es} → ef ≡ inj₂ es → AllPairs _≢_ (map TP.entryName es)
                 → (b : FB.FunBundle C.emptyCScope es) {ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋} → FB.bundle-find b ≡ just ir
                 → (Σ : Signature) (u : SigView-ef m ef mt Σ)
                   (wf : WellFormed Σ) (J : Obs.Interp Σ) (uniq : Unique (map (λ d → showCanonical (Decl.name d)) Σ))
                 → trIRAt (toInterp Σ wf J) (tableOf-go (FB.bundle→compiled b) []) ir
                   ≈ᵗ⟨ _≡_ ⟩ coreTr Σ (typedProgram-ef m ef mt hvm Σ u) J
    core-ef-tr m .(inj₂ _) mt (_ , mi) refl dist b {ir} fe Σ u wf J uniq =
      SO.observe-R Σ (toInterp Σ wf J) (Obs.Interp.world J) (SSg.agree Σ wf J uniq fmt (SP.noVars Σ))
        (agree-at {Σ} {wf} {J} {uniq} fe
          (TWm.walk mt b mi (SP.Tele.[]) TR.[] TR.[] TR.[] [] inv₀ u (dist , TP.none-in-empty _)))
      where
        module TWm = TW fmt Σ wf J uniq
        inv₀ : TWI.Inv fmt Σ wf J uniq C.emptyCScope (SP.Tele.[]) TR.[] TR.[] TR.[] []
        inv₀ = record { iself = [] ; rel = λ _ _ _ _ _ → tt , tt , λ _ () }

  -- For EVERY signature declaring the module's FFI words, under distinct
  -- names, and EVERY Interpretation `J` of it: the compiled program's trace
  -- in the world `J` makes is the core program's in `J`'s.
  program-core-tr :
    ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : HasValidMain m mt)
      (Σ : Signature) (u : SigView (m , mt , hvm) Σ)
      (wf : WellFormed Σ) (J : Obs.Interp Σ) (uniq : Unique (map (λ d → showCanonical (Decl.name d)) Σ))
      (ir : IR ⌊ Unit {0} ⌋ ⌊ Unit {0} ⌋) (mi : moduleToIR m ≡ just ir)
    → ⟦ just (irProgram (moduleTable m) ir) ⟧IRᵗ fmt (toInterp Σ wf J)
      ≈ᵗ⟨ _≡_ ⟩ coreTr Σ (typedProgram (m , mt , hvm) Σ u) J
  program-core-tr m mt hvm Σ u wf J uniq ir mi with FB.program-node m ir mi
  ... | es , ef , b , ceq =
    subst (λ t → trT∞ ι [] t ≈ᵗ⟨ _≡_ ⟩ coreTr Σ (typedProgram (m , mt , hvm) Σ u) J)
          (sym (cong (λ tbl → evalᴰ fmt (tableEnv fmt (pureHalf ι) tbl) ir tt) (cong tableOfResult ceq)))
          (core-ef-tr m (Parser.extractFunctions m) mt hvm ef (TP.entries-distinct m ef) b fe Σ u wf J uniq)
    where
      ι = toInterp Σ wf J
      fe : FB.bundle-find b ≡ just ir
      fe = trans (sym (FB.find-agree b)) (trans (sym (cong moduleToIR-aux ceq)) mi)
