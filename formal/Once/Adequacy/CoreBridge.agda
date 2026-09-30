-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreBridge — plan 0.103 phase 6a: THE APEX MEANS THE CORE.
--
-- A typed module IS a core program (6c, `Spec.Core.Translate.toProgram`), and
-- its meaning is the core's (`Telescope.runProgram`): every definition typed
-- once, a reference meaning the entry (D239, D243, D246). This module states
-- that meaning as a `Behavior` and names the ONE open link between it and the
-- compiled chain:
--
--   exec ≋ IR program (codegen)                      — proved (backend)
--        ≋ SD of the resolved main, compiled env      — proved (MainExtract)
--        ≋ SD of `realize main`, linked env           — proved (MainRealizeAgrees)
--        ≋ core `runProgram (typedProgram tp)`         — `realize-core` (below)
--
-- `realize-core` is the 6b meaning bridge (clause by clause over `RelT`) at
-- the telescope's environments (`TelescopeEnv` over `ModTele`): each compiled
-- table entry means its core entry, by induction on the telescope; each
-- linked (spliced) telescope reference means the entry's instance (6e).
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
open import Once.Adequacy.SourceTrace using (moduleToIR)
import Once.Adequacy.MainExtract fmt as ME
import Once.Adequacy.MainRealizeAgrees fmt as MRA
import Once.Adequacy.ModuleComplete as MC
import Once.Adequacy.MainForm fmt as MF
import Once.Adequacy.FunBundle as FB
import Once.Adequacy.ResolveFaithful as RF
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

------------------------------------------------------------------------
-- Its meaning, as a Behavior.
------------------------------------------------------------------------

-- The run of `main` in the telescope's environment — what `runProgram` reads.
mainRun : Program → T ⟦ Unit ⟧ᴰ
mainRun (program defs main mainTy) =
  GM.⟦_⟧ _ (PT.instantiate _ noVars (λ ()) mainTy) fmt (Tele.teleSem fmt defs) (Data.Unit.tt)
    >>=T (λ clo → clo Data.Unit.tt)
  where import Data.Unit

postulate
  -- RESIDUAL, class DEFERRED PROOF (plan 0.103 6a). The core meaning is a
  -- prefix family: the analogue of `evalᴰ-good` (DenotPrefix) for the core
  -- denotation, by the same induction — `GM.⟦_⟧` is built from the same
  -- `returnT`/`>>=T`/`emit` combinators. Stated about `mainRun` of a PROGRAM,
  -- not an arbitrary computation (which would be false). It replaces
  -- `MainMeaning.mainMeaningᵈ-pf`, the surface meaning's twin.
  core-pf : ∀ (P : Program) → PrefixFamily (mainRun P)

coreBehavior : Program → Behavior
coreBehavior P = mkBehavior (runProgram fmt P) (coh (core-pf P)) (bnd (core-pf P)) (sat (core-pf P))

------------------------------------------------------------------------
-- The one open link (6b + TelescopeEnv over ModTele + 6e).
------------------------------------------------------------------------

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
  inv₀ = record { valid = tt ; iself = [] ; rel = λ _ _ _ _ _ → tt , tt }

  run-at : ∀ {σ σ′} {Ψ} (se : _) (n : ℕ) → σ ≡ σ′ → ME.runMainˢ {Ψ} σ se n ≡ ME.runMainˢ σ′ se n
  run-at se n refl = refl

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
            → (b : FB.FunBundle C.emptyCScope es) (bme : FB.BMainExists b) (n : ℕ)
            → ME.runMainˢ (TW.σMain b bme []) (proj₂ (MC.mainRealized-ef m ef mt hvm)) n
              ≡ runProgram fmt (typedProgram-ef m ef mt hvm) n
  core-ef m .(inj₂ _) mt (_ , mi) refl dist vd b bme n =
    TW.walk mt b mi bme Tele.[] TR.[] TR.[] _ [] inv₀ (dist , none-in-empty _) vd n

  -- `main`'s node: the compiled program's environment is the walk's at `main`.
  core-node : ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : HasValidMain m mt) {ir} (N : MF.MainNode m ir) (n : ℕ)
            → ME.runMainˢ (RF.σR fmt (ME.ρ-of m)
                             (C.cpolys (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ N))))))
                             (C.declImps (C.CScope.ctele (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ N)))))))
                             (("main" , EffUU) ∷ C.CScope.cimps (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ N)))))) 0)
                          (proj₂ (MC.mainRealized m mt hvm)) n
              ≡ runProgram fmt (typedProgram (m , mt , hvm)) n
  core-node m mt hvm (es , ef-eq , b , bme , msc , mbody , mΨ , mse , md , mf , mce , ir≡ , rw , msc≡ , ceq) n =
    trans (run-at (proj₂ (MC.mainRealized m mt hvm)) n
             (cong₂ (λ tbl sc → RF.σR fmt (tableEnv fmt tbl) (C.cpolys sc) (C.declImps (C.CScope.ctele sc))
                                        (("main" , EffUU) ∷ C.CScope.cimps sc) 0)
                    (cong tableOfResult ceq) (sym msc≡)))
          (core-ef m (C.extractFunctions (C.extractAliases m) m) mt hvm ef-eq (entries-distinct m ef-eq) (valid-mod m ef-eq) b bme n)

------------------------------------------------------------------------
-- THE LINK (6b + the telescope walk, `TeleWalk`; its steps are the residuals)
------------------------------------------------------------------------

-- The surface meaning of `main` in the COMPILED program's environment (calls:
-- its function table; references: the resolver's splices) is the core meaning
-- of the program.
realize-core :
  ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : HasValidMain m mt) (n : ℕ)
  → ME.runMainˢ (MRA.σTp m (proj₁ (MC.moduleToIR-complete m mt hvm)) (proj₂ (MC.moduleToIR-complete m mt hvm)))
                (proj₂ (MC.mainRealized m mt hvm)) n
    ≡ runProgram fmt (typedProgram (m , mt , hvm)) n
realize-core m mt hvm n =
  core-node m mt hvm (MF.main-node-of m (proj₁ (MC.moduleToIR-complete m mt hvm)) (proj₂ (MC.moduleToIR-complete m mt hvm))) n
