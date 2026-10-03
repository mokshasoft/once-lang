-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.Program — the IR as a PROGRAM (D244/D245).
--
-- A program is a function table plus `main`. That is the shape codegen emits:
-- one `once_<name>` section per definition, with a `call once_<name>` at each
-- use. It is the IR twin of the core `Program` (D239). An internal call
-- (`Call f`) means the table entry `f`, and `tableEnv` is the call environment
-- that says so.
--
-- The table is kept LATEST-FIRST, like the core's scope. Each entry is evaluated
-- in the environment of the entries declared before it, which is the tail of
-- the list. Because there is no recursion (D241), that is structural recursion
-- on the table: no fuel, no well-founded induction.
------------------------------------------------------------------------

module Once.Denotation.Program where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Unit using (tt)
open import Data.Product using (_,_; _×_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (Dec; yes; no)

open import Once.CanonicalName using (CanonicalName; _≟ᶜ_; gen)
open import Once.IR using (IR; IRTy; Unit)
open Once.IR.IR
open import Once.IRTy using (_≟IRTy_; ⌈_⌉)
open import Once.Target.Arch using (TargetNum)
open import Once.Denotation.TraceMonad using (T; halt; haltOp; unlinkedT)
open import Once.SigOp.Info using (FFIAnswers)
open import Once.Functor.Translate using (base-Unit)
open import Once.Type using () renaming (Unit to UnitT)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; callEnv; ⟦_⟧ᴰᴵ)

------------------------------------------------------------------------
-- A table entry: a definition's name and its compiled body as the DIRECT-CALL
-- MORPHISM codegen emits for it (D064, `directCallIR`): an arrow definition
-- uncurried to `A → B`, anything else `Unit → B`.
------------------------------------------------------------------------

record IRFun : Set where
  constructor irFun
  field
    fname : CanonicalName
    fdom  : IRTy
    fcod  : IRTy
    fbody : IR fdom fcod

open IRFun public

------------------------------------------------------------------------
-- The call environment of a table.
--
-- An UNLINKED call names no entry of the table at its type. It stops the
-- program without an event. The compiler never emits one: linkedness is carried
-- to the apex (`Linked`), and this clause is only what the environment says of
-- a call the apex never runs.
------------------------------------------------------------------------

-- A call of a name the table does not hold. A linked program never makes one
-- (`LinkedProgram`), but the environment must be total: the call HALTS, on a
-- reserved operation, so the domain needs no silent stop (plan 0.105).

-- The program's call environment: its table, then the interpretation's pure
-- FFI contracts (plan 0.105).
tableEnv   : TargetNum → FFIAnswers → List IRFun → CallEnv
tableCalls : TargetNum → FFIAnswers → List IRFun → CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T ⟦ B ⟧ᴰᴵ

-- The entry `e`, asked for as `f : A → B`, answers when the name and both
-- objects match; otherwise the lookup falls to the earlier entries. (A
-- top-level helper taking the decisions, not a `with`.)
tableEnv-at : TargetNum → FFIAnswers → (e : IRFun) → List IRFun → (f : CanonicalName) → (A B : IRTy)
            → Dec (fname e ≡ f) → Dec (fdom e ≡ A) → Dec (fcod e ≡ B) → ⟦ A ⟧ᴰᴵ → T ⟦ B ⟧ᴰᴵ
-- The two object equations are TRANSPORTED along, not matched on: matching
-- `refl` would make the lookup reduce only at a literal `refl`, never at the
-- proof a decision procedure returns.
tableEnv-at fmt φ e es f A B (yes _) (yes p) (yes q) a =
  subst (λ Y → T ⟦ Y ⟧ᴰᴵ) q
    (evalᴰ fmt (tableEnv fmt φ es) (fbody e) (subst ⟦_⟧ᴰᴵ (sym p) a))
tableEnv-at fmt φ e es f A B (yes _) (yes _) (no _)  a = tableCalls fmt φ es f A B a
tableEnv-at fmt φ e es f A B (yes _) (no _)  _       a = tableCalls fmt φ es f A B a
tableEnv-at fmt φ e es f A B (no _)  _       _       a = tableCalls fmt φ es f A B a

tableCalls fmt φ []       f A B a = unlinkedT
tableCalls fmt φ (e ∷ es) f A B a = tableEnv-at fmt φ e es f A B (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) a

tableEnv fmt φ es = callEnv (tableCalls fmt φ es) φ

------------------------------------------------------------------------
-- Linkedness
------------------------------------------------------------------------

LinkedAt : List IRFun → CanonicalName → IRTy → IRTy → Set

LinkedAt-at : (e : IRFun) → List IRFun → (f : CanonicalName) → (A B : IRTy)
            → Dec (fname e ≡ f) → Dec (fdom e ≡ A) → Dec (fcod e ≡ B) → Set
LinkedAt-at e es f A B (yes _) (yes _) (yes _) = ⊤
LinkedAt-at e es f A B (yes _) (yes _) (no _)  = LinkedAt es f A B
LinkedAt-at e es f A B (yes _) (no _)  _       = LinkedAt es f A B
LinkedAt-at e es f A B (no _)  _       _       = LinkedAt es f A B

LinkedAt []       f A B = ⊥
LinkedAt (e ∷ es) f A B = LinkedAt-at e es f A B (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B)

Linked : List IRFun → ∀ {A B} → IR A B → Set
Linked tbl (g ∘ f)          = Linked tbl g × Linked tbl f
Linked tbl ⟨ f , g ⟩        = Linked tbl f × Linked tbl g
Linked tbl (case f g)       = Linked tbl f × Linked tbl g
Linked tbl (curry f)        = Linked tbl f
Linked tbl (Cata _ alg)     = Linked tbl alg
Linked tbl (Ana _ coalg)    = Linked tbl coalg
Linked tbl (Call {A} {B} f) = LinkedAt tbl f A B
Linked tbl id               = ⊤
Linked tbl fst              = ⊤
Linked tbl snd              = ⊤
Linked tbl inl              = ⊤
Linked tbl inr              = ⊤
Linked tbl terminal         = ⊤
Linked tbl initial          = ⊤
Linked tbl apply            = ⊤
Linked tbl (In _)           = ⊤
Linked tbl (out-μ _)        = ⊤
Linked tbl (Out _)          = ⊤
Linked tbl (in-ν _)         = ⊤
Linked tbl (SigOp _)        = ⊤
Linked tbl (const _ _)      = ⊤

------------------------------------------------------------------------
-- THE IR PROGRAM (D244): the function table and `main`, the shape codegen
-- emits. `main` runs in the environment of the whole table. The table holds
-- every entry of the module (D246: an FFI declaration's is its SigOp wrapper;
-- D253: `main` too), and the program's `main` is the call of the entry `main`.
------------------------------------------------------------------------

record IRProgram : Set where
  constructor irProgram
  field
    table : List IRFun
    main  : IR Unit Unit

open IRProgram public

runIR : TargetNum → FFIAnswers → IRProgram → T ⟦ Unit ⟧ᴰᴵ
runIR fmt φ p = evalᴰ fmt (tableEnv fmt φ (table p)) (main p) tt

-- A LINKED PROGRAM: every call, in `main` and in every entry of the table, names
-- an entry of the table at its objects. The compiler's output is linked (the
-- telescope, D241); the backend's correctness is stated for linked programs.
LinkedProgram : IRProgram → Set
LinkedProgram p = Linked (table p) (main p) × All (λ e → Linked (table p) (fbody e)) (table p)
