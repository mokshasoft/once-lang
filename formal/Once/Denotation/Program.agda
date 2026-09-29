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
open import Data.Unit using (tt)
open import Data.Product using (_,_; _×_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (Dec; yes; no)

open import Once.CanonicalName using (CanonicalName; _≟ᶜ_)
open import Once.IR using (IR; IRTy; Unit)
open Once.IR.IR
open import Once.IRTy using (_≟IRTy_; ⌈_⌉)
open import Once.Denotation.DenotPrefix using (Good; GoodT; EnvGood; evalᴰ-good; const-empty-pf)
open import Once.Target.Arch using (TargetNum)
open import Once.Res using (stopped)
open import Once.Denotation.TraceMonad using (T; mkT)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; ⟦_⟧ᴰᴵ)

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

unlinkedT : ∀ {X} → T X
unlinkedT = mkT (λ _ → []) stopped

tableEnv : TargetNum → List IRFun → CallEnv

-- The entry `e`, asked for as `f : A → B`, answers when the name and both
-- objects match; otherwise the lookup falls to the earlier entries. (A
-- top-level helper taking the decisions, not a `with`.)
tableEnv-at : TargetNum → (e : IRFun) → List IRFun → (f : CanonicalName) → (A B : IRTy)
            → Dec (fname e ≡ f) → Dec (fdom e ≡ A) → Dec (fcod e ≡ B) → ⟦ A ⟧ᴰᴵ → T ⟦ B ⟧ᴰᴵ
-- The two object equations are TRANSPORTED along, not matched on: matching
-- `refl` would make the lookup reduce only at a literal `refl`, never at the
-- proof a decision procedure returns.
tableEnv-at fmt e es f A B (yes _) (yes p) (yes q) a =
  subst (λ Y → T ⟦ Y ⟧ᴰᴵ) q
    (evalᴰ fmt (tableEnv fmt es) (fbody e) (subst ⟦_⟧ᴰᴵ (sym p) a))
tableEnv-at fmt e es f A B (yes _) (yes _) (no _)  a = tableEnv fmt es f A B a
tableEnv-at fmt e es f A B (yes _) (no _)  _       a = tableEnv fmt es f A B a
tableEnv-at fmt e es f A B (no _)  _       _       a = tableEnv fmt es f A B a

tableEnv fmt []       f A B a = unlinkedT
tableEnv fmt (e ∷ es) f A B a = tableEnv-at fmt e es f A B (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) a

------------------------------------------------------------------------
-- A table's environment is GOOD (`EnvGood`, the hypothesis `evalᴰ-good` takes
-- at a call). Each entry's body is good in the environment of the earlier
-- entries, by induction on the table, and an unlinked call stops silently.
------------------------------------------------------------------------

unlinkedT-good : ∀ (B : IRTy) → GoodT ⌈ B ⌉ (unlinkedT {⟦ B ⟧ᴰᴵ})
unlinkedT-good B = (const-empty-pf stopped , tt)

tableEnv-good : ∀ (fmt : TargetNum) (es : List IRFun) → EnvGood (tableEnv fmt es)

tableEnv-at-good : ∀ (fmt : TargetNum) (e : IRFun) (es : List IRFun) (f : CanonicalName) (A B : IRTy)
                   (d₁ : Dec (fname e ≡ f)) (d₂ : Dec (fdom e ≡ A)) (d₃ : Dec (fcod e ≡ B))
                   (a : ⟦ A ⟧ᴰᴵ) → Good ⌈ A ⌉ a
                 → GoodT ⌈ B ⌉ (tableEnv-at fmt e es f A B d₁ d₂ d₃ a)
tableEnv-at-good fmt e es f .(fdom e) .(fcod e) (yes _) (yes refl) (yes refl) a ga =
  evalᴰ-good fmt (tableEnv fmt es) (tableEnv-good fmt es) (fbody e) a ga
tableEnv-at-good fmt e es f A B (yes _) (yes _) (no _) a ga = tableEnv-good fmt es f A B a ga
tableEnv-at-good fmt e es f A B (yes _) (no _)  _      a ga = tableEnv-good fmt es f A B a ga
tableEnv-at-good fmt e es f A B (no _)  _       _      a ga = tableEnv-good fmt es f A B a ga

tableEnv-good fmt []       f A B a ga = unlinkedT-good B
tableEnv-good fmt (e ∷ es) f A B a ga =
  tableEnv-at-good fmt e es f A B (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) a ga

------------------------------------------------------------------------
-- LINKEDNESS. `LinkedAt tbl f A B`: the table answers a call of `f : A → B`,
-- i.e. the lookup `tableEnv` performs SUCCEEDS (it is that lookup's success,
-- clause for clause). A compiled program's calls are all linked (the
-- telescope, D241/TeleSig). An unlinked call has no machine counterpart: the
-- image may hold `f` at another type, so the backend's correctness is stated
-- for linked IR (`Linked tbl ir`: every `Call` in it is linked).
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
-- emits. `main` runs in the environment of the whole table. The table holds the
-- program's own compiled definitions only: an FFI declaration is an
-- interpretation's code, not an entry of the image, and `main` is the image's
-- entry, not a callable one.
------------------------------------------------------------------------

record IRProgram : Set where
  constructor irProgram
  field
    table : List IRFun
    main  : IR Unit Unit

open IRProgram public

runIR : TargetNum → IRProgram → T ⟦ Unit ⟧ᴰᴵ
runIR fmt p = evalᴰ fmt (tableEnv fmt (table p)) (main p) tt

runIR-good : ∀ (fmt : TargetNum) (p : IRProgram) → GoodT ⌈ Unit ⌉ (runIR fmt p)
runIR-good fmt p = evalᴰ-good fmt (tableEnv fmt (table p)) (tableEnv-good fmt (table p)) (main p) tt tt
