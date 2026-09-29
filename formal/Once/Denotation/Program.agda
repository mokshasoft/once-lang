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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Once.CanonicalName using (CanonicalName; _≟ᶜ_)
open import Once.IR using (IR; IRTy; Unit)
open Once.IR.IR
open import Once.IRTy using (_≟IRTy_; ⌈_⌉)
open import Once.Denotation.DenotPrefix using (GoodT; EnvGood; evalᴰ-good; const-empty-pf)
open import Once.Target.Arch using (TargetNum)
open import Once.Res using (stopped)
open import Once.Denotation.TraceMonad using (T; mkT)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; ⟦_⟧ᴰᴵ)

------------------------------------------------------------------------
-- A table entry: a definition's name and its compiled body at the
-- closure-returner ABI (`once_f()` returns f's value, D064).
------------------------------------------------------------------------

record IRFun : Set where
  constructor irFun
  field
    fname : CanonicalName
    fcod  : IRTy
    fbody : IR Unit fcod

open IRFun public

------------------------------------------------------------------------
-- The call environment of a table.
--
-- An UNLINKED call names no entry of the table at its result type. It stops the
-- program without an event. The compiler never emits one: linkedness is carried
-- to the apex, and this clause is only what the environment says of a table the
-- apex never runs.
------------------------------------------------------------------------

unlinkedT : ∀ {X} → T X
unlinkedT = mkT (λ _ → []) stopped

tableEnv : TargetNum → List IRFun → CallEnv

-- The entry `e`, asked for as `f` at `B`, answers when both the name and the
-- result type match. Otherwise the lookup falls to the earlier entries.
-- (A top-level helper taking the two decisions, not a `with`.)
tableEnv-at : TargetNum → (e : IRFun) → List IRFun → (f : CanonicalName) → (B : IRTy)
            → Dec (fname e ≡ f) → Dec (fcod e ≡ B) → T ⟦ B ⟧ᴰᴵ
tableEnv-at fmt e es f .(fcod e) (yes _) (yes refl) = evalᴰ fmt (tableEnv fmt es) (fbody e) tt
tableEnv-at fmt e es f B         (yes _) (no _)     = tableEnv fmt es f B
tableEnv-at fmt e es f B         (no _)  _          = tableEnv fmt es f B

tableEnv fmt []       f B = unlinkedT
tableEnv fmt (e ∷ es) f B = tableEnv-at fmt e es f B (fname e ≟ᶜ f) (fcod e ≟IRTy B)

------------------------------------------------------------------------
-- A table's environment is GOOD (`EnvGood`, the hypothesis `evalᴰ-good` takes
-- at a call). Each entry's body is good in the environment of the earlier
-- entries, by induction on the table, and an unlinked call stops silently.
------------------------------------------------------------------------

unlinkedT-good : ∀ (B : IRTy) → GoodT ⌈ B ⌉ (unlinkedT {⟦ B ⟧ᴰᴵ})
unlinkedT-good B = (const-empty-pf stopped , tt)

tableEnv-good : ∀ (fmt : TargetNum) (es : List IRFun) → EnvGood (tableEnv fmt es)

tableEnv-at-good : ∀ (fmt : TargetNum) (e : IRFun) (es : List IRFun) (f : CanonicalName) (B : IRTy)
                   (d₁ : Dec (fname e ≡ f)) (d₂ : Dec (fcod e ≡ B))
                 → GoodT ⌈ B ⌉ (tableEnv-at fmt e es f B d₁ d₂)
tableEnv-at-good fmt e es f .(fcod e) (yes _) (yes refl) =
  evalᴰ-good fmt (tableEnv fmt es) (tableEnv-good fmt es) (fbody e) tt tt
tableEnv-at-good fmt e es f B (yes _) (no _) = tableEnv-good fmt es f B
tableEnv-at-good fmt e es f B (no _)  _      = tableEnv-good fmt es f B

tableEnv-good fmt []       f B = unlinkedT-good B
tableEnv-good fmt (e ∷ es) f B = tableEnv-at-good fmt e es f B (fname e ≟ᶜ f) (fcod e ≟IRTy B)

------------------------------------------------------------------------
-- LINKEDNESS. `LinkedAt tbl f B`: the table answers a call of `f` at `B`, i.e.
-- the lookup `tableEnv` performs SUCCEEDS (it is that lookup's success,
-- clause for clause). A compiled program's calls are all linked (the
-- telescope, D241/TeleSig). An unlinked call has no machine counterpart: the
-- image may hold `f` at another type, so the backend's correctness is stated
-- for linked IR (`Linked tbl ir`: every `Call` in it is linked).
------------------------------------------------------------------------

LinkedAt : List IRFun → CanonicalName → IRTy → Set

LinkedAt-at : (e : IRFun) → List IRFun → (f : CanonicalName) → (B : IRTy)
            → Dec (fname e ≡ f) → Dec (fcod e ≡ B) → Set
LinkedAt-at e es f B (yes _) (yes _) = ⊤
LinkedAt-at e es f B (yes _) (no _)  = LinkedAt es f B
LinkedAt-at e es f B (no _)  _       = LinkedAt es f B

LinkedAt []       f B = ⊥
LinkedAt (e ∷ es) f B = LinkedAt-at e es f B (fname e ≟ᶜ f) (fcod e ≟IRTy B)

Linked : List IRFun → ∀ {A B} → IR A B → Set
Linked tbl (g ∘ f)        = Linked tbl g × Linked tbl f
Linked tbl ⟨ f , g ⟩      = Linked tbl f × Linked tbl g
Linked tbl (case f g)     = Linked tbl f × Linked tbl g
Linked tbl (curry f)      = Linked tbl f
Linked tbl (Cata _ alg)   = Linked tbl alg
Linked tbl (Ana _ coalg)  = Linked tbl coalg
Linked tbl (Call {B} f)   = LinkedAt tbl f B
Linked tbl id             = ⊤
Linked tbl fst            = ⊤
Linked tbl snd            = ⊤
Linked tbl inl            = ⊤
Linked tbl inr            = ⊤
Linked tbl terminal       = ⊤
Linked tbl initial        = ⊤
Linked tbl apply          = ⊤
Linked tbl (In _)         = ⊤
Linked tbl (out-μ _)      = ⊤
Linked tbl (Out _)        = ⊤
Linked tbl (in-ν _)       = ⊤
Linked tbl (SigOp _)      = ⊤
Linked tbl (const _ _)    = ⊤
