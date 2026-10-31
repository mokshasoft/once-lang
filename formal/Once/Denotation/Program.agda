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
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Spec.Name using (CanonicalName)
open import Once.Name using (showCanonical)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.IR using (IR)
open Once.IR.IR
open import Once.IRTy using (_≟IRTy_; IRTy; Unit)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (T; unlinkedT)
open import Once.IR.Semantics.Iterative using (T∞; embed)
open import Once.SigOp.Info using (SigOpInfo; SigOpSem; blockV; primV; ffiV; callsV; emitsV; haltsV; module SigOpInfo)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open SigOpInfo using (name; sem)
open import Once.Contract using (ISig; key; valueKeys; answerKeys)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; callEnv)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)

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

open IRFun

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
tableCalls : TargetNum → FFIAnswers → List IRFun → CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ

-- The entry `e`, asked for as `f : A → B`, answers when the name and both
-- objects match; otherwise the lookup falls to the earlier entries. (A
-- top-level helper taking the decisions, not a `with`.)
tableEnv-at : TargetNum → FFIAnswers → (e : IRFun) → List IRFun → (f : CanonicalName) → (A B : IRTy)
            → Dec (fname e ≡ f) → Dec (fdom e ≡ A) → Dec (fcod e ≡ B) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ
-- The two object equations are TRANSPORTED along, not matched on: matching
-- `refl` would make the lookup reduce only at a literal `refl`, never at the
-- proof a decision procedure returns.
tableEnv-at fmt φ e es f A B (yes _) (yes p) (yes q) a =
  subst (λ Y → T∞ ⟦ Y ⟧ᴰᴵ) q
    (evalᴰ fmt (tableEnv fmt φ es) (fbody e) (subst ⟦_⟧ᴰᴵ (sym p) a))
tableEnv-at fmt φ e es f A B (yes _) (yes _) (no _)  a = tableCalls fmt φ es f A B a
tableEnv-at fmt φ e es f A B (yes _) (no _)  _       a = tableCalls fmt φ es f A B a
tableEnv-at fmt φ e es f A B (no _)  _       _       a = tableCalls fmt φ es f A B a

tableCalls fmt φ []       f A B a = embed unlinkedT
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

-- Plan 0.105 (D257 amendment 2): an FFI SigOp the program calls is DECLARED in
-- the interpretation signatures it is compiled against — the twin of a call
-- naming a table entry. Internal, emitting and halting SigOps owe nothing.
Declared-at : ISig → ∀ {A B} → SigOpInfo A B → SigOpSem A B → Set
Declared-at Σ {A} {B} si ffiV   = key (showCanonical (name si)) A B ∈ valueKeys Σ
Declared-at Σ {A} {B} si callsV = key (showCanonical (name si)) A B ∈ answerKeys Σ
Declared-at Σ si (blockV _ _ _) = ⊤
Declared-at Σ si (primV _)  = ⊤
Declared-at Σ si (emitsV _) = ⊤
Declared-at Σ si (haltsV _) = ⊤

Declared : ISig → ∀ {A B} → SigOpInfo A B → Set
Declared Σ si = Declared-at Σ si (sem si)

-- A predicate on an IR's LEAVES: `C i` at each call (its name and objects),
-- `S` at each SigOp; every other former is `⊤` (plan 0.129 B5: linkedness and
-- "every compiler-owned SigOp names a block" are two instances). The call
-- predicate's index `i` (linkedness: the table) is its own argument, so a
-- stuck `Leaves C i S ir` still determines `i`.
Leaves : ∀ {I : Set} → (I → CanonicalName → IRTy → IRTy → Set) → I → (∀ {A B} → SigOpInfo A B → Set) → ∀ {A B} → IR A B → Set
Leaves C i S (g ∘ f)          = Leaves C i S g × Leaves C i S f
Leaves C i S ⟨ f , g ⟩        = Leaves C i S f × Leaves C i S g
Leaves C i S (case f g)       = Leaves C i S f × Leaves C i S g
Leaves C i S (curry f)        = Leaves C i S f
Leaves C i S (Cata _ alg)     = Leaves C i S alg
Leaves C i S (Ana _ coalg)    = Leaves C i S coalg
Leaves C i S (Iter body)      = Leaves C i S body
Leaves C i S (Call {A} {B} f) = C i f A B
Leaves C i S id               = ⊤
Leaves C i S fst              = ⊤
Leaves C i S snd              = ⊤
Leaves C i S inl              = ⊤
Leaves C i S inr              = ⊤
Leaves C i S terminal         = ⊤
Leaves C i S initial          = ⊤
Leaves C i S apply            = ⊤
Leaves C i S (In _)           = ⊤
Leaves C i S (out-μ _)        = ⊤
Leaves C i S (Out _)          = ⊤
Leaves C i S (in-ν _)         = ⊤
Leaves C i S (SigOp si)       = S si
Leaves C i S (const _ _)      = ⊤

-- …and a map of the two predicates lifts to the leaves.
leaves-map : ∀ {I I′ : Set} {C : I → CanonicalName → IRTy → IRTy → Set} {C′ : I′ → CanonicalName → IRTy → IRTy → Set}
               {i i′} {S S′ : ∀ {A B} → SigOpInfo A B → Set}
           → (∀ f A B → C i f A B → C′ i′ f A B) → (∀ {A B} (si : SigOpInfo A B) → S si → S′ si)
           → ∀ {A B} (ir : IR A B) → Leaves C i S ir → Leaves C′ i′ S′ ir
leaves-map hc hs (g ∘ f)          (a , b) = leaves-map hc hs g a , leaves-map hc hs f b
leaves-map hc hs ⟨ f , g ⟩        (a , b) = leaves-map hc hs f a , leaves-map hc hs g b
leaves-map hc hs (case f g)       (a , b) = leaves-map hc hs f a , leaves-map hc hs g b
leaves-map hc hs (curry f)        a       = leaves-map hc hs f a
leaves-map hc hs (Cata _ alg)     a       = leaves-map hc hs alg a
leaves-map hc hs (Ana _ cg)       a       = leaves-map hc hs cg a
leaves-map hc hs (Iter cg)        a       = leaves-map hc hs cg a
leaves-map hc hs (Call {A} {B} f) a       = hc f A B a
leaves-map hc hs id               a       = tt
leaves-map hc hs fst              a       = tt
leaves-map hc hs snd              a       = tt
leaves-map hc hs inl              a       = tt
leaves-map hc hs inr              a       = tt
leaves-map hc hs terminal         a       = tt
leaves-map hc hs initial          a       = tt
leaves-map hc hs apply            a       = tt
leaves-map hc hs (In _)           a       = tt
leaves-map hc hs (out-μ _)        a       = tt
leaves-map hc hs (Out _)          a       = tt
leaves-map hc hs (in-ν _)         a       = tt
leaves-map hc hs (SigOp si)       a       = hs si a
leaves-map hc hs (const _ _)      a       = tt

Linked : ISig → List IRFun → ∀ {A B} → IR A B → Set
Linked Σ tbl = Leaves LinkedAt tbl (Declared Σ)

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

open IRProgram

runIR : TargetNum → FFIAnswers → IRProgram → T∞ ⟦ Unit ⟧ᴰᴵ
runIR fmt φ p = evalᴰ fmt (tableEnv fmt φ (table p)) (main p) tt

-- A LINKED PROGRAM: every call, in `main` and in every entry of the table, names
-- an entry of the table at its objects. The compiler's output is linked (the
-- telescope, D241); the backend's correctness is stated for linked programs.
--
-- plan 0.135 S3: …and AS A TELESCOPE, which is what the meaning reads. An entry
-- is evaluated in the environment of the entries AFTER it (`tableEnv-at`), so a
-- body linked only in the whole table may call an entry its meaning cannot see
-- (`unlinkedT`) while the machine finds and runs it. Each entry is linked in
-- its suffix (`TeleLinked`), and the names are distinct (a call is resolved by
-- name, `find-fn`; the extractor's guard, D249).
TeleLinked : ISig → List IRFun → Set
TeleLinked Σ []       = ⊤
TeleLinked Σ (e ∷ es) = Linked Σ es (fbody e) × TeleLinked Σ es

NamesDistinct : List IRFun → Set
NamesDistinct = AllPairs (λ e e′ → fname e ≢ fname e′)

LinkedProgram : ISig → IRProgram → Set
LinkedProgram Σ p = Linked Σ (table p) (main p) × All (λ e → Linked Σ (table p) (fbody e)) (table p)
                  × TeleLinked Σ (table p) × NamesDistinct (table p)
