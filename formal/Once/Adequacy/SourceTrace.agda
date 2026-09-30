-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SourceTrace — the source semantics `⟦_⟧` (Plan 0.24,
-- Phase C). Discharges the former `Once.Denotation.Behavior.⟦_⟧`
-- postulate.
--
-- `⟦ src ⟧` is the SigOp trace of the source program (its meaning), read
-- off its IR via the DENOTATIONAL `evalᴰ`. Option (a) "IR pivot":
-- `moduleToIR` reuses the compiler's own front-end (`gmoduleToModule` →
-- `compileResolvedModule` → the IR of `main`). The front-end is thus a
-- shared/trusted reference; `correct` verifies the backend against this
-- IR-level meaning (see plan 0.24's TCB section).
--
-- This module lives separately from `Behavior.agda` (which stays light,
-- as the per-arch CPU instances import it) because `moduleToIR` pulls in
-- the whole compiler front-end via `Once.Compile`.
--
-- D060 (2026-06-16): there is now ONE denotational meaning. The surface
-- `⟦_⟧ˢ` and IR `⟦_⟧ᴰ` are two presentations of it, tied by the proven
-- `faithful` (`Once.Adequacy.SourceFaithful`). The old independent
-- `SS.eval`/`runTrace` reference (and the `ElaborateFaithful` conjunct it
-- backed) is retired: `SourceSemantics`/`AnaTrace`/`ElaborateTrace` are
-- gone, and `faithful` is the standalone load-bearing fact rather than a
-- conjunct bolted onto the compiler theorem.
--
-- Plan 0.44: `Behavior = ℕ → List SigOpEvent` (the step-indexed SigOp
-- trace). `⟦ src ⟧ n` is the trace prefix `evalᴰ` observes within `n`
-- steps — no projection.
------------------------------------------------------------------------

module Once.Adequacy.SourceTrace where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; suc; _<_; z≤n)
open import Data.List using (List; []; _∷_; take; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₂)
open import Data.Unit using (tt)
open import Data.String using (String) renaming (_≟_ to _≟str_)
open import Once.CanonicalName using (CanonicalName; bare) renaming (_≟ᶜ_ to _≟cn_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type; Unit)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.Compile as C
import Once.Parser.Module.Core as P
-- D165: the arith-block lifting the BACKEND runs before codegen. Imported here
-- so the IR the emitter actually compiles can be NAMED (`moduleToIR-emitted`).
open import Once.Arith.Machine.Rewrite using (rewrite-ir)
open import Data.Product using (proj₁)
-- Plan 0.52: pull the LEXER+PARSER into the verified front-end — `srcToModule`
-- runs the executable `parseStrict` on the source TEXT (a front-end bug reds the
-- apex via `Once.Adequacy.FrontEndBridge`). Plan 0.51: and then the resolver, so
-- `moduleToIR` compiles the SAME (resolved) module the binary runs.
open import Once.Parser using (parseStrict)
open import Once.Parser.Module.Resolve using (resolveImports; ModuleMap)
open import Once.Denotation.Behavior using (Source; Behavior; mkBehavior; silent; at)
open import Once.Denotation.DenotTrace using (evalᴰ)
-- Plan 0.73 (D113): the meaning is target-relative at `Float`, so the format
-- is threaded in. An explicit ARGUMENT, not a module parameter — these are
-- recursive and a parameterised module stops reducing at a variable instance.
open import Once.Target.Arch using (TargetNum; int-bits; float-format)
open import Once.Denotation.TraceMonad
  using (projTrace; PrefixFamily; bnd; sat; coh)
open import Once.Denotation.Program using (IRFun; irFun; fname; fdom; fcod; fbody; IRProgram; irProgram; table; main; runIR; runIR-good; LinkedAt; LinkedAt-at; Linked; LinkedProgram)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Once.IR as I
open import Once.IRTy using (IRTy; _≟IRTy_)

------------------------------------------------------------------------
-- Source → IR of `main` (option (a): reuse the compiler's elaborator).
------------------------------------------------------------------------

-- | Recognise the `Unit` codomain so `main`'s entry IR (wrapped to
-- `IR ⌊ Unit ⌋ ⌊ Unit ⌋` by `maybeWrapMain`) can be coerced.
isUnit? : (T : Type) → Maybe (T ≡ Unit)
isUnit? Unit = just refl
isUnit? _    = nothing

open C.CompiledFun using (cfName; cfType; cfIR; cfIsPrimitive)

-- Explicit dispatch on the three decisions (no `with`-opacity, no dependent
-- `just refl` buried in a `with`), so `findMain`'s "is this the entry?" choice
-- is analyzable. `just refl` refines `cfType cf` to `Unit`, coercing
-- `cfIR cf : IR Unit (cfType cf)` to `IR ⌊ Unit ⌋ ⌊ Unit ⌋`.
--
-- The FIRST argument is `cfIsPrimitive cf`: a PRIMITIVE is never the entry —
-- its body is not emitted at codegen (`CompiledFun.cfIsPrimitive`), so it has
-- no real `_start` to run. Skipping primitives aligns this spec with the
-- backend and makes the entry provably trace back to a `DFunDef`.
findMain-here :
  (cf : C.CompiledFun) → Bool → Dec (cfName cf ≡ bare "main") → Maybe (cfType cf ≡ Unit)
  → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
findMain-here cf false (yes _) (just refl) cont = just (cfIR cf)
findMain-here cf false (yes _) nothing     cont = cont
findMain-here cf false (no  _) _           cont = cont
findMain-here cf true  _       _           cont = cont   -- primitive: never the entry

-- | The Boolean predicate `findMain` selects on: a non-primitive `main`-named
-- function whose (entry-wrapped) codomain is `Unit`. `findMain` returns the IR
-- of the FIRST such function. Factored out (Plan 0.55) so the SAME notion of
-- "which function is the entry" is nameable for the deterministic `mainRealized`
-- selector's alignment. Behaviour-preserving: `findMain`/`findMain-here` are
-- unchanged — `isMain cf ≡ true` exactly when `findMain-here cf … ≡ just (cfIR cf)`.
isMain : C.CompiledFun → Bool
isMain cf with cfIsPrimitive cf | cfName cf ≟cn bare "main" | isUnit? (cfType cf)
... | false | yes _ | just _ = true
... | _     | _     | _      = false

findMain : List C.CompiledFun → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
findMain []         = nothing
findMain (cf ∷ rest) =
  findMain-here cf (cfIsPrimitive cf) (cfName cf ≟cn bare "main") (isUnit? (cfType cf)) (findMain rest)

-- Explicit dispatch on the compile result (no `with`-opacity).
moduleToIR-aux : String ⊎ List C.CompiledFun → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
moduleToIR-aux (inj₁ _)    = nothing
moduleToIR-aux (inj₂ funs) = findMain funs

-- Non-resolving: the IR of `main` in an ALREADY-RESOLVED module. The
-- module-level proofs (`AcceptSound`/`MainBuilds`/`ModuleComplete`) reason
-- about THIS over a module `mod` (interpreted as the RESOLVED module);
-- resolution is confined to `srcToModule` below, so those proofs are untouched.
moduleToIR : P.Module → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
moduleToIR mod = moduleToIR-aux (C.compileResolvedModule C.Heap false mod)

------------------------------------------------------------------------
-- D244: THE COMPILED PROGRAM — the function table and `main`. The table is the
-- program's own definitions (not FFI declarations, whose code is an
-- interpretation's, and not `main`, the image's entry), LATEST-FIRST, so each
-- entry is evaluated in the ones declared before it (`tableEnv`). The compiler
-- emits in declaration order, so the table is that list reversed.
------------------------------------------------------------------------
-- Each entry is the DIRECT-CALL morphism the emitter compiles (D064,
-- `directCallIR`), which is what `once_<name>` implements in the image.
irFunOf : C.CompiledFun → IRFun
irFunOf cf = irFun (cfName cf) ⌊ proj₁ dc ⌋ ⌊ proj₁ (proj₂ dc) ⌋ (proj₂ (proj₂ dc))
  where dc = C.directCallIR (cfType cf) (cfIR cf)

-- keep an entry: not a primitive, and not the entry `main`.
tbl-keep : Bool → Bool → C.CompiledFun → List IRFun → List IRFun
tbl-keep false false cf acc = irFunOf cf ∷ acc
tbl-keep false true  cf acc = acc
tbl-keep true  _     cf acc = acc

tableOf-go : List C.CompiledFun → List IRFun → List IRFun
tableOf-go []         acc = acc
tableOf-go (cf ∷ cfs) acc = tableOf-go cfs (tbl-keep (cfIsPrimitive cf) (isMain cf) cf acc)

tableOf : List C.CompiledFun → List IRFun
tableOf funs = tableOf-go funs []

-- The table of a compile RESULT (a failed compile has none), and of a module.
tableOfResult : String ⊎ List C.CompiledFun → List IRFun
tableOfResult (inj₁ _)    = []
tableOfResult (inj₂ funs) = tableOf funs

moduleTable : P.Module → List IRFun
moduleTable mod = tableOfResult (C.compileResolvedModule C.Heap false mod)

-- The program at a table, given `main`. Stated over `moduleToIR` so that every
-- apex step that already has `moduleToIR m ≡ just ir` reaches the program by
-- rewriting with it.
programAt : List IRFun → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Maybe IRProgram
programAt tbl nothing   = nothing
programAt tbl (just ir) = just (irProgram tbl ir)

moduleToProgram : P.Module → Maybe IRProgram
moduleToProgram mod = programAt (moduleTable mod) (moduleToIR mod)

------------------------------------------------------------------------
-- D165: THE IR THE BACKEND ACTUALLY COMPILES.
--
-- `moduleToIR` is `main`'s IR as elaborated. It is NOT what the emitter turns
-- into text: `compileFunWithTarget` runs `directCallIR` and then `rewrite-ir`
-- — the arith-block lifting — and codegens the RESULT. At `main` the first is
-- the identity (`main` is entry-wrapped, so `cfType ≡ Unit`, the non-arrow
-- clause), so the whole difference is `rewrite-ir`.
--
-- That difference sat INSIDE `ArchCorrect.asm-trace-correct`, whose two sides
-- were the emitted text (rewritten) and the flat machine on the raw IR — so a
-- toolchain axiom was also asserting "and the arith pass preserved the
-- meaning", which is compiler logic and is not trivially true: lifting must
-- preserve both the event trace AND the computed values, since an arith result
-- flows into an observable SigOp's argument. D163's regression lived exactly
-- there and broke no theorem.
--
-- Naming the emitted IR is what lets that assumption be split out and counted.
------------------------------------------------------------------------
map-rewrite : Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
map-rewrite nothing   = nothing
map-rewrite (just ir) = just (proj₁ (rewrite-ir ir))

moduleToIR-emitted : P.Module → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
moduleToIR-emitted mod = map-rewrite (moduleToIR mod)

-- D244: …and the whole PROGRAM the backend compiles. The emitter runs the arith
-- lifting on EVERY definition (`compileFunWithTarget`), so the emitted program
-- rewrites `main` and each table entry alike.
rewrite-fun : IRFun → IRFun
rewrite-fun e = irFun (fname e) (fdom e) (fcod e) (proj₁ (rewrite-ir (fbody e)))

rewrite-table : List IRFun → List IRFun
rewrite-table []       = []
rewrite-table (e ∷ es) = rewrite-fun e ∷ rewrite-table es

rewrite-program : IRProgram → IRProgram
rewrite-program p = irProgram (rewrite-table (table p)) (proj₁ (rewrite-ir (main p)))

map-rewrite-program : Maybe IRProgram → Maybe IRProgram
map-rewrite-program nothing  = nothing
map-rewrite-program (just p) = just (rewrite-program p)

moduleToProgram-emitted : P.Module → Maybe IRProgram
moduleToProgram-emitted mod = map-rewrite-program (moduleToProgram mod)

------------------------------------------------------------------------
-- LINKEDNESS of the compiled program (D245). The backend's correctness is for
-- linked IR: every `Call` names an entry of the table at its objects.
------------------------------------------------------------------------

-- Rewriting a table keeps every entry's name and objects, which is all
-- `LinkedAt` reads.
linkedAt-rewrite : ∀ (tbl : List IRFun) (f : CanonicalName) (A B : IRTy)
                 → LinkedAt tbl f A B → LinkedAt (rewrite-table tbl) f A B
linkedAt-rewrite-at : ∀ (e : IRFun) (es : List IRFun) (f : CanonicalName) (A B : IRTy)
                      (d₁ : Dec (fname e ≡ f)) (d₂ : Dec (fdom e ≡ A)) (d₃ : Dec (fcod e ≡ B))
                    → LinkedAt-at e es f A B d₁ d₂ d₃
                    → LinkedAt-at (rewrite-fun e) (rewrite-table es) f A B d₁ d₂ d₃
linkedAt-rewrite-at e es f A B (yes _) (yes _) (yes _) lk = tt
linkedAt-rewrite-at e es f A B (yes _) (yes _) (no _)  lk = linkedAt-rewrite es f A B lk
linkedAt-rewrite-at e es f A B (yes _) (no _)  _       lk = linkedAt-rewrite es f A B lk
linkedAt-rewrite-at e es f A B (no _)  _       _       lk = linkedAt-rewrite es f A B lk
linkedAt-rewrite []       f A B ()
linkedAt-rewrite (e ∷ es) f A B lk =
  linkedAt-rewrite-at e es f A B (fname e ≟cn f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) lk

linked-retable : ∀ (tbl : List IRFun) {A B} (ir : IR A B) → Linked tbl ir → Linked (rewrite-table tbl) ir
linked-retable tbl (g I.∘ f)       (lg , lf) = linked-retable tbl g lg , linked-retable tbl f lf
linked-retable tbl I.⟨ f , g ⟩     (lf , lg) = linked-retable tbl f lf , linked-retable tbl g lg
linked-retable tbl (I.case f g)    (lf , lg) = linked-retable tbl f lf , linked-retable tbl g lg
linked-retable tbl (I.curry f)     lf = linked-retable tbl f lf
linked-retable tbl (I.Cata _ alg)  la = linked-retable tbl alg la
linked-retable tbl (I.Ana _ coalg) lc = linked-retable tbl coalg lc
linked-retable tbl (I.Call {A} {B} f) lk = linkedAt-rewrite tbl f A B lk
linked-retable tbl I.id            _ = tt
linked-retable tbl I.fst           _ = tt
linked-retable tbl I.snd           _ = tt
linked-retable tbl I.inl           _ = tt
linked-retable tbl I.inr           _ = tt
linked-retable tbl I.terminal      _ = tt
linked-retable tbl I.initial       _ = tt
linked-retable tbl I.apply         _ = tt
linked-retable tbl (I.In _)        _ = tt
linked-retable tbl (I.out-μ _)     _ = tt
linked-retable tbl (I.Out _)       _ = tt
linked-retable tbl (I.in-ν _)      _ = tt
linked-retable tbl (I.SigOp _)     _ = tt
linked-retable tbl (I.const _ _)   _ = tt

-- RESIDUALS, class DEFERRED PROOF (plan 0.103 6a″), both claims about the
-- compiler's own output and both true of a correct compiler:
--   * the compiled program is linked. References elaborate to `refIR` of an
--     EARLIER entry (the telescope, D241) at `directCallIR`'s objects, and
--     resolution leaves no `poly` placeholder behind. A false instance is a
--     compiler bug (a dangling `call once_f`), which is why it is stated, not
--     decided inside the meaning.
--   * the arith lifting keeps a body linked. It replaces closed arithmetic
--     subtrees by SigOps and leaves every `Call` in place; `rewrite-ir` is
--     TERMINATING, so this rides with `rewrite-program-preserves`' residual class.
postulate
  moduleToProgram-linked : ∀ (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋)
                         → moduleToIR m ≡ just ir → LinkedProgram (irProgram (moduleTable m) ir)
  rewrite-ir-linked : ∀ (tbl : List IRFun) {A B} (ir : IR A B)
                    → Linked tbl ir → Linked tbl (proj₁ (rewrite-ir ir))

-- …every entry of a table, rewritten, against the rewritten table.
all-rewrite-linked : ∀ (tbl es : List IRFun)
                   → All (λ e → Linked tbl (fbody e)) es
                   → All (λ e → Linked (rewrite-table tbl) (fbody e)) (rewrite-table es)
all-rewrite-linked tbl []       []         = []
all-rewrite-linked tbl (e ∷ es) (le ∷ les) =
  rewrite-ir-linked (rewrite-table tbl) (fbody e) (linked-retable tbl (fbody e) le)
  ∷ all-rewrite-linked tbl es les

rewrite-program-linked : ∀ (p : IRProgram) → LinkedProgram p → LinkedProgram (rewrite-program p)
rewrite-program-linked p (lm , les) =
  rewrite-ir-linked (rewrite-table (table p)) (main p) (linked-retable (table p) (main p) lm)
  , all-rewrite-linked (table p) (table p) les

------------------------------------------------------------------------
-- IR-level meaning (the source observable).
------------------------------------------------------------------------

-- The SigOp trace the denotational `evalᴰ` reads off `main`'s IR (the
-- elaborated meaning), at observation depth `n` (Plan 0.46: the monadic
-- `⟦_⟧ᴰ` is THE source observable; the operational `otrace` is retired).
-- D179: `Behavior` is a RECORD — the three laws travel with the family, so a
-- producer must supply them. They are not new obligations invented here: they
-- are exactly `PrefixFamily`, which `evalᴰ-good` proves for every IR. (`take n`
-- has gone from `at`: `bounded` says the prefix is already short enough, so the
-- cap was doing nothing but obscuring which family this is.)
⟦_⟧IR : Maybe IRProgram → TargetNum → Behavior
-- D244: the meaning of a compiled program is `main` run in the environment of
-- its function table (`runIR`); an internal call means its callee.
⟦ just p ⟧IR fmt = mkBehavior (projTrace m) (coh pf) (bnd pf) sat'
  where
    m  = runIR fmt p
    pf : PrefixFamily m
    pf = proj₁ (runIR-good fmt p)

    -- plan 0.97: `Saturating` is stated on the TRACE alone now (the value and
    -- the stop flag are budget-free, so there is nothing to project out of).
    sat' : ∀ n → length (projTrace m n) < n → projTrace m (suc n) ≡ projTrace m n
    sat' = sat pf
-- A module with no `main` observes nothing, at every depth — the empty family,
-- whose three laws are immediate.
⟦ nothing ⟧IR _   = silent

-- D165, RESTATED AT THE MEANING (plan 0.103 6a″): the arith lifting preserves
-- a program's denotation. `rewrite-ir` replaces a recognised closed arith
-- subtree by one `arith.block.<digest>` SigOp, so the block's VALUE must equal
-- the subtree's (an arith result reaches an observable SigOp's argument); the
-- events agree because arith SigOps are pure (plans 0.25/0.26). It used to be a
-- per-target flat-machine field (`ArchCorrect.rewrite-preserves`), but it is a
-- fact about the IR alone — the three flat machines agree with the meaning by
-- `ir-flat-correct`, so one statement here serves every target.
-- A NAMED RESIDUAL, class **deferred proof / codegen**.
postulate
  rewrite-program-preserves : ∀ (fmt : TargetNum) (p : IRProgram) (n : ℕ)
                            → at (⟦ just (rewrite-program p) ⟧IR fmt) n ≡ at (⟦ just p ⟧IR fmt) n

------------------------------------------------------------------------
-- The verified front-end (Plan 0.51): parse the user's grammar module,
-- THEN resolve its imports against the in-`Source` `ModuleMap`. This is the
-- resolution step the binary runs — now INSIDE the verified pipeline, so a
-- resolver bug is the apex's concern (`Once.Spec.Resolution` + its bridge), not a
-- trusted-I/O step. The INDEPENDENT meaning (`_⊢R_`/`⟦_⟧ˢ`) instead anchors on
-- the UN-resolved `gmoduleToModule (Source.srcModule src)`, so completeness is
-- not resolver-vacuous; `Once.Adequacy.ResolveBridge` proves the resolver right.
------------------------------------------------------------------------

eitherToMaybe : String ⊎ P.Module → Maybe P.Module
eitherToMaybe (inj₁ _) = nothing
eitherToMaybe (inj₂ m) = just m

srcToModule-aux : ModuleMap → Maybe P.Module → Maybe P.Module
srcToModule-aux mm nothing  = nothing
srcToModule-aux mm (just m) = eitherToMaybe (resolveImports mm m)

-- The verified front-end: lex+parse the source TEXT (`parseStrict`), then resolve
-- imports. Both the lexer and parser now run INSIDE `compile`; their correctness
-- is the apex's concern (`Once.Adequacy.FrontEndBridge`), as the resolver's is
-- (`Once.Adequacy.ResolveBridge`).
srcToModule : Source → Maybe P.Module
srcToModule src =
  srcToModule-aux (Source.srcImports src) (eitherToMaybe (parseStrict (Source.srcText src)))

-- The front-end SUCCEEDS to `mR` exactly when the source text parses to `mU`
-- and the resolver maps it to `mR`. (Reduction lemma the apex completeness path
-- uses to rewrite `srcToModule src` once both halves are known.)
srcToModule-just : ∀ (src : Source) (mU mR : P.Module) →
  parseStrict (Source.srcText src) ≡ inj₂ mU →
  resolveImports (Source.srcImports src) mU ≡ inj₂ mR →
  srcToModule src ≡ just mR
srcToModule-just src mU mR p-eq r-eq rewrite p-eq | r-eq = refl

-- Inversion: a successful front-end (`srcToModule src ≡ just mR`) DECOMPOSES
-- into a successful parse (`parseStrict text ≡ inj₂ mU`) and a successful
-- resolve (`resolveImports … mU ≡ inj₂ mR`). The apex soundness path uses this
-- to recover the un-resolved parsed module `mU` (for `_⊢R_`/the FrontEndBridge).
-- Clause-based on the `⊎` results (no `with`-opacity).
eitherToMaybe-inv : ∀ (e : String ⊎ P.Module) (m : P.Module) →
  eitherToMaybe e ≡ just m → e ≡ inj₂ m
eitherToMaybe-inv (inj₁ _)  m ()
eitherToMaybe-inv (inj₂ m') m eq = cong inj₂ (just-injective eq)

srcToModule-inv-p : ∀ (mm : ModuleMap) (pr : String ⊎ P.Module) (mR : P.Module) →
  srcToModule-aux mm (eitherToMaybe pr) ≡ just mR →
  Σ-syntax P.Module (λ mU → (pr ≡ inj₂ mU) × (resolveImports mm mU ≡ inj₂ mR))
srcToModule-inv-p mm (inj₁ _)  mR ()
srcToModule-inv-p mm (inj₂ mU) mR eq = mU , refl , eitherToMaybe-inv (resolveImports mm mU) mR eq

srcToModule-inv : ∀ (src : Source) (mR : P.Module) →
  srcToModule src ≡ just mR →
  Σ-syntax P.Module (λ mU →
    (parseStrict (Source.srcText src) ≡ inj₂ mU)
    × (resolveImports (Source.srcImports src) mU ≡ inj₂ mR))
srcToModule-inv src mR eq =
  srcToModule-inv-p (Source.srcImports src) (parseStrict (Source.srcText src)) mR eq

------------------------------------------------------------------------
-- The source semantics (discharges the `Behavior.⟦_⟧` postulate).
------------------------------------------------------------------------

-- D059/D060: the source meaning is the DENOTATIONAL `evalᴰ` (compositional →
-- reasons about Once programs; observation-depth → commensurable apex meter),
-- via `⟦_⟧IR ∘ moduleToProgram` (D244: main in its function table's environment). The surface presentation `⟦_⟧ˢ` agrees with this
-- IR presentation by the proven `faithful` (a standalone fact, no longer a
-- conjunct of the compiler theorem).
-- J-style dispatch on the parse result (explicit `Maybe`, no `with`), so
-- `⟦⟧-via-module` below can `rewrite` the parse equation through it.
sourceTrace-aux : Maybe P.Module → TargetNum → Behavior
sourceTrace-aux (just m) fmt = ⟦ moduleToProgram m ⟧IR fmt
sourceTrace-aux nothing  _   = silent

sourceTrace : Source → TargetNum → Behavior
sourceTrace src fmt = sourceTrace-aux (srcToModule src) fmt

-- `abstract`: keep `⟦_⟧` opaque downstream. Otherwise `⟦ src ⟧` unfolds
-- to `sourceTrace src`'s `with gmoduleToModule src …`, and
-- `Verified.Compile.correct`'s own `with gmoduleToModule src in g-eq`
-- reduces the goal's `⟦ src ⟧` while the per-stage postulate's stays
-- unreduced → `UnequalTerms`. Opacity makes both sides the same term.
abstract
  ⟦_⟧ : Source → TargetNum → Behavior
  ⟦ src ⟧ = sourceTrace src

  -- Reduction lemma (exported): when `src` parses AND RESOLVES to module `m`
  -- (`srcToModule src ≡ just m`), its meaning IS `m`'s source trace. Proven
  -- INSIDE the `abstract` block (where `⟦_⟧` reduces to `sourceTrace`); the
  -- J-style `sourceTrace-aux` makes the front-end equation `rewrite`-able with
  -- no `with`-opacity. This discharges `Compile.gmoduleToModule-correct`.
  ⟦⟧-via-module :
    ∀ (src : Source) (m : P.Module) → srcToModule src ≡ just m →
    ∀ (fmt : TargetNum) → ⟦ src ⟧ fmt ≡ ⟦ moduleToProgram m ⟧IR fmt
  ⟦⟧-via-module src m eq fmt rewrite eq = refl
