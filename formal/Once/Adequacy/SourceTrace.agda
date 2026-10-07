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

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit using (tt)
open import Data.String using (String) renaming ()
open import Once.CanonicalName using (CanonicalName) renaming (_≟ᶜ_ to _≟cn_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Unit)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
import Once.Compile as C
-- plan 0.107: the program is the COMPILER's (one walk) — defined in
-- `Once.Compile` beside the emitter, and read from there.
open import Once.Compile using (moduleToIR; moduleToProgram; rewrite-fun; rewrite-table; rewrite-program)
import Once.Parser.Module.Core as P
-- D165: the arith-block lifting the BACKEND runs before codegen. Imported here
-- so the IR the emitter actually compiles can be NAMED (`moduleToIR-emitted`).
open import Once.Arith.Machine.Rewrite using (rewrite-ir)
-- plan 0.103: the arith pass adds no call (proved).
open import Once.Adequacy.RewriteLinked using (rewrite-ir-linked)
open import Data.Product using (proj₁)
-- Plan 0.52: pull the LEXER+PARSER into the verified front-end — `srcToModule`
-- runs the executable `parseStrict` on the source TEXT (a front-end bug reds the
-- apex via `Once.Adequacy.FrontEndBridge`). Plan 0.51: and then the resolver, so
-- `moduleToIR` compiles the SAME (resolved) module the binary runs.
open import Once.Parser using (parseStrict)
open import Once.Parser.Module.Resolve using (resolveImports; ModuleMap)
open import Once.Denotation.Behavior using (Source; Behavior; mkBehavior; silent)
-- Plan 0.73 (D113): the meaning is target-relative at `Float`, so the format
-- is threaded in. An explicit ARGUMENT, not a module parameter — these are
-- recursive and a parameterised module stops reducing at a variable instance.
open import Once.Target.Arch using (TargetNum)
open import Once.Denotation.TraceMonad
  using (projTrace; PrefixFamily; projTrace-pf; Interp; pureHalf)
open Once.Denotation.TraceMonad.PrefixFamily using (bnd; coh; sat)
open import Once.Denotation.Program using (IRFun; IRProgram; runIR; LinkedAt; LinkedAt-at; Linked; LinkedProgram)
open Once.Denotation.Program.IRProgram using (main; table)
open Once.Denotation.Program.IRFun using (fbody; fcod; fdom; fname)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Once.Spec.Contract using (ISig)
import Once.IR as I
open import Once.IRTy using (IRTy; _≟IRTy_)

------------------------------------------------------------------------
-- Source → IR of `main` (option (a): reuse the compiler's elaborator).
------------------------------------------------------------------------

-- | Recognise `main`'s type, `IO Unit`.


-- D253: `main` is an entry like any other; the program's own `main` is the CALL
-- of it, `once_main`, which is exactly what `_start` runs.

-- Explicit dispatch on the three decisions (no `with`-opacity), so `findMain`'s
-- "is this the entry?" choice is analyzable. The FIRST argument is
-- `cfIsPrimitive cf`: a PRIMITIVE is never the entry — its body is not emitted
-- at codegen, so it has no `once_main` to call.

-- | A module is a PROGRAM when it has an entry `main : IO Unit`.

-- Explicit dispatch on the compile result (no `with`-opacity).

-- Non-resolving: the IR of the program's `main` (the call of the entry,
-- D253) in an ALREADY-RESOLVED module. The
-- module-level proofs (`AcceptSound`/`MainBuilds`/`ModuleComplete`) reason
-- about THIS over a module `mod` (interpreted as the RESOLVED module);
-- resolution is confined to `srcToModule` below, so those proofs are untouched.

------------------------------------------------------------------------
-- D244: THE COMPILED PROGRAM — the function table and `main`. The table is
-- every entry of the module (D246: an FFI declaration's is its SigOp wrapper;
-- D253: `main`'s is its direct-call form), LATEST-FIRST, so each entry is
-- evaluated in the ones declared before it (`tableEnv`). The compiler emits in
-- declaration order, so the table is that list reversed.
------------------------------------------------------------------------
-- Each entry is the DIRECT-CALL morphism the emitter compiles (D064,
-- `directCallIR`), which is what `once_<name>` implements in the image.

-- D253: every entry, `main` included — it is the callee of the program's `main`.


-- The table of a compile RESULT (a failed compile has none), and of a module.


-- The program at a table, given `main`. Stated over `moduleToIR` so that every
-- apex step that already has `moduleToIR m ≡ just ir` reaches the program by
-- rewriting with it.


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

linked-retable : ∀ {σ : ISig} (tbl : List IRFun) {A B} (ir : IR A B) → Linked σ tbl ir → Linked σ (rewrite-table tbl) ir
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
linked-retable tbl (I.SigOp _)     d = d
linked-retable tbl (I.const _ _)   _ = tt

-- The compiled program is linked: `Adequacy.ProgramLinked.moduleToProgram-linked`
-- (D253: `main` is an entry; D254: a body is its derivation's realization).
-- (the arith lifting keeps a body linked: PROVED, `RewriteLinked`.)

-- …every entry of a table, rewritten, against the rewritten table.
all-rewrite-linked : ∀ {σ : ISig} (tbl es : List IRFun)
                   → All (λ e → Linked σ tbl (fbody e)) es
                   → All (λ e → Linked σ (rewrite-table tbl) (fbody e)) (rewrite-table es)
all-rewrite-linked tbl []       []         = []
all-rewrite-linked tbl (e ∷ es) (le ∷ les) =
  rewrite-ir-linked (rewrite-table tbl) (fbody e) (linked-retable tbl (fbody e) le)
  ∷ all-rewrite-linked tbl es les

rewrite-program-linked : ∀ {σ : ISig} (p : IRProgram) → LinkedProgram σ p → LinkedProgram σ (rewrite-program p)
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
-- are exactly `PrefixFamily`, which every RUN satisfies (plan 0.105: the
-- observable is a `take` of one run's events, `projTrace-pf`).
⟦_⟧IR : Maybe IRProgram → TargetNum → Interp → Behavior
-- D244: the meaning of a compiled program is `main` run in the environment of
-- its function table (`runIR`); an internal call means its callee. Plan 0.105:
-- run AGAINST the interpretation — its pure half is the FFI values, its
-- answers what the calls return.
⟦ just p ⟧IR fmt ι = mkBehavior (projTrace ι m) (coh pf) (bnd pf) (sat pf)
  where
    m  = runIR fmt (pureHalf ι) p
    pf : PrefixFamily (projTrace ι m)
    pf = projTrace-pf ι m
-- A module with no `main` observes nothing, at every depth — the empty family,
-- whose three laws are immediate.
⟦ nothing ⟧IR _ _ = silent

-- D165, RESTATED AT THE MEANING (plan 0.103 6a″): the arith lifting preserves
-- a program's denotation — `Adequacy.RewritePreserves.rewrite-program-preserves`.

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
sourceTrace-aux : Maybe P.Module → TargetNum → Interp → Behavior
sourceTrace-aux (just m) fmt = ⟦ moduleToProgram m ⟧IR fmt
sourceTrace-aux nothing  _ _ = silent

sourceTrace : Source → TargetNum → Interp → Behavior
sourceTrace src fmt = sourceTrace-aux (srcToModule src) fmt

-- `abstract`: keep `⟦_⟧` opaque downstream. Otherwise `⟦ src ⟧` unfolds
-- to `sourceTrace src`'s `with gmoduleToModule src …`, and
-- `Verified.Compile.correct`'s own `with gmoduleToModule src in g-eq`
-- reduces the goal's `⟦ src ⟧` while the per-stage postulate's stays
-- unreduced → `UnequalTerms`. Opacity makes both sides the same term.
abstract
  -- Plan 0.105: a source's behaviour is relative to an interpretation of its
  -- FFI calls; correctness quantifies over it.
  ⟦_⟧ : Source → TargetNum → Interp → Behavior
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
