-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.NameClash
--
-- Plan 0.50 — the DISCHARGE of `program-no-clash`: the symbols the compiler
-- emits for a module's top-level definitions are pairwise distinct. This is
-- the precondition the assembler trust point (`assemble-correct`) demands, and
-- it is PROVED here, by exactly the decomposition the design
-- intends:
--
--   distinct DEFINITION names         (from `extractFunctions`' guard)
--   × each name is a valid identifier (from the same guard, lexer predicates)
--   ───────────────────────────────────────────────────────────────────────
--   distinct emitted SYMBOLS          (via `once-symbol-own-≢`, the proven
--                                      encoding injectivity)
--
-- It is UNCONDITIONAL in the module: `extractFunctions` only yields `inj₂`
-- when its well-formedness guard (`namesDistinct ∧ allValidNameB`) passes, so
-- the `inj₁` branch contributes an empty symbol list (trivially distinct) and
-- the `inj₂` branch carries the guard evidence.
------------------------------------------------------------------------

module Once.Adequacy.NameClash where

open import Once.Internal.Type.Instance using (kindsOf)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (nothing; just)
open import Data.String using (String; toList)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary using (yes; no; proof)
open import Relation.Nullary.Reflects using (Reflects; invert)
open import Relation.Nullary.Decidable using (¬?)
open import Data.List.Relation.Unary.AllPairs using (allPairs?)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Data.String using (_≟_)
open import Data.Sum.Properties using (inj₂-injective)
open import Once.Parser using
  ( FunInfo; PolyFunInfo; Entry; e-fun; e-poly; funsOf; polysOf
  ; extractFunctions; extractFunctions-go; thenExtract; sigsAdjacent; sigsFirst
  ; namesDistinct; allValidNameB; validNameB; validCharsB; allOpNameChars; opCharsB
  ; emittedNames; emittedNames-cons
  ; allIdentContinue; guardDistinct; distinctOrErr; entryNameOf )
open import Once.Parser.Module.Core using (Module; mkModule; Resolved; resolved)
open import Once.Parser.Lexer using (isIdentContinue; isOpNameChar)
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Target.SymbolInjective using (ValidName; ValidIdentChars; OpNameChars; NameChars; once-symbol-own-≢)
open import Once.Spec.Name using (bare)
import Once.Compile as C
import Once.IR as IR
import Once.TypeCheck.Elaborate as TE
import Once.TypeCheck.Classify as Classify
open import Once.Internal.Type.Instance using (rigidOf)
open import Once.Internal.Principal using (below)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Internal.Type.Honest using (honest?)

------------------------------------------------------------------------
-- Boolean elimination helpers.
------------------------------------------------------------------------

∧-elimˡ : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
∧-elimˡ {true}  _  = refl
∧-elimˡ {false} ()

∧-elimʳ : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
∧-elimʳ {true}  eq = eq
∧-elimʳ {false} ()

not-true→false : ∀ {b} → not b ≡ true → b ≡ false
not-true→false {false} _  = refl
not-true→false {true}  ()

T≢F : true ≢ false
T≢F ()

------------------------------------------------------------------------
-- Bool checks → Prop witnesses (`ValidName`).
------------------------------------------------------------------------

allIdentContinue-sound : ∀ cs → allIdentContinue cs ≡ true
  → All (λ d → isIdentContinue d ≡ true) cs
allIdentContinue-sound []       _  = []
allIdentContinue-sound (c ∷ cs) eq = ∧-elimˡ eq ∷ allIdentContinue-sound cs (∧-elimʳ eq)

validCharsB-sound : ∀ cs → validCharsB cs ≡ true → ValidIdentChars cs
validCharsB-sound []       ()
validCharsB-sound (c ∷ cs) eq = ∧-elimˡ eq , allIdentContinue-sound cs (∧-elimʳ eq)

allOpNameChars-sound : ∀ cs → allOpNameChars cs ≡ true → All (λ d → isOpNameChar d ≡ true) cs
allOpNameChars-sound []       _  = []
allOpNameChars-sound (c ∷ cs) eq = ∧-elimˡ eq ∷ allOpNameChars-sound cs (∧-elimʳ eq)

opCharsB-sound : ∀ cs → opCharsB cs ≡ true → OpNameChars cs
opCharsB-sound []       ()
opCharsB-sound (c ∷ cs) eq = allOpNameChars-sound (c ∷ cs) eq

-- (an identifier, else an operator's name)
nameChars-sound : ∀ cs → (b : Bool) → validCharsB cs ≡ b → (b ∨ opCharsB cs) ≡ true → NameChars cs
nameChars-sound cs true  e _  = inj₁ (validCharsB-sound cs e)
nameChars-sound cs false _ eq = inj₂ (opCharsB-sound cs eq)

validNameB-sound : ∀ s → validNameB s ≡ true → ValidName s
validNameB-sound s eq = nameChars-sound (toList s) (validCharsB (toList s)) refl eq

allValidNameB-sound : ∀ names → allValidNameB names ≡ true → All ValidName names
allValidNameB-sound []       _  = []
allValidNameB-sound (x ∷ xs) eq =
  validNameB-sound x (∧-elimˡ eq) ∷ allValidNameB-sound xs (∧-elimʳ eq)

------------------------------------------------------------------------
-- Bool distinctness → `AllPairs _≢_`.
------------------------------------------------------------------------

namesDistinct-sound : ∀ names → namesDistinct names ≡ true → AllPairs _≢_ names
namesDistinct-sound names eq =
  invert (subst (Reflects (AllPairs _≢_ names)) eq (proof (allPairs? (λ x y → ¬? (x ≟ y)) names)))

------------------------------------------------------------------------
-- Lift distinct+valid NAMES to distinct SYMBOLS via the proven encoding
-- injectivity (`once-symbol-own-≢`).
------------------------------------------------------------------------

allpairs-head : ∀ (x : String) (xs : List String)
  → All (λ y → x ≢ y) xs → ValidName x → All ValidName xs
  → All (λ s → once-symbol-own x ≢ s) (map once-symbol-own xs)
allpairs-head x []       []          vx []          = []
allpairs-head x (y ∷ ys) (x≢y ∷ rest) vx (vy ∷ vys) =
  once-symbol-own-≢ x y vx vy x≢y ∷ allpairs-head x ys rest vx vys

map-allpairs-own : ∀ (names : List String)
  → AllPairs _≢_ names → All ValidName names
  → AllPairs _≢_ (map once-symbol-own names)
map-allpairs-own []       []        []          = []
map-allpairs-own (x ∷ xs) (px ∷ ap) (vx ∷ vxs) =
  allpairs-head x xs px vx vxs ∷ map-allpairs-own xs ap vxs

------------------------------------------------------------------------
-- Distinctness OF THE REAL CODEGEN OUTPUT (`C.moduleSyms`, defined in
-- `Once.Compile` on the SAME cfs `compileFromModule` renders). This is the
-- precondition `assemble-correct` demands; proving it over `C.moduleSyms`
-- (not an `extractFunctions` re-derivation) is what makes a wrong set a type
-- error rather than a runtime regression.
------------------------------------------------------------------------

DistinctSymbols : Resolved → Set
DistinctSymbols m = AllPairs _≢_ (C.moduleSyms IR.Heap false m)

-- (a) the extractor guard fired ⇒ the well-formedness Bool was `true`.
distinctOrErr-true : ∀ b {m} {p p' : List Entry}
  → distinctOrErr b m (inj₂ p) ≡ inj₂ p' → b ≡ true
distinctOrErr-true true  _  = refl
distinctOrErr-true false ()

-- The parser's guard (D241): the emitted names are distinct and valid, and
-- every definition name — monomorphic and telescope together — is distinct.
-- D249: the whole guard, one more conjunct — every entry name is distinct.
GuardB : List Entry → Bool
GuardB es = ((namesDistinct (emittedNames (funsOf es)) ∧ allValidNameB (emittedNames (funsOf es)))
              ∧ namesDistinct (emittedNames (funsOf es) ++ map PolyFunInfo.pfunName (polysOf es)))
            ∧ namesDistinct (map entryNameOf es)

guard-whole : (r : String ⊎ List Entry) {es : List Entry} → guardDistinct r ≡ inj₂ es → GuardB es ≡ true
guard-whole (inj₁ _) ()
guard-whole (inj₂ es₀) eq with GuardB es₀ in beq
... | true  = subst (λ es → GuardB es ≡ true) (inj₂-injective eq) beq
... | false with eq
...   | ()

guard-all : (r : String ⊎ List Entry) {es : List Entry}
  → guardDistinct r ≡ inj₂ es
  → ((namesDistinct (emittedNames (funsOf es)) ∧ allValidNameB (emittedNames (funsOf es)))
      ∧ namesDistinct (emittedNames (funsOf es) ++ map PolyFunInfo.pfunName (polysOf es))) ≡ true
guard-all r eq = ∧-elimˡ (guard-whole r eq)

-- D249: every entry of an accepted module has its own name.
guard-entries : (r : String ⊎ List Entry) {es : List Entry}
  → guardDistinct r ≡ inj₂ es → AllPairs _≢_ (map entryNameOf es)
guard-entries r eq = namesDistinct-sound _ (∧-elimʳ (guard-whole r eq))

guard-true : (r : String ⊎ List Entry) {es : List Entry}
  → guardDistinct r ≡ inj₂ es
  → (namesDistinct (emittedNames (funsOf es)) ∧ allValidNameB (emittedNames (funsOf es))) ≡ true
guard-true r eq = ∧-elimˡ (guard-all r eq)

-- The telescope walk emits exactly the monomorphic definitions' symbols.
ce-syms : ∀ (doOpt : Bool) (sc : C.CScope) (es : List Entry) (cfs : List C.CompiledFun)
  → C.compileEntries IR.Heap doOpt sc es ≡ inj₂ cfs
  → C.emittedSyms cfs ≡ map once-symbol-own (emittedNames (funsOf es))
ce-syms-fun : ∀ (doOpt : Bool) (sc : C.CScope) (fi : FunInfo) (es : List Entry) (b : Bool)
  → FunInfo.funIsPrimitive fi ≡ b → (cfs : List C.CompiledFun)
  → C.ce-fun IR.Heap doOpt sc fi es b ≡ inj₂ cfs
  → C.emittedSyms cfs ≡ map once-symbol-own (emittedNames (funsOf (e-fun fi ∷ es)))

ce-syms doOpt sc [] cfs eq = cong C.emittedSyms (sym (inj₂-injective eq))
ce-syms doOpt sc (e-fun fi ∷ es) cfs eq = ce-syms-fun doOpt sc fi es (FunInfo.funIsPrimitive fi) refl cfs eq
ce-syms doOpt sc (e-poly pfi ∷ es) cfs eq
  with C.firstChecking (Classify.ctxAt (kindsOf (PolyFunInfo.pfunType pfi)) (C.ctop sc) (C.cpolys sc)) (PolyFunInfo.pfunBody pfi) (below (rigidOf (PolyFunInfo.pfunType pfi)))
... | just _ = case eq of λ ()
... | nothing
  with C.checkOK (TE.checkElabV (Classify.ctxAt (kindsOf (PolyFunInfo.pfunType pfi)) (C.ctop sc) (C.cpolys sc)) (PolyFunInfo.pfunBody pfi) (rigidOf (PolyFunInfo.pfunType pfi)))
...   | inj₁ _ = case eq of λ ()
...   | inj₂ _ = ce-syms doOpt (C.addEntry sc pfi) es cfs eq

ce-syms-fun doOpt sc fi es true ep cfs eq with FunInfo.funType fi
... | nothing = case eq of λ ()
... | just ty with isConcrete? ty | honest? ty
...   | nothing | _ = case eq of λ ()
...   | just _ | nothing = case eq of λ ()
...   | just _ | just _ =
          -- D274: an FFI declaration extends Σ only — no compiled function.
          subst (λ b → C.emittedSyms cfs
                       ≡ map once-symbol-own (emittedNames-cons b fi (emittedNames (funsOf es))))
                (sym ep) (ce-syms doOpt (C.extendSig sc (FunInfo.funName fi) ty) es cfs eq)
ce-syms-fun doOpt sc fi es false ep cfs eq
  with C.resolveFunType (C.ctop sc) (C.cpolys sc) (FunInfo.funType fi) (FunInfo.funBody fi)
... | inj₁ _ = case eq of λ ()
... | inj₂ ty
  with C.firstChecking (Classify.ctxWithImportsAndPolys (C.ctop sc) (C.cpolys sc)) (FunInfo.funBody fi) (below ty)
...   | just _ = case eq of λ ()
...   | nothing
    with C.compileFunM (FunInfo.funType fi) IR.Heap doOpt (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (FunInfo.funName fi) ty (FunInfo.funBody fi)
...         | inj₁ _ = case eq of λ ()
...         | inj₂ irFun
      with C.compileEntries IR.Heap doOpt (C.extendScope sc (FunInfo.funName fi) ty) es in rec
...           | inj₁ _ = case eq of λ ()
...           | inj₂ rest =
          subst (λ c → C.emittedSyms c ≡ map once-symbol-own (emittedNames (funsOf (e-fun fi ∷ es))))
                (inj₂-injective eq)
                (subst (λ b → C.emittedSyms (C.mkCompiledFun (bare (FunInfo.funName fi)) ty irFun ∷ rest)
                              ≡ map once-symbol-own (emittedNames-cons b fi (emittedNames (funsOf es))))
                       (sym ep) (cong (once-symbol-own (FunInfo.funName fi) ∷_) (ce-syms doOpt (C.extendScope sc (FunInfo.funName fi) ty) es rest rec)))

program-no-clash : ∀ (m : Resolved) → DistinctSymbols m
program-no-clash (resolved (mkModule ds) is)
  with extractFunctions (resolved (mkModule ds) is) in efeq
... | inj₁ _ = []
... | inj₂ es
    with C.compileEntries IR.Heap false C.emptyCScope es in caeq
...   | inj₁ _ = []
...   | inj₂ cfs =
        subst (AllPairs _≢_) (sym bridge)
          (map-allpairs-own (emittedNames (funsOf es))
            (namesDistinct-sound  _ (∧-elimˡ guard))
            (allValidNameB-sound _ (∧-elimʳ guard)))
      where
        guard : (namesDistinct (emittedNames (funsOf es)) ∧ allValidNameB (emittedNames (funsOf es))) ≡ true
        guard = guard-true (thenExtract (sigsAdjacent ds nothing) (extractFunctions-go (sigsFirst ds is) nothing)) efeq
        bridge : C.emittedSyms cfs ≡ map once-symbol-own (emittedNames (funsOf es))
        bridge = ce-syms false C.emptyCScope es cfs caeq
