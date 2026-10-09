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
-- when its well-formedness guard (`namesDistinct ∧ allValidIdentB`) passes, so
-- the `inj₁` branch contributes an empty symbol list (trivially distinct) and
-- the `inj₂` branch carries the guard evidence.
------------------------------------------------------------------------

module Once.Adequacy.NameClash where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (nothing; just)
open import Data.String using (String; toList)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Data.String using (_≟_)
open import Data.Sum.Properties using (inj₂-injective)
open import Once.Parser using
  ( FunInfo; PolyFunInfo; Entry; e-fun; e-poly; funsOf; polysOf
  ; extractFunctions; extractFunctions-go; extractAliases
  ; namesDistinct; nameElem; allValidIdentB; validIdentB; validCharsB
  ; emittedNames; emittedNames-cons
  ; allIdentContinue; guardDistinct; distinctOrErr; entryNameOf )
open import Once.Parser.Module.Core using (Module; mkModule)
open import Once.Parser.Lexer using (isIdentContinue)
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Target.SymbolInjective using (ValidIdent; ValidIdentChars; once-symbol-own-≢)
open import Once.CanonicalName using (bare)
import Once.Compile as C
import Once.TypeCheck.Elaborate as TE
import Once.TypeCheck.Classify as Classify
open import Once.Type.Rigid using (rigidOf; rigidFree?)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Type.Honest using (honest?)

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
-- Bool checks → Prop witnesses (`ValidIdent`).
------------------------------------------------------------------------

allIdentContinue-sound : ∀ cs → allIdentContinue cs ≡ true
  → All (λ d → isIdentContinue d ≡ true) cs
allIdentContinue-sound []       _  = []
allIdentContinue-sound (c ∷ cs) eq = ∧-elimˡ eq ∷ allIdentContinue-sound cs (∧-elimʳ eq)

validCharsB-sound : ∀ cs → validCharsB cs ≡ true → ValidIdentChars cs
validCharsB-sound []       ()
validCharsB-sound (c ∷ cs) eq = ∧-elimˡ eq , allIdentContinue-sound cs (∧-elimʳ eq)

validIdentB-sound : ∀ s → validIdentB s ≡ true → ValidIdent s
validIdentB-sound s eq = validCharsB-sound (toList s) eq

allValidIdentB-sound : ∀ names → allValidIdentB names ≡ true → All ValidIdent names
allValidIdentB-sound []       _  = []
allValidIdentB-sound (x ∷ xs) eq =
  validIdentB-sound x (∧-elimˡ eq) ∷ allValidIdentB-sound xs (∧-elimʳ eq)

------------------------------------------------------------------------
-- Bool distinctness → `AllPairs _≢_`.
------------------------------------------------------------------------

nameElem-false→All≢ : ∀ x xs → nameElem x xs ≡ false → All (λ y → x ≢ y) xs
nameElem-false→All≢ x []       _  = []
nameElem-false→All≢ x (y ∷ ys) eq with x ≟ y
... | yes _  = ⊥-elim (T≢F eq)
... | no ¬p  = (λ x≡y → ¬p x≡y) ∷ nameElem-false→All≢ x ys eq

namesDistinct-sound : ∀ names → namesDistinct names ≡ true → AllPairs _≢_ names
namesDistinct-sound []       _  = []
namesDistinct-sound (x ∷ xs) eq =
  nameElem-false→All≢ x xs (not-true→false (∧-elimˡ eq)) ∷ namesDistinct-sound xs (∧-elimʳ eq)

------------------------------------------------------------------------
-- Lift distinct+valid NAMES to distinct SYMBOLS via the proven encoding
-- injectivity (`once-symbol-own-≢`).
------------------------------------------------------------------------

allpairs-head : ∀ (x : String) (xs : List String)
  → All (λ y → x ≢ y) xs → ValidIdent x → All ValidIdent xs
  → All (λ s → once-symbol-own x ≢ s) (map once-symbol-own xs)
allpairs-head x []       []          vx []          = []
allpairs-head x (y ∷ ys) (x≢y ∷ rest) vx (vy ∷ vys) =
  once-symbol-own-≢ x y vx vy x≢y ∷ allpairs-head x ys rest vx vys

map-allpairs-own : ∀ (names : List String)
  → AllPairs _≢_ names → All ValidIdent names
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

DistinctSymbols : Module → Set
DistinctSymbols m = AllPairs _≢_ (C.moduleSyms C.Heap false m)

-- (a) the extractor guard fired ⇒ the well-formedness Bool was `true`.
distinctOrErr-true : ∀ b {p p' : List Entry}
  → distinctOrErr b (inj₂ p) ≡ inj₂ p' → b ≡ true
distinctOrErr-true true  _  = refl
distinctOrErr-true false ()

-- The parser's guard (D241): the emitted names are distinct and valid, and
-- every definition name — monomorphic and telescope together — is distinct.
-- D249: the whole guard, one more conjunct — every entry name is distinct.
GuardB : List Entry → Bool
GuardB es = ((namesDistinct (emittedNames (funsOf es)) ∧ allValidIdentB (emittedNames (funsOf es)))
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
  → ((namesDistinct (emittedNames (funsOf es)) ∧ allValidIdentB (emittedNames (funsOf es)))
      ∧ namesDistinct (emittedNames (funsOf es) ++ map PolyFunInfo.pfunName (polysOf es))) ≡ true
guard-all r eq = ∧-elimˡ (guard-whole r eq)

-- D249: every entry of an accepted module has its own name.
guard-entries : (r : String ⊎ List Entry) {es : List Entry}
  → guardDistinct r ≡ inj₂ es → AllPairs _≢_ (map entryNameOf es)
guard-entries r eq = namesDistinct-sound _ (∧-elimʳ (guard-whole r eq))

guard-true : (r : String ⊎ List Entry) {es : List Entry}
  → guardDistinct r ≡ inj₂ es
  → (namesDistinct (emittedNames (funsOf es)) ∧ allValidIdentB (emittedNames (funsOf es))) ≡ true
guard-true r eq = ∧-elimˡ (guard-all r eq)

-- A suffix of a distinct list is distinct.
namesDistinct-++ʳ : ∀ (xs ys : List String) → namesDistinct (xs ++ ys) ≡ true → namesDistinct ys ≡ true
namesDistinct-++ʳ []       ys eq = eq
namesDistinct-++ʳ (x ∷ xs) ys eq = namesDistinct-++ʳ xs ys (∧-elimʳ eq)

guard-polys : (r : String ⊎ List Entry) {es : List Entry}
  → guardDistinct r ≡ inj₂ es
  → AllPairs _≢_ (map PolyFunInfo.pfunName (polysOf es))
guard-polys r {es} eq =
  namesDistinct-sound _ (namesDistinct-++ʳ (emittedNames (funsOf es)) _ (∧-elimʳ (guard-all r eq)))

-- The telescope walk emits exactly the monomorphic definitions' symbols.
ce-syms : ∀ (doOpt : Bool) (sc : C.CScope) (es : List Entry) (cfs : List C.CompiledFun)
  → C.compileEntries C.Heap doOpt sc es ≡ inj₂ cfs
  → C.emittedSyms cfs ≡ map once-symbol-own (emittedNames (funsOf es))
ce-syms-fun : ∀ (doOpt : Bool) (sc : C.CScope) (fi : FunInfo) (es : List Entry) (b : Bool)
  → FunInfo.funIsPrimitive fi ≡ b → (cfs : List C.CompiledFun)
  → C.ce-fun C.Heap doOpt sc fi es b ≡ inj₂ cfs
  → C.emittedSyms cfs ≡ map once-symbol-own (emittedNames (funsOf (e-fun fi ∷ es)))

ce-syms doOpt sc [] cfs eq = cong C.emittedSyms (sym (inj₂-injective eq))
ce-syms doOpt sc (e-fun fi ∷ es) cfs eq = ce-syms-fun doOpt sc fi es (FunInfo.funIsPrimitive fi) refl cfs eq
ce-syms doOpt sc (e-poly pfi ∷ es) cfs eq
  with C.checkOK (TE.checkElabV (Classify.ctxWithImportsAndPolys (C.ctop sc) (C.cpolys sc)) (PolyFunInfo.pfunBody pfi) (rigidOf (PolyFunInfo.pfunType pfi)))
... | inj₁ _ = case eq of λ ()
... | inj₂ _ = ce-syms doOpt (C.addEntry sc pfi) es cfs eq

ce-syms-fun doOpt sc fi es true ep cfs eq with FunInfo.funType fi
... | nothing = case eq of λ ()
... | just ty with isConcrete? ty | honest? ty | rigidFree? ty
...   | nothing | _ | _ = case eq of λ ()
...   | just _ | nothing | _ = case eq of λ ()
...   | just _ | just _ | nothing = case eq of λ ()
...   | just _ | just _ | just _ =
          -- D274: an FFI declaration extends Σ only — no compiled function.
          subst (λ b → C.emittedSyms cfs
                       ≡ map once-symbol-own (emittedNames-cons b fi (emittedNames (funsOf es))))
                (sym ep) (ce-syms doOpt (C.extendSig sc (FunInfo.funName fi) ty) es cfs eq)
ce-syms-fun doOpt sc fi es false ep cfs eq
  with C.resolveFunType (C.ctop sc) (C.cpolys sc) (FunInfo.funType fi) (FunInfo.funBody fi)
... | inj₁ _ = case eq of λ ()
... | inj₂ ty with rigidFree? ty
...   | nothing = case eq of λ ()
...   | just _
    with C.compileFun C.Heap doOpt (C.ctop sc) (C.cpolys sc) (C.declImps (C.CScope.ctele sc)) (FunInfo.funName fi) ty (FunInfo.funBody fi)
...     | inj₁ _ = case eq of λ ()
...     | inj₂ irFun
      with C.compileEntries C.Heap doOpt (C.extendScope sc (FunInfo.funName fi) ty) es in rec
...       | inj₁ _ = case eq of λ ()
...       | inj₂ rest =
          subst (λ c → C.emittedSyms c ≡ map once-symbol-own (emittedNames (funsOf (e-fun fi ∷ es))))
                (inj₂-injective eq)
                (subst (λ b → C.emittedSyms (C.mkCompiledFun (bare (FunInfo.funName fi)) ty irFun ∷ rest)
                              ≡ map once-symbol-own (emittedNames-cons b fi (emittedNames (funsOf es))))
                       (sym ep) (cong (once-symbol-own (FunInfo.funName fi) ∷_) (ce-syms doOpt (C.extendScope sc (FunInfo.funName fi) ty) es rest rec)))

program-no-clash : ∀ (m : Module) → DistinctSymbols m
program-no-clash (mkModule ds)
  with extractFunctions (extractAliases (mkModule ds)) (mkModule ds) in efeq
... | inj₁ _ = []
... | inj₂ es
    with C.compileEntries C.Heap false C.emptyCScope es in caeq
...   | inj₁ _ = []
...   | inj₂ cfs =
        subst (AllPairs _≢_) (sym bridge)
          (map-allpairs-own (emittedNames (funsOf es))
            (namesDistinct-sound  _ (∧-elimˡ guard))
            (allValidIdentB-sound _ (∧-elimʳ guard)))
      where
        guard : (namesDistinct (emittedNames (funsOf es)) ∧ allValidIdentB (emittedNames (funsOf es))) ≡ true
        guard = guard-true (extractFunctions-go (extractAliases (mkModule ds)) ds nothing) efeq
        bridge : C.emittedSyms cfs ≡ map once-symbol-own (emittedNames (funsOf es))
        bridge = ce-syms false C.emptyCScope es cfs caeq
