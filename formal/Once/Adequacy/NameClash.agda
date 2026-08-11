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
open import Data.List using (List; []; _∷_; map)
open import Data.Char using (Char)
open import Data.Maybe using (nothing)
open import Data.String using (String; toList)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Data.String using (_≟_)
open import Data.Sum.Properties using (inj₂-injective)
open import Once.Parser using
  ( FunInfo; PolyFunInfo
  ; extractFunctions; extractFunctions-go; extractAliases
  ; namesDistinct; nameElem; allValidIdentB; validIdentB; validCharsB
  ; emittedNames; emittedNames-cons
  ; allIdentContinue; guardDistinct; distinctOrErr )
open import Once.Parser.Module.Core using (Module; mkModule)
open import Once.Parser.Lexer using (isIdentStart; isIdentContinue)
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Target.SymbolInjective using (ValidIdent; ValidIdentChars; once-symbol-own-≢)
open import Once.CanonicalName using (bare)
open import Once.TypeCheck.Elaborate using (PolyCtx)
open import Once.TypeCheck.Classify using (SigEffectCtx)
import Once.Compile as C

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
distinctOrErr-true : ∀ b {p p' : List FunInfo × List PolyFunInfo}
  → distinctOrErr b (inj₂ p) ≡ inj₂ p' → b ≡ true
distinctOrErr-true true  _  = refl
distinctOrErr-true false ()

guard-true : (r : String ⊎ (List FunInfo × List PolyFunInfo))
  {funs : List FunInfo} {polys : List PolyFunInfo}
  → guardDistinct r ≡ inj₂ (funs , polys)
  → (namesDistinct (emittedNames funs) ∧ allValidIdentB (emittedNames funs)) ≡ true
guard-true (inj₁ _) ()
guard-true (inj₂ (funs₀ , polys₀)) eq
  with namesDistinct (emittedNames funs₀) ∧ allValidIdentB (emittedNames funs₀) in beq
... | true  =
      subst (λ fs → (namesDistinct (emittedNames fs) ∧ allValidIdentB (emittedNames fs)) ≡ true)
            (cong proj₁ (inj₂-injective eq)) beq
... | false with eq
...   | ()

-- (b) the CODEGEN-FAITHFULNESS bridge: the symbols `compileAllFuns-go` actually
-- builds equal `once-symbol-own` of the NON-primitive funNames. Induction through
-- the mutual aux (template: `MainIRForm.caf-go-find-form`); `caf-go-wrap` builds
-- `mkCompiledFun (bare (funName fi)) … (funIsPrimitive fi)`, so this is forced.
caf-syms : ∀ (doOpt : Bool) (polys : PolyCtx) (sigEffs : SigEffectCtx)
  (funs : List FunInfo) (ctx : C.FunCtx) (cfs : List C.CompiledFun)
  → C.compileAllFuns-go C.Heap doOpt polys sigEffs funs ctx ≡ inj₂ cfs
  → C.emittedSyms cfs ≡ map once-symbol-own (emittedNames funs)
caf-syms doOpt polys sigEffs [] ctx cfs caf-eq =
  cong C.emittedSyms (sym (inj₂-injective caf-eq))
caf-syms doOpt polys sigEffs (fi ∷ rest) ctx cfs caf-eq
  with C.resolveFunType ctx polys (FunInfo.funType fi) (FunInfo.funBody fi) in rf-eq
... | inj₁ err = case caf-eq of λ ()
... | inj₂ ty
    with C.compileFun C.Heap doOpt ctx polys sigEffs (FunInfo.funName fi) ty (FunInfo.funBody fi) in cf-eq
...   | inj₁ err = case caf-eq of λ ()
...   | inj₂ irFun
      with C.compileAllFuns-go C.Heap doOpt polys sigEffs rest (C.extendFunCtx ctx (FunInfo.funName fi) ty) in rec-eq
...     | inj₁ err = case caf-eq of λ ()
...     | inj₂ compiled-rest =
          subst (λ c → C.emittedSyms c ≡ map once-symbol-own (emittedNames (fi ∷ rest)))
                (inj₂-injective caf-eq)
                (cons (FunInfo.funIsPrimitive fi) refl)
      where
        cfW = C.maybeWrapMain (FunInfo.funName fi) ty irFun
        IH : C.emittedSyms compiled-rest ≡ map once-symbol-own (emittedNames rest)
        IH = caf-syms doOpt polys sigEffs rest (C.extendFunCtx ctx (FunInfo.funName fi) ty) compiled-rest rec-eq
        cons : (b : Bool) → FunInfo.funIsPrimitive fi ≡ b
          → C.emittedSyms (C.mkCompiledFun (bare (FunInfo.funName fi)) (proj₁ cfW) (proj₂ cfW) b ∷ compiled-rest)
            ≡ map once-symbol-own (emittedNames-cons b fi (emittedNames rest))
        cons true  _ = IH
        cons false _ = cong (once-symbol-own (FunInfo.funName fi) ∷_) IH

-- PROVED: the symbols the codegen emits for `m` are distinct.
program-no-clash : ∀ (m : Module) → DistinctSymbols m
program-no-clash (mkModule ds)
  with extractFunctions (extractAliases (mkModule ds)) (mkModule ds) in efeq
... | inj₁ _ = []
... | inj₂ (funs , polys)
    with C.compileAllFuns C.Heap false funs (C.buildPolyCtx polys) (C.collectSigEffects ds) in caeq
...   | inj₁ _ = []
...   | inj₂ cfs =
        subst (AllPairs _≢_) (sym bridge)
          (map-allpairs-own (emittedNames funs)
            (namesDistinct-sound  _ (∧-elimˡ guard))
            (allValidIdentB-sound _ (∧-elimʳ guard)))
      where
        guard : (namesDistinct (emittedNames funs) ∧ allValidIdentB (emittedNames funs)) ≡ true
        guard = guard-true (extractFunctions-go (extractAliases (mkModule ds)) ds nothing) efeq
        bridge : C.emittedSyms cfs ≡ map once-symbol-own (emittedNames funs)
        bridge = caf-syms false (C.buildPolyCtx polys) (C.collectSigEffects ds) funs C.emptyFunCtx cfs caeq
