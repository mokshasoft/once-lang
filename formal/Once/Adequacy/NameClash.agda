-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.NameClash
--
-- Plan 0.50 — the DISCHARGE of `program-no-clash`: the symbols the compiler
-- emits for a module's top-level definitions are pairwise distinct. This is
-- the precondition the assembler trust point (`assemble-correct`) demands, and
-- it is PROVED here (no postulate), by exactly the decomposition the design
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
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)

open import Data.String using (_≟_)
open import Once.Parser using
  ( FunInfo; PolyFunInfo
  ; extractFunctions; extractFunctions-go; extractAliases
  ; namesDistinct; nameElem; allValidIdentB; validIdentB; validCharsB
  ; allIdentContinue; guardDistinct; distinctOrErr )
open import Once.Parser.Module.Core using (Module; mkModule)
open import Once.Parser.Lexer using (isIdentStart; isIdentContinue)
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Target.SymbolInjective using (ValidIdent; ValidIdentChars; once-symbol-own-≢)

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
-- The emitted-symbol list of a module, and its distinctness.
------------------------------------------------------------------------

symsOf : (String ⊎ (List FunInfo × List PolyFunInfo)) → List String
symsOf (inj₁ _)            = []
symsOf (inj₂ (funs , _))   = map once-symbol-own (map FunInfo.funName funs)

funSymsOf : Module → List String
funSymsOf m = symsOf (extractFunctions (extractAliases m) m)

-- The compiled top-level symbols of `m` are pairwise distinct.
DistinctSymbols : Module → Set
DistinctSymbols m = AllPairs _≢_ (funSymsOf m)

------------------------------------------------------------------------
-- The discharge.
------------------------------------------------------------------------

no-clash-bool : (b : Bool) (funs : List FunInfo) (polys : List PolyFunInfo)
  → b ≡ (namesDistinct (map FunInfo.funName funs) ∧ allValidIdentB (map FunInfo.funName funs))
  → AllPairs _≢_ (symsOf (distinctOrErr b (inj₂ (funs , polys))))
no-clash-bool true  funs polys beq =
  map-allpairs-own (map FunInfo.funName funs)
    (namesDistinct-sound  _ (∧-elimˡ (sym beq)))
    (allValidIdentB-sound _ (∧-elimʳ (sym beq)))
no-clash-bool false funs polys beq = []

no-clash-guard : (r : String ⊎ (List FunInfo × List PolyFunInfo))
  → AllPairs _≢_ (symsOf (guardDistinct r))
no-clash-guard (inj₁ _)            = []
no-clash-guard (inj₂ (funs , polys)) =
  no-clash-bool
    (namesDistinct (map FunInfo.funName funs) ∧ allValidIdentB (map FunInfo.funName funs))
    funs polys refl

-- PROVED (no postulate): every module's emitted def-symbols are distinct.
program-no-clash : ∀ (m : Module) → DistinctSymbols m
program-no-clash (mkModule ds) =
  no-clash-guard (extractFunctions-go (extractAliases (mkModule ds)) ds nothing)
