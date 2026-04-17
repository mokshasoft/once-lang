-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.Identities
--
-- Plan 0.3, gap G7 (first pass): algebraic identities of frontend
-- operations. Properties downstream tools and proofs rely on, stated
-- as theorems and bundled into `VerifiedTypeChecker`.
--
-- Identities landed here:
--   * `classifyAppHead`-determinism: classifying the same RawExpr
--     twice yields the same result (trivially `refl`, but stated as
--     a citable theorem).
--   * `decideLeq` returns `just _` exactly when `q' ≤q q ≡ true`
--     (both directions).
--   * `GType ↔ Type` round-trip is injective.
--   * `isArithmeticOp` and `isComparisonOp` are mutually exclusive
--     and exhaustive.
------------------------------------------------------------------------

module Once.TypeCheck.Identities where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; _,_)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_)

open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer;
                             _*_; _+_; _⇒[_]_; Eff; μ-type; ν-type;
                             Quantity; Zero; One; Many; _≤q_)
open import Once.TypeCheck.Raw using (BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod;
                                       OpLt; OpLe; OpGt; OpGe; OpEq; OpNe;
                                       isArithmeticOp; isComparisonOp;
                                       RawExpr; RVar)
open import Once.TypeCheck.Elaborate
  using (decideLeq; classifyAppHead;
         PolyBuiltinApp; pba-id; pba-fst; pba-snd; pba-terminal;
         pba-inl; pba-inr; pba-initial)

------------------------------------------------------------------------
-- classifyAppHead determinism
------------------------------------------------------------------------

-- Calling the classifier twice on the same RawExpr gives the same
-- answer (trivially refl; stated for downstream use).
classifyAppHead-deterministic :
  ∀ (e : RawExpr) → classifyAppHead e ≡ classifyAppHead e
classifyAppHead-deterministic _ = refl

------------------------------------------------------------------------
-- decideLeq correctness: just/nothing iff Bool decision is true/false
------------------------------------------------------------------------

-- Forward: if the Bool decision is true, decideLeq returns `just refl`.
decideLeq-correct-true :
  ∀ (q' q : Quantity)
  → (q' ≤q q) ≡ true
  → ∃[ p ] decideLeq q' q ≡ just p
decideLeq-correct-true Zero Zero _ = refl , refl
decideLeq-correct-true Zero One  _ = refl , refl
decideLeq-correct-true Zero Many _ = refl , refl
decideLeq-correct-true One  One  _ = refl , refl
decideLeq-correct-true One  Many _ = refl , refl
decideLeq-correct-true Many Many _ = refl , refl
decideLeq-correct-true One  Zero ()
decideLeq-correct-true Many Zero ()
decideLeq-correct-true Many One  ()

-- Reverse: if decideLeq returns `just p`, the Bool decision is true.
decideLeq-correct-just :
  ∀ (q' q : Quantity) {p}
  → decideLeq q' q ≡ just p
  → (q' ≤q q) ≡ true
decideLeq-correct-just Zero Zero _ = refl
decideLeq-correct-just Zero One  _ = refl
decideLeq-correct-just Zero Many _ = refl
decideLeq-correct-just One  One  _ = refl
decideLeq-correct-just One  Many _ = refl
decideLeq-correct-just Many Many _ = refl
decideLeq-correct-just One  Zero ()
decideLeq-correct-just Many Zero ()
decideLeq-correct-just Many One  ()

-- Forward: Bool decision false → decideLeq returns nothing.
decideLeq-correct-false :
  ∀ (q' q : Quantity)
  → (q' ≤q q) ≡ false
  → decideLeq q' q ≡ nothing
decideLeq-correct-false Zero Zero ()
decideLeq-correct-false Zero One  ()
decideLeq-correct-false Zero Many ()
decideLeq-correct-false One  One  ()
decideLeq-correct-false One  Many ()
decideLeq-correct-false Many Many ()
decideLeq-correct-false One  Zero _ = refl
decideLeq-correct-false Many Zero _ = refl
decideLeq-correct-false Many One  _ = refl

-- Reverse: decideLeq nothing → decision false.
decideLeq-correct-nothing :
  ∀ (q' q : Quantity)
  → decideLeq q' q ≡ nothing
  → (q' ≤q q) ≡ false
decideLeq-correct-nothing One  Zero _ = refl
decideLeq-correct-nothing Many Zero _ = refl
decideLeq-correct-nothing Many One  _ = refl
decideLeq-correct-nothing Zero Zero ()
decideLeq-correct-nothing Zero One  ()
decideLeq-correct-nothing Zero Many ()
decideLeq-correct-nothing One  One  ()
decideLeq-correct-nothing One  Many ()
decideLeq-correct-nothing Many Many ()

------------------------------------------------------------------------
-- isArithmeticOp / isComparisonOp exhaustiveness
------------------------------------------------------------------------

-- Every BinOp is either arithmetic or comparison, never both.
binop-classification-exhaustive :
  ∀ (op : BinOp) → (isArithmeticOp op ≡ true) ⊎ (isComparisonOp op ≡ true)
binop-classification-exhaustive OpAdd = inj₁ refl
binop-classification-exhaustive OpSub = inj₁ refl
binop-classification-exhaustive OpMul = inj₁ refl
binop-classification-exhaustive OpDiv = inj₁ refl
binop-classification-exhaustive OpMod = inj₁ refl
binop-classification-exhaustive OpLt  = inj₂ refl
binop-classification-exhaustive OpLe  = inj₂ refl
binop-classification-exhaustive OpGt  = inj₂ refl
binop-classification-exhaustive OpGe  = inj₂ refl
binop-classification-exhaustive OpEq  = inj₂ refl
binop-classification-exhaustive OpNe  = inj₂ refl

-- Arithmetic and comparison are mutually exclusive.
binop-classification-exclusive :
  ∀ (op : BinOp)
  → isArithmeticOp op ≡ true
  → isComparisonOp op ≡ true
  → ⊥
binop-classification-exclusive OpAdd _ ()
binop-classification-exclusive OpSub _ ()
binop-classification-exclusive OpMul _ ()
binop-classification-exclusive OpDiv _ ()
binop-classification-exclusive OpMod _ ()
binop-classification-exclusive OpLt  () _
binop-classification-exclusive OpLe  () _
binop-classification-exclusive OpGt  () _
binop-classification-exclusive OpGe  () _
binop-classification-exclusive OpEq  () _
binop-classification-exclusive OpNe  () _

------------------------------------------------------------------------
-- `classifyAppHead`: structural identities on polymorphic-builtin names
------------------------------------------------------------------------

classifyAppHead-id :
  classifyAppHead (RVar "id") ≡ just pba-id
classifyAppHead-id = refl

classifyAppHead-fst :
  classifyAppHead (RVar "fst") ≡ just pba-fst
classifyAppHead-fst = refl

classifyAppHead-snd :
  classifyAppHead (RVar "snd") ≡ just pba-snd
classifyAppHead-snd = refl

classifyAppHead-terminal :
  classifyAppHead (RVar "terminal") ≡ just pba-terminal
classifyAppHead-terminal = refl

classifyAppHead-inl :
  classifyAppHead (RVar "inl") ≡ just pba-inl
classifyAppHead-inl = refl

classifyAppHead-inr :
  classifyAppHead (RVar "inr") ≡ just pba-inr
classifyAppHead-inr = refl

classifyAppHead-initial :
  classifyAppHead (RVar "initial") ≡ just pba-initial
classifyAppHead-initial = refl

------------------------------------------------------------------------
-- QTT quantity order: reflexivity and transitivity
------------------------------------------------------------------------

-- Reflexivity: q ≤q q always.
≤q-refl : ∀ (q : Quantity) → (q ≤q q) ≡ true
≤q-refl Zero = refl
≤q-refl One  = refl
≤q-refl Many = refl

-- Transitivity: chain of quantity ≤q relations.
≤q-trans : ∀ (q₁ q₂ q₃ : Quantity)
         → (q₁ ≤q q₂) ≡ true
         → (q₂ ≤q q₃) ≡ true
         → (q₁ ≤q q₃) ≡ true
-- q₁ = Zero: Zero ≤q anything is true definitionally.
≤q-trans Zero _    _    _  _  = refl
-- q₁ = One: q₂ must be One or Many (else first premise is false).
≤q-trans One  Zero _    () _
≤q-trans One  One  Zero _  ()
≤q-trans One  One  One  _  _  = refl
≤q-trans One  One  Many _  _  = refl
≤q-trans One  Many Zero _  ()
≤q-trans One  Many One  _  ()
≤q-trans One  Many Many _  _  = refl
-- q₁ = Many: q₂ must be Many.
≤q-trans Many Zero _    () _
≤q-trans Many One  _    () _
≤q-trans Many Many Zero _  ()
≤q-trans Many Many One  _  ()
≤q-trans Many Many Many _  _  = refl

-- Zero is the minimum.
Zero-≤q-all : ∀ (q : Quantity) → (Zero ≤q q) ≡ true
Zero-≤q-all _ = refl

-- Many is the maximum.
all-≤q-Many : ∀ (q : Quantity) → (q ≤q Many) ≡ true
all-≤q-Many Zero = refl
all-≤q-Many One  = refl
all-≤q-Many Many = refl

------------------------------------------------------------------------
-- Grammar round-trip injectivity corollaries
------------------------------------------------------------------------

open import Once.Grammar.Convert
  using (gtypeToType; typeToGType;
         typeToGType-gtypeToType; gtypeToType-typeToGType)
open import Once.Grammar using (GType)

-- typeToGType is injective on its domain (restricted to grammar-
-- expressible types): if two types map to the same GType, they're
-- equal.
typeToGType-injective :
  ∀ {t₁ t₂ : Type} {g : GType}
  → typeToGType t₁ ≡ just g
  → typeToGType t₂ ≡ just g
  → (gtypeToType g ≡ just t₁) × (gtypeToType g ≡ just t₂)
typeToGType-injective {t₁} {t₂} {g} eq₁ eq₂ =
  typeToGType-gtypeToType t₁ g eq₁ , typeToGType-gtypeToType t₂ g eq₂
