-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
--   * `decideLeq` returns `just _` exactly when `q' ≤qᵇ q ≡ true`
--     (both directions).
--   * `GType ↔ Type` round-trip is injective.
--   * `isArithmeticOp` and `isComparisonOp` are mutually exclusive
--     and exhaustive.
------------------------------------------------------------------------

open import Once.Spec.Type using (Ty)
open import Once.Type.Grade using (_≤qᵇ_)
module Once.TypeCheck.Identities where

import Once.Internal.Laws.Grade as G
import Once.Surface.Properties as P
import Relation.Binary.PropositionalEquality as Eq

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃-syntax; _,_)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Grade using (Quantity; Zero; One; Many)
open import Once.Spec.Type using (Type)
open import Once.Internal.Syntax using (BinOp; OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe; isArithmeticOp; isComparisonOp; RawExpr; RResolved)
open import Once.Spec.Name using (gen)
open import Once.TypeCheck.Elaborate
  using (decideLeq)
open import Once.Internal.Typing.Scope using (classifyAppHead; pba-id; pba-fst; pba-snd; pba-terminal; pba-inl; pba-inr; pba-initial; NamedCtx; extendNamedCtx)
import Once.Internal.Typing.Scope as Classify

------------------------------------------------------------------------
-- classifyAppHead determinism
------------------------------------------------------------------------

-- Calling the classifier twice on the same RawExpr gives the same
-- answer (trivially refl; stated for downstream use).
classifyAppHead-deterministic : ∀ (e : RawExpr) → classifyAppHead e ≡ classifyAppHead e
classifyAppHead-deterministic _ = refl

------------------------------------------------------------------------
-- decideLeq correctness: just/nothing iff Bool decision is true/false
------------------------------------------------------------------------

-- Forward: if the Bool decision is true, decideLeq returns `just refl`.
decideLeq-correct-true : ∀ (q' q : Quantity)
  → (q' ≤qᵇ q) ≡ true
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
decideLeq-correct-just : ∀ (q' q : Quantity) {p}
  → decideLeq q' q ≡ just p
  → (q' ≤qᵇ q) ≡ true
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
decideLeq-correct-false : ∀ (q' q : Quantity)
  → (q' ≤qᵇ q) ≡ false
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
decideLeq-correct-nothing : ∀ (q' q : Quantity)
  → decideLeq q' q ≡ nothing
  → (q' ≤qᵇ q) ≡ false
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
binop-classification-exhaustive : ∀ (op : BinOp) → (isArithmeticOp op ≡ true) ⊎ (isComparisonOp op ≡ true)
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
binop-classification-exclusive : ∀ (op : BinOp)
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
-- `classifyAppHead`: structural identities on the GENERATORS (D136: a
-- generator is a canonical name, never a bare one)
------------------------------------------------------------------------

classifyAppHead-id :
  classifyAppHead (RResolved (gen "id")) ≡ just pba-id
classifyAppHead-id = refl

classifyAppHead-fst :
  classifyAppHead (RResolved (gen "fst")) ≡ just pba-fst
classifyAppHead-fst = refl

classifyAppHead-snd :
  classifyAppHead (RResolved (gen "snd")) ≡ just pba-snd
classifyAppHead-snd = refl

classifyAppHead-terminal :
  classifyAppHead (RResolved (gen "terminal")) ≡ just pba-terminal
classifyAppHead-terminal = refl

classifyAppHead-inl :
  classifyAppHead (RResolved (gen "inl")) ≡ just pba-inl
classifyAppHead-inl = refl

classifyAppHead-inr :
  classifyAppHead (RResolved (gen "inr")) ≡ just pba-inr
classifyAppHead-inr = refl

classifyAppHead-initial :
  classifyAppHead (RResolved (gen "initial")) ≡ just pba-initial
classifyAppHead-initial = refl

------------------------------------------------------------------------
-- QTT quantity order: reflexivity and transitivity
------------------------------------------------------------------------

-- Reflexivity: q ≤qᵇ q always.
≤q-refl : ∀ (q : Quantity) → (q ≤qᵇ q) ≡ true
≤q-refl Zero = refl
≤q-refl One  = refl
≤q-refl Many = refl

-- Transitivity: chain of quantity ≤qᵇ relations.
≤q-trans : ∀ (q₁ q₂ q₃ : Quantity)
         → (q₁ ≤qᵇ q₂) ≡ true
         → (q₂ ≤qᵇ q₃) ≡ true
         → (q₁ ≤qᵇ q₃) ≡ true
-- q₁ = Zero: Zero ≤qᵇ anything is true definitionally.
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
Zero-≤q-all : ∀ (q : Quantity) → (Zero ≤qᵇ q) ≡ true
Zero-≤q-all _ = refl

-- Many is the maximum.
all-≤q-Many : ∀ (q : Quantity) → (q ≤qᵇ Many) ≡ true
all-≤q-Many Zero = refl
all-≤q-Many One  = refl
all-≤q-Many Many = refl

------------------------------------------------------------------------
-- Grammar round-trip injectivity corollaries
------------------------------------------------------------------------

open import Once.Grammar.Convert
  using (gtypeToType; typeToGType; typeToGType-gtypeToType)
open import Once.Grammar using (GType)

-- typeToGType is injective on its domain (restricted to grammar-
-- expressible types): if two types map to the same GType, they're
-- equal.
typeToGType-injective : ∀ {m} {t₁ t₂ : Ty m} {g : GType}
  → typeToGType t₁ ≡ just g
  → typeToGType t₂ ≡ just g
  → (gtypeToType g ≡ just t₁) × (gtypeToType g ≡ just t₂)
typeToGType-injective {t₁ = t₁} {t₂ = t₂} {g = g} eq₁ eq₂ =
  typeToGType-gtypeToType t₁ g eq₁ , typeToGType-gtypeToType t₂ g eq₂

------------------------------------------------------------------------
-- QTT quantity algebra: commutativity, associativity, identity
------------------------------------------------------------------------

open import Once.Spec.Grade using (_+q_; _*q_)
open import Once.Type.Grade using (_⊔q_)

-- Quantity addition is commutative.
+q-comm : ∀ (q₁ q₂ : Quantity) → q₁ +q q₂ ≡ q₂ +q q₁
+q-comm = G.+q-comm

-- Zero is the left identity of +q.
+q-identity-left : ∀ (q : Quantity) → Zero +q q ≡ q
+q-identity-left = G.+q-identityˡ

-- Zero is also the right identity (by commutativity).
+q-identity-right : ∀ (q : Quantity) → q +q Zero ≡ q
+q-identity-right = G.+q-identityʳ

-- Many is absorbing for +q.
+q-absorbs-Many-left : ∀ (q : Quantity) → Many +q q ≡ Many
+q-absorbs-Many-left Zero = refl
+q-absorbs-Many-left One  = refl
+q-absorbs-Many-left Many = refl

+q-absorbs-Many-right : ∀ (q : Quantity) → q +q Many ≡ Many
+q-absorbs-Many-right Zero = refl
+q-absorbs-Many-right One  = refl
+q-absorbs-Many-right Many = refl

-- Quantity multiplication: Zero is absorbing.
*q-absorbs-Zero-left : ∀ (q : Quantity) → Zero *q q ≡ Zero
*q-absorbs-Zero-left = G.*q-zeroˡ

*q-absorbs-Zero-right : ∀ (q : Quantity) → q *q Zero ≡ Zero
*q-absorbs-Zero-right = G.*q-zeroʳ

-- One is the identity for *q.
*q-identity-left : ∀ (q : Quantity) → One *q q ≡ q
*q-identity-left = G.*q-identityˡ

*q-identity-right : ∀ (q : Quantity) → q *q One ≡ q
*q-identity-right = G.*q-identityʳ

-- Quantity join (⊔q) is commutative.
⊔q-comm : ∀ (q₁ q₂ : Quantity) → q₁ ⊔q q₂ ≡ q₂ ⊔q q₁
⊔q-comm = G.⊔q-comm

-- ⊔q is idempotent.
⊔q-idem : ∀ (q : Quantity) → q ⊔q q ≡ q
⊔q-idem = G.⊔q-idem

-- Zero is the bottom of ⊔q.
⊔q-Zero-left : ∀ (q : Quantity) → Zero ⊔q q ≡ q
⊔q-Zero-left _ = refl

⊔q-Zero-right : ∀ (q : Quantity) → q ⊔q Zero ≡ q
⊔q-Zero-right Zero = refl
⊔q-Zero-right One  = refl
⊔q-Zero-right Many = refl

-- Many is the top of ⊔q.
⊔q-Many-left : ∀ (q : Quantity) → Many ⊔q q ≡ Many
⊔q-Many-left Zero = refl
⊔q-Many-left One  = refl
⊔q-Many-left Many = refl

⊔q-Many-right : ∀ (q : Quantity) → q ⊔q Many ≡ Many
⊔q-Many-right Zero = refl
⊔q-Many-right One  = refl
⊔q-Many-right Many = refl

-- Associativity of +q. Zero absorbs on the left side; Many absorbs
-- completely; the interesting cases are One × One × {Zero, One, Many}.
+q-assoc : ∀ (q₁ q₂ q₃ : Quantity) → q₁ +q (q₂ +q q₃) ≡ (q₁ +q q₂) +q q₃
+q-assoc q₁ q₂ q₃ = Eq.sym (G.+q-assoc q₁ q₂ q₃)

-- Associativity of *q. The clauses of `_*q_` overlap for concrete
-- arguments, so we enumerate all 27 cases to force reduction.
*q-assoc : ∀ (q₁ q₂ q₃ : Quantity) → q₁ *q (q₂ *q q₃) ≡ (q₁ *q q₂) *q q₃
*q-assoc q₁ q₂ q₃ = Eq.sym (G.*q-assoc q₁ q₂ q₃)

-- Associativity of ⊔q.
⊔q-assoc : ∀ (q₁ q₂ q₃ : Quantity) → q₁ ⊔q (q₂ ⊔q q₃) ≡ (q₁ ⊔q q₂) ⊔q q₃
⊔q-assoc q₁ q₂ q₃ = Eq.sym (G.⊔q-assoc q₁ q₂ q₃)

-- Left-distributivity: q₁ *q (q₂ +q q₃) ≡ (q₁ *q q₂) +q (q₁ *q q₃).
*q-distrib-+q-left : ∀ (q₁ q₂ q₃ : Quantity) → q₁ *q (q₂ +q q₃) ≡ (q₁ *q q₂) +q (q₁ *q q₃)
*q-distrib-+q-left Zero _    _    = refl
*q-distrib-+q-left One  Zero Zero = refl
*q-distrib-+q-left One  Zero One  = refl
*q-distrib-+q-left One  Zero Many = refl
*q-distrib-+q-left One  One  Zero = refl
*q-distrib-+q-left One  One  One  = refl
*q-distrib-+q-left One  One  Many = refl
*q-distrib-+q-left One  Many Zero = refl
*q-distrib-+q-left One  Many One  = refl
*q-distrib-+q-left One  Many Many = refl
*q-distrib-+q-left Many Zero Zero = refl
*q-distrib-+q-left Many Zero One  = refl
*q-distrib-+q-left Many Zero Many = refl
*q-distrib-+q-left Many One  Zero = refl
*q-distrib-+q-left Many One  One  = refl
*q-distrib-+q-left Many One  Many = refl
*q-distrib-+q-left Many Many Zero = refl
*q-distrib-+q-left Many Many One  = refl
*q-distrib-+q-left Many Many Many = refl

------------------------------------------------------------------------
-- Usage-vector identities (per-position lifts of quantity laws)
------------------------------------------------------------------------

open import Data.Nat using (zero; suc)
open import Once.Internal.Context using (Usage; zeroUsage; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)
open Once.Internal.Context.Usage using () renaming (_∷_ to _∷ᵘ_; [] to []ᵘ)

-- Note: Once.Internal.Context.Usage is an indexed vector of Quantity.
-- Pattern matching exposes its per-position structure; the identities
-- lift the quantity identities pointwise.

-- +ᵘ is commutative.
+ᵘ-comm : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₁ +ᵘ Ψ₂ ≡ Ψ₂ +ᵘ Ψ₁
+ᵘ-comm = P.+ᵘ-comm

-- zeroUsage is the identity of +ᵘ on both sides.
+ᵘ-identity-left : ∀ {n} (Ψ : Usage n) → zeroUsage +ᵘ Ψ ≡ Ψ
+ᵘ-identity-left = P.+ᵘ-identityˡ

+ᵘ-identity-right : ∀ {n} (Ψ : Usage n) → Ψ +ᵘ zeroUsage ≡ Ψ
+ᵘ-identity-right = P.+ᵘ-identityʳ

-- ⊔ᵘ is commutative.
⊔ᵘ-comm : ∀ {n} (Ψ₁ Ψ₂ : Usage n) → Ψ₁ ⊔ᵘ Ψ₂ ≡ Ψ₂ ⊔ᵘ Ψ₁
⊔ᵘ-comm {zero}  []ᵘ []ᵘ = refl
⊔ᵘ-comm {suc n} (q₁ ∷ᵘ Ψ₁) (q₂ ∷ᵘ Ψ₂)
  rewrite ⊔q-comm q₁ q₂ | ⊔ᵘ-comm Ψ₁ Ψ₂ = refl

-- ⊔ᵘ is idempotent.
⊔ᵘ-idem : ∀ {n} (Ψ : Usage n) → Ψ ⊔ᵘ Ψ ≡ Ψ
⊔ᵘ-idem {zero}  []ᵘ = refl
⊔ᵘ-idem {suc n} (q ∷ᵘ Ψ) rewrite ⊔q-idem q | ⊔ᵘ-idem Ψ = refl

-- zeroUsage is bottom of ⊔ᵘ.
⊔ᵘ-zero-left : ∀ {n} (Ψ : Usage n) → zeroUsage ⊔ᵘ Ψ ≡ Ψ
⊔ᵘ-zero-left {zero}  []ᵘ = refl
⊔ᵘ-zero-left {suc n} (q ∷ᵘ Ψ) rewrite ⊔ᵘ-zero-left Ψ = refl

⊔ᵘ-zero-right : ∀ {n} (Ψ : Usage n) → Ψ ⊔ᵘ zeroUsage ≡ Ψ
⊔ᵘ-zero-right {zero}  []ᵘ = refl
⊔ᵘ-zero-right {suc n} (q ∷ᵘ Ψ)
  rewrite ⊔q-Zero-right q | ⊔ᵘ-zero-right Ψ = refl

-- +ᵘ associativity.
+ᵘ-assoc : ∀ {n} (Ψ₁ Ψ₂ Ψ₃ : Usage n) → Ψ₁ +ᵘ (Ψ₂ +ᵘ Ψ₃) ≡ (Ψ₁ +ᵘ Ψ₂) +ᵘ Ψ₃
+ᵘ-assoc Ψ₁ Ψ₂ Ψ₃ = Eq.sym (P.+ᵘ-assoc Ψ₁ Ψ₂ Ψ₃)

-- ⊔ᵘ associativity.
⊔ᵘ-assoc : ∀ {n} (Ψ₁ Ψ₂ Ψ₃ : Usage n) → Ψ₁ ⊔ᵘ (Ψ₂ ⊔ᵘ Ψ₃) ≡ (Ψ₁ ⊔ᵘ Ψ₂) ⊔ᵘ Ψ₃
⊔ᵘ-assoc {zero}  []ᵘ []ᵘ []ᵘ = refl
⊔ᵘ-assoc {suc n} (q₁ ∷ᵘ Ψ₁) (q₂ ∷ᵘ Ψ₂) (q₃ ∷ᵘ Ψ₃)
  rewrite ⊔q-assoc q₁ q₂ q₃ | ⊔ᵘ-assoc Ψ₁ Ψ₂ Ψ₃ = refl

-- *ᵘ identity: multiplying by `One` acts as an identity scalar.
*ᵘ-identity-One : ∀ {n} (Ψ : Usage n) → One *ᵘ Ψ ≡ Ψ
*ᵘ-identity-One = P.*ᵘ-identityˡ

-- *ᵘ absorbs zero scalar.
*ᵘ-Zero : ∀ {n} (Ψ : Usage n) → Zero *ᵘ Ψ ≡ zeroUsage
*ᵘ-Zero = P.*ᵘ-zeroˡ

------------------------------------------------------------------------
-- ≤qᵇ monotonicity w.r.t. quantity operators
------------------------------------------------------------------------

-- If q₁ ≤qᵇ q₂ and q₃ ≤qᵇ q₄, then q₁ +q q₃ ≤qᵇ q₂ +q q₄.
+q-mono : ∀ (q₁ q₂ q₃ q₄ : Quantity)
        → (q₁ ≤qᵇ q₂) ≡ true
        → (q₃ ≤qᵇ q₄) ≡ true
        → (q₁ +q q₃ ≤qᵇ q₂ +q q₄) ≡ true
+q-mono Zero Zero Zero Zero _ _ = refl
+q-mono Zero Zero Zero One  _ _ = refl
+q-mono Zero Zero Zero Many _ _ = refl
+q-mono Zero Zero One  One  _ _ = refl
+q-mono Zero Zero One  Many _ _ = refl
+q-mono Zero Zero Many Many _ _ = refl
+q-mono Zero One  Zero Zero _ _ = refl
+q-mono Zero One  Zero One  _ _ = refl
+q-mono Zero One  Zero Many _ _ = refl
+q-mono Zero One  One  One  _ _ = refl
+q-mono Zero One  One  Many _ _ = refl
+q-mono Zero One  Many Many _ _ = refl
+q-mono Zero Many Zero Zero _ _ = refl
+q-mono Zero Many Zero One  _ _ = refl
+q-mono Zero Many Zero Many _ _ = refl
+q-mono Zero Many One  One  _ _ = refl
+q-mono Zero Many One  Many _ _ = refl
+q-mono Zero Many Many Many _ _ = refl
+q-mono One  One  Zero Zero _ _ = refl
+q-mono One  One  Zero One  _ _ = refl
+q-mono One  One  Zero Many _ _ = refl
+q-mono One  One  One  One  _ _ = refl
+q-mono One  One  One  Many _ _ = refl
+q-mono One  One  Many Many _ _ = refl
+q-mono One  Many Zero Zero _ _ = refl
+q-mono One  Many Zero One  _ _ = refl
+q-mono One  Many Zero Many _ _ = refl
+q-mono One  Many One  One  _ _ = refl
+q-mono One  Many One  Many _ _ = refl
+q-mono One  Many Many Many _ _ = refl
+q-mono Many Many Zero Zero _ _ = refl
+q-mono Many Many Zero One  _ _ = refl
+q-mono Many Many Zero Many _ _ = refl
+q-mono Many Many One  One  _ _ = refl
+q-mono Many Many One  Many _ _ = refl
+q-mono Many Many Many Many _ _ = refl
-- absurd cases from false premises:
+q-mono One  Zero _    _    () _
+q-mono Many Zero _    _    () _
+q-mono Many One  _    _    () _
+q-mono _    _    One  Zero _ ()
+q-mono _    _    Many Zero _ ()
+q-mono _    _    Many One  _ ()

------------------------------------------------------------------------
-- Named-context structure identities
------------------------------------------------------------------------

-- `extendNamedCtx` grows the context's size by exactly one.
open Once.TypeCheck.Elaborate using ()

extendNamedCtx-size : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m)
  → Classify.NamedCtx.size (extendNamedCtx ctx x T) ≡ suc (Classify.NamedCtx.size ctx)
extendNamedCtx-size _ _ _ = refl

-- `extendNamedCtx` preserves the imports.
extendNamedCtx-imports : ∀ {m} (ctx : NamedCtx m) (x : String) (T : Ty m)
  → Classify.NamedCtx.imports (extendNamedCtx ctx x T) ≡ Classify.NamedCtx.imports ctx
extendNamedCtx-imports _ _ _ = refl
