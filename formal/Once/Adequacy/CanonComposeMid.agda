-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonComposeMid — discharge of `composeMid-canon` (the lone
-- deferred hole of `CanonPreserveMutual`'s Step-2 m-compose case).
--
-- `composeMid ctx f g A = composeMid-pick (composeArgB ctx g A) (domainOfHead ctx f)`
-- is INVARIANT under `canonExpr` on the well-typed arms `f`/`g`: prove the two
-- component invariances by casing the `⊢ᵐ` derivations (each concrete head — the
-- canonExpr image keeps builtins by `canon-builtin`; a named ref's `RVar`/`RResolved`
-- forms coincide via `showCanonical (canonical [x]) = x`), then `composeMid-canon`
-- follows by rewriting both.
------------------------------------------------------------------------

module Once.Adequacy.CanonComposeMid where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type)
open import Once.CanonicalName using (canonical; showCanonical)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.Parser.Module.Resolve using (canonExpr; isBuiltinName; elemStr)
open import Once.TypeCheck.Classify
  using (NamedCtx; composeArgB; domainOfHead; composeMid; composeMid-pick)
open import Once.TypeCheck.Judgment
open import Once.Adequacy.CanonPreserve
  using (canon-builtin; canon-RVar-keep; canon-RVar-resolve)

------------------------------------------------------------------------
-- domainOfHead is canonExpr-invariant on a well-typed morphism head.
-- (domainOfHead's RVar clause is GENERAL — no literal patterns — so the named
-- case is just the showCanonical coincidence.)
------------------------------------------------------------------------

domainOfHead-canon : ∀ {ctx f A π B} (bound : List String)
  → ctx ⊢ᵐ f ∶ A ⇨[ π ] B
  → domainOfHead ctx (canonExpr bound [] [] f) ≡ domainOfHead ctx f
domainOfHead-canon bound (m-id _ _)       rewrite canon-builtin bound "id" refl = refl
domainOfHead-canon bound (m-fst _ _)      rewrite canon-builtin bound "fst" refl = refl
domainOfHead-canon bound (m-snd _ _)      rewrite canon-builtin bound "snd" refl = refl
domainOfHead-canon bound (m-terminal _ _) rewrite canon-builtin bound "terminal" refl = refl
domainOfHead-canon bound (m-initial _ _)  rewrite canon-builtin bound "initial" refl = refl
domainOfHead-canon bound (m-inl _ _)      rewrite canon-builtin bound "inl" refl = refl
domainOfHead-canon bound (m-inr _ _)      rewrite canon-builtin bound "inr" refl = refl
domainOfHead-canon bound (m-compose _ _ _) rewrite canon-builtin bound "compose" refl = refl
domainOfHead-canon bound (m-case _ _)     rewrite canon-builtin bound "case" refl = refl
domainOfHead-canon bound (m-pair _ _)     rewrite canon-builtin bound "pair" refl = refl
domainOfHead-canon bound (m-curry _)      rewrite canon-builtin bound "curry" refl = refl
domainOfHead-canon bound (m-cata _ _)     rewrite canon-builtin bound "cata" refl = refl
domainOfHead-canon bound (m-const (g-int n))      = refl
domainOfHead-canon bound (m-const (g-float i f l p)) = refl
domainOfHead-canon bound (m-const (g-terminal _ _)) rewrite canon-builtin bound "terminal" refl = refl
domainOfHead-canon bound (m-const (g-pair _ _))   = refl
domainOfHead-canon bound (m-const (g-inl _))      rewrite canon-builtin bound "inl" refl = refl
domainOfHead-canon bound (m-const (g-inr _))      rewrite canon-builtin bound "inr" refl = refl
domainOfHead-canon bound (m-const (g-In _ _))     rewrite canon-builtin bound "In" refl = refl
domainOfHead-canon bound (m-named {x = x} _ _ _ _ _)
  with elemStr x bound ∨ isBuiltinName x in eb
... | true  rewrite canon-RVar-keep    bound x eb = refl
... | false rewrite canon-RVar-resolve bound x eb = refl
domainOfHead-canon bound (m-named-resolved _ _ _) = refl

------------------------------------------------------------------------
-- composeArgB is canonExpr-invariant on a well-typed morphism arm.
------------------------------------------------------------------------

-- For a NON-builtin name, the resolver's `RVar x → RResolved (canonical [x])`
-- leaves `composeArgB` unchanged: both reduce to `composeArgB-lookup ctx x A` —
-- the RResolved clause directly (`showCanonical (canonical [x]) = x`), the RVar one
-- after the `≟`-dispatch skips fst/snd/id/terminal (ruled out by `isBuiltinName`).
t≢f : true ≡ false → ⊥
t≢f ()

composeArgB-RVar-resolved :
  ∀ (ctx : NamedCtx) (y : String) (A : Type) → isBuiltinName y ≡ false
  → composeArgB ctx (Raw.RResolved (canonical (y ∷ []))) A ≡ composeArgB ctx (Raw.RVar y) A
composeArgB-RVar-resolved ctx y A nb with y ≟s "fst"
... | yes refl = ⊥-elim (t≢f nb)
... | no _ with y ≟s "snd"
...   | yes refl = ⊥-elim (t≢f nb)
...   | no _ with y ≟s "id"
...     | yes refl = ⊥-elim (t≢f nb)
...     | no _ with y ≟s "terminal"
...       | yes refl = ⊥-elim (t≢f nb)
...       | no _ = refl

composeArgB-canon : ∀ {ctx g A′ π B′} (bound : List String) (A : Type)
  → ctx ⊢ᵐ g ∶ A′ ⇨[ π ] B′
  → composeArgB ctx (canonExpr bound [] [] g) A ≡ composeArgB ctx g A
composeArgB-canon bound A (m-id _ _)       rewrite canon-builtin bound "id" refl = refl
composeArgB-canon bound A (m-fst _ _)      rewrite canon-builtin bound "fst" refl = refl
composeArgB-canon bound A (m-snd _ _)      rewrite canon-builtin bound "snd" refl = refl
composeArgB-canon bound A (m-terminal _ _) rewrite canon-builtin bound "terminal" refl = refl
composeArgB-canon bound A (m-initial _ _)  rewrite canon-builtin bound "initial" refl = refl
composeArgB-canon bound A (m-inl _ _)      rewrite canon-builtin bound "inl" refl = refl
composeArgB-canon bound A (m-inr _ _)      rewrite canon-builtin bound "inr" refl = refl
composeArgB-canon bound A (m-case _ _)     rewrite canon-builtin bound "case" refl = refl
composeArgB-canon bound A (m-pair _ _)     rewrite canon-builtin bound "pair" refl = refl
composeArgB-canon bound A (m-curry _)      rewrite canon-builtin bound "curry" refl = refl
composeArgB-canon bound A (m-cata _ _)     rewrite canon-builtin bound "cata" refl = refl
composeArgB-canon {ctx} bound A (m-compose {f = f} {g = g} _ df dg)
  rewrite canon-builtin bound "compose" refl
  rewrite composeArgB-canon bound A dg
  with composeArgB ctx g A
... | nothing = refl
... | just B′ rewrite composeArgB-canon bound B′ df = refl
composeArgB-canon bound A (m-const (g-int n))       = refl
composeArgB-canon bound A (m-const (g-float i f l p)) = refl
composeArgB-canon bound A (m-const (g-terminal _ _)) rewrite canon-builtin bound "terminal" refl = refl
composeArgB-canon bound A (m-const (g-pair _ _))    = refl
composeArgB-canon bound A (m-const (g-inl _))       rewrite canon-builtin bound "inl" refl = refl
composeArgB-canon bound A (m-const (g-inr _))       rewrite canon-builtin bound "inr" refl = refl
composeArgB-canon bound A (m-const (g-In _ _))      rewrite canon-builtin bound "In" refl = refl
composeArgB-canon {ctx = ctx} bound A (m-named {x = x} _ _ _ _ _)
  with elemStr x bound ∨ isBuiltinName x in eb
... | true  rewrite canon-RVar-keep    bound x eb = refl
... | false rewrite canon-RVar-resolve bound x eb =
      composeArgB-RVar-resolved ctx x A (∨-false-r eb)
  where ∨-false-r : ∀ {a} → (a ∨ isBuiltinName x) ≡ false → isBuiltinName x ≡ false
        ∨-false-r {false} e = e
        ∨-false-r {true}  ()
composeArgB-canon bound A (m-named-resolved _ _ _) = refl

------------------------------------------------------------------------
-- composeMid-canon: both components are canonExpr-invariant.
------------------------------------------------------------------------

composeMid-canon :
  ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type} {π} (bound : List String)
  → ctx ⊢ᵐ f ∶ B ⇨[ π ] C
  → ctx ⊢ᵐ g ∶ A ⇨[ π ] B
  → composeMid ctx f g A ≡ just B
  → composeMid ctx (canonExpr bound [] [] f) (canonExpr bound [] [] g) A ≡ just B
composeMid-canon {A = A} bound df dg eq
  rewrite composeArgB-canon bound A dg
  rewrite domainOfHead-canon bound df = eq
