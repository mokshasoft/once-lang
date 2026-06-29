-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CanonReflectMutual — Plan 0.51 REVERSE preservation.
--
-- The mirror of `CanonPreserveMutual`: the resolver's own-module
-- canonicalization `canonExpr bound [] []` REFLECTS the three mutual declarative
-- judgments `⊢ᵢ`/`⊢ᵐ`/`⊢ᶜ` (plus the value family `⊢ᵍ`). Given a derivation over
-- the CANONICALIZED expression, it reconstructs a derivation over the SOURCE.
--
-- Architecture (the two facts that make it type- AND termination-check):
--   * INDUCT ON `e` (the RawExpr), not on the derivation: `canonExpr e` only
--     reduces once `e`'s head constructor is exposed, so we case `e` first; THEN
--     the derivation's index is in constructor form and becomes case-able.
--   * The RVar/head dispatch (`canonVar b …`) is reduced by making the boolean
--     `b = elemStr x bound ∨ isBuiltinName x` an EXPLICIT PATTERN argument of the
--     `reflect-*var*` helpers — so `canonVar true/false` computes. Derivations are
--     passed through by DEFINITIONAL equality (never `subst`-coerced), keeping the
--     structural descent that the termination checker needs.
--
-- Crux case (`e = RVar x`, resolved branch `b = false`): `canonVar false … x =
-- RResolved (canonical [x])`, so the only `⊢ᵢ` rule is `t-var-resolved imp` with
-- `imp : lookupImport … (showCanonical (canonical [x])) ≡ just T`. Since
-- `showCanonical (canonical [x]) = x` DEFINITIONALLY, `imp : lookupImport … x ≡
-- just T`, and we rebuild `t-var-import ¬unit lkn imp`, recovering `¬unit` from
-- `isBuiltinName "unit" = true` and `lkn` from `Names⊆ + elemStr x bound = false`.
------------------------------------------------------------------------

module Once.Adequacy.CanonReflectMutual where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.String using (String) renaming (_≟_ to _≟s_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Type)
open import Once.CanonicalName using (CanonicalName; canonical; showCanonical)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.Parser.Module.Resolve
  using (canonExpr; canonVar; isBuiltinName; elemStr; lookupUnaliased)
open import Once.TypeCheck.Classify
  using (NamedCtx; lookupLocal; classifyAppHead; composeMid; composeArgB;
         domainOfHead; ctxWithImportsAndPolys)
open import Once.TypeCheck.Context using (names)
open import Once.TypeCheck.Judgment
open import Once.Adequacy.CanonPreserve
  using (lookup-just→elem; canon-RVar-keep; canon-RVar-resolve; _⊆ᵇ_; ⊆ᵇ-cons; ⊆ᵇ-nil)

------------------------------------------------------------------------
-- Boolean / bookkeeping lemmas.
------------------------------------------------------------------------

t≢f : true ≡ false → ⊥
t≢f ()

∨-false-l : ∀ {a b : Bool} → (a ∨ b) ≡ false → a ≡ false
∨-false-l {false} _  = refl
∨-false-l {true}  ()

∨-false-r : ∀ {a b : Bool} → (a ∨ b) ≡ false → b ≡ false
∨-false-r {false} e = e
∨-false-r {true}  ()

-- `bound` covers the context's locals (reuse the forward invariant).
Names⊆ : NamedCtx → List String → Set
Names⊆ ctx bound = names (NamedCtx.named ctx) ⊆ᵇ bound

-- A name NOT in `bound` is not a local (contrapositive of `lookup-just→elem`).
not-local : ∀ {ctx : NamedCtx} {x : String} {bound : List String}
          → Names⊆ ctx bound → elemStr x bound ≡ false → lookupLocal ctx x ≡ nothing
not-local {ctx} {x} sub ef with lookupLocal ctx x in eq
... | nothing = refl
... | just r  = ⊥-elim (t≢f (trans (sym (sub x (lookup-just→elem ctx x eq))) ef))

-- A resolved (`b = false`) name is not the unit builtin.
¬unit-from-false : ∀ {x : String} {bound : List String}
                 → (elemStr x bound ∨ isBuiltinName x) ≡ false → ¬ (x ≡ "unit")
¬unit-from-false ef refl = t≢f (∨-false-r ef)

------------------------------------------------------------------------
-- `classifyAppHead` reflects `nothing` through `canonExpr` (the reverse of
-- `CanonPreserve.classify-canon`). Only the applied-RVar head is non-trivial.
------------------------------------------------------------------------

-- A non-builtin applied head never classifies (mirror of the `pair`/`compose`/
-- `case` dispatch inside `classifyAppHead (RApp (RVar z) _)`).
classifyRVar-applied-nonbuiltin : ∀ (z : String) (g : RawExpr)
  → isBuiltinName z ≡ false → classifyAppHead (Raw.RApp (Raw.RVar z) g) ≡ nothing
classifyRVar-applied-nonbuiltin z g nb with z ≟s "pair"
... | yes refl = ⊥-elim (t≢f nb)
... | no _ with z ≟s "compose"
...   | yes refl = ⊥-elim (t≢f nb)
...   | no _ with z ≟s "case"
...     | yes refl = ⊥-elim (t≢f nb)
...     | no _ = refl

-- A non-builtin bare head never classifies (mirror of the 12-name dispatch
-- inside `classifyAppHead (RVar x)`).
classifyRVar-nonbuiltin : ∀ (x : String)
  → isBuiltinName x ≡ false → classifyAppHead (Raw.RVar x) ≡ nothing
classifyRVar-nonbuiltin x nb with x ≟s "id"
... | yes refl = ⊥-elim (t≢f nb)
... | no _ with x ≟s "fst"
...   | yes refl = ⊥-elim (t≢f nb)
...   | no _ with x ≟s "snd"
...     | yes refl = ⊥-elim (t≢f nb)
...     | no _ with x ≟s "terminal"
...       | yes refl = ⊥-elim (t≢f nb)
...       | no _ with x ≟s "inl"
...         | yes refl = ⊥-elim (t≢f nb)
...         | no _ with x ≟s "inr"
...           | yes refl = ⊥-elim (t≢f nb)
...           | no _ with x ≟s "initial"
...             | yes refl = ⊥-elim (t≢f nb)
...             | no _ with x ≟s "arr"
...               | yes refl = ⊥-elim (t≢f nb)
...               | no _ with x ≟s "curry"
...                 | yes refl = ⊥-elim (t≢f nb)
...                 | no _ with x ≟s "apply"
...                   | yes refl = ⊥-elim (t≢f nb)
...                   | no _ with x ≟s "In"
...                     | yes refl = ⊥-elim (t≢f nb)
...                     | no _ with x ≟s "cata"
...                       | yes refl = ⊥-elim (t≢f nb)
...                       | no _ = refl

-- Applied-RVar head dispatch with the boolean as an explicit pattern (so
-- `canonVar` computes and the hypothesis is in reduced form).
classify-decanon-rvar : ∀ (b : Bool) (bound : List String) (z : String) (g : RawExpr)
  → (elemStr z bound ∨ isBuiltinName z) ≡ b
  → classifyAppHead (Raw.RApp (canonVar b nothing z) g) ≡ nothing
  → classifyAppHead (Raw.RApp (Raw.RVar z) g) ≡ nothing
classify-decanon-rvar true  bound z g eb h = h
classify-decanon-rvar false bound z g eb h = classifyRVar-applied-nonbuiltin z g (∨-false-r eb)

-- The bare-RVar analogue (never reached on the apex path, but needed for
-- totality of `classify-decanon`).
classify-decanon-bare-rvar : ∀ (b : Bool) (bound : List String) (x : String)
  → (elemStr x bound ∨ isBuiltinName x) ≡ b
  → classifyAppHead (canonVar b nothing x) ≡ nothing
  → classifyAppHead (Raw.RVar x) ≡ nothing
classify-decanon-bare-rvar true  bound x eb h = h
classify-decanon-bare-rvar false bound x eb h = classifyRVar-nonbuiltin x (∨-false-r eb)

classify-decanon : ∀ (bound : List String) (f : RawExpr)
  → classifyAppHead (canonExpr bound [] [] f) ≡ nothing → classifyAppHead f ≡ nothing
-- Applied-RVar head: the only non-refl case.
classify-decanon bound (Raw.RApp (Raw.RVar z) g) h =
  classify-decanon-rvar (elemStr z bound ∨ isBuiltinName z) bound z
    (canonExpr bound [] [] g) refl h
-- Every other head: `classifyAppHead f` is `nothing` definitionally.
classify-decanon bound (Raw.RApp (Raw.RApp a b) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RQualified n al) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RResolved cn) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RLam y b) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RLet y e₁ e₂) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RPair a b) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RDestruct s xl el xr er) g) h = refl
classify-decanon bound (Raw.RApp Raw.RUnit g) h = refl
classify-decanon bound (Raw.RApp (Raw.RInt n) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RStringLit s) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RAnnot e t) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RBinOp op a b) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RUnaryOp op e) g) h = refl
classify-decanon bound (Raw.RApp (Raw.RAna F c) g) h = refl
classify-decanon bound (Raw.RVar x) h =
  classify-decanon-bare-rvar (elemStr x bound ∨ isBuiltinName x) bound x refl h
classify-decanon bound (Raw.RQualified n al) h = refl
classify-decanon bound (Raw.RResolved cn) h = refl
classify-decanon bound (Raw.RLam y b) h = refl
classify-decanon bound (Raw.RLet y e₁ e₂) h = refl
classify-decanon bound (Raw.RPair a b) h = refl
classify-decanon bound (Raw.RDestruct s xl el xr er) h = refl
classify-decanon bound Raw.RUnit h = refl
classify-decanon bound (Raw.RInt n) h = refl
classify-decanon bound (Raw.RStringLit s) h = refl
classify-decanon bound (Raw.RAnnot e t) h = refl
classify-decanon bound (Raw.RBinOp op a b) h = refl
classify-decanon bound (Raw.RUnaryOp op e) h = refl
classify-decanon bound (Raw.RAna F c) h = refl

------------------------------------------------------------------------
-- `composeMid` reflects `just B` (reuse the forward equalities, applied to the
-- reflected — i.e. un-canonicalized — arm derivations).
------------------------------------------------------------------------

open import Once.Adequacy.CanonComposeMid using (composeArgB-canon; domainOfHead-canon)

composeMid-decanon :
  ∀ {ctx : NamedCtx} {f g : RawExpr} {A B C : Type} {π} (bound : List String)
  → ctx ⊢ᵐ f ∶ B ⇨[ π ] C
  → ctx ⊢ᵐ g ∶ A ⇨[ π ] B
  → composeMid ctx (canonExpr bound [] [] f) (canonExpr bound [] [] g) A ≡ just B
  → composeMid ctx f g A ≡ just B
composeMid-decanon {A = A} bound df dg eq
  rewrite sym (composeArgB-canon bound A dg)
        | sym (domainOfHead-canon bound df) = eq

------------------------------------------------------------------------
-- Value-judgment reflection `⊢ᵍ` (independent — recurses only into itself).
-- `reflect-gvar`/`reflect-gapp` reduce the `canonVar` head via the explicit
-- boolean pattern; resolved heads (`b = false`) admit no `⊢ᵍ` rule (absurd).
------------------------------------------------------------------------

reflect-gvar : ∀ {ctx T} (b : Bool) (bound : List String) (x : String)
  → ctx ⊢ᵍ canonVar b nothing x ∶ T → ctx ⊢ᵍ Raw.RVar x ∶ T
reflect-gvar true  bound x D = D
reflect-gvar false bound x ()

mutual
  canon-reflects-ᵍ : ∀ {ctx T} (bound : List String) (e : RawExpr)
    → ctx ⊢ᵍ canonExpr bound [] [] e ∶ T → ctx ⊢ᵍ e ∶ T
  canon-reflects-ᵍ bound (Raw.RInt n) D = D
  canon-reflects-ᵍ bound (Raw.RVar x) D =
    reflect-gvar (elemStr x bound ∨ isBuiltinName x) bound x D
  canon-reflects-ᵍ bound (Raw.RPair a b) (g-pair d₁ d₂) =
    g-pair (canon-reflects-ᵍ bound a d₁) (canon-reflects-ᵍ bound b d₂)
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RVar y) arg) D =
    reflect-gapp (elemStr y bound ∨ isBuiltinName y) bound y arg D
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RApp a b) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RQualified n al) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RResolved cn) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RLam y b) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RLet y e₁ e₂) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RPair a b) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RDestruct s xl el xr er) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp Raw.RUnit arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RInt n) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RStringLit s) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RAnnot e t) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RBinOp op a b) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RUnaryOp op e) arg) ()
  canon-reflects-ᵍ bound (Raw.RApp (Raw.RAna F c) arg) ()
  canon-reflects-ᵍ bound (Raw.RQualified n al) ()
  canon-reflects-ᵍ bound (Raw.RResolved cn) ()
  canon-reflects-ᵍ bound (Raw.RLam x b) ()
  canon-reflects-ᵍ bound (Raw.RLet x e₁ e₂) ()
  canon-reflects-ᵍ bound (Raw.RDestruct s xl el xr er) ()
  canon-reflects-ᵍ bound Raw.RUnit ()
  canon-reflects-ᵍ bound (Raw.RStringLit s) ()
  canon-reflects-ᵍ bound (Raw.RAnnot e t) ()
  canon-reflects-ᵍ bound (Raw.RBinOp op a b) ()
  canon-reflects-ᵍ bound (Raw.RUnaryOp op e) ()
  canon-reflects-ᵍ bound (Raw.RAna F c) ()

  reflect-gapp : ∀ {ctx T} (b : Bool) (bound : List String) (y : String) (arg : RawExpr)
    → ctx ⊢ᵍ Raw.RApp (canonVar b nothing y) (canonExpr bound [] [] arg) ∶ T
    → ctx ⊢ᵍ Raw.RApp (Raw.RVar y) arg ∶ T
  reflect-gapp true bound y arg (g-inl d)  = g-inl (canon-reflects-ᵍ bound arg d)
  reflect-gapp true bound y arg (g-inr d)  = g-inr (canon-reflects-ᵍ bound arg d)
  reflect-gapp true bound y arg (g-In wf d) = g-In wf (canon-reflects-ᵍ bound arg d)
  reflect-gapp false bound y arg ()

------------------------------------------------------------------------
-- Bare-variable reflection for `⊢ᵢ` (the crux) and `⊢ᵐ`. Non-recursive: the
-- `b = true` (kept) branch returns the derivation unchanged; the `b = false`
-- (resolved) branch rebuilds the import rule from the resolved rule.
------------------------------------------------------------------------

reflect-var-ᵢ : ∀ {ctx A Ψ} (b : Bool) (bound : List String) (x : String)
  → Names⊆ ctx bound → (elemStr x bound ∨ isBuiltinName x) ≡ b
  → ctx ⊢ᵢ canonVar b nothing x ∶ A ⨾ Ψ → ctx ⊢ᵢ Raw.RVar x ∶ A ⨾ Ψ
reflect-var-ᵢ true  bound x sub eb D = D
reflect-var-ᵢ {ctx} false bound x sub eb (t-var-resolved imp) =
  t-var-import (¬unit-from-false {x} {bound} eb)
               (not-local {ctx} {x} {bound} sub (∨-false-l eb)) imp

reflect-var-ᵐ : ∀ {ctx A π B} (b : Bool) (bound : List String) (x : String)
  → Names⊆ ctx bound → (elemStr x bound ∨ isBuiltinName x) ≡ b
  → ctx ⊢ᵐ canonVar b nothing x ∶ A ⇨[ π ] B → ctx ⊢ᵐ Raw.RVar x ∶ A ⇨[ π ] B
reflect-var-ᵐ true  bound x sub eb D = D
reflect-var-ᵐ {ctx} false bound x sub eb (m-named-resolved imp) =
  m-named (¬unit-from-false {x} {bound} eb)
          (not-local {ctx} {x} {bound} sub (∨-false-l eb)) imp
