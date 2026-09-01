-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonReflectMutual — Plan 0.51 REVERSE preservation.
--
-- The mirror of `CanonPreserveMutual`: the resolver's own-module
-- canonicalization `canonExpr bound [] []` REFLECTS the three mutual declarative
-- judgments `⊢ᵢ`/`⊢ᶜ`. Given a derivation over
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
  using (lookup-just→elem; canon-RVar-keep; canon-RVar-resolve; _⊆ᵇ_; ⊆ᵇ-cons; ⊆ᵇ-nil;
         caHead-RApp-arg-irr)

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
...             | no _ with x ≟s "curry"
...               | yes refl = ⊥-elim (t≢f nb)
...               | no _ with x ≟s "apply"
...                 | yes refl = ⊥-elim (t≢f nb)
...                 | no _ with x ≟s "In"
...                   | yes refl = ⊥-elim (t≢f nb)
...                   | no _ with x ≟s "cata"
...                     | yes refl = ⊥-elim (t≢f nb)
...                     | no _ = refl

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
  trans (caHead-RApp-arg-irr z g (canonExpr bound [] [] g))
    (classify-decanon-rvar (elemStr z bound ∨ isBuiltinName z) bound z
      (canonExpr bound [] [] g) refl h)
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
classify-decanon bound (Raw.RApp (Raw.RFloat i fr fl _) g) h = refl
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
classify-decanon bound (Raw.RFloat i fr fl _) h = refl
classify-decanon bound (Raw.RStringLit s) h = refl
classify-decanon bound (Raw.RAnnot e t) h = refl
classify-decanon bound (Raw.RBinOp op a b) h = refl
classify-decanon bound (Raw.RUnaryOp op e) h = refl
classify-decanon bound (Raw.RAna F c) h = refl

-- D127: the `RApp (RApp (RVar z) f) g` head, for the two-argument combinator
-- helpers below. `classify-decanon` cannot serve: it states the hypothesis over
-- `canonExpr`, and these helpers have already reduced the head to `canonVar bz`.
decanon-cls-app2 : ∀ (bz : Bool) (bound : List String) (z : String) (f : RawExpr)
  → (elemStr z bound ∨ isBuiltinName z) ≡ bz
  → classifyAppHead (Raw.RApp (canonVar bz nothing z) (canonExpr bound [] [] f)) ≡ nothing
  → classifyAppHead (Raw.RApp (Raw.RVar z) f) ≡ nothing
decanon-cls-app2 bz bound z f eb h =
  trans (caHead-RApp-arg-irr z f (canonExpr bound [] [] f))
        (classify-decanon-rvar bz bound z (canonExpr bound [] [] f) eb h)

------------------------------------------------------------------------
-- `composeMid` reflects `just B` (reuse the forward equalities, applied to the
-- reflected — i.e. un-canonicalized — arm derivations).
------------------------------------------------------------------------

open import Once.Adequacy.CanonComposeMid using (composeArgB-canon; domainOfHead-canon)

composeMid-decanon :
  ∀ {ctx : NamedCtx} {A B : Type} (bound : List String) (f g : RawExpr)
  → composeMid ctx (canonExpr bound [] [] f) (canonExpr bound [] [] g) A ≡ just B
  → composeMid ctx f g A ≡ just B
composeMid-decanon {ctx} {A} bound f g eq
  rewrite sym (composeArgB-canon ctx bound A g)
        | sym (domainOfHead-canon ctx bound f) = eq

------------------------------------------------------------------------
-- Bare-variable reflection for `⊢ᵢ` (the crux). Non-recursive: the
-- `b = true` (kept) branch returns the derivation unchanged; the `b = false`
-- (resolved) branch rebuilds the import rule from the resolved rule.
------------------------------------------------------------------------

reflect-var-ᵢ : ∀ {ctx A Ψ} (b : Bool) (bound : List String) (x : String)
  → Names⊆ ctx bound → (elemStr x bound ∨ isBuiltinName x) ≡ b
  → ctx ⊢ᵢ canonVar b nothing x ∶ A ⨾ Ψ → ctx ⊢ᵢ Raw.RVar x ∶ A ⨾ Ψ
reflect-var-ᵢ true  bound x sub eb D = D
reflect-var-ᵢ {ctx} false bound x sub eb (t-var-resolved imp conc) =
  t-var-import (¬unit-from-false {x} {bound} eb)
               (not-local {ctx} {x} {bound} sub (∨-false-l eb)) imp conc

------------------------------------------------------------------------
-- Bare-variable reflection for `⊢ᶜ` (non-recursive). The kept branch returns the
-- derivation unchanged; the resolved branch handles the morph/embed bridges.
------------------------------------------------------------------------

reflect-var-ᶜ : ∀ {ctx A Ψ} (b : Bool) (bound : List String) (x : String)
  → Names⊆ ctx bound → (elemStr x bound ∨ isBuiltinName x) ≡ b
  → ctx ⊢ᶜ canonVar b nothing x ∶ A ⨾ Ψ → ctx ⊢ᶜ Raw.RVar x ∶ A ⨾ Ψ
reflect-var-ᶜ true  bound x sub eb D = D
-- D127: on the RESOLVED branch the index is `RResolved (canonical [x])`, so
-- every point-free leaf (`t-id-check` …, which all demand a bare `RVar "id"`
-- etc.) is ruled out by a CONSTRUCTOR CLASH — no clause, and no absurd pattern
-- either. Only the two bridges survive.
reflect-var-ᶜ false bound x sub eb (t-embed d)      = t-embed (reflect-var-ᵢ false bound x sub eb d)
reflect-var-ᶜ false bound x sub eb (t-subsume d)    = t-subsume (reflect-var-ᶜ false bound x sub eb d)

------------------------------------------------------------------------
-- PLAN 0.73 F3: a unary minus on a BARE VARIABLE.
--
-- Why this one operand needs a helper when the other fifteen do not. This
-- function inducts on `e` precisely because `canonExpr e` reduces only once
-- `e`'s head is exposed — and now the DERIVATION has a rule, `t-neg-float`,
-- whose index pins the operand to `RFloat i f l p`. So the operand's head has
-- to be exposed too. For fourteen of the sixteen heads `canonExpr` is
-- head-preserving, so exposing it is enough and the general clause covers
-- them; `RFloat` is its own clause. `RVar` is the one that stays stuck, since
-- `canonExpr … (RVar x)` is `canonVar b nothing x` and does not reduce until
-- `b` does.
--
-- Same remedy as `reflect-var-ᵢ`, and the same one the module header states:
-- make the boolean an EXPLICIT PATTERN argument. Both branches then have a
-- concrete operand — `RVar x` or `RResolved …` — and `t-neg-float` is ruled
-- out by a constructor clash rather than by an argument.
--
-- The recursion is passed IN rather than taken by mutual recursion: the call
-- `canon-reflects-ᵢ bound (RVar x) sub` sits at the call site, where `RVar x`
-- is visibly a subterm of `RUnaryOp OpNeg (RVar x)`. Inside a mutual block
-- this helper would instead CONSTRUCT `RVar x` from a `String`, and the
-- termination checker would have no descent to see.
reflect-neg-var-ᵢ : ∀ {ctx A Ψ} (b : Bool) (bound : List String) (x : String)
  → (elemStr x bound ∨ isBuiltinName x) ≡ b
  → (ih : ∀ {A' Ψ'} → ctx ⊢ᵢ canonVar b nothing x ∶ A' ⨾ Ψ'
                    → ctx ⊢ᵢ Raw.RVar x ∶ A' ⨾ Ψ')
  → ctx ⊢ᵢ Raw.RUnaryOp Raw.OpNeg (canonVar b nothing x) ∶ A ⨾ Ψ
  → ctx ⊢ᵢ Raw.RUnaryOp Raw.OpNeg (Raw.RVar x) ∶ A ⨾ Ψ
reflect-neg-var-ᵢ true  bound x eb ih (t-neg d) = t-neg (ih d)
reflect-neg-var-ᵢ false bound x eb ih (t-neg d) = t-neg (ih d)


------------------------------------------------------------------------
-- The mutual reverse reflection for ⊢ᵢ / ⊢ᶜ. Induct on `e`; reduce the
-- head dispatch via the boolean-pattern `reflect-app-*` helpers; recurse on
-- strict sub-derivations.
------------------------------------------------------------------------

mutual
  canon-reflects-ᵢ : ∀ {ctx A Ψ} (bound : List String) (e : RawExpr)
    → Names⊆ ctx bound → ctx ⊢ᵢ canonExpr bound [] [] e ∶ A ⨾ Ψ → ctx ⊢ᵢ e ∶ A ⨾ Ψ
  -- Leaves (canonExpr e = e definitionally).
  canon-reflects-ᵢ bound (Raw.RInt n) sub D = D
  canon-reflects-ᵢ bound (Raw.RFloat i fr fl _) sub D = D
  canon-reflects-ᵢ bound (Raw.RStringLit s) sub D = D
  canon-reflects-ᵢ bound Raw.RUnit sub D = D
  canon-reflects-ᵢ bound (Raw.RQualified n al) sub D = D
  canon-reflects-ᵢ bound (Raw.RResolved cn) sub D = D
  canon-reflects-ᵢ bound (Raw.RVar x) sub D =
    reflect-var-ᵢ (elemStr x bound ∨ isBuiltinName x) bound x sub refl D
  -- Structural.
  canon-reflects-ᵢ bound (Raw.RAnnot e₀ T) sub (t-annot d) =
    t-annot (canon-reflects-ᶜ bound e₀ sub d)
  canon-reflects-ᵢ bound (Raw.RPair a b) sub (t-pair d₁ d₂) =
    t-pair (canon-reflects-ᵢ bound a sub d₁) (canon-reflects-ᵢ bound b sub d₂)
  -- PLAN 0.73 F3. `t-neg-float` pins its operand to `RFloat i f l p`, so the
  -- operand's head has to be exposed before the derivation can be split. Two
  -- of the sixteen need saying: `RFloat` itself, and `RVar` (see
  -- `reflect-neg-var-ᵢ`). For the other fourteen `canonExpr` preserves the
  -- head, so the general clause below still covers them and `t-neg-float` is
  -- excluded by a constructor clash.
  --
  -- The `t-neg` case at an `RFloat` operand is absurd rather than merely
  -- unreachable: it would need `⊢ᵢ RFloat i f l p ∶ Int`, and `t-float` is the
  -- only rule with that expression as its index.
  canon-reflects-ᵢ bound (Raw.RUnaryOp Raw.OpNeg (Raw.RFloat i f l p)) sub
                   (t-neg ())
  canon-reflects-ᵢ bound (Raw.RUnaryOp Raw.OpNeg (Raw.RFloat i f l p)) sub
                   (t-neg-float .i .f .l .p) = t-neg-float i f l p
  canon-reflects-ᵢ bound (Raw.RUnaryOp Raw.OpNeg (Raw.RVar x)) sub D =
    reflect-neg-var-ᵢ (elemStr x bound ∨ isBuiltinName x) bound x refl
                      (canon-reflects-ᵢ bound (Raw.RVar x) sub) D
  canon-reflects-ᵢ bound (Raw.RUnaryOp Raw.OpNeg e₀) sub (t-neg d) =
    t-neg (canon-reflects-ᵢ bound e₀ sub d)
  canon-reflects-ᵢ bound (Raw.RBinOp op a b) sub (t-binop-arith p d₁ d₂) =
    t-binop-arith p (canon-reflects-ᵢ bound a sub d₁) (canon-reflects-ᵢ bound b sub d₂)
  -- PLAN 0.75 F4: structural, exactly as its integer twin above.
  canon-reflects-ᵢ bound (Raw.RBinOp op a b) sub (t-binop-arith-float p d₁ d₂) =
    t-binop-arith-float p (canon-reflects-ᵢ bound a sub d₁) (canon-reflects-ᵢ bound b sub d₂)
  -- D125: the mixed forms, structurally identical again.
  canon-reflects-ᵢ bound (Raw.RBinOp op a b) sub (t-binop-arith-float-il p d₁ d₂) =
    t-binop-arith-float-il p (canon-reflects-ᵢ bound a sub d₁) (canon-reflects-ᵢ bound b sub d₂)
  canon-reflects-ᵢ bound (Raw.RBinOp op a b) sub (t-binop-arith-float-ir p d₁ d₂) =
    t-binop-arith-float-ir p (canon-reflects-ᵢ bound a sub d₁) (canon-reflects-ᵢ bound b sub d₂)
  canon-reflects-ᵢ bound (Raw.RBinOp op a b) sub (t-binop-cmp p d₁ d₂) =
    t-binop-cmp p (canon-reflects-ᵢ bound a sub d₁) (canon-reflects-ᵢ bound b sub d₂)
  canon-reflects-ᵢ bound (Raw.RLet x e₁ e₂) sub (t-let d₁ d₂) =
    t-let (canon-reflects-ᵢ bound e₁ sub d₁)
          (canon-reflects-ᵢ (x ∷ bound) e₂ (⊆ᵇ-cons x sub) d₂)
  canon-reflects-ᵢ bound (Raw.RDestruct s xL eL xR eR) sub (t-case ds dL dR) =
    t-case (canon-reflects-ᵢ bound s sub ds)
           (canon-reflects-ᵢ (xL ∷ bound) eL (⊆ᵇ-cons xL sub) dL)
           (canon-reflects-ᵢ (xR ∷ bound) eR (⊆ᵇ-cons xR sub) dR)
  -- Application: RVar head via helper; concrete heads via t-app/t-effApp.
  canon-reflects-ᵢ bound (Raw.RApp (Raw.RVar y) X) sub D =
    reflect-app-var-ᵢ (elemStr y bound ∨ isBuiltinName y) bound y X sub refl D
  -- Non-RVar heads (RVar handled above): ONE clause per app rule. `hd` abstract —
  -- `classify-decanon bound hd cls` is well-typed for any head, so the 28 unrolled
  -- per-head clauses collapse to 2 (t-app / t-effApp).
  canon-reflects-ᵢ bound (Raw.RApp hd X) sub (t-app cls df dx) =
    t-app (classify-decanon bound hd cls) (canon-reflects-ᵢ bound hd sub df) (canon-reflects-ᶜ bound X sub dx)
  canon-reflects-ᵢ bound (Raw.RApp hd X) sub (t-effApp cls df dx) =
    t-effApp (classify-decanon bound hd cls) (canon-reflects-ᵢ bound hd sub df) (canon-reflects-ᶜ bound X sub dx)
  -- No ⊢ᵢ rule concludes RLam / RAna.
  canon-reflects-ᵢ bound (Raw.RLam x body) sub ()
  canon-reflects-ᵢ bound (Raw.RAna F c) sub ()

  reflect-app-var-ᵢ : ∀ {ctx A Ψ} (b : Bool) (bound : List String) (y : String) (X : RawExpr)
    → Names⊆ ctx bound → (elemStr y bound ∨ isBuiltinName y) ≡ b
    → ctx ⊢ᵢ Raw.RApp (canonVar b nothing y) (canonExpr bound [] [] X) ∶ A ⨾ Ψ
    → ctx ⊢ᵢ Raw.RApp (Raw.RVar y) X ∶ A ⨾ Ψ
  reflect-app-var-ᵢ true bound y X sub eb (t-id-app d)        = t-id-app (canon-reflects-ᵢ bound X sub d)
  reflect-app-var-ᵢ true bound y X sub eb (t-fst-app d)       = t-fst-app (canon-reflects-ᵢ bound X sub d)
  reflect-app-var-ᵢ true bound y X sub eb (t-snd-app d)       = t-snd-app (canon-reflects-ᵢ bound X sub d)
  reflect-app-var-ᵢ true bound y X sub eb (t-terminal-app d)  = t-terminal-app (canon-reflects-ᵢ bound X sub d)
  reflect-app-var-ᵢ true bound y X sub eb (t-apply-app-infer d) = t-apply-app-infer (canon-reflects-ᵢ bound X sub d)
  reflect-app-var-ᵢ true bound y X sub eb (t-app cls df dx)   = t-app cls df (canon-reflects-ᶜ bound X sub dx)
  reflect-app-var-ᵢ true bound y X sub eb (t-effApp cls df dx) = t-effApp cls df (canon-reflects-ᶜ bound X sub dx)
  reflect-app-var-ᵢ false bound y X sub eb (t-app cls df dx) =
    t-app (classifyRVar-nonbuiltin y (∨-false-r eb)) (reflect-var-ᵢ false bound y sub eb df) (canon-reflects-ᶜ bound X sub dx)
  reflect-app-var-ᵢ false bound y X sub eb (t-effApp cls df dx) =
    t-effApp (classifyRVar-nonbuiltin y (∨-false-r eb)) (reflect-var-ᵢ false bound y sub eb df) (canon-reflects-ᶜ bound X sub dx)

  canon-reflects-ᶜ : ∀ {ctx A Ψ} (bound : List String) (e : RawExpr)
    → Names⊆ ctx bound → ctx ⊢ᶜ canonExpr bound [] [] e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ A ⨾ Ψ
  -- Head-specific dispatch FIRST (so the case tree splits `e` first); the three
  -- universal lift bridges are the catch-all clauses LAST.
  canon-reflects-ᶜ bound (Raw.RVar x) sub D =
    reflect-var-ᶜ (elemStr x bound ∨ isBuiltinName x) bound x sub refl D
  canon-reflects-ᶜ bound (Raw.RPair a b) sub (t-pair-lit-check d₁ d₂) =
    t-pair-lit-check (canon-reflects-ᶜ bound a sub d₁) (canon-reflects-ᶜ bound b sub d₂)
  canon-reflects-ᶜ bound (Raw.RLam x body) sub (t-lam le d) =
    t-lam le (canon-reflects-ᶜ (x ∷ bound) body (⊆ᵇ-cons x sub) d)
  canon-reflects-ᶜ bound (Raw.RApp (Raw.RVar y) X) sub D =
    reflect-app-var-ᶜ (elemStr y bound ∨ isBuiltinName y) bound y X sub refl D
  -- D127: the TWO-ARGUMENT combinators (`compose`/`case`/`pair`) live in `⊢ᶜ`
  -- now, so this shape needs its own boolean-pattern helper — exactly what
  -- `canon-reflects-ᵐ` used to provide via `reflect-app2-var-ᵐ`. It must be
  -- BEFORE the general `RApp hd X` clause and the catch-alls, which it shadows
  -- for this shape (so it carries their rules too).
  canon-reflects-ᶜ bound (Raw.RApp (Raw.RApp (Raw.RVar z) f) g) sub D =
    reflect-app2-var-ᶜ (elemStr z bound ∨ isBuiltinName z) bound z f g sub refl D
  -- Non-RVar heads (RVar handled above): ONE clause — `hd` abstract, mirroring the
  -- `canon-reflects-ᵢ` collapse (14 unrolled per-head clauses → 1).
  canon-reflects-ᶜ bound (Raw.RApp hd X) sub (t-arg-driven-app-check cls darg df) =
    t-arg-driven-app-check (classify-decanon bound hd cls) (canon-reflects-ᵢ bound X sub darg) (canon-reflects-ᶜ bound hd sub df)
  -- Universal bridges (catch-all LAST; recurse on the same `e`).
  canon-reflects-ᶜ bound e sub (t-embed d)      = t-embed (canon-reflects-ᵢ bound e sub d)
  canon-reflects-ᶜ bound e sub (t-subsume d)    = t-subsume (canon-reflects-ᶜ bound e sub d)

  reflect-app-var-ᶜ : ∀ {ctx A Ψ} (b : Bool) (bound : List String) (y : String) (X : RawExpr)
    → Names⊆ ctx bound → (elemStr y bound ∨ isBuiltinName y) ≡ b
    → ctx ⊢ᶜ Raw.RApp (canonVar b nothing y) (canonExpr bound [] [] X) ∶ A ⨾ Ψ
    → ctx ⊢ᶜ Raw.RApp (Raw.RVar y) X ∶ A ⨾ Ψ
  reflect-app-var-ᶜ true bound y X sub eb (t-embed d)      = t-embed (reflect-app-var-ᵢ true bound y X sub eb d)
  -- D127: the ONE-argument combinators. `curry`'s arm is an ordinary term in
  -- the ambient context; `cata`'s algebra keeps the CLEARED context, whose
  -- `Names⊆` is the vacuous `⊆ᵇ-nil` (as in the forward direction).
  reflect-app-var-ᶜ true bound y X sub eb (t-curry-check df) =
    t-curry-check (canon-reflects-ᶜ bound X sub df)
  reflect-app-var-ᶜ true bound y X sub eb (t-cata-check eqW dalg) =
    t-cata-check eqW (canon-reflects-ᶜ bound X (⊆ᵇ-nil {bound}) dalg)
  reflect-app-var-ᶜ true bound y X sub eb (t-In-app-check wf d) = t-In-app-check wf (canon-reflects-ᶜ bound X sub d)
  reflect-app-var-ᶜ true bound y X sub eb (t-apply-check d)     = t-apply-check (canon-reflects-ᵢ bound X sub d)
  reflect-app-var-ᶜ true bound y X sub eb (t-inl-app-check d)   = t-inl-app-check (canon-reflects-ᶜ bound X sub d)
  reflect-app-var-ᶜ true bound y X sub eb (t-inr-app-check d)   = t-inr-app-check (canon-reflects-ᶜ bound X sub d)
  reflect-app-var-ᶜ true bound y X sub eb (t-initial-app-check d) = t-initial-app-check (canon-reflects-ᶜ bound X sub d)
  reflect-app-var-ᶜ true bound y X sub eb (t-arg-driven-app-check cls darg df) =
    t-arg-driven-app-check cls (canon-reflects-ᵢ bound X sub darg) df
  reflect-app-var-ᶜ true bound y X sub eb (t-subsume d) = t-subsume (reflect-app-var-ᶜ true bound y X sub eb d)
  reflect-app-var-ᶜ false bound y X sub eb (t-embed d)      = t-embed (reflect-app-var-ᵢ false bound y X sub eb d)
  reflect-app-var-ᶜ false bound y X sub eb (t-arg-driven-app-check cls darg df) =
    t-arg-driven-app-check (classifyRVar-nonbuiltin y (∨-false-r eb)) (canon-reflects-ᵢ bound X sub darg) (reflect-var-ᶜ false bound y sub eb df)
  reflect-app-var-ᶜ false bound y X sub eb (t-subsume d) = t-subsume (reflect-app-var-ᶜ false bound y X sub eb d)

  -- D127: the ⊢ᵢ twin of `reflect-app2-var-ᶜ`. Needed because `t-embed` at this
  -- shape carries an INFER derivation whose head is still `canonVar bz`, which
  -- only `bz`-as-a-pattern reduces; `canon-reflects-ᵢ` states it with
  -- `canonExpr` instead. `t-id-app` and the other builtin-app rules are ruled
  -- out by a constructor clash (their index is `RApp (RVar "id") x`).
  reflect-app2-var-ᵢ : ∀ {ctx A Ψ} (bz : Bool) (bound : List String)
      (z : String) (f g : RawExpr)
    → Names⊆ ctx bound → (elemStr z bound ∨ isBuiltinName z) ≡ bz
    → ctx ⊢ᵢ Raw.RApp (Raw.RApp (canonVar bz nothing z) (canonExpr bound [] [] f))
                      (canonExpr bound [] [] g) ∶ A ⨾ Ψ
    → ctx ⊢ᵢ Raw.RApp (Raw.RApp (Raw.RVar z) f) g ∶ A ⨾ Ψ
  reflect-app2-var-ᵢ bz bound z f g sub eb (t-app cls df dx) =
    t-app (decanon-cls-app2 bz bound z f eb cls)
          (reflect-app-var-ᵢ bz bound z f sub eb df)
          (canon-reflects-ᶜ bound g sub dx)
  reflect-app2-var-ᵢ bz bound z f g sub eb (t-effApp cls df dx) =
    t-effApp (decanon-cls-app2 bz bound z f eb cls)
             (reflect-app-var-ᵢ bz bound z f sub eb df)
             (canon-reflects-ᶜ bound g sub dx)

  -- D127: the two-argument combinators. On the RESOLVED branch (`bz = false`)
  -- the head is `RResolved (canonical [z])`, so `t-compose-check` and friends
  -- clash on it and only the three universal rules remain — which is why those
  -- three clauses are `bz`-polymorphic.
  reflect-app2-var-ᶜ : ∀ {ctx A Ψ} (bz : Bool) (bound : List String)
      (z : String) (f g : RawExpr)
    → Names⊆ ctx bound → (elemStr z bound ∨ isBuiltinName z) ≡ bz
    → ctx ⊢ᶜ Raw.RApp (Raw.RApp (canonVar bz nothing z) (canonExpr bound [] [] f))
                      (canonExpr bound [] [] g) ∶ A ⨾ Ψ
    → ctx ⊢ᶜ Raw.RApp (Raw.RApp (Raw.RVar z) f) g ∶ A ⨾ Ψ
  reflect-app2-var-ᶜ true bound z f g sub eb (t-compose-check cm df dg) =
    t-compose-check (composeMid-decanon bound f g cm)
                    (canon-reflects-ᶜ bound f sub df) (canon-reflects-ᶜ bound g sub dg)
  reflect-app2-var-ᶜ true bound z f g sub eb (t-case-copair-check df dg) =
    t-case-copair-check (canon-reflects-ᶜ bound f sub df) (canon-reflects-ᶜ bound g sub dg)
  reflect-app2-var-ᶜ true bound z f g sub eb (t-pair-morph-check df dg) =
    t-pair-morph-check (canon-reflects-ᶜ bound f sub df) (canon-reflects-ᶜ bound g sub dg)
  reflect-app2-var-ᶜ bz bound z f g sub eb (t-embed d) =
    t-embed (reflect-app2-var-ᵢ bz bound z f g sub eb d)
  reflect-app2-var-ᶜ bz bound z f g sub eb (t-subsume d) =
    t-subsume (reflect-app2-var-ᶜ bz bound z f g sub eb d)
  reflect-app2-var-ᶜ bz bound z f g sub eb (t-arg-driven-app-check cls darg df) =
    t-arg-driven-app-check (decanon-cls-app2 bz bound z f eb cls)
                           (canon-reflects-ᵢ bound g sub darg)
                           (reflect-app-var-ᶜ bz bound z f sub eb df)
