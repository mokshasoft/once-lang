-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.ReadTypedAdequate  (Plan 0.54 Phase B rung A / adequacy)
--
-- ADEQUACY of the type-directed reader `readTyped` (SMCore) against `ValidAtWF`
-- (ClosureWellFormed): if a value `v` of a READABLE type (Unit / Int / products
-- thereof — exactly the arith input shapes) is validly represented at `loc`,
-- then `readTyped` materialises exactly it: `readTyped A loc s ≡ just v`.
--
-- This is the bridge that makes `pure-sigop-output = semM (readTyped input)`
-- provably equal to `semM (input value) = eval (SigOp si) x` — closing rung A's
-- value-realized obligation. The IRTy/Type seam is crossed by `coh`
-- (`⟦ ⌊ A ⌋ ⟧ᴵ ≡ ⟦ A ⟧`, `refl` on base types).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.ReadTypedAdequate
  {FS : FrameSemantics} (program-bound : ℕ) where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Function using (id)

open import Once.Type using (Type; Unit; Int; _*_)
open import Once.IRTy using (⌊_⌋)
open import Once.Semantics.Machine using (⟦_⟧; ⟦_⟧ᴵ; coh)
open import Once.CCC.Machine.SMCore
open AbstractExec {FS}
open MemOps {FS}
open import Once.CCC.Machine.ClosureWellFormed
open ClosureWellFormedDef {FS} program-bound
  using (ValidAtWF; valid-unit-wf; valid-int-wf; valid-pair-wf; prim-sv)

-- Readable types: Unit, Int, and products thereof — the arith input shapes.
data Readable : Type → Set where
  r-unit : Readable Unit
  r-int  : Readable Int
  r-pair : ∀ {A B} → Readable A → Readable B → Readable (A * B)

-- Decision procedure, so the SigOp dispatch can ROUTE on readability: a Pure
-- SigOp over a readable input gets the real computed value; anything else falls
-- back (its `readTyped` is `nothing`, so `pure-sigop-output` keeps the sentinel
-- and no value claim is made). Arith blocks take tuples of Unit/Int
-- (`Arith.SigOp.Block.shape-as-type`), so they always take the readable route.
readable? : (A : Type) → Maybe (Readable A)
readable? Unit    = just r-unit
readable? Int     = just r-int
readable? (A * B) with readable? A | readable? B
... | just ra | just rb = just (r-pair ra rb)
... | _       | _       = nothing
readable? _       = nothing

-- Transport of a product decomposes componentwise (standard J-style).
subst-×-cong₂ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A) (b : B)
              → subst id (cong₂ _×_ p q) (a , b) ≡ (subst id p a , subst id q b)
subst-×-cong₂ refl refl a b = refl

-- ADEQUACY: a validly-represented value of a readable type is read back exactly
-- (`v` is the IRTy value; `subst id (coh A)` carries it to the `Type` domain).
-- Base cases: `coh Unit`/`coh Int` reduce to `refl` on the refined type. Product:
-- the transport splits (`subst-×-cong₂`) to match the two recursive reads.
readTyped-adequate : ∀ {A} → Readable A → ∀ {loc s m alloc} {v : ⟦ ⌊ A ⌋ ⟧ᴵ}
                   → ValidAtWF m alloc {⌊ A ⌋} v loc s
                   → readTyped A loc s ≡ just (subst id (coh A) v)
readTyped-adequate r-unit valid-unit-wf = refl
readTyped-adequate r-int (valid-int-wf bf rl) rewrite rl = refl
readTyped-adequate (r-pair rA rB)
  (valid-pair-wf {fst-loc = fl} {snd-loc = sl} lmm fp sp fb sb slb fv sv)
  rewrite fp | sp | readTyped-adequate rA fv | readTyped-adequate rB sv =
  cong just (sym (subst-×-cong₂ (coh _) (coh _) _ _))
