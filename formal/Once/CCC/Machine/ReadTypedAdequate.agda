-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Machine.ReadTypedAdequate (o : CanonicalName)
  {FS : FrameSemantics} (program-bound : ℕ) where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Function using (id)

open import Once.Type using (Type; Unit; Int; _*_)
import Once.Type
open import Once.IRTy using (⌊_⌋; fits-int)
open import Once.Semantics.Machine using (⟦_⟧; coh)
open import Once.Denotation.ValueDomain using (forget) renaming (⟦_⟧ᴰᴵ to ⟦_⟧ᴵ)
open import Once.CCC.Machine.SMCore
open AbstractExec {FS}
open MemOps {FS}
open import Once.CCC.Machine.ClosureWellFormed o
open ClosureWellFormedDef {FS} program-bound
  using (ValidAtWF; valid-unit-wf; valid-int-wf; valid-pair-wf; prim-sv;
         CellAt; cell-ptr; cell-inline; InlineRep; rep-prim; rep-unit; inline-sv)

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
-- D180: the value is DENOTATIONAL, so it is `forget`ten before it crosses the
-- seam — which is exactly what `evalᴰ (SigOp si)` does with its own input
-- (`subst id (coh A) (forget a)`, DenotTrace:145). Stating adequacy in that
-- same form is what lets the consumer's `rewrite` close by `refl`; a
-- separately-invented coherence would have needed a bridge lemma to `coh`.
readTyped-cell-adequate : ∀ {A} (r : Readable A) → ∀ {cl s alloc} {c : ⟦ ⌊ A ⌋ ⟧ᴵ}
                        → CellAt alloc ⌊ A ⌋ c cl s
                        → readTyped-cell (λ l → readTyped A l s) (readReg-typed A)
                            (readLoc s cl)
                          ≡ just (subst id (coh A) (forget c))
readTyped-adequate : ∀ {A} (r : Readable A) → ∀ {loc s m alloc} {v : ⟦ ⌊ A ⌋ ⟧ᴵ}
                   → ValidAtWF m alloc {⌊ A ⌋} v loc s
                   → readTyped A loc s ≡ just (subst id (coh A) (forget v))
readTyped-adequate r-unit valid-unit-wf = refl
readTyped-adequate r-int (valid-int-wf bf rl) rewrite rl = refl
readTyped-adequate (r-pair rA rB) (valid-pair-wf lmm slb fc sc)
  rewrite readTyped-cell-adequate rA fc | readTyped-cell-adequate rB sc =
  cong just (sym (subst-×-cong₂ (coh _) (coh _) _ _))

-- D187: the CELL-level half. A pair cell is a pointer or the component
-- itself, and `readTyped-cell` dispatches on exactly that — so this lemma has
-- one clause per residence and neither invents anything.
readTyped-cell-adequate r-unit (cell-ptr r bf v)    rewrite r = refl
readTyped-cell-adequate r-unit {s = s} (cell-inline rep r)  rewrite r = unit-cell rep
  where
    unit-cell : ∀ {c} (rep : InlineRep ⌊ Unit ⌋)
              → readTyped-cell (λ l → readTyped Unit l s) (readReg-typed Unit)
                  (just (inline-sv rep c))
                ≡ just tt
    unit-cell (rep-prim ())
    unit-cell (rep-unit _ (SV-Ptr _))   = refl
    unit-cell (rep-unit _ (SV-Tag _))   = refl
    unit-cell (rep-unit _ (SV-Lit _ _)) = refl
    unit-cell (rep-unit _ (SV-Code _))  = refl
readTyped-cell-adequate r-int  (cell-ptr r bf v)
  rewrite r = readTyped-adequate r-int v
readTyped-cell-adequate r-int  (cell-inline (rep-prim fits-int) r) rewrite r = refl
readTyped-cell-adequate r-int  (cell-inline (rep-unit () _) r)
readTyped-cell-adequate (r-pair rA rB) (cell-ptr r bf v)
  rewrite r = readTyped-adequate (r-pair rA rB) v
readTyped-cell-adequate (r-pair rA rB) (cell-inline (rep-prim ()) r)
readTyped-cell-adequate (r-pair rA rB) (cell-inline (rep-unit () _) r)
