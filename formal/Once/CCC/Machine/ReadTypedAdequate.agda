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

open import Once.CCC.FrameSemantics using (FrameSemantics)

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.CanonicalName using (CanonicalName)

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Machine.ReadTypedAdequate (o : CanonicalName) (tbl : List IRFun)
  {FS : FrameSemantics} where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Once.IR
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Function using (id)

open import Once.Type using (Type; Unit; Void; Int; Float; _*_; _+_; rigid)
import Once.Type
open import Once.IRTy using (⌊_⌋; fits-int; fits-float)
open import Once.Functor.Translate using (IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid)
open import Once.Denotation.ValueDomain using (forgetᵇ; cohᴰ) renaming (⟦_⟧ᴰᴵ to ⟦_⟧ᴵ)
open import Once.CCC.Machine.SMCore
open AbstractExec {FS}
open MemOps {FS}
open import Once.CCC.Machine.ClosureWellFormed o tbl
open ClosureWellFormedDef {FS}
  using (ValidAtWF; valid-unit-wf; valid-int-wf; valid-float-wf; valid-pair-wf; valid-inl-wf; valid-inr-wf; valid-inl-reg-wf; valid-inr-reg-wf; SumTag; CellAt; cell-ptr; cell-inline; InlineRep; rep-prim; rep-unit; inline-sv)

-- Readable types: Unit, Int, and products thereof — the arith input shapes.
data Readable : Type → Set where
  r-unit : Readable Unit
  r-int  : Readable Int
  r-pair : ∀ {A B} → Readable A → Readable B → Readable (A * B)
  -- plan 0.105 §g: a SigOp's argument is read from memory at every base type
  -- the machine represents with its content — Float and sums too.
  r-float : Readable Float
  r-sum  : ∀ {A B} → Readable A → Readable B → Readable (A + B)
  -- D258 (plan 0.106): with `Str`/`Buffer` gone, EVERY base type is readable;
  -- `Void` and a rigid parameter have no values, so they are read vacuously.
  r-void  : Readable Void
  r-rigid : ∀ {k i} → Readable (rigid k i)

-- Every base type is readable (D258).
readable-base : ∀ {A} → IsBaseType A → Readable A
readable-base base-Unit       = r-unit
readable-base base-Void       = r-void
readable-base base-Int        = r-int
readable-base base-Float      = r-float
readable-base (base-Prod a b) = r-pair (readable-base a) (readable-base b)
readable-base (base-Sum a b)  = r-sum (readable-base a) (readable-base b)
readable-base base-rigid      = r-rigid

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
{-# CATCHALL #-}
... | _       | _       = nothing
readable? Float   = just r-float
readable? Void    = just r-void
readable? (rigid _ _) = just r-rigid
readable? (A + B) with readable? A | readable? B
... | just ra | just rb = just (r-sum ra rb)
{-# CATCHALL #-}
... | _       | _       = nothing
{-# CATCHALL #-}
readable? _       = nothing

-- Transport of a product decomposes componentwise (standard J-style).
subst-×-cong₂ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A) (b : B)
              → subst id (cong₂ _×_ p q) (a , b) ≡ (subst id p a , subst id q b)
subst-×-cong₂ refl refl a b = refl

subst-⊎₁ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A)
         → subst id (cong₂ _⊎_ p q) (inj₁ a) ≡ inj₁ (subst id p a)
subst-⊎₁ refl refl a = refl

subst-⊎₂ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (b : B)
         → subst id (cong₂ _⊎_ p q) (inj₂ b) ≡ inj₂ (subst id q b)
subst-⊎₂ refl refl b = refl

-- A sum's tag cell, whatever the mode.
sumtag-eq : ∀ {m t s loc} → SumTag m t s loc → readLoc s loc ≡ just (SV-Tag t)
sumtag-eq {Once.IR.Heap}  e = e
sumtag-eq {Once.IR.Stack} e = e

-- ADEQUACY: a validly-represented value of a readable type is read back exactly
-- (`v` is the IRTy value; `subst id (coh A)` carries it to the `Type` domain).
-- Base cases: `coh Unit`/`coh Int` reduce to `refl` on the refined type. Product:
-- the transport splits (`subst-×-cong₂`) to match the two recursive reads.
-- D180: the value is DENOTATIONAL, so it is `forget`ten before it crosses the
-- seam — which is exactly what `evalᴰ (SigOp si)` does with its own input
-- (plan 0.105: `forgetᵇ (baseA si)`, at the base-type witness the SigOp
-- carries; the lemma takes the witness, so the consumer passes its own). Stating adequacy in that
-- same form is what lets the consumer's `rewrite` close by `refl`; a
-- separately-invented coherence would have needed a bridge lemma to `coh`.
readTyped-cell-adequate : ∀ {A} (r : Readable A) (ib : IsBaseType A) → ∀ {cl s alloc} {c : ⟦ ⌊ A ⌋ ⟧ᴵ}
                        → CellAt alloc ⌊ A ⌋ c cl s
                        → readTyped-cell (λ l → readTyped A l s) (readReg-typed A)
                            (readLoc s cl)
                          ≡ just (forgetᵇ ib (subst id (cohᴰ A) c))
readTyped-adequate : ∀ {A} (r : Readable A) (ib : IsBaseType A) → ∀ {loc s m alloc} {v : ⟦ ⌊ A ⌋ ⟧ᴵ}
                   → ValidAtWF m alloc {⌊ A ⌋} v loc s
                   → readTyped A loc s ≡ just (forgetᵇ ib (subst id (cohᴰ A) v))
readTyped-adequate r-unit base-Unit valid-unit-wf = refl
readTyped-adequate r-int base-Int (valid-int-wf bf rl) rewrite rl = refl
readTyped-adequate r-float base-Float (valid-float-wf bf rl) rewrite rl = refl
readTyped-adequate r-void  _ {v = ()} _
readTyped-adequate r-rigid _ {v = ()} _
-- A sum: the tag selects the injection, the payload cell is a pair-style cell.
readTyped-adequate (r-sum {A} {B} rA rB) (base-Sum iA iB) {loc} {s} (valid-inl-wf {a = a} _ tg pl bfp _ va)
  rewrite sumtag-eq tg =
  trans (cong (Data.Maybe.map inj₁) (readTyped-cell-adequate rA iA (cell-ptr {cell-loc = sucLoc loc} {s = s} pl bfp va)))
        (cong just (cong (forgetᵇ (base-Sum iA iB)) (sym (subst-⊎₁ (cohᴰ A) (cohᴰ B) a))))
readTyped-adequate (r-sum {A} {B} rA rB) (base-Sum iA iB) {loc} {s} (valid-inr-wf {b = b} _ tg pl bfp _ vb)
  rewrite sumtag-eq tg =
  trans (cong (Data.Maybe.map inj₂) (readTyped-cell-adequate rB iB (cell-ptr {cell-loc = sucLoc loc} {s = s} pl bfp vb)))
        (cong just (cong (forgetᵇ (base-Sum iA iB)) (sym (subst-⊎₂ (cohᴰ A) (cohᴰ B) b))))
readTyped-adequate (r-sum {A} {B} rA rB) (base-Sum iA iB) {loc} {s} {_} {alloc} (valid-inl-reg-wf {a = a} _ tg rep rl _)
  rewrite sumtag-eq tg =
  trans (cong (Data.Maybe.map inj₁) (readTyped-cell-adequate rA iA {alloc = alloc} (cell-inline {cell-loc = sucLoc loc} {s = s} rep rl)))
        (cong just (cong (forgetᵇ (base-Sum iA iB)) (sym (subst-⊎₁ (cohᴰ A) (cohᴰ B) a))))
readTyped-adequate (r-sum {A} {B} rA rB) (base-Sum iA iB) {loc} {s} {_} {alloc} (valid-inr-reg-wf {b = b} _ tg rep rl _)
  rewrite sumtag-eq tg =
  trans (cong (Data.Maybe.map inj₂) (readTyped-cell-adequate rB iB {alloc = alloc} (cell-inline {cell-loc = sucLoc loc} {s = s} rep rl)))
        (cong just (cong (forgetᵇ (base-Sum iA iB)) (sym (subst-⊎₂ (cohᴰ A) (cohᴰ B) b))))
readTyped-adequate (r-pair {A} {B} rA rB) (base-Prod iA iB) {v = v} (valid-pair-wf lmm slb fc sc)
  rewrite readTyped-cell-adequate rA iA fc | readTyped-cell-adequate rB iB sc =
  cong just (cong (forgetᵇ (base-Prod iA iB)) (sym (subst-×-cong₂ (cohᴰ A) (cohᴰ B) (proj₁ v) (proj₂ v))))

-- D187: the CELL-level half. A pair cell is a pointer or the component
-- itself, and `readTyped-cell` dispatches on exactly that — so this lemma has
-- one clause per residence and neither invents anything.
readTyped-cell-adequate r-unit base-Unit (cell-ptr r bf v)    rewrite r = refl
readTyped-cell-adequate r-unit base-Unit {s = s} (cell-inline rep r)  rewrite r = unit-cell rep
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
readTyped-cell-adequate r-int base-Int (cell-ptr r bf v)
  rewrite r = readTyped-adequate r-int base-Int v
readTyped-cell-adequate r-int base-Int (cell-inline (rep-prim fits-int) r) rewrite r = refl
readTyped-cell-adequate r-int base-Int (cell-inline (rep-unit () _) r)
readTyped-cell-adequate (r-pair rA rB) ib (cell-ptr r bf v)
  rewrite r = readTyped-adequate (r-pair rA rB) ib v
readTyped-cell-adequate (r-pair rA rB) _ (cell-inline (rep-prim ()) r)
readTyped-cell-adequate (r-pair rA rB) _ (cell-inline (rep-unit () _) r)
readTyped-cell-adequate r-float base-Float (cell-ptr r bf v)
  rewrite r = readTyped-adequate r-float base-Float v
readTyped-cell-adequate r-float base-Float (cell-inline (rep-prim fits-float) r) rewrite r = refl
readTyped-cell-adequate r-float base-Float (cell-inline (rep-unit () _) r)
readTyped-cell-adequate (r-sum rA rB) ib (cell-ptr r bf v)
  rewrite r = readTyped-adequate (r-sum rA rB) ib v
readTyped-cell-adequate (r-sum rA rB) _ (cell-inline (rep-prim ()) r)
readTyped-cell-adequate (r-sum rA rB) _ (cell-inline (rep-unit () _) r)
readTyped-cell-adequate r-void  _ {c = ()} _
readTyped-cell-adequate r-rigid _ {c = ()} _
