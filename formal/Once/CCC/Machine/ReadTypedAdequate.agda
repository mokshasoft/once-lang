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
open import Once.Spec.Type using (Base; b-*; b-+; b-Float; b-Int; b-Unit; b-Void; ∅ₖ)

-- Plan 0.63 (D089): parameterised by the DEFINITION'S identity, which keys its
-- labels. `o` is constant for a whole definition, so it belongs on the module
-- rather than on every lemma — which is what keeps the statements below
-- UNCHANGED: the emitter is imported APPLIED, so each call site reads as before.
open import Once.Spec.Name using (CanonicalName)

open import Data.List using (List)
open import Once.Denotation.Program using (IRFun)
open import Once.CCC.Machine.SMCore using (AbstractTrace)
module Once.CCC.Machine.ReadTypedAdequate (o : CanonicalName) (tbl : List IRFun)
  {FS : FrameSemantics} where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Once.IR
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Function using (id)

open import Once.Spec.Type using (Type; Unit; Void; Int; Float; _*_; _+_)
import Once.Type
open import Once.IRTy using (⌊_⌋; fits-int; fits-float)
open import Once.Denotation.ValueDomain using (forgetᵇ; cohᴰ) renaming (⟦_⟧ᴰᴵ to ⟦_⟧ᴵ)
open import Once.CCC.Machine.SMCore
open AbstractExec {FS}
open MemOps {FS}
open import Once.CCC.Machine.ValueRel
open ClosureWellFormedDef {FS}
  using (ValidAtWF; CellAt)
open ClosureWellFormedBase {FS}
  using (SumTag; cell-ptr; cell-inline; cell-flat; InlineRep; rep-prim; inline-sv; IsNode)
open import Once.CCC.Codegen.Size using (size)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Nat
open import Data.Nat using (suc)

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
  -- `Void` has no values, so it is read vacuously.
  r-void  : Readable Void

-- Every base type is readable (D258).
readable-base : ∀ {A} → Base ∅ₖ A → Readable A
readable-base b-Unit       = r-unit
readable-base b-Void       = r-void
readable-base b-Int        = r-int
readable-base b-Float      = r-float
readable-base (b-* a b) = r-pair (readable-base a) (readable-base b)
readable-base (b-+ a b)  = r-sum (readable-base a) (readable-base b)

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
-- plan 0.135 S1: `ValidAtWF` is relative to the program (its arrow case);
-- `prog` is bound HERE, not as a module parameter, so the prog-free names
-- above (`Readable`, `readable-base`, …) do not carry it.
-- plan 0.123 B.4 α: a base type is never a node (μ, ν, a closure), and its
-- reader's size is its layout's
base-not-node : ∀ {A} → Base ∅ₖ A → IsNode ⌊ A ⌋ → ⊥
base-not-node b-Unit    ()
base-not-node b-Void    ()
base-not-node b-Int     ()
base-not-node b-Float   ()
base-not-node (b-* _ _) ()
base-not-node (b-+ _ _) ()

tsize-size : ∀ {A} → Base ∅ₖ A → tsize A ≡ size ⌊ A ⌋
tsize-size b-Unit    = refl
tsize-size b-Void    = refl
tsize-size b-Int     = refl
tsize-size b-Float   = refl
tsize-size (b-* a b) = cong₂ Data.Nat._+_ (tsize-size a) (tsize-size b)
tsize-size (b-+ a b) = cong suc (cong₂ Data.Nat._⊔_ (tsize-size a) (tsize-size b))

-- the COMPONENT half: a component of a base value is its word (a scalar) or
-- its own words in place (a compound), read where it lies
readTyped-cell-adequate : ∀ {prog : AbstractTrace} {A} (r : Readable A) (ib : Base ∅ₖ A) → ∀ {cl s alloc} {c : ⟦ ⌊ A ⌋ ⟧ᴵ}
                        → CellAt {prog = prog} alloc ⌊ A ⌋ c cl s
                        → readTyped A cl s ≡ just (forgetᵇ ib (subst id (cohᴰ A) c))

readTyped-adequate : ∀ {prog : AbstractTrace} {A} (r : Readable A) (ib : Base ∅ₖ A) → ∀ {loc s m alloc} {v : ⟦ ⌊ A ⌋ ⟧ᴵ}
                   → ValidAtWF {prog = prog} m alloc {⌊ A ⌋} v loc s
                   → readTyped A loc s ≡ just (forgetᵇ ib (subst id (cohᴰ A) v))
readTyped-adequate r-unit b-Unit valid-unit-wf = refl
readTyped-adequate r-int b-Int (valid-int-wf bf rl) rewrite rl = refl
readTyped-adequate r-float b-Float (valid-float-wf bf rl) rewrite rl = refl
readTyped-adequate r-void  _ {v = ()} _
-- A sum: the tag selects the injection; the payload is embedded after it.
readTyped-adequate (r-sum {A} {B} rA rB) (b-+ iA iB) (valid-inl-wf nd _ _ _ _ _ _) = ⊥-elim (base-not-node iA nd)
readTyped-adequate (r-sum {A} {B} rA rB) (b-+ iA iB) (valid-inr-wf nd _ _ _ _ _ _) = ⊥-elim (base-not-node iB nd)
readTyped-adequate {prog = prog} (r-sum {A} {B} rA rB) (b-+ iA iB) {loc} {s} {_} {alloc} (valid-inl-reg-wf {a = a} _ tg rep rl _)
  rewrite sumtag-eq tg =
  trans (cong (Data.Maybe.map inj₁) (readTyped-cell-adequate {prog = prog} rA iA {alloc = alloc} (cell-inline {cell-loc = sucLoc loc} {s = s} rep rl)))
        (cong just (cong (forgetᵇ (b-+ iA iB)) (sym (subst-⊎₁ (cohᴰ A) (cohᴰ B) a))))
readTyped-adequate {prog = prog} (r-sum {A} {B} rA rB) (b-+ iA iB) {loc} {s} {_} {alloc} (valid-inr-reg-wf {b = b} _ tg rep rl _)
  rewrite sumtag-eq tg =
  trans (cong (Data.Maybe.map inj₂) (readTyped-cell-adequate {prog = prog} rB iB {alloc = alloc} (cell-inline {cell-loc = sucLoc loc} {s = s} rep rl)))
        (cong just (cong (forgetᵇ (b-+ iA iB)) (sym (subst-⊎₂ (cohᴰ A) (cohᴰ B) b))))
readTyped-adequate (r-sum {A} {B} rA rB) (b-+ iA iB) {loc} {s} (valid-inl-flat-wf {a = a} _ _ tg _ va)
  rewrite sumtag-eq tg =
  trans (cong (Data.Maybe.map inj₁) (readTyped-adequate rA iA va))
        (cong just (cong (forgetᵇ (b-+ iA iB)) (sym (subst-⊎₁ (cohᴰ A) (cohᴰ B) a))))
readTyped-adequate (r-sum {A} {B} rA rB) (b-+ iA iB) {loc} {s} (valid-inr-flat-wf {b = b} _ _ tg _ vb)
  rewrite sumtag-eq tg =
  trans (cong (Data.Maybe.map inj₂) (readTyped-adequate rB iB vb))
        (cong just (cong (forgetᵇ (b-+ iA iB)) (sym (subst-⊎₂ (cohᴰ A) (cohᴰ B) b))))
-- A pair: the first component at its address, the second after its words.
readTyped-adequate (r-pair {A} {B} rA rB) (b-* iA iB) {loc} {s} {v = v} (valid-pair-wf lmm slb fc sc)
  rewrite readTyped-cell-adequate rA iA fc | tsize-size iA | readTyped-cell-adequate rB iB sc =
  cong just (cong (forgetᵇ (b-* iA iB)) (sym (subst-×-cong₂ (cohᴰ A) (cohᴰ B) (proj₁ v) (proj₂ v))))

readTyped-cell-adequate _ ib (cell-ptr nd _ _ _) = ⊥-elim (base-not-node ib nd)
readTyped-cell-adequate r-int b-Int (cell-inline (rep-prim fits-int) r) rewrite r = refl
readTyped-cell-adequate r-float b-Float (cell-inline (rep-prim fits-float) r) rewrite r = refl
readTyped-cell-adequate r-unit b-Unit (cell-inline (rep-prim ()) _)
readTyped-cell-adequate (r-pair _ _) _ (cell-inline (rep-prim ()) _)
readTyped-cell-adequate (r-sum _ _) _ (cell-inline (rep-prim ()) _)
readTyped-cell-adequate r ib (cell-flat _ v) = readTyped-adequate r ib v
readTyped-cell-adequate r-void  _ {c = ()} _
