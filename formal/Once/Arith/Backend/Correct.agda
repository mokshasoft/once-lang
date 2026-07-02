-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.Correct  (width-parametric, PROVEN — Plan 0.54 Phase A)
--
-- Width-generic (`bits`): defines the concrete XInstr machine and proves
-- `exec-x86 (emit i) ≡ step i` per AbstractInstr (with the reg-bound the
-- 4-register `emit` needs). No baked-in width — the per-arch Correct picks it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)

module Once.Arith.Backend.Correct (bits : ℕ) where

open import Data.Nat using (_≟_; _+_; _*_; _∸_; _%_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import Data.Nat.DivMod using (%-distribˡ-+; m%n%n≡m%n)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Once.Arith.Machine.AbsState
open import Once.Arith.Machine.AbsInstr
open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.XInstr.CodeGen using (emit; emit-program; abs-reg; _≟x_)
open import Once.Arith.Machine.IR using (MArithIR; alit; ainput; aadd; asub; amul; aneg)
open import Once.Arith.Machine.Compile using (compile-go; compile-abs)
open import Once.Arith.Machine.WordSem using (module Sem)
open Sem bits using (eval-arith-W)
import Once.Arith.Machine.CompileCorrect as CC
open CC bits using (abs-validity)
open import Once.Word using (module Width)

open Width bits using (fromℤ; _⊕_; _⊖_; _⊗_; ⊝_; norm; modulus; modulus≢0)
open Exec bits using (step; run-abstract)

------------------------------------------------------------------------
-- Abstract register ↔ concrete XReg index
------------------------------------------------------------------------

xreg-idx : XReg → ℕ
xreg-idx XR12 = 0
xreg-idx XR13 = 1
xreg-idx XR14 = 2
xreg-idx XR15 = 3

-- Round-trip: if `emit` used `abs-reg r ≡ just xr`, the concrete reg maps back.
abs-reg-idx : ∀ (r : ℕ) (xr : XReg) → abs-reg r ≡ just xr → xreg-idx xr ≡ r
abs-reg-idx zero                         xr eq with eq
... | refl = refl
abs-reg-idx (suc zero)                   xr eq with eq
... | refl = refl
abs-reg-idx (suc (suc zero))             xr eq with eq
... | refl = refl
abs-reg-idx (suc (suc (suc zero)))       xr eq with eq
... | refl = refl
abs-reg-idx (suc (suc (suc (suc _))))    xr ()

------------------------------------------------------------------------
-- The concrete XInstr machine (XState = ArithAbsState, concretise = id)
------------------------------------------------------------------------

exec-xinstr : ∀ {sh} → XInstr → ArithAbsState sh → ArithAbsState sh
exec-xinstr (Xmov-imm d z)    s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ just (fromℤ z) ] }
exec-xinstr (Xmov-rr d src)   s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ ArithAbsState.regs s [ xreg-idx src ] ] }
exec-xinstr (Xmov-r-m sc src) s = record s { scratch = ArithAbsState.scratch s [ XScratch.slot sc ↦ ArithAbsState.regs s [ xreg-idx src ] ] }
exec-xinstr (Xmov-m-r d sc)   s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ ArithAbsState.scratch s [ XScratch.slot sc ] ] }
exec-xinstr (Xmov-arg d p)    s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ just (fromℤ (maybe-zero (project _ p (ArithAbsState.input s)))) ] }
exec-xinstr (Xadd-rr d src)   s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op _⊕_ (ArithAbsState.regs s [ xreg-idx d ]) (ArithAbsState.regs s [ xreg-idx src ]) ] }
exec-xinstr (Xsub-rr d src)   s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op _⊖_ (ArithAbsState.regs s [ xreg-idx d ]) (ArithAbsState.regs s [ xreg-idx src ]) ] }
exec-xinstr (Ximul-rr d src)  s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op _⊗_ (ArithAbsState.regs s [ xreg-idx d ]) (ArithAbsState.regs s [ xreg-idx src ]) ] }
exec-xinstr (Xneg-r d)        s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ un-op ⊝_ (ArithAbsState.regs s [ xreg-idx d ]) ] }
exec-xinstr (Xmov-out src)    s = record s { output = ArithAbsState.regs s [ xreg-idx src ] }

exec-x86 : ∀ {sh} → XProgram → ArithAbsState sh → ArithAbsState sh
exec-x86 []       s = s
exec-x86 (i ∷ is) s = exec-x86 is (exec-xinstr i s)

------------------------------------------------------------------------
-- refine, milestone 1: load-imm (validates the with-abstraction approach)
------------------------------------------------------------------------

refine-load-imm : ∀ {sh} (z : ℤ) (r : ℕ) (xr : XReg) → abs-reg r ≡ just xr →
  (s : ArithAbsState sh) →
  exec-x86 (emit (load-imm z r)) s ≡ step (load-imm z r) s
refine-load-imm z r xr eq s rewrite eq =
  cong (λ i → record s { regs = ArithAbsState.regs s [ i ↦ just (fromℤ z) ] })
       (abs-reg-idx r xr eq)

------------------------------------------------------------------------
-- Pointwise state-equivalence `~` (funext-free; mirrors CompileGoInv's
-- pointwise style so double-writing 2-instr emits need no funext).
------------------------------------------------------------------------

_~_ : ∀ {sh} → ArithAbsState sh → ArithAbsState sh → Set
s₁ ~ s₂ = (∀ j → ArithAbsState.regs s₁ [ j ] ≡ ArithAbsState.regs s₂ [ j ])
        × (∀ j → ArithAbsState.scratch s₁ [ j ] ≡ ArithAbsState.scratch s₂ [ j ])
        × (ArithAbsState.output s₁ ≡ ArithAbsState.output s₂)
        × (ArithAbsState.input s₁ ≡ ArithAbsState.input s₂)

~-refl : ∀ {sh} (s : ArithAbsState sh) → s ~ s
~-refl s = (λ _ → refl) , (λ _ → refl) , refl , refl

-- funext-free double-write collapse, per index.
-- The `with i ≟ j` abstraction reaches into both store reads (they share the
-- same `i ≟ j` dispatch), so each case reduces definitionally.
double-write : ∀ (σ : Store) i A B j → ((σ [ i ↦ A ]) [ i ↦ B ]) [ j ] ≡ (σ [ i ↦ B ]) [ j ]
double-write σ i A B j with i ≟ j
... | yes _  = refl
... | no ¬p = store-write-other σ i j A ¬p

------------------------------------------------------------------------
-- ~ is an equivalence; ≡ refines into ~
------------------------------------------------------------------------

≡→~ : ∀ {sh} {s₁ s₂ : ArithAbsState sh} → s₁ ≡ s₂ → s₁ ~ s₂
≡→~ refl = ~-refl _

~-sym : ∀ {sh} {s₁ s₂ : ArithAbsState sh} → s₁ ~ s₂ → s₂ ~ s₁
~-sym (r , sc , o , i) = (λ j → sym (r j)) , (λ j → sym (sc j)) , sym o , sym i

~-trans : ∀ {sh} {s₁ s₂ s₃ : ArithAbsState sh} → s₁ ~ s₂ → s₂ ~ s₃ → s₁ ~ s₃
~-trans (r₁ , sc₁ , o₁ , i₁) (r₂ , sc₂ , o₂ , i₂) =
  (λ j → trans (r₁ j) (r₂ j)) , (λ j → trans (sc₁ j) (sc₂ j)) , trans o₁ o₂ , trans i₁ i₂

------------------------------------------------------------------------
-- Single-write refines (full ≡, same shape as load-imm)
------------------------------------------------------------------------

refine-load-input : ∀ {sh} (p : InputPath) (r : ℕ) (xr : XReg) → abs-reg r ≡ just xr →
  (s : ArithAbsState sh) → exec-x86 (emit (load-input p r)) s ≡ step (load-input p r) s
refine-load-input p r xr eq s rewrite eq =
  cong (λ i → record s { regs = ArithAbsState.regs s [ i ↦ just (fromℤ (maybe-zero (project _ p (ArithAbsState.input s)))) ] })
       (abs-reg-idx r xr eq)

refine-spill : ∀ {sh} (src slot : ℕ) (xs : XReg) → abs-reg src ≡ just xs →
  (s : ArithAbsState sh) → exec-x86 (emit (spill src slot)) s ≡ step (spill src slot) s
refine-spill src slot xs eq s rewrite eq =
  cong (λ i → record s { scratch = ArithAbsState.scratch s [ slot ↦ ArithAbsState.regs s [ i ] ] })
       (abs-reg-idx src xs eq)

refine-reload : ∀ {sh} (slot dst : ℕ) (xd : XReg) → abs-reg dst ≡ just xd →
  (s : ArithAbsState sh) → exec-x86 (emit (reload slot dst)) s ≡ step (reload slot dst) s
refine-reload slot dst xd eq s rewrite eq =
  cong (λ i → record s { regs = ArithAbsState.regs s [ i ↦ ArithAbsState.scratch s [ slot ] ] })
       (abs-reg-idx dst xd eq)

refine-move-to-out : ∀ {sh} (src : ℕ) (xs : XReg) → abs-reg src ≡ just xs →
  (s : ArithAbsState sh) → exec-x86 (emit (move-to-out src)) s ≡ step (move-to-out src) s
refine-move-to-out src xs eq s rewrite eq =
  cong (λ i → record s { output = ArithAbsState.regs s [ i ] })
       (abs-reg-idx src xs eq)

------------------------------------------------------------------------
-- Word algebra (width-generic): commutativity + the sub identity that
-- `emit`'s aliasing optimizations need. All via ℕ facts under `norm`.
------------------------------------------------------------------------

⊕-comm : ∀ x y → x ⊕ y ≡ y ⊕ x
⊕-comm x y = cong norm (+-comm x y)

⊗-comm : ∀ x y → x ⊗ y ≡ y ⊗ x
⊗-comm x y = cong norm (*-comm x y)

-- norm absorbs a norm on the left of a `+`:  norm (norm x + y) ≡ norm (x + y).
norm-absorb-left : ∀ x y → norm (norm x + y) ≡ norm (x + y)
norm-absorb-left x y = trans (%-distribˡ-+ (x % modulus) y modulus)
                             (trans (cong (λ w → (w + (y % modulus)) % modulus) (m%n%n≡m%n x modulus))
                                    (sym (%-distribˡ-+ x y modulus)))

-- sub via neg-then-add:  (⊝ b) ⊕ a ≡ a ⊖ b.
sub-identity : ∀ a b → (⊝ b) ⊕ a ≡ a ⊖ b
sub-identity a b = trans (norm-absorb-left (modulus ∸ b) a) (cong norm (+-comm (modulus ∸ b) a))

-- `bin-op` inherits commutativity of the underlying op.
bin-op-comm : ∀ (f : ℕ → ℕ → ℕ) → (∀ x y → f x y ≡ f y x) →
  ∀ (ma mb : Maybe ℕ) → bin-op f ma mb ≡ bin-op f mb ma
bin-op-comm f fc (just x) (just y) = cong just (fc x y)
bin-op-comm f fc (just x) nothing  = refl
bin-op-comm f fc nothing  (just y) = refl
bin-op-comm f fc nothing  nothing  = refl

------------------------------------------------------------------------
-- neg-rr: 2-instr emit (mov; neg) → double-write, so ~ (not ≡).
------------------------------------------------------------------------

refine-neg : ∀ {sh} (dst a : ℕ) (xd xa : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa →
  (s : ArithAbsState sh) → exec-x86 (emit (neg-rr dst a)) s ~ step (neg-rr dst a) s
refine-neg dst a xd xa eqd eqa s
  rewrite eqd | eqa | abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa =
    (λ j → trans (double-write (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ])
                    (un-op ⊝_ ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ dst ])) j)
                 (cong (λ v → (ArithAbsState.regs s [ dst ↦ un-op ⊝_ v ]) [ j ])
                       (store-write-same (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ]))))
  , (λ _ → refl) , refl , refl

------------------------------------------------------------------------
-- Binary ops: mirror emit's aliasing dispatch (dst≡a | dst≡b | else).
------------------------------------------------------------------------

xreg-idx-inj : ∀ xd xb → xreg-idx xd ≡ xreg-idx xb → xd ≡ xb
xreg-idx-inj XR12 XR12 _ = refl
xreg-idx-inj XR13 XR13 _ = refl
xreg-idx-inj XR14 XR14 _ = refl
xreg-idx-inj XR15 XR15 _ = refl
xreg-idx-inj XR12 XR13 () ; xreg-idx-inj XR12 XR14 () ; xreg-idx-inj XR12 XR15 ()
xreg-idx-inj XR13 XR12 () ; xreg-idx-inj XR13 XR14 () ; xreg-idx-inj XR13 XR15 ()
xreg-idx-inj XR14 XR12 () ; xreg-idx-inj XR14 XR13 () ; xreg-idx-inj XR14 XR15 ()
xreg-idx-inj XR15 XR12 () ; xreg-idx-inj XR15 XR13 () ; xreg-idx-inj XR15 XR14 ()

-- dst ≡ a from xd ≡ xa (via round-trips).
idx-eq : ∀ {r₁ r₂ x₁ x₂} → abs-reg r₁ ≡ just x₁ → abs-reg r₂ ≡ just x₂ → x₁ ≡ x₂ → r₁ ≡ r₂
idx-eq {r₁} {r₂} {x₁} {x₂} e₁ e₂ xe =
  trans (sym (abs-reg-idx r₁ x₁ e₁)) (trans (cong xreg-idx xe) (abs-reg-idx r₂ x₂ e₂))

refine-add : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-x86 (emit (add-rrr dst a b)) s ~ step (add-rrr dst a b) s
refine-add dst a b xd xa xb eqd eqa eqb s rewrite eqd | eqa | eqb with xd ≟x xa
... | yes p rewrite abs-reg-idx dst xd eqd | abs-reg-idx b xb eqb =
      ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                (cong (λ r → bin-op _⊕_ r (ArithAbsState.regs s [ b ]))
                      (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqa p))))
... | no ¬pa with xd ≟x xb
...   | yes q rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa =
        ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                  (trans (cong (λ r → bin-op _⊕_ r (ArithAbsState.regs s [ a ]))
                               (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqb q)))
                         (bin-op-comm _⊕_ ⊕-comm (ArithAbsState.regs s [ b ]) (ArithAbsState.regs s [ a ]))))
...   | no ¬pb rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa | abs-reg-idx b xb eqb =
        (λ j → trans (double-write (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ])
                        (bin-op _⊕_ ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ dst ])
                                    ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ b ])) j)
                     (cong (λ v → (ArithAbsState.regs s [ dst ↦ v ]) [ j ])
                           (cong₂ (bin-op _⊕_)
                                  (store-write-same (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ]))
                                  (store-write-other (ArithAbsState.regs s) dst b (ArithAbsState.regs s [ a ]) dst≢b))))
        , (λ _ → refl) , refl , refl
        where
          dst≢b : ¬ (dst ≡ b)
          dst≢b e = ¬pb (xreg-idx-inj xd xb (trans (abs-reg-idx dst xd eqd)
                                                    (trans e (sym (abs-reg-idx b xb eqb)))))

refine-mul : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-x86 (emit (mul-rrr dst a b)) s ~ step (mul-rrr dst a b) s
refine-mul dst a b xd xa xb eqd eqa eqb s rewrite eqd | eqa | eqb with xd ≟x xa
... | yes p rewrite abs-reg-idx dst xd eqd | abs-reg-idx b xb eqb =
      ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                (cong (λ r → bin-op _⊗_ r (ArithAbsState.regs s [ b ]))
                      (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqa p))))
... | no ¬pa with xd ≟x xb
...   | yes q rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa =
        ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                  (trans (cong (λ r → bin-op _⊗_ r (ArithAbsState.regs s [ a ]))
                               (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqb q)))
                         (bin-op-comm _⊗_ ⊗-comm (ArithAbsState.regs s [ b ]) (ArithAbsState.regs s [ a ]))))
...   | no ¬pb rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa | abs-reg-idx b xb eqb =
        (λ j → trans (double-write (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ])
                        (bin-op _⊗_ ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ dst ])
                                    ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ b ])) j)
                     (cong (λ v → (ArithAbsState.regs s [ dst ↦ v ]) [ j ])
                           (cong₂ (bin-op _⊗_)
                                  (store-write-same (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ]))
                                  (store-write-other (ArithAbsState.regs s) dst b (ArithAbsState.regs s [ a ]) dst≢b))))
        , (λ _ → refl) , refl , refl
        where
          dst≢b : ¬ (dst ≡ b)
          dst≢b e = ¬pb (xreg-idx-inj xd xb (trans (abs-reg-idx dst xd eqd)
                                                    (trans e (sym (abs-reg-idx b xb eqb)))))

-- neg-then-add computes subtraction:  bin-op ⊕ (un-op ⊝ mb) ma ≡ bin-op ⊖ ma mb.
sub-bin-identity : ∀ (ma mb : Maybe ℕ) → bin-op _⊕_ (un-op ⊝_ mb) ma ≡ bin-op _⊖_ ma mb
sub-bin-identity (just a) (just b) = cong just (sub-identity a b)
sub-bin-identity (just a) nothing  = refl
sub-bin-identity nothing  (just b) = refl
sub-bin-identity nothing  nothing  = refl

refine-sub : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-x86 (emit (sub-rrr dst a b)) s ~ step (sub-rrr dst a b) s
refine-sub dst a b xd xa xb eqd eqa eqb s rewrite eqd | eqa | eqb with xd ≟x xa
-- dst≡a: single Xsub
... | yes p rewrite abs-reg-idx dst xd eqd | abs-reg-idx b xb eqb =
      ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                (cong (λ r → bin-op _⊖_ r (ArithAbsState.regs s [ b ]))
                      (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqa p))))
... | no ¬pa with xd ≟x xb
-- dst≡b: Xneg ∷ Xadd  (double-write, sub-identity)
...   | yes q rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa =
        (λ j → trans (double-write (ArithAbsState.regs s) dst (un-op ⊝_ (ArithAbsState.regs s [ dst ]))
                        (bin-op _⊕_ ((ArithAbsState.regs s [ dst ↦ un-op ⊝_ (ArithAbsState.regs s [ dst ]) ]) [ dst ])
                                    ((ArithAbsState.regs s [ dst ↦ un-op ⊝_ (ArithAbsState.regs s [ dst ]) ]) [ a ])) j)
                     (cong (λ v → (ArithAbsState.regs s [ dst ↦ v ]) [ j ])
                           (trans (cong₂ (bin-op _⊕_)
                                     (store-write-same (ArithAbsState.regs s) dst (un-op ⊝_ (ArithAbsState.regs s [ dst ])))
                                     (store-write-other (ArithAbsState.regs s) dst a (un-op ⊝_ (ArithAbsState.regs s [ dst ])) dst≢a))
                             (trans (cong (λ w → bin-op _⊕_ (un-op ⊝_ w) (ArithAbsState.regs s [ a ]))
                                          (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqb q)))
                                    (sub-bin-identity (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]))))))
        , (λ _ → refl) , refl , refl
        where
          dst≢a : ¬ (dst ≡ a)
          dst≢a e = ¬pa (xreg-idx-inj xd xa (trans (abs-reg-idx dst xd eqd)
                                                   (trans e (sym (abs-reg-idx a xa eqa)))))
-- else: Xmov ∷ Xsub  (double-write)
...   | no ¬pb rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa | abs-reg-idx b xb eqb =
        (λ j → trans (double-write (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ])
                        (bin-op _⊖_ ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ dst ])
                                    ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ b ])) j)
                     (cong (λ v → (ArithAbsState.regs s [ dst ↦ v ]) [ j ])
                           (cong₂ (bin-op _⊖_)
                                  (store-write-same (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ]))
                                  (store-write-other (ArithAbsState.regs s) dst b (ArithAbsState.regs s [ a ]) dst≢b))))
        , (λ _ → refl) , refl , refl
        where
          dst≢b : ¬ (dst ≡ b)
          dst≢b e = ¬pb (xreg-idx-inj xd xb (trans (abs-reg-idx dst xd eqd)
                                                    (trans e (sym (abs-reg-idx b xb eqb)))))

------------------------------------------------------------------------
-- Congruence of exec/step under ~, then the fold.
------------------------------------------------------------------------

store-cong2 : ∀ {σ₁ σ₂ : Store} → (∀ j → σ₁ [ j ] ≡ σ₂ [ j ]) →
  ∀ i {v₁ v₂ : Maybe NumValue} → v₁ ≡ v₂ → ∀ j → (σ₁ [ i ↦ v₁ ]) [ j ] ≡ (σ₂ [ i ↦ v₂ ]) [ j ]
store-cong2 h i ve j with i ≟ j
... | yes _ = ve
... | no  _ = h j

exec-xinstr-cong : ∀ {sh} (i : XInstr) {s₁ s₂ : ArithAbsState sh} → s₁ ~ s₂ → exec-xinstr i s₁ ~ exec-xinstr i s₂
exec-xinstr-cong (Xmov-imm d z)    (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) refl , sc , oc , ic
exec-xinstr-cong (Xmov-rr d src)   (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (rc (xreg-idx src)) , sc , oc , ic
exec-xinstr-cong (Xmov-r-m sc' src)(rc , sc , oc , ic) = rc , store-cong2 sc (XScratch.slot sc') (rc (xreg-idx src)) , oc , ic
exec-xinstr-cong (Xmov-m-r d sc')  (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (sc (XScratch.slot sc')) , sc , oc , ic
exec-xinstr-cong (Xmov-arg d p)    (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong (λ inp → just (fromℤ (maybe-zero (project _ p inp)))) ic) , sc , oc , ic
exec-xinstr-cong (Xadd-rr d src)   (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op _⊕_) (rc (xreg-idx d)) (rc (xreg-idx src))) , sc , oc , ic
exec-xinstr-cong (Xsub-rr d src)   (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op _⊖_) (rc (xreg-idx d)) (rc (xreg-idx src))) , sc , oc , ic
exec-xinstr-cong (Ximul-rr d src)  (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op _⊗_) (rc (xreg-idx d)) (rc (xreg-idx src))) , sc , oc , ic
exec-xinstr-cong (Xneg-r d)        (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong (un-op ⊝_) (rc (xreg-idx d))) , sc , oc , ic
exec-xinstr-cong (Xmov-out src)    (rc , sc , oc , ic) = rc , sc , rc (xreg-idx src) , ic

step-cong : ∀ {sh} (i : AbstractInstr) {s₁ s₂ : ArithAbsState sh} → s₁ ~ s₂ → step i s₁ ~ step i s₂
step-cong (load-input p r) (rc , sc , oc , ic) = store-cong2 rc r (cong (λ inp → just (fromℤ (maybe-zero (project _ p inp)))) ic) , sc , oc , ic
step-cong (load-imm z r)   (rc , sc , oc , ic) = store-cong2 rc r refl , sc , oc , ic
step-cong (add-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _⊕_) (rc a) (rc b)) , sc , oc , ic
step-cong (sub-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _⊖_) (rc a) (rc b)) , sc , oc , ic
step-cong (mul-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _⊗_) (rc a) (rc b)) , sc , oc , ic
step-cong (neg-rr dst a)   (rc , sc , oc , ic) = store-cong2 rc dst (cong (un-op ⊝_) (rc a)) , sc , oc , ic
step-cong (spill src slot) (rc , sc , oc , ic) = rc , store-cong2 sc slot (rc src) , oc , ic
step-cong (reload slot dst)(rc , sc , oc , ic) = store-cong2 rc dst (sc slot) , sc , oc , ic
step-cong (move-to-out src)(rc , sc , oc , ic) = rc , sc , rc src , ic

exec-x86-cong : ∀ {sh} (P : XProgram) {s₁ s₂ : ArithAbsState sh} → s₁ ~ s₂ → exec-x86 P s₁ ~ exec-x86 P s₂
exec-x86-cong []       eq = eq
exec-x86-cong (i ∷ is) eq = exec-x86-cong is (exec-xinstr-cong i eq)

exec-x86-++ : ∀ {sh} (xs ys : XProgram) (s : ArithAbsState sh) → exec-x86 (xs ++ ys) s ≡ exec-x86 ys (exec-x86 xs s)
exec-x86-++ []       ys s = refl
exec-x86-++ (i ∷ is) ys s = exec-x86-++ is ys (exec-xinstr i s)

-- Reg-bound: every reg index the instruction uses fits in the 4-register file.
InBound : ℕ → Set
InBound r = Σ[ xr ∈ XReg ] (abs-reg r ≡ just xr)

reg-bound : AbstractInstr → Set
reg-bound (load-input p r)  = InBound r
reg-bound (load-imm z r)    = InBound r
reg-bound (add-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (sub-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (mul-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (neg-rr dst a)    = InBound dst × InBound a
reg-bound (spill src slot)  = InBound src
reg-bound (reload slot dst) = InBound dst
reg-bound (move-to-out src) = InBound src

refine : ∀ {sh} (i : AbstractInstr) → reg-bound i → (s : ArithAbsState sh) → exec-x86 (emit i) s ~ step i s
refine (load-input p r)  (xr , e)                    s = ≡→~ (refine-load-input p r xr e s)
refine (load-imm z r)    (xr , e)                    s = ≡→~ (refine-load-imm z r xr e s)
refine (add-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = refine-add dst a b xd xa xb ed ea eb s
refine (sub-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = refine-sub dst a b xd xa xb ed ea eb s
refine (mul-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = refine-mul dst a b xd xa xb ed ea eb s
refine (neg-rr dst a)    ((xd , ed) , (xa , ea))     s = refine-neg dst a xd xa ed ea s
refine (spill src slot)  (xs , e)                    s = ≡→~ (refine-spill src slot xs e s)
refine (reload slot dst) (xd , e)                    s = ≡→~ (refine-reload slot dst xd e s)
refine (move-to-out src) (xs , e)                    s = ≡→~ (refine-move-to-out src xs e s)

All-bound : List AbstractInstr → Set
All-bound []       = ⊤
All-bound (i ∷ is) = reg-bound i × All-bound is

-- The fold: a reg-bounded program's XInstr run bisimulates the abstract run.
refine-program : ∀ {sh} (prog : List AbstractInstr) → All-bound prog →
  (s : ArithAbsState sh) → exec-x86 (emit-program prog) s ~ run-abstract prog s
refine-program []       _          s = ~-refl s
refine-program (i ∷ is) (bi , bis) s =
  subst (λ t → t ~ run-abstract is (step i s)) (sym (exec-x86-++ (emit i) (emit-program is) s))
        (~-trans (exec-x86-cong (emit-program is) (refine i bi s))
                 (refine-program is bis (step i s)))

------------------------------------------------------------------------
-- compile-abs stays inside the 4-register file (regs 0,1) — width-independent.
------------------------------------------------------------------------

bound0 : InBound 0
bound0 = XR12 , refl
bound1 : InBound 1
bound1 = XR13 , refl

All-bound-++ : ∀ (xs ys : List AbstractInstr) → All-bound xs → All-bound ys → All-bound (xs ++ ys)
All-bound-++ []       ys _          by = by
All-bound-++ (i ∷ is) ys (bi , bis) by = bi , All-bound-++ is ys bis by

compile-go-bound : ∀ {sh} (d : ℕ) (e : MArithIR sh) → All-bound (compile-go d e)
compile-go-bound d (alit z)   = bound0 , tt
compile-go-bound d (ainput p) = bound0 , tt
compile-go-bound d (aadd a b) =
  All-bound-++ (compile-go d a) _ (compile-go-bound d a)
    (bound0 , All-bound-++ (compile-go (suc d) b) _ (compile-go-bound (suc d) b)
                (bound1 , (bound0 , bound1 , bound0) , tt))
compile-go-bound d (asub a b) =
  All-bound-++ (compile-go d a) _ (compile-go-bound d a)
    (bound0 , All-bound-++ (compile-go (suc d) b) _ (compile-go-bound (suc d) b)
                (bound1 , (bound0 , bound1 , bound0) , tt))
compile-go-bound d (amul a b) =
  All-bound-++ (compile-go d a) _ (compile-go-bound d a)
    (bound0 , All-bound-++ (compile-go (suc d) b) _ (compile-go-bound (suc d) b)
                (bound1 , (bound0 , bound1 , bound0) , tt))
compile-go-bound d (aneg a) =
  All-bound-++ (compile-go d a) _ (compile-go-bound d a) ((bound0 , bound0) , tt)

compile-abs-bound : ∀ {sh} (e : MArithIR sh) → All-bound (compile-abs e)
compile-abs-bound e = All-bound-++ (compile-go 0 e) _ (compile-go-bound 0 e) (bound0 , tt)

------------------------------------------------------------------------
-- Block codegen correctness (width-generic): the emitted XInstr program
-- for `compile-abs e`, run on the concrete machine, outputs the block's
-- modular-Word value.  Composes the concrete refinement (refine-program
-- over the reg-bounded compile-abs) with the abstract validity.
------------------------------------------------------------------------

block-correct : ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (exec-x86 (emit-program (compile-abs e)) (init env)) ≡ just (eval-arith-W e env)
block-correct e env =
  trans (proj₁ (proj₂ (proj₂ (refine-program (compile-abs e) (compile-abs-bound e) (init env)))))
        (abs-validity e env)
