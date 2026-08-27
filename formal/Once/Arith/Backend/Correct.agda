-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.Correct  (width-parametric, PROVEN — Plan 0.54 Phase A)
--
-- Width-generic (`bits`): defines the concrete XInstr machine and proves
-- `exec-xprog (emit i) ≡ step i` per AbstractInstr (arch-neutral XInstr machine;
-- 4-register `emit` needs). No baked-in width — the per-arch Correct picks it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)

-- PLAN 0.75 F4: the FORMAT joins the width as a module parameter. This module
-- is pinned at `NInt` and never reads it, but `Sem` is now parameterised by
-- both and the format must come from the ARCHITECTURE — instantiating it at
-- some convenient `binary64` here would bake a format where all targets must
-- be served, which is the D109/D112 mistake. Taking it as a parameter makes
-- the dependency visible and costs the instantiating arch one word.
open import Once.Float.Dyadic using (FloatFormat)
module Once.Arith.Backend.Correct (bits : ℕ) (F : FloatFormat) where

open import Data.Nat using (_≟_; _+_; _*_; _∸_; _%_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import Data.Nat.DivMod using (%-distribˡ-+; m%n%n≡m%n)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Once.Arith.Machine.AbsState
open import Once.Arith.Machine.AbsInstr
open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.XInstr.CodeGen using (emit; emit-program; abs-reg; _≟x_)
-- PLAN 0.75 F4: the abstract-machine compile path is pinned at `NInt`, and
-- that restriction is STATED rather than assumed. Its instruction set
-- (`add-rrr`, `div-rrr`, …) is integer-register shaped, so a float block has
-- no lowering here yet; saying so in the type means the gate sees the gap
-- instead of a float tree silently taking the integer path.
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f)
open import Once.Arith.Machine.Compile
  using (compile-go; compile-abs; mul-op; mul-choose; div-op; div-choose; rem-op;
         div-instr; rem-instr; safe-divisor?; pow2?)
open import Once.Arith.Machine.WordSem using (module Sem)
open Sem bits F using (eval-arith-W)
import Once.Arith.Machine.CompileCorrect as CC
open CC bits F using (abs-validity)
open import Once.Word using (module Width)

open Width bits using (toℤ; fromℤ; _⊕_; _⊖_; _⊗_; _/ˢ_; _%ˢ_; ⊝_; shlᵂ; sdiv2ᵏ; norm; modulus; modulus≢0)
open Exec bits F using (step; run-abstract)
import Once.Float.Arith as FA
open import Once.Float.Decimal using (Decimal; round)

------------------------------------------------------------------------
-- Abstract register ↔ concrete XReg index
------------------------------------------------------------------------

xreg-idx : XReg → ℕ
xreg-idx XR0 = 0
xreg-idx XR1 = 1

-- Round-trip: if `emit` used `abs-reg r ≡ just xr`, the concrete reg maps back.
abs-reg-idx : ∀ (r : ℕ) (xr : XReg) → abs-reg r ≡ just xr → xreg-idx xr ≡ r
abs-reg-idx zero          xr eq with eq
... | refl = refl
abs-reg-idx (suc zero)    xr eq with eq
... | refl = refl
abs-reg-idx (suc (suc _)) xr ()

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
exec-xinstr (Xdiv-rrr d a b)  s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op _/ˢ_ (ArithAbsState.regs s [ xreg-idx a ]) (ArithAbsState.regs s [ xreg-idx b ]) ] }
exec-xinstr (Xrem-rrr d a b)  s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op _%ˢ_ (ArithAbsState.regs s [ xreg-idx a ]) (ArithAbsState.regs s [ xreg-idx b ]) ] }
-- `-safe` variants: SAME concrete meaning as the guarded div/rem (bare idiv is
-- a faithful realisation of `/ˢ`/`%ˢ` for a safe divisor — guaranteed by
-- construction, since compile-go emits `-safe` only for provably-safe literals).
exec-xinstr (Xdiv-safe-rrr d a b) s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op _/ˢ_ (ArithAbsState.regs s [ xreg-idx a ]) (ArithAbsState.regs s [ xreg-idx b ]) ] }
exec-xinstr (Xrem-safe-rrr d a b) s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op _%ˢ_ (ArithAbsState.regs s [ xreg-idx a ]) (ArithAbsState.regs s [ xreg-idx b ]) ] }
-- Strength-reduced multiply / divide by a power-of-two literal: SAME concrete
-- meaning as the AbsInstr `step` (single write `dst := un-op (shlᵂ ·)`/`(sdiv2ᵏ ·)`
-- of `src`). The per-arch Emit's shift/bias asm is the trusted realisation.
exec-xinstr (Xshl-rri d src imm)      s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ un-op (λ x → shlᵂ x imm) (ArithAbsState.regs s [ xreg-idx src ]) ] }
exec-xinstr (Xsdiv-pow2-rri d src imm) s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ un-op (λ x → sdiv2ᵏ x imm) (ArithAbsState.regs s [ xreg-idx src ]) ] }
exec-xinstr (Xneg-r d)        s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ un-op ⊝_ (ArithAbsState.regs s [ xreg-idx d ]) ] }
-- PLAN 0.75 F4: the float instructions, read at `F` through
-- `Once.Float.Arith` — the SAME functions the abstract machine's `step` and
-- the denotation's `block-semM` call, so `refine-program` has nothing to
-- reconcile beyond the register bookkeeping it already does.
exec-xinstr (Xfadd-rr d src)  s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op (FA.fadd F) (ArithAbsState.regs s [ xreg-idx d ]) (ArithAbsState.regs s [ xreg-idx src ]) ] }
exec-xinstr (Xfsub-rr d src)  s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op (FA.fsub F) (ArithAbsState.regs s [ xreg-idx d ]) (ArithAbsState.regs s [ xreg-idx src ]) ] }
exec-xinstr (Xfmul-rr d src)  s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op (FA.fmul F) (ArithAbsState.regs s [ xreg-idx d ]) (ArithAbsState.regs s [ xreg-idx src ]) ] }
exec-xinstr (Xfsubr-rr d src) s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ bin-op (FA.fsub F) (ArithAbsState.regs s [ xreg-idx src ]) (ArithAbsState.regs s [ xreg-idx d ]) ] }
exec-xinstr (Xfneg-r d)       s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ un-op (FA.fneg F) (ArithAbsState.regs s [ xreg-idx d ]) ] }
exec-xinstr (Xi2f-r d src)    s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ un-op (λ w → FA.i2f F (toℤ w)) (ArithAbsState.regs s [ xreg-idx src ]) ] }
exec-xinstr (Xmov-fimm d dc)  s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ just (round F dc) ] }
exec-xinstr (Xmov-farg d p)   s = record s { regs = ArithAbsState.regs s [ xreg-idx d ↦ just (maybe-zero-f (projectF _ p (ArithAbsState.input s))) ] }
exec-xinstr (Xmov-out src)    s = record s { output = ArithAbsState.regs s [ xreg-idx src ] }

exec-xprog : ∀ {sh} → XProgram → ArithAbsState sh → ArithAbsState sh
exec-xprog []       s = s
exec-xprog (i ∷ is) s = exec-xprog is (exec-xinstr i s)

------------------------------------------------------------------------
-- refine, milestone 1: load-imm (validates the with-abstraction approach)
------------------------------------------------------------------------

refine-load-imm : ∀ {sh} (z : ℤ) (r : ℕ) (xr : XReg) → abs-reg r ≡ just xr →
  (s : ArithAbsState sh) →
  exec-xprog (emit (load-imm z r)) s ≡ step (load-imm z r) s
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
  (s : ArithAbsState sh) → exec-xprog (emit (load-input p r)) s ≡ step (load-input p r) s
refine-load-input p r xr eq s rewrite eq =
  cong (λ i → record s { regs = ArithAbsState.regs s [ i ↦ just (fromℤ (maybe-zero (project _ p (ArithAbsState.input s)))) ] })
       (abs-reg-idx r xr eq)

refine-spill : ∀ {sh} (src slot : ℕ) (xs : XReg) → abs-reg src ≡ just xs →
  (s : ArithAbsState sh) → exec-xprog (emit (spill src slot)) s ≡ step (spill src slot) s
refine-spill src slot xs eq s rewrite eq =
  cong (λ i → record s { scratch = ArithAbsState.scratch s [ slot ↦ ArithAbsState.regs s [ i ] ] })
       (abs-reg-idx src xs eq)

refine-reload : ∀ {sh} (slot dst : ℕ) (xd : XReg) → abs-reg dst ≡ just xd →
  (s : ArithAbsState sh) → exec-xprog (emit (reload slot dst)) s ≡ step (reload slot dst) s
refine-reload slot dst xd eq s rewrite eq =
  cong (λ i → record s { regs = ArithAbsState.regs s [ i ↦ ArithAbsState.scratch s [ slot ] ] })
       (abs-reg-idx dst xd eq)

refine-move-to-out : ∀ {sh} (src : ℕ) (xs : XReg) → abs-reg src ≡ just xs →
  (s : ArithAbsState sh) → exec-xprog (emit (move-to-out src)) s ≡ step (move-to-out src) s
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
  (s : ArithAbsState sh) → exec-xprog (emit (neg-rr dst a)) s ~ step (neg-rr dst a) s
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
xreg-idx-inj XR0 XR0 _ = refl
xreg-idx-inj XR1 XR1 _ = refl
xreg-idx-inj XR0 XR1 ()
xreg-idx-inj XR1 XR0 ()

-- dst ≡ a from xd ≡ xa (via round-trips).
idx-eq : ∀ {r₁ r₂ x₁ x₂} → abs-reg r₁ ≡ just x₁ → abs-reg r₂ ≡ just x₂ → x₁ ≡ x₂ → r₁ ≡ r₂
idx-eq {r₁} {r₂} {x₁} {x₂} e₁ e₂ xe =
  trans (sym (abs-reg-idx r₁ x₁ e₁)) (trans (cong xreg-idx xe) (abs-reg-idx r₂ x₂ e₂))

refine-add : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-xprog (emit (add-rrr dst a b)) s ~ step (add-rrr dst a b) s
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
  (s : ArithAbsState sh) → exec-xprog (emit (mul-rrr dst a b)) s ~ step (mul-rrr dst a b) s
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
  (s : ArithAbsState sh) → exec-xprog (emit (sub-rrr dst a b)) s ~ step (sub-rrr dst a b) s
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
-- div / rem: THREE-address, single Xdiv-rrr/Xrem-rrr emit → single write,
-- so full ≡ (no aliasing dispatch — the 3-address form sidesteps it).
------------------------------------------------------------------------

-- `just x ≡ nothing` is absurd — rules out the impossible `abs-reg = nothing`
-- branches below (the hypotheses `eqd/eqa/eqb` say each read is `just`).
just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
just≢nothing ()

-- Shared just-just-just body: map the three concrete XRegs back to their
-- abstract indices with `abs-reg-idx`, congruently rewriting the single
-- `bin-op op` write. (`rewrite abs-reg-idx …` can't reach the index inside the
-- with-generated `emit` reduct, so we go through `cong₂` — as `refine-load-imm`
-- does — instead.) `op` is `_/ˢ_` for div and `_%ˢ_` for rem.
refine-3addr-just : ∀ {sh} (op : ℕ → ℕ → ℕ) (dst a b : ℕ) (xd′ xa′ xb′ : XReg)
  (s : ArithAbsState sh) →
  abs-reg dst ≡ just xd′ → abs-reg a ≡ just xa′ → abs-reg b ≡ just xb′ →
  record s { regs = ArithAbsState.regs s [ xreg-idx xd′ ↦
      bin-op op (ArithAbsState.regs s [ xreg-idx xa′ ]) (ArithAbsState.regs s [ xreg-idx xb′ ]) ] }
  ≡ record s { regs = ArithAbsState.regs s [ dst ↦
      bin-op op (ArithAbsState.regs s [ a ]) (ArithAbsState.regs s [ b ]) ] }
refine-3addr-just op dst a b xd′ xa′ xb′ s pd pa pb =
  cong₂ (λ i v → record s { regs = ArithAbsState.regs s [ i ↦ v ] })
        (abs-reg-idx dst xd′ pd)
        (cong₂ (λ j k → bin-op op (ArithAbsState.regs s [ j ]) (ArithAbsState.regs s [ k ]))
               (abs-reg-idx a xa′ pa) (abs-reg-idx b xb′ pb))

-- We case each `abs-reg` read via `with … in p` so `emit` reduces past its
-- dispatch (a bare `rewrite eqd | …` leaves it stuck inside the with-generated
-- function). The three `nothing` branches contradict `eqd/eqa/eqb`.
refine-div : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-xprog (emit (div-rrr dst a b)) s ≡ step (div-rrr dst a b) s
refine-div dst a b xd xa xb eqd eqa eqb s
  with abs-reg dst in pd | abs-reg a in pa | abs-reg b in pb
... | just xd′ | just xa′ | just xb′ = refine-3addr-just _/ˢ_ dst a b xd′ xa′ xb′ s pd pa pb
... | nothing  | _        | _        = ⊥-elim (just≢nothing (sym eqd))
... | just _   | nothing  | _        = ⊥-elim (just≢nothing (sym eqa))
... | just _   | just _   | nothing  = ⊥-elim (just≢nothing (sym eqb))

refine-rem : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-xprog (emit (rem-rrr dst a b)) s ≡ step (rem-rrr dst a b) s
refine-rem dst a b xd xa xb eqd eqa eqb s
  with abs-reg dst in pd | abs-reg a in pa | abs-reg b in pb
... | just xd′ | just xa′ | just xb′ = refine-3addr-just _%ˢ_ dst a b xd′ xa′ xb′ s pd pa pb
... | nothing  | _        | _        = ⊥-elim (just≢nothing (sym eqd))
... | just _   | nothing  | _        = ⊥-elim (just≢nothing (sym eqa))
... | just _   | just _   | nothing  = ⊥-elim (just≢nothing (sym eqb))

-- `-safe` variants: identical single-write refinement (same `-safe` step meaning).
refine-div-safe : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-xprog (emit (div-safe-rrr dst a b)) s ≡ step (div-safe-rrr dst a b) s
refine-div-safe dst a b xd xa xb eqd eqa eqb s
  with abs-reg dst in pd | abs-reg a in pa | abs-reg b in pb
... | just xd′ | just xa′ | just xb′ = refine-3addr-just _/ˢ_ dst a b xd′ xa′ xb′ s pd pa pb
... | nothing  | _        | _        = ⊥-elim (just≢nothing (sym eqd))
... | just _   | nothing  | _        = ⊥-elim (just≢nothing (sym eqa))
... | just _   | just _   | nothing  = ⊥-elim (just≢nothing (sym eqb))

refine-rem-safe : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-xprog (emit (rem-safe-rrr dst a b)) s ≡ step (rem-safe-rrr dst a b) s
refine-rem-safe dst a b xd xa xb eqd eqa eqb s
  with abs-reg dst in pd | abs-reg a in pa | abs-reg b in pb
... | just xd′ | just xa′ | just xb′ = refine-3addr-just _%ˢ_ dst a b xd′ xa′ xb′ s pd pa pb
... | nothing  | _        | _        = ⊥-elim (just≢nothing (sym eqd))
... | just _   | nothing  | _        = ⊥-elim (just≢nothing (sym eqa))
... | just _   | just _   | nothing  = ⊥-elim (just≢nothing (sym eqb))

------------------------------------------------------------------------
-- shl / sdiv-pow2: single-write, TWO-address (dst, src) + immediate. Same
-- single-write refinement shape as div/rem (but one operand is a read src,
-- and the write is `un-op (f · imm)` rather than `bin-op`). Full ≡.
------------------------------------------------------------------------

-- Shared just-just body: map both concrete XRegs back to their abstract
-- indices, congruently rewriting the single `un-op f` write.
refine-2addr-just : ∀ {sh} (f : ℕ → ℕ) (dst src : ℕ) (xd′ xs′ : XReg)
  (s : ArithAbsState sh) →
  abs-reg dst ≡ just xd′ → abs-reg src ≡ just xs′ →
  record s { regs = ArithAbsState.regs s [ xreg-idx xd′ ↦
      un-op f (ArithAbsState.regs s [ xreg-idx xs′ ]) ] }
  ≡ record s { regs = ArithAbsState.regs s [ dst ↦
      un-op f (ArithAbsState.regs s [ src ]) ] }
refine-2addr-just f dst src xd′ xs′ s pd ps =
  cong₂ (λ i v → record s { regs = ArithAbsState.regs s [ i ↦ v ] })
        (abs-reg-idx dst xd′ pd)
        (cong (λ j → un-op f (ArithAbsState.regs s [ j ])) (abs-reg-idx src xs′ ps))

refine-shl : ∀ {sh} (dst src imm : ℕ) (xd xs : XReg) →
  abs-reg dst ≡ just xd → abs-reg src ≡ just xs →
  (s : ArithAbsState sh) → exec-xprog (emit (shl-rri dst src imm)) s ≡ step (shl-rri dst src imm) s
refine-shl dst src imm xd xs eqd eqs s
  with abs-reg dst in pd | abs-reg src in ps
... | just xd′ | just xs′ = refine-2addr-just (λ x → shlᵂ x imm) dst src xd′ xs′ s pd ps
... | nothing  | _        = ⊥-elim (just≢nothing (sym eqd))
... | just _   | nothing  = ⊥-elim (just≢nothing (sym eqs))

refine-sdiv-pow2 : ∀ {sh} (dst src imm : ℕ) (xd xs : XReg) →
  abs-reg dst ≡ just xd → abs-reg src ≡ just xs →
  (s : ArithAbsState sh) → exec-xprog (emit (sdiv-pow2-rri dst src imm)) s ≡ step (sdiv-pow2-rri dst src imm) s
refine-sdiv-pow2 dst src imm xd xs eqd eqs s
  with abs-reg dst in pd | abs-reg src in ps
... | just xd′ | just xs′ = refine-2addr-just (λ x → sdiv2ᵏ x imm) dst src xd′ xs′ s pd ps
... | nothing  | _        = ⊥-elim (just≢nothing (sym eqd))
... | just _   | nothing  = ⊥-elim (just≢nothing (sym eqs))

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
exec-xinstr-cong (Xdiv-rrr d a b)  (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op _/ˢ_) (rc (xreg-idx a)) (rc (xreg-idx b))) , sc , oc , ic
exec-xinstr-cong (Xrem-rrr d a b)  (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op _%ˢ_) (rc (xreg-idx a)) (rc (xreg-idx b))) , sc , oc , ic
exec-xinstr-cong (Xdiv-safe-rrr d a b) (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op _/ˢ_) (rc (xreg-idx a)) (rc (xreg-idx b))) , sc , oc , ic
exec-xinstr-cong (Xrem-safe-rrr d a b) (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op _%ˢ_) (rc (xreg-idx a)) (rc (xreg-idx b))) , sc , oc , ic
exec-xinstr-cong (Xshl-rri d src imm)      (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong (un-op (λ x → shlᵂ x imm)) (rc (xreg-idx src))) , sc , oc , ic
exec-xinstr-cong (Xsdiv-pow2-rri d src imm) (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong (un-op (λ x → sdiv2ᵏ x imm)) (rc (xreg-idx src))) , sc , oc , ic
exec-xinstr-cong (Xneg-r d)        (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong (un-op ⊝_) (rc (xreg-idx d))) , sc , oc , ic
-- PLAN 0.75 F4: the float instructions. Same shape as their integer twins —
-- the congruence never inspects the operation, only where the write lands.
exec-xinstr-cong (Xfadd-rr d src)  (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op (FA.fadd F)) (rc (xreg-idx d)) (rc (xreg-idx src))) , sc , oc , ic
exec-xinstr-cong (Xfsub-rr d src)  (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op (FA.fsub F)) (rc (xreg-idx d)) (rc (xreg-idx src))) , sc , oc , ic
exec-xinstr-cong (Xfmul-rr d src)  (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op (FA.fmul F)) (rc (xreg-idx d)) (rc (xreg-idx src))) , sc , oc , ic
exec-xinstr-cong (Xfsubr-rr d src) (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong₂ (bin-op (FA.fsub F)) (rc (xreg-idx src)) (rc (xreg-idx d))) , sc , oc , ic
exec-xinstr-cong (Xfneg-r d)       (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong (un-op (FA.fneg F)) (rc (xreg-idx d))) , sc , oc , ic
exec-xinstr-cong (Xi2f-r d src)    (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong (un-op (λ w → FA.i2f F (toℤ w))) (rc (xreg-idx src))) , sc , oc , ic
exec-xinstr-cong (Xmov-fimm d dc)  (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) refl , sc , oc , ic
exec-xinstr-cong (Xmov-farg d p)   (rc , sc , oc , ic) = store-cong2 rc (xreg-idx d) (cong (λ inp → just (maybe-zero-f (projectF _ p inp))) ic) , sc , oc , ic
exec-xinstr-cong (Xmov-out src)    (rc , sc , oc , ic) = rc , sc , rc (xreg-idx src) , ic

step-cong : ∀ {sh} (i : AbstractInstr) {s₁ s₂ : ArithAbsState sh} → s₁ ~ s₂ → step i s₁ ~ step i s₂
step-cong (load-input p r) (rc , sc , oc , ic) = store-cong2 rc r (cong (λ inp → just (fromℤ (maybe-zero (project _ p inp)))) ic) , sc , oc , ic
step-cong (load-imm z r)   (rc , sc , oc , ic) = store-cong2 rc r refl , sc , oc , ic
step-cong (add-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _⊕_) (rc a) (rc b)) , sc , oc , ic
step-cong (sub-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _⊖_) (rc a) (rc b)) , sc , oc , ic
step-cong (mul-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _⊗_) (rc a) (rc b)) , sc , oc , ic
step-cong (div-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _/ˢ_) (rc a) (rc b)) , sc , oc , ic
step-cong (rem-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _%ˢ_) (rc a) (rc b)) , sc , oc , ic
step-cong (div-safe-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _/ˢ_) (rc a) (rc b)) , sc , oc , ic
step-cong (rem-safe-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op _%ˢ_) (rc a) (rc b)) , sc , oc , ic
step-cong (shl-rri dst src imm)      (rc , sc , oc , ic) = store-cong2 rc dst (cong (un-op (λ x → shlᵂ x imm)) (rc src)) , sc , oc , ic
step-cong (sdiv-pow2-rri dst src imm)(rc , sc , oc , ic) = store-cong2 rc dst (cong (un-op (λ x → sdiv2ᵏ x imm)) (rc src)) , sc , oc , ic
step-cong (neg-rr dst a)   (rc , sc , oc , ic) = store-cong2 rc dst (cong (un-op ⊝_) (rc a)) , sc , oc , ic
step-cong (spill src slot) (rc , sc , oc , ic) = rc , store-cong2 sc slot (rc src) , oc , ic
step-cong (reload slot dst)(rc , sc , oc , ic) = store-cong2 rc dst (sc slot) , sc , oc , ic
step-cong (load-finput p r)(rc , sc , oc , ic) = store-cong2 rc r (cong (λ inp → just (maybe-zero-f (projectF _ p inp))) ic) , sc , oc , ic
step-cong (load-fimm dc r) (rc , sc , oc , ic) = store-cong2 rc r refl , sc , oc , ic
step-cong (fadd-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op (FA.fadd F)) (rc a) (rc b)) , sc , oc , ic
step-cong (fsub-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op (FA.fsub F)) (rc a) (rc b)) , sc , oc , ic
step-cong (fmul-rrr dst a b)(rc , sc , oc , ic) = store-cong2 rc dst (cong₂ (bin-op (FA.fmul F)) (rc a) (rc b)) , sc , oc , ic
step-cong (fneg-rr dst a)  (rc , sc , oc , ic) = store-cong2 rc dst (cong (un-op (FA.fneg F)) (rc a)) , sc , oc , ic
step-cong (i2f-rr dst a)   (rc , sc , oc , ic) = store-cong2 rc dst (cong (un-op (λ w → FA.i2f F (toℤ w))) (rc a)) , sc , oc , ic
step-cong (move-to-out src)(rc , sc , oc , ic) = rc , sc , rc src , ic

exec-xprog-cong : ∀ {sh} (P : XProgram) {s₁ s₂ : ArithAbsState sh} → s₁ ~ s₂ → exec-xprog P s₁ ~ exec-xprog P s₂
exec-xprog-cong []       eq = eq
exec-xprog-cong (i ∷ is) eq = exec-xprog-cong is (exec-xinstr-cong i eq)

exec-xprog-++ : ∀ {sh} (xs ys : XProgram) (s : ArithAbsState sh) → exec-xprog (xs ++ ys) s ≡ exec-xprog ys (exec-xprog xs s)
exec-xprog-++ []       ys s = refl
exec-xprog-++ (i ∷ is) ys s = exec-xprog-++ is ys (exec-xinstr i s)

-- Reg-bound: every reg index the instruction uses fits in the 4-register file.
InBound : ℕ → Set
InBound r = Σ[ xr ∈ XReg ] (abs-reg r ≡ just xr)

reg-bound : AbstractInstr → Set
-- PLAN 0.75 F4: the float refinements.
refine-fadd : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-xprog (emit (fadd-rrr dst a b)) s ~ step (fadd-rrr dst a b) s
refine-fadd dst a b xd xa xb eqd eqa eqb s rewrite eqd | eqa | eqb with xd ≟x xa
... | yes p rewrite abs-reg-idx dst xd eqd | abs-reg-idx b xb eqb =
      ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                (cong (λ r → bin-op (FA.fadd F) r (ArithAbsState.regs s [ b ]))
                      (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqa p))))
... | no ¬pa with xd ≟x xb
...   | yes q rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa =
        ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                  (trans (cong (λ r → bin-op (FA.fadd F) r (ArithAbsState.regs s [ a ]))
                               (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqb q)))
                         (bin-op-comm (FA.fadd F) (FA.fadd-comm F) (ArithAbsState.regs s [ b ]) (ArithAbsState.regs s [ a ]))))
...   | no ¬pb rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa | abs-reg-idx b xb eqb =
        (λ j → trans (double-write (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ])
                        (bin-op (FA.fadd F) ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ dst ])
                                    ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ b ])) j)
                     (cong (λ v → (ArithAbsState.regs s [ dst ↦ v ]) [ j ])
                           (cong₂ (bin-op (FA.fadd F))
                                  (store-write-same (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ]))
                                  (store-write-other (ArithAbsState.regs s) dst b (ArithAbsState.regs s [ a ]) dst≢b))))
        , (λ _ → refl) , refl , refl
        where
          dst≢b : ¬ (dst ≡ b)
          dst≢b e = ¬pb (xreg-idx-inj xd xb (trans (abs-reg-idx dst xd eqd)
                                                    (trans e (sym (abs-reg-idx b xb eqb)))))

refine-fmul : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-xprog (emit (fmul-rrr dst a b)) s ~ step (fmul-rrr dst a b) s
refine-fmul dst a b xd xa xb eqd eqa eqb s rewrite eqd | eqa | eqb with xd ≟x xa
... | yes p rewrite abs-reg-idx dst xd eqd | abs-reg-idx b xb eqb =
      ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                (cong (λ r → bin-op (FA.fmul F) r (ArithAbsState.regs s [ b ]))
                      (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqa p))))
... | no ¬pa with xd ≟x xb
...   | yes q rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa =
        ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                  (trans (cong (λ r → bin-op (FA.fmul F) r (ArithAbsState.regs s [ a ]))
                               (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqb q)))
                         (bin-op-comm (FA.fmul F) (FA.fmul-comm F) (ArithAbsState.regs s [ b ]) (ArithAbsState.regs s [ a ]))))
...   | no ¬pb rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa | abs-reg-idx b xb eqb =
        (λ j → trans (double-write (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ])
                        (bin-op (FA.fmul F) ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ dst ])
                                    ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ b ])) j)
                     (cong (λ v → (ArithAbsState.regs s [ dst ↦ v ]) [ j ])
                           (cong₂ (bin-op (FA.fmul F))
                                  (store-write-same (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ]))
                                  (store-write-other (ArithAbsState.regs s) dst b (ArithAbsState.regs s [ a ]) dst≢b))))
        , (λ _ → refl) , refl , refl
        where
          dst≢b : ¬ (dst ≡ b)
          dst≢b e = ¬pb (xreg-idx-inj xd xb (trans (abs-reg-idx dst xd eqd)
                                                    (trans e (sym (abs-reg-idx b xb eqb)))))

refine-fneg : ∀ {sh} (dst a : ℕ) (xd xa : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa →
  (s : ArithAbsState sh) → exec-xprog (emit (fneg-rr dst a)) s ~ step (fneg-rr dst a) s
refine-fneg dst a xd xa eqd eqa s
  rewrite eqd | eqa | abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa =
    (λ j → trans (double-write (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ])
                    (un-op (FA.fneg F) ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ dst ])) j)
                 (cong (λ v → (ArithAbsState.regs s [ dst ↦ un-op (FA.fneg F) v ]) [ j ])
                       (store-write-same (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ]))))
  , (λ _ → refl) , refl , refl

refine-load-fimm : ∀ {sh} (dc : Decimal) (r : ℕ) (xr : XReg) → abs-reg r ≡ just xr →
  (s : ArithAbsState sh) →
  exec-xprog (emit (load-fimm dc r)) s ≡ step (load-fimm dc r) s
refine-load-fimm dc r xr eq s rewrite eq =
  cong (λ i → record s { regs = ArithAbsState.regs s [ i ↦ just (round F dc) ] })
       (abs-reg-idx r xr eq)


-- | The float subtract. Its `dst≡b` case is a SINGLE write, where the integer
-- twin needs a double-write plus a sub-identity — because `Xfsubr-rr` is the
-- operation the aliasing calls for rather than `neg` followed by `add`.
refine-fsub : ∀ {sh} (dst a b : ℕ) (xd xa xb : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa → abs-reg b ≡ just xb →
  (s : ArithAbsState sh) → exec-xprog (emit (fsub-rrr dst a b)) s ~ step (fsub-rrr dst a b) s
refine-fsub dst a b xd xa xb eqd eqa eqb s rewrite eqd | eqa | eqb with xd ≟x xa
... | yes p rewrite abs-reg-idx dst xd eqd | abs-reg-idx b xb eqb =
      ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                (cong (λ r → bin-op (FA.fsub F) r (ArithAbsState.regs s [ b ]))
                      (cong (ArithAbsState.regs s [_]) (idx-eq eqd eqa p))))
... | no ¬pa with xd ≟x xb
...   | yes q rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa =
        -- `Xfsubr-rr xd xa` writes `dst := regs[a] − regs[dst]`, and `dst ≡ b`
        -- here, so the only step is rewriting that index.
        ≡→~ (cong (λ v → record s { regs = ArithAbsState.regs s [ dst ↦ v ] })
                  (cong (λ r → bin-op (FA.fsub F) (ArithAbsState.regs s [ a ])
                                                  (ArithAbsState.regs s [ r ]))
                        (idx-eq eqd eqb q)))
...   | no ¬pb rewrite abs-reg-idx dst xd eqd | abs-reg-idx a xa eqa | abs-reg-idx b xb eqb =
        (λ j → trans (double-write (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ])
                        (bin-op (FA.fsub F) ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ dst ])
                                    ((ArithAbsState.regs s [ dst ↦ ArithAbsState.regs s [ a ] ]) [ b ])) j)
                     (cong (λ v → (ArithAbsState.regs s [ dst ↦ v ]) [ j ])
                           (cong₂ (bin-op (FA.fsub F))
                                  (store-write-same (ArithAbsState.regs s) dst (ArithAbsState.regs s [ a ]))
                                  (store-write-other (ArithAbsState.regs s) dst b (ArithAbsState.regs s [ a ]) dst≢b))))
        , (λ _ → refl) , refl , refl
        where
          dst≢b : ¬ (dst ≡ b)
          dst≢b e = ¬pb (xreg-idx-inj xd xb (trans (abs-reg-idx dst xd eqd)
                                                    (trans e (sym (abs-reg-idx b xb eqb)))))

-- | The widening and the float input leaf: single writes, no aliasing to
-- resolve — `Xi2f-r` reads its source register directly.
refine-i2f : ∀ {sh} (dst a : ℕ) (xd xa : XReg) →
  abs-reg dst ≡ just xd → abs-reg a ≡ just xa →
  (s : ArithAbsState sh) → exec-xprog (emit (i2f-rr dst a)) s ≡ step (i2f-rr dst a) s
refine-i2f dst a xd xa eqd eqa s rewrite eqd | eqa =
  cong₂ (λ i j → record s { regs = ArithAbsState.regs s [ i ↦ un-op (λ w → FA.i2f F (toℤ w)) (ArithAbsState.regs s [ j ]) ] })
        (abs-reg-idx dst xd eqd) (abs-reg-idx a xa eqa)

refine-load-finput : ∀ {sh} (p : InputPath) (r : ℕ) (xr : XReg) → abs-reg r ≡ just xr →
  (s : ArithAbsState sh) →
  exec-xprog (emit (load-finput p r)) s ≡ step (load-finput p r) s
refine-load-finput p r xr eq s rewrite eq =
  cong (λ i → record s { regs = ArithAbsState.regs s [ i ↦ just (maybe-zero-f (projectF _ p (ArithAbsState.input s))) ] })
       (abs-reg-idx r xr eq)


reg-bound (load-input p r)  = InBound r
reg-bound (load-imm z r)    = InBound r
reg-bound (add-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (sub-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (mul-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (div-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (rem-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (div-safe-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (rem-safe-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (shl-rri dst src imm)      = InBound dst × InBound src
reg-bound (sdiv-pow2-rri dst src imm) = InBound dst × InBound src
reg-bound (neg-rr dst a)    = InBound dst × InBound a
reg-bound (spill src slot)  = InBound src
reg-bound (reload slot dst) = InBound dst
reg-bound (load-finput p r) = InBound r
reg-bound (load-fimm dc r)  = InBound r
reg-bound (fadd-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (fsub-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (fmul-rrr dst a b) = InBound dst × InBound a × InBound b
reg-bound (fneg-rr dst a)   = InBound dst × InBound a
reg-bound (i2f-rr dst a)    = InBound dst × InBound a
reg-bound (move-to-out src) = InBound src

refine : ∀ {sh} (i : AbstractInstr) → reg-bound i → (s : ArithAbsState sh) → exec-xprog (emit i) s ~ step i s
refine (load-input p r)  (xr , e)                    s = ≡→~ (refine-load-input p r xr e s)
refine (load-imm z r)    (xr , e)                    s = ≡→~ (refine-load-imm z r xr e s)
refine (add-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = refine-add dst a b xd xa xb ed ea eb s
refine (sub-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = refine-sub dst a b xd xa xb ed ea eb s
refine (mul-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = refine-mul dst a b xd xa xb ed ea eb s
refine (div-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = ≡→~ (refine-div dst a b xd xa xb ed ea eb s)
refine (rem-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = ≡→~ (refine-rem dst a b xd xa xb ed ea eb s)
refine (div-safe-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = ≡→~ (refine-div-safe dst a b xd xa xb ed ea eb s)
refine (rem-safe-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = ≡→~ (refine-rem-safe dst a b xd xa xb ed ea eb s)
refine (shl-rri dst src imm)      ((xd , ed) , (xs , es)) s = ≡→~ (refine-shl dst src imm xd xs ed es s)
refine (sdiv-pow2-rri dst src imm) ((xd , ed) , (xs , es)) s = ≡→~ (refine-sdiv-pow2 dst src imm xd xs ed es s)
refine (neg-rr dst a)    ((xd , ed) , (xa , ea))     s = refine-neg dst a xd xa ed ea s
refine (spill src slot)  (xs , e)                    s = ≡→~ (refine-spill src slot xs e s)
refine (reload slot dst) (xd , e)                    s = ≡→~ (refine-reload slot dst xd e s)
refine (load-finput p r) (xr , e)                    s = ≡→~ (refine-load-finput p r xr e s)
refine (load-fimm dc r)  (xr , e)                    s = ≡→~ (refine-load-fimm dc r xr e s)
refine (fadd-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = refine-fadd dst a b xd xa xb ed ea eb s
refine (fsub-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = refine-fsub dst a b xd xa xb ed ea eb s
refine (fmul-rrr dst a b) ((xd , ed) , (xa , ea) , (xb , eb)) s = refine-fmul dst a b xd xa xb ed ea eb s
refine (fneg-rr dst a)   ((xd , ed) , (xa , ea))     s = refine-fneg dst a xd xa ed ea s
refine (i2f-rr dst a)    ((xd , ed) , (xa , ea))     s = ≡→~ (refine-i2f dst a xd xa ed ea s)
refine (move-to-out src) (xs , e)                    s = ≡→~ (refine-move-to-out src xs e s)

All-bound : List AbstractInstr → Set
All-bound []       = ⊤
All-bound (i ∷ is) = reg-bound i × All-bound is

-- The fold: a reg-bounded program's XInstr run bisimulates the abstract run.
refine-program : ∀ {sh} (prog : List AbstractInstr) → All-bound prog →
  (s : ArithAbsState sh) → exec-xprog (emit-program prog) s ~ run-abstract prog s
refine-program []       _          s = ~-refl s
refine-program (i ∷ is) (bi , bis) s =
  subst (λ t → t ~ run-abstract is (step i s)) (sym (exec-xprog-++ (emit i) (emit-program is) s))
        (~-trans (exec-xprog-cong (emit-program is) (refine i bi s))
                 (refine-program is bis (step i s)))

------------------------------------------------------------------------
-- compile-abs stays inside the 4-register file (regs 0,1) — width-independent.
------------------------------------------------------------------------

bound0 : InBound 0
bound0 = XR0 , refl
bound1 : InBound 1
bound1 = XR1 , refl

-- `div-op b` = `div-choose (pow2? b) (safe-divisor? b)`: a `sdiv-pow2-rri 0 1 j`
-- (reg-bound = InBound 0 × InBound 1) when `b` is a power-of-two literal, else
-- `div-instr t` = `div-rrr 0 1 0`/`-safe` twin (reg operands 0,1,0). We
-- pattern-match both decisions so `reg-bound` reduces.
div-instr-bound : (t : Bool) → reg-bound (div-instr t)
div-instr-bound true  = bound0 , bound1 , bound0
div-instr-bound false = bound0 , bound1 , bound0
div-choose-bound : (m : Maybe ℕ) (t : Bool) → reg-bound (div-choose m t)
div-choose-bound (just j) t = bound0 , bound1
div-choose-bound nothing  t = div-instr-bound t
div-op-bound : ∀ {sh} (b : MArithIR sh NInt) → reg-bound (div-op b)
div-op-bound b = div-choose-bound (pow2? b) (safe-divisor? b)

-- `mul-op b` = `mul-choose (pow2? b)`: a `shl-rri 0 1 j` (reg-bound =
-- InBound 0 × InBound 1) when `b` is a power-of-two literal, else `mul-rrr 0 1 0`.
mul-choose-bound : (m : Maybe ℕ) → reg-bound (mul-choose m)
mul-choose-bound (just j) = bound0 , bound1
mul-choose-bound nothing  = bound0 , bound1 , bound0
mul-op-bound : ∀ {sh} (b : MArithIR sh NInt) → reg-bound (mul-op b)
mul-op-bound b = mul-choose-bound (pow2? b)

rem-instr-bound : (t : Bool) → reg-bound (rem-instr t)
rem-instr-bound true  = bound0 , bound1 , bound0
rem-instr-bound false = bound0 , bound1 , bound0
rem-op-bound : ∀ {sh} (b : MArithIR sh NInt) → reg-bound (rem-op b)
rem-op-bound b = rem-instr-bound (safe-divisor? b)

All-bound-++ : ∀ (xs ys : List AbstractInstr) → All-bound xs → All-bound ys → All-bound (xs ++ ys)
All-bound-++ []       ys _          by = by
All-bound-++ (i ∷ is) ys (bi , bis) by = bi , All-bound-++ is ys bis by

compile-go-bound : ∀ {sh} (d : ℕ) (e : MArithIR sh NInt) → All-bound (compile-go d e)
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
                (bound1 , mul-op-bound b , tt))
compile-go-bound d (adiv a b) =
  All-bound-++ (compile-go d a) _ (compile-go-bound d a)
    (bound0 , All-bound-++ (compile-go (suc d) b) _ (compile-go-bound (suc d) b)
                (bound1 , div-op-bound b , tt))
compile-go-bound d (amod a b) =
  All-bound-++ (compile-go d a) _ (compile-go-bound d a)
    (bound0 , All-bound-++ (compile-go (suc d) b) _ (compile-go-bound (suc d) b)
                (bound1 , rem-op-bound b , tt))
compile-go-bound d (aneg a) =
  All-bound-++ (compile-go d a) _ (compile-go-bound d a) ((bound0 , bound0) , tt)

compile-abs-bound : ∀ {sh} (e : MArithIR sh NInt) → All-bound (compile-abs e)
compile-abs-bound e = All-bound-++ (compile-go 0 e) _ (compile-go-bound 0 e) (bound0 , tt)

------------------------------------------------------------------------
-- Block codegen correctness (width-generic): the emitted XInstr program
-- for `compile-abs e`, run on the concrete machine, outputs the block's
-- modular-Word value.  Composes the concrete refinement (refine-program
-- over the reg-bounded compile-abs) with the abstract validity.
------------------------------------------------------------------------

block-correct : ∀ {sh} (e : MArithIR sh NInt) (env : ⟦ sh ⟧S) →
  output-of (exec-xprog (emit-program (compile-abs e)) (init env)) ≡ just (eval-arith-W e env)
block-correct e env =
  trans (proj₁ (proj₂ (proj₂ (refine-program (compile-abs e) (compile-abs-bound e) (init env)))))
        (abs-validity e env)
