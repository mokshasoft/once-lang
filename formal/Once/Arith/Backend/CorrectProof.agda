-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.CorrectProof  (WIP scratch for Plan 0.54 Phase A)
--
-- Width-generic (`bits`): defines the concrete XInstr machine and proves
-- `exec-x86 (emit i) ≡ step i` per AbstractInstr (with the reg-bound the
-- 4-register `emit` needs). No baked-in width — the per-arch Correct picks it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)

module Once.Arith.Backend.CorrectProof (bits : ℕ) where

open import Data.Nat using (_≟_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)

open import Once.Arith.Machine.AbsState
open import Once.Arith.Machine.AbsInstr
open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.XInstr.CodeGen using (emit; emit-program; abs-reg)
open import Once.Word using (module Width)

open Width bits using (fromℤ; _⊕_; _⊖_; _⊗_; ⊝_)
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
