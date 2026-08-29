-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Machine.CompileCorrect  (width-parametric)
--
-- Correctness of `compile-abs` against the abstract executor, at ANY
-- word width `bits`.  The compiler itself (`compile-go`/`compile-abs`,
-- width-agnostic) lives in `Once.Arith.Machine.Compile`; this module
-- adds the proofs `run-abstract (compile-go d e)` lands
-- `eval-arith-W e` in reg 0.  No baked-in width — the arch supplies it.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

-- PLAN 0.75 F4: the FORMAT joins the width as a module parameter. This module
-- is pinned at `NInt` and never reads it, but `Sem` is now parameterised by
-- both and the format must come from the ARCHITECTURE — instantiating it at
-- some convenient `binary64` here would bake a format where all targets must
-- be served, which is the D109/D112 mistake. Taking it as a parameter makes
-- the dependency visible and costs the instantiating arch one word.
open import Once.Float.Dyadic using (FloatFormat)
import Once.Float.Arith as FA
module Once.Arith.Machine.CompileCorrect (bits : ℕ) (F : FloatFormat) where

open import Data.Nat using (zero; suc; _<_; s≤s; z≤n; _^_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Bool using (Bool; true; false)
open import Data.Nat.Properties using (<⇒≢; ≤-refl; m≤n⇒m≤1+n)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_)

open import Once.Arith.Machine.AbsState
  using (ArithAbsState; InputShape; ⟦_⟧S; init; output-of; InputPath; project; projectF;
         Store; empty-store; _[_↦_]; _[_]; store-write-same; store-write-other)
open import Once.Arith.Machine.AbsInstr
  using (load-finput; load-fimm; fadd-rrr; fsub-rrr; fmul-rrr; fdiv-rrr; fneg-rr; i2f-rr; AbstractInstr; load-input; load-imm; add-rrr; sub-rrr; mul-rrr;
         div-rrr; rem-rrr; div-safe-rrr; rem-safe-rrr; neg-rr; spill; reload;
         move-to-out; maybe-zero; maybe-zero-f; bin-op; un-op; module Exec)
open Exec bits F using (step; run-abstract)
-- PLAN 0.75 F4: the abstract-machine compile path is pinned at `NInt`, and
-- that restriction is STATED rather than assumed. Its instruction set
-- (`add-rrr`, `div-rrr`, …) is integer-register shaped, so a float block has
-- no lowering here yet; saying so in the type means the gate sees the gap
-- instead of a float tree silently taking the integer path.
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f;
         numtype-as-type; eval-arith)
open import Once.Word using (module Width)
open Width bits using
  (toℤ; fromℤ; _⊕_; _⊖_; _⊗_; _/ˢ_; _%ˢ_; ⊝_; modulus; modulus≢0; shlᵂ; sdiv2ᵏ; ⊗-pow2;
   /ˢ-zero; %ˢ-zero; fromℤ-0; fromℤ-in-range; fromℤ-neg1;
   /ˢ-negOne; %ˢ-negOne; /ˢ-in-range; %ˢ-in-range)
open import Once.Arith.Machine.WordSem using (module Sem)
open Sem bits F using (eval-arith-W)
open import Once.Arith.Machine.Compile
  using (compile-go; compile-abs; mul-op; mul-choose; div-op; div-choose; rem-op;
         div-instr; rem-instr; safe-divisor?; safe-lit?; pow2?; pow2-exp?; pow2-exp?-correct;
         normalize; fold-div; fold-mod)
open ArithAbsState

------------------------------------------------------------------------
-- Guard-elision (Part B) is semantics-preserving at the abstract level:
-- `div-op b` / `rem-op b` (which may pick the `-safe` variant) `step`
-- IDENTICALLY to the guarded `div-rrr 0 1 0` / `rem-rrr 0 1 0`. Both cases
-- of the `if` write the same `bin-op _/ˢ_`/`_%ˢ_`, so this is `refl`.
------------------------------------------------------------------------

step-div-safe≡ : ∀ {sh} (s : ArithAbsState sh) →
  step (div-safe-rrr 0 1 0) s ≡ step (div-rrr 0 1 0) s
step-div-safe≡ s = refl

step-div-instr : ∀ {sh} (t : Bool) (s : ArithAbsState sh) →
  step (div-instr t) s ≡ step (div-rrr 0 1 0) s
step-div-instr true  s = refl
step-div-instr false s = refl

-- Strength reduction (multiply / divide by a power-of-two literal) is
-- semantics-preserving GIVEN reg 0 holds the multiplier/divisor value
-- `eval-arith-W b`: `mul-op b`/`div-op b` (which may pick a shift) then
-- `step` identically to `mul-rrr 0 1 0`/`div-rrr 0 1 0`. The shift's write
-- `un-op (shlᵂ · j)`/`un-op (sdiv2ᵏ · j)` on reg 1 equals `bin-op _⊗_`/
-- `bin-op _/ˢ_` of reg 1 and reg 0 (= `fromℤ (+ 2^j)`), via `⊗-pow2` /
-- `sdiv2ᵏ`'s definition. Non-power-of-two `b` falls through to `refl` (mul)
-- or `step-div-instr` (div guard elision).

step-mul-op-eq : ∀ {sh} (b : MArithIR sh NInt) (env : ⟦ sh ⟧S) (s : ArithAbsState sh) →
  regs s [ 0 ] ≡ just (eval-arith-W b env) →
  step (mul-op b) s ≡ step (mul-rrr 0 1 0) s
step-mul-op-eq (alit k) env s h with pow2-exp? k in pe
... | just j  = cong (λ v → record s { regs = regs s [ 0 ↦ v ] }) inner
  where
    k≡ : k ≡ + (2 ^ j)
    k≡ = pow2-exp?-correct k j pe
    r0 : regs s [ 0 ] ≡ just (fromℤ (+ (2 ^ j)))
    r0 = trans h (cong (λ z → just (fromℤ z)) k≡)
    inner : un-op (λ x → shlᵂ x j) (regs s [ 1 ])
          ≡ bin-op _⊗_ (regs s [ 1 ]) (regs s [ 0 ])
    inner rewrite r0 with regs s [ 1 ]
    ... | just A  = cong just (sym (⊗-pow2 A j))
    ... | nothing = refl
... | nothing = refl
step-mul-op-eq (ainput p) env s h = refl
step-mul-op-eq (aadd a b) env s h = refl
step-mul-op-eq (asub a b) env s h = refl
step-mul-op-eq (amul a b) env s h = refl
step-mul-op-eq (adiv a b) env s h = refl
step-mul-op-eq (amod a b) env s h = refl
step-mul-op-eq (aneg a)   env s h = refl

step-div-op-eq : ∀ {sh} (b : MArithIR sh NInt) (env : ⟦ sh ⟧S) (s : ArithAbsState sh) →
  regs s [ 0 ] ≡ just (eval-arith-W b env) →
  step (div-op b) s ≡ step (div-rrr 0 1 0) s
step-div-op-eq (alit k) env s h with pow2-exp? k in pe
... | just j  = cong (λ v → record s { regs = regs s [ 0 ↦ v ] }) inner
  where
    k≡ : k ≡ + (2 ^ j)
    k≡ = pow2-exp?-correct k j pe
    r0 : regs s [ 0 ] ≡ just (fromℤ (+ (2 ^ j)))
    r0 = trans h (cong (λ z → just (fromℤ z)) k≡)
    inner : un-op (λ x → sdiv2ᵏ x j) (regs s [ 1 ])
          ≡ bin-op _/ˢ_ (regs s [ 1 ]) (regs s [ 0 ])
    inner rewrite r0 with regs s [ 1 ]
    ... | just A  = refl
    ... | nothing = refl
-- `safe-divisor? (alit k) = safe-lit? k` is a stuck neutral, so `div-op (alit k)`
-- does NOT reduce to a constructor here; feed the bool through `step-div-instr`.
... | nothing = step-div-instr (safe-lit? k) s
-- Non-literal divisors: `pow2? b = nothing` AND `safe-divisor? b = false`, so
-- `div-op b` reduces fully to `div-rrr 0 1 0` and the equation is `refl`.
step-div-op-eq (ainput p) env s h = refl
step-div-op-eq (aadd a b) env s h = refl
step-div-op-eq (asub a b) env s h = refl
step-div-op-eq (amul a b) env s h = refl
step-div-op-eq (adiv a b) env s h = refl
step-div-op-eq (amod a b) env s h = refl
step-div-op-eq (aneg a)   env s h = refl

step-rem-instr : ∀ {sh} (t : Bool) (s : ArithAbsState sh) →
  step (rem-instr t) s ≡ step (rem-rrr 0 1 0) s
step-rem-instr true  s = refl
step-rem-instr false s = refl

step-rem-op : ∀ {sh} (b : MArithIR sh NInt) (s : ArithAbsState sh) →
  step (rem-op b) s ≡ step (rem-rrr 0 1 0) s
step-rem-op b s = step-rem-instr (safe-divisor? b) s

------------------------------------------------------------------------
-- Strong invariant on `compile-go`
------------------------------------------------------------------------

-- PLAN 0.75 F4: kind-indexed. The invariant is the same sentence for both
-- kinds — reg 0 holds the tree's value, the scratch below `d` is untouched,
-- input and output are unchanged — because the register discipline does not
-- depend on which register file the values would live in on the metal.
record CompileGoInv {sh n} (d : ℕ) (e : MArithIR sh n) (s : ArithAbsState sh) : Set where
  field
    reg0      : regs (run-abstract (compile-go d e) s) [ 0 ]
                  ≡ just (eval-arith-W e (input s))
    scratch≤  : ∀ i → i < d →
                scratch (run-abstract (compile-go d e) s) [ i ]
                  ≡ scratch s [ i ]
    input-eq  : input (run-abstract (compile-go d e) s) ≡ input s
    output-eq : output (run-abstract (compile-go d e) s) ≡ output s

open CompileGoInv public

run-abstract-app : ∀ {sh} (xs ys : List AbstractInstr) (s : ArithAbsState sh) →
  run-abstract (xs ++ ys) s ≡ run-abstract ys (run-abstract xs s)
run-abstract-app []       ys s = refl
run-abstract-app (i ∷ is) ys s = run-abstract-app is ys (step i s)

eval-arith-W-ainput :
  ∀ {sh} (p : InputPath) (inp : ⟦ sh ⟧S) →
  eval-arith-W {sh} {NInt} (ainput p) inp ≡ fromℤ (maybe-zero (project sh p inp))
eval-arith-W-ainput {sh} p inp with project sh p inp
... | just _  = refl
... | nothing = refl

-- PLAN 0.75 F4: the float twin. Both branches are `refl` — there is no `fromℤ`
-- on this side to make the default non-trivial, which is D113 showing through
-- again: a float leaf is already a pattern.
eval-arith-W-finput :
  ∀ {sh} (p : InputPath) (inp : ⟦ sh ⟧S) →
  eval-arith-W {sh} {NFloat} (ainput p) inp ≡ maybe-zero-f (projectF sh p inp)
eval-arith-W-finput {sh} p inp with projectF sh p inp
... | just _  = refl
... | nothing = refl

compile-go-correct-ainput : ∀ {sh} (d : ℕ) (p : InputPath) (s : ArithAbsState sh) →
  CompileGoInv {n = NInt} d (ainput p) s
compile-go-correct-ainput {sh} d p s = record
  { reg0      = cong just (sym (eval-arith-W-ainput p (input s)))
  ; scratch≤  = λ _ _ → refl
  ; input-eq  = refl
  ; output-eq = refl
  }

private
  d≢i : ∀ {i d : ℕ} → i < d → ¬ (d ≡ i)
  d≢i lt eq = <⇒≢ lt (sym eq)

  <-suc : ∀ {i d : ℕ} → i < d → i < suc d
  <-suc lt = m≤n⇒m≤1+n lt

compile-go-correct : ∀ {sh n} (d : ℕ) (e : MArithIR sh n) (s : ArithAbsState sh) →
  CompileGoInv d e s

aneg-correct : ∀ {sh} (d : ℕ) (a : MArithIR sh NInt) (s : ArithAbsState sh) →
  CompileGoInv d (aneg a) s
aneg-correct {sh} d a s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong (un-op (⊝_)) (reg0 ih))
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                               (scratch≤ ih i lt)
  ; input-eq  = trans (cong input bridge) (input-eq ih)
  ; output-eq = trans (cong output bridge) (output-eq ih)
  }
  where
    ih : CompileGoInv d a s
    ih = compile-go-correct d a s

    bridge : run-abstract (compile-go d (aneg a)) s
           ≡ step (neg-rr 0 0) (run-abstract (compile-go d a) s)
    bridge = run-abstract-app (compile-go d a) (neg-rr 0 0 ∷ []) s

aadd-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh NInt) (s : ArithAbsState sh) →
  CompileGoInv d (aadd a b) s
aadd-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op _⊕_)
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (add-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (aadd a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ add-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ add-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

asub-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh NInt) (s : ArithAbsState sh) →
  CompileGoInv d (asub a b) s
asub-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op _⊖_)
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (sub-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (asub a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ sub-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ sub-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

amul-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh NInt) (s : ArithAbsState sh) →
  CompileGoInv d (amul a b) s
amul-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op _⊗_)
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (mul-rrr 0 1 0) s4

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

    regs-s4-0 : regs s4 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s4-0 = trans (store-write-other (regs s3) 1 0 (scratch s3 [ d ]) (λ ())) regs-s3-0

    -- `compile-go` emits `mul-op b` (a left shift when `b` is a power-of-two
    -- literal); `step-mul-op-eq` collapses it back to `mul-rrr 0 1 0` given
    -- reg 0 = the multiplier value, so the s5-based field proofs stand.
    bridge : run-abstract (compile-go d (amul a b)) s ≡ s5
    bridge = trans (trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ mul-op b ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ mul-op b ∷ []) s2))
      (step-mul-op-eq b (input s) s4 regs-s4-0)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

adiv-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh NInt) (s : ArithAbsState sh) →
  CompileGoInv d (adiv a b) s
adiv-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op _/ˢ_)
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (div-rrr 0 1 0) s4

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

    regs-s4-0 : regs s4 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s4-0 = trans (store-write-other (regs s3) 1 0 (scratch s3 [ d ]) (λ ())) regs-s3-0

    -- `compile-go` emits `div-op b` (guard-elided when safe, a sign-corrected
    -- shift when `b` is a power-of-two literal); `step-div-op-eq` collapses it
    -- back to `div-rrr 0 1 0` given reg 0 = the divisor value.
    bridge : run-abstract (compile-go d (adiv a b)) s ≡ s5
    bridge = trans (trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ div-op b ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ div-op b ∷ []) s2))
      (step-div-op-eq b (input s) s4 regs-s4-0)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

amod-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh NInt) (s : ArithAbsState sh) →
  CompileGoInv d (amod a b) s
amod-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op _%ˢ_)
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (rem-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (amod a b)) s ≡ s5
    bridge = trans (trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ rem-op b ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ rem-op b ∷ []) s2))
      (step-rem-op b s4)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

-- PLAN 0.75 F4: the float unary cases. Same proof as `aneg-correct` with the
-- operation swapped — the bookkeeping fields never mention it, which is the
-- evidence that the register discipline really is kind-independent.
fneg-correct : ∀ {sh} (d : ℕ) (a : MArithIR sh NFloat) (s : ArithAbsState sh) →
  CompileGoInv d (aneg a) s
fneg-correct {sh} d a s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong (un-op (FA.fneg F)) (reg0 ih))
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                               (scratch≤ ih i lt)
  ; input-eq  = trans (cong input bridge) (input-eq ih)
  ; output-eq = trans (cong output bridge) (output-eq ih)
  }
  where
    ih : CompileGoInv d a s
    ih = compile-go-correct d a s

    bridge : run-abstract (compile-go d (aneg a)) s
           ≡ step (fneg-rr 0 0) (run-abstract (compile-go d a) s)
    bridge = run-abstract-app (compile-go d a) (fneg-rr 0 0 ∷ []) s

-- …and D125's widening, the one node that crosses the kinds.
i2f-correct : ∀ {sh} (d : ℕ) (a : MArithIR sh NInt) (s : ArithAbsState sh) →
  CompileGoInv d (ai2f a) s
i2f-correct {sh} d a s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong (un-op (λ w → FA.i2f F (toℤ w))) (reg0 ih))
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                               (scratch≤ ih i lt)
  ; input-eq  = trans (cong input bridge) (input-eq ih)
  ; output-eq = trans (cong output bridge) (output-eq ih)
  }
  where
    ih : CompileGoInv d a s
    ih = compile-go-correct d a s

    bridge : run-abstract (compile-go d (ai2f a)) s
           ≡ step (i2f-rr 0 0) (run-abstract (compile-go d a) s)
    bridge = run-abstract-app (compile-go d a) (i2f-rr 0 0 ∷ []) s

-- The float binary cases. `amul`'s integer proof has to thread `mul-op`'s
-- power-of-two strength reduction; the float multiply has no such identity
-- that is exact for every operand, so `fmul-correct` mirrors `aadd` rather
-- than `amul` — simpler, and the reason is in `compile-go`.
fadd-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh NFloat) (s : ArithAbsState sh) →
  CompileGoInv d (aadd a b) s
fadd-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op (FA.fadd F))
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (fadd-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (aadd a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ fadd-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ fadd-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

fsub-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh NFloat) (s : ArithAbsState sh) →
  CompileGoInv d (asub a b) s
fsub-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op (FA.fsub F))
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (fsub-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (asub a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ fsub-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ fsub-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

fmul-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh NFloat) (s : ArithAbsState sh) →
  CompileGoInv d (amul a b) s
fmul-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op (FA.fmul F))
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (fmul-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (amul a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ fmul-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ fmul-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))


-- Division is structurally the multiplication proof with `FA.fdiv` in place of
-- `FA.fmul` — the sticky bit lives inside `fdiv`, not in the compilation, so
-- nothing here has to know about it.
fdiv-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh NFloat) (s : ArithAbsState sh) →
  CompileGoInv d (adiv a b) s
fdiv-correct {sh} d a b s = record
  { reg0      = trans (cong (λ x → regs x [ 0 ]) bridge)
                      (cong₂ (bin-op (FA.fdiv F))
                             (trans scratch-s3-d (reg0 ih-a))
                             regs-s3-0)
  ; scratch≤  = λ i lt → trans (cong (λ x → scratch x [ i ]) bridge)
                          (trans (scratch≤ ih-b i (<-suc lt))
                          (trans (store-write-other (scratch s1) d i
                                   (regs s1 [ 0 ]) (d≢i lt))
                                 (scratch≤ ih-a i lt)))
  ; input-eq  = trans (cong input bridge)
                      (trans (input-eq ih-b) (input-eq ih-a))
  ; output-eq = trans (cong output bridge)
                      (trans (output-eq ih-b) (output-eq ih-a))
  }
  where
    ih-a = compile-go-correct d a s
    s1   = run-abstract (compile-go d a) s
    s2   = step (spill 0 d) s1
    ih-b = compile-go-correct (suc d) b s2
    s3   = run-abstract (compile-go (suc d) b) s2
    s4   = step (reload d 1) s3
    s5   = step (fdiv-rrr 0 1 0) s4

    bridge : run-abstract (compile-go d (adiv a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ fdiv-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ fdiv-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))


-- Kind dispatch: the same node name selects the integer or the float proof.
compile-go-correct d (alit z) s = record
  { reg0      = refl
  ; scratch≤  = λ _ _ → refl
  ; input-eq  = refl
  ; output-eq = refl
  }
compile-go-correct {sh} {NInt} d (ainput p) s = compile-go-correct-ainput {sh} d p s
compile-go-correct {n = NInt} d (aneg a) s = aneg-correct d a s
compile-go-correct {n = NFloat} d (aflit dc) s = record
  { reg0 = refl ; scratch≤ = λ _ _ → refl ; input-eq = refl ; output-eq = refl }
compile-go-correct {n = NFloat} d (ainput p) s = record
  { reg0 = cong just (sym (eval-arith-W-finput p (input s)))
  ; scratch≤ = λ _ _ → refl ; input-eq = refl ; output-eq = refl }
compile-go-correct {n = NFloat} d (aneg a) s = fneg-correct d a s
compile-go-correct {n = NFloat} d (aadd a b) s = fadd-correct d a b s
compile-go-correct {n = NFloat} d (asub a b) s = fsub-correct d a b s
compile-go-correct {n = NFloat} d (amul a b) s = fmul-correct d a b s
compile-go-correct d (ai2f a) s = i2f-correct d a s
compile-go-correct {n = NInt} d (aadd a b) s = aadd-correct d a b s
compile-go-correct {n = NInt} d (asub a b) s = asub-correct d a b s
compile-go-correct {n = NInt} d (amul a b) s = amul-correct d a b s
compile-go-correct {n = NInt}   d (adiv a b) s = adiv-correct d a b s
compile-go-correct {n = NFloat} d (adiv a b) s = fdiv-correct d a b s
compile-go-correct d (amod a b) s = amod-correct d a b s

------------------------------------------------------------------------
-- Block validity: `output-of (run-abstract (compile-abs e) (init env))`
------------------------------------------------------------------------

abs-validity : ∀ {sh n} (e : MArithIR sh n) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs e) (init env)) ≡ just (eval-arith-W e env)
abs-validity {sh} e env =
  trans (cong output-of (run-abstract-app (compile-go 0 e) (move-to-out 0 ∷ []) (init env)))
        (reg0 (compile-go-correct 0 e (init env)))

------------------------------------------------------------------------
-- Degenerate-divisor folding preserves `eval-arith-W` (Part A soundness).
--
-- The `normalize` pre-pass (used by the per-arch `emit-arith-block`) is
-- meaning-preserving: `eval-arith-W (normalize e) ≡ eval-arith-W e`. Every
-- fold is discharged by the corresponding `Once.Word` identity (no
-- postulates). The `negOne`/in-range facts need bits ≥ 1, supplied as
-- `bits ≡ suc b`; each arch instantiates it (64 = suc 63, 32 = suc 31).
------------------------------------------------------------------------

module _ (b : ℕ) (eqb : bits ≡ suc b) where

  -- every arith value lands in `[0, modulus)` (needed for `/ˢ negOne = ⊝`).
  eval-in-range : ∀ {sh} (e : MArithIR sh NInt) (env : ⟦ sh ⟧S) → eval-arith-W e env < modulus
  eval-in-range (alit z)   env = fromℤ-in-range z
  eval-in-range (ainput p) env with project _ p env
  ... | just z  = fromℤ-in-range z
  ... | nothing = fromℤ-in-range (+ 0)
  eval-in-range (aadd a c) env = m%n<n _ modulus
  eval-in-range (asub a c) env = m%n<n _ modulus
  eval-in-range (amul a c) env = m%n<n _ modulus
  eval-in-range (adiv a c) env =
    /ˢ-in-range b eqb (eval-arith-W a env) (eval-arith-W c env)
  eval-in-range (amod a c) env =
    %ˢ-in-range b eqb (eval-arith-W a env) (eval-arith-W c env) (eval-in-range a env)
  eval-in-range (aneg a)   env = m%n<n _ modulus

  -- single-node folds (the `alit 0 / alit -1` divisor cases); every other
  -- divisor is left untouched (`fold-div a c = adiv a c`, `refl`).
  fold-div-preserves : ∀ {sh} (a c : MArithIR sh NInt) (env : ⟦ sh ⟧S) →
    eval-arith-W a env < modulus →
    eval-arith-W (fold-div a c) env ≡ eval-arith-W (adiv a c) env
  fold-div-preserves a (alit (+ 0)) env _ =
    trans (fromℤ-neg1 b eqb)
          (trans (sym (/ˢ-zero (eval-arith-W a env)))
                 (cong (eval-arith-W a env /ˢ_) (sym fromℤ-0)))
  fold-div-preserves a (alit (-[1+ 0 ])) env a<mod =
    sym (trans (cong (eval-arith-W a env /ˢ_) (fromℤ-neg1 b eqb))
               (/ˢ-negOne b eqb (eval-arith-W a env) a<mod))
  fold-div-preserves a (alit (+ (suc _)))     env _ = refl
  fold-div-preserves a (alit (-[1+ suc _ ]))  env _ = refl
  fold-div-preserves a (ainput _) env _ = refl
  fold-div-preserves a (aadd _ _) env _ = refl
  fold-div-preserves a (asub _ _) env _ = refl
  fold-div-preserves a (amul _ _) env _ = refl
  fold-div-preserves a (adiv _ _) env _ = refl
  fold-div-preserves a (amod _ _) env _ = refl
  fold-div-preserves a (aneg _)   env _ = refl

  fold-mod-preserves : ∀ {sh} (a c : MArithIR sh NInt) (env : ⟦ sh ⟧S) →
    eval-arith-W (fold-mod a c) env ≡ eval-arith-W (amod a c) env
  fold-mod-preserves a (alit (+ 0)) env =
    trans (sym (%ˢ-zero (eval-arith-W a env)))
          (cong (eval-arith-W a env %ˢ_) (sym fromℤ-0))
  fold-mod-preserves a (alit (-[1+ 0 ])) env =
    trans fromℤ-0
          (trans (sym (%ˢ-negOne b eqb (eval-arith-W a env)))
                 (cong (eval-arith-W a env %ˢ_) (sym (fromℤ-neg1 b eqb))))
  fold-mod-preserves a (alit (+ (suc _)))    env = refl
  fold-mod-preserves a (alit (-[1+ suc _ ])) env = refl
  fold-mod-preserves a (ainput _) env = refl
  fold-mod-preserves a (aadd _ _) env = refl
  fold-mod-preserves a (asub _ _) env = refl
  fold-mod-preserves a (amul _ _) env = refl
  fold-mod-preserves a (adiv _ _) env = refl
  fold-mod-preserves a (amod _ _) env = refl
  fold-mod-preserves a (aneg _)   env = refl

  normalize-preserves : ∀ {sh} (e : MArithIR sh NInt) (env : ⟦ sh ⟧S) →
    eval-arith-W (normalize e) env ≡ eval-arith-W e env
  normalize-preserves (alit z)   env = refl
  normalize-preserves (ainput p) env = refl
  normalize-preserves (aadd a c) env =
    cong₂ _⊕_ (normalize-preserves a env) (normalize-preserves c env)
  normalize-preserves (asub a c) env =
    cong₂ _⊖_ (normalize-preserves a env) (normalize-preserves c env)
  normalize-preserves (amul a c) env =
    cong₂ _⊗_ (normalize-preserves a env) (normalize-preserves c env)
  normalize-preserves (aneg a)   env = cong ⊝_ (normalize-preserves a env)
  normalize-preserves (adiv a c) env =
    trans (fold-div-preserves (normalize a) (normalize c) env
             (eval-in-range (normalize a) env))
          (cong₂ _/ˢ_ (normalize-preserves a env) (normalize-preserves c env))
  normalize-preserves (amod a c) env =
    trans (fold-mod-preserves (normalize a) (normalize c) env)
          (cong₂ _%ˢ_ (normalize-preserves a env) (normalize-preserves c env))
