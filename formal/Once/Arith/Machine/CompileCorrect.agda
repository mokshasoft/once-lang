-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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

module Once.Arith.Machine.CompileCorrect (bits : ℕ) where

open import Data.Nat using (zero; suc; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (<⇒≢; ≤-refl; m≤n⇒m≤1+n)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_)

open import Once.Arith.Machine.AbsState
  using (ArithAbsState; InputShape; ⟦_⟧S; init; output-of; InputPath; project;
         Store; empty-store; _[_↦_]; _[_]; store-write-same; store-write-other)
open import Once.Arith.Machine.AbsInstr
  using (AbstractInstr; load-input; load-imm; add-rrr; sub-rrr; mul-rrr;
         neg-rr; spill; reload; move-to-out;
         maybe-zero; bin-op; un-op; module Exec)
open Exec bits using (step; run-abstract)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; ainput; aadd; asub; amul; aneg; eval-arith)
open import Once.Word using (module Width)
open Width bits using (fromℤ; _⊕_; _⊖_; _⊗_; ⊝_)
open import Once.Arith.Machine.WordSem using (module Sem)
open Sem bits using (eval-arith-W)
open import Once.Arith.Machine.Compile using (compile-go; compile-abs)
open ArithAbsState

------------------------------------------------------------------------
-- Strong invariant on `compile-go`
------------------------------------------------------------------------

record CompileGoInv {sh} (d : ℕ) (e : MArithIR sh) (s : ArithAbsState sh) : Set where
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
  eval-arith-W {sh} (ainput p) inp ≡ fromℤ (maybe-zero (project sh p inp))
eval-arith-W-ainput {sh} p inp with project sh p inp
... | just _  = refl
... | nothing = refl

compile-go-correct-ainput : ∀ {sh} (d : ℕ) (p : InputPath) (s : ArithAbsState sh) →
  CompileGoInv d (ainput p) s
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

compile-go-correct : ∀ {sh} (d : ℕ) (e : MArithIR sh) (s : ArithAbsState sh) →
  CompileGoInv d e s

aneg-correct : ∀ {sh} (d : ℕ) (a : MArithIR sh) (s : ArithAbsState sh) →
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

aadd-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh) (s : ArithAbsState sh) →
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

asub-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh) (s : ArithAbsState sh) →
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

amul-correct : ∀ {sh} (d : ℕ) (a b : MArithIR sh) (s : ArithAbsState sh) →
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

    bridge : run-abstract (compile-go d (amul a b)) s ≡ s5
    bridge = trans
      (run-abstract-app (compile-go d a)
        (spill 0 d ∷ compile-go (suc d) b ++ (reload d 1 ∷ mul-rrr 0 1 0 ∷ [])) s)
      (run-abstract-app (compile-go (suc d) b)
        (reload d 1 ∷ mul-rrr 0 1 0 ∷ []) s2)

    scratch-s3-d : scratch s3 [ d ] ≡ regs s1 [ 0 ]
    scratch-s3-d = trans (scratch≤ ih-b d ≤-refl)
                         (store-write-same (scratch s1) d (regs s1 [ 0 ]))

    regs-s3-0 : regs s3 [ 0 ] ≡ just (eval-arith-W b (input s))
    regs-s3-0 = trans (reg0 ih-b)
                      (cong (λ x → just (eval-arith-W b x)) (input-eq ih-a))

compile-go-correct d (alit z) s = record
  { reg0      = refl
  ; scratch≤  = λ _ _ → refl
  ; input-eq  = refl
  ; output-eq = refl
  }
compile-go-correct {sh} d (ainput p) s = compile-go-correct-ainput {sh} d p s
compile-go-correct d (aneg a)   s = aneg-correct d a s
compile-go-correct d (aadd a b) s = aadd-correct d a b s
compile-go-correct d (asub a b) s = asub-correct d a b s
compile-go-correct d (amul a b) s = amul-correct d a b s

------------------------------------------------------------------------
-- Block validity: `output-of (run-abstract (compile-abs e) (init env))`
------------------------------------------------------------------------

abs-validity : ∀ {sh} (e : MArithIR sh) (env : ⟦ sh ⟧S) →
  output-of (run-abstract (compile-abs e) (init env)) ≡ just (eval-arith-W e env)
abs-validity {sh} e env =
  trans (cong output-of (run-abstract-app (compile-go 0 e) (move-to-out 0 ∷ []) (init env)))
        (reg0 (compile-go-correct 0 e (init env)))
