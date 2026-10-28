-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.OptimizePreserves — ONE OPTIMIZER PASS KEEPS THE RUN
-- (plan 0.39 A2).
--
-- `optimize-once` rewrites the IR by categorical laws. The IR means `T∞` runs,
-- compared step for step (`RelS`) under the value relation (`RelD`), so the
-- statement is a logical relation, as for the arith pass
-- (`Adequacy.RewritePreserves`): the optimized term at a call environment and
-- the original at a related one take related inputs to related runs.
--
-- Most rules keep the run as it is (identities, η, a case on a known
-- injection): the monad laws. Three drop a sub-term (`terminal ∘ f`,
-- `fst`/`snd ∘ ⟨ g , h ⟩`, a pure map into `Unit`); the optimizer drops one only
-- when `has-effect?` says it has none, and such a term returns at once
-- (`OptimizeQuiet.quiet-now`), so the run loses no step. The guard is read on
-- the OPTIMIZED sub-term; the original's run is related to it step for step,
-- so it returns at once too (`now-rel`).
------------------------------------------------------------------------

module Once.Adequacy.OptimizePreserves where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR
open import Once.IRTy using (IRTy; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute; _≟IRTy_; fits-int; fits-float)
import Once.IRTy as II
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Type.DecEq using (_≟T_)
open import Once.IR.Semantics.Trace using (T; ret; call; halt)
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_; bindBlock; fmap∞; module T∞;
  TreeEq∞; module TreeEq∞; BlockEq; ret≈; call≈; halt≈; StepEq; done≈; next≈)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; cata-ev-algᴰ; module CallEnv)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; coerce-functor-D; coerce-functor⁻¹-D)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; s-next; s-call; s-halt;
  RelS-bind; relS-ret; RelS-iter∞; RelS-≈ˡ; RelS-≈ʳ; ≈∞-idˡ; ≈∞-idʳ; ≈∞-sym; ≈∞-reflB)
open import Once.Denotation.ValueRel
open import Once.Denotation.EvalRel using (fo-eq; RelS-now; RelEnv; sigop-rel)
open import Once.IR.Semantics.StreamInf using (anaFᴵ; in-νᴵ; module νᴵ)
open import Once.IR.Semantics.FunctorMeaning using (translateF)
import Once.Type.Concrete as LW
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using () renaming (⟦_⟧F to ⟦_⟧F′)
open import Once.Semantics.Machine using (coerce-ν-out; coerce-ν-in)
open import Once.Optimize
open import Once.Adequacy.OptimizeQuiet using (Now; now; value; is; quiet-now)

open T∞ using (force)
open TreeEq∞ using (force≈)
open RelS using (forceS)
open νᴵ using (forceᴵ)

------------------------------------------------------------------------
-- Runs that return at once
------------------------------------------------------------------------

-- | Lockstep: a run related to one that returns at once returns at once, with
-- a related value.
now-rel : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {m′ : T∞ Y} → RelS R m m′ → (n : Now m)
        → Σ (Now m′) (λ n′ → R (value n) (value n′))
now-rel {Y = Y} {R = R} {m′ = m′} h (now v e) = fin (go (forceS h) e)
  where
    go : ∀ {l l′} → RelSB R l l′ → l ≡ ret (inj₁ v) → Σ Y (λ y → (l′ ≡ ret (inj₁ y)) × R v y)
    go (s-ret {y = y} r) refl = y , refl , r
    go (s-next _) ()
    go (s-call _) ()
    go s-halt     ()
    fin : Σ Y (λ y → (force m′ ≡ ret (inj₁ y)) × R v y) → Σ (Now m′) (λ n′ → R v (value n′))
    fin (y , e′ , r) = now y e′ , r

private
  -- a bind on a run that returns at once is its continuation
  now-seq : ∀ {Y Z} {n : T∞ Y} (nn : Now n) (k : Y → T∞ Z) → TreeEq∞ _≡_ (n >>=∞ k) (k (value nn))
  force≈ (now-seq {n = n} (now v e) k) =
    subst (λ l → BlockEq (StepEq _≡_ (TreeEq∞ _≡_)) (bindBlock l k) (force (k v))) (sym e)
          (≈∞-reflB (λ _ → refl) (force (k v)))

  sym≡ : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  sym≡ = sym

  -- pairing a run with one that returns at once, then projecting: the run
  pair-fst≈  : ∀ {Y Z} (m : T∞ Y) {n : T∞ Z} (nn : Now n)
             → TreeEq∞ _≡_ (fmap∞ proj₁ (m >>=∞ λ b → n >>=∞ λ c → return∞ (b , c))) m
  pair-fst≈B : ∀ {Y Z} (l : T (Y ⊎ T∞ Y)) {n : T∞ Z} (nn : Now n)
             → BlockEq (StepEq _≡_ (TreeEq∞ _≡_))
                 (bindBlock (bindBlock l (λ b → n >>=∞ λ c → return∞ (b , c))) (λ p → return∞ (proj₁ p))) l
  force≈ (pair-fst≈ m nn) = pair-fst≈B (force m) nn
  pair-fst≈B (ret (inj₁ b)) {n} (now c e) =
    subst (λ l → BlockEq (StepEq _≡_ (TreeEq∞ _≡_))
                   (bindBlock (bindBlock l (λ c′ → return∞ (b , c′))) (λ p → return∞ (proj₁ p))) (ret (inj₁ b)))
          (sym e) (ret≈ (done≈ refl))
  pair-fst≈B (ret (inj₂ m)) nn = ret≈ (next≈ (pair-fst≈ m nn))
  pair-fst≈B (call o a k)   nn = call≈ (λ b → pair-fst≈B (k b) nn)
  pair-fst≈B (halt o a)     nn = halt≈

  -- …and the other way: the run that does not return at once
  ret-proj≈  : ∀ {Y Z} (b : Y) (n : T∞ Z)
             → TreeEq∞ _≡_ ((n >>=∞ λ c → return∞ (b , c)) >>=∞ λ p → return∞ (proj₂ p)) n
  ret-proj≈B : ∀ {Y Z} (b : Y) (l : T (Z ⊎ T∞ Z))
             → BlockEq (StepEq _≡_ (TreeEq∞ _≡_)) (bindBlock (bindBlock l (λ c → return∞ (b , c))) (λ p → return∞ (proj₂ p))) l
  force≈ (ret-proj≈ b n) = ret-proj≈B b (force n)
  ret-proj≈B b (ret (inj₁ c)) = ret≈ (done≈ refl)
  ret-proj≈B b (ret (inj₂ m)) = ret≈ (next≈ (ret-proj≈ b m))
  ret-proj≈B b (call o a k)   = call≈ (λ x → ret-proj≈B b (k x))
  ret-proj≈B b (halt o a)     = halt≈

  pair-snd≈ : ∀ {Y Z} {m : T∞ Y} (mm : Now m) (n : T∞ Z)
            → TreeEq∞ _≡_ (fmap∞ proj₂ (m >>=∞ λ b → n >>=∞ λ c → return∞ (b , c))) n
  force≈ (pair-snd≈ {m = m} (now b e) n) =
    subst (λ l → BlockEq (StepEq _≡_ (TreeEq∞ _≡_))
                   (bindBlock (bindBlock l (λ b′ → n >>=∞ λ c → return∞ (b′ , c))) (λ p → return∞ (proj₂ p))) (force n))
          (sym e) (force≈ (ret-proj≈ b n))

  ∨-split : ∀ a {b} → a ∨ b ≡ false → a ≡ false × b ≡ false
  ∨-split false e = refl , e
  ∨-split true  ()
