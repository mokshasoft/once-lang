-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.MainExtract — the source meaning of a compiled `main`
-- (Plan 0.49 Phase 1: the SD bridge, assembled).
--
-- `moduleToIR m` is the compiled `main` IR — the entry-wrapped elaboration
-- of `main`'s (resolved) intrinsic surface term `seR`:
--
--     moduleToIR m ≡ just (wrapMainAsEntry (elaborate Heap seR))      -- main-ir-form
--
-- From that ONE plumbing fact, the INDEPENDENT surface meaning of `main`
-- (its `SD.⟦_⟧ˢ` run) equals the compiled IR's denotational trace `⟦_⟧IR`:
--
--     ⟦ just ir ⟧IR  ≋  runMainˢ seR
--
-- via `wrap-trace` (the entry-wrap denotation lemma) ∘ `faithful` (the proven
-- elaborator-faithfulness). This is where row-2 (`elaborate`) is genuinely
-- FORCED — `faithful` is load-bearing here.
--
-- `main-ir-form` is the single remaining NAMED gap: that `moduleToIR` extracts
-- exactly the entry-wrapped elaboration of `main`'s resolved term. It threads
-- through `findMain`/`compileResolvedModule` (the `MainBuilds`/`AcceptSound`
-- plumbing pattern); it is TRUE and codegen-structural, not a trust axiom.
------------------------------------------------------------------------

module Once.Adequacy.MainExtract where

open import Data.Nat using (ℕ)
open import Data.List using (List; _++_; take)
open import Data.Maybe using (just)
open import Data.Unit using (tt)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

open import Once.Type using (Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.Surface.Elaborate using (elaborate)
import Once.Compile as C
import Once.Parser.Module.Core as P
open import Once.Denotation.Behavior using (Behavior)
open import Once.Adequacy.SourceTrace using (moduleToIR; ⟦_⟧IR)
open import Once.Adequacy.WrapBridge using (wrap-trace)
open import Once.Adequacy.SourceFaithful using (faithful)
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace)
open import Once.Denotation.DenotTrace using (evalᴰ)

EffUU : _
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

-- Run an `Eff Unit Unit` action's INDEPENDENT surface denotation to a
-- Behavior: apply the closure `SD.⟦ se ⟧ˢ tt` to the Unit input, read the
-- depth-`n` SigOp-trace prefix. Mirrors `⟦_⟧IR` but through `SD`.
runMainˢ : ∀ {Ψ : Usage 0} → Expr ∅ Ψ EffUU → Behavior
runMainˢ se n = take n (projTrace (SD.⟦ se ⟧ˢ tt >>=T (λ clo → clo tt)) n)

-- Bind respects pointwise equality of the bound computation, at the trace level.
bind-cong-trace : ∀ {X Y} (m m′ : T X) (f : X → T Y) (n : ℕ) →
  m n ≡ m′ n → projTrace (m >>=T f) n ≡ projTrace (m′ >>=T f) n
bind-cong-trace m m′ f n eq = cong (λ p → proj₁ p ++ proj₁ (f (proj₂ p) n)) eq

-- DISCHARGED (no longer a postulate): the compiled `main` IR is the entry-wrap
-- of the elaborated resolved term — proven in `Once.Adequacy.MainIRForm` by the
-- value-tracking induction over `compileAllFuns-go` + `findMain`.
open import Once.Adequacy.MainForm using (main-ir-form; Form)

-- THE SD bridge: the compiled `main` IR's denotational trace equals the
-- INDEPENDENT surface meaning of `main`. Proven from `main-ir-form` (plumbing)
-- + `wrap-trace` (proven) + `faithful` (proven) + `bind-cong-trace`.
-- Top-level aux over the (strengthened, Plan 0.55) `Form` — extra payload
-- fields ignored here, same `seR`. Routing through this top-level helper (rather
-- than an inline `with main-ir-form …`) keeps `source-meaningᴰ m ir mi`
-- reducible to `source-meaningᴰ-aux ir (main-ir-form m ir mi)`, so
-- `MainRealizeAgrees.main-extract` can `with main-ir-form m ir mi` and share the
-- abstracted value with this call (recovering `seR`).
source-meaningᴰ-aux : ∀ (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Form ir →
  Σ-syntax (Usage 0) (λ Ψ →
    Σ-syntax (Expr ∅ Ψ EffUU) (λ seR →
      ∀ (n : ℕ) → ⟦ just ir ⟧IR n ≡ runMainˢ seR n))
source-meaningᴰ-aux ir (Ψ , seR , eq , _) = Ψ , seR , bridge
  where
    bridge : ∀ (n : ℕ) → ⟦ just ir ⟧IR n ≡ runMainˢ seR n
    bridge n =
      trans (cong (λ X → ⟦ just X ⟧IR n) eq)
        (trans (cong (take n) (wrap-trace (elaborate C.Heap seR) n))
               (cong (take n)
                 (bind-cong-trace (evalᴰ (elaborate C.Heap seR) tt)
                                  (SD.⟦ seR ⟧ˢ tt) (λ clo → clo tt) n
                                  (faithful seR tt n))))

source-meaningᴰ : ∀ (m : P.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) →
  moduleToIR m ≡ just ir →
  Σ-syntax (Usage 0) (λ Ψ →
    Σ-syntax (Expr ∅ Ψ EffUU) (λ seR →
      ∀ (n : ℕ) → ⟦ just ir ⟧IR n ≡ runMainˢ seR n))
source-meaningᴰ m ir mi = source-meaningᴰ-aux ir (main-ir-form m ir mi)
