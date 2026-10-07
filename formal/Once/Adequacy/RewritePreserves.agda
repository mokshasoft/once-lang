-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.RewritePreserves — THE ARITH LIFTING PRESERVES A PROGRAM'S
-- MEANING (D165, restated at the meaning in plan 0.103 6a″).
--
-- `rewrite-ir` replaces a recognised closed arithmetic subtree by one
-- `arith.block.<digest>` SigOp and otherwise walks the IR. Every IR former's
-- meaning is a function of its children's (`evalᴰ` is compositional), so the
-- walk preserves meaning by induction; a lifted block means the subtree it
-- replaced (`lift-sound`); and the program's table, rewritten entry by entry,
-- is the same call environment.
------------------------------------------------------------------------

module Once.Adequacy.RewritePreserves where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Postulates using (extensionality)
import Once.Adequacy.LiftSound
open import Once.Target.Arch using (TargetNum)
open import Once.IR
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.IRTy using (_≟IRTy_)
open import Relation.Nullary using (yes; no)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Arith.Machine.Rewrite using (rewrite-ir; rw-at; walk; try-lift; bare-at)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Denotation.TraceMonad using (>>=T-identityˡ)
open import Once.Denotation.TraceMonad using (T; _>>=T_; returnT; projTrace; Interp; pureHalf)
open import Once.SigOp.Info using (FFIAnswers)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; callEnv; cata-ev-algᴰ)
open import Once.Denotation.Program using (IRFun; fname; fdom; fcod; fbody; table; main; tableEnv; tableCalls; tableEnv-at)
open import Once.Semantics.Machine
open import Once.Denotation.ValueDomain
import Once.Denotation.DenotTrace
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Denotation.TraceMonad using (fmapT)
open import Once.Denotation.Behavior using ()
open Once.Denotation.Behavior.Behavior using (at)
open import Once.Adequacy.SourceTrace using (⟦_⟧IR)
open import Once.Compile using (rewrite-program; rewrite-table; rewrite-fun)

-- A lifted arith block means the subtree it replaced (`LiftSound`).
lift-sound : ∀ (fmt : TargetNum) (ρ : CallEnv) {A B} (ir ir′ : IR A B) (blk : ArithBlock)
           → try-lift ir ≡ just (ir′ , blk) → evalᴰ fmt ρ ir′ ≡ evalᴰ fmt ρ ir
lift-sound fmt ρ = LS.lift-sound
  where module LS = Once.Adequacy.LiftSound fmt ρ

------------------------------------------------------------------------
-- The walk preserves meaning
------------------------------------------------------------------------

module _ (fmt : TargetNum) (ρ : CallEnv) where
  private
    E : ∀ {A B} → IR A B → _
    E = evalᴰ fmt ρ

  rewrite-sound : ∀ {A B} (ir : IR A B) → E (proj₁ (rewrite-ir ir)) ≡ E ir
  rw-at-sound   : ∀ {A B} (ir : IR A B) (d : Maybe (IR A B × ArithBlock)) → try-lift ir ≡ d
                → E (proj₁ (rw-at ir d)) ≡ E ir
  walk-sound    : ∀ {A B} (ir : IR A B) → E (proj₁ (walk ir)) ≡ E ir

  -- Plan 0.108: a bare primitive is lifted as `SigOp si ∘ id`, which means
  -- `SigOp si` by the monad's left identity.
  bare-sound : ∀ {X Y} (si : SigOpInfo X Y) (d : Maybe (IR ⌊ X ⌋ ⌊ Y ⌋ × ArithBlock))
             → try-lift (SigOp si ∘ id) ≡ d → E (proj₁ (bare-at si d)) ≡ E (SigOp si)
  bare-sound si (just (ir′ , blk)) eq =
    trans (lift-sound fmt ρ (SigOp si ∘ id) ir′ blk eq)
          (extensionality λ a → >>=T-identityˡ a (E (SigOp si)))
  bare-sound si nothing eq = refl

  rewrite-sound ir = rw-at-sound ir (try-lift ir) refl

  rw-at-sound ir (just (ir′ , blk)) eq = lift-sound fmt ρ ir ir′ blk eq
  rw-at-sound ir nothing           eq = walk-sound ir

  walk-sound id       = refl
  walk-sound (g ∘ f)  = extensionality λ a →
    cong₂ (λ X Y → X a >>=T Y) (rewrite-sound f) (rewrite-sound g)
  walk-sound fst      = refl
  walk-sound snd      = refl
  walk-sound ⟨ f , g ⟩ = extensionality λ a →
    cong₂ (λ X Y → X a >>=T λ b → Y a >>=T λ c → returnT (b , c)) (rewrite-sound f) (rewrite-sound g)
  walk-sound inl      = refl
  walk-sound inr      = refl
  walk-sound (case f g) = extensionality λ
    { (inj₁ a) → cong (λ X → X a) (rewrite-sound f)
    ; (inj₂ b) → cong (λ X → X b) (rewrite-sound g) }
  walk-sound terminal = refl
  walk-sound initial  = extensionality λ ()
  walk-sound (curry f) = extensionality λ a →
    cong (λ X → returnT (λ b → X (a , b))) (rewrite-sound f)
  walk-sound apply    = refl
  walk-sound (In w)   = refl
  walk-sound (out-μ w) = refl
  walk-sound (Cata {F} w {E′} {C} alg) = extensionality λ a →
    cong (λ X → sem-cata (wf-⌈⌉ w) X (proj₂ a)) (alg≡ (proj₁ a))
    where
      alg≡ : ∀ env → cata-ev-algᴰ fmt ρ {F} {E′} {C} w (proj₁ (rewrite-ir alg)) env ≡ cata-ev-algᴰ fmt ρ {F} {E′} {C} w alg env
      alg≡ env = extensionality λ fc →
        cong (λ X → seqF ⌈ F ⌉F fc >>=T λ layer →
                      X (env , subst (λ Ty → ⟦ Ty ⟧ᴰ) (sym (⌈⟧TI-commute F C)) (coerce-functor⁻¹-D (wf-⌈⌉ w) ⌈ C ⌉ layer)))
             (rewrite-sound alg)
  walk-sound (Out w)  = refl
  walk-sound (in-ν w) = refl
  walk-sound (Ana {F} w {E′} {A′} c) = extensionality λ a →
    cong (λ X → returnT (anaFᵈ ⌈ F ⌉F
                           (λ a′ → fmapT (λ x → coerce-functor-D (wf-⌈⌉ w) ⌈ A′ ⌉
                                                  (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute F A′) x))
                                         (X (proj₁ a , a′)))
                           (proj₂ a)))
         (rewrite-sound c)
  walk-sound (const p v) = refl
  walk-sound (SigOp si)  = bare-sound si (try-lift (SigOp si ∘ id)) refl
  walk-sound (Call f)    = refl

------------------------------------------------------------------------
-- The rewritten table is the same call environment
------------------------------------------------------------------------

calls-sound : ∀ (fmt : TargetNum) (φ : FFIAnswers) (tbl : List IRFun)
            → tableCalls fmt φ (rewrite-table tbl) ≡ tableCalls fmt φ tbl
calls-sound fmt φ []       = refl
calls-sound fmt φ (e ∷ es) =
  extensionality λ f → extensionality λ A → extensionality λ B → extensionality λ a →
    at-sound f A B (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) a
  where
    ih  = calls-sound fmt φ es
    ihE : tableEnv fmt φ (rewrite-table es) ≡ tableEnv fmt φ es
    ihE = cong (λ c → callEnv c φ) ih
    at-sound : ∀ f A B d₁ d₂ d₃ a
             → tableEnv-at fmt φ (rewrite-fun e) (rewrite-table es) f A B d₁ d₂ d₃ a ≡ tableEnv-at fmt φ e es f A B d₁ d₂ d₃ a
    at-sound f A B (yes _) (yes p) (yes q) a =
      cong (subst (λ Y → T (Once.Denotation.DenotTrace.⟦_⟧ᴰᴵ Y)) q)
        (trans (cong (λ ρ → evalᴰ fmt ρ (proj₁ (rewrite-ir (fbody e))) _) ihE)
               (cong (λ X → X _) (rewrite-sound fmt (tableEnv fmt φ es) (fbody e))))
    at-sound f A B (yes _) (yes _) (no _)  a = cong (λ c → c f A B a) ih
    at-sound f A B (yes _) (no _)  _       a = cong (λ c → c f A B a) ih
    at-sound f A B (no _)  _       _       a = cong (λ c → c f A B a) ih

table-sound : ∀ (fmt : TargetNum) (φ : FFIAnswers) (tbl : List IRFun) → tableEnv fmt φ (rewrite-table tbl) ≡ tableEnv fmt φ tbl
table-sound fmt φ tbl = cong (λ c → callEnv c φ) (calls-sound fmt φ tbl)

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

rewrite-program-preserves : ∀ (fmt : TargetNum) (ι : Interp) (p : Once.Denotation.Program.IRProgram) (n : ℕ)
                          → at (⟦ just (rewrite-program p) ⟧IR fmt ι) n ≡ at (⟦ just p ⟧IR fmt ι) n
rewrite-program-preserves fmt ι p n =
  cong (λ t → projTrace ι t n)
    (trans (cong (λ ρ → evalᴰ fmt ρ (proj₁ (rewrite-ir (main p))) _) (table-sound fmt (pureHalf ι) (table p)))
           (cong (λ X → X _) (rewrite-sound fmt (tableEnv fmt (pureHalf ι) (table p)) (main p))))
