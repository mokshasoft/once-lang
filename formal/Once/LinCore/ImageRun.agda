-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageRun — plan 0.146 B1.4a: running an image.
--
-- A16's steps, with a RETURN STACK in place of the inlined continuation:
--
--   * `call κ` opens a frame (a temporary, D407, as A16's `enter`) and runs
--     κ's block, its continuation pushed; reaching `end` returns (the frame
--     closed, as A16's `leave`);
--   * a loop's round runs with its continuation pushed silently (no frame:
--     A16 expands it inline);
--   * the code-word instructions dispatch on the cell's `Lam` (or its ν's
--     contents): each calls the trampoline the cell names (D417), which
--     does the cell's part and calls the block, as the flat run does.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.ImageRun
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_; fsz)
open import Once.LinCore.Image fmt ans bw

------------------------------------------------------------------------
-- 1. THE RETURN STACK: what runs when the current code ends.
------------------------------------------------------------------------

infixr 5 _∷ⁱ_
data Ret : Sh → Sh → Set where
  []ʳ  : ∀ {T} → Ret T T
  -- ★ a call's (D415): the caller's continuation and its configuration below
  -- the argument; the callee's frame closes when it is resumed
  frm  : ∀ {t Es B S U T} → Codeᴵ (t ⊳ Es ∣ B ∷ S) U → Slots (t ⊳ Es) → Stk S → Ret U T
       → Ret (t ⊳ [] ∣ B ∷ []) T
  -- a loop's: no frame
  _∷ⁱ_ : ∀ {sh U T} → Codeᴵ sh U → Ret U T → Ret sh T

------------------------------------------------------------------------
-- 2. ONE STEP.
------------------------------------------------------------------------

data StepI {T : Sh} : ∀ {sh U sh′ U′} → Codeᴵ sh U → Ret U T → Cfg sh → ℕ → Trace
                    → Codeᴵ sh′ U′ → Ret U′ T → Cfg sh′ → ℕ → Set where
  i-unpair : ∀ {Es A B S U} {k : Codeᴵ (Es ∣ A ∷ B ∷ S) U} {r : Ret U T} {es} {a : MV A} {b : MV B} {os n}
           → StepI (unpair ⨾ k) r (es ∥ mpair a b ∷ˢ os) n [] k r (es ∥ a ∷ˢ b ∷ˢ os) n
  i-pair   : ∀ {Es A B S U} {k : Codeᴵ (Es ∣ (A ⊗t B) ∷ S) U} {r : Ret U T} {es} {a : MV A} {b : MV B} {os n}
           → StepI (pair ⨾ k) r (es ∥ a ∷ˢ b ∷ˢ os) n [] k r (es ∥ mpair a b ∷ˢ os) n
  i-swap   : ∀ {Es A B S U} {k : Codeᴵ (Es ∣ B ∷ A ∷ S) U} {r : Ret U T} {es} {a : MV A} {b : MV B} {os n}
           → StepI (swap ⨾ k) r (es ∥ a ∷ˢ b ∷ˢ os) n [] k r (es ∥ b ∷ˢ a ∷ˢ os) n
  i-unit   : ∀ {Es S U} {k : Codeᴵ (Es ∣ One ∷ S) U} {r : Ret U T} {es os n}
           → StepI (unit ⨾ k) r (es ∥ os) n [] k r (es ∥ mone ∷ˢ os) n
  i-prim   : ∀ {Γ} {ds : Defs Γ} {Es A B S U} {g : LTm Γ A B} {k : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es v w os n n′ t}
           → Run ds g mone v n (gives w n′) t → StepI (prim ds g ⨾ k) r (es ∥ v ∷ˢ os) n t k r (es ∥ w ∷ˢ os) n′
  -- an op whose block ends: the image stops there
  i-opend  : ∀ {Γ} {ds : Defs Γ} {Es} {s : Sig} {S U} {k : Codeᴵ (Es ∣ ⌜ scod s ⌝ ∷ S) U} {r : Ret U T} {es}
               {x : MV ⌜ sdom s ⌝} {os n t w}
           → OpPath (opF s (toF (sdom s) (er x))) t (inj₂ w)
           → StepI (prim ds (lop s) ⨾ k) r (es ∥ x ∷ˢ os) n t halted r (es ∥ os) n
  i-untag  : ∀ {Es l X A S U} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) U} {r : Ret U T} {es} {x : MV X} {a : MV A} {os n}
           → StepI (untag {l = l} ⨾ k) r (es ∥ mpair (mct x) a ∷ˢ os) n [] k r (es ∥ mpair x a ∷ˢ os) n
  i-untag₁ : ∀ {Es l X S U} {k : Codeᴵ (Es ∣ X ∷ S) U} {r : Ret U T} {es} {x : MV X} {os n}
           → StepI (untag₁ {l = l} ⨾ k) r (es ∥ mct x ∷ˢ os) n [] k r (es ∥ x ∷ˢ os) n
  i-tag₁   : ∀ {Es l X S U} {k : Codeᴵ (Es ∣ Ct l X ∷ S) U} {r : Ret U T} {es} {x : MV X} {os n}
           → StepI (tag₁ ⨾ k) r (es ∥ x ∷ˢ os) n [] k r (es ∥ mct x ∷ˢ os) n
  i-case₁  : ∀ {Es A B S U} {c₁ : Codeᴵ (Es ∣ A ∷ S) U} {c₂ : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es a os n}
           → StepI (case c₁ c₂) r (es ∥ minl a ∷ˢ os) n [] c₁ r (es ∥ a ∷ˢ os) n
  i-case₂  : ∀ {Es A B S U} {c₁ : Codeᴵ (Es ∣ A ∷ S) U} {c₂ : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es b os n}
           → StepI (case c₁ c₂) r (es ∥ minr b ∷ˢ os) n [] c₂ r (es ∥ b ∷ˢ os) n
  i-elend  : ∀ {E Es X A S U} {k : Codeᴵ ((E ⊗t X) ∷ E ∷ Es ∣ A ∷ S) U} {r : Ret U T} {es : Slots (E ∷ Es)} {x : MV X} {a : MV A} {os n}
           → StepI (elend ⨾ k) r (es ∥ mpair x a ∷ˢ os) n [] k r (ln (see es) x es ∥ a ∷ˢ os) n
  i-eunlend : ∀ {E Es X B S U} {k : Codeᴵ (E ∷ Es ∣ (X ⊗t B) ∷ S) U} {r : Ret U T} {e : MV E} {es : Slots (E ∷ Es)}
                {x : MV X} {w : MV B} {os n}
           → StepI (eunlend ⨾ k) r (ln e x es ∥ w ∷ˢ os) n [] k r (es ∥ mpair x w ∷ˢ os) n
  i-elift  : ∀ {Es S U} {k : Codeᴵ (One ∷ Es ∣ S) U} {r : Ret U T} {es os n}
           → StepI (elift ⨾ k) r (es ∥ os) n [] k r (vw mone es ∥ os) n
  i-efst   : ∀ {E₁ E₂ Es S U} {k : Codeᴵ (E₁ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S) U} {r : Ret U T} {e₁ : MV E₁} {e₂ : MV E₂} {es os n}
           → see es ≡ mpair e₁ e₂ → StepI (efst ⨾ k) r (es ∥ os) n [] k r (vw e₁ es ∥ os) n
  i-esnd   : ∀ {E₁ E₂ Es S U} {k : Codeᴵ (E₂ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S) U} {r : Ret U T} {e₁ : MV E₁} {e₂ : MV E₂} {es os n}
           → see es ≡ mpair e₁ e₂ → StepI (esnd ⨾ k) r (es ∥ os) n [] k r (vw e₂ es ∥ os) n
  i-eout   : ∀ {F Es S U} {k : Codeᴵ (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S) U} {r : Ret U T} {i v} {es : Slots (μt F ∷ Es)} {os n}
           → see es ≡ mmu i v → StepI (eout ⨾ k) r (es ∥ os) n (peek i ∷ []) k r (vw v es ∥ os) n
  i-eoutq  : ∀ {F Es S U} {k : Codeᴵ (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S) U} {r : Ret U T} {i v} {es : Slots (μt F ∷ Es)} {os n}
           → see es ≡ mmu i v → StepI (eoutq ⨾ k) r (es ∥ os) n [] k r (vw v es ∥ os) n
  i-ecase₁ : ∀ {E₁ E₂ Es S U} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) U} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) U}
               {r : Ret U T} {e es os n}
           → see es ≡ minl e → StepI (ecase c₁ c₂) r (es ∥ os) n [] c₁ r (vw e es ∥ os) n
  i-ecase₂ : ∀ {E₁ E₂ Es S U} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) U} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) U}
               {r : Ret U T} {e es os n}
           → see es ≡ minr e → StepI (ecase c₁ c₂) r (es ∥ os) n [] c₂ r (vw e es ∥ os) n
  i-eapp   : ∀ {l X Es S U} {k : Codeᴵ (X ∷ Ct l X ∷ Es ∣ S) U} {r : Ret U T} {x : MV X} {es os n}
           → see es ≡ mct x → StepI (eapp ⨾ k) r (es ∥ os) n [] k r (vw x es ∥ os) n
  i-epop   : ∀ {E Es S U} {k : Codeᴵ (Es ∣ S) U} {r : Ret U T} {e : MV E} {es os n}
           → StepI (epop ⨾ k) r (vw e es ∥ os) n [] k r (es ∥ os) n
  i-eword  : ∀ {b Es S U} {k : Codeᴵ (Bt b ∷ Es ∣ Bt b ∷ S) U} {r : Ret U T} {x} {es : Slots (Bt b ∷ Es)} {os n}
           → see es ≡ mbase x → StepI (eword ⨾ k) r (es ∥ mone ∷ˢ os) n [] k r (es ∥ mbase x ∷ˢ os) n
  -- ★ a call opens a frame of its own (D415): the caller's top view and the
  -- argument; reaching the end of a block returns its result to the caller
  i-call   : ∀ {σ Es S U} {κ : Key σ} {k : Codeᴵ (top σ ⊳ Es ∣ cod σ ∷ S) U} {r : Ret U T}
               {es : Slots (top σ ⊳ Es)} {a : MV (dom σ)} {os : Stk S} {n}
           → StepI (call κ ⨾ k) r (es ∥ a ∷ˢ os) n (tmp (tnew fsz) ∷ [])
                   (blockᴵ κ) (frm k es os r) (topv (top σ) es ∥ a ∷ˢ []ˢ) n
  i-ret    : ∀ {t Es B S U} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots (t ⊳ Es)} {os : Stk S}
               {e′ : Slots (t ⊳ [])} {b : MV B} {n}
           → StepI end (frm k es os r) (e′ ∥ b ∷ˢ []ˢ) n (tmp (tdel fsz) ∷ []) k r (es ∥ b ∷ˢ os) n
  i-reti   : ∀ {sh U} {k : Codeᴵ sh U} {r : Ret U T} {m n}
           → StepI end (k ∷ⁱ r) m n [] k r m n
  -- ★ the loop: the round, then what it says
  i-loop   : ∀ {E Es A B S U} {body : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)}
               {k : Codeᴵ (E ∷ Es ∣ B ∷ S) U} {r : Ret U T} {m n}
           → StepI (loop body ⨾ k) r m n [] body (case k (loop body ⨾ k) ∷ⁱ r) m n
  -- ★ THROUGH A CELL'S CODE WORD (D417): a call of the trampoline the cell
  -- names, in a frame of its own, as `i-call` (the flat run's
  -- `instr-call-closure`): the caller's top view (a copy's) and the operand
  i-icall  : ∀ {Es g X A B S U} {k : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots Es} {i}
               {lam : Lam once g X A B} {x a} {os : Stk S} {n}
           → StepI (icall ⨾ k) r (es ∥ mpair (mfn i lam x) a ∷ˢ os) n (tmp (tnew fsz) ∷ [])
                   (blockᴵ (tr1 lam)) (frm {t = nothing} k es os r) ([]ᵉ ∥ mpair (mfn i lam x) a ∷ˢ []ˢ) n
  i-icallω : ∀ {Es g X A B S U} {k : Codeᴵ (Fn many g A B ∷ Es ∣ B ∷ S) U} {r : Ret U T}
               {lam : Lam many g X A B} {i x} {es : Slots (Fn many g A B ∷ Es)} {a} {os : Stk S} {n}
           → see es ≡ mfn i lam x
           → StepI (icallω ⨾ k) r (es ∥ a ∷ˢ os) n (tmp (tnew fsz) ∷ [])
                   (blockᴵ (trω lam)) (frm {t = just _} k es os r) (vw (see es) []ᵉ ∥ a ∷ˢ []ˢ) n
  i-iobs   : ∀ {Γ} {ds : Defs Γ} {Es F S S′ U} {k : Codeᴵ (Es ∣ LF∙ F (Nu F) ∷ S′) U} {r : Ret U T} {es : Slots Es} {i}
               {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n}
           → StepI (iobs ds ⨾ k) r (es ∥ mnu i p ∷ˢ os) n (tmp (tnew fsz) ∷ [])
                   (blockᴵ (ktro ds F S)) (frm {t = nothing} k es os r) ([]ᵉ ∥ mnu i p ∷ˢ []ˢ) n
  i-ccopy  : ∀ {Es kd g X A B S U} {k : Codeᴵ (Fn kd g A B ∷ Es ∣ Fn kd g A B ∷ S) U} {r : Ret U T}
               {lam : Lam kd g X A B} {i x} {es : Slots (Fn kd g A B ∷ Es)} {os : Stk S} {n}
           → see es ≡ mfn i lam x
           → StepI (ccopy ⨾ k) r (es ∥ mone ∷ˢ os) n (tmp (tnew fsz) ∷ [])
                   (blockᴵ (ktrc X (Fn kd g A B))) (frm {t = just _} k es os r) (vw (see es) []ᵉ ∥ mone ∷ˢ []ˢ) n
  i-ncopy  : ∀ {Es F S S′ U} {k : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S′) U} {r : Ret U T} {i} {p : MV (Coalg F S ⊗t S)}
               {es : Slots (Nu F ∷ Es)} {os : Stk S′} {n}
           → see es ≡ mnu i p
           → StepI (ncopy ⨾ k) r (es ∥ mone ∷ˢ os) n (tmp (tnew fsz) ∷ [])
                   (blockᴵ (ktrc (Coalg F S ⊗t S) (Nu F))) (frm {t = just _} k es os r) (vw (see es) []ᵉ ∥ mone ∷ˢ []ˢ) n
  i-cfree  : ∀ {Es kd g X A B S U} {c : Codeᴵ (Es ∣ One ∷ S) U} {r : Ret U T} {es : Slots Es} {i}
               {lam : Lam kd g X A B} {x : MV X} {os : Stk S} {n}
           → StepI (cfree ⨾ c) r (es ∥ mfn i lam x ∷ˢ os) n (tmp (tnew fsz) ∷ [])
                   (blockᴵ (ktrf X (Fn kd g A B))) (frm {t = nothing} c es os r) ([]ᵉ ∥ mfn i lam x ∷ˢ []ˢ) n
  i-nfree  : ∀ {Es F S S′ U} {c : Codeᴵ (Es ∣ One ∷ S′) U} {r : Ret U T} {es : Slots Es} {i}
               {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n}
           → StepI (nfree ⨾ c) r (es ∥ mnu i p ∷ˢ os) n (tmp (tnew fsz) ∷ [])
                   (blockᴵ (ktrf (Coalg F S ⊗t S) (Nu F))) (frm {t = nothing} c es os r) ([]ᵉ ∥ mnu i p ∷ˢ []ˢ) n
  -- ★ a trampoline's cell part (D417)
  -- a one-shot closure: its environment beside the argument, the cell freed
  i-open1  : ∀ {Es g X A B S U} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) U} {r : Ret U T} {es i}
               {lam : Lam once g X A B} {x a os n}
           → StepI (open1 ⨾ k) r (es ∥ mpair (mfn i lam x) a ∷ˢ os) n (free i ∷ []) k r (es ∥ mpair x a ∷ˢ os) n
  -- a many-use closure: its environment viewed
  i-openω  : ∀ {Es g X A B S U} {k : Codeᴵ (X ∷ Fn many g A B ∷ Es ∣ S) U} {r : Ret U T}
               {lam : Lam many g X A B} {i x} {es : Slots (Fn many g A B ∷ Es)} {os n}
           → see es ≡ mfn i lam x → StepI (openω ⨾ k) r (es ∥ os) n (peek i ∷ []) k r (vw x es ∥ os) n
  -- a ν: its coalgebra and seed, the cell freed
  i-nopen  : ∀ {Es F S S′ U} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) U} {r : Ret U T} {es i}
               {p : MV (Coalg F S ⊗t S)} {os n}
           → StepI (nopen ⨾ k) r (es ∥ mnu i p ∷ˢ os) n (free i ∷ []) k r (es ∥ p ∷ˢ os) n
  -- a copy: the viewed cell's contents viewed …
  i-copen  : ∀ {Es kd g X A B S U} {k : Codeᴵ (X ∷ Fn kd g A B ∷ Es ∣ S) U} {r : Ret U T}
               {lam : Lam kd g X A B} {i x} {es : Slots (Fn kd g A B ∷ Es)} {os n}
           → see es ≡ mfn i lam x → StepI (copen ⨾ k) r (es ∥ os) n [] k r (vw x es ∥ os) n
  i-copenν : ∀ {Es F S S′ U} {k : Codeᴵ ((Coalg F S ⊗t S) ∷ Nu F ∷ Es ∣ S′) U} {r : Ret U T}
               {i} {p : MV (Coalg F S ⊗t S)} {es : Slots (Nu F ∷ Es)} {os n}
           → see es ≡ mnu i p → StepI (copen ⨾ k) r (es ∥ os) n [] k r (vw p es ∥ os) n
  -- … then a fresh cell around their copy, with the viewed cell's code words
  i-reclose : ∀ {Es kd g X A B S U} {k : Codeᴵ (Fn kd g A B ∷ Es ∣ Fn kd g A B ∷ S) U} {r : Ret U T}
                {lam : Lam kd g X A B} {i x} {es : Slots (Fn kd g A B ∷ Es)} {x′ : MV X} {os n}
            → see es ≡ mfn i lam x
            → StepI (reclose ⨾ k) r (es ∥ x′ ∷ˢ os) n (alloc (szc X , n) ∷ []) k r (es ∥ mfn (szc X , n) lam x′ ∷ˢ os) (suc n)
  i-recloseν : ∀ {Es F S S′ U} {k : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S′) U} {r : Ret U T}
                 {i} {p : MV (Coalg F S ⊗t S)} {es : Slots (Nu F ∷ Es)} {p′ : MV (Coalg F S ⊗t S)} {os n}
             → see es ≡ mnu i p
             → StepI (reclose ⨾ k) r (es ∥ p′ ∷ˢ os) n (alloc (szν F S , n) ∷ []) k r (es ∥ mnu (szν F S , n) p′ ∷ˢ os) (suc n)
  -- a free: the cell freed, what it held out
  i-fopen  : ∀ {Es kd g X A B S U} {k : Codeᴵ (Es ∣ X ∷ S) U} {r : Ret U T} {es i} {lam : Lam kd g X A B} {x : MV X} {os n}
           → StepI (fopen ⨾ k) r (es ∥ mfn i lam x ∷ˢ os) n (free i ∷ []) k r (es ∥ x ∷ˢ os) n
  i-fopenν : ∀ {Es F S S′ U} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) U} {r : Ret U T} {es i} {p : MV (Coalg F S ⊗t S)} {os n}
           → StepI (fopen ⨾ k) r (es ∥ mnu i p ∷ˢ os) n (free i ∷ []) k r (es ∥ p ∷ˢ os) n
