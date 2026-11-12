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
--     contents): each becomes a direct call of the block the cell names.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
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

infixr 5 _∷ᶜ_ _∷ⁱ_
data Ret : Sh → Sh → Set where
  []ʳ  : ∀ {T} → Ret T T
  -- a call's continuation: its frame closes when it is resumed
  _∷ᶜ_ : ∀ {sh U T} → Codeᴵ sh U → Ret U T → Ret sh T
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
  i-epush  : ∀ {Es A S U} {k : Codeᴵ (A ∷ Es ∣ S) U} {r : Ret U T} {es} {a : MV A} {os n}
           → StepI (epush ⨾ k) r (es ∥ a ∷ˢ os) n [] k r (vw a es ∥ os) n
  i-epull  : ∀ {Es A S U} {k : Codeᴵ (Es ∣ A ∷ S) U} {r : Ret U T} {es} {a : MV A} {os n}
           → StepI (epull ⨾ k) r (vw a es ∥ os) n [] k r (es ∥ a ∷ˢ os) n
  i-eword  : ∀ {b Es S U} {k : Codeᴵ (Bt b ∷ Es ∣ Bt b ∷ S) U} {r : Ret U T} {x} {es : Slots (Bt b ∷ Es)} {os n}
           → see es ≡ mbase x → StepI (eword ⨾ k) r (es ∥ mone ∷ˢ os) n [] k r (es ∥ mbase x ∷ˢ os) n
  -- ★ a call opens a frame; reaching the end of a block returns
  i-call   : ∀ {σ Es S U} {κ : Key σ} {k : Codeᴵ (top σ ⊳ Es ∣ cod σ ∷ S) U} {r : Ret U T} {m n}
           → StepI (call κ ⨾ k) r m n (tmp (tnew fsz) ∷ []) (blockᴵ κ) (k ∷ᶜ r) m n
  i-ret    : ∀ {sh U} {k : Codeᴵ sh U} {r : Ret U T} {m n}
           → StepI end (k ∷ᶜ r) m n (tmp (tdel fsz) ∷ []) k r m n
  i-reti   : ∀ {sh U} {k : Codeᴵ sh U} {r : Ret U T} {m n}
           → StepI end (k ∷ⁱ r) m n [] k r m n
  -- ★ the loop: the round, then what it says
  i-loop   : ∀ {E Es A B S U} {body : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)}
               {k : Codeᴵ (E ∷ Es ∣ B ∷ S) U} {r : Ret U T} {m n}
           → StepI (loop body ⨾ k) r m n [] body (case k (loop body ⨾ k) ∷ⁱ r) m n
  -- ★ THROUGH A CELL'S CODE WORD: each a direct call of the block it names
  i-icall  : ∀ {Es g X A B S U} {k : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {Δ} {ds′ : Defs Δ}
               {b : Tm Δ One (X ⊗t A) B} {γ : Gd g b} {es i x a os n}
           → StepI (icall ⨾ k) r (es ∥ mpair (mfn i (c1 ds′ b γ) x) a ∷ˢ os) n (free i ∷ [])
                   (call (kbody1 ds′ b γ) ⨾ k) r (es ∥ mpair x a ∷ˢ os) n
  i-icallω : ∀ {Es g X A B S U} {k : Codeᴵ (Fn many g A B ∷ Es ∣ B ∷ S) U} {r : Ret U T} {Δ} {ds′ : Defs Δ}
               {b : Tm Δ X A B} {γ : Gd g b} {i x} {es : Slots (Fn many g A B ∷ Es)} {os n}
           → see es ≡ mfn i (cω ds′ b γ) x
           → StepI (icallω ⨾ k) r (es ∥ os) n (peek i ∷ []) (call (kbodyω ds′ b γ) ⨾ epop ⨾ k) r (vw x es ∥ os) n
  i-iobs   : ∀ {Es F S S′ U} {k : Codeᴵ (Es ∣ LF∙ F (Nu F) ∷ S′) U} {r : Ret U T} {es i} {p : MV (Coalg F S ⊗t S)} {os n}
           → StepI (iobs ⨾ k) r (es ∥ mnu i p ∷ˢ os) n (free i ∷ []) (call (kobs F S) ⨾ k) r (es ∥ p ∷ˢ os) n
  -- a copy: what the cell holds, then a cell with the same code word
  i-ccopy1 : ∀ {Es g X A B S U} {k : Codeᴵ (Fn once g A B ∷ Es ∣ Fn once g A B ∷ S) U} {r : Ret U T} {Δ}
               {ds′ : Defs Δ} {b : Tm Δ One (X ⊗t A) B} {γ : Gd g b} {i x} {es : Slots (Fn once g A B ∷ Es)} {os n}
           → see es ≡ mfn i (c1 ds′ b γ) x
           → StepI (ccopy ⨾ k) r (es ∥ mone ∷ˢ os) n []
                   (call (kcopy X) ⨾ epop ⨾ prim ds′ (llam b γ) ⨾ k) r (vw x es ∥ mone ∷ˢ os) n
  i-ccopyω : ∀ {Es g X A B S U} {k : Codeᴵ (Fn many g A B ∷ Es ∣ Fn many g A B ∷ S) U} {r : Ret U T} {Δ}
               {ds′ : Defs Δ} {b : Tm Δ X A B} {γ : Gd g b} {i x} {es : Slots (Fn many g A B ∷ Es)} {os n}
           → see es ≡ mfn i (cω ds′ b γ) x
           → StepI (ccopy ⨾ k) r (es ∥ mone ∷ˢ os) n []
                   (call (kcopy X) ⨾ epop ⨾ prim ds′ (llamω b γ) ⨾ k) r (vw x es ∥ mone ∷ˢ os) n
  i-ncopy  : ∀ {Es F S S′ U} {k : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S′) U} {r : Ret U T} {i} {p : MV (Coalg F S ⊗t S)}
               {es : Slots (Nu F ∷ Es)} {os n}
           → see es ≡ mnu i p
           → StepI (ncopy ⨾ k) r (es ∥ mone ∷ˢ os) n []
                   (call (kcopy (Coalg F S ⊗t S)) ⨾ epop ⨾ prim ε (lunf {F = F} {S}) ⨾ k) r (vw p es ∥ mone ∷ˢ os) n
  -- a free: the cell, then what it held
  i-cfree  : ∀ {Es k g X A B S U} {c : Codeᴵ (Es ∣ One ∷ S) U} {r : Ret U T} {es i} {lam : Lam k g X A B} {x : MV X} {os n}
           → StepI (cfree ⨾ c) r (es ∥ mfn i lam x ∷ˢ os) n (free i ∷ []) (call (kfree X) ⨾ c) r (es ∥ x ∷ˢ os) n
  i-nfree  : ∀ {Es F S S′ U} {c : Codeᴵ (Es ∣ One ∷ S′) U} {r : Ret U T} {es i} {p : MV (Coalg F S ⊗t S)} {os n}
           → StepI (nfree ⨾ c) r (es ∥ mnu i p ∷ˢ os) n (free i ∷ []) (call (kfree (Coalg F S ⊗t S)) ⨾ c) r (es ∥ p ∷ˢ os) n
