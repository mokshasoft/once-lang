-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImagePt — plan 0.146 B1.4b (D417): the image's CONTROL, at
-- program points.
--
-- The image runs on code terms; the flat run on addresses. Every code the
-- image ever holds — the current code, and each continuation on its return
-- stack — is AT A POINT of the program: a path into the start code or into
-- a key's block (`Sub`), or the dispatch point of a loop (`disp`: the code
-- a loop's turn pushes, `case k (loop b ⨾ k)`, is never a subterm; on the
-- flat side it is the loop's dispatch at `Ld`). Every step keeps it (`place`),
-- word-free; the word layer then needs ONE relation: the flat `pc` is the
-- address of the point, the flat code there the lowering at that point.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.ImagePt
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Cfg)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; done; _⟫_)

------------------------------------------------------------------------
-- 1. ★ POINTS: a code's place in a root's code.
------------------------------------------------------------------------

-- `c` is reached from `root` by a path
data Sub {sh U} (root : Codeᴵ sh U) : ∀ {sh′ U′} → Codeᴵ sh′ U′ → Set where
  whole : Sub root root
  next  : ∀ {s s′ V} {i : Insᴵ s s′} {k : Codeᴵ s′ V} → Sub root (i ⨾ k) → Sub root k
  left  : ∀ {Es A B S V} {c₁ : Codeᴵ (Es ∣ A ∷ S) V} {c₂ : Codeᴵ (Es ∣ B ∷ S) V}
        → Sub root (case c₁ c₂) → Sub root c₁
  right : ∀ {Es A B S V} {c₁ : Codeᴵ (Es ∣ A ∷ S) V} {c₂ : Codeᴵ (Es ∣ B ∷ S) V}
        → Sub root (case c₁ c₂) → Sub root c₂
  eleft : ∀ {E₁ E₂ Es S V} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V}
        → Sub root (ecase c₁ c₂) → Sub root c₁
  eright : ∀ {E₁ E₂ Es S V} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V}
         → Sub root (ecase c₁ c₂) → Sub root c₂
  body  : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
        → Sub root (loop b ⨾ k) → Sub root b

-- a point: a path, or a loop's dispatch
data Pt {sh U} (root : Codeᴵ sh U) : ∀ {sh′ U′} → Codeᴵ sh′ U′ → Set where
  at   : ∀ {sh′ U′} {c : Codeᴵ sh′ U′} → Sub root c → Pt root c
  disp : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
       → Sub root (loop b ⨾ k) → Pt root (case k (loop b ⨾ k))

module _ {sh U} {root : Codeᴵ sh U} where
  pnext : ∀ {s s′ V} {i : Insᴵ s s′} {k : Codeᴵ s′ V} → Pt root (i ⨾ k) → Pt root k
  pnext (at p) = at (next p)

  pcase₁ : ∀ {Es A B S V} {c₁ : Codeᴵ (Es ∣ A ∷ S) V} {c₂ : Codeᴵ (Es ∣ B ∷ S) V} → Pt root (case c₁ c₂) → Pt root c₁
  pcase₁ (at p)   = at (left p)
  pcase₁ (disp p) = at (next p)

  pcase₂ : ∀ {Es A B S V} {c₁ : Codeᴵ (Es ∣ A ∷ S) V} {c₂ : Codeᴵ (Es ∣ B ∷ S) V} → Pt root (case c₁ c₂) → Pt root c₂
  pcase₂ (at p)   = at (right p)
  pcase₂ (disp p) = at p

  pecase₁ : ∀ {E₁ E₂ Es S V} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V}
          → Pt root (ecase c₁ c₂) → Pt root c₁
  pecase₁ (at p) = at (eleft p)

  pecase₂ : ∀ {E₁ E₂ Es S V} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V}
          → Pt root (ecase c₁ c₂) → Pt root c₂
  pecase₂ (at p) = at (eright p)

  pbody : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
        → Pt root (loop b ⨾ k) → Pt root b
  pbody (at p) = at (body p)

  pdisp : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
        → Pt root (loop b ⨾ k) → Pt root (case k (loop b ⨾ k))
  pdisp (at p) = disp p

------------------------------------------------------------------------
-- 2. ★ PLACED: at a point of the start code or of a key's block (a
-- trampoline's too), or stopped.
------------------------------------------------------------------------

module Places {sh₀ U₀} (c₀ : Codeᴵ sh₀ U₀) where

  data Placed : ∀ {sh U} → Codeᴵ sh U → Set where
    in-start : ∀ {sh U} {c : Codeᴵ sh U} → Pt c₀ c → Placed c
    in-block : ∀ {σ sh U} {c : Codeᴵ sh U} (κ : Key σ) → Pt (blockᴵ κ) c → Placed c
    halt     : ∀ {sh U} → Placed (halted {sh} {U})

  -- every continuation on the return stack, too
  RPl : ∀ {U T} → Ret U T → Set
  RPl []ʳ             = ⊤
  RPl (frm k es os r) = Placed k × RPl r
  RPl (k ∷ⁱ r)        = Placed k × RPl r

  private
    nxt : ∀ {s s′ V} {i : Insᴵ s s′} {k : Codeᴵ s′ V} → Placed (i ⨾ k) → Placed k
    nxt (in-start p)   = in-start (pnext p)
    nxt (in-block κ p) = in-block κ (pnext p)

    cs₁ : ∀ {Es A B S V} {c₁ : Codeᴵ (Es ∣ A ∷ S) V} {c₂ : Codeᴵ (Es ∣ B ∷ S) V} → Placed (case c₁ c₂) → Placed c₁
    cs₁ (in-start p)   = in-start (pcase₁ p)
    cs₁ (in-block κ p) = in-block κ (pcase₁ p)

    cs₂ : ∀ {Es A B S V} {c₁ : Codeᴵ (Es ∣ A ∷ S) V} {c₂ : Codeᴵ (Es ∣ B ∷ S) V} → Placed (case c₁ c₂) → Placed c₂
    cs₂ (in-start p)   = in-start (pcase₂ p)
    cs₂ (in-block κ p) = in-block κ (pcase₂ p)

    ecs₁ : ∀ {E₁ E₂ Es S V} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V}
         → Placed (ecase c₁ c₂) → Placed c₁
    ecs₁ (in-start p)   = in-start (pecase₁ p)
    ecs₁ (in-block κ p) = in-block κ (pecase₁ p)

    ecs₂ : ∀ {E₁ E₂ Es S V} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) V}
         → Placed (ecase c₁ c₂) → Placed c₂
    ecs₂ (in-start p)   = in-start (pecase₂ p)
    ecs₂ (in-block κ p) = in-block κ (pecase₂ p)

    bdy : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
        → Placed (loop b ⨾ k) → Placed b
    bdy (in-start p)   = in-start (pbody p)
    bdy (in-block κ p) = in-block κ (pbody p)

    dsp : ∀ {E Es A B S V} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V}
        → Placed (loop b ⨾ k) → Placed (case k (loop b ⨾ k))
    dsp (in-start p)   = in-start (pdisp p)
    dsp (in-block κ p) = in-block κ (pdisp p)

    -- a block entered: its start
    entry : ∀ {σ} (κ : Key σ) → Placed (blockᴵ κ)
    entry κ = in-block κ (at whole)

  ----------------------------------------------------------------------
  -- 3. ★ EVERY STEP STAYS PLACED: the image's control is the program's.
  ----------------------------------------------------------------------

  place : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t}
        → StepI c r m n t c′ r′ m′ n′ → Placed c → RPl r → Placed c′ × RPl r′
  place i-unpair      P R = nxt P , R
  place i-pair        P R = nxt P , R
  place i-swap        P R = nxt P , R
  place i-unit        P R = nxt P , R
  place (i-prim _)    P R = nxt P , R
  place (i-opend _)   P R = halt , R
  place i-untag       P R = nxt P , R
  place i-untag₁      P R = nxt P , R
  place i-tag₁        P R = nxt P , R
  place i-case₁       P R = cs₁ P , R
  place i-case₂       P R = cs₂ P , R
  place i-elend       P R = nxt P , R
  place i-eunlend     P R = nxt P , R
  place i-elift       P R = nxt P , R
  place (i-efst _)    P R = nxt P , R
  place (i-esnd _)    P R = nxt P , R
  place (i-eout _)    P R = nxt P , R
  place (i-eoutq _)   P R = nxt P , R
  place (i-ecase₁ _)  P R = ecs₁ P , R
  place (i-ecase₂ _)  P R = ecs₂ P , R
  place (i-eapp _)    P R = nxt P , R
  place i-epop        P R = nxt P , R
  place (i-eword _)   P R = nxt P , R
  -- ★ a call: the block's start, the return point after the call
  place (i-call {κ = κ}) P R = entry κ , nxt P , R
  place i-ret         P (K , R) = K , R
  place i-reti        P (K , R) = K , R
  -- ★ the loop: its body, its dispatch pushed
  place i-loop        P R = bdy P , dsp P , R
  -- ★ a dispatch: the trampoline's start (D417)
  place (i-icall {lam = lam})   P R = entry (tr1 lam) , nxt P , R
  place (i-icallω {lam = lam} _) P R = entry (trω lam) , nxt P , R
  place (i-iobs {ds = ds} {F = F} {S = S}) P R = entry (ktro ds F S) , nxt P , R
  place (i-ccopy {X = X} _)     P R = entry (ktrc X _) , nxt P , R
  place (i-ncopy {F = F} {S = S} _) P R = entry (ktrc (Coalg F S ⊗t S) (Nu F)) , nxt P , R
  place (i-cfree {X = X})       P R = entry (ktrf X _) , nxt P , R
  place (i-nfree {F = F} {S = S}) P R = entry (ktrf (Coalg F S ⊗t S) (Nu F)) , nxt P , R
  place i-open1       P R = nxt P , R
  place (i-openω _)   P R = nxt P , R
  place i-nopen       P R = nxt P , R
  place (i-copen _)   P R = nxt P , R
  place (i-copenν _)  P R = nxt P , R
  place (i-reclose _) P R = nxt P , R
  place (i-recloseν _) P R = nxt P , R
  place i-fopen       P R = nxt P , R
  place i-fopenν      P R = nxt P , R

  places : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m m′ n n′ t}
         → StepsI c r m n t c′ r′ m′ n′ → Placed c → RPl r → Placed c′ × RPl r′
  places done P R = P , R
  places (s ⟫ st) P R with place s P R
  ... | (P′ , R′) = places st P′ R′

  -- ★ from the start: every configuration the image reaches is at points
  placed-always : ∀ {sh U} {c′ : Codeᴵ sh U} {r′ : Ret U U₀} {m₀ m′ n′ mt}
                → StepsI c₀ []ʳ m₀ 0 mt c′ r′ m′ n′ → Placed c′ × RPl r′
  placed-always st = places st (in-start (at whole)) tt
