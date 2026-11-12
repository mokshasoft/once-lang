-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LowAt — plan 0.146 B1.4b (D417, step 3): the flat code AT
-- A POINT.
--
-- A root's code (the start code, a block's) is lowered once, by `lowC`, at
-- a frame `φ`, a block index `j`, a first label `m` and what its `end`
-- becomes (`fin`): its `Low`. Every point inside it (`ImagePt.Sub`) has a
-- `Low` of its own — the counter and `fin` its lowering was given there —
-- and its lowered code lies INSIDE the root's (`sub-low`). A loop's dispatch
-- point is the loop's dispatch code, followed by the code after the loop
-- (`dispC`, `disp-in`). Word-free: lists only.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.Machine.SMCore

module Once.LinCore.LowAt
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.ImagePt fmt ans bw using (Sub; whole; next; left; right; eleft; eright; body)

------------------------------------------------------------------------
-- 1. INSIDE: a list within a list.
------------------------------------------------------------------------

Inside : AbstractTrace → AbstractTrace → Set
Inside big small = Σ AbstractTrace λ pre → Σ AbstractTrace λ post → big ≡ pre ++ (small ++ post)

in-refl : ∀ xs → Inside xs xs
in-refl xs = [] , [] , sym (++-identityʳ xs)

in-trans : ∀ {a b c} → Inside a b → Inside b c → Inside a c
in-trans {c = c} (p₁ , q₁ , e₁) (p₂ , q₂ , e₂) =
  p₁ ++ p₂ , q₂ ++ q₁ ,
  trans e₁ (trans (cong (λ z → p₁ ++ (z ++ q₁)) e₂)
    (trans (cong (p₁ ++_) (++-assoc p₂ (c ++ q₂) q₁))
      (trans (cong (λ z → p₁ ++ (p₂ ++ z)) (++-assoc c q₂ q₁))
        (sym (++-assoc p₁ p₂ (c ++ (q₂ ++ q₁)))))))

in-l : ∀ xs ys → Inside (xs ++ ys) xs
in-l xs ys = [] , ys , refl

in-r : ∀ xs ys → Inside (xs ++ ys) ys
in-r xs ys = xs , [] , cong (xs ++_) (sym (++-identityʳ ys))

in-∷ : ∀ {x xs} → Inside (x ∷ xs) xs
in-∷ {x} {xs} = in-r (x ∷ []) xs

-- the suffix of a middle piece and what follows it
in-mid : ∀ xs ys zs → Inside ((xs ++ ys) ++ zs) (ys ++ zs)
in-mid xs ys zs = xs , [] , trans (++-assoc xs ys zs) (cong (xs ++_) (sym (++-identityʳ (ys ++ zs))))

------------------------------------------------------------------------
-- 2. ★ A POINT'S LOWERING, inside its root's.
------------------------------------------------------------------------

module At (U : Univ)
          (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
          (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
          (φ : Frame) (j : ℕ) where
  open In U
  open Lowering U ncty ldConst

  -- what a code is lowered with: its first label, its `end`, its evidence
  record Low {sh V} (c : Codeᴵ sh V) : Set where
    constructor low
    field
      lm   : ℕ
      lfin : AbstractTrace
      lcin : CIn c
  open Low public

  code : ∀ {sh V} {c : Codeᴵ sh V} → Low c → AbstractTrace
  code {c = c} (low m fin ev) = proj₁ (lowC φ j m fin c ev)

  -- a code's lowering inside the root's
  record SubLow {sh V sh′ V′} {root : Codeᴵ sh V} (L₀ : Low root) (c : Codeᴵ sh′ V′) : Set where
    constructor sublow
    field
      L   : Low c
      ins : Inside (code L₀) (code L)
  open SubLow public

  module _ {sh V} {root : Codeᴵ sh V} {L₀ : Low root} where
    nextL : ∀ {s s′ W} {i : Insᴵ s s′} {k : Codeᴵ s′ W} → SubLow L₀ (i ⨾ k) → SubLow L₀ k
    nextL {i = i} {k} (sublow (low m fin (ei , ek)) ins) =
      let li = lowI φ j m i ei
      in sublow (low (proj₂ li) fin ek) (in-trans ins (in-r (proj₁ li) (proj₁ (lowC φ j (proj₂ li) fin k ek))))

    caseL₁ : ∀ {Es A B S W} {c₁ : Codeᴵ (Es ∣ A ∷ S) W} {c₂ : Codeᴵ (Es ∣ B ∷ S) W}
           → SubLow L₀ (case c₁ c₂) → SubLow L₀ c₁
    caseL₁ {A = A} {B} {S} {c₁ = c₁} {c₂} (sublow (low m fin (e₁ , e₂)) ins) =
      let t = Tp φ ((A ⊕t B) ∷ S) ; bot = Tp φ S
          l₂ = lowC φ j (suc m) fin c₂ e₂ ; l₁ = lowC φ j (proj₂ l₂) fin c₁ e₁
          MB = mvSSd (suc t) (bot ∸ wsz B) (wsz B) ; MA = mvSSd (suc t) (bot ∸ wsz A) (wsz A)
      in sublow (low (proj₂ l₂) fin e₁)
           (in-trans ins (in-trans in-∷ (in-trans in-∷ (in-trans in-∷
             (in-trans (in-r MB _) (in-trans (in-r (proj₁ l₂) _) (in-trans in-∷ (in-r MA (proj₁ l₁)))))))))

    caseL₂ : ∀ {Es A B S W} {c₁ : Codeᴵ (Es ∣ A ∷ S) W} {c₂ : Codeᴵ (Es ∣ B ∷ S) W}
           → SubLow L₀ (case c₁ c₂) → SubLow L₀ c₂
    caseL₂ {A = A} {B} {S} {c₁ = c₁} {c₂} (sublow (low m fin (e₁ , e₂)) ins) =
      let t = Tp φ ((A ⊕t B) ∷ S) ; bot = Tp φ S
          l₂ = lowC φ j (suc m) fin c₂ e₂
          MB = mvSSd (suc t) (bot ∸ wsz B) (wsz B)
      in sublow (low (suc m) fin e₂)
           (in-trans ins (in-trans in-∷ (in-trans in-∷ (in-trans in-∷
             (in-trans (in-r MB _) (in-l (proj₁ l₂) _))))))

    ecaseL₁ : ∀ {E₁ E₂ Es S W} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) W} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) W}
            → SubLow L₀ (ecase c₁ c₂) → SubLow L₀ c₁
    ecaseL₁ {E₁} {E₂} {Es} {c₁ = c₁} {c₂} (sublow (low m fin (e₁ , e₂)) ins) =
      let e = ws Es ; nb = e + wsz (E₁ ⊕t E₂)
          l₂ = lowC φ j (suc m) fin c₂ e₂ ; l₁ = lowC φ j (proj₂ l₂) fin c₁ e₁
          M₂ = mvSS (suc e) nb (wsz E₂) ; M₁ = mvSS (suc e) nb (wsz E₁)
      in sublow (low (proj₂ l₂) fin e₁)
           (in-trans ins (in-trans in-∷ (in-trans in-∷ (in-trans in-∷
             (in-trans (in-r M₂ _) (in-trans (in-r (proj₁ l₂) _) (in-trans in-∷ (in-r M₁ (proj₁ l₁)))))))))

    ecaseL₂ : ∀ {E₁ E₂ Es S W} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) W} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) W}
            → SubLow L₀ (ecase c₁ c₂) → SubLow L₀ c₂
    ecaseL₂ {E₁} {E₂} {Es} {c₁ = c₁} {c₂} (sublow (low m fin (e₁ , e₂)) ins) =
      let e = ws Es ; nb = e + wsz (E₁ ⊕t E₂)
          l₂ = lowC φ j (suc m) fin c₂ e₂
          M₂ = mvSS (suc e) nb (wsz E₂)
      in sublow (low (suc m) fin e₂)
           (in-trans ins (in-trans in-∷ (in-trans in-∷ (in-trans in-∷
             (in-trans (in-r M₂ _) (in-l (proj₁ l₂) _))))))

    -- a loop's body: lowered after its head label, its `end` the jump to
    -- the dispatch
    bodyL : ∀ {E Es A B S W} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) W}
          → SubLow L₀ (loop b ⨾ k) → SubLow L₀ b
    bodyL {b = b} {k} (sublow (low m fin (eb , ek)) ins) =
      let li = lowI φ j m (loop b) eb
          lb = lowC φ j (suc (suc (suc m))) (instr-ctrl (c-jmp (jl j (suc m))) ∷ []) b eb
      in sublow (low (suc (suc (suc m))) (instr-ctrl (c-jmp (jl j (suc m))) ∷ []) eb)
           (in-trans ins (in-trans (in-l (proj₁ li) _) (in-trans in-∷ (in-l (proj₁ lb) _))))

  -- ★ every path's lowering lies inside the root's
  sub-low : ∀ {sh V sh′ V′} {root : Codeᴵ sh V} (L₀ : Low root) {c : Codeᴵ sh′ V′} → Sub root c → SubLow L₀ c
  sub-low L₀ whole      = sublow L₀ (in-refl (code L₀))
  sub-low L₀ (next p)   = nextL (sub-low L₀ p)
  sub-low L₀ (left p)   = caseL₁ (sub-low L₀ p)
  sub-low L₀ (right p)  = caseL₂ (sub-low L₀ p)
  sub-low L₀ (eleft p)  = ecaseL₁ (sub-low L₀ p)
  sub-low L₀ (eright p) = ecaseL₂ (sub-low L₀ p)
  sub-low L₀ (body p)   = bodyL (sub-low L₀ p)

  ----------------------------------------------------------------------
  -- 3. ★ A LOOP'S DISPATCH POINT: the dispatch, then the code after the
  -- loop.
  ----------------------------------------------------------------------

  dispC : ∀ {E Es A B S W} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) W}
        → Low (loop b ⨾ k) → AbstractTrace
  dispC {A = A} {B} {S} {b = b} {k} (low m fin (eb , ek)) =
    let Lh = jl j m ; Ld = jl j (suc m) ; Li = jl j (suc (suc m))
        lb = lowC φ j (suc (suc (suc m))) (instr-ctrl (c-jmp Ld) ∷ []) b eb
        t = Tp φ ((B ⊕t A) ∷ S) ; bot = Tp φ S
    in (instr-ctrl (c-label Ld) ∷ lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li)
        ∷ mvSSd (suc t) (bot ∸ wsz A) (wsz A) ++ instr-ctrl (c-jmp Lh)
        ∷ instr-ctrl (c-label Li) ∷ mvSSd (suc t) (bot ∸ wsz B) (wsz B))
       ++ proj₁ (lowC φ j (proj₂ lb) fin k ek)

  disp-in : ∀ {E Es A B S W} {b : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) W}
          → (L : Low (loop b ⨾ k)) → Inside (code L) (dispC L)
  disp-in {A = A} {B} {S} {b = b} {k} (low m fin (eb , ek)) =
    let Ld = jl j (suc m)
        lb = lowC φ j (suc (suc (suc m))) (instr-ctrl (c-jmp Ld) ∷ []) b eb
    in in-trans in-∷ (in-mid (proj₁ lb) _ (proj₁ (lowC φ j (proj₂ lb) fin k ek)))
