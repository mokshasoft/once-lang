-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Once.LinCore.Sized
--
-- ★ D469: WELL-SIZED IDS. A cell's id carries its block's size (`szμ`,
-- `szc`, `szν`: the image's). Every cell a run makes has its type's size
-- (`r-In`, `r-lam`, `r-lamω`, `r-unf`, `copy`), and a run moves cells, never
-- renames them (`r-cata-reuse` keeps a node for a node of the same functor):
-- so every value a run gives is well-sized when its environment and its
-- argument are (`ws-run`). What the gated free needs of a held cell's size
-- comes from here, not from the cell's place in memory.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Data.Nat using (ℕ)

module Once.LinCore.Sized
  (fmt : TargetNum)
  (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Agda.Builtin.Sigma using (fst; snd)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.LinCore.Flat using (funit; fvoid; fw; _f*_; _f+_)
open import Once.LinCore.Core fmt
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Events fmt ans bw

------------------------------------------------------------------------
-- A value's cells, each at its type's size
------------------------------------------------------------------------

WS : ∀ {A} → MV A → Set
WS mone                    = ⊤
WS (mpair a b)             = WS a × WS b
WS (minl a)                = WS a
WS (minr b)                = WS b
WS (mbase _)               = ⊤
WS (mmu {F} i v)           = fst i ≡ szμ F × WS v
WS (mct x)                 = WS x
WS (mfn {X = X} i _ x)     = fst i ≡ szc X × WS x
WS (mnu {F} {S} i p)       = fst i ≡ szν F S × WS p

-- a copy's cells are fresh, at their types' sizes
ws-copy : ∀ {A} (v : MV A) n → WS v → WS (fst (copy v n))
ws-copy mone        n w = tt
ws-copy (mpair a b) n (wa , wb) = ws-copy a n wa , ws-copy b (fst (snd (copy a n))) wb
ws-copy (minl a)    n w = ws-copy a n w
ws-copy (minr b)    n w = ws-copy b n w
ws-copy (mbase x)   n w = tt
ws-copy (mmu i v)   n (_ , w) = refl , ws-copy v n w
ws-copy (mct x)     n w = ws-copy x n w
ws-copy (mfn i c x) n (_ , w) = refl , ws-copy x n w
ws-copy (mnu i p)   n (_ , w) = refl , ws-copy p n w

-- tagging moves no cell
ws-tag : ∀ {l X} F (x : MV (LF∙ F X)) → WS x → WS (tag {l = l} F x)
ws-tag Idf      x            w = w
ws-tag Kone     x            w = w
ws-tag Kzero    ()           w
ws-tag (Kb b)   x            w = w
ws-tag (Kμ G)   x            w = w
ws-tag (G ⊕f H) (minl x)     w = ws-tag G x w
ws-tag (G ⊕f H) (minr x)     w = ws-tag H x w
ws-tag (G ⊗f H) (mpair x x′) (w , w′) = ws-tag G x w , ws-tag H x′ w′

-- a flat value has no cell
ws-flat : ∀ a (x : ⟦ a ⟧f) → WS (mvF a x)
ws-flat funit    x        = tt
ws-flat fvoid    ()
ws-flat (fw b)   x        = tt
ws-flat (a f* b) (x , y)  = ws-flat a x , ws-flat b y
ws-flat (a f+ b) (inj₁ x) = ws-flat a x
ws-flat (a f+ b) (inj₂ y) = ws-flat b y

------------------------------------------------------------------------
-- ★ A run gives well-sized values
------------------------------------------------------------------------

ws-map : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n y n′ t}
       → RunMap ds F alg e G x n (gives y n′) t → WS e → WS x → WS y
ws-run : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e : MV E} {v : MV A} {w : MV B} {n n′ t}
       → Run ds f e v n (gives w n′) t → WS e → WS v → WS w

ws-run r-id we wv = wv
ws-run (r-∘ rg (go-on rf)) we wv = ws-run rf we (ws-run rg we wv)
ws-run (r-⊗ rf (go-on (fm-gives rg))) we (wa , wc) = ws-run rf we wa , ws-run rg we wc
ws-run r-ρ we (wa , _) = wa
ws-run r-ρ⁻ we wa = wa , tt
ws-run r-λ we (_ , wa) = wa
ws-run r-λ⁻ we wa = tt , wa
ws-run r-α we ((wa , wb) , wc) = wa , (wb , wc)
ws-run r-α⁻ we (wa , (wb , wc)) = (wa , wb) , wc
ws-run r-swap we (wa , wb) = wb , wa
ws-run (r-dup {v = v} {n}) we wv = wv , ws-copy v n wv
ws-run r-drop we wv = tt
ws-run r-inl we wa = wa
ws-run r-inr we wb = wb
ws-run (r-case₁ r) we wa = ws-run r we wa
ws-run (r-case₂ r) we wb = ws-run r we wb
ws-run r-In we wv = refl , wv
ws-run r-Outμ we (_ , wv) = wv
ws-run (r-clo {F = F} {x = x}) we wx = ws-tag F x wx
ws-run (r-app _ r) we (wx , wa) = ws-run r tt (wx , wa)
ws-run (r-cata rm (go-on ra)) we (_ , wv) = ws-run ra we (ws-map rm we wv)
ws-run (r-cata-reuse rm (go-on (fm-gives rg))) we (wi , wv) = wi , ws-run rg we (ws-map rm we wv)
ws-run (r-lend (fm-gives r)) we (wx , wa) = wx , ws-run r (we , wx) wa
ws-run (r-lift r) we wa = ws-run r tt wa
ws-run (r-fst r) (we , _) wa = ws-run r we wa
ws-run (r-snd r) (_ , we) wa = ws-run r we wa
ws-run (r-caseE₁ r) we wa = ws-run r we wa
ws-run (r-caseE₂ r) we wa = ws-run r we wa
ws-run (r-out r) (_ , we) wa = ws-run r we wa
ws-run (r-copy {e = e} {n}) we _ = ws-copy e n we
ws-run (r-bapp _ r) we wa = ws-run r we wa
ws-run r-lam we wx = refl , wx
ws-run r-lamω we wx = refl , wx
ws-run (r-ev r) we ((_ , wx) , wa) = ws-run r tt (wx , wa)
ws-run (r-bev r) (_ , we) wa = ws-run r we wa
ws-run (r-evω r) we ((_ , wx) , wa) = ws-run r tt (wx , wa)
ws-run r-lamωᶜ we wx = refl , wx
ws-run (r-evωᶜ r) we ((_ , wx) , wa) = ws-run r tt (wx , wa)
ws-run (r-bevᶜ r) (_ , we) wa = ws-run r we wa
ws-run r-unf we wp = refl , wp
ws-run (r-nout r) we (_ , wp) = ws-run r tt wp
ws-run r-const we _ = tt
ws-run (r-op {s = s} {y = y} _) we _ = ws-flat (scod s) y
ws-run (r-iter r (go-on done)) we wa = ws-run r we wa
ws-run (r-iter r (go-on (again rn))) we wa = ws-run rn we (ws-run r we wa)
ws-run (r-tmp r _ _) we wv = ws-run r we wv

ws-map (m-id r) we wx = ws-run r we wx
ws-map m-one we wx = wx
ws-map m-b we wx = wx
ws-map m-μ we wx = wx
ws-map (m-inl (fm-gives r)) we wx = ws-map r we wx
ws-map (m-inr (fm-gives r)) we wx = ws-map r we wx
ws-map (m-pair r (go-on (fm-gives r′))) we (wx , wx′) = ws-map r we wx , ws-map r′ we wx′
