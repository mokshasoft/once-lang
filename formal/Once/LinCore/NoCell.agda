-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.NoCell — plan 0.146 B1.4b (D422): ★ A ROOT'S CODE HAS NO
-- TRAMPOLINE CELL PART.
--
-- A trampoline's cell part (`open1 openω nopen copen reclose fopen`, D417)
-- occurs only in a trampoline's block, whose flat code is `tramp`, never a
-- lowering of that block. The roots the word layer lowers — the start's
-- code and the blocks of the universe's keys — are compiled terms, a fold's
-- traversal, a copy or a free: none has a cell part, and every path into
-- them keeps that (`sub-nc`). So a cell part at a root's path is absurd. Nor
-- has one the image's `halted` (B1.5): it is where a run ends, never code.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-map⁻)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.NoCell
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw using (AKey; Got; ks; tmGot; defsGot; allK; univ; kc; kf; obsK; ∈-cmap⁻; keys; tys; nus; obs)
open import Once.LinCore.ImagePt fmt ans bw using (Sub; whole; next; left; right; eleft; eright; body)

------------------------------------------------------------------------
-- 1. NO CELL PART, by the code.
------------------------------------------------------------------------

NoCellI : ∀ {sh sh′} → Insᴵ sh sh′ → Set
NoCellC : ∀ {sh U} → Codeᴵ sh U → Set

NoCellI open1    = ⊥
NoCellI openω    = ⊥
NoCellI nopen    = ⊥
NoCellI copen    = ⊥
NoCellI reclose  = ⊥
NoCellI fopen    = ⊥
NoCellI (loop c) = NoCellC c
{-# CATCHALL #-}
NoCellI _        = ⊤

NoCellC (i ⨾ k)       = NoCellI i × NoCellC k
NoCellC (case c₁ c₂)  = NoCellC c₁ × NoCellC c₂
NoCellC (ecase c₁ c₂) = NoCellC c₁ × NoCellC c₂
NoCellC end           = ⊤
NoCellC halted        = ⊥

-- ★ a path into a code without a cell part reaches one without
sub-nc : ∀ {sh U sh′ U′} {root : Codeᴵ sh U} {c : Codeᴵ sh′ U′} → Sub root c → NoCellC root → NoCellC c
sub-nc whole      n = n
sub-nc (next s)   n = proj₂ (sub-nc s n)
sub-nc (left s)   n = proj₁ (sub-nc s n)
sub-nc (right s)  n = proj₂ (sub-nc s n)
sub-nc (eleft s)  n = proj₁ (sub-nc s n)
sub-nc (eright s) n = proj₂ (sub-nc s n)
sub-nc (body s)   n = proj₁ (sub-nc s n)

------------------------------------------------------------------------
-- 2. ★ COMPILED CODE HAS NONE: a term, a fold's traversal, a copy, a free.
------------------------------------------------------------------------

comp-nc : ∀ {Γ} (ds : Defs Γ) {E A B} (t : Tm Γ E A B) {Es S T} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) T}
        → NoCellC k → NoCellC (compᴵ ds t k)
comp-nc ds lid           n = n
comp-nc ds (f ∘l g)      n = comp-nc ds g (comp-nc ds f n)
comp-nc ds (f ⊗l g)      n = tt , comp-nc ds f (tt , comp-nc ds g (tt , tt , n))
comp-nc ds (lcase f g)   n = comp-nc ds f n , comp-nc ds g n
comp-nc ds (lcata F alg) n = tt , n
comp-nc ds (liter f φ)   n = comp-nc ds f tt , n
comp-nc ds (lapp p)      n = tt , tt , n
comp-nc ds (lend b)      n = tt , comp-nc ds b (tt , n)
comp-nc ds (blift f)     n = tt , comp-nc ds f (tt , n)
comp-nc ds (bfst f)      n = tt , comp-nc ds f (tt , n)
comp-nc ds (bsnd f)      n = tt , comp-nc ds f (tt , n)
comp-nc ds (bcaseE f g)  n = comp-nc ds f (tt , n) , comp-nc ds g (tt , n)
comp-nc ds (bout f)      n = tt , comp-nc ds f (tt , n)
comp-nc ds bcopy         n = tt , n
comp-nc ds (bapp p)      n = tt , tt , tt , n
comp-nc ds ρl            n = tt , n
comp-nc ds ρl⁻           n = tt , n
comp-nc ds lul           n = tt , n
comp-nc ds lul⁻          n = tt , n
comp-nc ds lassoc        n = tt , n
comp-nc ds lassoc⁻       n = tt , n
comp-nc ds lswap         n = tt , n
comp-nc ds dup           n = tt , tt , tt , tt , tt , tt , tt , tt , n
comp-nc ds drop          n = tt , n
comp-nc ds linl          n = tt , n
comp-nc ds linr          n = tt , n
comp-nc ds lIn           n = tt , n
comp-nc ds lOutμ         n = tt , n
comp-nc ds (lclo F p)    n = tt , n
comp-nc ds (lconst v)    n = tt , n
comp-nc ds (lop s)       n = tt , n
comp-nc ds lzero         n = tt , n
comp-nc ds (llam b γ)    n = tt , n
comp-nc ds (llamω b γ)   n = tt , n
comp-nc ds lev           n = tt , n
comp-nc ds bev           n = tt , n
comp-nc ds lunf          n = tt , n
comp-nc ds lout          n = tt , n

trav-nc : ∀ {Γ} (ds : Defs Γ) F {E A} (alg : Tm Γ E (LF∙ F A) A) G {Es S T} {k : Codeᴵ (E ∷ Es ∣ LF∙ G A ∷ S) T}
        → NoCellC k → NoCellC (travᴵ ds F alg G k)
trav-nc ds F alg Idf      n = tt , n
trav-nc ds F alg Kone     n = n
trav-nc ds F alg Kzero    n = n
trav-nc ds F alg (Kb _)   n = n
trav-nc ds F alg (Kμ _)   n = n
trav-nc ds F alg (G ⊕f H) n = trav-nc ds F alg G (tt , n) , trav-nc ds F alg H (tt , n)
trav-nc ds F alg (G ⊗f H) n = tt , trav-nc ds F alg G (tt , trav-nc ds F alg H (tt , tt , n))

copy-nc : ∀ A → NoCellC (copyᴵ A)
copy-nc One          = tt
copy-nc Zero         = tt , tt
copy-nc (A ⊗t B)     = tt , tt , tt , tt , tt , tt , tt , tt , tt , tt
copy-nc (A ⊕t B)     = (tt , tt , tt , tt) , (tt , tt , tt , tt)
copy-nc (Bt b)       = tt , tt
copy-nc (μt F)       = tt , tt , tt , tt , tt
copy-nc (Ct l X)     = tt , tt , tt , tt , tt
copy-nc (Fn k g A B) = tt , tt
copy-nc (Nu F)       = tt , tt

free-nc : ∀ A → NoCellC (freeᴵ A)
free-nc One          = tt
free-nc Zero         = tt , tt
free-nc (A ⊗t B)     = tt , tt , tt , tt , tt , tt , tt
free-nc (A ⊕t B)     = (tt , tt) , (tt , tt)
free-nc (Bt b)       = tt , tt
free-nc (μt F)       = tt , tt , tt
free-nc (Ct l X)     = tt , tt , tt
free-nc (Fn k g A B) = tt , tt
free-nc (Nu F)       = tt , tt

------------------------------------------------------------------------
-- 3. ★ THE BLOCKS OF THE UNIVERSE: no trampoline's among them.
------------------------------------------------------------------------

-- a key that names a block, not a trampoline
NT : ∀ {σ} → Key σ → Set
NT (ktr1 _ _ _) = ⊥
NT (ktrω _ _ _) = ⊥
NT (ktro _ _ _) = ⊥
NT (ktrc _ _)   = ⊥
NT (ktrf _ _)   = ⊥
{-# CATCHALL #-}
NT _            = ⊤

NTk : AKey → Set
NTk (_ , κ) = NT κ

block-nc : ∀ {σ} (κ : Key σ) → NT κ → NoCellC (blockᴵ κ)
block-nc (kbody1 ds b γ)  _ = tt , comp-nc ds b (tt , tt)
block-nc (kbodyω ds b γ)  _ = comp-nc ds b tt
block-nc (kfold ds F alg) _ = tt , trav-nc ds F alg F (comp-nc ds alg tt)
block-nc (kobs ds F S)    _ = tt , comp-nc ds (obsT F S) (tt , tt)
block-nc (kcopy A)        _ = copy-nc A
block-nc (kfree A)        _ = free-nc A
block-nc (ktr1 _ _ _)     ()
block-nc (ktrω _ _ _)     ()
block-nc (ktro _ _ _)     ()
block-nc (ktrc _ _)       ()
block-nc (ktrf _ _)       ()

key1-nt : ∀ {Γ l g X A B} (ds : Defs Γ) (p : Γ ∋[ l ] sg once g X A B) → NT (key1 ds p)
key1-nt (ds ▸ _)      (there p) = key1-nt ds p
key1-nt (ds ▸ b1 b γ) here      = tt

keyω-nt : ∀ {Γ l g X A B} (ds : Defs Γ) (p : Γ ∋[ l ] sg many g X A B) → NT (keyω ds p)
keyω-nt (ds ▸ _)      (there p) = keyω-nt ds p
keyω-nt (ds ▸ bω b γ) here      = tt

-- a term's keys
tm-nt : ∀ {Γ} (ds : Defs Γ) {E A B} (t : Tm Γ E A B) → All NTk (ks (tmGot ds t))
tm-nt ds (f ∘l g)      = ++⁺ (tm-nt ds f) (tm-nt ds g)
tm-nt ds (f ⊗l g)      = ++⁺ (tm-nt ds f) (tm-nt ds g)
tm-nt ds (lcase f g)   = ++⁺ (tm-nt ds f) (tm-nt ds g)
tm-nt ds (lcata F alg) = ++⁺ (tt All.∷ All.[]) (tm-nt ds alg)
tm-nt ds (liter f φ)   = tm-nt ds f
tm-nt ds (lapp p)      = key1-nt ds p All.∷ All.[]
tm-nt ds (lend b)      = tm-nt ds b
tm-nt ds (blift f)     = tm-nt ds f
tm-nt ds (bfst f)      = tm-nt ds f
tm-nt ds (bsnd f)      = tm-nt ds f
tm-nt ds (bcaseE f g)  = ++⁺ (tm-nt ds f) (tm-nt ds g)
tm-nt ds (bout f)      = tm-nt ds f
tm-nt ds bcopy         = All.[]
tm-nt ds (bapp p)      = keyω-nt ds p All.∷ All.[]
tm-nt ds dup           = All.[]
tm-nt ds drop          = All.[]
tm-nt ds (llam b γ)    = ++⁺ (tt All.∷ All.[]) (++⁺ All.[] (tm-nt ds b))
tm-nt ds (llamω b γ)   = ++⁺ (tt All.∷ All.[]) (++⁺ All.[] (tm-nt ds b))
tm-nt ds lunf          = ++⁺ All.[] All.[]
tm-nt ds lout          = All.[]
tm-nt ds lid           = All.[]
tm-nt ds ρl            = All.[]
tm-nt ds ρl⁻           = All.[]
tm-nt ds lul           = All.[]
tm-nt ds lul⁻          = All.[]
tm-nt ds lassoc        = All.[]
tm-nt ds lassoc⁻       = All.[]
tm-nt ds lswap         = All.[]
tm-nt ds linl          = All.[]
tm-nt ds linr          = All.[]
tm-nt ds lzero         = All.[]
tm-nt ds lIn           = All.[]
tm-nt ds lOutμ         = All.[]
tm-nt ds (lclo F p)    = All.[]
tm-nt ds lev           = All.[]
tm-nt ds bev           = All.[]
tm-nt ds (lconst v)    = All.[]
tm-nt ds (lop s)       = All.[]

-- a table's keys
defs-nt : ∀ {Γ} (ds : Defs Γ) → All NTk (ks (defsGot ds))
defs-nt ε               = All.[]
defs-nt (ds ▸ b1 b γ)   = ++⁺ (defs-nt ds) (++⁺ (tt All.∷ All.[]) (tm-nt ds b))
defs-nt (ds ▸ bω b γ)   = ++⁺ (defs-nt ds) (++⁺ (tt All.∷ All.[]) (tm-nt ds b))

-- ★ every key of a program's universe names a block
allK-nt : ∀ {Γ} (ds : Defs Γ) {E A B} (f : Tm Γ E A B) {κ} → κ ∈ allK (univ ds f) → NTk κ
allK-nt ds f m = case ∈-++⁻ (keys U) m of λ where
    (inj₁ p) → Data.List.Relation.Unary.All.lookup (++⁺ (defs-nt ds) (tm-nt ds f)) p
    (inj₂ p) → case ∈-++⁻ (map kc (tys U)) p of λ where
      (inj₁ q) → case ∈-map⁻ kc q of λ where
        (T , _ , refl) → tt
      (inj₂ q) → case ∈-++⁻ (map kf (tys U)) q of λ where
        (inj₁ r) → case ∈-map⁻ kf r of λ where
          (T , _ , refl) → tt
        (inj₂ r) → case ∈-cmap⁻ (obs U) r of λ where
          (d , _ , s) → case ∈-map⁻ (λ n → _ , kobs (proj₂ d) (proj₁ n) (proj₂ n)) s of λ where
            (n , _ , refl) → tt
  where
    U = univ ds f
