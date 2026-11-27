-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.CopyCode — plan 0.157 S2 step 4 (D501): GOOD KEYS AND GOOD
-- CODE, statically (split from `CopyRun`, the run half).
--
-- A key is GOOD when its block calls no copy of cells: a body, a fold or a
-- trampoline over copy-free terms (`CopyFree.CF`), an observation whose layer
-- does not branch, a copy at a type without cells (words), any free — never a
-- closure's copy trampoline (`ktrc`). Code is good when it calls only good keys,
-- never copies a closure or a ν (`ccopy`, `ncopy`: the only ways into `ktrc`),
-- and builds only copy-free closures and ν's. A copy-free term's code is good
-- (`comp-c`); a good key's block is good code (`block-c`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.LinCore.Flat using (Base)
open import Data.Nat using (ℕ)

module Once.LinCore.CopyCode (fmt : TargetNum) (bw : Base → ℕ) where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Once.LinCore.Core fmt
open import Once.LinCore.Code fmt bw using (Sh; _∣_)
open import Once.LinCore.Image fmt bw
open import Once.LinCore.CopyFree fmt

------------------------------------------------------------------------
-- 1. ★ GOOD KEYS AND GOOD CODE.
------------------------------------------------------------------------

module Good (lc : LTy → Bool) where

  GoodK : ∀ {σ} → Key σ → Set
  GoodK (kbody1 ds b γ)  = CFD lc ds × CF lc b
  GoodK (kbodyω ds b γ)  = CFD lc ds × CF lc b
  GoodK (kfold ds F alg) = CFD lc ds × CF lc alg
  GoodK (kobs ds F S)    = CFD lc ds × T (not (coCopies F))
  GoodK (kcopy A)        = NC A
  GoodK (kfree A)        = ⊤
  GoodK (ktr1 ds b γ)    = CFD lc ds × CF lc b
  GoodK (ktrω ds b γ)    = CFD lc ds × CF lc b
  GoodK (ktro ds F S)    = CFD lc ds × T (not (coCopies F))
  GoodK (ktrc X C)       = ⊥
  GoodK (ktrf X C)       = ⊤

  IC : ∀ {sh sh′} → Insᴵ sh sh′ → Set
  CC : ∀ {sh T} → Codeᴵ sh T → Set

  IC (call κ)    = GoodK κ
  IC (prim ds g) = CFD lc ds × CF lc g
  IC (loop c)    = CC c
  IC ccopy       = ⊥
  IC ncopy       = ⊥
  {-# CATCHALL #-}
  IC _           = ⊤

  CC end           = ⊤
  CC (i ⨾ c)       = IC i × CC c
  CC (case c₁ c₂)  = CC c₁ × CC c₂
  CC (ecase c₁ c₂) = CC c₁ × CC c₂
  CC halted        = ⊤

  -- a table's labels are good keys
  good-key1 : ∀ {Γ l g X A B} (ds : Defs Γ) (p : Γ ∋[ l ] sg once g X A B) → CFD lc ds → GoodK (key1 ds p)
  good-key1 (ds ▸ _)      (there p) (d , _) = good-key1 ds p d
  good-key1 (ds ▸ b1 b γ) here      (d , c) = d , c

  good-keyω : ∀ {Γ l g X A B} (ds : Defs Γ) (p : Γ ∋[ l ] sg many g X A B) → CFD lc ds → GoodK (keyω ds p)
  good-keyω (ds ▸ _)      (there p) (d , _) = good-keyω ds p d
  good-keyω (ds ▸ bω b γ) here      (d , c) = d , c

  ----------------------------------------------------------------------
  -- 2. ★ A COPY-FREE TERM'S CODE IS GOOD (`Image.compᴵ`, case for case).
  ----------------------------------------------------------------------

  comp-c : ∀ {Γ} (ds : Defs Γ) {E A B} (t : Tm Γ E A B) {Es S T} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) T}
         → CFD lc ds → CF lc t → CC k → CC (compᴵ ds t k)
  right-c : ∀ {Γ} (ds : Defs Γ) {E B B′} (g : Tm Γ E B B′) (m : Maybe (IsLid g)) {Es A S T}
            {k : Codeᴵ (E ∷ Es ∣ A ∷ B′ ∷ S) T} → CFD lc ds → CF lc g → CC k → CC (rightᴵ ds g m k)

  right-c ds g (just is-lid) d c ck = ck
  right-c ds g nothing       d c ck = tt , comp-c ds g d c (tt , ck)

  comp-c ds lid d c ck               = ck
  comp-c ds (f ∘l g) d (cf , cg) ck  = comp-c ds g d cg (comp-c ds f d cf ck)
  comp-c ds (f ⊗l g) d (cf , cg) ck  = tt , comp-c ds f d cf (right-c ds g (isLid? g) d cg (tt , ck))
  comp-c ds (lcase f g) d (cf , cg) ck = comp-c ds f d cf ck , comp-c ds g d cg ck
  comp-c ds (lcata F alg) d c ck     = (d , c) , ck
  comp-c ds (liter f φ) d c ck       = comp-c ds f d c tt , ck
  comp-c ds (lapp p) d c ck          = tt , good-key1 ds p d , ck
  comp-c ds (lend b) d c ck          = tt , comp-c ds b d c (tt , ck)
  comp-c ds (blift f) d c ck         = tt , comp-c ds f d c (tt , ck)
  comp-c ds (bfst f) d c ck          = tt , comp-c ds f d c (tt , ck)
  comp-c ds (bsnd f) d c ck          = tt , comp-c ds f d c (tt , ck)
  comp-c ds (bcaseE f g) d (cf , cg) ck = comp-c ds f d cf (tt , ck) , comp-c ds g d cg (tt , ck)
  comp-c ds (bout f) d c ck          = tt , comp-c ds f d c (tt , ck)
  comp-c ds bcopy d c ck             = c , ck
  comp-c ds (bapp p) d c ck          = tt , good-keyω ds p d , tt , ck
  comp-c ds ρl d c ck                = (d , tt) , ck
  comp-c ds ρl⁻ d c ck               = (d , tt) , ck
  comp-c ds lul d c ck               = (d , tt) , ck
  comp-c ds lul⁻ d c ck              = (d , tt) , ck
  comp-c ds lassoc d c ck            = (d , tt) , ck
  comp-c ds lassoc⁻ d c ck           = (d , tt) , ck
  comp-c ds lswap d c ck             = (d , tt) , ck
  comp-c ds dup d c ck               = tt , tt , tt , tt , tt , c , tt , tt , ck
  comp-c ds drop d c ck              = tt , ck
  comp-c ds linl d c ck              = (d , tt) , ck
  comp-c ds ldist d c ck             = (d , tt) , ck
  comp-c ds linr d c ck              = (d , tt) , ck
  comp-c ds lIn d c ck               = (d , tt) , ck
  comp-c ds lOutμ d c ck             = (d , tt) , ck
  comp-c ds (lclo F p) d c ck        = (d , tt) , ck
  comp-c ds (lconst v) d c ck        = (d , tt) , ck
  comp-c ds (lop s) d c ck           = (d , tt) , ck
  comp-c ds lzero d c ck             = tt , ck
  comp-c ds (llam b γ) d c ck        = (d , c) , ck
  comp-c ds (llamω b γ) d c ck       = (d , c) , ck
  comp-c ds lev d c ck               = tt , ck
  comp-c ds bev d c ck               = tt , ck
  comp-c ds (llamωᶜ b₀ γ) d c ck     = (d , c) , ck
  comp-c ds levω d c ck              = tt , tt , ck
  comp-c ds lunf d c ck              = (d , c) , ck
  comp-c ds lout d c ck              = tt , ck

  ----------------------------------------------------------------------
  -- 3. ★ A GOOD KEY'S BLOCK IS GOOD CODE.
  ----------------------------------------------------------------------

  trav-c : ∀ {Γ} (ds : Defs Γ) F {E A} (alg : Tm Γ E (LF∙ F A) A) G {Es S T} {k : Codeᴵ (E ∷ Es ∣ LF∙ G A ∷ S) T}
         → GoodK (kfold ds F alg) → CC k → CC (travᴵ ds F alg G k)
  trav-c ds F alg Idf      g ck = g , ck
  trav-c ds F alg Kone     g ck = ck
  trav-c ds F alg Kzero    g ck = ck
  trav-c ds F alg (Kb _)   g ck = ck
  trav-c ds F alg (Kμ _)   g ck = ck
  trav-c ds F alg (G ⊕f H) g ck = trav-c ds F alg G g ((tt , tt) , ck) , trav-c ds F alg H g ((tt , tt) , ck)
  trav-c ds F alg (G ⊗f H) g ck = tt , trav-c ds F alg G g (tt , trav-c ds F alg H g (tt , tt , ck))

  -- a copy at a type without cells copies words, calling only such copies
  copy-c : ∀ A → NC A → CC (copyᴵ A)
  copy-c One          n = tt
  copy-c Zero         n = tt , tt
  copy-c (A ⊗t B)     n = tt , not-∨ˡ n , tt , tt , tt , not-∨ʳ n , tt , tt , tt , tt
  copy-c (A ⊕t B)     n = (not-∨ˡ n , tt , (tt , tt) , tt) , (not-∨ʳ n , tt , (tt , tt) , tt)
  copy-c (Bt b)       n = tt , tt
  copy-c (μt F)       ()
  copy-c (Ct l X)     n = tt , n , tt , tt , tt
  copy-c (Fn k g A B) ()
  copy-c (Nu F)       ()

  -- (D503: a μ's free loop calls only frees)
  peel-c : ∀ {F} G (t : Tail G) {Es S U} {k : Codeᴵ (Es ∣ (One ⊕t μt F) ∷ S) U} → CC k → CC (peel G t k)
  peel-c Idf      t-id         ck = (tt , tt) , ck
  peel-c Kone     t-one        ck = (tt , tt) , ck
  peel-c Kzero    t-zero       ck = tt , ck
  peel-c (Kb b)   t-b          ck = tt , (tt , tt) , ck
  peel-c (Kμ G)   t-μ          ck = tt , (tt , tt) , ck
  peel-c (G ⊗f H) (t-pair n t) ck = tt , tt , tt , (tt , tt) , peel-c H t ck
  peel-c (G ⊕f H) (t-sum a b)  ck = peel-c G a ck , peel-c H b ck

  freeμ-c : ∀ F (t : Maybe (Tail F)) → CC (freeμ F t)
  freeμ-c F (just t) = tt , ((tt , tt) , peel-c F t tt) , tt , tt
  freeμ-c F nothing  = (tt , tt) , tt , tt

  free-c : ∀ A → CC (freeᴵ A)
  free-c One          = tt
  free-c Zero         = _
  free-c (A ⊗t B)     = _
  free-c (A ⊕t B)     = _
  free-c (Bt b)       = _
  free-c (μt F)       = freeμ-c F (tail? F)
  free-c (Ct l X)     = _
  free-c (Fn k g A B) = _
  free-c (Nu F)       = _

  block-c : ∀ {σ} (κ : Key σ) → GoodK κ → CC (blockᴵ κ)
  block-c (kbody1 ds b γ)  (d , c) = tt , comp-c ds b d c (tt , tt)
  block-c (kbodyω ds b γ)  (d , c) = comp-c ds b d c tt
  block-c (kfold ds F alg) (d , c) = (d , tt) , trav-c ds F alg F (d , c) (comp-c ds alg d c tt)
  block-c (kobs ds F S)    (d , t) = tt , comp-c ds (obsT F S) d (cf-obsT lc F S t) (tt , tt)
  block-c (kcopy A)        n       = copy-c A n
  block-c (kfree A)        _       = free-c A
  block-c (ktr1 ds b γ)    g       = tt , g , tt
  block-c (ktrω ds b γ)    g       = tt , g , tt , tt
  block-c (ktro ds F S)    g       = tt , g , tt
  block-c (ktrc X C)       ()
  block-c (ktrf X C)       _       = tt , tt , tt

------------------------------------------------------------------------
