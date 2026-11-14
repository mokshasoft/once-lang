-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Labels — plan 0.146 B1.4b (D417, step 3): the image's jump
-- labels, part 1: the code that has none.
--
-- Only a `case`, an `ecase` and a loop emit labels (`c-label`); every other
-- instruction's lowering, every move, a cell's header and every trampoline
-- is LABEL-FREE (`NoLab`). (A base constant's loader is a parameter until
-- B1.7: it is assumed to be no label, `ld-nl`.)
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
import Once.Spec.Type as ST
open import Once.SigOp.Info using (module SigOpInfo)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore

module Once.LinCore.Labels
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw

module NoLabels {FS : FrameSemantics} where
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (label-of?; entry-of?)

  -- an instruction that defines a jump label or a callable entry is MARKED;
  -- `NoLab` code defines neither (each proof below is the same `refl`, as
  -- both scans reduce on a concrete instruction)
  both : ∀ {A B : Set} → Maybe A → Maybe B → Maybe ⊤
  both nothing  nothing  = nothing
  both nothing  (just _) = just tt
  both (just _) _        = just tt

  mark : AbstractInstr → Maybe ⊤
  mark x = both (label-of? x) (entry-of? x)

  mark-l : ∀ x → mark x ≡ nothing → label-of? x ≡ nothing
  mark-l x e = go (label-of? x) (entry-of? x) e
    where go : ∀ {A B : Set} (a : Maybe A) (b : Maybe B) → both a b ≡ nothing → a ≡ nothing
          go nothing nothing refl = refl

  mark-e : ∀ x → mark x ≡ nothing → entry-of? x ≡ nothing
  mark-e x e = go (label-of? x) (entry-of? x) e
    where go : ∀ {A B : Set} (a : Maybe A) (b : Maybe B) → both a b ≡ nothing → b ≡ nothing
          go nothing nothing refl = refl

  NoLab : AbstractTrace → Set
  NoLab = All (λ x → mark x ≡ nothing)

  nl : ∀ xs {ys} → NoLab xs → NoLab ys → NoLab (xs ++ ys)
  nl xs p q = ++⁺ p q

  ----------------------------------------------------------------------
  -- 1. MOVES.
  ----------------------------------------------------------------------

  mvSS-nl : ∀ a b n → NoLab (mvSS a b n)
  mvSS-nl a b zero    = []
  mvSS-nl a b (suc n) = refl ∷ refl ∷ mvSS-nl (suc a) (suc b) n

  mvSSd-nl : ∀ a b n → NoLab (mvSSd a b n)
  mvSSd-nl a b zero    = []
  mvSSd-nl a b (suc n) = refl ∷ refl ∷ mvSSd-nl a b n

  mvPS-nl : ∀ o b n → NoLab (mvPS o b n)
  mvPS-nl o b zero    = []
  mvPS-nl o b (suc n) = refl ∷ refl ∷ mvPS-nl (suc o) (suc b) n

  mvSP-nl : ∀ a o n → NoLab (mvSP a o n)
  mvSP-nl a o zero    = []
  mvSP-nl a o (suc n) = refl ∷ refl ∷ mvSP-nl (suc a) (suc o) n

  stores-nl : ∀ b n → NoLab (stores b n)
  stores-nl b zero    = []
  stores-nl b (suc n) = refl ∷ stores-nl (suc b) n

  ----------------------------------------------------------------------
  -- 2. ★ THE LOWERING'S LABEL-FREE PARTS.
  ----------------------------------------------------------------------

  module Free (U : Univ)
              (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
              (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
              (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → mark (ldConst v) ≡ nothing) where
    open In U
    open Lowering U ncty ldConst

    header-nl : ∀ w jb jc jf → NoLab (header w jb jc jf)
    header-nl w jb jc jf = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

    -- D428: the argument's instruction, by its base
    argIn-nl : ∀ {A} (b : ST.Base ST.∅ₖ A) bot w → mark (argIn b bot w) ≡ nothing
    argIn-nl (ST.b-var {i = ()} _) bot w
    argIn-nl ST.b-Unit    bot w = refl
    argIn-nl ST.b-Void    bot w = refl
    argIn-nl ST.b-Int     bot w = refl
    argIn-nl ST.b-Float   bot w = refl
    argIn-nl (ST.b-* _ _) bot w = refl
    argIn-nl (ST.b-+ _ _) bot w = refl

    answer-nl : ∀ w bot → NoLab (answer w bot)
    answer-nl zero          bot = []
    answer-nl (suc zero)    bot = refl ∷ []
    answer-nl (suc (suc w)) bot = []

    -- D428: an op's code, by the sigop it runs
    lowOp-nl : ∀ s m bot → NoLab (lowOp s m bot)
    lowOp-nl s nothing  bot = argIn-nl (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ refl ∷ refl ∷ answer-nl (wsz ⌜ scod s ⌝) bot
    lowOp-nl s (just o) bot = argIn-nl (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

    -- a cell's build: its header, its contents, its address
    cell-nl : ∀ w jb jc jf a o d → NoLab (header w jb jc jf ++ mvSP a o w ++ mov-to-output ∷ store-at-slot d ∷ [])
    cell-nl w jb jc jf a o d = nl (header w jb jc jf) (header-nl w jb jc jf) (nl (mvSP a o w) (mvSP-nl a o w) (refl ∷ refl ∷ []))

    lowP-nl : ∀ {Γ} (ds : Defs Γ) {A B} (g : LTm Γ A B) φ S (p : PrimIn ds g) → NoLab (lowP ds g φ S p)
    lowP-nl ds lid φ S p          = []
    lowP-nl ds (_ ∘l _) φ S p     = []
    lowP-nl ds (_ ⊗l _) φ S p     = []
    lowP-nl ds ρl φ S p           = []
    lowP-nl ds ρl⁻ φ S p          = []
    lowP-nl ds lul φ S p          = []
    lowP-nl ds lul⁻ φ S p         = []
    lowP-nl ds lassoc φ S p       = []
    lowP-nl ds lassoc⁻ φ S p      = []
    lowP-nl ds (lswap {A = A} {B = B}) φ S p =
      let t = Tp φ (A ∷ B ∷ S) ; wA = wsz A ; wB = wsz B ; tmp = t ∸ wA
      in nl (mvSS t tmp wA) (mvSS-nl t tmp wA) (nl (mvSS (t + wA) t wB) (mvSS-nl (t + wA) t wB) (mvSS-nl tmp (t + wB) wA))
    lowP-nl ds dup φ S p          = []
    lowP-nl ds drop φ S p         = []
    lowP-nl ds (linl {A = A} {B = B}) φ S p =
      let bot = Tp φ S ; M = wsz A ⊔ wsz B
      in nl (mvSS (bot ∸ wsz A) (bot ∸ M) (wsz A)) (mvSS-nl (bot ∸ wsz A) (bot ∸ M) (wsz A))
            (refl ∷ refl ∷ stores-nl (bot ∸ (M ∸ wsz A)) (M ∸ wsz A))
    lowP-nl ds (linr {A = A} {B = B}) φ S p =
      let bot = Tp φ S ; M = wsz A ⊔ wsz B
      in nl (mvSS (bot ∸ wsz B) (bot ∸ M) (wsz B)) (mvSS-nl (bot ∸ wsz B) (bot ∸ M) (wsz B))
            (refl ∷ refl ∷ stores-nl (bot ∸ (M ∸ wsz B)) (M ∸ wsz B))
    lowP-nl ds (lcase _ _) φ S p  = []
    lowP-nl ds lzero φ S p        = []
    lowP-nl ds (lIn {F = F}) φ S p =
      let bot = Tp φ S ; wL = wsz (LF∙ F (μt F))
      in refl ∷ refl ∷ nl (mvSP (bot ∸ wL) 0 wL) (mvSP-nl (bot ∸ wL) 0 wL) (refl ∷ refl ∷ [])
    lowP-nl ds (lOutμ {F = F}) φ S p =
      let bot = Tp φ S ; wL = wsz (LF∙ F (μt F))
      in refl ∷ nl (mvPS 0 (bot ∸ wL) wL) (mvPS-nl 0 (bot ∸ wL) wL) (refl ∷ [])
    lowP-nl ds (lcata _ _) φ S p  = []
    lowP-nl ds (lclo _ _) φ S p   = []
    lowP-nl ds (lapp _) φ S p     = []
    lowP-nl ds (lend _) φ S p     = []
    lowP-nl ds (blift _) φ S p    = []
    lowP-nl ds bcopy φ S p        = []
    lowP-nl ds (llam {X = X} b γ) φ S (kb , x) =
      cell-nl (wsz X) (idx kb) (idx (inC x)) (idx (inF x)) (Tp φ S ∸ wsz X) hdr (Tp φ S ∸ 1)
    lowP-nl ds (llamω {X = X} b γ) φ S (kb , x) =
      cell-nl (wsz X) (idx kb) (idx (inC x)) (idx (inF x)) (Tp φ S ∸ wsz X) hdr (Tp φ S ∸ 1)
    lowP-nl ds lev φ S p          = []
    lowP-nl ds (lunf {F = F} {S = S₀}) φ S (n , o) =
      cell-nl (wsz (cty (F , S₀))) (idx (inO o n)) (idx (inC (ncty n))) (idx (inF (ncty n))) (Tp φ S ∸ wsz (cty (F , S₀))) hdr (Tp φ S ∸ 1)
    lowP-nl ds lout φ S p         = []
    lowP-nl ds (lconst v) φ S p   = ld-nl v ∷ refl ∷ []
    lowP-nl ds (lop s) φ S p      = lowOp-nl s (cmpOf s) (Tp φ S)
    lowP-nl ds (liter _ _) φ S p  = []

    -- every instruction but the loop
    NotLoop : ∀ {sh sh′} → Insᴵ sh sh′ → Set
    NotLoop (loop _) = ⊥
    {-# CATCHALL #-}
    NotLoop _        = ⊤

    lowI-nl : ∀ φ j m {sh sh′} (i : Insᴵ sh sh′) (ei : IIn i) → NotLoop i → NoLab (proj₁ (lowI φ j m i ei))
    lowI-nl φ j m unpair ei _  = []
    lowI-nl φ j m pair ei _    = []
    lowI-nl φ j m unit ei _    = []
    lowI-nl φ j m untag ei _   = []
    lowI-nl φ j m untag₁ ei _  = []
    lowI-nl φ j m tag₁ ei _    = []
    lowI-nl φ j m elift ei _   = []
    lowI-nl φ j m epop ei _    = []
    lowI-nl φ j m stuck ei _   = []
    lowI-nl φ j m (swap {A = A} {B} {S}) ei _ =
      let t = Tp φ (A ∷ B ∷ S) ; wA = wsz A ; wB = wsz B ; tmp = t ∸ wA
      in nl (mvSS t tmp wA) (mvSS-nl t tmp wA) (nl (mvSS (t + wA) t wB) (mvSS-nl (t + wA) t wB) (mvSS-nl tmp (t + wB) wA))
    lowI-nl φ j m (prim ds {S = S} g) ei _ = lowP-nl ds g φ S ei
    lowI-nl φ j m (elend {E} {Es} {X} {A} {S}) ei _ =
      let e = ws Es ; wE = wsz E
      in nl (mvSS e (e + wE) wE) (mvSS-nl e (e + wE) wE) (mvSS-nl (Tp φ ((X ⊗t A) ∷ S)) (e + wE + wE) (wsz X))
    lowI-nl φ j m (eunlend {E} {Es} {X} {B} {S}) ei _ =
      let e = ws Es ; wE = wsz E in mvSS-nl (e + wE + wE) (Tp φ (B ∷ S) ∸ wsz X) (wsz X)
    lowI-nl φ j m (efst {E₁} {E₂} {Es}) ei _ = mvSS-nl (ws Es) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₁)
    lowI-nl φ j m (esnd {E₁} {E₂} {Es}) ei _ = mvSS-nl (ws Es + wsz E₁) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₂)
    lowI-nl φ j m (eout {F} {Es}) ei _  = refl ∷ mvPS-nl 0 (suc (ws Es)) (wsz (LF∙ F (μt F)))
    lowI-nl φ j m (eoutq {F} {Es}) ei _ = refl ∷ mvPS-nl 0 (suc (ws Es)) (wsz (LF∙ F (μt F)))
    lowI-nl φ j m (eapp {l} {X} {Es}) ei _ = mvSS-nl (ws Es) (ws Es + wsz X) (wsz X)
    lowI-nl φ j m (eword {b} {Es} {S}) ei _ = mvSS-nl (ws Es) (Tp φ S ∸ 1) 1
    lowI-nl φ j m (call {bsig nothing A B} κ) ei _  = refl ∷ refl ∷ refl ∷ []
    lowI-nl φ j m (call {bsig (just E) A B} κ) ei _ = refl ∷ refl ∷ refl ∷ refl ∷ []
    lowI-nl φ j m icall ei _   = refl ∷ refl ∷ refl ∷ refl ∷ []
    lowI-nl φ j m icallω ei _  = refl ∷ refl ∷ refl ∷ refl ∷ []
    lowI-nl φ j m (iobs ds) ei _ = refl ∷ refl ∷ refl ∷ refl ∷ []
    lowI-nl φ j m ccopy ei _   = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
    lowI-nl φ j m ncopy ei _   = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
    lowI-nl φ j m cfree ei _   = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
    lowI-nl φ j m nfree ei _   = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
    lowI-nl φ j m open1 ei _   = []
    lowI-nl φ j m openω ei _   = []
    lowI-nl φ j m nopen ei _   = []
    lowI-nl φ j m copen ei _   = []
    lowI-nl φ j m reclose ei _ = []
    lowI-nl φ j m fopen ei _   = []
    lowI-nl φ j m (loop c) ei ()

    -- ★ a trampoline: none, or its callable entry `e-thunk (tl j)`, then
    -- code that defines no label and no entry
    TrampShape : ℕ → AbstractTrace → Set
    TrampShape j xs = xs ≡ [] ⊎ Σ ℕ λ b → Σ AbstractTrace λ r → xs ≡ instr-ctrl (c-entry (e-thunk (tl j)) b) ∷ r × NoLab r

    tramp-nl : ∀ {σ} j (κ : Key σ) → TrampShape j (tramp j κ)
    tramp-nl j (kbody1 {X = X} {A = A} {B = B} ds b γ) =
      let wX = wsz X ; wA = wsz A ; wB = wsz B ; M = (wX + wA) ⊔ wB ; Mc = suc wA ⊔ wB ; a = M ∸ (wX + wA)
      in inj₂ (_ , _ , refl , refl ∷ refl ∷ refl ∷ nl (mvPS hdr a wX) (mvPS-nl hdr a wX)
           (refl ∷ nl (mvPS (Mc ∸ wA) (a + wX) wA) (mvPS-nl (Mc ∸ wA) (a + wX) wA)
             (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ nl (mvSP (M ∸ wB) (Mc ∸ wB) wB) (mvSP-nl (M ∸ wB) (Mc ∸ wB) wB) (refl ∷ []))))
    tramp-nl j (kbodyω {X = X} ds b γ) = inj₂ (_ , _ , refl , refl ∷ cA (wsz X) ∷ refl ∷ refl ∷ refl ∷ [])
      where cA : ∀ w → mark (contentsAddr w) ≡ nothing
            cA zero    = refl
            cA (suc w) = refl
    tramp-nl j (kobs ds F S) =
      let wP = wsz (cty (F , S)) ; wL = wsz (LF∙ F (Nu F)) ; M = wP ⊔ wL ; Mc = 1 ⊔ wL
      in inj₂ (_ , _ , refl , refl ∷ refl ∷ refl ∷ nl (mvPS hdr (M ∸ wP) wP) (mvPS-nl hdr (M ∸ wP) wP)
           (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ nl (mvSP (M ∸ wL) (Mc ∸ wL) wL) (mvSP-nl (M ∸ wL) (Mc ∸ wL) wL) (refl ∷ [])))
    tramp-nl j (kcopy T₀) =
      let w = wsz T₀
      in inj₂ (_ , _ , refl , refl ∷ refl ∷ refl ∷ refl ∷ cA w ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl
         ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl
         ∷ nl (mvSP 0 hdr w) (mvSP-nl 0 hdr w) (refl ∷ refl ∷ refl ∷ refl ∷ []))
      where cA : ∀ w → mark (contentsAddr w) ≡ nothing
            cA zero    = refl
            cA (suc w) = refl
    tramp-nl j (kfree T₀) =
      let w = wsz T₀
      in inj₂ (_ , _ , refl , refl ∷ refl ∷ nl (mvPS hdr 0 w) (mvPS-nl hdr 0 w) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))
    tramp-nl j (kfold ds F alg) = inj₁ refl
    tramp-nl j (ktr1 ds b γ) = inj₁ refl
    tramp-nl j (ktrω ds b γ) = inj₁ refl
    tramp-nl j (ktro ds F S) = inj₁ refl
    tramp-nl j (ktrc X C)    = inj₁ refl
    tramp-nl j (ktrf X C)    = inj₁ refl

    -- a block's prologue: its entry, the saves, the copies in
    view-nl : ∀ t φ → NoLab (view-in t φ)
    view-nl nothing  φ = []
    view-nl (just E) φ = refl ∷ mvPS-nl 0 0 (wsz E)
