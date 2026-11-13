-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LabelsC — plan 0.146 B1.4b (D417, step 3): the image's jump
-- labels, part 2: a lowered code's labels.
--
-- `lowC φ j m fin c` from label counter `m` to `n` defines exactly labels
-- `jl j k` of block `j`, each `k` in the window `[m, n)` and no two alike
-- (`Ok`): the counter threads distinct indices, a `case`/`ecase` takes one,
-- a loop three. The algebra is `CCC.Codegen.LabelDefs`' (`Dst`, `Dj`,
-- `Win`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; m≤n⇒m≤1+n)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Codegen.LabelDefs using (Dst; Dj; Win; dj-sym; dj-++ʳ; dst-++; dj-win; win-weaken; fresh-below)

module Once.LinCore.LabelsC
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.Labels fmt ans bw

module LabsC {FS : FrameSemantics} where
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (label-of?)
  open NoLabels {FS}

  ----------------------------------------------------------------------
  -- 1. A TRACE'S LABELS.
  ----------------------------------------------------------------------

  lab : Maybe LabelId → List LabelId → List LabelId
  lab (just l) r = l ∷ r
  lab nothing  r = r

  Labs : AbstractTrace → List LabelId
  Labs []       = []
  Labs (x ∷ xs) = lab (label-of? x) (Labs xs)

  Labs-++ : ∀ xs ys → Labs (xs ++ ys) ≡ Labs xs ++ Labs ys
  Labs-++ []       ys = refl
  Labs-++ (x ∷ xs) ys = go (label-of? x)
    where
      go : ∀ mo → lab mo (Labs (xs ++ ys)) ≡ lab mo (Labs xs) ++ Labs ys
      go (just l) = cong (l ∷_) (Labs-++ xs ys)
      go nothing  = Labs-++ xs ys

  Labs-nl : ∀ {xs} → NoLab xs → Labs xs ≡ []
  Labs-nl {[]}     []      = refl
  Labs-nl {x ∷ xs} (e ∷ p) = go (label-of? x) (mark-l x e)
    where
      go : ∀ mo → mo ≡ nothing → lab mo (Labs xs) ≡ []
      go nothing refl = Labs-nl p

  ----------------------------------------------------------------------
  -- 2. ★ BLOCK `j`'s LABELS IN A WINDOW, DISTINCT.
  ----------------------------------------------------------------------

  record Ok (j a b : ℕ) (xs : AbstractTrace) : Set where
    constructor ok
    field
      idxs : List ℕ
      eq  : Labs xs ≡ map (jl j) idxs
      win : Win a b idxs
      dst : Dst idxs
  open Ok public

  ok-nl : ∀ {j a b xs} → NoLab xs → Ok j a b xs
  ok-nl p = ok [] (Labs-nl p) [] []

  widen : ∀ {j a b a′ b′ xs} → a′ ≤ a → b ≤ b′ → Ok j a b xs → Ok j a′ b′ xs
  widen l r (ok ks e w d) = ok ks e (win-weaken l r w) d

  join : ∀ {j a b xs ys} (o₁ : Ok j a b xs) (o₂ : Ok j a b ys) → Dj (idxs o₁) (idxs o₂) → Ok j a b (xs ++ ys)
  join {j} {xs = xs} {ys} (ok k₁ e₁ w₁ d₁) (ok k₂ e₂ w₂ d₂) dj =
    ok (k₁ ++ k₂) (trans (Labs-++ xs ys) (trans (cong₂ _++_ e₁ e₂) (sym (map-++ (jl j) k₁ k₂))))
       (All-++⁺ w₁ w₂) (dst-++ d₁ d₂ dj)

  -- label-free code in front
  ok-pre : ∀ {j a b xs} P → NoLab P → Ok j a b xs → Ok j a b (P ++ xs)
  ok-pre P p o = join (ok-nl p) o []

  -- a label defined in front
  ok-lab : ∀ {j a b xs} k → a ≤ k → k < b → (o : Ok j a b xs) → All (k ≢_) (idxs o) → Ok j a b (instr-ctrl (c-label (jl j k)) ∷ xs)
  ok-lab {j} k a≤k k<b (ok ks e w d) fr = ok (k ∷ ks) (cong (jl j k ∷_) e) ((a≤k , k<b) ∷ w) (fr ∷ d)

  -- a code's counter and labels
  Good : ℕ → ℕ → AbstractTrace × ℕ → Set
  Good j m (xs , n) = m ≤ n × Ok j m n xs

  plainOk : ∀ {j m xs n} → n ≡ m → NoLab xs → Good j m (xs , n)
  plainOk refl p = ≤-refl , ok-nl p

  ----------------------------------------------------------------------
  -- 3. ★ THE LOWERING'S LABELS.
  ----------------------------------------------------------------------

  module C (U : Univ)
           (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → mark (ldConst v) ≡ nothing) where
    open In U
    open Lowering U ncty ldConst
    open Free U ncty ldConst ld-nl

    -- one stretch, then the next
    seqG : ∀ {j m xs ys n n′} → Good j m (xs , n) → Good j n (ys , n′) → Good j m (xs ++ ys , n′)
    seqG {j} (l₁ , o₁) (l₂ , o₂) =
      ≤-trans l₁ l₂ , join (widen ≤-refl l₂ o₁) (widen l₁ ≤-refl o₂) (dj-win (win o₁) (win o₂) ≤-refl)

    -- ★ a branch: the `inr` side from `m + 1`, the label `m`, the `inl` side
    branchG : ∀ {j m P Q R ys zs n₂ n₁} → NoLab P → NoLab Q → NoLab R
            → Good j (suc m) (ys , n₂) → Good j n₂ (zs , n₁)
            → Good j m (P ++ ys ++ instr-ctrl (c-label (jl j m)) ∷ Q ++ zs , n₁)
    branchG {j} {m} {P} {Q} pP pQ pR (l₂ , o₂) (l₁ , o₁) =
      let m≤n₂ = ≤-trans (n≤1+n m) l₂
          oz = widen m≤n₂ ≤-refl (join (ok-nl pQ) o₁ [])
          ol = ok-lab m ≤-refl (≤-trans l₂ l₁) oz (fresh-below l₂ (win o₁))
          oy = widen (n≤1+n m) l₁ o₂
          oyl = join oy ol (dj-++ʳ (dj-sym (fresh-below (s≤s ≤-refl) (win o₂) ∷ [])) (dj-win (win o₂) (win o₁) ≤-refl))
      in ≤-trans (n≤1+n m) (≤-trans l₂ l₁) , join (ok-nl pP) oyl []

    mutual
      lowI-ok : ∀ φ j m {sh sh′} (i : Insᴵ sh sh′) (ei : IIn i) → Good j m (lowI φ j m i ei)
      -- every other instruction: label-free, the counter untouched (the
      -- as-pattern passes the matched instruction, implicits and all)
      lowI-ok φ j m i@unpair ei  = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@pair ei    = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@unit ei    = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@untag ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@untag₁ ei  = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@tag₁ ei    = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@elift ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@epop ei    = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@stuck ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@swap ei    = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@(prim ds g) ei = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@elend ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@eunlend ei = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@efst ei    = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@esnd ei    = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@eout ei    = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@eoutq ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@eapp ei    = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@eword ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@(call {bsig nothing A B} κ) ei  = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@(call {bsig (just E) A B} κ) ei = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@icall ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@icallω ei  = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@(iobs ds) ei = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@ccopy ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@ncopy ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@cfree ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@nfree ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@open1 ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@openω ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@nopen ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@copen ei   = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@reclose ei = plainOk refl (lowI-nl φ j m i ei tt)
      lowI-ok φ j m i@fopen ei   = plainOk refl (lowI-nl φ j m i ei tt)
      -- ★ the loop: its head `m`, the body from `m + 3`, the dispatch `m + 1`, the exit `m + 2`
      lowI-ok φ j m (loop {E} {Es} {A} {B} {S} b) eb =
        let Ld = jl j (suc m)
            t = Tp φ ((B ⊕t A) ∷ S) ; bot = Tp φ S
            MA = mvSSd (suc t) (bot ∸ wsz A) (wsz A) ; MB = mvSSd (suc t) (bot ∸ wsz B) (wsz B)
            (lb , ob) = lowC-ok φ j (suc (suc (suc m))) (instr-ctrl (c-jmp Ld) ∷ []) (refl ∷ []) b eb
            nb = proj₂ (lowC φ j (suc (suc (suc m))) (instr-ctrl (c-jmp Ld) ∷ []) b eb)
            m3≤ = lb
            m1≤3 = ≤-trans (n≤1+n (suc m)) (n≤1+n (suc (suc m)))
            -- the exit and its moves: `m + 2`, in `[m + 1, m + 3)`
            oi : Ok j (suc m) (suc (suc (suc m))) (instr-ctrl (c-label (jl j (suc (suc m)))) ∷ MB)
            oi = ok-lab (suc (suc m)) (n≤1+n _) ≤-refl (ok-nl (mvSSd-nl _ _ _)) []
            -- the dispatch: its label `m + 1`, the tag test, the `inr` moves, the jump back, the exit
            od : Ok j (suc m) (suc (suc (suc m)))
                    (instr-ctrl (c-label Ld) ∷ lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero (jl j (suc (suc m))))
                     ∷ MA ++ instr-ctrl (c-jmp (jl j m)) ∷ instr-ctrl (c-label (jl j (suc (suc m)))) ∷ MB)
            od = ok-lab (suc m) ≤-refl (n≤1+n _)
                   (ok-pre (lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero (jl j (suc (suc m)))) ∷ []) (refl ∷ refl ∷ refl ∷ [])
                     (ok-pre MA (mvSSd-nl _ _ _) (ok-pre (instr-ctrl (c-jmp (jl j m)) ∷ []) (refl ∷ []) oi)))
                   ((λ ()) ∷ [])
            -- the body (from `m + 3`), then the dispatch: in `[m + 1, nb)`
            obd = join (widen m1≤3 ≤-refl ob) (widen ≤-refl m3≤ od) (dj-sym (dj-win (win od) (win ob) ≤-refl))
        in ≤-trans (n≤1+n m) (≤-trans m1≤3 m3≤)
         , ok-lab m ≤-refl (≤-trans m1≤3 m3≤) (widen (n≤1+n m) ≤-refl obd) (fresh-below ≤-refl (win obd))

      lowC-ok : ∀ φ j m fin → NoLab fin → ∀ {sh T} (c : Codeᴵ sh T) (ev : CIn c) → Good j m (lowC φ j m fin c ev)
      lowC-ok φ j m fin nf end ev    = plainOk refl nf
      lowC-ok φ j m fin nf halted ev = plainOk refl []
      lowC-ok φ j m fin nf (i ⨾ c) (ei , ec) =
        seqG (lowI-ok φ j m i ei) (lowC-ok φ j (proj₂ (lowI φ j m i ei)) fin nf c ec)
      lowC-ok φ j m fin nf (case {Es} {A} {B} {S} c₁ c₂) (e₁ , e₂) =
        let t = Tp φ ((A ⊕t B) ∷ S) ; bot = Tp φ S
            l₂ = lowC φ j (suc m) fin c₂ e₂
        in branchG {P = lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero (jl j m)) ∷ mvSSd (suc t) (bot ∸ wsz B) (wsz B)}
             (refl ∷ refl ∷ refl ∷ mvSSd-nl _ _ _) (mvSSd-nl _ _ _) []
             (lowC-ok φ j (suc m) fin nf c₂ e₂) (lowC-ok φ j (proj₂ l₂) fin nf c₁ e₁)
      lowC-ok φ j m fin nf (ecase {E₁} {E₂} {Es} c₁ c₂) (e₁ , e₂) =
        let e = ws Es ; nb = e + wsz (E₁ ⊕t E₂)
            l₂ = lowC φ j (suc m) fin c₂ e₂
        in branchG {P = lea-slot e ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero (jl j m)) ∷ mvSS (suc e) nb (wsz E₂)}
             (refl ∷ refl ∷ refl ∷ mvSS-nl _ _ _) (mvSS-nl _ _ _) []
             (lowC-ok φ j (suc m) fin nf c₂ e₂) (lowC-ok φ j (proj₂ l₂) fin nf c₁ e₁)
