-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LabelsI — plan 0.146 B1.4b (D417, step 3): the image's jump
-- labels, part 3: image-wide.
--
-- Block `j`'s labels are `jl j k` (owner `nameOf j`), the start's
-- `jl j₀ k`; `nameOf` is injective (postulate-free: `showNat` is
-- `fromList ∘ charsInBase 10`, and the builtin `primStringFromListInjective`
-- is `--safe`). So the image's labels are distinct (`image-dst`), and a
-- jump finds its label where it is defined (`image-label`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; suc-injective; <-irrefl; +-suc; m<m+n)
open import Data.Nat.Show.Properties using (charsInBase-injective)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate) renaming (map to All-map; head to All-head)
open import Data.List.Relation.Unary.All.Properties using (++⁻ʳ) renaming (++⁺ to All-++⁺; map⁺ to All-map⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to AP-map)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to AP-++⁺; map⁺ to AP-map⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Agda.Builtin.String.Properties using (primStringFromListInjective)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (LabelId; module LabelId; ≡ᵇᴵ-refl)
open import Once.CCC.Codegen.LabelDefs using (Dst)

module Once.LinCore.LabelsI
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.Labels fmt ans bw
open import Once.LinCore.LabelsC fmt ans bw
open import Once.LinCore.LowAt fmt ans bw using (Inside)

------------------------------------------------------------------------
-- 1. NAMES ARE INJECTIVE.
------------------------------------------------------------------------

private
  part₂ : CanonicalName → String
  part₂ (canonical [])            = ""
  part₂ (canonical (_ ∷ []))      = ""
  part₂ (canonical (_ ∷ s ∷ _))   = s

nameOf-inj : ∀ {i j} → nameOf i ≡ nameOf j → i ≡ j
nameOf-inj {i} {j} e = charsInBase-injective 10 i j (primStringFromListInjective _ _ (cong part₂ e))

jl-inj : ∀ {j j′ m m′} → jl j m ≡ jl j′ m′ → j ≡ j′ × m ≡ m′
jl-inj e = nameOf-inj (cong LabelId.owner e) , suc-injective (cong LabelId.idx e)

------------------------------------------------------------------------
-- 2. ★ IN A TRACE WITH DISTINCT LABELS, A LABEL IS FOUND WHERE IT IS DEFINED.
------------------------------------------------------------------------

module Find {FS : FrameSemantics} where
  open FlatMachine {FS} using (label-of?; find-label; fl-go; fl-label-match)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (find-label-distrib)
  open LabsC {FS} using (Labs; Labs-++)

  LDst : AbstractTrace → Set
  LDst xs = AllPairs _≢_ (Labs xs)

  -- distinct: what comes before `y` differs from it
  ap-pre : ∀ (xs : List LabelId) {y ys} → AllPairs _≢_ (xs ++ y ∷ ys) → All (_≢ y) xs
  ap-pre []       _          = []
  ap-pre (x ∷ xs) (px ∷ pxs) = All-head (++⁻ʳ xs px) ∷ ap-pre xs pxs

  -- no label of `xs` is `l`, read instruction by instruction
  skip : ∀ {l} xs → All (_≢ l) (Labs xs) → All (λ x → ¬ (label-of? x ≡ just l)) xs
  skip [] _ = []
  skip (x ∷ xs) p with label-of? x in eq
  ... | just m  = (λ e → All-head p (just-injective (trans (sym eq) e))) ∷ skip xs (Data.List.Relation.Unary.All.tail p)
    where import Data.List.Relation.Unary.All
  ... | nothing = (λ e → nj (trans (sym eq) e)) ∷ skip xs p
    where nj : ∀ {l′ : LabelId} → nothing ≢ just l′
          nj ()

  found : ∀ pre l post → LDst (pre ++ instr-ctrl (c-label l) ∷ post)
        → find-label (pre ++ instr-ctrl (c-label l) ∷ post) l ≡ just (length pre)
  found pre l post d =
    find-label-distrib pre (instr-ctrl (c-label l) ∷ []) post l 0
      (skip pre (ap-pre (Labs pre) (subst (AllPairs _≢_) (Labs-++ pre (instr-ctrl (c-label l) ∷ post)) d)))
      (cong (λ b → fl-label-match b [] l 0) (≡ᵇᴵ-refl l))

  found-in : ∀ {img l rest} → LDst img → (ins : Inside img (instr-ctrl (c-label l) ∷ rest))
           → find-label img l ≡ just (length (proj₁ ins))
  found-in {l = l} {rest} d (pre , post , refl) = found pre l (rest ++ post) d

------------------------------------------------------------------------
-- 3. ★ THE IMAGE'S LABELS ARE DISTINCT.
------------------------------------------------------------------------

-- a label of a block in `[lo, hi)`
InB : ℕ → ℕ → LabelId → Set
InB lo hi l = Σ ℕ λ j → Σ ℕ λ k → lo ≤ j × j < hi × l ≡ jl j k

map-dst : ∀ j {is} → Dst is → AllPairs _≢_ (map (jl j) is)
map-dst j d = AP-map⁺ (AP-map (λ {i} {i′} (ne : i ≢ i′) (e : jl j i ≡ jl j i′) → ne (proj₂ (jl-inj {j} {j} {i} {i′} e))) d)

-- block `j`'s labels against later blocks'
sep : ∀ {j i hi r} → InB (suc j) hi r → jl j i ≢ r
sep (j′ , k , lo , _ , refl) e = <-irrefl (proj₁ (jl-inj e)) lo

-- the start's labels (`j₀`) against the blocks' (below `j₀`)
sep₀ : ∀ {j₀ i r} → InB 0 j₀ r → jl j₀ i ≢ r
sep₀ (j′ , k , _ , hi , refl) e = <-irrefl (sym (proj₁ (jl-inj e))) hi

module Img {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing) where
  open FlatMachine {FS} using (label-of?; find-label)
  open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
  open Program ds f using (U; blocks-in; start-in)
  open ProgramRun ds f using (ncty)
  open In U
  open Program′ ds f ldConst
  open NoLabels {FS}
  open Free U ncty ldConst ld-nl
  open LabsC {FS}
  open C U ncty ldConst ld-nl
  open Find {FS}

  -- a trampoline's labels: none
  tramp-labs : ∀ {j xs} → TrampShape j xs → Labs xs ≡ []
  tramp-labs (inj₁ refl)              = refl
  tramp-labs (inj₂ (_ , _ , refl , p)) = Labs-nl p

  -- ★ block `j`'s code: its entry `e-fn (nameOf j)`, then labels distinct and no entry
  BlockOk : ℕ → AbstractTrace → Set
  BlockOk j xs = Σ ℕ λ n → Σ ℕ λ b → Σ AbstractTrace λ r → xs ≡ instr-ctrl (c-entry (e-fn (nameOf j)) b) ∷ r × Ok j 0 n r

  blockOk : ∀ j (a : AKey) (ev : BIn a) → BlockOk j (lowBlock j (proj₂ a) ev)
  blockOk j (bsig t A B , κ) ev =
    let φ = frameOf (blockᴵ κ) ; M = wsz A ⊔ wsz B ; b = fbudget φ
        fin = restore-input (sv₁ φ) ∷ mvSP (Tp φ (B ∷ [])) (M ∸ wsz B) (wsz B) ++ instr-ctrl (c-ret b) ∷ []
        fin-nl = refl ∷ nl (mvSP (Tp φ (B ∷ [])) (M ∸ wsz B) (wsz B)) (mvSP-nl _ _ _) (refl ∷ [])
        r = lowC-ok φ j 0 fin fin-nl (blockᴵ κ) ev
    in _ , _ , _ , refl , ok-pre (store-at-slot (sv₂ φ) ∷ mov-to-output ∷ store-at-slot (sv₁ φ) ∷ [])
             (refl ∷ refl ∷ refl ∷ [])
             (ok-pre (mvPS (M ∸ wsz A) (Tp φ (A ∷ [])) (wsz A)) (mvPS-nl _ _ _)
               (ok-pre (view-in t φ) (view-nl t φ) (proj₂ r)))

  -- ★ the blocks from `j`: distinct labels, each a block's in `[j, j + |ks|)`
  blocks-lab : ∀ ks (ev : ∀ {κ} → κ ∈ ks → BIn κ) j
             → AllPairs _≢_ (Labs (blocksOf ks ev j)) × All (InB j (j + length ks)) (Labs (blocksOf ks ev j))
  blocks-lab []             ev j = [] , []
  blocks-lab ((σ , κ) ∷ ks) ev j = finish (blockOk j (σ , κ) (ev (here refl))) (blocks-lab ks (λ p → ev (there p)) (suc j))
    where
      rest = blocksOf ks (λ p → ev (there p)) (suc j)
      lowB = lowBlock j κ (ev (here refl))
      n′ = length ks
      widen-in : ∀ {r} → InB (suc j) (suc j + n′) r → InB j (j + suc n′) r
      widen-in (j′ , k , lo , hi , e) = j′ , k , ≤-trans (n≤1+n j) lo , subst (j′ <_) (sym (+-suc j n′)) hi , e
      finish : BlockOk j lowB
             → AllPairs _≢_ (Labs rest) × All (InB (suc j) (suc j + n′)) (Labs rest)
             → AllPairs _≢_ (Labs (lowB ++ tramp j κ ++ rest)) × All (InB j (j + suc n′)) (Labs (lowB ++ tramp j κ ++ rest))
      finish (_ , _ , _ , e , o) (dR , wR) =
        let eqL : Labs (lowB ++ tramp j κ ++ rest) ≡ map (jl j) (idxs o) ++ Labs rest
            eqL = trans (Labs-++ lowB (tramp j κ ++ rest))
                    (cong₂ _++_ (trans (cong Labs e) (eq o)) (trans (Labs-++ (tramp j κ) rest) (cong (_++ Labs rest) (tramp-labs {j} (tramp-nl j κ)))))
            cross = tabulate {xs = idxs o} (λ _ → All-map sep wR)
            here-in = All-map⁺ (tabulate {xs = idxs o} (λ {i} _ → j , i , ≤-refl , m<m+n j (s≤s z≤n) , refl))
        in subst (AllPairs _≢_) (sym eqL) (AP-++⁺ (map-dst j (dst o)) dR (All-map⁺ cross))
         , subst (All (InB j (j + suc n′))) (sym eqL) (All-++⁺ here-in (All-map widen-in wR))

  -- ★ the image's labels are distinct
  image-dst : LDst image
  image-dst = finish (lowC-ok φ j₀ 0 (instr-ctrl c-leave ∷ []) (refl ∷ []) main (start-in {[]} {[]} tt))
                     (blocks-lab (allK U) blocks-in 0)
    where
      main = compᴵ ds f {[]} {[]} end
      φ = frameOf main
      code = proj₁ (lowC φ j₀ 0 (instr-ctrl c-leave ∷ []) main (start-in {[]} {[]} tt))
      bl = blocksOf (allK U) blocks-in 0
      finish : Good j₀ 0 (lowC φ j₀ 0 (instr-ctrl c-leave ∷ []) main (start-in {[]} {[]} tt))
             → AllPairs _≢_ (Labs bl) × All (InB 0 j₀) (Labs bl)
             → AllPairs _≢_ (Labs (code ++ bl))
      finish (_ , o) (dB , wB) =
        subst (AllPairs _≢_) (sym (trans (Labs-++ code bl) (cong (_++ Labs bl) (eq o))))
          (AP-++⁺ (map-dst j₀ (dst o)) dB (All-map⁺ (tabulate {xs = idxs o} (λ _ → All-map sep₀ wB))))

  -- ★ a jump label is found where it is defined
  image-label : ∀ {l rest} (ins : Inside image (instr-ctrl (c-label l) ∷ rest))
              → find-label image l ≡ just (length (proj₁ ins))
  image-label ins = found-in image-dst ins
