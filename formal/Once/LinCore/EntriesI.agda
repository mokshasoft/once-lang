-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.EntriesI — plan 0.146 B1.4b (D417, step 3): the image's
-- callable entries and its block layout.
--
-- Block `j` is entered by name (`e-fn (nameOf j)`, its first instruction),
-- its trampoline through a cell's code word (`e-thunk (tl j)`); the lowered
-- code defines no entry (`Ok`'s `ne`). So the image's entries are distinct
-- (`image-edst`), every key's block and trampoline sit in the image at its
-- index (`image-at`), and a call lands on them (`image-fn`, `image-tramp`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; <-irrefl; +-suc; +-identityʳ; m<m+n)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate) renaming (map to All-map; head to All-head; tail to All-tail)
open import Data.List.Relation.Unary.All.Properties using (++⁻ʳ) renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to AP-++⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Name using (CanonicalName)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (LabelId; module LabelId; EntryId; e-thunk; e-fn; _≡ᵇᴱ_; ≡ᵇᴱ-true; ≡ᵇᴱ-refl)

module Once.LinCore.EntriesI
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
open import Once.LinCore.LabelsI fmt ans bw using (nameOf-inj; module Img)
open import Once.LinCore.LowAt fmt ans bw using (Inside; in-trans; in-r)

------------------------------------------------------------------------
-- 1. INSIDE, UP TO AN EQUATION OF THE PART (its prefix unchanged).
------------------------------------------------------------------------

in-≡ : ∀ {big small small′} (ins : Inside big small) → small ≡ small′
     → Σ (Inside big small′) λ ins′ → proj₁ ins′ ≡ proj₁ ins
in-≡ (pre , post , e) refl = (pre , post , e) , refl

------------------------------------------------------------------------
-- 2. ★ IN A TRACE WITH DISTINCT ENTRIES, AN ENTRY IS FOUND WHERE IT IS DEFINED.
------------------------------------------------------------------------

module FindE {FS : FrameSemantics} where
  open FlatMachine {FS} using (entry-of?; ft-go; ft-match; find-entry; ft-go-++-miss)
  open LabsC {FS} using (Ents; Ents-++)

  EDst : AbstractTrace → Set
  EDst xs = AllPairs _≢_ (Ents xs)

  ap-pre : ∀ (xs : List EntryId) {y ys} → AllPairs _≢_ (xs ++ y ∷ ys) → All (_≢ y) xs
  ap-pre []       _          = []
  ap-pre (x ∷ xs) (px ∷ pxs) = All-head (++⁻ʳ xs px) ∷ ap-pre xs pxs

  -- no entry of `xs` is `e`: the scan misses
  miss : ∀ {e} xs i → All (_≢ e) (Ents xs) → ft-go xs e i ≡ nothing
  miss [] i _ = refl
  miss {e} (x ∷ xs) i p with entry-of? x
  ... | just m  = fm (m ≡ᵇᴱ e) (≡ᵇᴱ-true m e)
    where
      fm : ∀ b → (b ≡ true → m ≡ e) → ft-match b xs e i ≡ nothing
      fm true  h = ⊥-elim (All-head p (h refl))
      fm false _ = miss xs (suc i) (All-tail p)
  ... | nothing = miss xs (suc i) p

  found-e : ∀ pre e b post → EDst (pre ++ instr-ctrl (c-entry e b) ∷ post)
          → find-entry (pre ++ instr-ctrl (c-entry e b) ∷ post) e ≡ just (length pre)
  found-e pre e b post d =
    trans (ft-go-++-miss pre (instr-ctrl (c-entry e b) ∷ post) e 0
            (miss pre 0 (ap-pre (Ents pre) (subst (AllPairs _≢_) (Ents-++ pre (instr-ctrl (c-entry e b) ∷ post)) d))))
      (trans (cong (λ z → ft-match z post e (length pre + 0)) (≡ᵇᴱ-refl e))
             (cong just (+-identityʳ (length pre))))

  found-e-in : ∀ {img e b rest} → EDst img → (ins : Inside img (instr-ctrl (c-entry e b) ∷ rest))
             → find-entry img e ≡ just (length (proj₁ ins))
  found-e-in {e = e} {b} {rest} d (pre , post , refl) = found-e pre e b (rest ++ post) d

------------------------------------------------------------------------
-- 3. ★ THE IMAGE'S ENTRIES ARE DISTINCT.
------------------------------------------------------------------------

-- block `j`'s entries: its own and its trampoline's
OfJ : ℕ → EntryId → Set
OfJ j e = e ≡ e-fn (nameOf j) ⊎ e ≡ e-thunk (tl j)

private
  own : EntryId → CanonicalName
  own (e-fn f)    = f
  own (e-thunk l) = LabelId.owner l

ofj-sep : ∀ {j j′ e e′} → OfJ j e → OfJ j′ e′ → j ≢ j′ → e ≢ e′
ofj-sep (inj₁ refl) (inj₁ refl) ne q = ne (nameOf-inj (cong own q))
ofj-sep (inj₁ refl) (inj₂ refl) ne ()
ofj-sep (inj₂ refl) (inj₁ refl) ne ()
ofj-sep (inj₂ refl) (inj₂ refl) ne q = ne (nameOf-inj (cong own q))

-- an entry of a block in `[lo, hi)`
EnB : ℕ → ℕ → EntryId → Set
EnB lo hi e = Σ ℕ λ j → lo ≤ j × j < hi × OfJ j e

module ImgE {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
            (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
            (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing) where
  open FlatMachine {FS} using (find-entry; find-fn; find-thunk)
  open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
  open Program ds f using (U; blocks-in; start-in)
  open ProgramRun ds f using (ncty)
  open In U
  open Program′ ds f ldConst
  open NoLabels {FS}
  open Free U ncty ldConst ld-nl
  open LabsC {FS}
  open C U ncty ldConst ld-nl
  open Img {FS} ds f ldConst ld-nl using (BlockOk; blockOk)
  open FindE {FS}

  -- a block's entry, then its trampoline's (if any)
  seg-ents : ∀ {j xs} → TrampShape j xs
           → AllPairs _≢_ (e-fn (nameOf j) ∷ Ents xs) × All (OfJ j) (e-fn (nameOf j) ∷ Ents xs)
  seg-ents (inj₁ refl)              = ([] ∷ []) , (inj₁ refl ∷ [])
  seg-ents {j} (inj₂ (_ , r , refl , p)) =
    subst (λ z → AllPairs _≢_ (e-fn (nameOf j) ∷ e-thunk (tl j) ∷ z) × All (OfJ j) (e-fn (nameOf j) ∷ e-thunk (tl j) ∷ z))
      (sym (Ents-nl p))
      ((((λ ()) ∷ []) ∷ [] ∷ []) , (inj₁ refl ∷ inj₂ refl ∷ []))

  -- ★ the blocks from `j`: distinct entries, each a block's in `[j, j + |ks|)`
  blocks-ent : ∀ ks (ev : ∀ {κ} → κ ∈ ks → BIn κ) j
             → AllPairs _≢_ (Ents (blocksOf ks ev j)) × All (EnB j (j + length ks)) (Ents (blocksOf ks ev j))
  blocks-ent []             ev j = [] , []
  blocks-ent ((σ , κ) ∷ ks) ev j =
    finish (blockOk j (σ , κ) (ev (here refl))) (seg-ents {j} (tramp-nl j κ)) (blocks-ent ks (λ p → ev (there p)) (suc j))
    where
      rest = blocksOf ks (λ p → ev (there p)) (suc j)
      lowB = lowBlock j κ (ev (here refl))
      S = e-fn (nameOf j) ∷ Ents (tramp j κ)
      n′ = length ks
      widen-in : ∀ {r} → EnB (suc j) (suc j + n′) r → EnB j (j + suc n′) r
      widen-in (j′ , lo , hi , o) = j′ , ≤-trans (n≤1+n j) lo , subst (j′ <_) (sym (+-suc j n′)) hi , o
      sep : ∀ {e r} → OfJ j e → EnB (suc j) (suc j + n′) r → e ≢ r
      sep o (j′ , lo , _ , o′) = ofj-sep o o′ (λ q → <-irrefl q lo)
      finish : BlockOk j lowB
             → AllPairs _≢_ S × All (OfJ j) S
             → AllPairs _≢_ (Ents rest) × All (EnB (suc j) (suc j + n′)) (Ents rest)
             → AllPairs _≢_ (Ents (lowB ++ tramp j κ ++ rest)) × All (EnB j (j + suc n′)) (Ents (lowB ++ tramp j κ ++ rest))
      finish (_ , _ , r , e , o) (dS , wS) (dR , wR) =
        let eqE : Ents (lowB ++ tramp j κ ++ rest) ≡ S ++ Ents rest
            eqE = trans (Ents-++ lowB (tramp j κ ++ rest))
                    (trans (cong (_++ Ents (tramp j κ ++ rest)) (trans (cong Ents e) (cong (e-fn (nameOf j) ∷_) (ne o))))
                           (cong (e-fn (nameOf j) ∷_) (Ents-++ (tramp j κ) rest)))
            cross = All-map (λ oj → All-map (sep oj) wR) wS
            here-in = All-map (λ {e} oj → j , ≤-refl , m<m+n j (s≤s z≤n) , oj) wS
        in subst (AllPairs _≢_) (sym eqE) (AP-++⁺ dS dR cross)
         , subst (All (EnB j (j + suc n′))) (sym eqE) (All-++⁺ here-in (All-map widen-in wR))

  -- the start's code: no entry
  main = compᴵ ds f {[]} {[]} end
  φ₀ = frameOf main
  code₀ = proj₁ (lowC φ₀ j₀ 0 (instr-ctrl c-leave ∷ []) main (start-in {[]} {[]} tt))
  bl = blocksOf (allK U) blocks-in 0

  code₀-ne : Ents code₀ ≡ []
  code₀-ne = ne (proj₂ (lowC-ok φ₀ j₀ 0 (instr-ctrl c-leave ∷ []) (refl ∷ []) main (start-in {[]} {[]} tt)))

  -- ★ the image's entries are distinct
  image-edst : EDst image
  image-edst = subst (AllPairs _≢_) (sym (trans (Ents-++ code₀ bl) (cong (_++ Ents bl) code₀-ne)))
                 (proj₁ (blocks-ent (allK U) blocks-in 0))

  ----------------------------------------------------------------------
  -- 4. ★ THE LAYOUT: every key's block and trampoline, at its index.
  ----------------------------------------------------------------------

  blocks-at : ∀ ks (ev : ∀ {κ} → κ ∈ ks → BIn κ) j {σ} {κ : Key σ} (p : (σ , κ) ∈ ks)
            → Inside (blocksOf ks ev j) (lowBlock (j + idx p) κ (ev p) ++ tramp (j + idx p) κ)
  blocks-at ((σ , κ) ∷ ks) ev j (here refl) =
    subst (λ z → Inside (blocksOf ((σ , κ) ∷ ks) ev j) (lowBlock z κ (ev (here refl)) ++ tramp z κ)) (sym (+-identityʳ j))
      ([] , blocksOf ks (λ p → ev (there p)) (suc j) ,
       sym (++-assoc (lowBlock j κ (ev (here refl))) (tramp j κ) (blocksOf ks (λ p → ev (there p)) (suc j))))
  blocks-at ((σ′ , κ′) ∷ ks) ev j {κ = κ} (there p) =
    let lowB = lowBlock j κ′ (ev (here refl)) ; rest = blocksOf ks (λ q → ev (there q)) (suc j)
    in in-trans (in-trans (in-r lowB (tramp j κ′ ++ rest)) (in-r (tramp j κ′) rest))
         (subst (λ z → Inside rest (lowBlock z κ (ev (there p)) ++ tramp z κ)) (sym (+-suc j (idx p)))
           (blocks-at ks (λ q → ev (there q)) (suc j) p))

  image-at : ∀ {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U)
           → Inside image (lowBlock (idx p) κ (blocks-in p) ++ tramp (idx p) κ)
  image-at p = in-trans (in-r (instr-ctrl (c-start (fbudget φ₀)) ∷ code₀) bl) (blocks-at (allK U) blocks-in 0 p)

  ----------------------------------------------------------------------
  -- 5. ★ A CALL LANDS ON ITS BLOCK; A CODE WORD ON ITS TRAMPOLINE.
  ----------------------------------------------------------------------

  -- by name: block `idx p`'s first instruction
  image-fn : ∀ {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U)
           → find-fn image (nameOf (idx p)) ≡ just (length (proj₁ (image-at p)))
  image-fn {σ} {κ} p = at-entry (blockOk (idx p) (σ , κ) (blocks-in p))
    where
      at-entry : BlockOk (idx p) (lowBlock (idx p) κ (blocks-in p)) → find-fn image (nameOf (idx p)) ≡ just (length (proj₁ (image-at p)))
      at-entry (_ , b , r , e , _) =
        let (ins , pe) = in-≡ (image-at p) (cong (_++ tramp (idx p) κ) e)
        in trans (found-e-in image-edst ins) (cong (λ z → just (length z)) pe)

  -- through a code word: the trampoline after the block
  image-tramp : ∀ {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) {b r}
              → tramp (idx p) κ ≡ instr-ctrl (c-entry (e-thunk (tl (idx p))) b) ∷ r
              → find-thunk image (tl (idx p)) ≡ just (length (proj₁ (image-at p)) + length (lowBlock (idx p) κ (blocks-in p)))
  image-tramp {σ} {κ} p e =
    let lowB = lowBlock (idx p) κ (blocks-in p)
        (ins , pe) = in-≡ (in-trans (image-at p) (in-r lowB (tramp (idx p) κ))) e
    in trans (found-e-in image-edst ins)
         (cong just (trans (cong length pe) (Data.List.Properties.length-++ (proj₁ (image-at p)))))
    where import Data.List.Properties
