-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.AnsWrite — plan 0.146 B1.5 (D449): A SIGOP'S ANSWER IN MEMORY
-- IS THE IMAGE'S. `ArgDecode`'s mirror: the machine's in-place writer
-- (`writeTyped`, a sigop whose answer is a product or a sum) at a slot of a
-- frame writes the answer's words there — the image's (`VW`), a sum's padding
-- zero words — and nothing else: not the heap, not another frame, no slot of
-- the frame outside the answer's words.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; s≤s; z≤n)
import Data.Nat.Properties as NP
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Properties using (length-++; length-replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum
import Data.Maybe
import Once.Semantics.Machine
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
import Once.Spec.Type as ST
open import Once.Type using (fits-int; fits-float)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack)

module Once.LinCore.AnsWrite
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; int; float; ⟦_⟧b)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Values fmt bw using (MV; mvF; wsz)
open import Once.LinCore.Keys fmt bw using (Univ)
open import Once.LinCore.Words fmt ans bw using (module Rel)
open import Once.LinCore.Lower fmt bw using (flatB)
open import Once.LinCore.ArgDecode fmt ans bw using (tsize-wsz)

-- writing a value in place touches nothing else (no image words needed)
module Keep {FS : FrameSemantics} where
  open AbstractExec {FS} using (writeTyped; writeZeros; zero-word; tsize; sigop-store-at)
  open MemOps {FS} using (writeLoc)
  open LocState using (stackMem; heapMem)
  open FrameSemantics FS using (Frame)
  open import Once.LinCore.Moves {FS} using (store-other; store-frame)

  ----------------------------------------------------------------------
  -- 2. NOTHING ELSE: not the heap, not another frame, no other slot.
  ----------------------------------------------------------------------
  private
    out1 : ∀ k j → (j < k ⊎ k + 1 ≤ j) → ¬ k ≡ j
    out1 k j (inj₁ lt) refl = NP.<-irrefl refl lt
    out1 k j (inj₂ le) refl = NP.<-irrefl refl (subst (_≤ k) (NP.+-comm k 1) le)

  zeros-heap : ∀ n (f : Frame) k (s : LocState FS) → heapMem (writeZeros n (AtStack f k) s) ≡ heapMem s
  zeros-heap zero    f k s = refl
  zeros-heap (suc n) f k s = zeros-heap n f (suc k) (writeLoc s (AtStack f k) zero-word)

  zeros-frame : ∀ n (f : Frame) k (s : LocState FS) f′ j → ¬ f ≡ f′
              → stackMem (writeZeros n (AtStack f k) s) f′ j ≡ stackMem s f′ j
  zeros-frame zero    f k s f′ j ne = refl
  zeros-frame (suc n) f k s f′ j ne =
    trans (zeros-frame n f (suc k) (writeLoc s (AtStack f k) zero-word) f′ j ne) (store-frame s f k zero-word f′ j ne)

  zeros-out : ∀ n (f : Frame) k (s : LocState FS) j → (j < k ⊎ k + n ≤ j)
            → stackMem (writeZeros n (AtStack f k) s) f j ≡ stackMem s f j
  zeros-out zero    f k s j o = refl
  zeros-out (suc n) f k s j o =
    trans (zeros-out n f (suc k) (writeLoc s (AtStack f k) zero-word) j o′) (store-other s f k zero-word j (out1 k j o1))
    where
      o′ : j < suc k ⊎ suc k + n ≤ j
      o′ = Data.Sum.map NP.m<n⇒m<1+n (subst (_≤ j) (NP.+-suc k n)) o
      o1 : j < k ⊎ k + 1 ≤ j
      o1 = Data.Sum.map (λ lt → lt) (NP.≤-trans (NP.+-monoʳ-≤ k (s≤s z≤n))) o

  wt-heap : ∀ {A} (b : ST.Base ST.∅ₖ A) v (f : Frame) k (s : LocState FS)
          → heapMem (writeTyped A v (AtStack f k) s) ≡ heapMem s
  wt-heap (ST.b-var {i = ()} _) v f k s
  wt-heap ST.b-Unit    v f k s = refl
  wt-heap ST.b-Void    () f k s
  wt-heap ST.b-Int     v f k s = refl
  wt-heap ST.b-Float   v f k s = refl
  wt-heap (ST.b-* {A = A₁} a b) (x , y) f k s =
    trans (wt-heap b y f (tsize A₁ + k) (writeTyped A₁ x (AtStack f k) s)) (wt-heap a x f k s)
  wt-heap (ST.b-+ {A = A₁} {B = B₁} a b) (inj₁ x) f k s =
    trans (zeros-heap ((tsize A₁ ⊔ tsize B₁) ∸ tsize A₁) f (suc (tsize A₁) + k) (writeTyped A₁ x (AtStack f (suc k)) (writeLoc s (AtStack f k) (SV-Tag 0)))) (wt-heap a x f (suc k) (writeLoc s (AtStack f k) (SV-Tag 0)))
  wt-heap (ST.b-+ {A = A₁} {B = B₁} a b) (inj₂ y) f k s =
    trans (zeros-heap ((tsize A₁ ⊔ tsize B₁) ∸ tsize B₁) f (suc (tsize B₁) + k) (writeTyped B₁ y (AtStack f (suc k)) (writeLoc s (AtStack f k) (SV-Tag 1)))) (wt-heap b y f (suc k) (writeLoc s (AtStack f k) (SV-Tag 1)))

  wt-frame : ∀ {A} (b : ST.Base ST.∅ₖ A) v (f : Frame) k (s : LocState FS) f′ j → ¬ f ≡ f′
           → stackMem (writeTyped A v (AtStack f k) s) f′ j ≡ stackMem s f′ j
  wt-frame (ST.b-var {i = ()} _) v f k s f′ j ne
  wt-frame ST.b-Unit    v f k s f′ j ne = refl
  wt-frame ST.b-Void    () f k s f′ j ne
  wt-frame ST.b-Int     v f k s f′ j ne = store-frame s f k _ f′ j ne
  wt-frame ST.b-Float   v f k s f′ j ne = store-frame s f k _ f′ j ne
  wt-frame (ST.b-* {A = A₁} a b) (x , y) f k s f′ j ne =
    trans (wt-frame b y f (tsize A₁ + k) (writeTyped A₁ x (AtStack f k) s) f′ j ne) (wt-frame a x f k s f′ j ne)
  wt-frame (ST.b-+ {A = A₁} {B = B₁} a b) (inj₁ x) f k s f′ j ne =
    trans (zeros-frame ((tsize A₁ ⊔ tsize B₁) ∸ tsize A₁) f (suc (tsize A₁) + k) (writeTyped A₁ x (AtStack f (suc k)) (writeLoc s (AtStack f k) (SV-Tag 0))) f′ j ne)
          (trans (wt-frame a x f (suc k) (writeLoc s (AtStack f k) (SV-Tag 0)) f′ j ne) (store-frame s f k _ f′ j ne))
  wt-frame (ST.b-+ {A = A₁} {B = B₁} a b) (inj₂ y) f k s f′ j ne =
    trans (zeros-frame ((tsize A₁ ⊔ tsize B₁) ∸ tsize B₁) f (suc (tsize B₁) + k) (writeTyped B₁ y (AtStack f (suc k)) (writeLoc s (AtStack f k) (SV-Tag 1))) f′ j ne)
          (trans (wt-frame b y f (suc k) (writeLoc s (AtStack f k) (SV-Tag 1)) f′ j ne) (store-frame s f k _ f′ j ne))

  private
    -- a sum's parts: the tag at `k`, the payload of `t` words after it, the padding to `M`
    sum-o1 : ∀ k M j → (j < k ⊎ k + suc M ≤ j) → (j < k ⊎ k + 1 ≤ j)
    sum-o1 k M j = Data.Sum.map (λ lt → lt) (NP.≤-trans (NP.+-monoʳ-≤ k (s≤s z≤n)))

    sum-oP : ∀ k t M j → t ≤ M → (j < k ⊎ k + suc M ≤ j) → (j < suc k ⊎ suc k + t ≤ j)
    sum-oP k t M j tM = Data.Sum.map NP.m<n⇒m<1+n
      (NP.≤-trans (subst (suc (k + t) ≤_) (sym (NP.+-suc k M)) (s≤s (NP.+-monoʳ-≤ k tM))))

    pad-eq : ∀ k t M → t ≤ M → (t + k) + (M ∸ t) ≡ k + M
    pad-eq k t M tM = trans (cong (_+ (M ∸ t)) (NP.+-comm t k))
                        (trans (NP.+-assoc k t (M ∸ t)) (cong (k +_) (NP.m+[n∸m]≡n tM)))

    sum-oZ : ∀ k t M j → t ≤ M → (j < k ⊎ k + suc M ≤ j) → (j < suc t + k ⊎ (suc t + k) + (M ∸ t) ≤ j)
    sum-oZ k t M j tM = Data.Sum.map (λ lt → NP.<-≤-trans lt (NP.m≤n+m k (suc t)))
      (subst (_≤ j) (trans (NP.+-suc k M) (cong suc (sym (pad-eq k t M tM)))))

  wt-out : ∀ {A} (b : ST.Base ST.∅ₖ A) v (f : Frame) k (s : LocState FS) j → (j < k ⊎ k + tsize A ≤ j)
         → stackMem (writeTyped A v (AtStack f k) s) f j ≡ stackMem s f j
  wt-out (ST.b-var {i = ()} _) v f k s j o
  wt-out ST.b-Unit    v f k s j o = refl
  wt-out ST.b-Void    () f k s j o
  wt-out ST.b-Int     v f k s j o = store-other s f k _ j (out1 k j o)
  wt-out ST.b-Float   v f k s j o = store-other s f k _ j (out1 k j o)
  wt-out (ST.b-* {A = A₁} {B = B₁} a b) (x , y) f k s j o =
    trans (wt-out b y f (tsize A₁ + k) (writeTyped A₁ x (AtStack f k) s) j oB) (wt-out a x f k s j oA)
    where
      oA : j < k ⊎ k + tsize A₁ ≤ j
      oA = Data.Sum.map (λ lt → lt) (NP.≤-trans (NP.+-monoʳ-≤ k (NP.m≤m+n (tsize A₁) (tsize B₁)))) o
      oB : j < tsize A₁ + k ⊎ (tsize A₁ + k) + tsize B₁ ≤ j
      oB = Data.Sum.map (λ lt → NP.<-≤-trans lt (NP.m≤n+m k (tsize A₁)))
             (subst (_≤ j) (trans (sym (NP.+-assoc k (tsize A₁) (tsize B₁))) (cong (_+ tsize B₁) (NP.+-comm k (tsize A₁))))) o
  wt-out (ST.b-+ {A = A₁} {B = B₁} a b) (inj₁ x) f k s j o =
    trans (zeros-out ((tsize A₁ ⊔ tsize B₁) ∸ tsize A₁) f (suc (tsize A₁) + k) (writeTyped A₁ x (AtStack f (suc k)) (writeLoc s (AtStack f k) (SV-Tag 0))) j (sum-oZ k (tsize A₁) M j tM o))
          (trans (wt-out a x f (suc k) (writeLoc s (AtStack f k) (SV-Tag 0)) j (sum-oP k (tsize A₁) M j tM o))
                 (store-other s f k _ j (out1 k j (sum-o1 k M j o))))
    where
      M = tsize A₁ ⊔ tsize B₁
      tM = NP.m≤m⊔n (tsize A₁) (tsize B₁)
  wt-out (ST.b-+ {A = A₁} {B = B₁} a b) (inj₂ y) f k s j o =
    trans (zeros-out ((tsize A₁ ⊔ tsize B₁) ∸ tsize B₁) f (suc (tsize B₁) + k) (writeTyped B₁ y (AtStack f (suc k)) (writeLoc s (AtStack f k) (SV-Tag 1))) j (sum-oZ k (tsize B₁) M j tM o))
          (trans (wt-out b y f (suc k) (writeLoc s (AtStack f k) (SV-Tag 1)) j (sum-oP k (tsize B₁) M j tM o))
                 (store-other s f k _ j (out1 k j (sum-o1 k M j o))))
    where
      M = tsize A₁ ⊔ tsize B₁
      tM = NP.m≤n⊔m (tsize A₁) (tsize B₁)


  -- ★ the sigop's store at a destination in a frame (`sigop-store-at`, an answer in memory)
  st-heap : ∀ {A} (b : ST.Base ST.∅ₖ A) (mb : Bool) → mb ≡ true → ∀ (ma : Maybe (Once.Semantics.Machine.Value.⟦ A ⟧)) (f : Frame) k (s : LocState FS)
          → heapMem (sigop-store-at {B = A} mb (just (AtStack f k)) ma s) ≡ heapMem s
  st-heap b .true refl (just v) f k s = wt-heap b v f k s
  st-heap b .true refl nothing  f k s = refl

  st-frame : ∀ {A} (b : ST.Base ST.∅ₖ A) (mb : Bool) → mb ≡ true → ∀ (ma : Maybe (Once.Semantics.Machine.Value.⟦ A ⟧)) (f : Frame) k (s : LocState FS) f′ j
           → ¬ f ≡ f′ → stackMem (sigop-store-at {B = A} mb (just (AtStack f k)) ma s) f′ j ≡ stackMem s f′ j
  st-frame b .true refl (just v) f k s f′ j ne = wt-frame b v f k s f′ j ne
  st-frame b .true refl nothing  f k s f′ j ne = refl

  st-out : ∀ {A} (b : ST.Base ST.∅ₖ A) (mb : Bool) → mb ≡ true → ∀ (ma : Maybe (Once.Semantics.Machine.Value.⟦ A ⟧)) (f : Frame) k (s : LocState FS) j
         → (j < k ⊎ k + tsize A ≤ j)
         → stackMem (sigop-store-at {B = A} mb (just (AtStack f k)) ma s) f j ≡ stackMem s f j
  st-out b .true refl (just v) f k s j o = wt-out b v f k s j o
  st-out b .true refl nothing  f k s j o = refl

module Wr {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS)
          (w-int   : ∀ (n : ⟦ int ⟧b)   → wordOf {int} n ≡ SV-Lit fits-int n)
          (w-float : ∀ (n : ⟦ float ⟧b) → wordOf {float} n ≡ SV-Lit fits-float n) where
  open Rel {FS} U wordOf using (W; VW; vone; vpair; vinl; vinr; vbase; SlotsAt; vw-len)
  open AbstractExec {FS} using (writeTyped; writeZeros; zero-word; tsize)
  open MemOps {FS} using (writeLoc)
  open LocState using (stackMem; heapMem)
  open FrameSemantics FS using (Frame)
  open import Once.LinCore.Moves {FS} using (store-same; store-other; store-frame)
  open Keep {FS}

  ----------------------------------------------------------------------
  -- 1. SLOTS: a run of words kept, and two runs after each other.
  ----------------------------------------------------------------------
  slots-pt : ∀ {sm sm′ : ℕ → Maybe W} o (ws : List W)
           → (∀ j → o ≤ j → j < length ws + o → sm′ j ≡ sm j) → SlotsAt sm o ws → SlotsAt sm′ o ws
  slots-pt o []       h _       = _
  slots-pt {sm} {sm′} o (w ∷ ws) h (e , s) =
    trans (h o NP.≤-refl (s≤s (NP.m≤n+m o (length ws)))) e , slots-pt (suc o) ws h′ s
    where
      h′ : ∀ j → suc o ≤ j → j < length ws + suc o → sm′ j ≡ sm j
      h′ j lo hi = h j (NP.≤-trans (NP.n≤1+n o) lo) (subst (j <_) (NP.+-suc (length ws) o) hi)

  slots-cat : ∀ {sm : ℕ → Maybe W} o (xs ys : List W)
            → SlotsAt sm o xs → SlotsAt sm (length xs + o) ys → SlotsAt sm o (xs ++ ys)
  slots-cat o []       ys _       sy = sy
  slots-cat {sm} o (x ∷ xs) ys (e , sx) sy =
    e , slots-cat (suc o) xs ys sx (subst (λ z → SlotsAt sm z ys) (sym (NP.+-suc (length xs) o)) sy)

  ----------------------------------------------------------------------
  -- 3. ★ THE WORDS: the answer's, the image's (`VW`), where it was written.
  ----------------------------------------------------------------------
  zeros-words : ∀ n (f : Frame) k (s : LocState FS)
              → SlotsAt (stackMem (writeZeros n (AtStack f k) s) f) k (replicate n zero-word)
  zeros-words zero    f k s = _
  zeros-words (suc n) f k s =
    trans (zeros-out n f (suc k) s₁ k (inj₁ (NP.n<1+n k))) (store-same s f k zero-word) , zeros-words n f (suc k) s₁
    where s₁ = writeLoc s (AtStack f k) zero-word

  wt-words : ∀ {A} (b : ST.Base ST.∅ₖ A) (v : Once.Semantics.Machine.Value.⟦ A ⟧) (f : Frame) k (s : LocState FS) {h}
           → Σ (List W) λ ws → VW h (mvF (flatB b) (fromV b v)) ws
               × SlotsAt (stackMem (writeTyped A v (AtStack f k) s) f) k ws
  wt-words (ST.b-var {i = ()} _) v f k s
  wt-words ST.b-Unit    v f k s = [] , vone , _
  wt-words ST.b-Void    () f k s
  wt-words ST.b-Int     v f k s = wordOf {int} v ∷ [] , vbase , (trans (store-same s f k _) (cong just (sym (w-int v))) , _)
  wt-words ST.b-Float   v f k s = wordOf {float} v ∷ [] , vbase , (trans (store-same s f k _) (cong just (sym (w-float v))) , _)
  wt-words (ST.b-* {A = A₁} {B = B₁} a b) (x , y) f k s {h} =
    wa ++ wb , vpair pa pb ,
    slots-cat k wa wb (slots-pt k wa keep sa) (subst (λ z → SlotsAt (stackMem s₂ f) (z + k) wb) (sym la) sb)
    where
      s₁ = writeTyped A₁ x (AtStack f k) s
      ra = wt-words a x f k s {h}
      wa = proj₁ ra ; pa = proj₁ (proj₂ ra) ; sa = proj₂ (proj₂ ra)
      rb = wt-words b y f (tsize A₁ + k) s₁ {h}
      wb = proj₁ rb ; pb = proj₁ (proj₂ rb) ; sb = proj₂ (proj₂ rb)
      s₂ = writeTyped B₁ y (AtStack f (tsize A₁ + k)) s₁
      la : length wa ≡ tsize A₁
      la = trans (vw-len pa) (sym (tsize-wsz {FS} a))
      keep : ∀ j → k ≤ j → j < length wa + k → stackMem s₂ f j ≡ stackMem s₁ f j
      keep j lo hi = wt-out b y f (tsize A₁ + k) s₁ j (inj₁ (subst (λ z → j < z + k) la hi))
  wt-words (ST.b-+ {A = A₁} {B = B₁} a b) (inj₁ x) f k s {h} =
    SV-Tag 0 ∷ wa ++ pad , vinl pa lenp ,
    ( trans (zeros-out (M ∸ tsize A₁) f (suc (tsize A₁) + k) s₂ k (inj₁ (s≤s (NP.m≤n+m k (tsize A₁)))))
        (trans (wt-out a x f (suc k) s₁ k (inj₁ (NP.n<1+n k))) (store-same s f k _))
    , slots-cat (suc k) wa pad (slots-pt (suc k) wa keepZ sa)
        (subst (λ z → SlotsAt (stackMem s₃ f) z pad) (sym e) (zeros-words (M ∸ tsize A₁) f (suc (tsize A₁) + k) s₂)) )
    where
      M = tsize A₁ ⊔ tsize B₁
      s₁ = writeLoc s (AtStack f k) (SV-Tag 0)
      ra = wt-words a x f (suc k) s₁ {h}
      wa = proj₁ ra ; pa = proj₁ (proj₂ ra) ; sa = proj₂ (proj₂ ra)
      s₂ = writeTyped A₁ x (AtStack f (suc k)) s₁
      s₃ = writeZeros (M ∸ tsize A₁) (AtStack f (suc (tsize A₁) + k)) s₂
      pad = replicate (M ∸ tsize A₁) zero-word
      la : length wa ≡ tsize A₁
      la = trans (vw-len pa) (sym (tsize-wsz {FS} a))
      lenp : length (wa ++ pad) ≡ wsz ⌜ flatB a ⌝ ⊔ wsz ⌜ flatB b ⌝
      lenp = trans (length-++ wa) (trans (cong₂ _+_ la (length-replicate (M ∸ tsize A₁)))
               (trans (NP.m+[n∸m]≡n (NP.m≤m⊔n (tsize A₁) (tsize B₁))) (cong₂ _⊔_ (tsize-wsz {FS} a) (tsize-wsz {FS} b))))
      e : length wa + suc k ≡ suc (tsize A₁) + k
      e = trans (cong (_+ suc k) la) (NP.+-suc (tsize A₁) k)
      keepZ : ∀ j → suc k ≤ j → j < length wa + suc k → stackMem s₃ f j ≡ stackMem s₂ f j
      keepZ j lo hi = zeros-out (M ∸ tsize A₁) f (suc (tsize A₁) + k) s₂ j (inj₁ (subst (j <_) e hi))
  wt-words (ST.b-+ {A = A₁} {B = B₁} a b) (inj₂ y) f k s {h} =
    SV-Tag 1 ∷ wb ++ pad , vinr pb lenp ,
    ( trans (zeros-out (M ∸ tsize B₁) f (suc (tsize B₁) + k) s₂ k (inj₁ (s≤s (NP.m≤n+m k (tsize B₁)))))
        (trans (wt-out b y f (suc k) s₁ k (inj₁ (NP.n<1+n k))) (store-same s f k _))
    , slots-cat (suc k) wb pad (slots-pt (suc k) wb keepZ sb)
        (subst (λ z → SlotsAt (stackMem s₃ f) z pad) (sym e) (zeros-words (M ∸ tsize B₁) f (suc (tsize B₁) + k) s₂)) )
    where
      M = tsize A₁ ⊔ tsize B₁
      s₁ = writeLoc s (AtStack f k) (SV-Tag 1)
      rb = wt-words b y f (suc k) s₁ {h}
      wb = proj₁ rb ; pb = proj₁ (proj₂ rb) ; sb = proj₂ (proj₂ rb)
      s₂ = writeTyped B₁ y (AtStack f (suc k)) s₁
      s₃ = writeZeros (M ∸ tsize B₁) (AtStack f (suc (tsize B₁) + k)) s₂
      pad = replicate (M ∸ tsize B₁) zero-word
      lb : length wb ≡ tsize B₁
      lb = trans (vw-len pb) (sym (tsize-wsz {FS} b))
      lenp : length (wb ++ pad) ≡ wsz ⌜ flatB a ⌝ ⊔ wsz ⌜ flatB b ⌝
      lenp = trans (length-++ wb) (trans (cong₂ _+_ lb (length-replicate (M ∸ tsize B₁)))
               (trans (NP.m+[n∸m]≡n (NP.m≤n⊔m (tsize A₁) (tsize B₁))) (cong₂ _⊔_ (tsize-wsz {FS} a) (tsize-wsz {FS} b))))
      e : length wb + suc k ≡ suc (tsize B₁) + k
      e = trans (cong (_+ suc k) lb) (NP.+-suc (tsize B₁) k)
      keepZ : ∀ j → suc k ≤ j → j < length wb + suc k → stackMem s₃ f j ≡ stackMem s₂ f j
      keepZ j lo hi = zeros-out (M ∸ tsize B₁) f (suc (tsize B₁) + k) s₂ j (inj₁ (subst (j <_) e hi))

  -- ★ the sigop's store, an answer `w` in memory: its words, where it wrote them
  st-words : ∀ {A} (b : ST.Base ST.∅ₖ A) (mb : Bool) → mb ≡ true
           → ∀ (ma : Maybe (Once.Semantics.Machine.Value.⟦ A ⟧)) w → ma ≡ just w → ∀ (f : Frame) k (s : LocState FS) {h}
           → Σ (List W) λ ws → VW h (mvF (flatB b) (fromV b w)) ws
               × SlotsAt (stackMem (AbstractExec.sigop-store-at {FS} {B = A} mb (just (AtStack f k)) ma s) f) k ws
  st-words b .true refl .(just w) w refl f k s = wt-words b w f k s
