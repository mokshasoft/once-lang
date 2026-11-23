-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Once.LinCore.LiveRun
--
-- ★ D469: EVERY HELD CELL'S BLOCK IS LIVE, at its id's size, step by step.
-- A heap-level statement (`HLive`): the abstract heap `h` (the cells held)
-- against the machine's allocator state. A step keeps it when its flat run
-- freed only blocks of the step's frees (`Keep`'s list), kept the sizes
-- below the counter, and left every cell it allocated live at its size:
-- then a cell held after was allocated by the step, or was held before and
-- its block is none the step freed (`held-after`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Data.Nat using (ℕ)

module Once.LinCore.LiveRun
  (fmt : TargetNum)
  (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Data.Nat using (_≤_; _<_; s≤s; z≤n; _+_)
open import Data.Nat.Properties using (≰⇒>; ≤-trans; ≤-reflexive; m≤m+n)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AllocState; module AllocState)
open import Once.LinCore.Core fmt
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Events fmt ans bw
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Data.List using (List; []; _∷_)
import Level
open import Once.LinCore.StepKinds fmt ans bw using (Local; LocalCases; local-elim)
open import Data.Sum using ([_,_]′)
open import Once.LinCore.Code fmt bw using (Cfg; _∣_; _∥_; _∷ˢ_; []ˢ; Slots; Stk)
open import Once.LinCore.Image fmt bw using (Codeᴵ; _⊳_)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; StepI; frm)
open import Once.LinCore.Held fmt ans bw using (Owned; own; held)
open import Once.LinCore.HeldI fmt ans bw using (InvI; InvH; module InvH; OwnR; i-h; inv-stepI)

-- ★ a call: the argument onto the callee's stack under a view that owns nothing, the caller's
-- frame saved; every cell held after is one held before
sub-call : ∀ {t U T Es A B S} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) U} {es : Slots (t ⊳ Es)} {os : Stk S} {r : Ret U T}
             {e′ : Slots (t ⊳ [])} {a : MV A}
         → (∀ i → own e′ i ≡ 0)
         → ∀ i → 1 ≤ Owned (e′ ∥ a ∷ˢ []ˢ) i + OwnR (frm {t = t} {Es = Es} k es os r) i → 1 ≤ Owned (es ∥ a ∷ˢ os) i + OwnR r i
sub-call {es = es} {os} {r} {e′} {a} z i p =
  ≤-trans p (≤-reflexive (trans (cong (λ v → (v + (cnt a i + 0)) + ((own es i + held os i) + OwnR r i)) (z i))
                                (shuffle (own es i) (cnt a i) (held os i) (OwnR r i))))
  where
    shuffle : ∀ e c o R → (0 + (c + 0)) + ((e + o) + R) ≡ (e + (c + o)) + R
    shuffle = solve-∀

module _ {FS : FrameSemantics} where
  open AllocState {FS} using (block-size; freed; next-heap-ref)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (falloc)
  open import Once.LinCore.Moves {FS} using (Keep; module Keep)

  -- a cell's block, live at its id's size
  LiveId : AllocState {FS} → Id → Set
  LiveId al i = block-size al (serial i) ≡ proj₁ i × freed al (serial i) ≡ false

  -- every held cell's
  HLive : Heap → AllocState {FS} → Set
  HLive h al = ∀ i → 1 ≤ h i → LiveId al i

  private
    t≢f : true ≡ false → ⊥
    t≢f ()

  -- ★ a step keeps it
  live-step : ∀ {t h} {al al′ : AllocState {FS}}
            → OK t h → SerU h → (∀ i → next-heap-ref al ≤ serial i → h i ≡ 0)
            → HLive h al
            → (∀ r → freed al′ r ≡ true → freed al r ≡ true ⊎ r ∈ freesOf t)
            → (∀ r → r < next-heap-ref al → block-size al′ r ≡ block-size al r)
            → (∀ i → alloc i ∈ t → 1 ≤ play t h i → LiveId al′ i)
            → HLive (play t h) al′
  live-step {t} {h} {al} {al′} ok u above L unfr size new i p = by (held-after t h i ok u p)
    where
      by : (alloc i ∈ t) ⊎ (1 ≤ h i × ¬ (serial i ∈ freesOf t)) → LiveId al′ i
      by (inj₁ m)         = new i m p
      by (inj₂ (hi , nf)) = trans (size (serial i) under) (proj₁ (L i hi)) , unfreed (freed al′ (serial i)) refl
        where
          under : serial i < next-heap-ref al
          under = ≰⇒> (λ le → no1 (subst (1 ≤_) (above i le) hi))
            where no1 : 1 ≤ 0 → ⊥
                  no1 ()
          unfreed : ∀ b → freed al′ (serial i) ≡ b → freed al′ (serial i) ≡ false
          unfreed false e = e
          unfreed true  e = by′ (unfr (serial i) e)
            where
              by′ : freed al (serial i) ≡ true ⊎ serial i ∈ freesOf t → freed al′ (serial i) ≡ false
              by′ (inj₁ e′) = ⊥-elim (t≢f (trans (sym e′) (proj₂ (L i hi))))
              by′ (inj₂ m)  = ⊥-elim (nf m)

  -- ★ nothing at or past the counter is freed (a fresh block is live)
  FreshAl : AllocState {FS} → Set
  FreshAl al = ∀ s → next-heap-ref al ≤ s → freed al s ≡ false

  fresh-step : ∀ {fl} {al al′ : AllocState {FS}} → FreshAl al
             → (∀ r → freed al′ r ≡ true → freed al r ≡ true ⊎ r ∈ fl)
             → (∀ {s} → s ∈ fl → s < next-heap-ref al) → next-heap-ref al ≤ next-heap-ref al′
             → FreshAl al′
  fresh-step {fl} {al} {al′} F unfr below grow s le = by (freed al′ s) refl
    where
      old : next-heap-ref al ≤ s
      old = Data.Nat.Properties.≤-trans grow le
        where import Data.Nat.Properties
      by : ∀ b → freed al′ s ≡ b → freed al′ s ≡ false
      by false e = e
      by true  e = case′ (unfr s e)
        where
          case′ : freed al s ≡ true ⊎ s ∈ fl → freed al′ s ≡ false
          case′ (inj₁ e′) = ⊥-elim (t≢f (trans (sym e′) (F s old)))
          case′ (inj₂ m)  = ⊥-elim (Data.Nat.Properties.<⇒≱ (below m) old)
            where import Data.Nat.Properties

  -- ★ what a step's flat run says of the allocator, against the step's trace
  record StepFx (t : Trace) (fs fs′ : FlatState) : Set where
    constructor kt
    field
      kfl   : List ℕ                       -- the blocks the run freed
      keepT : Keep kfl fs fs′
      kfl⊆  : ∀ {q} → q ∈ kfl → q ∈ freesOf t
      kfl<  : ∀ {q} → q ∈ kfl → q < next-heap-ref (falloc fs)
      -- a step frees nothing, or allocates nothing
      kshape : freesOf t ≡ [] ⊎ (∀ i → ¬ (alloc i ∈ t))
      -- every cell the step allocated: its block live at its id's size
      bornT : ∀ i → alloc i ∈ t → LiveId (falloc fs′) i
  open StepFx public

  -- the held cells of a configuration and its saved frames, live
  LiveG : ∀ {sh U T} → Ret U T → Cfg sh → FlatState → Set
  LiveG r m fs = ∀ i → 1 ≤ Owned m i + OwnR r i → LiveId (falloc fs) i

  -- ★ what liveness needs of a step's run: the allocator part (a call's or a
  -- return's run moves frames, so no `Keep`; its blocks are untouched)
  record AlFx (t : Trace) (fs fs′ : FlatState) : Set where
    constructor ax
    field
      afl    : List ℕ
      aunfr  : ∀ r → freed (falloc fs′) r ≡ true → freed (falloc fs) r ≡ true ⊎ r ∈ afl
      asize  : ∀ r → r < next-heap-ref (falloc fs) → block-size (falloc fs′) r ≡ block-size (falloc fs) r
      anext  : next-heap-ref (falloc fs) ≤ next-heap-ref (falloc fs′)
      afl⊆   : ∀ {q} → q ∈ afl → q ∈ freesOf t
      afl<   : ∀ {q} → q ∈ afl → q < next-heap-ref (falloc fs)
      aborn  : ∀ i → alloc i ∈ t → LiveId (falloc fs′) i

  al-of : ∀ {t fs fs′} → StepFx t fs fs′ → AlFx t fs fs′
  al-of (kt fl K sub bl _ bn) = ax fl (Keep.k-unfr K) (Keep.k-size K) (Keep.k-next K) sub bl bn

  -- a run with no allocator event: no event in the trace
  al-quiet : ∀ {t fs fs′} → (∀ r → freed (falloc fs′) r ≡ freed (falloc fs) r)
           → (∀ r → r < next-heap-ref (falloc fs) → block-size (falloc fs′) r ≡ block-size (falloc fs) r)
           → next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs) → (∀ i → ¬ (alloc i ∈ t)) → AlFx t fs fs′
  al-quiet fe se ne na = ax [] (λ r e → inj₁ (trans (sym (fe r)) e)) se (≤-reflexive (sym ne)) (λ ()) (λ ()) (λ i m → ⊥-elim (na i m))
    where open import Data.Nat.Properties using (≤-reflexive)

  -- ★ a step keeps it
  live-after : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′ h fs fs′}
             → StepI c r m n t c′ r′ m′ n′ → InvI m r n h → next-heap-ref (falloc fs) ≡ n
             → LiveG r m fs → AlFx t fs fs′ → LiveG r′ m′ fs′
  live-after {t = t} {r′ = r′} {m′ = m′} {h = h} {fs} {fs′} st inv nx L (ax fl unfr size _ sub _ bn) i p =
    live-step {t = t} {h = h} {falloc fs} {falloc fs′} ok (InvH.i-ser (i-h inv)) (λ j le → InvH.i-above (i-h inv) j (subst (_≤ serial j) nx le))
      (λ j q → L j (subst (1 ≤_) (InvH.i-exact (i-h inv) j) q))
      (λ q e → [ inj₁ , (λ m → inj₂ (sub m)) ]′ (unfr q e)) size (λ j m _ → bn j m)
      i (subst (1 ≤_) (sym (InvH.i-exact (i-h inv′) i)) p)
    where
      ok = proj₁ (inv-stepI st inv)
      inv′ = proj₂ (inv-stepI st inv)

  fresh-after : ∀ {t fs fs′} → FreshAl (falloc fs) → AlFx t fs fs′ → FreshAl (falloc fs′)
  fresh-after {fs = fs} {fs′} F (ax fl unfr _ nx _ bl _) = fresh-step {fl = fl} {falloc fs} {falloc fs′} F unfr bl nx

  -- ★ a step whose held cells are among those before, its run touching no block (a return)
  live-eq : ∀ {sh sh′ U U′ T} {r : Ret U T} {r′ : Ret U′ T} {m : Cfg sh} {m′ : Cfg sh′} {fs fs′}
          → (∀ i → 1 ≤ Owned m′ i + OwnR r′ i → 1 ≤ Owned m i + OwnR r i)
          → (∀ q → freed (falloc fs′) q ≡ freed (falloc fs) q) → (∀ q → block-size (falloc fs′) q ≡ block-size (falloc fs) q)
          → LiveG r m fs → LiveG r′ m′ fs′
  live-eq sub fe se L i p = trans (se (serial i)) (proj₁ (L i (sub i p))) , trans (fe (serial i)) (proj₂ (L i (sub i p)))

  fresh-eq : ∀ {fs fs′} → (∀ q → freed (falloc fs′) q ≡ freed (falloc fs) q) → next-heap-ref (falloc fs′) ≡ next-heap-ref (falloc fs)
           → FreshAl (falloc fs) → FreshAl (falloc fs′)
  fresh-eq fe ne F q le = trans (fe q) (F q (subst (_≤ q) ne le))

  -- ★ a return: the callee's top view dropped, the caller's frame back in the configuration;
  -- every cell held after is one held before
  live-ret : ∀ {t U T Es B S} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) U} {es : Slots (t ⊳ Es)} {os : Stk S} {r : Ret U T}
               {e′ : Slots (t ⊳ [])} {b : MV B} {fs}
           → LiveG (frm {t = t} {Es = Es} k es os r) (e′ ∥ b ∷ˢ []ˢ) fs → LiveG r (es ∥ b ∷ˢ os) fs
  live-ret {es = es} {os} {r} {e′} {b} L i p =
    L i (≤-trans p (≤-trans (m≤m+n _ (own e′ i)) (≤-reflexive (shuffle (own es i) (cnt b i) (held os i) (OwnR r i) (own e′ i)))))
    where
      shuffle : ∀ a c o R e → ((a + (c + o)) + R) + e ≡ (e + (c + 0)) + ((a + o) + R)
      shuffle = solve-∀

  -- ★ a cell held after a step that frees nothing, or allocates nothing, is no block it freed
  away-local : ∀ {t h j} → OK t h → SerU h → freesOf t ≡ [] ⊎ (∀ i → ¬ (alloc i ∈ t)) → 1 ≤ play t h j
             → ¬ (serial j ∈ freesOf t)
  away-local {t} {h} {j} ok u sh p = by (held-after t h j ok u p) sh
    where
      by : (alloc j ∈ t) ⊎ (1 ≤ h j × ¬ (serial j ∈ freesOf t)) → freesOf t ≡ [] ⊎ (∀ i → ¬ (alloc i ∈ t)) → ¬ (serial j ∈ freesOf t)
      by (inj₂ (_ , nf)) _ = nf
      by (inj₁ m) (inj₂ na) = ⊥-elim (na j m)
      by (inj₁ m) (inj₁ e) = λ q → empty∈ (subst (serial j ∈_) e q)
        where empty∈ : serial j ∈ [] → ⊥
              empty∈ ()

  -- ★ a local step keeps the saved frames' cells
  own-cases : ∀ {T} → LocalCases {Level.zero} {T}
  own-cases = record
    { P        = λ {r = r} {r′ = r′} _ → ∀ j → OwnR r′ j ≡ OwnR r j
    ; unpair′  = λ _ → refl ; pair′ = λ _ → refl ; swap′ = λ _ → refl ; unit′ = λ _ → refl
    ; prim′    = λ _ _ _ → refl
    ; untag′   = λ _ → refl ; untag₁′ = λ _ → refl ; tag₁′ = λ _ → refl
    ; case₁′   = λ _ → refl ; case₂′ = λ _ → refl
    ; elend′   = λ _ → refl ; eunlend′ = λ _ → refl ; elift′ = λ _ → refl
    ; efst′    = λ _ _ → refl ; esnd′ = λ _ _ → refl ; eout′ = λ _ _ → refl ; eoutq′ = λ _ _ → refl
    ; ecase₁′  = λ _ _ → refl ; ecase₂′ = λ _ _ → refl ; eapp′ = λ _ _ → refl
    ; epop′    = λ _ → refl ; eword′ = λ _ _ → refl ; oncify′ = λ _ → refl
    }

  local-ownR : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
             → (st : StepI c r m n t c′ r′ m′ n′) → Local st → ∀ j → OwnR r′ j ≡ OwnR r j
  local-ownR st l = local-elim own-cases st l

  -- nothing held: nothing to say
  live-start : ∀ (al : AllocState {FS}) → HLive (λ _ → 0) al
  live-start al i ()
