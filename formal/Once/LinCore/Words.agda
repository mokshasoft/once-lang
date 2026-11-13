-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Words — plan 0.146 B1.4b, `LowerSim` layer (2): a value's
-- words on the flat machine (D416).
--
-- `VW rd v ws`: the image's value `v` is the words `ws`, and every cell it
-- holds is in the heap `rd` reads: a cell `i` is the block whose reference
-- is `i`'s serial (the flat allocator's counter is the run's), a μ node
-- holding its layer's words, a closure or a ν
-- `[contents-word, code, copy, free, contents…]`, each code word a
-- trampoline of a key of the universe (`CodeOf`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (length-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)
open import Once.CCC.Machine.SMCore using (StoredValue; SV-Ptr; SV-Tag; SV-Code)

module Once.LinCore.Words
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw using (tl; idx; hdr)

module Rel {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where

  W : Set
  W = StoredValue FS

  -- a cell's block, at an offset
  cellLoc : Id → ℕ → HeapLocation
  cellLoc i k = heap-loc (mkHeapRef (serial i)) k

  cellPtr : Id → W
  cellPtr i = SV-Ptr (AtDynamic (cellLoc i 0))

  -- words at consecutive offsets of a cell's block
  At : (HeapLocation → Maybe W) → Id → ℕ → List W → Set
  At rd i o []       = ⊤
  At rd i o (w ∷ ws) = rd (cellLoc i o) ≡ just w × At rd i (suc o) ws

  -- a code word: the trampoline of a key of the universe
  CodeOf : Σ BSig Key → W → Set
  CodeOf κ w = Σ (κ ∈ allK U) λ m → w ≡ SV-Code (tl (idx m))

  -- ★ a value's words, its cells in the heap
  data VW (rd : HeapLocation → Maybe W) : ∀ {A} → MV A → List W → Set where
    vone  : VW rd mone []
    vpair : ∀ {A B} {a : MV A} {b : MV B} {wa wb} → VW rd a wa → VW rd b wb → VW rd (mpair a b) (wa ++ wb)
    vinl  : ∀ {A B} {a : MV A} {wa pad} → VW rd a wa → length (wa ++ pad) ≡ wsz A ⊔ wsz B
          → VW rd (minl {B = B} a) (SV-Tag 0 ∷ wa ++ pad)
    vinr  : ∀ {A B} {b : MV B} {wb pad} → VW rd b wb → length (wb ++ pad) ≡ wsz A ⊔ wsz B
          → VW rd (minr {A = A} b) (SV-Tag 1 ∷ wb ++ pad)
    vbase : ∀ {b} {x : ⟦ b ⟧b} → VW rd (mbase x) (wordOf x ∷ [])
    vmu   : ∀ {F i} {v : MV (LF∙ F (μt F))} {wv} → VW rd v wv → At rd i 0 wv → VW rd (mmu i v) (cellPtr i ∷ [])
    vct   : ∀ {l X} {x : MV X} {w} → VW rd x w → VW rd (mct {l = l} x) w
    vfn   : ∀ {k g X A B i} {lam : Lam k g X A B} {x : MV X} {wx wb wc wf}
          → CodeOf (key-of lam) wb → CodeOf (kc X) wc → CodeOf (kf X) wf → VW rd x wx
          → At rd i 0 (cellPtr i ∷ wb ∷ wc ∷ wf ∷ wx)
          → VW rd (mfn i lam x) (cellPtr i ∷ [])
    vnu   : ∀ {F S i} {p : MV (Coalg F S ⊗t S)} {wp wo wc wf}
          → CodeOf (_ , kobs ε F S) wo → CodeOf (kc (cty (F , S))) wc → CodeOf (kf (cty (F , S))) wf
          → VW rd p wp
          → At rd i 0 (cellPtr i ∷ wo ∷ wc ∷ wf ∷ wp)
          → VW rd (mnu i p) (cellPtr i ∷ [])

  -- a value's words are its type's
  vw-len : ∀ {rd A} {v : MV A} {ws} → VW rd v ws → length ws ≡ wsz A
  vw-len vone            = refl
  vw-len (vpair {wa = wa} {wb} p q) = trans (length-++ wa) (cong₂ _+_ (vw-len p) (vw-len q))
  vw-len (vinl p e)      = cong suc e
  vw-len (vinr p e)      = cong suc e
  vw-len vbase           = refl
  vw-len (vmu p c)       = refl
  vw-len (vct p)         = vw-len p
  vw-len (vfn _ _ _ p c) = refl
  vw-len (vnu _ _ _ p c) = refl

  ----------------------------------------------------------------------
  -- ★ A VALUE'S WORDS STAND while its cells' blocks do: the heap may change
  -- anywhere else (a move, a fresh cell, another value's cell).
  ----------------------------------------------------------------------

  At-frame : ∀ {rd rd′ : HeapLocation → Maybe W} {j o ws}
           → (∀ k → rd′ (cellLoc j k) ≡ rd (cellLoc j k)) → At rd j o ws → At rd′ j o ws
  At-frame {ws = []}     e tt      = tt
  At-frame {o = o} {ws = w ∷ ws} e (r , a) = trans (e o) r , At-frame e a

  private
    lft : ∀ {a b} → 1 Data.Nat.≤ a → 1 Data.Nat.≤ a + b
    lft {a} {b} p = Data.Nat.Properties.≤-trans p (Data.Nat.Properties.m≤m+n a b)
      where import Data.Nat.Properties
    rgt : ∀ {a b} → 1 Data.Nat.≤ b → 1 Data.Nat.≤ a + b
    rgt {a} {b} p = Data.Nat.Properties.≤-trans p (Data.Nat.Properties.m≤n+m b a)
      where import Data.Nat.Properties
    self : ∀ j n → 1 Data.Nat.≤ δ j j + n
    self j n = Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive (sym (δ-same j))) (Data.Nat.Properties.m≤m+n (δ j j) n)
      where import Data.Nat.Properties

  vw-frame : ∀ {rd rd′ : HeapLocation → Maybe W} {A} {v : MV A} {ws} → VW rd v ws
           → (∀ i k → 1 Data.Nat.≤ cnt v i → rd′ (cellLoc i k) ≡ rd (cellLoc i k)) → VW rd′ v ws
  vw-frame vone h = vone
  vw-frame (vpair p q) h = vpair (vw-frame p (λ i k c → h i k (lft c))) (vw-frame q (λ i k c → h i k (rgt c)))
  vw-frame (vinl p e) h = vinl (vw-frame p h) e
  vw-frame (vinr p e) h = vinr (vw-frame p h) e
  vw-frame vbase h = vbase
  vw-frame (vmu {i = j} {v = v} p c) h =
    vmu (vw-frame p (λ i k c′ → h i k (rgt {a = δ j i} c′))) (At-frame (λ k → h j k (self j (cnt v j))) c)
  vw-frame (vct p) h = vct (vw-frame p h)
  vw-frame (vfn {i = j} {x = x} cb cc cf p c) h =
    vfn cb cc cf (vw-frame p (λ i k c′ → h i k (rgt {a = δ j i} c′))) (At-frame (λ k → h j k (self j (cnt x j))) c)
  vw-frame (vnu {i = j} {p = q} co cc cf p c) h =
    vnu co cc cf (vw-frame p (λ i k c′ → h i k (rgt {a = δ j i} c′))) (At-frame (λ k → h j k (self j (cnt q j))) c)

  ----------------------------------------------------------------------
  -- LAYER (3): A CONFIGURATION IN A FRAME. `sm` the frame's slots.
  ----------------------------------------------------------------------

  open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)
  open import Data.Nat using (_≤_; _∸_)

  -- words at consecutive slots
  SlotsAt : (ℕ → Maybe W) → ℕ → List W → Set
  SlotsAt sm o []       = ⊤
  SlotsAt sm o (w ∷ ws) = sm o ≡ just w × SlotsAt sm (suc o) ws

  -- the environment's buffers: each slot holds the words of what it sees,
  -- at the words of the slots below it
  EnvW : (HeapLocation → Maybe W) → (ℕ → Maybe W) → ∀ {Es} → Slots Es → Set
  EnvW rd sm []ᵉ = ⊤
  EnvW rd sm (vw {Es = Es} e es) = Σ (List W) (λ w → VW rd e w × SlotsAt sm (ws Es) w) × EnvW rd sm es
  EnvW rd sm (ln {E = E} {Es = Es} e x es) =
    Σ (List W) (λ w → VW rd (mpair e x) w × SlotsAt sm (ws (E ∷ Es)) w) × EnvW rd sm es

  -- the operand stack, downward from the region's top: each value's words
  -- at the region's top less the words of it and those below it
  StkW : (HeapLocation → Maybe W) → (ℕ → Maybe W) → Frame → ∀ {S} → Stk S → Set
  StkW rd sm φ []ˢ = ⊤
  StkW rd sm φ (_∷ˢ_ {A} {S} v os) = Σ (List W) (λ w → VW rd v w × SlotsAt sm (budget φ ∸ ws (A ∷ S)) w) × StkW rd sm φ os

  -- ★ a configuration in its frame: both regions hold their words, and fit
  record CfgW (rd : HeapLocation → Maybe W) (sm : ℕ → Maybe W) (φ : Frame) {sh : Sh} (m : Cfg sh) : Set where
    field
      c-env  : EnvW rd sm (Cfg.envs m)
      c-stk  : StkW rd sm φ (Cfg.opds m)
      c-efit : envW sh ≤ EP φ
      c-sfit : opW sh ≤ OP φ
