-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandEvents — the expanded run shows what the primitive
-- one shows (D470, 3c3b).
--
-- From related states, at every fuel `n` of the primitive program there is a
-- fuel `m` of its expansion at which the two `flat-events` are EQUAL and the
-- expansion counts at least the primitive's control steps (what `FlatShows`
-- reads: `k ≤ flat-ctrls`). By fuel: a halted state ends both runs alike (the
-- flags and `left` related), a pc off the program is off the expansion
-- (`fetch-none`), and a step is the expansion's steps (`dispatch`), whose events
-- are the step's own: both logs grow by them from related logs (`chain-log`,
-- `step-log`), so the chain's are the step's.
--
-- `Good` is what the primitive run keeps (the apex's reached states): the
-- fetched instruction emittable, the step not faulting, the store well formed.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandEvents {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Properties
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {FS} using (flat-events; flat-events-step; flat-events-fetch; event-of; flat-events-steps; chain-events
                               ; step-log; chain-log; flat-ctrls; flat-ctrls-step; flat-ctrls-fetch; ctrl-of; chain-ctrls; flat-ctrls-steps)
open import Once.IR.Semantics.Out using (Out; _▹_; ended; end-of-left)
open import Once.CCC.Machine.FrameFree using (EmittableI; ImageI)
import Data.Empty
open import Once.CCC.Label using (LabelId; module LabelId)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRel {FS} using (Rel; module Rel)
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; fetch-none)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L)
import Once.CCC.Codegen.AllocExpandDispatch
import Once.CCC.Machine.FlatStoreWF

------------------------------------------------------------------------
-- A fuelled run's first step, unfolded
------------------------------------------------------------------------

ev-unfold : ∀ n prog (fs : FlatState) {i} → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just i
          → flat-events (suc n) prog fs ≡ event-of i fs ▹ flat-events n prog (flat-exec-instr i prog fs)
ev-unfold n prog fs h f = trans (cong (λ b → flat-events-step b n prog fs) h) (cong (λ mi → flat-events-fetch mi n prog fs) f)

ct-unfold : ∀ n prog (fs : FlatState) {i} → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just i
          → flat-ctrls (suc n) prog fs ≡ ctrl-of i + flat-ctrls n prog (flat-exec-instr i prog fs)
ct-unfold n prog fs h f = trans (cong (λ b → flat-ctrls-step b n prog fs) h) (cong (λ mi → flat-ctrls-fetch mi n prog fs) f)

ev-none : ∀ n prog (fs : FlatState) → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ nothing
        → flat-events (suc n) prog fs ≡ flat-events-fetch nothing n prog fs
ev-none n prog fs h f = trans (cong (λ b → flat-events-step b n prog fs) h) (cong (λ mi → flat-events-fetch mi n prog fs) f)

ct-none : ∀ n prog (fs : FlatState) → LocState.halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ nothing
        → flat-ctrls (suc n) prog fs ≡ 0
ct-none n prog fs h f = trans (cong (λ b → flat-ctrls-step b n prog fs) h) (cong (λ mi → flat-ctrls-fetch mi n prog fs) f)

ev-halt : ∀ n prog (fs : FlatState) → LocState.halted (floc fs) ≡ true
        → flat-events (suc n) prog fs ≡ flat-events-step true n prog fs
ev-halt n prog fs h = cong (λ b → flat-events-step b n prog fs) h

ct-halt : ∀ n prog (fs : FlatState) → LocState.halted (floc fs) ≡ true → flat-ctrls (suc n) prog fs ≡ 0
ct-halt n prog fs h = cong (λ b → flat-ctrls-step b n prog fs) h

------------------------------------------------------------------------
-- ★ The two runs show the same
------------------------------------------------------------------------

module _ (C : Classes) (P : AbstractTrace) (Sz : ℕ → Set)
         (uniform  : ∀ k k′ → Sz k → Sz k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′)
         (fits     : ∀ k → k ≤ bsz C k)
         (in-range : ∀ k → cls C k < count C)
         (sz-alloc : ∀ n k → fetch P n ≡ just (instr-alloc-heap k) → Sz k)
         (sz-free  : ∀ n k → fetch P n ≡ just (instr-free-heap k) → Sz k)
         (img      : ∀ n m → fetch P n ≡ just (instr-ctrl (c-label m)) → ImgL m)
         (jmp-lbl  : ∀ n m → fetch P n ≡ just (instr-ctrl (c-jmp m)) → ImgL m)
         (br-lbl   : ∀ n m → fetch P n ≡ just (instr-ctrl (c-branch-tag-zero m)) → ImgL m)
         where
  open Rel
  module D = Once.CCC.Codegen.AllocExpandDispatch {FS}
  module WF = Once.CCC.Machine.FlatStoreWF FS
  E = expand C P

  -- what the primitive run keeps
  record Keeps (Good : FlatState → Set) : Set where
    field
      g-step : ∀ {fs i} → Good fs → LocState.halted (floc fs) ≡ false → fetch P (fpc fs) ≡ just i → Good (flat-exec-instr i P fs)
      g-em   : ∀ {fs i} → Good fs → fetch P (fpc fs) ≡ just i → ImageI i
      g-ns   : ∀ {fs i} → Good fs → fetch P (fpc fs) ≡ just i → ∀ b → i ≡ instr-ctrl (c-start b) → Data.Empty.⊥
      g-nr   : ∀ {fs i} → Good fs → fetch P (fpc fs) ≡ just i → D.NoRecI C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl i
      g-nf   : ∀ {fs i} → Good fs → LocState.halted (floc fs) ≡ false → fetch P (fpc fs) ≡ just i
             → LocState.faulted (floc (flat-exec-instr i P fs)) ≡ false
      g-wf   : ∀ {fs} → Good fs → WF.StoreWF (AllocState.next-heap-ref (falloc fs)) (floc fs)
      g-cw   : ∀ {fs} → Good fs → WF.sv-below (AllocState.next-heap-ref (falloc fs)) (fclosure fs)

  Same : ℕ → FlatState → ℕ → FlatState → Set
  Same m gs n fs = (flat-events m E gs ≡ flat-events n P fs) × (flat-ctrls n P fs ≤ flat-ctrls m E gs)

  module Run {Good : FlatState → Set} (K : Keeps Good) where
    open Keeps K

    -- the chain's events are the step's: both logs grow by them from related logs
    events-of : ∀ {fs gs gs′ i N} (R : Rel C P Sz fs gs) (c : FlatSteps E N gs gs′) → Rel C P Sz (flat-exec-instr i P fs) gs′
              → chain-events c ≡ event-of i fs
    events-of {fs} {gs} {gs′} {i} R c R′ =
      Data.List.Properties.++-cancelˡ (LocState.ev-log (floc gs)) (chain-events c) (event-of i fs)
        (trans (sym (chain-log c))
          (trans (L.LRel.l-log (r-loc R′))
            (trans (step-log i P fs) (cong (_++ event-of i fs) (sym (L.LRel.l-log (r-loc R)))))))

    ev : ∀ n {fs gs} → Good fs → Rel C P Sz fs gs → Σ ℕ λ m → Same m gs n fs
    ev zero    G R = 0 , refl , z≤n
    ev (suc n) {fs} {gs} G R = by-h (LocState.halted (floc fs)) refl
      where
        hg : ∀ {b} → LocState.halted (floc fs) ≡ b → LocState.halted (floc gs) ≡ b
        hg e = trans (L.LRel.l-halt (r-loc R)) e

        by-f : ∀ mi → fetch P (fpc fs) ≡ mi → LocState.halted (floc fs) ≡ false → Σ ℕ λ m → Same m gs (suc n) fs
        by-f nothing ef h =
          1 , trans (ev-none 0 E gs (hg h) (trans (cong (fetch E) (r-pc R)) (fetch-none C 0 P (fpc fs) ef))) (sym (ev-none n P fs h ef))
            , subst (_≤ flat-ctrls 1 E gs) (sym (ct-none n P fs h ef)) z≤n
        by-f (just i) ef h = go (D.dispatch C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl R i ef (g-em G ef) (g-ns G ef) (g-nr G ef) h (g-nf G h ef) (g-wf G) (g-cw G))
          where
            go : D.Step C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl i fs gs → Σ ℕ λ m → Same m gs (suc n) fs
            go (N , gs′ , c , cb , R′) = go′ (ev n (g-step G h ef) R′)
              where
                go′ : Σ ℕ (λ m → Same m gs′ n (flat-exec-instr i P fs)) → Σ ℕ λ m → Same m gs (suc n) fs
                go′ (m′ , ee , ec) =
                  suc N + m′
                  , trans (flat-events-steps c m′) (trans (cong₂ _▹_ (events-of {i = i} R c R′) ee) (sym (ev-unfold n P fs h ef)))
                  , subst (_≤ flat-ctrls (suc N + m′) E gs) (sym (ct-unfold n P fs h ef))
                      (subst (ctrl-of i + flat-ctrls n P (flat-exec-instr i P fs) ≤_) (sym (flat-ctrls-steps c m′))
                        (Data.Nat.Properties.+-mono-≤ cb ec))

        by-h : ∀ b → LocState.halted (floc fs) ≡ b → Σ ℕ λ m → Same m gs (suc n) fs
        by-h true  e =
          1 , trans (ev-halt 0 E gs (hg e)) (trans (cong (λ l → ended (end-of-left l)) (L.LRel.l-left (r-loc R))) (sym (ev-halt n P fs e)))
            , subst (_≤ flat-ctrls 1 E gs) (sym (ct-halt n P fs e)) z≤n
        by-h false e = by-f (fetch P (fpc fs)) refl e

------------------------------------------------------------------------
-- Two chains from one state: the longer passes where the shorter ends (with
-- its length), or the shorter ends before the longer one's end
------------------------------------------------------------------------

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open FlatStepsAPI {FS} using ([]; _∷_; Sound)
import Once.CCC.Machine.FlatLeft

meet : ∀ {prog n m a b c} → FlatSteps prog n a b → FlatSteps prog m a c
     → (Σ ℕ λ j → FlatSteps prog j b c × m ≡ n + j) ⊎ (Σ ℕ λ j → FlatSteps prog (suc j) c b)
meet []      q  = inj₁ (_ , q , refl)
meet (s ∷ p) [] = inj₂ (_ , s ∷ p)
meet {prog} (_∷_ {i = i} (_ , f) p) (_∷_ {i = i′} (_ , f′) q) = tail (just-injective (trans (sym f) f′)) p q
  where
    up : ∀ {n m b c} → (Σ ℕ λ j → FlatSteps prog j b c × m ≡ n + j) ⊎ (Σ ℕ λ j → FlatSteps prog (suc j) c b)
       → (Σ ℕ λ j → FlatSteps prog j b c × suc m ≡ suc n + j) ⊎ (Σ ℕ λ j → FlatSteps prog (suc j) c b)
    up (inj₁ (j , r , e)) = inj₁ (j , r , cong suc e)
    up (inj₂ x)           = inj₂ x
    tail : ∀ {a b c n m} → i ≡ i′ → FlatSteps prog n (flat-exec-instr i prog a) b → FlatSteps prog m (flat-exec-instr i′ prog a) c
         → (Σ ℕ λ j → FlatSteps prog j b c × suc m ≡ suc n + j) ⊎ (Σ ℕ λ j → FlatSteps prog (suc j) c b)
    tail refl p q = up (meet p q)

-- a chain to a running state keeps the fault flag
chain-fault : ∀ {prog k a b} → FlatSteps prog k a b → LocState.halted (floc b) ≡ false → LocState.faulted (floc b) ≡ LocState.faulted (floc a)
chain-fault [] _ = refl
chain-fault {prog} (_∷_ {fs = a} {i = i} _ rest) hb = trans (chain-fault rest hb) (Once.CCC.Machine.FlatLeft.FaultPres.flat-exec-instr-fault {FS} i prog a (head-run rest hb))
  where
    head-run : ∀ {k x b} → FlatSteps prog k x b → LocState.halted (floc b) ≡ false → LocState.halted (floc x) ≡ false
    head-run []            hb′ = hb′
    head-run ((h , _) ∷ _) _   = h

------------------------------------------------------------------------
-- ★ The expanded run never faults
------------------------------------------------------------------------

module _ (C : Classes) (P : AbstractTrace) (Sz : ℕ → Set)
         (uniform  : ∀ k k′ → Sz k → Sz k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′)
         (fits     : ∀ k → k ≤ bsz C k)
         (in-range : ∀ k → cls C k < count C)
         (sz-alloc : ∀ n k → fetch P n ≡ just (instr-alloc-heap k) → Sz k)
         (sz-free  : ∀ n k → fetch P n ≡ just (instr-free-heap k) → Sz k)
         (img      : ∀ n m → fetch P n ≡ just (instr-ctrl (c-label m)) → ImgL m)
         (jmp-lbl  : ∀ n m → fetch P n ≡ just (instr-ctrl (c-jmp m)) → ImgL m)
         (br-lbl   : ∀ n m → fetch P n ≡ just (instr-ctrl (c-branch-tag-zero m)) → ImgL m)
         {Good : FlatState → Set} where
  open Rel
  private
    module DX = Once.CCC.Codegen.AllocExpandDispatch {FS}
    EX = expand C P
    K = Keeps C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl Good

  module NoFault (Kp : K) where
    open Keeps Kp

    sound-at : ∀ b {fs gs k x} → k ≤ b → Good fs → LocState.faulted (floc fs) ≡ false → Rel C P Sz fs gs
             → FlatSteps EX k gs x → LocState.faulted (floc x) ≡ false
    sound-at b kb G nf0 R [] = trans (L.LRel.l-fault (r-loc R)) nf0
    sound-at b {fs} {gs} {k} {x} kb G nf0 R d@((hg , fg) ∷ _) = by-f (fetch P (fpc fs)) refl
      where
        h : LocState.halted (floc fs) ≡ false
        h = trans (sym (L.LRel.l-halt (r-loc R))) hg

        by-f : ∀ mi → fetch P (fpc fs) ≡ mi → LocState.faulted (floc x) ≡ false
        by-f nothing ef = ⊥-elim (no (trans (sym fg) (trans (cong (fetch EX) (r-pc R)) (fetch-none C 0 P (fpc fs) ef))))
          where
            no : ∀ {X : Set} {v : X} → just v ≡ nothing → ⊥
            no ()
        by-f (just i) ef = go (DX.dispatch C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl R i ef (g-em G ef) (g-ns G ef) (g-nr G ef) h (g-nf G h ef) (g-wf G) (g-cw G))
          where
            go : DX.Step C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl i fs gs → LocState.faulted (floc x) ≡ false
            go (N , gs′ , c , _ , R′) = split (meet c d) b kb
              where
                split : ((Σ ℕ λ j → FlatSteps EX j gs′ x × k ≡ suc N + j) ⊎ (Σ ℕ λ j → FlatSteps EX (suc j) x gs′))
                      → ∀ b′ → k ≤ b′ → LocState.faulted (floc x) ≡ false
                split (inj₁ (j , r , e)) zero    kb′ = ⊥-elim (Data.Nat.Properties.<⇒≱ (subst (0 <_) (sym e) (Data.Nat.s≤s z≤n)) kb′)
                split (inj₁ (j , r , e)) (suc b′) kb′ =
                  sound-at b′
                    (Data.Nat.Properties.≤-pred (Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-trans (Data.Nat.s≤s (Data.Nat.Properties.m≤n+m j N)) (Data.Nat.Properties.≤-reflexive (sym e))) kb′))
                    (g-step G h ef) (g-nf G h ef) R′ r
                split (inj₂ (j , (hx , _) ∷ _)) _ _ = trans (chain-fault d hx) (trans (L.LRel.l-fault (r-loc R)) nf0)

    sound : ∀ {fs gs} → Good fs → LocState.faulted (floc fs) ≡ false → Rel C P Sz fs gs → Sound EX gs
    sound G nf0 R d = sound-at _ Data.Nat.Properties.≤-refl G nf0 R d

------------------------------------------------------------------------
-- ★ From the start: the start's step alike (it reads no program), then the
-- expansion's set-up (no event) to the first relation
------------------------------------------------------------------------

open import Once.CCC.Codegen.AllocExpandStart {FS} using (Start; module First)
open import Once.CCC.Codegen.AllocExpandPc {FS} using (fetch-exp)

module Start′ (C : Classes) (P : AbstractTrace) (Sz : ℕ → Set)
         (uniform  : ∀ k k′ → Sz k → Sz k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′)
         (fits     : ∀ k → k ≤ bsz C k)
         (in-range : ∀ k → cls C k < count C)
         (sz-alloc : ∀ n k → fetch P n ≡ just (instr-alloc-heap k) → Sz k)
         (sz-free  : ∀ n k → fetch P n ≡ just (instr-free-heap k) → Sz k)
         (img      : ∀ n m → fetch P n ≡ just (instr-ctrl (c-label m)) → ImgL m)
         (jmp-lbl  : ∀ n m → fetch P n ≡ just (instr-ctrl (c-jmp m)) → ImgL m)
         (br-lbl   : ∀ n m → fetch P n ≡ just (instr-ctrl (c-branch-tag-zero m)) → ImgL m)
         {Good : FlatState → Set} (Kp : Keeps C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl Good)
         (s₀ : FlatState) (b : ℕ) (st : fetch P 0 ≡ just (instr-ctrl (c-start b)))
         (pc0 : fpc s₀ ≡ 0) (h0 : LocState.halted (floc s₀) ≡ false)
         (S : Start (flat-exec-instr (instr-ctrl (c-start b)) P s₀))
         (pc1 : fpc (flat-exec-instr (instr-ctrl (c-start b)) P s₀) ≡ 1)
         (link : flink (flat-exec-instr (instr-ctrl (c-start b)) P s₀) ≡ nothing)
         (G₁ : Good (flat-exec-instr (instr-ctrl (c-start b)) P s₀)) where
  private
    EB = expand C P
    x = flat-exec-instr (instr-ctrl (c-start b)) P s₀

    off0 : ∀ Q → off C 0 Q 0 ≡ 0
    off0 []      = refl
    off0 (_ ∷ _) = refl

    fe : ∀ j i → fetch (setup C) j ≡ just i → fetch EB (j + fpc x) ≡ just i
    fe j i e = subst (λ q → fetch EB q ≡ just i)
                 (trans (cong (_+ suc j) (off0 P)) (trans (sym (Data.Nat.Properties.+-comm j 1)) (cong (j +_) (sym pc1))))
                 (fetch-exp C 0 P 0 (instr-ctrl (c-start b)) st (suc j) i e)

    fe0 : fetch EB (fpc s₀) ≡ just (instr-ctrl (c-start b))
    fe0 = subst (λ q → fetch EB q ≡ just (instr-ctrl (c-start b))) (trans (cong (_+ 0) (off0 P)) (sym pc0))
                (fetch-exp C 0 P 0 (instr-ctrl (c-start b)) st 0 _ refl)

    st₀ : fetch P (fpc s₀) ≡ just (instr-ctrl (c-start b))
    st₀ = subst (λ q → fetch P q ≡ just (instr-ctrl (c-start b))) (sym pc0) st

    module F = First C P Sz x S fe pc1 link b st
    module SR = F.SR

    -- the start's step and the set-up, one chain
    c₀ : FlatSteps EB (suc (4 + (count C + 6))) s₀ SR.z₆
    c₀ = (h0 , fe0) ∷ SR.run

    -- the set-up logs nothing (its end's log is the start's: `R₀`)
    quiet : chain-events SR.run ≡ []
    quiet = Data.List.Properties.++-cancelˡ (LocState.ev-log (floc x)) (chain-events SR.run) []
              (trans (sym (chain-log SR.run)) (trans (L.LRel.l-log (Rel.r-loc F.R₀)) (sym (Data.List.Properties.++-identityʳ _))))

  ev-start : ∀ n → Σ ℕ λ m → Same C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl (suc m) s₀ (suc n) s₀
  ev-start n = go (Run.ev C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl Kp n G₁ F.R₀)
    where
      go : Σ ℕ (λ m → Same C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl m SR.z₆ n x)
         → Σ ℕ λ m → Same C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl (suc m) s₀ (suc n) s₀
      go (m , ee , ec) =
        (4 + (count C + 6)) + m
        , trans (flat-events-steps c₀ m) (trans (cong₂ _▹_ quiet ee) (sym (ev-unfold n P s₀ h0 st₀)))
        , subst (_≤ flat-ctrls (suc (4 + (count C + 6)) + m) EB s₀) (sym (ct-unfold n P s₀ h0 st₀))
            (subst (ctrl-of (instr-ctrl (c-start b)) + flat-ctrls n P x ≤_) (sym (flat-ctrls-steps c₀ m))
              (Data.Nat.Properties.+-mono-≤ (Data.Nat.Properties.m≤m+n (ctrl-of (instr-ctrl (c-start b))) (chain-ctrls SR.run)) ec))

  -- …and the expanded run from the start never faults
  sound-start : LocState.faulted (floc s₀) ≡ false → LocState.faulted (floc x) ≡ false → Sound EB s₀
  sound-start nf0 nf1 {k} {y} d = split (meet c₀ d)
    where
      split : ((Σ ℕ λ j → FlatSteps EB j SR.z₆ y × k ≡ suc (4 + (count C + 6)) + j) ⊎ (Σ ℕ λ j → FlatSteps EB (suc j) y SR.z₆))
            → LocState.faulted (floc y) ≡ false
      split (inj₁ (j , r , _)) = NoFault.sound C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl Kp G₁ nf1 F.R₀ r
      split (inj₂ (j , (hy , _) ∷ _)) = trans (chain-fault d hy) nf0
