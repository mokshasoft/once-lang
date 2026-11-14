-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ArgDecode — plan 0.146 B1.5 (D428): THE MACHINE DECODES AN
-- OP'S ARGUMENT AS THE IMAGE HOLDS IT. At the sigop's state (`StepOp.arg`)
-- the machine's `decode-at` reads back the argument's value: a scalar from
-- the register its word was loaded into, a compound base value through its
-- address, in place (`readTyped`, D381: a product's words after each other,
-- a sum's tag then its payload) — the image's words (`VW`). Relative to the
-- word a base value is (`wordOf`: an `Int` or a `Float` is its literal).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc; _+_)
import Data.Nat.Properties
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just)
import Data.Maybe
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
import Once.Spec.Type as ST
open import Once.Type using (fits-int; fits-float)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.ArgDecode
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; er; mone; mpair; minl; minr; mbase)
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Layout fmt ans bw using (wsz)
open import Once.LinCore.Words fmt ans bw using (module Rel)
open import Once.LinCore.Lower fmt ans bw using (flatB)
open import Once.LinCore.StepOp fmt ans bw using (module Agree)

-- a base value's words: the machine's count is the image's
module _ {FS : FrameSemantics} where
  open AbstractExec {FS} using (tsize)

  tsize-wsz : ∀ {A} (b : ST.Base ST.∅ₖ A) → tsize A ≡ wsz ⌜ flatB b ⌝
  tsize-wsz (ST.b-var {i = ()} _)
  tsize-wsz ST.b-Unit    = refl
  tsize-wsz ST.b-Void    = refl
  tsize-wsz ST.b-Int     = refl
  tsize-wsz ST.b-Float   = refl
  tsize-wsz (ST.b-* a b) = cong₂ _+_ (tsize-wsz a) (tsize-wsz b)
  tsize-wsz (ST.b-+ a b) = cong suc (cong₂ Data.Nat._⊔_ (tsize-wsz a) (tsize-wsz b))

module Dec {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS)
           (w-int   : ∀ (n : ⟦ int ⟧b)   → wordOf {int} n ≡ SV-Lit fits-int n)
           (w-float : ∀ (n : ⟦ float ⟧b) → wordOf {float} n ≡ SV-Lit fits-float n) where
  open Rel {FS} U wordOf using (W; VW; vone; vpair; vinl; vinr; vbase; SlotsAt; vw-len)
  open AbstractExec {FS} using (readTyped; readTyped-int; readTyped-float; readTyped-sum; combine-typed; decode-at; tsize)
  open FlatMachine {FS} using (FlatState; floc; falloc)
  open Agree {FS} U wordOf using (arg; at-arg; argV)

  -- words after words
  slots-++ : ∀ {sm : ℕ → Maybe W} {d} (xs ys : List W) → SlotsAt sm d (xs ++ ys)
           → SlotsAt sm d xs × SlotsAt sm (length xs + d) ys
  slots-++ []       ys s       = _ , s
  slots-++ {sm} {d} (x ∷ xs) ys (e , s) = (e , proj₁ (slots-++ xs ys s)) , subst (λ z → SlotsAt sm z ys) (Data.Nat.Properties.+-suc (length xs) d) (proj₂ (slots-++ xs ys s))

  -- ★ a base value's words in place, read back
  read-in : ∀ {A} (b : ST.Base ST.∅ₖ A) (s : LocState FS) cf d {h} {x : MV ⌜ flatB b ⌝} {wx : List W}
          → VW h x wx → SlotsAt (LocState.stackMem s cf) d wx
          → readTyped A (AtStack cf d) s ≡ just (toV b (toF (flatB b) (er x)))
  read-in (ST.b-var {i = ()} _) s cf d p sx
  read-in ST.b-Unit s cf d vone sx = refl
  read-in ST.b-Void s cf d () sx
  read-in ST.b-Int s cf d (vbase {x = n}) (e , _) =
    trans (cong readTyped-int e) (cong (λ w → readTyped-int (just w)) (w-int n))
  read-in ST.b-Float s cf d (vbase {x = n}) (e , _) =
    trans (cong readTyped-float e) (cong (λ w → readTyped-float (just w)) (w-float n))
  read-in (ST.b-* {A = A₁} {B = B₁} a b) s cf d (vpair {wa = wa} {wb} pa pb) sx =
    cong₂ combine-typed (read-in a s cf d pa (proj₁ (slots-++ wa wb sx)))
      (read-in b s cf (tsize A₁ + d) pb (subst (λ z → SlotsAt (LocState.stackMem s cf) (z + d) wb) ln (proj₂ (slots-++ wa wb sx))))
    where
      ln : length wa ≡ tsize A₁
      ln = trans (vw-len pa) (sym (tsize-wsz {FS} a))
  read-in (ST.b-+ {A = A₁} {B = B₁} a b) s cf d (vinl {wa = wa} {pad} pa _) (e , sx) =
    trans (cong (λ z → readTyped-sum (λ _ → readTyped A₁ (AtStack cf (suc d)) s) (λ _ → readTyped B₁ (AtStack cf (suc d)) s) z
                                     (LocState.stackMem s cf (suc d))) e)
          (cong (Data.Maybe.map inj₁) (read-in a s cf (suc d) pa (proj₁ (slots-++ wa pad sx))))
  read-in (ST.b-+ {A = A₁} {B = B₁} a b) s cf d (vinr {wb = wb} {pad} pb _) (e , sx) =
    trans (cong (λ z → readTyped-sum (λ _ → readTyped A₁ (AtStack cf (suc d)) s) (λ _ → readTyped B₁ (AtStack cf (suc d)) s) z
                                     (LocState.stackMem s cf (suc d))) e)
          (cong (Data.Maybe.map inj₂) (read-in b s cf (suc d) pb (proj₁ (slots-++ wb pad sx))))

  -- ★ the machine's argument at the sigop's state is the image's (D428)
  arg-dec : ∀ {A} (b : ST.Base ST.∅ₖ A) (fs : FlatState) d (v : StoredValue FS) {h} {x : MV ⌜ flatB b ⌝} {wx : List W}
          → VW h x wx → SlotsAt (LocState.stackMem (floc fs) (AllocState.current-frame (falloc fs))) d wx
          → decode-at b (argV b fs d wx) (at-arg fs v) ≡ just (toV b (toF (flatB b) (er x)))
  arg-dec (ST.b-var {i = ()} _) fs d v p sx
  arg-dec ST.b-Unit fs d v vone sx = refl
  arg-dec ST.b-Void fs d v () sx
  arg-dec ST.b-Int fs d v (vbase {x = n}) sx = cong (λ w → decode-at ST.b-Int w (at-arg fs v)) (w-int n)
  arg-dec ST.b-Float fs d v (vbase {x = n}) sx = cong (λ w → decode-at ST.b-Float w (at-arg fs v)) (w-float n)
  arg-dec (ST.b-* a b) fs d v p sx = read-in (ST.b-* a b) (at-arg fs v) (AllocState.current-frame (falloc fs)) d p sx
  arg-dec (ST.b-+ a b) fs d v p sx = read-in (ST.b-+ a b) (at-arg fs v) (AllocState.current-frame (falloc fs)) d p sx
