-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Once.LinCore.SizedI
--
-- ★ D471 on the image: every cell a configuration and its saved frames hold
-- is well-sized (`Sized.WS`), step by step (`ws-stepI`): a step moves values
-- (or views them), runs a primitive (`ws-run`), or builds a cell of its
-- type's size (`i-reclose`).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Data.Nat using (ℕ)

module Once.LinCore.SizedI
  (fmt : TargetNum)
  (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Data.Maybe using (just; nothing)
open import Data.List using (_∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.LinCore.Core fmt
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)
open import Once.LinCore.Image fmt bw using (Codeᴵ; topv; _⊳_)
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.Sized fmt ans bw using (WS; ws-run)
open import Once.LinCore.Machine fmt ans bw using (start)

WSE : ∀ {Es} → Slots Es → Set
WSE []ᵉ         = ⊤
WSE (vw e es)   = WS e × WSE es
WSE (ln e x es) = (WS e × WS x) × WSE es

WSS : ∀ {S} → Stk S → Set
WSS []ˢ       = ⊤
WSS (v ∷ˢ os) = WS v × WSS os

WSC : ∀ {sh} → Cfg sh → Set
WSC (es ∥ os) = WSE es × WSS os

WSR : ∀ {U T} → Ret U T → Set
WSR []ʳ             = ⊤
WSR (frm k es os r) = WSE es × (WSS os × WSR r)
WSR (k ∷ⁱ r)        = WSR r

ws-see : ∀ {E Es} (es : Slots (E ∷ Es)) → WSE es → WS (see es)
ws-see (vw e es)   (w , _) = w
ws-see (ln e x es) (w , _) = w

seen : ∀ {E Es} (es : Slots (E ∷ Es)) {v : MV E} → see es ≡ v → WSE es → WS v
seen es refl w = ws-see es w

ws-topv : ∀ t {Es} (es : Slots (t ⊳ Es)) → WSE es → WSE (topv t es)
ws-topv nothing  es w = tt
ws-topv (just E) es w = ws-see es w , tt

-- the start: nothing held
ws-start : WSC start
ws-start = (tt , tt) , (tt , tt)

-- ★ a step keeps every held cell well-sized
ws-stepI : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
         → StepI c r m n t c′ r′ m′ n′ → WSC m → WSR r → WSC m′ × WSR r′
ws-stepI i-unpair (we , ((wa , wb) , wo)) wr = (we , (wa , (wb , wo))) , wr
ws-stepI i-pair (we , (wa , (wb , wo))) wr = (we , ((wa , wb) , wo)) , wr
ws-stepI i-swap (we , (wa , (wb , wo))) wr = (we , (wb , (wa , wo))) , wr
ws-stepI i-unit (we , wo) wr = (we , (tt , wo)) , wr
ws-stepI (i-prim run) (we , (wv , wo)) wr = (we , (ws-run run tt wv , wo)) , wr
ws-stepI (i-opend _) (we , (_ , wo)) wr = (we , wo) , wr
ws-stepI i-untag c wr = c , wr
ws-stepI i-oncify c wr = c , wr
ws-stepI i-untag₁ c wr = c , wr
ws-stepI i-tag₁ c wr = c , wr
ws-stepI i-case₁ c wr = c , wr
ws-stepI i-case₂ c wr = c , wr
ws-stepI (i-elend {es = es}) (we , ((wx , wa) , wo)) wr = (((ws-see es we , wx) , we) , (wa , wo)) , wr
ws-stepI i-eunlend (((_ , wx) , wes) , (ww , wo)) wr = (wes , ((wx , ww) , wo)) , wr
ws-stepI i-elift (we , wo) wr = ((tt , we) , wo) , wr
ws-stepI (i-efst {es = es} eq) (we , wo) wr = ((proj₁ (seen es eq we) , we) , wo) , wr
ws-stepI (i-esnd {es = es} eq) (we , wo) wr = ((proj₂ (seen es eq we) , we) , wo) , wr
ws-stepI (i-eout {es = es} eq) (we , wo) wr = ((proj₂ (seen es eq we) , we) , wo) , wr
ws-stepI (i-eoutq {es = es} eq) (we , wo) wr = ((proj₂ (seen es eq we) , we) , wo) , wr
ws-stepI (i-ecase₁ {es = es} eq) (we , wo) wr = ((seen es eq we , we) , wo) , wr
ws-stepI (i-ecase₂ {es = es} eq) (we , wo) wr = ((seen es eq we , we) , wo) , wr
ws-stepI (i-eapp {es = es} eq) (we , wo) wr = ((seen es eq we , we) , wo) , wr
ws-stepI i-epop ((_ , we) , wo) wr = (we , wo) , wr
ws-stepI (i-eword _) (we , (_ , wo)) wr = (we , (tt , wo)) , wr
ws-stepI (i-call {es = es}) (we , (wa , wo)) wr = (ws-topv _ es we , (wa , tt)) , (we , (wo , wr))
ws-stepI i-ret (_ , (wb , _)) (we , (wo , wr)) = (we , (wb , wo)) , wr
ws-stepI i-reti c wr = c , wr
ws-stepI i-loop c wr = c , wr
ws-stepI i-icall (we , (wf , wo)) wr = (tt , (wf , tt)) , (we , (wo , wr))
ws-stepI (i-icallω {es = es} _) (we , (wa , wo)) wr = ((ws-see es we , tt) , (wa , tt)) , (we , (wo , wr))
ws-stepI i-iobs (we , (wn , wo)) wr = (tt , (wn , tt)) , (we , (wo , wr))
ws-stepI (i-ccopy {es = es} _) (we , (_ , wo)) wr = ((ws-see es we , tt) , (tt , tt)) , (we , (wo , wr))
ws-stepI (i-ncopy {es = es} _) (we , (_ , wo)) wr = ((ws-see es we , tt) , (tt , tt)) , (we , (wo , wr))
ws-stepI i-cfree (we , (wf , wo)) wr = (tt , (wf , tt)) , (we , (wo , wr))
ws-stepI i-nfree (we , (wn , wo)) wr = (tt , (wn , tt)) , (we , (wo , wr))
ws-stepI i-open1 (we , (((_ , wx) , wa) , wo)) wr = (we , ((wx , wa) , wo)) , wr
ws-stepI (i-openω {es = es} eq) (we , wo) wr = ((proj₂ (seen es eq we) , we) , wo) , wr
ws-stepI i-nopen (we , ((_ , wp) , wo)) wr = (we , (wp , wo)) , wr
ws-stepI (i-copen {es = es} eq) (we , wo) wr = ((proj₂ (seen es eq we) , we) , wo) , wr
ws-stepI (i-copenν {es = es} eq) (we , wo) wr = ((proj₂ (seen es eq we) , we) , wo) , wr
ws-stepI (i-reclose _) (we , (wx , wo)) wr = (we , ((refl , wx) , wo)) , wr
ws-stepI (i-recloseν _) (we , (wp , wo)) wr = (we , ((refl , wp) , wo)) , wr
ws-stepI i-fopen (we , ((_ , wx) , wo)) wr = (we , (wx , wo)) , wr
ws-stepI i-fopenν (we , ((_ , wp) , wo)) wr = (we , (wp , wo)) , wr
