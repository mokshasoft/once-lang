-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.AgreeRun — plan 0.146 B1.5 (D426, D429): THE MACHINE AGREES
-- WITH AN IMAGE RUN THE WORLD ANSWERED. An image run whose calls the
-- interpretation's world answered (`Total.WTr`, from the history `L`)
-- meets the machine's world at every op step (`RunWord.AgreesAll`), given
-- what an op owes at the machine (`o-op`, `o-opend`: the sigop at a state
-- whose log is the history computes the op's contract path). By induction
-- on the run, the history threaded: a step that gives a value adds its
-- events to it (it holds no halt), a halting op ends the run.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Event using (SigOpEvent)
open import Once.IR.Semantics.Trace using (FFIAnswers; Interp; callEvent)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.AgreeRun
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; Cfg)
open import Once.LinCore.Image fmt ans bw using (Codeᴵ; halted)
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; done; _⟫_)
open import Once.LinCore.Total fmt ans bw using (World; WTr)
open import Once.LinCore.StepOp fmt ans bw using (module Agree; evsOf; ioEvent)
open import Once.LinCore.Keys fmt ans bw using (Univ; ops)
open import Once.LinCore.StepIos fmt ans bw using (module IosG)
open import Once.LinCore.Global fmt ans bw using (module Relate)
import Once.LinCore.BudgetSound
module BudgetSound = Once.LinCore.BudgetSound fmt ans bw

------------------------------------------------------------------------
-- 1. A run that gives a value holds no halt
------------------------------------------------------------------------

IsCall : Io → Set
IsCall (io-call _ _ _) = ⊤
IsCall (io-halt _ _)   = ⊥

NoHalt : Trace → Set
NoHalt t = All IsCall (ios t)

private
  nh-++ : ∀ t₁ t₂ → NoHalt t₁ → NoHalt t₂ → NoHalt (t₁ ++ t₂)
  nh-++ t₁ t₂ a b = subst (All IsCall) (sym (ios-++ t₁ t₂)) (++⁺ a b)

  nh-[] : ∀ t → ios t ≡ [] → NoHalt t
  nh-[] t q = subst (All IsCall) (sym q) []

  path-nh : ∀ {X : Set} {b : T X} {t x} → OpPath b t (inj₁ x) → NoHalt t
  path-nh p-ret      = []
  path-nh (p-call p) = tt ∷ path-nh p

mutual
  gives-nh : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n w n′ t} → Run ds f e v n (gives w n′) t → NoHalt t
  gives-nh r-id = []
  gives-nh (r-∘ {t₁ = t₁} {t₂} rg (go-on rf)) = nh-++ t₁ t₂ (gives-nh′ rg) (gives-nh rf)
  gives-nh (r-⊗ {t₁ = t₁} {t₂} rf (go-on (fm-gives rg))) = nh-++ t₁ t₂ (gives-nh′ rf) (gives-nh rg)
  gives-nh r-ρ = []
  gives-nh r-ρ⁻ = []
  gives-nh r-λ = []
  gives-nh r-λ⁻ = []
  gives-nh r-α = []
  gives-nh r-α⁻ = []
  gives-nh r-swap = []
  gives-nh (r-dup {v = v} {n}) = nh-[] (proj₂ (proj₂ (copy v n))) (ios-copy v n)
  gives-nh (r-drop {v = v}) = nh-[] (freeAll v) (ios-freeAll v)
  gives-nh r-inl = []
  gives-nh r-inr = []
  gives-nh (r-case₁ r) = gives-nh r
  gives-nh (r-case₂ r) = gives-nh r
  gives-nh r-In = []
  gives-nh r-Outμ = []
  gives-nh r-clo = []
  gives-nh (r-app q r) = gives-nh r
  gives-nh (r-cata {t₁ = t₁} {t₂} rm (go-on ra)) = nh-++ t₁ t₂ (gives-nhM′ rm) (gives-nh ra)
  gives-nh (r-cata-reuse {t₁ = t₁} {t₂} rm (go-on (fm-gives rg))) = nh-++ t₁ t₂ (gives-nhM′ rm) (gives-nh rg)
  gives-nh (r-lend (fm-gives r)) = gives-nh r
  gives-nh (r-lift r) = gives-nh r
  gives-nh (r-fst r) = gives-nh r
  gives-nh (r-snd r) = gives-nh r
  gives-nh (r-caseE₁ r) = gives-nh r
  gives-nh (r-caseE₂ r) = gives-nh r
  gives-nh (r-out r) = gives-nh r
  gives-nh (r-copy {e = e} {n}) = nh-[] (proj₂ (proj₂ (copy e n))) (ios-copy e n)
  gives-nh (r-bapp q r) = gives-nh r
  gives-nh r-lam = []
  gives-nh r-lamω = []
  gives-nh (r-ev r) = gives-nh r
  gives-nh (r-bev r) = gives-nh r
  gives-nh r-unf = []
  gives-nh (r-nout r) = gives-nh r
  gives-nh r-const = []
  gives-nh (r-op p) = path-nh p
  gives-nh (r-iter {t₁ = t₁} r (go-on done)) = nh-++ t₁ [] (gives-nh r) []
  gives-nh (r-iter {t₁ = t₁} {t₂} r (go-on (again rn))) = nh-++ t₁ t₂ (gives-nh r) (gives-nh rn)
  gives-nh (r-tmp r wv p) = subst (All IsCall) (sym (ios-weave wv)) (gives-nh r)

  -- a sub-run that gave (any outcome type)
  gives-nh′ : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n w n′ t} → Run ds f e v n (gives w n′) t → NoHalt t
  gives-nh′ = gives-nh

  gives-nhM′ : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n w n′ t}
             → RunMap ds F alg e G x n (gives w n′) t → NoHalt t
  gives-nhM′ (m-id r) = gives-nh r
  gives-nhM′ m-one = []
  gives-nhM′ m-b = []
  gives-nhM′ m-μ = []
  gives-nhM′ (m-inl (fm-gives r)) = gives-nhM′ r
  gives-nhM′ (m-inr (fm-gives r)) = gives-nhM′ r
  gives-nhM′ (m-pair {t₁ = t₁} {t₂} r (go-on (fm-gives r′))) = nh-++ t₁ t₂ (gives-nhM′ r) (gives-nhM′ r′)

------------------------------------------------------------------------
-- 2. ★ The machine agrees along an image run the world answered
------------------------------------------------------------------------

open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.Keys fmt ans bw using (module Program)
open import Once.LinCore.RunWord fmt ans bw using (module RunW)
open import Function using (case_of_)

module AR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
          (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
          (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
          (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) (ι : Interp)
          (o-op : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {y₀ tp L L′}
                → OpPath (opF s (toF (sdom s) (er x))) tp (inj₁ y₀) → WTr (BudgetSound.W.Wι ι) L tp L′
                → ∀ fs → LocState.ev-log (FlatMachine.floc {FS} fs) ≡ L
                → Agree.OpVal {FS} (Program.U ds f) wordOf s x (mvF (scod s) y₀) (evsOf tp) fs)
          (o-opend : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {tp L L′} → s ∈ ops (Program.U ds f)
                → OpPath (opF s (toF (sdom s) (er x))) tp (inj₂ halted) → WTr (BudgetSound.W.Wι ι) L tp L′
                → ∀ fs → LocState.ev-log (FlatMachine.floc {FS} fs) ≡ L
                → Agree.OpHalt {FS} (Program.U ds f) wordOf s x (evsOf tp) fs) where
  open BudgetSound.W ι using (Wι; answered; wtr-split; wtr-weave; op-ret-run)
  open Agree {FS} (Program.U ds f) wordOf using (Agrees; OpVal; OpHalt)
  open RunW {FS} ds f ldConst ld-nl wordOf using (AgreesAll)
  open Relate {FS} ds f ldConst ld-nl wordOf using (Related; module Related)
  open IosG {FS} ds f ldConst ld-nl wordOf using (here-prim)
  open FlatMachine {FS} using (FlatState; floc)

  -- a trace with no halt: the history after it is the history and its events
  wtr-hist : ∀ {L L₁} t → WTr Wι L t L₁ → NoHalt t → L₁ ≡ L ++ evsOf t
  wtr-hist {L} []             refl _  = sym (++-identityʳ L)
  wtr-hist (alloc _ ∷ t)      w    nh = wtr-hist t w nh
  wtr-hist (free _ ∷ t)       w    nh = wtr-hist t w nh
  wtr-hist (peek _ ∷ t)       w    nh = wtr-hist t w nh
  wtr-hist (tmp _ ∷ t)        w    nh = wtr-hist t w nh
  wtr-hist {L} (io o a y ∷ t) (h₁ , e , w) (_ ∷ nh) = at (answered e)
    where
      at : _ → _
      at (ca , refl) = trans (wtr-hist t w nh) (++-assoc L (callEvent o a ∷ []) (evsOf t))
  wtr-hist (stp _ _ ∷ t)      w    (() ∷ _)

  -- the world's answers depend only on the calls
  WTrIo : List SigOpEvent → List Io → List SigOpEvent → Set
  WTrIo h []                  h′ = h′ ≡ h
  WTrIo h (io-call o a y ∷ p) h′ = Σ (List SigOpEvent) λ h₁ → (World.answer Wι h o a ≡ just (y , h₁)) × WTrIo h₁ p h′
  WTrIo h (io-halt _ _ ∷ p)   h′ = WTrIo h p h′

  to-io : ∀ {h h′} t → WTr Wι h t h′ → WTrIo h (ios t) h′
  to-io []              w = w
  to-io (alloc _ ∷ t)   w = to-io t w
  to-io (free _ ∷ t)    w = to-io t w
  to-io (peek _ ∷ t)    w = to-io t w
  to-io (tmp _ ∷ t)     w = to-io t w
  to-io (io o a y ∷ t)  (h₁ , e , w) = h₁ , e , to-io t w
  to-io (stp _ _ ∷ t)   w = to-io t w

  from-io : ∀ {h h′} t → WTrIo h (ios t) h′ → WTr Wι h t h′
  from-io []              w = w
  from-io (alloc _ ∷ t)   w = from-io t w
  from-io (free _ ∷ t)    w = from-io t w
  from-io (peek _ ∷ t)    w = from-io t w
  from-io (tmp _ ∷ t)     w = from-io t w
  from-io (io o a y ∷ t)  (h₁ , e , w) = h₁ , e , from-io t w
  from-io (stp _ _ ∷ t)   w = from-io t w

  wtr-ios : ∀ {h h′} t t′ → ios t ≡ ios t′ → WTr Wι h t h′ → WTr Wι h t′ h′
  wtr-ios t t′ e w = from-io t′ (subst (λ p → WTrIo _ p _) e (to-io t w))

  -- an op's run: its contract path, the machine's agreement, the history after
  prim-op : ∀ {Γ′} {ds′ : Defs Γ′} {s : Sig} {x : MV ⌜ sdom s ⌝} {y n n′ t L L₁}
          → Run ds′ (lop s) mone x n (gives y n′) t → WTr Wι L t L₁
          → (∀ fs → LocState.ev-log (floc fs) ≡ L → OpVal s x y (evsOf t) fs) × (L₁ ≡ L ++ evsOf t)
  prim-op {s = s} {x = x} (r-op p) w = (λ fs lg → o-op {s = s} {x = x} p w fs lg) , proj₂ (op-ret-run p w)
  prim-op {s = s} {x = x} {y = y} {L = L} (r-tmp r wv _) w =
    let (A , H) = prim-op r (wtr-weave wv w)
        e = cong (map ioEvent) (sym (ios-weave wv))
    in (λ fs lg → subst (λ E → OpVal s x y E fs) e (A fs lg)) , trans H (cong (L ++_) e)

  private
    quiet : ∀ {L L₁ : List SigOpEvent} → L₁ ≡ L → L₁ ≡ L ++ []
    quiet {L} w = trans w (sym (++-identityʳ L))

  module _ {T : Sh} where
    -- ★ one step: the machine agrees, and the history goes on (or the run halted)
    agree-step : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
                 (st : StepI c r m n t c′ r′ m′ n′) {L L₁} → WTr Wι L t L₁
               → (∀ fs → Related c r m n fs → LocState.ev-log (floc fs) ≡ L → Agrees st fs) × ((c′ ≡ halted) ⊎ (L₁ ≡ L ++ evsOf t))
    agree-step (i-prim {g = lop s} run) w = let (A , H) = prim-op run w in (λ fs _ lg → A fs lg) , inj₂ H
    agree-step (i-prim {g = lid} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = _ ∘l _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = _ ⊗l _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = ρl} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = ρl⁻} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lul} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lul⁻} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lassoc} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lassoc⁻} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lswap} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = dup} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = drop} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = linl} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = linr} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lcase _ _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lzero} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lIn} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lOutμ} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lcata _ _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lclo _ _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lapp _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lend _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = blift _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = bcopy} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = llam _ _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = llamω _ _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lev} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lunf} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lout} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = lconst _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-prim {g = liter _ _} {t = t} run) w = (λ _ _ _ → tt) , inj₂ (wtr-hist t w (gives-nh run))
    agree-step (i-opend {s = s} {x = x} p) w =
      (λ fs G lg → o-opend {s = s} {x = x} (here-prim (Related.g-pt G) (Related.g-here G)) p w fs lg) , inj₁ refl
    agree-step i-unpair w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-pair w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-swap w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-unit w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-untag w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-untag₁ w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-tag₁ w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-case₁ w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-case₂ w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-elend w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-eunlend w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-elift w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-epop w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-call w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-ret w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-reti w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-loop w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-icall w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-iobs w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-cfree w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-nfree w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-open1 w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-nopen w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-fopen w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step i-fopenν w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-efst _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-esnd _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-eout _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-eoutq _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-ecase₁ _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-ecase₂ _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-eapp _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-eword _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-icallω _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-ccopy _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-ncopy _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-openω _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-copen _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-copenν _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-reclose _) w = (λ _ _ _ → tt) , inj₂ (quiet w)
    agree-step (i-recloseν _) w = (λ _ _ _ → tt) , inj₂ (quiet w)

    private
      no-more : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′} {L}
           → c ≡ halted → (rest : StepsI c r m n t c′ r′ m′ n′) → AgreesAll L rest
      no-more refl done       = tt
      no-more refl (() ⟫ _)

    -- ★★ the whole run
    agrees-all : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
                 (st : StepsI c r m n t c′ r′ m′ n′) {L L′} → WTr Wι L t L′ → AgreesAll L st
    agrees-all done w = tt
    agrees-all (_⟫_ {t₁ = t₁} {t₂} st rest) {L} {L′} w =
      let (L₁ , w₁ , w₂) = wtr-split t₁ w
          (A , h) = agree-step st w₁
      in A , after h rest w₂
      where
        after : ∀ {L₁ sh″ U‴} {c₁ : Codeᴵ _ _} {r₁ m₁ n₁} {c″ : Codeᴵ sh″ U‴} {r″ m″ n″}
              → (c₁ ≡ halted) ⊎ (L₁ ≡ L ++ evsOf t₁) → (rest : StepsI c₁ r₁ m₁ n₁ t₂ c″ r″ m″ n″) → WTr Wι L₁ t₂ L′
              → AgreesAll (L ++ evsOf t₁) rest
        after (inj₁ e) rest w₂ = no-more e rest
        after (inj₂ h) rest w₂ = agrees-all rest (subst (λ z → WTr Wι z t₂ L′) h w₂)
