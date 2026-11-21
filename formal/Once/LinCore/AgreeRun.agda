-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.AgreeRun — plan 0.146 B1.5 (D443, D446): THE MACHINE AGREES
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
open import Data.Empty using (⊥; ⊥-elim)
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

open import Once.LinCore.Core fmt using (Sig; sdom; scod; ⌜_⌝; toF; LTm; One; Defs; lid; _∘l_; _⊗l_; ρl; ρl⁻; lul; lul⁻; lassoc; lassoc⁻; lswap; dup; drop; linl; linr; lcase; lzero; lIn; lOutμ; lcata; lclo; lapp; lend; blift; bfst; bsnd; bcaseE; bout; bcopy; bapp; llam; llamω; lev; bev; lunf; lout; lconst; lop; liter)
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.NbEPLinCore fmt ans using (opF)
open import Once.LinCore.Events fmt ans bw using (er; OpPath; Run; gives; ios; ios-weave; Io; io-call; io-halt; halted)
open import Once.LinCore.Values fmt bw using (MV; mvF; mone; Trace; alloc; free; peek; tmp; io; stp)
open import Once.LinCore.Code fmt bw using (Sh; Cfg)
open import Once.LinCore.Image fmt bw using (Codeᴵ; halted)
open import Once.LinCore.ImageRun fmt ans bw using (halted-stuck; Ret; StepI)
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; done; _⟫_)
open import Once.LinCore.Total fmt ans bw using (World; WTr)
open import Once.LinCore.StepOp fmt ans bw using (module Agree; evsOf; ioEvent)
open import Once.LinCore.Keys fmt bw using (Univ; module Univ)
open Univ using (ops)
open import Once.LinCore.StepIos fmt ans bw using (module IosG)
open import Once.LinCore.Global fmt ans bw using (module Relate)
import Once.LinCore.BudgetSound
module BudgetSound = Once.LinCore.BudgetSound fmt ans bw
open import Once.LinCore.NoHalt fmt ans bw using (IsCall; NoHalt; gives-nh; op-elim)

------------------------------------------------------------------------
-- 2. ★ The machine agrees along an image run the world answered
------------------------------------------------------------------------

open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.Keys fmt bw using (module Program)
open import Once.LinCore.RunWord fmt ans bw using (module RunW)
open import Function using (case_of_)

module AR {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
          (ldConst : ∀ {b} → Lit b → AbstractInstr)
          (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
          (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) (ι : Interp)
          (o-op : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {y₀ tp L L′}
                → OpPath (opF s (toF (sdom s) (er x))) tp (inj₁ y₀) → WTr (BudgetSound.W.Wι ι) L tp L′
                → ∀ fs → LocState.ev-log (FlatMachine.FlatState.floc {FS} fs) ≡ L
                → Agree.OpVal {FS} (Program.U ds f) wordOf s x (mvF (scod s) y₀) (evsOf tp) fs)
          (o-opend : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {tp L L′} → s ∈ ops (Program.U ds f)
                → OpPath (opF s (toF (sdom s) (er x))) tp (inj₂ halted) → WTr (BudgetSound.W.Wι ι) L tp L′
                → ∀ fs → LocState.ev-log (FlatMachine.FlatState.floc {FS} fs) ≡ L
                → Agree.OpHalt {FS} (Program.U ds f) wordOf s x (evsOf tp) fs) where
  open BudgetSound.W ι using (Wι; answered; wtr-split; wtr-weave; op-ret-run)
  open Agree {FS} (Program.U ds f) wordOf using (PrimOk; Agrees; OpVal; OpHalt; StepCase; sc-prim; sc-opend; sc-quiet; step-case)
  open RunW {FS} ds f ldConst ld-nl wordOf using (AgreesAll)
  open Relate {FS} ds f ldConst ld-nl wordOf using (Related; module Related)
  open IosG {FS} ds f ldConst ld-nl wordOf using (here-prim)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc)

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
  prim-op {s = s} {x = x} run w = op-elim Goal
      (λ p w → (λ fs lg → o-op {s = s} {x = x} p w fs lg) , proj₂ (op-ret-run p w))
      (λ {y} {t = t} {t′ = t′} r ih wv _ {L} w →
         let (A , H) = ih (wtr-weave wv w)
             e = cong (map ioEvent) (sym (ios-weave wv))
         in (λ fs lg → subst (λ E → OpVal s x y E fs) e (A fs lg)) , trans H (cong (L ++_) e))
      run w
    where
      -- (an op's run split once, in `NoHalt`)
      Goal : MV ⌜ scod s ⌝ → ℕ → ℕ → Trace → Set
      Goal y n n′ t = ∀ {L L₁} → WTr Wι L t L₁ → (∀ fs → LocState.ev-log (floc fs) ≡ L → OpVal s x y (evsOf t) fs) × (L₁ ≡ L ++ evsOf t)

  private
    quiet : ∀ {L L₁ : List SigOpEvent} → L₁ ≡ L → L₁ ≡ L ++ []
    quiet {L} w = trans w (sym (++-identityʳ L))

  module _ {T : Sh} where
    private
      -- a prim's agreement (`PrimOk`): an op's is its contract (`prim-op`), every other prim owes nothing
      prim-ok : ∀ {Γ′} {ds′ : Defs Γ′} {A B} {g : LTm Γ′ A B} {v w n n′ t}
                (run : Run ds′ g mone v n (gives w n′) t) {L L₁} → WTr Wι L t L₁
              → ∀ fs → LocState.ev-log (floc fs) ≡ L → PrimOk g v w t fs
      prim-ok {g = lop s} run w fs lg = proj₁ (prim-op run w) fs lg
      prim-ok {g = lid} _ _ _ _ = tt
      prim-ok {g = _ ∘l _} _ _ _ _ = tt
      prim-ok {g = _ ⊗l _} _ _ _ _ = tt
      prim-ok {g = ρl} _ _ _ _ = tt
      prim-ok {g = ρl⁻} _ _ _ _ = tt
      prim-ok {g = lul} _ _ _ _ = tt
      prim-ok {g = lul⁻} _ _ _ _ = tt
      prim-ok {g = lassoc} _ _ _ _ = tt
      prim-ok {g = lassoc⁻} _ _ _ _ = tt
      prim-ok {g = lswap} _ _ _ _ = tt
      prim-ok {g = dup} _ _ _ _ = tt
      prim-ok {g = drop} _ _ _ _ = tt
      prim-ok {g = linl} _ _ _ _ = tt
      prim-ok {g = linr} _ _ _ _ = tt
      prim-ok {g = lcase _ _} _ _ _ _ = tt
      prim-ok {g = lzero} _ _ _ _ = tt
      prim-ok {g = lIn} _ _ _ _ = tt
      prim-ok {g = lOutμ} _ _ _ _ = tt
      prim-ok {g = lcata _ _} _ _ _ _ = tt
      prim-ok {g = lclo _ _} _ _ _ _ = tt
      prim-ok {g = lapp _} _ _ _ _ = tt
      prim-ok {g = lend _} _ _ _ _ = tt
      prim-ok {g = blift _} _ _ _ _ = tt
      prim-ok {g = bcopy} _ _ _ _ = tt
      prim-ok {g = llam _ _} _ _ _ _ = tt
      prim-ok {g = llamω _ _} _ _ _ _ = tt
      prim-ok {g = lev} _ _ _ _ = tt
      prim-ok {g = lunf} _ _ _ _ = tt
      prim-ok {g = lout} _ _ _ _ = tt
      prim-ok {g = lconst _} _ _ _ _ = tt
      prim-ok {g = liter _ _} _ _ _ _ = tt

      -- a step with no i/o: the history stays
      quiet-io : ∀ {L L₁} t → ios t ≡ [] → WTr Wι L t L₁ → L₁ ≡ L ++ evsOf t
      quiet-io {L} t q w = trans (quiet (subst (λ p → WTrIo L p _) q (to-io t w))) (cong (λ p → L ++ map ioEvent p) (sym q))

      -- by the step's case (`step-case`: the one split on a step, in `StepOp`)
      by-case : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
                {st : StepI c r m n t c′ r′ m′ n′} → StepCase st → ∀ {L L₁} → WTr Wι L t L₁
              → (∀ fs → Related c r m n fs → LocState.ev-log (floc fs) ≡ L → Agrees st fs) × ((c′ ≡ halted) ⊎ (L₁ ≡ L ++ evsOf t))
      by-case (sc-prim {t = t} {run = run}) w = (λ fs _ lg → prim-ok run w fs lg) , inj₂ (wtr-hist t w (gives-nh run))
      by-case (sc-opend {s = s} {x = x} {p = p}) w =
        (λ fs G lg → o-opend {s = s} {x = x} (here-prim (Related.g-pt G) (Related.g-here G)) p w fs lg) , inj₁ refl
      by-case (sc-quiet {t = t} q a) w = (λ fs _ _ → a fs) , inj₂ (quiet-io t q w)

    -- ★ one step: the machine agrees, and the history goes on (or the run halted)
    agree-step : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
                 (st : StepI c r m n t c′ r′ m′ n′) {L L₁} → WTr Wι L t L₁
               → (∀ fs → Related c r m n fs → LocState.ev-log (floc fs) ≡ L → Agrees st fs) × ((c′ ≡ halted) ⊎ (L₁ ≡ L ++ evsOf t))
    agree-step st = by-case (step-case st)

    private
      no-more : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′} {L}
           → c ≡ halted → (rest : StepsI c r m n t c′ r′ m′ n′) → AgreesAll L rest
      no-more _ done       = tt
      no-more e (st ⟫ _) = ⊥-elim (halted-stuck e st)

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
