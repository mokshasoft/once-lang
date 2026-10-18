-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Backend.RunTraceMachine — the concrete machine as a machine
-- whose trace is read off by corecursion (D320, plan 0.119 §7 D4b).
--
-- `δ` is ONE step of `RunTraceCore.run-events`, read as what it shows
-- (`MachineTrace.Step`): a halted machine, a pc off the code and a failing
-- instruction end the run (`halted`); an arith block is a silent step; an
-- external call shows its events and continues where the call returns (or
-- halts there: a call with no answer, `ret-call`); any other instruction is a
-- silent step. The trace of the binary is `MachineTrace.Machine.trace δ`.
--
-- `ended-reaches`: a fuelled run that ENDED (`run-events … ≡ (es , just e)`)
-- is a run of `δ` that reaches `e` after the calls `es` — so its trace is the
-- finite trace of `es` and `e` (`MachineTrace.reaches-≈`). This is the bridge
-- from the fuelled correspondence to the trace.
------------------------------------------------------------------------

module Once.Arith.Backend.RunTraceMachine where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Lang.Event using (SigOpEvent; toEvent)
open import Once.Lang.Out using (Out; _▹_)
open import Once.Spec.Trace using (End)
import Once.Spec.Trace as ST
import Once.Arith.Backend.RunTraceCore as Core
open import Once.Adequacy.MachineTrace using (Step; silent; emit; stop; stuck; module Machine)

module RunMachine
  (State   : Set)
  (Program : Set)
  (Instr   : Set)
  (Payload : Set)
  (halted        : State → Bool)
  (pc            : State → ℕ)
  (fetch         : Program → ℕ → Maybe Instr)
  (execInstr     : Program → State → Instr → Maybe State)
  (matchCall     : Instr → Maybe String)
  (ret-call      : List SigOpEvent → String → State → State)
  (dispatchArith : Payload → State → State)
  where

  open Core.RunTrace State Program Instr Payload halted pc fetch execInstr matchCall ret-call dispatchArith

  -- A configuration: the calls made so far (the world answers from them) and
  -- the machine state.
  Conf : Set
  Conf = List SigOpEvent × State

  module _ (ev : EvExtractor) (env : ArithEnv) (prog : Program) where

    δ-h : Bool → List SigOpEvent → State → Step Conf
    δ-f : Maybe Instr → List SigOpEvent → State → Step Conf
    δ-i : Instr → Maybe String → List SigOpEvent → State → Step Conf
    δ-c : String → Maybe Payload → List SigOpEvent → State → Step Conf
    δ-e : Maybe State → List SigOpEvent → Step Conf

    δ : Conf → Step Conf
    δ (h , s) = δ-h (halted s) h s

    δ-h true  h s = stop [] ST.halted
    δ-h false h s = δ-f (fetch prog (pc s)) h s
    δ-f nothing  h s = stop [] ST.halted
    δ-f (just i) h s = δ-i i (matchCall i) h s
    δ-i i (just lbl) h s = δ-c lbl (env lbl) h s
    δ-i i nothing    h s = δ-e (execInstr prog s i) h
    δ-c lbl (just pl) h s = silent (h , dispatchArith pl s)
    δ-c lbl nothing   h s = emit (map toEvent (ev lbl s)) (h ++ ev lbl s , ret-call h lbl s)
    δ-e nothing   h = stop [] ST.halted
    δ-e (just s′) h = silent (h , s′)

    open Machine δ using (Reaches; r-silent; r-emit; r-stop)

    -- What a run shows, read as the Spec's calls.
    calls : Out → List _
    calls o = map toEvent (proj₁ o)

    private
      -- One clause of `run-events` each, by its scrutinee (no `with`).
      reach   : ∀ M h s {e} → proj₂ (run-events ev env h M prog s) ≡ just e
              → Reaches (h , s) (calls (run-events ev env h M prog s)) e
      reach-h : ∀ M h s (b : Bool) → halted s ≡ b → ∀ {e}
              → proj₂ (if b then Once.Lang.Out.stop else run-events-fetch ev env h M prog s (fetch prog (pc s))) ≡ just e
              → Reaches (h , s) (calls (if b then Once.Lang.Out.stop else run-events-fetch ev env h M prog s (fetch prog (pc s)))) e
      reach-f : ∀ M h s (mi : Maybe Instr) → fetch prog (pc s) ≡ mi → halted s ≡ false → ∀ {e}
              → proj₂ (run-events-fetch ev env h M prog s mi) ≡ just e
              → Reaches (h , s) (calls (run-events-fetch ev env h M prog s mi)) e
      reach-i : ∀ M h s i (ml : Maybe String) → matchCall i ≡ ml → fetch prog (pc s) ≡ just i → halted s ≡ false → ∀ {e}
              → proj₂ (run-events-instr ev env h M prog s i ml) ≡ just e
              → Reaches (h , s) (calls (run-events-instr ev env h M prog s i ml)) e
      reach-c : ∀ M h s i lbl (mp : Maybe Payload) → env lbl ≡ mp → matchCall i ≡ just lbl → fetch prog (pc s) ≡ just i
              → halted s ≡ false → ∀ {e}
              → proj₂ (run-events-call ev env h M prog s lbl mp) ≡ just e
              → Reaches (h , s) (calls (run-events-call ev env h M prog s lbl mp)) e
      reach-e : ∀ M h s i (ms : Maybe State) → execInstr prog s i ≡ ms → matchCall i ≡ nothing → fetch prog (pc s) ≡ just i
              → halted s ≡ false → ∀ {e}
              → proj₂ (run-events-exec ev env h M prog s ms) ≡ just e
              → Reaches (h , s) (calls (run-events-exec ev env h M prog s ms)) e

      δ≡ : ∀ h s {x} → δ (h , s) ≡ x → δ (h , s) ≡ x
      δ≡ h s q = q

      stopAt : ∀ {h s e} → δ (h , s) ≡ stop [] ST.halted → just ST.halted ≡ just e → Reaches (h , s) [] e
      stopAt q refl = r-stop q

    reach zero    h s ()
    reach (suc M) h s q = reach-h M h s (halted s) refl q

    reach-h M h s true  hs q = stopAt (trans (cong (λ b → δ-h b h s) hs) refl) q
    reach-h M h s false hs q = reach-f M h s (fetch prog (pc s)) refl hs q

    reach-f M h s nothing  fq hs q = stopAt (trans (cong (λ b → δ-h b h s) hs) (cong (λ m → δ-f m h s) fq)) q
    reach-f M h s (just i) fq hs q = reach-i M h s i (matchCall i) refl fq hs q

    reach-i M h s i (just lbl) mq fq hs q = reach-c M h s i lbl (env lbl) refl mq fq hs q
    reach-i M h s i nothing    mq fq hs q = reach-e M h s i (execInstr prog s i) refl mq fq hs q

    reach-c M h s i lbl (just pl) eq mq fq hs q =
      r-silent (trans (cong (λ b → δ-h b h s) hs) (trans (cong (λ m → δ-f m h s) fq)
               (trans (cong (λ m → δ-i i m h s) mq) (cong (λ m → δ-c lbl m h s) eq))))
               (reach M h (dispatchArith pl s) q)
    reach-c M h s i lbl nothing   eq mq fq hs {e} q =
      subst (λ es → Reaches (h , s) es e)
            (sym (map-++ toEvent (ev lbl s) (proj₁ (run-events ev env (h ++ ev lbl s) M prog (ret-call h lbl s)))))
            (r-emit (trans (cong (λ b → δ-h b h s) hs) (trans (cong (λ m → δ-f m h s) fq)
                    (trans (cong (λ m → δ-i i m h s) mq) (cong (λ m → δ-c lbl m h s) eq))))
                    (reach M (h ++ ev lbl s) (ret-call h lbl s) q))

    reach-e M h s i nothing   xq mq fq hs q =
      stopAt (trans (cong (λ b → δ-h b h s) hs) (trans (cong (λ m → δ-f m h s) fq)
             (trans (cong (λ m → δ-i i m h s) mq) (cong (λ m → δ-e m h) xq)))) q
    reach-e M h s i (just s′) xq mq fq hs q =
      r-silent (trans (cong (λ b → δ-h b h s) hs) (trans (cong (λ m → δ-f m h s) fq)
               (trans (cong (λ m → δ-i i m h s) mq) (cong (λ m → δ-e m h) xq))))
               (reach M h s′ q)

    -- THE BRIDGE: a fuelled run that ended is a run that reaches its end.
    ended-reaches : ∀ M h s {es e} → run-events ev env h M prog s ≡ (es , just e)
                  → Reaches (h , s) (map toEvent es) e
    ended-reaches M h s {es} {e} q =
      subst (λ o → Reaches (h , s) (calls o) e) q (reach M h s (cong proj₂ q))
