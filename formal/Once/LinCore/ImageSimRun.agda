-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageSimRun — plan 0.146 B1.4a: the image simulates the run
-- (A16's `Machine.sim`, for the image; the runs of the image and the
-- combinators are `ImageSim`'s). Split from `ImageSim` for its build time
-- (each module under 60 s alone); its context is one argument (`Ctx`), for
-- the termination checker.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Unit using (tt)
open import Data.Product using (_×_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (subst; sym; cong; trans)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.LinCore.Free using (_≼_; []≼; ≼-refl; weave-pre; Weave; w-[]; w-self)

module Once.LinCore.ImageSimRun
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt using (Defs; LF∙; LTm; LTy; One; Tm; ε)
open import Once.LinCore.Events fmt ans bw using (Outcome; Run; RunMap; gives; stop; go-on; stopped; again; done; fm-gives; fm-stop;
  m-id; m-one; m-b; m-μ; m-inl; m-inr; m-pair;
  r-id; r-∘; r-⊗; r-ρ; r-ρ⁻; r-λ; r-λ⁻; r-α; r-α⁻; r-swap; r-dup; r-drop; r-inl; r-inr; r-case₁; r-case₂; r-In; r-Outμ; r-clo;
  r-app; r-cata; r-cata-reuse; r-lend; r-lift; r-fst; r-snd; r-caseE₁; r-caseE₂; r-out; r-copy; r-bapp; r-lam; r-lamω; r-unf;
  r-nout; r-ev; r-bev; r-lamωᶜ; r-bevᶜ; r-evωᶜ; r-evω; r-const; r-op; r-opend; r-iter; r-exh; r-cut; r-tmp;
  halted; exhausted; ios; ios-weave; io-call; io-halt; OK; OK-weave; Pre; exchange; noleak; play; play-weave; lent₀)
open import Once.LinCore.Values fmt bw using (MV; Trace; TBal; TEv; TLeg; alloc; free; peek; io; stp; tmp; mone)
open import Once.LinCore.Temps fmt ans bw using (NoT-Bal; TOK-≼; erase; erase-NoT; erase-clean; k-alloc; k-free; k-peek; plain; weave-post)
open import Once.LinCore.Machine fmt ans bw using (Plain; PlainM; op-NoT)
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)
open import Once.LinCore.Spends fmt ans bw using (rounds; roundsM)
open import Once.LinCore.Image fmt bw using (Codeᴵ; compᴵ; travᴵ; _⨾_; end; halted; call; untag; eapp; epop; eout; openω; kbodyω)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; []ʳ; frm;
  i-unpair; i-pair; i-swap; i-unit; i-prim; i-opend; i-untag; i-case₁; i-case₂; i-elend; i-eunlend; i-elift; i-efst; i-esnd;
  i-eout; i-ecase₁; i-ecase₂; i-eapp; i-epop; i-call; i-reti; i-icall; i-icallω; i-icallᵒ; i-open1ω; i-iobs; i-nopen; i-open1; i-openω)
-- a ν is observed at the empty table (D440)
open import Once.LinCore.ObsTable fmt ans bw using (TF; tf-id; tf-∘; tf-⊗; tf-case; tf-inl; tf-inr; tf-lul; tf-lul⁻; tf-drop; tf-lend; tf-bsnd; tf-bcopy; tf-bev; tf-unf; rt; obsT-tf; rt-obsT)
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; done; loops; oneI; PausedI; paused; OutI; out; HaltIf; SimRI; sim-code;
  pre; preH; preR; preL; preLH; preLR; after; leaf; then; thenH; thenR; called′; calledH; calledR; calledR′; calledRω; around; tmpR;
  P-[]H; O-[]; doneO; copyS; freeS; look-key1; look-keyω; start)

------------------------------------------------------------------------
-- 6. ★ THE SIMULATION: the image runs the compiled code as the term runs,
-- for every outcome (A16's `sim`, with calls).
------------------------------------------------------------------------

-- what a simulation starts from, beside the run: the environment (its view the run's), the
-- stack under the operand, the code after, the returns. One argument: the termination
-- checker compares every argument of every call, and these nine, passed on in ever other
-- combinations, made its call graph the module's cost (72 s of 137).
record Ctx {E : LTy} (e : MV E) (B : LTy) : Set where
  constructor ctx
  field
    {Es S} : List LTy
    {Tr U} : Sh
    es : Slots (E ∷ Es)
    eq : see es ≡ e
    os : Stk S
    k  : Codeᴵ (E ∷ Es ∣ B ∷ S) U
    ρ  : Ret U Tr

-- a simulation from a context, of a code over the code after
SimK : ∀ {E A B} {e : MV E} → Outcome B → (∀ {Es S U} → Codeᴵ (E ∷ Es ∣ B ∷ S) U → Codeᴵ (E ∷ Es ∣ A ∷ S) U)
     → MV A → ℕ → Trace → ℕ → Ctx e B → Set
SimK o c v n t j κ = SimRI o (c (Ctx.k κ)) (Ctx.ρ κ) (Ctx.es κ ∥ v ∷ˢ Ctx.os κ) n t (Ctx.k κ) (Ctx.ρ κ) (Ctx.es κ) (Ctx.os κ) j

mutual
  simMI : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x o n t}
        → (rm : RunMap ds F alg e G x n o t) → PlainM rm
        → (κ : Ctx e (LF∙ G A)) → SimK o (travᴵ ds F alg G) x n t (roundsM rm) κ
  simMI (m-id r) p (ctx es eq os k ρ) = simI r p (ctx es eq os k ρ)
  simMI m-one p (ctx es eq os k ρ) = doneO
  simMI m-b p (ctx es eq os k ρ) = doneO
  simMI m-μ p (ctx es eq os k ρ) = doneO
  simMI (m-inl (fm-gives r)) p (ctx es eq os k ρ) = pre i-case₁ (after (simMI r p (ctx es eq os _ ρ)) (i-prim r-inl))
  simMI (m-inl (fm-stop r)) p (ctx es eq os k ρ) = preH _ i-case₁ (simMI r p (ctx es eq os _ ρ))
  simMI (m-inr (fm-gives r)) p (ctx es eq os k ρ) = pre i-case₂ (after (simMI r p (ctx es eq os _ ρ)) (i-prim r-inr))
  simMI (m-inr (fm-stop r)) p (ctx es eq os k ρ) = preH _ i-case₂ (simMI r p (ctx es eq os _ ρ))
  simMI (m-pair {x′ = x′} r (go-on {u = y} (fm-gives r′))) (p , p′) (ctx es eq os k ρ) =
    pre i-unpair (then (simMI r p (ctx es eq (x′ ∷ˢ os) _ ρ))
                       (pre i-swap (after (after (simMI r′ p′ (ctx es eq (y ∷ˢ os) _ ρ)) i-swap) i-pair)))
  simMI (m-pair {x′ = x′} r (go-on {u = y} (fm-stop r′))) (p , p′) (ctx es eq os k ρ) =
    preH _ i-unpair (thenH _ (simMI r p (ctx es eq (x′ ∷ˢ os) _ ρ)) (preH _ i-swap (simMI r′ p′ (ctx es eq (y ∷ˢ os) _ ρ))))
  simMI (m-pair {x′ = x′} r stopped) p (ctx es eq os k ρ) = P-[]H _ (preH _ i-unpair (simMI r p (ctx es eq (x′ ∷ˢ os) _ ρ)))

  simI : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v o n t}
       → (r : Run ds f e v n o t) → Plain r
       → (κ : Ctx e B) → SimK o (compᴵ ds f) v n t (rounds r) κ
  simI r-id fr (ctx es eq os k ρ) = doneO
  simI (r-∘ rg (go-on {o = o} rf)) (pg , pf) (ctx es eq os k ρ) = thenR o (simI rg pg (ctx es eq os _ ρ)) (simI rf pf (ctx es eq os k ρ))
  simI (r-∘ rg stopped) pg (ctx es eq os k ρ) = P-[]H _ (simI rg pg (ctx es eq os _ ρ))
  simI (r-⊗ {c = c} rf (go-on {u = a′} (fm-gives rg))) (pf , pg) (ctx es eq os k ρ) =
    pre i-unpair (then (simI rf pf (ctx es eq (c ∷ˢ os) _ ρ))
                       (pre i-swap (after (after (simI rg pg (ctx es eq (a′ ∷ˢ os) _ ρ)) i-swap) i-pair)))
  simI (r-⊗ {c = c} rf (go-on {u = a′} (fm-stop rg))) (pf , pg) (ctx es eq os k ρ) =
    preH _ i-unpair (thenH _ (simI rf pf (ctx es eq (c ∷ˢ os) _ ρ)) (preH _ i-swap (simI rg pg (ctx es eq (a′ ∷ˢ os) _ ρ))))
  simI (r-⊗ {c = c} rf stopped) pf (ctx es eq os k ρ) = P-[]H _ (preH _ i-unpair (simI rf pf (ctx es eq (c ∷ˢ os) _ ρ)))
  simI r-ρ fr (ctx es eq os k ρ) = leaf (i-prim r-ρ) []
  simI r-ρ⁻ fr (ctx es eq os k ρ) = leaf (i-prim r-ρ⁻) []
  simI r-λ fr (ctx es eq os k ρ) = leaf (i-prim r-λ) []
  simI r-λ⁻ fr (ctx es eq os k ρ) = leaf (i-prim r-λ⁻) []
  simI r-α fr (ctx es eq os k ρ) = leaf (i-prim r-α) []
  simI r-α⁻ fr (ctx es eq os k ρ) = leaf (i-prim r-α⁻) []
  simI r-swap fr (ctx es eq os k ρ) = leaf (i-prim r-swap) []
  -- ★ `dup`: the operand lent (a lend's slot owns it), the copy block called
  -- on it, taken back beside its copy
  simI (r-dup {v = v} {n}) fr (ctx es eq os k ρ) =
    pre i-unit (pre i-swap (pre i-pair (pre i-elend (pre (i-esnd refl)
      (after (after (copyS v refl os n) i-epop) i-eunlend)))))
  -- ★ `drop`: the free block
  simI (r-drop {v = v} {n}) fr (ctx es eq os k ρ) = freeS v os n
  simI r-inl fr (ctx es eq os k ρ) = leaf (i-prim r-inl) []
  simI r-inr fr (ctx es eq os k ρ) = leaf (i-prim r-inr) []
  simI (r-case₁ {o = o} r) p (ctx es eq os k ρ) = preR o i-case₁ (simI r p (ctx es eq os k ρ))
  simI (r-case₂ {o = o} r) p (ctx es eq os k ρ) = preR o i-case₂ (simI r p (ctx es eq os k ρ))
  simI r-In fr (ctx es eq os k ρ) = leaf (i-prim r-In) (k-alloc ∷ [])
  simI r-Outμ fr (ctx es eq os k ρ) = leaf (i-prim r-Outμ) (k-free ∷ [])
  simI r-clo fr (ctx es eq os k ρ) = leaf (i-prim r-clo) []
  -- ★ a label's body: a call into its block
  simI (r-app {o = o} q r) p (ctx es eq os k ρ) =
    sim-code (cong (λ κ → untag ⨾ call κ ⨾ k) (sym (look-key1 q)))
      (preR o i-untag (calledR o (around o i-elift (simI r p (ctx (vw mone []ᵉ) refl []ˢ _ (frm {t = nothing} k es os ρ))))))
  -- ★ a fold: a call; the block frees the node, folds each child (calls),
  -- runs the algebra
  simI (r-cata rm (go-on {o = o} ra)) (pm , pa) (ctx es eq os k ρ) =
    calledRω o (thenR o (leaf (i-prim r-Outμ) (k-free ∷ []))
                        (thenR o (simMI rm pm (ctx (vw (see es) []ᵉ) eq []ˢ _ (frm {t = just _} k es os ρ)))
                                 (simI ra pa (ctx (vw (see es) []ᵉ) eq []ˢ end (frm {t = just _} k es os ρ)))))
  simI (r-cata {e = e} rm stopped) pm (ctx es eq os k ρ) =
    calledH _ i-call (thenH _ (leaf (i-prim r-Outμ) (k-free ∷ [])) (P-[]H _ (simMI rm pm (ctx (vw (see es) []ᵉ) eq []ˢ _ (frm {t = just _} k es os ρ)))))
  simI (r-cata-reuse rm th) () (ctx es eq os k ρ)
  simI (r-lend {x = x} (fm-gives r)) fr (ctx es refl os k ρ) =
    pre i-elend (after (simI r fr (ctx (ln (see es) x es) refl os _ ρ)) i-eunlend)
  simI (r-lend {x = x} (fm-stop r)) fr (ctx es refl os k ρ) = preH _ i-elend (simI r fr (ctx (ln (see es) x es) refl os _ ρ))
  simI (r-lift {o = o} r) fr (ctx es eq os k ρ) = around o i-elift (simI r fr (ctx (vw mone es) refl os _ ρ))
  simI (r-fst {e₁ = e₁} {o = o} r) fr (ctx es eq os k ρ) = around o (i-efst eq) (simI r fr (ctx (vw e₁ es) refl os _ ρ))
  simI (r-snd {e₂ = e₂} {o = o} r) fr (ctx es eq os k ρ) = around o (i-esnd eq) (simI r fr (ctx (vw e₂ es) refl os _ ρ))
  simI (r-caseE₁ {e = e} {o = o} r) fr (ctx es eq os k ρ) = around o (i-ecase₁ eq) (simI r fr (ctx (vw e es) refl os _ ρ))
  simI (r-caseE₂ {e = e} {o = o} r) fr (ctx es eq os k ρ) = around o (i-ecase₂ eq) (simI r fr (ctx (vw e es) refl os _ ρ))
  simI (r-out {B = B} {i = i} {v} {a} {o = o} {n} r) fr (ctx es eq os k ρ) = outR o (simI r fr (ctx (vw v es) refl os _ ρ))
    where
      outR : (o : Outcome B) → ∀ {c₁ t j} → SimRI o c₁ ρ (vw v es ∥ a ∷ˢ os) n t (epop ⨾ k) ρ (vw v es) os j
           → SimRI o (eout ⨾ c₁) ρ (es ∥ a ∷ˢ os) n (peek i ∷ t) k ρ es os j
      outR (gives _ _) r′ = then (leaf (i-eout eq) (k-peek ∷ [])) (after r′ i-epop)
      outR (stop _)    r′ = thenH _ (leaf (i-eout eq) (k-peek ∷ [])) r′
  -- ★ a lent copy: the copy block on the view
  simI (r-copy {n = n}) fr (ctx es refl os k ρ) = copyS (see es) refl os n
  simI (r-bapp {x = x} {o = o} q r) fr (ctx es eq os k ρ) =
    sim-code (cong (λ κ → eapp ⨾ call κ ⨾ epop ⨾ k) (sym (look-keyω q)))
      (around o (i-eapp eq) (calledRω o (simI r fr (ctx (vw x []ᵉ) refl []ˢ end (frm {t = just _} (epop ⨾ k) (vw x es) os ρ)))))
  simI r-lam fr (ctx es eq os k ρ) = leaf (i-prim r-lam) (k-alloc ∷ [])
  simI r-lamω fr (ctx es eq os k ρ) = leaf (i-prim r-lamω) (k-alloc ∷ [])
  simI r-unf fr (ctx es eq os k ρ) = leaf (i-prim r-unf) (k-alloc ∷ [])
  -- ★ through a cell's code word: its trampoline (D434), which does the
  -- cell's part and calls the block
  simI (r-nout {F = F} {S} {o = o} r) p (ctx es eq os k ρ) =
    calledR′ o i-iobs (thenR o (leaf i-nopen (k-free ∷ []))
      (calledR o (around o i-elift
        (sim-code (cong (λ u → compᴵ ε u (epop ⨾ end)) (rt-obsT F S))
          (simTF r (obsT-tf F S) p (ctx (vw mone []ᵉ) refl []ˢ _ (frm {t = nothing} end []ᵉ []ˢ (frm {t = nothing} k es os ρ))))))))
  simI (r-ev {o = o} r) p (ctx es eq os k ρ) =
    calledR′ o i-icall (thenR o (leaf i-open1 (k-free ∷ []))
      (calledR o (around o i-elift (simI r p (ctx (vw mone []ᵉ) refl []ˢ _ (frm {t = nothing} end []ᵉ []ˢ (frm {t = nothing} k es os ρ)))))))
  simI (r-bev {B = B} {ds′ = ds′} {b = b} {γ = γ} {i = i} {x} {a} {o} {n} r) p (ctx es eq os k ρ) =
    calledR′ o (i-icallω eq) (bevR o (calledRω o (simI r p (ctx (vw x []ᵉ) refl []ˢ end (frm {t = just _} (epop ⨾ end) (vw x E′) []ˢ R′)))))
    where
      E′ = vw (see es) []ᵉ
      R′ = frm {t = just _} k es os ρ
      bevR : (o : Outcome B) → ∀ {t j} → SimRI o (call (kbodyω ds′ b γ) ⨾ epop ⨾ end) R′ (vw x E′ ∥ a ∷ˢ []ˢ) n t (epop ⨾ end) R′ (vw x E′) []ˢ j
           → SimRI o (openω ⨾ call (kbodyω ds′ b γ) ⨾ epop ⨾ end) R′ (E′ ∥ a ∷ˢ []ˢ) n (peek i ∷ t) end R′ E′ []ˢ j
      bevR (gives _ _) r′ = then (leaf (i-openω eq) (k-peek ∷ [])) (after r′ i-epop)
      bevR (stop y)    r′ = thenH y (leaf (i-openω eq) (k-peek ∷ [])) r′
  simI r-const fr (ctx es eq os k ρ) = leaf (i-prim r-const) []
  simI (r-op p) fr (ctx es eq os k ρ) = leaf (i-prim (r-op p)) (op-NoT p)
  simI (r-opend {w = halted} p) fr (ctx es eq os k ρ) =
    paused halted ρ _ _ [] _ _ (oneI (i-opend p)) (w-self _) (subst (_≼ _) (sym (erase-NoT _ (op-NoT p))) (≼-refl _)) (op-NoT p) tt z≤n
    , (refl , sym (erase-NoT _ (op-NoT p)))
  simI (r-opend {w = exhausted} p) () (ctx es eq os k ρ)
  -- ★ the loop: its round with the branch pushed (no frame), then the branch
  simI (r-iter r (go-on done)) fr (ctx es eq os k ρ) =
    O-[] (preL (after (after (simI r fr (ctx es eq os end _)) i-reti) i-case₁))
  simI (r-iter r (go-on (again {o = o} rn))) (p , pn) (ctx es eq os k ρ) =
    preLR o (thenR o (simI r p (ctx es eq os end _)) (preR o i-reti (preR o i-case₂ (simI rn pn (ctx es eq os k ρ)))))
  simI (r-iter r stopped) fr (ctx es eq os k ρ) = P-[]H _ (preLH _ (simI r fr (ctx es eq os end _)))
  simI r-exh fr (ctx es eq os k ρ) = (paused _ ρ _ _ [] [] [] done w-[] []≼ [] tt z≤n , refl)
  simI (r-cut r q) () (ctx es eq os k ρ)
  simI (r-tmp {o = o} r w p) fr (ctx es eq os k ρ) = tmpR o w (simI r fr (ctx es eq os k ρ))

  -- ★ a TABLE-FREE term's run, on its code at the empty table (D440): as
  -- `simI`, by the run (the observation's block is `kobs ε`)
  simTF : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v o n t}
        → (r : Run ds f e v n o t) (w : TF f) → Plain r
        → (κ : Ctx e B) → SimK o (compᴵ ε (rt w)) v n t (rounds r) κ
  simTF (r-tmp {o = o} r wv tp) w fr (ctx es eq os k ρ) = tmpR o wv (simTF r w fr (ctx es eq os k ρ))
  simTF r-exh w fr (ctx es eq os k ρ) = (paused _ ρ _ _ [] [] [] done w-[] []≼ [] tt z≤n , refl)
  simTF (r-cut r q) w () (ctx es eq os k ρ)
  simTF r-id tf-id fr (ctx es eq os k ρ) = doneO
  simTF (r-∘ rg (go-on {o = o} rf)) (tf-∘ wf wg) (pg , pf) (ctx es eq os k ρ) =
    thenR o (simTF rg wg pg (ctx es eq os _ ρ)) (simTF rf wf pf (ctx es eq os k ρ))
  simTF (r-∘ rg stopped) (tf-∘ wf wg) pg (ctx es eq os k ρ) = P-[]H _ (simTF rg wg pg (ctx es eq os _ ρ))
  simTF (r-⊗ {c = c} rf (go-on {u = a′} (fm-gives rg))) (tf-⊗ wf wg) (pf , pg) (ctx es eq os k ρ) =
    pre i-unpair (then (simTF rf wf pf (ctx es eq (c ∷ˢ os) _ ρ))
                       (pre i-swap (after (after (simTF rg wg pg (ctx es eq (a′ ∷ˢ os) _ ρ)) i-swap) i-pair)))
  simTF (r-⊗ {c = c} rf (go-on {u = a′} (fm-stop rg))) (tf-⊗ wf wg) (pf , pg) (ctx es eq os k ρ) =
    preH _ i-unpair (thenH _ (simTF rf wf pf (ctx es eq (c ∷ˢ os) _ ρ)) (preH _ i-swap (simTF rg wg pg (ctx es eq (a′ ∷ˢ os) _ ρ))))
  simTF (r-⊗ {c = c} rf stopped) (tf-⊗ wf wg) pf (ctx es eq os k ρ) = P-[]H _ (preH _ i-unpair (simTF rf wf pf (ctx es eq (c ∷ˢ os) _ ρ)))
  simTF r-λ tf-lul fr (ctx es eq os k ρ) = leaf (i-prim r-λ) []
  simTF r-λ⁻ tf-lul⁻ fr (ctx es eq os k ρ) = leaf (i-prim r-λ⁻) []
  simTF (r-drop {v = v} {n}) tf-drop fr (ctx es eq os k ρ) = freeS v os n
  simTF r-inl tf-inl fr (ctx es eq os k ρ) = leaf (i-prim r-inl) []
  simTF r-inr tf-inr fr (ctx es eq os k ρ) = leaf (i-prim r-inr) []
  simTF (r-case₁ {o = o} r) (tf-case wf wg) p (ctx es eq os k ρ) = preR o i-case₁ (simTF r wf p (ctx es eq os k ρ))
  simTF (r-case₂ {o = o} r) (tf-case wf wg) p (ctx es eq os k ρ) = preR o i-case₂ (simTF r wg p (ctx es eq os k ρ))
  simTF (r-lend {x = x} (fm-gives r)) (tf-lend wb) fr (ctx es refl os k ρ) =
    pre i-elend (after (simTF r wb fr (ctx (ln (see es) x es) refl os _ ρ)) i-eunlend)
  simTF (r-lend {x = x} (fm-stop r)) (tf-lend wb) fr (ctx es refl os k ρ) = preH _ i-elend (simTF r wb fr (ctx (ln (see es) x es) refl os _ ρ))
  simTF (r-snd {e₂ = e₂} {o = o} r) (tf-bsnd wf) fr (ctx es eq os k ρ) = around o (i-esnd eq) (simTF r wf fr (ctx (vw e₂ es) refl os _ ρ))
  simTF (r-copy {n = n}) tf-bcopy fr (ctx es refl os k ρ) = copyS (see es) refl os n
  simTF r-unf tf-unf fr (ctx es eq os k ρ) = leaf (i-prim r-unf) (k-alloc ∷ [])
  simTF (r-bev {B = B} {ds′ = ds′} {b = b} {γ = γ} {i = i} {x} {a} {o} {n} r) tf-bev p (ctx es eq os k ρ) =
    calledR′ o (i-icallω eq) (bevR o (calledRω o (simI r p (ctx (vw x []ᵉ) refl []ˢ end (frm {t = just _} (epop ⨾ end) (vw x E′) []ˢ R′)))))
    where
      E′ = vw (see es) []ᵉ
      R′ = frm {t = just _} k es os ρ
      bevR : (o : Outcome B) → ∀ {t j} → SimRI o (call (kbodyω ds′ b γ) ⨾ epop ⨾ end) R′ (vw x E′ ∥ a ∷ˢ []ˢ) n t (epop ⨾ end) R′ (vw x E′) []ˢ j
           → SimRI o (openω ⨾ call (kbodyω ds′ b γ) ⨾ epop ⨾ end) R′ (E′ ∥ a ∷ˢ []ˢ) n (peek i ∷ t) end R′ E′ []ˢ j
      bevR (gives _ _) r′ = then (leaf (i-openω eq) (k-peek ∷ [])) (after r′ i-epop)
      bevR (stop y)    r′ = thenH y (leaf (i-openω eq) (k-peek ∷ [])) r′

------------------------------------------------------------------------
-- 7. ★ ON THE IMAGE (A16's §7).
------------------------------------------------------------------------

private
  pre₀ : ∀ {n} → Pre (λ _ → 0) n mone (λ _ → 0)
  pre₀ = record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n }

  -- the simulation from a closed program's start
  ctx₀ : Ctx mone One
  ctx₀ = ctx (vw mone []ᵉ) refl []ˢ end []ʳ

-- the world sees the same of a trace and of its erasure
ios-erase : ∀ t → ios (erase t) ≡ ios t
ios-erase []             = refl
ios-erase (alloc _ ∷ t)  = ios-erase t
ios-erase (free _ ∷ t)   = ios-erase t
ios-erase (peek _ ∷ t)   = ios-erase t
ios-erase (io s x y ∷ t) = cong (io-call s x y ∷_) (ios-erase t)
ios-erase (stp s x ∷ t)  = cong (io-halt s x ∷_) (ios-erase t)
ios-erase (tmp _ ∷ t)    = ios-erase t

-- ★ a finished run of a closed program: the image on its compiled code is
-- legal on the cell heap, leaves it empty, closes every frame it opened, and
-- shows the world what the run does (D446)
image-noleak : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {n′ t}
             → (run : Run ds f mone mone 1 (gives mone n′) t) → Plain run
             → Σ Trace λ mt → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 1 mt end []ʳ start n′
               × OK mt (λ _ → 0) × (∀ i → play mt (λ _ → 0) i ≡ 0) × TBal mt × ios mt ≡ ios t
image-noleak {ds = ds} {f = f} {n′ = n′} {t = t} run fr = at (simI run fr ctx₀)
  where
    Goal : Set
    Goal = Σ Trace λ mt → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 1 mt end []ʳ start n′
             × OK mt (λ _ → 0) × (∀ i → play mt (λ _ → 0) i ≡ 0) × TBal mt × ios mt ≡ ios t
    at : SimK (gives mone n′) (compᴵ ds f) mone 1 t (rounds run) ctx₀ → Goal
    at (out ts mt st w b _) =
      ( mt , st
      , OK-weave w (λ _ → 0) (fst (noleak (plain run)))
      , (λ i → trans (cong (λ h → h i) (play-weave w (λ _ → 0))) (snd (noleak (plain run)) i))
      , weave-post (gives mone 0) w (NoT-Bal (erase t) (erase-clean t)) b
      , trans (ios-weave w) (ios-erase t) )

-- ★ A HALTING run of a closed program (D446): the image reaches `halted`, showing the world what the
-- run does
image-halts : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {t}
            → (run : Run ds f mone mone 1 (stop halted) t) → Plain run
            → Σ Trace λ mt → Σ Sh λ sh → Σ Sh λ U → Σ (Ret U (One ∷ [] ∣ One ∷ [])) λ r′ → Σ (Cfg sh) λ m′ → Σ ℕ λ n′
                → StepsI (compᴵ ds f end) []ʳ start 1 mt (halted {sh} {U}) r′ m′ n′ × ios mt ≡ ios t
image-halts {ds = ds} {f = f} {t = t} run fr = at (simI run fr ctx₀)
  where
    Goal : Set
    Goal = Σ Trace λ mt → Σ Sh λ sh → Σ Sh λ U → Σ (Ret U (One ∷ [] ∣ One ∷ [])) λ r′ → Σ (Cfg sh) λ m′ → Σ ℕ λ n′
             → StepsI (compᴵ ds f end) []ʳ start 1 mt (halted {sh} {U}) r′ m′ n′ × ios mt ≡ ios t
    at : Σ (PausedI (compᴵ ds f end) []ʳ start 1 t (rounds run)) (HaltIf halted) → Goal
    at (paused {sh′} {U′} c′ r′ m′ n′ ts mt t₀ st w p cl l _ , (hc , ht)) =
      mt , sh′ , U′ , r′ , m′ , n′ , subst (λ c → StepsI (compᴵ ds f end) []ʳ start 1 mt c r′ m′ n′) hc st
         , trans (ios-weave w) (trans (cong ios ht) (ios-erase t))

-- ★ ANY stopped run of a closed program from nothing (a server cut after its
-- last round, a halt): the image runs at least as far, and what it did up to
-- the run's last event is legal on the cell heap, with legal frames
image-legal : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {y t}
            → (run : Run ds f mone mone 1 (stop y) t) → Plain run
            → Σ Trace λ mt′ → Σ (List TEv) λ ts′ → Weave tmp (erase t) ts′ mt′
               × OK mt′ (λ _ → 0) × TLeg mt′
               × Σ Trace λ mt → mt′ ≼ mt × Σ Sh λ sh → Σ Sh λ U → Σ (Codeᴵ sh U) λ c′ → Σ (Ret U (One ∷ [] ∣ One ∷ [])) λ r′
                 → Σ (Cfg sh) λ m′ → Σ ℕ λ n′ → StepsI (compᴵ ds f end) []ʳ start 1 mt c′ r′ m′ n′
image-legal {ds = ds} {f = f} {y = y} {t = t} run fr = at (simI run fr ctx₀)
  where
    Goal : Set
    Goal = Σ Trace λ mt′ → Σ (List TEv) λ ts′ → Weave tmp (erase t) ts′ mt′
             × OK mt′ (λ _ → 0) × TLeg mt′
             × Σ Trace λ mt → mt′ ≼ mt × Σ Sh λ sh → Σ Sh λ U → Σ (Codeᴵ sh U) λ c′ → Σ (Ret U (One ∷ [] ∣ One ∷ [])) λ r′
               → Σ (Cfg sh) λ m′ → Σ ℕ λ n′ → StepsI (compᴵ ds f end) []ʳ start 1 mt c′ r′ m′ n′
    at : Σ (PausedI (compᴵ ds f end) []ʳ start 1 t (rounds run)) (HaltIf y) → Goal
    at (paused {sh′} {U′} c′ r′ m′ n′ ts mt t₀ st w p cl l _ , _) =
      let (ts′ , mt′ , w′ , q) = weave-pre w p
      in ( mt′ , ts′ , w′
         , OK-weave w′ (λ _ → 0) (fst (exchange (plain run) pre₀ lent₀))
         , TOK-≼ q (weave-post (stop {One} exhausted) w (fst (NoT-Bal t₀ cl)) l)
         , mt , q , sh′ , U′ , c′ , r′ , m′ , n′ , st )

-- ★ A RUN THE BUDGET CUT (D447): the image pauses, having shown the world exactly what the run did, and
-- having entered a loop once for every round the run started
image-cut : ∀ {Γ} {ds : Defs Γ} {f : LTm Γ One One} {t}
          → (run : Run ds f mone mone 1 (stop exhausted) t) → Plain run
          → Σ Trace λ mt → Σ Sh λ sh → Σ Sh λ U → Σ (Codeᴵ sh U) λ c′ → Σ (Ret U (One ∷ [] ∣ One ∷ [])) λ r′
              → Σ (Cfg sh) λ m′ → Σ ℕ λ n′ → Σ (StepsI (compᴵ ds f end) []ʳ start 1 mt c′ r′ m′ n′) λ st
              → (ios mt ≡ ios t) × (rounds run ≤ loops st)
image-cut {ds = ds} {f = f} {t = t} run fr = at (simI run fr ctx₀)
  where
    Goal : Set
    Goal = Σ Trace λ mt → Σ Sh λ sh → Σ Sh λ U → Σ (Codeᴵ sh U) λ c′ → Σ (Ret U (One ∷ [] ∣ One ∷ [])) λ r′
             → Σ (Cfg sh) λ m′ → Σ ℕ λ n′ → Σ (StepsI (compᴵ ds f end) []ʳ start 1 mt c′ r′ m′ n′) λ st
             → (ios mt ≡ ios t) × (rounds run ≤ loops st)
    at : Σ (PausedI (compᴵ ds f end) []ʳ start 1 t (rounds run)) (HaltIf exhausted) → Goal
    at (paused {sh′} {U′} c′ r′ m′ n′ ts mt t₀ st w p cl l lp , ht) =
      mt , sh′ , U′ , c′ , r′ , m′ , n′ , st , trans (ios-weave w) (trans (cong ios ht) (ios-erase t)) , lp
