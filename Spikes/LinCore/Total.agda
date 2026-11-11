-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- LinCore.Total — plan 0.146 A14: EVERY PROGRAM HAS A RUN.
--
-- The memory theorems are about every run that exists; a term with no run
-- would satisfy them vacuously. Here an evaluator BUILDS a run of every
-- term, from every lent value, input and counter, for every world: the
-- world is any machine answering SigOps (a state, and an answer function).
--
-- No relation on the type is needed (★ D405): applying a closure runs a body
-- of a strictly shorter prefix of the table, so the table's runners are built
-- in order, as its meaning is (`⟦_⟧D`); a fold recurses on the value; the
-- term shrinks everywhere else. Only the loop may run forever: it is given
-- FUEL, a number of rounds, and a run that uses it up ends `exhausted` after
-- the rounds it ran (D374: a server's run is cut a round at a time).
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import LinCore.Flat using (FTy)

module LinCore.Total
  (Base : Set) (⟦_⟧b : Base → Set)
  (Sig : Set) (sdom scod : Sig → FTy Base)
  (bw : Base → ℕ)
  where

open import LinCore.NbEPLinCore Base ⟦_⟧b Sig sdom scod
open import LinCore.Events Base ⟦_⟧b Sig sdom scod bw

-- ★ a WORLD: any machine that answers SigOps (its state may be the whole
-- history, so this is every strategy). It may give NO answer — it must, for
-- an op whose answer type is empty (`void`: an exit called by `lop`), and
-- may, for any other — and then the run is cut at that call (D408).
record World : Set₁ where
  field
    WSt : Set
    ans : WSt → (s : Sig) → ⟦ sdom s ⟧f → Maybe (⟦ scod s ⟧f × WSt)

module _ (W : World) where
  open World W

  -- a run, found: its outcome, its events, the derivation, the world after it
  record Ran {Γ} (ds : Defs Γ) {E A B} (f : Tm Γ E A B) (e : MV E) (v : MV A) (n : ℕ) : Set where
    constructor ran
    field
      out   : Outcome B
      trace : Trace
      run   : Run ds f e v n out trace
      after : WSt

  record RanM {Γ} (ds : Defs Γ) {E A} (F : LF) (alg : Tm Γ E (LF∙ F A) A) (e : MV E)
              (G : LF) (x : MV (LF∙ G (μt F))) (n : ℕ) : Set where
    constructor ranM
    field
      out   : Outcome (LF∙ G A)
      trace : Trace
      run   : RunMap ds F alg e G x n out trace
      after : WSt

  -- what a label's body does, for any fuel, environment, argument, counter, world
  Runner : ∀ {Δ σ} → Defs Δ → Body Δ σ → Set
  Runner ds (b1 b) = ∀ (k : ℕ) x a n → WSt → Ran ds b mone (mpair x a) n
  Runner ds (bω b) = ∀ (k : ℕ) x a n → WSt → Ran ds b x a n

  -- the runners of a table, in order (as `Env`)
  data REnv : ∀ {Γ} → Defs Γ → Set where
    ε   : REnv ε
    _▸_ : ∀ {Γ σ} {ds : Defs Γ} {b : Body Γ σ} → REnv ds → Runner ds b → REnv (ds ▸ b)

  -- a label's body, where it is, and its runner
  record Found {Γ l σ} (ds : Defs Γ) (p : Γ ∋[ l ] σ) : Set where
    constructor found
    field
      {Δ}  : Cx
      {ds′} : Defs Δ
      {b}  : Body Δ σ
      look : Look ds p ds′ b
      go   : Runner ds′ b

  find : ∀ {Γ l σ} {ds : Defs Γ} → REnv ds → (p : Γ ∋[ l ] σ) → Found ds p
  find (ρ ▸ r) here      = found lk-here r
  find (ρ ▸ r) (there p) with find ρ p
  ... | found q r′ = found (lk-there q) r′

  ------------------------------------------------------------------------
  -- THE EVALUATOR, over a table and its runners. It terminates by: the
  -- fuel (only `liter` spends it), then the term, then the value (a fold).
  ------------------------------------------------------------------------

  module Eval {Γ} (ds : Defs Γ) (ρ : REnv ds) where
    mutual
      go : ∀ {E A B} (k : ℕ) (f : Tm Γ E A B) (e : MV E) (v : MV A) (n : ℕ) → WSt → Ran ds f e v n
      go k lid e v n σ = ran _ _ r-id σ
      go k (f ∘l g) e v n σ with go k g e v n σ
      ... | ran (gives u n₁) t₁ rg σ₁ with go k f e u n₁ σ₁
      ...   | ran o t₂ rf σ₂ = ran o (t₁ ++ t₂) (r-∘ rg (go-on rf)) σ₂
      go k (f ∘l g) e v n σ | ran (stop y) t rg σ₁ = ran (stop y) (t ++ []) (r-∘ rg stopped) σ₁
      go k (f ⊗l g) e (mpair a c) n σ with go k f e a n σ
      ... | ran (stop y) t rf σ₁ = ran (stop y) (t ++ []) (r-⊗ rf stopped) σ₁
      ... | ran (gives a′ n₁) t₁ rf σ₁ with go k g e c n₁ σ₁
      ...   | ran (gives c′ n₂) t₂ rg σ₂ = ran _ (t₁ ++ t₂) (r-⊗ rf (go-on (fm-gives rg))) σ₂
      ...   | ran (stop y) t₂ rg σ₂ = ran (stop y) (t₁ ++ t₂) (r-⊗ rf (go-on (fm-stop rg))) σ₂
      go k ρl e (mpair a mone) n σ = ran _ _ r-ρ σ
      go k ρl⁻ e a n σ = ran _ _ r-ρ⁻ σ
      go k lul e (mpair mone a) n σ = ran _ _ r-λ σ
      go k lul⁻ e a n σ = ran _ _ r-λ⁻ σ
      go k lassoc e (mpair (mpair a b) c) n σ = ran _ _ r-α σ
      go k lassoc⁻ e (mpair a (mpair b c)) n σ = ran _ _ r-α⁻ σ
      go k lswap e (mpair a b) n σ = ran _ _ r-swap σ
      go k dup e v n σ = ran _ _ r-dup σ
      go k drop e v n σ = ran _ _ r-drop σ
      go k linl e a n σ = ran _ _ r-inl σ
      go k linr e b n σ = ran _ _ r-inr σ
      go k (lcase f g) e (minl a) n σ with go k f e a n σ
      ... | ran o t r σ₁ = ran o t (r-case₁ r) σ₁
      go k (lcase f g) e (minr b) n σ with go k g e b n σ
      ... | ran o t r σ₁ = ran o t (r-case₂ r) σ₁
      go k lzero e () n σ
      go k lIn e v n σ = ran _ _ r-In σ
      go k lOutμ e (mmu i v) n σ = ran _ _ r-Outμ σ
      go k (lcata F alg) e x n σ = cata k F alg e x n σ
      go k (lclo F p) e x n σ = ran _ _ r-clo σ
      go k (lapp p) e (mpair (mct x) a) n σ with find ρ p
      ... | found {b = b1 b} q r with r k x a n σ
      ...   | ran o t rb σ₁ = ran o t (r-app q rb) σ₁
      go k (lend b) e (mpair x a) n σ with go k b (mpair e x) a n σ
      ... | ran (gives w n′) t r σ₁ = ran _ t (r-lend (fm-gives r)) σ₁
      ... | ran (stop y) t r σ₁ = ran (stop y) t (r-lend (fm-stop r)) σ₁
      go k (blift f) e a n σ with go k f mone a n σ
      ... | ran o t r σ₁ = ran o t (r-lift r) σ₁
      go k (bfst f) (mpair e₁ e₂) a n σ with go k f e₁ a n σ
      ... | ran o t r σ₁ = ran o t (r-fst r) σ₁
      go k (bsnd f) (mpair e₁ e₂) a n σ with go k f e₂ a n σ
      ... | ran o t r σ₁ = ran o t (r-snd r) σ₁
      go k (bcaseE f g) (minl e) a n σ with go k f e a n σ
      ... | ran o t r σ₁ = ran o t (r-caseE₁ r) σ₁
      go k (bcaseE f g) (minr e) a n σ with go k g e a n σ
      ... | ran o t r σ₁ = ran o t (r-caseE₂ r) σ₁
      go k (bout f) (mmu i v) a n σ with go k f v a n σ
      ... | ran o t r σ₁ = ran o (peek i ∷ t) (r-out r) σ₁
      go k bcopy e mone n σ = ran _ _ r-copy σ
      go k (bapp p) (mct x) a n σ with find ρ p
      ... | found {b = bω b} q r with r k x a n σ
      ...   | ran o t rb σ₁ = ran o t (r-bapp q rb) σ₁
      go k (lop s) e x n σ with ans σ s (toF (sdom s) (er x))
      ... | just (y , σ₁) = ran _ _ (r-op {y = y}) σ₁
      ... | nothing       = ran _ _ r-exh σ
      go k (lhalt s) e x n σ = ran _ _ r-halt σ
      -- ★ the loop: a round, then (if it continues) the loop on one less fuel
      go zero (liter f) e a n σ = ran _ _ r-exh σ
      go (suc k) (liter f) e a n σ with go (suc k) f e a n σ
      ... | ran (gives (minl b) n′) t r σ₁ = ran _ (t ++ []) (r-iter r (go-on done)) σ₁
      ... | ran (stop y) t r σ₁ = ran (stop y) (t ++ []) (r-iter r stopped) σ₁
      ... | ran (gives (minr a′) n₁) t₁ r σ₁ with go k (liter f) e a′ n₁ σ₁
      ...   | ran o t₂ rn σ₂ = ran o (t₁ ++ t₂) (r-iter r (go-on (again rn))) σ₂

      -- the fold: free the node, fold its positions, run the algebra
      cata : ∀ {E A} (k : ℕ) F (alg : Tm Γ E (LF∙ F A) A) (e : MV E) (x : MV (μt F)) (n : ℕ) → WSt
           → Ran ds (lcata F alg) e x n
      cata k F alg e (mmu i v) n σ with fold k F alg e F v n σ
      ... | ranM (stop y) t rm σ₁ = ran (stop y) (free i ∷ (t ++ [])) (r-cata rm stopped) σ₁
      ... | ranM (gives u n₁) t₁ rm σ₁ with go k alg e u n₁ σ₁
      ...   | ran o t₂ ra σ₂ = ran o (free i ∷ (t₁ ++ t₂)) (r-cata rm (go-on ra)) σ₂

      fold : ∀ {E A} (k : ℕ) F (alg : Tm Γ E (LF∙ F A) A) (e : MV E) G (x : MV (LF∙ G (μt F))) (n : ℕ) → WSt
           → RanM ds F alg e G x n
      fold k F alg e Idf x n σ with cata k F alg e x n σ
      ... | ran o t r σ₁ = ranM o t (m-id r) σ₁
      fold k F alg e Kone x n σ = ranM _ _ m-one σ
      fold k F alg e Kzero () n σ
      fold k F alg e (Kb b) x n σ = ranM _ _ m-b σ
      fold k F alg e (Kμ G) x n σ = ranM _ _ m-μ σ
      fold k F alg e (G ⊕f H) (minl x) n σ with fold k F alg e G x n σ
      ... | ranM (gives y n′) t r σ₁ = ranM _ t (m-inl (fm-gives r)) σ₁
      ... | ranM (stop w) t r σ₁ = ranM (stop w) t (m-inl (fm-stop r)) σ₁
      fold k F alg e (G ⊕f H) (minr x) n σ with fold k F alg e H x n σ
      ... | ranM (gives y n′) t r σ₁ = ranM _ t (m-inr (fm-gives r)) σ₁
      ... | ranM (stop w) t r σ₁ = ranM (stop w) t (m-inr (fm-stop r)) σ₁
      fold k F alg e (G ⊗f H) (mpair x x′) n σ with fold k F alg e G x n σ
      ... | ranM (stop w) t r σ₁ = ranM (stop w) (t ++ []) (m-pair r stopped) σ₁
      ... | ranM (gives y n₁) t₁ r σ₁ with fold k F alg e H x′ n₁ σ₁
      ...   | ranM (gives y′ n₂) t₂ r′ σ₂ = ranM _ (t₁ ++ t₂) (m-pair r (go-on (fm-gives r′))) σ₂
      ...   | ranM (stop w) t₂ r′ σ₂ = ranM (stop w) (t₁ ++ t₂) (m-pair r (go-on (fm-stop r′))) σ₂

  -- the runners of a table, built in order: each body runs over its prefix
  runners : ∀ {Γ} (ds : Defs Γ) → REnv ds
  runners ε            = ε
  runners (ds ▸ b1 b)  = runners ds ▸ λ k x a n σ → Eval.go ds (runners ds) k b mone (mpair x a) n σ
  runners (ds ▸ bω b)  = runners ds ▸ λ k x a n σ → Eval.go ds (runners ds) k b x a n σ

  -- ★ A14: EVERY TERM HAS A RUN, from every lent value, input, counter and
  -- world state, with any number of loop rounds
  exec : ∀ {Γ} (ds : Defs Γ) {E A B} (k : ℕ) (f : Tm Γ E A B) (e : MV E) (v : MV A) (n : ℕ) → WSt → Ran ds f e v n
  exec ds = Eval.go ds (runners ds)
