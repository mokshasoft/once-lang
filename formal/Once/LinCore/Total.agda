-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Total — plan 0.146 A14: EVERY PROGRAM HAS A RUN.
--
-- The memory theorems are about every run that exists; a term with no run
-- would satisfy them vacuously. Here an evaluator BUILDS a run of every
-- term, from every lent value, input and counter, for every world: the
-- world is any machine answering SigOps (a state, and an answer function).
--
-- Only the loop may run forever: it is given FUEL, a number of rounds, and a
-- run that uses it up ends `exhausted` after the rounds it ran (D374: a
-- server's run is cut a round at a time). Everything else terminates, and
-- why is the simply typed calculus's normalization (★ D428 part 3):
-- applying a closure VALUE runs a body that is not structurally smaller than
-- anything at hand (it came from the data). So, by TAIT'S METHOD, a value is
-- `Good` at its type: a closure is good when its code, run on any argument
-- that is good, has a run whose outcome is good. The evaluator takes good
-- inputs to good outcomes; building a closure proves it good by running its
-- body, a subterm; applying one uses that proof, and calls nothing. Every
-- value is good (`allGood`, by induction on the value), so `exec` needs no
-- hypothesis. Labels (D424) are run in table order, as before.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; cong; cong₂; subst; sym)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Function using (case_of_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.Spec.Word using (Carrier)
import Once.IR.Semantics.Value Carrier Carrier as Val
open import Once.LinCore.Flat using (Base; FTy; funit; fvoid; fw; _f*_; _f+_)

module Once.LinCore.Total
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (funit; fvoid; fw; _f*_; _f+_; Base; ⟦_⟧b)
open import Once.IR.Semantics.Trace using (T; ret; call; halt; CallOp)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Spends fmt ans bw using (module Budget)

------------------------------------------------------------------------
-- 0. THE SAME VALUE, up to its cells' names: what a copy is of its original.
------------------------------------------------------------------------

infix 4 _~_
data _~_ : ∀ {A} → MV A → MV A → Set where
  ~one  : mone ~ mone
  ~pair : ∀ {A B} {a a′ : MV A} {b b′ : MV B} → a ~ a′ → b ~ b′ → mpair a b ~ mpair a′ b′
  ~inl  : ∀ {A B} {a a′ : MV A} → a ~ a′ → minl {B = B} a ~ minl a′
  ~inr  : ∀ {A B} {b b′ : MV B} → b ~ b′ → minr {A = A} b ~ minr b′
  ~base : ∀ {b} {x : ⟦ b ⟧b} → mbase x ~ mbase x
  ~mu   : ∀ {F i j} {v v′ : MV (LF∙ F (μt F))} → v ~ v′ → mmu i v ~ mmu j v′
  ~ct   : ∀ {l X} {x x′ : MV X} → x ~ x′ → mct {l} x ~ mct x′
  ~fn   : ∀ {k g X A B} {c : Lam k g X A B} {i j x x′} → x ~ x′ → mfn i c x ~ mfn j c x′
  ~nu   : ∀ {F S i j} {p p′ : MV (Coalg F S ⊗t S)} → p ~ p′ → mnu i p ~ mnu j p′

~-refl : ∀ {A} (v : MV A) → v ~ v
~-refl mone        = ~one
~-refl (mpair a b) = ~pair (~-refl a) (~-refl b)
~-refl (minl a)    = ~inl (~-refl a)
~-refl (minr b)    = ~inr (~-refl b)
~-refl (mbase x)   = ~base
~-refl (mmu i v)   = ~mu (~-refl v)
~-refl (mct x)     = ~ct (~-refl x)
~-refl (mfn i c x) = ~fn (~-refl x)
~-refl (mnu i p)   = ~nu (~-refl p)

~-trans : ∀ {A} {u v w : MV A} → u ~ v → v ~ w → u ~ w
~-trans ~one        ~one          = ~one
~-trans (~pair p q) (~pair p′ q′) = ~pair (~-trans p p′) (~-trans q q′)
~-trans (~inl p)    (~inl p′)     = ~inl (~-trans p p′)
~-trans (~inr p)    (~inr p′)     = ~inr (~-trans p p′)
~-trans ~base       ~base         = ~base
~-trans (~mu p)     (~mu p′)      = ~mu (~-trans p p′)
~-trans (~ct p)     (~ct p′)      = ~ct (~-trans p p′)
~-trans (~fn p)     (~fn p′)      = ~fn (~-trans p p′)
~-trans (~nu p)     (~nu p′)      = ~nu (~-trans p p′)

-- a copy is its original, its cells renamed
copy-~ : ∀ {A} (v : MV A) n → fst (copy v n) ~ v
copy-~ mone n = ~one
copy-~ (mpair a b) n = ~pair (copy-~ a n) (copy-~ b (fst (snd (copy a n))))
copy-~ (minl a) n = ~inl (copy-~ a n)
copy-~ (minr b) n = ~inr (copy-~ b n)
copy-~ (mbase x) n = ~base
copy-~ (mmu i v) n = ~mu (copy-~ v n)
copy-~ (mct x) n = ~ct (copy-~ x n)
copy-~ (mfn i c x) n = ~fn (copy-~ x n)
copy-~ (mnu i p) n = ~nu (copy-~ p n)

-- ★ a WORLD: any machine that answers SigOps (its state may be the whole
-- history, so this is every strategy). It may give NO answer — it must, for
-- an op whose answer type is empty (`void`: an exit called by `lop`), and
-- may, for any other — and then the run is cut at that call (D427).
record World : Set₁ where
  field
    WSt : Set
    -- ★ B1.2: it answers master's calls (`CallOp`), or gives no answer
    answer : WSt → (o : CallOp) → Val.⟦ CallOp.cdom o ⟧ → Maybe (Val.⟦ CallOp.ccod o ⟧ × WSt)

module _ (W : World) where
  open World W

  -- ★ why a found run ended `exhausted`: a loop had no rounds left, or the
  -- world gave no answer to a call. Nothing else.
  data Spent : Set where
    out-of-fuel : Spent
    unanswered  : ∀ σ o x → answer σ o x ≡ nothing → Spent

  Because : Why → Set
  Because halted    = ⊤
  Because exhausted = Spent

  Cause : ∀ {B} → Outcome B → Set
  Cause (gives _ _) = ⊤
  Cause (stop y)    = Because y

  -- ★ why an op's path was cut: at a call the world did not answer (D450)
  data CutAt {X : Set} : (b : T X) → ∀ {t} → OpPath b t (inj₂ exhausted) → Set where
    c-here : ∀ {o a k} σ → answer σ o a ≡ nothing → CutAt (call o a k) p-cut
    c-call : ∀ {o a k y t} {p : OpPath (k y) t (inj₂ exhausted)} → CutAt (k y) p → CutAt (call o a k) (p-call p)

  cut-spent : ∀ {X} {b : T X} {t} {p : OpPath b t (inj₂ exhausted)} → CutAt b p → Spent
  cut-spent (c-here σ e) = unanswered σ _ _ e
  cut-spent (c-call c)   = cut-spent c

  -- an op's: the budget's `Cut`
  CutOp : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {t} → OpPath (opF s (toF (sdom s) (er x))) t (inj₂ exhausted) → Set
  CutOp {s} {x} p = CutAt (opF s (toF (sdom s) (er x))) p

  open Budget (λ {s} {x} {t} p → CutOp {s} {x} {t} p) using (Spends; SpendsM; Again)

  -- what an op's run ended by
  OpCause : ∀ {X} {b : T X} {t} {r : X ⊎ Why} → OpPath b t r → Set
  OpCause {b = b} {r = inj₂ exhausted} p = CutAt b p
  OpCause {r = inj₂ halted} p = ⊤
  OpCause {r = inj₁ _} p = ⊤

  call-cause : ∀ {X} {o a} {k : Val.⟦ CallOp.ccod o ⟧ → T X} {y t} {r : X ⊎ Why} (p : OpPath (k y) t r)
             → OpCause p → OpCause (p-call {o = o} {a = a} {k = k} p)
  call-cause {r = inj₁ _} p c = tt
  call-cause {r = inj₂ halted} p c = tt
  call-cause {r = inj₂ exhausted} p c = c-call c

  -- ★ the world answered the trace's calls, from `σ` to `σ′` (D448): each call as the world's answer
  -- at its state; every other event leaves the world as it is
  WTr : WSt → Trace → WSt → Set
  WTr σ []              σ′ = σ′ ≡ σ
  WTr σ (io o a y ∷ t) σ′ = Σ WSt λ σ₁ → (answer σ o a ≡ just (y , σ₁)) × WTr σ₁ t σ′
  {-# CATCHALL #-}
  WTr σ (_ ∷ t)        σ′ = WTr σ t σ′

  wtr-++ : ∀ {σ σ₁ σ₂} t₁ {t₂} → WTr σ t₁ σ₁ → WTr σ₁ t₂ σ₂ → WTr σ (t₁ ++ t₂) σ₂
  wtr-++ []                 refl w₂ = w₂
  wtr-++ (alloc _ ∷ t₁)     w₁ w₂ = wtr-++ t₁ w₁ w₂
  wtr-++ (free _ ∷ t₁)      w₁ w₂ = wtr-++ t₁ w₁ w₂
  wtr-++ (peek _ ∷ t₁)      w₁ w₂ = wtr-++ t₁ w₁ w₂
  wtr-++ (io o a y ∷ t₁)    (σ₁ , e , w₁) w₂ = (σ₁ , e , wtr-++ t₁ w₁ w₂)
  wtr-++ (stp _ _ ∷ t₁)     w₁ w₂ = wtr-++ t₁ w₁ w₂
  wtr-++ (tmp _ ∷ t₁)       w₁ w₂ = wtr-++ t₁ w₁ w₂

  wtr-[] : ∀ {σ σ′} t → WTr σ t σ′ → WTr σ (t ++ []) σ′
  wtr-[] t w = wtr-++ t w refl

  -- a trace with no call leaves the world as it is
  wtr-quiet : ∀ {σ} t → ios t ≡ [] → WTr σ t σ
  wtr-quiet []               _ = refl
  wtr-quiet (alloc _ ∷ t)    q = wtr-quiet t q
  wtr-quiet (free _ ∷ t)     q = wtr-quiet t q
  wtr-quiet (peek _ ∷ t)     q = wtr-quiet t q
  wtr-quiet (io _ _ _ ∷ t)   ()
  wtr-quiet (stp _ _ ∷ t)    ()
  wtr-quiet (tmp _ ∷ t)      q = wtr-quiet t q

  -- a run, found at a budget of loop rounds: its outcome, its events, the derivation, the world
  -- after it, the cause if it ran out, and the budget left (D449: one budget, spent along the run)
  record Ran {Γ} (ds : Defs Γ) {E A B} (f : Tm Γ E A B) (e : MV E) (v : MV A) (n : ℕ) (k : ℕ) (σ₀ : WSt) : Set where
    constructor ran
    field
      out   : Outcome B
      trace : Trace
      run   : Run ds f e v n out trace
      after : WSt
      cause : Cause out
      left  : ℕ
      spent : left ≤ k
      spends : Spends run k left
      world  : WTr σ₀ trace after

  -- ★ D480: a kept owned body's lent run is its run on a copy of the environment
  cinRan : ∀ {Γ} {ds : Defs Γ} {X A B} {b₀ : Tm Γ One (X ⊗t A) B} {x : MV X} {a : MV A} {n k σ}
         → Ran ds b₀ mone (mpair (fst (copy x n)) a) (fst (snd (copy x n))) k σ → Ran ds (cin b₀) x a n k σ
  cinRan {x = x} {n = n} {k = k} (ran o t rb σ₁ c l s sp wo) =
    ran o _ (r-∘ (r-∘ r-λ⁻ (go-on (r-⊗ r-copy (go-on (fm-gives r-id))))) (go-on (r-lift rb))) σ₁ c l s
        (k , (k , refl , (k , refl , refl)) , sp)
        (wtr-++ (snd (snd (copy x n)) ++ []) (wtr-quiet (snd (snd (copy x n)) ++ [])
                  (trans (ios-++ (snd (snd (copy x n))) []) (cong (_++ []) (ios-copy x n)))) wo)

  cinRanG : ∀ {Γ} {ds : Defs Γ} {X A B} {b₀ : Tm Γ One (X ⊗t A) B} {x : MV X} {a : MV A} {n k σ} {G : Outcome B → Set}
          → Σ (Ran ds b₀ mone (mpair (fst (copy x n)) a) (fst (snd (copy x n))) k σ) (λ r → G (Ran.out r))
          → Σ (Ran ds (cin b₀) x a n k σ) (λ r → G (Ran.out r))
  cinRanG (ran o t rb σ₁ c l s sp wo , g) = (cinRan (ran o t rb σ₁ c l s sp wo) , g)

  -- ★ D480: a plain many-use body's owned run: lent its environment, which is freed after
  ownRanG : ∀ {Γ} {ds : Defs Γ} {X A B} {b : Tm Γ X A B} {x : MV X} {a : MV A} {n k σ} {G : Outcome B → Set}
          → Σ (Ran ds b x a n k σ) (λ r → G (Ran.out r)) → Σ (Ran ds (ownBg b) mone (mpair x a) n k σ) (λ r → G (Ran.out r))
  ownRanG (ran (stop y) t rb σ₁ c l s sp wo , g) =
    (ran (stop y) _ (r-∘ (r-lend (fm-stop (r-snd rb))) stopped) σ₁ c l s sp (wtr-[] t wo) , g)
  ownRanG {x = x} (ran (gives w n₁) t rb σ₁ c l s sp wo , g) =
    ( ran (gives w n₁) _ (r-∘ (r-lend (fm-gives (r-snd rb))) (go-on (r-∘ (r-⊗ r-drop (go-on (fm-gives r-id))) (go-on r-λ))))
          σ₁ c l s (l , sp , (l , (l , refl , refl) , refl))
          (wtr-++ t wo (wtr-quiet ((freeAll x ++ []) ++ [])
                         (trans (ios-++ (freeAll x ++ []) []) (cong (_++ []) (trans (ios-++ (freeAll x) []) (cong (_++ []) (ios-freeAll x)))))))
    , g )

  -- ★ B1.2: an op's contract block, run in the world: each call answered, or
  -- the run cut where the world gave no answer
  Ends : ∀ {X : Set} → X ⊎ Why → Set
  Ends (inj₁ _) = ⊤
  Ends (inj₂ w) = Because w

  record OpRan {X : Set} (b : T X) (σ₀ : WSt) : Set where
    constructor opran
    field
      otrace : Trace
      oend   : X ⊎ Why
      opath  : OpPath b otrace oend
      oafter : WSt
      ocause : OpCause opath
      oworld : WTr σ₀ otrace oafter

  runOp   : ∀ {X} (b : T X) → (σ : WSt) → OpRan b σ
  runCall : ∀ {X} o a (k : Val.⟦ CallOp.ccod o ⟧ → T X) σ (m : Maybe (Val.⟦ CallOp.ccod o ⟧ × WSt))
          → answer σ o a ≡ m → OpRan (call o a k) σ
  runOp (ret x)      σ = opran [] (inj₁ x) p-ret σ tt refl
  runOp (call o a k) σ = runCall o a k σ (answer σ o a) refl
  runOp (halt o a)   σ = opran _ (inj₂ halted) p-halt σ tt refl
  runCall o a k σ (just (y , σ₁)) eq = case runOp (k y) σ₁ of λ where
    (opran t r p σ₂ c w) → opran (io o a y ∷ t) r (p-call p) σ₂ (call-cause p c) (σ₁ , eq , w)
  runCall o a k σ nothing eq = opran [] (inj₂ exhausted) p-cut σ (c-here σ eq) refl

  record RanM {Γ} (ds : Defs Γ) {E A} (F : LF) (alg : Tm Γ E (LF∙ F A) A) (e : MV E)
              (G : LF) (x : MV (LF∙ G (μt F))) (n : ℕ) (k : ℕ) (σ₀ : WSt) : Set where
    constructor ranM
    field
      out   : Outcome (LF∙ G A)
      trace : Trace
      run   : RunMap ds F alg e G x n out trace
      after : WSt
      cause : Cause out
      left  : ℕ
      spent : left ≤ k
      spends : SpendsM run k left
      world  : WTr σ₀ trace after

  ----------------------------------------------------------------------
  -- 1. ★ TAIT: GOOD VALUES, by recursion on the type. A closure is good when
  -- its code, on any environment the same as its own up to names (a copy)
  -- and any good argument, with any fuel, from any counter and world, has a
  -- run with a good outcome. μ data holds no closures (`LF`), so it is good.
  ----------------------------------------------------------------------

  -- ★ a ν is good when every observation of it (or of a copy) has a run whose
  -- layer's νs are good again: COINDUCTIVE, as the Spec's ν is
  mutual
    record GoodNu (F : LF) (v : MV (Nu F)) : Set where
      coinductive
      field obs : ∀ v′ → v′ ~ v → ∀ {Γ} (ds : Defs Γ) {E} (e : MV E) (k : ℕ) n (σ : WSt)
                → Σ (Ran ds (lout {F = F}) e v′ n k σ) (λ r → GoodLO F (Ran.out r))

    GoodLayer : ∀ F G → MV (LF∙ G (Nu F)) → Set
    GoodLayer F Idf      v            = GoodNu F v
    GoodLayer F Kone     _            = ⊤
    GoodLayer F Kzero    _            = ⊤
    GoodLayer F (Kb b)   _            = ⊤
    GoodLayer F (Kμ G)   _            = ⊤
    GoodLayer F (G ⊕f H) (minl w)     = GoodLayer F G w
    GoodLayer F (G ⊕f H) (minr w)     = GoodLayer F H w
    GoodLayer F (G ⊗f H) (mpair w w′) = GoodLayer F G w × GoodLayer F H w′

    GoodLO : ∀ F → Outcome (LF∙ F (Nu F)) → Set
    GoodLO F (gives w _) = GoodLayer F F w
    GoodLO F (stop _)    = ⊤
  open GoodNu

  -- a ν's goodness holds of its copies
  goodNu~ : ∀ {F} {v v′ : MV (Nu F)} → v′ ~ v → GoodNu F v → GoodNu F v′
  obs (goodNu~ q g) v″ q′ = obs g v″ (~-trans q′ q)

  mutual
    Good : (A : LTy) → MV A → Set
    Good (Nu F)      v            = GoodNu F v
    Good One         _            = ⊤
    Good Zero        _            = ⊤
    Good (A ⊗t B)    (mpair a b)  = Good A a × Good B b
    Good (A ⊕t B)    (minl a)     = Good A a
    Good (A ⊕t B)    (minr b)     = Good B b
    Good (Ct l X)    (mct x)      = Good X x
    Good (Fn once g A B) (mfn i (c1 ds b γ) x) =
      ∀ x′ → x′ ~ x → ∀ (k : ℕ) a n (σ : WSt) → Good A a
      → Σ (Ran ds b mone (mpair x′ a) n k σ) (λ r → GoodO B (Ran.out r))
    -- (D493: lent, its body's run; applied owned, its owned form's)
    Good (Fn many g A B) (mfn i (cω ds b γ) x) =
      (∀ x′ → x′ ~ x → ∀ (k : ℕ) a n (σ : WSt) → Good A a
        → Σ (Ran ds b x′ a n k σ) (λ r → GoodO B (Ran.out r)))
      × (∀ x′ → x′ ~ x → ∀ (k : ℕ) a n (σ : WSt) → Good A a
        → Σ (Ran ds (ownω b) mone (mpair x′ a) n k σ) (λ r → GoodO B (Ran.out r)))
    -- (D480: a kept owned body: good as a one-shot closure's)
    Good (Fn many g A B) (mfn i (cωᶜ ds b₀ γ) x) =
      ∀ x′ → x′ ~ x → ∀ (k : ℕ) a n (σ : WSt) → Good A a
      → Σ (Ran ds b₀ mone (mpair x′ a) n k σ) (λ r → GoodO B (Ran.out r))
    Good (μt F)      _            = ⊤
    Good (Bt b)      _            = ⊤

    GoodO : (B : LTy) → Outcome B → Set
    GoodO B (gives w _) = Good B w
    GoodO B (stop _)    = ⊤

  -- a run found, with a good outcome
  Ran⁺ : ∀ {Γ} (ds : Defs Γ) {E A B} (f : Tm Γ E A B) (e : MV E) (v : MV A) (n : ℕ) (k : ℕ) (σ : WSt) → Set
  Ran⁺ ds {B = B} f e v n k σ = Σ (Ran ds f e v n k σ) (λ r → GoodO B (Ran.out r))

  RanM⁺ : ∀ {Γ} (ds : Defs Γ) {E A} (F : LF) (alg : Tm Γ E (LF∙ F A) A) (e : MV E)
          (G : LF) (x : MV (LF∙ G (μt F))) (n : ℕ) (k : ℕ) (σ : WSt) → Set
  RanM⁺ ds {A = A} F alg e G x n k σ = Σ (RanM ds F alg e G x n k σ) (λ r → GoodO (LF∙ G A) (RanM.out r))

  -- goodness depends on the value, not on its cells' names
  good-~ : ∀ {A} {v v′ : MV A} → v′ ~ v → Good A v → Good A v′
  good-~ ~one        g        = tt
  good-~ (~pair p q) (ga , gb) = (good-~ p ga , good-~ q gb)
  good-~ (~inl p)    g        = good-~ p g
  good-~ (~inr p)    g        = good-~ p g
  good-~ ~base       g        = tt
  good-~ (~mu p)     g        = tt
  good-~ (~ct p)     g        = good-~ p g
  good-~ (~fn {c = c1 ds b γ} p) g = λ x″ q → g x″ (~-trans q p)
  good-~ (~fn {c = cω ds b γ} p) g = (λ x″ q → proj₁ g x″ (~-trans q p)) , (λ x″ q → proj₂ g x″ (~-trans q p))
  good-~ (~fn {c = cωᶜ ds b₀ γ} p) g = λ x″ q → g x″ (~-trans q p)
  good-~ (~nu p)     g        = goodNu~ (~nu p) g

  -- a layer of μ data is good: it holds no closure
  goodμ : ∀ G {F} (v : MV (LF∙ G (μt F))) → Good (LF∙ G (μt F)) v
  goodμ Idf      v           = tt
  goodμ Kone     v           = tt
  goodμ Kzero    ()
  goodμ (Kb b)   v           = tt
  goodμ (Kμ H)   v           = tt
  goodμ (G ⊕f H) (minl v)    = goodμ G v
  goodμ (G ⊕f H) (minr v)    = goodμ H v
  goodμ (G ⊗f H) (mpair v w) = (goodμ G v , goodμ H w)

  -- a flat value is good
  goodF : ∀ a (y : ⟦ a ⟧f) → Good ⌜ a ⌝ (mvF a y)
  goodF funit    y        = tt
  goodF fvoid    ()
  goodF (fw b)   y        = tt
  goodF (a f* b) (x , y)  = (goodF a x , goodF b y)
  goodF (a f+ b) (inj₁ x) = goodF a x
  goodF (a f+ b) (inj₂ y) = goodF b y

  -- tagging a layer's environments keeps them good
  good-tag : ∀ {l X} F (x : MV (LF∙ F X)) → Good (LF∙ F X) x → Good (LF∙ F (Ct l X)) (tag {l} F x)
  good-tag Idf      x            g        = g
  good-tag Kone     x            g        = tt
  good-tag Kzero    ()
  good-tag (Kb b)   x            g        = tt
  good-tag (Kμ G)   x            g        = tt
  good-tag (G ⊕f H) (minl x)     g        = good-tag G x g
  good-tag (G ⊕f H) (minr x)     g        = good-tag H x g
  good-tag (G ⊗f H) (mpair x x′) (g , g′) = (good-tag G x g , good-tag H x′ g′)

  -- a good layer of νs is a good value
  layer-good : ∀ F G (w : MV (LF∙ G (Nu F))) → GoodLayer F G w → Good (LF∙ G (Nu F)) w
  layer-good F Idf      w            g        = g
  layer-good F Kone     w            g        = tt
  layer-good F Kzero    ()
  layer-good F (Kb b)   w            g        = tt
  layer-good F (Kμ G)   w            g        = tt
  layer-good F (G ⊕f H) (minl w)     g        = layer-good F G w g
  layer-good F (G ⊕f H) (minr w)     g        = layer-good F H w g
  layer-good F (G ⊗f H) (mpair w w′) (g , g′) = (layer-good F G w g , layer-good F H w′ g′)

  glo : ∀ F (o : Outcome (LF∙ F (Nu F))) → GoodLO F o → GoodO (LF∙ F (Nu F)) o
  glo F (gives w _) g = layer-good F F w g
  glo F (stop _)    g = tt

  ----------------------------------------------------------------------
  -- 1½. ★ OBSERVING A GOOD ν: the run of `obsT`, built from the goodness of
  -- its coalgebra (Tait: no evaluator is called), and the new νs good again,
  -- by a guarded corecursion (the Spec's `anaA`/`mapA`).
  ----------------------------------------------------------------------

  -- a run that gives a value with a property
  record GaveP {Γ} (ds : Defs Γ) {E A B} (f : Tm Γ E A B) (e : MV E) (v : MV A) (n : ℕ) (P : MV B → Set) : Set where
    constructor gaveP
    field
      {w}  : MV B
      {n′} : ℕ
      {t}  : Trace
      run  : Run ds f e v n (gives w n′) t
      good : P w
      spare : ∀ k → Spends run k k
      quiet : ios t ≡ []

  -- a copy of the coalgebra beside each seed
  strRun : ∀ {Γ} (ds : Defs Γ) {F S} G (c : MV (Coalg F S)) → Good (Coalg F S) c
         → (w : MV (LF∙ G S)) → Good (LF∙ G S) w → ∀ n
         → GaveP ds (strL F G S) (mpair mone c) w n (Good (LF∙ G (Coalg F S ⊗t S)))
  strRun ds Idf c gc s gs n =
    gaveP (r-∘ r-λ⁻ (go-on (r-⊗ (r-snd r-copy) (go-on (fm-gives r-id))))) (good-~ (copy-~ c n) gc , gs)
          (λ k → (k , refl , (k , refl , refl)))
          (trans (ios-++ (snd (snd (copy c n))) []) (cong (_++ []) (ios-copy c n)))
  strRun ds Kone     c gc w gw n = gaveP r-id tt (λ k → refl) refl
  strRun ds Kzero    c gc () gw n
  strRun ds (Kb b)   c gc w gw n = gaveP r-id tt (λ k → refl) refl
  strRun ds (Kμ G)   c gc w gw n = gaveP r-id tt (λ k → refl) refl
  strRun ds (G ⊕f H) c gc (minl w) gw n = case strRun ds G c gc w gw n of λ where
    (gaveP {t = t} r g fr q) → gaveP (r-case₁ (r-∘ r (go-on r-inl))) g (λ k → (k , fr k , refl)) (trans (ios-++ t []) (cong (_++ []) q))
  strRun ds (G ⊕f H) c gc (minr w) gw n = case strRun ds H c gc w gw n of λ where
    (gaveP {t = t} r g fr q) → gaveP (r-case₂ (r-∘ r (go-on r-inr))) g (λ k → (k , fr k , refl)) (trans (ios-++ t []) (cong (_++ []) q))
  strRun ds (G ⊗f H) c gc (mpair w w′) (g₁ , g₂) n = case strRun ds G c gc w g₁ n of λ where
    (gaveP {n′ = n₁} {t = t₁} r₁ h₁ fr₁ q₁) → case strRun ds H c gc w′ g₂ n₁ of λ where
      (gaveP {t = t₂} r₂ h₂ fr₂ q₂) → gaveP (r-⊗ r₁ (go-on (fm-gives r₂))) (h₁ , h₂) (λ k → (k , fr₁ k , fr₂ k))
                                       (trans (ios-++ t₁ t₂) (cong₂ _++_ q₁ q₂))

  -- ★ D496: runs that give a good value at once, composed
  GaveG : ∀ {Γ} (ds : Defs Γ) {E A B} (f : Tm Γ E A B) (e : MV E) (v : MV A) (n : ℕ) → Set
  GaveG ds {B = B} f e v n = GaveP ds f e v n (Good B)

  gp-∘ : ∀ {Γ} {ds : Defs Γ} {E A B C} {f : Tm Γ E B C} {g : Tm Γ E A B} {e : MV E} {v : MV A} {n}
       → GaveG ds g e v n → (∀ (u : MV B) n′ → Good B u → GaveG ds f e u n′) → GaveG ds (f ∘l g) e v n
  gp-∘ (gaveP {w = u} {n′ = n₁} {t = t₁} r₁ g₁ s₁ q₁) k = case k u n₁ g₁ of λ where
    (gaveP {t = t₂} r₂ g₂ s₂ q₂) → gaveP (r-∘ r₁ (go-on r₂)) g₂ (λ l → (l , s₁ l , s₂ l)) (trans (ios-++ t₁ t₂) (cong₂ _++_ q₁ q₂))

  gp-⊗ : ∀ {Γ} {ds : Defs Γ} {E A B C D} {f : Tm Γ E A B} {g : Tm Γ E C D} {e : MV E} {a : MV A} {c : MV C} {n}
       → GaveG ds f e a n → (∀ n′ → GaveG ds g e c n′) → GaveG ds (f ⊗l g) e (mpair a c) n
  gp-⊗ (gaveP {n′ = n₁} {t = t₁} r₁ g₁ s₁ q₁) k = case k n₁ of λ where
    (gaveP {t = t₂} r₂ g₂ s₂ q₂) → gaveP (r-⊗ r₁ (go-on (fm-gives r₂))) (g₁ , g₂) (λ l → (l , s₁ l , s₂ l)) (trans (ios-++ t₁ t₂) (cong₂ _++_ q₁ q₂))

  gp-lend : ∀ {Γ} {ds : Defs Γ} {E X A B} {b : Tm Γ (E ⊗t X) A B} {e : MV E} {x : MV X} {a : MV A} {n}
          → Good X x → GaveG ds b (mpair e x) a n → GaveG ds (lend b) e (mpair x a) n
  gp-lend gx (gaveP r g s q) = gaveP (r-lend (fm-gives r)) (gx , g) s q

  gp-drop : ∀ {Γ} {ds : Defs Γ} {E A} {e : MV E} (v : MV A) n → GaveG ds (drop {A = A}) e v n
  gp-drop v n = gaveP r-drop tt (λ k → refl) (ios-freeAll v)

  -- the coalgebra freed beside a constant
  gp-free : ∀ {Γ} {ds : Defs Γ} {C X} (c : MV C) (x : MV X) → Good X x → ∀ n → GaveG ds (lul ∘l (drop ⊗l lid)) mone (mpair c x) n
  gp-free c x gx n =
    gp-∘ (gp-⊗ (gp-drop c n) (λ n′ → gaveP r-id gx (λ k → refl) refl))
         (λ { (mpair mone x′) n′ (_ , gx′) → gaveP r-λ gx′ (λ k → refl) refl })

  -- ★ D496: the coalgebra owned into the layer (`strO`), its run from goodness
  strORun : ∀ {Γ} (ds : Defs Γ) {F S} G (c : MV (Coalg F S)) → Good (Coalg F S) c
          → (w : MV (LF∙ G S)) → Good (LF∙ G S) w → ∀ n → GaveG ds (strO F G S) mone (mpair c w) n
  strPRun : ∀ {Γ} (ds : Defs Γ) {F S} G H b (c : MV (Coalg F S)) → Good (Coalg F S) c
          → (w : MV (LF∙ G S)) → Good (LF∙ G S) w → (w′ : MV (LF∙ H S)) → Good (LF∙ H S) w′ → ∀ n
          → GaveG ds (strP F G H S b) mone (mpair c (mpair w w′)) n
  strORun ds Idf      c gc s gs n = gaveP r-id (gc , gs) (λ k → refl) refl
  strORun ds Kone     c gc w gw n = gp-free c w gw n
  strORun ds Kzero    c gc () gw n
  strORun ds (Kb b)   c gc w gw n = gp-free c w gw n
  strORun ds (Kμ G)   c gc w gw n = gp-free c w gw n
  strORun ds (G ⊕f H) c gc (minl w) gw n = case strORun ds G c gc w gw n of λ where
    (gaveP {t = t} r g fr q) → gaveP (r-∘ r-dist₁ (go-on (r-case₁ (r-∘ r (go-on r-inl))))) g (λ k → (k , refl , (k , fr k , refl)))
                                     (trans (ios-++ t []) (cong (_++ []) q))
  strORun ds (G ⊕f H) c gc (minr w) gw n = case strORun ds H c gc w gw n of λ where
    (gaveP {t = t} r g fr q) → gaveP (r-∘ r-dist₂ (go-on (r-case₂ (r-∘ r (go-on r-inr))))) g (λ k → (k , refl , (k , fr k , refl)))
                                     (trans (ios-++ t []) (cong (_++ []) q))
  strORun ds (G ⊗f H) c gc (mpair w w′) (g₁ , g₂) n = strPRun ds G H (hasId H) c gc w g₁ w′ g₂ n
  strPRun ds {F} {S} G H true c gc w gw w′ gw′ n =
    gp-∘ (gp-∘ (gp-∘ (gp-∘ (gp-lend gc (gp-⊗ (strRun ds G c gc w gw n) (λ n′ → gaveP r-id gw′ (λ k → refl) refl)))
                           (λ { (mpair c′ (mpair v v′)) n′ (gc′ , (gv , gv′)) → gaveP r-α⁻ ((gc′ , gv) , gv′) (λ k → refl) refl }))
                     (λ { (mpair (mpair c′ v) v′) n′ ((gc′ , gv) , gv′) →
                            gp-⊗ (gaveP r-swap (gv , gc′) (λ k → refl) refl) (λ n″ → gaveP r-id gv′ (λ k → refl) refl) }))
               (λ { (mpair (mpair v c′) v′) n′ ((gv , gc′) , gv′) → gaveP r-α (gv , (gc′ , gv′)) (λ k → refl) refl }))
         (λ { (mpair v (mpair c′ v′)) n′ (gv , (gc′ , gv′)) →
                gp-⊗ (gaveP r-id gv (λ k → refl) refl) (λ n″ → strORun ds H c′ gc′ v′ gv′ n″) })
  strPRun ds {F} {S} G H false c gc w gw w′ gw′ n =
    gp-∘ (gp-∘ (gp-lend gc (gp-⊗ (gaveP r-id gw (λ k → refl) refl) (λ n′ → strRun ds H c gc w′ gw′ n′)))
               (λ { (mpair c′ (mpair v v′)) n′ (gc′ , (gv , gv′)) → gaveP r-α⁻ ((gc′ , gv) , gv′) (λ k → refl) refl }))
         (λ { (mpair (mpair c′ v) v′) n′ ((gc′ , gv) , gv′) →
                gp-⊗ (strORun ds G c′ gc′ v gv n′) (λ n″ → gaveP r-id gv′ (λ k → refl) refl) })

  -- each pair of a layer a ν: the values, at a counter, and their run
  mapV : ∀ {F S} G → MV (LF∙ G (Coalg F S ⊗t S)) → ℕ → MV (LF∙ G (Nu F)) × ℕ
  mapV {F} {S} Idf p n   = (mnu (szν F S , n) p , suc n)
  mapV Kone     w n      = (w , n)
  mapV Kzero    () n
  mapV (Kb b)   w n      = (w , n)
  mapV (Kμ G)   w n      = (w , n)
  mapV (G ⊕f H) (minl w) n = (minl (fst (mapV G w n)) , snd (mapV G w n))
  mapV (G ⊕f H) (minr w) n = (minr (fst (mapV H w n)) , snd (mapV H w n))
  mapV (G ⊗f H) (mpair w w′) n =
    (mpair (fst (mapV G w n)) (fst (mapV H w′ (snd (mapV G w n)))) , snd (mapV H w′ (snd (mapV G w n))))

  mapRun : ∀ {Γ} (ds : Defs Γ) {F S} G (w : MV (LF∙ G (Coalg F S ⊗t S))) n
         → Σ Trace λ t → Run ds (mapNu F G S) mone w n (gives (fst (mapV G w n)) (snd (mapV G w n))) t
  mapRun ds Idf      p n = (_ , r-unf)
  mapRun ds Kone     w n = (_ , r-id)
  mapRun ds Kzero    () n
  mapRun ds (Kb b)   w n = (_ , r-id)
  mapRun ds (Kμ G)   w n = (_ , r-id)
  mapRun ds {F} {S} (G ⊕f H) (minl w) n = (_ , r-case₁ (r-∘ (snd (mapRun ds {F} {S} G w n)) (go-on r-inl)))
  mapRun ds {F} {S} (G ⊕f H) (minr w) n = (_ , r-case₂ (r-∘ (snd (mapRun ds {F} {S} H w n)) (go-on r-inr)))
  mapRun ds {F} {S} (G ⊗f H) (mpair w w′) n =
    (_ , r-⊗ (snd (mapRun ds {F} {S} G w n)) (go-on (fm-gives (snd (mapRun ds {F} {S} H w′ (snd (mapV G w n)))))))

  -- …and with no call
  map-quiet : ∀ {Γ} (ds : Defs Γ) {F S} G (w : MV (LF∙ G (Coalg F S ⊗t S))) n → ios (fst (mapRun ds {F} {S} G w n)) ≡ []
  map-quiet ds Idf      p n = refl
  map-quiet ds Kone     w n = refl
  map-quiet ds Kzero    () n
  map-quiet ds (Kb b)   w n = refl
  map-quiet ds (Kμ G)   w n = refl
  map-quiet ds {F} {S} (G ⊕f H) (minl w) n =
    trans (ios-++ (fst (mapRun ds {F} {S} G w n)) []) (cong (_++ []) (map-quiet ds {F} {S} G w n))
  map-quiet ds {F} {S} (G ⊕f H) (minr w) n =
    trans (ios-++ (fst (mapRun ds {F} {S} H w n)) []) (cong (_++ []) (map-quiet ds {F} {S} H w n))
  map-quiet ds {F} {S} (G ⊗f H) (mpair w w′) n =
    trans (ios-++ (fst (mapRun ds {F} {S} G w n)) (fst (mapRun ds {F} {S} H w′ (snd (mapV G w n)))))
          (cong₂ _++_ (map-quiet ds {F} {S} G w n) (map-quiet ds {F} {S} H w′ (snd (mapV G w n))))

  -- a layer's νs are built without a loop: nothing spent
  map-free : ∀ {Γ} (ds : Defs Γ) {F S} G (w : MV (LF∙ G (Coalg F S ⊗t S))) n k → Spends (snd (mapRun ds {F} {S} G w n)) k k
  map-free ds Idf      p n k = refl
  map-free ds Kone     w n k = refl
  map-free ds Kzero    () n k
  map-free ds (Kb b)   w n k = refl
  map-free ds (Kμ G)   w n k = refl
  map-free ds {F} {S} (G ⊕f H) (minl w) n k = (k , map-free ds {F} {S} G w n k , refl)
  map-free ds {F} {S} (G ⊕f H) (minr w) n k = (k , map-free ds {F} {S} H w n k , refl)
  map-free ds {F} {S} (G ⊗f H) (mpair w w′) n k =
    (k , map-free ds {F} {S} G w n k , map-free ds {F} {S} H w′ (snd (mapV G w n)) k)

  mutual
    -- ★ a ν built from a good coalgebra and seed is good: its observation (of
    -- it or of a copy) runs, and the νs it gives are good again (corecursion,
    -- guarded by `obs`, as the Spec's `anaA` by `outν`)
    goodν : ∀ {F S} (p : MV (Coalg F S ⊗t S)) → Good (Coalg F S ⊗t S) p → ∀ i → GoodNu F (mnu i p)
    obs (goodν p gp i) (mnu i′ p′) (~nu q) ds e k n σ = observe p′ (good-~ q gp) i′ ds e k n σ

    -- one observation: the coalgebra (good) on the seed, then the layer
    observe : ∀ {F S} (p : MV (Coalg F S ⊗t S)) → Good (Coalg F S ⊗t S) p → ∀ i {Γ} (ds : Defs Γ) {E} (e : MV E)
              (k : ℕ) n (σ : WSt) → Σ (Ran ds (lout {F = F}) e (mnu i p) n k σ) (λ r → GoodLO F (Ran.out r))
    observe {F} {S} (mpair (mfn j (cω ds′ b γ) x) s) (gc , gs) i ds e k n σ = case proj₁ gc x (~-refl x) k s n σ gs of λ where
      (ran (stop y) t rb σ₁ cz l sp sps wo , _) →
        ( ran (stop y) _ (r-nout (r-∘ (r-∘ (r-lend (fm-stop (r-snd (r-bev rb)))) stopped) stopped))
              σ₁ cz l sp sps (wtr-[] ((peek j ∷ t) ++ []) (wtr-[] (peek j ∷ t) wo))
        , tt )
      (ran (gives w n₁) t rb σ₁ _ l sp sps wo , gw) → case strORun ds F (mfn j (cω ds′ b γ) x) gc w gw n₁ of λ where
        (gaveP {w = w₂} {n′ = n₂} {t = t₂} r₂ g₂ fr₂ q₂) →
          ( ran _ _ (r-nout (r-∘ (r-∘ (r-lend (fm-gives (r-snd (r-bev rb)))) (go-on r₂)) (go-on (snd (mapRun ds {F} {S} F w₂ n₂)))))
                σ₁ tt l sp (l , (l , sps , fr₂ l) , map-free ds {F} {S} F w₂ n₂ l)
                (wtr-++ ((peek j ∷ t) ++ t₂) (wtr-++ (peek j ∷ t) wo (wtr-quiet t₂ q₂))
                        (wtr-quiet (fst (mapRun ds {F} {S} F w₂ n₂)) (map-quiet ds {F} {S} F w₂ n₂)))
          , layerGood F w₂ g₂ n₂ )

    observe {F} {S} (mpair (mfn j (cωᶜ ds′ b₀ γ) x) s) (gc , gs) i ds e k n σ = case cinRanG (gc (fst (copy x n)) (copy-~ x n) k s (fst (snd (copy x n))) σ gs) of λ where
      (ran (stop y) t rb σ₁ cz l sp sps wo , _) →
        ( ran (stop y) _ (r-nout (r-∘ (r-∘ (r-lend (fm-stop (r-snd (r-bevᶜ rb)))) stopped) stopped))
              σ₁ cz l sp sps (wtr-[] ((peek j ∷ t) ++ []) (wtr-[] (peek j ∷ t) wo))
        , tt )
      (ran (gives w n₁) t rb σ₁ _ l sp sps wo , gw) → case strORun ds F (mfn j (cωᶜ ds′ b₀ γ) x) gc w gw n₁ of λ where
        (gaveP {w = w₂} {n′ = n₂} {t = t₂} r₂ g₂ fr₂ q₂) →
          ( ran _ _ (r-nout (r-∘ (r-∘ (r-lend (fm-gives (r-snd (r-bevᶜ rb)))) (go-on r₂)) (go-on (snd (mapRun ds {F} {S} F w₂ n₂)))))
                σ₁ tt l sp (l , (l , sps , fr₂ l) , map-free ds {F} {S} F w₂ n₂ l)
                (wtr-++ ((peek j ∷ t) ++ t₂) (wtr-++ (peek j ∷ t) wo (wtr-quiet t₂ q₂))
                        (wtr-quiet (fst (mapRun ds {F} {S} F w₂ n₂)) (map-quiet ds {F} {S} F w₂ n₂)))
          , layerGood F w₂ g₂ n₂ )

    -- the layer's νs good again (the corecursive calls, in head position)
    layerGood : ∀ {F S} G (w : MV (LF∙ G (Coalg F S ⊗t S))) → Good (LF∙ G (Coalg F S ⊗t S)) w → ∀ n
              → GoodLayer F G (fst (mapV G w n))
    layerGood {F} {S} Idf p gp n = goodν p gp (szν F S , n)
    layerGood Kone     w gw n = tt
    layerGood Kzero    () gw n
    layerGood (Kb b)   w gw n = tt
    layerGood (Kμ G)   w gw n = tt
    layerGood {F} {S} (G ⊕f H) (minl w) gw n = layerGood {F} {S} G w gw n
    layerGood {F} {S} (G ⊕f H) (minr w) gw n = layerGood {F} {S} H w gw n
    layerGood {F} {S} (G ⊗f H) (mpair w w′) (g₁ , g₂) n =
      (layerGood {F} {S} G w g₁ n , layerGood {F} {S} H w′ g₂ (snd (mapV G w n)))

  ----------------------------------------------------------------------
  -- 2. The label table's runners (D424): each takes good inputs to a good
  -- outcome.
  ----------------------------------------------------------------------

  Runner : ∀ {Δ σ} → Defs Δ → Body Δ σ → Set
  Runner ds (b1 {X = X} {A} b _) = ∀ (k : ℕ) x a n (σ : WSt) → Good X x → Good A a → Ran⁺ ds b mone (mpair x a) n k σ
  Runner ds (bω {X = X} {A} b _) = ∀ (k : ℕ) x a n (σ : WSt) → Good X x → Good A a → Ran⁺ ds b x a n k σ

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
  find (ρ ▸ r) (there p) = let found q r′ = find ρ p in found (lk-there q) r′

  ------------------------------------------------------------------------
  -- 3. THE EVALUATOR, over a table and its runners, from good inputs to a
  -- good outcome. It terminates by: the fuel (only `liter` spends it), then
  -- the term, then the value (a fold). Building a closure runs its body, a
  -- subterm, inside the proof that it is good; applying one runs nothing.
  -- ★ Every result carries its CAUSE: a run found `exhausted` ran out of fuel
  -- at a loop or met a call the world did not answer, passed up from the
  -- sub-run that stopped. The evaluator never stops on its own.
  ------------------------------------------------------------------------

  -- ★ D493: a composite run from its pieces' runs (`go`'s `∘` and `⊗`, given the pieces)
  seqR : ∀ {Γ} {ds : Defs Γ} {E A B C} {f : Tm Γ E B C} {g : Tm Γ E A B} {e : MV E} {v : MV A} {n k σ}
       → Ran⁺ ds g e v n k σ
       → (∀ (u : MV B) n₁ l₁ (σ₁ : WSt) → Good B u → Ran⁺ ds f e u n₁ l₁ σ₁)
       → Ran⁺ ds (f ∘l g) e v n k σ
  seqR (ran (gives u n₁) t₁ rg σ₁ _ l₁ s₁ sp₁ wo₁ , gu) kf = case kf u n₁ l₁ σ₁ gu of λ where
    (ran o t₂ rf σ₂ c l₂ s₂ sp₂ wo₂ , gw) → (ran o (t₁ ++ t₂) (r-∘ rg (go-on rf)) σ₂ c l₂ (≤-trans s₂ s₁) (l₁ , sp₁ , sp₂) (wtr-++ t₁ wo₁ wo₂) , gw)
  seqR (ran (stop y) t rg σ₁ c l₁ s₁ sp₁ wo₁ , _) kf = (ran (stop y) (t ++ []) (r-∘ rg stopped) σ₁ c l₁ s₁ sp₁ (wtr-[] t wo₁) , tt)

  parR : ∀ {Γ} {ds : Defs Γ} {E A B C D} {f : Tm Γ E A B} {g : Tm Γ E C D} {e : MV E} {a : MV A} {c : MV C} {n k σ}
       → Ran⁺ ds f e a n k σ
       → (∀ n₁ l₁ (σ₁ : WSt) → Ran⁺ ds g e c n₁ l₁ σ₁)
       → Ran⁺ ds (f ⊗l g) e (mpair a c) n k σ
  parR (ran (stop y) t rf σ₁ w l₁ s₁ sp₁ wo₁ , _) kg = (ran (stop y) (t ++ []) (r-⊗ rf stopped) σ₁ w l₁ s₁ sp₁ (wtr-[] t wo₁) , tt)
  parR (ran (gives a′ n₁) t₁ rf σ₁ _ l₁ s₁ sp₁ wo₁ , ga′) kg = case kg n₁ l₁ σ₁ of λ where
    (ran (gives c′ n₂) t₂ rg σ₂ _ l₂ s₂ sp₂ wo₂ , gc′) →
      (ran _ (t₁ ++ t₂) (r-⊗ rf (go-on (fm-gives rg))) σ₂ tt l₂ (≤-trans s₂ s₁) (l₁ , sp₁ , sp₂) (wtr-++ t₁ wo₁ wo₂) , (ga′ , gc′))
    (ran (stop y) t₂ rg σ₂ w l₂ s₂ sp₂ wo₂ , _) →
      (ran (stop y) (t₁ ++ t₂) (r-⊗ rf (go-on (fm-stop rg))) σ₂ w l₂ (≤-trans s₂ s₁) (l₁ , sp₁ , sp₂) (wtr-++ t₁ wo₁ wo₂) , tt)

  -- ★ D494 amended: a body run lent beside the environment it reads (`go`'s `lend`, given the body's run)
  lendR : ∀ {Γ} {ds : Defs Γ} {X A B} {s : Tm Γ X A B} {x : MV X} {a : MV A} {n k σ}
        → Good X x → Ran⁺ ds s x a n k σ → Ran⁺ ds (lend (bsnd s)) mone (mpair x a) n k σ
  lendR gx (ran (gives w n′) t r σ₁ _ l s sp wo , gw) = (ran _ t (r-lend (fm-gives (r-snd r))) σ₁ tt l s sp wo , (gx , gw))
  lendR gx (ran (stop y) t r σ₁ c l s sp wo , _) = (ran (stop y) t (r-lend (fm-stop (r-snd r))) σ₁ c l s sp wo , tt)

  -- the halves of the environment beside the parts of the argument: words moved, nothing run
  mixR : ∀ {Γ} {ds : Defs Γ} {X₁ X₂ A₁ A₂} (u : MV ((X₁ ⊗t X₂) ⊗t (A₁ ⊗t A₂))) n k (σ : WSt)
       → Good ((X₁ ⊗t X₂) ⊗t (A₁ ⊗t A₂)) u → Ran⁺ ds mixO mone u n k σ
  mixR (mpair (mpair x₁ x₂) (mpair a₁ a₂)) n k σ ((g₁ , g₂) , (h₁ , h₂)) =
    seqR (seqR (ran _ _ r-α σ tt k ≤-refl refl refl , (g₁ , (g₂ , (h₁ , h₂))))
               (λ { (mpair x₁′ (mpair x₂′ (mpair a₁′ a₂′))) n₁ l₁ σ₁ (g₁′ , (g₂′ , (h₁′ , h₂′))) →
                      parR (ran _ _ r-id σ₁ tt l₁ ≤-refl refl refl , g₁′)
                           (λ n₂ l₂ σ₂ →
                              seqR (seqR (ran _ _ r-α⁻ σ₂ tt l₂ ≤-refl refl refl , ((g₂′ , h₁′) , h₂′))
                                         (λ { (mpair (mpair x₂″ a₁″) a₂″) n₃ l₃ σ₃ ((g₂″ , h₁″) , h₂″) →
                                                parR (ran _ _ r-swap σ₃ tt l₃ ≤-refl refl refl , (h₁″ , g₂″))
                                                     (λ n₄ l₄ σ₄ → ran _ _ r-id σ₄ tt l₄ ≤-refl refl refl , h₂″) }))
                                   (λ { (mpair (mpair a₁‴ x₂‴) a₂‴) n₃ l₃ σ₃ ((h₁‴ , g₂‴) , h₂‴) →
                                          ran _ _ r-α σ₃ tt l₃ ≤-refl refl refl , (h₁‴ , (g₂‴ , h₂‴)) })) }))
         (λ { (mpair x₁′ (mpair a₁′ (mpair x₂′ a₂′))) n₁ l₁ σ₁ (g₁′ , (h₁′ , (g₂′ , h₂′))) →
                ran _ _ r-α⁻ σ₁ tt l₁ ≤-refl refl refl , ((g₁′ , h₁′) , (g₂′ , h₂′)) })

  -- a many-use closure applied owned: by its goodness, no recursive call
  evωR : ∀ {Γ} {ds : Defs Γ} {E g A B} (e : MV E) (f : MV (Fn many g A B)) (a : MV A) n k (σ : WSt)
       → Good (Fn many g A B) f → Good A a → Ran⁺ ds (levω {g = g}) e (mpair f a) n k σ
  evωR e (mfn i (cωᶜ ds′ b₀ γ) x) a n k σ gf ga = case gf x (~-refl x) k a n σ ga of λ where
    (ran o t rb σ₁ c l s sp wo , gw) → (ran o (free i ∷ t) (r-evωᶜ rb) σ₁ c l s sp wo , gw)
  evωR e (mfn i (cω ds′ b γ) x) a n k σ gf ga = case proj₂ gf x (~-refl x) k a n σ ga of λ where
    (ran o t rb σ₁ c l s sp wo , gw) → (ran o (free i ∷ t) (r-evω rb) σ₁ c l s sp wo , gw)

  module Eval {Γ} (ds : Defs Γ) (ρ : REnv ds) where
    mutual
      go : ∀ {E A B} (k : ℕ) (f : Tm Γ E A B) (e : MV E) (v : MV A) (n : ℕ) (σ : WSt)
         → Good E e → Good A v → Ran⁺ ds f e v n k σ
      go k lid e v n σ ge gv = (ran _ _ r-id σ tt k ≤-refl refl refl , gv)
      go k (f ∘l g) e v n σ ge gv = case go k g e v n σ ge gv of λ where
        (ran (gives u n₁) t₁ rg σ₁ _ l₁ s₁ sp₁ wo₁ , gu) → case go l₁ f e u n₁ σ₁ ge gu of λ where
          (ran o t₂ rf σ₂ c l₂ s₂ sp₂ wo₂ , gw) → (ran o (t₁ ++ t₂) (r-∘ rg (go-on rf)) σ₂ c l₂ (≤-trans s₂ s₁) (l₁ , sp₁ , sp₂) (wtr-++ t₁ wo₁ wo₂) , gw)
        (ran (stop y) t rg σ₁ c l₁ s₁ sp₁ wo₁ , _) → (ran (stop y) (t ++ []) (r-∘ rg stopped) σ₁ c l₁ s₁ sp₁ (wtr-[] t wo₁) , tt)
      go k (f ⊗l g) e (mpair a c) n σ ge (ga , gc) = case go k f e a n σ ge ga of λ where
        (ran (stop y) t rf σ₁ w l₁ s₁ sp₁ wo₁ , _) → (ran (stop y) (t ++ []) (r-⊗ rf stopped) σ₁ w l₁ s₁ sp₁ (wtr-[] t wo₁) , tt)
        (ran (gives a′ n₁) t₁ rf σ₁ _ l₁ s₁ sp₁ wo₁ , ga′) → case go l₁ g e c n₁ σ₁ ge gc of λ where
          (ran (gives c′ n₂) t₂ rg σ₂ _ l₂ s₂ sp₂ wo₂ , gc′) →
            (ran _ (t₁ ++ t₂) (r-⊗ rf (go-on (fm-gives rg))) σ₂ tt l₂ (≤-trans s₂ s₁) (l₁ , sp₁ , sp₂) (wtr-++ t₁ wo₁ wo₂) , (ga′ , gc′))
          (ran (stop y) t₂ rg σ₂ w l₂ s₂ sp₂ wo₂ , _) →
            (ran (stop y) (t₁ ++ t₂) (r-⊗ rf (go-on (fm-stop rg))) σ₂ w l₂ (≤-trans s₂ s₁) (l₁ , sp₁ , sp₂) (wtr-++ t₁ wo₁ wo₂) , tt)
      go k ρl e (mpair a mone) n σ ge (ga , _) = (ran _ _ r-ρ σ tt k ≤-refl refl refl , ga)
      go k ρl⁻ e a n σ ge ga = (ran _ _ r-ρ⁻ σ tt k ≤-refl refl refl , (ga , tt))
      go k lul e (mpair mone a) n σ ge (_ , ga) = (ran _ _ r-λ σ tt k ≤-refl refl refl , ga)
      go k lul⁻ e a n σ ge ga = (ran _ _ r-λ⁻ σ tt k ≤-refl refl refl , (tt , ga))
      go k lassoc e (mpair (mpair a b) c) n σ ge ((ga , gb) , gc) = (ran _ _ r-α σ tt k ≤-refl refl refl , (ga , (gb , gc)))
      go k lassoc⁻ e (mpair a (mpair b c)) n σ ge (ga , (gb , gc)) = (ran _ _ r-α⁻ σ tt k ≤-refl refl refl , ((ga , gb) , gc))
      go k lswap e (mpair a b) n σ ge (ga , gb) = (ran _ _ r-swap σ tt k ≤-refl refl refl , (gb , ga))
      go k dup e v n σ ge gv = (ran _ _ r-dup σ tt k ≤-refl refl (wtr-quiet (snd (snd (copy v n))) (ios-copy v n)) , (gv , good-~ (copy-~ v n) gv))
      go k drop e v n σ ge gv = (ran _ _ r-drop σ tt k ≤-refl refl (wtr-quiet (freeAll v) (ios-freeAll v)) , tt)
      go k linl e a n σ ge ga = (ran _ _ r-inl σ tt k ≤-refl refl refl , ga)
      go k linr e b n σ ge gb = (ran _ _ r-inr σ tt k ≤-refl refl refl , gb)
      go k (lcase f g) e (minl a) n σ ge ga = case go k f e a n σ ge ga of λ where
        (ran o t r σ₁ c l s sp wo , gw) → (ran o t (r-case₁ r) σ₁ c l s sp wo , gw)
      go k (lcase f g) e (minr b) n σ ge gb = case go k g e b n σ ge gb of λ where
        (ran o t r σ₁ c l s sp wo , gw) → (ran o t (r-case₂ r) σ₁ c l s sp wo , gw)
      go k lzero e () n σ ge gv
      go k ldist e (mpair x (minl a)) n σ ge (gx , ga) = (ran _ _ r-dist₁ σ tt k ≤-refl refl refl , (gx , ga))
      go k ldist e (mpair x (minr b)) n σ ge (gx , gb) = (ran _ _ r-dist₂ σ tt k ≤-refl refl refl , (gx , gb))
      go k lIn e v n σ ge gv = (ran _ _ r-In σ tt k ≤-refl refl refl , tt)
      go k (lOutμ {F}) e (mmu i v) n σ ge gv = (ran _ _ r-Outμ σ tt k ≤-refl refl refl , goodμ F v)
      go k (lcata F alg) e x n σ ge gx = cata k F alg e x n σ ge
      go k (lclo F p) e x n σ ge gx = (ran _ _ r-clo σ tt k ≤-refl refl refl , good-tag F x gx)
      go k (lapp p) e (mpair (mct x) a) n σ ge (gx , ga) = case find ρ p of λ where
        (found {b = b1 b _} q r) → case r k x a n σ gx ga of λ where
          (ran o t rb σ₁ c l s sp wo , gw) → (ran o t (r-app q rb) σ₁ c l s sp wo , gw)
      go k (lend b) e (mpair x a) n σ ge (gx , ga) = case go k b (mpair e x) a n σ (ge , gx) ga of λ where
        (ran (gives w n′) t r σ₁ _ l s sp wo , gw) → (ran _ t (r-lend (fm-gives r)) σ₁ tt l s sp wo , (gx , gw))
        (ran (stop y) t r σ₁ c l s sp wo , _) → (ran (stop y) t (r-lend (fm-stop r)) σ₁ c l s sp wo , tt)
      go k (blift f) e a n σ ge ga = case go k f mone a n σ tt ga of λ where
        (ran o t r σ₁ c l s sp wo , gw) → (ran o t (r-lift r) σ₁ c l s sp wo , gw)
      go k (bfst f) (mpair e₁ e₂) a n σ (ge₁ , _) ga = case go k f e₁ a n σ ge₁ ga of λ where
        (ran o t r σ₁ c l s sp wo , gw) → (ran o t (r-fst r) σ₁ c l s sp wo , gw)
      go k (bsnd f) (mpair e₁ e₂) a n σ (_ , ge₂) ga = case go k f e₂ a n σ ge₂ ga of λ where
        (ran o t r σ₁ c l s sp wo , gw) → (ran o t (r-snd r) σ₁ c l s sp wo , gw)
      go k (bcaseE f g) (minl e) a n σ ge ga = case go k f e a n σ ge ga of λ where
        (ran o t r σ₁ c l s sp wo , gw) → (ran o t (r-caseE₁ r) σ₁ c l s sp wo , gw)
      go k (bcaseE f g) (minr e) a n σ ge ga = case go k g e a n σ ge ga of λ where
        (ran o t r σ₁ c l s sp wo , gw) → (ran o t (r-caseE₂ r) σ₁ c l s sp wo , gw)
      go k (bout {F} f) (mmu i v) a n σ ge ga = case go k f v a n σ (goodμ F v) ga of λ where
        (ran o t r σ₁ c l s sp wo , gw) → (ran o (peek i ∷ t) (r-out r) σ₁ c l s sp wo , gw)
      go k bcopy e mone n σ ge gv = (ran _ _ r-copy σ tt k ≤-refl refl (wtr-quiet (snd (snd (copy e n))) (ios-copy e n)) , good-~ (copy-~ e n) ge)
      go k (bapp p) (mct x) a n σ gx ga = case find ρ p of λ where
        (found {b = bω b _} q r) → case r k x a n σ gx ga of λ where
          (ran o t rb σ₁ c l s sp wo , gw) → (ran o t (r-bapp q rb) σ₁ c l s sp wo , gw)
      -- ★ D428 part 3: a closure is good: its body, run on a good environment
      -- and argument, has a good run (by this evaluator, on a subterm)
      go k (llam b γ) e x n σ ge gx =
        (ran _ _ r-lam σ tt k ≤-refl refl refl , λ x′ p k′ a n′ σ′ ga → go k′ b mone (mpair x′ a) n′ σ′ tt (good-~ p gx , ga))
      go k (llamω b γ) e x n σ ge gx =
        (ran _ _ r-lamω σ tt k ≤-refl refl refl
        , (λ x′ p k′ a n′ σ′ ga → go k′ b x′ a n′ σ′ (good-~ p gx) ga)
        , (λ x′ p k′ a n′ σ′ ga → subst (λ t → Ran⁺ ds t mone (mpair x′ a) n′ k′ σ′) (sym (ownω-≡ b))
                                     (goOwn b (ownOf b) k′ x′ a n′ σ′ (good-~ p gx) ga)))
      -- applying one runs it, by its goodness: no recursive call
      go k lev e (mpair (mfn i (c1 ds′ b γ) x) a) n σ ge (gf , ga) = case gf x (~-refl x) k a n σ ga of λ where
        (ran o t rb σ₁ c l s sp wo , gw) → (ran o (free i ∷ t) (r-ev rb) σ₁ c l s sp wo , gw)
      go k bev (mfn i (cω ds′ b γ) x) a n σ gf ga = case proj₁ gf x (~-refl x) k a n σ ga of λ where
        (ran o t rb σ₁ c l s sp wo , gw) → (ran o (peek i ∷ t) (r-bev rb) σ₁ c l s sp wo , gw)
      -- ★ D480: a kept owned body: built, good as a one-shot closure; lent, its run on a copy;
      -- applied owned, its run on the environment (a plain closure's: lent, then freed)
      go k (llamωᶜ b₀ γ) e x n σ ge gx =
        (ran _ _ r-lamωᶜ σ tt k ≤-refl refl refl , λ x′ p k′ a n′ σ′ ga → go k′ b₀ mone (mpair x′ a) n′ σ′ tt (good-~ p gx , ga))
      go k bev (mfn i (cωᶜ ds′ b₀ γ) x) a n σ gf ga = case gf (fst (copy x n)) (copy-~ x n) k a (fst (snd (copy x n))) σ ga of λ where
        (r₀ , gw) → let R = cinRan r₀ in
          (ran (Ran.out R) (peek i ∷ Ran.trace R) (r-bevᶜ (Ran.run R)) (Ran.after R) (Ran.cause R) (Ran.left R) (Ran.spent R)
               (Ran.spends R) (Ran.world R) , gw)
      go k levω e (mpair f a) n σ ge (gf , ga) = evωR e f a n k σ gf ga
      -- ★ a ν: built, it is good (by `goodν`); observed, it runs by its
      -- goodness: no recursive call
      go k lunf e p n σ ge gp = (ran _ _ r-unf σ tt k ≤-refl refl refl , goodν p gp _)
      go k (lout {F}) e v n σ ge gv = case obs gv v (~-refl v) ds e k n σ of λ where
        (r , g) → (r , glo F (Ran.out r) g)
      go k (lconst v) e mone n σ ge gv = (ran _ _ r-const σ tt k ≤-refl refl refl , tt)
      go k (lop s) e x n σ ge gx = case runOp (opF s (toF (sdom s) (er x))) σ of λ where
        (opran t (inj₁ y) p σ₁ c ow) → (ran _ _ (r-op p) σ₁ tt k ≤-refl refl ow , goodF (scod s) y)
        (opran t (inj₂ halted) p σ₁ c ow) → (ran _ _ (r-opend p) σ₁ tt k ≤-refl refl ow , tt)
        (opran t (inj₂ exhausted) p σ₁ c ow) → (ran _ _ (r-opend p) σ₁ (cut-spent c) k ≤-refl (c , refl) ow , tt)
      go k (liter f φ) e a n σ ge ga = loop k (<-wellFounded k) f φ e a n σ ge ga

      -- ★ D493: a many-use body run OWNED, by its certificate: the pieces' runs, the
      -- body's subterms by `go` (so the recursion stays structural)
      goOwn : ∀ {X A B} (b : Tm Γ X A B) (o : Own b) (k : ℕ) (x : MV X) (a : MV A) (n : ℕ) (σ : WSt)
            → Good X x → Good A a → Ran⁺ ds (ownT o) mone (mpair x a) n k σ
      goOwn b o-bg k x a n σ gx ga = ownRanG (go k b x a n σ gx ga)
      goOwn _ o-ev k f a n σ gf ga = evωR mone f a n k σ gf ga
      goOwn _ (o-fst {f = f} o) k (mpair x₁ x₂) a n σ (g₁ , g₂) ga =
        seqR (parR (seqR (parR (ran _ _ r-id σ tt k ≤-refl refl refl , g₁)
                               (λ n₁ l₁ σ₁ → ran _ _ r-drop σ₁ tt l₁ ≤-refl refl (wtr-quiet (freeAll x₂) (ios-freeAll x₂)) , tt))
                         (λ { (mpair x₁′ mone) n₁ l₁ σ₁ (g₁′ , _) → ran _ _ r-ρ σ₁ tt l₁ ≤-refl refl refl , g₁′ }))
                   (λ n₁ l₁ σ₁ → ran _ _ r-id σ₁ tt l₁ ≤-refl refl refl , ga))
             (λ { (mpair x₁′ a′) n₁ l₁ σ₁ (g₁′ , ga′) → goOwn f o l₁ x₁′ a′ n₁ σ₁ g₁′ ga′ })
      goOwn _ (o-snd {f = f} o) k (mpair x₁ x₂) a n σ (g₁ , g₂) ga =
        seqR (parR (seqR (parR (ran _ _ r-drop σ tt k ≤-refl refl (wtr-quiet (freeAll x₁) (ios-freeAll x₁)) , tt)
                               (λ n₁ l₁ σ₁ → ran _ _ r-id σ₁ tt l₁ ≤-refl refl refl , g₂))
                         (λ { (mpair mone x₂′) n₁ l₁ σ₁ (_ , g₂′) → ran _ _ r-λ σ₁ tt l₁ ≤-refl refl refl , g₂′ }))
                   (λ n₁ l₁ σ₁ → ran _ _ r-id σ₁ tt l₁ ≤-refl refl refl , ga))
             (λ { (mpair x₂′ a′) n₁ l₁ σ₁ (g₂′ , ga′) → goOwn f o l₁ x₂′ a′ n₁ σ₁ g₂′ ga′ })
      goOwn _ (o-split {f = f} {g = g} p q) k (mpair x₁ x₂) a n σ (g₁ , g₂) ga =
        seqR (seqR (ran _ _ r-α σ tt k ≤-refl refl refl , (g₁ , (g₂ , ga)))
                   (λ { (mpair x₁′ (mpair x₂′ a′)) n₁ l₁ σ₁ (g₁′ , (g₂′ , ga′)) →
                          parR (ran _ _ r-id σ₁ tt l₁ ≤-refl refl refl , g₁′) (λ n₂ l₂ σ₂ → goOwn g q l₂ x₂′ a′ n₂ σ₂ g₂′ ga′) }))
             (λ { (mpair x₁′ b′) n₁ l₁ σ₁ (g₁′ , gb′) → goOwn f p l₁ x₁′ b′ n₁ σ₁ g₁′ gb′ })
      goOwn _ (o-case {f = f} {g = g} p q) k x (minl a) n σ gx ga =
        seqR (ran _ _ r-dist₁ σ tt k ≤-refl refl refl , (gx , ga)) (caseK f g p q)
      goOwn _ (o-case {f = f} {g = g} p q) k x (minr b) n σ gx gb =
        seqR (ran _ _ r-dist₂ σ tt k ≤-refl refl refl , (gx , gb)) (caseK f g p q)
      goOwn ((bfst f ⊗l bsnd g) ∘l s) (o-fork p q) k x a n σ gx ga =
        seqR (seqR (lendR gx (go k s x a n σ gx ga)) (λ u n₁ l₁ σ₁ gu → mixR u n₁ l₁ σ₁ gu))
             (λ { (mpair (mpair x₁ a₁) (mpair x₂ a₂)) n₁ l₁ σ₁ ((g₁ , h₁) , (g₂ , h₂)) →
                    parR (goOwn f p l₁ x₁ a₁ n₁ σ₁ g₁ h₁) (λ n₂ l₂ σ₂ → goOwn g q l₂ x₂ a₂ n₂ σ₂ g₂ h₂) })

      -- the arms, owned, after distributing
      caseK : ∀ {X A B C} (f : Tm Γ X A C) (g : Tm Γ X B C) (p : Own f) (q : Own g)
            → ∀ (u : MV ((X ⊗t A) ⊕t (X ⊗t B))) n₁ l₁ (σ₁ : WSt) → Good ((X ⊗t A) ⊕t (X ⊗t B)) u
            → Ran⁺ ds (lcase (ownT p) (ownT q)) mone u n₁ l₁ σ₁
      caseK f g p q (minl (mpair x a)) n₁ l₁ σ₁ (gx , ga) = case goOwn f p l₁ x a n₁ σ₁ gx ga of λ where
        (ran o t r σ₂ c l s sp wo , gw) → (ran o t (r-case₁ r) σ₂ c l s sp wo , gw)
      caseK f g p q (minr (mpair x b)) n₁ l₁ σ₁ (gx , gb) = case goOwn g q l₁ x b n₁ σ₁ gx gb of λ where
        (ran o t r σ₂ c l s sp wo , gw) → (ran o t (r-case₂ r) σ₂ c l s sp wo , gw)

      -- ★ the loop (D449): a round on the budget; a continuing round spends a unit of it, and
      -- with none left the run ends `exhausted` (as master's `approx`: a step per continuing
      -- round, counted along the whole run). The measure: the term, then the budget.
      loop : ∀ {E A B} (k : ℕ) → Acc _<_ k → (f : Tm Γ E A (B ⊕t A)) (φ : Blk f) (e : MV E) (a : MV A) (n : ℕ) (σ : WSt)
           → Good E e → Good A a → Ran⁺ ds (liter f φ) e a n k σ
      loop k ac f φ e a n σ ge ga = round k ac f φ e n ge (go k f e a n σ ge ga)

      round : ∀ {E A B} (k : ℕ) → Acc _<_ k → (f : Tm Γ E A (B ⊕t A)) (φ : Blk f) (e : MV E) {a : MV A} (n : ℕ)
            → Good E e → ∀ {σ} → Ran⁺ ds f e a n k σ → Ran⁺ ds (liter f φ) e a n k σ
      round k ac f φ e n ge (ran (gives (minl b) n′) t r σ₁ _ l s sp wo , gb) = (ran _ (t ++ []) (r-iter r (go-on done)) σ₁ tt l s sp (wtr-[] t wo) , gb)
      round k ac f φ e n ge (ran (stop y) t r σ₁ c l s sp wo , _) = (ran (stop y) (t ++ []) (r-iter r stopped) σ₁ c l s sp (wtr-[] t wo) , tt)
      round k ac f φ e n ge (ran (gives (minr a′) n₁) t₁ r σ₁ _ zero s sp wo , _) =
        (ran (stop exhausted) (t₁ ++ []) (r-iter r (go-on (again r-exh))) σ₁ out-of-fuel zero s (zero , sp , refl) (wtr-++ t₁ wo refl) , tt)
      round k (acc rs) f φ e n ge (ran (gives (minr a′) n₁) t₁ r σ₁ _ (suc l) s sp wo , ga′) =
        case loop l (rs s) f φ e a′ n₁ σ₁ ge ga′ of λ where
          (ran o t₂ rn σ₂ c l₂ s₂ sp₂ wo₂ , gw) →
            (ran o (t₁ ++ t₂) (r-iter r (go-on (again rn))) σ₂ c l₂ (≤-trans s₂ (≤-trans (n≤1+n l) s)) (suc l , sp , sp₂) (wtr-++ t₁ wo wo₂) , gw)

      -- the fold: free the node, fold its positions, run the algebra
      cata : ∀ {E A} (k : ℕ) F (alg : Tm Γ E (LF∙ F A) A) (e : MV E) (x : MV (μt F)) (n : ℕ) (σ : WSt)
           → Good E e → Ran⁺ ds (lcata F alg) e x n k σ
      cata k F alg e (mmu i v) n σ ge = case fold k F alg e F v n σ ge of λ where
        (ranM (stop y) t rm σ₁ c l s sp wo , _) → (ran (stop y) (free i ∷ (t ++ [])) (r-cata rm stopped) σ₁ c l s sp (wtr-[] t wo) , tt)
        (ranM (gives u n₁) t₁ rm σ₁ _ l₁ s₁ sp₁ wo₁ , gu) → case go l₁ alg e u n₁ σ₁ ge gu of λ where
          (ran o t₂ ra σ₂ c l₂ s₂ sp₂ wo₂ , gw) → (ran o (free i ∷ (t₁ ++ t₂)) (r-cata rm (go-on ra)) σ₂ c l₂ (≤-trans s₂ s₁) (l₁ , sp₁ , sp₂) (wtr-++ t₁ wo₁ wo₂) , gw)

      fold : ∀ {E A} (k : ℕ) F (alg : Tm Γ E (LF∙ F A) A) (e : MV E) G (x : MV (LF∙ G (μt F))) (n : ℕ) (σ : WSt)
           → Good E e → RanM⁺ ds F alg e G x n k σ
      fold k F alg e Idf x n σ ge = case cata k F alg e x n σ ge of λ where
        (ran o t r σ₁ c l s sp wo , gw) → (ranM o t (m-id r) σ₁ c l s sp wo , gw)
      fold k F alg e Kone x n σ ge = (ranM _ _ m-one σ tt k ≤-refl refl refl , tt)
      fold k F alg e Kzero () n σ ge
      fold k F alg e (Kb b) x n σ ge = (ranM _ _ m-b σ tt k ≤-refl refl refl , tt)
      fold k F alg e (Kμ G) x n σ ge = (ranM _ _ m-μ σ tt k ≤-refl refl refl , tt)
      fold k F alg e (G ⊕f H) (minl x) n σ ge = case fold k F alg e G x n σ ge of λ where
        (ranM (gives y n′) t r σ₁ _ l s sp wo , gy) → (ranM _ t (m-inl (fm-gives r)) σ₁ tt l s sp wo , gy)
        (ranM (stop w) t r σ₁ c l s sp wo , _) → (ranM (stop w) t (m-inl (fm-stop r)) σ₁ c l s sp wo , tt)
      fold k F alg e (G ⊕f H) (minr x) n σ ge = case fold k F alg e H x n σ ge of λ where
        (ranM (gives y n′) t r σ₁ _ l s sp wo , gy) → (ranM _ t (m-inr (fm-gives r)) σ₁ tt l s sp wo , gy)
        (ranM (stop w) t r σ₁ c l s sp wo , _) → (ranM (stop w) t (m-inr (fm-stop r)) σ₁ c l s sp wo , tt)
      fold k F alg e (G ⊗f H) (mpair x x′) n σ ge = case fold k F alg e G x n σ ge of λ where
        (ranM (stop w) t r σ₁ c l s sp wo , _) → (ranM (stop w) (t ++ []) (m-pair r stopped) σ₁ c l s sp (wtr-[] t wo) , tt)
        (ranM (gives y n₁) t₁ r σ₁ _ l₁ s₁ sp₁ wo₁ , gy) → case fold l₁ F alg e H x′ n₁ σ₁ ge of λ where
          (ranM (gives y′ n₂) t₂ r′ σ₂ _ l₂ s₂ sp₂ wo₂ , gy′) →
            (ranM _ (t₁ ++ t₂) (m-pair r (go-on (fm-gives r′))) σ₂ tt l₂ (≤-trans s₂ s₁) (l₁ , sp₁ , sp₂) (wtr-++ t₁ wo₁ wo₂) , (gy , gy′))
          (ranM (stop w) t₂ r′ σ₂ c l₂ s₂ sp₂ wo₂ , _) →
            (ranM (stop w) (t₁ ++ t₂) (m-pair r (go-on (fm-stop r′))) σ₂ c l₂ (≤-trans s₂ s₁) (l₁ , sp₁ , sp₂) (wtr-++ t₁ wo₁ wo₂) , tt)

  -- the runners of a table, built in order: each body runs over its prefix
  runners : ∀ {Γ} (ds : Defs Γ) → REnv ds
  runners ε            = ε
  runners (ds ▸ b1 b _)  = runners ds ▸ λ k x a n σ gx ga → Eval.go ds (runners ds) k b mone (mpair x a) n σ tt (gx , ga)
  runners (ds ▸ bω b _)  = runners ds ▸ λ k x a n σ gx ga → Eval.go ds (runners ds) k b x a n σ gx ga

  -- ★ TAIT'S LEMMA: every value is good (by induction on the value; a
  -- closure's environment is smaller than the closure)
  allGood : ∀ {A} (v : MV A) → Good A v
  allGood mone        = tt
  allGood (mpair a b) = (allGood a , allGood b)
  allGood (minl a)    = allGood a
  allGood (minr b)    = allGood b
  allGood (mbase x)   = tt
  allGood (mmu i v)   = tt
  allGood (mct x)     = allGood x
  allGood (mnu i p)   = goodν p (allGood p) i
  allGood (mfn i (c1 ds b γ) x) =
    λ x′ p k a n σ ga → Eval.go ds (runners ds) k b mone (mpair x′ a) n σ tt (good-~ p (allGood x) , ga)
  allGood (mfn i (cω ds b γ) x) =
    (λ x′ p k a n σ ga → Eval.go ds (runners ds) k b x′ a n σ (good-~ p (allGood x)) ga)
    , (λ x′ p k a n σ ga → Eval.go ds (runners ds) k (ownω b) mone (mpair x′ a) n σ tt (good-~ p (allGood x) , ga))
  allGood (mfn i (cωᶜ ds b₀ γ) x) =
    λ x′ p k a n σ ga → Eval.go ds (runners ds) k b₀ mone (mpair x′ a) n σ tt (good-~ p (allGood x) , ga)

  -- ★ A14: EVERY TERM HAS A RUN, from every lent value, input, counter and
  -- world state, with any number of loop rounds
  exec : ∀ {Γ} (ds : Defs Γ) {E A B} (k : ℕ) (f : Tm Γ E A B) (e : MV E) (v : MV A) (n : ℕ) (σ : WSt) → Ran ds f e v n k σ
  exec ds k f e v n σ = fst (Eval.go ds (runners ds) k f e v n σ (allGood e) (allGood v))

  -- ★ a world that always answers: a run it allows ends `exhausted` only
  -- because a loop ran out of rounds
  Answers : Set
  Answers = ∀ σ o x → answer σ o x ≡ nothing → ⊥

  fuel-only : Answers → (c : Spent) → c ≡ out-of-fuel
  fuel-only always out-of-fuel             = refl
  fuel-only always (unanswered σ o x eq)   = ⊥-elim (always σ o x eq)
