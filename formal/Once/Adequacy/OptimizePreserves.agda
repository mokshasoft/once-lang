-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.OptimizePreserves — ONE OPTIMIZER PASS KEEPS THE RUN
-- (plan 0.39 A2).
--
-- `optimize-once` rewrites the IR by categorical laws. The IR means `T∞` runs,
-- compared step for step (`RelS`) under the value relation (`RelD`), so the
-- statement is a logical relation, as for the arith pass
-- (`Adequacy.RewritePreserves`): the optimized term at a call environment and
-- the original at a related one take related inputs to related runs.
--
-- Most rules keep the run as it is (identities, η, a case on a known
-- injection): the monad laws. Three drop a sub-term (`terminal ∘ f`,
-- `fst`/`snd ∘ ⟨ g , h ⟩`, a pure map into `Unit`); the optimizer drops one only
-- when `has-effect?` says it has none, and such a term returns at once
-- (`OptimizeQuiet.quiet-now`), so the run loses no step. The guard is read on
-- the OPTIMIZED sub-term; the original's run is related to it step for step,
-- so it returns at once too (`now-rel`).
------------------------------------------------------------------------

module Once.Adequacy.OptimizePreserves where

open import Data.Bool using (Bool; true; false; _∨_; not)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (isYes)

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR
open import Once.IRTy using (IRTy; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute; _≟IRTy_; fits-int; fits-float)
import Once.IRTy as II
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Type.DecEq using (_≟T_)
open import Once.Spec.Type using () renaming (Void to VoidT)
open import Once.IR.Semantics.Trace using (T; ret; call; halt; Interp; pureHalf; FFIAnswers; rel-halt)
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_; bindBlock; fmap∞; module T∞;
  TreeEq∞; module TreeEq∞; BlockEq; ret≈; call≈; halt≈; StepEq; done≈; next≈)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; cata-ev-algᴰ; module CallEnv)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; coerce-functor-D; coerce-functor⁻¹-D)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; s-next; s-call; s-halt;
  RelS-embed; RelS-bind; relS-ret; RelS-iter∞; RelS-≈ˡ; RelS-≈ʳ; ≈∞-idˡ; ≈∞-idʳ; ≈∞-sym; ≈∞-reflB; ≈∞-refl;
  ≈∞-bind; ≈∞-assoc; ≈∞-trans)
open import Once.Denotation.ValueRel
open import Once.Denotation.EvalRel using (fo-eq; RelS-now; RelEnv; sigop-rel; eval-rel)
open import Once.Denotation.ValueRelPER using (RelD-sym; RelD-trans; RelS-sym; RelS-trans)
open import Once.Denotation.Program using (IRFun; irFun; tableEnv; tableCalls; tableEnv-at; runIR; IRProgram; irProgram)
open Once.Denotation.Program.IRProgram using (main; table)
open Once.Denotation.Program.IRFun using (fbody; fcod; fdom; fname)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.Spec.Trace using (_≈ᵗ⟨_⟩_)
open import Once.Denotation.TraceTr using (trT∞; RelS-tr)
open import Once.IR.Semantics.StreamInf using (anaFᴵ; in-νᴵ; module νᴵ)
open import Once.IR.Semantics.FunctorMeaning using (translateF)
import Once.Type.Concrete as LW
import Once.Spec.Type as LW
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using () renaming (⟦_⟧F to ⟦_⟧F′)
open import Once.Semantics.Machine using (coerce-ν-out; coerce-ν-in)
open import Once.Optimize
open import Once.Adequacy.OptimizeQuiet using (Now; now; quiet-now)
open Once.Adequacy.OptimizeQuiet.Now using (value; is)

open T∞ using (force)
open TreeEq∞ using (force≈)
open RelS using (forceS)
open νᴵ using (forceᴵ)

------------------------------------------------------------------------
-- Runs that return at once
------------------------------------------------------------------------

-- | Lockstep: a run related to one that returns at once returns at once, with
-- a related value.
now-rel : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {m′ : T∞ Y} → RelS R m m′ → (n : Now m)
        → Σ (Now m′) (λ n′ → R (value n) (value n′))
now-rel {Y = Y} {R = R} {m′ = m′} h (now v e) = fin (go (forceS h) e)
  where
    go : ∀ {l l′} → RelSB R l l′ → l ≡ ret (inj₁ v) → Σ Y (λ y → (l′ ≡ ret (inj₁ y)) × R v y)
    go (s-ret {y = y} r) refl = y , refl , r
    go (s-next _) ()
    go (s-call _) ()
    go s-halt     ()
    fin : Σ Y (λ y → (force m′ ≡ ret (inj₁ y)) × R v y) → Σ (Now m′) (λ n′ → R v (value n′))
    fin (y , e′ , r) = now y e′ , r

private
  -- a bind on a run that returns at once is its continuation
  now-seq : ∀ {Y Z} {n : T∞ Y} (nn : Now n) (k : Y → T∞ Z) → TreeEq∞ _≡_ (n >>=∞ k) (k (value nn))
  force≈ (now-seq {n = n} (now v e) k) =
    subst (λ l → BlockEq (StepEq _≡_ (TreeEq∞ _≡_)) (bindBlock l k) (force (k v))) (sym e)
          (≈∞-reflB (λ _ → refl) (force (k v)))

  sym≡ : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  sym≡ = sym

  -- pairing a run with one that returns at once, then projecting: the run
  pair-fst≈  : ∀ {Y Z} (m : T∞ Y) {n : T∞ Z} (nn : Now n)
             → TreeEq∞ _≡_ (fmap∞ proj₁ (m >>=∞ λ b → n >>=∞ λ c → return∞ (b , c))) m
  pair-fst≈B : ∀ {Y Z} (l : T (Y ⊎ T∞ Y)) {n : T∞ Z} (nn : Now n)
             → BlockEq (StepEq _≡_ (TreeEq∞ _≡_))
                 (bindBlock (bindBlock l (λ b → n >>=∞ λ c → return∞ (b , c))) (λ p → return∞ (proj₁ p))) l
  force≈ (pair-fst≈ m nn) = pair-fst≈B (force m) nn
  pair-fst≈B (ret (inj₁ b)) {n} (now c e) =
    subst (λ l → BlockEq (StepEq _≡_ (TreeEq∞ _≡_))
                   (bindBlock (bindBlock l (λ c′ → return∞ (b , c′))) (λ p → return∞ (proj₁ p))) (ret (inj₁ b)))
          (sym e) (ret≈ (done≈ refl))
  pair-fst≈B (ret (inj₂ m)) nn = ret≈ (next≈ (pair-fst≈ m nn))
  pair-fst≈B (call o a k)   nn = call≈ (λ b → pair-fst≈B (k b) nn)
  pair-fst≈B (halt o a)     nn = halt≈

  -- …and the other way: the run that does not return at once
  ret-proj≈  : ∀ {Y Z} (b : Y) (n : T∞ Z)
             → TreeEq∞ _≡_ ((n >>=∞ λ c → return∞ (b , c)) >>=∞ λ p → return∞ (proj₂ p)) n
  ret-proj≈B : ∀ {Y Z} (b : Y) (l : T (Z ⊎ T∞ Z))
             → BlockEq (StepEq _≡_ (TreeEq∞ _≡_)) (bindBlock (bindBlock l (λ c → return∞ (b , c))) (λ p → return∞ (proj₂ p))) l
  force≈ (ret-proj≈ b n) = ret-proj≈B b (force n)
  ret-proj≈B b (ret (inj₁ c)) = ret≈ (done≈ refl)
  ret-proj≈B b (ret (inj₂ m)) = ret≈ (next≈ (ret-proj≈ b m))
  ret-proj≈B b (call o a k)   = call≈ (λ x → ret-proj≈B b (k x))
  ret-proj≈B b (halt o a)     = halt≈

  pair-snd≈ : ∀ {Y Z} {m : T∞ Y} (mm : Now m) (n : T∞ Z)
            → TreeEq∞ _≡_ (fmap∞ proj₂ (m >>=∞ λ b → n >>=∞ λ c → return∞ (b , c))) n
  force≈ (pair-snd≈ {m = m} (now b e) n) =
    subst (λ l → BlockEq (StepEq _≡_ (TreeEq∞ _≡_))
                   (bindBlock (bindBlock l (λ b′ → n >>=∞ λ c → return∞ (b′ , c))) (λ p → return∞ (proj₂ p))) (force n))
          (sym e) (force≈ (ret-proj≈ b n))

  ∨-split : ∀ a {b} → a ∨ b ≡ false → a ≡ false × b ≡ false
  ∨-split false e = refl , e
  ∨-split true  ()

------------------------------------------------------------------------
-- One pass, rule by rule
------------------------------------------------------------------------

module _ (fmt : TargetNum) {ρ ρ′ : CallEnv} (re : RelEnv fmt ρ ρ′) where
  private
    E  : ∀ {A B} → IR A B → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ
    E  = evalᴰ fmt ρ
    E′ : ∀ {A B} → IR A B → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ
    E′ = evalᴰ fmt ρ′

  -- | The optimized term (at `ρ`) and the original (at `ρ′`) take related
  -- inputs to related runs.
  Rel : ∀ {A B} → IR A B → IR A B → Set
  Rel {A} {B} x y = ∀ {a a′} → RelD ⌈ A ⌉ a a′ → RelS (RelD ⌈ B ⌉) (E x a) (E′ y a′)

  private
    -- the source has no value: nothing to relate
    void-rel : ∀ {B} {x y : IR II.Void B} → Rel x y
    void-rel {a = ()}

    ≡refl : ∀ {X : Set} (x : X) → x ≡ x
    ≡refl _ = refl

    -- `g ∘ id → g`; `g ∘ initial` has no input
    compose-second-rel : ∀ {A B C} (g′ g : IR B C) (f′ f : IR A B) → Rel g′ g → Rel f′ f
                       → (v : ComposeSecondView f′) → Rel (compose-second-aux g′ f′ v) (g ∘ f)
    compose-second-rel g′ g _ f rg rf cs-id r = RelS-≈ˡ (≈∞-sym sym (≈∞-idˡ _ (E g′))) (RelS-bind (rf r) rg)
    compose-second-rel g′ g _ f rg rf cs-initial {()} r
    compose-second-rel g′ g _ f rg rf (cs-other f′) r = RelS-bind (rf r) rg

    -- `fst ∘ ⟨ a , b ⟩ → a`, `b` quiet: `b` returns at once
    fst-pair-rel : ∀ {A B C} (a : IR A B) (b : IR A C) (f : IR A (B II.* C)) (g : IR (B II.* C) B) → Rel ⟨ a , b ⟩ f → Rel fst g
                 → ∀ q → has-effect? b ≡ q → Rel (fst-pair a b q) (g ∘ f)
    fst-pair-rel a b f g rf rg true  _ r = RelS-bind (rf r) rg
    fst-pair-rel a b f g rf rg false q r =
      RelS-≈ˡ (≈∞-sym sym (pair-fst≈ (E a _) (quiet-now fmt ρ b q _))) (RelS-bind (rf r) rg)

    -- …through a chain: `fst ∘ (⟨ a , b ⟩ ∘ k) → a ∘ k`
    fst-chain-pair-rel : ∀ {A X B C} (a : IR X B) (b : IR X C) (k : IR A X) (f : IR A (B II.* C)) (g : IR (B II.* C) B)
                       → Rel (⟨ a , b ⟩ ∘ k) f → Rel fst g
                       → ∀ q → has-effect? b ≡ q → Rel (fst-chain-pair a b k q) (g ∘ f)
    fst-chain-pair-rel a b k f g rf rg true  _ r = RelS-bind (rf r) rg
    fst-chain-pair-rel {B = B} {C} a b k f g rf rg false q {x} r =
      RelS-≈ˡ (≈∞-bind (≈∞-refl ≡refl (E k x)) pointwise)
        (RelS-≈ˡ (≈∞-sym sym (≈∞-assoc (E k x) (E ⟨ a , b ⟩) (E (fst {B} {C})))) (RelS-bind (rf r) rg))
      where
        pointwise : ∀ {y y′} → y ≡ y′ → TreeEq∞ _≡_ (E a y) (E ⟨ a , b ⟩ y′ >>=∞ E (fst {B} {C}))
        pointwise {y} refl = ≈∞-sym sym (pair-fst≈ (E a y) (quiet-now fmt ρ b q y))

    fst-chain-aux-rel : ∀ {A X B C} (p : IR X (B II.* C)) (k : IR A X) (f : IR A (B II.* C)) (g : IR (B II.* C) B)
                      → Rel (p ∘ k) f → Rel fst g → (v : PairView p) → Rel (fst-chain-aux p k v) (g ∘ f)
    fst-chain-aux-rel _ k f g rf rg (is-pair a b)      = fst-chain-pair-rel a b k f g rf rg _ refl
    fst-chain-aux-rel _ k f g rf rg (is-other-pair p) r = RelS-bind (rf r) rg

    fst-chain-rel : ∀ {A B C} (f′ f : IR A (B II.* C)) (g : IR (B II.* C) B) → Rel f′ f → Rel fst g
                  → (w : ChainView f′) → Rel (fst-chain f′ w) (g ∘ f)
    fst-chain-rel _ f g rf rg (is-comp p k)  = fst-chain-aux-rel p k f g rf rg (pairView p)
    fst-chain-rel _ f g rf rg (not-comp f′) = compose-second-rel fst g f′ f rg rf (composeSecondView f′)

    fst-rel : ∀ {A B C} (f′ f : IR A (B II.* C)) (g : IR (B II.* C) B) → Rel f′ f → Rel fst g
            → (v : PairView f′) → Rel (fst-aux f′ v) (g ∘ f)
    fst-rel _ f g rf rg (is-pair a b)      = fst-pair-rel a b f g rf rg _ refl
    fst-rel _ f g rf rg (is-other-pair f′) = fst-chain-rel f′ f g rf rg (chainView f′)

    -- `snd ∘ ⟨ a , b ⟩ → b`, `a` quiet (and through a chain)
    snd-pair-rel : ∀ {A B C} (a : IR A B) (b : IR A C) (f : IR A (B II.* C)) (g : IR (B II.* C) C) → Rel ⟨ a , b ⟩ f → Rel snd g
                 → ∀ q → has-effect? a ≡ q → Rel (snd-pair a b q) (g ∘ f)
    snd-pair-rel a b f g rf rg true  _ r = RelS-bind (rf r) rg
    snd-pair-rel a b f g rf rg false q r =
      RelS-≈ˡ (≈∞-sym sym (pair-snd≈ (quiet-now fmt ρ a q _) (E b _))) (RelS-bind (rf r) rg)

    snd-chain-pair-rel : ∀ {A X B C} (a : IR X B) (b : IR X C) (k : IR A X) (f : IR A (B II.* C)) (g : IR (B II.* C) C)
                       → Rel (⟨ a , b ⟩ ∘ k) f → Rel snd g
                       → ∀ q → has-effect? a ≡ q → Rel (snd-chain-pair a b k q) (g ∘ f)
    snd-chain-pair-rel a b k f g rf rg true  _ r = RelS-bind (rf r) rg
    snd-chain-pair-rel {B = B} {C} a b k f g rf rg false q {x} r =
      RelS-≈ˡ (≈∞-bind (≈∞-refl ≡refl (E k x)) pointwise)
        (RelS-≈ˡ (≈∞-sym sym (≈∞-assoc (E k x) (E ⟨ a , b ⟩) (E (snd {B} {C})))) (RelS-bind (rf r) rg))
      where
        pointwise : ∀ {y y′} → y ≡ y′ → TreeEq∞ _≡_ (E b y) (E ⟨ a , b ⟩ y′ >>=∞ E (snd {B} {C}))
        pointwise {y} refl = ≈∞-sym sym (pair-snd≈ (quiet-now fmt ρ a q y) (E b y))

    snd-chain-aux-rel : ∀ {A X B C} (p : IR X (B II.* C)) (k : IR A X) (f : IR A (B II.* C)) (g : IR (B II.* C) C)
                      → Rel (p ∘ k) f → Rel snd g → (v : PairView p) → Rel (snd-chain-aux p k v) (g ∘ f)
    snd-chain-aux-rel _ k f g rf rg (is-pair a b)      = snd-chain-pair-rel a b k f g rf rg _ refl
    snd-chain-aux-rel _ k f g rf rg (is-other-pair p) r = RelS-bind (rf r) rg

    snd-chain-rel : ∀ {A B C} (f′ f : IR A (B II.* C)) (g : IR (B II.* C) C) → Rel f′ f → Rel snd g
                  → (w : ChainView f′) → Rel (snd-chain f′ w) (g ∘ f)
    snd-chain-rel _ f g rf rg (is-comp p k)  = snd-chain-aux-rel p k f g rf rg (pairView p)
    snd-chain-rel _ f g rf rg (not-comp f′) = compose-second-rel snd g f′ f rg rf (composeSecondView f′)

    snd-rel : ∀ {A B C} (f′ f : IR A (B II.* C)) (g : IR (B II.* C) C) → Rel f′ f → Rel snd g
            → (v : PairView f′) → Rel (snd-aux f′ v) (g ∘ f)
    snd-rel _ f g rf rg (is-pair a b)      = snd-pair-rel a b f g rf rg _ refl
    snd-rel _ f g rf rg (is-other-pair f′) = snd-chain-rel f′ f g rf rg (chainView f′)

    -- `case h k ∘ inl → h` (and `inr`), also through a chain: returning, then continuing
    post-case-chain-aux-rel : ∀ {A B C D X} (h : IR A C) (k : IR B C) (p : IR X (A II.+ B)) (m : IR D X)
                            (f : IR D (A II.+ B)) (g : IR (A II.+ B) C) → Rel (p ∘ m) f → Rel (case h k) g
                            → (v : CoprodView p) → Rel (post-case-chain-aux h k p m v) (g ∘ f)
    post-case-chain-aux-rel {A} {B} h k _ m f g rf rg is-inl {x} r =
      RelS-≈ˡ (≈∞-bind (≈∞-refl ≡refl (E m x)) pointwise)
        (RelS-≈ˡ (≈∞-sym sym (≈∞-assoc (E m x) (E (inl {A} {B})) (E (case h k)))) (RelS-bind (rf r) (λ {u} {v} q → rg {u} {v} q)))
      where
        pointwise : ∀ {y y′} → y ≡ y′ → TreeEq∞ _≡_ (E h y) (E (inl {A} {B}) y′ >>=∞ E (case h k))
        pointwise {y} refl = ≈∞-sym sym (≈∞-idˡ _ (E (case h k)))
    post-case-chain-aux-rel {A} {B} h k _ m f g rf rg is-inr {x} r =
      RelS-≈ˡ (≈∞-bind (≈∞-refl ≡refl (E m x)) pointwise)
        (RelS-≈ˡ (≈∞-sym sym (≈∞-assoc (E m x) (E (inr {A} {B})) (E (case h k)))) (RelS-bind (rf r) (λ {u} {v} q → rg {u} {v} q)))
      where
        pointwise : ∀ {y y′} → y ≡ y′ → TreeEq∞ _≡_ (E k y) (E (inr {A} {B}) y′ >>=∞ E (case h k))
        pointwise {y} refl = ≈∞-sym sym (≈∞-idˡ _ (E (case h k)))
    post-case-chain-aux-rel h k _ m f g rf rg (is-other-coprod p) r = RelS-bind (rf r) (λ {u} {v} q → rg {u} {v} q)

    post-case-chain-rel : ∀ {A B C D} (h : IR A C) (k : IR B C) (f′ f : IR D (A II.+ B)) (g : IR (A II.+ B) C)
                        → Rel f′ f → Rel (case h k) g → (w : ChainView f′) → Rel (post-case-chain h k f′ w) (g ∘ f)
    post-case-chain-rel h k _ f g rf rg (is-comp p m)  = post-case-chain-aux-rel h k p m f g rf (λ {x} {y} q → rg {x} {y} q) (coprodView p)
    post-case-chain-rel h k _ f g rf rg (not-comp f′) =
      compose-second-rel (case h k) g f′ f (λ {u} {v} q → rg {u} {v} q) rf (composeSecondView f′)

    post-case-rel : ∀ {A B C D} (h : IR A C) (k : IR B C) (f′ f : IR D (A II.+ B)) (g : IR (A II.+ B) C)
                  → Rel f′ f → Rel (case h k) g → (v : CoprodView f′) → Rel (post-case-aux h k f′ v) (g ∘ f)
    post-case-rel h k _ f g rf rg is-inl r =
      RelS-≈ˡ (≈∞-sym sym (≈∞-idˡ _ (E (case h k)))) (RelS-bind (rf r) (λ {x} {y} q → rg {x} {y} q))
    post-case-rel h k _ f g rf rg is-inr r =
      RelS-≈ˡ (≈∞-sym sym (≈∞-idˡ _ (E (case h k)))) (RelS-bind (rf r) (λ {x} {y} q → rg {x} {y} q))
    post-case-rel h k _ f g rf rg (is-other-coprod f′) = post-case-chain-rel h k f′ f g rf (λ {x} {y} q → rg {x} {y} q) (chainView f′)

    -- `terminal ∘ f → terminal`, `f` quiet: the original `f`'s run is related to
    -- the optimized one's, so it returns at once too
    terminal-rel : ∀ {A B} (f′ f : IR A B) (g : IR B II.Unit) → Rel f′ f → Rel terminal g
                 → ∀ q → has-effect? f′ ≡ q → Rel (terminal-drop f′ q) (g ∘ f)
    terminal-rel f′ f g rf rg true  _ r = RelS-bind (rf r) rg
    terminal-rel f′ f g rf rg false q {a} r =
      let nr = now-rel (rf r) (quiet-now fmt ρ f′ q a) in RelS-≈ʳ (now-seq (proj₁ nr) (E′ g)) (rg (proj₂ nr))

    cong-k : ∀ {X Y : Set} (k : X → T∞ Y) {x y} → x ≡ y → TreeEq∞ _≡_ (k x) (k y)
    cong-k k {x} refl = ≈∞-refl ≡refl (k x)

    -- applying a closure built in place runs its body: the monad laws only
    clo-beta≈ : ∀ {Y A B : Set} (K : T∞ Y) (G : T∞ A) (F : Y × A → T∞ B)
      → TreeEq∞ _≡_ ((K >>=∞ λ e → G >>=∞ λ x → return∞ (e , x)) >>=∞ F)
                    (((K >>=∞ λ e → return∞ (λ b → F (e , b))) >>=∞ (λ c → G >>=∞ λ x → return∞ (c , x)))
                       >>=∞ λ p → proj₁ p (proj₂ p))
    clo-beta≈ {Y} {A} {B} K G F = ≈∞-trans trans lhs (≈∞-sym sym rhs)
      where
        clo : Y → A → T∞ B
        clo e b = F (e , b)
        P : (A → T∞ B) → T∞ ((A → T∞ B) × A)
        P c = G >>=∞ λ x → return∞ (c , x)
        AP : (A → T∞ B) × A → T∞ B
        AP p = proj₁ p (proj₂ p)
        M : T∞ B
        M = K >>=∞ λ e → G >>=∞ λ x → F (e , x)

        idlF : ∀ e {x x′} → x ≡ x′ → TreeEq∞ _≡_ (return∞ (e , x) >>=∞ F) (F (e , x′))
        idlF e {x} refl = ≈∞-idˡ (e , x) F
        innerL : ∀ {e e′} → e ≡ e′ → TreeEq∞ _≡_ ((G >>=∞ λ x → return∞ (e , x)) >>=∞ F) (G >>=∞ λ x → F (e′ , x))
        innerL {e} refl = ≈∞-trans trans (≈∞-assoc G (λ x → return∞ (e , x)) F) (≈∞-bind (≈∞-refl ≡refl G) (idlF e))
        lhs : TreeEq∞ _≡_ ((K >>=∞ λ e → G >>=∞ λ x → return∞ (e , x)) >>=∞ F) M
        lhs = ≈∞-trans trans (≈∞-assoc K (λ e → G >>=∞ λ x → return∞ (e , x)) F) (≈∞-bind (≈∞-refl ≡refl K) innerL)

        idlA : ∀ e {x x′} → x ≡ x′ → TreeEq∞ _≡_ (return∞ (clo e , x) >>=∞ AP) (clo e x′)
        idlA e {x} refl = ≈∞-idˡ (clo e , x) AP
        innerR : ∀ {e e′} → e ≡ e′ → TreeEq∞ _≡_ ((return∞ (clo e) >>=∞ P) >>=∞ AP) (G >>=∞ λ x → F (e′ , x))
        innerR {e} refl = ≈∞-trans trans (≈∞-bind (≈∞-idˡ (clo e) P) (cong-k AP))
                            (≈∞-trans trans (≈∞-assoc G (λ x → return∞ (clo e , x)) AP)
                              (≈∞-bind (≈∞-refl ≡refl G) (idlA e)))
        rhs : TreeEq∞ _≡_ (((K >>=∞ λ e → return∞ (clo e)) >>=∞ P) >>=∞ AP) M
        rhs = ≈∞-trans trans (≈∞-bind (≈∞-assoc K (λ e → return∞ (clo e)) P) (cong-k AP))
                (≈∞-trans trans (≈∞-assoc K (λ e → return∞ (clo e) >>=∞ P) AP) (≈∞-bind (≈∞-refl ≡refl K) innerR))

    head-eq : ∀ {X Y A B} (c : IR Y (A II.⇛ B)) (k : IR X Y) (x : IR X A) (v : CurryView c) (a : ⟦ X ⟧ᴰᴵ)
            → TreeEq∞ _≡_ (E (beta-head c k x v) a) (E (apply ∘ ⟨ c ∘ k , x ⟩) a)
    head-eq _ k x (is-curry f)       a = clo-beta≈ (E k a) (E x a) (E f)
    head-eq c k x (is-other-curry _) a = ≈∞-refl ≡refl (E (apply ∘ ⟨ c ∘ k , x ⟩) a)

    bare-eq : ∀ {X A B} (c : IR X (A II.⇛ B)) (x : IR X A) (v : CurryView c) (a : ⟦ X ⟧ᴰᴵ)
            → TreeEq∞ _≡_ (E (beta-bare c x v) a) (E (apply ∘ ⟨ c , x ⟩) a)
    bare-eq _ x (is-curry f) a =
      ≈∞-trans trans (clo-beta≈ (return∞ a) (E x a) (E f))
        (≈∞-bind (≈∞-bind (≈∞-idˡ a (λ e → return∞ (λ b → E f (e , b)))) (cong-k (λ c → E x a >>=∞ λ y → return∞ (c , y))))
                 (cong-k (λ p → proj₁ p (proj₂ p))))
    bare-eq c x (is-other-curry _) a = ≈∞-refl ≡refl (E (apply ∘ ⟨ c , x ⟩) a)

    closure-eq : ∀ {X A B} (c : IR X (A II.⇛ B)) (x : IR X A) (w : ChainView c) (a : ⟦ X ⟧ᴰᴵ)
               → TreeEq∞ _≡_ (E (closure-beta c x w) a) (E (apply ∘ ⟨ c , x ⟩) a)
    closure-eq _ x (is-comp h k) a = head-eq h k x (curryView h) a
    closure-eq _ x (not-comp c)  a = bare-eq c x (curryView c) a

    -- an equation at every input holds after a common first step
    via-chain : ∀ {X Z W V B} (m : IR X Z) (P : IR Z W) (f : IR W B) (Q : IR Z V) (g : IR V B) (a : ⟦ X ⟧ᴰᴵ)
              → (∀ y → TreeEq∞ _≡_ (E (f ∘ P) y) (E (g ∘ Q) y)) → TreeEq∞ _≡_ (E (f ∘ (P ∘ m)) a) (E (g ∘ (Q ∘ m)) a)
    via-chain m P f Q g a h =
      ≈∞-trans trans (≈∞-assoc (E m a) (E P) (E f))
        (≈∞-trans trans (≈∞-bind (≈∞-refl ≡refl (E m a)) pt) (≈∞-sym sym (≈∞-assoc (E m a) (E Q) (E g))))
      where
        pt : ∀ {y y′} → y ≡ y′ → TreeEq∞ _≡_ (E P y >>=∞ E f) (E Q y′ >>=∞ E g)
        pt {y} refl = h y

    head-chain-eq : ∀ {X Z Y A B} (c : IR Y (A II.⇛ B)) (k : IR Z Y) (x : IR Z A) (m : IR X Z) (v : CurryView c) (a : ⟦ X ⟧ᴰᴵ)
                  → TreeEq∞ _≡_ (E (beta-head-chain c k x m v) a) (E (apply ∘ (⟨ c ∘ k , x ⟩ ∘ m)) a)
    head-chain-eq _ k x m (is-curry f) a =
      via-chain m ⟨ k , x ⟩ f ⟨ curry f ∘ k , x ⟩ apply a (head-eq (curry f) k x (is-curry f))
    head-chain-eq c k x m (is-other-curry _) a = ≈∞-refl ≡refl (E (apply ∘ (⟨ c ∘ k , x ⟩ ∘ m)) a)

    bare-chain-eq : ∀ {X Z A B} (c : IR Z (A II.⇛ B)) (x : IR Z A) (m : IR X Z) (v : CurryView c) (a : ⟦ X ⟧ᴰᴵ)
                  → TreeEq∞ _≡_ (E (beta-bare-chain c x m v) a) (E (apply ∘ (⟨ c , x ⟩ ∘ m)) a)
    bare-chain-eq _ x m (is-curry f) a =
      via-chain m ⟨ id , x ⟩ f ⟨ curry f , x ⟩ apply a (bare-eq (curry f) x (is-curry f))
    bare-chain-eq c x m (is-other-curry _) a = ≈∞-refl ≡refl (E (apply ∘ (⟨ c , x ⟩ ∘ m)) a)

    closure-chain-eq : ∀ {X Z A B} (c : IR Z (A II.⇛ B)) (x : IR Z A) (m : IR X Z) (w : ChainView c) (a : ⟦ X ⟧ᴰᴵ)
                     → TreeEq∞ _≡_ (E (closure-beta-chain c x m w) a) (E (apply ∘ (⟨ c , x ⟩ ∘ m)) a)
    closure-chain-eq _ x m (is-comp h k) a = head-chain-eq h k x m (curryView h) a
    closure-chain-eq _ x m (not-comp c)  a = bare-chain-eq c x m (curryView c) a

    -- `apply ∘ ⟨ curry f ∘ k , x ⟩ → f ∘ ⟨ k , x ⟩` (and through a chain)
    apply-chain-aux-rel : ∀ {X Z A B} (p : IR Z ((A II.⇛ B) II.* A)) (m : IR X Z) (F : IR X ((A II.⇛ B) II.* A))
                          (g : IR ((A II.⇛ B) II.* A) B) → Rel (p ∘ m) F → Rel apply g
                        → (v : PairView p) → Rel (apply-chain-aux p m v) (g ∘ F)
    apply-chain-aux-rel _ m F g rF rg (is-pair c x) {a} r =
      RelS-≈ˡ (closure-chain-eq c x m (chainView c) a) (RelS-bind (rF r) rg)
    apply-chain-aux-rel _ m F g rF rg (is-other-pair p) r = RelS-bind (rF r) rg

    apply-chain-rel : ∀ {X A B} (F′ F : IR X ((A II.⇛ B) II.* A)) (g : IR ((A II.⇛ B) II.* A) B)
                    → Rel F′ F → Rel apply g → (w : ChainView F′) → Rel (apply-chain F′ w) (g ∘ F)
    apply-chain-rel _ F g rF rg (is-comp p m) = apply-chain-aux-rel p m F g rF rg (pairView p)
    apply-chain-rel _ F g rF rg (not-comp F′) = compose-second-rel apply g F′ F rg rF (composeSecondView F′)

    apply-rel : ∀ {X A B} (F′ F : IR X ((A II.⇛ B) II.* A)) (g : IR ((A II.⇛ B) II.* A) B)
              → Rel F′ F → Rel apply g → (v : PairView F′) → Rel (apply-aux F′ v) (g ∘ F)
    apply-rel _ F g rF rg (is-pair c x) {a} r = RelS-≈ˡ (closure-eq c x (chainView c) a) (RelS-bind (rF r) rg)
    apply-rel _ F g rF rg (is-other-pair F′) = apply-chain-rel F′ F g rF rg (chainView F′)

    compose-go : ∀ {A B C} (g′ g : IR B C) (f′ f : IR A B) → Rel g′ g → Rel f′ f
               → (v : ComposeFirstView g′) → Rel (compose-aux g′ f′ v) (g ∘ f)
    compose-go _ g f′ f rg rf cf-id {a} r = RelS-≈ˡ (≈∞-sym sym (≈∞-idʳ (E f′ a))) (RelS-bind (rf r) rg)
    compose-go _ g f′ f rg rf cf-terminal = terminal-rel f′ f g rf rg _ refl
    compose-go _ g f′ f rg rf cf-fst = fst-rel f′ f g rf rg (pairView f′)
    compose-go _ g f′ f rg rf cf-snd = snd-rel f′ f g rf rg (pairView f′)
    compose-go _ g f′ f rg rf (cf-case h k) =
      post-case-rel h k f′ f g rf (λ {x} {y} q → rg {x} {y} q) (coprodView f′)
    -- `(h ∘ k) ∘ f → h ∘ (k ∘ f)`: bind is associative
    compose-go _ g f′ f rg rf (cf-comp h k) {a} r = RelS-≈ˡ (≈∞-assoc (E f′ a) (E k) (E h)) (RelS-bind (rf r) rg)
    compose-go _ g f′ f rg rf cf-apply = apply-rel f′ f g rf rg (pairView f′)
    compose-go _ g f′ f rg rf (cf-other g′) = compose-second-rel g′ g f′ f rg rf (composeSecondView f′)

  -- | `optimize-compose`: each rule that drops a term reads `has-effect?` of the
  -- OPTIMIZED term it drops; the original's run is related to it, so it returns
  -- at once too.
  compose-rel : ∀ {A B C} (g′ g : IR B C) (f′ f : IR A B) → Rel g′ g → Rel f′ f → Rel (optimize-compose g′ f′) (g ∘ f)
  compose-rel g′ g f′ f rg rf = compose-go g′ g f′ f rg rf (composeFirstView g′)

  private
    both : ∀ {A B C} (f′ f : IR C A) (g′ g : IR C B) → Rel f′ f → Rel g′ g → Rel ⟨ f′ , g′ ⟩ ⟨ f , g ⟩
    both f′ f g′ g rf rg r = RelS-bind (rf r) (λ r₁ → RelS-bind (rg r) (λ r₂ → relS-ret (r₁ , r₂)))

  private
    not-true : ∀ {b} → not b ≡ true → b ≡ false
    not-true {false} _ = refl
    not-true {true}  ()

    -- a term standing for any map into `Unit` (quiet) returns at once, and
    -- its value is related to any other
    unit-now : ∀ {A B} (f′ f : IR A B) (d : Dec (B ≡ II.Unit)) → unit-like-aux f′ d ≡ true → Rel f′ f
             → ∀ {a a′} → RelD ⌈ A ⌉ a a′ → Σ (Now (E′ f a′)) (λ n → ∀ y → RelD ⌈ B ⌉ y (value n))
    unit-now f′ f (yes refl) e rf {a} r = proj₁ (now-rel (rf r) (quiet-now fmt ρ f′ (not-true e) a)) , λ _ → tt
    unit-now f′ f (no _)     () rf r

    -- the first projection up to `Unit` returns the first component at once
    fst-now : ∀ {A B} (f′ f : IR (A II.* B) A) (v : FstSndView f′) → fst-like-aux f′ v ≡ true → Rel f′ f
            → ∀ {p p′} → RelD ⌈ A II.* B ⌉ p p′ → Σ (Now (E′ f p′)) (λ n → RelD ⌈ A ⌉ (proj₁ p) (value n))
    fst-now {A} .fst f fsv-fst _ rf {p} r = now-rel (rf r) (now (proj₁ p) refl)
    fst-now {A} f′ f fsv-snd e rf {p} r =
      let u = unit-now f′ f (A ≟IRTy II.Unit) e rf r in proj₁ u , proj₂ u (proj₁ p)
    fst-now {A} f′ f (fsv-other _) e rf {p} r =
      let u = unit-now f′ f (A ≟IRTy II.Unit) e rf r in proj₁ u , proj₂ u (proj₁ p)

    snd-now : ∀ {A B} (g′ g : IR (A II.* B) B) (v : FstSndView g′) → snd-like-aux g′ v ≡ true → Rel g′ g
            → ∀ {p p′} → RelD ⌈ A II.* B ⌉ p p′ → Σ (Now (E′ g p′)) (λ n → RelD ⌈ B ⌉ (proj₂ p) (value n))
    snd-now {B = B} g′ g fsv-fst e rf {p} r =
      let u = unit-now g′ g (B ≟IRTy II.Unit) e rf r in proj₁ u , proj₂ u (proj₂ p)
    snd-now {B = B} .snd g fsv-snd _ rf {p} r = now-rel (rf r) (now (proj₂ p) refl)
    snd-now {B = B} g′ g (fsv-other _) e rf {p} r =
      let u = unit-now g′ g (B ≟IRTy II.Unit) e rf r in proj₁ u , proj₂ u (proj₂ p)

    eta-pair-rel : ∀ {A B} (f′ f : IR (A II.* B) A) (g′ g : IR (A II.* B) B) → Rel f′ f → Rel g′ g
                 → ∀ x y → fst-like-aux f′ (fstSndView f′) ≡ x → snd-like-aux g′ (fstSndView g′) ≡ y
                 → Rel (eta-pair f′ g′ x y) ⟨ f , g ⟩
    eta-pair-rel f′ f g′ g rf rg true true ex ey {p} {p′} r =
      let (nf , rx) = fst-now f′ f (fstSndView f′) ex rf r
          (ng , ry) = snd-now g′ g (fstSndView g′) ey rg r
      in RelS-≈ʳ (now-seq nf _) (RelS-≈ʳ (now-seq ng _) (relS-ret (rx , ry)))
    eta-pair-rel f′ f g′ g rf rg true  false _ _ = both f′ f g′ g rf rg
    eta-pair-rel f′ f g′ g rf rg false _     _ _ = both f′ f g′ g rf rg

    pair-go : ∀ {A B C} (f′ f : IR C A) (g′ g : IR C B) → Rel f′ f → Rel g′ g
            → (d : Dec (C ≡ A II.* B)) → Rel (pair-aux f′ g′ d) ⟨ f , g ⟩
    pair-go f′ f g′ g rf rg (yes refl) = eta-pair-rel f′ f g′ g rf rg _ _ refl refl
    pair-go f′ f g′ g rf rg (no _)     = both f′ f g′ g rf rg

    -- a projection path has no effect
    proj-quiet : ∀ {A B} (p : Proj A B) → has-effect? (proj-ir p) ≡ false
    proj-quiet p-id      = refl
    proj-quiet p-fst     = refl
    proj-quiet p-snd     = refl
    proj-quiet (p-∘ p q) rewrite proj-quiet p | proj-quiet q = refl

    -- a run that returns at once is the return of its value
    now-ret : ∀ {Y} {n : T∞ Y} (nn : Now n) → TreeEq∞ _≡_ n (return∞ (value nn))
    now-ret {n = n} nn = ≈∞-trans trans (≈∞-sym sym (≈∞-idʳ n)) (now-seq nn return∞)

    -- `⟨ fst ∘ h , snd ∘ h ⟩` runs `h` twice; `h` has no effect, so that is its value
    uniq-eq≈ : ∀ {C A B} (p : Proj C (A II.* B)) (a : ⟦ C ⟧ᴰᴵ)
             → TreeEq∞ _≡_ (E (proj-ir p) a) (E ⟨ fst ∘ proj-ir p , snd ∘ proj-ir p ⟩ a)
    uniq-eq≈ {A = A} {B} p a = ≈∞-trans trans (now-ret n) (≈∞-sym sym pair≈)
      where
        h = proj-ir p
        n = quiet-now fmt ρ h (proj-quiet p) a
        v = value n
        K₁ : ⟦ A ⟧ᴰᴵ → T∞ ⟦ A II.* B ⟧ᴰᴵ
        K₁ b = E (snd ∘ h) a >>=∞ λ c → return∞ (b , c)
        K₂ : ⟦ B ⟧ᴰᴵ → T∞ ⟦ A II.* B ⟧ᴰᴵ
        K₂ c = return∞ (proj₁ v , c)
        pair≈ : TreeEq∞ _≡_ (E ⟨ fst ∘ h , snd ∘ h ⟩ a) (return∞ v)
        pair≈ = ≈∞-trans trans (≈∞-bind (now-seq n (E (fst {A} {B}))) (cong-k K₁))
                  (≈∞-trans trans (≈∞-idˡ (proj₁ v) K₁)
                    (≈∞-trans trans (≈∞-bind (now-seq n (E (snd {A} {B}))) (cong-k K₂))
                      (≈∞-idˡ (proj₂ v) K₂)))

    pair-u-rel : ∀ {A B C} (f′ f : IR C A) (g′ g : IR C B) → Rel f′ f → Rel g′ g
               → (v : PairUniq f′ g′) → Rel (pair-u f′ g′ v) ⟨ f , g ⟩
    pair-u-rel _ f _ g rf rg (uniq p) {a} r =
      RelS-≈ˡ (uniq-eq≈ p a) (both (fst ∘ proj-ir p) f (snd ∘ proj-ir p) g rf rg r)
    pair-u-rel {A} {B} {C} f′ f g′ g rf rg (not-uniq _ _) = pair-go f′ f g′ g rf rg (C ≟IRTy (A II.* B))

  -- | `⟨ fst ∘ h , snd ∘ h ⟩ → h` (a projection path), and `⟨ fst , snd ⟩ → id` up to `Unit`
  pair-rel : ∀ {A B C} (f′ f : IR C A) (g′ g : IR C B) → Rel f′ f → Rel g′ g → Rel (optimize-pair f′ g′) ⟨ f , g ⟩
  pair-rel f′ f g′ g rf rg = pair-u-rel f′ f g′ g rf rg (pairUniq f′ g′)

  private
    cases : ∀ {A B C} (f′ f : IR A C) (g′ g : IR B C) → Rel f′ f → Rel g′ g → Rel (case f′ g′) (case f g)
    cases f′ f g′ g rf rg {inj₁ _} {inj₁ _} r = rf r
    cases f′ f g′ g rf rg {inj₂ _} {inj₂ _} r = rg r
    cases f′ f g′ g rf rg {inj₁ _} {inj₂ _} ()
    cases f′ f g′ g rf rg {inj₂ _} {inj₁ _} ()

    -- out of `Void` there is no input
    void-dec-rel : ∀ {A B} (f x : IR A B) (d : Dec (A ≡ II.Void)) → isYes d ≡ true → Rel x f
    void-dec-rel f x (yes refl) _ {()} r
    void-dec-rel f x (no _)     ()

    void-like-rel : ∀ {A B} (f′ f : IR A B) (x : IR A B) → void-like f′ ≡ true → Rel x f
    void-like-rel {A} f′ f x e = void-dec-rel f x (A ≟IRTy II.Void) e

    -- the injection up to `Void` is the injection
    inl-rel : ∀ {A B} (f′ f : IR A (A II.+ B)) (v : InlInrView f′) → inl-like-aux f′ v ≡ true → Rel f′ f → Rel inl f
    inl-rel .inl f iiv-inl       _ rf = rf
    inl-rel f′   f iiv-inr       e rf = void-like-rel f′ f inl e
    inl-rel f′   f (iiv-other _) e rf = void-like-rel f′ f inl e

    inr-rel : ∀ {A B} (g′ g : IR B (A II.+ B)) (v : InlInrView g′) → inr-like-aux g′ v ≡ true → Rel g′ g → Rel inr g
    inr-rel g′   g iiv-inl       e rg = void-like-rel g′ g inr e
    inr-rel .inr g iiv-inr       _ rg = rg
    inr-rel g′   g (iiv-other _) e rg = void-like-rel g′ g inr e

    ids : ∀ {A B} (f : IR A (A II.+ B)) (g : IR B (A II.+ B)) → Rel inl f → Rel inr g → Rel id (case f g)
    ids f g rf rg {inj₁ _} {inj₁ _} r = rf r
    ids f g rf rg {inj₂ _} {inj₂ _} r = rg r
    ids f g rf rg {inj₁ _} {inj₂ _} ()
    ids f g rf rg {inj₂ _} {inj₁ _} ()

    eta-case-rel : ∀ {A B} (f′ f : IR A (A II.+ B)) (g′ g : IR B (A II.+ B)) → Rel f′ f → Rel g′ g
                 → ∀ x y → inl-like-aux f′ (inlInrView f′) ≡ x → inr-like-aux g′ (inlInrView g′) ≡ y
                 → Rel (eta-case f′ g′ x y) (case f g)
    eta-case-rel f′ f g′ g rf rg true true ex ey {a} {a′} r =
      ids f g (inl-rel f′ f (inlInrView f′) ex rf) (inr-rel g′ g (inlInrView g′) ey rg) {a} {a′} r
    eta-case-rel f′ f g′ g rf rg true  false _ _ {a} {a′} r = cases f′ f g′ g rf rg {a} {a′} r
    eta-case-rel f′ f g′ g rf rg false _     _ _ {a} {a′} r = cases f′ f g′ g rf rg {a} {a′} r

    case-go : ∀ {A B C} (f′ f : IR A C) (g′ g : IR B C) → Rel f′ f → Rel g′ g
            → (d : Dec (C ≡ A II.+ B)) → Rel (case-aux f′ g′ d) (case f g)
    case-go f′ f g′ g rf rg (yes refl) {a} {a′} r = eta-case-rel f′ f g′ g rf rg _ _ refl refl {a} {a′} r
    case-go f′ f g′ g rf rg (no _)     {a} {a′} r = cases f′ f g′ g rf rg {a} {a′} r

  -- | `[ inl , inr ] → id`, up to `Void`
  case-rel : ∀ {A B C} (f′ f : IR A C) (g′ g : IR B C) → Rel f′ f → Rel g′ g → Rel (optimize-case f′ g′) (case f g)
  case-rel {A} {B} {C} f′ f g′ g rf rg {a} {a′} r = case-go f′ f g′ g rf rg (C ≟IRTy (A II.+ B)) {a} {a′} r

  -- | A map into `Unit` without an effect returns at once; `terminal` too.
  unit-rel : ∀ {A} (ir : IR A II.Unit) → has-effect? ir ≡ false → Rel terminal ir
  unit-rel ir q {a′ = a′} r = RelS-now refl (is (quiet-now fmt ρ′ ir q a′)) tt

  -- | One pass keeps the run.
  opt-once-rel : ∀ {A B} (ir : IR A B) → Rel (optimize-once ir) ir
  struct-rel   : ∀ {A B} (ir : IR A B) → Rel (optimize-once-structural ir) ir

  opt-once-rel {A} {B} ir r with B ≟IRTy II.Unit
  ... | yes refl with has-effect? ir in q
  ...   | false = unit-rel ir q r
  ...   | true  = struct-rel ir r
  opt-once-rel {A} {B} ir r | no _ with A ≟IRTy II.Void
  ...   | yes refl = void-rel {x = initial} {y = ir} r
  ...   | no _     = struct-rel ir r

  struct-rel id         r = relS-ret r
  struct-rel (g ∘ f)    r = compose-rel (optimize-once g) g (optimize-once f) f (opt-once-rel g) (opt-once-rel f) r
  struct-rel fst        r = relS-ret (proj₁ r)
  struct-rel snd        r = relS-ret (proj₂ r)
  struct-rel ⟨ f , g ⟩  r = pair-rel (optimize-once f) f (optimize-once g) g (opt-once-rel f) (opt-once-rel g) r
  struct-rel inl        r = relS-ret r
  struct-rel inr        r = relS-ret r
  struct-rel (case f g) {a} {a′} r = case-rel (optimize-once f) f (optimize-once g) g (opt-once-rel f) (opt-once-rel g) {a} {a′} r
  struct-rel terminal   r = relS-ret tt
  struct-rel initial {()} r
  struct-rel (curry f)  r = relS-ret (λ r′ → opt-once-rel f (r , r′))
  struct-rel apply      r = proj₁ r (proj₂ r)
  struct-rel (SigOp {A} si) r with A ≟T VoidT
  ... | yes refl = void-rel {x = initial} {y = SigOp si} r
  ... | no _     = sigop-rel fmt re si r
  struct-rel (const fits-int v)   r = relS-ret refl
  struct-rel (const fits-float v) r = relS-ret refl
  struct-rel (Call {A} {B} f) r = proj₁ re f A B r
  struct-rel (In {F} w) r rewrite fo-eq w r = relS-ret refl
  struct-rel (out-μ {F} w) {x} r rewrite r =
    relS-ret (RelD-subst (sym (⌈⟧TI-commute F (II.μ-type F)))
               (cfD⁻¹-rel (wf-⌈⌉ w) ⌈ II.μ-type F ⌉ (frefl (wf-⌈⌉ w) _)))
    where
      frefl : ∀ {G} (wg : (LW.WFFun LW.∅ₖ) G) (l : ⟦ G ⟧F′ ⟦ ⌈ II.μ-type F ⌉ ⟧ᴰ)
            → FRel (RelD ⌈ II.μ-type F ⌉) G l l
      frefl (LW.wf-K b) l = fr-K
      frefl LW.wf-Id l = fr-Id refl
      frefl (LW.wf-⊕ wf wg) (inj₁ l) = fr-inl (frefl wf l)
      frefl (LW.wf-⊕ wf wg) (inj₂ l) = fr-inr (frefl wg l)
      frefl (LW.wf-⊗ wf wg) (l , l′) = fr-pair (frefl wf l) (frefl wg l′)
  struct-rel (Cata {F} w {E₀} {C} alg) {e , x} {e′ , x′} (re′ , refl) =
    sem-cata-rel (wf-⌈⌉ w) (λ fr → alg-step fr) x
    where
      alg-step : ∀ {l₁ l₂} → FRel (RelS (RelD ⌈ C ⌉)) ⌈ F ⌉F l₁ l₂
               → RelS (RelD ⌈ C ⌉) (cata-ev-algᴰ fmt ρ w (optimize-once alg) e l₁) (cata-ev-algᴰ fmt ρ′ w alg e′ l₂)
      alg-step fr =
        RelS-bind (seqF∞-rel ⌈ F ⌉F fr)
          (λ fl → opt-once-rel alg (re′ , RelD-subst (sym (⌈⟧TI-commute F C)) (cfD⁻¹-rel (wf-⌈⌉ w) ⌈ C ⌉ fl)))
  struct-rel (Out {F} w) {v} {v′} r =
    RelS-fmap (StreamRel.forceR r)
      (λ l → RelD-subst (sym (⌈⟧TI-commute F (II.ν-type F)))
               (cfD⁻¹-rel (wf-⌈⌉ w) ⌈ II.ν-type F ⌉ (cμout-rel (wf-⌈⌉ w) (layer→srel (translateF Carrier Carrier ⌈ F ⌉F) l))))
  struct-rel (in-ν {F} w) r =
    relS-ret (in-rel (cμin-rel ⌈ F ⌉F (cfD-rel (wf-⌈⌉ w) ⌈ II.ν-type F ⌉ (RelD-subst (⌈⟧TI-commute F (II.ν-type F)) r))))
  struct-rel (Ana {F} w {E₀} {A₀} c) {e , s} {e′ , s′} (re′ , rs) =
    relS-ret (anaᴵ-rel (λ r → RelS-fmap (RelS-fmap (opt-once-rel c (re′ , r))
                                          (λ q → cfD-rel (wf-⌈⌉ w) ⌈ A₀ ⌉ (RelD-subst (⌈⟧TI-commute F A₀) q)))
                                        (cμin-rel ⌈ F ⌉F))
                       rs)
  struct-rel (Iter {E₀} {A₀} {B₀} b) {e , s} {e′ , s′} (re′ , rs) =
    RelS-iter∞ {RB = RelD ⌈ B₀ ⌉} {S = RelD ⌈ B₀ II.+ A₀ ⌉}
               {f = λ a → E (optimize-once b) (e , a)} {f′ = λ a → E′ b (e′ , a)}
               (λ r → r) (λ r → opt-once-rel b (re′ , r)) (λ ()) (λ ()) rs

------------------------------------------------------------------------
-- Ten passes: each relates its output to its input, and the relation
-- composes (`ValueRelPER`).
------------------------------------------------------------------------

module _ (fmt : TargetNum) where

  -- the right-hand environment is related to itself
  env-self : ∀ {ρ ρ′} → RelEnv fmt ρ ρ′ → RelEnv fmt ρ′ ρ′
  env-self (calls , ffi) =
    (λ f A B {a} {a′} r →
       RelS-trans (RelD-trans ⌈ B ⌉)
         (RelS-sym (RelD-sym ⌈ B ⌉) (calls f A B (RelD-sym ⌈ A ⌉ r)))
         (calls f A B (RelD-trans ⌈ A ⌉ (RelD-sym ⌈ A ⌉ r) r)))
    , refl

  -- | `optimize-n n` keeps the run.
  opt-n-rel : ∀ n {ρ ρ′} (re : RelEnv fmt ρ ρ′) {A B} (ir : IR A B) → Rel fmt re (optimize-n n ir) ir
  opt-n-rel zero    re ir r = eval-rel fmt re ir r
  opt-n-rel (suc n) re {A} {B} ir {a} {a′} r =
    RelS-trans (RelD-trans ⌈ B ⌉)
      (opt-n-rel n re (optimize-once ir) r)
      (opt-once-rel fmt (env-self re) ir (RelD-trans ⌈ A ⌉ (RelD-sym ⌈ A ⌉ r) r))

  -- | The optimizer keeps the run.
  optimize-rel : ∀ {ρ ρ′} (re : RelEnv fmt ρ ρ′) {A B} (ir : IR A B) → Rel fmt re (optimize ir) ir
  optimize-rel = opt-n-rel 10

------------------------------------------------------------------------
-- Tables related entry by entry: the same names and types, and bodies that
-- take related inputs to related runs at any related environments. Two
-- programs with related tables and the same `main` have the same trace.
------------------------------------------------------------------------

module _ (fmt : TargetNum) where

  data EntryRel : IRFun → IRFun → Set where
    e-rel : ∀ n D C {b′ b : IR D C} → (∀ {ρ ρ′} (re : RelEnv fmt ρ ρ′) → Rel fmt re b′ b)
          → EntryRel (irFun n D C b′) (irFun n D C b)

  data TblRel : List IRFun → List IRFun → Set where
    t-nil  : TblRel [] []
    t-cons : ∀ {e′ e t′ t} → EntryRel e′ e → TblRel t′ t → TblRel (e′ ∷ t′) (e ∷ t)

module _ (fmt : TargetNum) (φ : FFIAnswers) where

  table-rel : ∀ {t′ t} → TblRel fmt t′ t → RelEnv fmt (tableEnv fmt φ t′) (tableEnv fmt φ t)
  calls-rel : ∀ {t′ t} → TblRel fmt t′ t → ∀ f (A B : IRTy) {a a′} → RelD ⌈ A ⌉ a a′
            → RelS (RelD ⌈ B ⌉) (tableCalls fmt φ t′ f A B a) (tableCalls fmt φ t f A B a′)
  table-rel tr = calls-rel tr , refl

  calls-rel t-nil f A B r = RelS-embed rel-halt
  calls-rel (t-cons {t′ = es′} {t = es} (e-rel n D C {b′} {b} rb) tr) f A B r = at (n ≟ᶜ f) (D ≟IRTy A) (C ≟IRTy B) r
    where
      hit : ∀ {A B} (p : D ≡ A) (q : C ≡ B) {a a′} → RelD ⌈ A ⌉ a a′
          → RelS (RelD ⌈ B ⌉)
              (subst (λ Y → T∞ ⟦ Y ⟧ᴰᴵ) q (evalᴰ fmt (tableEnv fmt φ es′) b′ (subst ⟦_⟧ᴰᴵ (sym p) a)))
              (subst (λ Y → T∞ ⟦ Y ⟧ᴰᴵ) q (evalᴰ fmt (tableEnv fmt φ es) b (subst ⟦_⟧ᴰᴵ (sym p) a′)))
      hit refl refl r = rb (table-rel tr) r
      at : ∀ d₁ d₂ d₃ {a a′} → RelD ⌈ A ⌉ a a′
         → RelS (RelD ⌈ B ⌉) (tableEnv-at fmt φ (irFun n D C b′) es′ f A B d₁ d₂ d₃ a)
                              (tableEnv-at fmt φ (irFun n D C b) es f A B d₁ d₂ d₃ a′)
      at (yes _) (yes p) (yes q) r = hit p q r
      at (yes _) (yes _) (no _)  r = calls-rel tr f A B r
      at (yes _) (no _)  _       r = calls-rel tr f A B r
      at (no _)  _       _       r = calls-rel tr f A B r

  program-rel : ∀ {t′ t} → TblRel fmt t′ t → (main : IR II.Unit II.Unit)
              → RelS (RelD ⌈ II.Unit ⌉) (runIR fmt φ (irProgram t′ main)) (runIR fmt φ (irProgram t main))
  program-rel tr main = eval-rel fmt (table-rel tr) main tt

-- | Programs with related tables and the same `main` have the same TRACE.
table-trace : ∀ (fmt : TargetNum) (ι : Interp) {t′ t} → TblRel fmt t′ t → (main : IR II.Unit II.Unit)
            → trT∞ ι [] (runIR fmt (pureHalf ι) (irProgram t′ main)) ≈ᵗ⟨ _≡_ ⟩ trT∞ ι [] (runIR fmt (pureHalf ι) (irProgram t main))
table-trace fmt ι tr main = RelS-tr ι [] (program-rel fmt (pureHalf ι) tr main)
