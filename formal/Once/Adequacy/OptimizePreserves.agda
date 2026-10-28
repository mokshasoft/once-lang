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

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

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
  RelS-embed; RelS-bind; relS-ret; RelS-iter∞; RelS-≈ˡ; RelS-≈ʳ; ≈∞-idˡ; ≈∞-idʳ; ≈∞-sym; ≈∞-reflB)
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

    -- `fst ∘ ⟨ p , h ⟩ → p`: `h` has no effect, so it returns at once
    fst-rel : ∀ {A B C} (f′ f : IR A (B II.* C)) (g : IR (B II.* C) B) → has-effect? f′ ≡ false
            → Rel f′ f → Rel fst g → Rel (optimize-fst f′) (g ∘ f)
    fst-rel f′ f g q rf rg r with pairView f′
    ... | is-pair p h =
      RelS-≈ˡ (≈∞-sym sym (pair-fst≈ (E p _) (quiet-now fmt ρ h (proj₂ (∨-split (has-effect? p) q)) _))) (RelS-bind (rf r) rg)
    ... | is-other-pair .f′ = RelS-bind (rf r) rg

    snd-rel : ∀ {A B C} (f′ f : IR A (B II.* C)) (g : IR (B II.* C) C) → has-effect? f′ ≡ false
            → Rel f′ f → Rel snd g → Rel (optimize-snd f′) (g ∘ f)
    snd-rel f′ f g q rf rg r with pairView f′
    ... | is-pair p h =
      RelS-≈ˡ (≈∞-sym sym (pair-snd≈ (quiet-now fmt ρ p (proj₁ (∨-split (has-effect? p) q)) _) (E h _))) (RelS-bind (rf r) rg)
    ... | is-other-pair .f′ = RelS-bind (rf r) rg

    -- `case h k ∘ inl → h` (and `inr`): returning, then continuing
    post-case-rel : ∀ {A B C D} (h : IR A C) (k : IR B C) (f′ f : IR D (A II.+ B)) (g : IR (A II.+ B) C)
                  → Rel f′ f → Rel (case h k) g → Rel (optimize-post-case h k f′) (g ∘ f)
    post-case-rel h k f′ f g rf rg r with coprodView f′
    ... | is-inl = RelS-≈ˡ (≈∞-sym sym (≈∞-idˡ _ (E (case h k)))) (RelS-bind (rf r) (λ {x} {y} q → rg {x} {y} q))
    ... | is-inr = RelS-≈ˡ (≈∞-sym sym (≈∞-idˡ _ (E (case h k)))) (RelS-bind (rf r) (λ {x} {y} q → rg {x} {y} q))
    ... | is-other-coprod .f′ = RelS-bind (rf r) (λ {x} {y} q → rg {x} {y} q)

    -- `g ∘ id → g`; `g ∘ initial` has no input
    compose-second-rel : ∀ {A B C} (g′ g : IR B C) (f′ f : IR A B) → Rel g′ g → Rel f′ f
                       → Rel (optimize-compose-second g′ f′) (g ∘ f)
    compose-second-rel g′ g f′ f rg rf r with composeSecondView f′
    ... | cs-id = RelS-≈ˡ (≈∞-sym sym (≈∞-idˡ _ (E g′))) (RelS-bind (rf r) rg)
    compose-second-rel g′ g .initial f rg rf {()} r | cs-initial
    ... | cs-other .f′ = RelS-bind (rf r) rg

  -- | `optimize-compose`: the drop rules read `has-effect?` of the OPTIMIZED
  -- `f′`; the original `f`'s run is related to `f′`'s, so it returns at once too.
  compose-rel : ∀ {A B C} (g′ g : IR B C) (f′ f : IR A B) → Rel g′ g → Rel f′ f → Rel (optimize-compose g′ f′) (g ∘ f)
  compose-rel g′ g f′ f rg rf {a} r with has-effect? f′ in q
  ... | true = RelS-bind (rf r) rg
  ... | false with composeFirstView g′
  ...   | cf-id = RelS-≈ˡ (≈∞-sym sym (≈∞-idʳ (E f′ a))) (RelS-bind (rf r) rg)
  ...   | cf-terminal =
    let nr = now-rel (rf r) (quiet-now fmt ρ f′ q a) in RelS-≈ʳ (now-seq (proj₁ nr) (E′ g)) (rg (proj₂ nr))
  ...   | cf-fst = fst-rel f′ f g q rf rg r
  ...   | cf-snd = snd-rel f′ f g q rf rg r
  ...   | cf-case h k = post-case-rel h k f′ f g rf (λ {x} {y} q → rg {x} {y} q) r
  ...   | cf-other .g′ = compose-second-rel g′ g f′ f rg rf r

  private
    both : ∀ {A B C} (f′ f : IR C A) (g′ g : IR C B) → Rel f′ f → Rel g′ g → Rel ⟨ f′ , g′ ⟩ ⟨ f , g ⟩
    both f′ f g′ g rf rg r = RelS-bind (rf r) (λ r₁ → RelS-bind (rg r) (λ r₂ → relS-ret (r₁ , r₂)))

  -- | `⟨ fst , snd ⟩ → id`
  pair-rel : ∀ {A B C} (f′ f : IR C A) (g′ g : IR C B) → Rel f′ f → Rel g′ g → Rel (optimize-pair f′ g′) ⟨ f , g ⟩
  pair-rel f′ f g′ g rf rg r with fstSndView f′ | fstSndView g′
  ... | fsv-fst       | fsv-snd       = retargetˡ refl (both fst f snd g rf rg r)
  ... | fsv-fst       | fsv-fst       = both fst f fst g rf rg r
  ... | fsv-fst       | fsv-other .g′ = both fst f g′ g rf rg r
  ... | fsv-snd       | fsv-fst       = both snd f fst g rf rg r
  ... | fsv-snd       | fsv-snd       = both snd f snd g rf rg r
  ... | fsv-snd       | fsv-other .g′ = both snd f g′ g rf rg r
  ... | fsv-other .f′ | fsv-fst       = both f′ f fst g rf rg r
  ... | fsv-other .f′ | fsv-snd       = both f′ f snd g rf rg r
  ... | fsv-other .f′ | fsv-other .g′ = both f′ f g′ g rf rg r

  private
    cases : ∀ {A B C} (f′ f : IR A C) (g′ g : IR B C) → Rel f′ f → Rel g′ g → Rel (case f′ g′) (case f g)
    cases f′ f g′ g rf rg {inj₁ _} {inj₁ _} r = rf r
    cases f′ f g′ g rf rg {inj₂ _} {inj₂ _} r = rg r
    cases f′ f g′ g rf rg {inj₁ _} {inj₂ _} ()
    cases f′ f g′ g rf rg {inj₂ _} {inj₁ _} ()

    ids : ∀ {A B} (f : IR A (A II.+ B)) (g : IR B (A II.+ B)) → Rel inl f → Rel inr g → Rel id (case f g)
    ids f g rf rg {inj₁ _} {inj₁ _} r = rf r
    ids f g rf rg {inj₂ _} {inj₂ _} r = rg r
    ids f g rf rg {inj₁ _} {inj₂ _} ()
    ids f g rf rg {inj₂ _} {inj₁ _} ()

  -- | `[ inl , inr ] → id`
  case-rel : ∀ {A B C} (f′ f : IR A C) (g′ g : IR B C) → Rel f′ f → Rel g′ g → Rel (optimize-case f′ g′) (case f g)
  case-rel f′ f g′ g rf rg {a} {a′} r with inlInrView f′ | inlInrView g′
  ... | iiv-inl       | iiv-inr       = ids f g rf rg {a} {a′} r
  ... | iiv-inl       | iiv-inl       = cases inl f inl g rf rg {a} {a′} r
  ... | iiv-inl       | iiv-other .g′ = cases inl f g′ g rf rg {a} {a′} r
  ... | iiv-inr       | iiv-inl       = cases inr f inl g rf rg {a} {a′} r
  ... | iiv-inr       | iiv-inr       = cases inr f inr g rf rg {a} {a′} r
  ... | iiv-inr       | iiv-other .g′ = cases inr f g′ g rf rg {a} {a′} r
  ... | iiv-other .f′ | iiv-inl       = cases f′ f inl g rf rg {a} {a′} r
  ... | iiv-other .f′ | iiv-inr       = cases f′ f inr g rf rg {a} {a′} r
  ... | iiv-other .f′ | iiv-other .g′ = cases f′ f g′ g rf rg {a} {a′} r

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
  struct-rel (inl {A} {B}) r with A ≟IRTy II.Void
  ... | yes refl = void-rel {x = initial} {y = inl} r
  ... | no _     = relS-ret r
  struct-rel (inr {A} {B}) r with B ≟IRTy II.Void
  ... | yes refl = void-rel {x = initial} {y = inr} r
  ... | no _     = relS-ret r
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
