-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.BudgetSound — plan 0.146 B1.5 (D429, D430): ★ A RUN IN THE
-- INTERPRETATION'S WORLD SHOWS WHAT THE MEANING SHOWS AT ITS BUDGET.
--
-- `Events.sound` (a run is a path through the term's meaning, cut anywhere)
-- at a budget of loop rounds: a run that spends its budget as `Spends` says
-- (a continuing round a unit; the cut only where none is left), whose calls
-- the world `Wι` answered (`Total.WTr`: the interpretation's answers, its
-- state the history), and which met no unanswered call (`UnCut`), has exactly
-- the events and end of master's budgeted run of the meaning
-- (`Trace.run ι h (approx k …)`, as the apex observes it). Clause for clause
-- as `sound`, master's budget lemmas (`Approx.run-approx-bind/iter/embed`) in
-- place of the path lemmas.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc; map-++)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Event using (SigOpEvent)
import Once.IR.Semantics.Trace as TM
open import Once.IR.Semantics.Trace using (FFIAnswers; Interp; callAnswer; callEvent; haltEvent; consE; appE)
open import Once.Denotation.Approx using (Ap; done; cut; approx; approxBlock; tagRun)
import Once.Res
open import Once.LinCore.Flat using (Base)
open import Once.LinCore.Free using (Weave; w-[]; w-run; w-tmp)

module Once.LinCore.BudgetSound
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Bisim fmt ans using (_≈_; Bl; block≈; ≈ret; ≈step; ≈call; ≈halt)
open import Once.LinCore.Total fmt ans bw using (World; WTr)
open import Once.LinCore.Spends fmt ans bw using (UnCut; UnCutM)
open import Once.LinCore.StepOp fmt ans bw using (evsOf; ioEvent)

module W (ι : Interp) where

  -- ★ the world the interpretation is: its state the history, its answer the interpretation's at it
  Wι : World
  Wι = record { WSt = List SigOpEvent
              ; answer = λ h o a → Data.Maybe.map (λ b → b , (h ++ callEvent o a ∷ [])) (callAnswer ι h o a) }

  -- the events a trace shows the log, over two traces
  evsOf-++ : ∀ t₁ t₂ → evsOf (t₁ ++ t₂) ≡ evsOf t₁ ++ evsOf t₂
  evsOf-++ t₁ t₂ = trans (cong (map ioEvent) (ios-++ t₁ t₂)) (map-++ ioEvent (ios t₁) (ios t₂))

  -- the world answered a call as the interpretation does at that history
  answered : ∀ {h h₁ : List SigOpEvent} {o : CallOp} {a y}
           → World.answer Wι h o a ≡ just (y , h₁) → (callAnswer ι h o a ≡ just y) × (h₁ ≡ h ++ callEvent o a ∷ [])
  answered {h} {h₁} {o} {a} {y} e = at (callAnswer ι h o a) e
    where
      at : ∀ mb → Data.Maybe.map (λ b → b , (h ++ callEvent o a ∷ [])) mb ≡ just (y , h₁)
         → (mb ≡ just y) × (h₁ ≡ h ++ callEvent o a ∷ [])
      at (just b) refl = refl , refl

  -- a trace with no call: the world as it was
  wtr-quiet-eq : ∀ {h h′} t → ios t ≡ [] → WTr Wι h t h′ → h′ ≡ h
  wtr-quiet-eq []             q refl = refl
  wtr-quiet-eq (alloc _ ∷ t)  q w    = wtr-quiet-eq t q w
  wtr-quiet-eq (free _ ∷ t)   q w    = wtr-quiet-eq t q w
  wtr-quiet-eq (peek _ ∷ t)   q w    = wtr-quiet-eq t q w
  wtr-quiet-eq (io _ _ _ ∷ t) () w
  wtr-quiet-eq (stp _ _ ∷ t)  () w
  wtr-quiet-eq (tmp _ ∷ t)    q w    = wtr-quiet-eq t q w

  -- two traces, one after the other: the world between them
  wtr-split : ∀ {h h″} t₁ {t₂} → WTr Wι h (t₁ ++ t₂) h″ → Σ (List SigOpEvent) λ h′ → WTr Wι h t₁ h′ × WTr Wι h′ t₂ h″
  wtr-split {h} []              w = h , refl , w
  wtr-split (alloc _ ∷ t₁)      w = wtr-split t₁ w
  wtr-split (free _ ∷ t₁)       w = wtr-split t₁ w
  wtr-split (peek _ ∷ t₁)       w = wtr-split t₁ w
  wtr-split (io o a y ∷ t₁)     (h₁ , e , w) = case-of (wtr-split t₁ w)
    where
      case-of : _ → _
      case-of (h′ , w₁ , w₂) = h′ , (h₁ , e , w₁) , w₂
  wtr-split (stp _ _ ∷ t₁)      w = wtr-split t₁ w
  wtr-split (tmp _ ∷ t₁)        w = wtr-split t₁ w

  -- temporaries leave the world as it is
  wtr-weave : ∀ {h h′ t ts t′} → Weave tmp t ts t′ → WTr Wι h t′ h′ → WTr Wι h t h′
  wtr-weave w-[]                       w = w
  wtr-weave (w-run {x = alloc _} wv)   w = wtr-weave wv w
  wtr-weave (w-run {x = free _} wv)    w = wtr-weave wv w
  wtr-weave (w-run {x = peek _} wv)    w = wtr-weave wv w
  wtr-weave (w-run {x = io o a y} wv)  (h₁ , e , w) = h₁ , e , wtr-weave wv w
  wtr-weave (w-run {x = stp _ _} wv)   w = wtr-weave wv w
  wtr-weave (w-run {x = tmp _} wv)     w = wtr-weave wv w
  wtr-weave (w-tmp wv)                 w = wtr-weave wv w

  -- how an outcome is observed at a budget: its value and the budget left, a halt, or the cut
  stopAp : ∀ {X : Set} → Why → Once.Res.Res (Ap X)
  stopAp halted    = Once.Res.stopped
  stopAp exhausted = Once.Res.returns cut

  outAp : ∀ {B} → Outcome B → ℕ → Once.Res.Res (Ap ⟦ B ⟧)
  outAp (gives w _) l = Once.Res.returns (done (er w) l)
  outAp (stop y)    l = stopAp y

  -- a run that gave a value: the world after it is the history and its events
  GivesHist : ∀ {B} → Outcome B → List SigOpEvent → Trace → List SigOpEvent → Set
  GivesHist (gives _ _) h t h′ = h′ ≡ h ++ evsOf t
  GivesHist (stop _)    h t h′ = ⊤

  -- ★ bisimilar computations, at every budget, run alike
  mutual
    blk-run : ∀ {X : Set} r {b b′ : TM.T (X ⊎ T∞ X)} → Bl b b′ → ∀ h → TM.run ι h (approxBlock r b) ≡ TM.run ι h (approxBlock r b′)
    blk-run r       ≈ret        h = refl
    blk-run zero    (≈step q)   h = refl
    blk-run (suc r) (≈step q)   h = run-≈ r q h
    blk-run r       (≈call {s = o} {x = a} f) h = call-cong h o a (callAnswer ι h o a) (λ b → blk-run r (f b) (h ++ callEvent o a ∷ []))
    blk-run r       ≈halt       h = refl

    run-≈ : ∀ {X : Set} r {m m′ : T∞ X} → m ≈ m′ → ∀ h → TM.run ι h (approx r m) ≡ TM.run ι h (approx r m′)
    run-≈ r q h = blk-run r (block≈ q) h

    call-cong : ∀ {X : Set} h (o : CallOp) a {K K′ : _ → TM.T X} (mb : Maybe _)
              → (∀ b → TM.run ι (h ++ callEvent o a ∷ []) (K b) ≡ TM.run ι (h ++ callEvent o a ∷ []) (K′ b))
              → TM.run-call ι h o a K mb ≡ TM.run-call ι h o a K′ mb
    call-cong h o a (just b) e = cong (consE (callEvent o a)) (e b)
    call-cong h o a nothing  e = refl

  -- the core's finite blocks, embedded, run as master's (`Approx.run-approx-embed`, at `emb`)
  mutual
    run-embB : ∀ {X : Set} r (b : TM.T X) h → TM.run ι h (approxBlock r (embB b)) ≡ tagRun r (TM.run ι h b)
    run-embB r (TM.ret x)      h = refl
    run-embB r (TM.halt o a)   h = refl
    run-embB r (TM.call o a k) h = run-emb-call r o a k h (callAnswer ι h o a)

    run-emb-call : ∀ {X : Set} r (o : CallOp) a (k : _ → TM.T X) h (mb : Maybe _)
                 → TM.run-call ι h o a (λ b → approxBlock r (embB (k b))) mb ≡ tagRun r (TM.run-call ι h o a k mb)
    run-emb-call r o a k h (just b) = cong (consE (callEvent o a)) (run-embB r (k b) (h ++ callEvent o a ∷ []))
    run-emb-call r o a k h nothing  = refl

  -- a mapped block runs as the block, its result mapped
  mutual
    run-fmapT : ∀ {X Y : Set} (g : X → Y) (t : TM.T X) h
              → TM.run ι h (fmapT g t) ≡ (proj₁ (TM.run ι h t) , Once.Res.mapRes g (proj₂ (TM.run ι h t)))
    run-fmapT g (TM.ret x)      h = refl
    run-fmapT g (TM.halt o a)   h = refl
    run-fmapT g (TM.call o a k) h = run-fmap-call g o a k h (callAnswer ι h o a)

    run-fmap-call : ∀ {X Y : Set} (g : X → Y) (o : CallOp) a (k : _ → TM.T X) h (mb : Maybe _)
                  → TM.run-call ι h o a (λ b → fmapT g (k b)) mb
                    ≡ (proj₁ (TM.run-call ι h o a k mb) , Once.Res.mapRes g (proj₂ (TM.run-call ι h o a k mb)))
    run-fmap-call g o a k h (just b) = cong (consE (callEvent o a)) (run-fmapT g (k b) (h ++ callEvent o a ∷ []))
    run-fmap-call g o a k h nothing  = refl

  -- ★ an op's contract path, answered by the world: master's run of the block
  op-ret-run : ∀ {X : Set} {t : TM.T X} {tr x h h′} → OpPath t tr (inj₁ x) → WTr Wι h tr h′
             → (TM.run ι h t ≡ (evsOf tr , Once.Res.returns x)) × (h′ ≡ h ++ evsOf tr)
  op-ret-run {h = h} p-ret w = refl , trans w (sym (++-identityʳ h))
  op-ret-run {h = h} (p-call {o = o} {a = a} {k = k} {y = y} {t = tr′} p) (h₁ , e , w) = at (answered e) (op-ret-run p w)
    where
      at : _ → _ → _
      at (ca , refl) (e₁ , e₂) =
        trans (cong (TM.run-call ι h o a k) ca) (cong (consE (callEvent o a)) e₁) ,
        trans e₂ (++-assoc h (callEvent o a ∷ []) (evsOf tr′))

  op-halt-run : ∀ {X : Set} {t : TM.T X} {tr h h′} → OpPath t tr (inj₂ halted) → WTr Wι h tr h′
              → TM.run ι h t ≡ (evsOf tr , Once.Res.stopped)
  op-halt-run {h = h} (p-call {o = o} {a = a} {k = k} p) (h₁ , e , w) = at (answered e) (op-halt-run p w)
    where
      at : _ → _ → _
      at (ca , refl) e₁ = trans (cong (TM.run-call ι h o a k) ca) (cong (consE (callEvent o a)) e₁)
  op-halt-run p-halt w = refl

------------------------------------------------------------------------
-- ★★ THE BUDGETED SOUNDNESS
------------------------------------------------------------------------

module S (ι : Interp) where
  open W ι
  open import Once.Denotation.Approx using (thenAp; thenIter; run-approx-bind; run-approx-iter)
  open import Once.LinCore.Spends fmt ans bw using (module Budget)
  open import Once.LinCore.Total fmt ans bw using (CutOp)
  open Budget (λ {s} {x} {t} p → CutOp Wι {s} {x} {t} p) using (Spends; SpendsM; Again)
  open import Once.LinCore.Grade fmt ans using (blk-coh; obs-coh)

  private
    evs-q : ∀ t → ios t ≡ [] → evsOf t ≡ []
    evs-q t q = cong (map ioEvent) q

    evs-[] : ∀ t → evsOf (t ++ []) ≡ evsOf t
    evs-[] t = cong evsOf (++-identityʳ t)

    -- a value, at the budget, as a step that shows nothing
    leaf : ∀ {X : Set} {x y : X} {l k h h′} (t : Trace) → x ≡ y → l ≡ k → ios t ≡ [] → WTr Wι h t h′
         → (TM.run ι h (approx k (return∞ x)) ≡ (evsOf t , Once.Res.returns (done y l))) × (h′ ≡ h ++ evsOf t)
    leaf {h = h} t refl refl q w =
      cong (λ z → (z , Once.Res.returns (done _ _))) (sym (evs-q t q)) ,
      trans (wtr-quiet-eq t q w) (sym (trans (cong (h ++_) (evs-q t q)) (++-identityʳ h)))

    then-stop : ∀ {X Y : Set} h (y : Why) es (g : X → T∞ Y) → thenAp ι h es (stopAp y) g ≡ (es , stopAp y)
    then-stop h halted    es g = refl
    then-stop h exhausted es g = refl

    iter-stop : ∀ {A B : Set} h (y : Why) es (g : A → T∞ (B ⊎ A)) → thenIter ι h es (stopAp y) g ≡ (es , stopAp y)
    iter-stop h halted    es g = refl
    iter-stop h exhausted es g = refl

    hist-cong : ∀ {B} (o : Outcome B) {h h′ t t′} → evsOf t ≡ evsOf t′ → GivesHist o h t h′ → GivesHist o h t′ h′
    hist-cong (gives _ _) {h} e hi = trans hi (cong (h ++_) e)
    hist-cong (stop _)    e hi = tt

    hist-seq : ∀ {B} (o : Outcome B) {h h₁ h′} t₁ t₂ → h₁ ≡ h ++ evsOf t₁ → GivesHist o h₁ t₂ h′ → GivesHist o h (t₁ ++ t₂) h′
    hist-seq (gives _ _) {h} t₁ t₂ e₁ e₂ =
      trans e₂ (trans (cong (_++ evsOf t₂) e₁) (trans (++-assoc h (evsOf t₁) (evsOf t₂)) (cong (h ++_) (sym (evsOf-++ t₁ t₂)))))
    hist-seq (stop _) t₁ t₂ e₁ e₂ = tt

    -- a mapped computation at a budget: the run, its value mapped
    mapAp : ∀ {X Y : Set} → (X → Y) → TM.Run (Ap X) → TM.Run (Ap Y)
    mapAp g (es , Once.Res.stopped)              = es , Once.Res.stopped
    mapAp g (es , Once.Res.returns cut)          = es , Once.Res.returns cut
    mapAp g (es , Once.Res.returns (done x r))   = es , Once.Res.returns (done (g x) r)

    then-fmap : ∀ {X Y : Set} h es (ρ : Once.Res.Res (Ap X)) (g : X → Y)
              → thenAp ι h es ρ (λ x → return∞ (g x)) ≡ mapAp g (es , ρ)
    then-fmap h es Once.Res.stopped            g = refl
    then-fmap h es (Once.Res.returns cut)      g = refl
    then-fmap h es (Once.Res.returns (done x r)) g = cong (λ z → (z , Once.Res.returns (done (g x) r))) (++-identityʳ es)

    run-fmap : ∀ {X Y : Set} h r (m : T∞ X) (g : X → Y) → TM.run ι h (approx r (fmap∞ g m)) ≡ mapAp g (TM.run ι h (approx r m))
    run-fmap h r m g = trans (run-approx-bind ι h r m (λ x → return∞ (g x)))
                             (then-fmap h (proj₁ (TM.run ι h (approx r m))) (proj₂ (TM.run ι h (approx r m))) g)

    -- a body at its grade runs as its term (at `act`, the embedded block: `Grade.blk-coh`)
    up-run : ∀ g {Δ} (ρ : Env Δ) {E A B} (b : Tm Δ E A B) (γ : Gd g b) e x r h
           → TM.run ι h (approx r (up g (Lg ρ g b γ e x))) ≡ TM.run ι h (approx r (Lᶜ ρ b e x))
    up-run act ρ b γ e x r h = sym (run-≈ r (blk-coh ρ γ e x) h)
    up-run eff ρ b γ e x r h = refl

  -- how a layer's fold is observed: the positions' values, read as the functor's
  outApM : ∀ G {A} → Outcome (LF∙ G A) → ℕ → Once.Res.Res (Ap (FS G ⟦ A ⟧))
  outApM G {A} (gives y _) l = Once.Res.returns (done (coh G A (er y)) l)
  outApM G     (stop y′)   l = stopAp y′

  outApM-Idf : ∀ {A} (o : Outcome A) l → outAp o l ≡ outApM Idf o l
  outApM-Idf (gives _ _) l = refl
  outApM-Idf (stop _)    l = refl

  mutual
    soundₖ : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v o n t} (r : Run ds f e v n o t) {k l}
           → Spends r k l → UnCut r → ∀ {h h′} → WTr Wι h t h′
           → (TM.run ι h (approx k (Lᶜ ⟦ ds ⟧D f (er e) (er v))) ≡ (evsOf t , outAp o l)) × GivesHist o h t h′
    soundₖ r-id sp u w = leaf [] refl sp refl w
    soundₖ r-ρ sp u w = leaf [] refl sp refl w
    soundₖ r-ρ⁻ sp u w = leaf [] refl sp refl w
    soundₖ r-λ sp u w = leaf [] refl sp refl w
    soundₖ r-λ⁻ sp u w = leaf [] refl sp refl w
    soundₖ r-α sp u w = leaf [] refl sp refl w
    soundₖ r-α⁻ sp u w = leaf [] refl sp refl w
    soundₖ r-swap sp u w = leaf [] refl sp refl w
    soundₖ (r-dup {v = v} {n}) sp u w = leaf (proj₂ (proj₂ (copy v n))) (cong (er v ,_) (sym (copy-er v n))) sp (ios-copy v n) w
    soundₖ (r-drop {v = v}) sp u w = leaf (freeAll v) refl sp (ios-freeAll v) w
    soundₖ r-inl sp u w = leaf [] refl sp refl w
    soundₖ r-inr sp u w = leaf [] refl sp refl w
    soundₖ (r-case₁ r) sp u w = soundₖ r sp u w
    soundₖ (r-case₂ r) sp u w = soundₖ r sp u w
    soundₖ (r-In {F = F} {n = n}) sp u w = leaf (alloc (szμ F , n) ∷ []) refl sp refl w
    soundₖ (r-Outμ {F = F} {v = v} {i = i}) sp u w = leaf (free i ∷ []) (coh⁻¹∘coh F (μt F) (er v)) sp refl w
    soundₖ (r-clo {F = F} {x = x}) sp u w = leaf [] (sym (tag-er F x)) sp refl w
    soundₖ (r-app {g = g} {ds′ = ds′} {b = b} {γ = γ} {x = x} {a = a} {o = o} {t = t} q r) {k} sp u {h} w =
      let (e₁ , hi) = soundₖ r sp u w in
           trans (cong (λ m → TM.run ι h (approx k (up g m))) (lookup-look q (er x) (er a)))
                          (trans (up-run g ⟦ ds′ ⟧D b γ tt (er x , er a) k h) e₁) , hi
    soundₖ (r-cata rm th) sp u w = soundCata rm th sp u w
    soundₖ (r-cata-reuse rm th) () u w
    soundₖ {ds = ds} (r-lend {b = b} {e = e} {x = x} {a = a} (fm-gives {t = t} r)) {k} sp u {h} w = let (e₁ , hi) = soundₖ r sp u w in
         trans (run-fmap h k (Lᶜ ⟦ ds ⟧D b (er e , er x) (er a)) (er x ,_)) (cong (mapAp (er x ,_)) e₁) , hi
    soundₖ {ds = ds} (r-lend {b = b} {e = e} {x = x} {a = a} (fm-stop {y = y} {t = t} r)) {k} sp u {h} w = let (e₁ , hi) = soundₖ r sp u w in
         trans (run-fmap h k (Lᶜ ⟦ ds ⟧D b (er e , er x) (er a)) (er x ,_)) (trans (cong (mapAp (er x ,_)) e₁) (map-stop (er x ,_) (evsOf t) y)) , tt
    soundₖ (r-lift r) sp u w = soundₖ r sp u w
    soundₖ (r-fst r) sp u w = soundₖ r sp u w
    soundₖ (r-snd r) sp u w = soundₖ r sp u w
    soundₖ (r-caseE₁ r) sp u w = soundₖ r sp u w
    soundₖ (r-caseE₂ r) sp u w = soundₖ r sp u w
    soundₖ (r-out {F} {f = f} {v = v} {a = a} r) {k} sp u {h} w = let (e₁ , hi) = soundₖ r sp u w in
         trans (cong (λ z → TM.run ι h (approx k (Lᶜ _ f z (er a)))) (coh⁻¹∘coh F (μt F) (er v))) e₁ , hist-cong _ refl hi
    soundₖ (r-copy {e = e} {n}) sp u w = leaf (proj₂ (proj₂ (copy e n))) (sym (copy-er e n)) sp (ios-copy e n) w
    soundₖ (r-bapp {g = g} {ds′ = ds′} {b = b} {γ = γ} {x = x} {a = a} q r) {k} sp u {h} w =
      let (e₁ , hi) = soundₖ r sp u w in
           trans (cong (λ m → TM.run ι h (approx k (up g m))) (lookup-look q (er x) (er a)))
                          (trans (up-run g ⟦ ds′ ⟧D b γ (er x) (er a) k h) e₁) , hi
    soundₖ (r-lam {X = X} {n = n}) sp u w = leaf (alloc (szc X , n) ∷ []) refl sp refl w
    soundₖ (r-lamω {X = X} {n = n}) sp u w = leaf (alloc (szc X , n) ∷ []) refl sp refl w
    soundₖ (r-ev {g = g} {ds′ = ds′} {b = b} {γ = γ} {x = x} {a = a} r) {k} sp u {h} w = let (e₁ , hi) = soundₖ r sp u w in
         trans (up-run g ⟦ ds′ ⟧D b γ tt (er x , er a) k h) e₁ , hist-cong _ refl hi
    soundₖ (r-bev {g = g} {ds′ = ds′} {b = b} {γ = γ} {x = x} {a = a} r) {k} sp u {h} w = let (e₁ , hi) = soundₖ r sp u w in
         trans (up-run g ⟦ ds′ ⟧D b γ (er x) (er a) k h) e₁ , hist-cong _ refl hi
    soundₖ (r-unf {F = F} {S = S} {n = n}) sp u w = leaf (alloc (szν F S , n) ∷ []) refl sp refl w
    soundₖ {ds = ds} (r-nout {E = E} {F} {S} {e = e} {p = p} r) {k} sp u {h} w = let (e₁ , hi) = soundₖ r sp u w in
         trans (sym (run-≈ k (obs-coh ⟦ ds ⟧D F S (proj₁ (er p)) (proj₂ (er p)) {E} (er e)) h)) e₁ , hist-cong _ refl hi
    soundₖ r-const sp u w = leaf [] refl sp refl w
    soundₖ (r-op {s = s} {x = x} {y = y} {t = t} p) {k} refl u {h} w = let (e₁ , hi) = op-ret-run p w in
         trans (run-embB k (opB s (er x)) h)
                        (trans (cong (tagRun k) (run-fmapT (fromF (scod s)) (opF s (toF (sdom s) (er x))) h))
                               (trans (cong (λ R → tagRun k (proj₁ R , Once.Res.mapRes (fromF (scod s)) (proj₂ R))) e₁)
                                      (cong (λ z → (evsOf t , Once.Res.returns (done z k))) (sym (er-mvF (scod s) y)))))
                  , hi
    soundₖ (r-opend {s = s} {x = x} {w = halted} p) {k} refl u {h} w =
      trans (run-embB k (opB s (er x)) h)
            (trans (cong (tagRun k) (run-fmapT (fromF (scod s)) (opF s (toF (sdom s) (er x))) h))
                   (cong (λ R → tagRun k (proj₁ R , Once.Res.mapRes (fromF (scod s)) (proj₂ R))) (op-halt-run p w))) , tt
    soundₖ (r-opend {w = exhausted} p) sp () w
    soundₖ (r-iter r th) sp u w = soundIter r th sp u w
    soundₖ r-exh () u w
    soundₖ (r-cut r q) () u w
    soundₖ (r-tmp {t = t} r wv p) sp u w = let (e₁ , hi) = soundₖ r sp u (wtr-weave wv w) in
         trans e₁ (cong (λ z → (z , _)) (sym (cong (map ioEvent) (ios-weave wv))))
                  , hist-cong _ (sym (cong (map ioEvent) (ios-weave wv))) hi
    soundₖ (r-∘ rg th) sp u w = soundSeq rg th sp u w
    soundₖ (r-⊗ rf th) sp u w = soundPar rf th sp u w

    -- one after the other: master's bind at the budget (`run-approx-bind`)
    soundSeq : ∀ {Γ} {ds : Defs Γ} {E A B C} {f : Tm Γ E B C} {g : Tm Γ E A B} {e v o₁ o n t₁ t₂}
               (rg : Run ds g e v n o₁ t₁) (th : Then (Run ds f e) o₁ o t₂) {k l}
             → Spends (r-∘ rg th) k l → UnCut (r-∘ rg th) → ∀ {h h′} → WTr Wι h (t₁ ++ t₂) h′
             → (TM.run ι h (approx k (Lᶜ ⟦ ds ⟧D (f ∘l g) (er e) (er v))) ≡ (evsOf (t₁ ++ t₂) , outAp o l)) × GivesHist o h (t₁ ++ t₂) h′
    soundSeq {ds = ds} {f = f} {g = g} {e = e} {v = v} {o = o} {t₁ = t₁} {t₂} rg (go-on {u = u} rf) {k} {l} (m , s₁ , s₂) (u₁ , u₂) {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , hi₁) = soundₖ rg s₁ u₁ w₁ in
             let (e₂ , hi₂) = soundₖ rf s₂ u₂ w₂ in
              
              trans (run-approx-bind ι h k (Lᶜ ⟦ ds ⟧D g (er e) (er v)) (Lᶜ ⟦ ds ⟧D f (er e)))
                (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) (Lᶜ ⟦ ds ⟧D f (er e))) e₁)
                  (trans (cong (λ z → appE (evsOf t₁) (TM.run ι z (approx m (Lᶜ ⟦ ds ⟧D f (er e) (er u))))) (sym hi₁))
                    (trans (cong (appE (evsOf t₁)) e₂)
                      (cong (λ z → (z , outAp o l)) (sym (evsOf-++ t₁ t₂))))))
              , hist-seq o t₁ t₂ hi₁ hi₂
    soundSeq {ds = ds} {f = f} {g = g} {e = e} {v = v} {t₁ = t₁} rg (stopped {y = y}) {k} {l} s₁ u₁ {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , _) = soundₖ rg s₁ u₁ w₁ in
            
            trans (run-approx-bind ι h k (Lᶜ ⟦ ds ⟧D g (er e) (er v)) (Lᶜ ⟦ ds ⟧D f (er e)))
              (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) (Lᶜ ⟦ ds ⟧D f (er e))) e₁)
                (trans (then-stop h y (evsOf t₁) (Lᶜ ⟦ ds ⟧D f (er e)))
                  (cong (λ z → (z , stopAp y)) (sym (evs-[] t₁)))))
            , tt


    map-stop : ∀ {X Y : Set} (g : X → Y) es (y : Why) → mapAp g (es , stopAp y) ≡ (es , stopAp y)
    map-stop g es halted    = refl
    map-stop g es exhausted = refl

    -- side by side: the left, then the right mapped into the pair
    soundPar : ∀ {Γ} {ds : Defs Γ} {E A B C D} {f : Tm Γ E A B} {g : Tm Γ E C D} {e a c o₁ o n t₁ t₂}
               (rf : Run ds f e a n o₁ t₁) (th : Then (λ a′ n₁ → Fmap (mpair a′) (Run ds g e c n₁)) o₁ o t₂) {k l}
             → Spends (r-⊗ rf th) k l → UnCut (r-⊗ rf th) → ∀ {h h′} → WTr Wι h (t₁ ++ t₂) h′
             → (TM.run ι h (approx k (Lᶜ ⟦ ds ⟧D (f ⊗l g) (er e) (er (mpair a c)))) ≡ (evsOf (t₁ ++ t₂) , outAp o l))
               × GivesHist o h (t₁ ++ t₂) h′
    soundPar {ds = ds} {f = f} {g = g} {e = e} {a = a} {c = c} {t₁ = t₁} {t₂} rf (go-on {u = a′} (fm-gives {u = c′} {n = n₂} rg)) {k} {l}
             (m , s₁ , s₂) (u₁ , u₂) {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , hi₁) = soundₖ rf s₁ u₁ w₁ in
             let (e₂ , hi₂) = soundₖ rg s₂ u₂ w₂ in
              
              trans (run-approx-bind ι h k (Lᶜ ⟦ ds ⟧D f (er e) (er a)) (λ a″ → fmap∞ (a″ ,_) (Lᶜ ⟦ ds ⟧D g (er e) (er c))))
                (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) (λ a″ → fmap∞ (a″ ,_) (Lᶜ ⟦ ds ⟧D g (er e) (er c)))) e₁)
                  (trans (cong (λ z → appE (evsOf t₁) (TM.run ι z (approx m (fmap∞ (er a′ ,_) (Lᶜ ⟦ ds ⟧D g (er e) (er c)))))) (sym hi₁))
                    (trans (cong (appE (evsOf t₁)) (trans (run-fmap h₁ m (Lᶜ ⟦ ds ⟧D g (er e) (er c)) (er a′ ,_)) (cong (mapAp (er a′ ,_)) e₂)))
                      (cong (λ z → (z , outAp (gives (mpair a′ c′) n₂) l)) (sym (evsOf-++ t₁ t₂))))))
              , hist-seq (gives (mpair a′ c′) n₂) t₁ t₂ hi₁ hi₂
    soundPar {ds = ds} {f = f} {g = g} {e = e} {a = a} {c = c} {t₁ = t₁} {t₂} rf (go-on {u = a′} (fm-stop {y = y} rg)) {k} {l}
             (m , s₁ , s₂) (u₁ , u₂) {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , hi₁) = soundₖ rf s₁ u₁ w₁ in
             let (e₂ , _) = soundₖ rg s₂ u₂ w₂ in
              
              trans (run-approx-bind ι h k (Lᶜ ⟦ ds ⟧D f (er e) (er a)) (λ a″ → fmap∞ (a″ ,_) (Lᶜ ⟦ ds ⟧D g (er e) (er c))))
                (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) (λ a″ → fmap∞ (a″ ,_) (Lᶜ ⟦ ds ⟧D g (er e) (er c)))) e₁)
                  (trans (cong (λ z → appE (evsOf t₁) (TM.run ι z (approx m (fmap∞ (er a′ ,_) (Lᶜ ⟦ ds ⟧D g (er e) (er c)))))) (sym hi₁))
                    (trans (cong (appE (evsOf t₁)) (trans (run-fmap h₁ m (Lᶜ ⟦ ds ⟧D g (er e) (er c)) (er a′ ,_))
                                                          (trans (cong (mapAp (er a′ ,_)) e₂) (map-stop (er a′ ,_) (evsOf t₂) y))))
                      (cong (λ z → (z , stopAp y)) (sym (evsOf-++ t₁ t₂))))))
              , tt
    soundPar {ds = ds} {f = f} {g = g} {e = e} {a = a} {c = c} {t₁ = t₁} rf (stopped {y = y}) {k} {l} s₁ u₁ {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , _) = soundₖ rf s₁ u₁ w₁ in
            
            trans (run-approx-bind ι h k (Lᶜ ⟦ ds ⟧D f (er e) (er a)) (λ a″ → fmap∞ (a″ ,_) (Lᶜ ⟦ ds ⟧D g (er e) (er c))))
              (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) (λ a″ → fmap∞ (a″ ,_) (Lᶜ ⟦ ds ⟧D g (er e) (er c)))) e₁)
                (trans (then-stop h y (evsOf t₁) (λ a″ → fmap∞ (a″ ,_) (Lᶜ ⟦ ds ⟧D g (er e) (er c))))
                  (cong (λ z → (z , stopAp y)) (sym (evs-[] t₁)))))
            , tt

    -- the loop: master's loop at the budget (`run-approx-iter`): a continuing round spends a unit
    soundIter : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A (B ⊕t A)} {φ : Blk f} {e a o₁ o n t₁ t₂}
                (r : Run ds f e a n o₁ t₁) (th : Then (Next ds f φ e) o₁ o t₂) {k l}
              → Spends (r-iter r th) k l → UnCut (r-iter r th) → ∀ {h h′} → WTr Wι h (t₁ ++ t₂) h′
              → (TM.run ι h (approx k (Lᶜ ⟦ ds ⟧D (liter f φ) (er e) (er a))) ≡ (evsOf (t₁ ++ t₂) , outAp o l))
                × GivesHist o h (t₁ ++ t₂) h′
    soundIter {ds = ds} {f = f} {e = e} {a = a} {t₁ = t₁} r (go-on (done {b = b} {n = n₁})) {k} {l} s₁ u₁ {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , hi₁) = soundₖ r s₁ u₁ w₁ in
            
            trans (run-approx-iter ι h k (Lᶜ ⟦ ds ⟧D f (er e) (er a)) (Lᶜ ⟦ ds ⟧D f (er e)))
              (trans (cong (λ R → thenIter ι h (proj₁ R) (proj₂ R) (Lᶜ ⟦ ds ⟧D f (er e))) e₁)
                (cong (λ z → (z , outAp (gives b n₁) l)) (sym (evs-[] t₁))))
            , hist-seq (gives b n₁) t₁ [] hi₁ (trans w₂ (sym (++-identityʳ h₁)))
    soundIter {ds = ds} {f = f} {e = e} {a = a} {t₁ = t₁} {t₂} r (go-on (again {a = a′} rn)) {k} {l} (suc m , s₁ , s₂) (u₁ , u₂) {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , hi₁) = soundₖ r s₁ u₁ w₁ in
             let (e₂ , hi₂) = soundₖ rn s₂ u₂ w₂ in
              
              trans (run-approx-iter ι h k (Lᶜ ⟦ ds ⟧D f (er e) (er a)) (Lᶜ ⟦ ds ⟧D f (er e)))
                (trans (cong (λ R → thenIter ι h (proj₁ R) (proj₂ R) (Lᶜ ⟦ ds ⟧D f (er e))) e₁)
                  (trans (cong (λ z → appE (evsOf t₁) (TM.run ι z (approx m (iterRun (Lᶜ ⟦ ds ⟧D f (er e)) (Lᶜ ⟦ ds ⟧D f (er e) (er a′)))))) (sym hi₁))
                    (trans (cong (appE (evsOf t₁)) e₂)
                      (cong (λ z → (z , _)) (sym (evsOf-++ t₁ t₂))))))
              , hist-seq _ t₁ t₂ hi₁ hi₂
    soundIter {ds = ds} {f = f} {e = e} {a = a} {t₁ = t₁} r (go-on (again rn)) {k} {l} (zero , s₁ , a₀) (u₁ , u₂) {h} w =
      again-zero rn a₀ λ { refl refl → let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , _) = soundₖ r s₁ u₁ w₁ in
            
            trans (run-approx-iter ι h k (Lᶜ ⟦ ds ⟧D f (er e) (er a)) (Lᶜ ⟦ ds ⟧D f (er e)))
              (trans (cong (λ R → thenIter ι h (proj₁ R) (proj₂ R) (Lᶜ ⟦ ds ⟧D f (er e))) e₁)
                (cong (λ z → (z , Once.Res.returns cut)) (sym (evs-[] t₁))))
            , tt }
    soundIter {ds = ds} {f = f} {e = e} {a = a} {t₁ = t₁} r (stopped {y = y}) {k} {l} s₁ u₁ {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , _) = soundₖ r s₁ u₁ w₁ in
            
            trans (run-approx-iter ι h k (Lᶜ ⟦ ds ⟧D f (er e) (er a)) (Lᶜ ⟦ ds ⟧D f (er e)))
              (trans (cong (λ R → thenIter ι h (proj₁ R) (proj₂ R) (Lᶜ ⟦ ds ⟧D f (er e))) e₁)
                (trans (iter-stop h y (evsOf t₁) (Lᶜ ⟦ ds ⟧D f (er e)))
                  (cong (λ z → (z , stopAp y)) (sym (evs-[] t₁)))))
            , tt

    -- a continuing round with no budget left: the continuation is the cut
    again-zero : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A (B ⊕t A)} {φ : Blk f} {e a o n t l} {P : Set}
                 (rn : Run ds (liter f φ) e a n o t) → Again rn zero l
               → (o ≡ stop exhausted → t ≡ [] → P) → P
    again-zero r-exh refl k = k refl refl
    again-zero (r-iter _ _) () k
    again-zero (r-cut _ _)  () k
    again-zero (r-tmp _ _ _) () k

    -- the fold: its positions folded (`soundMₖ`), then the algebra
    soundCata : ∀ {Γ} {ds : Defs Γ} {E F A} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {i v o₁ o n t₁ t₂}
                (rm : RunMap ds F alg e F v n o₁ t₁) (th : Then (Run ds alg e) o₁ o t₂) {k l}
              → Spends (r-cata {i = i} rm th) k l → UnCut (r-cata {i = i} rm th) → ∀ {h h′} → WTr Wι h (free i ∷ (t₁ ++ t₂)) h′
              → (TM.run ι h (approx k (Lᶜ ⟦ ds ⟧D (lcata F alg) (er e) (er (mmu i v)))) ≡ (evsOf (free i ∷ (t₁ ++ t₂)) , outAp o l))
                × GivesHist o h (free i ∷ (t₁ ++ t₂)) h′
    soundCata {ds = ds} {F = F} {A} {alg} {e} {v = v} {t₁ = t₁} {t₂} rm (go-on {u = u} ra) {k} {l} (m , s₁ , s₂) (u₁ , u₂) {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , hi₁) = soundMₖ rm s₁ u₁ w₁ in
             let (e₂ , hi₂) = soundₖ ra s₂ u₂ w₂ in
              
              trans (run-approx-bind ι h k (travC ⟦ ds ⟧D F F alg′ (coh F (μt F) (er v))) alg′)
                (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) alg′) e₁)
                  (trans (cong (λ z → appE (evsOf t₁) (TM.run ι z (approx m (alg′ (coh F A (er u)))))) (sym hi₁))
                    (trans (cong (λ z → appE (evsOf t₁) (TM.run ι h₁ (approx m (Lᶜ ⟦ ds ⟧D alg (er e) z)))) (coh⁻¹∘coh F A (er u)))
                      (trans (cong (appE (evsOf t₁)) e₂)
                        (cong (λ z → (z , _)) (sym (evsOf-++ t₁ t₂)))))))
              , hist-cong _ refl (hist-seq _ t₁ t₂ hi₁ hi₂)
      where
        alg′ = λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)
    soundCata {ds = ds} {F = F} {A} {alg} {e} {v = v} {t₁ = t₁} rm (stopped {y = y}) {k} {l} s₁ u₁ {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , _) = soundMₖ rm s₁ u₁ w₁ in
            
            trans (run-approx-bind ι h k (travC ⟦ ds ⟧D F F alg′ (coh F (μt F) (er v))) alg′)
              (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) alg′) e₁)
                (trans (then-stop h y (evsOf t₁) alg′)
                  (cong (λ z → (z , stopAp y)) (sym (evs-[] t₁)))))
            , tt
      where
        alg′ = λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)

    soundMₖ : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
              (rm : RunMap ds F alg e G x n o t) {k l} → SpendsM rm k l → UnCutM rm → ∀ {h h′} → WTr Wι h t h′
            → (TM.run ι h (approx k (travC ⟦ ds ⟧D F G (λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)) (coh G (μt F) (er x))))
                ≡ (evsOf t , outApM G o l))
              × GivesHist o h t h′
    soundMₖ (m-id {o = o} {t = t} r) {k} {l} sp u w = let (e₁ , hi) = soundₖ r sp u w in
         trans e₁ (cong (evsOf t ,_) (outApM-Idf o l)) , hi
    soundMₖ (m-one {x = x}) refl u {h} refl = refl , sym (++-identityʳ h)
    soundMₖ (m-b {x = x}) refl u {h} refl = refl , sym (++-identityʳ h)
    soundMₖ (m-μ {x = x}) refl u {h} refl = refl , sym (++-identityʳ h)
    soundMₖ {ds = ds} {A = A} {F = F} {alg = alg} {e = e} {G = G ⊕f H} {x = minl x} {t = t} (m-inl (fm-gives {u = y} r)) {k} {l} sp u {h} w =
      let (e₁ , hi) = soundMₖ r sp u w in
           trans (run-fmap h k (travC ⟦ ds ⟧D F G (λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)) (coh G (μt F) (er x))) inj₁)
                          (cong (mapAp inj₁) e₁) , hi
    soundMₖ {ds = ds} {A = A} {F = F} {alg = alg} {e = e} {G = G ⊕f H} {x = minl x} {t = t} (m-inl (fm-stop {y = y′} r)) {k} {l} sp u {h} w =
      let (e₁ , _) = soundMₖ r sp u w in
           trans (run-fmap h k (travC ⟦ ds ⟧D F G (λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)) (coh G (μt F) (er x))) inj₁)
                         (trans (cong (mapAp inj₁) e₁) (map-stop inj₁ (evsOf t) y′)) , tt
    soundMₖ {ds = ds} {A = A} {F = F} {alg = alg} {e = e} {G = G ⊕f H} {x = minr x} {t = t} (m-inr (fm-gives {u = y} r)) {k} {l} sp u {h} w =
      let (e₁ , hi) = soundMₖ r sp u w in
           trans (run-fmap h k (travC ⟦ ds ⟧D F H (λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)) (coh H (μt F) (er x))) inj₂)
                          (cong (mapAp inj₂) e₁) , hi
    soundMₖ {ds = ds} {A = A} {F = F} {alg = alg} {e = e} {G = G ⊕f H} {x = minr x} {t = t} (m-inr (fm-stop {y = y′} r)) {k} {l} sp u {h} w =
      let (e₁ , _) = soundMₖ r sp u w in
           trans (run-fmap h k (travC ⟦ ds ⟧D F H (λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)) (coh H (μt F) (er x))) inj₂)
                         (trans (cong (mapAp inj₂) e₁) (map-stop inj₂ (evsOf t) y′)) , tt
    soundMₖ {ds = ds} {A = A} {F = F} {alg = alg} {e = e} {G = G ⊗f H} {x = mpair x x′} {t = _} (m-pair {t₁ = t₁} {t₂} r (go-on {u = y} (fm-gives {u = y′} {n = n₂} r′))) {k} {l}
            (m , s₁ , s₂) (u₁ , u₂) {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , hi₁) = soundMₖ r s₁ u₁ w₁ in
             let (e₂ , hi₂) = soundMₖ r′ s₂ u₂ w₂ in
              
              trans (run-approx-bind ι h k (travC ⟦ ds ⟧D F G alg′ (coh G (μt F) (er x))) (λ u′ → fmap∞ (u′ ,_) (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′)))))
                (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) (λ u′ → fmap∞ (u′ ,_) (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′))))) e₁)
                  (trans (cong (λ z → appE (evsOf t₁) (TM.run ι z (approx m (fmap∞ (coh G A (er y) ,_) (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′))))))) (sym hi₁))
                    (trans (cong (appE (evsOf t₁)) (trans (run-fmap h₁ m (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′))) (coh G A (er y) ,_))
                                                          (cong (mapAp (coh G A (er y) ,_)) e₂)))
                      (cong (λ z → (z , _)) (sym (evsOf-++ t₁ t₂))))))
              , hist-seq (gives (mpair y y′) n₂) t₁ t₂ hi₁ hi₂
      where
        alg′ = λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)
    soundMₖ {ds = ds} {A = A} {F = F} {alg = alg} {e = e} {G = G ⊗f H} {x = mpair x x′} (m-pair {t₁ = t₁} {t₂} r (go-on {u = y} (fm-stop {y = y′} r′))) {k} {l}
            (m , s₁ , s₂) (u₁ , u₂) {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , hi₁) = soundMₖ r s₁ u₁ w₁ in
             let (e₂ , _) = soundMₖ r′ s₂ u₂ w₂ in
              
              trans (run-approx-bind ι h k (travC ⟦ ds ⟧D F G alg′ (coh G (μt F) (er x))) (λ u′ → fmap∞ (u′ ,_) (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′)))))
                (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) (λ u′ → fmap∞ (u′ ,_) (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′))))) e₁)
                  (trans (cong (λ z → appE (evsOf t₁) (TM.run ι z (approx m (fmap∞ (coh G A (er y) ,_) (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′))))))) (sym hi₁))
                    (trans (cong (appE (evsOf t₁)) (trans (run-fmap h₁ m (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′))) (coh G A (er y) ,_))
                                                          (trans (cong (mapAp (coh G A (er y) ,_)) e₂) (map-stop (coh G A (er y) ,_) (evsOf t₂) y′))))
                      (cong (λ z → (z , stopAp y′)) (sym (evsOf-++ t₁ t₂))))))
              , tt
      where
        alg′ = λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)
    soundMₖ {ds = ds} {A = A} {F = F} {alg = alg} {e = e} {G = G ⊗f H} {x = mpair x x′} (m-pair {t₁ = t₁} r (stopped {y = y′})) {k} {l} s₁ u₁ {h} w =
      let (h₁ , w₁ , w₂) = wtr-split t₁ w in
           let (e₁ , _) = soundMₖ r s₁ u₁ w₁ in
            
            trans (run-approx-bind ι h k (travC ⟦ ds ⟧D F G alg′ (coh G (μt F) (er x))) (λ u′ → fmap∞ (u′ ,_) (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′)))))
              (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) (λ u′ → fmap∞ (u′ ,_) (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′))))) e₁)
                (trans (then-stop h y′ (evsOf t₁) (λ u′ → fmap∞ (u′ ,_) (travC ⟦ ds ⟧D F H alg′ (coh H (μt F) (er x′)))))
                  (cong (λ z → (z , stopAp y′)) (sym (evs-[] t₁)))))
            , tt
      where
        alg′ = λ z → Lᶜ ⟦ ds ⟧D alg (er e) (coh⁻¹ F A z)
