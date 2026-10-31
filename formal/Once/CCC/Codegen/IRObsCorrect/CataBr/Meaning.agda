-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning   (plan 0.125 S3, cata M4 stage A)
--
-- WHAT A `strat-branching` CATA MEANS, as the SEQUENTIAL PROCESS the
-- emitted code performs (`cata-trace-branching`, IRToTrace):
--
--   * FLATTEN: a todo stack of nodes and an eval stack. Pop a node `t` off
--     todo, push it onto eval, push its `Id` children onto todo LEFT to
--     RIGHT (`visit-walk`, so the right child ends on top). The eval stack's
--     final content is `po root` — the LEFT-FIRST POST-ORDER of the tree
--     (`po t = poAll (children t) ++ [ t ]`), read top first.
--     Invariant: `FI todo eval` (`flatten-step`, `flatten-measure`).
--   * FOLD: pop a node off eval, rebuild its layer `⟦ G ⟧F C` popping one
--     result per `Id` position off the value stack, the RIGHT-most first
--     (`rebuild-walk`; `fill` here), run the algebra, push its result.
--     That loop is `runPO` (one node per `stepPO`).
--
-- THE LEMMA (`po-run`) is at the RUN level: for every Interpretation,
-- history and budget, `runPO (po t ++ xs) vs` runs exactly as the cata on
-- `t` followed by `runPO xs (c ∷ vs)` — same events, same end (value and
-- budget left / stop / cut). `T∞` has no bind-associativity law up to `≡`,
-- but its budgeted RUNS do (`bind-assoc`, from `Approx.run-approx-bind`
-- and `thenAp-assoc`), and that is all an observation (`⟪ _ ⟫ k`) reads.
-- The proof is by induction on the TREE (`po-run`) with an inner induction
-- on the functor matching `seqF∞` (`poL-run`: K returns, Id is the child's
-- fold, ⊕ by tag, ⊗ left first). The one fact about the layer the fold's
-- algebra receives — that `fill` gives back exactly what `seqF∞` returned
-- — holds because every result of `seqF∞` has the node's shape
-- (`seq-shape`, `fill-push`).
--
-- WHY A `T∞` MODEL (`runPO`) RATHER THAN A RELATION: the machine's fold
-- loop handles one node per round, and `runPO-step-run` gives exactly that
-- round's run equation (`thenAp` of the algebra's run, then the rest), the
-- shape `IterRounds` walks `run-approx-iter` by. The root corollary
-- (`fold-root`, and `cata-br-meaning` at the IR) closes the loop against
-- the obligation's `approx k (evalᴰ (Cata wf alg) (e , x))`.
--
-- The model is generic in the functor `G`, its well-formedness `w`, the
-- carrier `C` and the per-layer algebra `alg : ⟦ G ⟧F C → T∞ C`
-- (`module PO`); `cata-br-meaning` instantiates it at the IR's `Cata`.
------------------------------------------------------------------------

module Once.CCC.Codegen.IRObsCorrect.CataBr.Meaning where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Internal.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.Internal.Type.WellFormed using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Internal.Polynomial using (SFunctor; μS; ⟨_⟩; ⟦_⟧SF; sfmapCata)
open import Once.Internal.FunctorMeaning using (translateF)
open import Once.Spec.Word using (Carrier)
open import Once.Internal.Value Carrier Carrier using (⟦_⟧F; ⟦μ⟧; sem-cata; sem-fmap; sem-Out; coerce-μ-out)
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; seqF∞)
open import Once.Internal.Trace using (Interp; Run; appE)
open import Once.Internal.Trace using (run)
open import Once.Internal.Res using (Res; stopped; returns; mapRes)
open import Once.Internal.Event using (SigOpEvent)
open import Once.Denotation.Approx using (Ap; done; cut; approx; thenAp; run-approx-bind)

------------------------------------------------------------------------
-- RUN-LEVEL EQUIVALENCE: the same budgeted run under every Interpretation,
-- history and budget.
------------------------------------------------------------------------
-- (A record, not a bare Π, so the two runs are inferable from a proof.)
infix 0 _≋_
record _≋_ {X : Set} (m m′ : T∞ X) : Set where
  constructor ≋c
  field ≋r : ∀ (ι : Interp) (h : List SigOpEvent) (r : ℕ) → run ι h (approx r m) ≡ run ι h (approx r m′)
open _≋_

≋-refl : ∀ {X} (m : T∞ X) → m ≋ m
≋-refl m = ≋c λ ι h r → refl

≋-sym : ∀ {X} {m m′ : T∞ X} → m ≋ m′ → m′ ≋ m
≋-sym e = ≋c λ ι h r → sym (≋r e ι h r)

≋-trans : ∀ {X} {m m′ m″ : T∞ X} → m ≋ m′ → m′ ≋ m″ → m ≋ m″
≋-trans e e′ = ≋c λ ι h r → trans (≋r e ι h r) (≋r e′ ι h r)

≡→≋ : ∀ {X} {m m′ : T∞ X} → m ≡ m′ → m ≋ m′
≡→≋ refl = ≋c λ ι h r → refl

------------------------------------------------------------------------
-- `thenAp` ASSOCIATES (by cases on the first part's end), so budgeted runs
-- of binds associate.
------------------------------------------------------------------------
private
  appE-++ : ∀ {X} (es es′ : List SigOpEvent) (R : Run X) → appE (es ++ es′) R ≡ appE es (appE es′ R)
  appE-++ es es′ R = cong (λ l → l , proj₂ R) (++-assoc es es′ (proj₁ R))

  thenAp-app : ∀ {Y Z} (ι : Interp) (h es es′ : List SigOpEvent) (ρ : Res (Ap Y)) (g : Y → T∞ Z)
             → thenAp ι h (es ++ es′) ρ g ≡ appE es (thenAp ι (h ++ es) es′ ρ g)
  thenAp-app ι h es es′ stopped              g = refl
  thenAp-app ι h es es′ (returns cut)        g = refl
  thenAp-app ι h es es′ (returns (done y r)) g =
    trans (cong (λ hh → appE (es ++ es′) (run ι hh (approx r (g y)))) (sym (++-assoc h es es′)))
          (appE-++ es es′ (run ι ((h ++ es) ++ es′) (approx r (g y))))

thenAp-assoc : ∀ {X Y Z} (ι : Interp) (h es : List SigOpEvent) (ρ : Res (Ap X)) (f : X → T∞ Y) (g : Y → T∞ Z)
             → thenAp ι h (proj₁ (thenAp ι h es ρ f)) (proj₂ (thenAp ι h es ρ f)) g
               ≡ thenAp ι h es ρ (λ x → f x >>=∞ g)
thenAp-assoc ι h es stopped              f g = refl
thenAp-assoc ι h es (returns cut)        f g = refl
thenAp-assoc ι h es (returns (done x r)) f g =
  trans (thenAp-app ι h es (proj₁ R) (proj₂ R) g)
        (cong (appE es) (sym (run-approx-bind ι (h ++ es) r (f x) g)))
  where R = run ι (h ++ es) (approx r (f x))

bind-assoc : ∀ {X Y Z} (m : T∞ X) (f : X → T∞ Y) (g : Y → T∞ Z)
           → (m >>=∞ f) >>=∞ g ≋ m >>=∞ (λ x → f x >>=∞ g)
bind-assoc m f g = ≋c λ ι h r →
  trans (run-approx-bind ι h r (m >>=∞ f) g)
  (trans (cong (λ R → thenAp ι h (proj₁ R) (proj₂ R) g) (run-approx-bind ι h r m f))
  (trans (thenAp-assoc ι h (proj₁ (run ι h (approx r m))) (proj₂ (run ι h (approx r m))) f g)
         (sym (run-approx-bind ι h r m (λ x → f x >>=∞ g)))))

------------------------------------------------------------------------
-- CONGRUENCE under a bind, for every continuation value or only for the
-- values the first part can RETURN (`Returns P m`).
------------------------------------------------------------------------
Returns : ∀ {X} → (X → Set) → T∞ X → Set
Returns P m = ∀ (ι : Interp) (h : List SigOpEvent) (r : ℕ) {x r′}
            → proj₂ (run ι h (approx r m)) ≡ returns (done x r′) → P x

private
  thenAp-congP : ∀ {X Y} {P : X → Set} (ι : Interp) (h es : List SigOpEvent) (ρ : Res (Ap X)) (f g : X → T∞ Y)
               → (∀ {x r′} → ρ ≡ returns (done x r′) → P x) → (∀ x → P x → f x ≋ g x)
               → thenAp ι h es ρ f ≡ thenAp ι h es ρ g
  thenAp-congP ι h es stopped              f g p e = refl
  thenAp-congP ι h es (returns cut)        f g p e = refl
  thenAp-congP ι h es (returns (done x r)) f g p e = cong (appE es) (≋r (e x (p refl)) ι (h ++ es) r)

bind-congP : ∀ {X Y} {P : X → Set} (m : T∞ X) (f g : X → T∞ Y)
           → Returns P m → (∀ x → P x → f x ≋ g x) → m >>=∞ f ≋ m >>=∞ g
bind-congP m f g pm e = ≋c λ ι h r →
  trans (run-approx-bind ι h r m f)
  (trans (thenAp-congP ι h (proj₁ (run ι h (approx r m))) (proj₂ (run ι h (approx r m))) f g (pm ι h r) e)
         (sym (run-approx-bind ι h r m g)))

bind-cong : ∀ {X Y} (m : T∞ X) (f g : X → T∞ Y) → (∀ x → f x ≋ g x) → m >>=∞ f ≋ m >>=∞ g
bind-cong {X} m f g e = bind-congP {P = λ _ → ⊤} m f g (λ ι h r eq → tt) (λ x _ → e x)

Returns-ret : ∀ {X} {P : X → Set} {x : X} → P x → Returns P (return∞ x)
Returns-ret p ι h r refl = p

Returns-bind : ∀ {X Y} {P : X → Set} {Q : Y → Set} (m : T∞ X) (f : X → T∞ Y)
             → Returns P m → (∀ x → P x → Returns Q (f x)) → Returns Q (m >>=∞ f)
Returns-bind {P = P} {Q = Q} m f pm fq ι h r {z} {r″} eq =
  go (proj₁ (run ι h (approx r m))) (proj₂ (run ι h (approx r m))) (pm ι h r)
     (trans (sym (cong proj₂ (run-approx-bind ι h r m f))) eq)
  where
    go : ∀ es (ρ : Res (Ap _)) → (∀ {x r′} → ρ ≡ returns (done x r′) → P x)
       → proj₂ (thenAp ι h es ρ f) ≡ returns (done z r″) → Q z
    go es stopped              p ()
    go es (returns cut)        p ()
    go es (returns (done x r₀)) p e = fq x (p refl) ι (h ++ es) r₀ e

------------------------------------------------------------------------
-- THE MODEL, generic in the functor, its carrier and the per-layer algebra.
------------------------------------------------------------------------
module PO {G : Functor} (w : WellFormedF G) {C : Set} (alg : ⟦ G ⟧F C → T∞ C) where

  -- the tree's nodes
  N : Set
  N = ⟦μ⟧ G

  TF : Functor → SFunctor
  TF = translateF Carrier Carrier

  -- the fold's per-layer step (`DenotTrace.cata-ev-algᴰ`'s shape) and the fold
  algD : ⟦ G ⟧F (T∞ C) → T∞ C
  algD fc = seqF∞ G fc >>=∞ alg

  cata : N → T∞ C
  cata = sem-cata w algD

  ----------------------------------------------------------------------
  -- CHILDREN and the LEFT-FIRST POST-ORDER.
  ----------------------------------------------------------------------
  kids : ∀ (H : Functor) → ⟦ H ⟧F N → List N
  kids (K A)     _        = []
  kids Id        t        = [ t ]
  kids (H₁ ⊕ H₂) (inj₁ x) = kids H₁ x
  kids (H₁ ⊕ H₂) (inj₂ y) = kids H₂ y
  kids (H₁ ⊗ H₂) (x , y)  = kids H₁ x ++ kids H₂ y

  -- a node's `Id` children, left to right, read off its layer (`out-μ`)
  children : N → List N
  children t = kids G (sem-Out w t)

  mutual
    po : N → List N
    po ⟨ y ⟩ = poL w y ++ [ ⟨ y ⟩ ]

    poL : ∀ {H} → WellFormedF H → ⟦ TF H ⟧SF N → List N
    poL (wf-K _)      _        = []
    poL wf-Id         t        = po t
    poL (wf-Sum a b)  (inj₁ x) = poL a x
    poL (wf-Sum a b)  (inj₂ y) = poL b y
    poL (wf-Prod a b) (x , y)  = poL a x ++ poL b y

  poAll : List N → List N
  poAll []       = []
  poAll (t ∷ ts) = po t ++ poAll ts

  poAll-++ : ∀ (ts us : List N) → poAll (ts ++ us) ≡ poAll ts ++ poAll us
  poAll-++ []       us = refl
  poAll-++ (t ∷ ts) us = trans (cong (po t ++_) (poAll-++ ts us)) (sym (++-assoc (po t) (poAll ts) (poAll us)))

  private
    poL-kids : ∀ {H} (a : WellFormedF H) (y : ⟦ TF H ⟧SF N) → poL a y ≡ poAll (kids H (coerce-μ-out a N y))
    poL-kids (wf-K _)      y        = refl
    poL-kids wf-Id         t        = sym (++-identityʳ (po t))
    poL-kids (wf-Sum a b)  (inj₁ x) = poL-kids a x
    poL-kids (wf-Sum a b)  (inj₂ y) = poL-kids b y
    poL-kids {H₁ ⊗ H₂} (wf-Prod a b) (x , y)  =
      trans (cong₂ _++_ (poL-kids a x) (poL-kids b y))
            (sym (poAll-++ (kids H₁ (coerce-μ-out a N x)) (kids H₂ (coerce-μ-out b N y))))

  -- the post-order's defining equation
  po-eq : ∀ (t : N) → po t ≡ poAll (children t) ++ [ t ]
  po-eq ⟨ y ⟩ = cong (_++ [ ⟨ y ⟩ ]) (poL-kids w y)

  ----------------------------------------------------------------------
  -- FLATTEN: todo `ts` (top first), eval `es` (top first). `FI ts es` is
  -- the eval stack the loop ends with; one round (pop `t`, push it onto
  -- eval, push its children left to right onto todo) keeps it, and the
  -- measure `length (FI ts [])` drops by one.
  ----------------------------------------------------------------------
  FI : List N → List N → List N
  FI []       es = es
  FI (t ∷ ts) es = FI ts (po t ++ es)

  -- pushing a list onto a stack, its first element first (so its last ends on top)
  pushAll : ∀ {X : Set} → List X → List X → List X
  pushAll []       s = s
  pushAll (k ∷ ks) s = pushAll ks (k ∷ s)

  pushAll-++ : ∀ {X : Set} (ks ks′ s : List X) → pushAll (ks ++ ks′) s ≡ pushAll ks′ (pushAll ks s)
  pushAll-++ []       ks′ s = refl
  pushAll-++ (k ∷ ks) ks′ s = pushAll-++ ks ks′ (k ∷ s)

  FI-++ : ∀ (ts : List N) (X Y : List N) → FI ts (X ++ Y) ≡ FI ts X ++ Y
  FI-++ []       X Y = refl
  FI-++ (t ∷ ts) X Y = trans (cong (FI ts) (sym (++-assoc (po t) X Y))) (FI-++ ts (po t ++ X) Y)

  FI-push : ∀ (ks ts : List N) (X : List N) → FI (pushAll ks ts) X ≡ FI ts (poAll ks ++ X)
  FI-push []       ts X = refl
  FI-push (k ∷ ks) ts X = trans (FI-push ks (k ∷ ts) X) (cong (FI ts) (sym (++-assoc (po k) (poAll ks) X)))

  flatten-step : ∀ (t : N) (ts es : List N) → FI (pushAll (children t) ts) (t ∷ es) ≡ FI (t ∷ ts) es
  flatten-step t ts es =
    trans (FI-push (children t) ts (t ∷ es))
          (cong (FI ts) (trans (sym (++-assoc (poAll (children t)) [ t ] es)) (cong (_++ es) (sym (po-eq t)))))

  flatten-measure : ∀ (t : N) (ts : List N) → suc (length (FI (pushAll (children t) ts) [])) ≡ length (FI (t ∷ ts) [])
  flatten-measure t ts =
    trans (trans (+-comm 1 (length L)) (sym (length-++ L {[ t ]})))
          (cong length (trans (sym (FI-++ (pushAll (children t) ts) [] [ t ])) (flatten-step t ts [])))
    where L = FI (pushAll (children t) ts) []

  -- the loop starts with the root alone on todo, nothing on eval
  flatten-start : ∀ (t : N) → FI [ t ] [] ≡ po t ++ []
  flatten-start t = refl

  ----------------------------------------------------------------------
  -- FILL: rebuild a node's layer from the value stack (top first), one
  -- result per `Id` position, the RIGHT-most popped first (`rebuild-walk`).
  -- `K` payloads and `⊕` tags come from the node's own layer.
  ----------------------------------------------------------------------
  private
    inl-r : ∀ {H₁ H₂ : Functor} → Maybe (⟦ H₁ ⟧F C × List C) → Maybe (⟦ H₁ ⊕ H₂ ⟧F C × List C)
    inl-r nothing           = nothing
    inl-r (just (a , vs))   = just (inj₁ a , vs)

    inr-r : ∀ {H₁ H₂ : Functor} → Maybe (⟦ H₂ ⟧F C × List C) → Maybe (⟦ H₁ ⊕ H₂ ⟧F C × List C)
    inr-r nothing           = nothing
    inr-r (just (b , vs))   = just (inj₂ b , vs)

    pair-r : ∀ {H₁ H₂ : Functor} → ⟦ H₂ ⟧F C → Maybe (⟦ H₁ ⟧F C × List C) → Maybe (⟦ H₁ ⊗ H₂ ⟧F C × List C)
    pair-r b nothing         = nothing
    pair-r b (just (a , vs)) = just ((a , b) , vs)

  mutual
    fill : ∀ (H : Functor) → ⟦ H ⟧F N → List C → Maybe (⟦ H ⟧F C × List C)
    fill (K A)     x        vs       = just (x , vs)
    fill Id        _        []       = nothing
    fill Id        _        (c ∷ vs) = just (c , vs)
    fill (H₁ ⊕ H₂) (inj₁ x) vs       = inl-r {H₁} {H₂} (fill H₁ x vs)
    fill (H₁ ⊕ H₂) (inj₂ y) vs       = inr-r {H₁} {H₂} (fill H₂ y vs)
    fill (H₁ ⊗ H₂) (x , y)  vs       = fill-r H₁ H₂ x (fill H₂ y vs)

    fill-r : ∀ (H₁ H₂ : Functor) → ⟦ H₁ ⟧F N → Maybe (⟦ H₂ ⟧F C × List C) → Maybe (⟦ H₁ ⊗ H₂ ⟧F C × List C)
    fill-r H₁ H₂ x nothing          = nothing
    fill-r H₁ H₂ x (just (b , vs′)) = pair-r {H₁} {H₂} b (fill H₁ x vs′)

  -- what the children's folds leave on the value stack: left first, so the
  -- right-most result is on top
  pushL : ∀ (H : Functor) → ⟦ H ⟧F C → List C → List C
  pushL (K A)     _        vs = vs
  pushL Id        c        vs = c ∷ vs
  pushL (H₁ ⊕ H₂) (inj₁ a) vs = pushL H₁ a vs
  pushL (H₁ ⊕ H₂) (inj₂ b) vs = pushL H₂ b vs
  pushL (H₁ ⊗ H₂) (a , b)  vs = pushL H₂ b (pushL H₁ a vs)

  -- a result layer has the node's shape: its tags and `K` payloads
  SameShape : ∀ (H : Functor) → ⟦ H ⟧F N → ⟦ H ⟧F C → Set
  SameShape (K A)     x        l        = x ≡ l
  SameShape Id        _        _        = ⊤
  SameShape (H₁ ⊕ H₂) (inj₁ x) (inj₁ a) = SameShape H₁ x a
  SameShape (H₁ ⊕ H₂) (inj₁ x) (inj₂ b) = ⊥
  SameShape (H₁ ⊕ H₂) (inj₂ y) (inj₁ a) = ⊥
  SameShape (H₁ ⊕ H₂) (inj₂ y) (inj₂ b) = SameShape H₂ y b
  SameShape (H₁ ⊗ H₂) (x , y)  (a , b)  = SameShape H₁ x a × SameShape H₂ y b

  fill-push : ∀ (H : Functor) (v : ⟦ H ⟧F N) (l : ⟦ H ⟧F C) (vs : List C)
            → SameShape H v l → fill H v (pushL H l vs) ≡ just (l , vs)
  fill-push (K A)     v        .v       vs refl = refl
  fill-push Id        v        l        vs _    = refl
  fill-push (H₁ ⊕ H₂) (inj₁ x) (inj₁ a) vs p  = cong (inl-r {H₁} {H₂}) (fill-push H₁ x a vs p)
  fill-push (H₁ ⊕ H₂) (inj₁ x) (inj₂ b) vs ()
  fill-push (H₁ ⊕ H₂) (inj₂ y) (inj₁ a) vs ()
  fill-push (H₁ ⊕ H₂) (inj₂ y) (inj₂ b) vs p  = cong (inr-r {H₁} {H₂}) (fill-push H₂ y b vs p)
  fill-push (H₁ ⊗ H₂) (x , y)  (a , b)  vs (p , q) =
    trans (cong (fill-r H₁ H₂ x) (fill-push H₂ y b (pushL H₁ a vs) q))
          (cong (pair-r {H₁} {H₂} b) (fill-push H₁ x a vs p))

  -- every result of sequencing a layer of computations has the layer's shape
  seq-shape : ∀ (H : Functor) (f : N → T∞ C) (v : ⟦ H ⟧F N) → Returns (SameShape H v) (seqF∞ H (sem-fmap H f v))
  seq-shape (K A)     f v        = Returns-ret refl
  seq-shape Id        f v        = λ ι h r eq → tt
  seq-shape (H₁ ⊕ H₂) f (inj₁ x) =
    Returns-bind (seqF∞ H₁ (sem-fmap H₁ f x)) (λ u → return∞ (inj₁ u)) (seq-shape H₁ f x) (λ u p → Returns-ret p)
  seq-shape (H₁ ⊕ H₂) f (inj₂ y) =
    Returns-bind (seqF∞ H₂ (sem-fmap H₂ f y)) (λ u → return∞ (inj₂ u)) (seq-shape H₂ f y) (λ u p → Returns-ret p)
  seq-shape (H₁ ⊗ H₂) f (x , y)  =
    Returns-bind (seqF∞ H₁ (sem-fmap H₁ f x)) (λ u → seqF∞ H₂ (sem-fmap H₂ f y) >>=∞ λ b → return∞ (u , b))
      (seq-shape H₁ f x)
      (λ u p → Returns-bind (seqF∞ H₂ (sem-fmap H₂ f y)) (λ b → return∞ (u , b)) (seq-shape H₂ f y)
                 (λ b q → Returns-ret (p , q)))

  ----------------------------------------------------------------------
  -- THE FOLD LOOP: process the nodes in order, top of the value stack first.
  -- (A `nothing` from `fill` — a stack too short — never happens on the
  -- loop's own inputs, `po-run`; it returns junk.)
  ----------------------------------------------------------------------
  mutual
    runPO : List N → List C → T∞ (List C)
    runPO []       vs = return∞ vs
    runPO (n ∷ ns) vs = stepPO ns (fill G (sem-Out w n) vs)

    stepPO : List N → Maybe (⟦ G ⟧F C × List C) → T∞ (List C)
    stepPO ns nothing           = return∞ []
    stepPO ns (just (l , rest)) = alg l >>=∞ λ c → runPO ns (c ∷ rest)

  -- one round of the fold loop, as the machine walks it
  runPO-step : ∀ (n : N) (ns : List N) (vs : List C) {l : ⟦ G ⟧F C} {rest : List C}
             → fill G (sem-Out w n) vs ≡ just (l , rest)
             → runPO (n ∷ ns) vs ≡ (alg l >>=∞ λ c → runPO ns (c ∷ rest))
  runPO-step n ns vs eq = cong (stepPO ns) eq

  runPO-step-run : ∀ (n : N) (ns : List N) (vs : List C) {l : ⟦ G ⟧F C} {rest : List C}
                 → fill G (sem-Out w n) vs ≡ just (l , rest)
                 → ∀ (ι : Interp) (h : List SigOpEvent) (r : ℕ)
                 → run ι h (approx r (runPO (n ∷ ns) vs))
                   ≡ thenAp ι h (proj₁ (run ι h (approx r (alg l)))) (proj₂ (run ι h (approx r (alg l))))
                            (λ c → runPO ns (c ∷ rest))
  runPO-step-run n ns vs {l} {rest} eq ι h r =
    trans (cong (λ m → run ι h (approx r m)) (runPO-step n ns vs eq))
          (run-approx-bind ι h r (alg l) (λ c → runPO ns (c ∷ rest)))

  -- the loop's exit: no node left, the value stack is the result
  runPO-[] : ∀ (vs : List C) (ι : Interp) (h : List SigOpEvent) (r : ℕ)
           → run ι h (approx r (runPO [] vs)) ≡ ([] , returns (done vs r))
  runPO-[] vs ι h r = refl

  ----------------------------------------------------------------------
  -- ONE UNFOLDING of the fold on a node `⟨ y ⟩`, read through `sem-Out`.
  ----------------------------------------------------------------------
  private
    alg″ : ⟦ TF G ⟧SF (T∞ C) → T∞ C
    alg″ x = algD (coerce-μ-out w (T∞ C) x)

    coh-cata : ∀ {H} (a : WellFormedF H) (y : ⟦ TF H ⟧SF N)
             → coerce-μ-out a (T∞ C) (sfmapCata (TF H) alg″ y) ≡ sem-fmap H cata (coerce-μ-out a N y)
    coh-cata (wf-K p)      y        = refl
    coh-cata wf-Id         t        = refl
    coh-cata (wf-Sum a b)  (inj₁ x) = cong inj₁ (coh-cata a x)
    coh-cata (wf-Sum a b)  (inj₂ y) = cong inj₂ (coh-cata b y)
    coh-cata (wf-Prod a b) (x , y)  = cong₂ _,_ (coh-cata a x) (coh-cata b y)

  cata-unfold : ∀ (y : ⟦ TF G ⟧SF N) → cata ⟨ y ⟩ ≡ algD (sem-fmap G cata (sem-Out w ⟨ y ⟩))
  cata-unfold y = cong algD (coh-cata w y)

  ----------------------------------------------------------------------
  -- THE LEMMA: the fold loop over a subtree's post-order runs as the
  -- subtree's cata, its result pushed. Induction on the tree (`po-run`),
  -- inner induction on the functor (`poL-run`, matching `seqF∞`).
  ----------------------------------------------------------------------
  mutual
    po-run : ∀ (t : N) (xs : List N) (vs : List C)
           → runPO (po t ++ xs) vs ≋ (cata t >>=∞ λ c → runPO xs (c ∷ vs))
    po-run ⟨ y ⟩ xs vs =
      ≋-trans (≡→≋ (cong (λ l → runPO l vs) (++-assoc (poL w y) [ ⟨ y ⟩ ] xs)))
      (≋-trans (poL-run w y (⟨ y ⟩ ∷ xs) vs)
      (≋-trans (bind-congP S (λ l → runPO (⟨ y ⟩ ∷ xs) (pushL G l vs)) (λ l → alg l >>=∞ κ)
                 (seq-shape G cata v)
                 (λ l p → ≡→≋ (runPO-step ⟨ y ⟩ xs (pushL G l vs) (fill-push G v l vs p))))
      (≋-trans (≋-sym (bind-assoc S alg κ))
               (≡→≋ (cong (_>>=∞ κ) (sym (cata-unfold y)))))))
      where
        v = sem-Out w ⟨ y ⟩
        S = seqF∞ G (sem-fmap G cata v)
        κ = λ (c : C) → runPO xs (c ∷ vs)

    poL-run : ∀ {H} (a : WellFormedF H) (y : ⟦ TF H ⟧SF N) (xs : List N) (vs : List C)
            → runPO (poL a y ++ xs) vs
              ≋ (seqF∞ H (sem-fmap H cata (coerce-μ-out a N y)) >>=∞ λ l → runPO xs (pushL H l vs))
    poL-run (wf-K p)      y        xs vs = ≋c λ ι h r → refl
    poL-run wf-Id         t        xs vs = po-run t xs vs
    poL-run {H₁ ⊕ H₂} (wf-Sum a b) (inj₁ x) xs vs =
      ≋-trans (poL-run a x xs vs)
        (≋-sym (≋-trans (bind-assoc S₁ (λ u → return∞ (inj₁ u)) κ)
                        (bind-cong S₁ (λ u → return∞ (inj₁ u) >>=∞ κ) (λ u → runPO xs (pushL H₁ u vs))
                                   (λ u → ≋c λ ι h r → refl))))
      where
        S₁ = seqF∞ H₁ (sem-fmap H₁ cata (coerce-μ-out a N x))
        κ  = λ (l : ⟦ H₁ ⊕ H₂ ⟧F C) → runPO xs (pushL (H₁ ⊕ H₂) l vs)
    poL-run {H₁ ⊕ H₂} (wf-Sum a b) (inj₂ y) xs vs =
      ≋-trans (poL-run b y xs vs)
        (≋-sym (≋-trans (bind-assoc S₂ (λ u → return∞ (inj₂ u)) κ)
                        (bind-cong S₂ (λ u → return∞ (inj₂ u) >>=∞ κ) (λ u → runPO xs (pushL H₂ u vs))
                                   (λ u → ≋c λ ι h r → refl))))
      where
        S₂ = seqF∞ H₂ (sem-fmap H₂ cata (coerce-μ-out b N y))
        κ  = λ (l : ⟦ H₁ ⊕ H₂ ⟧F C) → runPO xs (pushL (H₁ ⊕ H₂) l vs)
    poL-run {H₁ ⊗ H₂} (wf-Prod a b) (x , y) xs vs =
      ≋-trans (≡→≋ (cong (λ l → runPO l vs) (++-assoc (poL a x) (poL b y) xs)))
      (≋-trans (poL-run a x (poL b y ++ xs) vs)
      (≋-trans (bind-cong S₁ (λ u → runPO (poL b y ++ xs) (pushL H₁ u vs))
                             (λ u → S₂ >>=∞ λ c → runPO xs (pushL H₂ c (pushL H₁ u vs)))
                             (λ u → poL-run b y xs (pushL H₁ u vs)))
      (≋-sym (≋-trans (bind-assoc S₁ (λ u → S₂ >>=∞ λ c → return∞ (u , c)) κ)
               (bind-cong S₁ (λ u → (S₂ >>=∞ λ c → return∞ (u , c)) >>=∞ κ)
                             (λ u → S₂ >>=∞ λ c → runPO xs (pushL H₂ c (pushL H₁ u vs)))
                             (λ u → ≋-trans (bind-assoc S₂ (λ c → return∞ (u , c)) κ)
                                            (bind-cong S₂ (λ c → return∞ (u , c) >>=∞ κ)
                                                          (λ c → runPO xs (pushL H₂ c (pushL H₁ u vs)))
                                                          (λ c → ≋c λ ι h r → refl))))))))
      where
        S₁ = seqF∞ H₁ (sem-fmap H₁ cata (coerce-μ-out a N x))
        S₂ = seqF∞ H₂ (sem-fmap H₂ cata (coerce-μ-out b N y))
        κ  = λ (l : ⟦ H₁ ⊗ H₂ ⟧F C) → runPO xs (pushL (H₁ ⊗ H₂) l vs)

  ----------------------------------------------------------------------
  -- THE ROOT: the fold loop over the flatten loop's eval stack, from an
  -- empty value stack, runs as the cata, its result the stack's only entry.
  ----------------------------------------------------------------------
  single : Ap C → Ap (List C)
  single (done c r) = done [ c ] r
  single cut        = cut

  singleRun : Run (Ap C) → Run (Ap (List C))
  singleRun R = proj₁ R , mapRes single (proj₂ R)

  private
    thenAp-single : ∀ (ι : Interp) (h es : List SigOpEvent) (ρ : Res (Ap C))
                  → thenAp ι h es ρ (λ c → runPO [] (c ∷ [])) ≡ (es , mapRes single ρ)
    thenAp-single ι h es stopped              = refl
    thenAp-single ι h es (returns cut)        = refl
    thenAp-single ι h es (returns (done c r)) = cong (λ l → l , returns (done [ c ] r)) (++-identityʳ es)

  fold-root : ∀ (t : N) (ι : Interp) (h : List SigOpEvent) (r : ℕ)
            → run ι h (approx r (runPO (FI [ t ] []) [])) ≡ singleRun (run ι h (approx r (cata t)))
  fold-root t ι h r =
    trans (≋r (po-run t [] []) ι h r)
    (trans (run-approx-bind ι h r (cata t) (λ c → runPO [] (c ∷ [])))
           (thenAp-single ι h (proj₁ (run ι h (approx r (cata t)))) (proj₂ (run ι h (approx r (cata t))))))

------------------------------------------------------------------------
-- AT THE IR: the model's algebra is the IR algebra on the coerced layer
-- (`DenotTrace.cata-ev-algᴰ`), and its cata is `evalᴰ (Cata wf alg)`.
------------------------------------------------------------------------
open import Once.IR using (IR; Cata)
open import Once.IRTy using (IRTy; WellFormedFI; ⟦_⟧TI; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute; μ-type)
import Once.IRTy as I
open import Once.IRTy.WF using (wf-⌈⌉)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; coerce-functor⁻¹-D)
open import Once.Spec.Numerics using (TargetNum)
open import Relation.Binary.PropositionalEquality using (subst)
import Once.Denotation.DenotTrace as DT

-- the per-layer algebra the IR's `Cata` runs: the IR algebra on the layer
-- moved to `⟦ ⟦ F ⟧TI C ⟧ᴰᴵ`
cata-alg : ∀ (fmt : TargetNum) (ρ : DT.CallEnv) {F} (wf : WellFormedFI F) {E C : IRTy}
             (alg : IR (E I.* ⟦ F ⟧TI C) C) (e : ⟦ E ⟧ᴰᴵ)
         → ⟦ ⌈ F ⌉F ⟧F ⟦ C ⟧ᴰᴵ → T∞ ⟦ C ⟧ᴰᴵ
cata-alg fmt ρ {F} wf {E} {C} alg e layer =
  DT.evalᴰ fmt ρ alg (e , subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute F C)) (coerce-functor⁻¹-D (wf-⌈⌉ wf) ⌈ C ⌉ layer))

-- the model's cata IS the IR's
cata-is : ∀ (fmt : TargetNum) (ρ : DT.CallEnv) {F} (wf : WellFormedFI F) {E C : IRTy}
            (alg : IR (E I.* ⟦ F ⟧TI C) C) (e : ⟦ E ⟧ᴰᴵ) (x : ⟦ μ-type F ⟧ᴰᴵ)
        → PO.cata (wf-⌈⌉ wf) (cata-alg fmt ρ wf alg e) x ≡ DT.evalᴰ fmt ρ (Cata wf alg) (e , x)
cata-is fmt ρ wf alg e x = refl

-- THE COROLLARY the glue uses: the machine's two loops (flatten from the
-- root, fold from an empty value stack) run as the IR's cata.
cata-br-meaning : ∀ (fmt : TargetNum) (ρ : DT.CallEnv) {F} (wf : WellFormedFI F) {E C : IRTy}
                    (alg : IR (E I.* ⟦ F ⟧TI C) C) (e : ⟦ E ⟧ᴰᴵ) (x : ⟦ μ-type F ⟧ᴰᴵ)
                    (ι : Interp) (h : List SigOpEvent) (r : ℕ)
                → run ι h (approx r (PO.runPO (wf-⌈⌉ wf) (cata-alg fmt ρ wf alg e)
                                         (PO.FI (wf-⌈⌉ wf) (cata-alg fmt ρ wf alg e) [ x ] []) []))
                  ≡ PO.singleRun (wf-⌈⌉ wf) (cata-alg fmt ρ wf alg e)
                      (run ι h (approx r (DT.evalᴰ fmt ρ (Cata wf alg) (e , x))))
cata-br-meaning fmt ρ wf alg e x ι h r = PO.fold-root (wf-⌈⌉ wf) (cata-alg fmt ρ wf alg e) x ι h r
