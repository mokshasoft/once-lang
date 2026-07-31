------------------------------------------------------------------------
-- OCP-0009 · W0e — CODATA IN THE LINEAR CORE.  A SPIKE.
--
-- The blocker W0e records is a TYPING obstruction, not a difficulty:
--
--   `Lᶜ : LTm A B → ⟦ A ⟧C → ⟦ B ⟧C × ℕ`.  For CODATA the cost of a program
--   is not a `ℕ` — an `Ana` never finishes, so there is no finite number of
--   allocations to return.  `Lᶜ` cannot be extended to `ν` by adding a clause;
--   its RESULT TYPE is wrong.
--
-- ★ THE ANSWER, and it is the CLOSURE case again.  `NbEPLinDyn` already solved
-- the same shape at `⇒`: `⟦ A ⇒ B ⟧C = ⟦ A ⟧C → ⟦ B ⟧C × ℕ` — "a function
-- reports its own cost" — so building a closure is FREE and its body is paid at
-- `leval`, once per call.  `ν` is to `nout` what `⇒` is to `leval`:
--
--   * `⟦ νt F ⟧N` is a COINDUCTIVE RECORD whose `force` field is
--     `FS F (Nu F) × ℕ` — **unfolding reports its own cost**;
--   * `nana` builds FREE — nothing runs until observed;
--   * `nout` PAYS, once per observation, exactly one coalgebra step.
--
-- The total cost is then never assembled: there is no `ℕ` to return, and none
-- is asked for.  What replaces "the run costs zero" is a COINDUCTIVE statement
-- — `FreeNu`: every observation, at every depth, costs zero — which is
-- `dyn-linear`'s codata form and matches `NbEPLinLive`'s `□` shape ("inductive
-- balance is a count; coinductive balance is carried by productivity").
--
-- SCOPE.  A SPIKE, standalone: `Ty` has no `ν` and extending it would cascade
-- through the whole POC-0 chain, so this is a minimal object language with only
-- the generators needed to state the result.  `FS`/`Nu` are a private knot, NOT
-- the evaluator's `⟦_⟧FS`/`Fix` — positivity does not see through a re-export.
-- The cost algebra IS `NbEPLinPass`'s `ℕ`/`_+ℕ_`, imported rather than copied,
-- so the claim "this is `dyn-linear`'s codata form" is comparable on the nose.
--
-- `--safe --guardedness` (the `NbEPLinLive` precedent), NO sized types (hard
-- ban, PLAN §1.2), zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}
module poc.OCP0009.SpikeLinNu where

open import normalizer.Syntax.Types
  using ( Func; Id; One; Kc; _⊕_; _⊗_
        ; ⊤; tt; ⊥; ¬_; _×_; _,_; Σ; _⊎_; inj₁; inj₂
        ; _≡_; refl; cong; cong₂ )
open Σ using ( fst; snd )
open import poc.OCP0009.NbEPLinPass using ( ℕ; zero; suc; _+ℕ_ )

------------------------------------------------------------------------
-- 1. THE OBJECT LANGUAGE'S TYPES.  `νt` replaces `μ`; there is no `⇒` — the
--    exponential is W0's story and is not what is being tested here.
------------------------------------------------------------------------

infixr 7 _⊗t_
infixr 6 _⊕t_
data NTy : Set where
  U1   : NTy
  _⊗t_ : NTy → NTy → NTy
  _⊕t_ : NTy → NTy → NTy
  νt   : Func → NTy

-- the functor acting on object types.  `Kc G` is a constant CODE, and in the
-- coinductive reading a code is a `νt` — which keeps `Func` `NTy`-independent,
-- exactly as `⟦_⟧F` keeps it `Ty`-independent.
NF : Func → NTy → NTy
NF Id      X = X
NF One     X = U1
NF (Kc G)  X = νt G
NF (F ⊕ G) X = NF F X ⊕t NF G X
NF (F ⊗ G) X = NF F X ⊗t NF G X

------------------------------------------------------------------------
-- 2. ★ THE FINAL COALGEBRA, CARRYING ITS OWN COST.
--
-- `FS` is a private copy of the evaluator's `⟦_⟧FS` knot, mutual with `Nu`.
-- ⚠ Do NOT try to reuse `⟦_⟧FS` from `Testing.Evaluator`: positivity will not
-- see through the import, and `Nu`'s `force` field would be rejected.
--
-- The cost sits INSIDE the record, on the `force` field.  That is the whole
-- design: an unfolding is a step, a step has a price, and the price is paid by
-- whoever observes — never summed over the (infinite) run.
------------------------------------------------------------------------

mutual
  FS : Func → Set → Set
  FS Id      X = X
  FS One     X = ⊤
  FS (Kc G)  X = Nu G
  FS (F ⊕ G) X = FS F X ⊎ FS G X
  FS (F ⊗ G) X = FS F X × FS G X

  record Nu (F : Func) : Set where
    coinductive
    field
      force : FS F (Nu F) × ℕ
open Nu

⟦_⟧N : NTy → Set
⟦ U1 ⟧N       = ⊤
⟦ A ⊗t B ⟧N   = ⟦ A ⟧N × ⟦ B ⟧N
⟦ A ⊕t B ⟧N   = ⟦ A ⟧N ⊎ ⟦ B ⟧N
⟦ νt F ⟧N     = Nu F

-- the writer monad, verbatim from `NbEPLinDyn`.
retᶜ : ∀ {X : Set} → X → X × ℕ
retᶜ x = (x , zero)

infixl 1 _>>=ᶜ_
_>>=ᶜ_ : ∀ {X Y : Set} → X × ℕ → (X → Y × ℕ) → Y × ℕ
(x , m) >>=ᶜ k = (fst (k x) , (m +ℕ snd (k x)))

-- the functor coherence, at the codata domain.  `Kc G` is the case that makes
-- `NF`'s choice pay off: both sides are `Nu G`, so it is the identity.
cohN : ∀ F X → ⟦ NF F X ⟧N → FS F ⟦ X ⟧N
cohN Id      X x        = x
cohN One     X x        = x
cohN (Kc G)  X x        = x
cohN (F ⊕ G) X (inj₁ x) = inj₁ (cohN F X x)
cohN (F ⊕ G) X (inj₂ y) = inj₂ (cohN G X y)
cohN (F ⊗ G) X (x , y)  = (cohN F X x , cohN G X y)

cohN⁻¹ : ∀ F X → FS F ⟦ X ⟧N → ⟦ NF F X ⟧N
cohN⁻¹ Id      X x        = x
cohN⁻¹ One     X x        = x
cohN⁻¹ (Kc G)  X x        = x
cohN⁻¹ (F ⊕ G) X (inj₁ x) = inj₁ (cohN⁻¹ F X x)
cohN⁻¹ (F ⊕ G) X (inj₂ y) = inj₂ (cohN⁻¹ G X y)
cohN⁻¹ (F ⊗ G) X (x , y)  = (cohN⁻¹ F X x , cohN⁻¹ G X y)

------------------------------------------------------------------------
-- 3. THE LINEAR CORE, with the two codata generators.
--
-- `ndup` is the only generator with a cost, as in `LTm`.  `nout`/`nana` are
-- the additions W0e is about.
------------------------------------------------------------------------

infixr 9 _∘n_
infixr 8 _⊗n_
data NTm : NTy → NTy → Set where
  nid   : ∀ {A} → NTm A A
  _∘n_  : ∀ {A B C} → NTm B C → NTm A B → NTm A C
  _⊗n_  : ∀ {A B C D} → NTm A C → NTm B D → NTm (A ⊗t B) (C ⊗t D)
  ndup  : ∀ {A} → NTm A (A ⊗t A)
  ndrop : ∀ {A} → NTm A U1
  ninl  : ∀ {A B} → NTm A (A ⊕t B)
  ninr  : ∀ {A B} → NTm B (A ⊕t B)
  ncase : ∀ {A B C} → NTm A C → NTm B C → NTm (A ⊕t B) C
  -- ★ observe one coalgebra step
  nout  : ∀ {F} → NTm (νt F) (NF F (νt F))
  -- ★ the anamorphism: a coalgebra `A → F A` becomes a `νt F` producer
  nana  : ∀ {A} F → NTm A (NF F A) → NTm A (νt F)

------------------------------------------------------------------------
-- 4/5. ★ THE COST SEMANTICS, mutual with the unfolding.
--
-- `Nᶜ`'s result type is UNCHANGED — still `⟦ B ⟧N × ℕ`.  That is the finding:
-- codata does not force a different cost monad, it forces the cost to be
-- carried BY THE VALUE.  `nana` returns `(producer , zero)`; the producer's
-- prices are in its `force` fields, where they are paid one at a time.
--
-- `unfoldNu`/`mapU` are the exact dual of the evaluator's
-- `cata-Set`/`map-cata-Set`: `cata` recurses on a shrinking `Fix`, `unfold`
-- corecurses under `force`, and the functor-code descent is identical.
------------------------------------------------------------------------

mutual
  Nᶜ : ∀ {A B} → NTm A B → ⟦ A ⟧N → ⟦ B ⟧N × ℕ
  Nᶜ nid          x        = retᶜ x
  Nᶜ (f ∘n g)     x        = Nᶜ g x >>=ᶜ Nᶜ f
  Nᶜ (f ⊗n g)     (a , b)  = Nᶜ f a >>=ᶜ λ a' → Nᶜ g b >>=ᶜ λ b' → retᶜ (a' , b')
  Nᶜ ndup         a        = ((a , a) , suc zero)   -- ★ THE allocation
  Nᶜ ndrop        a        = retᶜ tt
  Nᶜ ninl         a        = retᶜ (inj₁ a)
  Nᶜ ninr         b        = retᶜ (inj₂ b)
  Nᶜ (ncase f g)  (inj₁ a) = Nᶜ f a
  Nᶜ (ncase f g)  (inj₂ b) = Nᶜ g b
  -- ★ observing PAYS whatever this step reports…
  Nᶜ (nout {F})   x        = (cohN⁻¹ F (νt F) (fst (force x)) , snd (force x))
  -- ★ …and building the producer is FREE.
  Nᶜ (nana F c)   a        = retᶜ (unfoldNu F c a)

  unfoldNu : ∀ {A} F → NTm A (NF F A) → ⟦ A ⟧N → Nu F
  force (unfoldNu {A} F c a) =
    ( mapU F F c (cohN F A (fst (Nᶜ c a))) , snd (Nᶜ c a) )

  mapU : ∀ {A} F G → NTm A (NF F A) → FS G ⟦ A ⟧N → FS G (Nu F)
  mapU F Id      c y        = unfoldNu F c y
  mapU F One     c y        = y
  mapU F (Kc _)  c y        = y
  mapU F (G ⊕ H) c (inj₁ y) = inj₁ (mapU F G c y)
  mapU F (G ⊕ H) c (inj₂ z) = inj₂ (mapU F H c z)
  mapU F (G ⊗ H) c (y , z)  = (mapU F G c y , mapU F H c z)

------------------------------------------------------------------------
-- 6. ★ "ALLOCATES NOTHING", COINDUCTIVELY.
--
-- For the inductive fragment `NbEPLinDyn.Free` is a finite predicate and the
-- payoff is `snd (Lᶜ f x) ≡ zero` — a NUMBER being zero.  At `ν` there is no
-- number, so the property becomes a coinductive record:
--
--     FreeNu F x  =  this observation costs zero  ∧  and so does every one
--                    reachable from it, at every depth, forever
--
-- That is `NbEPLinLive`'s `□` in the cost domain rather than the trace domain,
-- and it is the precise sense in which "linear ⇒ allocates nothing" survives
-- into codata: not as a bound on a total, but as a per-step invariant carried
-- by productivity.
------------------------------------------------------------------------

mutual
  FreeN : ∀ A → ⟦ A ⟧N → Set
  FreeN U1       x        = ⊤
  FreeN (A ⊗t B) (a , b)  = FreeN A a × FreeN B b
  FreeN (A ⊕t B) (inj₁ a) = FreeN A a
  FreeN (A ⊕t B) (inj₂ b) = FreeN B b
  FreeN (νt F)   x        = FreeNu F x

  -- `Free` lifted through a functor code.  Note this doubles as the "every
  -- position of the unfolded step is Free" predicate, because its `Id` case at
  -- `A = νt F` IS `FreeNu F` — so no separate `FreeU` is needed.
  FreeFS : ∀ G {A : NTy} → FS G ⟦ A ⟧N → Set
  FreeFS Id     {A} v        = FreeN A v
  FreeFS One        _        = ⊤
  FreeFS (Kc G)     v        = FreeNu G v
  FreeFS (G ⊕ H)    (inj₁ y) = FreeFS G y
  FreeFS (G ⊕ H)    (inj₂ z) = FreeFS H z
  FreeFS (G ⊗ H)    (y , z)  = FreeFS G y × FreeFS H z

  record FreeNu (F : Func) (x : Nu F) : Set where
    coinductive
    field
      costZero : snd (force x) ≡ zero          -- ★ THIS observation is free…
      next     : FreeFS F {νt F} (fst (force x)) -- ★ …and so is everything after
open FreeNu

freeCohN : ∀ G X (v : ⟦ NF G X ⟧N) → FreeN (NF G X) v → FreeFS G {X} (cohN G X v)
freeCohN Id      X v        fv        = fv
freeCohN One     X v        fv        = tt
freeCohN (Kc G)  X v        fv        = fv
freeCohN (G ⊕ H) X (inj₁ y) fy        = freeCohN G X y fy
freeCohN (G ⊕ H) X (inj₂ z) fz        = freeCohN H X z fz
freeCohN (G ⊗ H) X (y , z)  (fy , fz) =
  (freeCohN G X y fy , freeCohN H X z fz)

freeCohN⁻¹ : ∀ G X (v : FS G ⟦ X ⟧N) → FreeFS G {X} v → FreeN (NF G X) (cohN⁻¹ G X v)
freeCohN⁻¹ Id      X v        fv        = fv
freeCohN⁻¹ One     X v        fv        = tt
freeCohN⁻¹ (Kc G)  X v        fv        = fv
freeCohN⁻¹ (G ⊕ H) X (inj₁ y) fy        = freeCohN⁻¹ G X y fy
freeCohN⁻¹ (G ⊕ H) X (inj₂ z) fz        = freeCohN⁻¹ H X z fz
freeCohN⁻¹ (G ⊗ H) X (y , z)  (fy , fz) =
  (freeCohN⁻¹ G X y fy , freeCohN⁻¹ H X z fz)

------------------------------------------------------------------------
-- The linear sublanguage: every generator but `ndup`.
------------------------------------------------------------------------

data DupFreeN : ∀ {A B} → NTm A B → Set where
  dfn-id   : ∀ {A} → DupFreeN (nid {A})
  dfn-∘    : ∀ {A B C} {f : NTm B C} {g : NTm A B} →
             DupFreeN f → DupFreeN g → DupFreeN (f ∘n g)
  dfn-⊗    : ∀ {A B C D} {f : NTm A C} {g : NTm B D} →
             DupFreeN f → DupFreeN g → DupFreeN (f ⊗n g)
  dfn-drop : ∀ {A} → DupFreeN (ndrop {A})
  dfn-inl  : ∀ {A B} → DupFreeN (ninl {A} {B})
  dfn-inr  : ∀ {A B} → DupFreeN (ninr {A} {B})
  dfn-case : ∀ {A B C} {f : NTm A C} {g : NTm B C} →
             DupFreeN f → DupFreeN g → DupFreeN (ncase f g)
  dfn-out  : ∀ {F} → DupFreeN (nout {F})
  dfn-ana  : ∀ {A F} {c : NTm A (NF F A)} → DupFreeN c → DupFreeN (nana F c)

------------------------------------------------------------------------
-- 7. ★★ THE THEOREM — `dyn-linear` EXTENDED THROUGH `ν`.
--
-- Mixed induction–coinduction, the piece W0e flagged as the risk: `dynN`
-- INDUCTS on the `DupFreeN` derivation while `freeAna` CORECURSES under the
-- `next` copattern.  The two cycles are discharged differently and that is why
-- it goes through —
--
--   · dynN (dfn-ana dc) → freeAna dc → dynN dc  DECREASES on the derivation;
--   · freeAna dc → freeMap dc → freeAna dc      is GUARDED by `next`.
--
-- Read the `ν` cases together and the design is visible: `nana` is free
-- because building allocates nothing, and `nout` is free because the producer
-- carries the proof that its own step was free.
------------------------------------------------------------------------

mutual
  dynN : ∀ {A B} {f : NTm A B} → DupFreeN f → (x : ⟦ A ⟧N) → FreeN A x →
         FreeN B (fst (Nᶜ f x)) × (snd (Nᶜ f x) ≡ zero)
  dynN dfn-id          x        fx        = (fx , refl)
  dynN (dfn-∘ p q)     x        fx        =
    ( fst (dynN p _ (fst (dynN q x fx)))
    , cong₂ _+ℕ_ (snd (dynN q x fx))
                 (snd (dynN p _ (fst (dynN q x fx)))) )
  dynN (dfn-⊗ p q)     (a , b)  (fa , fb) =
    ( ( fst (dynN p a fa) , fst (dynN q b fb) )
    , cong₂ _+ℕ_ (snd (dynN p a fa))
                 (cong₂ _+ℕ_ (snd (dynN q b fb)) refl) )
  dynN dfn-drop        a        fa        = (tt , refl)
  dynN dfn-inl         a        fa        = (fa , refl)
  dynN dfn-inr         b        fb        = (fb , refl)
  dynN (dfn-case p q)  (inj₁ a) fa        = dynN p a fa
  dynN (dfn-case p q)  (inj₂ b) fb        = dynN q b fb
  -- ★ OBSERVING a `Free` producer: the step costs zero because the producer
  --   says so (`costZero`), and the observed shape is `Free` at every position
  --   because it says that too (`next`) — transported across the coherence.
  dynN (dfn-out {F})   x        fx        =
    ( freeCohN⁻¹ F (νt F) (fst (force x)) (next fx) , costZero fx )
  -- ★ BUILDING costs nothing, and the producer IS `FreeNu` — corecursively.
  dynN (dfn-ana dc)    a        fa        = (freeAna dc a fa , refl)

  freeAna : ∀ {A F} {c : NTm A (NF F A)} → DupFreeN c →
            (a : ⟦ A ⟧N) → FreeN A a → FreeNu F (unfoldNu F c a)
  costZero (freeAna dc a fa) = snd (dynN dc a fa)
  next (freeAna {A} {F} {c} dc a fa) =
    freeMap dc F (cohN F A (fst (Nᶜ c a)))
                 (freeCohN F A (fst (Nᶜ c a)) (fst (dynN dc a fa)))

  freeMap : ∀ {A F} {c : NTm A (NF F A)} → DupFreeN c → ∀ G →
            (y : FS G ⟦ A ⟧N) → FreeFS G {A} y → FreeFS G {νt F} (mapU F G c y)
  freeMap dc Id      y        fy        = freeAna dc y fy
  freeMap dc One     y        fy        = tt
  freeMap dc (Kc G)  y        fy        = fy
  freeMap dc (G ⊕ H) (inj₁ y) fy        = freeMap dc G y fy
  freeMap dc (G ⊕ H) (inj₂ z) fz        = freeMap dc H z fz
  freeMap dc (G ⊗ H) (y , z)  (fy , fz) =
    (freeMap dc G y fy , freeMap dc H z fz)

------------------------------------------------------------------------
-- 8. ★ THE NEGATIVE CONTROL — why the result type HAD to change.
--
-- Take `F = Id ⊗ Id`.  Then `NF F A = A ⊗t A`, so a coalgebra `NTm A (NF F A)`
-- is literally `ndup`: the producer that duplicates forever, an infinite binary
-- tree every node of which is an allocation.
--
-- `badAna` BUILDS for free and pays ONE PER OBSERVATION, at every depth,
-- forever (`bad-forever`).  There is therefore no `n : ℕ` that bounds its run —
-- observe `n+1` times and you have paid `n+1`.  This is the concrete witness
-- that `Lᶜ`'s `… → ⟦ B ⟧C × ℕ` cannot be extended to `ν`, and that carrying the
-- cost on `force` is not a stylistic choice.
------------------------------------------------------------------------

badF : Func
badF = Id ⊗ Id

badAna : ∀ {A} → NTm A (νt badF)
badAna = nana badF ndup

badProd : Nu badF
badProd = fst (Nᶜ (badAna {U1}) tt)

-- BUILDING is free…
bad-build-free : snd (Nᶜ (badAna {U1}) tt) ≡ zero
bad-build-free = refl

-- …and EVERY observation costs one.
bad-step : snd (force badProd) ≡ suc zero
bad-step = refl

-- descend the leftmost spine `n` times
spineL : ℕ → Nu badF → Nu badF
spineL zero    x = x
spineL (suc n) x = spineL n (fst (fst (force x)))

-- ★ AT EVERY DEPTH, forever.  No finite total exists.
bad-forever : ∀ n → snd (force (spineL n badProd)) ≡ suc zero
bad-forever zero    = refl
bad-forever (suc n) = bad-forever n

-- and the property has teeth: `badProd` is NOT `FreeNu`, and `badAna` is not
-- in the linear sublanguage to begin with (there is no `dfn-dup`).
bad-not-free : ¬ (FreeNu badF badProd)
bad-not-free fn with costZero fn
... | ()

bad-not-linear : ¬ (DupFreeN (badAna {U1}))
bad-not-linear (dfn-ana ())

------------------------------------------------------------------------
-- ★ THE POSITIVE CONTROL — `FreeNu` is INHABITED, and by something infinite.
--
-- Without this the theorem could be vacuous at `ν`: a coinductive record with
-- an unsatisfiable field is still a legal `Set`.  `nana Id nid` is a genuinely
-- non-terminating producer (it unfolds forever) whose every step is free, and
-- `dynN` proves it so — the whole point, since the inductive statement
-- ("the run costs zero") is not even expressible for it.
------------------------------------------------------------------------

goodAna : NTm U1 (νt Id)
goodAna = nana Id nid

good-linear : DupFreeN goodAna
good-linear = dfn-ana dfn-id

-- free forever, by the theorem — a `□` statement about an infinite run.
good-free : FreeNu Id (fst (Nᶜ goodAna tt))
good-free = fst (dynN good-linear tt tt)

-- and observing it is free too, end to end.
good-observe : DupFreeN (nout {Id} ∘n goodAna)
good-observe = dfn-∘ dfn-out good-linear

good-observe-free : snd (Nᶜ (nout {Id} ∘n goodAna) tt) ≡ zero
good-observe-free = snd (dynN good-observe tt tt)
