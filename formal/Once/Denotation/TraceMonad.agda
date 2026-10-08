-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.TraceMonad — the computation monad `T`: INTERACTION TREES
-- (plan 0.105, D-entry "Eff means an interaction tree").
--
-- An effectful arrow `A ⇒[ eff ] B` denotes the Kleisli arrow `⟦A⟧ᴰ → T ⟦B⟧ᴰ`.
-- A computation is a tree:
--
--   * done with a value (`ret`);
--   * a CALL of an answering SigOp, with its argument and a continuation
--     awaiting the answer (`call`) — an output (`Emits`) answers `⊤`, an
--     input answers data, so two reads are two calls with independent
--     answers;
--   * a call of a HALTING SigOp (`halt`, a `Void` codomain), which has no
--     continuation: the program ends there.
--
-- `pure` is the instance with no calls (D250: a pure computation is a value);
-- 0.98's `stopped` is the `halt` node. The tree is INDUCTIVE: Once is total, so
-- every computation makes finitely many calls; it branches over answers.
--
-- WHAT A CALL ANSWERS is not the compiler's business: an INTERPRETATION
-- answers it (`Interp`), given the calls before it. The observable (D058) is
-- the sequence of calls a run makes against an interpretation, capped at an
-- observation depth; correctness quantifies over interpretations.
--
-- Replaces the budget-indexed Writer of plans 0.46–0.98, which could record
-- what a computation emits but let nothing flow back in.
------------------------------------------------------------------------

module Once.Denotation.TraceMonad where

open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (0∸n≡0)
open import Data.List using (List; []; _∷_; _++_; length; take; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Once.Postulates using (extensionality)
open import Once.Res using (Res; stopped; returns; is-stopped; Res-rel; rel-stopped; rel-returns)
open import Once.Type using (Type; isUnit?) renaming (Unit to UnitT)
import Once.Type as Ty
open import Once.Functor.Translate using (IsBaseType)
open import Once.CanonicalName using (CanonicalName; showCanonical; gen)
open import Relation.Nullary using (Dec; yes; no)
import Data.List.Membership.DecPropositional as DecMem
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Functor.Translate using (base-Unit)
open import Once.Word using (Carrier)
import Once.Semantics.Value Carrier Carrier as M
open import Once.Denotation.Trace using (SigOpEvent; mk-event)
open import Once.SigOp.Info using (FFIAnswers)
open import Once.Spec.Contract using (Key; key; kdom; kcod; _∈K?_; ISig; valueKeys; answerKeys; Impl; answerI; pureI)

------------------------------------------------------------------------
-- The operations: one universal signature, keyed by the SigOp's identity
-- and declared types. An answering operation continues with a value of its
-- codomain; a halting one (a `Void` codomain) does not continue.
------------------------------------------------------------------------

record CallOp : Set where
  constructor callOp
  field
    cname  : CanonicalName
    cdom   : Type
    cbase  : IsBaseType cdom
    ccod   : Type
open CallOp

record HaltOp : Set where
  constructor haltOp
  field
    hname  : CanonicalName
    hdom   : Type
    hbase  : IsBaseType hdom
open HaltOp

-- The observable of a call is the call itself: its identity, domain and argument.
callEvent : (o : CallOp) → M.⟦ cdom o ⟧ → SigOpEvent
callEvent o a = mk-event (cname o) (cdom o) (cbase o) a

haltEvent : (o : HaltOp) → M.⟦ hdom o ⟧ → SigOpEvent
haltEvent o a = mk-event (hname o) (hdom o) (hbase o) a

------------------------------------------------------------------------
-- The tree and the monad
------------------------------------------------------------------------

data T (X : Set) : Set where
  ret  : X → T X
  call : (o : CallOp) → M.⟦ cdom o ⟧ → (M.⟦ ccod o ⟧ → T X) → T X
  halt : (o : HaltOp) → M.⟦ hdom o ⟧ → T X

returnT : ∀ {X} → X → T X
returnT = ret

infixl 1 _>>=T_ _>>T_
_>>=T_ : ∀ {X Y} → T X → (X → T Y) → T Y
ret x      >>=T f = f x
call o a k >>=T f = call o a (λ b → k b >>=T f)
halt o a   >>=T f = halt o a

_>>T_ : ∀ {X Y} → T X → T Y → T Y
m >>T k = m >>=T λ _ → k

fmapT : ∀ {X Y} → (X → Y) → T X → T Y
fmapT g m = m >>=T λ x → ret (g x)

-- One call of an answering operation, answered.
callT : (o : CallOp) → M.⟦ cdom o ⟧ → T M.⟦ ccod o ⟧
callT o a = call o a ret

-- A call of a halting operation: the program ends.
haltT : ∀ {X} (o : HaltOp) → M.⟦ hdom o ⟧ → T X
haltT o a = halt o a

------------------------------------------------------------------------
-- The monad laws: EQUALITIES of computations.
------------------------------------------------------------------------

>>=T-identityˡ : ∀ {X Y : Set} (x : X) (f : X → T Y) → (returnT x >>=T f) ≡ f x
>>=T-identityˡ x f = refl

>>=T-identityʳ : ∀ {X : Set} (m : T X) → (m >>=T returnT) ≡ m
>>=T-identityʳ (ret x)      = refl
>>=T-identityʳ (call o a k) = cong (call o a) (extensionality λ b → >>=T-identityʳ (k b))
>>=T-identityʳ (halt o a)   = refl

>>=T-assoc : ∀ {X Y Z : Set} (m : T X) (f : X → T Y) (g : Y → T Z)
           → ((m >>=T f) >>=T g) ≡ (m >>=T λ x → f x >>=T g)
>>=T-assoc (ret x)      f g = refl
>>=T-assoc (call o a k) f g = cong (call o a) (extensionality λ b → >>=T-assoc (k b) f g)
>>=T-assoc (halt o a)   f g = refl

>>=T-cong : ∀ {X Y : Set} (m : T X) {f g : X → T Y} → (∀ x → f x ≡ g x) → (m >>=T f) ≡ (m >>=T g)
>>=T-cong m h = cong (m >>=T_) (extensionality h)

fmapT-id : ∀ {X} (m : T X) → fmapT (λ x → x) m ≡ m
fmapT-id = >>=T-identityʳ

fmapT-∘ : ∀ {X Y Z} (g : Y → Z) (f : X → Y) (m : T X) → fmapT g (fmapT f m) ≡ fmapT (λ x → g (f x)) m
fmapT-∘ g f m = >>=T-assoc m _ _

fmapT-cong : ∀ {X Y} {f g : X → Y} → (∀ x → f x ≡ g x) → (m : T X) → fmapT f m ≡ fmapT g m
fmapT-cong h m = >>=T-cong m λ x → cong ret (h x)

fmapT->>=T : ∀ {X Y Z : Set} (g : X → Y) (m : T X) (f : Y → T Z) → (fmapT g m >>=T f) ≡ (m >>=T λ x → f (g x))
fmapT->>=T g m f = >>=T-assoc m _ f

>>=T-fmapT : ∀ {X Y Z : Set} (g : Y → Z) (m : T X) (f : X → T Y) → fmapT g (m >>=T f) ≡ (m >>=T λ x → fmapT g (f x))
>>=T-fmapT g m f = >>=T-assoc m f _

------------------------------------------------------------------------
-- Running against an interpretation
------------------------------------------------------------------------

callKey : CallOp → Key
callKey o = key (showCanonical (cname o)) (cdom o) (ccod o)


------------------------------------------------------------------------
-- INTERPRETATIONS (D061's three times; plan 0.105, D257 amendment 2)
--
-- Compiling a user program sees only an interpretation's DECLARED signatures
-- (`ISig`) and trusts them; the interpretation's author discharges their
-- contracts OFF-LINE. The FORM of a contract is the compiler's decision
-- (`contractOf`, read off the declared type as the elaborator reads it, D225):
-- interpretations follow the compiler, and the compiler never looks inside one.
------------------------------------------------------------------------

-- An INTERPRETATION: declared signatures with an implementation of them.
record Interp : Set where
  constructor interp
  field
    sig  : ISig
    impl : Impl sig
open Interp public

calls pures : Interp → List Key
calls ι = answerKeys (sig ι)
pures ι = valueKeys (sig ι)

answer : (ι : Interp) → List SigOpEvent → (o : CallOp) → callKey o ∈ calls ι → M.⟦ cdom o ⟧ → M.⟦ ccod o ⟧
answer ι h o p = answerI (impl ι) h (callKey o) p

pure : (ι : Interp) (k : Key) → k ∈ pures ι → M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧
pure ι = pureI (impl ι)

-- The interpretation that declares nothing: interpretations exist.
no-world : Interp
no-world = interp [] (record { answerI = λ _ _ () ; pureI = λ _ () })

-- The RESERVED operation an unlinked call halts on: a call the world does not
-- provide, or an internal call the table does not define (D244).
unlinkedOp : HaltOp
unlinkedOp = haltOp (gen "unlinked") UnitT base-Unit

-- Halting on it.
unlinkedT : ∀ {X} → T X
unlinkedT = halt unlinkedOp tt

-- A partial answer as a computation: a value, or unlinked.
resT : ∀ {X} → Res X → T X
resT (returns x) = ret x
resT stopped     = unlinkedT

-- A world's pure half, as the IR reads it: a provided contract's value, or
-- `stopped` for one it does not provide (unreachable for a linked program).
pureHalf-at : ∀ (ι : Interp) (k : Key) → Dec (k ∈ pures ι) → M.⟦ kdom k ⟧ → Res M.⟦ kcod k ⟧
pureHalf-at ι k (yes p) x = returns (pure ι k p x)
pureHalf-at ι k (no _)  x = stopped

pureHalf : Interp → FFIAnswers
pureHalf ι n A B = pureHalf-at ι (key (showCanonical n) A B) (key (showCanonical n) A B ∈K? pures ι)

-- The calls a run makes, and how it ended.
Run : Set → Set
Run X = List SigOpEvent × Res X

consE : ∀ {X} → SigOpEvent → Run X → Run X
consE e r = (e ∷ proj₁ r) , proj₂ r

appE : ∀ {X} → List SigOpEvent → Run X → Run X
appE es r = (es ++ proj₁ r) , proj₂ r

-- WHAT A CALL RETURNS, by the contract form: an emitting call (into `Unit`)
-- returns `tt` — it owes no answer; a declared answering call returns the
-- implementation's answer, given the calls before it; anything else has no
-- answer, and the run halts on the reserved operation (unreachable for a
-- program linked against the interpretation's signatures).
callAnswer-at : (ι : Interp) → List SigOpEvent → (o : CallOp) → M.⟦ cdom o ⟧
              → Dec (ccod o ≡ UnitT) → Dec (callKey o ∈ calls ι) → Maybe M.⟦ ccod o ⟧
callAnswer-at ι h o a (yes u) _       = just (subst M.⟦_⟧ (sym u) tt)
callAnswer-at ι h o a (no _)  (yes p) = just (answer ι h o p a)
callAnswer-at ι h o a (no _)  (no _)  = nothing

callAnswer : (ι : Interp) → List SigOpEvent → (o : CallOp) → M.⟦ cdom o ⟧ → Maybe M.⟦ ccod o ⟧
callAnswer ι h o a = callAnswer-at ι h o a (isUnit? (ccod o)) (callKey o ∈K? calls ι)

run      : ∀ {X} → Interp → List SigOpEvent → T X → Run X
run-call : ∀ {X} (ι : Interp) → List SigOpEvent → (o : CallOp) → M.⟦ cdom o ⟧ → (M.⟦ ccod o ⟧ → T X)
         → Maybe M.⟦ ccod o ⟧ → Run X
run ι h (ret x)      = [] , returns x
run ι h (call o a k) = run-call ι h o a k (callAnswer ι h o a)
run ι h (halt o a)   = [ haltEvent o a ] , stopped
run-call ι h o a k (just b) = consE (callEvent o a) (run ι (h ++ [ callEvent o a ]) (k b))
run-call ι h o a k nothing  = [ haltEvent unlinkedOp tt ] , stopped

-- Sequencing: the second run sees the first's calls.
thenRes : ∀ {X Y} → Interp → List SigOpEvent → List SigOpEvent → Res X → (X → T Y) → Run Y
thenRes ι h es stopped     f = es , stopped
thenRes ι h es (returns x) f = appE es (run ι (h ++ es) (f x))

then : ∀ {X Y} → Interp → List SigOpEvent → Run X → (X → T Y) → Run Y
then ι h r f = thenRes ι h (proj₁ r) (proj₂ r) f

-- THE RUN OF A BIND IS THE RUNS OF ITS PARTS, the history threaded.
mutual
  run-bind : ∀ {X Y} (ι : Interp) (h : List SigOpEvent) (m : T X) (f : X → T Y)
           → run ι h (m >>=T f) ≡ then ι h (run ι h m) f
  run-bind ι h (ret x)      f = cong (λ hh → run ι hh (f x)) (sym (++-identityʳ h))
  run-bind ι h (call o a k) f = run-bind-call ι h o a k f (callAnswer ι h o a)
  run-bind ι h (halt o a)   f = refl

  run-bind-call : ∀ {X Y} (ι : Interp) (h : List SigOpEvent) (o : CallOp) (a : M.⟦ cdom o ⟧)
                    (k : M.⟦ ccod o ⟧ → T X) (f : X → T Y) (mb : Maybe M.⟦ ccod o ⟧)
                → run-call ι h o a (λ b → k b >>=T f) mb ≡ then ι h (run-call ι h o a k mb) f
  run-bind-call ι h o a k f (just b) =
    trans (cong (consE (callEvent o a)) (run-bind ι (h ++ [ callEvent o a ]) (k b) f))
          (cons-then ι h (callEvent o a)
             (proj₁ (run ι (h ++ [ callEvent o a ]) (k b))) (proj₂ (run ι (h ++ [ callEvent o a ]) (k b))) f)
  run-bind-call ι h o a k f nothing = refl

  cons-then : ∀ {X Y} ι h e es (r : Res X) (f : X → T Y)
            → consE e (then ι (h ++ [ e ]) (es , r) f) ≡ then ι h (consE e (es , r)) f
  cons-then ι h e es stopped     f = refl
  cons-then ι h e es (returns x) f = cong (λ hh → appE (e ∷ es) (run ι hh (f x))) (++-assoc h [ e ] es)

------------------------------------------------------------------------
-- The observable (D058): the first n calls of a run from the empty history.
------------------------------------------------------------------------

eventsT : ∀ {X} → Interp → T X → List SigOpEvent
eventsT ι m = proj₁ (run ι [] m)

resultT : ∀ {X} → Interp → T X → Res X
resultT ι m = proj₂ (run ι [] m)

projTrace : ∀ {X} → Interp → T X → ℕ → List SigOpEvent
projTrace ι m n = take n (eventsT ι m)

atT : ∀ {X} → Interp → T X → ℕ → List SigOpEvent × Res X
atT ι m n = projTrace ι m n , resultT ι m

Stopped : Set
Stopped = Bool

stoppedT : ∀ {X} → Interp → T X → Stopped
stoppedT ι m = is-stopped (resultT ι m)

------------------------------------------------------------------------
-- A run's observable is a prefix family — for EVERY computation, because it
-- is a cap of one finite list.
------------------------------------------------------------------------

length-take-≤ : ∀ k (xs : List SigOpEvent) → length (take k xs) ≤ k
length-take-≤ zero    _        = z≤n
length-take-≤ (suc _) []       = z≤n
length-take-≤ (suc k) (_ ∷ xs) = s≤s (length-take-≤ k xs)

take-sat : ∀ k (xs : List SigOpEvent) → length (take k xs) < k → take (suc k) xs ≡ take k xs
take-sat (suc _) []       _        = refl
take-sat (suc k) (x ∷ xs) (s≤s lt) = cong (x ∷_) (take-sat k xs lt)

take-coh : ∀ k (xs : List SigOpEvent) → ∃[ rest ] (take (suc k) xs ≡ take k xs ++ rest)
take-coh zero    []       = [] , refl
take-coh (suc k) []       = [] , refl
take-coh zero    (x ∷ xs) = [ x ] , refl
take-coh (suc k) (x ∷ xs) = proj₁ (take-coh k xs) , cong (x ∷_) (proj₂ (take-coh k xs))

Bounded : (ℕ → List SigOpEvent) → Set
Bounded tr = ∀ k → length (tr k) ≤ k

Saturating : (ℕ → List SigOpEvent) → Set
Saturating tr = ∀ k → length (tr k) < k → tr (suc k) ≡ tr k

Coherent : (ℕ → List SigOpEvent) → Set
Coherent tr = ∀ k → ∃[ rest ] (tr (suc k) ≡ tr k ++ rest)

record PrefixFamily (tr : ℕ → List SigOpEvent) : Set where
  constructor prefixFamily
  field
    bnd : Bounded tr
    sat : Saturating tr
    coh : Coherent tr

take-pf : ∀ (xs : List SigOpEvent) → PrefixFamily (λ n → take n xs)
take-pf xs = prefixFamily (λ k → length-take-≤ k xs) (λ k → take-sat k xs) (λ k → take-coh k xs)

projTrace-pf : ∀ {X} (ι : Interp) (m : T X) → PrefixFamily (projTrace ι m)
projTrace-pf ι m = take-pf (eventsT ι m)

------------------------------------------------------------------------
-- Results
------------------------------------------------------------------------

Returns? : ∀ {X} → Res X → Set
Returns? stopped     = ⊥
Returns? (returns _) = ⊤

resVal : ∀ {X} (r : Res X) → Returns? r → X
resVal (returns x) _ = x
resVal stopped     ()

resVal-returns : ∀ {X} (r : Res X) (p : Returns? r) → r ≡ returns (resVal r p)
resVal-returns (returns x) _ = refl

-- A computation's result run MID-PROGRAM: against the interpretation, after
-- the calls `h` already made. An answering call's answer depends on `h`, so a
-- sub-computation's value is only defined at a history (the machine's log).
resultAt : ∀ {X} → Interp → List SigOpEvent → T X → Res X
resultAt ι h m = proj₂ (run ι h m)

-- The value it returns there, given that it does.
valueT : ∀ {X} (ι : Interp) (h : List SigOpEvent) (m : T X) {p : Returns? (resultAt ι h m)} → X
valueT ι h m {p} = resVal (resultAt ι h m) p

-- A relation on results, lifted (`stopped` relates only to `stopped`).
RelRes : ∀ {X Y : Set} (R : X → Y → Set) → Res X → Res Y → Set
RelRes = Res-rel

------------------------------------------------------------------------
-- Related computations: the SAME tree, related leaves.
--
-- Two computations are related when they make the same calls with the same
-- arguments, continue relatedly at EVERY answer, halt alike, and return
-- related values. This is the relational lifting of the tree; the old
-- budget-indexed relation (same trace prefix at every budget, related results)
-- is its observational consequence (`RelT′-run`), not its definition.
------------------------------------------------------------------------

data RelT′ {X Y : Set} (R : X → Y → Set) : T X → T Y → Set where
  rel-ret  : ∀ {x y} → R x y → RelT′ R (ret x) (ret y)
  rel-call : ∀ {o a} {k : M.⟦ ccod o ⟧ → T X} {k′ : M.⟦ ccod o ⟧ → T Y}
           → (∀ b → RelT′ R (k b) (k′ b)) → RelT′ R (call o a k) (call o a k′)
  rel-halt : ∀ {o a} → RelT′ R (halt o a) (halt o a)

RelT′-bind : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
             {m : T X} {m′ : T X′} {f : X → T Y} {f′ : X′ → T Y′}
           → RelT′ R m m′ → (∀ x x′ → R x x′ → RelT′ S (f x) (f′ x′))
           → RelT′ S (m >>=T f) (m′ >>=T f′)
RelT′-bind R S (rel-ret r)  hf = hf _ _ r
RelT′-bind R S (rel-call h) hf = rel-call λ b → RelT′-bind R S (h b) hf
RelT′-bind R S rel-halt     hf = rel-halt

RelT′-fmap : ∀ {X Y X′ Y′ : Set} (R : X → X′ → Set) (S : Y → Y′ → Set)
             {g : X → Y} {g′ : X′ → Y′} {m : T X} {m′ : T X′}
           → (∀ x x′ → R x x′ → S (g x) (g′ x′))
           → RelT′ R m m′ → RelT′ S (fmapT g m) (fmapT g′ m′)
RelT′-fmap R S hg rm = RelT′-bind R S rm λ x x′ r → rel-ret (hg x x′ r)

RelT′-refl : ∀ {X : Set} {R : X → X → Set} → (∀ x → R x x) → (m : T X) → RelT′ R m m
RelT′-refl hr (ret x)      = rel-ret (hr x)
RelT′-refl hr (call o a k) = rel-call λ b → RelT′-refl hr (k b)
RelT′-refl hr (halt o a)   = rel-halt

-- At a functional relation, relatedness IS an equation.
RelT′-≡ : ∀ {X Y : Set} (g : X → Y) {m : T X} {m′ : T Y}
        → RelT′ (λ x y → g x ≡ y) m m′ → fmapT g m ≡ m′
RelT′-≡ g (rel-ret refl) = refl
RelT′-≡ g (rel-call h)   = cong (call _ _) (extensionality λ b → RelT′-≡ g (h b))
RelT′-≡ g rel-halt       = refl

≡-RelT′ : ∀ {X Y : Set} (g : X → Y) (m : T X) {m′ : T Y}
        → fmapT g m ≡ m′ → RelT′ (λ x y → g x ≡ y) m m′
≡-RelT′ g m refl = to-fmap m
  where
    to-fmap : (m : T _) → RelT′ (λ x y → g x ≡ y) m (fmapT g m)
    to-fmap (ret x)      = rel-ret refl
    to-fmap (call o a k) = rel-call λ b → to-fmap (k b)
    to-fmap (halt o a)   = rel-halt

-- Related computations RUN alike: against any interpretation, from any
-- history, they make the same calls and end relatedly.
RelT′-events : ∀ {X Y : Set} {R : X → Y → Set} (ι : Interp) (h : List SigOpEvent) {m : T X} {m′ : T Y}
             → RelT′ R m m′ → proj₁ (run ι h m) ≡ proj₁ (run ι h m′)
RelT′-events ι h (rel-ret _)  = refl
RelT′-events ι h (rel-call {o} {a} hk) = go (callAnswer ι h o a)
  where go : (mb : Maybe M.⟦ ccod o ⟧) → proj₁ (run-call ι h o a _ mb) ≡ proj₁ (run-call ι h o a _ mb)
        go (just b) = cong (callEvent o a ∷_) (RelT′-events ι (h ++ [ callEvent o a ]) (hk b))
        go nothing  = refl
RelT′-events ι h rel-halt     = refl

RelT′-result : ∀ {X Y : Set} {R : X → Y → Set} (ι : Interp) (h : List SigOpEvent) {m : T X} {m′ : T Y}
             → RelT′ R m m′ → RelRes R (resultAt ι h m) (resultAt ι h m′)
RelT′-result ι h (rel-ret r)  = rel-returns r
RelT′-result ι h (rel-call {o} {a} hk) = go (callAnswer ι h o a)
  where go : (mb : Maybe M.⟦ ccod o ⟧) → RelRes _ (proj₂ (run-call ι h o a _ mb)) (proj₂ (run-call ι h o a _ mb))
        go (just b) = RelT′-result ι (h ++ [ callEvent o a ]) (hk b)
        go nothing  = rel-stopped
RelT′-result ι h rel-halt     = rel-stopped

------------------------------------------------------------------------
-- List arithmetic the observable proofs use
------------------------------------------------------------------------

take-++-split : ∀ {A : Set} (k : ℕ) (as bs : List A)
              → take k (as ++ bs) ≡ take k as ++ take (k ∸ length as) bs
take-++-split zero    as       bs = sym (cong (λ m → take m bs) (0∸n≡0 (length as)))
take-++-split (suc k) []       bs = refl
take-++-split (suc k) (a ∷ as) bs = cong (a ∷_) (take-++-split k as bs)

minus-take : ∀ {A : Set} (k : ℕ) (as : List A)
           → k ∸ length (take k as) ≡ k ∸ length as
minus-take zero    as       = sym (0∸n≡0 (length as))
minus-take (suc k) []       = refl
minus-take (suc k) (a ∷ as) = minus-take k as

take-++-threaded : ∀ {A : Set} (k : ℕ) (as bs : List A)
                 → take k (as ++ bs)
                   ≡ take k as ++ take (k ∸ length (take k as)) bs
take-++-threaded k as bs =
  trans (take-++-split k as bs)
        (cong (λ m → take k as ++ take m bs) (sym (minus-take k as)))
