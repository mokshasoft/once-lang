------------------------------------------------------------------------
-- OCP-0009 · LINEARIZATION step 3 — THE PASS, and its correctness
--
-- The linearization PASS itself: translate a CARTESIAN morphism to the linear
-- core (`NbEPLinRec.LTm`), making duplication explicit — every `⟨_,_⟩` emits
-- a `dup`, every discard (`terminal`, a projection's dropped half) emits a
-- `drop`. Its correctness is SEMANTICS PRESERVATION: the linearized term
-- denotes the same function as the source.
--
--   * `Lⁱ`      — a denotational semantics for the linear core (`dup a =
--                 (a,a)`, `drop a = tt` — the sharing/discard made concrete);
--   * `FO`      — the LINEARIZABLE fragment of the cartesian syntax. Since
--                 linearization-6 this includes the EXPONENTIALS
--                 (`fo-curry`/`fo-apply`); what it still omits is `initial`,
--                 `Out`, and the coinductive schemes. (The name is historical:
--                 it was the first-order fragment before closures were added.)
--   * `L⟦_⟧`    — THE PASS: `FO f → LTm A B`, `fst ↦ fstL`, `⟨f,g⟩ ↦ dup`-
--                 inserting `⟨_,_⟩L`, `terminal ↦ drop`, `curry ↦ lcurry`,
--                 `apply ↦ leval`, structurally;
--   * `L-sound` — **semantics preservation**: `Lⁱ (L⟦f⟧) x ≡ eval f x`, by
--                 induction on the fragment (the `cata` case via a fold
--                 congruence `cata-Set-cong`). The pass is meaning-preserving.
--
-- ★ LINEARIZATION-6 — THE EXPONENTIAL GAP, CLOSED. `PATHS.md` deferred
-- `curry`/`apply` as "needing the comonoid on the argument, a separate story".
-- The verdict is that they need NO comonoid at all. In this core `_*_` IS the
-- tensor, so `lcurry : LTm (A * B) C → LTm A (B ⇒ C)` SPLITS the environment
-- from the argument rather than duplicating a shared source, and `leval`
-- consumes closure and argument exactly once each. Both are dup-free
-- (`df-lcurry`/`df-leval`), so `pass-df` extends: **a pairing-free source with
-- closures still linearizes to a fully dup-free term** — closures contribute no
-- duplication of their own. The only cost is `funext`, needed in exactly one
-- clause of `L-sound` (`curry`'s conclusion is an equality of FUNCTIONS), and
-- threaded as a hypothesis per the POC's ground rules — the module stays
-- `--safe` and postulate-free.
--
-- ⚠ WHAT THIS DOES *NOT* SAY — read before quoting `pass-alloc` at closures.
-- `dupCount` is a STATIC count of `dup` generators. With closures the static
-- count stops being the DYNAMIC allocation count: `dupCount (lcurry f) =
-- dupCount f` counts the body's dups ONCE, but the body runs once per
-- application, so a closure applied n times performs n × (its body's dups)
-- allocations. `pass-alloc` remains exactly true as stated (a syntactic
-- identity, and the `fo-curry` case is proven), but "allocations = source
-- pairings" as an OPERATIONAL claim now holds only for closure-free code. This
-- is the same per-node multiplicity issue `PATHS.md` already flags for
-- recursion schemes ("a cata's algebra events × the number of nodes"); closures
-- put it on the exponentials too. A dynamic account needs an event trace, not a
-- count — see `NbEPLinLive` for the shape that would take.
--
-- What stays open after this: usage-driven `dup`/`drop` PLACEMENT for captured
-- environments (here the placement is the canonical one Fox dictates), and the
-- dynamic/multiplicity accounting above.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPLinPass where

open import normalizer.Syntax.Types
  using ( Ty; Func; Id; One; Kc; _⊕_; _⊗_; _*_; μ_; ⟦_⟧F
        ; ⊤; tt; _×_; _,_; _⊎_; inj₁; inj₂
        ; _≡_; refl; trans; cong; cong₂ )
open import normalizer.Syntax.CCC as C
  using ( Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_]; terminal; In; cata
        ; curry; apply )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; ⟦_⟧FS; Fix; fix; eval; coherence; coherence⁻¹
        ; cata-Set; map-cata-Set )
open import poc.OCP0009.NbEPLinRec
  using ( LTm; lid; _∘l_; _⊗l_; ρl; ρl⁻; lul; lul⁻; dup; drop
        ; linl; linr; lcase; lIn; lcata; fstL; sndL; ⟨_,_⟩L
        ; lcurry; leval
        ; DupFree; df-∘; df-⊗; df-id; df-ρl; df-ρl⁻; df-lul; df-lul⁻
        ; df-drop; df-linl; df-linr; df-case; df-In; df-cata; fstL-df; sndL-df
        ; df-lcurry; df-leval )

------------------------------------------------------------------------
-- A denotational semantics for the linear core. `dup`/`drop` are where the
-- copy/discard actually happen — everything else just reshuffles data.
------------------------------------------------------------------------

Lⁱ : ∀ {A B} → LTm A B → ⟦ A ⟧T → ⟦ B ⟧T
Lⁱ lid          x        = x
Lⁱ (f ∘l g)     x        = Lⁱ f (Lⁱ g x)
Lⁱ (f ⊗l g)     (a , b)  = (Lⁱ f a , Lⁱ g b)
Lⁱ ρl           (a , tt) = a
Lⁱ ρl⁻          a        = (a , tt)
Lⁱ lul          (tt , a) = a
Lⁱ lul⁻         a        = (tt , a)
Lⁱ dup          a        = (a , a)
Lⁱ drop         a        = tt
Lⁱ linl         a        = inj₁ a
Lⁱ linr         b        = inj₂ b
Lⁱ (lcase f g)  (inj₁ a) = Lⁱ f a
Lⁱ (lcase f g)  (inj₂ b) = Lⁱ g b
Lⁱ (lIn {F})    x        = fix (coherence F (μ F) x)
Lⁱ (lcata F alg) x       = cata-Set F (λ y → Lⁱ alg (coherence⁻¹ F _ y)) x
-- the closure captures `a` (the tensor's left factor) and awaits `b`.
Lⁱ (lcurry f)   a        = λ b → Lⁱ f (a , b)
Lⁱ leval        (f , a)  = f a

------------------------------------------------------------------------
-- The first-order recursion-scheme fragment of the cartesian syntax.
------------------------------------------------------------------------

data FO : ∀ {A B} → Term A B → Set where
  fo-id    : ∀ {A} → FO (id {A})
  fo-∘     : ∀ {A B C} {f : Term B C} {g : Term A B} → FO f → FO g → FO (f ∘ g)
  fo-fst   : ∀ {A B} → FO (fst {A} {B})
  fo-snd   : ∀ {A B} → FO (snd {A} {B})
  fo-pair  : ∀ {A B C} {f : Term C A} {g : Term C B} → FO f → FO g → FO ⟨ f , g ⟩
  fo-inl   : ∀ {A B} → FO (inl {A} {B})
  fo-inr   : ∀ {A B} → FO (inr {A} {B})
  fo-case  : ∀ {A B C} {f : Term A C} {g : Term B C} → FO f → FO g → FO [ f , g ]
  fo-term  : ∀ {A} → FO (terminal {A})
  fo-In    : ∀ {F} → FO (In {F})
  fo-cata  : ∀ {F A} {alg : Term (⟦ F ⟧F A) A} → FO alg → FO (cata F alg)
  -- exponentials (linearization-6)
  fo-curry : ∀ {A B C} {f : Term (A * B) C} → FO f → FO (curry f)
  fo-apply : ∀ {A B} → FO (apply {A} {B})

------------------------------------------------------------------------
-- THE PASS: cartesian → linear, inserting `dup`/`drop`.
------------------------------------------------------------------------

L⟦_⟧ : ∀ {A B} {f : Term A B} → FO f → LTm A B
L⟦ fo-id ⟧       = lid
L⟦ fo-∘ p q ⟧    = L⟦ p ⟧ ∘l L⟦ q ⟧
L⟦ fo-fst ⟧      = fstL
L⟦ fo-snd ⟧      = sndL
L⟦ fo-pair p q ⟧ = ⟨ L⟦ p ⟧ , L⟦ q ⟧ ⟩L
L⟦ fo-inl ⟧      = linl
L⟦ fo-inr ⟧      = linr
L⟦ fo-case p q ⟧ = lcase L⟦ p ⟧ L⟦ q ⟧
L⟦ fo-term ⟧     = drop
L⟦ fo-In ⟧       = lIn
L⟦ fo-cata {F} p ⟧ = lcata F L⟦ p ⟧
L⟦ fo-curry p ⟧  = lcurry L⟦ p ⟧
L⟦ fo-apply ⟧    = leval

------------------------------------------------------------------------
-- Fold congruence: pointwise-equal algebras give equal folds. (The `cata`
-- case of soundness — the algebras agree only by the IH, not definitionally.)
------------------------------------------------------------------------

mutual
  cata-Set-cong : ∀ F {A} {alg alg' : ⟦ F ⟧FS A → A} →
                  (∀ z → alg z ≡ alg' z) → ∀ y → cata-Set F alg y ≡ cata-Set F alg' y
  cata-Set-cong F {alg' = alg'} h (fix x) =
    trans (h (map-cata-Set F F _ x)) (cong alg' (map-cong F F h x))

  map-cong : ∀ F G {A} {alg alg' : ⟦ F ⟧FS A → A} →
             (∀ z → alg z ≡ alg' z) →
             ∀ x → map-cata-Set F G alg x ≡ map-cata-Set F G alg' x
  map-cong F Id      h x        = cata-Set-cong F h x
  map-cong F One     h x        = refl
  map-cong F (Kc _)  h x        = refl
  map-cong F (G ⊕ H) h (inj₁ y) = cong inj₁ (map-cong F G h y)
  map-cong F (G ⊕ H) h (inj₂ z) = cong inj₂ (map-cong F H h z)
  map-cong F (G ⊗ H) h (y , z)  = cong₂ _,_ (map-cong F G h y) (map-cong F H h z)

------------------------------------------------------------------------
-- SEMANTICS PRESERVATION: the pass preserves meaning.
--
-- `funext` is THREADED, not postulated (the POC's ground rule), and is needed
-- in exactly ONE clause: `curry`'s conclusion equates two FUNCTIONS
-- (`λ b → Lⁱ L⟦p⟧ (x , b)` vs `λ b → eval f (x , b)`), which the IH gives only
-- pointwise. Every other clause is unchanged and funext-free.
------------------------------------------------------------------------

FunExt : Set₁
FunExt = {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

L-sound : FunExt → ∀ {A B} {f : Term A B} (p : FO f) (x : ⟦ A ⟧T) →
          Lⁱ L⟦ p ⟧ x ≡ eval f x
L-sound fe fo-id          x        = refl
L-sound fe (fo-∘ {g = g} p q) x    =
  trans (cong (Lⁱ L⟦ p ⟧) (L-sound fe q x)) (L-sound fe p (eval g x))
L-sound fe fo-fst         (a , b)  = refl
L-sound fe fo-snd         (a , b)  = refl
L-sound fe (fo-pair p q)  x        = cong₂ _,_ (L-sound fe p x) (L-sound fe q x)
L-sound fe fo-inl         x        = refl
L-sound fe fo-inr         x        = refl
L-sound fe (fo-case p q)  (inj₁ a) = L-sound fe p a
L-sound fe (fo-case p q)  (inj₂ b) = L-sound fe q b
L-sound fe fo-term        x        = refl
L-sound fe fo-In          x        = refl
L-sound fe (fo-cata {F} {alg = alg} p) x =
  cata-Set-cong F (λ y → L-sound fe p (coherence⁻¹ F _ y)) x
-- ★ the closure case: pointwise by the IH, then funext.
L-sound fe (fo-curry p)   x        = fe (λ b → L-sound fe p (x , b))
L-sound fe fo-apply       (f , a)  = refl

------------------------------------------------------------------------
-- The payoff, first half: the pass inserts `dup` EXACTLY for pairings.
-- A pairing-free source (its only would-be sharing point removed) linearizes
-- to a fully dup-free — i.e. genuinely linear — term. So every duplication in
-- the output is traceable to one cartesian `⟨_,_⟩`; nothing else copies.
-- (Cf. `NbEPLinRec.para-not-df`: `Para`'s `dup` is one such pairing.)
------------------------------------------------------------------------

data PairFree : ∀ {A B} {f : Term A B} → FO f → Set where
  pf-id   : ∀ {A} → PairFree (fo-id {A})
  pf-∘    : ∀ {A B C} {f : Term B C} {g : Term A B} {p : FO f} {q : FO g} →
            PairFree p → PairFree q → PairFree (fo-∘ p q)
  pf-fst  : ∀ {A B} → PairFree (fo-fst {A} {B})
  pf-snd  : ∀ {A B} → PairFree (fo-snd {A} {B})
  pf-inl  : ∀ {A B} → PairFree (fo-inl {A} {B})
  pf-inr  : ∀ {A B} → PairFree (fo-inr {A} {B})
  pf-case : ∀ {A B C} {f : Term A C} {g : Term B C} {p : FO f} {q : FO g} →
            PairFree p → PairFree q → PairFree (fo-case p q)
  pf-term : ∀ {A} → PairFree (fo-term {A})
  pf-In   : ∀ {F} → PairFree (fo-In {F})
  pf-cata : ∀ {F A} {alg : Term (⟦ F ⟧F A) A} {p : FO alg} →
            PairFree p → PairFree (fo-cata p)
  -- ★ closures: pairing-freedom passes THROUGH a `curry`, and `apply` is a leaf.
  -- This is what makes `pass-df` extend to the exponentials.
  pf-curry : ∀ {A B C} {f : Term (A * B) C} {p : FO f} →
             PairFree p → PairFree (fo-curry p)
  pf-apply : ∀ {A B} → PairFree (fo-apply {A} {B})
  -- (no `pf-pair`: a pairing is the one construct the pass linearizes with `dup`)

pass-df : ∀ {A B} {f : Term A B} {p : FO f} → PairFree p → DupFree L⟦ p ⟧
pass-df pf-id        = df-id
pass-df (pf-∘ p q)   = df-∘ (pass-df p) (pass-df q)
pass-df pf-fst       = fstL-df
pass-df pf-snd       = sndL-df
pass-df pf-inl       = df-linl
pass-df pf-inr       = df-linr
pass-df (pf-case p q) = df-case (pass-df p) (pass-df q)
pass-df pf-term      = df-drop
pass-df pf-In        = df-In
pass-df (pf-cata {F} p) = df-cata F (pass-df p)
pass-df (pf-curry p) = df-lcurry (pass-df p)
pass-df pf-apply     = df-leval

------------------------------------------------------------------------
-- The payoff, quantitative: ALLOCATIONS = SOURCE PAIRINGS. Counting `dup`s in
-- the output (= heap allocations, the one genuine-sharing point) against
-- `⟨_,_⟩`s in the source, they are EQUAL — `AllocMode` is exactly one cell per
-- cartesian pairing, made precise and counted.
------------------------------------------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+ℕ_ : ℕ → ℕ → ℕ
zero  +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

-- Allocations emitted = number of `dup`s in the linear output.
dupCount : ∀ {A B} → LTm A B → ℕ
dupCount lid           = zero
dupCount (f ∘l g)      = dupCount f +ℕ dupCount g
dupCount (f ⊗l g)      = dupCount f +ℕ dupCount g
dupCount ρl            = zero
dupCount ρl⁻           = zero
dupCount lul           = zero
dupCount lul⁻          = zero
dupCount dup           = suc zero
dupCount drop          = zero
dupCount linl          = zero
dupCount linr          = zero
dupCount (lcase f g)   = dupCount f +ℕ dupCount g
dupCount lIn           = zero
dupCount (lcata F alg) = dupCount alg
-- ⚠ STATIC: the body's dups are counted ONCE, but run once per application.
-- See the header's multiplicity caveat before reading this operationally.
dupCount (lcurry f)    = dupCount f
dupCount leval         = zero

-- Pairings in the cartesian source.
pairCount : ∀ {A B} {f : Term A B} → FO f → ℕ
pairCount fo-id         = zero
pairCount (fo-∘ p q)    = pairCount p +ℕ pairCount q
pairCount fo-fst        = zero
pairCount fo-snd        = zero
pairCount (fo-pair p q) = (pairCount p +ℕ pairCount q) +ℕ suc zero
pairCount fo-inl        = zero
pairCount fo-inr        = zero
pairCount (fo-case p q) = pairCount p +ℕ pairCount q
pairCount fo-term       = zero
pairCount fo-In         = zero
pairCount (fo-cata p)   = pairCount p
pairCount (fo-curry p)  = pairCount p
pairCount fo-apply      = zero

pass-alloc : ∀ {A B} {f : Term A B} (p : FO f) → dupCount L⟦ p ⟧ ≡ pairCount p
pass-alloc fo-id         = refl
pass-alloc (fo-∘ p q)    = cong₂ _+ℕ_ (pass-alloc p) (pass-alloc q)
pass-alloc fo-fst        = refl
pass-alloc fo-snd        = refl
pass-alloc (fo-pair p q) = cong₂ _+ℕ_ (cong₂ _+ℕ_ (pass-alloc p) (pass-alloc q)) refl
pass-alloc fo-inl        = refl
pass-alloc fo-inr        = refl
pass-alloc (fo-case p q) = cong₂ _+ℕ_ (pass-alloc p) (pass-alloc q)
pass-alloc fo-term       = refl
pass-alloc fo-In         = refl
pass-alloc (fo-cata p)   = pass-alloc p
pass-alloc (fo-curry p)  = pass-alloc p
pass-alloc fo-apply      = refl

------------------------------------------------------------------------
-- THE BALANCE THEOREM (inductive fragment). "Allocation" = `dup` (the one
-- genuine-sharing point — where a heap cell with a refcount appears);
-- "free" = `drop`. Two facts, both structural, no heap and no trace:
--
--   1. the LINEAR sublanguage allocates nothing — `DupFree ⟹ allocs ≡ 0`;
--   2. the atomic alloc/free pair (`dup` then `drop` the copy) is a semantic
--      NO-OP with matched counts (allocs ≡ frees ≡ 1) — "one free per alloc"
--      = identity. This is `NbEPLinFox.counitR` realized in the semantics.
--
-- So: heap use is exactly the `dup`s the pass inserts for pairings
-- (`pass-alloc`), each cancellable by its `drop` — balance is the counit law,
-- not an operational safety proof.
------------------------------------------------------------------------

frees : ∀ {A B} → LTm A B → ℕ
frees lid           = zero
frees (f ∘l g)      = frees f +ℕ frees g
frees (f ⊗l g)      = frees f +ℕ frees g
frees ρl            = zero
frees ρl⁻           = zero
frees lul           = zero
frees lul⁻          = zero
frees dup           = zero
frees drop          = suc zero
frees linl          = zero
frees linr          = zero
frees (lcase f g)   = frees f +ℕ frees g
frees lIn           = zero
frees (lcata F alg) = frees alg
frees (lcurry f)    = frees f
frees leval         = zero

-- 1. The linear sublanguage is allocation-free.
dupfree-no-alloc : ∀ {A B} {f : LTm A B} → DupFree f → dupCount f ≡ zero
dupfree-no-alloc df-id        = refl
dupfree-no-alloc (df-∘ p q)   = cong₂ _+ℕ_ (dupfree-no-alloc p) (dupfree-no-alloc q)
dupfree-no-alloc (df-⊗ p q)   = cong₂ _+ℕ_ (dupfree-no-alloc p) (dupfree-no-alloc q)
dupfree-no-alloc df-ρl        = refl
dupfree-no-alloc df-ρl⁻       = refl
dupfree-no-alloc df-lul       = refl
dupfree-no-alloc df-lul⁻      = refl
dupfree-no-alloc df-drop      = refl
dupfree-no-alloc df-linl      = refl
dupfree-no-alloc df-linr      = refl
dupfree-no-alloc (df-case p q) = cong₂ _+ℕ_ (dupfree-no-alloc p) (dupfree-no-alloc q)
dupfree-no-alloc df-In        = refl
dupfree-no-alloc (df-cata F p) = dupfree-no-alloc p
dupfree-no-alloc (df-lcurry p) = dupfree-no-alloc p
dupfree-no-alloc df-leval     = refl

-- The canonical alloc/free pair: duplicate `a`, then free the copy.
alloc-free : ∀ {A} → LTm A A
alloc-free = ρl ∘l (lid ⊗l drop) ∘l dup

-- 2a. Matched counts: exactly one alloc and one free.
atomic-balance : ∀ {A} → dupCount (alloc-free {A}) ≡ frees (alloc-free {A})
atomic-balance = refl

-- 2b. …and it is the IDENTITY: one free per alloc cancels (the counit, in
-- the pass semantics). No leak (the alloc is freed), no residue (net identity).
alloc-free-id : ∀ {A} (a : ⟦ A ⟧T) → Lⁱ (alloc-free {A}) a ≡ a
alloc-free-id a = refl
