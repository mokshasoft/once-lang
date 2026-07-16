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
--   * `FO`      — the first-order recursion-scheme fragment of the cartesian
--                 syntax (`id`/`∘`/`fst`/`snd`/`⟨,⟩`/`inl`/`inr`/`case`/
--                 `terminal`/`In`/`cata`) — where linearization is clean (no
--                 exponentials: `curry`/`apply` need the comonoid on the
--                 argument, a separate story);
--   * `L⟦_⟧`    — THE PASS: `FO f → LTm A B`, `fst ↦ fstL`, `⟨f,g⟩ ↦ dup`-
--                 inserting `⟨_,_⟩L`, `terminal ↦ drop`, structurally;
--   * `L-sound` — **semantics preservation**: `Lⁱ (L⟦f⟧) x ≡ eval f x`, by
--                 induction on the fragment (the `cata` case via a fold
--                 congruence `cata-Set-cong`). The pass is meaning-preserving.
--
-- This is the pass PATHS.md flagged as remaining research, POC'd on the clean
-- fragment; what stays open is usage-driven `dup`/`drop` PLACEMENT (here the
-- placement is the canonical one Fox dictates) and the alloc-correctness
-- payoff on top of this soundness.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPLinPass where

open import normalizer.Syntax.Types
  using ( Ty; Func; Id; One; Kc; _⊕_; _⊗_; μ_; ⟦_⟧F
        ; ⊤; tt; _×_; _,_; _⊎_; inj₁; inj₂
        ; _≡_; refl; trans; cong; cong₂ )
open import normalizer.Syntax.CCC as C
  using ( Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_]; terminal; In; cata )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; ⟦_⟧FS; Fix; fix; eval; coherence; coherence⁻¹
        ; cata-Set; map-cata-Set )
open import poc.OCP0009.NbEPLinRec
  using ( LTm; lid; _∘l_; _⊗l_; ρl; ρl⁻; lul; lul⁻; dup; drop
        ; linl; linr; lcase; lIn; lcata; fstL; sndL; ⟨_,_⟩L
        ; DupFree; df-∘; df-id; df-drop; df-linl; df-linr; df-case; df-In
        ; df-cata; fstL-df; sndL-df )

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
------------------------------------------------------------------------

L-sound : ∀ {A B} {f : Term A B} (p : FO f) (x : ⟦ A ⟧T) →
          Lⁱ L⟦ p ⟧ x ≡ eval f x
L-sound fo-id          x        = refl
L-sound (fo-∘ {g = g} p q) x    =
  trans (cong (Lⁱ L⟦ p ⟧) (L-sound q x)) (L-sound p (eval g x))
L-sound fo-fst         (a , b)  = refl
L-sound fo-snd         (a , b)  = refl
L-sound (fo-pair p q)  x        = cong₂ _,_ (L-sound p x) (L-sound q x)
L-sound fo-inl         x        = refl
L-sound fo-inr         x        = refl
L-sound (fo-case p q)  (inj₁ a) = L-sound p a
L-sound (fo-case p q)  (inj₂ b) = L-sound q b
L-sound fo-term        x        = refl
L-sound fo-In          x        = refl
L-sound (fo-cata {F} {alg = alg} p) x =
  cata-Set-cong F (λ y → L-sound p (coherence⁻¹ F _ y)) x

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
