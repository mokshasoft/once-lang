------------------------------------------------------------------------
-- OCP-0009 · rung 2b part 2, STAGE L1 — POLARIZED COUNTING:
--            linearity SURVIVES closure
--
-- `NbEPMon` proved no-diagonal/no-discard for the ⊗-fragment by plain
-- resource counting. Closure breaks plain counting (`ι₁ ⊸ (ι₁ ⊗ ι₁)`
-- has three `ι₁`s but might still be uninhabited) — the right invariant
-- is SIGNED: count atom occurrences by POLARITY, where the left of `⊸`
-- flips sign. Every morphism preserves the BALANCE (positives minus
-- negatives, stated cross-wise to stay in ℕ):
--
--   bal : (f : CTm A B) → cntP a A + cntN a B ≡ cntN a A + cntP a B
--
-- By induction on `f`: the structural generators are assoc/comm
-- shuffles, `∘c` adds the two equations and cancels the middle, `⊗c` is
-- the interchange, and — the point of the stage — `Λc` is the SAME
-- equation reassociated (currying moves an atom across the turnstile,
-- flipping its polarity on the way: the count is invariant BY DESIGN),
-- `evc` is a four-term commutativity shuffle.
--
-- Corollaries (each a one-`with` refutation):
--   * `no-dupC`     — ¬ CTm ι₁ (ι₁ ⊗ ι₁): duplication inexpressible.
--   * `no-discardC` — ¬ CTm ι₁ I: discard inexpressible.
--   * `no-dup⊸`     — ¬ CTm I (ι₁ ⊸ (ι₁ ⊗ ι₁)): no duplicator VALUE
--     either — closure does not smuggle the diagonal back in.
--   * `no-weakenC`  — ¬ CTm I (ι₁ ⊸ (ι₂ ⊸ ι₁)): THE K COMBINATOR IS
--     UNINHABITED — weakening refuted inside the closed core, the
--     linear-logic classic, machine-checked.
--
-- (The `no-undo` directedness theorem needs a computational generator
-- — `NbEPMon`'s `gen` — which the free closed core deliberately omits;
-- it returns when the kernel core adds transitions.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonV where

open import normalizer.Syntax.Types
  using ( ⊥; ¬_; _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPMon
  using ( ℕ; zero; suc; _+ℕ_; +ℕ-idʳ; +ℕ-comm )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc
        ; Λc; evc )

------------------------------------------------------------------------
-- Arithmetic kit (NbEPMon has idʳ/comm; the rest is local).
------------------------------------------------------------------------

private
  +ℕ-assoc : ∀ m n k → ((m +ℕ n) +ℕ k) ≡ (m +ℕ (n +ℕ k))
  +ℕ-assoc zero    n k = refl
  +ℕ-assoc (suc m) n k = cong suc (+ℕ-assoc m n k)

  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl

  +ℕ-cancelˡ : ∀ k {m n} → (k +ℕ m) ≡ (k +ℕ n) → m ≡ n
  +ℕ-cancelˡ zero    e = e
  +ℕ-cancelˡ (suc k) e = +ℕ-cancelˡ k (suc-inj e)

  +ℕ-cancelʳ : ∀ k {m n} → (m +ℕ k) ≡ (n +ℕ k) → m ≡ n
  +ℕ-cancelʳ k {m} {n} e =
    +ℕ-cancelˡ k (trans (+ℕ-comm k m) (trans e (+ℕ-comm n k)))

  -- (a+b)+(c+d) ≡ (a+c)+(b+d)
  inter : ∀ a b c d → ((a +ℕ b) +ℕ (c +ℕ d)) ≡ ((a +ℕ c) +ℕ (b +ℕ d))
  inter a b c d =
    trans (+ℕ-assoc a b (c +ℕ d))
    (trans (cong (a +ℕ_) (sym (+ℕ-assoc b c d)))
    (trans (cong (λ z → a +ℕ (z +ℕ d)) (+ℕ-comm b c))
    (trans (cong (a +ℕ_) (+ℕ-assoc c b d))
           (sym (+ℕ-assoc a c (b +ℕ d))))))

  -- (a+b)+(c+d) ≡ (a+d)+(c+b)
  swap-mid : ∀ a b c d → ((a +ℕ b) +ℕ (c +ℕ d)) ≡ ((a +ℕ d) +ℕ (c +ℕ b))
  swap-mid a b c d =
    trans (inter a b c d)
    (trans (cong ((a +ℕ c) +ℕ_) (+ℕ-comm b d))
           (sym (inter a d c b)))

------------------------------------------------------------------------
-- Polarized occurrence counting: `⊸` flips the sign on the left.
------------------------------------------------------------------------

data Atom : Set where
  a₁ a₂ : Atom

is₁ : Atom → ℕ
is₁ a₁ = suc zero
is₁ a₂ = zero

is₂ : Atom → ℕ
is₂ a₁ = zero
is₂ a₂ = suc zero

cntP : Atom → CTy → ℕ
cntN : Atom → CTy → ℕ

cntP a ι₁      = is₁ a
cntP a ι₂      = is₂ a
cntP a I       = zero
cntP a (A ⊗ B) = cntP a A +ℕ cntP a B
cntP a (A ⊸ B) = cntN a A +ℕ cntP a B

cntN a ι₁      = zero
cntN a ι₂      = zero
cntN a I       = zero
cntN a (A ⊗ B) = cntN a A +ℕ cntN a B
cntN a (A ⊸ B) = cntP a A +ℕ cntN a B

------------------------------------------------------------------------
-- THE BALANCE INVARIANT.
------------------------------------------------------------------------

bal : ∀ {A B} (a : Atom) (f : CTm A B) →
      (cntP a A +ℕ cntN a B) ≡ (cntN a A +ℕ cntP a B)

bal a (idc {A}) = +ℕ-comm (cntP a A) (cntN a A)

bal a (_∘c_ {A} {B} {D} f g) =
  +ℕ-cancelʳ (cntP a B +ℕ cntN a B)
    (trans (swap-mid (cntP a A) (cntN a D) (cntP a B) (cntN a B))
    (trans (cong₂ _+ℕ_ (bal a g) (bal a f))
    (trans (swap-mid (cntN a A) (cntP a B) (cntN a B) (cntP a D))
           (cong ((cntN a A +ℕ cntP a D) +ℕ_)
                 (+ℕ-comm (cntN a B) (cntP a B))))))

bal a (_⊗c_ {A} {B} {D} {E} f g) =
  trans (inter (cntP a A) (cntP a D) (cntN a B) (cntN a E))
  (trans (cong₂ _+ℕ_ (bal a f) (bal a g))
         (sym (inter (cntN a A) (cntN a D) (cntP a B) (cntP a E))))

bal a (αrc {A} {B} {D}) =
  trans (cong (_+ℕ (cntN a A +ℕ (cntN a B +ℕ cntN a D)))
              (+ℕ-assoc (cntP a A) (cntP a B) (cntP a D)))
  (trans (+ℕ-comm (cntP a A +ℕ (cntP a B +ℕ cntP a D))
                  (cntN a A +ℕ (cntN a B +ℕ cntN a D)))
         (cong (_+ℕ (cntP a A +ℕ (cntP a B +ℕ cntP a D)))
               (sym (+ℕ-assoc (cntN a A) (cntN a B) (cntN a D)))))

bal a (αlc {A} {B} {D}) =
  trans (cong ((cntP a A +ℕ (cntP a B +ℕ cntP a D)) +ℕ_)
              (+ℕ-assoc (cntN a A) (cntN a B) (cntN a D)))
  (trans (+ℕ-comm (cntP a A +ℕ (cntP a B +ℕ cntP a D))
                  (cntN a A +ℕ (cntN a B +ℕ cntN a D)))
         (cong ((cntN a A +ℕ (cntN a B +ℕ cntN a D)) +ℕ_)
               (sym (+ℕ-assoc (cntP a A) (cntP a B) (cntP a D)))))

bal a (ƛrc {A}) = +ℕ-comm (cntP a A) (cntN a A)
bal a (ƛlc {A}) = +ℕ-comm (cntP a A) (cntN a A)

bal a (ρrc {A}) =
  trans (cong (_+ℕ cntN a A) (+ℕ-idʳ (cntP a A)))
  (trans (+ℕ-comm (cntP a A) (cntN a A))
         (cong (_+ℕ cntP a A) (sym (+ℕ-idʳ (cntN a A)))))

bal a (ρlc {A}) =
  trans (cong (cntP a A +ℕ_) (+ℕ-idʳ (cntN a A)))
  (trans (+ℕ-comm (cntP a A) (cntN a A))
         (cong (cntN a A +ℕ_) (sym (+ℕ-idʳ (cntP a A)))))

bal a (σc {A} {B}) =
  trans (+ℕ-comm (cntP a A +ℕ cntP a B) (cntN a B +ℕ cntN a A))
        (cong₂ _+ℕ_ (+ℕ-comm (cntN a B) (cntN a A))
                    (+ℕ-comm (cntP a A) (cntP a B)))

bal a (Λc {A} {B} {D} f) =
  trans (sym (+ℕ-assoc (cntP a A) (cntP a B) (cntN a D)))
  (trans (bal a f)
         (+ℕ-assoc (cntN a A) (cntN a B) (cntP a D)))

bal a (evc {A} {B}) =
  trans (+ℕ-assoc (cntN a A +ℕ cntP a B) (cntP a A) (cntN a B))
  (trans (+ℕ-comm (cntN a A +ℕ cntP a B) (cntP a A +ℕ cntN a B))
         (sym (+ℕ-assoc (cntP a A +ℕ cntN a B) (cntN a A) (cntP a B))))

------------------------------------------------------------------------
-- Corollaries: linearity — and the refusal of weakening — survive
-- closure.
------------------------------------------------------------------------

no-dupC : ¬ CTm ι₁ (ι₁ ⊗ ι₁)
no-dupC m with bal a₁ m
... | ()

no-discardC : ¬ CTm ι₁ I
no-discardC m with bal a₁ m
... | ()

no-dup⊸ : ¬ CTm I (ι₁ ⊸ (ι₁ ⊗ ι₁))
no-dup⊸ m with bal a₁ m
... | ()

-- THE K COMBINATOR IS UNINHABITED: count the ι₂ that K would discard.
no-weakenC : ¬ CTm I (ι₁ ⊸ (ι₂ ⊸ ι₁))
no-weakenC m with bal a₂ m
... | ()
