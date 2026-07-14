------------------------------------------------------------------------
-- OCP-0009 · rung 2b part 2, STAGE L2a — EXTENSIONAL SOUNDNESS:
--            the refutation oracle for the closed linear core
--
-- The wiring invariant (first-order) had soundness for free; with `⊸`
-- the model has function spaces, so soundness must be EXTENSIONAL —
-- the standard logical-relations move (`NbEPRel`/`NbEPFund`'s shape,
-- replayed for the closed monoidal core):
--
--   * `Ext` — the type-indexed PER on the Set-model: `≡` at atoms,
--     componentwise at `⊗`, related-inputs-to-related-outputs at `⊸`.
--     Proven symmetric and transitive by type recursion.
--   * `evalC-Ext` — THE FUNDAMENTAL LEMMA: every closed-core program
--     respects `Ext`.
--   * `soundE` — SOUNDNESS: `f ≈c g` implies `Ext`-relatedness of the
--     evaluations. The congruence cases are PER plumbing; EVERY axiom
--     case — β⊸ and η⊸ included — is a one-liner `evalC-Ext`, because
--     both sides evaluate to definitionally equal functions (record-η
--     for `⊗`, function-η for `⊸` doing the collapsing).
--   * `no-σc-id` — the refutation oracle at work: σ ≠ id at `ι₁ ⊗ ι₁`
--     in the CLOSED theory (the `conv-refutes` analogue, one level up).
--
-- What this stage does NOT give (and the ledger should not claim):
-- decidability. `Ext` at `⊸` quantifies over the model's function
-- space. The DECISION procedure for the closed core is stage L3
-- (linear NbE / the Kelly–Mac Lane pairing); this stage gives the
-- sound REFUTATION side and the semantic backbone L3 will normalize
-- against.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonX where

open import normalizer.Syntax.Types
  using ( ⊤; tt; ⊥; ¬_; Σ; _,_; _≡_; refl; sym; trans )
open import poc.OCP0009.NbEPMonL as L
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc
        ; Λc; evc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong; Λc-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘
        ; cα-nat; cƛ-nat; cρ-nat; cσ-nat
        ; cα-iso₁; cα-iso₂; cƛ-iso₁; cƛ-iso₂; cρ-iso₁; cρ-iso₂
        ; cσ-invol; cpentagon; ctriangle; chexagon; β⊸; η⊸ )

module ExtModel (X₁ X₂ : Set) where

  open L.ModelC X₁ X₂ public

  --------------------------------------------------------------------
  -- The type-indexed PER.
  --------------------------------------------------------------------

  Ext : ∀ A → ⟦ A ⟧ → ⟦ A ⟧ → Set
  Ext ι₁      x       y         = x ≡ y
  Ext ι₂      x       y         = x ≡ y
  Ext I       _       _         = ⊤
  Ext (A ⊗ B) (a , b) (a' , b') = Σ (Ext A a a') (λ _ → Ext B b b')
  Ext (A ⊸ B) f       g         =
    ∀ {a a'} → Ext A a a' → Ext B (f a) (g a')

  Ext-sym : ∀ A {x y} → Ext A x y → Ext A y x
  Ext-sym ι₁      e         = sym e
  Ext-sym ι₂      e         = sym e
  Ext-sym I       _         = tt
  Ext-sym (A ⊗ B) (ea , eb) = Ext-sym A ea , Ext-sym B eb
  Ext-sym (A ⊸ B) e         = λ r → Ext-sym B (e (Ext-sym A r))

  Ext-trans : ∀ A {x y z} → Ext A x y → Ext A y z → Ext A x z
  Ext-trans ι₁      e₁         e₂         = trans e₁ e₂
  Ext-trans ι₂      e₁         e₂         = trans e₁ e₂
  Ext-trans I       _          _          = tt
  Ext-trans (A ⊗ B) (ea , eb) (ea' , eb') =
    Ext-trans A ea ea' , Ext-trans B eb eb'
  Ext-trans (A ⊸ B) e₁ e₂ =
    λ r → Ext-trans B (e₁ r) (e₂ (Ext-trans A (Ext-sym A r) r))

  --------------------------------------------------------------------
  -- The fundamental lemma: programs respect the PER.
  --------------------------------------------------------------------

  evalC-Ext : ∀ {A B} (f : CTm A B) {x x'} →
              Ext A x x' → Ext B (evalC f x) (evalC f x')
  evalC-Ext idc      r                     = r
  evalC-Ext (f ∘c g) r                     = evalC-Ext f (evalC-Ext g r)
  evalC-Ext (f ⊗c g) (ra , rb)             = evalC-Ext f ra , evalC-Ext g rb
  evalC-Ext αrc      ((ra , rb) , rd)      = ra , (rb , rd)
  evalC-Ext αlc      (ra , (rb , rd))      = (ra , rb) , rd
  evalC-Ext ƛrc      (_ , ra)              = ra
  evalC-Ext ƛlc      ra                    = tt , ra
  evalC-Ext ρrc      (ra , _)              = ra
  evalC-Ext ρlc      ra                    = ra , tt
  evalC-Ext σc       (ra , rb)             = rb , ra
  evalC-Ext (Λc f)   ra                    = λ rb → evalC-Ext f (ra , rb)
  evalC-Ext evc      (rh , ra)             = rh ra

  --------------------------------------------------------------------
  -- Soundness: provable equality is extensional equality.
  --------------------------------------------------------------------

  soundE : ∀ {A B} {f g : CTm A B} → f ≈c g →
           ∀ {x x'} → Ext A x x' → Ext B (evalC f x) (evalC g x')
  soundE {A} {B} (≈crefl {f = f}) r = evalC-Ext f r
  soundE {A} {B} (≈csym p)        r =
    Ext-sym B (soundE p (Ext-sym A r))
  soundE {A} {B} (≈ctrans p q)    r =
    Ext-trans B (soundE p r)
                (soundE q (Ext-trans A (Ext-sym A r) r))
  soundE (∘c-cong p q) r = soundE p (soundE q r)
  soundE (⊗c-cong p q) (ra , rb) = soundE p ra , soundE q rb
  soundE (Λc-cong p)   ra = λ rb → soundE p (ra , rb)
  -- every axiom: both sides evaluate definitionally equal (η!) —
  -- one `evalC-Ext` each.
  soundE (cid-l {f = f})    r = evalC-Ext f r
  soundE (cid-r {f = f})    r = evalC-Ext f r
  soundE (c∘-assoc {f = f} {g} {h}) r = evalC-Ext (f ∘c (g ∘c h)) r
  soundE c⊗-id              r = r
  soundE (c⊗-∘ {f = f} {g} {h} {k}) r =
    evalC-Ext ((f ⊗c h) ∘c (g ⊗c k)) r
  soundE (cα-nat {f = f} {g} {h}) r =
    evalC-Ext ((f ⊗c (g ⊗c h)) ∘c αrc) r
  soundE (cƛ-nat {f = f})   r = evalC-Ext (f ∘c ƛrc) r
  soundE (cρ-nat {f = f})   r = evalC-Ext (f ∘c ρrc) r
  soundE (cσ-nat {f = f} {g}) r = evalC-Ext ((g ⊗c f) ∘c σc) r
  soundE cα-iso₁            r = r
  soundE cα-iso₂            r = r
  soundE cƛ-iso₁            r = r
  soundE cƛ-iso₂            r = r
  soundE cρ-iso₁            r = r
  soundE cρ-iso₂            r = r
  soundE cσ-invol           r = r
  soundE cpentagon          r = evalC-Ext (αrc ∘c αrc) r
  soundE ctriangle          r = evalC-Ext (ρrc ⊗c idc) r
  soundE chexagon           r = evalC-Ext (αrc ∘c (σc ∘c αrc)) r
  soundE (β⊸ {f = f})       r = evalC-Ext f r
  soundE (η⊸ {g = g})       r = evalC-Ext g r

------------------------------------------------------------------------
-- The refutation oracle at work: σ ≠ id in the CLOSED theory.
------------------------------------------------------------------------

private
  data Two : Set where
    t₂ f₂ : Two

no-σc-id : ¬ (σc {ι₁} {ι₁} ≈c idc)
no-σc-id e with M.soundE e {t₂ , f₂} {t₂ , f₂} (refl , refl)
  where module M = ExtModel Two Two
... | (eq , _) with eq
...   | ()
