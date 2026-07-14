------------------------------------------------------------------------
-- OCP-0009 · rung 2b part 2, STAGE L0 — THE CLOSED LINEAR CORE: syntax,
--            theory, model, and the bridge from the decided fragment
--
-- The ⊸ expedition begins (agreed ordering: hybrid skeleton ✓ → THIS →
-- re-instantiate the kernel skeleton over the extended core). This
-- stage is deliberately proof-light: fix the OBJECTS of the climb
-- before climbing.
--
--   * `CTy`/`CTm` — the free symmetric monoidal CLOSED category:
--     the SMC generators over `{ι₁, ι₂, I, ⊗}` extended with `_⊸_`,
--     `Λc` (currying) and `evc` (application).
--   * `_≈c_` — the SMCC theory: every SMC axiom, plus the ADJUNCTION
--       β⊸ : ev ∘ (Λf ⊗ 1) ≈ f        η⊸ : Λ(ev ∘ (g ⊗ 1)) ≈ g
--     (β + the universal-property η — together: Hom(A⊗B, C) ≅
--     Hom(A, B⊸C), naturally).
--   * `emb`/`embT`/`embE` — THE BRIDGE: the proven-decidable SMC
--     fragment embeds, and every `≈m`-derivation maps to a
--     `≈c`-derivation. (The converse — conservativity — is exactly
--     what the eventual completeness theorem will yield; recorded.)
--   * `ModelC` — the Set-model with `⟦ A ⊸ B ⟧ = ⟦A⟧ → ⟦B⟧`; β⊸ and
--     η⊸ validated by `refl` (Agda's definitional function-η doing the
--     latter), hexagon/pentagon instances by `refl` pointwise.
--
-- THE INVARIANT ROADMAP (stated now, before it is needed):
--   L1 — polarized leaves + SIGNED resource counting → linearity
--        survives closure (no-diagonal/no-discard for `CTm`).
--   L2 — the Kelly–Mac Lane pairing (polarized wiring: an involution
--        between opposite-polarity atom occurrences) → `≈c-sound` →
--        the REFUTATION oracle for the closed core. KM's theorem says
--        graphs are complete only for `I`-proper shapes — the famous
--        triple-unit obstruction; the pairing is stage-L2 soundness,
--        NOT the final decision procedure.
--   L3 — linear NbE: decide βη-conversion by evaluation into a
--        Kripke model whose worlds are nf-CANONICAL CONTEXTS (leaf
--        lists — the summit's normal forms as the structural quotient,
--        the two towers merging inside the model). The unit problem is
--        the research frontier here; Beylin–Dybjer for stage 3, GoI /
--        proof nets as the fallback semantics.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonL where

open import normalizer.Syntax.Types
  using ( ⊤; tt; Σ; _,_; _≡_; refl )
open import poc.OCP0009.NbEPMon as M
  using ( MTy )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-nat; ƛ-nat; ρ-nat; σ-nat
        ; α-iso₁; α-iso₂; ƛ-iso₁; ƛ-iso₂; ρ-iso₁; ρ-iso₂
        ; σ-invol; pentagon; triangle; hexagon )

------------------------------------------------------------------------
-- Types and terms of the closed linear core.
------------------------------------------------------------------------

infixr 7 _⊗_
infixr 5 _⊸_

data CTy : Set where
  ι₁ ι₂ I : CTy
  _⊗_ : CTy → CTy → CTy
  _⊸_ : CTy → CTy → CTy

infixl 9 _∘c_
infixr 7 _⊗c_

data CTm : CTy → CTy → Set where
  idc  : ∀ {A} → CTm A A
  _∘c_ : ∀ {A B D} → CTm B D → CTm A B → CTm A D
  _⊗c_ : ∀ {A B D E} → CTm A B → CTm D E → CTm (A ⊗ D) (B ⊗ E)
  αrc  : ∀ {A B D} → CTm ((A ⊗ B) ⊗ D) (A ⊗ (B ⊗ D))
  αlc  : ∀ {A B D} → CTm (A ⊗ (B ⊗ D)) ((A ⊗ B) ⊗ D)
  ƛrc  : ∀ {A} → CTm (I ⊗ A) A
  ƛlc  : ∀ {A} → CTm A (I ⊗ A)
  ρrc  : ∀ {A} → CTm (A ⊗ I) A
  ρlc  : ∀ {A} → CTm A (A ⊗ I)
  σc   : ∀ {A B} → CTm (A ⊗ B) (B ⊗ A)
  -- closure: the tensor–hom adjunction, as syntax
  Λc   : ∀ {A B D} → CTm (A ⊗ B) D → CTm A (B ⊸ D)
  evc  : ∀ {A B} → CTm ((A ⊸ B) ⊗ A) B

------------------------------------------------------------------------
-- The SMCC equational theory.
------------------------------------------------------------------------

infix 3 _≈c_

data _≈c_ : ∀ {A B} → CTm A B → CTm A B → Set where
  -- equivalence + congruence
  ≈crefl  : ∀ {A B} {f : CTm A B} → f ≈c f
  ≈csym   : ∀ {A B} {f g : CTm A B} → f ≈c g → g ≈c f
  ≈ctrans : ∀ {A B} {f g h : CTm A B} → f ≈c g → g ≈c h → f ≈c h
  ∘c-cong : ∀ {A B D} {f f' : CTm B D} {g g' : CTm A B} →
            f ≈c f' → g ≈c g' → (f ∘c g) ≈c (f' ∘c g')
  ⊗c-cong : ∀ {A B D E} {f f' : CTm A B} {g g' : CTm D E} →
            f ≈c f' → g ≈c g' → (f ⊗c g) ≈c (f' ⊗c g')
  Λc-cong : ∀ {A B D} {f g : CTm (A ⊗ B) D} → f ≈c g → Λc f ≈c Λc g
  -- category
  cid-l    : ∀ {A B} {f : CTm A B} → (idc ∘c f) ≈c f
  cid-r    : ∀ {A B} {f : CTm A B} → (f ∘c idc) ≈c f
  c∘-assoc : ∀ {A B D E} {f : CTm D E} {g : CTm B D} {h : CTm A B} →
             ((f ∘c g) ∘c h) ≈c (f ∘c (g ∘c h))
  -- ⊗ functoriality
  c⊗-id : ∀ {A B} → (idc {A} ⊗c idc {B}) ≈c idc
  c⊗-∘  : ∀ {A B D X Y Z} {f : CTm B D} {g : CTm A B}
            {h : CTm Y Z} {k : CTm X Y} →
          ((f ∘c g) ⊗c (h ∘c k)) ≈c ((f ⊗c h) ∘c (g ⊗c k))
  -- naturality
  cα-nat : ∀ {A A' B B' D D'}
             {f : CTm A A'} {g : CTm B B'} {h : CTm D D'} →
           (αrc ∘c ((f ⊗c g) ⊗c h)) ≈c ((f ⊗c (g ⊗c h)) ∘c αrc)
  cƛ-nat : ∀ {A A'} {f : CTm A A'} →
           (ƛrc ∘c (idc {I} ⊗c f)) ≈c (f ∘c ƛrc)
  cρ-nat : ∀ {A A'} {f : CTm A A'} →
           (ρrc ∘c (f ⊗c idc {I})) ≈c (f ∘c ρrc)
  cσ-nat : ∀ {A A' B B'} {f : CTm A A'} {g : CTm B B'} →
           (σc ∘c (f ⊗c g)) ≈c ((g ⊗c f) ∘c σc)
  -- iso pairs + involution
  cα-iso₁ : ∀ {A B D} → (αrc {A} {B} {D} ∘c αlc) ≈c idc
  cα-iso₂ : ∀ {A B D} → (αlc {A} {B} {D} ∘c αrc) ≈c idc
  cƛ-iso₁ : ∀ {A} → (ƛrc {A} ∘c ƛlc) ≈c idc
  cƛ-iso₂ : ∀ {A} → (ƛlc {A} ∘c ƛrc) ≈c idc
  cρ-iso₁ : ∀ {A} → (ρrc {A} ∘c ρlc) ≈c idc
  cρ-iso₂ : ∀ {A} → (ρlc {A} ∘c ρrc) ≈c idc
  cσ-invol : ∀ {A B} → (σc {B} {A} ∘c σc {A} {B}) ≈c idc
  -- coherence
  cpentagon : ∀ {A B D E} →
              ((idc {A} ⊗c αrc {B} {D} {E}) ∘c (αrc ∘c (αrc ⊗c idc {E})))
              ≈c (αrc ∘c αrc)
  ctriangle : ∀ {A B} →
              ((idc {A} ⊗c ƛrc {B}) ∘c αrc) ≈c (ρrc ⊗c idc)
  chexagon  : ∀ {A B D} →
              ((idc {B} ⊗c σc {A} {D}) ∘c (αrc ∘c (σc {A} {B} ⊗c idc))) ≈c
              (αrc ∘c (σc {A} {B ⊗ D} ∘c αrc))
  -- THE ADJUNCTION — closure's β and (universal-property) η
  β⊸ : ∀ {A B D} {f : CTm (A ⊗ B) D} →
       (evc ∘c (Λc f ⊗c idc {B})) ≈c f
  η⊸ : ∀ {A B D} {g : CTm A (B ⊸ D)} →
       Λc (evc ∘c (g ⊗c idc {B})) ≈c g

------------------------------------------------------------------------
-- THE BRIDGE — the decided SMC fragment embeds, derivations and all.
------------------------------------------------------------------------

emb : MTy → CTy
emb M.ι₁        = ι₁
emb M.ι₂        = ι₂
emb M.I         = I
emb (M._⊗_ A B) = emb A ⊗ emb B

embT : ∀ {A B} → STm A B → CTm (emb A) (emb B)
embT idm      = idc
embT (f ∘m g) = embT f ∘c embT g
embT (f ⊗m g) = embT f ⊗c embT g
embT αr       = αrc
embT αl       = αlc
embT ƛr       = ƛrc
embT ƛl       = ƛlc
embT ρr       = ρrc
embT ρl       = ρlc
embT σm       = σc

embE : ∀ {A B} {f g : STm A B} → f ≈m g → embT f ≈c embT g
embE ≈refl        = ≈crefl
embE (≈sym p)     = ≈csym (embE p)
embE (≈trans p q) = ≈ctrans (embE p) (embE q)
embE (∘-cong p q) = ∘c-cong (embE p) (embE q)
embE (⊗-cong p q) = ⊗c-cong (embE p) (embE q)
embE id-l         = cid-l
embE id-r         = cid-r
embE ∘-assoc      = c∘-assoc
embE ⊗-id         = c⊗-id
embE ⊗-∘          = c⊗-∘
embE α-nat        = cα-nat
embE ƛ-nat        = cƛ-nat
embE ρ-nat        = cρ-nat
embE σ-nat        = cσ-nat
embE α-iso₁       = cα-iso₁
embE α-iso₂       = cα-iso₂
embE ƛ-iso₁       = cƛ-iso₁
embE ƛ-iso₂       = cƛ-iso₂
embE ρ-iso₁       = cρ-iso₁
embE ρ-iso₂       = cρ-iso₂
embE σ-invol      = cσ-invol
embE pentagon     = cpentagon
embE triangle     = ctriangle
embE hexagon      = chexagon

------------------------------------------------------------------------
-- The Set-model: closure is the function space. β⊸ by `refl`, η⊸ by
-- Agda's definitional function-η.
------------------------------------------------------------------------

module ModelC (X₁ X₂ : Set) where

  ⟦_⟧ : CTy → Set
  ⟦ ι₁ ⟧    = X₁
  ⟦ ι₂ ⟧    = X₂
  ⟦ I ⟧     = ⊤
  ⟦ A ⊗ B ⟧ = Σ ⟦ A ⟧ (λ _ → ⟦ B ⟧)
  ⟦ A ⊸ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

  evalC : ∀ {A B} → CTm A B → ⟦ A ⟧ → ⟦ B ⟧
  evalC idc      x                = x
  evalC (f ∘c g) x                = evalC f (evalC g x)
  evalC (f ⊗c g) (a , b)          = evalC f a , evalC g b
  evalC αrc      ((a , b) , d)    = a , (b , d)
  evalC αlc      (a , (b , d))    = (a , b) , d
  evalC ƛrc      (tt , a)         = a
  evalC ƛlc      a                = tt , a
  evalC ρrc      (a , tt)         = a
  evalC ρlc      a                = a , tt
  evalC σc       (a , b)          = b , a
  evalC (Λc f)   a                = λ b → evalC f (a , b)
  evalC evc      (h , a)          = h a

  -- β⊸, pointwise, by refl:
  _ : ∀ {A B D} (f : CTm (A ⊗ B) D) (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
      evalC (evc ∘c (Λc f ⊗c idc)) (a , b) ≡ evalC f (a , b)
  _ = λ f a b → refl

  -- η⊸, pointwise, by refl (definitional function-η):
  _ : ∀ {A B D} (g : CTm A (B ⊸ D)) (a : ⟦ A ⟧) →
      evalC (Λc (evc ∘c (g ⊗c idc))) a ≡ evalC g a
  _ = λ g a → refl

  -- A hexagon instance, pointwise, by refl:
  _ : ∀ {A B D} (a : ⟦ A ⟧) (b : ⟦ B ⟧) (d : ⟦ D ⟧) →
      evalC ((idc {B} ⊗c σc {A} {D}) ∘c (αrc ∘c (σc {A} {B} ⊗c idc)))
            ((a , b) , d)
      ≡ evalC (αrc ∘c (σc {A} {B ⊗ D} ∘c αrc)) ((a , b) , d)
  _ = λ a b d → refl

  -- Closure interacting with the SMC layer — the "swap arguments"
  -- combinator, and its β-behaviour, by refl:
  flipC : ∀ {A B D} → CTm A (B ⊸ D) → CTm B (A ⊸ D)
  flipC g = Λc (evc ∘c ((g ⊗c idc) ∘c σc))

  _ : ∀ {A B D} (g : CTm A (B ⊸ D)) (a : ⟦ A ⟧) (b : ⟦ B ⟧) →
      evalC (flipC g) b a ≡ evalC g a b
  _ = λ g a b → refl
