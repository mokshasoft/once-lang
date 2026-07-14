------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3D (part 1) — GENERATOR SQUARES: α, ρ, ƛ
--
-- The key lemma (3E) needs, for each structural generator `g : X → Y`, the
-- square `nt Y R ∘ (g ⊗ 1_R) ≈ permM (pOf g) ∘ nt X R`. For `α`, `ƛ`, `ρ`
-- the permutation is the IDENTITY (the accumulator normal form absorbs
-- bracketing and units definitionally), so the squares say: flattening
-- coequalizes the structural isos —
--
--   * `nt-α` — `nt (A⊗(B⊗D)) R ∘ (αr ⊗ 1) ≈ nt ((A⊗B)⊗D) R`. Pentagon
--     (via `PENTL`) + α-naturality. The pentagon axiom's SECOND spending.
--   * `nt-ρ` — `nt A R ∘ (ρr ⊗ 1) ≈ nt (A⊗I) R`. The TRIANGLE axiom,
--     verbatim (one step).
--   * `nt-ƛ` — `nt A R ∘ (ƛr ⊗ 1) ≈ nt (I⊗A) R`. Needs the classical
--     KELLY UNIT-COHERENCE lemma `K2 : ƛ_A ⊗ 1_B ≈ ƛ_{A⊗B} ∘ α_{I,A,B}`,
--     proven here from triangle + pentagon by CANCELLATION OF `1_I ⊗ −`
--     (`cancel-1I`, justified by `ƛ`-naturality conjugation) — the
--     textbook argument (Mac Lane VII.2 / Kelly 1964), machine-checked.
--
-- Also: `pid-real` (the identity permutation realizes the identity).
-- Remaining 3D: `nt-σ` (the bswap square) and the inverse squares.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonG where

open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-nat; ƛ-nat; ρ-nat
        ; α-iso₁; α-iso₂; ƛ-iso₁; ƛ-iso₂; ρ-iso₁; ρ-iso₂
        ; pentagon; triangle )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ; norm; nt )
open import poc.OCP0009.NbEPMonP
  using ( IsL; lnil; lcons; pid; permM; insM; here )
open import poc.OCP0009.NbEPMonY
  using ( fuse⊗ˡ; fuse⊗ʳ; ⊗α-cancelˡ′; ⊗α-cancelʳ; PENTL )

------------------------------------------------------------------------
-- The identity permutation realizes the identity.
------------------------------------------------------------------------

pid-real : ∀ {xs} (r : IsL xs) → permM (pid r) ≈m idm
pid-real lnil         = ≈refl
pid-real (lcons _ r)  =
  ≈trans id-l (≈trans (⊗-cong ≈refl (pid-real r)) ⊗-id)

------------------------------------------------------------------------
-- nt-α — flattening coequalizes the reassociator (pentagon spent).
------------------------------------------------------------------------

nt-α : ∀ {A B D R} →
       (nt (A ⊗ (B ⊗ D)) R ∘m (αr {A} {B} {D} ⊗m idm {R})) ≈m
       nt ((A ⊗ B) ⊗ D) R
nt-α {A} {B} {D} {R} =
  ≈trans ∘-assoc
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congˡ (≈sym fuse⊗ˡ)))
  (≈trans (∘-congʳ (∘-congˡ (∘-congʳ (≈sym fuse⊗ˡ))))
  (≈trans (∘-congʳ (∘-congʳ PENTL))
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ ∘-assoc))
  (≈trans (∘-congʳ (∘-congʳ (∘-congʳ (≈sym ∘-assoc))))
  (≈trans (∘-congʳ (∘-congʳ (∘-congʳ (∘-congˡ ⊗α-cancelˡ′))))
  (≈trans (∘-congʳ (∘-congʳ (∘-congʳ id-l)))
  (≈trans (∘-congʳ (∘-congʳ (≈sym ∘-assoc)))
  (≈trans (∘-congʳ (∘-congʳ (∘-congˡ (≈sym α-nat))))
  (≈trans (∘-congʳ (∘-congʳ (∘-congˡ (∘-congʳ (⊗-cong ⊗-id ≈refl)))))
  (≈trans (∘-congʳ (∘-congʳ ∘-assoc))
          (≈sym rhs-shape))))))))))))))
  where
  rhs-shape : nt ((A ⊗ B) ⊗ D) R ≈m
              (nt A (norm B (norm D R)) ∘m
               ((idm ⊗m nt B (norm D R)) ∘m
                (αr ∘m ((idm ⊗m nt D R) ∘m αr))))
  rhs-shape = ≈trans ∘-assoc (∘-congʳ ∘-assoc)

------------------------------------------------------------------------
-- nt-ρ — the triangle axiom, verbatim.
------------------------------------------------------------------------

nt-ρ : ∀ {A R} →
       (nt A R ∘m (ρr {A} ⊗m idm {R})) ≈m nt (A ⊗ I) R
nt-ρ = ∘-congʳ (≈sym triangle)

------------------------------------------------------------------------
-- Kelly's unit-coherence lemma, and nt-ƛ.
------------------------------------------------------------------------

-- Conjugation by ƛ: every morphism is recovered from its `1_I ⊗ −` image.
conj-ƛ : ∀ {A B} (f : STm A B) → f ≈m ((ƛr ∘m (idm {I} ⊗m f)) ∘m ƛl)
conj-ƛ f =
  ≈trans (≈sym id-r)
  (≈trans (∘-congʳ (≈sym ƛ-iso₁))
  (≈trans (≈sym ∘-assoc)
          (∘-congˡ (≈sym ƛ-nat))))

cancel-1I : ∀ {A B} {f g : STm A B} →
            (idm {I} ⊗m f) ≈m (idm ⊗m g) → f ≈m g
cancel-1I {f = f} {g} p =
  ≈trans (conj-ƛ f)
  (≈trans (∘-congˡ (∘-congʳ p))
          (≈sym (conj-ƛ g)))

-- K2 : ƛ_A ⊗ 1_B ≈ ƛ_{A⊗B} ∘ α — proven under `1_I ⊗ −`, then cancelled.
K2 : ∀ {A B} → (ƛr {A} ⊗m idm {B}) ≈m (ƛr {A ⊗ B} ∘m αr {I} {A} {B})
K2 {A} {B} = cancel-1I (≈trans lhs-red (≈sym rhs-red))
  where
  -- (1_I ⊗ ƛ_X) solved from the triangle: ≈ (ρ_I ⊗ 1_X) ∘ αl.
  tri-solve : ∀ {X} → (idm {I} ⊗m ƛr {X}) ≈m ((ρr ⊗m idm) ∘m αl)
  tri-solve =
    ≈trans (≈sym id-r)
    (≈trans (∘-congʳ (≈sym α-iso₁))
    (≈trans (≈sym ∘-assoc)
            (∘-congˡ triangle)))

  -- 1_I ⊗ (ƛ_A ⊗ 1_B) ≈ αr ∘ ((((ρ_I⊗1_A)⊗1_B) ∘ (αl⊗1_B)) ∘ αl)
  lhs-red : (idm {I} ⊗m (ƛr {A} ⊗m idm {B})) ≈m
            (αr ∘m ((((ρr {I} ⊗m idm {A}) ⊗m idm {B}) ∘m (αl ⊗m idm)) ∘m αl))
  lhs-red =
    ≈trans (≈sym id-r)
    (≈trans (∘-congʳ (≈sym α-iso₁))
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ (≈sym α-nat))
    (≈trans ∘-assoc
            (∘-congʳ (∘-congˡ (≈trans (⊗-cong tri-solve ≈refl)
                                       (≈sym fuse⊗ʳ))))))))

  -- the inverse pair for the pentagon instance at (I,I,A,B)
  cancel-r : ((αr {I} {I ⊗ A} {B} ∘m (αr {I} {I} {A} ⊗m idm {B})) ∘m
              ((αl ⊗m idm) ∘m αl)) ≈m idm
  cancel-r =
    ≈trans ∘-assoc
    (≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (∘-congʳ (∘-congˡ ⊗α-cancelʳ))
    (≈trans (∘-congʳ id-l)
            α-iso₁)))

  -- 1_I ⊗ αr solved from the pentagon (at I,I,A,B).
  pent-solve : (idm {I} ⊗m αr {I} {A} {B}) ≈m
               ((αr ∘m αr) ∘m ((αl {I} {I} {A} ⊗m idm {B}) ∘m αl))
  pent-solve =
    ≈trans (≈sym id-r)
    (≈trans (∘-congʳ (≈sym cancel-r))
    (≈trans (≈sym ∘-assoc)
            (∘-congˡ pentagon)))

  -- αr ∘ ((ρ_I⊗1_A)⊗1_B) ≈ (ρ_I⊗1_{A⊗B}) ∘ αr (α-naturality, 1⊗1 fused).
  ρ-α-nat : ((ρr {I} ⊗m idm {A ⊗ B}) ∘m αr {I ⊗ I} {A} {B}) ≈m
            (αr {I} {A} {B} ∘m ((ρr ⊗m idm) ⊗m idm))
  ρ-α-nat = ≈sym (≈trans α-nat (∘-congˡ (⊗-cong ≈refl ⊗-id)))

  -- 1_I ⊗ (ƛ_{A⊗B} ∘ α) ≈ the same normal form
  rhs-red : (idm {I} ⊗m (ƛr {A ⊗ B} ∘m αr {I} {A} {B})) ≈m
            (αr ∘m ((((ρr {I} ⊗m idm {A}) ⊗m idm {B}) ∘m (αl ⊗m idm)) ∘m αl))
  rhs-red =
    ≈trans (≈sym fuse⊗ˡ)
    (≈trans (∘-congˡ tri-solve)
    (≈trans (∘-congʳ pent-solve)
    (≈trans ∘-assoc
    (≈trans (∘-congʳ (≈sym ∘-assoc))
    (≈trans (∘-congʳ (∘-congˡ (≈sym ∘-assoc)))
    (≈trans (∘-congʳ (∘-congˡ (∘-congˡ α-iso₂)))
    (≈trans (∘-congʳ (∘-congˡ id-l))
    (≈trans (≈sym ∘-assoc)
    (≈trans (∘-congˡ ρ-α-nat)
    (≈trans ∘-assoc
            (∘-congʳ (≈sym ∘-assoc))))))))))))

nt-ƛ : ∀ {A R} →
       (nt A R ∘m (ƛr {A} ⊗m idm {R})) ≈m nt (I ⊗ A) R
nt-ƛ =
  ≈trans (∘-congʳ K2)
  (≈sym (≈trans (≈sym ∘-assoc)
        (≈trans (∘-congˡ ƛ-nat) ∘-assoc)))
