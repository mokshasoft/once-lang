------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3E — THE SUMMIT: COMPLETENESS
--
--   dec≈ : ∀ f g → Dec (f ≈m g)
--
-- Conversion for the free symmetric monoidal category is DECIDABLE: the
-- wiring is a COMPLETE invariant. Soundness (`≈m-sound`, the base camp)
-- said provably-equal morphisms wire alike; this module proves the
-- converse — morphisms that wire alike are provably equal — so `conv?`
-- upgrades from a refutation oracle to a full decision procedure for the
-- linear core's equality. No rewriting, no confluence, all `--safe`.
--
-- The assembly (everything below is plumbing on proven parts):
--   * `nt-ƛl`/`nt-ρl` — the last two inverse generator squares, by the
--     `nt-αl` conjugation pattern (one `fuse⊗ʳ`, one iso, done).
--   * `pOf f r` — THE PERMUTATION OF A MORPHISM, by recursion on `f`:
--     identity ↦ `pid`; composition ↦ `⊙P`; tensor ↦ `⊙P` + `padP`
--     (the accumulator absorbs the append); the α/ƛ/ρ isos ↦ `pid`
--     (the normal form absorbs bracketing and units); σ ↦ `bswap`.
--   * `keySq` — THE KEY LEMMA, by induction on `f`:
--       nt B R ∘ (f ⊗ 1_R) ≈ permM (pOf f r) ∘ nt A R
--     Every case is its stage-3D generator square plus plumbing
--     (`⊙P-real`, `nt-perm-nat`, functoriality).
--   * `canon` — every morphism IS its permutation, conjugated by the
--     stage-1 isos: `f ≈ topn ∘ permM (pOf f) ∘ ntop`.
--   * `complete` — equal wirings ⇒ equal permutation wirings (soundness
--     of `keyTop` + injectivity of `wire (ntop)` from the round-trip)
--     ⇒ equal actions (stage 2's agreement theorem `wire-permM`)
--     ⇒ IDENTICAL `Perm`s (stage 3B's `applyP-inj`) ⇒ `f ≈m g`. ∎
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonE where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; Dec; yes; no )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-nat; ρ-nat; ƛ-iso₁; ρ-iso₁; ρ-iso₂
        ; Leaf; goL; goR; wire; ≈m-sound; conv? )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ; norm; list; nt
        ; ntop; topn; ntop-topn; topn-ntop )
open import poc.OCP0009.NbEPMonP
  using ( IsL; lnil; isL-norm; isL-list
        ; Perm; pid; permM; applyP; wire-permM )
open import poc.OCP0009.NbEPMonA
  using ( _⊙P_; padP; bswap )
open import poc.OCP0009.NbEPMonU
  using ( applyP-inj )
open import poc.OCP0009.NbEPMonQ
  using ( ⊙P-real; nt-perm-nat )
open import poc.OCP0009.NbEPMonG
  using ( pid-real; nt-α; nt-ρ; nt-ƛ )
open import poc.OCP0009.NbEPMonR
  using ( inv-nat )
open import poc.OCP0009.NbEPMonY
  using ( fuse⊗ʳ )
open import poc.OCP0009.NbEPMonZ
  using ( nt-αl; nt-σ )

------------------------------------------------------------------------
-- The last two inverse generator squares (the nt-αl conjugation).
------------------------------------------------------------------------

nt-ƛl : ∀ {A R} →
        (nt (I ⊗ A) R ∘m (ƛl {A} ⊗m idm {R})) ≈m nt A R
nt-ƛl =
  ≈trans (∘-congˡ (≈sym nt-ƛ))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ fuse⊗ʳ)
  (≈trans (∘-congʳ (≈trans (⊗-cong ƛ-iso₁ ≈refl) ⊗-id))
          id-r)))

nt-ρl : ∀ {A R} →
        (nt (A ⊗ I) R ∘m (ρl {A} ⊗m idm {R})) ≈m nt A R
nt-ρl =
  ≈trans (∘-congˡ (≈sym nt-ρ))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ fuse⊗ʳ)
  (≈trans (∘-congʳ (≈trans (⊗-cong ρ-iso₁ ≈refl) ⊗-id))
          id-r)))

------------------------------------------------------------------------
-- The permutation of a morphism.
------------------------------------------------------------------------

pOf : ∀ {A B} (f : STm A B) {R} (r : IsL R) →
      Perm (norm A R) (norm B R)
pOf (idm {A})            r = pid (isL-norm A r)
pOf (f ∘m g)             r = pOf g r ⊙P pOf f r
pOf (_⊗m_ {A} {B} {D} f g) r = pOf f (isL-norm D r) ⊙P padP B (pOf g r)
pOf (αr {A} {B} {D})     r = pid (isL-norm ((A ⊗ B) ⊗ D) r)
pOf (αl {A} {B} {D})     r = pid (isL-norm ((A ⊗ B) ⊗ D) r)
pOf (ƛr {A})             r = pid (isL-norm A r)
pOf (ƛl {A})             r = pid (isL-norm A r)
pOf (ρr {A})             r = pid (isL-norm A r)
pOf (ρl {A})             r = pid (isL-norm A r)
pOf (σm {A} {B})         r = bswap A B r

------------------------------------------------------------------------
-- The key lemma: flattening intertwines every morphism with its
-- permutation.
------------------------------------------------------------------------

private
  -- Prepend a realized identity permutation.
  pid-intro : ∀ {P Q} {p : Perm Q Q} {m : STm P Q} →
              permM p ≈m idm → m ≈m (permM p ∘m m)
  pid-intro pr = ≈sym (≈trans (∘-congˡ pr) id-l)

keySq : ∀ {A B} (f : STm A B) {R} (r : IsL R) →
        (nt B R ∘m (f ⊗m idm {R})) ≈m (permM (pOf f r) ∘m nt A R)

keySq (idm {A}) r =
  ≈trans (∘-congʳ ⊗-id)
  (≈trans id-r (pid-intro (pid-real (isL-norm A r))))

keySq (f ∘m g) r =
  ≈trans (∘-congʳ (≈sym fuse⊗ʳ))
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (keySq f r))
  (≈trans ∘-assoc
  (≈trans (∘-congʳ (keySq g r))
  (≈trans (≈sym ∘-assoc)
          (∘-congˡ (≈sym (⊙P-real (pOf g r) (pOf f r)))))))))

keySq (_⊗m_ {A} {B} {D} {E} f g) {R} r =
  ≈trans ∘-assoc
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (∘-congʳ (∘-congʳ α-nat))
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (∘-congʳ (∘-congˡ mix))
  (≈trans (∘-congʳ ∘-assoc)
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (≈sym ∘-assoc))
  (≈trans (∘-congˡ (∘-congˡ (nt-perm-nat B (pOf g r))))
  (≈trans (∘-congˡ ∘-assoc)
  (≈trans (∘-congˡ (∘-congʳ (keySq f (isL-norm D r))))
  (≈trans (∘-congˡ (≈sym ∘-assoc))
  (≈trans (∘-congˡ (∘-congˡ (≈sym (⊙P-real (pOf f (isL-norm D r))
                                           (padP B (pOf g r))))))
          ∘-assoc))))))))))))
  where
  -- Slide g's square out of the tensor, then split the tensor of
  -- composites so the accumulator permutation sits against nt B.
  mix : ((idm {B} ⊗m nt E R) ∘m (f ⊗m (g ⊗m idm {R}))) ≈m
        (((idm {B} ⊗m permM (pOf g r)) ∘m (f ⊗m idm)) ∘m
         (idm {A} ⊗m nt D R))
  mix =
    ≈trans (≈sym ⊗-∘)
    (≈trans (⊗-cong id-l (keySq g r))
    (≈trans (⊗-cong (≈sym id-r) ≈refl)
    (≈trans ⊗-∘
            (∘-congˡ (≈trans (⊗-cong (≈sym id-l) (≈sym id-r)) ⊗-∘)))))

keySq (αr {A} {B} {D}) r =
  ≈trans nt-α (pid-intro (pid-real (isL-norm ((A ⊗ B) ⊗ D) r)))
keySq (αl {A} {B} {D}) r =
  ≈trans nt-αl (pid-intro (pid-real (isL-norm ((A ⊗ B) ⊗ D) r)))
keySq (ƛr {A}) r =
  ≈trans nt-ƛ (pid-intro (pid-real (isL-norm A r)))
keySq (ƛl {A}) r =
  ≈trans nt-ƛl (pid-intro (pid-real (isL-norm A r)))
keySq (ρr {A}) r =
  ≈trans nt-ρ (pid-intro (pid-real (isL-norm A r)))
keySq (ρl {A}) r =
  ≈trans nt-ρl (pid-intro (pid-real (isL-norm A r)))
keySq (σm {A} {B}) r = nt-σ A B r

------------------------------------------------------------------------
-- Top level: the key lemma through the ρ-conjugated flattener.
------------------------------------------------------------------------

keyTop : ∀ {A B} (f : STm A B) →
         (ntop B ∘m f) ≈m (permM (pOf f lnil) ∘m ntop A)
keyTop f =
  ≈trans ∘-assoc
  (≈trans (∘-congʳ (≈sym (inv-nat ρ-iso₂ ρ-iso₁ ρ-nat)))
  (≈trans (≈sym ∘-assoc)
  (≈trans (∘-congˡ (keySq f lnil))
          ∘-assoc)))

-- The canonical form: every morphism IS its permutation, conjugated.
canon : ∀ {A B} (f : STm A B) →
        f ≈m (topn B ∘m (permM (pOf f lnil) ∘m ntop A))
canon {A} {B} f =
  ≈trans (≈sym id-l)
  (≈trans (∘-congˡ (≈sym (topn-ntop B)))
  (≈trans ∘-assoc
          (∘-congʳ (keyTop f))))

------------------------------------------------------------------------
-- COMPLETENESS — equal wiring implies provable equality.
------------------------------------------------------------------------

private
  permM-cong : ∀ {xs ys} {p q : Perm xs ys} → p ≡ q → permM p ≈m permM q
  permM-cong refl = ≈refl

complete : ∀ {A B} (f g : STm A B) →
           (∀ l → wire f l ≡ wire g l) → f ≈m g
complete {A} {B} f g h =
  ≈trans (canon f)
  (≈trans (∘-congʳ (∘-congˡ (permM-cong pf≡pg)))
          (≈sym (canon g)))
  where
  pf = pOf f lnil
  pg = pOf g lnil

  -- Soundness of the top-level key lemma, pointwise.
  soundTop : (k : STm A B) (l : Leaf (list B)) →
             wire k (wire (ntop B) l) ≡
             wire (ntop A) (wire (permM (pOf k lnil)) l)
  soundTop k l = ≈m-sound (keyTop k) l

  -- `wire (ntop A)` is injective: `wire (topn A)` retracts it.
  winj : ∀ {x y : Leaf (list A)} →
         wire (ntop A) x ≡ wire (ntop A) y → x ≡ y
  winj {x} {y} e =
    trans (sym (≈m-sound (ntop-topn A) x))
    (trans (cong (wire (topn A)) e)
           (≈m-sound (ntop-topn A) y))

  permEq : ∀ l → wire (permM pf) l ≡ wire (permM pg) l
  permEq l =
    winj (trans (sym (soundTop f l))
         (trans (h (wire (ntop B) l))
                (soundTop g l)))

  applyEq : ∀ l → applyP pf l ≡ applyP pg l
  applyEq l =
    trans (sym (wire-permM pf l)) (trans (permEq l) (wire-permM pg l))

  pf≡pg : pf ≡ pg
  pf≡pg = applyP-inj (isL-list A) pf pg applyEq

------------------------------------------------------------------------
-- THE DECISION PROCEDURE — conversion in the free SMC is decidable.
------------------------------------------------------------------------

dec≈ : ∀ {A B} (f g : STm A B) → Dec (f ≈m g)
dec≈ f g with conv? f g
... | yes w = yes (complete f g w)
... | no ¬w = no (λ e → ¬w (≈m-sound e))

------------------------------------------------------------------------
-- Demos — hard-won theorems, now one-liners by decision.
------------------------------------------------------------------------

-- Kelly's K3′ at a leaf type (module NbEPMonK spent the hexagon on it):
_ : (ƛr {ι₁} ∘m σm {ι₁} {I}) ≈m ρr {ι₁}
_ = complete _ _ (λ l → refl)

-- The braiding involution, re-proven from wiring alone:
_ : (σm {ι₁} {ι₂} ∘m σm {ι₂} {ι₁}) ≈m idm
_ = complete _ _ (λ { (goL _) → refl ; (goR _) → refl })
