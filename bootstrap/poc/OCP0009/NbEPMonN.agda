------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 1 — TYPE NORMALIZATION, isos in-theory
--
-- The completeness climb (equal wiring ⇒ `≈m`, plan §10 rung 2b) begins
-- where Beylin–Dybjer began: normalize the TYPES. Every `MTy` is
-- `≈m`-isomorphic to a canonical right-nested list of its leaves, and the
-- isomorphism is built IN THE SYNTAX (`nt`/`tn : STm …`) and proven IN THE
-- THEORY (`nt-tn`/`tn-nt : … ≈m idm`).
--
-- The accumulator trick (`norm (A ⊗ B) R = norm A (norm B R)`) is the
-- load-bearing move: it makes tensor ASSOCIATIVITY and UNIT ABSORPTION
-- DEFINITIONAL at the type level —
--
--     list ((A ⊗ B) ⊗ D) ≡ list (A ⊗ (B ⊗ D))     by refl
--     list (I ⊗ A) ≡ list A ≡ list (A ⊗ I)         by refl
--
-- so stages 2–3 can compare morphisms between literally-equal list types,
-- with all bracketing/unit noise gone. The pentagon and triangle axioms do
-- their real work HERE, inside the `nt-tn`/`tn-nt` proofs.
--
-- What remains after this stage (documented, scheduled):
--   stage 2 — canonical realizations: every wiring between list types is
--     realized by a canonical morphism (adjacent transpositions);
--   stage 3 — the key lemma: `f ≈m topn ∘ canon (wire f) ∘ ntop`, by
--     induction on `f`; completeness falls out by transitivity.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonN where

open import normalizer.Syntax.Types
  using ( _≡_; refl )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ∘-cong; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-iso₁; α-iso₂; ƛ-iso₁; ƛ-iso₂; ρ-iso₁; ρ-iso₂
        ; wire; ≈m-sound )

------------------------------------------------------------------------
-- Small proof kit over `_≈m_`.
------------------------------------------------------------------------

∘-congˡ : ∀ {A B D} {f f' : STm B D} {g : STm A B} →
          f ≈m f' → (f ∘m g) ≈m (f' ∘m g)
∘-congˡ p = ∘-cong p ≈refl

∘-congʳ : ∀ {A B D} {f : STm B D} {g g' : STm A B} →
          g ≈m g' → (f ∘m g) ≈m (f ∘m g')
∘-congʳ p = ∘-cong ≈refl p

-- The reusable collapse: an inverse pair in the middle cancels.
cancel : ∀ {A B D E} {f : STm B E} {g : STm D B} {h : STm B D} {k : STm A B} →
         (g ∘m h) ≈m idm → ((f ∘m g) ∘m (h ∘m k)) ≈m (f ∘m k)
cancel p =
  ≈trans ∘-assoc
  (≈trans (∘-congʳ (≈sym ∘-assoc))
  (≈trans (∘-congʳ (∘-congˡ p))
          (∘-congʳ id-l)))

------------------------------------------------------------------------
-- Normalization of types: right-nested leaf lists, by accumulator.
------------------------------------------------------------------------

norm : MTy → MTy → MTy
norm ι₁      R = ι₁ ⊗ R
norm ι₂      R = ι₂ ⊗ R
norm I       R = R
norm (A ⊗ B) R = norm A (norm B R)

list : MTy → MTy
list A = norm A I

-- THE PAYOFF — bracketing and units are gone DEFINITIONALLY:
_ : ∀ {A B D} → list ((A ⊗ B) ⊗ D) ≡ list (A ⊗ (B ⊗ D))
_ = refl

_ : ∀ {A} → list (I ⊗ A) ≡ list A
_ = refl

_ : ∀ {A} → list (A ⊗ I) ≡ list A
_ = refl

------------------------------------------------------------------------
-- The isomorphism, in the syntax: flatten (`nt`) and rebuild (`tn`),
-- both with an accumulator.
------------------------------------------------------------------------

nt : ∀ A R → STm (A ⊗ R) (norm A R)
nt ι₁      R = idm
nt ι₂      R = idm
nt I       R = ƛr
nt (A ⊗ B) R = nt A (norm B R) ∘m ((idm ⊗m nt B R) ∘m αr)

tn : ∀ A R → STm (norm A R) (A ⊗ R)
tn ι₁      R = idm
tn ι₂      R = idm
tn I       R = ƛl
tn (A ⊗ B) R = αl ∘m ((idm ⊗m tn B R) ∘m tn A (norm B R))

------------------------------------------------------------------------
-- The isomorphism, in the theory: `nt`/`tn` are mutually inverse UP TO
-- `≈m` — proven by induction on the type, the iso axioms and
-- functoriality doing the per-former work, `cancel` doing the plumbing.
------------------------------------------------------------------------

nt-tn : ∀ A R → (nt A R ∘m tn A R) ≈m idm
tn-nt : ∀ A R → (tn A R ∘m nt A R) ≈m idm

nt-tn ι₁      R = id-l
nt-tn ι₂      R = id-l
nt-tn I       R = ƛ-iso₁
nt-tn (A ⊗ B) R =
  ≈trans (∘-congˡ (≈sym ∘-assoc))
  (≈trans (cancel α-iso₁)
  (≈trans (cancel mid-cancel)
          (nt-tn A (norm B R))))
  where
  mid-cancel : ((idm ⊗m nt B R) ∘m (idm ⊗m tn B R)) ≈m idm
  mid-cancel = ≈trans (≈sym ⊗-∘) (≈trans (⊗-cong id-l (nt-tn B R)) ⊗-id)

tn-nt ι₁      R = id-l
tn-nt ι₂      R = id-l
tn-nt I       R = ƛ-iso₂
tn-nt (A ⊗ B) R =
  ≈trans ∘-assoc
  (≈trans (∘-congʳ (cancel (tn-nt A (norm B R))))
  (≈trans (∘-congʳ (≈trans (≈sym ∘-assoc)
                   (≈trans (∘-congˡ mid'-cancel) id-l)))
          α-iso₂))
  where
  mid'-cancel : ((idm ⊗m tn B R) ∘m (idm ⊗m nt B R)) ≈m idm
  mid'-cancel = ≈trans (≈sym ⊗-∘) (≈trans (⊗-cong id-l (tn-nt B R)) ⊗-id)

------------------------------------------------------------------------
-- Top-level: every type is `≈m`-isomorphic to its leaf list.
------------------------------------------------------------------------

ntop : ∀ A → STm A (list A)
ntop A = nt A I ∘m ρl

topn : ∀ A → STm (list A) A
topn A = ρr ∘m tn A I

ntop-topn : ∀ A → (ntop A ∘m topn A) ≈m idm
ntop-topn A = ≈trans (cancel ρ-iso₂) (nt-tn A I)

topn-ntop : ∀ A → (topn A ∘m ntop A) ≈m idm
topn-ntop A = ≈trans (cancel (tn-nt A I)) ρ-iso₁

------------------------------------------------------------------------
-- Connection to the decision layer (`NbEPMonC`): the iso proofs transport
-- through `≈m-sound`, so the WIRINGS of the round-trips are the identity —
-- checked here on a concrete type via the wiring itself.
------------------------------------------------------------------------

Aex : MTy
Aex = (ι₁ ⊗ (I ⊗ ι₂)) ⊗ ι₁

_ : ∀ l → wire (ntop Aex ∘m topn Aex) l ≡ wire (idm {list Aex}) l
_ = ≈m-sound (ntop-topn Aex)

_ : ∀ l → wire (topn Aex ∘m ntop Aex) l ≡ wire (idm {Aex}) l
_ = ≈m-sound (topn-ntop Aex)
