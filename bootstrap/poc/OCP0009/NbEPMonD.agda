------------------------------------------------------------------------
-- OCP-0009 · THE TWO TOWERS MEET — a directed-kernel skeleton whose
--            conversion rule IS the decided linear-core equality
--
-- The DT tower built kernels whose conversion is decidable (NbE); the
-- monoidal tower just proved the linear core's equality decidable
-- (`dec≈`, SMC coherence completeness). This module plugs the second
-- into the shape of the first — the rung-3 silhouette at ⊗-fragment
-- cost:
--
--   * `nf` — CONVERSION BY NORMALIZATION, the NbE shape recovered:
--     `nf f = pOf f lnil` is a normal-form function into first-order
--     data (`Perm`), and `nf-sound`/`nf-complete` repackage soundness +
--     completeness as   f ≈m g  ⟺  nf f ≡ nf g.
--     Equality of programs = identity of normal forms.
--   * `invS`/`inv-l`/`inv-r` — the free SMC is a GROUPOID: every
--     structural program is syntactically invertible. So the `≈m` axis
--     is the (symmetric) EQUALITY axis of the future directed kernel;
--     directedness proper lives on the TRANSITION axis (`NbEPMon`'s
--     `gen`, `NbEPDirU`'s `hom) — the two axes never collide.
--   * `U`/`El` — the kernel universe: `` `shom A B `` (linear programs
--     as a type) and `` `conv f g `` (CONVERSION AS A TYPE), decoded to
--     `nf f ≡ nf g`. Because `nf` COMPUTES, conversion checking for
--     closed programs is literally `refl` — the kernel experience:
--     hexagon instances, σ-involution, unit shuffles all check by
--     `refl` below. Introduction/elimination are `nf-sound`/
--     `nf-complete`; inhabitation is decided by `dec≈`.
--   * `Fam`/`transp` — THE CONVERSION RULE: type families over programs
--     defined through `nf` are automatically `≈m`-respecting, and
--     transport along `` `conv `` is `subst` on normal forms — which
--     DISAPPEARS (computes away) on convertible closed indices.
--
-- Honest ceiling: this universe's own conversion is still Agda's
-- kernel (as in `NbEPUniv`/`NbEPDirU`); what is NEW is that the
-- object-language hom-equality inside it is Once-owned and decided by
-- Once's theorem, not assumed. Scaling this from the ⊗-fragment to the
-- full core is exactly the ⊸/proof-net climb (plan §10, rung 2b.2).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonD where

open import normalizer.Syntax.Types
  using ( ⊤; tt; ⊥; _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; ƛr; ƛl; ρr; ρl; σm
        ; _≈m_; ≈refl; ≈sym; ≈trans; ⊗-cong
        ; id-l; id-r; ∘-assoc; ⊗-id; ⊗-∘
        ; α-iso₁; α-iso₂; ƛ-iso₁; ƛ-iso₂; ρ-iso₁; ρ-iso₂; σ-invol
        ; Leaf; wire; ≈m-sound )
open import poc.OCP0009.NbEPMonN
  using ( ∘-congˡ; ∘-congʳ; cancel; list; ntop; topn; ntop-topn )
open import poc.OCP0009.NbEPMonP
  using ( lnil; isL-list; Perm; permM; applyP; wire-permM )
open import poc.OCP0009.NbEPMonU
  using ( applyP-inj )
open import poc.OCP0009.NbEPMonE
  using ( pOf; keyTop; canon )

------------------------------------------------------------------------
-- Conversion by normalization — the NbE shape, recovered.
------------------------------------------------------------------------

nf : ∀ {A B} → STm A B → Perm (list A) (list B)
nf f = pOf f lnil

private
  permM-cong : ∀ {xs ys} {p q : Perm xs ys} → p ≡ q → permM p ≈m permM q
  permM-cong refl = ≈refl

-- Provably equal programs have IDENTICAL normal forms.
nf-sound : ∀ {A B} {f g : STm A B} → f ≈m g → nf f ≡ nf g
nf-sound {A} {B} {f} {g} e =
  applyP-inj (isL-list A) (nf f) (nf g) applyEq
  where
  winj : ∀ {x y : Leaf (list A)} →
         wire (ntop A) x ≡ wire (ntop A) y → x ≡ y
  winj {x} {y} e' =
    trans (sym (≈m-sound (ntop-topn A) x))
    (trans (cong (wire (topn A)) e')
           (≈m-sound (ntop-topn A) y))

  permEq : ∀ l → wire (permM (nf f)) l ≡ wire (permM (nf g)) l
  permEq l =
    winj (trans (sym (≈m-sound (keyTop f) l))
         (trans (≈m-sound e (wire (ntop B) l))
                (≈m-sound (keyTop g) l)))

  applyEq : ∀ l → applyP (nf f) l ≡ applyP (nf g) l
  applyEq l =
    trans (sym (wire-permM (nf f) l))
          (trans (permEq l) (wire-permM (nf g) l))

-- Identical normal forms make programs provably equal.
nf-complete : ∀ {A B} {f g : STm A B} → nf f ≡ nf g → f ≈m g
nf-complete {f = f} {g} e =
  ≈trans (canon f)
  (≈trans (∘-congʳ (∘-congˡ (permM-cong e)))
          (≈sym (canon g)))

------------------------------------------------------------------------
-- The structural fragment is a GROUPOID — every program is invertible.
-- So `≈m` is the kernel's (symmetric) equality axis; directedness
-- proper is the transition axis (`NbEPMon`'s `gen`), untouched here.
------------------------------------------------------------------------

invS : ∀ {A B} → STm A B → STm B A
invS idm       = idm
invS (f ∘m g)  = invS g ∘m invS f
invS (f ⊗m g)  = invS f ⊗m invS g
invS αr        = αl
invS αl        = αr
invS ƛr        = ƛl
invS ƛl        = ƛr
invS ρr        = ρl
invS ρl        = ρr
invS σm        = σm

inv-l : ∀ {A B} (f : STm A B) → (invS f ∘m f) ≈m idm
inv-l idm      = id-l
inv-l (f ∘m g) = ≈trans (cancel (inv-l f)) (inv-l g)
inv-l (f ⊗m g) =
  ≈trans (≈sym ⊗-∘) (≈trans (⊗-cong (inv-l f) (inv-l g)) ⊗-id)
inv-l αr = α-iso₂
inv-l αl = α-iso₁
inv-l ƛr = ƛ-iso₂
inv-l ƛl = ƛ-iso₁
inv-l ρr = ρ-iso₂
inv-l ρl = ρ-iso₁
inv-l σm = σ-invol

inv-r : ∀ {A B} (f : STm A B) → (f ∘m invS f) ≈m idm
inv-r idm      = id-l
inv-r (f ∘m g) = ≈trans (cancel (inv-r g)) (inv-r f)
inv-r (f ⊗m g) =
  ≈trans (≈sym ⊗-∘) (≈trans (⊗-cong (inv-r f) (inv-r g)) ⊗-id)
inv-r αr = α-iso₁
inv-r αl = α-iso₂
inv-r ƛr = ƛ-iso₁
inv-r ƛl = ƛ-iso₂
inv-r ρr = ρ-iso₁
inv-r ρl = ρ-iso₂
inv-r σm = σ-invol

------------------------------------------------------------------------
-- The kernel universe: linear programs and their CONVERSION as types.
------------------------------------------------------------------------

mutual
  data U : Set where
    `⊥ `unit : U
    `shom : (A B : MTy) → U                       -- the type of programs
    `conv : ∀ {A B} → STm A B → STm A B → U       -- conversion as a TYPE
    `π    : (a : U) → (El a → U) → U

  El : U → Set
  El `⊥          = ⊥
  El `unit       = ⊤
  El (`shom A B) = STm A B
  El (`conv f g) = nf f ≡ nf g      -- decoded to NORMAL-FORM identity
  El (`π a b)    = (x : El a) → El (b x)

-- Introduction and elimination: the judgment `f ≈m g` moves in and out
-- of the object language through the normalization theorems.
mk-conv : ∀ {A B} {f g : STm A B} → f ≈m g → El (`conv f g)
mk-conv = nf-sound

use-conv : ∀ {A B} {f g : STm A B} → El (`conv f g) → f ≈m g
use-conv = nf-complete

-- The equality axis is symmetric (the groupoid, seen internally).
sym-conv : ∀ {A B} {f g : STm A B} → El (`conv f g) → El (`conv g f)
sym-conv = sym

------------------------------------------------------------------------
-- THE CONVERSION RULE. Families over programs defined through `nf` are
-- automatically respectful, and transport along `conv is subst on
-- normal forms — it COMPUTES AWAY on convertible closed indices.
------------------------------------------------------------------------

Fam : ∀ {A B} → (Perm (list A) (list B) → U) → STm A B → U
Fam Q f = Q (nf f)

Fam-resp : ∀ {A B} {f g : STm A B} (Q : Perm (list A) (list B) → U) →
           f ≈m g → Fam Q f ≡ Fam Q g
Fam-resp Q e = cong Q (nf-sound e)

private
  substU : ∀ {X : Set} (P : X → Set) {x y : X} → x ≡ y → P x → P y
  substU P refl v = v

transp : ∀ {A B} {f g : STm A B} (Q : Perm (list A) (list B) → U) →
         El (`conv f g) → El (Fam Q f) → El (Fam Q g)
transp Q e v = substU (λ p → El (Q p)) e v

------------------------------------------------------------------------
-- Demos — conversion checking for closed programs is `refl`, because
-- `nf` computes. This is the kernel-with-decidable-conversion
-- experience, running on Once's own theorem.
------------------------------------------------------------------------

-- The σ-involution, checked by the kernel:
_ : El (`conv (σm {ι₁} {ι₂} ∘m σm) idm)
_ = refl

-- A unit round-trip:
_ : El (`conv (ρr {ι₁} ∘m ρl) idm)
_ = refl

-- A HEXAGON instance — a coherence axiom, verified by normalization:
_ : El (`conv ((idm {ι₂} ⊗m σm {ι₁} {ι₁}) ∘m (αr ∘m (σm {ι₁} {ι₂} ⊗m idm)))
              (αr ∘m (σm {ι₁} {ι₂ ⊗ ι₁} ∘m αr)))
_ = refl

-- Internal quantification over programs: right-unit conversion, ∀f.
_ : El (`π (`shom ι₁ ι₂) (λ f → `conv (f ∘m idm) f))
_ = λ f → mk-conv {f = f ∘m idm} {g = f} id-r

-- Every program converts with its syntactic inverse's inverse-path:
_ : El (`π (`shom ι₁ ι₂) (λ f → `conv (f ∘m (invS f ∘m f)) f))
_ = λ f → mk-conv {f = f ∘m (invS f ∘m f)} {g = f}
                  (≈trans (∘-congʳ (inv-l f)) id-r)

-- Transport along a closed conversion proof is invisible: casting a
-- value across the two hexagon sides is definitionally the identity.
_ : transp {f = (idm {ι₂} ⊗m σm {ι₁} {ι₁}) ∘m (αr ∘m (σm {ι₁} {ι₂} ⊗m idm))}
           {g = αr ∘m (σm {ι₁} {ι₂ ⊗ ι₁} ∘m αr)}
           (λ _ → `shom ι₁ ι₁) refl idm ≡ idm
_ = refl
