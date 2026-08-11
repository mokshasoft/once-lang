------------------------------------------------------------------------
-- Once.Semantics.Functor
--
-- Base functor interpretation without dependency on full ⟦_⟧.
--
-- This module provides a functor interpretation that takes Set directly
-- in the K case, avoiding the circular dependency:
--   ⟦_⟧ → ⟦_⟧F → SPF.μ → ⟦μ⟧ → ⟦_⟧
--
-- By having K take a Set directly, we can define:
--   SPF.μ without depending on ⟦_⟧
--   Then Core can define ⟦μ⟧ = SPF.μ
--
-- OCP-0003 Phase 6: Enables proving μ-coherence.
------------------------------------------------------------------------

module Once.Semantics.Functor where

open import Level using (Level; 0ℓ; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

------------------------------------------------------------------------
-- Semantic Functor (Set-level)
--
-- Unlike Once.Type.Functor where K takes a Type, here K takes a Set
-- directly. This breaks the dependency on the type interpretation.
------------------------------------------------------------------------

-- | Semantic functor codes
--
-- These represent polynomial functors at the Set level.
-- K takes a Set directly, not a Type.
--
data SFunctor : Set₁ where
  SK   : Set → SFunctor              -- Constant (takes Set directly)
  SId  : SFunctor                    -- Recursive position
  _S⊕_ : SFunctor → SFunctor → SFunctor  -- Sum
  _S⊗_ : SFunctor → SFunctor → SFunctor  -- Product

infixr 30 _S⊕_
infixr 40 _S⊗_

------------------------------------------------------------------------
-- Functor Interpretation
------------------------------------------------------------------------

-- | Interpret semantic functor as Set → Set
--
⟦_⟧SF : SFunctor → Set → Set
⟦ SK A ⟧SF X = A           -- A is already a Set!
⟦ SId ⟧SF X = X            -- Recursive position
⟦ F S⊕ G ⟧SF X = ⟦ F ⟧SF X ⊎ ⟦ G ⟧SF X
⟦ F S⊗ G ⟧SF X = ⟦ F ⟧SF X × ⟦ G ⟧SF X

------------------------------------------------------------------------
-- Functorial Map
------------------------------------------------------------------------

-- | Functorial map for semantic functors
--
sfmap : ∀ F → {X Y : Set} → (X → Y) → ⟦ F ⟧SF X → ⟦ F ⟧SF Y
sfmap (SK A) f x = x
sfmap SId f x = f x
sfmap (F S⊕ G) f (inj₁ x) = inj₁ (sfmap F f x)
sfmap (F S⊕ G) f (inj₂ y) = inj₂ (sfmap G f y)
sfmap (F S⊗ G) f (x , y) = (sfmap F f x , sfmap G f y)

------------------------------------------------------------------------
-- Functor Laws
------------------------------------------------------------------------

-- | sfmap preserves identity
sfmap-id : ∀ F {X : Set} (x : ⟦ F ⟧SF X) → sfmap F (λ z → z) x ≡ x
sfmap-id (SK A) x = refl
sfmap-id SId x = refl
sfmap-id (F S⊕ G) (inj₁ x) = cong inj₁ (sfmap-id F x)
sfmap-id (F S⊕ G) (inj₂ y) = cong inj₂ (sfmap-id G y)
sfmap-id (F S⊗ G) (x , y) = cong₂ _,_ (sfmap-id F x) (sfmap-id G y)

-- | sfmap preserves composition
sfmap-comp : ∀ F {X Y Z : Set} (f : X → Y) (g : Y → Z) (x : ⟦ F ⟧SF X)
           → sfmap F (λ z → g (f z)) x ≡ sfmap F g (sfmap F f x)
sfmap-comp (SK A) f g x = refl
sfmap-comp SId f g x = refl
sfmap-comp (F S⊕ G) f g (inj₁ x) = cong inj₁ (sfmap-comp F f g x)
sfmap-comp (F S⊕ G) f g (inj₂ y) = cong inj₂ (sfmap-comp G f g y)
sfmap-comp (F S⊗ G) f g (x , y) = cong₂ _,_ (sfmap-comp F f g x) (sfmap-comp G f g y)

------------------------------------------------------------------------
-- Fixed Points
------------------------------------------------------------------------

-- | Initial algebra (least fixed point)
--
-- μS F represents the least fixed point of F.
-- μS F ≅ ⟦ F ⟧SF (μS F)
--
data μS (F : SFunctor) : Set where
  ⟨_⟩ : ⟦ F ⟧SF (μS F) → μS F

-- | Destructor for μS
outS : ∀ (F : SFunctor) → μS F → ⟦ F ⟧SF (μS F)
outS F ⟨ x ⟩ = x

-- | Greatest fixed point (coinductive)
--
record νS (F : SFunctor) : Set where
  coinductive
  field
    unfoldS : ⟦ F ⟧SF (νS F)

open νS public

------------------------------------------------------------------------
-- Catamorphism
------------------------------------------------------------------------

-- | Catamorphism (fold)
--
mutual
  cataS : ∀ {F} {A : Set} → (⟦ F ⟧SF A → A) → μS F → A
  cataS {F} alg ⟨ x ⟩ = alg (sfmapCata F alg x)

  sfmapCata : ∀ F {G} {A : Set} → (⟦ G ⟧SF A → A) → ⟦ F ⟧SF (μS G) → ⟦ F ⟧SF A
  sfmapCata (SK B) alg x = x
  sfmapCata SId alg x = cataS alg x
  sfmapCata (F S⊕ G) alg (inj₁ x) = inj₁ (sfmapCata F alg x)
  sfmapCata (F S⊕ G) alg (inj₂ y) = inj₂ (sfmapCata G alg y)
  sfmapCata (F S⊗ G) alg (x , y) = (sfmapCata F alg x , sfmapCata G alg y)

------------------------------------------------------------------------
-- Anamorphism
------------------------------------------------------------------------

-- | Anamorphism (unfold)
--
-- D062: guardedness-CHECKED corecursion (global `--guardedness`) — the
-- corecursive `anaS` calls are placed structurally at `SId` leaves by the
-- mutual `sfmapAna` (the coinductive dual of `cataS`'s `sfmapCata`), so Agda
-- sees the guard. No `TERMINATING` assertion: productivity is verified.
mutual
  anaS : ∀ {F} {A : Set} → (A → ⟦ F ⟧SF A) → A → νS F
  unfoldS (anaS {F} coalg a) = sfmapAna F coalg (coalg a)

  sfmapAna : ∀ {F : SFunctor} (H : SFunctor) {A : Set}
           → (A → ⟦ F ⟧SF A) → ⟦ H ⟧SF A → ⟦ H ⟧SF (νS F)
  sfmapAna (SK B)     coalg x        = x
  sfmapAna SId        coalg a        = anaS coalg a
  sfmapAna (H₁ S⊕ H₂) coalg (inj₁ x) = inj₁ (sfmapAna H₁ coalg x)
  sfmapAna (H₁ S⊕ H₂) coalg (inj₂ y) = inj₂ (sfmapAna H₂ coalg y)
  sfmapAna (H₁ S⊗ H₂) coalg (x , y)  = (sfmapAna H₁ coalg x , sfmapAna H₂ coalg y)

------------------------------------------------------------------------
-- Lambek's Lemma
------------------------------------------------------------------------

-- | fold-unfold: out ∘ In = id
fold-unfoldS : ∀ (F : SFunctor) (x : ⟦ F ⟧SF (μS F)) → outS F ⟨ x ⟩ ≡ x
fold-unfoldS F x = refl

-- | unfold-fold: In ∘ out = id
unfold-foldS : ∀ (F : SFunctor) (x : μS F) → ⟨ outS F x ⟩ ≡ x
unfold-foldS F ⟨ x ⟩ = refl

------------------------------------------------------------------------
-- Catamorphism Laws
------------------------------------------------------------------------

mutual
  sfmapCata-is-sfmap : ∀ F {G} {A : Set} (alg : ⟦ G ⟧SF A → A) (x : ⟦ F ⟧SF (μS G))
                     → sfmapCata F alg x ≡ sfmap F (cataS alg) x
  sfmapCata-is-sfmap (SK B) alg x = refl
  sfmapCata-is-sfmap SId alg x = refl
  sfmapCata-is-sfmap (F S⊕ G) alg (inj₁ x) = cong inj₁ (sfmapCata-is-sfmap F alg x)
  sfmapCata-is-sfmap (F S⊕ G) alg (inj₂ y) = cong inj₂ (sfmapCata-is-sfmap G alg y)
  sfmapCata-is-sfmap (F S⊗ G) alg (x , y) =
    cong₂ _,_ (sfmapCata-is-sfmap F alg x) (sfmapCata-is-sfmap G alg y)

-- | Catamorphism computation law
cataS-computation : ∀ (F : SFunctor) {A : Set} (alg : ⟦ F ⟧SF A → A) (x : ⟦ F ⟧SF (μS F))
                  → cataS {F} alg ⟨ x ⟩ ≡ alg (sfmap F (cataS {F} alg) x)
cataS-computation F {A} alg x = cong alg (sfmapCata-is-sfmap F {F} {A} alg x)

-- | Identity catamorphism
mutual
  cataS-In-id : ∀ {F} (x : μS F) → cataS ⟨_⟩ x ≡ x
  cataS-In-id {F} ⟨ x ⟩ = cong ⟨_⟩ (sfmapCata-In-id F x)

  sfmapCata-In-id : ∀ F {G} (x : ⟦ F ⟧SF (μS G)) → sfmapCata F ⟨_⟩ x ≡ x
  sfmapCata-In-id (SK B) x = refl
  sfmapCata-In-id SId x = cataS-In-id x
  sfmapCata-In-id (F S⊕ G) (inj₁ x) = cong inj₁ (sfmapCata-In-id F x)
  sfmapCata-In-id (F S⊕ G) (inj₂ y) = cong inj₂ (sfmapCata-In-id G y)
  sfmapCata-In-id (F S⊗ G) (x , y) =
    cong₂ _,_ (sfmapCata-In-id F x) (sfmapCata-In-id G y)

-- | Catamorphism congruence: pointwise-equal algebras give equal folds.
-- (D062: lifts `appNatTr-F`/transform congruence through `sem-fuseNat`.)
mutual
  cataS-cong : ∀ {F} {A : Set} {alg₁ alg₂ : ⟦ F ⟧SF A → A}
             → (∀ y → alg₁ y ≡ alg₂ y) → (x : μS F)
             → cataS alg₁ x ≡ cataS alg₂ x
  cataS-cong {F} {A} {alg₁} {alg₂} eq ⟨ x ⟩ =
    trans (cong alg₁ (sfmapCata-cong F eq x)) (eq (sfmapCata F alg₂ x))

  sfmapCata-cong : ∀ F {G} {A : Set} {alg₁ alg₂ : ⟦ G ⟧SF A → A}
                 → (∀ y → alg₁ y ≡ alg₂ y) → (x : ⟦ F ⟧SF (μS G))
                 → sfmapCata F alg₁ x ≡ sfmapCata F alg₂ x
  sfmapCata-cong (SK B) eq x = refl
  sfmapCata-cong SId eq x = cataS-cong eq x
  sfmapCata-cong (F S⊕ G) eq (inj₁ x) = cong inj₁ (sfmapCata-cong F eq x)
  sfmapCata-cong (F S⊕ G) eq (inj₂ y) = cong inj₂ (sfmapCata-cong G eq y)
  sfmapCata-cong (F S⊗ G) eq (x , y) =
    cong₂ _,_ (sfmapCata-cong F eq x) (sfmapCata-cong G eq y)

------------------------------------------------------------------------
-- Anamorphism Laws
------------------------------------------------------------------------

-- | The mutual `sfmapAna` IS `sfmap` of the corecursor (D062): structural
-- induction on the functor code, refl at every leaf. Lets the laws below stay
-- in terms of `sfmap` even though `unfoldS (anaS …)` reduces via `sfmapAna`.
-- `F` (the target) is EXPLICIT: it appears only under the non-injective
-- `⟦ F ⟧SF` in `coalg`, so it can't be inferred.
sfmapAna-is-sfmap : ∀ (F : SFunctor) (H : SFunctor) {A : Set}
                    (coalg : A → ⟦ F ⟧SF A) (x : ⟦ H ⟧SF A)
                  → sfmapAna {F} H coalg x ≡ sfmap H (anaS coalg) x
sfmapAna-is-sfmap F (SK B)     coalg x        = refl
sfmapAna-is-sfmap F SId        coalg a        = refl
sfmapAna-is-sfmap F (H₁ S⊕ H₂) coalg (inj₁ x) = cong inj₁ (sfmapAna-is-sfmap F H₁ coalg x)
sfmapAna-is-sfmap F (H₁ S⊕ H₂) coalg (inj₂ y) = cong inj₂ (sfmapAna-is-sfmap F H₂ coalg y)
sfmapAna-is-sfmap F (H₁ S⊗ H₂) coalg (x , y)  =
  cong₂ _,_ (sfmapAna-is-sfmap F H₁ coalg x) (sfmapAna-is-sfmap F H₂ coalg y)

-- | ana-unfold (computation). No longer refl: `unfoldS (anaS …)` reduces via
-- `sfmapAna`, bridged to `sfmap` by `sfmapAna-is-sfmap`.
anaS-unfold : ∀ (F : SFunctor) {A : Set} (coalg : A → ⟦ F ⟧SF A) (a : A)
            → unfoldS (anaS {F} coalg a) ≡ sfmap F (anaS coalg) (coalg a)
anaS-unfold F coalg a = sfmapAna-is-sfmap F F coalg (coalg a)

------------------------------------------------------------------------
-- Paramorphism
------------------------------------------------------------------------

-- | Paramorphism: fold with access to original substructure
--
-- Derived from cataS, so termination is cataS's.
-- Para's algebra receives both the recursive result AND the original
-- substructure, enabling bounded recursion patterns like `obs`.
--
-- Mathematically: para alg ⟨ x ⟩ = alg (sfmap (λ y → (y , para alg y)) x)
--
-- Implementation: Encode via cataS with a product that carries both
-- the original structure and the recursive result.
--
paraS : ∀ {F} {A : Set} → (⟦ F ⟧SF (μS F × A) → A) → μS F → A
paraS {F} {A} alg x = proj₂ (cataS {F} alg' x)
  where
    alg' : ⟦ F ⟧SF (μS F × A) → (μS F × A)
    alg' fx = (⟨ sfmap F proj₁ fx ⟩ , alg fx)

------------------------------------------------------------------------
-- Fusion (μ-anchored hylomorphism)
------------------------------------------------------------------------

-- | Natural transformation fusion (TERMINATING-free)
--
-- When transform is a NATURAL TRANSFORMATION (parametric in the recursive
-- position), fusion reduces to cata with a composed algebra. This version
-- rides cataS's structural recursion.
--
-- A natural transformation `∀ {A} → ⟦ G ⟧SF A → ⟦ F ⟧SF A` satisfies:
--   transform ∘ sfmap G f = sfmap F f ∘ transform  (naturality)
--
-- This means transform cannot inspect the A values - it only reorganizes
-- the functor structure. Examples:
--   - Swapping sum branches: λ { (inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y }
--   - Projecting from product: λ (x , _) → x
--   - Copying: λ x → (x , x)  (for Id → Id ⊗ Id)
--
-- Mathematically: fuseNatS transform alg = cataS (alg ∘ transform)
--
fuseNatS : ∀ {F G} {B : Set}
         → (∀ {A} → ⟦ G ⟧SF A → ⟦ F ⟧SF A)  -- natural transform: G → F
         → (⟦ F ⟧SF B → B)                   -- algebra: F(B) → B
         → μS G → B
fuseNatS {F} {G} {B} transform alg = cataS {G} (alg ∘ transform)

-- | Monoid-threaded natural fusion — the *Writer-carrier catamorphism*.
--
-- This is the generalization of `fuseNatS`: when the transform is a (monoidal)
-- NATURAL transformation — parametric in the recursive position, with a
-- shape-determined monoid annotation — the whole fold is just `cataS` at the
-- carrier `M × B`, so its termination is cataS's (unlike the monomorphic
-- `fuseW`, which needs its own argument). The recursion is `cataS`'s
-- structural descent; the per-layer monoid
-- is accumulated in fused depth-first order — transform (pre), children (in
-- functor order, via `collectM`), algebra (post) — matching `fuseW` exactly but
-- provably structural. `fuseNatS` is its `⊤`-monoid instance.
--
-- The naming discipline (D06x): `cataS` (the catamorphism) is THE sanctioned
-- structural μ-recursion primitive — its mutual `sfmapCata` is the one place
-- the functor-map is defunctionalized so foetus sees the descent. Every
-- genuinely-structural fold should be a `cataS`-derivative (as `paraS`,
-- `fuseNatS`, and now `fuseNatW` are) rather than hand-writing `sfmap F recfn`.
fuseNatW : ∀ {F G} {B M : Set}
         → (M → M → M) → M                              -- monoid: `⊕` and `ε`
         → (∀ {A} → ⟦ G ⟧SF A → M × ⟦ F ⟧SF A)          -- monoidal natural transform
         → (⟦ F ⟧SF B → M × B)                          -- algebra: F(B) → (M , B)
         → μS G → M × B
fuseNatW {F} {G} {B} {M} _·_ ε transform alg = cataS {G} φ
  where
    -- accumulate the children's monoid out of one F-layer (structural on F).
    collectM : ∀ H → ⟦ H ⟧SF (M × B) → M
    collectM (SK A)     _         = ε
    collectM SId        (m , _)   = m
    collectM (H₁ S⊕ H₂) (inj₁ y)  = collectM H₁ y
    collectM (H₁ S⊕ H₂) (inj₂ y)  = collectM H₂ y
    collectM (H₁ S⊗ H₂) (y₁ , y₂) = collectM H₁ y₁ · collectM H₂ y₂

    φ : ⟦ G ⟧SF (M × B) → M × B
    φ gmb = let tr   = transform gmb            -- (M , ⟦F⟧SF (M × B))
                m-ch = collectM F (proj₂ tr)
                al   = alg (sfmap F proj₂ (proj₂ tr))   -- (M , B)
            in ((proj₁ tr · m-ch) · proj₁ al , proj₂ al)

------------------------------------------------------------------------
-- Natural-transformation calculus  (D062 / approach A, M1)
--
-- `fuseNatS`/`fuseNatW` are total because their transform is a NATURAL
-- transformation `∀ {X} → ⟦ G ⟧SF X → ⟦ F ⟧SF X` — parametric in the
-- recursive position, hence unable to inspect or synthesize μ-substructure.
-- But a bare polymorphic Agda function of that type is neither *manifestly*
-- natural (Agda has no internal parametricity to lean on) nor compilable.
--
-- `NatSF G F` is the manifestly-natural, first-order, compilable witness:
-- a polynomial-functor (container) morphism `G ⇒ F`. By construction its
-- interpretation `appNatSF` NEVER touches the `X`-positions — it only
-- routes/copies/discards them (`ntId`, structural ctors) and runs a pure
-- map on the constant parts (`ntK`). So:
--   * naturality holds definitionally-up-to-induction (`appNatSF-natural`);
--   * it is total data (finite syntax, no recursion-position access);
--   * it compiles to straight-line data-flow (M5): case/project/inject/dup.
--
-- This is exactly the transform Fuse/Hylo should carry (D062, approach A):
-- a *structural* deforestation, total-by-construction. Transforms that run
-- effects or synthesize substructure are NOT natural — they are the
-- value-synthesizing divergent hylos `fuseW`'s the termination pragma was
-- (dishonestly) covering, and belong to the layer-3 well-founded-loop story,
-- not the meaning of a finite fold.
------------------------------------------------------------------------

-- | Container morphism `G ⇒ F`: the syntax of natural transformations
-- between the polynomial functors `⟦ G ⟧SF` and `⟦ F ⟧SF`.
--
-- Source eliminators (`ntFst`/`ntSnd`/`ntCase`) and target introductions
-- (`ntInl`/`ntInr`/`ntPair`) interleave; leaves are the identity on the
-- recursive position (`ntId`) and a pure map on constants (`ntK`).
data NatSF : SFunctor → SFunctor → Set₁ where
  ntId   : NatSF SId SId
  ntK    : ∀ {A B : Set} → (A → B) → NatSF (SK A) (SK B)
  ntFst  : ∀ {G₁ G₂ F} → NatSF G₁ F → NatSF (G₁ S⊗ G₂) F
  ntSnd  : ∀ {G₁ G₂ F} → NatSF G₂ F → NatSF (G₁ S⊗ G₂) F
  ntCase : ∀ {G₁ G₂ F} → NatSF G₁ F → NatSF G₂ F → NatSF (G₁ S⊕ G₂) F
  ntInl  : ∀ {G F₁ F₂} → NatSF G F₁ → NatSF G (F₁ S⊕ F₂)
  ntInr  : ∀ {G F₁ F₂} → NatSF G F₂ → NatSF G (F₁ S⊕ F₂)
  ntPair : ∀ {G F₁ F₂} → NatSF G F₁ → NatSF G F₂ → NatSF G (F₁ S⊗ F₂)

-- | The witnessed natural transformation. Manifestly parametric in `X`:
-- the `X`-positions are only routed, never inspected.
appNatSF : ∀ {G F} → NatSF G F → ∀ {X : Set} → ⟦ G ⟧SF X → ⟦ F ⟧SF X
appNatSF ntId          x         = x
appNatSF (ntK f)       a         = f a
appNatSF (ntFst t)     (x , _)   = appNatSF t x
appNatSF (ntSnd t)     (_ , y)   = appNatSF t y
appNatSF (ntCase t u)  (inj₁ x)  = appNatSF t x
appNatSF (ntCase t u)  (inj₂ y)  = appNatSF u y
appNatSF (ntInl t)     g         = inj₁ (appNatSF t g)
appNatSF (ntInr t)     g         = inj₂ (appNatSF t g)
appNatSF (ntPair t u)  g         = (appNatSF t g , appNatSF u g)

-- | Naturality: `appNatSF` commutes with `sfmap` — it is a genuine natural
-- transformation, not merely a polymorphically-typed function. This is the
-- correctness justification for denoting Fuse/Hylo via `fuseNat*` (the
-- container morphism never depends on the carrier, so reindexing the
-- recursive positions and applying it commute).
appNatSF-natural : ∀ {G F} (t : NatSF G F) {X Y : Set} (h : X → Y)
                 → (g : ⟦ G ⟧SF X)
                 → appNatSF t (sfmap G h g) ≡ sfmap F h (appNatSF t g)
appNatSF-natural ntId         h x        = refl
appNatSF-natural (ntK f)      h a        = refl
appNatSF-natural (ntFst t)    h (x , _)  = appNatSF-natural t h x
appNatSF-natural (ntSnd t)    h (_ , y)  = appNatSF-natural t h y
appNatSF-natural (ntCase t u) h (inj₁ x) = appNatSF-natural t h x
appNatSF-natural (ntCase t u) h (inj₂ y) = appNatSF-natural u h y
appNatSF-natural (ntInl t)    h g        = cong inj₁ (appNatSF-natural t h g)
appNatSF-natural (ntInr t)    h g        = cong inj₂ (appNatSF-natural t h g)
appNatSF-natural (ntPair t u) h g        =
  cong₂ _,_ (appNatSF-natural t h g) (appNatSF-natural u h g)

-- | Fusion through a container morphism — the value fold. Total: `fuseNatS`
-- is `cataS (alg ∘ appNatSF t)`, no the termination pragma.
fuseNT : ∀ {F G} {B : Set}
       → NatSF G F → (⟦ F ⟧SF B → B) → μS G → B
fuseNT {F} {G} {B} t alg = fuseNatS {F} {G} {B} (appNatSF t) alg

-- | Fusion through a container morphism — the monoid-threaded fold (the trace
-- carrier). A *natural* transform realizes no effects, so it contributes the
-- monoid unit `ε` per layer; all accumulation comes from `alg`. Total via
-- `fuseNatW`.
fuseNTW : ∀ {F G} {B M : Set}
        → (M → M → M) → M
        → NatSF G F → (⟦ F ⟧SF B → M × B) → μS G → M × B
fuseNTW {F} {G} {B} {M} _·_ ε t alg =
  fuseNatW {F} {G} {B} {M} _·_ ε (λ {A} g → (ε , appNatSF t g)) alg

-- D062 / approach A: the monomorphic `fuseW`/`fuseS` (the the termination pragma
-- fusion folds whose transform `⟦ G ⟧SF (μS G) → ⟦ F ⟧SF (μS G)` could inspect
-- or synthesize μ-substructure — the assertion being FALSE for value-
-- synthesizing divergent hylos) have been DELETED. Structural fusion is now
-- carried by a natural transformation (`NatSF` above / `NatTr` at the IR level)
-- and folded by the total, `cataS`-derived `fuseNatS`/`fuseNatW`/`fuseNT`/
-- `fuseNTW`. This was the last `TERMINATING` in the denotational meaning's
-- use-chain. The measured (well-founded-coalgebra) hylo is a separate,
-- deferred layer-3 concern with an explicit termination certificate.

