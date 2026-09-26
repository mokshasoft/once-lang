------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE ANNOTATED KERNEL JUDGMENT `⊢ᴬ`.
--                      (PLAN-BIDI §3d — the judgment the checker checks)
--
-- ★ RULE FOR RULE the kernel's `⊢`, with every datum `⊢` takes from the
--   DERIVATION now read off the TERM (`lam A`, `pair B`, `natrec M`, …) —
--   so a kernel term determines its type (PLAN-BIDI §0).
--
-- ★★ CONVERSION IS ON ERASURES (decision (c)):
--       ⊢ᴬconv : Γ ⊢ᴬ t ∷ A → ⌈ A ⌉ᵀ ≅ᵀ ⌈ B ⌉ᵀ → Γ ⊢ᴬ t ∷ B
--   Annotations are typing data; they never decide an equality.  That is
--   what lets every metatheorem of `RTm` TRANSFER (`Metatheory/Erasure`)
--   instead of being re-proved, and what makes conversion decidable by the
--   existing `decide-≅`/`decConvᵀ`.
--
-- ★ CONTEXTS ARE DEFINED TOGETHER WITH THEIR ERASURE (induction-recursion),
--   so the de Bruijn depth of an annotated context IS that of its erasure,
--   definitionally — no transport between the layers, ever.
--
-- ★ THE INDUCTIVE FORMERS (levitated): descriptions are annotated TERMS
--   of `Desc I`, so their well-formedness is `⊢ᴬ` itself; the method type
--   comes from `Spec/AnnotatedDesc` (`MethTyᴬ`, `iinstᴬ`).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.TypingA where
open import normalizer.Syntax.Types using ( _≡_ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false; occTm; NoNatC; flat? )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _≅ᵀ_; _×_; _,,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.AnnotatedDesc

------------------------------------------------------------------------
-- Annotated contexts, and their erasure — MUTUALLY.
------------------------------------------------------------------------

data ACtx : Set
⌈_⌉ᶜ : ACtx → Ctx

-- the de Bruijn depth of an annotated context is its erasure's, by DEFINITION
⌊_⌋ᴬ : ACtx → Cx
⌊ Γ ⌋ᴬ = ⌊ ⌈ Γ ⌉ᶜ ⌋

infixl 5 _▹ᴬ_
data ACtx where
  ◇ᴬ   : ACtx
  _▹ᴬ_ : (Γ : ACtx) → ATy ⌊ Γ ⌋ᴬ → ACtx

⌈ ◇ᴬ ⌉ᶜ     = ◇
⌈ Γ ▹ᴬ A ⌉ᶜ = ⌈ Γ ⌉ᶜ ▹ ⌈ A ⌉ᵀ

private
  variable
    Γ : ACtx

------------------------------------------------------------------------
-- The annotated substitutions the rules mention.
------------------------------------------------------------------------

nrsᴬ : {Δ : Cx} → Subᴬ (Δ ∙) ((Δ ∙) ∙)
nrsᴬ vz     = nsuc (var (vs vz))
nrsᴬ (vs x) = var (vs (vs x))

------------------------------------------------------------------------
-- Variables.
------------------------------------------------------------------------

infix 3 _∋ᴬ_∷_
data _∋ᴬ_∷_ : (Γ : ACtx) → Var ⌊ Γ ⌋ᴬ → ATy ⌊ Γ ⌋ᴬ → Set where
  hereᴬ  : {A : ATy ⌊ Γ ⌋ᴬ} → (Γ ▹ᴬ A) ∋ᴬ vz ∷ renTyᴬ vs A
  thereᴬ : {A B : ATy ⌊ Γ ⌋ᴬ} {x : Var ⌊ Γ ⌋ᴬ} →
           Γ ∋ᴬ x ∷ A → (Γ ▹ᴬ B) ∋ᴬ vs x ∷ renTyᴬ vs A

------------------------------------------------------------------------
-- ★ The judgment.
------------------------------------------------------------------------

infix 3 _⊢ᴬ_∷_ _⊢tyᴬ_
data _⊢ᴬ_∷_ : (Γ : ACtx) → ATm ⌊ Γ ⌋ᴬ → ATy ⌊ Γ ⌋ᴬ → Set
data _⊢tyᴬ_ : (Γ : ACtx) → ATy ⌊ Γ ⌋ᴬ → Set
-- ★ LEVITATION: no description well-formedness judgment — a description
--   is an annotated TERM of `Desc I`, checked like any other.

-- the motive's context: index, then scrutinee
motCtxᴬ : (Γ : ACtx) → ATm ⌊ Γ ⌋ᴬ → ATm ⌊ Γ ⌋ᴬ → ACtx
motCtxᴬ Γ I D = (Γ ▹ᴬ El I) ▹ᴬ IMu (renTmᴬ vs I) (renTmᴬ vs D) (var vz)

data _⊢ᴬ_∷_ where
  ⊢ᴬvar  : ∀ {Γ x A} → Γ ∋ᴬ x ∷ A → Γ ⊢ᴬ var x ∷ A
  -- the DOMAIN is in the term
  ⊢ᴬlam  : ∀ {Γ A B t} → Γ ⊢tyᴬ A → (Γ ▹ᴬ A) ⊢ᴬ t ∷ B → Γ ⊢ᴬ lam A t ∷ Π A B
  ⊢ᴬapp  : ∀ {Γ A B t u} → Γ ⊢ᴬ t ∷ Π A B → Γ ⊢ᴬ u ∷ A →
                           Γ ⊢ᴬ app t u ∷ subTyᴬ (singleᴬ u) B
  -- the FAMILY is in the term
  ⊢ᴬpair : ∀ {Γ A B a b} → (Γ ▹ᴬ A) ⊢tyᴬ B →
                           Γ ⊢ᴬ a ∷ A → Γ ⊢ᴬ b ∷ subTyᴬ (singleᴬ a) B →
                           Γ ⊢ᴬ pair B a b ∷ Σ' A B
  ⊢ᴬabsurd : ∀ {Γ c e} → Γ ⊢ᴬ c ∷ U → Γ ⊢ᴬ e ∷ base → Γ ⊢ᴬ absurd c e ∷ El c
  ⊢ᴬordtr : ∀ {Γ a t u p q} →
            Γ ⊢ᴬ a ∷ Nat → Γ ⊢ᴬ t ∷ Nat → Γ ⊢ᴬ u ∷ Nat →
            Γ ⊢ᴬ p ∷ Hom Nat a t → Γ ⊢ᴬ q ∷ Hom Nat t u →
            Γ ⊢ᴬ ordtr a t u p q ∷ Hom Nat a u
  ⊢ᴬfst  : ∀ {Γ A B p} → Γ ⊢ᴬ p ∷ Σ' A B → Γ ⊢ᴬ fst p ∷ A
  ⊢ᴬsnd  : ∀ {Γ A B p} → Γ ⊢ᴬ p ∷ Σ' A B →
                         Γ ⊢ᴬ snd p ∷ subTyᴬ (singleᴬ (fst p)) B
  ⊢ᴬ⌜base⌝ : ∀ {Γ} → Γ ⊢ᴬ ⌜base⌝ ∷ U
  ⊢ᴬ⌜Π⌝  : ∀ {Γ c d} → Γ ⊢ᴬ c ∷ U → (Γ ▹ᴬ El c) ⊢ᴬ d ∷ U → Γ ⊢ᴬ ⌜Π⌝ c d ∷ U
  ⊢ᴬ⌜Σ⌝  : ∀ {Γ c d} → Γ ⊢ᴬ c ∷ U → (Γ ▹ᴬ El c) ⊢ᴬ d ∷ U → Γ ⊢ᴬ ⌜Σ⌝ c d ∷ U
  ⊢ᴬ⌜Hom⌝ : ∀ {Γ c a b} → Γ ⊢ᴬ c ∷ U → Γ ⊢ᴬ a ∷ El c → Γ ⊢ᴬ b ∷ El c →
                          Γ ⊢ᴬ ⌜Hom⌝ c a b ∷ U
  ⊢ᴬhrefl : ∀ {Γ c t} → Γ ⊢ᴬ c ∷ U → Γ ⊢ᴬ t ∷ El c →
                        Γ ⊢ᴬ hrefl c t ∷ Hom (El c) t t
  ⊢ᴬtrU  : ∀ {Γ p e t u} →
           Γ ⊢ᴬ t ∷ U → Γ ⊢ᴬ u ∷ U →
           Γ ⊢ᴬ p ∷ Hom U t u → Γ ⊢ᴬ e ∷ El t →
           Γ ⊢ᴬ tr U t u (var vz) p e ∷ El u
  -- the side conditions are about COMPUTATION, so they read the erasure
  -- ★ the AMBIENT and ENDPOINTS are in the term (the §1 audit's finding)
  ⊢ᴬtr   : ∀ {Γ A c a p e t u} →
           Γ ⊢tyᴬ A →
           (Γ ▹ᴬ A) ⊢ᴬ c ∷ U → (Γ ▹ᴬ A) ⊢ᴬ a ∷ El c →
           (Γ ▹ᴬ A) ⊢ᴬ var vz ∷ El c →
           NoNatC ⌈ c ⌉ →
           occTm vz ⌈ c ⌉ ≡ false → occTm vz ⌈ a ⌉ ≡ false →
           Γ ⊢ᴬ t ∷ A → Γ ⊢ᴬ u ∷ A →
           Γ ⊢ᴬ p ∷ Hom A t u →
           Γ ⊢ᴬ e ∷ El (subTmᴬ (singleᴬ t) (⌜Hom⌝ c a (var vz))) →
           Γ ⊢ᴬ tr A t u (⌜Hom⌝ c a (var vz)) p e
             ∷ El (subTmᴬ (singleᴬ u) (⌜Hom⌝ c a (var vz)))
  ⊢ᴬap   : ∀ {Γ cA cB b p t u} →
           Γ ⊢ᴬ cA ∷ U → flat? ⌈ cA ⌉ ≡ true →
           Γ ⊢ᴬ cB ∷ U →
           (Γ ▹ᴬ El cA) ⊢ᴬ b ∷ El (renTmᴬ vs cB) →
           Γ ⊢ᴬ t ∷ El cA → Γ ⊢ᴬ u ∷ El cA →
           Γ ⊢ᴬ p ∷ Hom (El cA) t u →
           Γ ⊢ᴬ ap cA t u cB b p ∷ Hom (El cB) (subTmᴬ (singleᴬ t) b) (subTmᴬ (singleᴬ u) b)
  ⊢ᴬ⌜Id⌝ : ∀ {Γ c a b} → Γ ⊢ᴬ c ∷ U → Γ ⊢ᴬ a ∷ El c → Γ ⊢ᴬ b ∷ El c →
                         Γ ⊢ᴬ ⌜Id⌝ c a b ∷ U
  ⊢ᴬ⌜Nat⌝  : ∀ {Γ} → Γ ⊢ᴬ ⌜Nat⌝ ∷ U
  ⊢ᴬ⌜IMu⌝  : ∀ {Γ I D i} → Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ D ∷ Desc I → Γ ⊢ᴬ i ∷ El I → Γ ⊢ᴬ ⌜IMu⌝ I D i ∷ U
  ⊢ᴬ⌜Fin⌝  : ∀ {Γ n} → Γ ⊢ᴬ ⌜Fin⌝ n ∷ U
  ⊢ᴬ⌜Unit⌝ : ∀ {Γ} → Γ ⊢ᴬ ⌜Unit⌝ ∷ U
  ⊢ᴬidrefl : ∀ {Γ c t} → Γ ⊢ᴬ c ∷ U → Γ ⊢ᴬ t ∷ El c →
                         Γ ⊢ᴬ idrefl c t ∷ Id (El c) t t
  ⊢ᴬjsub : ∀ {Γ A d t u p e} →
           Γ ⊢tyᴬ A →
           (Γ ▹ᴬ A) ⊢ᴬ d ∷ U →
           Γ ⊢ᴬ t ∷ A → Γ ⊢ᴬ u ∷ A →
           Γ ⊢ᴬ p ∷ Id A t u →
           Γ ⊢ᴬ e ∷ El (subTmᴬ (singleᴬ t) d) →
           Γ ⊢ᴬ jsub A t u d p e ∷ El (subTmᴬ (singleᴬ u) d)
  ⊢ᴬunit  : ∀ {Γ} → Γ ⊢ᴬ unit ∷ Unit
  ⊢ᴬnzero : ∀ {Γ} → Γ ⊢ᴬ nzero ∷ Nat
  ⊢ᴬnsuc  : ∀ {Γ n} → Γ ⊢ᴬ n ∷ Nat → Γ ⊢ᴬ nsuc n ∷ Nat
  -- the MOTIVE is in the term
  ⊢ᴬnatrec : ∀ {Γ M z s n} →
             (Γ ▹ᴬ Nat) ⊢tyᴬ M →
             Γ ⊢ᴬ z ∷ subTyᴬ (singleᴬ nzero) M →
             ((Γ ▹ᴬ Nat) ▹ᴬ M) ⊢ᴬ s ∷ subTyᴬ nrsᴬ M →
             Γ ⊢ᴬ n ∷ Nat →
             Γ ⊢ᴬ natrec M z s n ∷ subTyᴬ (singleᴬ n) M
  -- ★★ LEVITATED FAMILIES — index code (and motive, index) in the term
  ⊢ᴬdι   : ∀ {Γ I j} → Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ j ∷ El I → Γ ⊢ᴬ dι I j ∷ Desc I
  ⊢ᴬdσ   : ∀ {Γ I S f} → Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ S ∷ U →
           Γ ⊢ᴬ f ∷ Π (El S) (Desc (renTmᴬ vs I)) → Γ ⊢ᴬ dσ I S f ∷ Desc I
  ⊢ᴬdρ   : ∀ {Γ I j C} → Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ j ∷ El I → Γ ⊢ᴬ C ∷ Desc I → Γ ⊢ᴬ dρ I j C ∷ Desc I
  ⊢ᴬdpay : ∀ {Γ I D C i} → Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ D ∷ Desc I → Γ ⊢ᴬ C ∷ Desc I → Γ ⊢ᴬ i ∷ El I →
           Γ ⊢ᴬ dpay I D C i ∷ U
  ⊢ᴬcon  : ∀ {Γ I D i p} → Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ D ∷ Desc I → Γ ⊢ᴬ i ∷ El I →
           Γ ⊢ᴬ p ∷ El (dpay I D D i) → Γ ⊢ᴬ con I D i p ∷ IMu I D i
  ⊢ᴬdih  : ∀ {Γ I D M e C i p} →
           Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ D ∷ Desc I → motCtxᴬ Γ I D ⊢tyᴬ M → Γ ⊢ᴬ e ∷ MethTyᴬ I D M →
           Γ ⊢ᴬ C ∷ Desc I → Γ ⊢ᴬ i ∷ El I → Γ ⊢ᴬ p ∷ El (dpay I D C i) →
           Γ ⊢ᴬ dih I D M e C i p ∷ DIh I D M C i p
  ⊢ᴬielim : ∀ {Γ I D M e i t} →
            Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ D ∷ Desc I → motCtxᴬ Γ I D ⊢tyᴬ M → Γ ⊢ᴬ e ∷ MethTyᴬ I D M →
            Γ ⊢ᴬ i ∷ El I → Γ ⊢ᴬ t ∷ IMu I D i →
            Γ ⊢ᴬ ielim I D M i e t ∷ iinstᴬ i t M
  ⊢ᴬfzero  : ∀ {Γ n} → Γ ⊢ᴬ fzero n ∷ Fin (suc n)
  ⊢ᴬfsuc   : ∀ {Γ n t} → Γ ⊢ᴬ t ∷ Fin n → Γ ⊢ᴬ fsuc n t ∷ Fin (suc n)
  ⊢ᴬfcase  : ∀ {Γ n P t a b} →
             (Γ ▹ᴬ Fin (suc n)) ⊢tyᴬ P → Γ ⊢ᴬ t ∷ Fin (suc n) →
             Γ ⊢ᴬ a ∷ subTyᴬ (singleᴬ (fzero n)) P →
             (Γ ▹ᴬ Fin n) ⊢ᴬ b ∷ subTyᴬ (fsucSᴬ n) P →
             Γ ⊢ᴬ fcase n P t a b ∷ subTyᴬ (singleᴬ t) P
  ⊢ᴬfcase0 : ∀ {Γ P t} → (Γ ▹ᴬ Fin zero) ⊢tyᴬ P → Γ ⊢ᴬ t ∷ Fin zero →
             Γ ⊢ᴬ fcase0 P t ∷ subTyᴬ (singleᴬ t) P
  ⊢ᴬpsplit : ∀ {Γ A B P q b} →
             Γ ⊢tyᴬ A → (Γ ▹ᴬ A) ⊢tyᴬ B → (Γ ▹ᴬ Σ' A B) ⊢tyᴬ P → Γ ⊢ᴬ q ∷ Σ' A B →
             ((Γ ▹ᴬ A) ▹ᴬ B) ⊢ᴬ b ∷ subTyᴬ (pairSᴬ B) P →
             Γ ⊢ᴬ psplit A B P b q ∷ subTyᴬ (singleᴬ q) P
  -- ★ (c): conversion of ERASURES
  ⊢ᴬconv : ∀ {Γ t A B} → Γ ⊢ᴬ t ∷ A → ⌈ A ⌉ᵀ ≅ᵀ ⌈ B ⌉ᵀ → Γ ⊢ᴬ t ∷ B

data _⊢tyᴬ_ where
  tyᴬ-base : ∀ {Γ} → Γ ⊢tyᴬ base
  tyᴬ-U    : ∀ {Γ} → Γ ⊢tyᴬ U
  tyᴬ-Π    : ∀ {Γ A B} → Γ ⊢tyᴬ A → (Γ ▹ᴬ A) ⊢tyᴬ B → Γ ⊢tyᴬ Π A B
  tyᴬ-Σ    : ∀ {Γ A B} → Γ ⊢tyᴬ A → (Γ ▹ᴬ A) ⊢tyᴬ B → Γ ⊢tyᴬ Σ' A B
  tyᴬ-El   : ∀ {Γ c} → Γ ⊢ᴬ c ∷ U → Γ ⊢tyᴬ El c
  tyᴬ-Id   : ∀ {Γ A t u} → Γ ⊢tyᴬ A → Γ ⊢ᴬ t ∷ A → Γ ⊢ᴬ u ∷ A → Γ ⊢tyᴬ Id A t u
  tyᴬ-Unit : ∀ {Γ} → Γ ⊢tyᴬ Unit
  tyᴬ-Nat  : ∀ {Γ} → Γ ⊢tyᴬ Nat
  tyᴬ-IMu  : ∀ {Γ I D i} → Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ D ∷ Desc I → Γ ⊢ᴬ i ∷ El I → Γ ⊢tyᴬ IMu I D i
  tyᴬ-Desc : ∀ {Γ I} → Γ ⊢ᴬ I ∷ U → Γ ⊢tyᴬ Desc I
  tyᴬ-DIh  : ∀ {Γ I D M C i p} →
             Γ ⊢ᴬ I ∷ U → Γ ⊢ᴬ D ∷ Desc I → motCtxᴬ Γ I D ⊢tyᴬ M → Γ ⊢ᴬ C ∷ Desc I →
             Γ ⊢ᴬ i ∷ El I → Γ ⊢ᴬ p ∷ El (dpay I D C i) → Γ ⊢tyᴬ DIh I D M C i p
  tyᴬ-Fin  : ∀ {Γ n} → Γ ⊢tyᴬ Fin n
  tyᴬ-Hom  : ∀ {Γ A t u} → Γ ⊢tyᴬ A → Γ ⊢ᴬ t ∷ A → Γ ⊢ᴬ u ∷ A → Γ ⊢tyᴬ Hom A t u

