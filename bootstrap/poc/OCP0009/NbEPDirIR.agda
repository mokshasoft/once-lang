------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 6 — the real IR's `NatTr`/`Fuse`, DIRECTED
--
-- The on-ramp from the POC's directed cata (`NbEPDirC`/`NbEPDirF`) to the
-- REAL compiler IR (`formal/Once/IR.agda`, branch plan-0.52). The real IR's
-- total recursion scheme is `Fuse`, μ-anchored deforestation:
--
--     Fuse : (⟦F⟧B → B) → NatTr G F → (μG → B)      Fuse alg τ = cata (alg ∘ τ)
--
-- and its totality rides on the shape of `NatTr`. The KEY design fact —
-- the one that makes this port clean — is that the real IR's `NatTr` is
-- NOT a bundled morphism-plus-coherence: it is a SYNTACTIC INDUCTIVE type
-- whose constructors mirror the polynomial-functor combinators
-- (`ntId`/`ntK`/`ntFst`/`ntSnd`/`ntCase`/`ntInl`/`ntInr`/`ntPair`). Every
-- such `τ` is a POLYNOMIAL natural transformation (a container/lens
-- morphism), so naturality is automatic — there is no coherence square to
-- discharge, and the directed-naturality "wall" never arises.
--
--   * `NatTr`      — the eight-constructor structural nat-transformation,
--                    faithful to the real IR (`Kc` in place of its `K`);
--   * `⟦_⟧nt`      — its interpretation as a directed IR morphism, one
--                    clause per constructor (`fst`/`snd`/copair/inj/pair);
--   * `fuseD`      — the modeled `Fuse`, `fuseD τ alg = cata G (alg ∘ ⟦τ⟧)`;
--   * `fuse-spec`  — the real IR's defining law `Fuse alg τ = cata (alg ∘ τ)`
--                    holds DEFINITIONALLY here (the model realizes the spec);
--   * `fuse-run`   — the structural COMPUTATION, as a directed step:
--                    `fuseD τ alg ∘ In ⟶* alg ∘ (⟦τ⟧ ∘ fmap G (fuseD τ alg))`;
--                    Fuse is total because it IS a directed cata.
--
-- Scope: `μ`/`Cata`/`Fuse` only — no `Ana`/`Out`/`Hylo`/`ν` (codata).
-- `Para` (fold with access to the substructure) is a natural next port; its
-- computation rule needs `cata`-uniqueness (`NbEPDirF`), not just reduction.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirIR where

open import normalizer.Syntax.Types
  using ( Ty; Func; Id; One; Kc; _⊕_; _⊗_; μ_; ⟦_⟧F
        ; _≡_; refl; cong; cong₂; _×_; _,_; _⊎_; inj₁; inj₂ )
open import normalizer.Syntax.CCC as C
  using ( Term; id; _∘_; fst; snd; inl; inr; [_,_]; ⟨_,_⟩; In; cata; fmap
        ; _⟶_; _⟶*_; done; step; assoc-r; ⟶*-trans
        ; id-left; id-right; eta-case; eta-pair
        ; ⟶*-∘-l; ⟶*-∘-r; ⟶*-case; ⟶*-pair )
open import normalizer.Testing.Evaluator using ( ⟦_⟧T; eval )
open import poc.OCP0009.NbEPDir  using ( Hom )
open import poc.OCP0009.NbEPDirC using ( cata-run; cataH )

------------------------------------------------------------------------
-- The real IR's `NatTr`, verbatim in shape (its `K` is `Kc` here).
-- A structural — hence automatically natural — transformation of
-- polynomial functors `G ⇒ F`.
------------------------------------------------------------------------

data NatTr : Func → Func → Set where
  ntId   : NatTr Id Id
  ntK    : ∀ {G₁ G₂} → Term (μ G₁) (μ G₂) → NatTr (Kc G₁) (Kc G₂)
  ntFst  : ∀ {G₁ G₂ F} → NatTr G₁ F → NatTr (G₁ ⊗ G₂) F
  ntSnd  : ∀ {G₁ G₂ F} → NatTr G₂ F → NatTr (G₁ ⊗ G₂) F
  ntCase : ∀ {G₁ G₂ F} → NatTr G₁ F → NatTr G₂ F → NatTr (G₁ ⊕ G₂) F
  ntInl  : ∀ {G F₁ F₂} → NatTr G F₁ → NatTr G (F₁ ⊕ F₂)
  ntInr  : ∀ {G F₁ F₂} → NatTr G F₂ → NatTr G (F₁ ⊕ F₂)
  ntPair : ∀ {G F₁ F₂} → NatTr G F₁ → NatTr G F₂ → NatTr G (F₁ ⊗ F₂)

------------------------------------------------------------------------
-- Interpretation: a `NatTr G F` is a directed IR morphism, uniformly in
-- the carrier `X` — `⟦G⟧X → ⟦F⟧X` built from the CCC's plumbing.
------------------------------------------------------------------------

⟦_⟧nt : ∀ {G F} → NatTr G F → ∀ {X} → Term (⟦ G ⟧F X) (⟦ F ⟧F X)
⟦ ntId ⟧nt         = id
⟦ ntK m ⟧nt        = m
⟦ ntFst τ ⟧nt      = ⟦ τ ⟧nt ∘ fst
⟦ ntSnd τ ⟧nt      = ⟦ τ ⟧nt ∘ snd
⟦ ntCase τ₁ τ₂ ⟧nt = [ ⟦ τ₁ ⟧nt , ⟦ τ₂ ⟧nt ]
⟦ ntInl τ ⟧nt      = inl ∘ ⟦ τ ⟧nt
⟦ ntInr τ ⟧nt      = inr ∘ ⟦ τ ⟧nt
⟦ ntPair τ₁ τ₂ ⟧nt = ⟨ ⟦ τ₁ ⟧nt , ⟦ τ₂ ⟧nt ⟩

------------------------------------------------------------------------
-- The modeled `Fuse`, and its two defining facts.
------------------------------------------------------------------------

-- `Fuse alg τ = cata (alg ∘ τ)` — total by being a `cata`.
fuseD : ∀ {G F B} → NatTr G F → Term (⟦ F ⟧F B) B → Term (μ G) B
fuseD {G} τ alg = cata G (alg ∘ ⟦ τ ⟧nt)

-- The real IR's defining law, holding DEFINITIONALLY in this model.
fuse-spec : ∀ {G F B} (τ : NatTr G F) (alg : Term (⟦ F ⟧F B) B) →
            Hom (fuseD τ alg) (cata G (alg ∘ ⟦ τ ⟧nt))
fuse-spec τ alg = done

-- The structural computation rule, as a directed step: applying the fused
-- fold to a constructed value consumes ONE G-layer through `⟦τ⟧` and
-- recurses under `fmap G` — Fuse computes by reduction, exactly as `cata`.
fuse-run : ∀ {G F B} (τ : NatTr G F) (alg : Term (⟦ F ⟧F B) B) →
           Hom (fuseD τ alg ∘ In)
               (alg ∘ (⟦ τ ⟧nt ∘ fmap G (fuseD τ alg)))
fuse-run {G} τ alg = ⟶*-trans (cata-run G) (step assoc-r done)

------------------------------------------------------------------------
-- A concrete, non-trivial `NatTr` witnessing the datatype computes: the
-- summand swap `Id ⊕ Id ⇒ Id ⊕ Id`. `fuse-run` fires on it uniformly.
------------------------------------------------------------------------

swap⊕ : NatTr (Id ⊕ Id) (Id ⊕ Id)
swap⊕ = ntCase (ntInr ntId) (ntInl ntId)

-- Its interpretation is the copair that flips the tags (`[inr∘id, inl∘id]`).
_ : ∀ {X} → Term (⟦ Id ⊕ Id ⟧F X) (⟦ Id ⊕ Id ⟧F X)
_ = ⟦ swap⊕ ⟧nt

-- Fusing over `μ(Id ⊕ Id)` with the swap computes as a directed step.
_ : ∀ {B} (alg : Term (⟦ Id ⊕ Id ⟧F B) B) →
    Hom (fuseD swap⊕ alg ∘ In)
        (alg ∘ (⟦ swap⊕ ⟧nt ∘ fmap (Id ⊕ Id) (fuseD swap⊕ alg)))
_ = λ alg → fuse-run swap⊕ alg

------------------------------------------------------------------------
-- Fuse GENERALIZES Cata: the identity structural `NatTr` interprets to the
-- identity, so `Fuse alg idNat` reduces to `cata alg` — directionally.
--
-- `idNat` exists for the ONE-free polynomial functors (`Poly`): the real
-- IR has no bare `One` leaf — its base is `K Unit`, an `ntK` — and a bare
-- `One` has no self-`NatTr` (there is no directed `terminal ⟶ id`). The
-- `idNat-id` proof is `NbEPDirC.fmap-idH` verbatim in shape: the identity
-- transformation and the identity `fmap` collapse the same way.
------------------------------------------------------------------------

data Poly : Func → Set where
  pId : Poly Id
  pKc : ∀ {G} → Poly (Kc G)
  p⊕  : ∀ {F G} → Poly F → Poly G → Poly (F ⊕ G)
  p⊗  : ∀ {F G} → Poly F → Poly G → Poly (F ⊗ G)

idNat : ∀ {F} → Poly F → NatTr F F
idNat pId        = ntId
idNat pKc        = ntK id
idNat (p⊕ pf pg) = ntCase (ntInl (idNat pf)) (ntInr (idNat pg))
idNat (p⊗ pf pg) = ntPair (ntFst (idNat pf)) (ntSnd (idNat pg))

idNat-id : ∀ {F} (pf : Poly F) {X} → Hom (⟦ idNat pf ⟧nt {X}) id
idNat-id pId        = done
idNat-id pKc        = done
idNat-id (p⊕ pf pg) =
  ⟶*-trans (⟶*-case (⟶*-∘-r inl (idNat-id pf)) (⟶*-∘-r inr (idNat-id pg)))
  (⟶*-trans (⟶*-case (step id-right done) (step id-right done))
            (step eta-case done))
idNat-id (p⊗ pf pg) =
  ⟶*-trans (⟶*-pair (⟶*-∘-l fst (idNat-id pf)) (⟶*-∘-l snd (idNat-id pg)))
  (⟶*-trans (⟶*-pair (step id-left done) (step id-left done))
            (step eta-pair done))

-- Fuse with the identity structural transformation IS Cata (directionally).
fuse-idNat : ∀ {F B} (pf : Poly F) (alg : Term (⟦ F ⟧F B) B) →
             Hom (fuseD (idNat pf) alg) (cata F alg)
fuse-idNat {F} pf alg =
  cataH F (⟶*-trans (⟶*-∘-r alg (idNat-id pf)) (step id-right done))

------------------------------------------------------------------------
-- The ℕ analog `μ(Kc One ⊕ Id)` (the real IR's `K Unit ⊕ Id`): its
-- identity Fuse reduces to the plain fold.
------------------------------------------------------------------------

NatK : Func
NatK = Kc One ⊕ Id

_ : ∀ {B} (alg : Term (⟦ NatK ⟧F B) B) →
    Hom (fuseD (idNat (p⊕ pKc pId)) alg) (cata NatK alg)
_ = λ alg → fuse-idNat (p⊕ pKc pId) alg

------------------------------------------------------------------------
-- Every structural `NatTr` IS natural — the coherence layer.
--
-- Because `NatTr` is a POLYNOMIAL transformation, naturality is a THEOREM,
-- provable by induction on the constructor (no coherence field is stored).
-- Stated semantically (`eval`, pointwise) — the honest form without funext,
-- matching `NbEPDirF`'s `≡`-level coherence. The square
-- `fmap F f ∘ ⟦τ⟧ = ⟦τ⟧ ∘ fmap G f` commutes: transporting a carrier `f`
-- through the target functor after `τ` equals `τ` after transporting through
-- the source functor. Each case is IH glued by `cong`/`cong₂` — the
-- CCC/`fmap` plumbing computes the rest definitionally.
------------------------------------------------------------------------

nt-nat : ∀ {G F} (τ : NatTr G F) {A B} (f : Term A B)
         (x : ⟦ ⟦ G ⟧F A ⟧T) →
         eval (fmap F f ∘ ⟦ τ ⟧nt) x ≡ eval (⟦ τ ⟧nt ∘ fmap G f) x
nt-nat ntId           f x         = refl
nt-nat (ntK m)        f x         = refl
nt-nat (ntFst τ)      f (x₁ , x₂) = nt-nat τ f x₁
nt-nat (ntSnd τ)      f (x₁ , x₂) = nt-nat τ f x₂
nt-nat (ntCase τ₁ τ₂) f (inj₁ y)  = nt-nat τ₁ f y
nt-nat (ntCase τ₁ τ₂) f (inj₂ z)  = nt-nat τ₂ f z
nt-nat (ntInl τ)      f x         = cong inj₁ (nt-nat τ f x)
nt-nat (ntInr τ)      f x         = cong inj₂ (nt-nat τ f x)
nt-nat (ntPair τ₁ τ₂) f x         = cong₂ _,_ (nt-nat τ₁ f x) (nt-nat τ₂ f x)
