------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 3 — DIRECTED RECURSION: the cata fragment
--
-- The wall-free half of the variance story (`NbEPDirV`). Catamorphisms
-- live over POLYNOMIAL functors (`Func = Id | One | Kc | ⊕ | ⊗` — no
-- exponential), so there is no η debt: `fmap` and `cata` are directed
-- functors BY REDUCTION (`⟶*`), and the fold's computation rule is a
-- directed step. Scope: `μ`/`Cata`/folds only — no `ana`/`Hylo`/`ν`.
--
--   * `fmapH`       — a polynomial functor acts on directed maps;
--   * `fmap-idH`    — …preserving identity (the functor law, by `⟶*`);
--   * `cataH`       — `cata` is a directed functor in its ALGEBRA;
--   * `cata-run`    — `cata alg ∘ In` UNFOLDS one layer as a directed step
--                     (the fold computes by reduction);
--   * `cata-zero` / `cata-succ` — the unfolding on `ℕ = μ(One ⊕ Id)`:
--     each constructor layer is consumed EXACTLY ONCE (the linearity of a
--     fold, visible in the directed trace).
--
-- Fold FUSION (`h ∘ cata alg ⟶* cata alg'` under `h ∘ alg = alg' ∘ fmap h`)
-- is the flagship, but it needs `cata`-UNIQUENESS — an induction principle
-- on `μ`, i.e. a SEMANTIC step beyond `⟶*`. Flagged at the end, not faked.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirC where

open import normalizer.Syntax.Types
  using ( Ty; Unit; _+_; Func; Id; One; Kc; _⊕_; _⊗_; μ_; ⟦_⟧F )
open import normalizer.Syntax.CCC as C
  using ( Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_]; In; cata; fmap
        ; _⟶_; _⟶*_; done; step
        ; id-left; id-right; eta-pair; eta-case; case-inl; case-inr; cata-β
        ; assoc-l; assoc-r
        ; ⟶*-trans; ⟶*-∘-l; ⟶*-∘-r; ⟶*-pair; ⟶*-case; ⟶*-cata; fmap-⟶* )
open import poc.OCP0009.NbEPDir
  using ( Hom )

------------------------------------------------------------------------
-- Polynomial functors act on directed maps (covariant, wall-free).
------------------------------------------------------------------------

fmapH : ∀ F {A B} {f f' : Term A B} → Hom f f' → Hom (fmap F f) (fmap F f')
fmapH F = fmap-⟶* F

-- The functor identity law, purely by reduction.
fmap-idH : ∀ F {A} → Hom (fmap F (id {A})) id
fmap-idH Id      = done
fmap-idH One     = done
fmap-idH (Kc G)  = done
fmap-idH (F ⊕ G) =
  ⟶*-trans (⟶*-case (⟶*-∘-r inl (fmap-idH F)) (⟶*-∘-r inr (fmap-idH G)))
  (⟶*-trans (⟶*-case (step id-right done) (step id-right done))
            (step eta-case done))
fmap-idH (F ⊗ G) =
  ⟶*-trans (⟶*-pair (⟶*-∘-l fst (fmap-idH F)) (⟶*-∘-l snd (fmap-idH G)))
  (⟶*-trans (⟶*-pair (step id-left done) (step id-left done))
            (step eta-pair done))

------------------------------------------------------------------------
-- `cata` is a directed functor in its algebra, and it COMPUTES.
------------------------------------------------------------------------

cataH : ∀ F {A} {alg alg' : Term (⟦ F ⟧F A) A} →
        Hom alg alg' → Hom (cata F alg) (cata F alg')
cataH F = ⟶*-cata F

-- The fold's computation rule, as a directed step: applying `cata alg` to a
-- constructed value unfolds one functor layer, recursing under `fmap`.
cata-run : ∀ F {A} {alg : Term (⟦ F ⟧F A) A} →
           Hom (cata F alg ∘ In) (alg ∘ fmap F (cata F alg))
cata-run F = step cata-β done

------------------------------------------------------------------------
-- The fold on ℕ = μ(One ⊕ Id): each constructor layer consumed ONCE.
--
-- `⟦ One ⊕ Id ⟧F X = Unit + X` — a Nat is either `zero` (`In ∘ inl`) or a
-- successor (`In ∘ inr`). Folding unfolds each layer by a directed chain,
-- and the RECURSIVE CALL appears EXACTLY ONCE per successor node — the
-- linearity of a fold, read straight off the directed trace (relevant to
-- linearizing `Cata`: a linear algebra ⇒ a linear fold).
------------------------------------------------------------------------

NatF : Func
NatF = One ⊕ Id

zero : Term Unit (μ NatF)
zero = In ∘ inl

suc : Term (μ NatF) (μ NatF)
suc = In ∘ inr

-- Folding `zero` picks the base branch (`alg ∘ inl`) — no recursion.
cata-zero : ∀ {A} {alg : Term (Unit + A) A} →
            Hom (cata NatF alg ∘ zero) (alg ∘ inl)
cata-zero {alg = alg} =
  ⟶*-trans (step assoc-l done)
  (⟶*-trans (⟶*-∘-l inl (cata-run NatF))
  (⟶*-trans (step assoc-r done)
  (⟶*-trans (⟶*-∘-r alg (step case-inl done))
            (⟶*-∘-r alg (step id-right done)))))

-- Folding a successor consumes the layer once and issues EXACTLY ONE
-- recursive call `cata NatF alg` on the predecessor.
cata-suc : ∀ {A} {alg : Term (Unit + A) A} →
           Hom (cata NatF alg ∘ suc) (alg ∘ (inr ∘ cata NatF alg))
cata-suc {alg = alg} =
  ⟶*-trans (step assoc-l done)
  (⟶*-trans (⟶*-∘-l inr (cata-run NatF))
  (⟶*-trans (step assoc-r done)
            (⟶*-∘-r alg (step case-inr done))))
