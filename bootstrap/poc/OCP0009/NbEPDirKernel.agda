------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 15 — the STRICT CARTESIAN DEPENDENT KERNEL:
--                              `Id = Hom`, substitution commutes with `⟶*`
--
-- The design conclusion of this POC (HANDOFF §1–2), realized as a module:
-- add dependent types to Once as a CARTESIAN dependent type theory whose
-- IDENTITY TYPE is the reduction relation `Hom a b := a ⟶* b`. This is the
-- "one POC that demonstrates the whole recommendation end-to-end" (§2).
--
-- The lever the point-free CCC hands us for free: SUBSTITUTION IS PRE-
-- COMPOSITION. A term-in-context is a morphism `Term Γ B`; a substitution
-- `σ : Sub Δ Γ` is a morphism `Term Δ Γ`; and `t[σ] := t ∘ σ`. Everything
-- below is then a fact about `_∘_` and `_⟶*_` — no bespoke substitution
-- calculus, no coherence fight.
--
--   * `_[_]`         — substitution = precomposition (strict by construction);
--   * `Id`           — the identity type = `NbEPDir.Hom` = `_⟶*_`;
--   * `Id-sub`       — THE SUBSTANTIVE LEMMA: substitution commutes with
--                      reduction, `(a ⟶* b)[σ] → (a[σ] ⟶* b[σ])`. This makes
--                      `Id` STABLE under substitution — a well-behaved former.
--                      (It IS `CCC.⟶*-∘-l`, named at the kernel level.)
--   * `sub-idˡ`/`sub-∘` — the substitution COHERENCE LAWS ARE REDUCTIONS:
--                      `t[id] ⟶ t` is `id-right`, `t[σ][τ] ⟶ t[σ∘τ]` is
--                      `assoc-r`. So substitution is strict *up to `Hom`* —
--                      and since `core(Hom) =` definitional equality, that is
--                      strict up to definitional equality. "Strict substitution"
--                      and "Id = Hom" are the SAME relation. That is the whole
--                      design in one observation.
--   * `Id-sub-idH`/`Id-sub-trans` — substitution is a FUNCTOR of the directed
--                      identity type (preserves `idH` / chain composition): the
--                      structural form of "directed `J` (NbEPDirJ.J⟶) commutes
--                      with subst".
--   * `Core`         — the GROUPOID CORE `Id a b × Id b a` (inter-reducible):
--                      symmetric BY CONSTRUCTION (the symmetry `Id` itself
--                      refuses — `NbEPDirJ.no-sym`), reflexive, transitive, and
--                      subst-stable. This is `core(Hom)` = the definitional
--                      equality NbE decides. The reversible reshuffles
--                      (assoc/unit) live here; the irreversible `opt`
--                      (`NbEPDir.no-way-back`) provably does NOT.
--   * `core→≋`       — the bridge: `core(Hom) ⊆ ≋` (denotational equality),
--                      hence decided by the engine (`Sound.conv-decides` on
--                      closed first-order terms). Given axiom-free on the
--                      associativity witness; funext-parameterized in general
--                      (discharged by `EvalSound.eval-sound`).
--
-- `--safe`, ZERO axioms in this module. The single axiom the denotational
-- bridge ultimately rests on (funext, for `eval`-soundness) is threaded as a
-- hypothesis, per the tower's ground rules — never assumed here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirKernel where

open import normalizer.Syntax.Types
  using ( Ty; _≡_; refl; cong; trans; ¬_; _×_; _,_; Σ )
open import normalizer.Syntax.CCC
  using ( Term; _∘_; id; _⟶_; _⟶*_; done; step
        ; id-right; assoc-l; assoc-r; ⟶-∘-l; ⟶*-∘-l; ⟶*-∘-r; ⟶*-trans )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; eval )
open import poc.OCP0009.NbEPDir
  using ( Hom; idH; src; tgt; opt; no-way-back )
open import poc.OCP0009.NbEPDirJ
  using ( no-sym )
open Σ  -- fst / snd

private
  variable
    A B C D Γ Δ Θ : Ty

------------------------------------------------------------------------
-- Substitution = precomposition. In the point-free kernel a term-in-context
-- `Γ` of type `B` is a morphism `Term Γ B`, a substitution `Sub Δ Γ` is a
-- morphism `Term Δ Γ`, and reindexing is `_∘_`. Nothing exotic.
------------------------------------------------------------------------

Sub : Ty → Ty → Set
Sub Δ Γ = Term Δ Γ

_[_] : Term Γ B → Sub Δ Γ → Term Δ B
t [ σ ] = t ∘ σ

------------------------------------------------------------------------
-- The identity type IS the directed reduction hom `Hom a b = a ⟶* b`.
------------------------------------------------------------------------

Id : Term A B → Term A B → Set
Id a b = Hom a b

------------------------------------------------------------------------
-- THE SUBSTANTIVE LEMMA (HANDOFF §2): substitution commutes with reduction.
--   single step  — `a ⟶ b  →  a[σ] ⟶ b[σ]`     (a congruence of `_⟶_`);
--   closure      — `a ⟶* b →  a[σ] ⟶* b[σ]`    ( = `Id` stable under subst).
-- The forward reindexing map `(a ⟶* b)[σ] → (a[σ] ⟶* b[σ])` — this is what
-- makes `Id` a well-behaved (substitution-stable) type former, and hands
-- `core(Id) =` NbE-convertibility as the definitional equality for free.
------------------------------------------------------------------------

⟶-sub : (σ : Sub Δ Γ) {a b : Term Γ B} → a ⟶ b → (a [ σ ]) ⟶ (b [ σ ])
⟶-sub σ r = ⟶-∘-l r

Id-sub : (σ : Sub Δ Γ) {a b : Term Γ B} → Id a b → Id (a [ σ ]) (b [ σ ])
Id-sub σ p = ⟶*-∘-l σ p

-- `Id` is also covariant in its type index: a type-level map `τ` acts on the
-- endpoints (whiskering), `Id a b → Id (τ ∘ a) (τ ∘ b)`. (`NbEPDirV` variance.)
Id-whisker : (τ : Term B C) {a b : Term Γ B} → Id a b → Id (τ ∘ a) (τ ∘ b)
Id-whisker τ p = ⟶*-∘-r τ p

------------------------------------------------------------------------
-- The substitution COHERENCE LAWS are themselves REDUCTIONS — they live in
-- `Hom`, i.e. hold definitionally in the `Id = core(Hom)` sense. This is the
-- design's keystone: substitution is strict "up to `Hom`", and there is no
-- separate strictness obligation to discharge, because `Hom` is the identity
-- type. (On-the-nose strictness would need a de Bruijn calculus; here the
-- coherences are `id-right` and `assoc-r`, one reduction step each.)
------------------------------------------------------------------------

sub-idˡ : (t : Term Γ B) → (t [ id ]) ⟶ t
sub-idˡ t = id-right

sub-∘ : (t : Term Γ B) (σ : Sub Δ Γ) (τ : Sub Θ Δ) →
        ((t [ σ ]) [ τ ]) ⟶ (t [ σ ∘ τ ])
sub-∘ t σ τ = assoc-r

-- ...packaged as inhabitants of `Id`, i.e. as definitional equalities:
sub-idˡ-Id : (t : Term Γ B) → Id (t [ id ]) t
sub-idˡ-Id t = step (sub-idˡ t) done

sub-∘-Id : (t : Term Γ B) (σ : Sub Δ Γ) (τ : Sub Θ Δ) →
           Id ((t [ σ ]) [ τ ]) (t [ σ ∘ τ ])
sub-∘-Id t σ τ = step (sub-∘ t σ τ) done

------------------------------------------------------------------------
-- SUBSTITUTION IS A FUNCTOR OF THE DIRECTED IDENTITY TYPE.
-- `Id-sub σ` preserves reflexivity (`idH`) and composition (`_∘H_`) of homs
-- — precomposition-by-`σ` is a functor on the free reduction category. This
-- is exactly "directed `J` commutes with substitution" in structural form:
-- `J⟶` (NbEPDirJ) is the fold over reduction chains, and a functor commutes
-- with that fold.
------------------------------------------------------------------------

-- reflexivity: `Id-sub` preserves the identity hom (`idH = done`).
Id-sub-idH : (σ : Sub Δ Γ) {a : Term Γ B} → Id-sub σ (idH {t = a}) ≡ idH
Id-sub-idH σ = refl

-- composition: `Id-sub` preserves chain composition (`⟶*-trans`, the free
-- category's composite). Together with `Id-sub-idH`, precomposition-by-`σ`
-- is a FUNCTOR on the directed identity type — the structural content of
-- "directed `J` commutes with substitution". (Stated over `⟶*`/`⟶*-trans`,
-- which recurses on its first argument, so the `done`-case endpoint collapse
-- propagates cleanly through the `⟶*-∘-l` wrapper.)
Id-sub-trans : (σ : Sub Δ Γ) {a b c : Term Γ B} (p : a ⟶* b) (q : b ⟶* c) →
               ⟶*-∘-l σ (⟶*-trans p q) ≡ ⟶*-trans (⟶*-∘-l σ p) (⟶*-∘-l σ q)
Id-sub-trans σ done       q = refl
Id-sub-trans σ (step s p) q = cong (step (⟶-∘-l s)) (Id-sub-trans σ p q)

------------------------------------------------------------------------
-- THE GROUPOID CORE — `core(Hom)` = the definitional equality NbE decides.
-- The INVERTIBLE part of the directed `Id`: `a` and `b` inter-reducible.
------------------------------------------------------------------------

Core : Term A B → Term A B → Set
Core a b = Id a b × Id b a

core-refl : {a : Term A B} → Core a a
core-refl = idH , idH

-- Symmetric BY CONSTRUCTION — the one law the directed `Id` provably REFUSES
-- (`no-sym`). The core is where symmetry is recovered: swap the pair.
core-sym : {a b : Term A B} → Core a b → Core b a
core-sym (ab , ba) = ba , ab

core-trans : {a b c : Term A B} → Core a b → Core b c → Core a c
core-trans (ab , ba) (bc , cb) = ⟶*-trans ab bc , ⟶*-trans cb ba

-- The symmetric definitional equality is ALSO substitution-stable — a
-- well-behaved conversion — since each component reindexes by `Id-sub`.
core-sub : (σ : Sub Δ Γ) {a b : Term Γ B} → Core a b → Core (a [ σ ]) (b [ σ ])
core-sub σ (ab , ba) = Id-sub σ ab , Id-sub σ ba

------------------------------------------------------------------------
-- DIRECTED vs CORE, made concrete. The reversible reshuffles are in `Core`;
-- the irreversible optimizer step provably is NOT — the whole point of a
-- DIRECTED identity type whose core is the ordinary one.
------------------------------------------------------------------------

-- Associativity is reversible (`assoc-l`/`assoc-r` are mutual inverses as
-- reductions) — so it is a genuine `Core` witness, a definitional equality.
assoc-core : {f : Term C D} {g : Term B C} {h : Term A B} →
             Core (f ∘ (g ∘ h)) ((f ∘ g) ∘ h)
assoc-core = step assoc-l done , step assoc-r done

-- The optimizer step `opt : Id src tgt` (project a duplicated value) exists
-- FORWARD, but `no-way-back` refutes its reverse — so it is NOT in `Core`.
-- Direction is real: `opt` is a transformation, not a definitional equality.
opt-directed : Id src tgt
opt-directed = opt

opt-∉-core : ¬ Core src tgt
opt-∉-core c = no-way-back (snd c)

------------------------------------------------------------------------
-- THE BRIDGE — `core(Hom) ⊆ ≋` (denotational equality), hence decided by the
-- engine. `_≋_` is observational equality of IR morphisms (`Sound._≋_`).
------------------------------------------------------------------------

-- (a record, not a plain Π, so the endpoints stay recoverable by unification
--  — `eval` is not injective, so a bare `∀ x → eval t x ≡ eval u x` would
--  block `≋-trans`'s middle-term inference.)
record _≋_ {A B} (t u : Term A B) : Set where
  constructor mk≋
  field app : (x : ⟦ A ⟧T) → eval t x ≡ eval u x
open _≋_

≋-refl : {t : Term A B} → t ≋ t
≋-refl = mk≋ (λ x → refl)

≋-trans : {t u v : Term A B} → t ≋ u → u ≋ v → t ≋ v
≋-trans e₁ e₂ = mk≋ (λ x → trans (app e₁ x) (app e₂ x))

-- A directed reduction chain lands in `≋`, GIVEN reduction is denotationally
-- sound (`sound = EvalSound.eval-sound`, the tower's one funext theorem —
-- threaded, never assumed here).
Id→≋ : (sound : ∀ {A B} {t u : Term A B} → t ⟶ u → t ≋ u) →
       {a b : Term A B} → Id a b → a ≋ b
Id→≋ sound done       = ≋-refl
Id→≋ sound (step s p) = ≋-trans (sound s) (Id→≋ sound p)

-- Hence `core(Hom)` collapses into denotational equality — the definitional
-- equality a type-checker decides (`Sound.conv-decides`, closed first-order).
core→≋ : (sound : ∀ {A B} {t u : Term A B} → t ⟶ u → t ≋ u) →
         {a b : Term A B} → Core a b → a ≋ b
core→≋ sound (ab , _) = Id→≋ sound ab

------------------------------------------------------------------------
-- The bridge, AXIOM-FREE, on the associativity witness: precomposition
-- associates on the nose under `eval`, so no funext is needed here — a
-- concrete `Core → ≋` with zero axioms, witnessing the general map above.
------------------------------------------------------------------------

assoc-≋ : (f : Term C D) (g : Term B C) (h : Term A B) →
          (f ∘ (g ∘ h)) ≋ ((f ∘ g) ∘ h)
assoc-≋ f g h = mk≋ (λ x → refl)
