------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — the identity type `Id` + `J` (Rung 3)
--
-- Base CwF (`NbEPCwF`/`NbEPEl`) gives dependent types over the total core.
-- Rung 3 turns *indexing* into a *logic*: a type `Id A a b` one can inhabit
-- (by `Refl`) and eliminate (by `J`) — the machinery for STATING and PROVING
-- equalities inside the language.
--
-- Model (the honest one for a core with DECIDABLE conversion). The identity
-- type is indexed by the NbE VALUE of a term:
--
--   Id {A} (u v : Val Unit A) : Set   with   Refl : Id u u.
--
-- So on terms, `Id-tm a b = Id ⟦a⟧ ⟦b⟧` is inhabited by `Refl` EXACTLY when
-- `a` and `b` have the same NbE value — i.e. exactly when they are CONVERTIBLE
-- (the principled `nf` decision). This is the *definitional* identity type,
-- and — crucially — it supports the FULL dependent eliminator `J` (by pattern
-- matching on `Refl`), not merely `subst`. Convertibility is thereby reflected
-- as a genuine, `J`-computing propositional equality:
--
--   `Id-tm (double 1) 2` holds by `Refl` (they share the value for 2), and `J`
--   transports any value-indexed motive along it.
--
-- Honest scope / the intensional boundary. Here `Id`-equality COINCIDES with
-- conversion (both decidable). A *proof-relevant intensional* `Id` that proves
-- strictly MORE than conversion — e.g. `n + 0 ≡ n` for a VARIABLE `n`, which is
-- propositional-but-not-definitional (`Open.agda`) and needs an induction on
-- `n` — is NOT this type. That needs `Id` as a primitive NbE type-FORMER with
-- its own eliminator carrying the induction (a genuine engine extension), or an
-- axiom (funext). This module delivers the definitional `Id` + real `J`; the
-- extra-propositional layer is named, not built.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPId where

open import normalizer.Syntax.Types hiding ( Id )   -- `Id` names our type, not the functor
open import poc.OCP0009.NbEK using ( Val; vUnit; reifyVal )
open import poc.OCP0009.NbEP
  using ( Tm; _⊙_; nf; eval; zero; suc; one; two; double )
open import poc.OCP0009.NbEPCwF using ( Nat )
open import poc.OCP0009.NbEPEl  using ( Code; El; `nat; ⌜_⌝ )

------------------------------------------------------------------------
-- The identity type on NbE values, with its constructor and eliminator.
------------------------------------------------------------------------

data Id {A : Ty} (u : Val Unit A) : Val Unit A → Set where
  Refl : Id u u

-- The full dependent eliminator (`J` / based path induction) — genuine, by
-- pattern matching on `Refl` (NOT a `subst` surrogate).
J : ∀ {A} {u : Val Unit A}
  → (C : (v : Val Unit A) → Id u v → Set)
  → C u Refl
  → ∀ {v} (p : Id u v) → C v p
J C d Refl = d

-- Transport (the non-dependent corollary) and the groupoid laws, all from `J`.
transp : ∀ {A} {u v : Val Unit A} (C : Val Unit A → Set) → Id u v → C u → C v
transp C p cu = J (λ v _ → C v) cu p

Id-sym : ∀ {A} {u v : Val Unit A} → Id u v → Id v u
Id-sym {u = u} p = J (λ v _ → Id v u) Refl p

Id-trans : ∀ {A} {u v w : Val Unit A} → Id u v → Id v w → Id u w
Id-trans {u = u} p q = J (λ w _ → Id u w) p q

------------------------------------------------------------------------
-- The term-level identity type: two terms are `Id`-equal when their NbE
-- values agree — i.e. exactly when the principled checker converts them.
------------------------------------------------------------------------

⟦_⟧ : ∀ {A} → Tm Unit A → Val Unit A
⟦ a ⟧ = eval a vUnit

Id-tm : ∀ {A} → Tm Unit A → Tm Unit A → Set
Id-tm a b = Id ⟦ a ⟧ ⟦ b ⟧

Refl-tm : ∀ {A} (a : Tm Unit A) → Id-tm a a
Refl-tm a = Refl

-- SOUND: an `Id`-proof entails NbE convertibility (`nf a ≡ nf b`). (The
-- converse — conversion ⇒ `Id` — is `reifyVal`-injectivity on the two values;
-- for CODES it is `NbEPEl.faithful`, and closed convertibles get `Refl`
-- directly, as the examples show.)
-- (Eliminated via `J`/`transp`, not by matching `Refl` on the non-variable
-- value indices `⟦a⟧`/`⟦b⟧` — that split is stuck; `nf a` reduces to
-- `reifyVal ⟦a⟧` definitionally, so the result type matches.)
Id→conv : ∀ {A} {a b : Tm Unit A} → Id-tm a b → nf a ≡ nf b
Id→conv {a = a} p = transp (λ v → reifyVal ⟦ a ⟧ ≡ reifyVal v) p refl

------------------------------------------------------------------------
-- The CwF identity type: `Id` at a decoded code type `El A`.
------------------------------------------------------------------------

IdTy : (A : Code) → Tm Unit (El A) → Tm Unit (El A) → Set
IdTy A a b = Id-tm a b

------------------------------------------------------------------------
-- Examples — `Refl` inhabits exactly the convertible equations.
------------------------------------------------------------------------

-- Reflexivity on `Nat`.
_ : Id-tm {Nat} two two
_ = Refl

-- Conversion reflected as a propositional equality: `double 1` and `2` are
-- syntactically different terms but share the NbE value, so `Refl` proves them
-- equal — `Id (double 1) 2`, at type `Nat`.
_ : Id-tm {Nat} (double ⊙ one) two
_ = Refl

-- …and the same at a decoded CODE type (`El `nat = Nat`): the CwF identity type.
_ : IdTy `nat (double ⊙ one) two
_ = Refl

-- `J` computes: transporting the reflexive proof returns the point.
_ : ∀ {A} {u : Val Unit A} (C : Val Unit A → Set) (cu : C u)
  → transp C (Refl {u = u}) cu ≡ cu
_ = λ C cu → refl
