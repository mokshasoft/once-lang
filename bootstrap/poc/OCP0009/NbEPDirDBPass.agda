------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 19 — PASS STABILITY: an optimizer pass survives
--                            substitution, via the de Bruijn `Id-sub`
--
-- Connects `NbEPDirPass` (an optimizer pass IS an inhabitant of the directed
-- `Id`) with `NbEPDirDB`'s key lemma (substitution commutes with reduction).
-- Over genuine variables, a pass can act in an OPEN context — mentioning free
-- variables — and the payoff of `Id-sub` is:
--
--     pass-stable : Pass s t → Pass (sub σ s) (sub σ t)         ( = Id-sub)
--
-- i.e. an optimization proven ONCE on an open term holds in EVERY instance
-- obtained by substituting its free variables. This is the compiler-relevant
-- consequence of subst-commutes-with-reduction: optimizations are stable under
-- INSTANTIATION / inlining of their context — you prove the rewrite generically
-- and it survives specialization. β-reduction here IS the pass (function
-- inlining); `Id-sub` carries it across the substitution.
--
-- `--safe`, ZERO axioms (`Id-sub` is the funext-free lemma of `NbEPDirDB`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBPass where

open import poc.OCP0009.NbEPDirDB
  using ( Ty; ι; _⇒_; Con; ∅; _,_; _∋_; vz; _⊢_; var; lam; app
        ; Sub; sub; sub1; _⟶*_; done; step; β; Id; Id-sub )

private
  variable
    Γ Δ : Con
    A : Ty

------------------------------------------------------------------------
-- A pass is an inhabitant of the directed identity type (as in `NbEPDirPass`,
-- now over de Bruijn terms).
------------------------------------------------------------------------

Pass : Γ ⊢ A → Γ ⊢ A → Set
Pass s t = Id s t

-- THE CONNECTION: a pass is stable under substitution — precisely `Id-sub`
-- (= subst-commutes-with-reduction). Optimizations survive instantiation.
pass-stable : (σ : Sub Γ Δ) {s t : Γ ⊢ A} → Pass s t → Pass (sub σ s) (sub σ t)
pass-stable σ = Id-sub σ

------------------------------------------------------------------------
-- Concrete: an inlining pass on an OPEN term, then a closed instance for free.
------------------------------------------------------------------------

-- An open program with one free variable `g : ι ⇒ ι`: the identity combinator
-- applied to `g` — a β-redex (an inlined call). β optimizes it to `g`.
open-redex : (∅ , (ι ⇒ ι)) ⊢ (ι ⇒ ι)
open-redex = app (lam (var vz)) (var vz)

pass-open : Pass open-redex (var vz)
pass-open = step (β (var vz) (var vz)) done

-- The closed identity function, and the substitution instantiating `g` with it.
idfn : ∅ ⊢ (ι ⇒ ι)
idfn = lam (var vz)

inst : Sub (∅ , (ι ⇒ ι)) ∅
inst = sub1 idfn

-- The pass SURVIVES instantiation: the same optimization, on the fully-closed
-- instance `app (lam (var vz)) idfn ⟶* idfn`, obtained for FREE from the open
-- pass by `pass-stable` — no re-proving. This is why subst-commutes-with-
-- reduction is the right kernel lemma for an optimizer: rewrites specialize.
pass-closed : Pass (sub inst open-redex) idfn
pass-closed = pass-stable inst pass-open
