-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ExprOps — plan 0.146 B1.7 (D445 at the bridge): the bridge's
-- program's ops are declared.
--
-- A term is `OK` when every op it runs (`lop`) satisfies `D`; then every op
-- its code names (`Keys.tmGot`'s `ps`) does (`ok-ps`), and a table's and a
-- program's universe's (`univ-ok`), as `LinkedCore` gives for the pass's.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.LinCore.Flat using (Base)
open import Data.Nat using (ℕ)

module Once.LinCore.ExprOps (fmt : TargetNum) (bw : Base → ℕ) where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here)

open import Once.LinCore.Core fmt
open import Once.LinCore.Keys fmt bw using (ps; tmGot; defsGot; ops; univ)

module _ (D : Sig → Set) where

  -- every op a term runs satisfies `D`
  OK : ∀ {Γ E A B} → Tm Γ E A B → Set
  OK (f ∘l g)     = OK f × OK g
  OK (f ⊗l g)     = OK f × OK g
  OK (lcase f g)  = OK f × OK g
  OK (lcata F alg) = OK alg
  OK (liter f φ)  = OK f
  OK (lend b)     = OK b
  OK (blift f)    = OK f
  OK (bfst f)     = OK f
  OK (bsnd f)     = OK f
  OK (bcaseE f g) = OK f × OK g
  OK (bout f)     = OK f
  OK (llam b γ)   = OK b
  OK (llamω b γ)  = OK b
  OK (lop s)      = D s
  {-# CATCHALL #-}
  OK _            = ⊤

  private
    either : ∀ {s : Sig} xs {ys} → s ∈ xs ++ ys → (s ∈ xs → D s) → (s ∈ ys → D s) → D s
    either xs m l r = go (∈-++⁻ xs m)
      where
        go : _ → _
        go (inj₁ a) = l a
        go (inj₂ b) = r b

  -- ★ the ops a term's code names satisfy `D`
  ok-ps : ∀ {Γ} (ds : Defs Γ) {E A B} (t : Tm Γ E A B) → OK t → ∀ {s} → s ∈ ps (tmGot ds t) → D s
  ok-ps ds (f ∘l g)      (of , og) m = either (ps (tmGot ds f)) m (ok-ps ds f of) (ok-ps ds g og)
  ok-ps ds (f ⊗l g)      (of , og) m = either (ps (tmGot ds f)) m (ok-ps ds f of) (ok-ps ds g og)
  ok-ps ds (lcase f g)   (of , og) m = either (ps (tmGot ds f)) m (ok-ps ds f of) (ok-ps ds g og)
  ok-ps ds (lcata F alg) o         m = ok-ps ds alg o m
  ok-ps ds (liter f φ)   o         m = ok-ps ds f o m
  ok-ps ds (lend b)      o         m = ok-ps ds b o m
  ok-ps ds (blift f)     o         m = ok-ps ds f o m
  ok-ps ds (bfst f)      o         m = ok-ps ds f o m
  ok-ps ds (bsnd f)      o         m = ok-ps ds f o m
  ok-ps ds (bcaseE f g)  (of , og) m = either (ps (tmGot ds f)) m (ok-ps ds f of) (ok-ps ds g og)
  ok-ps ds (bout f)      o         m = ok-ps ds f o m
  ok-ps ds (llam b γ)    o         m = ok-ps ds b o m
  ok-ps ds (llamω b γ)   o         m = ok-ps ds b o m
  ok-ps ds (lop s)       o (here refl) = o
  ok-ps ds lid       o ()
  ok-ps ds ρl        o ()
  ok-ps ds ρl⁻       o ()
  ok-ps ds lul       o ()
  ok-ps ds lul⁻      o ()
  ok-ps ds lassoc    o ()
  ok-ps ds lassoc⁻   o ()
  ok-ps ds lswap     o ()
  ok-ps ds dup       o ()
  ok-ps ds drop      o ()
  ok-ps ds linl      o ()
  ok-ps ds linr      o ()
  ok-ps ds lzero     o ()
  ok-ps ds lIn       o ()
  ok-ps ds lOutμ     o ()
  ok-ps ds (lclo F p) o ()
  ok-ps ds (lapp p)  o ()
  ok-ps ds bcopy     o ()
  ok-ps ds (bapp p)  o ()
  ok-ps ds lev       o ()
  ok-ps ds bev       o ()
  ok-ps ds lunf      o ()
  ok-ps ds lout      o ()
  ok-ps ds (lconst v) o ()

  -- a table each of whose bodies is OK
  data DefsOK : ∀ {Γ} → Defs Γ → Set where
    ε   : DefsOK ε
    _▸₁_ : ∀ {Γ g X A B} {ds : Defs Γ} {b : LTm Γ (X ⊗t A) B} {γ : Gd g b} → DefsOK ds → OK b → DefsOK (ds ▸ b1 b γ)
    _▸ω_ : ∀ {Γ g X A B} {ds : Defs Γ} {b : Tm Γ X A B} {γ : Gd g b} → DefsOK ds → OK b → DefsOK (ds ▸ bω b γ)

  defs-ok : ∀ {Γ} (ds : Defs Γ) → DefsOK ds → ∀ {s} → s ∈ ps (defsGot ds) → D s
  defs-ok ε ε ()
  defs-ok (ds ▸ b1 b γ) (od ▸₁ ob) m = either (ps (defsGot ds)) m (defs-ok ds od) (ok-ps ds b ob)
  defs-ok (ds ▸ bω b γ) (od ▸ω ob) m = either (ps (defsGot ds)) m (defs-ok ds od) (ok-ps ds b ob)

  -- ★ a program's universe's ops
  univ-ok : ∀ {Γ} (ds : Defs Γ) {E A B} (f : Tm Γ E A B) → DefsOK ds → OK f → ∀ {s} → s ∈ ops (univ ds f) → D s
  univ-ok ds f od of m = either (ps (defsGot ds)) m (defs-ok ds od) (ok-ps ds f of)

------------------------------------------------------------------------
-- 2. ★ THE BRIDGE'S OPS are its IR's SigOp leaves (and the halting
-- `unlinked`, which owes nothing): a linked expression's bridge is OK.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (subst; subst₂)
open import Once.Contract using (ISig)
open import Once.Denotation.Program using (Declared; Leaves)
open import Once.SigOp.Info using (SigOpInfo)
import Once.IR as M
open import Once.IRTy using (IRTy)
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_; _⊑ᵘ_; _⊑∷_)
open import Once.Context using (z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
import Once.Spec.Grade as G
import Data.Fin
open import Once.LinCore.FromExpr fmt
  using (weak; split; carryL; mixL; var-at; bindL; apω; dist; cast)
open import Once.LinCore.PassTr fmt using (copyIn)

module Ops (Σι : ISig) where
  Dc : Sig → Set
  Dc s = Declared Σι (info s)

  ok-cast : ∀ {L E A A′ B B′} (p : A ≡ A′) (q : B ≡ B′) {t : Tm L E A B} → OK Dc t → OK Dc (cast p q t)
  ok-cast refl refl o = o

  ok-weak : ∀ {L E m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′) → OK Dc (weak {L} {E} {Γ = Γ} p)
  ok-weak {Γ = SC.∅}       []         = tt
  ok-weak {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) = ok-weak {Γ = Γ} p
  ok-weak {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) = tt , (ok-weak {Γ = Γ} p , tt)
  ok-weak {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) = tt , (ok-weak {Γ = Γ} p , tt)
  ok-weak {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) = ok-weak {Γ = Γ} p , tt
  ok-weak {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) = ok-weak {Γ = Γ} p , tt
  ok-weak {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) = ok-weak {Γ = Γ} p , tt

  ok-split : ∀ {L E m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) → OK Dc (split {L} {E} Γ Ψ₁ Ψ₂)
  ok-split SC.∅          []          []          = tt
  ok-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) = ok-split Γ Ψ₁ Ψ₂
  ok-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) = tt , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) = tt , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)

  ok-var : ∀ {L E m n} {Γ : Ctx m n} (i : Data.Fin.Fin n) → OK Dc (var-at {L} {E} {Γ = Γ} i)
  ok-var {Γ = Γ SC.▸ A} Data.Fin.zero    = _
  ok-var {Γ = Γ SC.▸ A} (Data.Fin.suc i) = ok-var {Γ = Γ} i

  ok-bind : ∀ {L E m n} {Γ : Ctx m n} {Ψ : Usage n} {A} (q : G.Quantity) → OK Dc (bindL {L} {E} {Γ = Γ} {Ψ} {A} q)
  ok-bind G.Zero = _
  ok-bind G.One  = tt
  ok-bind G.Many = tt
