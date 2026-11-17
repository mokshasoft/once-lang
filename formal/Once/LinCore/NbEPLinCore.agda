-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.NbEPLinCore — THE LINEAR CORE'S MEANING (plan 0.146; D403).
--
-- The core itself (its types, values and terms) is `Once.LinCore.Core`, at the
-- target's numerics alone (D440: what is compiled sees no Interpretation).
-- Here, at the pure FFI answers too: a SigOp means its contract's block
-- (`opF`/`opB`, `DenotTrace.sigOpT`), a term its computation in `T∞` (`Lᶜ`,
-- `Sem`), and a program's table the functions its bodies mean (`⟦_⟧D`).
--
-- `--safe --guardedness`, no sized types, no postulates, no holes.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import Once.LinCore.Flat
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Word using (Carrier)
import Once.Spec.Word
import Once.Spec.Float.Decimal
import Once.Spec.Numerics
open import Once.Spec.Type using (Type; b-Unit; b-Void; b-Int; b-Float; b-*; b-+; ∅ₖ)
import Once.Spec.Type as ST
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open import Once.IR.Semantics.Trace using (FFIAnswers)
import Once.IR.Semantics.Value Carrier Carrier as Val
open import Once.Denotation.DenotTrace using (sigOpT)

module Once.LinCore.NbEPLinCore (fmt : TargetNum) (ans : FFIAnswers) where

-- D440: the core's syntax and values (`Core`) take the numerics only
open import Once.LinCore.Core fmt

-- ★ B1.2: a SigOp means its contract's BLOCK (`DenotTrace.sigOpT`, as
-- `evalᴰ`'s `SigOp` clause): a pure op returns with no event, an emitting or
-- answering one calls, a halting one halts
opF : (s : Sig) → ⟦ sdom s ⟧f → T ⟦ scod s ⟧f
opF s x = fmapT (fromV (SigOpInfo.conB (info s)))
                (sigOpT fmt ans (info s) (toV (SigOpInfo.baseA (info s)) x))

-- the same, on the core's values
opB : (s : Sig) → ⟦ ⌜ sdom s ⌝ ⟧ → T ⟦ ⌜ scod s ⌝ ⟧
opB s x = fmapT (fromF (scod s)) (opF s (toF (sdom s) x))

------------------------------------------------------------------------
-- 6. ★ THE MEANING, mutual with the recursion operators (`evalᴰ`'s shape).
--
-- `cataC`/`travC` descend a shrinking `Mu`, children left to right, then the
-- algebra. ★ D406: nothing corecurses: a ν is observed by a call.
--
-- ★ D405: at the meaning `ρ` of the labels in scope. A label means a function
-- of its environment and its argument; applying a closure looks it up. The
-- recursion is structural: a body is met only when the table is built
-- (`⟦_⟧D`), over the labels before it.
------------------------------------------------------------------------
module Sem {Γ : Cx} (ρ : Env Γ) where
  mutual
    -- a term means a function of the lent value, which it does not consume, and
    -- of its input, which it does
    Lᶜ : ∀ {E A B} → Tm Γ E A B → ⟦ E ⟧ → ⟦ A ⟧ → T∞ ⟦ B ⟧
    Lᶜ lid            e         x              = return∞ x
    Lᶜ (f ∘l g)       e         x              = Lᶜ g e x >>=∞ Lᶜ f e
    Lᶜ (f ⊗l g)       e         (a , b)        = Lᶜ f e a >>=∞ λ a' → fmap∞ (a' ,_) (Lᶜ g e b)
    Lᶜ ρl             e         (a , tt)       = return∞ a
    Lᶜ ρl⁻            e         a              = return∞ (a , tt)
    Lᶜ lul            e         (tt , a)       = return∞ a
    Lᶜ lul⁻           e         a              = return∞ (tt , a)
    Lᶜ lassoc         e         ((a , b) , c)  = return∞ (a , (b , c))
    Lᶜ lassoc⁻        e         (a , (b , c))  = return∞ ((a , b) , c)
    Lᶜ lswap          e         (a , b)        = return∞ (b , a)
    Lᶜ dup            e         a              = return∞ (a , a)
    Lᶜ drop           e         a              = return∞ tt
    Lᶜ linl           e         a              = return∞ (inj₁ a)
    Lᶜ linr           e         b              = return∞ (inj₂ b)
    Lᶜ (lcase f g)    e         (inj₁ a)       = Lᶜ f e a
    Lᶜ (lcase f g)    e         (inj₂ b)       = Lᶜ g e b
    Lᶜ lzero          e         ()
    Lᶜ (lIn {F})      e         x              = return∞ (inμ (coh F (μt F) x))
    Lᶜ (lOutμ {F})    e         x              = return∞ (coh⁻¹ F (μt F) (outμ x))
    Lᶜ (lcata F alg)  e         x              = cataC F (λ y → Lᶜ alg e (coh⁻¹ F _ y)) x
    Lᶜ (lclo F {l = l} {X = X} p) e x        = return∞ (coh⁻¹ F (Ct l X) (coh F X x))
    Lᶜ (lapp {g = g} p) e       (x , a)        = up g (lookup ρ p x a)
    Lᶜ (lend b)       e         (x , a)        = fmap∞ (x ,_) (Lᶜ b (e , x) a)
    Lᶜ (blift f)      e         a              = Lᶜ f tt a
    Lᶜ (bfst f)       (e₁ , e₂) a              = Lᶜ f e₁ a
    Lᶜ (bsnd f)       (e₁ , e₂) a              = Lᶜ f e₂ a
    Lᶜ (bcaseE f g)   (inj₁ e)  a              = Lᶜ f e a
    Lᶜ (bcaseE f g)   (inj₂ e)  a              = Lᶜ g e a
    Lᶜ (bout {F} f)   e         a              = Lᶜ f (coh⁻¹ F (μt F) (outμ e)) a
    Lᶜ bcopy          e         a              = return∞ e
    Lᶜ (bapp {g = g} p) x       a              = up g (lookup ρ p x a)
    -- ★ D409 part 3: a closure means a function of its argument, its body's
    -- meaning at its grade (`Lg`) at the environment it holds; applying it is
    -- applying that function. Structural: the body is a subterm.
    Lᶜ (llam {g = g} b γ) e     x              = return∞ (λ a → Lg g b γ tt (x , a))
    Lᶜ (llamω {g = g} b γ) e    x              = return∞ (λ a → Lg g b γ x a)
    Lᶜ (lev {g = g})  e         (f , a)        = up g (f a)
    Lᶜ (bev {g = g})  f         a              = up g (f a)
    -- ★ the Spec's unfold and observation
    Lᶜ (lunf {F} {S}) e         cs             = return∞ (anaN F (cohc F S (fst cs)) (snd cs))
    Lᶜ (lout {F})     e         v              = emb (fmapT (coh⁻¹ F (Nu F)) (outν v))
    Lᶜ (lconst v)     e         _              = return∞ (lit v)
    Lᶜ (lop s)        e         x              = emb (opB s x)
    Lᶜ (liter f _)    e         a              = iter∞ (Lᶜ f e) a

    cataC : ∀ F {X : Set} → (FS F X → T∞ X) → Mu F → T∞ X
    cataC F alg (inμ w) = travC F F alg w >>=∞ alg

    travC : ∀ F G {X : Set} → (FS F X → T∞ X) → FS G (Mu F) → T∞ (FS G X)
    travC F Idf      alg y        = cataC F alg y
    travC F Kone     alg y        = return∞ y
    travC F Kzero    alg ()
    travC F (Kb _)   alg y        = return∞ y
    travC F (Kμ _)   alg y        = return∞ y
    travC F (G ⊕f H) alg (inj₁ y) = fmap∞ inj₁ (travC F G alg y)
    travC F (G ⊕f H) alg (inj₂ z) = fmap∞ inj₂ (travC F H alg z)
    travC F (G ⊗f H) alg (y , z)  = travC F G alg y >>=∞ λ u → fmap∞ (u ,_) (travC F H alg z)

    -- ★ a body at its arrow's grade: a block means a `T` (the Spec's `M act`)
    Lg : ∀ g {E A B} (t : Tm Γ E A B) → Gd g t → ⟦ E ⟧ → ⟦ A ⟧ → Mg g ⟦ B ⟧
    Lg act t φ = Lᴮ φ
    Lg eff t _ = Lᶜ t

    -- ★ A FINITE BLOCK'S MEANING, by induction on the grade judgment: the
    -- Spec's meaning at `act`, a `T`. (`Once.LinCore.Grade`: `Lᶜ t ≈ emb (Lᴮ φ)`.)
    Lᴮ : ∀ {E A B} {t : Tm Γ E A B} → Blk t → ⟦ E ⟧ → ⟦ A ⟧ → T ⟦ B ⟧
    Lᴮ k-id          e         x             = ret x
    Lᴮ (k-∘ φ ψ)     e         x             = bindT (Lᴮ ψ e x) (Lᴮ φ e)
    Lᴮ (k-⊗ φ ψ)     e         (a , b)       = bindT (Lᴮ φ e a) λ a' → fmapT (a' ,_) (Lᴮ ψ e b)
    Lᴮ k-ρ           e         (a , tt)      = ret a
    Lᴮ k-ρ⁻          e         a             = ret (a , tt)
    Lᴮ k-lul         e         (tt , a)      = ret a
    Lᴮ k-lul⁻        e         a             = ret (tt , a)
    Lᴮ k-assoc       e         ((a , b) , c) = ret (a , (b , c))
    Lᴮ k-assoc⁻      e         (a , (b , c)) = ret ((a , b) , c)
    Lᴮ k-swap        e         (a , b)       = ret (b , a)
    Lᴮ k-dup         e         a             = ret (a , a)
    Lᴮ k-drop        e         a             = ret tt
    Lᴮ k-inl         e         a             = ret (inj₁ a)
    Lᴮ k-inr         e         b             = ret (inj₂ b)
    Lᴮ (k-case φ ψ)  e         (inj₁ a)      = Lᴮ φ e a
    Lᴮ (k-case φ ψ)  e         (inj₂ b)      = Lᴮ ψ e b
    Lᴮ k-zero        e         ()
    Lᴮ (k-in {F})    e         x             = ret (inμ (coh F (μt F) x))
    Lᴮ (k-out {F})   e         x             = ret (coh⁻¹ F (μt F) (outμ x))
    Lᴮ (k-cata {F} φ) e        x             = cataB F (λ y → Lᴮ φ e (coh⁻¹ F _ y)) x
    Lᴮ (k-clo {F} {l} {X = X}) e x           = ret (coh⁻¹ F (Ct l X) (coh F X x))
    Lᴮ (k-app {p = p}) e       (x , a)       = lookup ρ p x a
    Lᴮ (k-lend φ)    e         (x , a)       = fmapT (x ,_) (Lᴮ φ (e , x) a)
    Lᴮ (k-lift φ)    e         a             = Lᴮ φ tt a
    Lᴮ (k-fst φ)     (e₁ , e₂) a             = Lᴮ φ e₁ a
    Lᴮ (k-snd φ)     (e₁ , e₂) a             = Lᴮ φ e₂ a
    Lᴮ (k-caseE φ ψ) (inj₁ e)  a             = Lᴮ φ e a
    Lᴮ (k-caseE φ ψ) (inj₂ e)  a             = Lᴮ ψ e a
    Lᴮ (k-bout {F} φ) e        a             = Lᴮ φ (coh⁻¹ F (μt F) (outμ e)) a
    Lᴮ k-copy        e         a             = ret e
    Lᴮ (k-bapp {p = p}) x      a             = lookup ρ p x a
    Lᴮ (k-lam {g} {b = b} {γ}) e x           = ret (λ a → Lg g b γ tt (x , a))
    Lᴮ (k-lamω {g} {b = b} {γ}) e x          = ret (λ a → Lg g b γ x a)
    Lᴮ k-ev          e         (f , a)       = f a
    Lᴮ k-bev         f         a             = f a
    Lᴮ (k-unf {F} {S}) e       cs            = ret (anaN F (cohc F S (fst cs)) (snd cs))
    Lᴮ (k-nout {F})  e         v             = fmapT (coh⁻¹ F (Nu F)) (outν v)
    Lᴮ (k-const {v = v}) e     _             = ret (lit v)
    Lᴮ (k-op {s})    e         x             = opB s x

    cataB : ∀ F {X : Set} → (FS F X → T X) → Mu F → T X
    cataB F alg (inμ w) = bindT (travB F F alg w) alg

    travB : ∀ F G {X : Set} → (FS F X → T X) → FS G (Mu F) → T (FS G X)
    travB F Idf      alg y        = cataB F alg y
    travB F Kone     alg y        = ret y
    travB F Kzero    alg ()
    travB F (Kb _)   alg y        = ret y
    travB F (Kμ _)   alg y        = ret y
    travB F (G ⊕f H) alg (inj₁ y) = fmapT inj₁ (travB F G alg y)
    travB F (G ⊕f H) alg (inj₂ z) = fmapT inj₂ (travB F H alg z)
    travB F (G ⊗f H) alg (y , z)  = bindT (travB F G alg y) λ u → fmapT (u ,_) (travB F H alg z)

open Sem public

------------------------------------------------------------------------
-- 7. ★ D405: THE TABLE'S MEANING, built in order: each body means a function
-- over the labels before it.
------------------------------------------------------------------------

-- what a body means, at the meaning of its prefix
⟦_⟧Bd : ∀ {Γ σ} → Body Γ σ → Env Γ → ⟦ env σ ⟧ → ⟦ dom σ ⟧ → Mg (gr σ) ⟦ cod σ ⟧
⟦ b1 {g} b γ ⟧Bd ρ x a = Lg ρ g b γ tt (x , a)
⟦ bω {g} b γ ⟧Bd ρ x a = Lg ρ g b γ x a

⟦_⟧D : ∀ {Γ} → Defs Γ → Env Γ
⟦ ε ⟧D      = ε
⟦ ds ▸ b ⟧D = ⟦ ds ⟧D ▸ ⟦ b ⟧Bd ⟦ ds ⟧D

-- applying a closure means running its label's body (by induction on the label)
lookup-look : ∀ {Γ Δ l σ} {ds : Defs Γ} {p : Γ ∋[ l ] σ} {ds′ : Defs Δ} {b : Body Δ σ}
            → Look ds p ds′ b → ∀ x a → lookup ⟦ ds ⟧D p x a ≡ ⟦ b ⟧Bd ⟦ ds′ ⟧D x a
lookup-look lk-here      x a = refl
lookup-look (lk-there q) x a = lookup-look q x a
