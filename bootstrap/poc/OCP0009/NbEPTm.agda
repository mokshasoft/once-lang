------------------------------------------------------------------------
-- OCP-0009 · Principled NbE — the fragment SYNTAX `Tm` (pure data, `--safe`)
--
-- The fragment term syntax `Tm` (`{Unit, ×, +, μ}`, no `⇒`), its embedding into
-- the bootstrap IR (`emb`), and the `Nat` term examples. This is split out of
-- `NbEP` so that the pure syntax — which uses NO unsafe features — can live in a
-- `--safe` module: downstream consumers that only manipulate `Tm` (the graded
-- QTT judgment, elaboration, …) can then be `--safe` too, without waiting on the
-- `eval`/`nf` termination proof (which needs a `TERMINATING` pragma and hence
-- keeps `NbEP` itself out of `--safe`). `NbEP` re-exports this module publicly, so
-- existing `open import … NbEP using (Tm; …)` imports are unchanged.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPTm where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC as C using ()

------------------------------------------------------------------------
-- Fragment syntax `{Unit, ×, +, μ}` (no `⇒`).
------------------------------------------------------------------------

infixr 30 _⊙_
data Tm : Ty → Ty → Set where
  idT   : ∀ {A} → Tm A A
  _⊙_   : ∀ {A B D} → Tm B D → Tm A B → Tm A D
  fstT  : ∀ {A B} → Tm (A * B) A
  sndT  : ∀ {A B} → Tm (A * B) B
  pair  : ∀ {A B D} → Tm D A → Tm D B → Tm D (A * B)
  inlT  : ∀ {A B} → Tm A (A + B)
  inrT  : ∀ {A B} → Tm B (A + B)
  case  : ∀ {A B D} → Tm A D → Tm B D → Tm (A + B) D
  termT : ∀ {A} → Tm A Unit
  InT   : ∀ {F} → Tm (⟦ F ⟧F (μ F)) (μ F)
  OutT  : ∀ {F} → Tm (μ F) (⟦ F ⟧F (μ F))
  cataT : ∀ F {A} → Tm (⟦ F ⟧F A) A → Tm (μ F) A

-- Embedding into the bootstrap IR (for the neutral carriers / reified NF).
emb : ∀ {A B} → Tm A B → C.Term A B
emb idT        = C.id
emb (f ⊙ g)    = emb f C.∘ emb g
emb fstT       = C.fst
emb sndT       = C.snd
emb (pair f g) = C.⟨ emb f , emb g ⟩
emb inlT       = C.inl
emb inrT       = C.inr
emb (case f g) = C.[ emb f , emb g ]
emb termT      = C.terminal
emb InT        = C.In
emb OutT       = C.Out
emb (cataT F a) = C.cata F (emb a)

------------------------------------------------------------------------
-- `Nat` and some closed numerals / recursors, as pure `Tm` terms.
------------------------------------------------------------------------

NatF : Func
NatF = One ⊕ Id

Nat : Ty
Nat = μ NatF

zero : Tm Unit Nat
zero = InT ⊙ inlT

suc : Tm Nat Nat
suc = InT ⊙ inrT

one two : Tm Unit Nat
one = suc ⊙ zero
two = suc ⊙ one

double : Tm Nat Nat
double = cataT NatF (case zero (suc ⊙ suc))
