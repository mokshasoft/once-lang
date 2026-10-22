-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecCore.TermR — the compiler's ground core terms as the
-- Spec's (plan 0.121, the core bridge).
--
-- The two cores have the same formers (the Spec's was transcribed from the
-- compiler's). `TmR Δ t t′`: the compiler's term `t` is the Spec's `t′`,
-- former by former, its annotations related by `TyR`. It concerns the terms
-- alone, so it is stated over the compiler's signature only; their typings
-- are related former by former.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Internal.Contract using (ISig)
import Once.Internal.Core.PolyTy as LP

module Once.Adequacy.SpecCore.TermR {Fs : ISig} {s : ℕ} (S : LP.Sig Fs s) where

open import Data.Fin using (Fin; zero; suc)

import Once.Internal.Type as LT

import Once.Spec.Type as LT
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Internal.Core.Syntax S as L
open import Once.Spec.Signature using (⌜_⌝ᵈ)
open import Once.Adequacy.SpecGrammar.Conv using (qS; πS; φS; kS)
open import Once.Adequacy.SpecCore.Type
open import Once.Adequacy.SpecCore.Schema

S′ : SC.Defs s
S′ = defsS S

------------------------------------------------------------------------
-- Literals and primitives
------------------------------------------------------------------------

open import Once.Adequacy.SpecCore.Prim S using (litS; primS)

module _ {m} {Δ : ST.KCtx m} where

  private
    ii : TyR Δ (LT.Int LT.* LT.Int) (ST.Int ST.* ST.Int)
    ii = r-* r-int r-int
    ff : TyR Δ (LT.Float LT.* LT.Float) (ST.Float ST.* ST.Float)
    ff = r-* r-float r-float
    bool : TyR Δ (LT.Unit LT.+ LT.Unit) (ST.Unit ST.+ ST.Unit)
    bool = r-+ r-unit r-unit

  primDom-R : ∀ p → TyR Δ (L.primDom p) (SC.primDom (primS p))
  primDom-R L.p-add  = ii
  primDom-R L.p-sub  = ii
  primDom-R L.p-mul  = ii
  primDom-R L.p-div  = ii
  primDom-R L.p-mod  = ii
  primDom-R L.p-neg  = r-int
  primDom-R L.p-lt   = ii
  primDom-R L.p-le   = ii
  primDom-R L.p-gt   = ii
  primDom-R L.p-ge   = ii
  primDom-R L.p-eq   = ii
  primDom-R L.p-ne   = ii
  primDom-R L.p-fadd = ff
  primDom-R L.p-fsub = ff
  primDom-R L.p-fmul = ff
  primDom-R L.p-fdiv = ff
  primDom-R L.p-i2f  = r-int

  primCod-R : ∀ p → TyR Δ (L.primCod p) (SC.primCod (primS p))
  primCod-R L.p-add  = r-int
  primCod-R L.p-sub  = r-int
  primCod-R L.p-mul  = r-int
  primCod-R L.p-div  = r-int
  primCod-R L.p-mod  = r-int
  primCod-R L.p-neg  = r-int
  primCod-R L.p-lt   = bool
  primCod-R L.p-le   = bool
  primCod-R L.p-gt   = bool
  primCod-R L.p-ge   = bool
  primCod-R L.p-eq   = bool
  primCod-R L.p-ne   = bool
  primCod-R L.p-fadd = r-float
  primCod-R L.p-fsub = r-float
  primCod-R L.p-fmul = r-float
  primCod-R L.p-fdiv = r-float
  primCod-R L.p-i2f  = r-float

------------------------------------------------------------------------
-- References to definitions
------------------------------------------------------------------------

module _ {m} {Δ : ST.KCtx m} where

  ref-type : ∀ {s′} (S₀ : LP.Sig Fs s′) (d : Fin s′) {τ τ′}
           → Clean (LP.Schema.type (S₀ LP.!! d)) → InstR {Δ = Δ} τ τ′
           → TyR Δ (LP.Schema.type (S₀ LP.!! d) LP.⟪ τ ⟫) (SC.Schema.type (defsS S₀ SC.!! d) ST.⟨ castSub S₀ d τ′ ⟩)
  ref-type (S₀ LP.▷ sc) zero    c r = TyR-inst c r
  ref-type (S₀ LP.▷ sc) (suc d) c r = ref-type S₀ d c r

  ref-respects : ∀ {s′} (S₀ : LP.Sig Fs s′) (d : Fin s′) {τ τ′}
               → LP.Respects (LP.Schema.kinds (S₀ LP.!! d)) τ → InstR {Δ = Δ} τ τ′
               → ST.Respects (SC.Schema.kinds (defsS S₀ SC.!! d)) Δ (castSub S₀ d τ′)
  ref-respects (S₀ LP.▷ sc) zero    rs r = respects-S rs r
  ref-respects (S₀ LP.▷ sc) (suc d) rs r = ref-respects S₀ d rs r

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

data TmR {m} (Δ : ST.KCtx m) : ∀ {n} → L.Tm n → SC.Tm S′ m n → Set where
  r-var    : ∀ {n} (i : Fin n) → TmR Δ (L.var i) (SC.var i)
  r-lam    : ∀ {n A A′ q π} {t : L.Tm (ℕ.suc n)} {t′}
           → TyR Δ A A′ → TmR Δ t t′ → TmR Δ (L.lam A q π t) (SC.lam A′ (qS q) (πS π) t′)
  r-app    : ∀ {n} {f x : L.Tm n} {f′ x′} → TmR Δ f f′ → TmR Δ x x′ → TmR Δ (L.app f x) (SC.app f′ x′)
  r-let    : ∀ {n q} {e : L.Tm n} {b e′ b′} → TmR Δ e e′ → TmR Δ b b′ → TmR Δ (L.let′ q e b) (SC.let′ (qS q) e′ b′)
  r-unit   : ∀ {n} → TmR Δ (L.unit {n}) SC.unit
  r-pair   : ∀ {n} {a b : L.Tm n} {a′ b′} → TmR Δ a a′ → TmR Δ b b′ → TmR Δ (L.pair a b) (SC.pair a′ b′)
  r-fst    : ∀ {n} {p : L.Tm n} {p′} → TmR Δ p p′ → TmR Δ (L.fst p) (SC.fst p′)
  r-snd    : ∀ {n} {p : L.Tm n} {p′} → TmR Δ p p′ → TmR Δ (L.snd p) (SC.snd p′)
  r-inl    : ∀ {n B B′} {a : L.Tm n} {a′} → TyR Δ B B′ → TmR Δ a a′ → TmR Δ (L.inl B a) (SC.inl B′ a′)
  r-inr    : ∀ {n A A′} {b : L.Tm n} {b′} → TyR Δ A A′ → TmR Δ b b′ → TmR Δ (L.inr A b) (SC.inr A′ b′)
  r-case   : ∀ {n qℓ qr} {e : L.Tm n} {l r e′ l′ r′} → TmR Δ e e′ → TmR Δ l l′ → TmR Δ r r′
           → TmR Δ (L.case qℓ qr e l r) (SC.case (qS qℓ) (qS qr) e′ l′ r′)
  r-absurd : ∀ {n A A′} {e : L.Tm n} {e′} → TyR Δ A A′ → TmR Δ e e′ → TmR Δ (L.absurd A e) (SC.absurd A′ e′)
  r-roll   : ∀ {n F F′} {t : L.Tm n} {t′} → FunR Δ F F′ → TmR Δ t t′ → TmR Δ (L.roll F t) (SC.roll F′ t′)
  r-fold   : ∀ {n F F′} {a t : L.Tm n} {a′ t′} → FunR Δ F F′ → TmR Δ a a′ → TmR Δ t t′
           → TmR Δ (L.fold F a t) (SC.fold F′ a′ t′)
  r-unfold : ∀ {n F F′} {c t : L.Tm n} {c′ t′} → FunR Δ F F′ → TmR Δ c c′ → TmR Δ t t′
           → TmR Δ (L.unfold F c t) (SC.unfold F′ c′ t′)
  r-out    : ∀ {n} {t : L.Tm n} {t′} → TmR Δ t t′ → TmR Δ (L.out t) (SC.out t′)
  r-iter   : ∀ {n} {f t : L.Tm n} {f′ t′} → TmR Δ f f′ → TmR Δ t t′ → TmR Δ (L.iter f t) (SC.iter f′ t′)
  r-coerce : ∀ {n A A′ B B′} {t : L.Tm n} {t′} → TyR Δ A A′ → TyR Δ B B′ → TmR Δ t t′
           → TmR Δ (L.coerce A B t) (SC.coerce A′ B′ t′)
  r-lit    : ∀ {n} l → TmR Δ (L.lit {n} l) (SC.lit (litS l))
  r-prim   : ∀ {n} p {t : L.Tm n} {t′} → TmR Δ t t′ → TmR Δ (L.prim p t) (SC.prim (primS p) t′)
  r-sigop  : ∀ {n c A t} → TyR Δ A (⌜_⌝ᵈ {m} t) → TmR Δ (L.sigop {n} c A) (SC.sigop c t)
  r-ref    : ∀ {n} (d : Fin s) {τ τ′} → InstR {Δ = Δ} τ τ′ → TmR Δ (L.ref {n} d τ) (SC.ref d (castSub S d τ′))

