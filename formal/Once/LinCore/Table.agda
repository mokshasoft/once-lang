-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Table — plan 0.146 B1.3: the table's two meanings.
--
-- ★ `env-ok`: the translated table (`FromIR.trTable`), its labels meaning
-- `Pass.⟦_⟧P`, against master's `tableCalls`: a resolved call is related to
-- master's (the entry's body by `BridgeProof.bridge`, over the entries before
-- it), and an unresolved one is master's `unlinkedT`. By induction on the
-- table, each entry deciding a name and its two objects as both lookups do.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
import Data.Maybe
open import Relation.Nullary using (Dec; yes; no)
open import Once.Denotation.Program using (tableEnv-at)
open import Once.IR.Semantics.Trace using (unlinkedT)
open import Once.IR.Semantics.Iterative using (embed)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.IRTy using (IRTy; _≟IRTy_)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.Denotation.Program using (IRFun; module IRFun; tableCalls)
open import Once.Denotation.DenotTrace using (evalᴰ; callEnv)
open IRFun using (fname; fdom; fcod; fbody)
import Once.LinCore.FromIR
import Once.LinCore.Bridge
import Once.LinCore.BridgeProof
import Once.LinCore.Casts
import Once.LinCore.Bisim

module Once.LinCore.Table (fmt : TargetNum) (ans : FFIAnswers) where

open import Once.LinCore.NbEPLinCore fmt ans
open Once.LinCore.FromIR fmt ans
open Once.LinCore.Bridge fmt ans using (W)
module BP = Once.LinCore.BridgeProof fmt ans
open Once.LinCore.Casts fmt ans using (casts)
open Once.LinCore.Bisim fmt ans using (_≈[_]_; ≈-≈R; ≈-sym)
open TrProg using (prog; rs)

private
  bind-just : ∀ {X Y : Set} {m : Maybe X} {k : X → Maybe Y} {y} → (m >>= k) ≡ just y
            → Σ X (λ x → m ≡ just x × k x ≡ just y)
  bind-just {m = just x} e = x , refl , e

  map-nothing : ∀ {X Y : Set} {f : X → Y} (m : Maybe X) → Data.Maybe.map f m ≡ nothing → m ≡ nothing
  map-nothing nothing refl = refl

-- the entry's body, at its grade, against master's
body≈ : ∀ {Γ} (P : P.Prog Γ) (rs : Resolver Γ) (es : List IRFun)
        (ok : BP.EnvOK P.⟦ P ⟧P (tableCalls fmt ans es) rs)
        (e : IRFun) {b : P.IR Γ ⟪ fdom e ⟫ ⟪ fcod e ⟫} → Tr rs (fbody e) b
      → ∀ g (γ : P.GdIR Γ g b) {a a′} → W (fdom e) a a′
      → up g (P.evG P.⟦ P ⟧P g b γ a) ≈[ W (fcod e) ] evalᴰ fmt (callEnv (tableCalls fmt ans es) ans) (fbody e) a′
body≈ P rs es ok e t act γ {a} w =
  ≈-≈R (≈-sym (P.ev-coh P.⟦ P ⟧P γ a)) (BP.bridge P.⟦ P ⟧P (tableCalls fmt ans es) (casts P.⟦ P ⟧P (tableCalls fmt ans es)) ok t w)
body≈ P rs es ok e t eff γ w = BP.bridge P.⟦ P ⟧P (tableCalls fmt ans es) (casts P.⟦ P ⟧P (tableCalls fmt ans es)) ok t w

-- ★ one more entry: its label against master's lookup at it
module _ {Γ} (P : P.Prog Γ) (rs : Resolver Γ) (es : List IRFun)
         (ok : BP.EnvOK P.⟦ P ⟧P (tableCalls fmt ans es) rs)
         (e : IRFun) {b : P.IR Γ ⟪ fdom e ⟫ ⟪ fcod e ⟫} (t : Tr rs (fbody e) b) (g : Gr) (γ : P.GdIR Γ g b) where

  private
    δ′ : Env (Γ ▸ sg once g One ⟪ fdom e ⟫ ⟪ fcod e ⟫)
    δ′ = P.⟦ P P.▹ b ∣ γ ⟧P

    weak-hit : ∀ {f A B g′ l} {p′ : (Γ ▸ sg once g One ⟪ fdom e ⟫ ⟪ fcod e ⟫) ∋[ l ] sg once g′ One ⟪ A ⟫ ⟪ B ⟫}
             → Data.Maybe.map weaken (rs f A B) ≡ just (hit g′ p′) → ∀ {a a′} → W A a a′
             → up g′ (lookup δ′ p′ tt a) ≈[ W B ] tableCalls fmt ans es f A B a′
    weak-hit {f} {A} {B} eq w with rs f A B in eq₀
    weak-hit refl w | just (hit g₀ p₀) = BP.EnvOK.hit≈ ok eq₀ w

    hit-yes : ∀ {f A B g′ l} {p′ : (Γ ▸ sg once g One ⟪ fdom e ⟫ ⟪ fcod e ⟫) ∋[ l ] sg once g′ One ⟪ A ⟫ ⟪ B ⟫}
              (n : fname e ≡ f) (p : fdom e ≡ A) (q : fcod e ≡ B)
            → extend-at g rs e f A B (yes n) (yes p) (yes q) ≡ just (hit g′ p′) → ∀ {a a′} → W A a a′
            → up g′ (lookup δ′ p′ tt a) ≈[ W B ] tableEnv-at fmt ans e es f A B (yes n) (yes p) (yes q) a′
    hit-yes n refl refl refl w = body≈ P rs es ok e t g γ w

    miss-yes : ∀ {f A B} (n : fname e ≡ f) (p : fdom e ≡ A) (q : fcod e ≡ B)
             → extend-at g rs e f A B (yes n) (yes p) (yes q) ≡ nothing → ⊥
    miss-yes n refl refl ()

    hit-at : ∀ {f A B g′ l} {p′ : (Γ ▸ sg once g One ⟪ fdom e ⟫ ⟪ fcod e ⟫) ∋[ l ] sg once g′ One ⟪ A ⟫ ⟪ B ⟫}
             (d₁ : Dec (fname e ≡ f)) (d₂ : Dec (fdom e ≡ A)) (d₃ : Dec (fcod e ≡ B))
           → extend-at g rs e f A B d₁ d₂ d₃ ≡ just (hit g′ p′) → ∀ {a a′} → W A a a′
           → up g′ (lookup δ′ p′ tt a) ≈[ W B ] tableEnv-at fmt ans e es f A B d₁ d₂ d₃ a′
    hit-at (yes n) (yes p)    (yes q)    eq   w = hit-yes n p q eq w
    hit-at (yes _) (yes _)    (no _)     eq   w = weak-hit eq w
    hit-at (yes _) (no _)     _          eq   w = weak-hit eq w
    hit-at (no _)  _          _          eq   w = weak-hit eq w

    miss-at : ∀ {f A B} (d₁ : Dec (fname e ≡ f)) (d₂ : Dec (fdom e ≡ A)) (d₃ : Dec (fcod e ≡ B))
            → extend-at g rs e f A B d₁ d₂ d₃ ≡ nothing → ∀ a′ → tableEnv-at fmt ans e es f A B d₁ d₂ d₃ a′ ≡ embed unlinkedT
    miss-at (yes n) (yes p) (yes q) eq a′ = ⊥-elim (miss-yes n p q eq)
    miss-at {f} {A} {B} (yes _) (yes _) (no _) eq a′ = BP.EnvOK.miss≡ ok (map-nothing (rs f A B) eq) a′
    miss-at {f} {A} {B} (yes _) (no _)  _      eq a′ = BP.EnvOK.miss≡ ok (map-nothing (rs f A B) eq) a′
    miss-at {f} {A} {B} (no _)  _       _      eq a′ = BP.EnvOK.miss≡ ok (map-nothing (rs f A B) eq) a′

  entry-ok : BP.EnvOK δ′ (tableCalls fmt ans (e ∷ es)) (extend g rs e)
  entry-ok = record
    { hit≈  = λ {f} {A} {B} eq w → hit-at (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) eq w
    ; miss≡ = λ {f} {A} {B} eq a′ → miss-at (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) eq a′
    }

-- ★ THE TABLE: its translation's labels against master's lookup
EnvOKT : TrProg → List IRFun → Set
EnvOKT t tbl = BP.EnvOK P.⟦ prog t ⟧P (tableCalls fmt ans tbl) (rs t)

env-ok : ∀ (tbl : List IRFun) {t} → trTable tbl ≡ just t → EnvOKT t tbl
env-ok [] refl = record { hit≈ = λ () ; miss≡ = λ _ _ → refl }
env-ok (e ∷ es) eq with bind-just {m = trTable es} eq
... | t , et , e₁ with bind-just {m = trI (rs t) (fbody e)} e₁
... | b , eb , refl = at (blk? b)
  where
  ok = env-ok es et
  tr = trI-Tr (rs t) (fbody e) eb
  at : (m : Maybe (P.BlkIR _ b)) → EnvOKT (entry-at (prog t) (rs t) e b m) (e ∷ es)
  at (just φ) = entry-ok (prog t) (rs t) es ok e tr act φ
  at nothing  = entry-ok (prog t) (rs t) es ok e tr eff tt
