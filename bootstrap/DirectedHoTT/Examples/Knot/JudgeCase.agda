-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the `⊢` rows' shared machinery (D077):
--   * `CaseRow` — a row whose conclusion TYPE is a constructor pattern
--     with fresh variables: the fibre cases on the type (`Lib/SynPat`),
--     the case's convoy is `(Γ , term payload)` (`JudgeTmIx`);
--   * the weakenings a σ-prefix (existentials) passes its data through;
--   * a σ-bound type or term, typed.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.JudgeCase (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
import DirectedHoTT.Lib.NatCode 𝒮 𝓃 as ᴵNatCode
open ᴵNatCode using ( fromI )
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; _∷_; tag; lt-z; lt-s; []ᵈ; _∷ᵈ_; v₀; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 𝓃 ok using ( PayV )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Lib.SynFib 𝒮 𝓃 ok using ( Row )
open import DirectedHoTT.Lib.SynPat 𝒮 𝓃 ok using ( module Pat; lookSh )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf using ( rows; ⊢rows )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.JudgeTmIx 𝒮 wf
open import DirectedHoTT.Examples.Knot.JudgeFib 𝒮 wf using () renaming ( RowOK to RowOKₒ )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜TSig⌝; ⌜TSig⌝-sub; ⊢⌜TSig⌝ )
open import DirectedHoTT.Examples.Knot.Ctors 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( wk; ⊢wkS )
open ᴵNatCode using ( ⊢isuc )

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- 1. Weakenings under a σ-prefix, and their commutation.
------------------------------------------------------------------------

w1 w2 w3 : RTm Δ → RTm _
w1 x = renTm vs x
w2 x = renTm vs (renTm vs x)
w3 x = renTm vs (renTm vs (renTm vs x))

w1-sub : (σ : Sub Δ Θ) (x : RTm Δ) → subTm (extS σ) (w1 x) ≡ w1 (subTm σ x)
w1-sub σ x = wkS σ x

w2-sub : (σ : Sub Δ Θ) (x : RTm Δ) → subTm (extS (extS σ)) (w2 x) ≡ w2 (subTm σ x)
w2-sub σ x = trans (wkS (extS σ) (w1 x)) (cong w1 (wkS σ x))

w3-sub : (σ : Sub Δ Θ) (x : RTm Δ) → subTm (extS (extS (extS σ))) (w3 x) ≡ w3 (subTm σ x)
w3-sub σ x = trans (wkS (extS (extS σ)) (w2 x)) (cong w1 (w2-sub σ x))

-- σ-binders, congruent (explicit arguments: metas here cost minutes)
dσ¹-cong : (X X' : RTm Δ) (Z Z' : RTm (Δ ∙)) → X ≡ X' → Z ≡ Z' → dσ X (lam Z) ≡ dσ X' (lam Z')
dσ¹-cong X X' Z Z' refl refl = refl

dσ²-cong : (X X' : RTm Δ) (Y Y' : RTm (Δ ∙)) (Z Z' : RTm ((Δ ∙) ∙)) → X ≡ X' → Y ≡ Y' → Z ≡ Z' →
           dσ X (lam (dσ Y (lam Z))) ≡ dσ X' (lam (dσ Y' (lam Z')))
dσ²-cong X X' Y Y' Z Z' refl refl refl = refl

dσ³-cong : (X X' : RTm Δ) (Y Y' : RTm (Δ ∙)) (W W' : RTm ((Δ ∙) ∙)) (Z Z' : RTm (((Δ ∙) ∙) ∙)) →
           X ≡ X' → Y ≡ Y' → W ≡ W' → Z ≡ Z' →
           dσ X (lam (dσ Y (lam (dσ W (lam Z))))) ≡ dσ X' (lam (dσ Y' (lam (dσ W' (lam Z')))))
dσ³-cong X X' Y Y' W W' Z Z' refl refl refl refl = refl

------------------------------------------------------------------------
-- 2. A σ-bound type or term, typed; a term as its code's element.
------------------------------------------------------------------------

hereTm : {Θ : Ctx} {m : RTm ⌊ Θ ⌋} → (Θ ▹ El (⌜Tm⌝ m)) ⊢ v₀ ∷ K 1 (renTm vs m)
hereTm {Θ} {m} = ⊢conv (⊢-cast {Θ ▹ El (⌜Tm⌝ m)} {v₀} {renTy vs (El (⌜Tm⌝ m))} {El (⌜Tm⌝ (renTm vs m))}
                               (cong El (⌜Tm⌝-ren vs m)) (⊢var here))
                       (credᵀ El-⌜Tm⌝)

toTm : {Γ : Ctx} {d a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ K 1 d → Γ ⊢ a ∷ El (⌜Tm⌝ d)
toTm da = ⊢conv da (csymᵀ (credᵀ El-⌜Tm⌝))

-- the motive's context `(Γ ▹ El I) ▹ IMu (wk I) (wk D) (var 0)`, typed
⊢mc : {Ξ : Ctx} {j g I D : RTm ⌊ Ξ ⌋} → Ξ ⊢ j ∷ El ⌜Nat⌝ → Ξ ⊢ g ∷ KCtx j → Ξ ⊢ I ∷ K 1 j → Ξ ⊢ D ∷ K 1 j →
      Ξ ⊢ mc j g I D ∷ KCtx (nsuc (nsuc j))
⊢mc dj dg dI dD = ⊢cext (⊢isuc dj) (⊢cext dj dg (⊢kEl dj dI))
                        (⊢kIMu (⊢isuc dj) (⊢wkS (lt-s lt-z) dj dI) (⊢wkS (lt-s lt-z) dj dD) (⊢kvar (⊢isuc dj) (⊢fzero (fromI dj))))

------------------------------------------------------------------------
-- 3. ★ A ROW BY CASE ON THE CONCLUSION TYPE.
------------------------------------------------------------------------

-- a bare telescope (a case's row)
defRow₀ : (T : {Δ : Cx} → RTm Δ → RTm Δ → RTm Δ → RTm Δ → Tel Δ) → TelLaw T → Row
defRow₀ T law = record { R = λ q j p c → ⌜ T q j p c ⌝ᵗ ; R-sub = law }

-- term shape `sh`, the type's head `h`, the case's row `r` over `(j , q , (Γ , p))`
module CaseRow (sh : Shape) (shok : ShOK 2 sh) (h : ℕ) (r : Row) where
  open Pat KOK ⌜TSig⌝ ⌜TSig⌝-sub ⊢⌜TSig⌝ JT JT-sub ⊢JT (CI sh) (CI-sub sh) (⊢CI shok) 0 h r public

  CX : RTm Δ → RTm Δ → RTm Δ → RTm Δ → RTm Δ
  CX q j p c = CASE q j (snd c) ((fst c) ,ₚ p)

  rX : Row
  rX = record
    { R = λ q j p c → rows (CX q j p c ∷ [])
    ; R-sub = λ σ q j p c →
        trans (rows-sub' σ (CX q j p c ∷ []))
              (cong (λ X → rows (X ∷ [])) {x = subTm σ (CX q j p c)} {y = CX (subTm σ q) (subTm σ j) (subTm σ p) (subTm σ c)}
                    (CASE-sub σ q j (snd c) ((fst c) ,ₚ p))) }

  ⊢CX : RowOK 0 (lookSh KSig 0 h) r → {Ξ : Ctx} {q j p c : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜TSig⌝ → Ξ ⊢ j ∷ El ⌜Nat⌝ →
        Ξ ⊢ p ∷ PayV sh ((tag 1) ,ₚ j) (SI 2) (SD KSig) → Ξ ⊢ c ∷ El (CTat ((tag 1) ,ₚ j)) →
        Ξ ⊢ CX q j p c ∷ Desc JT
  ⊢CX rok {Ξ} {q} {j} {p} {c} dq dj dp dc =
    ⊢CASE {Ξ} {q} {j} {snd c} {pair (fst c) p} rok lt-z dq dj (⊢tyOf dc) (⊢cI sh shok dj (⊢ctxOf dc) dp)

  okX : RowOK 0 (lookSh KSig 0 h) r → RowOKₒ 1 sh rX
  okX rok {Ξ} {q} {j} {p} {c} dq dj dp dc = ⊢rows {Ξ} {JT} {1} {CX q j p c ∷ []} ⊢JT (⊢CX rok {Ξ} {q} {j} {p} {c} dq dj dp dc ∷ᵈ []ᵈ)

------------------------------------------------------------------------
-- 4. GOAL-DIRECTED σ-PREFIX TYPING: the contexts flow from the goal (a
--   pinned context restates the whole prefix at every step and compares it
--   against the goal's syntactic form — measured quadratic).
------------------------------------------------------------------------

okσJ : {Γ : Ctx} {S : RTm ⌊ Γ ⌋} {T : Tel (⌊ Γ ⌋ ∙)} → Γ ⊢ S ∷ U → TelOK (Γ ▹ El S) JT T → TelOK Γ JT (tσ S T)
okσJ {Γ} {S} {T} dS ok = ok-σ dS (subst (λ X → TelOK (Γ ▹ El S) X T) (sym (JT-ren vs)) ok)

wkN : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → (Γ ▹ B) ⊢ renTm vs t ∷ El ⌜Nat⌝
wkN {Γ} {B} {t} dt = ⊢wk {Γ} {B} {t} {El ⌜Nat⌝} dt

wkK : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {s : ℕ} {d t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ K s d → (Γ ▹ B) ⊢ renTm vs t ∷ K s (renTm vs d)
wkK {Γ} {B} {s} {d} {t} dt = ⊢wkSK {Γ = Γ} {B = B} {sg = KSig} {s = s} {d = d} {t = t} dt

wkG : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {d g : RTm ⌊ Γ ⌋} → Γ ⊢ g ∷ KCtx d → (Γ ▹ B) ⊢ renTm vs g ∷ KCtx (renTm vs d)
wkG {Γ} {B} {d} {g} dg = ⊢wkCtx {Γ} {B} {d} {g} dg
