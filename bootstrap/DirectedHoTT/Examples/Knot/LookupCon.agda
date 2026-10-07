-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ `Γ ∋ x ∷ A`: THE FIBRE COMPUTES, and the two
-- constructors.
--
-- The fibre function (`Knot/Lookup.D∋`) is a case on the context, then on
-- the variable.  At a canonical index it computes to the one row:
--
--     app D∋ (suc m , Γ' ▹ A' , fzero  , A) ⟶* [ here  row ]
--     app D∋ (suc m , Γ' ▹ A' , fsuc y , A) ⟶* [ there row ]
--
-- (the variable's case is the kernel's `fcase`: one `fcase-z`/`fcase-s`)
--
-- The chains are built at VARIABLES, where the substitution algebra
-- computes, and moved to any terms by `⟶*-sub`.  The closed pieces (the
-- methods, the descriptions) never reduce under a substitution: each one's
-- closedness is a structural lemma, cast once
-- (`knot-description-normalisation-trap`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.LookupCon (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: over a well-formed signature, at all its names
private
  𝓃 = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 𝓃 wf
  refs = Entries.refsOK 𝒮 𝓃 (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 𝓃 hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 𝓃 using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.RedCong 𝒮
open import DirectedHoTT.Lib.Sugar 𝒮 𝓃 ok using ( Cons; []; _∷_; conₗ; tag; selF; selF-sub; Dσ-sub; ⊢selF; selF-β; subC; nth-z; nth-s; lt-z; ⊢tag; ⊢pay-σ; ⊢con-fib; []ᵈ; _∷ᵈ_; v₀; v₁; v₂; v₃; v₄; v₅; _,ₚ_ )
open import DirectedHoTT.Lib.Tel 𝒮 𝓃 ok
open import DirectedHoTT.Lib.MethAt 𝒮 𝓃 ok
open import DirectedHoTT.Lib.NatFib 𝒮 𝓃 ok
open import DirectedHoTT.Lib.NatCode 𝒮 𝓃
open import DirectedHoTT.Lib.Syn 𝒮 𝓃 ok
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf
open import DirectedHoTT.Examples.Knot.Ren 𝒮 wf using ( wk; wk-sub; ⊢wkS )
open import DirectedHoTT.Examples.Knot.Lookup 𝒮 wf
open import DirectedHoTT.Lib.SynFib 𝒮 𝓃 ok using ( ⊢conRow )

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- 1. ★ CLOSEDNESS of the fibre function's pieces.
------------------------------------------------------------------------

rows-sub : {c : ℕ} (τ : Sub Δ Θ) (Cs : Cons Δ c) → subTm τ (rows Cs) ≡ rows (subC τ Cs)
rows-sub τ Cs = Dσ-sub τ Cs

hereT-sub : (σ : Sub Δ Θ) (m a' a : RTm Δ) →
            subTm σ ⌜ hereT m a' a ⌝ᵗ ≡ ⌜ hereT (subTm σ m) (subTm σ a') (subTm σ a) ⌝ᵗ
hereT-sub σ m a' a =
  cong₂ (λ X W → dσ (⌜Id⌝ X (subTm σ a) W) (lam dι)) (⌜Ty⌝-sub σ (nsuc m)) (wk-sub σ 0 m a')

thereT-sub : (σ : Sub Δ Θ) (m g y a : RTm Δ) →
             subTm σ ⌜ thereT m g y a ⌝ᵗ ≡ ⌜ thereT (subTm σ m) (subTm σ g) (subTm σ y) (subTm σ a) ⌝ᵗ
thereT-sub σ m g y a =
  cong₂ (λ X Y → dσ X (lam Y)) (⌜Ty⌝-sub σ m)
    (cong₂ dρ (cong₃ (λ u w z → ix∋ u w z v₀) (wkS σ m) (wkS σ g) (wkS σ y))
              (cong (λ Z → dσ Z (lam dι))
                    (cong₃ ⌜Id⌝ (trans (⌜Ty⌝-sub σ' (nsuc (renTm vs m)))
                                       (cong (λ z → ⌜Ty⌝ (nsuc z)) {x = subTm σ' (renTm vs m)} {y = renTm vs (subTm σ m)} (wkS σ m)))
                                (wkS σ a)
                                (trans (wk-sub σ' 0 (renTm vs m) v₀)
                                       (cong (λ z → wk 0 z v₀) {x = subTm σ' (renTm vs m)} {y = renTm vs (subTm σ m)} (wkS σ m))))))
  where σ' = extS σ

private
  lam4 : RTm ((((Θ ∙) ∙) ∙) ∙) → RTm Θ
  lam4 b = lam (lam (lam (lam b)))

-- a one-row fibre under a substitution
hr-sub : (τ : Sub Δ Θ) (m a' a : RTm Δ) →
         subTm τ (rows (⌜ hereT m a' a ⌝ᵗ ∷ [])) ≡ rows (⌜ hereT (subTm τ m) (subTm τ a') (subTm τ a) ⌝ᵗ ∷ [])
hr-sub τ m a' a =
  trans {x = subTm τ (rows (⌜ hereT m a' a ⌝ᵗ ∷ []))} {y = rows (subTm τ ⌜ hereT m a' a ⌝ᵗ ∷ [])}
        {z = rows (⌜ hereT (subTm τ m) (subTm τ a') (subTm τ a) ⌝ᵗ ∷ [])}
        (rows-sub τ (⌜ hereT m a' a ⌝ᵗ ∷ []))
        (cong (λ C → rows (C ∷ [])) {x = subTm τ ⌜ hereT m a' a ⌝ᵗ} {y = ⌜ hereT (subTm τ m) (subTm τ a') (subTm τ a) ⌝ᵗ}
              (hereT-sub τ m a' a))

tr-sub : (τ : Sub Δ Θ) (m g y a : RTm Δ) →
         subTm τ (rows (⌜ thereT m g y a ⌝ᵗ ∷ [])) ≡ rows (⌜ thereT (subTm τ m) (subTm τ g) (subTm τ y) (subTm τ a) ⌝ᵗ ∷ [])
tr-sub τ m g y a =
  trans {x = subTm τ (rows (⌜ thereT m g y a ⌝ᵗ ∷ []))} {y = rows (subTm τ ⌜ thereT m g y a ⌝ᵗ ∷ [])}
        {z = rows (⌜ thereT (subTm τ m) (subTm τ g) (subTm τ y) (subTm τ a) ⌝ᵗ ∷ [])}
        (rows-sub τ (⌜ thereT m g y a ⌝ᵗ ∷ []))
        (cong (λ C → rows (C ∷ [])) {x = subTm τ ⌜ thereT m g y a ⌝ᵗ}
              {y = ⌜ thereT (subTm τ m) (subTm τ g) (subTm τ y) (subTm τ a) ⌝ᵗ}
              (thereT-sub τ m g y a))

W1 W2 W3 W4 W5 : {Γ : Cx} → RTm Γ → RTm _
W1 t = renTm vs t
W2 t = renTm vs (W1 t)
W3 t = renTm vs (W2 t)
W4 t = renTm vs (W3 t)
W5 t = renTm vs (W4 t)

-- the variable method's rows
HR : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
HR M A' A = rows (⌜ hereT M A' A ⌝ᵗ ∷ [])
TR : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
TR M G Y A = rows (⌜ thereT M G Y A ⌝ᵗ ∷ [])

-- the context method's body, every position a parameter: the payload's
--   components bound by λ (A' then Γ'), then the case on the variable
FBx : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm ((Γ ∙) ∙)
FBx M X A = fcase (W2 X) (HR (W2 M) v₁ (W2 A)) (TR (W3 M) v₁ v₀ (W3 A))

GBx : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
GBx M P X A = app (app (lam (lam (FBx M X A))) (fst (snd P))) (fst P)

private
  w2s : (σ : Sub Δ Θ) (t : RTm Δ) → subTm (extS (extS σ)) (W2 t) ≡ W2 (subTm σ t)
  w2s σ t = trans (wkS (extS σ) (W1 t)) (cong W1 (wkS σ t))
  w3s : (σ : Sub Δ Θ) (t : RTm Δ) → subTm (extS (extS (extS σ))) (W3 t) ≡ W3 (subTm σ t)
  w3s σ t = trans (wkS (extS (extS σ)) (W2 t)) (cong W1 (w2s σ t))

FBx-sub : (σ : Sub Δ Θ) (M X A : RTm Δ) → subTm (extS (extS σ)) (FBx M X A) ≡ FBx (subTm σ M) (subTm σ X) (subTm σ A)
FBx-sub σ M X A =
  cong₃ fcase (w2s σ X)
        (trans (hr-sub (extS (extS σ)) (W2 M) v₁ (W2 A)) (cong₂ (λ u w → HR u v₁ w) (w2s σ M) (w2s σ A)))
        (trans (tr-sub (extS (extS (extS σ))) (W3 M) v₁ v₀ (W3 A)) (cong₂ (λ u w → TR u v₁ v₀ w) (w3s σ M) (w3s σ A)))

GBx-sub : (σ : Sub Δ Θ) (M P X A : RTm Δ) → subTm σ (GBx M P X A) ≡ GBx (subTm σ M) (subTm σ P) (subTm σ X) (subTm σ A)
GBx-sub σ M P X A = cong (λ F → app (app (lam (lam F)) (fst (snd (subTm σ P)))) (fst (subTm σ P))) (FBx-sub σ M X A)

gs-sub : (σ : Sub Δ Θ) → subTm (extS σ) (gs {Δ}) ≡ gs {Θ}
gs-sub σ = cong lam4 (GBx-sub (extS (extS (extS (extS (extS σ))))) v₄ v₃ v₁ v₀)

gz-sub : (σ : Sub Δ Θ) → subTm σ (gz {Δ}) ≡ gz {Θ}
gz-sub σ = refl

gM-sub : (σ : Sub Δ Θ) → subTm σ (gM {Δ}) ≡ gM {Θ}
gM-sub {Δ} {Θ} σ =
  trans {x = subTm σ (gM {Δ})} {y = methN (subTm σ (methAt (gz ∷ []))) (subTm (extS σ) (methAt (gs ∷ [])))} {z = gM {Θ}}
    (methN-sub σ (methAt (gz ∷ [])) (methAt (gs ∷ [])))
    (cong₂ methN {x = subTm σ (methAt (gz ∷ []))} {x' = methAt (gz ∷ [])}
                 {y = subTm (extS σ) (methAt (gs ∷ []))} {y' = methAt (gs ∷ [])}
           (trans {x = subTm σ (methAt (gz ∷ []))} {y = methAt (subC σ (gz ∷ []))} {z = methAt (gz ∷ [])}
                  (methAt-sub σ (gz ∷ [])) (cong methAt {x = subC σ (gz ∷ [])} {y = gz ∷ []} (cong₂ _∷_ (gz-sub σ) refl)))
           (trans {x = subTm (extS σ) (methAt (gs ∷ []))} {y = methAt (subC (extS σ) (gs ∷ []))} {z = methAt (gs ∷ [])}
                  (methAt-sub (extS σ) (gs ∷ [])) (cong methAt {x = subC (extS σ) (gs ∷ [])} {y = gs ∷ []} (cong₂ _∷_ (gs-sub σ) refl))))

D∋-sub : (σ : Sub Δ Θ) → subTm σ (D∋ {Δ}) ≡ D∋ {Θ}
D∋-sub {Δ} {Θ} σ =
  cong lam (cong₂ (λ D G → app (app (ielim D (fst v₀) G (fst (snd v₀))) (fst (snd (snd v₀))))
                              (snd (snd (snd v₀))))
                  {x = subTm (extS σ) (CtxD {Δ ∙})} {x' = CtxD} {y = subTm (extS σ) (gM {Δ ∙})} {y' = gM}
                  (CtxD-sub (extS σ)) (gM-sub (extS σ)))

-- ★ the index's projections, generic in every component AND in the method
--   (so nothing can unfold)
projChain : {Γ : Cx} (d gc x a G : RTm Γ) →
  app (app (ielim CtxD (fst (ix∋ d gc x a)) G (fst (snd (ix∋ d gc x a)))) (fst (snd (snd (ix∋ d gc x a)))))
      (snd (snd (snd (ix∋ d gc x a))))
  ⟶* app (app (ielim CtxD d G gc) x) a
projChain d gc x a G =
  ⟶*-trans {t = app (app E1 (fst (snd (snd i)))) (snd (snd (snd i)))} {u = app (app E3 (fst (snd (snd i)))) (snd (snd (snd i)))}
           {v = app (app E3 x) a}
    (⟶*-appˡ (⟶*-appˡ (⟶*-trans {t = E1} {u = E2} {v = E3} (⟶*-ielimⁱ pD) (⟶*-ielimᵗ pG))))
    (⟶*-trans {t = app (app E3 (fst (snd (snd i)))) (snd (snd (snd i)))} {u = app (app E3 x) (snd (snd (snd i)))}
              {v = app (app E3 x) a}
       (⟶*-appˡ (⟶*-appʳ pX)) (⟶*-appʳ pA))
  where
    r2 = pair x a
    r = pair gc r2
    i = pair d r
    E1 = ielim CtxD (fst i) G (fst (snd i))
    E2 = ielim CtxD d G (fst (snd i))
    E3 = ielim CtxD d G gc
    pD : fst i ⟶* d
    pD = step (βfst d r) done
    pG : fst (snd i) ⟶* gc
    pG = ⟶*-trans {t = fst (snd i)} {u = fst r} {v = gc} (⟶*-fst (step (βsnd d r) done)) (step (βfst gc r2) done)
    pX : fst (snd (snd i)) ⟶* x
    pX = ⟶*-trans {t = fst (snd (snd i))} {u = fst r2} {v = x}
           (⟶*-fst (⟶*-trans {t = snd (snd i)} {u = snd r} {v = r2} (⟶*-snd (step (βsnd d r) done)) (step (βsnd gc r2) done)))
           (step (βfst x a) done)
    pA : snd (snd (snd i)) ⟶* a
    pA = ⟶*-trans {t = snd (snd (snd i))} {u = snd r2} {v = a}
           (⟶*-snd (⟶*-trans {t = snd (snd i)} {u = snd r} {v = r2} (⟶*-snd (step (βsnd d r) done)) (step (βsnd gc r2) done)))
           (step (βsnd x a) done)

-- ★ one β, then a cast to the CLEAN reduct: the substitution never nests
--   (a tower of nested substitutions was the measured cost: 172k `subTm`
--   conversion checks, `tools/agda-profile.sh`)
βcast : {Γ : Cx} (t : RTm (Γ ∙)) (u v : RTm Γ) → subTm (single u) t ≡ v → app (lam t) u ⟶* v
βcast t u v e = step (β t u) (subst (λ z → z ⟶* v) (sym e) done)

lam2 : {Γ : Cx} → RTm ((Γ ∙) ∙) → RTm Γ
lam2 b = lam (lam b)
lam3 : {Γ : Cx} → RTm (((Γ ∙) ∙) ∙) → RTm Γ
lam3 b = lam (lam (lam b))

------------------------------------------------------------------------
-- 2. ★ THE `here` FIBRE, at variables (m , Γ' , A' , A).
------------------------------------------------------------------------

module HereV (Θ₀ : Cx) where
  Γv : Cx
  Γv = (((Θ₀ ∙) ∙) ∙) ∙
  m g a' a : RTm Γv
  m  = v₃
  g  = v₂
  a' = v₁
  a  = v₀
  p q : RTm Γv
  p = pair g (a' ,ₚ unit)
  q = pair (tag 0) p
  X : RTm Γv
  X = fzero
  i : RTm Γv
  i = ix∋ (nsuc m) (cext g a') X a

  B : RTm (Γv ∙)
  B = app (app (ielim CtxD (fst v₀) gM (fst (snd v₀))) (fst (snd (snd v₀)))) (snd (snd (snd v₀)))

  T1 T2 : RTm Γv
  T1 = app (app (ielim CtxD (fst i) gM (fst (snd i))) (fst (snd (snd i)))) (snd (snd (snd i)))
  T2 = app (app (ielim CtxD (nsuc m) gM (cext g a')) X) a

  c1 : app D∋ i ⟶* T1
  c1 = step (β B i) (subst (λ z → z ⟶* T1) (sym e1) done)
    where
      e1 : subTm (single i) B ≡ T1
      e1 = cong₂ (λ D G → app (app (ielim D (fst i) G (fst (snd i))) (fst (snd (snd i)))) (snd (snd (snd i))))
                 (CtxD-sub (single i)) (gM-sub (single i))

  c2 : T1 ⟶* T2
  c2 = projChain (nsuc m) (cext g a') X a gM

  h : RTm Γv
  h = dih CtxD gM (app CtxD (nsuc m)) q
  gs' : RTm Γv
  gs' = subTm (single m) gs
  T3 T4 : RTm Γv
  T3 = app (app (app (app (subTm (single m) (methAt (gs ∷ []))) q) h) X) a
  T4 = app (app (app (app gs' p) h) X) a

  c3 : T2 ⟶* T3
  c3 = ⟶*-appˡ (⟶*-appˡ (ιN-s {D = CtxD} {E0 = methAt (gz ∷ [])} {m = m} {q = q} {ES = methAt (gs ∷ [])}))

  c4 : T3 ⟶* T4
  c4 = subst (λ z → app (app (app (app z q) h) X) a ⟶* T4) (sym (methAt-sub (single m) (gs ∷ [])))
             (⟶*-appˡ (⟶*-appˡ (methAt-β {k = 0} {m = gs'} {p = p} {h = h} {ms = gs' ∷ []} nth-z)))

  -- the four β's of the context method, each cast to its clean reduct
  T5 : RTm Γv
  T5 = GBx m p X a
  t0 t1 t2 t3 : RTm _
  t0 = lam3 (GBx (W4 m) v₃ v₁ v₀)
  t1 = lam2 (GBx (W3 m) (W3 p) v₁ v₀)
  t2 = lam (GBx (W2 m) (W2 p) v₁ v₀)
  t3 = GBx (W1 m) (W1 p) (W1 X) v₀
  e0 : gs' ≡ lam t0
  e0 = cong (λ Z → lam (lam3 Z)) (GBx-sub (extS (extS (extS (extS (single m))))) v₄ v₃ v₁ v₀)
  e1 : subTm (single p) t0 ≡ lam t1
  e1 = cong (λ Z → lam (lam2 Z)) (GBx-sub (extS (extS (extS (single p)))) (W4 m) v₃ v₁ v₀)
  e2 : subTm (single h) t1 ≡ lam t2
  e2 = cong (λ Z → lam (lam Z)) (GBx-sub (extS (extS (single h))) (W3 m) (W3 p) v₁ v₀)
  e3 : subTm (single X) t2 ≡ lam t3
  e3 = cong lam (GBx-sub (extS (single X)) (W2 m) (W2 p) v₁ v₀)
  e4 : subTm (single a) t3 ≡ T5
  e4 = GBx-sub (single a) (W1 m) (W1 p) (W1 X) v₀

  c5 : T4 ⟶* T5
  c5 = subst (λ z → app (app (app (app z p) h) X) a ⟶* T5) (sym e0)
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (βcast t0 p (lam t1) e1))))
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (βcast t1 h (lam t2) e2)))
         (⟶*-trans (⟶*-appˡ (βcast t2 X (lam t3) e3))
                   (βcast t3 a T5 e4))))

  -- the payload's projections reduce, then the two let-β's
  F : RTm ((Γv ∙) ∙)
  F = FBx m X a
  T6 : RTm Γv
  T6 = app (app (lam (lam F)) a') g

  c6 : T5 ⟶* T6
  c6 = ⟶*-trans (⟶*-appˡ (⟶*-appʳ (⟶*-trans (⟶*-fst (step (βsnd _ _) done)) (step (βfst _ _) done))))
                (⟶*-appʳ (step (βfst _ _) done))

  F1 : RTm (Γv ∙)
  F1 = fcase (W1 X) (HR (W1 m) (W1 a') (W1 a)) (TR (W2 m) v₁ v₀ (W2 a))
  F2 : RTm Γv
  F2 = fcase X (HR m a' a) (TR (W1 m) (W1 g) v₀ (W1 a))
  f1 : subTm (extS (single a')) F ≡ F1
  f1 = cong₂ (fcase (W1 X)) (hr-sub (extS (single a')) (W2 m) v₁ (W2 a))
                            (tr-sub (extS (extS (single a'))) (W3 m) v₁ v₀ (W3 a))
  f2 : subTm (single g) F1 ≡ F2
  f2 = cong₂ (fcase X) (hr-sub (single g) (W1 m) (W1 a') (W1 a))
                       (tr-sub (extS (single g)) (W2 m) v₁ v₀ (W2 a))

  c7 : T6 ⟶* F2
  c7 = ⟶*-trans (⟶*-appˡ (βcast (lam F) a' (lam F1) (cong lam f1))) (βcast F1 g F2 f2)

  R : RTm Γv
  R = HR m a' a

  c8 : F2 ⟶* R
  c8 = step (fcase-z (HR m a' a) _) done

  -- ★ the fibre, at variables
  fibV : app D∋ i ⟶* R
  fibV = ⟶*-trans c1 (⟶*-trans c2 (⟶*-trans c3 (⟶*-trans c4 (⟶*-trans c5 (⟶*-trans c6 (⟶*-trans c7 c8))))))

------------------------------------------------------------------------
-- 3. ★ THE `there` FIBRE, at variables (m , Γ' , A' , y , A).
------------------------------------------------------------------------

module ThereV (Θ₀ : Cx) where
  Γv : Cx
  Γv = ((((Θ₀ ∙) ∙) ∙) ∙) ∙
  m g a' y a : RTm Γv
  m  = v₄
  g  = v₃
  a' = v₂
  y  = v₁
  a  = v₀
  p q : RTm Γv
  p = pair g (a' ,ₚ unit)
  q = pair (tag 0) p
  X : RTm Γv
  X = fsuc y
  i : RTm Γv
  i = ix∋ (nsuc m) (cext g a') X a

  B : RTm (Γv ∙)
  B = app (app (ielim CtxD (fst v₀) gM (fst (snd v₀))) (fst (snd (snd v₀)))) (snd (snd (snd v₀)))

  T1 T2 : RTm Γv
  T1 = app (app (ielim CtxD (fst i) gM (fst (snd i))) (fst (snd (snd i)))) (snd (snd (snd i)))
  T2 = app (app (ielim CtxD (nsuc m) gM (cext g a')) X) a

  c1 : app D∋ i ⟶* T1
  c1 = step (β B i) (subst (λ z → z ⟶* T1) (sym e1) done)
    where
      e1 : subTm (single i) B ≡ T1
      e1 = cong₂ (λ D G → app (app (ielim D (fst i) G (fst (snd i))) (fst (snd (snd i)))) (snd (snd (snd i))))
                 (CtxD-sub (single i)) (gM-sub (single i))

  c2 : T1 ⟶* T2
  c2 = projChain (nsuc m) (cext g a') X a gM

  h : RTm Γv
  h = dih CtxD gM (app CtxD (nsuc m)) q
  gs' : RTm Γv
  gs' = subTm (single m) gs
  T3 T4 : RTm Γv
  T3 = app (app (app (app (subTm (single m) (methAt (gs ∷ []))) q) h) X) a
  T4 = app (app (app (app gs' p) h) X) a

  c3 : T2 ⟶* T3
  c3 = ⟶*-appˡ (⟶*-appˡ (ιN-s {D = CtxD} {E0 = methAt (gz ∷ [])} {m = m} {q = q} {ES = methAt (gs ∷ [])}))

  c4 : T3 ⟶* T4
  c4 = subst (λ z → app (app (app (app z q) h) X) a ⟶* T4) (sym (methAt-sub (single m) (gs ∷ [])))
             (⟶*-appˡ (⟶*-appˡ (methAt-β {k = 0} {m = gs'} {p = p} {h = h} {ms = gs' ∷ []} nth-z)))

  -- the four β's of the context method, each cast to its clean reduct
  T5 : RTm Γv
  T5 = GBx m p X a
  t0 t1 t2 t3 : RTm _
  t0 = lam3 (GBx (W4 m) v₃ v₁ v₀)
  t1 = lam2 (GBx (W3 m) (W3 p) v₁ v₀)
  t2 = lam (GBx (W2 m) (W2 p) v₁ v₀)
  t3 = GBx (W1 m) (W1 p) (W1 X) v₀
  e0 : gs' ≡ lam t0
  e0 = cong (λ Z → lam (lam3 Z)) (GBx-sub (extS (extS (extS (extS (single m))))) v₄ v₃ v₁ v₀)
  e1 : subTm (single p) t0 ≡ lam t1
  e1 = cong (λ Z → lam (lam2 Z)) (GBx-sub (extS (extS (extS (single p)))) (W4 m) v₃ v₁ v₀)
  e2 : subTm (single h) t1 ≡ lam t2
  e2 = cong (λ Z → lam (lam Z)) (GBx-sub (extS (extS (single h))) (W3 m) (W3 p) v₁ v₀)
  e3 : subTm (single X) t2 ≡ lam t3
  e3 = cong lam (GBx-sub (extS (single X)) (W2 m) (W2 p) v₁ v₀)
  e4 : subTm (single a) t3 ≡ T5
  e4 = GBx-sub (single a) (W1 m) (W1 p) (W1 X) v₀

  c5 : T4 ⟶* T5
  c5 = subst (λ z → app (app (app (app z p) h) X) a ⟶* T5) (sym e0)
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (βcast t0 p (lam t1) e1))))
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (βcast t1 h (lam t2) e2)))
         (⟶*-trans (⟶*-appˡ (βcast t2 X (lam t3) e3))
                   (βcast t3 a T5 e4))))

  -- the payload's projections reduce, then the two let-β's
  F : RTm ((Γv ∙) ∙)
  F = FBx m X a
  T6 : RTm Γv
  T6 = app (app (lam (lam F)) a') g

  c6 : T5 ⟶* T6
  c6 = ⟶*-trans (⟶*-appˡ (⟶*-appʳ (⟶*-trans (⟶*-fst (step (βsnd _ _) done)) (step (βfst _ _) done))))
                (⟶*-appʳ (step (βfst _ _) done))

  F1 : RTm (Γv ∙)
  F1 = fcase (W1 X) (HR (W1 m) (W1 a') (W1 a)) (TR (W2 m) v₁ v₀ (W2 a))
  F2 : RTm Γv
  F2 = fcase X (HR m a' a) (TR (W1 m) (W1 g) v₀ (W1 a))
  f1 : subTm (extS (single a')) F ≡ F1
  f1 = cong₂ (fcase (W1 X)) (hr-sub (extS (single a')) (W2 m) v₁ (W2 a))
                            (tr-sub (extS (extS (single a'))) (W3 m) v₁ v₀ (W3 a))
  f2 : subTm (single g) F1 ≡ F2
  f2 = cong₂ (fcase X) (hr-sub (single g) (W1 m) (W1 a') (W1 a))
                       (tr-sub (extS (single g)) (W2 m) v₁ v₀ (W2 a))

  c7 : T6 ⟶* F2
  c7 = ⟶*-trans (⟶*-appˡ (βcast (lam F) a' (lam F1) (cong lam f1))) (βcast F1 g F2 f2)

  R : RTm Γv
  R = TR m g y a

  c8 : F2 ⟶* R
  c8 = step (fcase-s y (HR m a' a) _) (subst (λ z → z ⟶* R) (sym (tr-sub (single y) (W1 m) (W1 g) v₀ (W1 a))) done)

  -- ★ the fibre, at variables
  fibV : app D∋ i ⟶* R
  fibV = ⟶*-trans c1 (⟶*-trans c2 (⟶*-trans c3 (⟶*-trans c4 (⟶*-trans c5 (⟶*-trans c6 (⟶*-trans c7 c8))))))

------------------------------------------------------------------------
-- 4. ★ …AT ANY TERMS: the variable chains, substituted.
------------------------------------------------------------------------

module _ {Γ : Cx} where
  private
    σH : RTm Γ → RTm Γ → RTm Γ → RTm Γ → Sub (HereV.Γv Γ) Γ
    σH m g a' a vz                      = a
    σH m g a' a (vs vz)                 = a'
    σH m g a' a (vs (vs vz))            = g
    σH m g a' a (vs (vs (vs vz)))       = m
    σH m g a' a (vs (vs (vs (vs x))))   = var x

    σT : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → Sub (ThereV.Γv Γ) Γ
    σT m g a' y a vz                        = a
    σT m g a' y a (vs vz)                   = y
    σT m g a' y a (vs (vs vz))              = a'
    σT m g a' y a (vs (vs (vs vz)))         = g
    σT m g a' y a (vs (vs (vs (vs vz))))    = m
    σT m g a' y a (vs (vs (vs (vs (vs x))))) = var x

  fib-here : (m g a' a : RTm Γ) →
             app D∋ (ix∋ (nsuc m) (cext g a') fzero a) ⟶* rows (⌜ hereT m a' a ⌝ᵗ ∷ [])
  fib-here m g a' a =
    subst (λ z → app D∋ (ix∋ (nsuc m) (cext g a') fzero a) ⟶* z)
          (hr-sub σ v₃ v₁ v₀)
      (subst (λ z → app z (ix∋ (nsuc m) (cext g a') fzero a) ⟶* subTm σ (HereV.R Γ)) (D∋-sub σ)
             (⟶*-sub σ (HereV.fibV Γ)))
    where σ = σH m g a' a

  fib-there : (m g a' y a : RTm Γ) →
              app D∋ (ix∋ (nsuc m) (cext g a') (fsuc y) a) ⟶* rows (⌜ thereT m g y a ⌝ᵗ ∷ [])
  fib-there m g a' y a =
    subst (λ z → app D∋ (ix∋ (nsuc m) (cext g a') (fsuc y) a) ⟶* z)
          (tr-sub σ v₄ v₃ v₁ v₀)
      (subst (λ z → app z (ix∋ (nsuc m) (cext g a') (fsuc y) a) ⟶* subTm σ (ThereV.R Γ)) (D∋-sub σ)
             (⟶*-sub σ (ThereV.fibV Γ)))
    where σ = σT m g a' y a

------------------------------------------------------------------------
-- 5. ★ THE CONSTRUCTORS.
------------------------------------------------------------------------

here∋ : {Γ : Cx} → RTm Γ → RTm Γ
here∋ e = conₗ 0 (e ,ₚ unit)

there∋ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
there∋ b r e = conₗ 0 (b ,ₚ r ,ₚ e ,ₚ unit)

module _ {Θ : Ctx} {m g a' a : RTm ⌊ Θ ⌋} where
  -- here : (Γ ▹ A') ∋ vz ∷ wk A'
  ⊢here∋ : {e : RTm ⌊ Θ ⌋} → Θ ⊢ m ∷ El ⌜Nat⌝ → Θ ⊢ g ∷ KCtx m → Θ ⊢ a' ∷ K 0 m → Θ ⊢ a ∷ K 0 (nsuc m) →
           Θ ⊢ e ∷ El (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m a')) →
           Θ ⊢ here∋ e ∷ K∋ (ix∋ (nsuc m) (cext g a') fzero a)
  ⊢here∋ {e} dm dg da' da de =
    ⊢conRow {Θ} {I∋} {D∋} {ix∋ (nsuc m) (cext g a') fzero a} {⌜ hereT m a' a ⌝ᵗ} {pair e unit} ⊢I∋ ⊢D∋
            (⊢ix∋ (⊢isuc dm) (⊢cext dm dg da') (⊢fzero (fromI dm)) da)
            (fib-here m g a' a)
            (⊢tel {Θ} {I∋} {hereT m a' a} ⊢I∋ ok)
            (⊢payσ {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m a')} {e} {unit} {tι} ok de
                   (⊢payι {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {unit} ⊢unit))
    where
      ok : TelOK Θ I∋ (hereT m a' a)
      ok = hereOK {Θ} {m} {a'} {a} dm da' da

module _ {Θ : Ctx} {m g a' y a : RTm ⌊ Θ ⌋} where
  -- there : Γ' ∋ y ∷ B → (Γ' ▹ A') ∋ vs y ∷ wk B
  ⊢there∋ : {b r e : RTm ⌊ Θ ⌋} → Θ ⊢ m ∷ El ⌜Nat⌝ → Θ ⊢ g ∷ KCtx m → Θ ⊢ a' ∷ K 0 m → Θ ⊢ y ∷ Fin m →
            Θ ⊢ a ∷ K 0 (nsuc m) → Θ ⊢ b ∷ K 0 m → Θ ⊢ r ∷ K∋ (ix∋ m g y b) →
            Θ ⊢ e ∷ El (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b)) →
            Θ ⊢ there∋ b r e ∷ K∋ (ix∋ (nsuc m) (cext g a') (fsuc y) a)
  ⊢there∋ {b} {r} {e} dm dg da' dy da db dr de =
    ⊢conRow {Θ} {I∋} {D∋} {ix∋ (nsuc m) (cext g a') (fsuc y) a} {⌜ thereT m g y a ⌝ᵗ} {pair b (r ,ₚ e ,ₚ unit)}
            ⊢I∋ ⊢D∋ (⊢ix∋ (⊢isuc dm) (⊢cext dm dg da') (⊢fsuc dy) da)
            (fib-there m g a' y a)
            (⊢tel {Θ} {I∋} {thereT m g y a} ⊢I∋ okT)
            (⊢payσ {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {⌜Ty⌝ m} {b} {pair r (e ,ₚ unit)} {Tρ} okT (toTy db)
                   (⊢-cast {Θ} {pair r (e ,ₚ unit)} {El (dpay I∋ D∋ ⌜ Tρ' ⌝ᵗ)} {El (dpay I∋ D∋ (subTm (single b) ⌜ Tρ ⌝ᵗ))}
                           (cong (λ C → El (dpay I∋ D∋ C)) (sym instT)) dp1))
    where
      okT : TelOK Θ I∋ (thereT m g y a)
      okT = thereOK {Θ} {m} {g} {y} {a} dm dg dy da
      Tρ : Tel (⌊ Θ ⌋ ∙)
      Tρ = tρ (ix∋ (renTm vs m) (renTm vs g) (renTm vs y) v₀)
              (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc (renTm vs m))) (renTm vs a) (wk 0 (renTm vs m) v₀)) tι)
      Tρ' : Tel ⌊ Θ ⌋
      Tρ' = tρ (ix∋ m g y b) (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b)) tι)
      wkc : (t : RTm ⌊ Θ ⌋) → subTm (single b) (renTm vs t) ≡ t
      wkc t = wk-cancel-tm b t
      instT : subTm (single b) ⌜ Tρ ⌝ᵗ ≡ ⌜ Tρ' ⌝ᵗ
      instT = cong₂ (λ J X → dρ J (dσ X (lam dι)))
                (cong₃ (λ u w z → ix∋ u w z b) (wkc m) (wkc g) (wkc y))
                (cong₃ ⌜Id⌝ (trans (⌜Ty⌝-sub (single b) (nsuc (renTm vs m)))
                                   (cong (λ z → ⌜Ty⌝ (nsuc z)) {x = subTm (single b) (renTm vs m)} {y = m} (wkc m)))
                            (wkc a)
                            (trans (wk-sub (single b) 0 (renTm vs m) v₀)
                                   (cong (λ z → wk 0 z b) {x = subTm (single b) (renTm vs m)} {y = m} (wkc m))))
      dId : Θ ⊢ ⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b) ∷ U
      dId = ⊢⌜Id⌝ {Θ} {⌜Ty⌝ (nsuc m)} {a} {wk 0 m b} (⊢⌜Ty⌝ (⊢isuc dm)) (toTy da) (toTy (⊢wkS {Θ} {0} {m} {b} lt-z dm db))
      dp1 : Θ ⊢ pair r (e ,ₚ unit) ∷ El (dpay I∋ D∋ ⌜ Tρ' ⌝ᵗ)
      dp1 = ⊢payρ {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {ix∋ m g y b} {r} {pair e unit} {tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b)) tι}
              (ok-ρ (⊢ix∋ dm dg dy db) (ok-σ dId ok-ι)) dr
              (⊢payσ {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b)} {e} {unit} {tι} (ok-σ dId ok-ι) de
                     (⊢payι {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {unit} ⊢unit))
