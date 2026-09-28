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
-- The chains are built at VARIABLES, where the substitution algebra
-- computes, and moved to any terms by `⟶*-sub`.  The closed pieces (the
-- methods, the descriptions) never reduce under a substitution: each one's
-- closedness is a structural lemma, cast once
-- (`knot-description-normalisation-trap`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.LookupCon where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.RedCong
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; conₗ; tag; selF; selF-sub; ⊢selF; selF-β; subC; nth-z; nth-s; lt-z; ⊢tag; ⊢pay-σ; ⊢con-fib; []ᵈ; _∷ᵈ_ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.NatFib
open import DirectedHoTT.Lib.FinFam
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Examples.Knot.Sig
open import DirectedHoTT.Examples.Knot.Ctx
open import DirectedHoTT.Examples.Knot.Ren using ( wk; wk-sub; ⊢wkS )
open import DirectedHoTT.Examples.Knot.Lookup

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- 1. ★ CLOSEDNESS of the fibre function's pieces.
------------------------------------------------------------------------

rows-sub : {c : ℕ} (τ : Sub Δ Θ) (Cs : Cons Δ c) → subTm τ (rows Cs) ≡ rows (subC τ Cs)
rows-sub {c = c} τ Cs = cong (dσ (⌜Fin⌝ c)) (selF-sub τ Cs)

hereT-sub : (σ : Sub Δ Θ) (m a' a : RTm Δ) →
            subTm σ ⌜ hereT m a' a ⌝ᵗ ≡ ⌜ hereT (subTm σ m) (subTm σ a') (subTm σ a) ⌝ᵗ
hereT-sub σ m a' a =
  cong₂ (λ X W → dσ (⌜Id⌝ X (subTm σ a) W) (lam dι)) (⌜Ty⌝-sub σ (nsuc m)) (wk-sub σ 0 m a')

thereT-sub : (σ : Sub Δ Θ) (m g y a : RTm Δ) →
             subTm σ ⌜ thereT m g y a ⌝ᵗ ≡ ⌜ thereT (subTm σ m) (subTm σ g) (subTm σ y) (subTm σ a) ⌝ᵗ
thereT-sub σ m g y a =
  cong₂ (λ X Y → dσ X (lam Y)) (⌜Ty⌝-sub σ m)
    (cong₂ dρ (cong₃ (λ u w z → ix∋ u w z (var vz)) (wkS σ m) (wkS σ g) (wkS σ y))
              (cong (λ Z → dσ Z (lam dι))
                    (cong₃ ⌜Id⌝ (trans (⌜Ty⌝-sub σ' (nsuc (renTm vs m)))
                                       (cong (λ z → ⌜Ty⌝ (nsuc z)) {x = subTm σ' (renTm vs m)} {y = renTm vs (subTm σ m)} (wkS σ m)))
                                (wkS σ a)
                                (trans (wk-sub σ' 0 (renTm vs m) (var vz))
                                       (cong (λ z → wk 0 z (var vz)) {x = subTm σ' (renTm vs m)} {y = renTm vs (subTm σ m)} (wkS σ m))))))
  where σ' = extS σ

private
  -- the method bodies' row, under any substitution of their binders
  lam5 : RTm (((((Θ ∙) ∙) ∙) ∙) ∙) → RTm Θ
  lam5 b = lam (lam (lam (lam (lam b))))

  e6 : Sub Δ Θ → Sub (((((((Δ ∙) ∙) ∙) ∙) ∙) ∙)) (((((((Θ ∙) ∙) ∙) ∙) ∙) ∙))
  e6 σ = extS (extS (extS (extS (extS (extS σ)))))

xz-sub : (σ : Sub Δ Θ) → subTm (extS σ) (xz {Δ}) ≡ xz {Θ}
xz-sub {Δ} {Θ} σ =
  cong lam5 {x = subTm (e6 σ) (rows (HB ∷ []))} {y = rows (HB ∷ [])}
    (trans {x = subTm (e6 σ) (rows (HB ∷ []))} {y = rows (subTm (e6 σ) HB ∷ [])} {z = rows (HB ∷ [])}
           (rows-sub (e6 σ) (HB ∷ []))
           (cong (λ C → rows (C ∷ [])) {x = subTm (e6 σ) HB} {y = HB} (hereT-sub (e6 σ) V5 (var (vs (vs vz))) (var vz))))
  where
    V5 : {Ξ : Cx} → RTm ((((((Ξ ∙) ∙) ∙) ∙) ∙) ∙)
    V5 = (var (vs (vs (vs (vs (vs vz))))))
    HB : {Ξ : Cx} → RTm ((((((Ξ ∙) ∙) ∙) ∙) ∙) ∙)
    HB = ⌜ hereT V5 (var (vs (vs vz))) (var vz) ⌝ᵗ

xs-sub : (σ : Sub Δ Θ) → subTm (extS σ) (xs {Δ}) ≡ xs {Θ}
xs-sub {Δ} {Θ} σ =
  cong lam5 {x = subTm (e6 σ) (rows (TB ∷ []))} {y = rows (TB ∷ [])}
    (trans {x = subTm (e6 σ) (rows (TB ∷ []))} {y = rows (subTm (e6 σ) TB ∷ [])} {z = rows (TB ∷ [])}
           (rows-sub (e6 σ) (TB ∷ []))
           (cong (λ C → rows (C ∷ [])) {x = subTm (e6 σ) TB} {y = TB}
                 (thereT-sub (e6 σ) V5 (var (vs vz)) (fst (var (vs (vs (vs (vs vz)))))) (var vz))))
  where
    V5 : {Ξ : Cx} → RTm ((((((Ξ ∙) ∙) ∙) ∙) ∙) ∙)
    V5 = (var (vs (vs (vs (vs (vs vz))))))
    TB : {Ξ : Cx} → RTm ((((((Ξ ∙) ∙) ∙) ∙) ∙) ∙)
    TB = ⌜ thereT V5 (var (vs vz)) (fst (var (vs (vs (vs (vs vz)))))) (var vz) ⌝ᵗ

xM-sub : (σ : Sub Δ Θ) → subTm σ (xM {Δ}) ≡ xM {Θ}
xM-sub {Δ} {Θ} σ =
  trans {x = subTm σ (xM {Δ})} {y = methN (subTm σ (methAt [])) (subTm (extS σ) (methAt (xz ∷ xs ∷ [])))} {z = xM {Θ}}
    (methN-sub σ (methAt []) (methAt (xz ∷ xs ∷ [])))
    (cong₂ methN {x = subTm σ (methAt [])} {x' = methAt []}
                 {y = subTm (extS σ) (methAt (xz ∷ xs ∷ []))} {y' = methAt (xz ∷ xs ∷ [])}
           refl
           (trans {x = subTm (extS σ) (methAt (xz ∷ xs ∷ []))} {y = methAt (subC (extS σ) (xz ∷ xs ∷ []))}
                  {z = methAt (xz ∷ xs ∷ [])}
                  (methAt-sub (extS σ) (xz ∷ xs ∷ []))
                  (cong methAt {x = subC (extS σ) (xz ∷ xs ∷ [])} {y = xz ∷ xs ∷ []}
                        (cong₂ _∷_ (xz-sub σ) (cong₂ _∷_ (xs-sub σ) refl)))))

private
  lam4 : RTm ((((Θ ∙) ∙) ∙) ∙) → RTm Θ
  lam4 b = lam (lam (lam (lam b)))

  gsBody : RTm (((((Θ ∙) ∙) ∙) ∙) ∙) → RTm (((((Θ ∙) ∙) ∙) ∙) ∙)
  gsBody X = app (app (app (ielim FinD (nsuc (var (vs (vs (vs (vs vz)))))) X (var (vs vz)))
                           (fst (snd (var (vs (vs (vs vz)))))))
                      (fst (var (vs (vs (vs vz))))))
                 (var vz)

gs-sub : (σ : Sub Δ Θ) → subTm (extS σ) (gs {Δ}) ≡ gs {Θ}
gs-sub {Δ} {Θ} σ = cong (λ X → lam4 (gsBody X)) {x = subTm σ5 (xM {Δ ∙ ∙ ∙ ∙ ∙})} {y = xM {Θ ∙ ∙ ∙ ∙ ∙}} (xM-sub σ5)
  where σ5 = extS (extS (extS (extS (extS σ))))

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
  cong lam (cong₂ (λ D G → app (app (ielim D (fst (var vz)) G (fst (snd (var vz)))) (fst (snd (snd (var vz)))))
                              (snd (snd (snd (var vz)))))
                  {x = subTm (extS σ) (CtxD {Δ ∙})} {x' = CtxD} {y = subTm (extS σ) (gM {Δ ∙})} {y' = gM}
                  (CtxD-sub (extS σ)) (gM-sub (extS σ)))

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

W1 W2 W3 W4 W5 : {Γ : Cx} → RTm Γ → RTm _
W1 t = renTm vs t
W2 t = renTm vs (W1 t)
W3 t = renTm vs (W2 t)
W4 t = renTm vs (W3 t)
W5 t = renTm vs (W4 t)

lam2 : {Γ : Cx} → RTm ((Γ ∙) ∙) → RTm Γ
lam2 b = lam (lam b)
lam3 : {Γ : Cx} → RTm (((Γ ∙) ∙) ∙) → RTm Γ
lam3 b = lam (lam (lam b))

-- the context method's body, with every position a parameter
GBx : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
GBx X M P x A = app (app (app (ielim FinD (nsuc M) X x) (fst (snd P))) (fst P)) A

-- the variable method's rows
HR : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
HR M A' A = rows (⌜ hereT M A' A ⌝ᵗ ∷ [])
TR : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
TR M G Y A = rows (⌜ thereT M G Y A ⌝ᵗ ∷ [])

------------------------------------------------------------------------
-- 2. ★ THE `here` FIBRE, at variables (m , Γ' , A' , A).
------------------------------------------------------------------------

module HereV (Θ₀ : Cx) where
  Γv : Cx
  Γv = (((Θ₀ ∙) ∙) ∙) ∙
  m g a' a : RTm Γv
  m  = var (vs (vs (vs vz)))
  g  = var (vs (vs vz))
  a' = var (vs vz)
  a  = var vz
  p q : RTm Γv
  p = pair g (pair a' unit)
  q = pair (tag 0) p
  i : RTm Γv
  i = ix∋ (nsuc m) (cext g a') ffz a

  B : RTm (Γv ∙)
  B = app (app (ielim CtxD (fst (var vz)) gM (fst (snd (var vz)))) (fst (snd (snd (var vz))))) (snd (snd (snd (var vz))))

  T1 T2 : RTm Γv
  T1 = app (app (ielim CtxD (fst i) gM (fst (snd i))) (fst (snd (snd i)))) (snd (snd (snd i)))
  T2 = app (app (ielim CtxD (nsuc m) gM (cext g a')) ffz) a

  c1 : app D∋ i ⟶* T1
  c1 = step (β B i) (subst (λ z → z ⟶* T1) (sym e1) done)
    where
      e1 : subTm (single i) B ≡ T1
      e1 = cong₂ (λ D G → app (app (ielim D (fst i) G (fst (snd i))) (fst (snd (snd i)))) (snd (snd (snd i))))
                 (CtxD-sub (single i)) (gM-sub (single i))

  c2 : T1 ⟶* T2
  c2 = projChain (nsuc m) (cext g a') ffz a gM

  h : RTm Γv
  h = dih CtxD gM (app CtxD (nsuc m)) q
  gs' : RTm Γv
  gs' = subTm (single m) gs
  T3 T4 : RTm Γv
  T3 = app (app (app (app (subTm (single m) (methAt (gs ∷ []))) q) h) ffz) a
  T4 = app (app (app (app gs' p) h) ffz) a

  c3 : T2 ⟶* T3
  c3 = ⟶*-appˡ (⟶*-appˡ (ιN-s {D = CtxD} {E0 = methAt (gz ∷ [])} {m = m} {q = q} {ES = methAt (gs ∷ [])}))

  c4 : T3 ⟶* T4
  c4 = subst (λ z → app (app (app (app z q) h) ffz) a ⟶* T4) (sym (methAt-sub (single m) (gs ∷ [])))
             (⟶*-appˡ (⟶*-appˡ (methAt-β {k = 0} {m = gs'} {p = p} {h = h} {ms = gs' ∷ []} nth-z)))

  -- the four β's of the context method, each cast to its clean reduct
  T5 : RTm Γv
  T5 = GBx xM m p ffz a
  t0 t1 t2 t3 : RTm _
  t0 = lam3 (GBx xM (W4 m) (var (vs (vs (vs (vz))))) (var (vs (vz))) (var vz))
  t1 = lam2 (GBx xM (W3 m) (W3 p) (var (vs (vz))) (var vz))
  t2 = lam (GBx xM (W2 m) (W2 p) (var (vs (vz))) (var vz))
  t3 = GBx xM (W1 m) (W1 p) (W1 ffz) (var vz)
  e0 : gs' ≡ lam t0
  e0 = cong (λ Z → lam (lam3 (GBx Z (W4 m) (var (vs (vs (vs (vz))))) (var (vs (vz))) (var vz))))
            {x = subTm (extS (extS (extS (extS (single m))))) xM} {y = xM} (xM-sub (extS (extS (extS (extS (single m))))))
  e1 : subTm (single p) t0 ≡ lam t1
  e1 = cong (λ Z → lam (lam2 (GBx Z (W3 m) (W3 p) (var (vs (vz))) (var vz))))
            {x = subTm (extS (extS (extS (single p)))) xM} {y = xM} (xM-sub (extS (extS (extS (single p)))))
  e2 : subTm (single h) t1 ≡ lam t2
  e2 = cong (λ Z → lam (lam (GBx Z (W2 m) (W2 p) (var (vs (vz))) (var vz))))
            {x = subTm (extS (extS (single h))) xM} {y = xM} (xM-sub (extS (extS (single h))))
  e3 : subTm (single ffz) t2 ≡ lam t3
  e3 = cong (λ Z → lam (GBx Z (W1 m) (W1 p) (W1 ffz) (var vz)))
            {x = subTm (extS (single ffz)) xM} {y = xM} (xM-sub (extS (single ffz)))
  e4 : subTm (single a) t3 ≡ T5
  e4 = cong (λ Z → GBx Z m p ffz a) {x = subTm (single a) xM} {y = xM} (xM-sub (single a))

  c5 : T4 ⟶* T5
  c5 = subst (λ z → app (app (app (app z p) h) ffz) a ⟶* T5) (sym e0)
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (βcast t0 p (lam t1) e1))))
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (βcast t1 h (lam t2) e2)))
         (⟶*-trans (⟶*-appˡ (βcast t2 ffz (lam t3) e3))
                   (βcast t3 a T5 e4))))

  T6 : RTm Γv
  T6 = app (app (app (ielim FinD (nsuc m) xM ffz) a') g) a

  c6 : T5 ⟶* T6
  c6 = ⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appʳ (⟶*-trans (⟶*-fst (step (βsnd _ _) done)) (step (βfst _ _) done)))))
                (⟶*-appˡ (⟶*-appʳ (step (βfst _ _) done)))

  h2 : RTm Γv
  h2 = dih FinD xM (app FinD (nsuc m)) (pair (tag 0) unit)
  xz' : RTm Γv
  xz' = subTm (single m) xz
  T7 T8 : RTm Γv
  T7 = app (app (app (app (app (subTm (single m) (methAt (xz ∷ xs ∷ []))) (pair (tag 0) unit)) h2) a') g) a
  T8 = app (app (app (app (app xz' unit) h2) a') g) a

  c7 : T6 ⟶* T7
  c7 = ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (ιN-s {D = FinD} {E0 = methAt []} {m = m} {q = pair (tag 0) unit} {ES = methAt (xz ∷ xs ∷ [])})))

  c8 : T7 ⟶* T8
  c8 = subst (λ z → app (app (app (app (app z (pair (tag 0) unit)) h2) a') g) a ⟶* T8)
             (sym (methAt-sub (single m) (xz ∷ xs ∷ [])))
             (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (methAt-β {k = 0} {m = xz'} {p = unit} {h = h2}
                                                     {ms = xz' ∷ subTm (single m) xs ∷ []} nth-z))))

  -- the five β's of the variable method, each cast to its clean reduct
  R : RTm Γv
  R = HR m a' a
  u0 u1 u2 u3 u4 : RTm _
  u0 = lam3 (lam (HR (W5 m) (var (vs (vs (vz)))) (var vz)))
  u1 = lam3 (HR (W4 m) (var (vs (vs (vz)))) (var vz))
  u2 = lam2 (HR (W3 m) (var (vs (vs (vz)))) (var vz))
  u3 = lam (HR (W2 m) (W2 a') (var vz))
  u4 = HR (W1 m) (W1 a') (var vz)
  f0 : xz' ≡ lam u0
  f0 = cong (λ Z → lam (lam3 (lam Z))) {x = subTm (extS (extS (extS (extS (extS (single m)))))) (HR (var (vs (vs (vs (vs (vs (vz))))))) (var (vs (vs (vz)))) (var vz))}
            {y = HR (W5 m) (var (vs (vs (vz)))) (var vz)}
            (hr-sub (extS (extS (extS (extS (extS (single m)))))) (var (vs (vs (vs (vs (vs (vz))))))) (var (vs (vs (vz)))) (var vz))
  f1 : subTm (single unit) u0 ≡ lam u1
  f1 = cong (λ Z → lam (lam3 Z)) {x = subTm (extS (extS (extS (extS (single unit))))) (HR (W5 m) (var (vs (vs (vz)))) (var vz))}
            {y = HR (W4 m) (var (vs (vs (vz)))) (var vz)}
            (hr-sub (extS (extS (extS (extS (single unit))))) (W5 m) (var (vs (vs (vz)))) (var vz))
  f2 : subTm (single h2) u1 ≡ lam u2
  f2 = cong (λ Z → lam (lam2 Z)) {x = subTm (extS (extS (extS (single h2)))) (HR (W4 m) (var (vs (vs (vz)))) (var vz))}
            {y = HR (W3 m) (var (vs (vs (vz)))) (var vz)}
            (hr-sub (extS (extS (extS (single h2)))) (W4 m) (var (vs (vs (vz)))) (var vz))
  f3 : subTm (single a') u2 ≡ lam u3
  f3 = cong (λ Z → lam (lam Z)) {x = subTm (extS (extS (single a'))) (HR (W3 m) (var (vs (vs (vz)))) (var vz))}
            {y = HR (W2 m) (W2 a') (var vz)}
            (hr-sub (extS (extS (single a'))) (W3 m) (var (vs (vs (vz)))) (var vz))
  f4 : subTm (single g) u3 ≡ lam u4
  f4 = cong lam {x = subTm (extS (single g)) (HR (W2 m) (W2 a') (var vz))} {y = HR (W1 m) (W1 a') (var vz)}
            (hr-sub (extS (single g)) (W2 m) (W2 a') (var vz))
  f5 : subTm (single a) u4 ≡ R
  f5 = hr-sub (single a) (W1 m) (W1 a') (var vz)

  c9 : T8 ⟶* R
  c9 = subst (λ z → app (app (app (app (app z unit) h2) a') g) a ⟶* R) (sym f0)
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (βcast u0 unit (lam u1) f1)))))
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (βcast u1 h2 (lam u2) f2))))
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (βcast u2 a' (lam u3) f3)))
         (⟶*-trans (⟶*-appˡ (βcast u3 g (lam u4) f4))
                   (βcast u4 a R f5)))))

  -- ★ the here fibre, at variables
  fibV : app D∋ i ⟶* R
  fibV = ⟶*-trans c1 (⟶*-trans c2 (⟶*-trans c3 (⟶*-trans c4 (⟶*-trans c5 (⟶*-trans c6 (⟶*-trans c7 (⟶*-trans c8 c9)))))))

------------------------------------------------------------------------
-- 3. ★ THE `there` FIBRE, at variables (m , Γ' , A' , y , A).  The same
--   walk; the variable's method is the second.
------------------------------------------------------------------------

module ThereV (Θ₀ : Cx) where
  Γv : Cx
  Γv = ((((Θ₀ ∙) ∙) ∙) ∙) ∙
  m g a' y a : RTm Γv
  m  = var (vs (vs (vs (vs vz))))
  g  = var (vs (vs (vs vz)))
  a' = var (vs (vs vz))
  y  = var (vs vz)
  a  = var vz
  p q : RTm Γv
  p = pair g (pair a' unit)
  q = pair (tag 0) p
  i : RTm Γv
  i = ix∋ (nsuc m) (cext g a') (ffs y) a

  B : RTm (Γv ∙)
  B = app (app (ielim CtxD (fst (var vz)) gM (fst (snd (var vz)))) (fst (snd (snd (var vz))))) (snd (snd (snd (var vz))))

  T1 T2 : RTm Γv
  T1 = app (app (ielim CtxD (fst i) gM (fst (snd i))) (fst (snd (snd i)))) (snd (snd (snd i)))
  T2 = app (app (ielim CtxD (nsuc m) gM (cext g a')) (ffs y)) a

  c1 : app D∋ i ⟶* T1
  c1 = step (β B i) (subst (λ z → z ⟶* T1) (sym e1) done)
    where
      e1 : subTm (single i) B ≡ T1
      e1 = cong₂ (λ D G → app (app (ielim D (fst i) G (fst (snd i))) (fst (snd (snd i)))) (snd (snd (snd i))))
                 (CtxD-sub (single i)) (gM-sub (single i))

  c2 : T1 ⟶* T2
  c2 = projChain (nsuc m) (cext g a') (ffs y) a gM

  h : RTm Γv
  h = dih CtxD gM (app CtxD (nsuc m)) q
  gs' : RTm Γv
  gs' = subTm (single m) gs
  T3 T4 : RTm Γv
  T3 = app (app (app (app (subTm (single m) (methAt (gs ∷ []))) q) h) (ffs y)) a
  T4 = app (app (app (app gs' p) h) (ffs y)) a

  c3 : T2 ⟶* T3
  c3 = ⟶*-appˡ (⟶*-appˡ (ιN-s {D = CtxD} {E0 = methAt (gz ∷ [])} {m = m} {q = q} {ES = methAt (gs ∷ [])}))

  c4 : T3 ⟶* T4
  c4 = subst (λ z → app (app (app (app z q) h) (ffs y)) a ⟶* T4) (sym (methAt-sub (single m) (gs ∷ [])))
             (⟶*-appˡ (⟶*-appˡ (methAt-β {k = 0} {m = gs'} {p = p} {h = h} {ms = gs' ∷ []} nth-z)))

  -- the four β's of the context method, each cast to its clean reduct
  T5 : RTm Γv
  T5 = GBx xM m p (ffs y) a
  t0 t1 t2 t3 : RTm _
  t0 = lam3 (GBx xM (W4 m) (var (vs (vs (vs (vz))))) (var (vs (vz))) (var vz))
  t1 = lam2 (GBx xM (W3 m) (W3 p) (var (vs (vz))) (var vz))
  t2 = lam (GBx xM (W2 m) (W2 p) (var (vs (vz))) (var vz))
  t3 = GBx xM (W1 m) (W1 p) (W1 (ffs y)) (var vz)
  e0 : gs' ≡ lam t0
  e0 = cong (λ Z → lam (lam3 (GBx Z (W4 m) (var (vs (vs (vs (vz))))) (var (vs (vz))) (var vz))))
            {x = subTm (extS (extS (extS (extS (single m))))) xM} {y = xM} (xM-sub (extS (extS (extS (extS (single m))))))
  e1 : subTm (single p) t0 ≡ lam t1
  e1 = cong (λ Z → lam (lam2 (GBx Z (W3 m) (W3 p) (var (vs (vz))) (var vz))))
            {x = subTm (extS (extS (extS (single p)))) xM} {y = xM} (xM-sub (extS (extS (extS (single p)))))
  e2 : subTm (single h) t1 ≡ lam t2
  e2 = cong (λ Z → lam (lam (GBx Z (W2 m) (W2 p) (var (vs (vz))) (var vz))))
            {x = subTm (extS (extS (single h))) xM} {y = xM} (xM-sub (extS (extS (single h))))
  e3 : subTm (single (ffs y)) t2 ≡ lam t3
  e3 = cong (λ Z → lam (GBx Z (W1 m) (W1 p) (W1 (ffs y)) (var vz)))
            {x = subTm (extS (single (ffs y))) xM} {y = xM} (xM-sub (extS (single (ffs y))))
  e4 : subTm (single a) t3 ≡ T5
  e4 = cong (λ Z → GBx Z m p (ffs y) a) {x = subTm (single a) xM} {y = xM} (xM-sub (single a))

  c5 : T4 ⟶* T5
  c5 = subst (λ z → app (app (app (app z p) h) (ffs y)) a ⟶* T5) (sym e0)
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (βcast t0 p (lam t1) e1))))
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (βcast t1 h (lam t2) e2)))
         (⟶*-trans (⟶*-appˡ (βcast t2 (ffs y) (lam t3) e3))
                   (βcast t3 a T5 e4))))

  T6 : RTm Γv
  T6 = app (app (app (ielim FinD (nsuc m) xM (ffs y)) a') g) a

  c6 : T5 ⟶* T6
  c6 = ⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appʳ (⟶*-trans (⟶*-fst (step (βsnd _ _) done)) (step (βfst _ _) done)))))
                (⟶*-appˡ (⟶*-appʳ (step (βfst _ _) done)))

  py : RTm Γv
  py = pair y unit
  h2 : RTm Γv
  h2 = dih FinD xM (app FinD (nsuc m)) (pair (tag 1) py)
  xs' : RTm Γv
  xs' = subTm (single m) xs
  T7 T8 : RTm Γv
  T7 = app (app (app (app (app (subTm (single m) (methAt (xz ∷ xs ∷ []))) (pair (tag 1) py)) h2) a') g) a
  T8 = app (app (app (app (app xs' py) h2) a') g) a

  c7 : T6 ⟶* T7
  c7 = ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (ιN-s {D = FinD} {E0 = methAt []} {m = m} {q = pair (tag 1) py} {ES = methAt (xz ∷ xs ∷ [])})))

  c8 : T7 ⟶* T8
  c8 = subst (λ z → app (app (app (app (app z (pair (tag 1) py)) h2) a') g) a ⟶* T8)
             (sym (methAt-sub (single m) (xz ∷ xs ∷ [])))
             (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (methAt-β {k = 1} {m = xs'} {p = py} {h = h2}
                                                     {ms = subTm (single m) xz ∷ xs' ∷ []} (nth-s nth-z)))))

  -- the five β's of the variable method, each cast to its clean reduct
  R : RTm Γv
  R = TR m g (fst py) a
  k0 k1 k2 k3 k4 : RTm _
  k0 = lam3 (lam (TR (W5 m) (var (vs (vz))) (fst (var (vs (vs (vs (vs (vz))))))) (var vz)))
  k1 = lam3 (TR (W4 m) (var (vs (vz))) (fst (W4 py)) (var vz))
  k2 = lam2 (TR (W3 m) (var (vs (vz))) (fst (W3 py)) (var vz))
  k3 = lam (TR (W2 m) (var (vs (vz))) (fst (W2 py)) (var vz))
  k4 = TR (W1 m) (W1 g) (fst (W1 py)) (var vz)
  f0 : xs' ≡ lam k0
  f0 = cong (λ Z → lam (lam3 (lam Z)))
            {x = subTm (extS (extS (extS (extS (extS (single m)))))) (TR (var (vs (vs (vs (vs (vs (vz))))))) (var (vs (vz))) (fst (var (vs (vs (vs (vs (vz))))))) (var vz))}
            {y = TR (W5 m) (var (vs (vz))) (fst (var (vs (vs (vs (vs (vz))))))) (var vz)}
            (tr-sub (extS (extS (extS (extS (extS (single m)))))) (var (vs (vs (vs (vs (vs (vz))))))) (var (vs (vz))) (fst (var (vs (vs (vs (vs (vz))))))) (var vz))
  f1 : subTm (single py) k0 ≡ lam k1
  f1 = cong (λ Z → lam (lam3 Z)) {x = subTm (extS (extS (extS (extS (single py))))) (TR (W5 m) (var (vs (vz))) (fst (var (vs (vs (vs (vs (vz))))))) (var vz))}
            {y = TR (W4 m) (var (vs (vz))) (fst (W4 py)) (var vz)}
            (tr-sub (extS (extS (extS (extS (single py))))) (W5 m) (var (vs (vz))) (fst (var (vs (vs (vs (vs (vz))))))) (var vz))
  f2 : subTm (single h2) k1 ≡ lam k2
  f2 = cong (λ Z → lam (lam2 Z)) {x = subTm (extS (extS (extS (single h2)))) (TR (W4 m) (var (vs (vz))) (fst (W4 py)) (var vz))}
            {y = TR (W3 m) (var (vs (vz))) (fst (W3 py)) (var vz)}
            (tr-sub (extS (extS (extS (single h2)))) (W4 m) (var (vs (vz))) (fst (W4 py)) (var vz))
  f3 : subTm (single a') k2 ≡ lam k3
  f3 = cong (λ Z → lam (lam Z)) {x = subTm (extS (extS (single a'))) (TR (W3 m) (var (vs (vz))) (fst (W3 py)) (var vz))}
            {y = TR (W2 m) (var (vs (vz))) (fst (W2 py)) (var vz)}
            (tr-sub (extS (extS (single a'))) (W3 m) (var (vs (vz))) (fst (W3 py)) (var vz))
  f4 : subTm (single g) k3 ≡ lam k4
  f4 = cong lam {x = subTm (extS (single g)) (TR (W2 m) (var (vs (vz))) (fst (W2 py)) (var vz))}
            {y = TR (W1 m) (W1 g) (fst (W1 py)) (var vz)}
            (tr-sub (extS (single g)) (W2 m) (var (vs (vz))) (fst (W2 py)) (var vz))
  f5 : subTm (single a) k4 ≡ R
  f5 = tr-sub (single a) (W1 m) (W1 g) (fst (W1 py)) (var vz)

  c9 : T8 ⟶* R
  c9 = subst (λ z → app (app (app (app (app z py) h2) a') g) a ⟶* R) (sym f0)
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (βcast k0 py (lam k1) f1)))))
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (βcast k1 h2 (lam k2) f2))))
         (⟶*-trans (⟶*-appˡ (⟶*-appˡ (βcast k2 a' (lam k3) f3)))
         (⟶*-trans (⟶*-appˡ (βcast k3 g (lam k4) f4))
                   (βcast k4 a R f5)))))

  fibV : app D∋ i ⟶* R
  fibV = ⟶*-trans c1 (⟶*-trans c2 (⟶*-trans c3 (⟶*-trans c4 (⟶*-trans c5 (⟶*-trans c6 (⟶*-trans c7 (⟶*-trans c8 c9)))))))

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
             app D∋ (ix∋ (nsuc m) (cext g a') ffz a) ⟶* rows (⌜ hereT m a' a ⌝ᵗ ∷ [])
  fib-here m g a' a =
    subst (λ z → app D∋ (ix∋ (nsuc m) (cext g a') ffz a) ⟶* z)
          (hr-sub σ (var (vs (vs (vs vz)))) (var (vs vz)) (var vz))
      (subst (λ z → app z (ix∋ (nsuc m) (cext g a') ffz a) ⟶* subTm σ (HereV.R Γ)) (D∋-sub σ)
             (⟶*-sub σ (HereV.fibV Γ)))
    where σ = σH m g a' a

  fib-there : (m g a' y a : RTm Γ) →
              app D∋ (ix∋ (nsuc m) (cext g a') (ffs y) a) ⟶* rows (⌜ thereT m g (fst (pair y unit)) a ⌝ᵗ ∷ [])
  fib-there m g a' y a =
    subst (λ z → app D∋ (ix∋ (nsuc m) (cext g a') (ffs y) a) ⟶* z)
          (tr-sub σ (var (vs (vs (vs (vs vz))))) (var (vs (vs (vs vz)))) (fst (pair (var (vs vz)) unit)) (var vz))
      (subst (λ z → app z (ix∋ (nsuc m) (cext g a') (ffs y) a) ⟶* subTm σ (ThereV.R Γ)) (D∋-sub σ)
             (⟶*-sub σ (ThereV.fibV Γ)))
    where σ = σT m g a' y a

------------------------------------------------------------------------
-- 5. ★ THE CONSTRUCTORS.
------------------------------------------------------------------------

-- a constructor of a one-row fibre
⊢conRow : {Ξ : Ctx} {I D i C p : RTm ⌊ Ξ ⌋} → Ξ ⊢ I ∷ U → Ξ ⊢ D ∷ DescF I → Ξ ⊢ i ∷ El I →
          app D i ⟶* rows (C ∷ []) → Ξ ⊢ C ∷ Desc I → Ξ ⊢ p ∷ El (dpay I D C) → Ξ ⊢ conₗ 0 p ∷ IMu I D i
⊢conRow {Ξ} {I} {D} {i} {C} {p} dI dD di r dC dp =
  ⊢con-fib dI dD di r
    (⊢pay-σ dI dD (⊢selF dI (dC ∷ᵈ []ᵈ)) (⊢conv (⊢tag lt-z) (csymᵀ (credᵀ El-⌜Fin⌝)))
            (⊢conv dp (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β {Cs = C ∷ []} nth-z)))))))

here∋ : {Γ : Cx} → RTm Γ → RTm Γ
here∋ e = conₗ 0 (pair e unit)

there∋ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
there∋ b r e = conₗ 0 (pair b (pair r (pair e unit)))

module _ {Θ : Ctx} {m g a' a : RTm ⌊ Θ ⌋} where
  -- here : (Γ ▹ A') ∋ vz ∷ wk A'
  ⊢here∋ : {e : RTm ⌊ Θ ⌋} → Θ ⊢ m ∷ El ⌜Nat⌝ → Θ ⊢ g ∷ KCtx m → Θ ⊢ a' ∷ K 0 m → Θ ⊢ a ∷ K 0 (nsuc m) →
           Θ ⊢ e ∷ El (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m a')) →
           Θ ⊢ here∋ e ∷ K∋ (ix∋ (nsuc m) (cext g a') ffz a)
  ⊢here∋ {e} dm dg da' da de =
    ⊢conRow {Θ} {I∋} {D∋} {ix∋ (nsuc m) (cext g a') ffz a} {⌜ hereT m a' a ⌝ᵗ} {pair e unit} ⊢I∋ ⊢D∋
            (⊢ix∋ (⊢isuc dm) (⊢cext dm dg da') (⊢ffz dm) da)
            (fib-here m g a' a)
            (⊢tel {Θ} {I∋} {hereT m a' a} ⊢I∋ ok)
            (⊢payσ {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m a')} {e} {unit} {tι} ok de
                   (⊢payι {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {unit} ⊢unit))
    where
      ok : TelOK Θ I∋ (hereT m a' a)
      ok = hereOK {Θ} {m} {a'} {a} dm da' da

module _ {Θ : Ctx} {m g a' y a : RTm ⌊ Θ ⌋} where
  private
    y' : RTm ⌊ Θ ⌋
    y' = fst (pair y unit)

  -- there : Γ' ∋ y ∷ B → (Γ' ▹ A') ∋ vs y ∷ wk B
  ⊢there∋ : {b r e : RTm ⌊ Θ ⌋} → Θ ⊢ m ∷ El ⌜Nat⌝ → Θ ⊢ g ∷ KCtx m → Θ ⊢ a' ∷ K 0 m → Θ ⊢ y ∷ FinI m →
            Θ ⊢ a ∷ K 0 (nsuc m) → Θ ⊢ b ∷ K 0 m → Θ ⊢ r ∷ K∋ (ix∋ m g y b) →
            Θ ⊢ e ∷ El (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b)) →
            Θ ⊢ there∋ b r e ∷ K∋ (ix∋ (nsuc m) (cext g a') (ffs y) a)
  ⊢there∋ {b} {r} {e} dm dg da' dy da db dr de =
    ⊢conRow {Θ} {I∋} {D∋} {ix∋ (nsuc m) (cext g a') (ffs y) a} {⌜ thereT m g y' a ⌝ᵗ} {pair b (pair r (pair e unit))}
            ⊢I∋ ⊢D∋ (⊢ix∋ (⊢isuc dm) (⊢cext dm dg da') (⊢ffs dm dy) da)
            (fib-there m g a' y a)
            (⊢tel {Θ} {I∋} {thereT m g y' a} ⊢I∋ okT)
            (⊢payσ {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {⌜Ty⌝ m} {b} {pair r (pair e unit)} {Tρ} okT (toTy db)
                   (⊢-cast {Θ} {pair r (pair e unit)} {El (dpay I∋ D∋ ⌜ Tρ' ⌝ᵗ)} {El (dpay I∋ D∋ (subTm (single b) ⌜ Tρ ⌝ᵗ))}
                           (cong (λ C → El (dpay I∋ D∋ C)) (sym instT)) dp1))
    where
      dy' : Θ ⊢ y' ∷ FinI m
      dy' = ⊢fst {Θ} {FinI m} {Unit} (⊢pair ty-Unit dy ⊢unit)
      okT : TelOK Θ I∋ (thereT m g y' a)
      okT = thereOK {Θ} {m} {g} {y'} {a} dm dg dy' da
      Tρ : Tel (⌊ Θ ⌋ ∙)
      Tρ = tρ (ix∋ (renTm vs m) (renTm vs g) (renTm vs y') (var vz))
              (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc (renTm vs m))) (renTm vs a) (wk 0 (renTm vs m) (var vz))) tι)
      Tρ' : Tel ⌊ Θ ⌋
      Tρ' = tρ (ix∋ m g y' b) (tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b)) tι)
      wkc : (t : RTm ⌊ Θ ⌋) → subTm (single b) (renTm vs t) ≡ t
      wkc t = wk-cancel-tm b t
      instT : subTm (single b) ⌜ Tρ ⌝ᵗ ≡ ⌜ Tρ' ⌝ᵗ
      instT = cong₂ (λ J X → dρ J (dσ X (lam dι)))
                (cong₃ (λ u w z → ix∋ u w z b) (wkc m) (wkc g) (wkc y'))
                (cong₃ ⌜Id⌝ (trans (⌜Ty⌝-sub (single b) (nsuc (renTm vs m)))
                                   (cong (λ z → ⌜Ty⌝ (nsuc z)) {x = subTm (single b) (renTm vs m)} {y = m} (wkc m)))
                            (wkc a)
                            (trans (wk-sub (single b) 0 (renTm vs m) (var vz))
                                   (cong (λ z → wk 0 z b) {x = subTm (single b) (renTm vs m)} {y = m} (wkc m))))
      dId : Θ ⊢ ⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b) ∷ U
      dId = ⊢⌜Id⌝ {Θ} {⌜Ty⌝ (nsuc m)} {a} {wk 0 m b} (⊢⌜Ty⌝ (⊢isuc dm)) (toTy da) (toTy (⊢wkS {Θ} {0} {m} {b} lt-z dm db))
      dr' : Θ ⊢ r ∷ IMu I∋ D∋ (ix∋ m g y' b)
      dr' = ⊢conv {Θ} {r} {K∋ (ix∋ m g y b)} {IMu I∋ D∋ (ix∋ m g y' b)} dr
                  (csymᵀ (credᵀ (ξ-IMuⁱ (ξ-pairʳ (ξ-pairʳ (ξ-pairˡ (βfst y unit)))))))
      dp1 : Θ ⊢ pair r (pair e unit) ∷ El (dpay I∋ D∋ ⌜ Tρ' ⌝ᵗ)
      dp1 = ⊢payρ {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {ix∋ m g y' b} {r} {pair e unit} {tσ (⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b)) tι}
              (ok-ρ (⊢ix∋ dm dg dy' db) (ok-σ dId ok-ι)) dr'
              (⊢payσ {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {⌜Id⌝ (⌜Ty⌝ (nsuc m)) a (wk 0 m b)} {e} {unit} {tι} (ok-σ dId ok-ι) de
                     (⊢payι {Θ} {I∋} {D∋} ⊢I∋ ⊢D∋ {unit} ⊢unit))
