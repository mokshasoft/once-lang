------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ FAMILIES FIBRED OVER ℕ: a family whose fibre is
-- computed by CASE ON A NATURAL-NUMBER INDEX.
--
--   DN C₀ Cₛ = λ i. natrec (Dσ C₀) (Dσ Cₛ)[m] i
--
-- the constructors at `0`, and the constructors at `suc m` (a list over
-- the PREDECESSOR `m`).  `Fin` is the example: `Fin 0 = ∅`,
-- `Fin (suc m) = fzero | fsuc (Fin m)` — its targets are presented BY
-- FIBRES (D075's reasoning at a numeric index), so no constructor carries
-- an index equation and none owes a transport.
--
-- ★ THE METHODS PATTERN-MATCH ON THE INDEX, as in `Lib/Sorted`: the one
--   method is a `natrec`-case on `i`; each case is a method at the index
--   TERM `0` or `suc m` (`Lib/MethAt`), where the fibre computes.  The
--   case types are the kernel's method body `T₀` re-based by the case's
--   substitution, so every obligation is a pointwise-`refl` flattening.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.NatFib where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-dpayᶜ; ⟶ᵀ*-El; red→≅ᵀ; ⟶*-appˡ )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢wk; ⊢-cast; wk-cancel-tm; ren-ty; sub-ty; Ren⊢-ext; ren-lemma; Ren⊢; ∋-cast
        ; conv-ctxᵀ; sub-lemma; Sub⊢; ⊢single )
open import DirectedHoTT.Metatheory.Premises using ( mot-ren; ⊢wkD; MethTy-wf )
open import DirectedHoTT.Lib.Sugar using ( sel )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Nth; subC; Dσ; selF; conₗ; tag; selF-β; selF-sub; nth-sub; nth-lt
        ; AllD; []ᵈ; _∷ᵈ_; ⊢Dσ; ⊢selF; ⊢con-fib; ⊢pay-σ; ⊢tag; subAllD )
open import DirectedHoTT.Lib.MethAt

private
  variable
    Γ Δ Θ : Cx
    c c₀ cₛ k : ℕ

------------------------------------------------------------------------
-- 1. THE FAMILY.
------------------------------------------------------------------------

-- the predecessor, under the step's two binders (`m`, the recursive fibre)
ρS : Ren (Δ ∙) (((Δ ∙) ∙) ∙)
ρS vz     = vs vz
ρS (vs x) = vs (vs (vs x))

DN : Cons (Δ ∙) c₀ → Cons (Δ ∙) cₛ → RTm Δ
DN C0 CS = lam (natrec (Dσ C0) (renTm ρS (Dσ CS)) (var vz))

-- ★ the family commutes with substitution (its lists under the index binder)
Dσ-sub : {Θ : Cx} (τ : Sub (Δ ∙) (Θ ∙)) (Cs : Cons (Δ ∙) c) → subTm τ (Dσ Cs) ≡ Dσ (subC τ Cs)
Dσ-sub τ Cs = cong (dσ (⌜Fin⌝ _)) (selF-sub τ Cs)

DN-sub : {Θ : Cx} (σ : Sub Δ Θ) (C0 : Cons (Δ ∙) c₀) (CS : Cons (Δ ∙) cₛ) →
         subTm σ (DN C0 CS) ≡ DN (subC (extS σ) C0) (subC (extS σ) CS)
DN-sub σ C0 CS =
  cong lam (cong₂ (λ a b → natrec a b (var vz)) (Dσ-sub (extS σ) C0)
                  (trans (trans (subTm-renTm (Dσ CS)) (trans (subTm-cong pt (Dσ CS)) (sym (renTm-subTm (Dσ CS)))))
                         (cong (renTm ρS) (Dσ-sub (extS σ) CS))))
  where
    pt : ∀ x → (extS (extS (extS σ)) ₛ∘ᵣ ρS) x ≡ (ρS ᵣ∘ₛ extS σ) x
    pt vz     = refl
    pt (vs y) = trans (trans (cong (renTm vs) (renTm-renTm (σ y))) (renTm-renTm (σ y))) (sym (renTm-renTm (σ y)))

elNat : El (⌜Nat⌝ {Δ}) ≅ᵀ Nat
elNat = credᵀ El-⌜Nat⌝

-- the index binder read as `Nat`, and the step's predecessor as an index
hS : {Γ : Ctx} {B : RTy ((⌊ Γ ⌋ ∙) ∙)} → Sub⊢ (Γ ▹ El ⌜Nat⌝) (((Γ ▹ El ⌜Nat⌝) ▹ Nat) ▹ B) ⟨ ρS ⟩ᵣ
hS here = ⊢conv (⊢var (there here)) (csymᵀ elNat)
hS (there {A = A₀} v) =
  ⊢-cast (trans (trans (cong (renTy vs) (renTy-renTy A₀)) (renTy-renTy A₀))
                (sym (trans (subTy-var ρS (renTy vs A₀)) (renTy-renTy A₀))))
         (⊢var (there (there (there v))))

⊢DN : {Γ : Ctx} {C0 : Cons (⌊ Γ ⌋ ∙) c₀} {CS : Cons (⌊ Γ ⌋ ∙) cₛ} →
      AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ C0 → AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CS → Γ ⊢ DN C0 CS ∷ DescF ⌜Nat⌝
⊢DN {Γ = Γ} {CS = CS} d0 dS =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢natrec (ty-Desc ⊢⌜Nat⌝) (⊢Dσ ⊢⌜Nat⌝ d0)
      (subst (λ t → (((Γ ▹ El ⌜Nat⌝) ▹ Nat) ▹ Desc ⌜Nat⌝) ⊢ t ∷ Desc ⌜Nat⌝) (subTm-var ρS (Dσ CS)) (sub-lemma (⊢Dσ ⊢⌜Nat⌝ dS) hS))
      (⊢conv (⊢var here) elNat))

------------------------------------------------------------------------
-- 2. ★ THE FIBRE COMPUTES at `0` and at `suc m`.
------------------------------------------------------------------------

fibN-z : (C0 : Cons (Δ ∙) c₀) (CS : Cons (Δ ∙) cₛ) →
         app (DN C0 CS) nzero ⟶* dσ (⌜Fin⌝ c₀) (selF (subC (single nzero) C0))
fibN-z {c₀ = c₀} C0 CS =
  step (β _ _) (step (natrec-zero _ _)
    (subst (λ X → dσ (⌜Fin⌝ c₀) (subTm (single nzero) (selF C0)) ⟶* dσ (⌜Fin⌝ c₀) X)
           (selF-sub (single nzero) C0) done))

-- the substitution a successor case leaves on a step-body: the predecessor
sucS : RTm Δ → Sub (Δ ∙) Δ
sucS m = single m

private
  step-flat : (m r : RTm Δ) (t : RTm (Δ ∙)) →
              subTm (single r) (subTm (extS (single m)) (subTm (extS (extS (single (nsuc m)))) (renTm ρS t)))
              ≡ subTm (single m) t
  step-flat m r t =
    trans (cong (λ z → subTm (single r) (subTm (extS (single m)) z)) (subTm-renTm t))
      (trans (cong (subTm (single r)) (subTm-subTm t))
        (trans (subTm-subTm t) (subTm-cong pt t)))
    where
      pt : ∀ x → (single r ∘ₛ (extS (single m) ∘ₛ (extS (extS (single (nsuc m))) ₛ∘ᵣ ρS))) x ≡ single m x
      pt vz     = wk-cancel-tm r m
      pt (vs x) = refl

fibN-s : (C0 : Cons (Δ ∙) c₀) (CS : Cons (Δ ∙) cₛ) (m : RTm Δ) →
         app (DN C0 CS) (nsuc m) ⟶* dσ (⌜Fin⌝ cₛ) (selF (subC (single m) CS))
fibN-s {cₛ = cₛ} C0 CS m =
  step (β _ _) (step (natrec-suc _ _ _)
    (subst (λ X → X ⟶* dσ (⌜Fin⌝ cₛ) (selF (subC (single m) CS))) (sym (step-flat m _ (Dσ CS)))
      (subst (λ X → dσ (⌜Fin⌝ cₛ) (subTm (single m) (selF CS)) ⟶* dσ (⌜Fin⌝ cₛ) X)
             (selF-sub (single m) CS) done)))

------------------------------------------------------------------------
-- 3. ★ CONSTRUCTORS at `0` and at `suc m`.
------------------------------------------------------------------------

⊢conN-z : {Γ : Ctx} {C0 : Cons (⌊ Γ ⌋ ∙) c₀} {CS : Cons (⌊ Γ ⌋ ∙) cₛ} {C : RTm (⌊ Γ ⌋ ∙)} {p : RTm ⌊ Γ ⌋} →
          AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ C0 → AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CS → Nth C0 k C →
          Γ ⊢ p ∷ El (dpay ⌜Nat⌝ (DN C0 CS) (subTm (single nzero) C)) →
          Γ ⊢ conₗ k p ∷ IMu ⌜Nat⌝ (DN C0 CS) nzero
⊢conN-z {C0 = C0} {CS} d0 dS nt dp =
  ⊢con-fib ⊢⌜Nat⌝ dD dz (fibN-z C0 CS)
    (⊢pay-σ ⊢⌜Nat⌝ dD (⊢selF ⊢⌜Nat⌝ (subAllD d0 dz))
            (⊢conv (⊢tag (nth-lt nt)) (csymᵀ (credᵀ El-⌜Fin⌝)))
            (⊢conv dp (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β (nth-sub (single nzero) nt))))))))
  where
    dD = ⊢DN d0 dS
    dz = ⊢conv ⊢nzero (csymᵀ elNat)

⊢conN-s : {Γ : Ctx} {C0 : Cons (⌊ Γ ⌋ ∙) c₀} {CS : Cons (⌊ Γ ⌋ ∙) cₛ} {C : RTm (⌊ Γ ⌋ ∙)} {m p : RTm ⌊ Γ ⌋} →
          AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ C0 → AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CS → Nth CS k C →
          Γ ⊢ m ∷ El ⌜Nat⌝ →
          Γ ⊢ p ∷ El (dpay ⌜Nat⌝ (DN C0 CS) (subTm (single m) C)) →
          Γ ⊢ conₗ k p ∷ IMu ⌜Nat⌝ (DN C0 CS) (nsuc m)
⊢conN-s {C0 = C0} {CS} {m = m} d0 dS nt dm dp =
  ⊢con-fib ⊢⌜Nat⌝ dD (⊢conv (⊢nsuc (⊢conv dm elNat)) (csymᵀ elNat)) (fibN-s C0 CS m)
    (⊢pay-σ ⊢⌜Nat⌝ dD (⊢selF ⊢⌜Nat⌝ (subAllD dS dm))
            (⊢conv (⊢tag (nth-lt nt)) (csymᵀ (credᵀ El-⌜Fin⌝)))
            (⊢conv dp (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β (nth-sub (single m) nt))))))))
  where
    dD = ⊢DN d0 dS

------------------------------------------------------------------------
-- 4. ★★ THE ONE METHOD: a `natrec`-case on the index.
------------------------------------------------------------------------

open import DirectedHoTT.Lib.Sorted using ( T₀; ⊢T₀ )

-- the successor case's index substitution
σS : Sub (Δ ∙) (Δ ∙)
σS vz     = nsuc (var vz)
σS (vs x) = var (vs x)

-- the two case types: the kernel's method body at `0` and at `suc m`
NT0 : RTm Δ → RTy ((Δ ∙) ∙) → RTy Δ
NT0 D M = subTy (single nzero) (T₀ ⌜Nat⌝ D M)

NTS : RTm Δ → RTy ((Δ ∙) ∙) → RTy (Δ ∙)
NTS D M = subTy σS (T₀ ⌜Nat⌝ D M)

methN : RTm Δ → RTm (Δ ∙) → RTm Δ
methN E0 ES = lam (natrec (renTm vs E0) (renTm ρS ES) (var vz))

private
  Π-cod : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} → Γ ⊢ty Π A B → (Γ ▹ A) ⊢ty B
  Π-cod (ty-Π _ d) = d

⊢methN : {Γ : Ctx} {D : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {E0 : RTm ⌊ Γ ⌋} {ES : RTm (⌊ Γ ⌋ ∙)} →
         Γ ⊢ D ∷ DescF ⌜Nat⌝ → motCtx Γ ⌜Nat⌝ D ⊢ty M →
         Γ ⊢ E0 ∷ NT0 D M → (Γ ▹ El ⌜Nat⌝) ⊢ ES ∷ NTS D M →
         Γ ⊢ methN E0 ES ∷ MethTy ⌜Nat⌝ D M
⊢methN {Γ = Γ} {D} {M} {E0} {ES} dD dM dE0 dES =
  subst (λ X → Γ ⊢ methN E0 ES ∷ X) (sym (MethTy-At ⌜Nat⌝ D M))
    (⊢lam (ty-El ⊢⌜Nat⌝) (⊢-cast eqP (⊢natrec dP dz ds (⊢conv (⊢var here) elNat))))
  where
    T = T₀ ⌜Nat⌝ D M
    Γ₁ = Γ ▹ El ⌜Nat⌝
    dT : Γ₁ ⊢ty T
    dT = ⊢T₀ ⊢⌜Nat⌝ dD dM
    ρP : Ren ⌊ Γ₁ ⌋ (⌊ Γ₁ ⌋ ∙)
    ρP vz     = vz
    ρP (vs y) = vs (vs y)
    hρP : Ren⊢ Γ₁ (Γ₁ ▹ El ⌜Nat⌝) ρP
    hρP here = here
    hρP (there {A = A₀} v) = ∋-cast (trans (renTy-renTy A₀) (sym (renTy-renTy A₀))) (there (there v))
    P = renTy ρP T
    dP : (Γ₁ ▹ Nat) ⊢ty P
    dP = conv-ctxᵀ elNat (ren-ty dT hρP)
    eqP : subTy (single (var vz)) P ≡ T
    eqP = trans (subTy-renTy T) (trans (subTy-cong pt T) (subTy-id T))
      where
        pt : ∀ x → (single (var vz) ₛ∘ᵣ ρP) x ≡ idₛ x
        pt vz     = refl
        pt (vs y) = refl
    dz : Γ₁ ⊢ renTm vs E0 ∷ subTy (single nzero) P
    dz = ⊢-cast (trans (renTy-subTy T) (trans (subTy-cong pt T) (sym (subTy-renTy T)))) (⊢wk dE0)
      where
        pt : ∀ x → (vs ᵣ∘ₛ single nzero) x ≡ (single nzero ₛ∘ᵣ ρP) x
        pt vz     = refl
        pt (vs y) = refl
    ds : ((Γ₁ ▹ Nat) ▹ P) ⊢ renTm ρS ES ∷ subTy nrs P
    ds = subst (λ t → ((Γ₁ ▹ Nat) ▹ P) ⊢ t ∷ subTy nrs P) (subTm-var ρS ES)
           (⊢-cast (trans (subTy-subTy T) (trans (subTy-cong pt T) (sym (subTy-renTy T)))) (sub-lemma dES hS))
      where
        pt : ∀ x → (⟨ ρS ⟩ᵣ ∘ₛ σS) x ≡ (nrs ₛ∘ᵣ ρP) x
        pt vz     = refl
        pt (vs y) = refl

private
  cong₆ : {A B C D E F G : Set} (g : A → B → C → D → E → F → G)
          {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {f f' : F} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f ≡ f' → g a b c d e f ≡ g a' b' c' d' e' f'
  cong₆ g refl refl refl refl refl refl = refl

  sr-flat : {Θ Ξ Ω : Cx} (σ : Sub Θ Ξ) (ρ : Ren Ω Θ) (ρ' : Ren Ω Ξ) →
            (∀ x → σ (ρ x) ≡ var (ρ' x)) → (t : RTm Ω) → subTm σ (renTm ρ t) ≡ renTm ρ' t
  sr-flat σ ρ ρ' h t = trans (subTm-renTm t) (trans (subTm-cong h t) (subTm-var ρ' t))

-- the case types, as methods at the index terms `0` and `suc m`
NT0-inst : (D : RTm Δ) (M : RTy ((Δ ∙) ∙)) →
           NT0 D M ≡ MethAt ⌜Nat⌝ D M nzero (app D nzero) (con (var (vs vz)))
NT0-inst D M =
  trans (MethAt-sub (single nzero) ⌜Nat⌝ (renTm vs D) (wk1M M) (var vz) (app (renTm vs D) (var vz)) (con (var (vs vz))))
        (cong₆ MethAt refl (wk-cancel-tm nzero D) Mc refl (cong₂ app (wk-cancel-tm nzero D) refl) refl)
  where
    Mc : subTy (extS (extS (single nzero))) (wk1M M) ≡ M
    Mc = trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-id M))
      where
        pt : ∀ x → (extS (extS (single nzero)) ₛ∘ᵣ extR (extR vs)) x ≡ idₛ x
        pt vz          = refl
        pt (vs vz)     = refl
        pt (vs (vs x)) = refl

NTS-inst : (D : RTm Δ) (M : RTy ((Δ ∙) ∙)) →
           NTS D M ≡ MethAt ⌜Nat⌝ (renTm vs D) (wk1M M) (nsuc (var vz)) (app (renTm vs D) (nsuc (var vz)))
                            (con (var (vs vz)))
NTS-inst D M =
  trans (MethAt-sub σS ⌜Nat⌝ (renTm vs D) (wk1M M) (var vz) (app (renTm vs D) (var vz)) (con (var (vs vz))))
        (cong₆ MethAt refl fl Mc refl (cong₂ app fl refl) refl)
  where
    fl = sr-flat σS vs vs (λ y → refl) D
    Mc : subTy (extS (extS σS)) (wk1M M) ≡ wk1M M
    Mc = trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-var (extR (extR vs)) M))
      where
        pt : ∀ x → (extS (extS σS) ₛ∘ᵣ extR (extR vs)) x ≡ ⟨ extR (extR vs) ⟩ᵣ x
        pt vz          = refl
        pt (vs vz)     = refl
        pt (vs (vs x)) = refl

-- the fibre of the WEAKENED family at `suc` of the fresh variable
fibN-s-wk : (C0 : Cons (Δ ∙) c₀) (CS : Cons (Δ ∙) cₛ) →
            app (renTm vs (DN C0 CS)) (nsuc (var vz)) ⟶* dσ (⌜Fin⌝ cₛ) (selF (subC (single (var vz) ₛ∘ᵣ extR vs) CS))
fibN-s-wk {cₛ = cₛ} C0 CS =
  step (β _ _) (step (natrec-suc _ _ _)
    (subst (λ X → X ⟶* dσ (⌜Fin⌝ cₛ) (selF (subC τ CS))) (sym flat)
      (subst (λ X → dσ (⌜Fin⌝ cₛ) (subTm τ (selF CS)) ⟶* dσ (⌜Fin⌝ cₛ) X) (selF-sub τ CS) done)))
  where
    τ = single (var vz) ₛ∘ᵣ extR vs
    t = Dσ CS
    r = natrec (subTm (single (nsuc (var vz))) (renTm (extR vs) (Dσ C0)))
               (subTm (extS (extS (single (nsuc (var vz))))) (renTm (extR (extR (extR vs))) (renTm ρS t))) (var vz)
    flat : subTm (single r) (subTm (extS (single (var vz)))
             (subTm (extS (extS (single (nsuc (var vz))))) (renTm (extR (extR (extR vs))) (renTm ρS t))))
           ≡ subTm τ t
    flat = trans (cong (λ z → subTm (single r) (subTm (extS (single (var vz))) (subTm (extS (extS (single (nsuc (var vz))))) z)))
                       (renTm-renTm t))
             (trans (cong (λ z → subTm (single r) (subTm (extS (single (var vz))) z)) (subTm-renTm t))
               (trans (cong (subTm (single r)) (subTm-subTm t))
                 (trans (subTm-subTm t) (subTm-cong pt t))))
      where
        pt : ∀ x → (single r ∘ₛ (extS (single (var vz)) ∘ₛ (extS (extS (single (nsuc (var vz)))) ₛ∘ᵣ (extR (extR (extR vs)) ∘ᵣ ρS)))) x
                   ≡ τ x
        pt vz     = refl
        pt (vs x) = refl

-- ★ the two cases, from one method per constructor at the case's index
⊢caseZ : {Γ : Ctx} {C0 : Cons (⌊ Γ ⌋ ∙) c₀} {CS : Cons (⌊ Γ ⌋ ∙) cₛ} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {ms : Cons ⌊ Γ ⌋ c₀} →
         AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ C0 → AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CS → motCtx Γ ⌜Nat⌝ (DN C0 CS) ⊢ty M →
         PerKAt Γ ⌜Nat⌝ (DN C0 CS) M nzero (selF (subC (single nzero) C0)) zero ms →
         Γ ⊢ methAt ms ∷ NT0 (DN C0 CS) M
⊢caseZ {C0 = C0} {CS} {M} d0 dS dM ps =
  ⊢-cast (sym (NT0-inst (DN C0 CS) M))
    (⊢conv (⊢methAt ⊢⌜Nat⌝ (⊢DN d0 dS) dM (⊢conv ⊢nzero (csymᵀ elNat))
                    (⊢selF ⊢⌜Nat⌝ (subAllD d0 (⊢conv ⊢nzero (csymᵀ elNat)))) (fibN-z C0 CS) ps)
           (csymᵀ (red→≅ᵀ (MethAt-monoᶜ (fibN-z C0 CS)))))

⊢caseS : {Γ : Ctx} {C0 : Cons (⌊ Γ ⌋ ∙) c₀} {CS : Cons (⌊ Γ ⌋ ∙) cₛ} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {ms : Cons (⌊ Γ ⌋ ∙) cₛ} →
         AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ C0 → AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CS → motCtx Γ ⌜Nat⌝ (DN C0 CS) ⊢ty M →
         PerKAt (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs (DN C0 CS)) (wk1M M) (nsuc (var vz))
                (selF (subC (single (var vz) ₛ∘ᵣ extR vs) CS)) zero ms →
         (Γ ▹ El ⌜Nat⌝) ⊢ methAt ms ∷ NTS (DN C0 CS) M
⊢caseS {Γ = Γ} {C0 = C0} {CS} {M} d0 dS dM ps =
  ⊢-cast (sym (NTS-inst (DN C0 CS) M))
    (⊢conv (⊢methAt ⊢⌜Nat⌝ (⊢wkD (⊢DN d0 dS)) (mot-ren there dM) dsm
                    (⊢selF ⊢⌜Nat⌝ (subAllDτ dS)) (fibN-s-wk C0 CS) ps)
           (csymᵀ (red→≅ᵀ (MethAt-monoᶜ (fibN-s-wk C0 CS)))))
  where
    dsm : (Γ ▹ El ⌜Nat⌝) ⊢ nsuc (var vz) ∷ El ⌜Nat⌝
    dsm = ⊢conv (⊢nsuc (⊢conv (⊢var here) elNat)) (csymᵀ elNat)
    τ = single (var vz) ₛ∘ᵣ extR vs
    hτ : Sub⊢ (Γ ▹ El ⌜Nat⌝) (Γ ▹ El ⌜Nat⌝) τ
    hτ here = ⊢var here
    hτ (there {A = A₀} v) = ⊢-cast (sym (trans (subTy-renTy A₀) (subTy-var vs A₀))) (⊢var (there v))
    subAllDτ : {c : ℕ} {Cs : Cons (⌊ Γ ⌋ ∙) c} → AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ Cs → AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ (subC τ Cs)
    subAllDτ []ᵈ = []ᵈ
    subAllDτ (d ∷ᵈ ds) = sub-lemma d hτ ∷ᵈ subAllDτ ds

------------------------------------------------------------------------
-- 5. ★ …AND IT COMPUTES.
------------------------------------------------------------------------

ιN-z : {D E0 q : RTm Δ} {ES : RTm (Δ ∙)} →
       ielim D nzero (methN E0 ES) (con q)
         ⟶* app (app E0 q) (dih D (methN E0 ES) (app D nzero) q)
ιN-z {D = D} {E0 = E0} {q = q} {ES = ES} =
  step (ι _ _ _ _)
   (step (ξ-appˡ (ξ-appˡ (β _ _)))
    (step (ξ-appˡ (ξ-appˡ (natrec-zero _ _)))
     (subst (λ X → app (app X q) h ⟶* app (app E0 q) h) (sym (wk-cancel-tm nzero E0)) done)))
  where h = dih D (methN E0 ES) (app D nzero) q

ιN-s : {D E0 m q : RTm Δ} {ES : RTm (Δ ∙)} →
       ielim D (nsuc m) (methN E0 ES) (con q)
         ⟶* app (app (subTm (single m) ES) q) (dih D (methN E0 ES) (app D (nsuc m)) q)
ιN-s {D = D} {E0} {m} {q} {ES} =
  step (ι _ _ _ _)
   (step (ξ-appˡ (ξ-appˡ (β _ _)))
    (step (ξ-appˡ (ξ-appˡ (natrec-suc _ _ _)))
     (subst (λ X → app (app X q) h ⟶* app (app (subTm (single m) ES) q) h) (sym flat) done)))
  where
    h = dih D (methN E0 ES) (app D (nsuc m)) q
    r = natrec (subTm (single (nsuc m)) (renTm vs E0)) (subTm (extS (extS (single (nsuc m)))) (renTm ρS ES)) m
    flat : subTm (single r) (subTm (extS (single m)) (subTm (extS (extS (single (nsuc m)))) (renTm ρS ES)))
           ≡ subTm (single m) ES
    flat = trans (cong (λ z → subTm (single r) (subTm (extS (single m)) z)) (subTm-renTm ES))
             (trans (cong (subTm (single r)) (subTm-subTm ES))
               (trans (subTm-subTm ES) (subTm-cong pt ES)))
      where
        pt : ∀ x → (single r ∘ₛ (extS (single m) ∘ₛ (extS (extS (single (nsuc m))) ₛ∘ᵣ ρS))) x ≡ single m x
        pt vz     = wk-cancel-tm r m
        pt (vs x) = refl

------------------------------------------------------------------------
-- 6. ★ ONE METHOD ENTRY of the successor case, read along its telescope
--    (`Lib/TelAt.HypAt`): constructor `k`'s body at the index `suc m`.
------------------------------------------------------------------------

open import DirectedHoTT.Lib.Tel using ( Tel; Tels; ⌜_⌝ᵗ; ⌜_⌝ₛ; NthT; nth-⌜⌝; AllOK; TelOK; ⊢tel; allD )
open import DirectedHoTT.Lib.TelAt using ( HypAt; ⊢methTσ; nth-OK )

-- the predecessor's substitution on the successor case's telescopes
τS : Sub (Δ ∙) (Δ ∙)
τS = single (var vz) ₛ∘ᵣ extR vs

entN : {Γ : Ctx} {C0 : Cons (⌊ Γ ⌋ ∙) c₀} {Ts : Tels (⌊ Γ ⌋ ∙) cₛ} {T : Tel (⌊ Γ ⌋ ∙)}
       {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {b : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)} →
       AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ C0 → AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ Ts →
       motCtx Γ ⌜Nat⌝ (DN C0 ⌜ Ts ⌝ₛ) ⊢ty M → NthT Ts k T →
       HypAt (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs (DN C0 ⌜ Ts ⌝ₛ)) (wk1M M) τS T
         ⊢ b ∷ subTy (atS (nsuc (var vz)) (conₗ k (var (vs vz)))) (wk1M M) →
       (app (selF (subC τS ⌜ Ts ⌝ₛ)) (tag k) ⟶* subTm τS ⌜ T ⌝ᵗ)
       × ((Γ ▹ El ⌜Nat⌝) ⊢ lam (lam b) ∷ MethKAt ⌜Nat⌝ (renTm vs (DN C0 ⌜ Ts ⌝ₛ)) (wk1M M) (nsuc (var vz))
                                                 (subTm τS ⌜ T ⌝ᵗ) k)
entN {Γ = Γ} {Ts = Ts} {T = T} d0 oks dM nt db =
  selF-β (nth-sub τS (nth-⌜⌝ nt)) ,
  ⊢methTσ {σ = τS} {T = T} ⊢⌜Nat⌝ (⊢wkD (⊢DN d0 (allD (⊢wk ⊢⌜Nat⌝) oks))) (mot-ren there dM)
          (sub-lemma (⊢tel (⊢wk ⊢⌜Nat⌝) (nth-OK oks nt)) hτ) db
  where
    hτ : Sub⊢ (Γ ▹ El ⌜Nat⌝) (Γ ▹ El ⌜Nat⌝) τS
    hτ here = ⊢var here
    hτ (there {A = A₀} v) = ⊢-cast (sym (trans (subTy-renTy A₀) (subTy-var vs A₀))) (⊢var (there v))

-- ★ …and ONE METHOD ENTRY of the ZERO case: constructor `k`'s body at `0`
entZ : {Γ : Ctx} {Ts : Tels (⌊ Γ ⌋ ∙) c₀} {CS : Cons (⌊ Γ ⌋ ∙) cₛ} {T : Tel (⌊ Γ ⌋ ∙)}
       {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {b : RTm ((⌊ Γ ⌋ ∙) ∙)} →
       AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ Ts → AllD (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ CS →
       motCtx Γ ⌜Nat⌝ (DN ⌜ Ts ⌝ₛ CS) ⊢ty M → NthT Ts k T →
       HypAt Γ ⌜Nat⌝ (DN ⌜ Ts ⌝ₛ CS) M (single nzero) T ⊢ b ∷ subTy (atS nzero (conₗ k (var (vs vz)))) M →
       (app (selF (subC (single nzero) ⌜ Ts ⌝ₛ)) (tag k) ⟶* subTm (single nzero) ⌜ T ⌝ᵗ)
       × (Γ ⊢ lam (lam b) ∷ MethKAt ⌜Nat⌝ (DN ⌜ Ts ⌝ₛ CS) M nzero (subTm (single nzero) ⌜ T ⌝ᵗ) k)
entZ {Γ = Γ} {Ts = Ts} {T = T} oks dS dM nt db =
  selF-β (nth-sub (single nzero) (nth-⌜⌝ nt)) ,
  ⊢methTσ {σ = single nzero} {T = T} ⊢⌜Nat⌝ (⊢DN (allD (⊢wk ⊢⌜Nat⌝) oks) dS) dM
          (sub-lemma (⊢tel (⊢wk ⊢⌜Nat⌝) (nth-OK oks nt)) (⊢single (⊢conv ⊢nzero (csymᵀ elNat)))) db
