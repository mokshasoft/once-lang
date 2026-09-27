------------------------------------------------------------------------
-- OCP-0009 · Lib — ★★★ THE GENERIC TRAVERSAL of a `Lib/Syn` syntax:
-- renaming and substitution are ONE theorem, instantiated twice.
--
-- A KIT (Allais et al.'s syntactic "Semantics") says what a variable
-- becomes: a family of VALUES over depths, how a value survives one more
-- binder (`WK`), the fresh variable as a value (`V0`), and how a value
-- stands for a variable NODE (`NODE`):
--
--              values      WK            V0         NODE
--   renaming   Fin e       fsuc          fzero      var v
--   subst      Tm e        rename by fsuc  var fzero  v
--
-- The traversal takes a term at depth `d`, a depth `e` and an environment
-- `Fin d → V e`, and rebuilds the term at `e`, lifting the environment
-- under every binder (`LIFT`, a case on the fibred `Fin`).
--
-- ★ EVERY OPERATION IS A CLOSED OBJECT-LEVEL FUNCTION whose parameters are
--   λ-bound VARIABLES, so every renaming of it computes definitionally
--   (`variable-is-the-cheapest-position`).  The kit's own terms are closed
--   too, and say so (`*-sub`, `refl` for a concrete kit).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.SynTrav where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; red→≅ᵀ; ⟶ᵀ*-IMu; ⟶ᵀ*-El; ⟶ᵀ*-Πˡ; ⟶*-pairˡ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; ren-lemma; sub-lemma; Sub⊢ )
open import DirectedHoTT.Metatheory.Premises using ( mot-ren )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; nth-z; nth-s; []ᵈ; selF; subC; tag; conₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.TelAt using ( ⊢payAt )
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.NatFib
open import DirectedHoTT.Lib.FinFam
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Sorted using ( unSortI )
open import DirectedHoTT.Lib.SynView
open import DirectedHoTT.Spec.Syntax using ( cong₄ )

private
  variable
    Γ Δ : Cx
    n : ℕ

------------------------------------------------------------------------
-- 1. THE KIT.
------------------------------------------------------------------------

-- a closed code family at a depth, and its decode
Vat : RTm Γ → RTm Γ → RTy Γ
Vat VF e = El (app VF e)

record Kit (n : ℕ) (sg : Sig n) : Set₁ where
  field
    vsort : ℕ
    VF    : {Γ : Cx} → RTm Γ       -- λ e. the code of the values at depth e
    WK    : {Γ : Cx} → RTm Γ       -- λ e v. v, one binder further
    V0    : {Γ : Cx} → RTm Γ       -- λ e. the fresh variable
    NODE  : {Γ : Cx} → RTm Γ       -- λ e v. the variable node v stands for
    VF-sub   : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (VF {Γ}) ≡ VF {Δ}
    WK-sub   : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (WK {Γ}) ≡ WK {Δ}
    V0-sub   : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (V0 {Γ}) ≡ V0 {Δ}
    NODE-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (NODE {Γ}) ≡ NODE {Δ}
    ⊢VF   : {Γ : Ctx} → Γ ⊢ VF ∷ Π (El ⌜Nat⌝) U
    ⊢WK   : {Γ : Ctx} → Γ ⊢ WK ∷ Π (El ⌜Nat⌝) (Π (Vat VF (var vz)) (Vat VF (nsuc (var (vs vz)))))
    ⊢V0   : {Γ : Ctx} → Γ ⊢ V0 ∷ Π (El ⌜Nat⌝) (Vat VF (nsuc (var vz)))
    ⊢NODE : {Γ : Ctx} → Γ ⊢ NODE ∷ Π (El ⌜Nat⌝) (Π (Vat VF (var vz)) (SK sg vsort (var (vs vz))))

------------------------------------------------------------------------
-- 2. ENVIRONMENTS, and LIFTING one under a binder.
------------------------------------------------------------------------

module _ {sg : Sig n} (ok : SigOK n sg) (κ : Kit n sg) where
  open Kit κ

  -- `Fin d → V e`
  Env : RTm Γ → RTm Γ → RTy Γ
  Env d e = Π (FinI d) (Vat VF (renTm vs e))

  -- the predecessor, as an index (the successor case's `m`)
  predT : RTm Γ → RTm Γ
  predT i = natrec nzero (var (vs vz)) i

  -- the lift's motive, at a target depth `e` two binders out:
  --   L(i, x) = Env (pred i) e → V (suc e)
  LM : RTm Γ → RTy ((Γ ∙) ∙)
  LM e = Π (Env (predT (var (vs vz))) (renTm vs (renTm vs e))) (Vat VF (nsuc (renTm vs (renTm vs (renTm vs e)))))

  -- the lift's methods at `suc m`: fzero ↦ V0 e ; fsuc y ↦ WK e (env y)
  --   (binders: m, payload, hypotheses, env)
  wk3 : RTm Γ → RTm (((Γ ∙) ∙) ∙)
  wk3 t = renTm vs (renTm vs (renTm vs t))

  wk4 : RTm Γ → RTm ((((Γ ∙) ∙) ∙) ∙)
  wk4 t = renTm vs (wk3 t)

  lz ls : RTm Γ → RTm (Γ ∙)
  lz e = lam (lam (lam (app V0 (wk4 e))))
  ls e = lam (lam (lam (app (app WK (wk4 e)) (app (var vz) (fst (var (vs (vs vz))))))))

  liftM : RTm Γ → RTm Γ
  liftM e = methN (methAt []) (methAt (lz e ∷ ls e ∷ []))

  -- ★ LIFT = λ e d env x. (case x of fzero ↦ V0 e ; fsuc y ↦ WK e (env y))
  LIFT : RTm Γ
  LIFT = lam (lam (lam (lam
           (app (ielim FinD (nsuc (var (vs (vs vz)))) (liftM (var (vs (vs (vs vz))))) (var vz)) (var (vs vz))))))

  -- the kit's code commutes with substitution, hence so do its decodes
  Vat-sub : (σ : Sub Γ Δ) (e : RTm Γ) → subTy σ (Vat VF e) ≡ Vat VF (subTm σ e)
  Vat-sub σ e = cong (λ X → El (app X (subTm σ e))) (VF-sub σ)

  Env-sub : (σ : Sub Γ Δ) (d e : RTm Γ) → subTy σ (Env d e) ≡ Env (subTm σ d) (subTm σ e)
  Env-sub σ d e =
    cong (Π (FinI (subTm σ d)))
         (trans (Vat-sub (extS σ) (renTm vs e)) (cong (Vat VF) (wk-sub σ e)))
    where open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )

  Env-ren : (ρ : Ren Γ Δ) (d e : RTm Γ) → renTy ρ (Env d e) ≡ Env (renTm ρ d) (renTm ρ e)
  Env-ren ρ d e = trans (sym (subTy-var ρ (Env d e)))
                    (trans (Env-sub ⟨ ρ ⟩ᵣ d e) (cong₂ Env (subTm-var ρ d) (subTm-var ρ e)))
    where open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )

  ⊢predT : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El ⌜Nat⌝ → Γ ⊢ predT i ∷ El ⌜Nat⌝
  ⊢predT di = ⊢natrec (ty-El ⊢⌜Nat⌝) (⊢conv ⊢nzero (csymᵀ elNat))
                      (⊢conv (⊢var (there here)) (csymᵀ elNat)) (⊢conv di elNat)

  ty-Env : {Γ : Ctx} {d e : RTm ⌊ Γ ⌋} → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ty Env d e
  ty-Env dd de = ty-Π (ty-IMu ⊢⌜Nat⌝ ⊢FinD dd) (ty-El (⊢app ⊢VF (⊢wk de)))

  ty-Vat : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ty Vat VF e
  ty-Vat de = ty-El (⊢app ⊢VF de)

  -- the lift's motive under any substitution of its two binders
  LM-sub : (e : RTm Γ) (τ : Sub ((Γ ∙) ∙) Δ) →
           subTy τ (LM e) ≡ Π (Env (predT (τ (vs vz))) (subTm τ (renTm vs (renTm vs e))))
                              (Vat VF (nsuc (subTm (extS τ) (renTm vs (renTm vs (renTm vs e))))))
  LM-sub e τ = cong₂ Π (Env-sub τ (predT (var (vs vz))) (renTm vs (renTm vs e)))
                       (Vat-sub (extS τ) (nsuc (renTm vs (renTm vs (renTm vs e)))))

  -- ★ the kit's terms, applied — the laws' casts confined here
  ⊢V0· : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ app V0 e ∷ Vat VF (nsuc e)
  ⊢V0· {e = e} de = ⊢-cast (Vat-sub (single e) (nsuc (var vz))) (⊢app ⊢V0 de)

  ⊢WK· : {Γ : Ctx} {e v : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ v ∷ Vat VF e →
         Γ ⊢ app (app WK e) v ∷ Vat VF (nsuc e)
  ⊢WK· {Γ = Γ} {e = e} {v = v} de dv =
    ⊢-cast (trans (Vat-sub (single v) (nsuc (renTm vs e))) (cong (λ z → Vat VF (nsuc z)) (wk-cancel-tm v e)))
      (⊢app (⊢-cast (cong₂ Π (Vat-sub (single e) (var vz)) (Vat-sub (extS (single e)) (nsuc (var (vs vz)))))
                    (⊢app ⊢WK de)) dv)
    where open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )

  ⊢NODE· : {Γ : Ctx} {e v : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ v ∷ Vat VF e →
           Γ ⊢ app (app NODE e) v ∷ SK sg vsort e
  ⊢NODE· {e = e} {v = v} de dv =
    ⊢-cast (trans (SK-sub (single v) sg vsort (renTm vs e)) (cong (SK sg vsort) (wk-cancel-tm v e)))
      (⊢app (⊢-cast (cong₂ Π (Vat-sub (single e) (var vz)) (SK-sub (extS (single e)) sg vsort (var (vs vz)))) (⊢app ⊢NODE de)) dv)
    where open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )

  ⊢Env· : {Γ : Ctx} {d e f x : RTm ⌊ Γ ⌋} → Γ ⊢ f ∷ Env d e → Γ ⊢ x ∷ FinI d → Γ ⊢ app f x ∷ Vat VF e
  ⊢Env· {e = e} {x = x} df dx =
    ⊢-cast (trans (Vat-sub (single x) (renTm vs e)) (cong (Vat VF) (wk-cancel-tm x e))) (⊢app df dx)
    where open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )

  private
    sr-flat : {Θ Ξ Ω : Cx} (σ : Sub Θ Ξ) (ρ : Ren Ω Θ) (ρ' : Ren Ω Ξ) →
              (∀ x → σ (ρ x) ≡ var (ρ' x)) → (t : RTm Ω) → subTm σ (renTm ρ t) ≡ renTm ρ' t
    sr-flat σ ρ ρ' h t = trans (subTm-renTm t) (trans (subTm-cong h t) (subTm-var ρ' t))
      where open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( subTm-var )

    rr2 : (t : RTm Γ) → renTm vs (renTm vs t) ≡ renTm (λ x → vs (vs x)) t
    rr2 t = renTm-renTm t

    rr3 : (t : RTm Γ) → wk3 t ≡ renTm (λ x → vs (vs (vs x))) t
    rr3 t = trans (cong (renTm vs) (renTm-renTm t)) (renTm-renTm t)

    rr4 : (t : RTm Γ) → wk4 t ≡ renTm (λ x → vs (vs (vs (vs x)))) t
    rr4 t = trans (cong (renTm vs) (rr3 t)) (renTm-renTm t)

  -- the lift's method type at constructor `k` of the successor case
  bodyTy : (e : RTm Γ) (k : ℕ) →
           subTy (atS (nsuc (var vz)) (conₗ k (var (vs vz)))) (wk1M (LM e))
           ≡ Π (Env (predT (nsuc (var (vs (vs vz))))) (wk3 e)) (Vat VF (nsuc (wk4 e)))
  bodyTy e k =
    trans (subTy-renTy (LM e))
      (trans (LM-sub e τ)
        (cong₂ (λ a b → Π (Env (predT (nsuc (var (vs (vs vz))))) a) (Vat VF (nsuc b)))
               (trans (trans (cong (subTm τ) (rr2 e)) (sr-flat τ _ (λ x → vs (vs (vs x))) (λ x → refl) e)) (sym (rr3 e)))
               (trans (trans (cong (subTm (extS τ)) (rr3 e)) (sr-flat (extS τ) _ (λ x → vs (vs (vs (vs x))))
                                                                      (λ x → refl) e)) (sym (rr4 e)))))
    where τ = atS (nsuc (var vz)) (conₗ k (var (vs vz))) ₛ∘ᵣ extR (extR vs)

  ⊢liftM : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ liftM e ∷ MethTy ⌜Nat⌝ FinD (LM e)
  ⊢liftM {Γ = Γ} {e = e} de =
    ⊢methN ⊢FinD dLM (⊢caseZ []ᵈ dS dLM []ₐ) (⊢caseS []ᵈ dS dLM perL)
    where
      dS = allD (⊢wk ⊢⌜Nat⌝) (FinOK {Γ})
      dLM : motCtx Γ ⌜Nat⌝ FinD ⊢ty LM e
      dLM = ty-Π (ty-Env (⊢predT (⊢var (there here))) (⊢wk (⊢wk de))) (ty-Vat (⊢isuc (⊢wk (⊢wk (⊢wk de)))))
      perL : PerKAt (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs FinD) (wk1M (LM e)) (nsuc (var vz))
                    (selF (subC τS ⌜ FinTs ⌝ₛ)) zero (lz e ∷ ls e ∷ [])
      perL = entN {Ts = FinTs} {T = fzeroT} []ᵈ FinOK dLM nthᵗ-z
               (⊢-cast (sym (bodyTy e zero))
                 (⊢lam (ty-Env (⊢predT (⊢isuc (⊢var (there (there here))))) (⊢wk (⊢wk (⊢wk de))))
                       (⊢V0· (⊢wk (⊢wk (⊢wk (⊢wk de)))))))
          ∷ₐ entN {Ts = FinTs} {T = fsucT} []ᵈ FinOK dLM (nthᵗ-s nthᵗ-z)
               (⊢-cast (sym (bodyTy e (suc zero)))
                 (⊢lam (ty-Env (⊢predT (⊢isuc (⊢var (there (there here))))) (⊢wk (⊢wk (⊢wk de))))
                       (⊢WK· (⊢wk (⊢wk (⊢wk (⊢wk de))))
                             (⊢Env· (⊢-cast (Env-ren vs _ _) (⊢var here))
                                    (⊢conv (⊢wk (⊢fst (⊢payAt {I = ⌜Nat⌝} {D = renTm vs FinD} {M = wk1M (LM e)}
                                                               {σ = τS} {T = fsucT})))
                                           (csymᵀ (credᵀ (ξ-IMuⁱ (natrec-suc _ _ _)))))))))
          ∷ₐ []ₐ

  -- ★ LIFT's type: an environment `Fin d → V e` lifted under one binder
  LIFTTy : RTy Γ
  LIFTTy = Π (El ⌜Nat⌝) (Π (El ⌜Nat⌝) (Π (Env (var vz) (var (vs vz)))
             (Env (nsuc (var (vs vz))) (nsuc (var (vs (vs vz)))))))

  ⊢LIFT : {Γ : Ctx} → Γ ⊢ LIFT ∷ LIFTTy
  ⊢LIFT {Γ} =
    ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-Env (⊢var here) (⊢var (there here)))
      (⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢isuc (⊢var (there here))))
        (⊢-cast (Vat-sub (single (var (vs vz))) (nsuc (renTm vs e5)))
          (⊢app (⊢-cast (trans (subTy-subTy (LM e5)) (LM-sub e5 _)) d1)
                (⊢conv (⊢-cast (trans (cong (renTy vs) (Env-ren vs (var vz) (var (vs vz))))
                                      (Env-ren vs (var (vs vz)) (var (vs (vs vz)))))
                               (⊢var (there here)))
                       (csymᵀ (credᵀ (ξ-Πˡ (ξ-IMuⁱ (natrec-suc _ _ _)))))))))))
    where
      e5 : RTm ((((⌊ Γ ⌋ ∙) ∙) ∙) ∙)
      e5 = var (vs (vs (vs vz)))
      de5 = ⊢var (there (there (there here)))
      d1 = ⊢ielim ⊢⌜Nat⌝ ⊢FinD
             (ty-Π (ty-Env (⊢predT (⊢var (there here))) (⊢wk (⊢wk de5))) (ty-Vat (⊢isuc (⊢wk (⊢wk (⊢wk de5))))))
             (⊢liftM de5) (⊢isuc (⊢var (there (there here)))) (⊢var here)

  ------------------------------------------------------------------------
  -- 3. LIFTING UNDER k BINDERS.
  ------------------------------------------------------------------------

  private
    wkc : (a t : RTm Γ) → subTm (single a) (renTm vs t) ≡ t
    wkc = wk-cancel-tm
      where open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )

    -- the two-binder instantiation of a twice-weakened term
    wkc2 : (a b t : RTm Γ) → subTm (single a) (subTm (extS (single b)) (renTm vs (renTm vs t))) ≡ t
    wkc2 a b t = trans (cong (subTm (single a)) (trans (wk-sub (single b) (renTm vs t)) (cong (renTm vs) (wkc b t))))
                       (wkc a t)
      where open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )

  ⊢LIFT· : {Γ : Ctx} {e d f : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ f ∷ Env d e →
           Γ ⊢ app (app (app LIFT e) d) f ∷ Env (nsuc d) (nsuc e)
  ⊢LIFT· {e = e} {d} {f} de dd df =
    ⊢-cast eqC (⊢app (⊢app (⊢app ⊢LIFT de) dd) (⊢-cast (sym eqD) df))
    where
      eqD : subTy (single d) (subTy (extS (single e)) (Env (var vz) (var (vs vz)))) ≡ Env d e
      eqD = trans (cong (subTy (single d)) (Env-sub (extS (single e)) (var vz) (var (vs vz))))
                  (trans (Env-sub (single d) (var vz) (renTm vs e)) (cong (Env d) (wkc d e)))
      eqC : subTy (single f) (subTy (extS (single d)) (subTy (extS (extS (single e)))
              (Env (nsuc (var (vs vz))) (nsuc (var (vs (vs vz)))))))
            ≡ Env (nsuc d) (nsuc e)
      eqC = trans (cong (λ z → subTy (single f) (subTy (extS (single d)) z))
                        (Env-sub (extS (extS (single e))) (nsuc (var (vs vz))) (nsuc (var (vs (vs vz))))))
            (trans (cong (subTy (single f)) (Env-sub (extS (single d)) (nsuc (var (vs vz))) (nsuc (renTm vs (renTm vs e)))))
            (trans (Env-sub (single f) (nsuc (renTm vs d)) (nsuc (subTm (extS (single d)) (renTm vs (renTm vs e)))))
                   (cong₂ (λ a b → Env (nsuc a) (nsuc b)) (wkc f d) (wkc2 f d e))))

  LIFTS : ℕ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  LIFTS zero    e d f = f
  LIFTS (suc k) e d f = app (app (app LIFT (nsucs k e)) (nsucs k d)) (LIFTS k e d f)

  ⊢LIFTS : {Γ : Ctx} (k : ℕ) {e d f : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ d ∷ El ⌜Nat⌝ →
           Γ ⊢ f ∷ Env d e → Γ ⊢ LIFTS k e d f ∷ Env (nsucs k d) (nsucs k e)
  ⊢LIFTS zero    de dd df = df
  ⊢LIFTS (suc k) de dd df = ⊢LIFT· (⊢nsucs k de) (⊢nsucs k dd) (⊢LIFTS k de dd df)

  ------------------------------------------------------------------------
  -- 4. ★ THE TRAVERSAL'S MOTIVE:  M(i, t) = ∀ e. Env (snd i) e → Syn (fst i) e
  ------------------------------------------------------------------------

  TM : RTy ((Γ ∙) ∙)
  TM = Π (El ⌜Nat⌝) (Π (Env (snd (var (vs (vs vz)))) (var vz))
                       (IMu (SI n) (SD sg) (pair (fst (var (vs (vs (vs vz))))) (var (vs vz)))))

  ⊢TM : {Γ : Ctx} → motCtx Γ (SI n) (SD sg) ⊢ty TM
  ⊢TM = ty-Π (ty-El ⊢⌜Nat⌝)
          (ty-Π (ty-Env (⊢depth (⊢var (there (there here)))) (⊢var here))
                (ty-IMu ⊢SI (⊢SD ok) (⊢conv (⊢pair (ty-El ⊢⌜Nat⌝) (⊢fst (unSortI (⊢var (there (there (there here))))))
                                                   (⊢var (there here)))
                                            (csymᵀ (credᵀ (El-⌜Σ⌝ _ _))))))

  private
    wkS : (σ : Sub Γ Δ) (t : RTm Γ) → subTm (extS σ) (renTm vs t) ≡ renTm vs (subTm σ t)
    wkS = wk-sub
      where open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )

    -- three binders instantiated back: a thrice-weakened term
    wkc3 : (v e t J : RTm Γ) →
           subTm (single v) (subTm (extS (single e)) (subTm (extS (extS (single t))) (renTm vs (renTm vs (renTm vs J))))) ≡ J
    wkc3 v e t J =
      trans (cong (λ z → subTm (single v) (subTm (extS (single e)) z))
                  (trans (wkS (extS (single t)) (renTm vs (renTm vs J)))
                         (cong (renTm vs) (trans (wkS (single t) (renTm vs J)) (cong (renTm vs) (wkc t J))))))
            (wkc2 v e J)

  -- ★ a hypothesis at the traversal's motive, applied to a depth and an
  --   environment at its index
  ⊢TM· : {Γ : Ctx} {J t f e v : RTm ⌊ Γ ⌋} →
         Γ ⊢ f ∷ iinst J t TM → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ v ∷ Env (snd J) e →
         Γ ⊢ app (app f e) v ∷ IMu (SI n) (SD sg) (pair (fst J) e)
  ⊢TM· {J = J} {t} {f} {e} {v} df de dv =
    ⊢-cast eqR (⊢app (⊢app df de) (⊢-cast (sym eqA) dv))
    where
      eqA : subTy (single e) (subTy (extS (single t)) (subTy (extS (extS (single J))) (Env (snd (var (vs (vs vz)))) (var vz))))
            ≡ Env (snd J) e
      eqA = trans (cong (λ z → subTy (single e) (subTy (extS (single t)) z))
                        (Env-sub (extS (extS (single J))) (snd (var (vs (vs vz)))) (var vz)))
            (trans (cong (subTy (single e)) (Env-sub (extS (single t)) (snd (renTm vs (renTm vs J))) (var vz)))
            (trans (Env-sub (single e) (snd (subTm (extS (single t)) (renTm vs (renTm vs J)))) (var vz))
                   (cong (λ z → Env (snd z) e) (wkc2 e t J))))
      eqR : subTy (single v) (subTy (extS (single e)) (subTy (extS (extS (single t)))
              (subTy (extS (extS (extS (single J)))) (IMu (SI n) (SD sg) (pair (fst (var (vs (vs (vs vz))))) (var (vs vz)))))))
            ≡ IMu (SI n) (SD sg) (pair (fst J) e)
      eqR = cong₂ (λ D j → IMu (SI n) D j)
              (trans (cong (λ z → subTm (single v) (subTm (extS (single e)) (subTm (extS (extS (single t))) z)))
                           (SD-sub (extS (extS (extS (single J)))) sg))
                (trans (cong (λ z → subTm (single v) (subTm (extS (single e)) z)) (SD-sub (extS (extS (single t))) sg))
                  (trans (cong (subTm (single v)) (SD-sub (extS (single e)) sg)) (SD-sub (single v) sg))))
              (cong₂ pair (cong fst (wkc3 v e t J)) (wkc v e))

  ------------------------------------------------------------------------
  -- 5. ★★ ONE NODE, generically: the payload rebuilt field by field — a
  --    subterm under `k` binders is its hypothesis at depth `k + e` with
  --    the environment lifted `k` times; a natural is copied.
  ------------------------------------------------------------------------

  tpay : Shape → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  tpay []ʰ             p h e f d = unit
  tpay (rec s k ∷ʰ sh) p h e f d = pair (app (app (fst h) (nsucs k e)) (LIFTS k e d f)) (tpay sh (snd p) (snd h) e f d)
  tpay (nat ∷ʰ sh)     p h e f d = pair (fst p) (tpay sh (snd p) h e f d)
  tpay vʰ              p h e f d = unit

  private
    M-cancel : (a : RTm Γ) (M : RTy ((Γ ∙) ∙)) → subTy (extS (extS (single a))) (renTy (extR (extR vs)) M) ≡ M
    M-cancel a M = trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-id M))
      where
        pt : ∀ x → (extS (extS (single a)) ₛ∘ᵣ extR (extR vs)) x ≡ idₛ x
        pt vz          = refl
        pt (vs vz)     = refl
        pt (vs (vs x)) = refl

  -- a FIELDS shape (not the variable), well-formed
  data FOK : Shape → Set where
    []ᶠ  : FOK []ʰ
    _∷ᶠ_ : {fl : Fld} {sh : Shape} → FldOK n fl → FOK sh → FOK (fl ∷ʰ sh)

  ⊢tpay : {Γ : Ctx} {sh : Shape} {i p h e f d : RTm ⌊ Γ ⌋} → FOK sh →
          Γ ⊢ p ∷ PayV sh i (SI n) (SD sg) → Γ ⊢ h ∷ IhV sh i (SD sg) TM p →
          Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ d ∷ El ⌜Nat⌝ → snd i ⟶* d → Γ ⊢ f ∷ Env d e →
          Args Γ n (SD sg) e sh (tpay sh p h e f d)
  ⊢tpay []ᶠ dp dh de dd r df = a[]
  ⊢tpay {Γ = Γ} {sh = rec s k ∷ʰ sh} {i} {p} {h} {e} {f} {d} (ok-rec lt ∷ᶠ ok) dp dh de dd r df =
    a-rec (⊢conv (⊢TM· (⊢fst dh) (⊢nsucs k de)
                       (⊢conv (⊢LIFTS k de dd df)
                              (csymᵀ (red→≅ᵀ (⟶ᵀ*-Πˡ (⟶ᵀ*-IMu (step (βsnd _ _) (⟶*-nsucs k r))))))))
                 (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairˡ (step (βfst _ _) done)))))
          (⊢tpay ok dp' dh' de dd r df)
    where
      dp' : Γ ⊢ snd p ∷ PayV sh i (SI n) (SD sg)
      dp' = ⊢-cast (trans (PayV-sub (single (fst p)) sh (renTm vs i) (renTm vs (SI n)) (renTm vs (SD sg)))
                          (cong₂ (λ a b → PayV sh a (SI n) b) (wkc (fst p) i) (wkc (fst p) (SD sg))))
                   (⊢snd dp)
      dh' : Γ ⊢ snd h ∷ IhV sh i (SD sg) TM (snd p)
      dh' = ⊢-cast (trans (IhV-sub (single (fst h)) sh (renTm vs i) (renTm vs (SD sg)) (renTy (extR (extR vs)) TM)
                                   (snd (renTm vs p)))
                          (cong₄ (IhV sh) (wkc (fst h) i) (wkc (fst h) (SD sg)) (M-cancel (fst h) TM)
                                 (cong snd (wkc (fst h) p))))
                   (⊢snd dh)
  ⊢tpay {Γ = Γ} {sh = nat ∷ʰ sh} {i} {p} {h} (ok-nat ∷ᶠ ok) dp dh de dd r df =
    a-nat (⊢fst dp) (⊢tpay ok dp' dh de dd r df)
    where
      dp' : Γ ⊢ snd p ∷ PayV sh i (SI n) (SD sg)
      dp' = ⊢-cast (trans (PayV-sub (single (fst p)) sh (renTm vs i) (renTm vs (SI n)) (renTm vs (SD sg)))
                          (cong₂ (λ a b → PayV sh a (SI n) b) (wkc (fst p) i) (wkc (fst p) (SD sg))))
                   (⊢snd dp)
