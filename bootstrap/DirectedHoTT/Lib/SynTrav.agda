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
--   (`variable-is-the-cheapest-position`).  The kit's value code is closed
--   too, and says so (`VF-sub`, `refl` for a concrete kit).
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
open import DirectedHoTT.Metatheory.Premises using ( mot-ren; ⊢wkD )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; nth-z; nth-s; []ᵈ; selF; subC; tag; conₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.TelAt using ( ⊢payAt )
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.NatFib
open import DirectedHoTT.Lib.FinFam
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.Sorted using ( unSortI; σₛ; ιₛ; ⊢ιₛ; PerS; []ₚ; _∷ₚ_; SortT; ⊢sortMeth; ⊢methₛ; NthS; nthˢ-z; nthˢ-s )
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
    ⊢VF   : {Γ : Ctx} → Γ ⊢ VF ∷ Π (El ⌜Nat⌝) U
    ⊢WK   : {Γ : Ctx} → Γ ⊢ WK ∷ Π (El ⌜Nat⌝) (Π (Vat VF (var vz)) (Vat VF (nsuc (var (vs vz)))))
    ⊢V0   : {Γ : Ctx} → Γ ⊢ V0 ∷ Π (El ⌜Nat⌝) (Vat VF (nsuc (var vz)))
    ⊢NODE : {Γ : Ctx} → Γ ⊢ NODE ∷ Π (El ⌜Nat⌝) (Π (Vat VF (var vz)) (SK sg vsort (var (vs vz))))

------------------------------------------------------------------------
-- 2. ENVIRONMENTS, and LIFTING one under a binder.
------------------------------------------------------------------------

module Trav {sg : Sig n} (ok : SigOK n sg) (κ : Kit n sg) where
  open Kit κ

  -- `Fin d → V e`
  Env : RTm Γ → RTm Γ → RTy Γ
  Env d e = Π (FinI d) (Vat VF (renTm vs e))

  -- the predecessor, as an index (the successor case's `m`)
  predT : RTm Γ → RTm Γ
  predT i = natrec nzero (var (vs vz)) i

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

  Vat-ren : (ρ : Ren Γ Δ) (e : RTm Γ) → renTy ρ (Vat VF e) ≡ Vat VF (renTm ρ e)
  Vat-ren ρ e = trans (sym (subTy-var ρ (Vat VF e))) (trans (Vat-sub ⟨ ρ ⟩ᵣ e) (cong (Vat VF) (subTm-var ρ e)))
    where open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )

  ⊢predT : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El ⌜Nat⌝ → Γ ⊢ predT i ∷ El ⌜Nat⌝
  ⊢predT di = ⊢natrec (ty-El ⊢⌜Nat⌝) (⊢conv ⊢nzero (csymᵀ elNat))
                      (⊢conv (⊢var (there here)) (csymᵀ elNat)) (⊢conv di elNat)

  ty-Env : {Γ : Ctx} {d e : RTm ⌊ Γ ⌋} → Γ ⊢ d ∷ El ⌜Nat⌝ → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ty Env d e
  ty-Env dd de = ty-Π (ty-IMu ⊢⌜Nat⌝ ⊢FinD dd) (ty-El (⊢app ⊢VF (⊢wk de)))

  ty-Vat : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ty Vat VF e
  ty-Vat de = ty-El (⊢app ⊢VF de)

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
    wkc : (a t : RTm Γ) → subTm (single a) (renTm vs t) ≡ t
    wkc = wk-cancel-tm
      where open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )

    -- the two-binder instantiation of a twice-weakened term
    wkc2 : (a b t : RTm Γ) → subTm (single a) (subTm (extS (single b)) (renTm vs (renTm vs t))) ≡ t
    wkc2 a b t = trans (cong (subTm (single a)) (trans (wk-sub (single b) (renTm vs t)) (cong (renTm vs) (wkc b t))))
                       (wkc a t)
      where open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )

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

  -- a value, one binder further out
  ⊢wkV : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {e t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Vat VF e → (Γ ▹ B) ⊢ renTm vs t ∷ Vat VF (renTm vs e)
  ⊢wkV {e = e} dt = ⊢-cast (Vat-ren vs e) (⊢wk dt)

  hereV : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → (Γ ▹ Vat VF e) ⊢ var vz ∷ Vat VF (renTm vs e)
  hereV {e = e} = ⊢-cast (Vat-ren vs e) (⊢var here)

  ⊢wkE : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {d e t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Env d e → (Γ ▹ B) ⊢ renTm vs t ∷ Env (renTm vs d) (renTm vs e)
  ⊢wkE {d = d} {e} dt = ⊢-cast (Env-ren vs d e) (⊢wk dt)

  hereE : {Γ : Ctx} {d e : RTm ⌊ Γ ⌋} → (Γ ▹ Env d e) ⊢ var vz ∷ Env (renTm vs d) (renTm vs e)
  hereE {d = d} {e} = ⊢-cast (Env-ren vs d e) (⊢var here)

  ------------------------------------------------------------------------
  -- ★ CONS — the σ-calculus's one primitive, `(ρ , u)`:
  --
  --     CONS e d u ρ x = case x of fzero ↦ u ; fsuc y ↦ ρ y
  --
  --   `LIFT` and `single` are its instances.  The motive is the convoy
  --   `Env (pred i) e → V e` (the case's index is not `d`); `e` and `u`
  --   ride free in it — λ-bound variables of the closed `CONS`.
  --   (Quantifying them INSIDE the motive instead costs: measured, the
  --   module went from 42 s to an OOM at 5.5 GB.)
  ------------------------------------------------------------------------

  wk3 : RTm Γ → RTm (((Γ ∙) ∙) ∙)
  wk3 t = renTm vs (renTm vs (renTm vs t))

  wk4 : RTm Γ → RTm ((((Γ ∙) ∙) ∙) ∙)
  wk4 t = renTm vs (wk3 t)

  -- C(i, x) = Env (pred i) e → V e, at a target depth `e` two binders out
  CM : RTm Γ → RTy ((Γ ∙) ∙)
  CM e = Π (Env (predT (var (vs vz))) (renTm vs (renTm vs e))) (Vat VF (wk3 e))

  CM-sub : (e : RTm Γ) (τ : Sub ((Γ ∙) ∙) Δ) →
           subTy τ (CM e) ≡ Π (Env (predT (τ (vs vz))) (subTm τ (renTm vs (renTm vs e)))) (Vat VF (subTm (extS τ) (wk3 e)))
  CM-sub e τ = cong₂ Π (Env-sub τ (predT (var (vs vz))) (renTm vs (renTm vs e))) (Vat-sub (extS τ) (wk3 e))

  ⊢CM : {Γ : Ctx} {e : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → motCtx Γ ⌜Nat⌝ FinD ⊢ty CM e
  ⊢CM de = ty-Π (ty-Env (⊢predT (⊢var (there here))) (⊢wk (⊢wk de))) (ty-Vat (⊢wk (⊢wk (⊢wk de))))

  -- at `suc m` (binders: m, payload, hypotheses, ρ)
  cz : RTm Γ → RTm (Γ ∙)
  cz u = lam (lam (lam (wk4 u)))

  cs : RTm (Γ ∙)
  cs = lam (lam (lam (app (var vz) (fst (var (vs (vs vz)))))))

  consM : RTm Γ → RTm Γ
  consM u = methN (methAt []) (methAt (cz u ∷ cs ∷ []))

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

    -- the method type at constructor `k` of the successor case
    bodyTy : (e : RTm Γ) (k : ℕ) →
             subTy (atS (nsuc (var vz)) (conₗ k (var (vs vz)))) (wk1M (CM e))
             ≡ Π (Env (predT (nsuc (var (vs (vs vz))))) (wk3 e)) (Vat VF (wk4 e))
    bodyTy e k =
      trans (subTy-renTy (CM e))
        (trans (CM-sub e τ)
          (cong₂ (λ a b → Π (Env (predT (nsuc (var (vs (vs vz))))) a) (Vat VF b))
                 (trans (trans (cong (subTm τ) (rr2 e)) (sr-flat τ _ (λ x → vs (vs (vs x))) (λ x → refl) e)) (sym (rr3 e)))
                 (trans (trans (cong (subTm (extS τ)) (rr3 e)) (sr-flat (extS τ) _ (λ x → vs (vs (vs (vs x))))
                                                                        (λ x → refl) e)) (sym (rr4 e)))))
      where τ = atS (nsuc (var vz)) (conₗ k (var (vs vz))) ₛ∘ᵣ extR (extR vs)

  ⊢consM : {Γ : Ctx} {e u : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ u ∷ Vat VF e →
           Γ ⊢ consM u ∷ MethTy ⌜Nat⌝ FinD (CM e)
  ⊢consM {Γ = Γ} {e = e} {u = u} de du =
    ⊢methN ⊢FinD (⊢CM de) (⊢caseZ []ᵈ dS (⊢CM de) []ₐ) (⊢caseS []ᵈ dS (⊢CM de) perC)
    where
      dS = allD (⊢wk ⊢⌜Nat⌝) (FinOK {Γ})
      perC : PerKAt (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs FinD) (wk1M (CM e)) (nsuc (var vz))
                    (selF (subC τS ⌜ FinTs ⌝ₛ)) zero (cz u ∷ cs ∷ [])
      perC = entN {Ts = FinTs} {T = fzeroT} []ᵈ FinOK (⊢CM de) nthᵗ-z
               (⊢-cast (sym (bodyTy e zero))
                 (⊢lam (ty-Env (⊢predT (⊢isuc (⊢var (there (there here))))) (⊢wk (⊢wk (⊢wk de))))
                       (⊢wkV (⊢wkV (⊢wkV (⊢wkV du))))))
          ∷ₐ entN {Ts = FinTs} {T = fsucT} []ᵈ FinOK (⊢CM de) (nthᵗ-s nthᵗ-z)
               (⊢-cast (sym (bodyTy e (suc zero)))
                 (⊢lam (ty-Env (⊢predT (⊢isuc (⊢var (there (there here))))) (⊢wk (⊢wk (⊢wk de))))
                       (⊢Env· hereE
                              (⊢conv (⊢wk (⊢fst (⊢payAt {I = ⌜Nat⌝} {D = renTm vs FinD} {M = wk1M (CM e)}
                                                         {σ = τS} {T = fsucT})))
                                     (csymᵀ (credᵀ (ξ-IMuⁱ (natrec-suc _ _ _))))))))
          ∷ₐ []ₐ

  -- ★ CONS = λ e d u ρ x. (case x) ρ
  CONS : RTm Γ
  CONS = lam (lam (lam (lam (lam
           (app (ielim FinD (nsuc (var (vs (vs (vs vz))))) (consM (var (vs (vs vz)))) (var vz)) (var (vs vz)))))))

  CONSTy : RTy Γ
  CONSTy = Π (El ⌜Nat⌝) (Π (El ⌜Nat⌝) (Π (Vat VF (var (vs vz))) (Π (Env (var (vs vz)) (var (vs (vs vz))))
             (Env (nsuc (var (vs (vs vz)))) (var (vs (vs (vs vz))))))))

  -- the body of CONS, in its five binders (e, d, u, ρ, x)
  module _ {Γ : Ctx} where
    private
      Γ5 : Ctx
      Γ5 = ((((Γ ▹ El ⌜Nat⌝) ▹ El ⌜Nat⌝) ▹ Vat VF (var (vs vz))) ▹ Env (var (vs vz)) (var (vs (vs vz))))
           ▹ FinI (nsuc (var (vs (vs vz))))
      e5 d5 u5 : RTm ⌊ Γ5 ⌋
      e5 = var (vs (vs (vs (vs vz))))
      d5 = var (vs (vs (vs vz)))
      u5 = var (vs (vs vz))
      de5 : Γ5 ⊢ e5 ∷ El ⌜Nat⌝
      de5 = ⊢var (there (there (there (there here))))
      du5 : Γ5 ⊢ u5 ∷ Vat VF e5
      du5 = ⊢wkV (⊢wkV hereV)
      τ5 : Sub ((⌊ Γ5 ⌋ ∙) ∙) ⌊ Γ5 ⌋
      τ5 = single (var vz) ∘ₛ extS (single (nsuc d5))
      d1 : Γ5 ⊢ ielim FinD (nsuc d5) (consM u5) (var vz) ∷ iinst (nsuc d5) (var vz) (CM e5)
      d1 = ⊢ielim {Γ5} {⌜Nat⌝} {FinD} {CM e5} {consM u5} {nsuc d5} {var vz}
                  ⊢⌜Nat⌝ ⊢FinD (⊢CM {Γ5} {e5} de5) (⊢consM {Γ5} {e5} {u5} de5 du5) (⊢isuc (⊢var (there (there (there here))))) (⊢var here)
      eq1 : iinst (nsuc d5) (var vz) (CM e5) ≡ Π (Env (predT (nsuc d5)) e5) (Vat VF (renTm vs e5))
      eq1 = trans {x = iinst (nsuc d5) (var vz) (CM e5)} {y = subTy (single (var vz) ∘ₛ extS (single (nsuc d5))) (CM e5)}
                  {z = Π (Env (predT (nsuc d5)) e5) (Vat VF (renTm vs e5))}
                  (subTy-subTy {τ = single (var vz)} {σ = extS (single (nsuc d5))} (CM e5))
                  (CM-sub e5 (single (var vz) ∘ₛ extS (single (nsuc d5))))
      d2 : Γ5 ⊢ ielim FinD (nsuc d5) (consM u5) (var vz) ∷ Π (Env (predT (nsuc d5)) e5) (Vat VF (renTm vs e5))
      d2 = ⊢-cast {Γ5} {ielim FinD (nsuc d5) (consM u5) (var vz)} {iinst (nsuc d5) (var vz) (CM e5)}
                  {Π (Env (predT (nsuc d5)) e5) (Vat VF (renTm vs e5))} eq1 d1
      denv : Γ5 ⊢ var (vs vz) ∷ Env (predT (nsuc d5)) e5
      denv = ⊢conv {Γ5} {var (vs vz)} {Env d5 e5} {Env (predT (nsuc d5)) e5}
                   (⊢wkE hereE) (csymᵀ (credᵀ (ξ-Πˡ (ξ-IMuⁱ (natrec-suc nzero (var (vs vz)) d5)))))
      body : Γ5 ⊢ app (ielim FinD (nsuc d5) (consM u5) (var vz)) (var (vs vz)) ∷ Vat VF e5
      bapp : Γ5 ⊢ app (ielim FinD (nsuc d5) (consM u5) (var vz)) (var (vs vz)) ∷ subTy (single (var (vs vz))) (Vat VF (renTm vs e5))
      bapp = ⊢app {Γ5} {Env (predT (nsuc d5)) e5} {Vat VF (renTm vs e5)} {ielim FinD (nsuc d5) (consM u5) (var vz)} {var (vs vz)} d2 denv
      beq : subTy (single (var (vs vz))) (Vat VF (renTm vs e5)) ≡ Vat VF e5
      beq = Vat-sub (single (var (vs vz))) (renTm vs e5)
      body = ⊢-cast {Γ5} {app (ielim FinD (nsuc d5) (consM u5) (var vz)) (var (vs vz))} beq bapp

    ⊢CONS : Γ ⊢ CONS ∷ CONSTy
    ⊢CONS = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-Vat (⊢var (there here)))
              (⊢lam (ty-Env (⊢var (there here)) (⊢var (there (there here))))
                (⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢isuc (⊢var (there (there here))))) body))))

  -- ★ CONS applied: `(ρ , u) : Env (suc d) e`
  ⊢CONS· : {Γ : Ctx} {e d u f : RTm ⌊ Γ ⌋} → Γ ⊢ e ∷ El ⌜Nat⌝ → Γ ⊢ d ∷ El ⌜Nat⌝ →
           Γ ⊢ u ∷ Vat VF e → Γ ⊢ f ∷ Env d e → Γ ⊢ app (app (app (app CONS e) d) u) f ∷ Env (nsuc d) e
  ⊢CONS· {Γ} {e} {d} {u} {f} de dd du df = ⊢-cast eqC f4
    where
      R : RTy (((⌊ Γ ⌋ ∙) ∙) ∙)
      R = Π (Env (var (vs vz)) (var (vs (vs vz)))) (Env (nsuc (var (vs (vs vz)))) (var (vs (vs (vs vz)))))
      eqU : subTy (single d) (subTy (extS (single e)) (Π (Vat VF (var (vs vz))) R))
            ≡ Π (Vat VF e) (subTy (extS (single d)) (subTy (extS (extS (single e))) R))
      eqU = cong (λ X → Π X (subTy (extS (single d)) (subTy (extS (extS (single e))) R)))
                 (trans (cong (subTy (single d)) (Vat-sub (extS (single e)) (var (vs vz))))
                        (trans (Vat-sub (single d) (renTm vs e)) (cong (Vat VF) (wkc d e))))
      eqD : subTy (single u) (subTy (extS (single d)) (subTy (extS (extS (single e))) (Env (var (vs vz)) (var (vs (vs vz))))))
            ≡ Env d e
      eqD = trans (cong (λ z → subTy (single u) (subTy (extS (single d)) z))
                        (Env-sub (extS (extS (single e))) (var (vs vz)) (var (vs (vs vz)))))
            (trans (cong (subTy (single u)) (Env-sub (extS (single d)) (var (vs vz)) (renTm vs (renTm vs e))))
            (trans (Env-sub (single u) (renTm vs d) (subTm (extS (single d)) (renTm vs (renTm vs e))))
                   (cong₂ Env (wkc u d) (wkc2 u d e))))
      f1 : Γ ⊢ app CONS e ∷ Π (El ⌜Nat⌝) (subTy (extS (single e)) (Π (Vat VF (var (vs vz))) R))
      f1 = ⊢app {Γ} {El ⌜Nat⌝} {Π (El ⌜Nat⌝) (Π (Vat VF (var (vs vz))) R)} {CONS} {e} ⊢CONS de
      f2 : Γ ⊢ app (app CONS e) d ∷ subTy (single d) (subTy (extS (single e)) (Π (Vat VF (var (vs vz))) R))
      f2 = ⊢app {Γ} {El ⌜Nat⌝} {subTy (extS (single e)) (Π (Vat VF (var (vs vz))) R)} {app CONS e} {d} f1 dd
      R' : RTy (⌊ Γ ⌋ ∙)
      R' = subTy (extS (single d)) (subTy (extS (extS (single e))) R)
      f3 : Γ ⊢ app (app (app CONS e) d) u ∷ subTy (single u) R'
      f3 = ⊢app {Γ} {Vat VF e} {R'} {app (app CONS e) d} {u}
                (⊢-cast {Γ} {app (app CONS e) d} {subTy (single d) (subTy (extS (single e)) (Π (Vat VF (var (vs vz))) R))} {Π (Vat VF e) R'} eqU f2) du
      df' : Γ ⊢ f ∷ subTy (single u) (subTy (extS (single d)) (subTy (extS (extS (single e))) (Env (var (vs vz)) (var (vs (vs vz))))))
      df' = ⊢-cast (sym eqD) df
      f4 : Γ ⊢ app (app (app (app CONS e) d) u) f
             ∷ subTy (single f) (subTy (extS (single u)) (subTy (extS (extS (single d))) (subTy (extS (extS (extS (single e))))
                 (Env (nsuc (var (vs (vs vz)))) (var (vs (vs (vs vz))))))))
      f4 = ⊢app {Γ} {subTy (single u) (subTy (extS (single d)) (subTy (extS (extS (single e))) (Env (var (vs vz)) (var (vs (vs vz))))))}
                {subTy (extS (single u)) (subTy (extS (extS (single d))) (subTy (extS (extS (extS (single e))))
                   (Env (nsuc (var (vs (vs vz)))) (var (vs (vs (vs vz)))))))}
                {app (app (app CONS e) d) u} {f} f3 df'
      eqC : subTy (single f) (subTy (extS (single u)) (subTy (extS (extS (single d))) (subTy (extS (extS (extS (single e))))
              (Env (nsuc (var (vs (vs vz)))) (var (vs (vs (vs vz))))))))
            ≡ Env (nsuc d) e
      eqC = trans (cong (λ z → subTy (single f) (subTy (extS (single u)) (subTy (extS (extS (single d))) z)))
                        (Env-sub (extS (extS (extS (single e)))) (nsuc (var (vs (vs vz)))) (var (vs (vs (vs vz))))))
            (trans (cong (λ z → subTy (single f) (subTy (extS (single u)) z))
                         (Env-sub (extS (extS (single d))) (nsuc (var (vs (vs vz)))) (renTm vs (renTm vs (renTm vs e)))))
            (trans (cong (subTy (single f))
                         (Env-sub (extS (single u)) (nsuc (renTm vs (renTm vs d)))
                                  (subTm (extS (extS (single d))) (renTm vs (renTm vs (renTm vs e))))))
            (trans (Env-sub (single f) (nsuc (subTm (extS (single u)) (renTm vs (renTm vs d))))
                            (subTm (extS (single u)) (subTm (extS (extS (single d))) (renTm vs (renTm vs (renTm vs e))))))
                   (cong₂ (λ a b → Env (nsuc a) b) (wkc2 f u d) (wkc3 f u d e)))))

  ------------------------------------------------------------------------
  -- ★ LIFT = λ e d ρ. (λ y. WK e (ρ y) , V0 e) — one binder further
  ------------------------------------------------------------------------

  LIFT : RTm Γ
  LIFT = lam (lam (lam (app (app (app (app CONS (nsuc (var (vs (vs vz))))) (var (vs vz)))
                                 (app V0 (var (vs (vs vz)))))
                            (lam (app (app WK (var (vs (vs (vs vz))))) (app (var (vs vz)) (var vz)))))))

  LIFTTy : RTy Γ
  LIFTTy = Π (El ⌜Nat⌝) (Π (El ⌜Nat⌝) (Π (Env (var vz) (var (vs vz)))
             (Env (nsuc (var (vs vz))) (nsuc (var (vs (vs vz)))))))

  module _ {Γ : Ctx} where
    private
      Γ3 : Ctx
      Γ3 = ((Γ ▹ El ⌜Nat⌝) ▹ El ⌜Nat⌝) ▹ Env (var vz) (var (vs vz))
      e3 d3 : RTm ⌊ Γ3 ⌋
      e3 = var (vs (vs vz))
      d3 = var (vs vz)
      de3 : Γ3 ⊢ e3 ∷ El ⌜Nat⌝
      de3 = ⊢var (there (there here))
      dd3 : Γ3 ⊢ d3 ∷ El ⌜Nat⌝
      dd3 = ⊢var (there here)
      dy : (Γ3 ▹ FinI d3) ⊢ app (var (vs vz)) (var vz) ∷ Vat VF (renTm vs e3)
      dy = ⊢Env· (⊢wkE hereE) (⊢var here)
      dwk : Γ3 ⊢ lam (app (app WK (var (vs (vs (vs vz))))) (app (var (vs vz)) (var vz))) ∷ Env d3 (nsuc e3)
      dwk = ⊢lam (ty-IMu ⊢⌜Nat⌝ ⊢FinD dd3) (⊢WK· (⊢wk de3) dy)
      dv0 : Γ3 ⊢ app V0 e3 ∷ Vat VF (nsuc e3)
      dv0 = ⊢V0· de3
      body : Γ3 ⊢ app (app (app (app CONS (nsuc e3)) d3) (app V0 e3))
                      (lam (app (app WK (var (vs (vs (vs vz))))) (app (var (vs vz)) (var vz))))
               ∷ Env (nsuc d3) (nsuc e3)
      body = ⊢CONS· {Γ3} {nsuc e3} {d3} {app V0 e3} {lam (app (app WK (var (vs (vs (vs vz))))) (app (var (vs vz)) (var vz)))}
                    (⊢isuc de3) dd3 dv0 dwk

    ⊢LIFT : Γ ⊢ LIFT ∷ LIFTTy
    ⊢LIFT = ⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-El ⊢⌜Nat⌝) (⊢lam (ty-Env (⊢var here) (⊢var (there here))) body))

  ------------------------------------------------------------------------
  -- 3. LIFTING UNDER k BINDERS.
  ------------------------------------------------------------------------

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

  ⊢tpay : {Γ : Ctx} {sh : Shape} {i p h e f d : RTm ⌊ Γ ⌋} → FOK n sh →
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

  ------------------------------------------------------------------------
  -- 6. THE MOTIVE AND THE FAMILY ARE CLOSED.
  ------------------------------------------------------------------------

  private
    open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )

  SD-ren : (ρ : Ren Γ Δ) → renTm ρ (SD {Δ = Γ} sg) ≡ SD sg
  SD-ren ρ = trans (sym (subTm-var ρ (SD sg))) (SD-sub ⟨ ρ ⟩ᵣ sg)

  -- the motive under any substitution of its two binders
  TM-sub : (τ : Sub ((Γ ∙) ∙) Δ) →
           subTy τ TM ≡ Π (El ⌜Nat⌝) (Π (Env (snd (renTm vs (τ (vs vz)))) (var vz))
                                        (IMu (SI n) (SD sg) (pair (fst (renTm vs (renTm vs (τ (vs vz))))) (var (vs vz)))))
  TM-sub τ =
    cong (Π (El ⌜Nat⌝))
      (cong₂ Π (Env-sub (extS τ) (snd (var (vs (vs vz)))) (var vz))
               (cong₂ (λ D j → IMu (SI n) D j) (SD-sub (extS (extS τ)) sg) refl))

  TM-ren : (ρ : Ren Γ Δ) → renTy (extR (extR ρ)) TM ≡ TM
  TM-ren ρ = trans (sym (subTy-var (extR (extR ρ)) TM)) (TM-sub ⟨ extR (extR ρ) ⟩ᵣ)

  ------------------------------------------------------------------------
  -- 7. ★★ CONSTRUCTOR `k` OF SORT `s`: its method at the sort's index
  --    `pair (tag s) j` (binders: payload, hypotheses, then the motive's
  --    `e` and `f`).  The variable rebuilds nothing: it is its value.
  ------------------------------------------------------------------------

  -- a fields row: rebuild the node; the variable row: its value's node
  mTf : Shape → ℕ → RTm (Γ ∙)
  mTf sh k = lam (lam (lam (lam (conₗ k (tpay sh (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var (vs vz)) (var vz)
                                               (var (vs (vs (vs (vs vz))))))))))

  mTv : RTm (Γ ∙)
  mTv = lam (lam (lam (lam (app (app NODE (var (vs vz))) (app (var vz) (fst (var (vs (vs (vs vz))))))))))

  mT : Shape → ℕ → RTm (Γ ∙)
  mT []ʰ         k = mTf []ʰ k
  mT (fl ∷ʰ sh)  k = mTf (fl ∷ʰ sh) k
  mT vʰ          k = mTv

  r4 : (t : RTm Γ) → RTm ((((Γ ∙) ∙) ∙) ∙)
  r4 t = renTm vs (renTm vs (renTm vs (renTm vs t)))

  SDr : {Θ : Cx} {t : RTm Γ} → t ≡ SD sg → (ρ : Ren Γ Θ) → renTm ρ t ≡ SD sg
  SDr refl ρ = SD-ren ρ

  SD-r4 : r4 (renTm vs (SD {Δ = Γ} sg)) ≡ SD sg
  SD-r4 = SDr (SDr (SDr (SDr (SDr refl vs) vs) vs) vs) vs

  -- a telescope instantiated at `ιₛ s`, then renamed four times
  tel-r4 : (s : ℕ) (sh : Shape) →
           r4 (subTm (σₛ s) ⌜ tel sh (var vz) ⌝ᵗ) ≡ ⌜ tel {Δ = (((((Γ ∙) ∙) ∙) ∙) ∙)} sh (r4 (ιₛ s)) ⌝ᵗ
  tel-r4 s sh =
    trans (cong r4 (sub-tel (σₛ s) sh (var vz)))
      (trans (cong (λ z → renTm vs (renTm vs (renTm vs z))) (ren-tel vs sh _))
        (trans (cong (λ z → renTm vs (renTm vs z)) (ren-tel vs sh _))
          (trans (cong (renTm vs) (ren-tel vs sh _)) (ren-tel vs sh _))))

  TMr : {Θ : Cx} {M : RTy ((Γ ∙) ∙)} → M ≡ TM → (ρ : Ren Γ Θ) → renTy (extR (extR ρ)) M ≡ TM
  TMr refl ρ = TM-ren ρ

  tagr4 : (s : ℕ) → r4 {Γ = Γ} (tag s) ≡ tag s
  tagr4 s = trans (cong (λ z → renTm vs (renTm vs (renTm vs z))) (tag-ren vs s))
              (trans (cong (λ z → renTm vs (renTm vs z)) (tag-ren vs s))
                (trans (cong (renTm vs) (tag-ren vs s)) (tag-ren vs s)))
    where open import DirectedHoTT.Lib.Sugar using ( tag-ren )

  -- ★ a FIELDS row's method, typed
  ⊢mT-f : {Γ : Ctx} {s k c : ℕ} {shs : Shapes c} {sh : Shape} →
          FOK n sh → NthG sg s shs → NthSh shs k sh →
          (Γ ▹ El ⌜Nat⌝) ⊢ mTf sh k ∷ MethKAt (renTm vs (SI n)) (renTm vs (SD sg)) (wk1M TM) (ιₛ s)
                                             (subTm (σₛ s) ⌜ tel sh (var vz) ⌝ᵗ) k
  ⊢mT-f {Γ = Γ} {s = s} {k = k} {sh = sh} fok ng nh =
    ⊢lam dPay (⊢lam dHyp (⊢-cast (sym eqT) BODY))
    where
      Γ' = Γ ▹ El ⌜Nat⌝
      ιx = ιₛ {Δ = ⌊ Γ ⌋} s
      C = subTm (σₛ s) ⌜ tel sh (var vz) ⌝ᵗ
      dix : Γ' ⊢ ιx ∷ El (SI n)
      dix = ⊢ιₛ ⊢⌜Nat⌝ (nthG-lt ng)
      dC : Γ' ⊢ C ∷ Desc (SI n)
      dC = subst (λ X → Γ' ⊢ X ∷ Desc (SI n)) (sym (sub-tel (σₛ s) sh (var vz))) (⊢tel ⊢SI (telOKf fok dix))
      dD' = ⊢wkD {B = El ⌜Nat⌝} (⊢SD {Γ = Γ} ok)
      dPay = ty-El (⊢dpay ⊢SI dD' dC)
      dHyp = ty-DIh ⊢SI (⊢wkD dD') (mot-ren there (mot-ren there (⊢TM {Γ = Γ}))) (⊢wk dC) (⊢var here)
      τ = atS ιx (conₗ k (var (vs vz))) ₛ∘ᵣ extR (extR vs)
      eqT = trans (subTy-renTy TM) (TM-sub τ)
      ι₃ = renTm vs (renTm vs (renTm vs ιx))
      ι₄ = r4 ιx
      Pay = El (dpay (renTm vs (SI n)) (renTm vs (SD sg)) C)
      Hyp = DIh (renTm vs (renTm vs (SD sg))) (wk1M (wk1M TM)) (renTm vs C) (var vz)
      Γ₂ = (Γ' ▹ Pay) ▹ Hyp
      Γ₄ = (Γ₂ ▹ El ⌜Nat⌝) ▹ Env (snd ι₃) (var vz)
      p₄ h₄ e₄ f₄ j₄ : RTm ⌊ Γ₄ ⌋
      p₄ = var (vs (vs (vs vz)))
      h₄ = var (vs (vs vz))
      e₄ = var (vs vz)
      f₄ = var vz
      j₄ = var (vs (vs (vs (vs vz))))
      -- the payload and the hypotheses, at their views
      dp : Γ₄ ⊢ p₄ ∷ PayV sh ι₄ (SI n) (SD sg)
      dp = ⊢conv (⊢-cast (cong₂ (λ D X → El (dpay (SI n) D X)) SD-r4 (tel-r4 s sh)) (⊢var (there (there (there here)))))
                 (red→≅ᵀ (payV-red sh ι₄ (SI n) (SD sg)))
      dh : Γ₄ ⊢ h₄ ∷ IhV sh ι₄ (SD sg) TM p₄
      dh = ⊢conv (⊢-cast (cong₃ (λ D M X → DIh D M X p₄) SD-r4
                                (TMr (TMr (TMr (TMr (TMr refl vs) vs) vs) vs) vs) (tel-r4 s sh))
                         (⊢var (there (there here))))
                 (red→≅ᵀ (ihV-red sh ι₄ (SD sg) TM p₄))
      de : Γ₄ ⊢ e₄ ∷ El ⌜Nat⌝
      de = ⊢var (there here)
      dd : Γ₄ ⊢ j₄ ∷ El ⌜Nat⌝
      dd = ⊢var (there (there (there (there here))))
      df : Γ₄ ⊢ f₄ ∷ Env j₄ e₄
      df = ⊢conv (⊢-cast (Env-ren vs (snd ι₃) (var vz)) (⊢var here))
                 (red→≅ᵀ (⟶ᵀ*-Πˡ (⟶ᵀ*-IMu (step (βsnd _ _) done))))
      CON : Γ₄ ⊢ conₗ k (tpay sh p₄ h₄ e₄ f₄ j₄) ∷ SK sg s e₄
      CON = ⊢conSyn ok ng nh de (⊢tpay fok dp dh de dd (step (βsnd _ _) done) df)
      BODY : Γ₂ ⊢ lam (lam (conₗ k (tpay sh p₄ h₄ e₄ f₄ j₄)))
                 ∷ Π (El ⌜Nat⌝) (Π (Env (snd ι₃) (var vz))
                                   (IMu (SI n) (SD sg) (pair (fst ι₄) (var (vs vz)))))
      BODY = ⊢lam (ty-El ⊢⌜Nat⌝)
               (⊢lam (ty-Env (⊢depth (⊢wk (⊢wk (⊢wk dix)))) (⊢var here))
                 (⊢conv (⊢-cast (cong (λ z → IMu (SI n) (SD sg) (pair z e₄)) (sym (tagr4 s))) CON)
                        (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairˡ (step (βfst _ _) done)))))))
