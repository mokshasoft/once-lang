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
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; red→≅ᵀ; ⟶ᵀ*-IMu; ⟶ᵀ*-El )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; ren-lemma; sub-lemma; Sub⊢ )
open import DirectedHoTT.Metatheory.Premises using ( mot-ren )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; nth-z; nth-s; []ᵈ; selF; subC; tag; conₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.NatFib
open import DirectedHoTT.Lib.FinFam
open import DirectedHoTT.Lib.Syn

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

module _ {sg : Sig n} (κ : Kit n sg) where
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
  w4 : Ren Γ ((((Γ ∙) ∙) ∙) ∙)
  w4 x = vs (vs (vs (vs x)))

  lz ls : RTm Γ → RTm (Γ ∙)
  lz e = lam (lam (lam (app V0 (renTm w4 e))))
  ls e = lam (lam (lam (app (app WK (renTm w4 e)) (app (var vz) (fst (var (vs (vs vz))))))))

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
