-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CanonPrincipal — the D072 oracle is canon-invariant.
--
-- `principalGround` commutes with the resolver's body canonicalization
-- (`canonExpr b [] []`, the import-free fragment) and poly-context
-- canonicalization (`canonPolysCtx`): POINTWISE EQUALITY, not just
-- success transport. This is possible — unlike for `inferElab` — because
-- the oracle was built for it (D072 design rule 2):
--
--   * `RVar x` and `RResolved cn` dispatch through ONE name-keyed
--     lookup (`lookupName`), and `showCanonical (canonical [x]) ≡ x`
--     holds definitionally;
--   * `pInfer`'s context is `(Imports, SchemaCtx)` — poly BODIES are
--     out of scope BY TYPE, so `canonPolysCtx` (bodies-only) invariance
--     is `projSchemas-canon`, a three-line projection lemma;
--   * `pInfer` is `with`-free in its recursive spine (`_>>=R_` chains),
--     so the proof is equational: rewrite the scrutinee via the IH,
--     then congruence on the continuation.
--
-- The one non-congruence leaf: an own-module bare `RVar x` (not bound,
-- not builtin) becomes `RResolved (canonical [x])` — neutralized by the
-- singleton-canonical definitional equality plus `EnvBound` (binders
-- are always in the resolver's bound set, so a canonicalized name is
-- never a binder).
------------------------------------------------------------------------

module Once.Adequacy.CanonPrincipal where

open import Data.String using (String)
open import Data.String.Properties as StrProp using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Once.Type
open import Once.CanonicalName using (canonical; showCanonical)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.TypeCheck.Classify
  using (NamedCtx; Imports; PolyCtx; ctxWithImportsAndPolys; lookupPoly)
open import Once.TypeCheck.Principal as P using ()
open import Once.Parser.Module.Resolve
  using (canonExpr; canonVar; isBuiltinName; elemStr)
open import Once.Adequacy.CanonPolyTransport
  using (canonPolysCtx; canon-entry; lookupPoly-canon)

------------------------------------------------------------------------
-- Small helpers
------------------------------------------------------------------------

bool-clash : true ≡ false → ∀ {ℓ} {A : Set ℓ} → A
bool-clash ()

-- | `canonExpr` on a variable leaf, by the three routing outcomes.
canonVar-bare : ∀ (bound : List String) (x : String)
  → elemStr x bound ≡ true
  → canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RVar x
canonVar-bare bound x eqB rewrite eqB = refl

canonVar-bareB : ∀ (bound : List String) (x : String)
  → elemStr x bound ≡ false → isBuiltinName x ≡ true
  → canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RVar x
canonVar-bareB bound x eqB eqIB rewrite eqB | eqIB = refl

canonVar-res : ∀ (bound : List String) (x : String)
  → elemStr x bound ≡ false → isBuiltinName x ≡ false
  → canonExpr bound [] [] (Raw.RVar x) ≡ Raw.RResolved (canonical (x ∷ []))
canonVar-res bound x eqB eqIB rewrite eqB | eqIB = refl

-- | Binders threaded through `pInfer`'s Env are always in `canonExpr`'s
-- bound set (they enter both in lockstep).
EnvBound : P.Env → List String → Set
EnvBound env bound =
  ∀ x t → P.lookupEnv x env ≡ just t → elemStr x bound ≡ true

envBound-[] : ∀ (bound : List String) → EnvBound [] bound
envBound-[] bound x t ()

envBound-ext : ∀ (env : P.Env) (bound : List String) (x : String) (t : PolyType)
  → EnvBound env bound → EnvBound ((x , t) ∷ env) (x ∷ bound)
envBound-ext env bound x t eb y u eq with y ≟ x
... | yes _ = refl
... | no _  = eb y u eq

------------------------------------------------------------------------
-- The invariance (module-parameterized by the shared import table, the
-- source poly context, and the resolver's module-level bound set `b`)
------------------------------------------------------------------------

-- | `canonPolysCtx` canonicalizes BODIES only — the schema projection
-- is untouched. This is the whole polys-side invariance.
projSchemas-canon : ∀ (b : List String) (p : PolyCtx)
  → P.projSchemas (canonPolysCtx b p) ≡ P.projSchemas p
projSchemas-canon b [] = refl
projSchemas-canon b ((nm , sc , body) ∷ rest) =
  cong ((nm , sc) ∷_) (projSchemas-canon b rest)

module _ (imps : Imports) (sch : P.SchemaCtx) where

  bindCong : ∀ (r : P.Result) {k k' : PolyType × ℕ × P.PSubst → P.Result}
     → (∀ v → k v ≡ k' v) → (r P.>>=R k) ≡ (r P.>>=R k')
  bindCong nothing  h = refl
  bindCong (just v) h = h v

  step2 : ∀ {rC rS : P.Result} {kC kS : PolyType × ℕ × P.PSubst → P.Result}
    → rC ≡ rS → (∀ v → kC v ≡ kS v)
    → (rC P.>>=R kC) ≡ (rS P.>>=R kS)
  step2 {rC} {rS} {kC} {kS} eqR eqK =
    trans (cong (λ r → r P.>>=R kC) eqR) (bindCong rS eqK)

  -- A bare-kept variable: both sides are literally the same call.
  pInfer-var-same : ∀ (env : P.Env) (x : String) (n : ℕ) (s : P.PSubst)
    → P.pInfer imps sch env (Raw.RVar x) n s ≡ P.pInfer imps sch env (Raw.RVar x) n s
  pInfer-var-same env x n s = refl

  -- A canonicalized own-module variable: `showCanonical (canonical [x])`
  -- is definitionally `x`, and it cannot be a binder (EnvBound).
  pInfer-var-res : ∀ (env : P.Env) (bound : List String) (x : String)
      (n : ℕ) (s : P.PSubst)
    → EnvBound env bound → elemStr x bound ≡ false
    → P.pInfer imps sch env (Raw.RResolved (canonical (x ∷ []))) n s
      ≡ P.pInfer imps sch env (Raw.RVar x) n s
  pInfer-var-res env bound x n s eb eqB with P.lookupEnv x env in eqE
  ... | just t  = bool-clash (trans (sym (eb x t eqE)) eqB)
  ... | nothing = refl

  mutual
    pInfer-canon : ∀ (env : P.Env) (bound : List String) (e : RawExpr)
        (n : ℕ) (s : P.PSubst)
      → EnvBound env bound
      → P.pInfer imps sch env (canonExpr bound [] [] e) n s
        ≡ P.pInfer imps sch env e n s
    pInfer-canon env bound (Raw.RVar x) n s eb = goVar (elemStr x bound) refl
      where
      goVar : (bv : Bool) → elemStr x bound ≡ bv
        → P.pInfer imps sch env (canonExpr bound [] [] (Raw.RVar x)) n s
          ≡ P.pInfer imps sch env (Raw.RVar x) n s
      goVar true eqB rewrite canonVar-bare bound x eqB =
        pInfer-var-same env x n s
      goVar false eqB = goVar2 (isBuiltinName x) refl
        where
        goVar2 : (ib : Bool) → isBuiltinName x ≡ ib
          → P.pInfer imps sch env (canonExpr bound [] [] (Raw.RVar x)) n s
            ≡ P.pInfer imps sch env (Raw.RVar x) n s
        goVar2 true eqIB rewrite canonVar-bareB bound x eqB eqIB =
          pInfer-var-same env x n s
        goVar2 false eqIB rewrite canonVar-res bound x eqB eqIB =
          pInfer-var-res env bound x n s eb eqB
    pInfer-canon env bound (Raw.RQualified q al) n s eb = refl
    pInfer-canon env bound (Raw.RResolved cn) n s eb = refl
    -- Compose-candidate application: delegated to a top-level mutual
    -- member (NOT a where-fn) so the head subterm `ff` stays a real
    -- argument through lifting — the termination checker needs it.
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RVar y) f') g) n s eb =
      composeCase env bound y ff f' g n s eb refl
    -- Single application with a bare-variable head: `id e`, `myId 0`, …
    pInfer-canon env bound (Raw.RApp (Raw.RVar y) x) n s eb =
      goV (elemStr y bound) refl
      where
      goV : (bv : Bool) → elemStr y bound ≡ bv
        → P.pInfer imps sch env
            (canonExpr bound [] [] (Raw.RApp (Raw.RVar y) x)) n s
          ≡ P.pInfer imps sch env (Raw.RApp (Raw.RVar y) x) n s
      goV true eqB =
        trans
          (cong (λ hh → P.pInferApp imps sch env hh
                          (canonExpr bound [] [] x) n s)
                (canonVar-bare bound y eqB))
          (step2 (pInfer-var-same env y n s)
            λ { (tf , n₁ , s₁) →
                step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl })
      goV false eqB = goV2 (isBuiltinName y) refl
        where
        goV2 : (ib : Bool) → isBuiltinName y ≡ ib
          → P.pInfer imps sch env
              (canonExpr bound [] [] (Raw.RApp (Raw.RVar y) x)) n s
            ≡ P.pInfer imps sch env (Raw.RApp (Raw.RVar y) x) n s
        goV2 true eqIB =
          trans
            (cong (λ hh → P.pInferApp imps sch env hh
                            (canonExpr bound [] [] x) n s)
                  (canonVar-bareB bound y eqB eqIB))
            (step2 (pInfer-var-same env y n s)
              λ { (tf , n₁ , s₁) →
                  step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl })
        goV2 false eqIB =
          trans
            (cong (λ hh → P.pInferApp imps sch env hh
                            (canonExpr bound [] [] x) n s)
                  (canonVar-res bound y eqB eqIB))
            (step2 (pInfer-var-res env bound y n s eb eqB)
              λ { (tf , n₁ , s₁) →
                  step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl })
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RApp a2 b2) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RResolved cn) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RLam v bdy) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RLet v le1 le2) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RPair pa pb) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RDestruct de dxl de1 dxr de2) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RAnnot ae aT) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RBinOp bop ba bbb) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RUnaryOp uop ua) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp Raw.RUnit f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RInt i) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp (Raw.RApp (Raw.RFloat i fr fl _) f') g) n s eb = refl
    pInfer-canon env bound (Raw.RApp ff@(Raw.RApp (Raw.RStringLit str) f') g) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp (Raw.RApp (Raw.RQualified q al) f') g) n s eb = refl
    pInfer-canon env bound (Raw.RApp (Raw.RApp (Raw.RAna F c) f') g) n s eb = refl
    pInfer-canon env bound (Raw.RApp ff@(Raw.RResolved cn) x) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RLam v bdy) x) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RLet v le1 le2) x) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RPair pa pb) x) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RDestruct de dxl de1 dxr de2) x) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RAnnot ae aT) x) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RBinOp bop ba bbb) x) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp ff@(Raw.RUnaryOp uop ua) x) n s eb =
      step2 (pInfer-canon env bound ff n s eb)
        λ { (tf , n₁ , s₁) →
            step2 (pInfer-canon env bound x n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RApp Raw.RUnit x) n s eb =
      step2 (pInfer-canon env bound x n s eb) λ _ → refl
    pInfer-canon env bound (Raw.RApp (Raw.RInt i) x) n s eb =
      step2 (pInfer-canon env bound x n s eb) λ _ → refl
    pInfer-canon env bound (Raw.RApp (Raw.RFloat i fr fl _) x) n s eb = refl
    pInfer-canon env bound (Raw.RApp (Raw.RStringLit str) x) n s eb =
      step2 (pInfer-canon env bound x n s eb) λ _ → refl
    pInfer-canon env bound (Raw.RApp (Raw.RQualified q al) x) n s eb = refl
    pInfer-canon env bound (Raw.RApp (Raw.RAna F c) x) n s eb = refl
    pInfer-canon env bound (Raw.RLam x body) n s eb =
      step2 (pInfer-canon ((x , PTVar (P.mv n)) ∷ env) (x ∷ bound) body
               (suc n) s (envBound-ext env bound x (PTVar (P.mv n)) eb))
        λ _ → refl
    pInfer-canon env bound (Raw.RLet x e₁ e₂) n s eb =
      step2 (pInfer-canon env bound e₁ n s eb)
        λ { (t₁ , n₁ , s₁) →
            pInfer-canon ((x , t₁) ∷ env) (x ∷ bound) e₂ n₁ s₁
              (envBound-ext env bound x t₁ eb) }
    pInfer-canon env bound (Raw.RPair a bb) n s eb =
      step2 (pInfer-canon env bound a n s eb)
        λ { (ta , n₁ , s₁) →
            step2 (pInfer-canon env bound bb n₁ s₁ eb) λ _ → refl }
    pInfer-canon env bound (Raw.RDestruct e xl e₁ xr e₂) n s eb =
      step2 (pInfer-canon env bound e n s eb)
        λ { (te , n₁ , s₁) →
            destructFinish-canon env bound xl e₁ xr e₂ te n₁ s₁ eb }
    pInfer-canon env bound Raw.RUnit n s eb = refl
    pInfer-canon env bound (Raw.RInt i) n s eb = refl
    pInfer-canon env bound (Raw.RFloat i fr fl _) n s eb = refl
    pInfer-canon env bound (Raw.RStringLit str) n s eb = refl
    pInfer-canon env bound (Raw.RAnnot e T) n s eb with P.typeToPoly T
    ... | nothing = refl
    ... | just tT = step2 (pInfer-canon env bound e n s eb) λ _ → refl
    pInfer-canon env bound (Raw.RBinOp op a bb) n s eb =
      step2 (pInfer-canon env bound a n s eb)
        λ { (ta , n₁ , s₁) →
            bindCong (P.retTy PInt n₁ (P.unify P.fuelD s₁ ta PInt))
              λ { (_ , _ , s₂) →
                  step2 (pInfer-canon env bound bb n₁ s₂ eb) λ _ → refl } }
    pInfer-canon env bound (Raw.RUnaryOp op a) n s eb =
      step2 (pInfer-canon env bound a n s eb) λ _ → refl
    pInfer-canon env bound (Raw.RAna F c) n s eb = refl

    -- The compose-candidate case, with `ff` (the whole head) as a real
    -- parameter plus the defining equation. All recursive calls pass
    -- parameters, so lifting preserves the subterm relations.
    composeCase : ∀ (env : P.Env) (bound : List String) (y : String)
        (ff f' g : RawExpr) (n : ℕ) (s : P.PSubst)
      → EnvBound env bound
      → ff ≡ Raw.RApp (Raw.RVar y) f'
      → P.pInfer imps sch env
          (canonExpr bound [] [] (Raw.RApp (Raw.RApp (Raw.RVar y) f') g)) n s
        ≡ P.pInfer imps sch env (Raw.RApp (Raw.RApp (Raw.RVar y) f') g) n s
    composeCase env bound y ff f' g n s eb ffEq = goH (elemStr y bound) refl
      where
      ihff : ∀ n' s'
        → P.pInfer imps sch env
            (Raw.RApp (canonExpr bound [] [] (Raw.RVar y))
              (canonExpr bound [] [] f')) n' s'
          ≡ P.pInfer imps sch env (Raw.RApp (Raw.RVar y) f') n' s'
      ihff n' s' =
        subst
          (λ w → P.pInfer imps sch env (canonExpr bound [] [] w) n' s'
                 ≡ P.pInfer imps sch env w n' s')
          ffEq
          (pInfer-canon env bound ff n' s' eb)
      goC : canonExpr bound [] [] (Raw.RVar y) ≡ Raw.RVar y
        → (d : Relation.Nullary.Dec (y ≡ "compose")) →
        P.pInferAppB imps sch env
          (Raw.RApp (Raw.RVar y) (canonExpr bound [] [] f'))
          (canonExpr bound [] [] f') (canonExpr bound [] [] g) n s
          (P.isYes d)
        ≡ P.pInferAppB imps sch env (Raw.RApp (Raw.RVar y) f') f' g n s
          (P.isYes d)
      goC eqH (yes _) =
        step2 (pInfer-canon env bound f' n s eb)
          λ { (tf , n₁ , s₁) →
              step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
      goC eqH (no _) =
        step2
          (subst
            (λ hh → P.pInfer imps sch env
                      (Raw.RApp hh (canonExpr bound [] [] f')) n s
                    ≡ P.pInfer imps sch env (Raw.RApp (Raw.RVar y) f') n s)
            eqH (ihff n s))
          λ { (tf , n₁ , s₁) →
              step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
      headBare : canonExpr bound [] [] (Raw.RVar y) ≡ Raw.RVar y
        → P.pInfer imps sch env
            (canonExpr bound [] [] (Raw.RApp (Raw.RApp (Raw.RVar y) f') g)) n s
          ≡ P.pInfer imps sch env (Raw.RApp (Raw.RApp (Raw.RVar y) f') g) n s
      headBare eq =
        trans
          (cong (λ hh → P.pInferApp imps sch env
                          (Raw.RApp hh (canonExpr bound [] [] f'))
                          (canonExpr bound [] [] g) n s) eq)
          (goC eq (y ≟ "compose"))
      headRes : elemStr y bound ≡ false → isBuiltinName y ≡ false
        → P.pInfer imps sch env
            (canonExpr bound [] [] (Raw.RApp (Raw.RApp (Raw.RVar y) f') g)) n s
          ≡ P.pInfer imps sch env (Raw.RApp (Raw.RApp (Raw.RVar y) f') g) n s
      headRes eqB eqIB =
        trans
          (cong (λ hh → P.pInferApp imps sch env
                          (Raw.RApp hh (canonExpr bound [] [] f'))
                          (canonExpr bound [] [] g) n s)
                (canonVar-res bound y eqB eqIB))
          (goR (y ≟ "compose"))
        where
        goR : (d : Relation.Nullary.Dec (y ≡ "compose")) →
          P.pInferApp imps sch env
            (Raw.RApp (Raw.RResolved (canonical (y ∷ [])))
              (canonExpr bound [] [] f'))
            (canonExpr bound [] [] g) n s
          ≡ P.pInferAppB imps sch env (Raw.RApp (Raw.RVar y) f') f' g n s
            (P.isYes d)
        goR (yes refl) = bool-clash eqIB
        goR (no _) =
          step2
            (subst
              (λ hh → P.pInfer imps sch env
                        (Raw.RApp hh (canonExpr bound [] [] f')) n s
                      ≡ P.pInfer imps sch env (Raw.RApp (Raw.RVar y) f') n s)
              (canonVar-res bound y eqB eqIB) (ihff n s))
            λ { (tf , n₁ , s₁) →
                step2 (pInfer-canon env bound g n₁ s₁ eb) λ _ → refl }
      goH : (bv : Bool) → elemStr y bound ≡ bv
        → P.pInfer imps sch env
            (canonExpr bound [] [] (Raw.RApp (Raw.RApp (Raw.RVar y) f') g)) n s
          ≡ P.pInfer imps sch env (Raw.RApp (Raw.RApp (Raw.RVar y) f') g) n s
      goH true eqB = headBare (canonVar-bare bound y eqB)
      goH false eqB = goH2 (isBuiltinName y) refl
        where
        goH2 : (ib : Bool) → isBuiltinName y ≡ ib
          → P.pInfer imps sch env
              (canonExpr bound [] [] (Raw.RApp (Raw.RApp (Raw.RVar y) f') g)) n s
            ≡ P.pInfer imps sch env (Raw.RApp (Raw.RApp (Raw.RVar y) f') g) n s
        goH2 true eqIB = headBare (canonVar-bareB bound y eqB eqIB)
        goH2 false eqIB = headRes eqB eqIB

    destructFinish-canon : ∀ (env : P.Env) (bound : List String)
        (xl : String) (e₁ : RawExpr) (xr : String) (e₂ : RawExpr)
        (te : PolyType) (n₁ : ℕ) (s₁ : P.PSubst)
      → EnvBound env bound
      → P.destructFinish imps sch env xl (canonExpr (xl ∷ bound) [] [] e₁)
          xr (canonExpr (xr ∷ bound) [] [] e₂) te n₁ s₁
        ≡ P.destructFinish imps sch env xl e₁ xr e₂ te n₁ s₁
    destructFinish-canon env bound xl e₁ xr e₂ te n₁ s₁ eb
      with P.unify P.fuelD s₁ te
             (PTVar (P.mv n₁) P+ PTVar (P.mv (suc n₁)))
    ... | nothing = refl
    ... | just s₂ =
          step2 (pInfer-canon ((xl , PTVar (P.mv n₁)) ∷ env) (xl ∷ bound)
                   e₁ (suc (suc n₁)) s₂
                   (envBound-ext env bound xl (PTVar (P.mv n₁)) eb))
            λ { (t₁ , n₂ , s₃) →
                step2 (pInfer-canon ((xr , PTVar (P.mv (suc n₁))) ∷ env)
                         (xr ∷ bound) e₂ n₂ s₃
                         (envBound-ext env bound xr (PTVar (P.mv (suc n₁))) eb))
                  λ _ → refl }

  ------------------------------------------------------------------------
  -- The invariance at the traversal level.
  ------------------------------------------------------------------------

  pInfer-canon-top : ∀ (bound : List String) (e : RawExpr)
    → P.pInfer imps sch [] (canonExpr bound [] [] e) 0 []
      ≡ P.pInfer imps sch [] e 0 []
  pInfer-canon-top bound e = pInfer-canon [] bound e 0 [] (envBound-[] bound)

------------------------------------------------------------------------
-- The oracle corollaries, stated on the `NamedCtx` entry points used by
-- `Compile.inferType`.
------------------------------------------------------------------------

-- Body + polys both canonicalized (the USER-function transport).
principal-canon : ∀ (imps : Imports) (polys : PolyCtx) (b : List String)
    (e : RawExpr)
  → P.principal (ctxWithImportsAndPolys imps (canonPolysCtx b polys))
      (canonExpr b [] [] e)
    ≡ P.principal (ctxWithImportsAndPolys imps polys) e
principal-canon imps polys b e =
  trans
    (cong (λ sc → P.finishP (P.pInfer imps sc [] (canonExpr b [] [] e) 0 []))
          (projSchemas-canon b polys))
    (cong P.finishP
      (pInfer-canon-top imps (P.projSchemas polys) b e))

principalGround-canon : ∀ (imps : Imports) (polys : PolyCtx)
    (b : List String) (e : RawExpr)
  → P.principalGround (ctxWithImportsAndPolys imps (canonPolysCtx b polys))
      (canonExpr b [] [] e)
    ≡ P.principalGround (ctxWithImportsAndPolys imps polys) e
principalGround-canon imps polys b e =
  cong P.pgProj (principal-canon imps polys b e)

-- Polys canonicalized, body UNTOUCHED (the PRIMITIVE-function
-- transport): pure congruence — `pInfer` cannot see poly bodies.
principalGround-polys : ∀ (imps : Imports) (polys : PolyCtx)
    (b : List String) (e : RawExpr)
  → P.principalGround (ctxWithImportsAndPolys imps (canonPolysCtx b polys)) e
    ≡ P.principalGround (ctxWithImportsAndPolys imps polys) e
principalGround-polys imps polys b e =
  cong (λ sc → P.pgProj (P.finishP (P.pInfer imps sc [] e 0 [])))
    (projSchemas-canon b polys)

-- The sig-less routing criterion (D072 M3) is canon-invariant — the
-- empty-context instance of the invariance (no imports, no schemas).
siglessSchema-canon : ∀ (b : List String) (e : RawExpr)
  → P.siglessSchema (canonExpr b [] [] e) ≡ P.siglessSchema e
siglessSchema-canon b e =
  cong (λ r → P.pgSchema (P.finishP r)) (pInfer-canon-top [] [] b e)
