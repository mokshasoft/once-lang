------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ THE CONSTRUCTOR-LIST SURFACE, elaborated into the
--               ONE-TELESCOPE kernel (SPIKE-LEVITATION S4, promoted; D072).
--
-- The kernel has ONE telescope per family: `IMu I D i` for `D : Desc I`.
-- The surface — examples, the Knot — keeps writing a constructor LIST
-- `C₀ … C_{c-1}` and one method PER constructor.  This module is the
-- elaboration, VERIFIED:
--
--   Dₗ Cs     = dσ (⌜Fin⌝ c) (λ t. sel Cs t)      -- the datatype
--   conₗ k p  = con (pair (tag k) p)                -- constructor k
--
--   (a) `⊢Dₗ`    — each `Cₖ ∷ Desc I`  ⇒  `Dₗ Cs ∷ Desc I`
--   (b) `⊢conₗ`  — `p ∷ El (dpay I D Cₖ i)`  ⇒  `conₗ k p ∷ IMu I D i`
--   (c) `sel-β`  — the constructor LOOKUP is a reduction:
--                  `app (selF Cs) (tag k) ⟶* Cₖ`
--
-- ★ `sel` is a chain of BINARY `fcase`s (the kernel's tag eliminator is
--   `Fin (suc n) ≅ 1 + Fin n`): constructor 0 at `fzero`, the rest one
--   binder further in, at the predecessor.  Canonicity (`Canonicity`'s
--   `fcaseS`) makes every closed lookup fire — what the old list form's
--   `lkp dnil k` could not.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Sugar where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-dpayᶜ; ⟶ᵀ*-El; red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-Πˡ; ⟶*-appˡ )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub; ≅ᵀ-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢wk; ⊢-cast; wk-cancel-tm; ren-ty; sub-ty; Ren⊢-ext; wk-ren; ren-lemma; Ren⊢; ∋-cast; conv-ctxᵀ )
open import DirectedHoTT.Metatheory.Premises
  using ( fsucS⊢; MethG; MethG-wf; MethCtx; MethG-sub; MethG-monoᶜ; mot-ren
        ; methSg; MethTy-wf; MethTy-MethG )
open import DirectedHoTT.Metatheory.Validity using ( wk-app-vz )
open import DirectedHoTT.Spec.Variance using ( ren-as-sub )

private
  variable
    Δ : Cx
    c k : ℕ

------------------------------------------------------------------------
-- 0. Constructor lists, tags, and the selector.
------------------------------------------------------------------------

-- a list of `c` constructor telescopes (length in the type: no length
--   lemmas at the use site)
infixr 5 _∷_
data Cons (Δ : Cx) : ℕ → Set where
  []  : Cons Δ zero
  _∷_ : RTm Δ → Cons Δ c → Cons Δ (suc c)

wkC : Cons Δ c → Cons (Δ ∙) c
wkC []       = []
wkC (C ∷ Cs) = renTm vs C ∷ wkC Cs

subC : {Θ : Cx} → Sub Δ Θ → Cons Δ c → Cons Θ c
subC σ []       = []
subC σ (C ∷ Cs) = subTm σ C ∷ subC σ Cs

-- the `k`-th tag
tag : ℕ → RTm Δ
tag zero    = fzero
tag (suc k) = fsuc (tag k)

-- the selector: `fcase` on the tag, constructor 0 at `fzero`, the rest at
--   the predecessor (one binder in)
sel : Cons Δ c → RTm Δ → RTm Δ
sel []       t = fcase0 t
sel (C ∷ Cs) t = fcase t C (sel (wkC Cs) (var vz))

selF : Cons Δ c → RTm Δ
selF Cs = lam (sel (wkC Cs) (var vz))

Dₗ : Cons Δ c → RTm Δ
Dₗ {c = c} Cs = dσ (⌜Fin⌝ c) (selF Cs)

conₗ : ℕ → RTm Δ → RTm Δ
conₗ k p = con (pair (tag k) p)

-- the `k`-th entry
data Nth : Cons Δ c → ℕ → RTm Δ → Set where
  nth-z : {C : RTm Δ} {Cs : Cons Δ c} → Nth (C ∷ Cs) zero C
  nth-s : {C C' : RTm Δ} {Cs : Cons Δ c} → Nth Cs k C → Nth (C' ∷ Cs) (suc k) C

------------------------------------------------------------------------
-- 1. ★ (c) THE LOOKUP IS A REDUCTION.
------------------------------------------------------------------------

-- substitution commutes with the list operations
subC-wkC : {Θ : Cx} (σ : Sub Δ Θ) (Cs : Cons Δ c) → subC (extS σ) (wkC Cs) ≡ wkC (subC σ Cs)
subC-wkC σ []       = refl
subC-wkC σ (C ∷ Cs) = cong₂ _∷_ (wk-sub σ C) (subC-wkC σ Cs)

sel-sub : {Θ : Cx} (σ : Sub Δ Θ) (Cs : Cons Δ c) (t : RTm Δ) →
          subTm σ (sel Cs t) ≡ sel (subC σ Cs) (subTm σ t)
sel-sub σ []       t = refl
sel-sub σ (C ∷ Cs) t =
  cong (fcase (subTm σ t) (subTm σ C))
       (trans (sel-sub (extS σ) (wkC Cs) (var vz))
              (cong (λ X → sel X (var vz)) (subC-wkC σ Cs)))

-- a weakening cancelled by the substitution that instantiates it
subC-cancel : (a : RTm Δ) (Cs : Cons Δ c) → subC (single a) (wkC Cs) ≡ Cs
subC-cancel a []       = refl
subC-cancel a (C ∷ Cs) = cong₂ _∷_ (wk-cancel-tm a C) (subC-cancel a Cs)

sel-β : {Cs : Cons Δ c} {C : RTm Δ} → Nth Cs k C → sel Cs (tag k) ⟶* C
sel-β {Cs = C ∷ Cs} nth-z = step (fcase-z C (sel (wkC Cs) (var vz))) done
sel-β {k = suc k} {Cs = C' ∷ Cs} (nth-s nt) =
  step (fcase-s (tag k) C' (sel (wkC Cs) (var vz)))
       (subst (λ X → X ⟶* _)
              (sym (trans (sel-sub (single (tag k)) (wkC Cs) (var vz))
                          (cong (λ X → sel X (tag k)) (subC-cancel (tag k) Cs))))
              (sel-β nt))

-- ★ the lookup through the selector FUNCTION: one β, then `sel-β`
selF-β : {Cs : Cons Δ c} {C : RTm Δ} → Nth Cs k C → app (selF Cs) (tag k) ⟶* C
selF-β {k = k} {Cs = Cs} nt =
  step (β (sel (wkC Cs) (var vz)) (tag k))
       (subst (λ X → X ⟶* _)
              (sym (trans (sel-sub (single (tag k)) (wkC Cs) (var vz))
                          (cong (λ X → sel X (tag k)) (subC-cancel (tag k) Cs))))
              (sel-β nt))

------------------------------------------------------------------------
-- 2. ★ (a) THE DATATYPE TYPES.
------------------------------------------------------------------------

-- every entry is a description over `I`
infixr 5 _∷ᵈ_
data AllD (Γ : Ctx) (I : RTm ⌊ Γ ⌋) : Cons ⌊ Γ ⌋ c → Set where
  []ᵈ  : AllD Γ I []
  _∷ᵈ_ : {C : RTm ⌊ Γ ⌋} {Cs : Cons ⌊ Γ ⌋ c} →
         Γ ⊢ C ∷ Desc I → AllD Γ I Cs → AllD Γ I (C ∷ Cs)

wkAllD : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {B : RTy ⌊ Γ ⌋} {Cs : Cons ⌊ Γ ⌋ c} →
         AllD Γ I Cs → AllD (Γ ▹ B) (renTm vs I) (wkC Cs)
wkAllD []ᵈ       = []ᵈ
wkAllD (d ∷ᵈ ds) = ⊢wk d ∷ᵈ wkAllD ds

private
  -- `fsucS` only touches the bound variable, so it fixes a weakened term
  fsucS-wk : {Δ : Cx} (t : RTm Δ) → subTm fsucS (renTm vs t) ≡ renTm vs t
  fsucS-wk t = trans (subTm-renTm t) (sym (ren-as-sub vs t))

-- a tag in range
data Lt : ℕ → ℕ → Set where
  lt-z : {n : ℕ} → Lt zero (suc n)
  lt-s : {n : ℕ} → Lt k n → Lt (suc k) (suc n)

nth-lt : {Cs : Cons Δ c} {C : RTm Δ} → Nth Cs k C → Lt k c
nth-lt nth-z      = lt-z
nth-lt (nth-s nt) = lt-s (nth-lt nt)

⊢tag : {Γ : Ctx} {n : ℕ} → Lt k n → Γ ⊢ tag k ∷ Fin n
⊢tag lt-z     = ⊢fzero
⊢tag (lt-s l) = ⊢fsuc (⊢tag l)

-- ★ THE SELECTION TYPES AT ANY MOTIVE.  `sel` is generic in its entries,
--   so one lemma types every use: entry `k` at `Q[tag k]`, the selection
--   at `Q[t]`.  The recursion re-bases the motive at the successor
--   (`subTy fsucS Q` — `Q ∘ fsuc`), which is why `AllQ`'s tail is typed
--   there: constructor `k+1` of `Q` is constructor `k` of `Q ∘ fsuc`.
infixr 5 _∷q_
data AllQ (Γ : Ctx) : {n : ℕ} → RTy (⌊ Γ ⌋ ∙) → Cons ⌊ Γ ⌋ n → Set where
  []q  : {Q : RTy (⌊ Γ ⌋ ∙)} → AllQ Γ {zero} Q []
  _∷q_ : {n : ℕ} {Q : RTy (⌊ Γ ⌋ ∙)} {m : RTm ⌊ Γ ⌋} {ms : Cons ⌊ Γ ⌋ n} →
         Γ ⊢ m ∷ subTy (single fzero) Q → AllQ Γ (subTy fsucS Q) ms → AllQ Γ {suc n} Q (m ∷ ms)

-- a cast of the motive (a lemma, not `subst`: `AllQ`'s length is hidden)
castQ : {Γ : Ctx} {n : ℕ} {ms : Cons ⌊ Γ ⌋ n} {Q Q' : RTy (⌊ Γ ⌋ ∙)} →
        Q ≡ Q' → AllQ Γ Q ms → AllQ Γ Q' ms
castQ refl a = a

private
  -- weakening commutes with `single fzero` and with `fsucS`
  wk-single-fzero : {Δ : Cx} (Q : RTy (Δ ∙)) →
                    subTy (single fzero) (renTy (extR vs) Q) ≡ renTy vs (subTy (single fzero) Q)
  wk-single-fzero Q = trans (subTy-renTy Q) (trans (subTy-cong pt Q) (sym (renTy-subTy Q)))
    where
      pt : ∀ x → (single fzero ₛ∘ᵣ extR vs) x ≡ (vs ᵣ∘ₛ single fzero) x
      pt vz     = refl
      pt (vs x) = refl

  wk-fsucS : {Δ : Cx} (Q : RTy (Δ ∙)) →
             subTy fsucS (renTy (extR vs) Q) ≡ renTy (extR vs) (subTy fsucS Q)
  wk-fsucS Q = trans (subTy-renTy Q) (trans (subTy-cong pt Q) (sym (renTy-subTy Q)))
    where
      pt : ∀ x → (fsucS ₛ∘ᵣ extR vs) x ≡ (extR vs ᵣ∘ₛ fsucS) x
      pt vz     = refl
      pt (vs x) = refl

wkAllQ : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {n : ℕ} {Q : RTy (⌊ Γ ⌋ ∙)} {ms : Cons ⌊ Γ ⌋ n} →
         AllQ Γ Q ms → AllQ (Γ ▹ B) (renTy (extR vs) Q) (wkC ms)
wkAllQ []q = []q
wkAllQ {Q = Q} (dm ∷q ds) =
  ⊢-cast (sym (wk-single-fzero Q)) (⊢wk dm)
  ∷q castQ (sym (wk-fsucS Q)) (wkAllQ ds)

⊢selG : {Γ : Ctx} {n : ℕ} {Q : RTy (⌊ Γ ⌋ ∙)} {ms : Cons ⌊ Γ ⌋ n} {t : RTm ⌊ Γ ⌋} →
        (Γ ▹ Fin n) ⊢ty Q → AllQ Γ Q ms → Γ ⊢ t ∷ Fin n →
        Γ ⊢ sel ms t ∷ subTy (single t) Q
⊢selG dQ []q dt = ⊢fcase0 dQ dt
⊢selG {Q = Q} dQ (dm ∷q ds) dt =
  ⊢fcase dQ dt dm
    (⊢-cast (wk-app-vz (subTy fsucS Q))
            (⊢selG (ren-ty (sub-ty dQ fsucS⊢) (Ren⊢-ext there)) (wkAllQ ds) (⊢var here)))

-- the selector types at `Desc I`: `⊢selG` at the CONSTANT motive
--   `Desc I↑`, whose instances all cancel to `Desc I`.
private
  allD→Q : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {n : ℕ} {Cs : Cons ⌊ Γ ⌋ n} →
           AllD Γ I Cs → AllQ Γ (Desc (renTm vs I)) Cs
  allD→Q []ᵈ = []q
  allD→Q {I = I} (dC ∷ᵈ ds) =
    ⊢-cast (sym (cong Desc (wk-cancel-tm fzero I))) dC
    ∷q castQ (sym (cong Desc (fsucS-wk I))) (allD→Q ds)

⊢sel : {Γ : Ctx} {I t : RTm ⌊ Γ ⌋} {Cs : Cons ⌊ Γ ⌋ c} →
       Γ ⊢ I ∷ U → AllD Γ I Cs → Γ ⊢ t ∷ Fin c → Γ ⊢ sel Cs t ∷ Desc I
⊢sel {I = I} {t = t} dI ds dt =
  ⊢-cast (cong Desc (wk-cancel-tm t I)) (⊢selG (ty-Desc (⊢wk dI)) (allD→Q ds) dt)

⊢selF : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Cs : Cons ⌊ Γ ⌋ c} →
        Γ ⊢ I ∷ U → AllD Γ I Cs → Γ ⊢ selF Cs ∷ Π (El (⌜Fin⌝ c)) (Desc (renTm vs I))
⊢selF dI ds =
  ⊢lam (ty-El ⊢⌜Fin⌝) (⊢sel (⊢wk dI) (wkAllD ds) (⊢conv (⊢var here) (credᵀ El-⌜Fin⌝)))

-- ★ (a)
⊢Dₗ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Cs : Cons ⌊ Γ ⌋ c} →
      Γ ⊢ I ∷ U → AllD Γ I Cs → Γ ⊢ Dₗ Cs ∷ Desc I
⊢Dₗ dI ds = ⊢dσ dI ⊢⌜Fin⌝ (⊢selF dI ds)

------------------------------------------------------------------------
-- 3. ★ (b) CONSTRUCTOR `k`, from a payload of ITS telescope.  The payload
--    of `Dₗ Cs` is `Σ (tag) (payload of the selected telescope)`, and the
--    selection converts to `Cₖ` (`selF-β`).
------------------------------------------------------------------------

-- ★ A PAYLOAD, ONE FIELD AT A TIME — the three telescope heads.  A
--   payload is the Σ-chain `dpay` computes; these type it head by head.
--   `ι`: the index equation (Fording is IN the payload); `σ`: a field of
--   code `S` and the rest at the selected telescope `f a`; `ρ`: a
--   recursive field at its own index, and the rest.
⊢pay-ι : {Γ : Ctx} {I D j i e : RTm ⌊ Γ ⌋} →
         Γ ⊢ e ∷ Id (El I) j i → Γ ⊢ e ∷ El (dpay I D (dι j) i)
⊢pay-ι {I = I} {D} {j} {i} de =
  ⊢conv de (csymᵀ (ctrnᵀ (credᵀ (ξ-El (dpay-ι I D j i))) (credᵀ (El-⌜Id⌝ I j i))))

⊢pay-σ : {Γ : Ctx} {I D S f i a p : RTm ⌊ Γ ⌋} →
         Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → Γ ⊢ f ∷ Π (El S) (Desc (renTm vs I)) → Γ ⊢ i ∷ El I →
         Γ ⊢ a ∷ El S → Γ ⊢ p ∷ El (dpay I D (app f a) i) →
         Γ ⊢ pair a p ∷ El (dpay I D (dσ S f) i)
⊢pay-σ {Γ = Γ} {I = I} {D = D} {S = S} {f = f} {i = i} {a = a} dI dD df di da dp =
  ⊢conv (⊢pair dB da dp') cv
  where
    dapp : (Γ ▹ El S) ⊢ app (renTm vs f) (var vz) ∷ Desc (renTm vs I)
    dapp = ⊢-cast (wk-app-vz (Desc (renTm vs I))) (⊢app (⊢wk df) (⊢var here))
    dB = ty-El (⊢dpay (⊢wk dI) (⊢wk dD) dapp (⊢wk di))
    dp' = ⊢-cast (sym (cong₄ (λ x y g k → El (dpay x y (app g a) k))
                             (wk-cancel-tm a I) (wk-cancel-tm a D)
                             (wk-cancel-tm a f) (wk-cancel-tm a i)))
                 dp
    cv = csymᵀ (ctrnᵀ (credᵀ (ξ-El (dpay-σ I D S f i))) (credᵀ (El-⌜Σ⌝ _ _)))

-- the common case `f = λ C`: the rest at `C[a]`, one β away
⊢pay-σλ : {Γ : Ctx} {I D S i a p : RTm ⌊ Γ ⌋} {C : RTm (⌊ Γ ⌋ ∙)} →
          Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → Γ ⊢ lam C ∷ Π (El S) (Desc (renTm vs I)) → Γ ⊢ i ∷ El I →
          Γ ⊢ a ∷ El S → Γ ⊢ p ∷ El (dpay I D (subTm (single a) C) i) →
          Γ ⊢ pair a p ∷ El (dpay I D (dσ S (lam C)) i)
⊢pay-σλ {a = a} {C = C} dI dD df di da dp =
  ⊢pay-σ dI dD df di da (⊢conv dp (csymᵀ (credᵀ (ξ-El (ξ-dpayᶜ (β C a))))))

⊢pay-ρ : {Γ : Ctx} {I D j C i r p : RTm ⌊ Γ ⌋} →
         Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → Γ ⊢ C ∷ Desc I → Γ ⊢ i ∷ El I →
         Γ ⊢ r ∷ IMu I D j → Γ ⊢ p ∷ El (dpay I D C i) →
         Γ ⊢ pair r p ∷ El (dpay I D (dρ j C) i)
⊢pay-ρ {Γ = Γ} {I = I} {D = D} {j = j} {C = C} {i = i} {r = r} dI dD dC di dr dp =
  ⊢conv (⊢pair dB (⊢conv dr (csymᵀ (credᵀ El-⌜IMu⌝))) dp') cv
  where
    dB = ty-El (⊢dpay (⊢wk dI) (⊢wk dD) (⊢wk dC) (⊢wk di))
    dp' = ⊢-cast (sym (cong₄ (λ x y z k → El (dpay x y z k))
                             (wk-cancel-tm r I) (wk-cancel-tm r D)
                             (wk-cancel-tm r C) (wk-cancel-tm r i)))
                 dp
    cv = csymᵀ (ctrnᵀ (credᵀ (ξ-El (dpay-ρ I D j C i))) (credᵀ (El-⌜Σ⌝ _ _)))

-- ★ a constructor of a `dσ` family from a (tag , payload) pair, for ANY
--   tag term: the payload lives at the SELECTED telescope `f t`.
⊢con-σ : {Γ : Ctx} {I S f i t p : RTm ⌊ Γ ⌋} →
         Γ ⊢ I ∷ U → Γ ⊢ S ∷ U → Γ ⊢ f ∷ Π (El S) (Desc (renTm vs I)) → Γ ⊢ i ∷ El I →
         Γ ⊢ t ∷ El S → Γ ⊢ p ∷ El (dpay I (dσ S f) (app f t) i) →
         Γ ⊢ con (pair t p) ∷ IMu I (dσ S f) i
⊢con-σ dI dS df di dt dp = ⊢con dI dD di (⊢pay-σ dI dD df di dt dp)
  where dD = ⊢dσ dI dS df

-- ★ (b) constructor `k` of the list form: `⊢con-σ` at `tag k`, the
--   selection converted to `Cₖ` (`selF-β`)
⊢conₗ : {Γ : Ctx} {I i p C : RTm ⌊ Γ ⌋} {Cs : Cons ⌊ Γ ⌋ c} →
        Γ ⊢ I ∷ U → AllD Γ I Cs → Γ ⊢ i ∷ El I → Nth Cs k C →
        Γ ⊢ p ∷ El (dpay I (Dₗ Cs) C i) → Γ ⊢ conₗ k p ∷ IMu I (Dₗ Cs) i
⊢conₗ dI ds di nt dp =
  ⊢con-σ dI ⊢⌜Fin⌝ (⊢selF dI ds) di (⊢conv (⊢tag (nth-lt nt)) (csymᵀ (credᵀ El-⌜Fin⌝)))
         (⊢conv dp (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β nt))))))

------------------------------------------------------------------------
-- 4. ★ THE ONE METHOD, from one method PER CONSTRUCTOR.
--
--      methₗ ms = λ i q. psplit (λ t p'. (sel (msᵢ) t) p') q
--
--    where `msᵢ` is each per-constructor method applied to the index.
--    `psplit` is REQUIRED: the kernel has no Σ-η (D071), so the payload
--    `q` must be split before the selection can see its tag; `sel`'s
--    motive abstracts the payload and the hypotheses, whose types depend
--    on the tag.
------------------------------------------------------------------------

-- ★ the method type of constructor `k` with telescope `C`: the kernel's
--   `MethTy` with `C` for the whole telescope and `conₗ k` for `con`
--   (`Premises.MethG`, the general form).
MethK : RTm Δ → RTm Δ → RTy ((Δ ∙) ∙) → RTm Δ → ℕ → RTy Δ
MethK I D M C k = MethG I D M C (conₗ k (var (vs vz)))

-- ★ the TAG-GENERIC method type, over the tag: the selected telescope
--   `f tag`, and the scrutinee `con (tag , p)`.  The motive of the method
--   selection; `MethK … Cₖ k` converts to its instance at `tag k`.
MethT : RTm Δ → RTm Δ → RTy ((Δ ∙) ∙) → RTm Δ → RTy (Δ ∙)
MethT I D M f =
  MethG (renTm vs I) (renTm vs D) (renTy (extR (extR vs)) M) (app (renTm vs f) (var vz))
        (con (pair (var (vs (vs (vs vz)))) (var (vs vz))))

-- the method SELECTOR: a function of the tag, like `selF`
selM : Cons Δ c → RTm Δ
selM ms = lam (sel (wkC ms) (var vz))

-- ★ THE ONE METHOD
methₗ : Cons Δ c → RTm Δ
methₗ ms =
  lam (lam (psplit (app (app (app (renTm (λ x → vs (vs (vs (vs x)))) (selM ms))
                                  (var (vs vz)))
                             (var (vs (vs (vs vz)))))
                        (var vz))
                   (var vz)))

------------------------------------------------------------------------
-- 5. The selection's motive, shifted, and the per-constructor method
--    type as an INSTANCE of the tag-generic one.
------------------------------------------------------------------------

-- iterated successor; the tags are its instances at `fzero`
fsucs : ℕ → RTm Δ → RTm Δ
fsucs zero    t = t
fsucs (suc k) t = fsuc (fsucs k t)

tag-fsucs : (k : ℕ) → tag {Δ} k ≡ fsucs k fzero
tag-fsucs zero    = refl
tag-fsucs (suc k) = cong fsuc (tag-fsucs k)

fsucs-fsuc : (k : ℕ) (t : RTm Δ) → fsucs k (fsuc t) ≡ fsuc (fsucs k t)
fsucs-fsuc zero    t = refl
fsucs-fsuc (suc k) t = cong fsuc (fsucs-fsuc k t)

fsucs-sub : {Θ : Cx} (σ : Sub Δ Θ) (k : ℕ) (t : RTm Δ) → subTm σ (fsucs k t) ≡ fsucs k (subTm σ t)
fsucs-sub σ zero    t = refl
fsucs-sub σ (suc k) t = cong fsuc (fsucs-sub σ k t)

-- a tag is CLOSED
tag-ren : {Θ : Cx} (ρ : Ren Δ Θ) (k : ℕ) → renTm ρ (tag k) ≡ tag k
tag-ren ρ zero    = refl
tag-ren ρ (suc k) = cong fsuc (tag-ren ρ k)

-- the motive re-based at the `k`-th successor: constructor `k` of `Q` is
--   constructor 0 of `Q ∘ fsucᵏ`
fsucsS : ℕ → Sub (Δ ∙) (Δ ∙)
fsucsS k vz     = fsucs k (var vz)
fsucsS k (vs x) = var (vs x)

fsucsS-zero : (Q : RTy (Δ ∙)) → subTy (fsucsS zero) Q ≡ Q
fsucsS-zero Q = trans (subTy-cong pt Q) (subTy-id Q)
  where
    pt : ∀ x → fsucsS zero x ≡ idₛ x
    pt vz     = refl
    pt (vs x) = refl

fsucsS-suc : (k : ℕ) (Q : RTy (Δ ∙)) → subTy fsucS (subTy (fsucsS k) Q) ≡ subTy (fsucsS (suc k)) Q
fsucsS-suc k Q = trans (subTy-subTy Q) (subTy-cong pt Q)
  where
    pt : ∀ x → (fsucS ∘ₛ fsucsS k) x ≡ fsucsS (suc k) x
    pt vz     = trans (fsucs-sub fsucS k (var vz)) (fsucs-fsuc k (var vz))
    pt (vs x) = refl

fsucsS-head : (k : ℕ) (Q : RTy (Δ ∙)) →
              subTy (single fzero) (subTy (fsucsS k) Q) ≡ subTy (single (tag k)) Q
fsucsS-head k Q = trans (subTy-subTy Q) (subTy-cong pt Q)
  where
    pt : ∀ x → (single fzero ∘ₛ fsucsS k) x ≡ single (tag k) x
    pt vz     = trans (fsucs-sub (single fzero) k (var vz)) (sym (tag-fsucs k))
    pt (vs x) = refl

-- a weakening past the tag's binder commutes with instantiating at a tag
wk-single-tag : (k : ℕ) (X : RTy (Δ ∙)) →
                subTy (single (tag k)) (renTy (extR vs) X) ≡ renTy vs (subTy (single (tag k)) X)
wk-single-tag k X = trans (subTy-renTy X) (trans (subTy-cong pt X) (sym (renTy-subTy X)))
  where
    pt : ∀ x → (single (tag k) ₛ∘ᵣ extR vs) x ≡ (vs ᵣ∘ₛ single (tag k)) x
    pt vz     = sym (tag-ren vs k)
    pt (vs x) = refl

private
  cong₅ : {A B C D E F : Set} (g : A → B → C → D → E → F)
          {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → g a b c d e ≡ g a' b' c' d' e'
  cong₅ g refl refl refl refl refl = refl

  -- the motive under the tag's binder, weakened then instantiated: itself
  M-cancel : (a : RTm Δ) (M : RTy ((Δ ∙) ∙)) →
             subTy (extS (extS (single a))) (renTy (extR (extR vs)) M) ≡ M
  M-cancel a M = trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-id M))
    where
      pt : ∀ x → (extS (extS (single a)) ₛ∘ᵣ extR (extR vs)) x ≡ idₛ x
      pt vz          = refl
      pt (vs vz)     = refl
      pt (vs (vs x)) = refl

-- ★ the tag-generic method type at `tag k` IS constructor `k`'s, with the
--   selection `f (tag k)` for its telescope
MethT-inst : (I D : RTm Δ) (M : RTy ((Δ ∙) ∙)) (f : RTm Δ) (k : ℕ) →
             subTy (single (tag k)) (MethT I D M f)
             ≡ MethG I D M (app f (tag k)) (conₗ k (var (vs vz)))
MethT-inst I D M f k =
  trans (MethG-sub (single (tag k)) (renTm vs I) (renTm vs D) (renTy (extR (extR vs)) M)
                   (app (renTm vs f) (var vz)) (con (pair (var (vs (vs (vs vz)))) (var (vs vz)))))
        (cong₅ MethG (wk-cancel-tm (tag k) I) (wk-cancel-tm (tag k) D) (M-cancel (tag k) M)
                     (cong (λ g → app g (tag k)) (wk-cancel-tm (tag k) f))
                     (cong (λ z → con (pair z (var (vs vz))))
                           (trans (cong (λ z → renTm vs (renTm vs z)) (tag-ren vs k))
                                  (trans (cong (renTm vs) (tag-ren vs k)) (tag-ren vs k)))))

-- ★ constructor `k`'s method type converts to the tag-generic one's
--   instance: the lookup `f (tag k) ⟶* Cₖ` inside `dpay`/`DIh`
MethK≅T : {I D f C : RTm Δ} {M : RTy ((Δ ∙) ∙)} (k : ℕ) → app f (tag k) ⟶* C →
          MethK I D M C k ≅ᵀ subTy (single (tag k)) (MethT I D M f)
MethK≅T {I = I} {D} {f} {C} {M} k r =
  subst (λ X → MethK I D M C k ≅ᵀ X) (sym (MethT-inst I D M f k))
        (csymᵀ (red→≅ᵀ (MethG-monoᶜ r)))

------------------------------------------------------------------------
-- 6. ★ THE METHOD SELECTOR TYPES.
------------------------------------------------------------------------

-- conversions are stable under a renaming
≅ᵀ-ren : {Θ : Cx} (ρ : Ren Δ Θ) {A B : RTy Δ} → A ≅ᵀ B → renTy ρ A ≅ᵀ renTy ρ B
≅ᵀ-ren ρ {A} {B} c =
  subst (λ X → X ≅ᵀ renTy ρ B) (subTy-var ρ A)
        (subst (λ X → subTy ⟨ ρ ⟩ᵣ A ≅ᵀ X) (subTy-var ρ B) (≅ᵀ-sub ⟨ ρ ⟩ᵣ c))

-- weakening a selector keeps its codomain a WEAKENING of the index code
--   (`⊢wk` alone leaves `renTm (extR vs)` towers)
⊢wkF : {Γ : Ctx} {B : RTy ⌊ Γ ⌋} {S I f : RTm ⌊ Γ ⌋} →
       Γ ⊢ f ∷ Π (El S) (Desc (renTm vs I)) →
       (Γ ▹ B) ⊢ renTm vs f ∷ Π (El (renTm vs S)) (Desc (renTm vs (renTm vs I)))
⊢wkF {S = S} {I = I} df =
  ⊢-cast (cong (λ z → Π (El (renTm vs S)) (Desc z)) (wk-ren vs I)) (⊢wk df)

-- the tag-generic method type is well-formed over the tag
MethT-wf : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {Cs : Cons ⌊ Γ ⌋ c} →
           Γ ⊢ I ∷ U → AllD Γ I Cs → motCtx Γ I (Dₗ Cs) ⊢ty M →
           (Γ ▹ Fin c) ⊢ty MethT I (Dₗ Cs) M (selF Cs)
MethT-wf {c = c} {Γ = Γ} {I = I} {M = M} {Cs = Cs} dI ds dM =
  MethG-wf (⊢wk dI) (⊢wk dD) dC (mot-ren there dM)
           (⊢con-σ (⊢wk (⊢wk (⊢wk (⊢wk dI)))) ⊢⌜Fin⌝ (⊢wkF (⊢wkF (⊢wkF (⊢wkF df))))
                   (⊢var (there (there here)))
                   (⊢conv (⊢var (there (there (there here)))) (csymᵀ (credᵀ El-⌜Fin⌝)))
                   (⊢var (there here)))
  where
    D = Dₗ Cs
    f = selF Cs
    df = ⊢selF dI ds
    dD = ⊢Dₗ dI ds
    dC : (Γ ▹ Fin c) ⊢ app (renTm vs f) (var vz) ∷ Desc (renTm vs I)
    dC = ⊢-cast (wk-app-vz (Desc (renTm vs I)))
                (⊢app (⊢wk df) (⊢conv (⊢var here) (csymᵀ (credᵀ El-⌜Fin⌝))))

-- ★ one method PER CONSTRUCTOR, each at ITS constructor's method type,
--   with the selection's lookup for that constructor (`selF-β` gives it
--   from an `Nth`)
infixr 5 _∷ₘ_
data PerK (Γ : Ctx) (I D : RTm ⌊ Γ ⌋) (M : RTy ((⌊ Γ ⌋ ∙) ∙)) (f : RTm ⌊ Γ ⌋) :
          ℕ → {n : ℕ} → Cons ⌊ Γ ⌋ n → Set where
  []ₘ  : {k : ℕ} → PerK Γ I D M f k []
  _∷ₘ_ : {k n : ℕ} {C m : RTm ⌊ Γ ⌋} {ms : Cons ⌊ Γ ⌋ n} →
         (app f (tag k) ⟶* C) × (Γ ⊢ m ∷ MethK I D M C k) →
         PerK Γ I D M f (suc k) ms → PerK Γ I D M f k (m ∷ ms)

mkAllQ : {Γ : Ctx} {I D f : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {B : RTy ⌊ Γ ⌋} {k n : ℕ}
         {ms : Cons ⌊ Γ ⌋ n} → PerK Γ I D M f k ms →
         AllQ (Γ ▹ B) (subTy (fsucsS k) (renTy (extR vs) (MethT I D M f))) (wkC ms)
mkAllQ []ₘ = []q
mkAllQ {I = I} {D} {f} {M} {k = k} ((r , dm) ∷ₘ ps) =
  ⊢-cast (sym (trans (fsucsS-head k (renTy (extR vs) (MethT I D M f)))
                     (wk-single-tag k (MethT I D M f))))
         (⊢conv (⊢wk dm) (≅ᵀ-ren vs (MethK≅T k r)))
  ∷q castQ (sym (fsucsS-suc k (renTy (extR vs) (MethT I D M f)))) (mkAllQ ps)

-- ★ the SELECTOR: a function of the tag, at the tag-generic method type
⊢selM : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {Cs ms : Cons ⌊ Γ ⌋ c} →
        Γ ⊢ I ∷ U → AllD Γ I Cs → motCtx Γ I (Dₗ Cs) ⊢ty M →
        PerK Γ I (Dₗ Cs) M (selF Cs) zero ms →
        Γ ⊢ selM ms ∷ Π (El (⌜Fin⌝ c)) (MethT I (Dₗ Cs) M (selF Cs))
⊢selM {I = I} {M = M} {Cs = Cs} dI ds dM ps =
  ⊢lam (ty-El ⊢⌜Fin⌝)
       (⊢-cast (wk-app-vz MT)
               (⊢selG (ren-ty (MethT-wf dI ds dM) (Ren⊢-ext there))
                      (castQ (fsucsS-zero (renTy (extR vs) MT)) (mkAllQ ps))
                      (⊢conv (⊢var here) (credᵀ El-⌜Fin⌝))))
  where
    MT = MethT I (Dₗ Cs) M (selF Cs)

------------------------------------------------------------------------
-- 7. ★★ (c) THE ONE METHOD TYPES, and (d) THE DERIVED ι.
--
--   `⊢methₗ`: from one method per constructor (each at ITS constructor's
--   method type), the one method `methₗ` inhabits the kernel's `MethTy`.
--   The split's branch is the selector at (tag, index, payload); its
--   hypotheses' type at the whole telescope computes (`DIh-σ`, `βfst`,
--   `βsnd`) to the one at the selection, and every other obligation is a
--   weakening/substitution identity checked POINTWISE by `refl` after
--   flattening each side to one substitution (the S4 technique).
--
--   `ιₗ`: at constructor `k`, the one method IS constructor `k`'s method —
--   ι, two β, the split, then the tag selection (`selF-β`: `selM` is
--   `selF` at the methods).
------------------------------------------------------------------------

private
  Π-cod : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} → Γ ⊢ty Π A B → (Γ ▹ A) ⊢ty B
  Π-cod (ty-Π _ d) = d

  w4 : {Δ : Cx} → Ren Δ ((((Δ ∙) ∙) ∙) ∙)
  w4 x = vs (vs (vs (vs x)))

  -- four weakenings are one renaming
  ren4 : {Δ : Cx} (t : RTm Δ) → renTm vs (renTm vs (renTm vs (renTm vs t))) ≡ renTm w4 t
  ren4 t = trans (cong (λ z → renTm vs (renTm vs z)) (renTm-renTm t))
                 (trans (cong (renTm vs) (renTm-renTm t)) (renTm-renTm t))

  ren4ᵀ : {Δ : Cx} (A : RTy Δ) → renTy vs (renTy vs (renTy vs (renTy vs A))) ≡ renTy w4 A
  ren4ᵀ A = trans (cong (λ z → renTy vs (renTy vs z)) (renTy-renTy A))
                  (trans (cong (renTy vs) (renTy-renTy A)) (renTy-renTy A))


⊢methₗ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {Cs ms : Cons ⌊ Γ ⌋ c} →
         Γ ⊢ I ∷ U → AllD Γ I Cs → motCtx Γ I (Dₗ Cs) ⊢ty M →
         PerK Γ I (Dₗ Cs) M (selF Cs) zero ms →
         Γ ⊢ methₗ ms ∷ MethTy I (Dₗ Cs) M
⊢methₗ {c = c} {Γ = Γ} {I = I} {M = M} {Cs = Cs} {ms = ms} dI ds dM ps =
  subst (λ X → Γ ⊢ methₗ ms ∷ X) (sym (MethTy-MethG I D M))
    (⊢lam (ty-El dI) (⊢lam dP₁ (⊢-cast eqP (⊢psplit dA dB dP dq db))))
  where
    D = Dₗ Cs
    S = ⌜Fin⌝ {⌊ Γ ⌋} c
    f = selF Cs
    dD = ⊢Dₗ dI ds
    df = ⊢selF dI ds
    P₁ = El (dpay (renTm vs I) (renTm vs D) (renTm vs D) (var vz))
    dP₁ = ty-El (⊢dpay (⊢wk dI) (⊢wk dD) (⊢wk dD) (⊢var here))
    Γ₂ = (Γ ▹ El I) ▹ P₁
    s₁ : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)
    s₁ = con (var (vs vz))
    T : RTy ⌊ Γ₂ ⌋
    T = Π (DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs (renTm vs D)) (var vz)) (subTy (methSg s₁) M)
    dT : Γ₂ ⊢ty T
    dT = Π-cod (Π-cod (subst (λ X → Γ ⊢ty X) (MethTy-MethG I D M) (MethTy-wf dI dD dM)))
    I₂ = renTm vs (renTm vs I)
    D₂ = renTm vs (renTm vs D)
    f₂ = renTm vs (renTm vs f)
    Q₂ = renTy vs P₁
    A = El (⌜Fin⌝ {⌊ Γ₂ ⌋} c)
    B = El (dpay (renTm vs I₂) (renTm vs D₂) (app (renTm vs f₂) (var vz)) (var (vs (vs vz))))
    cvq : Q₂ ≅ᵀ Σ' A B
    cvq = ctrnᵀ (credᵀ (ξ-El (dpay-σ I₂ D₂ (⌜Fin⌝ c) f₂ (var (vs vz))))) (credᵀ (El-⌜Σ⌝ _ _))
    dq = ⊢conv (⊢var here) cvq
    dA = ty-El (⊢⌜Fin⌝ {n = c})
    dI₂ = ⊢wk (⊢wk dI)
    dD₂ = ⊢wk (⊢wk dD)
    dB : (Γ₂ ▹ A) ⊢ty B
    dB = ty-El (⊢dpay (⊢wk dI₂) (⊢wk dD₂)
                      (⊢-cast (cong Desc (wk-cancel-tm (var vz) (renTm vs I₂)))
                              (⊢app (⊢wkF (⊢wkF (⊢wkF df))) (⊢var here)))
                      (⊢var (there (there here))))
    -- the motive: the method type's inner Π, its payload variable read as
    --   the Σ variable
    ρP : Ren ⌊ Γ₂ ⌋ (⌊ Γ₂ ⌋ ∙)
    ρP vz     = vz
    ρP (vs y) = vs (vs y)
    hρP : Ren⊢ Γ₂ (Γ₂ ▹ Q₂) ρP
    hρP here = ∋-cast (trans (renTy-renTy P₁) (sym (renTy-renTy P₁))) here
    hρP (there {A = A₀} v) = ∋-cast (trans (renTy-renTy A₀) (sym (renTy-renTy A₀))) (there (there v))
    dP : (Γ₂ ▹ Σ' A B) ⊢ty renTy ρP T
    dP = conv-ctxᵀ cvq (ren-ty dT hρP)
    eqP : subTy (single (var vz)) (renTy ρP T) ≡ T
    eqP = trans (subTy-renTy T) (trans (subTy-cong pt T) (subTy-id T))
      where
        pt : ∀ x → (single (var vz) ₛ∘ᵣ ρP) x ≡ idₛ x
        pt vz     = refl
        pt (vs y) = refl
    -- ── the branch: the selector at the tag, the index, the payload ──
    Γ₄ = (Γ₂ ▹ A) ▹ B
    MT = MethT I D M f
    h4 : Ren⊢ Γ Γ₄ w4
    h4 {A = A₀} v = ∋-cast (ren4ᵀ A₀) (there (there (there (there v))))
    dF : Γ₄ ⊢ renTm w4 (selM ms) ∷ Π (El (⌜Fin⌝ c)) (renTy (extR w4) MT)
    dF = ren-lemma (⊢selM dI ds dM ps) h4
    t : RTm ⌊ Γ₄ ⌋
    t = var (vs vz)
    i : RTm ⌊ Γ₄ ⌋
    i = var (vs (vs (vs vz)))
    I₄ = renTm w4 I
    D₄ = renTm w4 D
    f₄ = renTm w4 f
    M₄ = renTy (extR (extR w4)) M
    s₄ : RTm ((((⌊ Γ₄ ⌋ ∙) ∙) ∙))
    s₄ = con (pair (var (vs (vs (vs (vs vz))))) (var (vs vz)))
    τ = single t ₛ∘ᵣ extR w4
    wk-τ : (x : RTm ⌊ Γ ⌋) → subTm τ (renTm vs x) ≡ renTm w4 x
    wk-τ x = trans (subTm-renTm x) (subTm-var w4 x)
    E1 : subTy (single t) (renTy (extR w4) MT) ≡ MethG I₄ D₄ M₄ (app f₄ t) s₄
    E1 = trans (subTy-renTy MT)
           (trans (MethG-sub τ (renTm vs I) (renTm vs D) (renTy (extR (extR vs)) M)
                             (app (renTm vs f) (var vz)) (con (pair (var (vs (vs (vs vz)))) (var (vs vz)))))
                  (cong₅ MethG (wk-τ I) (wk-τ D) eM (cong (λ g → app g t) (wk-τ f)) refl))
      where
        eM : subTy (extS (extS τ)) (renTy (extR (extR vs)) M) ≡ M₄
        eM = trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-var (extR (extR w4)) M))
          where
            pt : ∀ x → (extS (extS τ) ₛ∘ᵣ extR (extR vs)) x ≡ ⟨ extR (extR w4) ⟩ᵣ x
            pt vz          = refl
            pt (vs vz)     = refl
            pt (vs (vs x)) = refl
    d1 = ⊢-cast E1 (⊢app dF (⊢var (there here)))
    di : Γ₄ ⊢ i ∷ El I₄
    di = ⊢-cast (cong El (ren4 I)) (⊢var (there (there (there here))))
    C₄ = app f₄ t
    d2 = ⊢app d1 di
    dp : Γ₄ ⊢ var vz ∷ El (dpay I₄ D₄ C₄ i)
    dp = ⊢-cast (cong₃ (λ a b g → El (dpay a b (app g t) i)) (ren4 I) (ren4 D) (ren4 f)) (⊢var here)
    Y : RTy (⌊ Γ₄ ⌋ ∙)
    Y = Π (subTy (extS (single i)) (DIh (renTm vs (renTm vs D₄)) (wk2M M₄) (renTm vs (renTm vs C₄)) (var vz)))
          (subTy (extS (extS (single i))) (subTy (methSg s₄) M₄))
    d2' = ⊢-cast (cong (λ X → Π X Y)
                       (cong₃ (λ a b g → El (dpay a b g i))
                              (wk-cancel-tm i I₄) (wk-cancel-tm i D₄) (wk-cancel-tm i C₄)))
                 d2
    d3 = ⊢app d2' dp
    p' : RTm ⌊ Γ₄ ⌋
    p' = var vz
    -- ── the two domains, and the one codomain ──
    Gc = subTy (extS pairS) (renTy (extR ρP) (subTy (methSg s₁) M))
    cancel2 : (x : RTm ⌊ Γ₄ ⌋) → subTm (single p') (subTm (extS (single i)) (renTm vs (renTm vs x))) ≡ x
    cancel2 x = trans (cong (subTm (single p')) (trans (wk-sub (single i) (renTm vs x))
                                                       (cong (renTm vs) (wk-cancel-tm i x))))
                      (wk-cancel-tm p' x)
    domL : subTy (single p') (subTy (extS (single i))
             (DIh (renTm vs (renTm vs D₄)) (wk2M M₄) (renTm vs (renTm vs C₄)) (var vz)))
           ≡ DIh D₄ M₄ C₄ p'
    domL = cong₄ DIh (cancel2 D₄) eM (cancel2 C₄) refl
      where
        eM : subTy (extS (extS (single p'))) (subTy (extS (extS (extS (single i)))) (wk2M M₄)) ≡ M₄
        eM = trans (cong (subTy (extS (extS (single p')))) (subTy-renTy M₄))
               (trans (subTy-subTy M₄) (trans (subTy-cong pt M₄) (subTy-id M₄)))
          where
            pt : ∀ x → (extS (extS (single p')) ∘ₛ
                        (extS (extS (extS (single i))) ₛ∘ᵣ extR (extR (λ y → vs (vs y))))) x ≡ idₛ x
            pt vz          = refl
            pt (vs vz)     = refl
            pt (vs (vs x)) = refl
    domR : subTy pairS (renTy ρP (DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs (renTm vs D)) (var vz)))
           ≡ DIh D₄ M₄ D₄ (pair t p')
    domR = cong₄ DIh eD eM eD refl
      where
        eD : subTm pairS (renTm ρP (renTm vs (renTm vs D))) ≡ D₄
        eD = trans (cong (subTm pairS) (trans (renTm-renTm (renTm vs D)) (renTm-renTm D)))
                   (trans (subTm-renTm D) (trans (subTm-cong (λ x → refl) D) (subTm-var w4 D)))
        eM : subTy (extS (extS pairS)) (renTy (extR (extR ρP)) (wk2M M)) ≡ M₄
        eM = trans (cong (subTy (extS (extS pairS))) (renTy-renTy M))
               (trans (subTy-renTy M) (trans (subTy-cong pt M) (subTy-var (extR (extR w4)) M)))
          where
            pt : ∀ x → (extS (extS pairS) ₛ∘ᵣ (extR (extR ρP) ∘ᵣ extR (extR (λ y → vs (vs y))))) x
                       ≡ ⟨ extR (extR w4) ⟩ᵣ x
            pt vz          = refl
            pt (vs vz)     = refl
            pt (vs (vs x)) = refl
    cod : subTy (extS (single p')) (subTy (extS (extS (single i))) (subTy (methSg s₄) M₄)) ≡ Gc
    cod = trans (cong (λ z → subTy (extS (single p')) (subTy (extS (extS (single i))) z)) (subTy-renTy M))
            (trans (cong (subTy (extS (single p'))) (subTy-subTy M))
              (trans (subTy-subTy M)
                (trans (subTy-cong pt M)
                  (sym (trans (cong (subTy (extS pairS)) (renTy-subTy M)) (subTy-subTy M))))))
      where
        pt : ∀ x → (extS (single p') ∘ₛ (extS (extS (single i)) ∘ₛ (methSg s₄ ₛ∘ᵣ extR (extR w4)))) x
                   ≡ (extS pairS ∘ₛ (extR ρP ᵣ∘ₛ methSg s₁)) x
        pt vz          = refl
        pt (vs vz)     = refl
        pt (vs (vs x)) = refl
    -- the hypotheses at the whole telescope compute to those at the selection
    red : DIh D₄ M₄ D₄ (pair t p') ⟶ᵀ* DIh D₄ M₄ C₄ p'
    red = stepᵀ (DIh-σ D₄ M₄ (⌜Fin⌝ c) f₄ (pair t p'))
            (stepᵀ (ξ-DIhᶜ (ξ-appʳ (βfst t p'))) (stepᵀ (ξ-DIhᵖ (βsnd t p')) doneᵀ))
    cvfinal : subTy (single p') Y ≅ᵀ subTy pairS (renTy ρP T)
    cvfinal = subst (λ X → X ≅ᵀ subTy pairS (renTy ρP T)) (sym (cong₂ Π domL cod))
                (subst (λ X → Π (DIh D₄ M₄ C₄ p') Gc ≅ᵀ X) (sym (cong (λ X → Π X Gc) domR))
                  (csymᵀ (red→≅ᵀ (⟶ᵀ*-Πˡ red))))
    db : Γ₄ ⊢ app (app (app (renTm w4 (selM ms)) t) i) (var vz) ∷ subTy pairS (renTy ρP T)
    db = ⊢conv d3 cvfinal

-- ★ THE DERIVED ι: the one method at constructor `k` IS constructor `k`'s
--   method — ι, two β, the split, and the tag selection.
ιₗ : {Δ : Cx} {k : ℕ} {D i p m : RTm Δ} {ms : Cons Δ c} → Nth ms k m →
     ielim D i (methₗ ms) (conₗ k p)
       ⟶* app (app (app m i) p) (dih D (methₗ ms) D (pair (tag k) p))
ιₗ {Δ = Δ} {k = k} {D = D} {i = i} {p = p} {m = m} {ms = ms} nt =
  step (ι D i e q)
   (step (ξ-appˡ (ξ-appˡ (β (lam (psplit b (var vz))) i)))
    (step (ξ-appˡ (β (psplit b₁ (var vz)) q))
     (step (ξ-appˡ (psplit-β b₂ (tag k) p))
      (subst (λ z → app z h ⟶* app (app (app m i) p) h) (sym E)
             (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (selF-β nt))))))))
  where
    e = methₗ ms
    q = pair (tag k) p
    h = dih D e D q
    b : RTm ((((Δ ∙) ∙) ∙) ∙)
    b = app (app (app (renTm w4 (selM ms)) (var (vs vz))) (var (vs (vs (vs vz))))) (var vz)
    b₁ = subTm (extS (extS (extS (single i)))) b
    b₂ = subTm (extS (extS (single q))) b₁
    -- the three substitutions undo the weakenings
    L4 : (X : RTm Δ) → subTm (single2 (tag k) p) (subTm (extS (extS (single q)))
                         (subTm (extS (extS (extS (single i)))) (renTm w4 X))) ≡ X
    L4 X = trans (cong (λ z → subTm (single2 (tag k) p) (subTm (extS (extS (single q))) z)) (subTm-renTm X))
             (trans (cong (subTm (single2 (tag k) p)) (subTm-subTm X))
               (trans (subTm-subTm X) (trans (subTm-cong pt X) (subTm-id X))))
      where
        pt : ∀ x → (single2 (tag k) p ∘ₛ (extS (extS (single q)) ∘ₛ (extS (extS (extS (single i))) ₛ∘ᵣ w4))) x ≡ idₛ x
        pt x = refl
    L3 : (X : RTm Δ) → subTm (single2 (tag k) p) (subTm (extS (extS (single q)))
                         (renTm vs (renTm vs (renTm vs X)))) ≡ X
    L3 X = trans (cong (λ z → subTm (single2 (tag k) p) (subTm (extS (extS (single q))) z))
                       (trans (cong (renTm vs) (renTm-renTm X)) (renTm-renTm X)))
             (trans (cong (subTm (single2 (tag k) p)) (subTm-renTm X))
               (trans (subTm-subTm X) (trans (subTm-cong pt X) (subTm-id X))))
      where
        pt : ∀ x → (single2 (tag k) p ∘ₛ (extS (extS (single q)) ₛ∘ᵣ (vs ∘ᵣ (vs ∘ᵣ vs)))) x ≡ idₛ x
        pt x = refl
    E : subTm (single2 (tag k) p) b₂ ≡ app (app (app (selM ms) (tag k)) i) p
    E = cong₂ app (cong₂ app (cong₂ app (L4 (selM ms)) refl) (L3 i)) refl
