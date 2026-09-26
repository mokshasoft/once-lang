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
  using ( ⟶*-trans; ⟶*-dpayᶜ; ⟶ᵀ*-El; red→≅ᵀ )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub; ≅ᵀ-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast; wk-cancel-tm; ren-ty; sub-ty; Ren⊢-ext; wk-ren )
open import DirectedHoTT.Metatheory.Premises
  using ( fsucS⊢; MethG; MethG-wf; MethCtx; MethG-sub; MethG-monoᶜ; mot-ren )
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

-- ★ a constructor of a `dσ` family from a (tag , payload) pair, for ANY
--   tag term: the payload lives at the SELECTED telescope `f t`.  Kept
--   abstract in `S`/`f`, so it types under any renaming unchanged.
⊢con-σ : {Γ : Ctx} {I S f i t p : RTm ⌊ Γ ⌋} →
         Γ ⊢ I ∷ U → Γ ⊢ S ∷ U → Γ ⊢ f ∷ Π (El S) (Desc (renTm vs I)) → Γ ⊢ i ∷ El I →
         Γ ⊢ t ∷ El S → Γ ⊢ p ∷ El (dpay I (dσ S f) (app f t) i) →
         Γ ⊢ con (pair t p) ∷ IMu I (dσ S f) i
⊢con-σ {Γ = Γ} {I = I} {S = S} {f = f} {i = i} {t = t} dI dS df di dt dp =
  ⊢con dI dD di (⊢conv (⊢pair dB dt dp') cv)
  where
    D = dσ S f
    dD = ⊢dσ dI dS df
    dapp : (Γ ▹ El S) ⊢ app (renTm vs f) (var vz) ∷ Desc (renTm vs I)
    dapp = ⊢-cast (wk-app-vz (Desc (renTm vs I))) (⊢app (⊢wk df) (⊢var here))
    dB = ty-El (⊢dpay (⊢wk dI) (⊢wk dD) dapp (⊢wk di))
    dp' = ⊢-cast (sym (cong₄ (λ a b g j → El (dpay a b (app g t) j))
                             (wk-cancel-tm t I) (wk-cancel-tm t D)
                             (wk-cancel-tm t f) (wk-cancel-tm t i)))
                 dp
    cv = csymᵀ (ctrnᵀ (credᵀ (ξ-El (dpay-σ I D S f i))) (credᵀ (El-⌜Σ⌝ _ _)))

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
