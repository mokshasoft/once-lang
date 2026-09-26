------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ THE CONSTRUCTOR-LIST SURFACE, elaborated into the
--               ONE-TELESCOPE kernel (SPIKE-LEVITATION S4, promoted; D072).
--
-- The kernel's family is FIBRED (D074): `IMu I D i` for
-- `D : Π (El I) (Desc I)` — a telescope over every index.  The surface —
-- examples, the Knot — keeps writing a constructor LIST `C₀ … C_{c-1}`
-- (each a telescope OVER THE INDEX VARIABLE) and one method PER
-- constructor.  This module is the elaboration, VERIFIED:
--
--   Dₗ Cs     = λ i. dσ (⌜Fin⌝ c) (λ t. sel Cs t)    -- the datatype
--   conₗ k p  = con (pair (tag k) p)                  -- constructor k
--
--   (a) `⊢Dₗ`    — each `Cₖ ∷ Desc I` (over `i`)  ⇒  `Dₗ Cs ∷ Π (El I) (Desc I)`
--   (b) `⊢conₗ`  — `p ∷ El (dpay I D Cₖ[i])`  ⇒  `conₗ k p ∷ IMu I D i`
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
  using ( ⟶*-trans; ⟶*-dpayᶜ; ⟶ᵀ*-El; red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-Πˡ
        ; ⟶*-appˡ; ⟶*-appʳ )
open import DirectedHoTT.Metatheory.SubjectReductionBase
  using ( wk-sub; ≅ᵀ-sub )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic
  using ( ⟨_⟩ᵣ; subTy-var; subTm-var )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢wk; ⊢-cast; wk-cancel-tm; ren-ty; sub-ty; Ren⊢-ext; wk-ren
        ; ren-lemma; Ren⊢; ∋-cast; conv-ctxᵀ; sub-lemma )
open import DirectedHoTT.Metatheory.Premises
  using ( fsucS⊢; MethG; MethG-wf; MethCtx; MethG-sub; MethG-monoᶜ; mot-ren
        ; methSg; MethTy-wf; MethTy-MethG; ⊢wkD )
open import DirectedHoTT.Metatheory.Validity
  using ( wk-app-vz; srᵀ* )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢single )
open import DirectedHoTT.Spec.Variance
  using ( ren-as-sub )

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

-- ★ D074: the FIBRE over the index variable — the tag, then the selected
--   constructor telescope (the list lives OVER the index) — and the family
Dσ : Cons (Δ ∙) c → RTm (Δ ∙)
Dσ {c = c} Cs = dσ (⌜Fin⌝ c) (selF Cs)

Dₗ : Cons (Δ ∙) c → RTm Δ
Dₗ Cs = lam (Dσ Cs)

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

-- the selector commutes with substitution
selF-sub : {Θ : Cx} (σ : Sub Δ Θ) (Cs : Cons Δ c) → subTm σ (selF Cs) ≡ selF (subC σ Cs)
selF-sub σ Cs =
  cong lam (trans (sel-sub (extS σ) (wkC Cs) (var vz)) (cong (λ X → sel X (var vz)) (subC-wkC σ Cs)))

nth-sub : {Θ : Cx} (σ : Sub Δ Θ) {Cs : Cons Δ c} {C : RTm Δ} → Nth Cs k C →
          Nth (subC σ Cs) k (subTm σ C)
nth-sub σ nth-z     = nth-z
nth-sub σ (nth-s n) = nth-s (nth-sub σ n)

-- ★ the FIBRE over an index: one β, the selector at the instantiated list
fib-β : (Cs : Cons (Δ ∙) c) (i : RTm Δ) →
        app (Dₗ Cs) i ⟶* dσ (⌜Fin⌝ c) (selF (subC (single i) Cs))
fib-β {c = c} Cs i =
  step (β (Dσ Cs) i)
       (subst (λ X → dσ (⌜Fin⌝ c) (subTm (single i) (selF Cs)) ⟶* dσ (⌜Fin⌝ c) X)
              (selF-sub (single i) Cs) done)

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

-- ★ (a) the fibre over the index variable, and the family
⊢Dσ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Cs : Cons (⌊ Γ ⌋ ∙) c} →
      Γ ⊢ I ∷ U → AllD (Γ ▹ El I) (renTm vs I) Cs → (Γ ▹ El I) ⊢ Dσ Cs ∷ Desc (renTm vs I)
⊢Dσ dI ds = ⊢dσ (⊢wk dI) ⊢⌜Fin⌝ (⊢selF (⊢wk dI) ds)

⊢Dₗ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Cs : Cons (⌊ Γ ⌋ ∙) c} →
      Γ ⊢ I ∷ U → AllD (Γ ▹ El I) (renTm vs I) Cs → Γ ⊢ Dₗ Cs ∷ DescF I
⊢Dₗ dI ds = ⊢lam (ty-El dI) (⊢Dσ dI ds)

-- the entries AT an index: the list instantiated
subAllD : {Γ : Ctx} {I i : RTm ⌊ Γ ⌋} {Cs : Cons (⌊ Γ ⌋ ∙) c} →
          AllD (Γ ▹ El I) (renTm vs I) Cs → Γ ⊢ i ∷ El I → AllD Γ I (subC (single i) Cs)
subAllD []ᵈ di = []ᵈ
subAllD {I = I} {i = i} (d ∷ᵈ ds) di =
  ⊢-cast (cong Desc (wk-cancel-tm i I)) (sub-lemma d (⊢single di)) ∷ᵈ subAllD ds di

------------------------------------------------------------------------
-- 3. ★ (b) CONSTRUCTOR `k`, from a payload of ITS telescope.  The payload
--    of `Dₗ Cs` is `Σ (tag) (payload of the selected telescope)`, and the
--    selection converts to `Cₖ` (`selF-β`).
------------------------------------------------------------------------

-- ★ A PAYLOAD, ONE FIELD AT A TIME — the three telescope heads.  A
--   payload is the Σ-chain `dpay` computes; these type it head by head.
--   `ι`: nothing (the index is the FIBRE's — D074); `σ`: a field of code
--   `S` and the rest at the selected telescope `f a`; `ρ`: a recursive
--   field at its own index, and the rest.
⊢pay-ι : {Γ : Ctx} {I D e : RTm ⌊ Γ ⌋} →
         Γ ⊢ e ∷ Unit → Γ ⊢ e ∷ El (dpay I D dι)
⊢pay-ι {I = I} {D} de =
  ⊢conv de (csymᵀ (ctrnᵀ (credᵀ (ξ-El (dpay-ι I D))) (credᵀ El-⌜Unit⌝)))

⊢pay-σ : {Γ : Ctx} {I D S f a p : RTm ⌊ Γ ⌋} →
         Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ f ∷ Π (El S) (Desc (renTm vs I)) →
         Γ ⊢ a ∷ El S → Γ ⊢ p ∷ El (dpay I D (app f a)) →
         Γ ⊢ pair a p ∷ El (dpay I D (dσ S f))
⊢pay-σ {Γ = Γ} {I = I} {D = D} {S = S} {f = f} {a = a} dI dD df da dp =
  ⊢conv (⊢pair dB da dp') cv
  where
    dapp : (Γ ▹ El S) ⊢ app (renTm vs f) (var vz) ∷ Desc (renTm vs I)
    dapp = ⊢-cast (wk-app-vz (Desc (renTm vs I))) (⊢app (⊢wk df) (⊢var here))
    dB = ty-El (⊢dpay (⊢wk dI) (⊢wkD dD) dapp)
    dp' = ⊢-cast (sym (cong₃ (λ x y g → El (dpay x y (app g a)))
                             (wk-cancel-tm a I) (wk-cancel-tm a D) (wk-cancel-tm a f)))
                 dp
    cv = csymᵀ (ctrnᵀ (credᵀ (ξ-El (dpay-σ I D S f))) (credᵀ (El-⌜Σ⌝ _ _)))

-- the common case `f = λ C`: the rest at `C[a]`, one β away
⊢pay-σλ : {Γ : Ctx} {I D S a p : RTm ⌊ Γ ⌋} {C : RTm (⌊ Γ ⌋ ∙)} →
          Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ lam C ∷ Π (El S) (Desc (renTm vs I)) →
          Γ ⊢ a ∷ El S → Γ ⊢ p ∷ El (dpay I D (subTm (single a) C)) →
          Γ ⊢ pair a p ∷ El (dpay I D (dσ S (lam C)))
⊢pay-σλ {a = a} {C = C} dI dD df da dp =
  ⊢pay-σ dI dD df da (⊢conv dp (csymᵀ (credᵀ (ξ-El (ξ-dpayᶜ (β C a))))))

⊢pay-ρ : {Γ : Ctx} {I D j C r p : RTm ⌊ Γ ⌋} →
         Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ C ∷ Desc I →
         Γ ⊢ r ∷ IMu I D j → Γ ⊢ p ∷ El (dpay I D C) →
         Γ ⊢ pair r p ∷ El (dpay I D (dρ j C))
⊢pay-ρ {Γ = Γ} {I = I} {D = D} {j = j} {C = C} {r = r} dI dD dC dr dp =
  ⊢conv (⊢pair dB (⊢conv dr (csymᵀ (credᵀ El-⌜IMu⌝))) dp') cv
  where
    dB = ty-El (⊢dpay (⊢wk dI) (⊢wkD dD) (⊢wk dC))
    dp' = ⊢-cast (sym (cong₃ (λ x y z → El (dpay x y z))
                             (wk-cancel-tm r I) (wk-cancel-tm r D) (wk-cancel-tm r C)))
                 dp
    cv = csymᵀ (ctrnᵀ (credᵀ (ξ-El (dpay-ρ I D j C))) (credᵀ (El-⌜Σ⌝ _ _)))

-- ★ a constructor, from a payload of ANY telescope its fibre reduces to
⊢con-fib : {Γ : Ctx} {I D i C p : RTm ⌊ Γ ⌋} →
           Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ i ∷ El I → app D i ⟶* C →
           Γ ⊢ p ∷ El (dpay I D C) → Γ ⊢ con p ∷ IMu I D i
⊢con-fib dI dD di r dp = ⊢con dI dD di (⊢conv dp (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ r)))))

-- ★ (b) constructor `k` of the list form: the fibre is `dσ` over the tags,
--   and the selection at `tag k` converts to `Cₖ[i]` (`selF-β`)
⊢conₗ : {Γ : Ctx} {I i p : RTm ⌊ Γ ⌋} {C : RTm (⌊ Γ ⌋ ∙)} {Cs : Cons (⌊ Γ ⌋ ∙) c} →
        Γ ⊢ I ∷ U → AllD (Γ ▹ El I) (renTm vs I) Cs → Γ ⊢ i ∷ El I → Nth Cs k C →
        Γ ⊢ p ∷ El (dpay I (Dₗ Cs) (subTm (single i) C)) → Γ ⊢ conₗ k p ∷ IMu I (Dₗ Cs) i
⊢conₗ {i = i} {Cs = Cs} dI ds di nt dp =
  ⊢con-fib dI dD di (fib-β Cs i)
    (⊢pay-σ dI dD (⊢selF dI (subAllD ds di))
            (⊢conv (⊢tag (nth-lt nt)) (csymᵀ (credᵀ El-⌜Fin⌝)))
            (⊢conv dp (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β (nth-sub (single i) nt))))))))
  where dD = ⊢Dₗ dI ds

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
MethK : RTm Δ → RTm Δ → RTy ((Δ ∙) ∙) → RTm (Δ ∙) → ℕ → RTy Δ
MethK I D M C k = MethG I D M C (conₗ k (var (vs vz)))

-- ★ the TAG-GENERIC method type, over the tag: the selector `f` (over the
--   INDEX) at the method's index and the tag, and the scrutinee
--   `con (tag , p)`.  The motive of the method selection; `MethK … Cₖ k`
--   converts to its instance at `tag k`.
MethT : RTm Δ → RTm Δ → RTy ((Δ ∙) ∙) → RTm (Δ ∙) → RTy (Δ ∙)
MethT I D M f =
  MethG (renTm vs I) (renTm vs D) (renTy (extR (extR vs)) M) (app (renTm (extR vs) f) (var (vs vz)))
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

-- a weakening under a binder, instantiated at the binder's own variable
--   or at any term under it: itself
ext-cancel : (a : RTm Δ) (t : RTm (Δ ∙)) → subTm (extS (single a)) (renTm (extR vs) t) ≡ t
ext-cancel a t = trans (subTm-renTm t) (trans (subTm-cong pt t) (subTm-id t))
  where
    pt : ∀ x → (extS (single a) ₛ∘ᵣ extR vs) x ≡ idₛ x
    pt vz     = refl
    pt (vs x) = refl

vz-cancel : (t : RTm (Δ ∙)) → subTm (single (var vz)) (renTm (extR vs) t) ≡ t
vz-cancel t = trans (subTm-renTm t) (trans (subTm-cong pt t) (subTm-id t))
  where
    pt : ∀ x → (single (var vz) ₛ∘ᵣ extR vs) x ≡ idₛ x
    pt vz     = refl
    pt (vs x) = refl

-- ★ the tag-generic method type at `tag k` IS constructor `k`'s, with the
--   selection `f (tag k)` for its telescope
MethT-inst : (I D : RTm Δ) (M : RTy ((Δ ∙) ∙)) (f : RTm (Δ ∙)) (k : ℕ) →
             subTy (single (tag k)) (MethT I D M f)
             ≡ MethG I D M (app f (tag k)) (conₗ k (var (vs vz)))
MethT-inst I D M f k =
  trans (MethG-sub (single (tag k)) (renTm vs I) (renTm vs D) (renTy (extR (extR vs)) M)
                   (app (renTm (extR vs) f) (var (vs vz))) (con (pair (var (vs (vs (vs vz)))) (var (vs vz)))))
        (cong₅ MethG (wk-cancel-tm (tag k) I) (wk-cancel-tm (tag k) D) (M-cancel (tag k) M)
                     (cong₂ app (ext-cancel (tag k) f) (tag-ren vs k))
                     (cong (λ z → con (pair z (var (vs vz))))
                           (trans (cong (λ z → renTm vs (renTm vs z)) (tag-ren vs k))
                                  (trans (cong (renTm vs) (tag-ren vs k)) (tag-ren vs k)))))

-- ★ constructor `k`'s method type converts to the tag-generic one's
--   instance: the lookup `f (tag k) ⟶* Cₖ` inside `dpay`/`DIh`
MethK≅T : {I D : RTm Δ} {f C : RTm (Δ ∙)} {M : RTy ((Δ ∙) ∙)} (k : ℕ) → app f (tag k) ⟶* C →
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

private
  -- a substitution after a renaming that lands on variables is a renaming
  sr-flat : {Θ Ξ Ω : Cx} (σ : Sub Θ Ξ) (ρ : Ren Ω Θ) (ρ' : Ren Ω Ξ) →
            (∀ x → σ (ρ x) ≡ var (ρ' x)) → (t : RTm Ω) → subTm σ (renTm ρ t) ≡ renTm ρ' t
  sr-flat σ ρ ρ' h t = trans (subTm-renTm t) (trans (subTm-cong h t) (subTm-var ρ' t))

  -- the index binder mapped to a variable deep in the context, the rest
  --   weakened past four binders
  ρidx : {Γ : Cx} → Ren (Γ ∙) ((((Γ ∙) ∙) ∙) ∙)
  ρidx vz     = vs (vs vz)
  ρidx (vs x) = vs (vs (vs (vs x)))

  -- four weakenings are one renaming
  r4 : {Γ : Cx} (t : RTm Γ) → renTm vs (renTm vs (renTm vs (renTm vs t)))
                              ≡ renTm (λ x → vs (vs (vs (vs x)))) t
  r4 t = trans (cong (λ z → renTm vs (renTm vs z)) (renTm-renTm t))
               (trans (cong (renTm vs) (renTm-renTm t)) (renTm-renTm t))

  r4ᵀ : {Γ : Cx} (A : RTy Γ) → renTy vs (renTy vs (renTy vs (renTy vs A)))
                               ≡ renTy (λ x → vs (vs (vs (vs x)))) A
  r4ᵀ A = trans (cong (λ z → renTy vs (renTy vs z)) (renTy-renTy A))
                (trans (cong (renTy vs) (renTy-renTy A)) (renTy-renTy A))

-- the tag-generic method type is well-formed over the tag
MethT-wf : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {Cs : Cons (⌊ Γ ⌋ ∙) c} →
           Γ ⊢ I ∷ U → AllD (Γ ▹ El I) (renTm vs I) Cs → motCtx Γ I (Dₗ Cs) ⊢ty M →
           (Γ ▹ Fin c) ⊢ty MethT I (Dₗ Cs) M (selF Cs)
MethT-wf {c = c} {Γ = Γ} {I = I} {M = M} {Cs = Cs} dI ds dM =
  MethG-wf (⊢wk dI) (⊢wkD dD) dC (mot-ren there dM) dscr
  where
    D = Dₗ Cs
    f = selF Cs
    dD = ⊢Dₗ dI ds
    df : (Γ ▹ El I) ⊢ f ∷ Π (El (⌜Fin⌝ c)) (Desc (renTm vs (renTm vs I)))
    df = ⊢selF (⊢wk dI) ds
    I2 = renTm vs (renTm vs I)
    -- the selector at the method's index and the tag
    eqI : subTm (single (var (vs vz))) (renTm (extR (extR vs)) (renTm vs (renTm vs I))) ≡ I2
    eqI = trans (cong (subTm (single (var (vs vz)))) (trans (cong (renTm (extR (extR vs))) (renTm-renTm I))
                                                             (renTm-renTm I)))
                (trans (sr-flat _ _ (λ x → vs (vs x)) (λ x → refl) I) (sym (renTm-renTm I)))
    dC : ((Γ ▹ Fin c) ▹ El (renTm vs I)) ⊢ app (renTm (extR vs) f) (var (vs vz)) ∷ Desc I2
    dC = ⊢-cast (cong Desc eqI)
           (⊢app (ren-lemma df (Ren⊢-ext there))
                 (⊢conv (⊢var (there here)) (csymᵀ (credᵀ El-⌜Fin⌝))))
    -- the scrutinee `con (tag , p)` at the method's index
    I4 = renTm vs (renTm vs (renTm vs (renTm vs I)))
    D4 = renTm vs (renTm vs (renTm vs (renTm vs D)))
    dI4 = ⊢wk (⊢wk (⊢wk (⊢wk dI)))
    dD4 = ⊢wkD (⊢wkD (⊢wkD (⊢wkD dD)))
    eqf : subTm (single (var (vs (vs vz))))
            (renTm (extR vs) (renTm (extR vs) (renTm (extR vs) (renTm (extR vs) f))))
          ≡ renTm ρidx f
    eqf = trans (cong (subTm (single (var (vs (vs vz)))))
                      (trans (cong (renTm (extR vs)) (trans (cong (renTm (extR vs)) (renTm-renTm f))
                                                             (renTm-renTm f)))
                             (renTm-renTm f)))
                (sr-flat _ _ ρidx (λ { vz → refl ; (vs x) → refl }) f)
    red : app D4 (var (vs (vs vz))) ⟶* dσ (⌜Fin⌝ c) (renTm ρidx f)
    red = step (β _ _)
            (subst (λ X → dσ (⌜Fin⌝ c) (subTm (single (var (vs (vs vz))))
                            (renTm (extR vs) (renTm (extR vs) (renTm (extR vs) (renTm (extR vs) f)))))
                          ⟶* dσ (⌜Fin⌝ c) X) eqf done)
    hidx : Ren⊢ (Γ ▹ El I) (MethCtx (Γ ▹ Fin c) (renTm vs I) (renTm vs D)
                              (renTy (extR (extR vs)) M) (app (renTm (extR vs) f) (var (vs vz))))
                ρidx
    hidx here = ∋-cast (cong El (trans (r4 I) (sym (renTm-renTm I)))) (there (there here))
    hidx (there {A = A₀} v) = ∋-cast (trans (r4ᵀ A₀) (sym (renTy-renTy A₀))) (there (there (there (there v))))
    dfi : _ ⊢ renTm ρidx f ∷ Π (El (⌜Fin⌝ c)) (Desc (renTm vs I4))
    dfi = ⊢-cast (cong (λ X → Π (El (⌜Fin⌝ c)) (Desc X))
                       (trans (cong (renTm (extR ρidx)) (renTm-renTm I))
                              (trans (renTm-renTm I)
                                     (sym (trans (cong (renTm vs) (r4 I)) (renTm-renTm I))))))
                 (ren-lemma df hidx)
    eqp : renTm vs (renTm vs (renTm (extR vs) f)) ≡ renTm ρidx f
    eqp = trans (cong (renTm vs) (renTm-renTm f))
                (trans (renTm-renTm f) (renTm-cong (λ { vz → refl ; (vs x) → refl }) f))
    dp4 = ⊢-cast (cong (λ g → El (dpay I4 D4 (app g (var (vs (vs (vs vz))))))) eqp)
                 (⊢var (there here))
    dscr = ⊢con-fib dI4 dD4 (⊢var (there (there here))) red
             (⊢pay-σ dI4 dD4 dfi (⊢conv (⊢var (there (there (there here)))) (csymᵀ (credᵀ El-⌜Fin⌝))) dp4)

-- ★ one method PER CONSTRUCTOR, each at ITS constructor's method type,
--   with the selection's lookup for that constructor (`selF-β` gives it
--   from an `Nth`)
infixr 5 _∷ₘ_
data PerK (Γ : Ctx) (I D : RTm ⌊ Γ ⌋) (M : RTy ((⌊ Γ ⌋ ∙) ∙)) (f : RTm (⌊ Γ ⌋ ∙)) :
          ℕ → {n : ℕ} → Cons ⌊ Γ ⌋ n → Set where
  []ₘ  : {k : ℕ} → PerK Γ I D M f k []
  _∷ₘ_ : {k n : ℕ} {C : RTm (⌊ Γ ⌋ ∙)} {m : RTm ⌊ Γ ⌋} {ms : Cons ⌊ Γ ⌋ n} →
         (app f (tag k) ⟶* C) × (Γ ⊢ m ∷ MethK I D M C k) →
         PerK Γ I D M f (suc k) ms → PerK Γ I D M f k (m ∷ ms)

mkAllQ : {Γ : Ctx} {I D : RTm ⌊ Γ ⌋} {f : RTm (⌊ Γ ⌋ ∙)} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {B : RTy ⌊ Γ ⌋} {k n : ℕ}
         {ms : Cons ⌊ Γ ⌋ n} → PerK Γ I D M f k ms →
         AllQ (Γ ▹ B) (subTy (fsucsS k) (renTy (extR vs) (MethT I D M f))) (wkC ms)
mkAllQ []ₘ = []q
mkAllQ {I = I} {D} {f} {M} {k = k} ((r , dm) ∷ₘ ps) =
  ⊢-cast (sym (trans (fsucsS-head k (renTy (extR vs) (MethT I D M f)))
                     (wk-single-tag k (MethT I D M f))))
         (⊢conv (⊢wk dm) (≅ᵀ-ren vs (MethK≅T k r)))
  ∷q castQ (sym (fsucsS-suc k (renTy (extR vs) (MethT I D M f)))) (mkAllQ ps)

-- ★ the SELECTOR: a function of the tag, at the tag-generic method type
⊢selM : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {Cs : Cons (⌊ Γ ⌋ ∙) c} {ms : Cons ⌊ Γ ⌋ c} →
        Γ ⊢ I ∷ U → AllD (Γ ▹ El I) (renTm vs I) Cs → motCtx Γ I (Dₗ Cs) ⊢ty M →
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


-- ★ the one method at the family's OPEN FIBRE `Dσ Cs` (over the method's
--   index binder); the kernel's `MethTy` is one β from it (`⊢methₗ`).
⊢methσ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {Cs : Cons (⌊ Γ ⌋ ∙) c} {ms : Cons ⌊ Γ ⌋ c} →
         Γ ⊢ I ∷ U → AllD (Γ ▹ El I) (renTm vs I) Cs → motCtx Γ I (Dₗ Cs) ⊢ty M →
         PerK Γ I (Dₗ Cs) M (selF Cs) zero ms →
         Γ ⊢ methₗ ms ∷ MethG I (Dₗ Cs) M (Dσ Cs) (con (var (vs vz)))
⊢methσ {c = c} {Γ = Γ} {I = I} {M = M} {Cs = Cs} {ms = ms} dI ds dM ps =
  ⊢lam (ty-El dI) (⊢lam dP₁ (⊢-cast eqP (⊢psplit dA dB dP dq db)))
  where
    D = Dₗ Cs
    Cσ = Dσ Cs
    f = selF Cs
    dD = ⊢Dₗ dI ds
    df : (Γ ▹ El I) ⊢ f ∷ Π (El (⌜Fin⌝ c)) (Desc (renTm vs (renTm vs I)))
    df = ⊢selF (⊢wk dI) ds
    P₁ = El (dpay (renTm vs I) (renTm vs D) Cσ)
    dP₁ = ty-El (⊢dpay (⊢wk dI) (⊢wkD dD) (⊢Dσ dI ds))
    Γ₂ = (Γ ▹ El I) ▹ P₁
    s₁ : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)
    s₁ = con (var (vs vz))
    T : RTy ⌊ Γ₂ ⌋
    T = Π (DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs Cσ) (var vz)) (subTy (methSg s₁) M)
    -- the kernel's method type is well-formed, and one β from this one
    fib : app (renTm vs D) (var vz) ⟶* Cσ
    fib = step (β _ _) (subst (_⟶*_ (subTm (single (var vz)) (renTm (extR vs) Cσ))) (vz-cancel Cσ) done)
    dT : Γ₂ ⊢ty T
    dT = Π-cod (Π-cod (srᵀ* (subst (λ X → Γ ⊢ty X) (MethTy-MethG I D M) (MethTy-wf dI dD dM))
                            (MethG-monoᶜ fib)))
    I₂ = renTm vs (renTm vs I)
    D₂ = renTm vs (renTm vs D)
    f₂ = renTm vs f
    Q₂ = renTy vs P₁
    A = El (⌜Fin⌝ {⌊ Γ₂ ⌋} c)
    B = El (dpay (renTm vs I₂) (renTm vs D₂) (app (renTm vs f₂) (var vz)))
    cvq : Q₂ ≅ᵀ Σ' A B
    cvq = ctrnᵀ (credᵀ (ξ-El (dpay-σ I₂ D₂ (⌜Fin⌝ c) f₂))) (credᵀ (El-⌜Σ⌝ _ _))
    dq = ⊢conv (⊢var here) cvq
    dA = ty-El (⊢⌜Fin⌝ {n = c})
    dI₂ = ⊢wk (⊢wk dI)
    dD₂ = ⊢wkD (⊢wkD dD)
    dB : (Γ₂ ▹ A) ⊢ty B
    dB = ty-El (⊢dpay (⊢wk dI₂) (⊢wkD dD₂)
                      (⊢-cast (cong Desc (wk-cancel-tm (var vz) (renTm vs I₂)))
                              (⊢app (⊢wkF (⊢wkF df)) (⊢var here))))
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
    M₄ = renTy (extR (extR w4)) M
    f₄ : RTm (⌊ Γ₄ ⌋ ∙)
    f₄ = renTm (extR w4) f
    -- `f` at the branch's index
    ρi : Ren (⌊ Γ ⌋ ∙) ⌊ Γ₄ ⌋
    ρi vz     = vs (vs (vs vz))
    ρi (vs x) = w4 x
    fi = renTm ρi f
    s₄ : RTm ((((⌊ Γ₄ ⌋ ∙) ∙) ∙))
    s₄ = con (pair (var (vs (vs (vs (vs vz))))) (var (vs vz)))
    τ = single t ₛ∘ᵣ extR w4
    wk-τ : (x : RTm ⌊ Γ ⌋) → subTm τ (renTm vs x) ≡ renTm w4 x
    wk-τ x = trans (subTm-renTm x) (subTm-var w4 x)
    E1 : subTy (single t) (renTy (extR w4) MT) ≡ MethG I₄ D₄ M₄ (app f₄ (renTm vs t)) s₄
    E1 = trans (subTy-renTy MT)
           (trans (MethG-sub τ (renTm vs I) (renTm vs D) (renTy (extR (extR vs)) M)
                             (app (renTm (extR vs) f) (var (vs vz))) (con (pair (var (vs (vs (vs vz)))) (var (vs vz)))))
                  (cong₅ MethG (wk-τ I) (wk-τ D) eM
                               (cong₂ app (sr-flat (extS τ) (extR vs) (extR w4) (λ { vz → refl ; (vs x) → refl }) f)
                                          refl)
                               refl))
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
    C₄ : RTm (⌊ Γ₄ ⌋ ∙)
    C₄ = app f₄ (renTm vs t)
    Csub : subTm (single i) C₄ ≡ app fi t
    Csub = cong₂ app (sr-flat (single i) (extR w4) ρi (λ { vz → refl ; (vs x) → refl }) f)
                     (wk-cancel-tm i t)
    d2 = ⊢app d1 di
    eqfi : renTm vs (renTm vs (renTm vs f)) ≡ fi
    eqfi = trans (cong (renTm vs) (renTm-renTm f))
                 (trans (renTm-renTm f) (renTm-cong (λ { vz → refl ; (vs x) → refl }) f))
    dp : Γ₄ ⊢ var vz ∷ El (dpay I₄ D₄ (app fi t))
    dp = ⊢-cast (cong₃ (λ a b g → El (dpay a b (app g t))) (ren4 I) (ren4 D) eqfi) (⊢var here)
    Y : RTy (⌊ Γ₄ ⌋ ∙)
    Y = Π (subTy (extS (single i)) (DIh (renTm vs (renTm vs D₄)) (wk2M M₄) (renTm vs C₄) (var vz)))
          (subTy (extS (extS (single i))) (subTy (methSg s₄) M₄))
    d2' = ⊢-cast (cong (λ X → Π X Y)
                       (cong₃ (λ a b g → El (dpay a b g))
                              (wk-cancel-tm i I₄) (wk-cancel-tm i D₄) Csub))
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
    cancelC : subTm (single p') (subTm (extS (single i)) (renTm vs C₄)) ≡ app fi t
    cancelC = trans (cong (subTm (single p')) (trans (wk-sub (single i) C₄) (cong (renTm vs) Csub)))
                    (wk-cancel-tm p' (app fi t))
    domL : subTy (single p') (subTy (extS (single i))
             (DIh (renTm vs (renTm vs D₄)) (wk2M M₄) (renTm vs C₄) (var vz)))
           ≡ DIh D₄ M₄ (app fi t) p'
    domL = cong₄ DIh (cancel2 D₄) eM cancelC refl
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
    domR : subTy pairS (renTy ρP (DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs Cσ) (var vz)))
           ≡ DIh D₄ M₄ (renTm ρi Cσ) (pair t p')
    domR = cong₄ DIh eD eM eC refl
      where
        eD : subTm pairS (renTm ρP (renTm vs (renTm vs D))) ≡ D₄
        eD = trans (cong (subTm pairS) (trans (renTm-renTm (renTm vs D)) (renTm-renTm D)))
                   (trans (subTm-renTm D) (trans (subTm-cong (λ x → refl) D) (subTm-var w4 D)))
        eC : subTm pairS (renTm ρP (renTm vs Cσ)) ≡ renTm ρi Cσ
        eC = trans (cong (subTm pairS) (renTm-renTm Cσ))
                   (sr-flat pairS _ ρi (λ { vz → refl ; (vs x) → refl }) Cσ)
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
    -- the hypotheses at the whole fibre compute to those at the selection
    red : DIh D₄ M₄ (renTm ρi Cσ) (pair t p') ⟶ᵀ* DIh D₄ M₄ (app fi t) p'
    red = stepᵀ (DIh-σ D₄ M₄ (⌜Fin⌝ c) fi (pair t p'))
            (stepᵀ (ξ-DIhᶜ (ξ-appʳ (βfst t p'))) (stepᵀ (ξ-DIhᵖ (βsnd t p')) doneᵀ))
    cvfinal : subTy (single p') Y ≅ᵀ subTy pairS (renTy ρP T)
    cvfinal = subst (λ X → X ≅ᵀ subTy pairS (renTy ρP T)) (sym (cong₂ Π domL cod))
                (subst (λ X → Π (DIh D₄ M₄ (app fi t) p') Gc ≅ᵀ X) (sym (cong (λ X → Π X Gc) domR))
                  (csymᵀ (red→≅ᵀ (⟶ᵀ*-Πˡ red))))
    db : Γ₄ ⊢ app (app (app (renTm w4 (selM ms)) t) i) (var vz) ∷ subTy pairS (renTy ρP T)
    db = ⊢conv d3 cvfinal

-- ★ (c) the one method inhabits the kernel's `MethTy`: one β (the fibre
--   at the method's own index variable) from `⊢methσ`
⊢methₗ : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {M : RTy ((⌊ Γ ⌋ ∙) ∙)} {Cs : Cons (⌊ Γ ⌋ ∙) c} {ms : Cons ⌊ Γ ⌋ c} →
         Γ ⊢ I ∷ U → AllD (Γ ▹ El I) (renTm vs I) Cs → motCtx Γ I (Dₗ Cs) ⊢ty M →
         PerK Γ I (Dₗ Cs) M (selF Cs) zero ms →
         Γ ⊢ methₗ ms ∷ MethTy I (Dₗ Cs) M
⊢methₗ {Γ = Γ} {I = I} {M = M} {Cs = Cs} {ms = ms} dI ds dM ps =
  subst (λ X → Γ ⊢ methₗ ms ∷ X) (sym (MethTy-MethG I (Dₗ Cs) M))
    (⊢conv (⊢methσ dI ds dM ps) (csymᵀ (red→≅ᵀ (MethG-monoᶜ fib))))
  where
    fib : app (renTm vs (Dₗ Cs)) (var vz) ⟶* Dσ Cs
    fib = step (β _ _) (subst (_⟶*_ (subTm (single (var vz)) (renTm (extR vs) (Dσ Cs)))) (vz-cancel (Dσ Cs)) done)

-- ★ THE DERIVED ι: the one method at constructor `k` IS constructor `k`'s
--   method — ι, two β, the split, and the tag selection.
ιₗ : {Δ : Cx} {k : ℕ} {D i p m : RTm Δ} {ms : Cons Δ c} → Nth ms k m →
     ielim D i (methₗ ms) (conₗ k p)
       ⟶* app (app (app m i) p) (dih D (methₗ ms) (app D i) (pair (tag k) p))
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
    h = dih D e (app D i) q
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
