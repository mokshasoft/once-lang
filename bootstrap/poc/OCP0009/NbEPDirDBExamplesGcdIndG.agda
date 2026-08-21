------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — gcd's `IndStep`, GENERIC IN THE MOTIVE.
--
-- ⚠⚠ THIS FILE IS THE AMORTISATION TEST, and it is the point of the
--   three-customer criterion.  `…ExamplesGcdDvd*` proved `IndStep` for the
--   divisibility motive in ~700 lines across eight modules.  If the SECOND
--   customer needed those 700 lines again, that is the "three bespoke
--   rebuilds" the criterion names as the warning sign.
--
-- ★ SO THE PLUMBING IS PARAMETERISED OVER THE MOTIVE, and both customers
--   instantiate it.  What a customer supplies is exactly:
--     · the motive code `PC u₁ u₂ v`, its typing and its two naturality
--       laws (`-sub`, `-ren`);
--     · the two conversions saying its slots REDUCE;
--     · FOUR LEAVES — one per branch of gcd.
--   Everything else — the internalised `IndPW`, the split motive, the
--   three `natrec`s and their boundaries — is supplied once, here.
--
-- ⚠ THE PRICE OF GENERICITY, and it is exactly what `…GcdStepExt`'s
--   `probe₁-at = refl` bought at the concrete motive: with `PC` opaque the
--   motive boundaries no longer COMPUTE, so each one now costs a `PC-sub`.
--   Four probes, four rewrites.  ⭐ Against that, the elaborated terms
--   SHRINK — an opaque `PC u₁ u₂ v` is a variable application where
--   `QCode u₁ u₂ v` unfolded to a `⌜Σ⌝` of two `⌜Id⌝`s over a `mulTm`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdIndG where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs; RTy; RTm; El; U; Nat; Hom; Π
        ; var; fst; snd; app; nzero; nsuc; natrec; ⌜Nat⌝
        ; subTm; subTy; renTm; renTy; Ren; Sub; extR; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; ty-Hom; ty-Nat; ty-Π; ty-El; ⊢⌜Nat⌝
        ; ⊢conv; _≅ᵀ_; csymᵀ; _⟶*_; step; done )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-El )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-ren )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; Ren⊢; ⊢[] )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; sub-w; sub-w²; ren-w; cong₃; cong₄ )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT; asN )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm; ⊢monus )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( IdN; ⊢tyIdN )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( Prv; prv; prvOk; prv-cast; wR; renren; module AmTΠ )
open import poc.OCP0009.NbEPDirDBLibIHCall
  using ( ihCallT; ihCall; ⊢ihCallT; ihCallIntro; ihCallElim )
open import poc.OCP0009.NbEPDirDBLibAmrecInd using ( PAtR; IndPW; IndStep )
open import poc.OCP0009.NbEPDirDBLibNatrec using ( Ren⊢-id; ⊢natrec-var )
open import poc.OCP0009.NbEPDirDBType
  using ( natrec-zero; β; ξ-appˡ; ⊢natrec )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( msr; ⊢msr; gcdIH; ⊢gcdIH; gcdG; ⊢gcdG; gcdStp; gcdBody
        ; G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExt
  using ( appGcdIH; gcdIH-w; gcdIH-w²; gcdAt; red-β; μ₁; f₁; μ₂; f₂; μ₃; f₃ )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtE using ( gcdIH-sub )

------------------------------------------------------------------------
-- ★ WHAT A CUSTOMER SUPPLIES.  Six facts about the motive and four
--   leaves — and nothing about `natrec`s, contexts or renamings.
------------------------------------------------------------------------

record Motive : Set₁ where
  field
    PC     : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
    ⊢PC    : {Γ : Ctx} {u₁ u₂ v : RTm ⌊ Γ ⌋} →
             Γ ⊢ u₁ ∷ Nat → Γ ⊢ u₂ ∷ Nat → Γ ⊢ v ∷ Nat →
             Γ ⊢ PC u₁ u₂ v ∷ U
    PC-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (u₁ u₂ v : RTm Γ) →
             subTm σ (PC u₁ u₂ v)
           ≡ PC (subTm σ u₁) (subTm σ u₂) (subTm σ v)
    PC-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (u₁ u₂ v : RTm Γ) →
             renTm ρ (PC u₁ u₂ v)
           ≡ PC (renTm ρ u₁) (renTm ρ u₂) (renTm ρ v)
    -- ⚠ TERM-LEVEL `⟶*`, not `≅ᵀ`.  The split bridge has to lift a
    --   reduction of the recursor THROUGH two `Π`s, and `⟶ᵀ*-Πʳ` takes a
    --   `⟶ᵀ*`; a `≅ᵀ` (which is symmetric) cannot be lifted.  Both
    --   customers have exactly this shape already.
    PC-redV : {Γ : Cx} {v v' : RTm Γ} (u₁ u₂ : RTm Γ) →
              v ⟶* v' → PC u₁ u₂ v ⟶* PC u₁ u₂ v'
    PC-redU : {Γ : Cx} {u₁ u₁' u₂ u₂' : RTm Γ} (v : RTm Γ) →
              u₁ ⟶* u₁' → u₂ ⟶* u₂' → PC u₁ u₂ v ⟶* PC u₁' u₂' v

    -- ★★ THE FOUR LEAVES — one per branch of gcd, and the ONLY place a
    --    customer does mathematics.
    leaf-b0 : {Γ : Ctx} {u : RTm ⌊ Γ ⌋} → Γ ⊢ u ∷ Nat →
              Prv Γ (El (PC u nzero u))
    leaf-a0 : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat →
              Prv Γ (El (PC nzero (nsuc b) (nsuc b)))
    leaf-le : {Γ : Ctx} {a b v e ih : RTm ⌊ Γ ⌋} →
              Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ v ∷ Nat →
              Γ ⊢ e ∷ IdN (monusTm a b) nzero →
              Γ ⊢ ih ∷ El (PC a (monusTm b a) v) →
              Prv Γ (El (PC a b v))
    leaf-gt : {Γ : Ctx} {a b v p e ih : RTm ⌊ Γ ⌋} →
              Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ v ∷ Nat → Γ ⊢ p ∷ Nat →
              Γ ⊢ e ∷ IdN (monusTm a b) (nsuc p) →
              Γ ⊢ ih ∷ El (PC (monusTm a b) b v) →
              Prv Γ (El (PC a b v))

------------------------------------------------------------------------
-- ★★ THE PLUMBING, ONCE.
------------------------------------------------------------------------

module Plumb (M : Motive) where

  open Motive M

  -- the motive at the pair carrier: slot [1] = the pair, [0] = the result
  gP : {Γ : Cx} → RTm ((Γ ∙) ∙)
  gP = PC (fst (var (vs vz))) (snd (var (vs vz))) (var vz)

  ⊢gP : {Δ : Ctx} → ((Δ ▹ PairT) ▹ El ⌜Nat⌝) ⊢ gP ∷ U
  ⊢gP = ⊢PC (⊢fst dx) (⊢snd dx) (asN (⊢var here))
    where dx = ⊢var (there here)

  -- ⚠ stated at `Cx`, not `Ctx`: `PAtR` is `Cx`-indexed and `⌊_⌋` is not
  --   injective, so at `Ctx` the target context never solves.
  PAtR-P : {Γ Γ' : Cx} (ρ : Ren Γ Γ') (y val : RTm Γ') →
           PAtR ρ gP y val ≡ PC (fst y) (snd y) val
  PAtR-P ρ y val =
    trans (cong (λ t → subTm (single val) (subTm (extS (single y)) t))
                (PC-ren {ρ = extR (extR ρ)}
                        (fst (var (vs vz))) (snd (var (vs vz))) (var vz)))
      (trans (cong (subTm (single val))
                   (PC-sub {σ = extS (single y)}
                           (fst (var (vs vz))) (snd (var (vs vz))) (var vz)))
        (trans (PC-sub {σ = single val} (fst (w y)) (snd (w y)) (var vz))
               (cong (λ u → PC (fst u) (snd u) val) (wk-single {v = val} y))))

  ------------------------------------------------------------------------
  -- ★★★ `IndPW`, INTERNALISED — the linchpin, and it is motive-generic.
  ------------------------------------------------------------------------

  ww : {Γ : Cx} (t : RTm Γ) → w (w t) ≡ renTm (λ v → vs (vs v)) t
  ww t = renren {ϑ = vs} {ρ = vs} {ρ' = λ v → vs (vs v)} (λ _ → refl) t

  indPWT : {Γ : Cx} (μa ih : RTm Γ) → RTy Γ
  -- ⚠ DEFINED as `…LibIHCall.ihCallT` at the payload `El (PC … (ihCall ih))`.
  --   Same type as before, definitionally; stating it this way is what makes
  --   the shared shape a CLIENT of the library rather than a coincidence.
  indPWT μa ih =
    ihCallT PairT msr (w μa)
      (El (PC (fst (var (vs vz))) (snd (var (vs vz))) (ihCall ih)))

  ⊢indPWT : {Γ : Ctx} {μa ih : RTm ⌊ Γ ⌋} →
            Γ ⊢ μa ∷ Nat → Γ ⊢ ih ∷ gcdIH μa → Γ ⊢ty indPWT μa ih
  ⊢indPWT {μa = μa} dμ di =
    ⊢ihCallT ⊢PairT ⊢msr (⊢wk dμ)
             (ty-El (⊢PC (⊢fst dy) (⊢snd dy) (asN dcall)))
    where
      dy    = ⊢var (there here)
      dcall = appGcdIH (⊢-cast (gcdIH-w² μa) (⊢wk (⊢wk di))) dy (⊢var here)

  indPWIntro : {Δ Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {a ih : RTm ⌊ Θ ⌋} →
               Θ ⊢ subTm (single a) msr ∷ Nat →
               IndPW Δ PairT ⌜Nat⌝ msr gP Θ ρ a ih →
               Prv Θ (indPWT (subTm (single a) msr) ih)
  indPWIntro {ρ = ρ} {a = a} {ih = ih} dμ pw =
    prv _ (ihCallIntro ⊢PairT (ty-Hom ty-Nat (⊢nsuc ⊢msr) (⊢wk dμ))
                       (⊢-cast bodyEq (prvOk inner)))
    where
      μa = subTm (single a) msr

      inner = pw (wR (wR Ren⊢-id)) (λ v → refl) (var (vs vz)) (var vz)
                 (⊢var (there here))
                 (⊢-cast (cong (Hom Nat (nsuc (w msr))) (ww μa)) (⊢var here))

      -- ⚠ the ambient renaming is the COMPOSITE `vs ∘ vs ∘ ρ`, and it must
      --   be pinned: `PAtR` is defined, so it will not solve from the goal.
      bodyEq = trans (cong El (PAtR-P (λ v → vs (vs (ρ v))) (var (vs vz))
                                (app (app (renTm (λ v → vs (vs v)) ih)
                                          (var (vs vz)))
                                     (var vz))))
                     (cong (λ t → El (PC (fst (var (vs vz))) (snd (var (vs vz)))
                                         (app (app t (var (vs vz))) (var vz))))
                           (sym (ww ih)))

  indPWElim : {Γ : Ctx} {μ i h y q : RTm ⌊ Γ ⌋} →
              Γ ⊢ h ∷ indPWT μ i → Γ ⊢ y ∷ PairT →
              Γ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) msr)) μ →
              Γ ⊢ app (app h y) q ∷ El (PC (fst y) (snd y) (app (app i y) q))
  -- ⚠ THE APPLICATION is now `…LibIHCall.ihCallElim` (two `⊢app`s at an
  --   arbitrary payload); everything below it is the PAYLOAD PEEL, which
  --   is client-side by construction and is why the shared shape saves
  --   lines here and not seconds.
  indPWElim {μ = μ} {i = i} {y = y} {q = q} dh dy dq =
    ⊢-cast (cong El (trans (cong (subTm (single q)) payload) eq2))
           (ihCallElim dh dy (⊢-cast homEq dq))
    where
      peel₁ : (t : RTm ⌊ _ ⌋) → subTm (extS (single y)) (w (w t)) ≡ w t
      peel₁ t = trans (sub-w {σ = single y} (w t)) (cong w (wk-single {v = y} t))

      homEq = cong (Hom Nat (nsuc (subTm (single y) msr)))
                   (sym (wk-single {v = y} μ))

      payload = trans (PC-sub {σ = extS (single y)}
                         (fst (var (vs vz))) (snd (var (vs vz)))
                         (app (app (w (w i)) (var (vs vz))) (var vz)))
                      (cong (λ z → PC (fst (w y)) (snd (w y))
                                      (app (app z (w y)) (var vz)))
                            (peel₁ i))

      eq2 = trans (PC-sub {σ = single q}
                     (fst (w y)) (snd (w y)) (app (app (w i) (w y)) (var vz)))
                  (cong₂ (λ z u → PC (fst u) (snd u) (app (app z u) q))
                         (wk-single {v = q} i) (wk-single {v = q} y))

  indPWT-w : {Γ : Cx} (μ i : RTm Γ) →
             renTy vs (indPWT μ i) ≡ indPWT (w μ) (w i)
  indPWT-w μ i =
    cong₂ (λ u c → Π PairT (Π (Hom Nat (nsuc msr) u) (El c)))
          (ren-w μ)
          (trans (PC-ren {ρ = extR (extR vs)}
                    (fst (var (vs vz))) (snd (var (vs vz)))
                    (app (app (w (w i)) (var (vs vz))) (var vz)))
                 (cong (λ z → PC (fst (var (vs vz))) (snd (var (vs vz)))
                                 (app (app z (var (vs vz))) (var vz)))
                       (wwr i)))
    where
      wwr : (t : RTm _) → renTm (extR (extR vs)) (w (w t)) ≡ w (w (w t))
      wwr t = trans (ren-w {ρ = extR vs} (w t)) (cong w (ren-w t))

  ------------------------------------------------------------------------
  -- ★★★★ `indG` — the split motive, motive-generic.
  ------------------------------------------------------------------------

  gcdG-w² : {Γ : Cx} (μ : RTm Γ) →
            renTy vs (renTy vs (gcdG μ)) ≡ gcdG (w (w μ))
  gcdG-w² μ = cong (λ T → Π T (El ⌜Nat⌝)) (gcdIH-w² μ)

  indG : {Γ : Cx} (μx f u₁ u₂ : RTm Γ) → RTy Γ
  indG μx f u₁ u₂ =
    Π (gcdIH μx)
      (Π (indPWT (w μx) (var vz))
         (El (PC (w (w u₁)) (w (w u₂)) (app (w (w f)) (var (vs vz))))))

  ⊢indG : {Γ : Ctx} {μx f u₁ u₂ : RTm ⌊ Γ ⌋} →
          Γ ⊢ μx ∷ Nat → Γ ⊢ f ∷ gcdG μx →
          Γ ⊢ u₁ ∷ Nat → Γ ⊢ u₂ ∷ Nat → Γ ⊢ty indG μx f u₁ u₂
  ⊢indG {μx = μx} dμ df d1 d2 =
    ty-Π (⊢gcdIH dμ)
      (ty-Π (⊢indPWT (⊢wk dμ) (⊢-cast (gcdIH-w μx) (⊢var here)))
            (ty-El (⊢PC (⊢wk (⊢wk d1)) (⊢wk (⊢wk d2)) (asN dfi))))
    where
      dfi = ⊢app (⊢-cast (gcdG-w² μx) (⊢wk (⊢wk df)))
                 (⊢-cast (gcdIH-w² μx) (⊢var (there here)))

  -- ★ the two derived conversions the leaves use
  PC-conv : {Γ : Cx} {v v' : RTm Γ} (u₁ u₂ : RTm Γ) →
            v ⟶* v' → El (PC u₁ u₂ v) ≅ᵀ El (PC u₁ u₂ v')
  PC-conv u₁ u₂ r = red→≅ᵀ (⟶ᵀ*-El (PC-redV u₁ u₂ r))

  PC-convU : {Γ : Cx} {u₁ u₁' u₂ u₂' : RTm Γ} (v : RTm Γ) →
             u₁ ⟶* u₁' → u₂ ⟶* u₂' → El (PC u₁ u₂ v) ≅ᵀ El (PC u₁' u₂' v)
  PC-convU v r₁ r₂ = red→≅ᵀ (⟶ᵀ*-El (PC-redU v r₁ r₂))

  indG-red : {Γ : Cx} {μ u₁ u₂ f g : RTm Γ} → f ⟶* g →
             indG μ f u₁ u₂ ≅ᵀ indG μ g u₁ u₂
  indG-red {u₁ = u₁} {u₂ = u₂} r =
    red→≅ᵀ (⟶ᵀ*-Πʳ (⟶ᵀ*-Πʳ
      (⟶ᵀ*-El (PC-redV (w (w u₁)) (w (w u₂))
                       (⟶*-appˡ (⟶*-ren vs (⟶*-ren vs r)))))))

  ------------------------------------------------------------------------
  -- ★ `indG`'s substitution law and its elimination.
  ------------------------------------------------------------------------

  indPWT-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ i : RTm Γ) →
               subTy σ (indPWT μ i) ≡ indPWT (subTm σ μ) (subTm σ i)
  indPWT-sub {σ = σ} μ i =
    cong₂ (λ u c → Π PairT (Π (Hom Nat (nsuc msr) u) (El c)))
          (sub-w {σ = σ} μ)
          (trans (PC-sub {σ = extS (extS σ)}
                    (fst (var (vs vz))) (snd (var (vs vz)))
                    (app (app (w (w i)) (var (vs vz))) (var vz)))
                 (cong (λ z → PC (fst (var (vs vz))) (snd (var (vs vz)))
                                 (app (app z (var (vs vz))) (var vz)))
                       (sub-w² {σ = σ} i)))

  indG-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (μ f u₁ u₂ : RTm Γ) →
             subTy σ (indG μ f u₁ u₂)
           ≡ indG (subTm σ μ) (subTm σ f) (subTm σ u₁) (subTm σ u₂)
  indG-sub {σ = σ} μ f u₁ u₂ =
    cong₂ Π (gcdIH-sub μ)
      (cong₂ Π (trans (indPWT-sub (w μ) (var vz))
                      (cong (λ u → indPWT u (var vz)) (sub-w {σ = σ} μ)))
               (cong El
                  (trans (PC-sub {σ = extS (extS σ)}
                            (w (w u₁)) (w (w u₂)) (app (w (w f)) (var (vs vz))))
                         (cong₃ (λ a b z → PC a b (app z (var (vs vz))))
                                (sub-w² {σ = σ} u₁) (sub-w² {σ = σ} u₂)
                                (sub-w² {σ = σ} f)))))

  indGElim : {Γ : Ctx} {μ f u₁ u₂ e i h : RTm ⌊ Γ ⌋} →
             Γ ⊢ e ∷ indG μ f u₁ u₂ → Γ ⊢ i ∷ gcdIH μ → Γ ⊢ h ∷ indPWT μ i →
             Γ ⊢ app (app e i) h ∷ El (PC u₁ u₂ (app f i))
  indGElim {μ = μ} {f = f} {u₁ = u₁} {u₂ = u₂} {i = i} {h = h} de di dh =
    ⊢-cast (cong El eq2) (⊢app (⊢-cast eq1 (⊢app de di)) dh)
    where
      p₁ : (t : RTm ⌊ _ ⌋) → subTm (extS (single i)) (w (w t)) ≡ w t
      p₁ t = trans (sub-w {σ = single i} (w t)) (cong w (wk-single {v = i} t))

      eq1 = cong₂ Π (trans (indPWT-sub (w μ) (var vz))
                           (cong (λ u → indPWT u i) (wk-single {v = i} μ)))
                    (cong El
                       (trans (PC-sub {σ = extS (single i)}
                                 (w (w u₁)) (w (w u₂))
                                 (app (w (w f)) (var (vs vz))))
                              (cong₃ (λ a b z → PC a b (app z (w i)))
                                     (p₁ u₁) (p₁ u₂) (p₁ f))))

      eq2 = trans (PC-sub {σ = single h} (w u₁) (w u₂) (app (w f) (w i)))
                  (cong₄ (λ a b z u → PC a b (app z u))
                         (wk-single {v = h} u₁) (wk-single {v = h} u₂)
                         (wk-single {v = h} f) (wk-single {v = h} i))

  ------------------------------------------------------------------------
  -- ★★ THE THREE SPLIT MOTIVES.
  --
  -- ⚠⚠ THE BOUNDARIES ARE NO LONGER `refl` — THAT IS GENERICITY'S PRICE.
  --   At the concrete motive every `subTy` COMPUTED (`…GcdDvd`'s
  --   `probeI₁-at = refl`).  With `PC` opaque each one costs an
  --   `indG-sub`.  Four probes, four rewrites — and nothing else changed.
  ------------------------------------------------------------------------

  MI₁ : {Γ : Cx} → RTy (Γ ∙ ∙)
  MI₁ = indG μ₁ f₁ (fst (var (vs vz))) (var vz)

  ΘI₂ : Ctx → Ctx
  ΘI₂ Γ = ((Γ ▹ PairT) ▹ Nat) ▹ MI₁

  MI₂ : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙)
  MI₂ = indG μ₂ f₂ (var vz) (nsuc (var (vs (vs vz))))

  ΘI₃ : Ctx → Ctx
  ΘI₃ Γ = (ΘI₂ Γ ▹ Nat) ▹ MI₂

  uA₃ uB₃ μAB : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
  uA₃ = nsuc (var (vs vz))
  uB₃ = nsuc (var (vs (vs (vs vz))))
  μAB = monusTm uA₃ uB₃

  MI₃ : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙ ∙ ∙)
  MI₃ = Π (IdN (w μAB) (var vz))
          (indG (w (w (plusTm uA₃ uB₃))) (w f₃) (w (w uA₃)) (w (w uB₃)))

  probeI₁-at : {Γ : Cx} →
               subTy (single (snd (var vz))) (MI₁ {Γ})
             ≡ indG msr gcdBody (fst (var vz)) (snd (var vz))
  probeI₁-at = indG-sub μ₁ f₁ (fst (var (vs vz))) (var vz)

  probeI₁-z : {Γ : Cx} →
              subTy (single nzero) (MI₁ {Γ})
            ≡ indG (plusTm (fst (var vz)) nzero)
                   (natrec G1z gcdInn1 nzero) (fst (var vz)) nzero
  probeI₁-z = indG-sub μ₁ f₁ (fst (var (vs vz))) (var vz)

  ------------------------------------------------------------------------
  -- ★ LEAF 1 — `snd x = 0`.  IH-free: `G1z` returns `fst x` on the nose.
  ------------------------------------------------------------------------

  redI₁z : {Γ : Cx} (i : RTm (Γ ∙ ∙ ∙)) →
           app (w (w (natrec (G1z {Γ}) gcdInn1 nzero))) i
         ⟶* fst (var (vs (vs vz)))
  redI₁z i = ⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done)) (step (β _ i) done)

  leafI₁z : {Γ : Ctx} →
            Prv (Γ ▹ PairT)
                (indG (plusTm (fst (var vz)) nzero)
                      (natrec G1z gcdInn1 nzero) (fst (var vz)) nzero)
  leafI₁z =
    prv _ (⊢lam (⊢gcdIH dμ)
            (⊢lam (⊢indPWT (⊢wk dμ) (⊢-cast (gcdIH-w _) (⊢var here)))
                  (⊢conv (prvOk (leaf-b0 du))
                         (csymᵀ (PC-conv _ nzero (redI₁z (var (vs vz))))))))
    where
      dμ = ⊢plus (⊢fst (⊢var here)) ⊢nzero
      du = ⊢fst (⊢var (there (there here)))

  ------------------------------------------------------------------------
  -- ★ LEAF 2 — `fst x = 0`.  IH-free: `G2z` returns `suc n'`.
  ------------------------------------------------------------------------

  redI₂z : {Γ : Cx} (sb i : RTm (Γ ∙ ∙ ∙ ∙ ∙)) →
           app (w (w (natrec (G2z {Γ}) sb nzero))) i
         ⟶* nsuc (var (vs (vs (vs vz))))
  redI₂z sb i = ⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done)) (step (β _ i) done)

  leafI₂z : {Γ : Ctx} → Prv (ΘI₂ Γ) (subTy (single nzero) MI₂)
  leafI₂z =
    ⊢-castPrv (sym (indG-sub μ₂ f₂ (var vz) (nsuc (var (vs (vs vz))))))
      (prv _ (⊢lam (⊢gcdIH dμ)
               (⊢lam (⊢indPWT (⊢wk dμ) (⊢-cast (gcdIH-w _) (⊢var here)))
                     (⊢conv (prvOk (leaf-a0 db))
                            (csymᵀ (PC-conv nzero _
                                     (redI₂z _ (var (vs vz)))))))))
    where
      dμ = ⊢plus ⊢nzero (⊢nsuc (⊢var (there here)))
      db = ⊢var (there (there (there here)))
      ⊢-castPrv : {Γ : Ctx} {T T' : RTy ⌊ Γ ⌋} → T ≡ T' → Prv Γ T → Prv Γ T'
      ⊢-castPrv refl q = q

  ------------------------------------------------------------------------
  -- ⬜ WHAT IS NOT HERE, AND WHY — the honest half of the experiment.
  --
  -- Split 3's two DEEP leaves and the three-`natrec` assembly are NOT in
  -- this module.  Ported here, it **OOM-KILLED (exit 143, uncontended)** —
  -- at exactly the point and for exactly the reason the CONCRETE version
  -- did (`…GcdDvdL`/`…GcdDvdLs`/`…GcdDvdA1`…`A`: context depth 10, ~1.7x
  -- per slot, the file had to split six ways).
  --
  -- ⇒ **GENERICITY DOES NOT RESCUE THE COST PROFILE.**  The hope was that
  --   an opaque `PC u₁ u₂ v` — a variable application — would elaborate
  --   smaller than `QCode u₁ u₂ v` unfolding to a `⌜Σ⌝` of two `⌜Id⌝`s over
  --   a `mulTm`.  It may well; it did not move the wall.
  --
  -- ★ WHAT THE EXPERIMENT DID ESTABLISH, and it is most of the question:
  --   everything above ports with NO mathematical work — the `PAtR` peel,
  --   the internalised `IndPW`, `indG` and its substitution law, its
  --   elimination, both split probes and both IH-free leaves.  The only
  --   new cost is a PEEL AT EVERY MOTIVE BOUNDARY, where the concrete
  --   version got `refl` for free (`…GcdDvd`'s `probeI₁-at = refl`).
  --
  -- ⇒ the remaining port is mechanical but needs the SAME multi-file
  --   discipline: extract `Motive` to its own module, make this one
  --   `(M : Motive)`-parameterised at FILE level, and carry the deep
  --   leaves and the assembly in further parameterised files.
  ------------------------------------------------------------------------
