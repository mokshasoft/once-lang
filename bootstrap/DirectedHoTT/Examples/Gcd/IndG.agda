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
module DirectedHoTT.Examples.Gcd.IndG where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs; RTy; RTm; El; U; Nat; Hom; Π
        ; var; fst; snd; app; nzero; nsuc; natrec; ⌜Nat⌝
        ; subTm; subTy; renTm; renTy; Ren; Sub; extR; extS )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nzero; ⊢nsuc
        ; βfst; βsnd
        ; ⊢lam; ⊢app; ty-Hom; ty-Nat; ty-Π; ty-El; ⊢⌜Nat⌝
        ; ⊢conv; _≅ᵀ_; csymᵀ; _⟶*_; step; done; wk-single; natrec-suc; ⊢pair; ctrnᵀ )
open import DirectedHoTT.Metatheory.Injectivity
  using ( red→≅ᵀ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-El; doneᵀ )
open import DirectedHoTT.Metatheory.Confluence using ( ⟶*-trans; ⟶*-appˡ; ⟶*-ren )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast; Ren⊢; ⊢[] )
open import DirectedHoTT.Lib.Wk using ( w; sub-w; sub-w²; ren-w; cong₃; cong₄; pw1 )
open import DirectedHoTT.Lib.Pair using ( PairT; ⊢PairT; asN )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Monus using ( monusTm; ⊢monus )
open import DirectedHoTT.Lib.ArithComm using ( IdN; ⊢tyIdN; reflN; ⊢reflN )
open import DirectedHoTT.Lib.Amrec
  using ( Prv; prv; prvOk; prv-cast; wR; renren; module AmTΠ )
open import DirectedHoTT.Lib.IHCall
  using ( ihCallT; ihCall; ⊢ihCallT; ihCallIntro; ihCallElim )
open import DirectedHoTT.Lib.AmrecInd using ( PAtR; IndPW; IndStep )
open import DirectedHoTT.Lib.Natrec using ( Ren⊢-id; ⊢natrec-var; prvNatrec )
open import DirectedHoTT.Spec.Typing
  using ( natrec-zero; β; ξ-appˡ; ⊢natrec )
open import DirectedHoTT.Examples.Gcd.Step
  using ( msr; ⊢msr; gcdIH; ⊢gcdIH; gcdG; ⊢gcdG; gcdStp; gcdBody
        ; PAIRᶻ; ⊢PAIRᶻ; CERTᶻ; ⊢CERTᶻ; PAIRˢ; CERTˢ; KS; NS
        ; G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s )
open import DirectedHoTT.Examples.Gcd.StepExt
  using ( appGcdIH; gcdIH-w; gcdIH-w²; gcdAt; red-β; μ₁; f₁; μ₂; f₂; μ₃; f₃
        ; probe₁-s; probe₂-s )
open import DirectedHoTT.Examples.Gcd.StepExtE using ( gcdIH-sub )
open import DirectedHoTT.Examples.Gcd.StepExtL using ( red₃z )
open import DirectedHoTT.Examples.Gcd.StepExtLs using ( red₃s )
open import DirectedHoTT.Lib.ArithMonus using ( ⊢desc-left )
open import DirectedHoTT.Lib.Pair using ( msrPair )

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
    -- ⚠ was a LOCALLY re-derived `⊢-castPrv`, character-for-character
    --   `Lib/Amrec.prv-cast`, in a file that already imports it.
    prv-cast (sym (indG-sub μ₂ f₂ (var vz) (nsuc (var (vs (vs vz))))))
      (prv _ (⊢lam (⊢gcdIH dμ)
               (⊢lam (⊢indPWT (⊢wk dμ) (⊢-cast (gcdIH-w _) (⊢var here)))
                     (⊢conv (prvOk (leaf-a0 db))
                            (csymᵀ (PC-conv nzero _
                                     (redI₂z _ (var (vs vz)))))))))
    where
      dμ = ⊢plus ⊢nzero (⊢nsuc (⊢var (there here)))
      db = ⊢var (there (there (there here)))


  ------------------------------------------------------------------------
  -- ★★★ SPLIT 3's DEEP ZERO LEAF — MOTIVE-GENERIC.
  --
  -- ⚠⚠ THIS IS THE LEAF THE 2026-08-17 EXPERIMENT COULD NOT PLACE.  Its
  --   absence was recorded as "GENERICITY DOES NOT RESCUE THE COST
  --   PROFILE", on an OOM (exit 143, believed uncontended).  RE-TESTED
  --   2026-08-21 under `+RTS -c`: see the note at the foot of this file.
  --
  -- ★ AND THE GENERIC LEAF IS *SHORTER* THAN THE CONCRETE ONE.  Compare
  --   `…GcdDvdL`: there the IH's two conjuncts are taken apart on the spot
  --   with `⊢Q-fst`/`⊢Q-snd` before `gcdLeaf-le` can use them.  Here
  --   `leaf-le` receives `El (PC a (monusTm b a) v)` WHOLE and the
  --   customer does its own projecting — the `⌜Σ⌝` customer with
  --   `⊢Q-fst`/`⊢Q-snd`, the `⌜Π⌝` customer by decoding to a function
  --   type.  That interface choice is what carries the genericity.
  ------------------------------------------------------------------------

  B₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
  B₃ = plusTm uA₃ uB₃

  ⊢B₃ : {Γ : Ctx} → ΘI₃ Γ ⊢ B₃ ∷ Nat
  ⊢B₃ = ⊢plus (⊢nsuc (⊢var (there here)))
              (⊢nsuc (⊢var (there (there (there here)))))

  F₃ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
  F₃ = subTm (single nzero) f₃

  Θ₃E : Ctx → Ctx
  Θ₃E Γ = ΘI₃ Γ ▹ IdN μAB nzero

  Θ₃L : Ctx → Ctx
  Θ₃L Γ = (Θ₃E Γ ▹ gcdIH (w B₃)) ▹ indPWT (w (w B₃)) (var vz)

  A₈ B₈ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  A₈ = w (w (w uA₃))
  B₈ = w (w (w uB₃))

  dA₈ : {Γ : Ctx} → Θ₃L Γ ⊢ A₈ ∷ Nat
  dA₈ = ⊢nsuc (⊢var (there (there (there (there here)))))

  dB₈ : {Γ : Ctx} → Θ₃L Γ ⊢ B₈ ∷ Nat
  dB₈ = ⊢nsuc (⊢var (there (there (there (there (there (there here)))))))

  dPAIR : {Γ : Ctx} → Θ₃L Γ ⊢ w (w PAIRᶻ) ∷ PairT
  dPAIR = ⊢wk (⊢wk ⊢PAIRᶻ)

  dCERT : {Γ : Ctx} → Θ₃L Γ ⊢ w (w CERTᶻ)
            ∷ Hom Nat (nsuc (subTm (single (w (w PAIRᶻ))) msr)) (w (w (w B₃)))
  dCERT = ⊢wk (⊢wk ⊢CERTᶻ)

  dIH : {Γ : Ctx} → Θ₃L Γ ⊢ var (vs vz) ∷ gcdIH (w (w (w B₃)))
  dIH = ⊢-cast (gcdIH-w² (w B₃)) (⊢var (there here))

  dV : {Γ : Ctx} → Θ₃L Γ ⊢ app (app (var (vs vz)) (w (w PAIRᶻ))) (w (w CERTᶻ)) ∷ Nat
  dV = asN (appGcdIH dIH dPAIR dCERT)

  -- ★ `IndPW`, ELIMINATED at `(PAIRᶻ , CERTᶻ)` — where the hypothesis is spent.
  dcall : {Γ : Ctx} →
          Θ₃L Γ ⊢ app (app (var vz) (w (w PAIRᶻ))) (w (w CERTᶻ))
            ∷ El (PC A₈ (monusTm B₈ A₈)
                    (app (app (var (vs vz)) (w (w PAIRᶻ))) (w (w CERTᶻ))))
  dcall =
    ⊢conv (indPWElim (⊢-cast (indPWT-w (w (w B₃)) (var vz)) (⊢var here))
                     dPAIR dCERT)
          (PC-convU _ (step (βfst _ _) done) (step (βsnd _ _) done))

  dEq : {Γ : Ctx} → Θ₃L Γ ⊢ var (vs (vs vz)) ∷ IdN (monusTm A₈ B₈) nzero
  dEq = ⊢var (there (there here))

  innerI₃z : {Γ : Ctx} → Prv (Θ₃L Γ) (El (PC A₈ B₈ (app (w (w (w F₃))) (var (vs vz)))))
  innerI₃z =
    prv _ (⊢conv (prvOk (leaf-le dA₈ dB₈ dV dEq dcall))
                 (csymᵀ (PC-conv A₈ B₈ (red₃z _ (var (vs vz))))))

  -- ★ the two inner binders, at the SUBSTITUTED `indG` — stated exactly as
  --   `indG-sub`'s right-hand side so the cast below lines up by construction.
  bodyI₃z : {Γ : Ctx} →
            Prv (ΘI₃ Γ ▹ IdN μAB nzero)
                (indG (subTm (extS (single nzero)) (w (w B₃)))
                      (subTm (extS (single nzero)) (w f₃))
                      (subTm (extS (single nzero)) (w (w uA₃)))
                      (subTm (extS (single nzero)) (w (w uB₃))))
  bodyI₃z =
    prv _ (⊢lam (⊢gcdIH (⊢wk ⊢B₃))
            -- ⚠ NO PINNING NEEDED, and that was TESTED (2026-08-21): pinning
            --   `⊢indPWT`'s `{μa}`/`{ih}` was tried and then REMOVED, and the
            --   module still builds. The implicits solve once the goal is
            --   stated in the substituted form below. Do not add pinning
            --   here on the strength of `pin-implicits-on-defined-set-types`
            --   without re-testing — that rule is real, but it is not what
            --   was wrong here.
            (⊢lam (⊢indPWT (⊢wk (⊢wk ⊢B₃))
                           (⊢-cast (gcdIH-w (w B₃)) (⊢var here)))
                  (prvOk innerI₃z)))

  leafI₃z : {Γ : Ctx} → Prv (ΘI₃ Γ) (subTy (single nzero) MI₃)
  leafI₃z =
    -- ⚠⚠ THE GENERIC TAX, PRECISELY.  Concretely `subTm σ (QCode …)` UNFOLDS
    --   — `QCode` is a definition, so Agda pushes the substitution in
    --   structurally and `…GcdDvdL`'s leaf needs no cast here at all.
    --   Generically `subTm σ (PC …)` is STUCK: `PC` is a module parameter,
    --   so the substitution law has to be CITED.  That is what `indG-sub`
    --   is for, and `leafI₂z` above pays the same tax.
    prv _ (⊢lam (⊢tyIdN (⊢monus (⊢nsuc (⊢var (there here)))
                                (⊢nsuc (⊢var (there (there (there here))))))
                        ⊢nzero)
            (⊢-cast (sym (indG-sub {σ = extS (single nzero)}
                            (w (w B₃)) (w f₃) (w (w uA₃)) (w (w uB₃))))
                    (prvOk bodyI₃z)))


  ------------------------------------------------------------------------
  -- ★★★ SPLIT 3's DEEP SUCCESSOR LEAF — MOTIVE-GENERIC.
  --
  -- ⚠ THE SAME ONE TAX AS `leafI₃z`, and only that one: `subTm σ (PC …)`
  --   is STUCK where `subTm σ (QCode …)` unfolds, so `indG-sub` must be
  --   cited — here at `σ = extS nrs`, the `natrec` SUCCESSOR substitution.
  --   No implicit needs pinning; that was tested for `leafI₃z` and the
  --   pinning removed again.
  ------------------------------------------------------------------------

  B₄ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  B₄ = plusTm (nsuc (var (vs (vs (vs vz)))))
              (nsuc (var (vs (vs (vs (vs (vs vz)))))))

  F₄ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  F₄ = subTm nrs f₃

  ⊢B₄ : {Γ : Ctx} → ((ΘI₃ Γ ▹ Nat) ▹ MI₃) ⊢ B₄ ∷ Nat
  ⊢B₄ = ⊢plus (⊢nsuc (⊢var (there (there (there here)))))
              (⊢nsuc (⊢var (there (there (there (there (there here)))))))

  rr₄ : {Γ : Cx} → subTm nrs (f₃ {Γ}) ⟶* G3s
  rr₄ = step (natrec-suc _ _ _) done

  EqT : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  EqT = IdN (monusTm (nsuc (var (vs (vs (vs vz)))))
                     (nsuc (var (vs (vs (vs (vs (vs vz))))))))
            (nsuc (var (vs vz)))

  ⊢EqT : {Γ : Ctx} → ((ΘI₃ Γ ▹ Nat) ▹ MI₃) ⊢ty EqT
  ⊢EqT = ⊢tyIdN (⊢monus (⊢nsuc (⊢var (there (there (there here)))))
                        (⊢nsuc (⊢var (there (there (there (there (there here))))))))
                (⊢nsuc (⊢var (there here)))

  Θ₄E : Ctx → Ctx
  Θ₄E Γ = (((ΘI₃ Γ ▹ Nat) ▹ MI₃) ▹ EqT)

  Θ₄ : Ctx → Ctx
  Θ₄ Γ = ((Θ₄E Γ) ▹ gcdIH (w B₄)) ▹ indPWT (w (w B₄)) (var vz)

  A₁₀ B₁₀ P₁₀ : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  A₁₀ = nsuc (var (vs (vs (vs (vs (vs (vs vz)))))))
  B₁₀ = nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))
  P₁₀ = var (vs (vs (vs (vs vz))))

  dA₁₀ : {Γ : Ctx} → Θ₄ Γ ⊢ A₁₀ ∷ Nat
  dA₁₀ = ⊢nsuc (⊢var (there (there (there (there (there (there here)))))))

  dB₁₀ : {Γ : Ctx} → Θ₄ Γ ⊢ B₁₀ ∷ Nat
  dB₁₀ = ⊢nsuc (⊢var (there (there (there (there (there (there (there (there here)))))))))

  dP₁₀ : {Γ : Ctx} → Θ₄ Γ ⊢ P₁₀ ∷ Nat
  dP₁₀ = ⊢var (there (there (there (there here))))

  -- ⚠⚠ `⊢PAIRˢ`/`⊢CERTˢ` RE-DERIVED, NOT IMPORTED — same measurement as
  --   `…GcdDvdLs`: `…GcdStep` states them at `CΓs Γ B C D`, whose last slot
  --   is hard-wired to `gcdIH …`, and this branch binds the SCRUTINEE
  --   EQUATION there.  Generalising `CΓs` over that slot OOM-KILLED
  --   `…ExamplesGcdLeEq`/`…GcdLeMid`.  Six lines of duplication, not a
  --   regression there.
  dksL : {Γ : Ctx} → Θ₄E Γ ⊢ KS ∷ Nat
  dksL = ⊢var (there (there (there (there here))))

  dnsL : {Γ : Ctx} → Θ₄E Γ ⊢ NS ∷ Nat
  dnsL = ⊢var (there (there (there (there (there (there here))))))

  ⊢PAIRˢL : {Γ : Ctx} → Θ₄E Γ ⊢ PAIRˢ ∷ PairT
  ⊢PAIRˢL = ⊢pair ty-Nat (⊢monus (⊢nsuc dksL) (⊢nsuc dnsL)) (⊢nsuc dnsL)

  ⊢CERTˢL : {Γ : Ctx} → Θ₄E Γ ⊢ CERTˢ
              ∷ Hom Nat (nsuc (plusTm (fst PAIRˢ) (snd PAIRˢ)))
                        (plusTm (nsuc KS) (nsuc NS))
  ⊢CERTˢL =
    ⊢conv (⊢desc-left dksL dnsL)
          (csymᵀ (msrPair (monusTm (nsuc KS) (nsuc NS)) (nsuc NS)
                           (plusTm (nsuc KS) (nsuc NS))))

  dPAIRs : {Γ : Ctx} → Θ₄ Γ ⊢ w (w PAIRˢ) ∷ PairT
  dPAIRs = ⊢wk (⊢wk ⊢PAIRˢL)

  dCERTs : {Γ : Ctx} → Θ₄ Γ ⊢ w (w CERTˢ)
             ∷ Hom Nat (nsuc (subTm (single (w (w PAIRˢ))) msr)) (w (w (w B₄)))
  dCERTs = ⊢wk (⊢wk ⊢CERTˢL)

  dIHs : {Γ : Ctx} → Θ₄ Γ ⊢ var (vs vz) ∷ gcdIH (w (w (w B₄)))
  dIHs = ⊢-cast (gcdIH-w² (w B₄)) (⊢var (there here))

  dVs : {Γ : Ctx} → Θ₄ Γ ⊢ app (app (var (vs vz)) (w (w PAIRˢ))) (w (w CERTˢ)) ∷ Nat
  dVs = asN (appGcdIH dIHs dPAIRs dCERTs)

  dcalls : {Γ : Ctx} →
           Θ₄ Γ ⊢ app (app (var vz) (w (w PAIRˢ))) (w (w CERTˢ))
             ∷ El (PC (monusTm A₁₀ B₁₀) B₁₀
                     (app (app (var (vs vz)) (w (w PAIRˢ))) (w (w CERTˢ))))
  dcalls =
    ⊢conv (indPWElim (⊢-cast (indPWT-w (w (w B₄)) (var vz)) (⊢var here))
                     dPAIRs dCERTs)
          (PC-convU _ (step (βfst _ _) done) (step (βsnd _ _) done))

  dEqs : {Γ : Ctx} → Θ₄ Γ ⊢ var (vs (vs vz)) ∷ IdN (monusTm A₁₀ B₁₀) (nsuc P₁₀)
  dEqs = ⊢var (there (there here))

  innerI₃s : {Γ : Ctx} → Prv (Θ₄ Γ) (El (PC A₁₀ B₁₀ (app (w (w (w F₄))) (var (vs vz)))))
  innerI₃s =
    prv _ (⊢conv (prvOk (leaf-gt dA₁₀ dB₁₀ dVs dP₁₀ dEqs dcalls))
                 (csymᵀ (PC-conv A₁₀ B₁₀ (red₃s rr₄ (var (vs vz))))))

  -- ★ the two inner binders at the SUBSTITUTED `indG`, stated as
  --   `indG-sub`'s right-hand side (σ = extS nrs).
  bodyI₃s : {Γ : Ctx} →
            Prv (Θ₄E Γ)
                (indG (subTm (extS nrs) (w (w B₃)))
                      (subTm (extS nrs) (w f₃))
                      (subTm (extS nrs) (w (w uA₃)))
                      (subTm (extS nrs) (w (w uB₃))))
  bodyI₃s =
    prv _ (⊢lam (⊢gcdIH (⊢wk ⊢B₄))
            (⊢lam (⊢indPWT (⊢wk (⊢wk ⊢B₄))
                           (⊢-cast (gcdIH-w (w B₄)) (⊢var here)))
                  (prvOk innerI₃s)))

  leafI₃s : {Γ : Ctx} → Prv ((ΘI₃ Γ ▹ Nat) ▹ MI₃) (subTy nrs MI₃)
  leafI₃s =
    prv _ (⊢lam ⊢EqT
            (⊢-cast (sym (indG-sub {σ = extS nrs}
                            (w (w B₃)) (w f₃) (w (w uA₃)) (w (w uB₃))))
                    (prvOk bodyI₃s)))


  ------------------------------------------------------------------------
  -- ★★ THE THREE MOTIVES, TYPED.
  ------------------------------------------------------------------------

  ⊢MI₁ : {Γ : Ctx} → ((Γ ▹ PairT) ▹ Nat) ⊢ty MI₁
  ⊢MI₁ = ⊢indG (⊢plus (⊢fst (⊢var (there here))) (⊢var here))
               (⊢natrec-var ⊢G1 ⊢G1z ⊢gcdInn1)
               (⊢fst (⊢var (there here))) (⊢var here)

  ⊢MI₂ : {Γ : Ctx} → (ΘI₂ Γ ▹ Nat) ⊢ty MI₂
  ⊢MI₂ = ⊢indG (⊢plus (⊢var here) (⊢nsuc (⊢var (there (there here)))))
               (⊢natrec-var ⊢G2 ⊢G2z ⊢gcdInn2)
               (⊢var here) (⊢nsuc (⊢var (there (there here))))

  ⊢MI₃ : {Γ : Ctx} → (ΘI₃ Γ ▹ Nat) ⊢ty MI₃
  ⊢MI₃ =
    ty-Π (⊢tyIdN (⊢monus (⊢nsuc (⊢var (there (there here))))
                         (⊢nsuc (⊢var (there (there (there (there here)))))))
                 (⊢var here))
         (⊢indG (⊢wk (⊢plus (⊢nsuc (⊢var (there (there here))))
                            (⊢nsuc (⊢var (there (there (there (there here))))))))
                (⊢wk (⊢natrec-var ⊢G3 ⊢G3z ⊢G3s))
                (⊢wk (⊢nsuc (⊢var (there (there here)))))
                (⊢wk (⊢nsuc (⊢var (there (there (there (there here))))))))


  ------------------------------------------------------------------------
  -- ★★★ THE THREE SPLITS — the nested `natrec`s.
  ------------------------------------------------------------------------

  split3 : {Γ : Ctx} → Prv (ΘI₃ Γ) (subTy (single μAB) MI₃)
  split3 = prvNatrec ⊢MI₃ leafI₃z leafI₃s
                     (⊢monus (⊢nsuc (⊢var (there here)))
                             (⊢nsuc (⊢var (there (there (there here))))))


  -- ⚠ `probeI₃-at` IS `refl` IN THE CONCRETE DEVELOPMENT AND CANNOT BE HERE.
  --   `subTm σ (QCode …)` UNFOLDS, so Agda pushes the substitution through
  --   `indG` structurally and `…GcdDvd`'s probe is `refl`.  `subTm σ (PC …)`
  --   is STUCK — `PC` is a module parameter — so `indG-sub` must be cited.
  --   Same opacity tax as the leaves, in the assembly this time.
  probeI₃-atP : {Γ : Cx} →
                subTy (single μAB) (MI₃ {Γ})
              ≡ Π (IdN μAB μAB)
                  (indG (subTm (extS (single μAB)) (w (w (plusTm uA₃ uB₃))))
                        (subTm (extS (single μAB)) (w f₃))
                        (subTm (extS (single μAB)) (w (w uA₃)))
                        (subTm (extS (single μAB)) (w (w uB₃))))
  probeI₃-atP =
    cong₂ Π refl (indG-sub {σ = extS (single μAB)}
                    (w (w (plusTm uA₃ uB₃))) (w f₃) (w (w uA₃)) (w (w uB₃)))


  -- ⚠ THE STEP `StepExt` DOES NOT HAVE: discharge the equation with `reflN`.
  split3app : {Γ : Ctx} →
              Prv (ΘI₃ Γ) (indG (plusTm uA₃ uB₃) (subTm (single μAB) f₃) uA₃ uB₃)
  split3app {Γ} =
    prv _ (⊢-cast peel
            (⊢app (⊢-cast probeI₃-atP (prvOk split3))
                  (⊢reflN (⊢monus (⊢nsuc (⊢var (there here)))
                                  (⊢nsuc (⊢var (there (there (there here)))))))))
    where
      R = reflN (μAB {Γ = ⌊ Γ ⌋})

      pk : (t : RTm ⌊ ΘI₃ Γ ⌋) →
           subTm (single R) (subTm (extS (single μAB)) (w (w t))) ≡ t
      pk t = trans (cong (subTm (single R)) (pw1 {u = μAB} t)) (wk-single {v = R} t)

      pf : subTm (single R) (subTm (extS (single μAB)) (w f₃))
         ≡ subTm (single μAB) f₃
      pf = trans (cong (subTm (single R)) (sub-w {σ = single μAB} f₃))
                 (wk-single {v = R} (subTm (single μAB) f₃))

      peel = trans (indG-sub {σ = single R}
                      (subTm (extS (single μAB)) (w (w (plusTm uA₃ uB₃))))
                      (subTm (extS (single μAB)) (w f₃))
                      (subTm (extS (single μAB)) (w (w uA₃)))
                      (subTm (extS (single μAB)) (w (w uB₃))))
                   (cong₄ indG (pk (plusTm uA₃ uB₃)) pf (pk uA₃) (pk uB₃))


  -- ⚠ ONE MORE STEP THAN THE CONCRETE VERSION.  `…GcdDvdA` writes this as
  --   `indG-red probe₂-s` alone, because `subTy nrs (indG …)` unfolds when
  --   the motive is `QCode`.  With `PC` a parameter it is STUCK, so
  --   `indG-sub` has to be cited before the reduction can apply.
  eq→≅ᵀ : {Γ : Cx} {T T' : RTy Γ} → T ≡ T' → T ≅ᵀ T'
  eq→≅ᵀ refl = red→≅ᵀ doneᵀ

  conv₂I : {Γ : Cx} →
           subTy nrs (MI₂ {Γ})
         ≅ᵀ indG (plusTm uA₃ uB₃) (subTm (single μAB) f₃) uA₃ uB₃
  conv₂I = ctrnᵀ (eq→≅ᵀ (indG-sub {σ = nrs} μ₂ f₂ (var vz) (nsuc (var (vs (vs vz))))))
                 (indG-red probe₂-s)

  -- ⚠ `{⌊ Γ ⌋}` PINNED: `MI₂` is a DEFINED function and `⌊_⌋` is not
  --   injective, so the raw context never solves from the expected type.
  split2 : {Γ : Ctx} →
           Prv (ΘI₂ Γ) (subTy (single (fst (var (vs (vs vz))))) MI₂)
  split2 {Γ} = prvNatrec ⊢MI₂ leafI₂z
                         (prv _ (⊢conv (prvOk split3app) (csymᵀ (conv₂I {⌊ Γ ⌋}))))
                         (⊢fst (⊢var (there (there here))))

  conv₁I : {Γ : Cx} →
           subTy nrs (MI₁ {Γ}) ≅ᵀ subTy (single (fst (var (vs (vs vz))))) MI₂
  conv₁I =
    ctrnᵀ (eq→≅ᵀ (indG-sub {σ = nrs} μ₁ f₁ (fst (var (vs vz))) (var vz)))
      (ctrnᵀ (indG-red probe₁-s)
             (eq→≅ᵀ (sym (indG-sub {σ = single (fst (var (vs (vs vz))))}
                            μ₂ f₂ (var vz) (nsuc (var (vs (vs vz))))))))

  ------------------------------------------------------------------------
  -- ★★★★★ THE INDUCTION, AT THE GENERIC CARRIER.
  ------------------------------------------------------------------------

  -- ⚠ THE CAST THE CONCRETE VERSION DOES NOT NEED.  `⊢natrec` lands at
  --   `subTy (single (snd (var vz))) MI₁`; concretely that REDUCES to the
  --   `indG` form because `QCode` unfolds, so `…GcdDvdA` states the result
  --   directly.  Generically `subTm σ (PC …)` is stuck — cite `indG-sub`.
  ind : {Γ : Ctx} →
        Prv (Γ ▹ PairT) (indG msr gcdBody (fst (var vz)) (snd (var vz)))
  ind {Γ} =
    prv-cast peel
      (prvNatrec ⊢MI₁
                 (prv-cast (sym peelz) leafI₁z)
                 (prv _ (⊢conv (prvOk split2) (csymᵀ (conv₁I {⌊ Γ ⌋}))))
                 (⊢snd (⊢var here)))
    where
      N = snd (var vz)
      -- ⚠ `leafI₁z` is stated in the SUBSTITUTED form; `⊢natrec` wants
      --   `subTy (single nzero) MI₁`.  Concretely those coincide by
      --   computation; generically `indG-sub` must bridge them.
      --   (`leafI₂z` already carries its own `⊢-castPrv` for this.)
      peelz = indG-sub {σ = single nzero} μ₁ f₁ (fst (var (vs vz))) (var vz)
      peel = trans (indG-sub {σ = single N} μ₁ f₁ (fst (var (vs vz))) (var vz))
                   (cong₄ indG refl refl refl refl)

  ------------------------------------------------------------------------
  -- ★★★★★★ …AND `IndStep`, DISCHARGED — MOTIVE-GENERIC.
  ------------------------------------------------------------------------

  -- ⚠ `ρ` is BOUND and PASSED: `PAtR` is a defined function, so the ambient
  --   renaming never solves from the goal.
  indStep : {Δ : Ctx} → IndStep Δ PairT ⌜Nat⌝ msr gcdStp gP
  indStep {Δ} {Θ} {ρ} hρ a ih da dih pw =
    prv-cast (cong El (sym (PAtR-P ρ a (app (app gcdStp a) ih))))
      (prv _ (⊢conv (indGElim (⊢-cast (indG-sub {σ = single a}
                                         msr gcdBody (fst (var vz)) (snd (var vz)))
                                      (⊢[] (prvOk ind) da))
                              dih
                              (prvOk (indPWIntro (⊢plus (⊢fst da) (⊢snd da)) pw)))
                    (csymᵀ (PC-conv (fst a) (snd a) (red-β a ih)))))

  ------------------------------------------------------------------------
  -- ⬜ WHAT IS STILL NOT HERE — and the old reason was WRONG.
  --
  -- ⚠⚠ RETRACTED 2026-08-21. This block used to read "GENERICITY DOES NOT
  --   RESCUE THE COST PROFILE", on the evidence that split 3's deep leaf
  --   OOM-KILLED (exit 143, believed uncontended) when ported here.
  --
  --   `leafI₃z` IS NOW ABOVE, and it builds in **6s under the DEFAULT
  --   copying collector** (5s under `-c`), so MEMORY WAS NEVER THE
  --   CONSTRAINT and neither was the collector.
  --
  -- ⚠⚠ WHAT ACTUALLY FIXED IT — and an earlier version of this note got
  --   this WRONG, so read the method as well as the answer. The port needed
  --   TWO changes at once: (a) pinning `⊢indPWT`'s implicits, and (b)
  --   citing `indG-sub` so the goal is stated in the SUBSTITUTED form
  --   (`bodyI₃z`). Attributing the fix to (a) was the obvious reading —
  --   `pin-implicits-on-defined-set-types` is a real and well-documented
  --   trap here.
  --
  --   ⇒ IT WAS TESTED AND IT WAS (b). Removing the pinning afterwards
  --     leaves the module green. (a) was never necessary.
  --     ⭐ Two changes, one fix: attributing without ablating is guessing.
  --
  -- ⬜ SO WHY 2026-08-17 OOM'd IS STILL UNKNOWN. It was not a memory wall
  --   (this builds in 6s), not the collector (the default suffices), and
  --   not unpinned implicits (tested above). Whatever that port did
  --   differently was not recorded, and the OOM is the only surviving
  --   evidence — which, per `exit-143-is-not-evidence-about-cost`, is
  --   evidence of very little. Do not invent a third cause to close the
  --   gap; the honest state is that the conclusion drawn from it was
  --   unsupported, not that we know what happened.
  --
  -- ★ WHAT THE PORT ACTUALLY COSTS, now that it exists — and the old note
  --   had the right instinct with the wrong mechanism. It is not a peel
  --   here and there: ABSTRACTION MAKES THE MOTIVE OPAQUE, and opacity
  --   costs every DEFINITIONAL equality that used to run through it.
  --     · `subTm σ (QCode …)` UNFOLDS — Agda pushes the substitution in
  --       structurally, so `…GcdDvdL`'s leaf cites nothing.
  --       `subTm σ (PC …)` is STUCK, so `indG-sub` must be cited by hand.
  --     · `⊢indPWT`'s implicits SOLVE concretely; here they must be pinned,
  --       because `PC` is a parameter and unification cannot see into it.
  --   ⇒ The same opacity that makes the generic term SMALLER is what
  --     blocks the reductions. Those are one property, not two.
  --
  -- ⬜ REMAINING: split 3's SUCCESSOR deep leaf (`leafI₃s`, concretely in
  --   `…GcdDvdLs`) and the three-`natrec` assembly. Both are now expected
  --   to be mechanical — the same two taxes, already characterised.

  ------------------------------------------------------------------------
