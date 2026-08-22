------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — GAP B LAYER 2: gcd MEETS THE DIVISIBILITY SPEC.
--
-- ⚠⚠ THE MOTIVE IS A CONJUNCTION, AND THAT IS FORCED, NOT A CHOICE.
--   gcd's `a > b` branch recurses at `(a ∸ b , b)`, so the IH gives
--   `d ∣ (a ∸ b)`; reaching `d ∣ a` needs `a ≡ (a ∸ b) + b` (`monusPlus`)
--   AND the second conjunct `d ∣ b`.  Symmetrically for `d ∣ b` in the
--   `a ≤ b` branch.  ⇒ **neither `gcd ∣ a` nor `gcd ∣ b` is provable
--   alone by this recursion**; they are ONE pass with two projections.
--
-- ★ AND IT IS A CODE.  `amrec-ind`'s motive lives in `U`, because `⊢jsub`
--   transports code families — the same constraint that forced certificate
--   irrelevance in `amrec-unfold-Id`.  `⊢dvdCode` was built to clear it.
--
-- ⇒ this file is step 5 of `GAP-B-LAYER2-PLAN.md`; `IndStep` is step 7.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Gcd.Dvd where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs
        ; RTy; RTm; Nat; U; El; Σ'
        ; var; fst; snd; ⌜Nat⌝; nzero; nsuc; Π; app; Hom; natrec; subTy
        ; subTm; renTm; renTy; Ren; extR; extS )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app; ty-Hom; ty-Nat; ty-Π; ty-El; ⊢⌜Nat⌝
        ; ⊢conv; _≅ᵀ_; csymᵀ; natrec-zero; _⟶*_; step; done; β; ξ-appˡ; wk-single )
open import DirectedHoTT.Metatheory.Confluence using ( ⟶*-trans; ⟶*-appˡ; ⟶*-ren )
open import DirectedHoTT.Metatheory.Injectivity using ( red→≅ᵀ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-El )
open import DirectedHoTT.Lib.Wk using ( w; sub-w; ren-w )
open import DirectedHoTT.Lib.Pair using ( PairT; asN; asP )
open import DirectedHoTT.Lib.DvdArith
  using ( QCode; ⊢QCode; QCode-sub; QCode-ren; QCode-red; QCode-conv
        ; ⊢Q-intro; ⊢Q-fst; ⊢Q-snd
        ; ⊢dvd-zero; ⊢dvd-refl; ⊢dvd-plus; ⊢dvd-cong; ⊢congPL )
open import DirectedHoTT.Lib.Dvd using ( dvdT )
open import DirectedHoTT.Lib.Monus using ( monusTm; ⊢monus )
open import DirectedHoTT.Lib.ArithComm using ( IdN; ⊢symN; ⊢transN )
open import DirectedHoTT.Lib.MonusPlus using ( monusPlus )
open import DirectedHoTT.Lib.MonusLe using ( monusLe )
open import DirectedHoTT.Lib.Amrec using ( Prv; prv; prvOk; wR; renren )
open import DirectedHoTT.Lib.AmrecInd using ( PAtR; IndPW )
open import DirectedHoTT.Lib.Natrec using ( Ren⊢-id )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast; Ren⊢ )
open import DirectedHoTT.Examples.Gcd.Step
  using ( msr; ⊢msr; gcdIH; ⊢gcdIH; gcdG; ⊢gcdG
        ; G1z; gcdInn1; G2z; gcdInn2; G3z; G3s; gcdBody; gcdStp )
open import DirectedHoTT.Examples.Gcd.StepExt
  using ( appGcdIH; gcdIH-w; gcdIH-w²; gcdAt; red-β
        ; μ₁; f₁; μ₂; f₂; μ₃; f₃; Θ₂; Θ₃; probe₁-s; probe₂-s )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Pair using ( ⊢PairT )


------------------------------------------------------------------------
-- ★★★ THE MOTIVE.  Slot [1] is the ARGUMENT (the pair), slot [0] the
--   RESULT (gcd of it) — the order `amrec-ind` fixes.
--
--     P (x , v)  :=  v ∣ fst x  ∧  v ∣ snd x
------------------------------------------------------------------------

gcdP : {Γ : Cx} → RTm ((Γ ∙) ∙)
gcdP = QCode (fst (var (vs vz))) (snd (var (vs vz))) (var vz)

⊢gcdP : {Δ : Ctx} → ((Δ ▹ PairT) ▹ El ⌜Nat⌝) ⊢ gcdP ∷ U
⊢gcdP = ⊢QCode (⊢fst dx) (⊢snd dx) (asN (⊢var here))
  where
    -- ⚠ `PairT = Σ' Nat Nat` is CLOSED, so `renTy vs (renTy vs PairT)`
    --   computes back to `PairT` and this needs no cast.
    dx = ⊢var (there here)

------------------------------------------------------------------------
-- ★★ …AND `PAtR` AT IT.  `amrec-ind` states every premise through `PAtR`;
--   this is the one peel that turns those statements into readable
--   divisibility goals.
--
-- ⚠ THREE REWRITES, NOT ZERO: the ambient renaming, then the argument
--   slot, then the result slot — and each needs `QCode`'s naturality
--   because `dvdCode` contains a `mulTm`, which commutes with neither
--   `subTm` nor `renTm` definitionally.
------------------------------------------------------------------------

-- ⚠ STATED AT `Cx`, NOT `Ctx`.  `PAtR` is `Cx`-indexed, and `⌊_⌋` is not
--   injective — at `Ctx` the target context never solves and every call
--   site leaves an unsolved meta.  (Cost of getting it wrong: one round.)
PAtR-gcd : {Γ Γ' : Cx} (ρ : Ren Γ Γ') (y val : RTm Γ') →
           PAtR ρ gcdP y val ≡ QCode (fst y) (snd y) val
PAtR-gcd ρ y val =
  trans (cong (λ t → subTm (single val) (subTm (extS (single y)) t))
              (QCode-ren {ρ = extR (extR ρ)}
                         (fst (var (vs vz))) (snd (var (vs vz))) (var vz)))
    (trans (cong (subTm (single val))
                 (QCode-sub {σ = extS (single y)}
                            (fst (var (vs vz))) (snd (var (vs vz))) (var vz)))
      (trans (QCode-sub {σ = single val} (fst (w y)) (snd (w y)) (var vz))
             (cong (λ u → QCode (fst u) (snd u) val)
                   (wk-single {v = val} y))))

------------------------------------------------------------------------
-- ★★★★★ THE FOUR LEAVES OF `IndStep`, AS TOP-LEVEL `Def`-BACKED LEMMAS.
--
-- ★ THIS IS THE MATHEMATICAL CONTENT of gap B layer 2; everything left
--   after it is `natrec` plumbing.  Each leaf is stated at an ARBITRARY
--   context with the components as explicit terms — the `⊢strong-base'`
--   pattern, applied before the plumbing rather than after an OOM.
--
-- ⚠ NOTE WHERE THE IH IS AND IS NOT USED.  The two BASE leaves discharge
--   the spec outright; only the two RECURSIVE leaves consume the induction
--   hypothesis — and each consumes BOTH conjuncts.  That is the concrete
--   form of "the motive must be a conjunction".
------------------------------------------------------------------------

-- ★ 1.  b = 0 :  gcd (a , 0) = a.   Need `a ∣ a` and `a ∣ 0`.
gcdLeaf-b0 : {Γ : Ctx} {u : RTm ⌊ Γ ⌋} → Γ ⊢ u ∷ Nat →
             Prv Γ (El (QCode u nzero u))
gcdLeaf-b0 du = prv _ (⊢Q-intro ⊢nzero du (⊢dvd-refl du) (⊢dvd-zero du))

-- ★ 2.  a = 0, b = suc b' :  gcd (0 , b) = b.   `b ∣ 0` and `b ∣ b`.
gcdLeaf-a0 : {Γ : Ctx} {b' : RTm ⌊ Γ ⌋} → Γ ⊢ b' ∷ Nat →
             Prv Γ (El (QCode nzero (nsuc b') (nsuc b')))
gcdLeaf-a0 db =
  prv _ (⊢Q-intro (⊢nsuc db) (⊢nsuc db)
                  (⊢dvd-zero (⊢nsuc db)) (⊢dvd-refl (⊢nsuc db)))

-- ★★ 3.  a ≤ b  (`a ∸ b ≡ 0`) :  recurse at `(a , b ∸ a)`.
--    The IH gives `v ∣ a` and `v ∣ (b ∸ a)`; the first conjunct is
--    immediate, the second is `⊢dvd-plus` then `monusLe`.
gcdLeaf-le : {Γ : Ctx} {a b v h₁ h₂ e : RTm ⌊ Γ ⌋} →
             Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ v ∷ Nat →
             Γ ⊢ e ∷ IdN (monusTm a b) nzero →
             Γ ⊢ h₁ ∷ dvdT v a → Γ ⊢ h₂ ∷ dvdT v (monusTm b a) →
             Prv Γ (El (QCode a b v))
gcdLeaf-le {b = b} {v = v} da db dv de dh1 dh2 =
  prv _ (⊢Q-intro db dv dh1 dvb)
  where
    dsum = ⊢plus (⊢monus db da) da
    dvb  = ⊢dvd-cong dv dsum db
             (⊢symN db dsum (monusLe da db de))
             (⊢dvd-plus dv (⊢monus db da) da dh2 dh1)

-- ★★ 4.  a > b  (`a ∸ b ≡ suc p`) :  recurse at `(a ∸ b , b)`.
--    The IH gives `v ∣ (a ∸ b)` and `v ∣ b`; the SECOND conjunct is
--    immediate, the first is `⊢dvd-plus` then `monusPlus`.
gcdLeaf-gt : {Γ : Ctx} {a b v p h₁ h₂ e : RTm ⌊ Γ ⌋} →
             Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ v ∷ Nat → Γ ⊢ p ∷ Nat →
             Γ ⊢ e ∷ IdN (monusTm a b) (nsuc p) →
             Γ ⊢ h₁ ∷ dvdT v (monusTm a b) → Γ ⊢ h₂ ∷ dvdT v b →
             Prv Γ (El (QCode a b v))
gcdLeaf-gt {a = a} {v = v} da db dv dp de dh1 dh2 =
  prv _ (⊢Q-intro db dv dva dh2)
  where
    dsum  = ⊢plus (⊢monus da db) db
    dsum' = ⊢plus (⊢nsuc dp) db
    deq   = ⊢transN dsum dsum' da
              (⊢congPL db (⊢monus da db) (⊢nsuc dp) de)
              (⊢symN da dsum' (monusPlus da db dp de))
    dva   = ⊢dvd-cong dv dsum da deq
              (⊢dvd-plus dv (⊢monus da db) db dh1 dh2)

------------------------------------------------------------------------
-- ★★★★★ INTERNALISING `IndPW` — THE LINCHPIN, exactly as `pwIntro` is
--   for `StepExt` (`…GcdStepExt`).
--
-- ⚠ WHY IT IS NEEDED AND NOT AN OPTIMISATION.  The three splits put the
--   proof at `Θ ▹ PairT ▹ Hom … ▹ …`, and `IndPW` is a META-level
--   hypothesis available only at `Θ`.  Stated there it is CIRCULAR to use
--   inside a branch.  As a TERM of an object-language `Π`-type it can ride
--   the split motives as a Π-bound variable, so each branch receives its
--   own induction hypothesis at its own bound — which is exactly what
--   `⊢gcdStp`'s three motives already do with `gcdG (plusTm …)`.
--
-- ⭐ `IndPW` is renaming-indexed (the 2026-08-16 generalisation), so this
--   is a two-line instantiation at `ϑ = vs ∘ vs` rather than a rebuild.
------------------------------------------------------------------------

-- `vs` twice, fused.  ⚠ `renren`'s three renamings are all implicit and
--   none is determined by the argument, so it has to be pinned.
ww : {Γ : Cx} (t : RTm Γ) → w (w t) ≡ renTm (λ v → vs (vs v)) t
ww t = renren {ϑ = vs} {ρ = vs} {ρ' = λ v → vs (vs v)} (λ _ → refl) t

-- `(y : Pair) (q : μ y < μ a) → P (y , ih y q)`, INTERNALLY.
-- ⚠ indexed by a RAW `Cx`: it carries no typing information, and the split
--   motives need it at depths that are not `⌊ _ ⌋` of anything.
indPWT : {Γ : Cx} (μa ih : RTm Γ) → RTy Γ
indPWT μa ih =
  Π PairT
    (Π (Hom Nat (nsuc msr) (w μa))
       (El (QCode (fst (var (vs vz))) (snd (var (vs vz)))
                  (app (app (w (w ih)) (var (vs vz))) (var vz)))))

indPWIntro : {Δ Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} {a ih : RTm ⌊ Θ ⌋} →
             Θ ⊢ subTm (single a) msr ∷ Nat →
             IndPW Δ PairT ⌜Nat⌝ msr gcdP Θ ρ a ih →
             Prv Θ (indPWT (subTm (single a) msr) ih)
indPWIntro {a = a} {ih = ih} dμ pw =
  prv _ (⊢lam ⊢PairT
          (⊢lam (ty-Hom ty-Nat (⊢nsuc ⊢msr) (⊢wk dμ))
                (⊢-cast bodyEq (prvOk inner))))
  where
    μa = subTm (single a) msr

    inner = pw (wR (wR Ren⊢-id)) (λ v → refl) (var (vs vz)) (var vz)
               (⊢var (there here))
               (⊢-cast (cong (Hom Nat (nsuc (w msr))) (ww μa)) (⊢var here))

    -- ⚠ the result slot must be PINNED: `PAtR` is a defined function, so
    --   Agda unfolds instead of decomposing and the meta never solves.
    bodyEq = trans (cong El (PAtR-gcd (λ v → vs (vs v)) (var (vs vz))
                              (app (app (renTm (λ v → vs (vs v)) ih)
                                        (var (vs vz)))
                                   (var vz))))
                   (cong (λ t → El (QCode (fst (var (vs vz))) (snd (var (vs vz)))
                                          (app (app t (var (vs vz))) (var vz))))
                         (sym (ww ih)))

------------------------------------------------------------------------
-- ★★ …AND ITS TYPING.  Mirrors `⊢pwT` exactly; `appGcdIH` is the one peel
--   applying an `aIHTat`-typed handle needs.
------------------------------------------------------------------------

⊢indPWT : {Γ : Ctx} {μa ih : RTm ⌊ Γ ⌋} →
          Γ ⊢ μa ∷ Nat → Γ ⊢ ih ∷ gcdIH μa → Γ ⊢ty indPWT μa ih
⊢indPWT {μa = μa} dμ di =
  ty-Π ⊢PairT
    (ty-Π (ty-Hom ty-Nat (⊢nsuc ⊢msr) (⊢wk dμ))
          (ty-El (⊢QCode (⊢fst dy) (⊢snd dy) (asN dcall))))
  where
    dy    = ⊢var (there here)
    dcall = appGcdIH (⊢-cast (gcdIH-w² μa) (⊢wk (⊢wk di))) dy (⊢var here)

------------------------------------------------------------------------
-- ★★★★ `indG` — THE `P`-ANALOGUE OF `gcdG`, and the split motive.
--
--   gcdG μ      =  (ih : gcdIH μ) → Nat
--   eqG  μ f    =  (i₁ i₂ : gcdIH μ) → i₁ ≐ i₂ → f i₁ ≡ f i₂     (StepExt)
--   indG μ f u₁ u₂ =  (ih : gcdIH μ) → P-of-all-its-calls → P (u₁,u₂, f ih)
--
-- ★ THE IH AND THE HYPOTHESIS ARE Π-BOUND, exactly as in `eqG`, and for
--   the same reason: every branch then receives its own induction
--   hypothesis AT ITS OWN BOUND, so the recursive leaves' certificates
--   (`⊢CERTᶻ`/`⊢CERTˢ`, stated at `plusTm (nsuc k') (nsuc n')`) are
--   precisely what `⊢app` wants.  No transport, no order hypothesis.
--
-- ⚠ `u₁`/`u₂` — the pair's two COMPONENTS — are parameters, not projections
--   of a carrier.  `PairT = Σ' Nat Nat` has no η, so a split cannot replace
--   `a` by `pair (fst a) (snd a)`; generalising a COMPONENT in the motive
--   is well-formed where generalising the pair is not.
------------------------------------------------------------------------

gcdG-w² : {Γ : Cx} (μ : RTm Γ) →
          renTy vs (renTy vs (gcdG μ)) ≡ gcdG (w (w μ))
gcdG-w² μ = cong (λ T → Π T (El ⌜Nat⌝)) (gcdIH-w² μ)

indG : {Γ : Cx} (μx f u₁ u₂ : RTm Γ) → RTy Γ
indG μx f u₁ u₂ =
  Π (gcdIH μx)
    (Π (indPWT (w μx) (var vz))
       (El (QCode (w (w u₁)) (w (w u₂)) (app (w (w f)) (var (vs vz))))))

⊢indG : {Γ : Ctx} {μx f u₁ u₂ : RTm ⌊ Γ ⌋} →
        Γ ⊢ μx ∷ Nat → Γ ⊢ f ∷ gcdG μx →
        Γ ⊢ u₁ ∷ Nat → Γ ⊢ u₂ ∷ Nat → Γ ⊢ty indG μx f u₁ u₂
⊢indG {μx = μx} dμ df d1 d2 =
  ty-Π (⊢gcdIH dμ)
    (ty-Π (⊢indPWT (⊢wk dμ) (⊢-cast (gcdIH-w μx) (⊢var here)))
          (ty-El (⊢QCode (⊢wk (⊢wk d1)) (⊢wk (⊢wk d2)) (asN dfi))))
  where
    dfi = ⊢app (⊢-cast (gcdG-w² μx) (⊢wk (⊢wk df)))
               (⊢-cast (gcdIH-w² μx) (⊢var (there here)))

------------------------------------------------------------------------
-- ★★ SPLIT 1's MOTIVE — on `snd x`.  ctx: [0]=n' [1]=x
--
-- ⭐ THE BOUNDARIES ARE `refl`, and that is the whole reason this is
--   tractable: everything in `gcdStp` is built from VARIABLES, so every
--   `subTy`/`subTm` at a boundary COMPUTES.  `…GcdStepExt` records the same
--   for `eqG`; it holds for `indG` because `QCode`'s extra slots are
--   themselves variables or projections of one.
------------------------------------------------------------------------

MI₁ : {Γ : Cx} → RTy (Γ ∙ ∙)
MI₁ = indG μ₁ f₁ (fst (var (vs vz))) (var vz)

probeI₁-at : {Γ : Cx} →
             subTy (single (snd (var vz))) (MI₁ {Γ})
           ≡ indG msr gcdBody (fst (var vz)) (snd (var vz))
probeI₁-at = refl

probeI₁-z : {Γ : Cx} →
            subTy (single nzero) (MI₁ {Γ})
          ≡ indG (plusTm (fst (var vz)) nzero)
                 (natrec G1z gcdInn1 nzero)
                 (fst (var vz)) nzero
probeI₁-z = refl

------------------------------------------------------------------------
-- ★★★ THE BRIDGE BETWEEN SPLITS — a reduction of `f` is a CONVERSION of
--     `indG μ f u₁ u₂`.  The `eqG-red` analogue.
--
-- ⚠ WHY IT IS NEEDED.  Split n's successor branch must inhabit
--   `subTy nrs Mₙ`, whose function slot is `natrec … (nsuc k)`; split n+1
--   produces the same statement about that term's `natrec-suc` REDUCT.  The
--   two are related by one step, not equal, so the branch cannot be a cast.
--
-- ⭐ `indG` mentions `f` only in `QCode`'s VALUE slot under two `Π`s, and
--   `QCode-red` pushes a reduction all the way into the code — so this is
--   `⟶ᵀ*-Πʳ` twice over `QCode-red`, and stays ONE `⊢conv` per split.
------------------------------------------------------------------------

indG-red : {Γ : Cx} {μ u₁ u₂ f g : RTm Γ} → f ⟶* g →
           indG μ f u₁ u₂ ≅ᵀ indG μ g u₁ u₂
indG-red {u₁ = u₁} {u₂ = u₂} r =
  red→≅ᵀ (⟶ᵀ*-Πʳ (⟶ᵀ*-Πʳ
    (⟶ᵀ*-El (QCode-red (w (w u₁)) (w (w u₂))
                       (⟶*-appˡ (⟶*-ren vs (⟶*-ren vs r)))))))

------------------------------------------------------------------------
-- ★ LEAF 1 — `snd x = 0`, so `gcd (a , 0) = a`.  IH-FREE.
--
-- ⭐ `G1z`'s body is `fst <the carrier>`, and the carrier does not mention
--   the `ih` the `lam` just bound, so `β` lands on `fst x` on the nose —
--   which is exactly `gcdLeaf-b0`'s subject.
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
                (⊢conv (prvOk (gcdLeaf-b0 du))
                       (csymᵀ (QCode-conv _ nzero (redI₁z (var (vs vz))))))))
  where
    dμ = ⊢plus (⊢fst (⊢var here)) ⊢nzero
    du = ⊢fst (⊢var (there (there here)))

------------------------------------------------------------------------
-- ★★ SPLIT 2 — on `fst x`.  ctx: [0]=k' [1]=MI₁ [2]=n' [3]=x
--
-- ⭐ Splits 1 and 2 MEET in one `natrec-suc` step (`probe₁-s`), which is
--   `…GcdStepExt`'s lemma reused verbatim — it is about `gcdStp`'s own
--   `natrec`s, not about the motive.
------------------------------------------------------------------------

MI₂ : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙)
MI₂ = indG μ₂ f₂ (var vz) (nsuc (var (vs (vs vz))))

-- ⚠ MY OWN SPLIT CONTEXTS.  `…GcdStepExt`'s `Θ₂`/`Θ₃` carry ITS motives
--   (`M₁`/`M₂`, the `eqG` ones) in the slots the splits introduce.  Nothing
--   in either development LOOKS at those slots — every `there` steps over
--   them — but the `natrec` assembly does have to agree on them.
ΘI₂ : Ctx → Ctx
ΘI₂ Γ = ((Γ ▹ PairT) ▹ Nat) ▹ MI₁

ΘI₃ : Ctx → Ctx
ΘI₃ Γ = (ΘI₂ Γ ▹ Nat) ▹ MI₂

probeI₂-z : {Γ : Cx} →
            subTy (single nzero) (MI₂ {Γ})
          ≡ indG (plusTm nzero (nsuc (var (vs vz))))
                 (natrec G2z (subTm (extS (extS (single nzero)))
                                    (renTm (extR (extR vs)) gcdInn2)) nzero)
                 nzero (nsuc (var (vs vz)))
probeI₂-z = refl

------------------------------------------------------------------------
-- ★ LEAF 2 — `fst x = 0`, so `gcd (0 , b) = b`.  IH-FREE, same shape as
--   leaf 1: `G2z`'s body is `nsuc n'`, which does not mention the bound
--   `ih`, so `β` lands on it exactly.
------------------------------------------------------------------------

redI₂z : {Γ : Cx} (sb i : RTm (Γ ∙ ∙ ∙ ∙ ∙)) →
         app (w (w (natrec (G2z {Γ}) sb nzero))) i
       ⟶* nsuc (var (vs (vs (vs vz))))
redI₂z sb i = ⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done)) (step (β _ i) done)

leafI₂z : {Γ : Ctx} → Prv (ΘI₂ Γ) (subTy (single nzero) MI₂)
leafI₂z =
  prv _ (⊢lam (⊢gcdIH dμ)
          (⊢lam (⊢indPWT (⊢wk dμ) (⊢-cast (gcdIH-w _) (⊢var here)))
                (⊢conv (prvOk (gcdLeaf-a0 db))
                       (csymᵀ (QCode-conv nzero _ (redI₂z _ (var (vs vz))))))))
  where
    dμ = ⊢plus ⊢nzero (⊢nsuc (⊢var (there here)))
    db = ⊢var (there (there (there here)))

------------------------------------------------------------------------
-- ★★★ ELIMINATING THE INTERNAL HYPOTHESIS — the mirror of `pwElim`.
--
-- Two `⊢app`s and the peels they leave.  ⚠ The `w`s are the whole cost:
-- `indPWT` states its body at the two binders' depth, so every slot
-- arrives under one or two weakenings that `sub-w`/`wk-single` strip.
-- BOTH recursive leaves use this once.
------------------------------------------------------------------------

indPWElim : {Γ : Ctx} {μ i h y q : RTm ⌊ Γ ⌋} →
            Γ ⊢ h ∷ indPWT μ i → Γ ⊢ y ∷ PairT →
            Γ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) msr)) μ →
            Γ ⊢ app (app h y) q
              ∷ El (QCode (fst y) (snd y) (app (app i y) q))
indPWElim {μ = μ} {i = i} {y = y} {q = q} dh dy dq =
  ⊢-cast (cong El eq2) (⊢app (⊢-cast eq1 (⊢app dh dy)) dq)
  where
    -- one binder in: the handle loses one `w`, the bound loses its `w`
    peel₁ : (t : RTm ⌊ _ ⌋) → subTm (extS (single y)) (w (w t)) ≡ w t
    peel₁ t = trans (sub-w {σ = single y} (w t)) (cong w (wk-single {v = y} t))

    eq1 = cong₂ (λ u c → Π (Hom Nat (nsuc (subTm (single y) msr)) u) (El c))
                (wk-single {v = y} μ)
                (trans (QCode-sub {σ = extS (single y)}
                          (fst (var (vs vz))) (snd (var (vs vz)))
                          (app (app (w (w i)) (var (vs vz))) (var vz)))
                       (cong (λ z → QCode (fst (w y)) (snd (w y))
                                          (app (app z (w y)) (var vz)))
                             (peel₁ i)))

    eq2 = trans (QCode-sub {σ = single q}
                   (fst (w y)) (snd (w y)) (app (app (w i) (w y)) (var vz)))
                (cong₂ (λ z u → QCode (fst u) (snd u) (app (app z u) q))
                       (wk-single {v = q} i) (wk-single {v = q} y))

-- ★ `indPWT` past a weakening — the hypothesis reaches each leaf as a
--   Π-BOUND VARIABLE, and `here` hands it back under a `renTy vs`.
indPWT-w : {Γ : Cx} (μ i : RTm Γ) →
           renTy vs (indPWT μ i) ≡ indPWT (w μ) (w i)
indPWT-w μ i =
  cong₂ (λ u c → Π PairT (Π (Hom Nat (nsuc msr) u) (El c)))
        (ren-w μ)
        (trans (QCode-ren {ρ = extR (extR vs)}
                  (fst (var (vs vz))) (snd (var (vs vz)))
                  (app (app (w (w i)) (var (vs vz))) (var vz)))
               (cong (λ z → QCode (fst (var (vs vz))) (snd (var (vs vz)))
                                  (app (app z (var (vs vz))) (var vz)))
                     (wwr i)))
  where
    wwr : (t : RTm _) → renTm (extR (extR vs)) (w (w t)) ≡ w (w (w t))
    wwr t = trans (ren-w {ρ = extR vs} (w t)) (cong w (ren-w t))

------------------------------------------------------------------------
-- ★★★★★ SPLIT 3 — the COMPARISON, on `a ∸ b`.
--     ctx `Θ₃`: [0]=MI₂ [1]=k' [2]=MI₁ [3]=n' [4]=x,  so a = suc k',
--     b = suc n'.
--
-- ⚠⚠ THIS IS THE ONE PLACE THE TWO DEVELOPMENTS DIVERGE.  `…GcdStepExt`'s
--   `G3`/`M₃` motive is CONSTANT — `StepExt` needs to know only WHETHER
--   `a ∸ b` is zero, never its value.  Here the leaves need the EQUATION:
--   the `a ≤ b` leaf must feed `a ∸ b ≡ 0` to `monusLe`, and the `a > b`
--   leaf `a ∸ b ≡ suc p` to `monusPlus`.
--
-- ★ SO THE MOTIVE IS INDEXED BY ITS OWN SCRUTINEE — the `inspect`
--   encoding, available because `⊢natrec`'s motive is
--   `(Γ ▹ Nat) ⊢ty M` (GAP-B-LAYER2-PLAN §2).  At the elimination the
--   equation slot instantiates to `IdN (a ∸ b) (a ∸ b)`, discharged by
--   `reflN`; in each branch it arrives as the fact that branch was entered
--   FOR.
------------------------------------------------------------------------

uA₃ uB₃ μAB : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
uA₃ = nsuc (var (vs vz))
uB₃ = nsuc (var (vs (vs (vs vz))))
μAB = monusTm uA₃ uB₃

MI₃ : {Γ : Cx} → RTy (Γ ∙ ∙ ∙ ∙ ∙ ∙)
MI₃ = Π (IdN (w μAB) (var vz))
        (indG (w (w (plusTm uA₃ uB₃))) (w f₃) (w (w uA₃)) (w (w uB₃)))

-- ⭐ …and the boundary is `refl` HERE TOO, equation slot included.
probeI₃-at : {Γ : Cx} →
             subTy (single μAB) (MI₃ {Γ})
           ≡ Π (IdN μAB μAB)
               (indG (w (plusTm uA₃ uB₃)) (w (natrec G3z G3s μAB))
                     (w uA₃) (w uB₃))
probeI₃-at = refl
