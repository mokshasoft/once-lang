------------------------------------------------------------------------
-- OCP-0009 · W1h — the INDEXED payload machinery for `fund`.
--
-- ★ WHY THIS IS A SEPARATE MODULE.  None of it is mutual with `fund`.
--   Everything here type-checks against the logical relation alone, so it
--   iterates in seconds rather than minutes.  The same split
--   `Fundamental/Syntactic` and `Fundamental/Semantic` already make, for
--   the same reason.
--
-- ★ WHAT IS IN IT.  Every definition is the exact mirror of a non-indexed
--   twin in `Fundamental` (`interpK`/`interpD`/`payInterp`/`liftPay`/
--   `payLiftK`/`payLiftD`/`liftPayAt`/`selSem`), with an ENVIRONMENT
--   threaded through: after PLAN-INDEXED §9.2 `ipayTy` walks a TELESCOPE,
--   so its semantics has to walk it in lockstep.

------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Fundamental.Indexed where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )

open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Σ'; Unit; Id; U
        ; RTm; fst; snd; sel; ⌜Id⌝; var
        ; renTy-renTy; renTy-subTy; subTy-subTy
        ; Ren; extR; renTy
        ; Sub; subTy; subTm; extS; renTm
        ; subTy-cong; subTy-renTy; subTy-id
        ; εwkTy; εwkTm; εwkTm-sub
        ; IMu; icon; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; ipayTy; ipayTy-cong; ipayTy-sub; ilookupD; _∈ID_; hereID; thereID
        ; iext; isingle; isingle-sub )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; iinst; iihTy; iatCon; iconS
        ; _⊢_∷_; _⟶ᵀ_; El-⌜Id⌝
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; ICodeWf; icw-clo; icw-ford
        ; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTyFrom )
open import DirectedHoTT.Metatheory.RedCong
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub )
open import DirectedHoTT.Metatheory.TySub
  using ( ipayTy-sub-single; iihTy-sub; iihTy-cong )
open import DirectedHoTT.Metatheory.LogicalRelation
  using ( SN
        ; ⊩₀_; _⊩₀∋_; ⊩₀Id
        ; ⊩₁_; _⊩₁∋_; ⊩₁Unit; ⊩₁Σ; ⊩₁IMu
        ; ILift; IMuMem
        ; IKInterp; iki-ι; iki-ρ; iki-κ
        ; IDInterp; idi-nil; idi-cons
        ; ikpredsOf; ipredsOf; ilookupP
        ; irrel₁; CR1₁; emb; emb-coh; wk-single
        ; projl; projr; dfst; dsnd )
open import DirectedHoTT.Spec.Typing using ( _≅ᵀ_; crflᵀ )

open import DirectedHoTT.Metatheory.Fundamental.Syntactic
open import DirectedHoTT.Metatheory.Fundamental.Semantic

private
  variable
    Θ Ξ : Cx
    Γ : Ctx

------------------------------------------------------------------------
-- 0. two casts and one substitution law.
------------------------------------------------------------------------

-- membership rides across a `⊩₁cast` — the equation is matched away.
⊩₁cast-mem : {A A' : RTy Ξ} (eq : A ≡ A') (R : ⊩₁ A) {t : RTm Ξ} →
             R ⊩₁∋ t → (⊩₁cast eq R) ⊩₁∋ t
⊩₁cast-mem refl R h = h

-- ★ the payload type at the STARTING environment is natural.  `⊢icon`
--   types its payload at `isingle i`; `fund` needs it at `isingle (σ i)`.
ipayTy-sub-isingle : (τ : Sub Ξ Θ) (D : IDesc) (I : RTy ε) (i : RTm Ξ)
                     (C : ICon (ε ∙)) →
                     subTy τ (ipayTy D I (isingle i) C)
                       ≡ ipayTy D I (isingle (subTm τ i)) C
ipayTy-sub-isingle τ D I i C =
  trans (ipayTy-sub τ D I (isingle i) C)
        (ipayTy-cong D I C (isingle-sub τ i))

-- ★★ the TWO-SLOT twin of `sub-single-Ty`: `⊢ielim`'s result type is
--   `iinst i t M`, and `fund-ty` on the motive delivers `M` under a
--   CONS-substitution of both slots.  ⚠ Its `inner` is `nrs-cons-Tm`'s
--   `inner` at the TYPE level — the same "extS absorbs extS" bridge, and
--   the same reason it is needed: two nested singles ARE one cons.
iinst-cons-Ty : (σ : Sub Θ Ξ) (j u : RTm Ξ) (M : RTy ((Θ ∙) ∙)) →
                iinst j u (subTy (extS (extS σ)) M)
                  ≡ subTy ((σ ,ₛ j) ,ₛ u) M
iinst-cons-Ty {Θ = Θ} σ j u M =
  trans (cong (subTy (single u)) inner) (sub-single-Ty (σ ,ₛ j) u M)
  where
    bridge : (x : Var ((Θ ∙) ∙)) →
             subTm (extS (single j)) (extS (extS σ) x) ≡ extS (σ ,ₛ j) x
    bridge vz     = refl
    bridge (vs y) =
      trans (wk-sub (single j) (extS σ y))
            (cong (renTm vs) (single-exts σ j y))

    inner : subTy (extS (single j)) (subTy (extS (extS σ)) M)
              ≡ subTy (extS (σ ,ₛ j)) M
    inner = trans (subTy-subTy M) (subTy-cong bridge M)

-- ★ `⊩ˢ-ext` landing at `iext` rather than `_,ₛ_`.  The two agree
--   POINTWISE but not as FUNCTIONS, and the telescope is walked with
--   `iext` throughout (`ipayTy`, `iihs`, `ILift`) — so the bridge is
--   crossed once, here, instead of at every call site.
⊩ˢ-iext : {Δ : Ctx} {B : RTy ⌊ Δ ⌋} {τ : Sub ⌊ Δ ⌋ Ξ} →
          Δ ⊩ˢ τ → (R : ⊩₁ (subTy τ B)) (v : RTm Ξ) → R ⊩₁∋ v →
          (Δ ▹ B) ⊩ˢ (iext τ v)
⊩ˢ-iext {Δ = Δ} {τ = τ} hτ R v hv {x = x} {A = A'} d =
  relCast (subTy-cong pt A') (pt x) (⊩ˢ-ext hτ R v hv d)
  where
    pt : (y : Var (⌊ Δ ⌋ ∙)) → (τ ,ₛ v) y ≡ iext τ v y
    pt vz     = refl
    pt (vs y) = refl

-- ⚠ `iκW`, `interpIK` and `interpID` live in `Fundamental` ITSELF, not
--   here: `iκW` calls `elW`, so it is MUTUAL with `fund`, and the
--   termination argument needs the `ICodeWf` to be a visible structural
--   subterm of the `IDescWf` the clause matched.  Everything BELOW is
--   independent of `fund` and stays here.

------------------------------------------------------------------------
-- 2. the payload type's CANONICAL interpretation, and the two directions
--    between it and `ILift`.
--
-- ⚠ THE FAMILY IS NOT CONSTANT here, unlike `payInterp`'s.  `payTy`'s
--   tail is WEAKENED past the field binder, so the non-indexed Σ-chain is
--   really a product; `ipayTy`'s tail is `ipayTy D I (extS σ) C`, which
--   genuinely depends on the field's VALUE.  `ipayTy-sub-single` is what
--   turns "the tail at `single u`" into "the tail at `iext σ u`", and
--   §10 is what makes the κ slot's interp available at `iext σ u` at all.
------------------------------------------------------------------------

ipayInterp : (D : IDesc) (I : RTy ε) (di : IDInterp Ξ D)
             {C : ICon Θ} (ki : IKInterp Ξ C) (σ : Sub Θ Ξ) →
             ⊩₁ (ipayTy D I σ C)
ipayInterp D I di iki-ι σ = ⊩₁Unit doneᵀ
ipayInterp D I di (iki-ρ {C = C} ki) σ =
  ⊩₁Σ doneᵀ (⊩₁IMu doneᵀ di)
      (λ u r → ⊩₁cast (sym (ipayTy-sub-single D I σ u C))
                      (ipayInterp D I di ki (iext σ u)))
ipayInterp D I di (iki-κ {C = C} w ki) σ =
  ⊩₁Σ doneᵀ (emb (w σ))
      (λ u r → ⊩₁cast (sym (ipayTy-sub-single D I σ u C))
                      (ipayInterp D I di ki (iext σ u)))

-- ILift → membership in the canonical interp.  (`liftPay`'s twin.)
iliftPay : (D : IDesc) (I : RTy ε) (di : IDInterp Ξ D)
           {C : ICon Θ} (ki : IKInterp Ξ C) (σ : Sub Θ Ξ) (p : RTm Ξ) →
           ILift C (ikpredsOf ki) (IMuMem D I (ipredsOf di)) σ p →
           (ipayInterp D I di ki σ) ⊩₁∋ p
iliftPay D I di iki-ι σ p l = l
iliftPay D I di (iki-ρ {C = C} ki) σ p (sp , (hf , rest)) =
  ( sp
  , ( hf
    , ⊩₁cast-mem (sym (ipayTy-sub-single D I σ (fst p) C))
                 (ipayInterp D I di ki (iext σ (fst p)))
                 (iliftPay D I di ki (iext σ (fst p)) (snd p) rest) ) )
iliftPay D I di (iki-κ {C = C} w ki) σ p (sp , (q , rest)) =
  ( sp
  , ( projl (emb-coh (w σ)) (fst p) q
    , ⊩₁cast-mem (sym (ipayTy-sub-single D I σ (fst p) C))
                 (ipayInterp D I di ki (iext σ (fst p)))
                 (iliftPay D I di ki (iext σ (fst p)) (snd p) rest) ) )

-- membership in ANY interp of the payload type → ILift.  (`payLiftK`.)
ipayLiftK : (D : IDesc) (I : RTy ε) (di : IDInterp Ξ D)
            {C : ICon Θ} (ki : IKInterp Ξ C) (σ : Sub Θ Ξ)
            (R : ⊩₁ (ipayTy D I σ C)) (p : RTm Ξ) → R ⊩₁∋ p →
            ILift C (ikpredsOf ki) (IMuMem D I (ipredsOf di)) σ p
ipayLiftK D I di iki-ι σ R p h = CR1₁ R h
ipayLiftK D I di (iki-ρ {C = C} ki) σ R p h =
  ( CR1₁ R h
  , ( projl (irrel₁ crflᵀ (dfst m₁) (⊩₁IMu doneᵀ di)) (fst p) (dsnd m₁)
    , ipayLiftK D I di ki (iext σ (fst p)) (dfst m₂) (snd p) (dsnd m₂) ) )
  where
    m₁ = ⊩₁-fstm R h
    m₂ = relTy (ipayTy-sub-single D I σ (fst p) C) (⊩₁-sndm R h)
ipayLiftK D I di (iki-κ {C = C} w ki) σ R p h =
  ( CR1₁ R h
  , ( projr (emb-coh (w σ)) (fst p)
            (projl (irrel₁ crflᵀ (dfst m₁) (emb (w σ))) (fst p) (dsnd m₁))
    , ipayLiftK D I di ki (iext σ (fst p)) (dfst m₂) (snd p) (dsnd m₂) ) )
  where
    m₁ = ⊩₁-fstm R h
    m₂ = relTy (ipayTy-sub-single D I σ (fst p) C) (⊩₁-sndm R h)

-- ⚠ the suffix-walking forms, for the same reason `payLiftD`/`liftPayAt`
--   have them: at a VARIABLE description the lookup is stuck, so the
--   `IDInterp` must be walked rather than indexed into.
ipayLiftD : (D : IDesc) (I : RTy ε) (di : IDInterp Ξ D)
            {E : IDesc} (dj : IDInterp Ξ E) (i : RTm Ξ) (k : ℕ)
            (R : ⊩₁ (ipayTy D I (isingle i) (ilookupD E k))) (p : RTm Ξ) →
            R ⊩₁∋ p →
            ILift (ilookupD E k) (ilookupP (ipredsOf dj) k)
                  (IMuMem D I (ipredsOf di)) (isingle i) p
ipayLiftD D I di idi-nil          i k       R p h = CR1₁ R h
ipayLiftD D I di (idi-cons ki dj) i zero    R p h =
  ipayLiftK D I di ki (isingle i) R p h
ipayLiftD D I di (idi-cons ki dj) i (suc k) R p h =
  ipayLiftD D I di dj i k R p h

iliftPayAt : (D : IDesc) (I : RTy ε) (di : IDInterp Ξ D)
             {E : IDesc} (dj : IDInterp Ξ E) (i : RTm Ξ) (k : ℕ)
             (p : RTm Ξ) →
             ILift (ilookupD E k) (ilookupP (ipredsOf dj) k)
                   (IMuMem D I (ipredsOf di)) (isingle i) p →
             Rel (ipayTy D I (isingle i) (ilookupD E k)) p
iliftPayAt D I di idi-nil          i k       p l = (⊩₁Unit doneᵀ , l)
iliftPayAt D I di (idi-cons ki dj) i zero    p l =
  ( ipayInterp D I di ki (isingle i)
  , iliftPay D I di ki (isingle i) p l )
iliftPayAt D I di (idi-cons ki dj) i (suc k) p l =
  iliftPayAt D I di dj i k p l

------------------------------------------------------------------------
-- 3. `sel k` extracts method `k` AT ITS OWN TAG, semantically.
--
-- The exact mirror of `selSem`, arithmetic included.  ⚠ NO INDEX
-- PARAMETER — after PLAN-INDEXED §9.1 a method's type mentions no
-- particular index, which is what lets ONE tuple serve every recursive
-- field.  The `k ∈ID E` premise is again what kills the `inil` case.
------------------------------------------------------------------------

iselSem : (D : IDesc) (I : RTy ε) (MI : RTy ((Ξ ∙) ∙)) (E : IDesc)
          (j k : ℕ) (ms : RTm Ξ) → k ∈ID E →
          (R : ⊩₁ (imethsTyFrom D I MI j E)) → R ⊩₁∋ ms →
          Rel (imethTy D I (j + k) (ilookupD E k) MI) (sel k ms)
iselSem D I MI (C ◂ E) j zero ms hereID R h =
  relTy (cong (λ n → imethTy D I n C MI) (sym (+zero j))) (⊩₁-fstm R h)
  where
    +zero : (n : ℕ) → (n + zero) ≡ n
    +zero zero    = refl
    +zero (suc n) = cong suc (+zero n)
iselSem {Ξ = Ξ} D I MI (C ◂ E) j (suc k) ms (thereID i) R h =
  relTy (cong (λ n → imethTy D I n (ilookupD E k) MI) (sym (+-suc j k)))
        (iselSem D I MI E (suc j) k (snd ms) i (dfst m₂) (dsnd m₂))
  where
    +-suc : (n o : ℕ) → (n + suc o) ≡ suc (n + o)
    +-suc zero    o = refl
    +-suc (suc n) o = cong suc (+-suc n o)

    wk-sub-single : (A : RTy Ξ) (u : RTm Ξ) →
                    subTy (single u) (renTy vs A) ≡ A
    wk-sub-single A u =
      trans (subTy-renTy A) (trans (subTy-cong (λ x → refl) A) (subTy-id A))

    m₂ = relTy (wk-sub-single (imethsTyFrom D I MI (suc j) E) (fst ms))
               (⊩₁-sndm R h)

------------------------------------------------------------------------
-- 4. ★★★ THE METHOD'S TYPE, INSTANTIATED — three peeling lemmas.
--
-- After PLAN-INDEXED §9.1 a method has THREE binders — index, payload, IH
-- tuple — so applying one walks three `subTy (single _)`s through
-- `imethTy`.  Each lemma below says what ONE of its four components
-- becomes.  ⚠ Stated with the substituted terms ABSTRACT (`j`, `p`,
-- `ih`): a substitution lemma's cost is its DEPTH, not its content.
------------------------------------------------------------------------

-- (a) the PAYLOAD domain — `ipayTy` at the actual index.  A special case
--     of `ipayTy-sub-isingle`; named for symmetry with (b) and (c).
imeth-pay : (D : IDesc) (I : RTy ε) (C : ICon (ε ∙)) (j : RTm Ξ) →
            subTy (single j) (ipayTy D I (isingle (var vz)) C)
              ≡ ipayTy D I (isingle j) C
imeth-pay D I C j = ipayTy-sub-isingle (single j) D I (var vz) C

-- (b') the MOTIVE survives both instantiations: `imethTy` pushes `M` past
--      the index binder and again past the payload binder, and
--      `single j` / `single p` undo exactly those two.
imeth-mot : (j p : RTm Ξ) (MI : RTy ((Ξ ∙) ∙)) →
            subTy (extS (extS (single p)))
              (subTy (extS (extS (extS (single j))))
                (renTy (extR (extR vs)) (renTy (extR (extR vs)) MI)))
              ≡ MI
imeth-mot j p MI =
  trans (cong (subTy (extS (extS (single p))))
              (trans (cong (subTy (extS (extS (extS (single j)))))
                           (renTy-renTy MI))
                     (subTy-renTy MI)))
        (trans (subTy-subTy MI)
               (trans (subTy-cong (λ { vz → refl ; (vs vz) → refl
                                     ; (vs (vs y)) → refl }) MI)
                      (subTy-id MI)))

-- (b) the IH-TUPLE domain.
imeth-ih : (D : IDesc) (I : RTy ε) (C : ICon (ε ∙)) (j p : RTm Ξ)
           (MI : RTy ((Ξ ∙) ∙)) →
           subTy (single p)
             (subTy (extS (single j))
               (iihTy D I (isingle (var (vs vz))) C (var vz)
                      (renTy (extR (extR vs)) (renTy (extR (extR vs)) MI))))
             ≡ iihTy D I (isingle j) C p MI
imeth-ih D I C j p MI =
  trans (cong (subTy (single p))
              (trans (iihTy-sub (extS (single j)) D I
                                (isingle (var (vs vz))) C (var vz) _)
                     (iihTy-cong D I C (var vz) _ (λ { vz → refl }))))
        (trans (iihTy-sub (single p) D I (isingle (renTm vs j)) C (var vz) _)
               (trans (iihTy-cong D I C p _ (λ { vz → wk-single j }))
                      (cong (iihTy D I (isingle j) C p) (imeth-mot j p MI))))

-- (c) the CODOMAIN — THE LANDING.  Instantiating the re-based motive at
--     the index, the payload and the IH tuple IS the two-slot motive at
--     this constructor: `iatCon-inst`'s twin, one binder deeper.
imeth-land : (k : ℕ) (j p ih : RTm Ξ) (MI : RTy ((Ξ ∙) ∙)) →
             subTy (single ih)
               (subTy (extS (single p))
                 (subTy (extS (extS (single j)))
                   (renTy vs (iatCon k (var vz)
                                     (renTy (extR (extR vs)) MI)))))
               ≡ iinst j (icon k p) MI
imeth-land k j p ih MI =
  trans (cong (subTy (single ih))
              (cong (subTy (extS (single p)))
                    (cong (subTy (extS (extS (single j))))
                          (trans (cong (renTy vs) (subTy-renTy MI))
                                 (renTy-subTy MI)))))
        (trans (cong (subTy (single ih))
                     (cong (subTy (extS (single p))) (subTy-subTy MI)))
               (trans (cong (subTy (single ih)) (subTy-subTy MI))
                      (trans (subTy-subTy MI)
                             (trans (subTy-cong pt MI)
                                    (sym (subTy-subTy MI))))))
  where
    pt : (x : Var ((_ ∙) ∙)) →
         subTm (single ih)
               (subTm (extS (single p))
                      (subTm (extS (extS (single j)))
                             (renTm vs (iconS k (var vz)
                                              (extR (extR vs) x)))))
           ≡ subTm (single (icon k p)) (extS (single j) x)
    pt vz          = cong (icon k) (wk-single p)
    pt (vs vz)     =
      trans (cong (subTm (single ih))
                  (trans (wk-sub (single p) (renTm vs j))
                         (cong (renTm vs) (wk-single j))))
            (trans (wk-single j) (sym (wk-single j)))
    pt (vs (vs y)) = refl
