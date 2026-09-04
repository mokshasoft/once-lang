------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `extR`, AND WITH IT THE OBJECT-LEVEL
-- **RENAMING** LAYER THE ENCODING NEVER BUILT.
--
--     Ren Γ Δ = Var Γ → Var Δ          Spec/Syntax:273   ← FIRST
--     renTm   : Ren Γ Δ → RTm Γ → RTm Δ            :281
--     Sub Γ Δ = Var Γ → RTm Δ                      :330   ← SECOND
--     extS σ (vs x) = renTm vs (σ x)               :335   ← uses renTm
--
-- ⚠⚠ **RENAMING IS PRIOR TO SUBSTITUTION**, and that is why the encoding
--   cannot express `renTm vs` as `subTm wkSub`: `Knot/WkSub` imports
--   `Knot/SubMot`, and `extS`'s own `vs` row needs `renTm vs`.  The cycle
--   is not a module-layout accident — it is the kernel's layering, and
--   the fix is to mirror it.  See `PLAN-RENAMING.md` §8.
--
-- ★★★ AND `extR` IS WHAT BREAKS THE CYCLE:
--
--     extR ρ vz     = vz
--     extR ρ (vs x) = vs (ρ x)
--
--   NO `renTm` ON THE RIGHT.  Extending a RENAMING under a binder is
--   pure `vz`/`vs` — which is exactly why the kernel can define renaming
--   before substitution, and why this module has no dependency on
--   `Knot/SubMot` at all.
--
-- ★★ TWO ROWS, AND ONE OF THEM IS THE JUNK ROW.  `extR ρ vz = vz` and
--   the do-nothing answer is also `vz` — a `Var` exists at every
--   successor depth — so `cVar-vz` reuses `constMethR` and only
--   `cVar-vs` is this module's own work.  ⇒ ONE real row, against
--   `Knot/SubMot`'s two.
--
-- ⚠ SHAPE: `Knot/SubMot`'s `ext…` section, with `sTm` → `sVar` in the
--   motive's codomain and the `vs` row's `wkK (pair sTm n) (app σ x)`
--   replaced by `Var-vsK n (app ρ x)`.  The ford transport is
--   character-for-character the same — `⊢fordPredN` then `⊢symN` then
--   one `⊢jsub`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenMot where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; pair; snd; Nat; Π; IMu
        ; ICon; IDesc; _◂_; inil; nsuc; nzero; unit; natrec; renTm; renTy; εwkTy
        ; app; fst; jsub; ⌜IMu⌝; ielim; Σ'; isingle; ipayTy; εwk-ren; ipayTy-ren; ipayTy-cong
        ; ⌜Id⌝; ⌜Nat⌝; idrefl; El; _∈ID_; ilookupD )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢pair; ⊢unit; ⊢icon; ⊢lam; ⊢nsuc; ⊢nzero; ⊢natrec; wk-single; ty-Nat; ty-Π; ty-IMu; ty-Unit
        ; IConWf; imethTy; imethsTyFrom; ty-Σ; βsnd; βfst; ξ-pairʳ; ξ-pairˡ; ξ-nsuc; single
        ; _⟶*_; done; step; natrec-suc; natrec-zero; csymᵀ; iinst; iihTy
        ; ⊢app; ⊢jsub; ⊢fst; ⊢conv; ⊢⌜IMu⌝; ⊢⌜Id⌝; ⊢⌜Nat⌝; ty-El; ⊢ielim; imethsTy
        ; IDescWfFrom; idwf-nil; idwf-cons )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy; w; sub-w; ren-w; sub-w-single; towerA; towerJ )
open import DirectedHoTT.Lib.IMeths using ( CDesc; cd-stop; cd-cons; cdRest; cdPos; cdTake; methsFrom-sub )
open import DirectedHoTT.Lib.IFold using ( eqℕ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )
import DirectedHoTT.Lib.ISub as IS
open import DirectedHoTT.Lib.IWk
  using ( Maybe; just; nothing )
open import DirectedHoTT.Lib.IPay
  using ( Split; spl-nil; spl-cons; spl-mem; spl-look; spl-step )
open import DirectedHoTT.Spec.Syntax using ( Sub; ipayTy; subTm; extS; extR )
open import DirectedHoTT.Lib.Monus using ( predTm; ⊢pred; pred-suc; pred-zero )
open import DirectedHoTT.Lib.ArithMonus using ( pred*; pred-snd-pair )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-natrecⁿ; ⟶*-natrecᶻ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-⌜Id⌝ˡ )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ; ⟶ᵀ*-IMu; ⟶ᵀ*-Πˡ; ⟶ᵀ*-El )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN; elIdN; ⊢reflN )
open import DirectedHoTT.Lib.IdSuc using ( predN; ⊢fordPredN )
open import DirectedHoTT.Lib.ICast
  using ( muFwd; muBwd*; fordAs; toMu; fromMu; ⟶*-castᵣ; ⟶*-castₗ )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkK )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢-cast; isingle-Sub⊢; iihTy-wf; ren-ty; ⊢wk; iihTy-ren; iihTy-cong )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf; ⊢methLam )
open import DirectedHoTT.Examples.Knot.Tags
  using ( memTm-nzero; memTm-var; memVar-vz; tagVar-vz; tagVar-vs; tagTm-var )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-nzeroK; Tm-varK )
open import DirectedHoTT.Examples.Knot.Terms using ( fordFst; fordSnd; tyFordFst; ixConv; SubTy )
open import DirectedHoTT.Examples.Knot.Build
  using ( Var-vzK; Var-vsK; ⊢Var-vzKv; ⊢Var-vzKt; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz )
open import DirectedHoTT.Examples.Knot.Desc using ( cVar-vz; cVar-vs; cTm-var )
open import DirectedHoTT.Examples.Knot.Wf using ( cVar-vzWf; cVar-vsWf; cTm-varWf )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sTm; sDesc; sDCon; sIDesc; sICon; sVar
        ; ⊢sTm; ⊢sVar; ⊢ixP; toI; fromI; num; ⊢num )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methsFrom; ⊢methsCons; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )

------------------------------------------------------------------------
-- Binder layout.  The motive is checked at
--     Θ = Γ ▹ εwkTy IPair ▹ K (var vz)
-- so `vz` is the SCRUTINEE and `vs vz` the ambient INDEX.  Under the
-- motive's own `Π Nat`:  n = vz · t = vs vz · i = vs (vs vz).
--
-- ⚠ THE SCRUTINEE NEVER APPEARS.  That is deliberate and it is what
--   makes `iatCon` compute later: instantiating the motive at a row
--   touches only the INDEX slot.

------------------------------------------------------------------------
-- ★ THE TYPE OF A RENAMING, object-level — `Knot/Terms.SubTy`'s twin
--   one level down: a `Var` in, a `Var` out.
------------------------------------------------------------------------

RenTy : {Γ : Cx} → RTm Γ → RTm Γ → RTy Γ
RenTy d n = Π (K (pair sVar d)) (K (pair sVar (renTm vs n)))

ty-RenTy : {Γ : Ctx} {d n : RTm ⌊ Γ ⌋} →
           Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ty RenTy d n
ty-RenTy dd dn = ty-Π (ty-IMu KnotWf (⊢ixP ⊢sVar dd))
                      (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢wk dn)))

------------------------------------------------------------------------
-- ★ THE MOTIVE.  `Knot/SubMot`'s `extMotK` with the answer at `sVar`.
------------------------------------------------------------------------

extRMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
extRMotK =
  Π Nat (Π (Π (IMu KnotD IPair (pair sVar (predTm (snd (var (vs (vs vz)))))))
              (IMu KnotD IPair (pair sVar (var (vs vz)))))
           (IMu KnotD IPair (pair sVar (nsuc (var (vs vz))))))

⊢extRMotK : {Γ : Ctx} →
            ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty extRMotK
⊢extRMotK =
  ty-Π ty-Nat
    (ty-Π (ty-Π (ty-IMu KnotWf
                   (⊢ixP ⊢sVar (⊢pred (⊢snd (⊢var (there (there here)))))))
                (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here)))))
          (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢nsuc (⊢var (there here))))))

------------------------------------------------------------------------
-- ★★★ THE DO-NOTHING METHOD — AND IT IS ALSO THE `vz` ROW.
--
-- The answer must inhabit `K (pair sVar (nsuc n))`, and `Var-vzK n` does
-- at every `n`.  `Knot/SubMot` needs `Tm-nzeroK` here and a SEPARATE
-- `extVz`; for a renaming the two coincide, because `extR ρ vz = vz`.
------------------------------------------------------------------------

constMethR : {Γ : Cx} → RTm Γ
constMethR = lam (lam (lam (lam (lam (Var-vzK (var (vs vz)))))))

⊢constMethR : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
              IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
              Γ ⊢ constMethR ∷ imethTy KnotD IPair k C extRMotK
⊢constMethR k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢extRMotK
    (⊢lam ty-Nat
      (⊢lam (ty-Π (ty-IMu KnotWf
                     (⊢ixP ⊢sVar (⊢pred (⊢snd (⊢var (there (there (there here))))))))
                  (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here)))))
        (⊢Var-vzKt (⊢var (there here)))))

------------------------------------------------------------------------
-- ★★★ `extR ρ (vs x) = vs (ρ x)` — THE ONE REAL ROW.
--
-- ⚠ The ford transport is `Knot/SubMot`'s `extVs`, character for
--   character: `⊢fordPredN` turns the DEPTH ford `snd ⟨i⟩ ≡ nsuc m` into
--   `predTm (snd ⟨i⟩) ≡ m`, `⊢symN` orients it, and one `⊢jsub` moves
--   `x` to where `ρ` can eat it.
------------------------------------------------------------------------

extRVs : {Γ : Cx} → RTm Γ
extRVs =
  lam (lam (lam (lam (lam
    (Var-vsK (var (vs vz))
             (app (var vz)
                  (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                        (symN (predTm (snd (var (vs (vs (vs (vs vz)))))))
                              (predN (snd (var (vs (vs (vs (vs vz))))))
                                     (fst (snd (snd (snd (var (vs (vs (vs vz))))))))))
                        (fst (snd (var (vs (vs (vs vz)))))))))))))

⊢extRVs : {Γ : Ctx} →
         Γ ⊢ extRVs ∷ imethTy KnotD IPair tagVar-vs cVar-vs extRMotK
⊢extRVs {Γ = Γ} =
  ⊢lam ⊢IPair
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) cVar-vs
                     KnotWf cVar-vsWf
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) cVar-vs}
                      KnotD IPair extRMotK (isingle (var (vs vz))) cVar-vs (var vz) cVar-vsWf
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢extRMotK
                      (⊢var here))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf
                         (⊢ixP ⊢sVar (⊢pred (⊢snd (⊢var (there (there (there here))))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here)))))
            -- ⚠ TWO β STEPS, INNERMOST FIRST: `sh i` projects `i` twice
            --   and both projections are redexes at `pair sTm n`.
            -- ★★★ `Var-vsK`, AND NOTHING ELSE.  `Knot/SubMot`'s row pays
            --   `wkK` plus two β-steps here because `extS`'s answer is a
            --   TERM one binder deeper; a renaming's answer is a `Var`,
            --   and `vs` IS the constructor for that.  ⇒ no weakening at
            --   all, which is the whole reason this module can exist
            --   below `Knot/SubMot` instead of above it.
            (⊢Var-vsKt (⊢var (there here)) (⊢app (⊢var here) tx))))))
  where
    -- the payload binder, and the two components the method needs
    dp = ⊢var (there (there (there here)))
    dm = elAsNat (⊢fst dp)
    dsi = ⊢pred (⊢snd (⊢var (there (there (there (there here))))))
    -- ★ THE FORD, INVERTED AND ORIENTED.
    deq = ⊢symN (⊢pred (⊢snd (⊢var (there (there (there (there here)))))))
                dm
                (⊢fordPredN (⊢snd (⊢var (there (there (there (there here))))))
                            dm
                            (fordAs (⊢fst (⊢snd (⊢snd (⊢snd dp))))))
    -- ⚠ `⊢jsub`'s ENDPOINTS live at `El ⌜Nat⌝` (that is `IdN`'s carrier)
    --   while `⊢pred`/`⊢symN`/`⊢fordPredN` all want `Nat`.  Both forms of
    --   the same two terms are needed; the conversion is free but the
    --   mismatch is invisible until `⊢jsub` is applied.
    tx = fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                       (natAsEl dm) (natAsEl dsi) deq
                       (toMu (⊢fst (⊢snd dp))))


------------------------------------------------------------------------
-- ★★★ THE TUPLE — 52 do-nothing rows, then `cVar-vs`.
--
-- ⚠ `Knot/SubMot` needs its own `constMethsFrom`/`imethsTyFromK-wf`
--   ladder because it predates `Lib/IPay.⊢methsFrom`; this module uses
--   the library, which is generic in the motive and takes the junk
--   method as a callback.  ⇒ the whole assembly is a dozen lines.
------------------------------------------------------------------------

RD52 : IDesc
RD52 = cdRest (cdTake 52 KnotD)

rspl52 : Split KnotD 52 RD52
rspl52 = splTake spl-nil (cdTake 52 KnotD)

extRTail : {Γ : Cx} → RTm Γ
extRTail = pair extRVs unit

⊢extRTail : {Γ : Ctx} →
            Γ ⊢ extRTail ∷ imethsTyFrom KnotD IPair extRMotK 52 RD52
⊢extRTail =
  ⊢methsCons KnotD IPair 52 {C = cVar-vs} inil KnotWf
             (idwfDrop (spl-step rspl52) KnotWf) (spl-step rspl52)
             ⊢IPair ⊢extRMotK ⊢extRVs ⊢unit

extRMethsK : {Γ : Cx} → RTm Γ
extRMethsK = methsFrom (cdTake 52 KnotD) constMethR extRTail

⊢extRMethsK : {Γ : Ctx} →
              Γ ⊢ extRMethsK ∷ imethsTy KnotD IPair extRMotK KnotD
⊢extRMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 52 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢extRMotK (λ {k} {C} wC _ _ → ⊢constMethR k C wC)
             extRTail ⊢extRTail

------------------------------------------------------------------------
-- ★ THE INDEX ARITHMETIC THE WRAPPER NEEDS.  ⚠⚠ MOVED DOWN FROM
--   `Knot/SubMot`, whose own comment said it should be: *"local only
--   because this is its first customer; a second one moves it down."*
--   This is the second customer, and it is BELOW `Knot/SubMot`, so the
--   move is forced rather than optional.
------------------------------------------------------------------------

predSndPair : {Γ : Cx} (d : RTm Γ) →
              predTm (snd (pair sVar (nsuc d))) ⟶* d
predSndPair d = pred-snd-pair sVar d

predSndSub : {Γ : Cx} (v D : RTm Γ) →
             subTm (single v) (predTm (snd (w (pair sVar (nsuc D))))) ⟶* D
predSndSub v D =
  ⟶*-castᵣ (wk-single {v = v} D)
           (predSndPair (subTm (single v) (w D)))

------------------------------------------------------------------------
-- ★★★ `extR` AS AN ELIMINATOR, THEN AS A RENAMING.
--
--     extRK i k  : ∀n. (Var (predTm (snd i)) → Var n) → Var (nsuc n)
--     extRNK d n ρ : RenTy (nsuc d) (nsuc n)
--
-- ⚠ `Knot/SubMot`'s `⊢extSK`/`⊢extNK`, with `sTm` → `sVar` throughout.
--   The two casts are the same two: the codomain differs by a RENAMING
--   (`ren-w`, an `≡`) and the domain by a REDUCTION (`predSndSub`,
--   lifted through `Π` by `⟶ᵀ*-Πˡ`).
------------------------------------------------------------------------

extRK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
extRK i k = ielim KnotD i extRMethsK k

⊢extRK : {Γ : Ctx} {i k : RTm ⌊ Γ ⌋} →
         Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ k ∷ K i →
         Γ ⊢ extRK i k ∷ Π Nat (Π (Π (K (pair sVar (predTm (snd (w i)))))
                                     (K (pair sVar (var (vs vz)))))
                                  (K (pair sVar (nsuc (var (vs vz))))))
⊢extRK {i = i} {k = k} di dk =
  ⊢-cast (cong (λ z → Π Nat (Π (Π (K (pair sVar (predTm (snd z))))
                                  (K (pair sVar (var (vs vz)))))
                               (K (pair sVar (nsuc (var (vs vz)))))))
               (trans (sub-w {σ = single k} (w i)) (cong w (wk-single {v = k} i))))
         (⊢ielim KnotWf ⊢extRMotK di ⊢extRMethsK dk)

extRNK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
extRNK d n ρ =
  lam (app (app (extRK (pair sVar (nsuc (w d))) (var vz)) (w n)) (w ρ))

⊢extRNK : {Γ : Ctx} {d n rn : RTm ⌊ Γ ⌋} →
          Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ rn ∷ RenTy d n →
          Γ ⊢ extRNK d n rn ∷ RenTy (nsuc d) (nsuc n)
⊢extRNK {d = d} {n = n} {rn = rn} dd dn drn =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢nsuc dd)))
    (⊢-cast (cong (λ z → K (pair sVar (nsuc z)))
                  (wk-single {v = renTm vs rn} (renTm vs n)))
      (⊢app (⊢app (⊢extRK (⊢ixP ⊢sVar (⊢nsuc (⊢wk dd))) (⊢var here))
                  (⊢wk dn))
            (⊢conv (⊢-cast (cong (λ z → Π (K (pair sVar (renTm vs d)))
                                          (K (pair sVar z)))
                                 (ren-w {ρ = vs} n))
                           (⊢wk drn))
                   (csymᵀ (red→≅ᵀ (⟶ᵀ*-Πˡ
                     (⟶ᵀ*-IMu (⟶*-pairʳ (predSndSub (renTm vs n) (renTm vs d))))))))))
