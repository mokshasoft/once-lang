------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `renTm ρ`, OBJECT-LEVEL — AND IT IS
-- `Lib/ISub` AT `smap = id`.
--
-- ⚠⚠ THE POINT OF THE MODULE IS THAT `ρ` IS AN ARGUMENT.  `Knot/Wk.wkK`
--   is a weakening with its renaming INLINED into `Lib/IWk`'s fold, and
--   that is the whole of `PLAN-RENAMING.md`: a parameter that decides
--   the answer and does not appear in the interface is where a silent
--   disagreement lives.  Here it appears.
--
-- ★★★ AND SUBSTITUTION'S LIBRARY TAKES A RENAMING WITHOUT CHANGE.
--   `Lib/ISub.Sub` is parameterised by `extN`/`smap`/`decStable`/
--   `fordMap` and its `Typing` by the substitution's TYPE and the
--   motive.  A renaming is that library at
--
--       extN      = extRNK        (Knot/RenMot, and it needs no renTm)
--       smap      = λ s → s       renaming PRESERVES the sort
--       decStable = λ _ → just done
--       fordMap   = the witness, COPIED
--
--   ⇒ everything `Knot/SubMot` pays for `sortMap` collapses: six
--     reduction chains, a decision procedure over them, and a `jsub`
--     ford action all become `done`, `just done` and the identity.
--     THAT is what "substitution maps `sVar ↦ sTm` and renaming does
--     not" costs, measured.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenTm where
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
open import DirectedHoTT.Lib.IMeths using ( CDesc; cd-stop; cd-cons; cdRest; cdPos; cdTake )
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
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶*-trans; ⟶*-natrecⁿ; ⟶*-natrecᶻ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-⌜Id⌝ˡ )
open import DirectedHoTT.Metatheory.Injectivity
  using ( red→≅ᵀ; ⟶ᵀ*-IMu; ⟶ᵀ*-Πˡ; ⟶ᵀ*-El )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN; elIdN; ⊢reflN )
open import DirectedHoTT.Lib.IdSuc using ( predN; ⊢fordPredN )
open import DirectedHoTT.Lib.ICast
  using ( muFwd; muBwd*; fordAs; toMu; fromMu; ⟶*-castᵣ; ⟶*-castₗ )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkK )
open import DirectedHoTT.Metatheory.SubjectReduction
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
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-varKv )
open import DirectedHoTT.Examples.Knot.RenMot
  using ( RenTy; ty-RenTy; extRNK; ⊢extRNK )
open import DirectedHoTT.Lib.Wk using ( towerA; towerJ )

------------------------------------------------------------------------
-- ★ THE MOTIVE.  `Knot/SubMot`'s `subMotK` with `sortMap` deleted and
--   the passenger's codomain at `sVar`.
------------------------------------------------------------------------

renMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
renMotK =
  Π Nat (Π (Π (IMu KnotD IPair (pair sVar (snd (var (vs (vs vz))))))
              (IMu KnotD IPair (pair sVar (var (vs vz)))))
           (IMu KnotD IPair (pair (fst (var (vs (vs (vs vz))))) (var (vs vz)))))

⊢renMotK : {Γ : Ctx} →
           ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty renMotK
⊢renMotK =
  ty-Π ty-Nat
    (ty-Π (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢snd (⊢var (there (there here))))))
                (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here)))))
          (ty-IMu KnotWf
             (⊢ixP (⊢fst (⊢var (there (there (there here)))))
                   (⊢var (there here)))))

------------------------------------------------------------------------
-- ★★★ THE FOUR PARAMETERS `Lib/ISub.Sub` WANTS — and three of them are
--   TRIVIAL, which is exactly the content of `smap = id`.
------------------------------------------------------------------------

renSmap : {Γ : Cx} → RTm Γ → RTm Γ
renSmap s = s

renDecStable : (k : ℕ) → Maybe ({Δ : Cx} → renSmap {Δ} (num k) ⟶* num k)
renDecStable k = just done

-- ⚠ THE WITNESS IS COPIED, and `Lib/IWk`'s `⊢kaComp` is why that is
--   sound: the two ford types are CONVERTIBLE when the sort is not
--   moved.  `Knot/SubMot` needs a `jsub` here precisely because
--   `sortMap (fst ⟨i⟩)` does not reduce to `fst ⟨i⟩`.
renFordMap : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
renFordMap fi b p = p

⊢renFordMap : {Γ : Ctx} {fi t : RTm ⌊ Γ ⌋} (k : ℕ) →
              ({Δ : Cx} → renSmap {Δ} (num k) ⟶* num k) →
              Γ ⊢ fi ∷ Nat → Γ ⊢ t ∷ El (⌜Id⌝ ⌜Nat⌝ fi (num k)) →
              Γ ⊢ renFordMap fi (num k) t ∷ El (⌜Id⌝ ⌜Nat⌝ (renSmap fi) (num k))
⊢renFordMap k st dfi dt = dt

open IS.Sub extRNK renSmap renDecStable renFordMap

------------------------------------------------------------------------
-- ★ APPLYING THE MOTIVE'S TWO PASSENGERS — `Knot/SubApp`'s `⊢motAppK`
--   with the sort left alone.  Fourth `…AppK` of the session.
------------------------------------------------------------------------

⊢renAppK : {Γ : Ctx} {s dd u h m rn : RTm ⌊ Γ ⌋} →
           Γ ⊢ h ∷ iinst (pair s dd) u renMotK → Γ ⊢ m ∷ Nat →
           Γ ⊢ rn ∷ RenTy dd m →
           Γ ⊢ app (app h m) rn ∷ IMu KnotD IPair (pair (renSmap s) m)
⊢renAppK {s = s} {dd = dd} {u = u} {m = m} {rn = rn} dh dm drn =
  ⊢conv (⊢-cast (cong₂ (λ a b → K (pair (fst a) b))
                       (towerJ rn m u (pair s dd)) (wk-single {v = rn} m))
                (⊢app (⊢app dh dm)
                  (⊢conv drn
                    (csymᵀ (red→≅ᵀ (⟶ᵀ*-Πˡ (⟶ᵀ*-IMu
                      (⟶*-pairʳ (⟶*-castₗ (cong snd (towerA m u (pair s dd)))
                                          (step (βsnd s dd) done))))))))))
        (red→≅ᵀ (⟶ᵀ*-IMu (⟶*-pairˡ (step (βfst s dd) done))))

open Typing KnotD IPair RenTy renMotK ⊢extRNK ⊢renAppK ⊢renFordMap

------------------------------------------------------------------------
-- ★★★ THE THREE GIVEN ROWS — the same three as `Knot/SubMot` (`cTm-var`,
--   `cVar-vz`, `cVar-vs`: the rows with an `sVar` field), and each is
--   its substitution twin with `sortMap` deleted.
--
-- ⚠⚠ AND THE `Var` ROWS PRODUCE A **VAR**, NOT A TERM.  `Knot/SubMot`'s
--   header notes that at sort `sVar` its motive's target is
--   `K (pair (sortMap (fst ⟨i⟩)) n)` and `sortMap sVar ⟶* sTm`, so its
--   `Var` methods build a TERM — which is what substituting a variable
--   does.  A RENAMING sends a variable to a VARIABLE, so here the target
--   really is `K (pair sVar n)` and `app ρ x` inhabits it directly.
--   ⇒ the one place the two functions genuinely differ in KIND, and the
--     motive is where it shows.
------------------------------------------------------------------------

-- ★ `sortConv` with the sort map gone.  ⚠ Its `s'`/`sortMap s ⟶* s'`
--   parameters DISAPPEAR: they exist so `Knot/SubMot`'s `Var` rows can
--   build at `sTm` while their ford names `sVar`, and with `smap = id`
--   there is no gap to bridge.
renConv : {Γ : Ctx} {fi s n t p : RTm ⌊ Γ ⌋} →
          Γ ⊢ fi ∷ Nat → Γ ⊢ s ∷ Nat → Γ ⊢ n ∷ Nat →
          Γ ⊢ p ∷ IdN fi s →
          Γ ⊢ t ∷ K (pair s n) →
          Γ ⊢ jsub (⌜IMu⌝ KnotD IPair (pair (var vz) (w n))) (symN fi p) t
            ∷ K (pair fi n)
renConv {fi = fi} {s = s} {n = n} dfi ds dn dp dt =
  ⊢-cast (cong (λ z → K (pair fi z)) (wk-single {v = fi} n))
   (fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP (elAsNat (⊢var here)) (⊢wk dn)))
                (natAsEl ds) (natAsEl dfi)
                (⊢symN dfi ds dp)
                (toMu (⊢-cast (cong (λ z → K (pair s z))
                                    (sym (wk-single {v = s} n)))
                              dt))))

-- ★ the depth-ford transport, unchanged — it is stated at `sVar` and a
--   renaming never leaves it.
renVarAt : {Γ : Ctx} {di m t p : RTm ⌊ Γ ⌋} →
           Γ ⊢ di ∷ Nat → Γ ⊢ m ∷ Nat →
           Γ ⊢ p ∷ IdN di (nsuc m) →
           Γ ⊢ t ∷ K (pair sVar (nsuc m)) →
           Γ ⊢ jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz))) (symN di p) t
             ∷ K (pair sVar di)
renVarAt ddi dm dp dt =
  fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                (natAsEl (⊢nsuc dm)) (natAsEl ddi)
                (⊢symN ddi (⊢nsuc dm) dp)
                (toMu dt))

------------------------------------------------------------------------
-- ★★★ ROW 11 — `renTm ρ (var x) = var (ρ x)`.
--
-- ⚠ ONE `Tm-varK` MORE THAN `subVarM`, AND THAT IS THE WHOLE DIFFERENCE.
--   `σ x` is already a term; `ρ x` is a variable and must be injected.
------------------------------------------------------------------------

renVarM : {Γ : Cx} → RTm Γ
renVarM =
  lam (lam (lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair (pair (var vz) (var (vs (vs vz)))))
          (symN (fst (var (vs (vs (vs (vs vz))))))
                (fst (snd (var (vs (vs (vs vz)))))))
          (Tm-varK (app (var vz) (fst (var (vs (vs (vs vz)))))))))))) 

⊢renVarM : {Γ : Ctx} →
           Γ ⊢ renVarM ∷ imethTy KnotD IPair tagTm-var cTm-var renMotK
⊢renVarM {Γ = Γ} =
  ⊢methLam KnotD IPair tagTm-var cTm-var KnotWf cTm-varWf ⊢IPair ⊢renMotK
    (⊢lam ty-Nat
      (⊢lam (ty-Π (ty-IMu KnotWf
                     (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                  (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here)))))
        (renConv (⊢fst (⊢var (there (there (there (there here))))))
                 ⊢sTm
                 (⊢var (there here))
                 (fordAs (⊢fst (⊢snd (⊢var (there (there (there here)))))))
                 (⊢Tm-varKv _ (⊢var (there here))
                            (⊢app (⊢var here)
                                  (⊢fst (⊢var (there (there (there here)))))))))) 

------------------------------------------------------------------------
-- ★★★ ROWS 51 AND 52 — `ρ` applied to the rebuilt variable.
--
-- ⚠ TWO TRANSPORTS EACH, exactly as in `Knot/SubMot`: the DEPTH ford
--   (`snd ⟨i⟩ ≡ nsuc m`, closed by `renVarAt`) to hand `ρ` a variable at
--   the ambient depth, and the SORT ford (`fst ⟨i⟩ ≡ sVar`, closed by
--   `renConv`) to read the answer at `fst ⟨i⟩`.
------------------------------------------------------------------------

renVzM : {Γ : Cx} → RTm Γ
renVzM =
  lam (lam (lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair (pair (var vz) (var (vs (vs vz)))))
          (symN (fst (var (vs (vs (vs (vs vz))))))
                (fst (snd (var (vs (vs (vs vz)))))))
          (app (var vz)
               (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                     (symN (snd (var (vs (vs (vs (vs vz)))))) (fst (snd (snd (var (vs (vs (vs vz))))))))
                     (Var-vzK (fst (var (vs (vs (vs vz)))))))))))))

⊢renVzM : {Γ : Ctx} →
          Γ ⊢ renVzM ∷ imethTy KnotD IPair tagVar-vz cVar-vz renMotK
⊢renVzM {Γ = Γ} =
  ⊢methLam KnotD IPair tagVar-vz cVar-vz KnotWf cVar-vzWf ⊢IPair ⊢renMotK
    (⊢lam ty-Nat
      (⊢lam (ty-Π (ty-IMu KnotWf
                     (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                  (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here)))))
        (renConv (⊢fst (⊢var (there (there (there (there here))))))
                 ⊢sVar
                 (⊢var (there here))
                 (fordAs (⊢fst (⊢snd (⊢var (there (there (there here)))))))
                 (⊢app (⊢var here)
                       (renVarAt (⊢snd (⊢var (there (there (there (there here))))))
                                 (elAsNat (⊢fst (⊢var (there (there (there here))))))
                                 (fordAs (⊢fst (⊢snd (⊢snd (⊢var (there (there (there here))))))))
                                 (⊢Var-vzKt (elAsNat (⊢fst (⊢var (there (there (there here))))))))))))

renVsM : {Γ : Cx} → RTm Γ
renVsM =
  lam (lam (lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair (pair (var vz) (var (vs (vs vz)))))
          (symN (fst (var (vs (vs (vs (vs vz))))))
                (fst (snd (snd (var (vs (vs (vs vz))))))))
          (app (var vz)
               (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                     (symN (snd (var (vs (vs (vs (vs vz)))))) (fst (snd (snd (snd (var (vs (vs (vs vz)))))))))
                     (Var-vsK (fst (var (vs (vs (vs vz))))) (fst (snd (var (vs (vs (vs vz))))))))))))))

⊢renVsM : {Γ : Ctx} →
          Γ ⊢ renVsM ∷ imethTy KnotD IPair tagVar-vs cVar-vs renMotK
⊢renVsM {Γ = Γ} =
  ⊢methLam KnotD IPair tagVar-vs cVar-vs KnotWf cVar-vsWf ⊢IPair ⊢renMotK
    (⊢lam ty-Nat
      (⊢lam (ty-Π (ty-IMu KnotWf
                     (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                  (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here)))))
        (renConv (⊢fst (⊢var (there (there (there (there here))))))
                 ⊢sVar
                 (⊢var (there here))
                 (fordAs (⊢fst (⊢snd (⊢snd (⊢var (there (there (there here))))))))
                 (⊢app (⊢var here)
                       (renVarAt (⊢snd (⊢var (there (there (there (there here))))))
                                 (elAsNat (⊢fst (⊢var (there (there (there here))))))
                                 (fordAs (⊢fst (⊢snd (⊢snd (⊢snd (⊢var (there (there (there here)))))))))
                                 (⊢Var-vsKt (elAsNat (⊢fst (⊢var (there (there (there here))))))
                                            (⊢fst (⊢snd (⊢var (there (there (there here)))))))))))) 

------------------------------------------------------------------------
-- ★★★ THE TUPLE — 50 COMPUTED, 3 GIVEN, and the mask is `Knot/SubMot`'s
--   because the LOOKUP ROWS ARE THE SAME THREE: a row is given exactly
--   when it carries an `sVar` field, which is a property of `KnotD` and
--   not of what is being pushed through it.
------------------------------------------------------------------------

orB : 𝔹 → 𝔹 → 𝔹
orB true  _ = true
orB false b = b

pickTm : {Γ : Cx} → 𝔹 → RTm Γ → RTm Γ → RTm Γ
pickTm true  a b = a
pickTm false a b = b

payRenR : {Γ : Cx} (v : RTm Γ) (C : ICon (ε ∙)) →
          renTy vs (ipayTy KnotD IPair (isingle v) C) ≡
          ipayTy KnotD IPair (isingle (renTm vs v)) C
payRenR v C = trans (ipayTy-ren vs KnotD IPair (isingle v) C)
                    (ipayTy-cong KnotD IPair C (λ { vz → refl ; (vs ()) }))

------------------------------------------------------------------------
-- ★★★ THE 50 COMPUTED ROWS' TYPING — `Knot/SubMot`'s `⊢isubMethodK`
--   with `sortMap` deleted from the result index and the passenger's
--   codomain at `sVar`.  ⚠ It is SubMot-LOCAL there, so it is copied;
--   a third instantiation should parameterise `Lib/ISub` by it.
------------------------------------------------------------------------


-- ★ and the same, one level up, for the IH tuple's type.
ihRenR : {Γ : Cx} (v q : RTm Γ) (C : ICon (ε ∙)) (M : RTy ((Γ ∙) ∙)) →
         renTy vs (iihTy KnotD IPair (isingle v) C q M)
           ≡ iihTy KnotD IPair (isingle (renTm vs v)) C (renTm vs q)
                   (renTy (extR (extR vs)) M)
ihRenR v q C M =
  trans (iihTy-ren vs KnotD IPair (isingle v) C q M)
        (iihTy-cong KnotD IPair C (renTm vs q) (renTy (extR (extR vs)) M)
                    (λ { vz → refl ; (vs ()) }))

⊢isubMethodR : {Γ : Ctx} (k : ℕ) {C : ICon (ε ∙)}
               (w : SubCon vz C) → IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
               k ∈ID KnotD → ilookupD KnotD k ≡ C →
               Γ ⊢ isubMethod k w ∷ imethTy KnotD IPair k C renMotK
⊢isubMethodR {Γ = Γ} k {C = C} w wC mem look =
  ⊢lam ⊢IPair
    (⊢lam (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) C
                     KnotWf wC
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (⊢lam (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) C}
                      KnotD IPair renMotK (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢renMotK
                      (⊢-cast (payRenR (var vz) C) (⊢var here)))
        (⊢lam ty-Nat
          (⊢lam (ty-Π (ty-IMu KnotWf
                         (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                      (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here)))))
            (⊢icon KnotWf mem
                   (⊢ixP ((⊢fst (⊢var (there (there (there (there here))))))) (⊢var (there here)))
                   (⊢-cast (cong (ipayTy KnotD IPair
                                    (isingle (pair (fst (var (vs (vs (vs (vs vz))))))
                                                   (var (vs vz)))))
                                 (sym look))
                     (⊢isubPay w wC KnotWf
                       (isingle-Sub⊢ (⊢var (there (there (there (there here))))))
                       (isingle-Sub⊢ (⊢ixP ((⊢fst (⊢var (there (there (there (there here)))))))
                                           (⊢var (there here))))
                       refl (step (βfst _ _) done) refl (step (βsnd _ _) done)
                       (⊢fst (⊢var (there (there (there (there here)))))) (⊢snd (⊢var (there (there (there (there here)))))) (⊢var (there here))
                       (⊢var here)
                       (var (vs (vs (vs vz)))) (var (vs (vs vz)))
                       -- ⚠ FOUR RENAMINGS, not three: a binder's TYPE
                       --   lives in the context BEFORE it, so the payload
                       --   is weakened past ITSELF as well as past `ih`,
                       --   `n` and `σ`.
                       (⊢-cast (trans (cong (renTy vs)
                                 (trans (cong (renTy vs)
                                   (trans (cong (renTy vs) (payRenR (var vz) C))
                                          (payRenR (var (vs vz)) C)))
                                   (payRenR (var (vs (vs vz))) C)))
                                 (payRenR (var (vs (vs (vs vz)))) C))
                               (⊢var (there (there (there here)))))
                       -- ⚠ THREE, for the same reason the payload took
                       --   four: `ih` is weakened past itself, `n` and
                       --   `σ`.  ★ And the MOTIVE cancels by `refl` —
                       --   see `renMotK-ren`.
                       (⊢-cast (trans (cong (renTy vs)
                                 (trans (cong (renTy vs)
                                          (ihRenR (var (vs vz)) (var vz) C renMotK))
                                        (ihRenR (var (vs (vs vz))) (var (vs vz)) C renMotK)))
                                 (ihRenR (var (vs (vs (vs vz)))) (var (vs (vs vz))) C renMotK))
                               (⊢var (there (there here)))))))))))

-- ★ the method TYPE's well-formedness, `Knot/SubMot`'s with the motive
--   swapped and `⊢sortMap` gone from the result index.
imethTySubR-wf : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
                 IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
                 Γ ⊢ty imethTy KnotD IPair k C renMotK
imethTySubR-wf {Γ = Γ} k C wC =
  ty-Π ⊢IPair
    (ty-Π (ipayTy-wf {Γ = Γ ▹ εwkTy IPair} KnotD IPair (isingle (var vz)) C
                     KnotWf wC
                     (isingle-Sub⊢ (⊢-cast (εwk-ren vs IPair) (⊢var here))))
      (ty-Π (iihTy-wf {Γ = (Γ ▹ εwkTy IPair) ▹ ipayTy KnotD IPair (isingle (var vz)) C}
                      KnotD IPair renMotK (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs IPair))
                                                   (εwk-ren vs IPair))
                                            (⊢var (there here))))
                      ⊢renMotK
                      (⊢-cast (payRenR (var vz) C) (⊢var here)))
            (ty-Π ty-Nat
              (ty-Π (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢snd (⊢var (there (there (there here)))))))
                          (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here)))))
                    (ty-IMu KnotWf
                       (⊢ixP (⊢fst (⊢var (there (there (there (there here)))))) (⊢var (there here))))))))

imethsTyFromSubR-wf : {Γ : Ctx} (j : ℕ) (E : IDesc) →
                      IDescWfFrom KnotD IPair E →
                      Γ ⊢ty imethsTyFrom KnotD IPair renMotK j E
imethsTyFromSubR-wf j inil    idwf-nil          = ty-Unit
imethsTyFromSubR-wf j (C ◂ E) (idwf-cons wC wE) =
  ty-Σ (imethTySubR-wf j C wC)
       (ren-ty (imethsTyFromSubR-wf (suc j) E wE) there)


-- ★ the obligation ladder, `Knot/SubMot`'s with the motive swapped.
--   ⚠ It is SubMot-LOCAL there (hard-wired to `subMotK`), so it is
--     copied rather than reused; a third customer should parameterise it.
data OKg : Set where
  okg : OKg

data Pr (A B : Set) : Set where
  pr : A → B → Pr A B

GiveOK : (Γ : Ctx) (give : (k : ℕ) → RTm ⌊ Γ ⌋) → ℕ → {E : IDesc} → SubDesc E → Set
GiveOK Γ give j sd-nil        = OKg
GiveOK Γ give j (sd-comp _ W) = GiveOK Γ give (suc j) W
GiveOK Γ give j (sd-give {C = C} W) =
  Pr (Γ ⊢ give j ∷ imethTy KnotD IPair j C renMotK) (GiveOK Γ give (suc j) W)

⊢isubMethsR : {Γ : Ctx} {j : ℕ} {E : IDesc} {give : (k : ℕ) → RTm ⌊ Γ ⌋}
              (W : SubDesc E) → Split KnotD j E → IDescWfFrom KnotD IPair E →
              GiveOK Γ give j W →
              Γ ⊢ isubMeths give j W ∷ imethsTyFrom KnotD IPair renMotK j E
⊢isubMethsR sd-nil        sp idwf-nil          okg      = ⊢unit
⊢isubMethsR {j = j} {give = give} (sd-comp w W) sp (idwf-cons wC wE) g =
  ⊢pair (ren-ty (imethsTyFromSubR-wf (suc j) _ wE) there)
        (⊢isubMethodR j w wC (spl-mem sp) (spl-look sp))
        (⊢-cast (sym (wk-singleTy {v = isubMethod j w} _))
                (⊢isubMethsR W (spl-step sp) wE g))
⊢isubMethsR {j = j} {give = give} (sd-give W) sp (idwf-cons wC wE) (pr dg g) =
  ⊢pair (ren-ty (imethsTyFromSubR-wf (suc j) _ wE) there)
        dg
        (⊢-cast (sym (wk-singleTy {v = give j} _))
                (⊢isubMethsR W (spl-step sp) wE g))

renIsLookup : ℕ → 𝔹
renIsLookup k = orB (eqℕ k 11) (orB (eqℕ k 51) (eqℕ k 52))

renGiveK : {Γ : Cx} (k : ℕ) → RTm Γ
renGiveK k = pickTm (eqℕ k 11) renVarM
               (pickTm (eqℕ k 51) renVzM
                 (pickTm (eqℕ k 52) renVsM unit))

renDescK : SubDesc KnotD
renDescK = decSub renIsLookup 0 KnotD

renGiveOKK : {Γ : Ctx} → GiveOK Γ renGiveK 0 renDescK
renGiveOKK = pr ⊢renVarM (pr ⊢renVzM (pr ⊢renVsM okg))

renMethsK : {Γ : Cx} → RTm Γ
renMethsK = isubMeths renGiveK 0 renDescK

⊢renMethsK : {Γ : Ctx} → Γ ⊢ renMethsK ∷ imethsTy KnotD IPair renMotK KnotD
⊢renMethsK = ⊢isubMethsR {give = renGiveK} renDescK spl-nil KnotWf renGiveOKK

------------------------------------------------------------------------
-- ★★★ `renTm ρ`, AT LAST — AND `ρ` IS AN ARGUMENT.
------------------------------------------------------------------------

renTmK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
renTmK i x = ielim KnotD i renMethsK x

⊢renTmK : {Γ : Ctx} {i x : RTm ⌊ Γ ⌋} →
          Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ x ∷ K i →
          Γ ⊢ renTmK i x ∷ iinst i x renMotK
⊢renTmK di dx = ⊢ielim KnotWf ⊢renMotK di ⊢renMethsK dx

------------------------------------------------------------------------
-- ★★★ `renTm ρ t` AT A SORT AND A DEPTH — `Knot/SubApp`'s `⊢subAtK`,
--   MINUS ITS STABILITY PREMISE.
--
-- ⚠ `⊢subAtK` takes `sortMap s ⟶* s` because its result lands at
--   `pair (sortMap s) m` and the caller wants `pair s m`.  With
--   `smap = id` there is nothing to move: `⊢renAppK` already concludes
--   at `pair s m`, so this is one application and no conversion.
------------------------------------------------------------------------

renTmAtK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
renTmAtK s dd m rn t = app (app (renTmK (pair s dd) t) m) rn

⊢renTmAtK : {Γ : Ctx} {s dd m rn t : RTm ⌊ Γ ⌋} →
            Γ ⊢ s ∷ Nat → Γ ⊢ dd ∷ Nat → Γ ⊢ m ∷ Nat →
            Γ ⊢ rn ∷ RenTy dd m → Γ ⊢ t ∷ K (pair s dd) →
            Γ ⊢ renTmAtK s dd m rn t ∷ K (pair s m)
⊢renTmAtK ds dd dm drn dt = ⊢renAppK (⊢renTmK (⊢ixP ds dd) dt) dm drn

------------------------------------------------------------------------
-- ★★★ AND `vs` ITSELF, AS A VALUE.  ⚠⚠ THIS IS THE POINT OF THE WHOLE
--   ARC.  `Knot/Wk.wkK` is a weakening whose renaming lives inside
--   `Lib/IWk`'s fold, unnamed and unrecoverable; here it is a `lam` you
--   can read, apply, and test pointwise.
------------------------------------------------------------------------

vsRenK : {Γ : Cx} → RTm Γ → RTm Γ
vsRenK n = lam (Var-vsK (renTm vs n) (var vz))

⊢vsRenK : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ Nat → Γ ⊢ vsRenK n ∷ RenTy n (nsuc n)
⊢vsRenK dn =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar dn)) (⊢Var-vsKt (⊢wk dn) (⊢var here))
