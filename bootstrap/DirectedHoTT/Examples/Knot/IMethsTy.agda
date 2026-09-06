------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `imethsTyFrom` AND `imethsTy`, ASSEMBLED.
--
-- ★ TWO ROWS OF 53 ARE REAL, and one is the junk method: `cIDesc-nil`
--   (46) takes it and for it the junk IS the answer; `cIDesc-cons` (47)
--   is the row below.
-- ⚠ ITS `ICon` FIELD IS PINNED (`lit(1)`), so it still occupies an IH
--   SLOT — `⊢ihSkipρ` steps past it — even though the field itself is
--   copied rather than descended into.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IMethsTy where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTm; IDesc; var; lam; snd; pair; unit; app; fst
        ; ICon; iρ; iκ; iι; ⌜Id⌝; ⌜Nat⌝; isingle; iext; _◂_; ielim
        ; nzero; nsuc; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢var; here; there; ⊢snd; ⊢fst; ⊢lam; ⊢unit
        ; ⊢nzero; ⊢nsuc; ty-Nat; ty-IMu; imethTy
        ; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ; ⊢methsFrom; ⊢methsCons
        ; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sICon; sIDesc; ⊢sIDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cIDesc-cons )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cIDesc-consWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagIDesc-cons )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-SgK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK )
open import DirectedHoTT.Examples.Knot.IMethTy using ( imethTyK )
open import DirectedHoTT.Examples.Knot.IMethsTyMot
  using ( imethsTyMotK; ⊢imethsTyMotK; imethsTyJunk; ⊢imethsTyJunk
        ; ⊢imethsAppK; ⊢imethsRowCons )

------------------------------------------------------------------------
-- ★ THE `cIDesc-cons` ROW.
------------------------------------------------------------------------

imethsTyCons : {Γ : Cx} → RTm Γ
imethsTyCons =
  lam (lam (lam (lam (lam (lam (lam (lam
    (Ty-SgK (imethTyK (var (vs (vs (vs (vs vz)))))        -- n
                      (var vz)                            -- j
                      (var (vs (vs (vs vz))))             -- D
                      (var (vs (vs vz)))                  -- I
                      (fst (var (vs (vs (vs (vs (vs (vs vz))))))))  -- C
                      (var (vs vz)))                      -- M
            (wkTyK (var (vs (vs (vs (vs vz)))))
                   (app (app (app (app (app
                          (fst (snd (var (vs (vs (vs (vs (vs vz)))))))) 
                          (var (vs (vs (vs (vs vz)))))) 
                          (var (vs (vs (vs vz)))))
                          (var (vs (vs vz))))
                          (var (vs vz)))
                        (nsuc (var vz)))))))))))) 

⊢imethsTyCons : {Γ : Ctx} →
                Γ ⊢ imethsTyCons
                  ∷ imethTy KnotD IPair tagIDesc-cons cIDesc-cons imethsTyMotK
⊢imethsTyCons =
  ⊢methLam KnotD IPair tagIDesc-cons cIDesc-cons KnotWf cIDesc-consWf
           ⊢IPair ⊢imethsTyMotK
    (⊢lam ty-Nat
      (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var here)))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTy ⊢nzero))
          (⊢lam (ty-IMu KnotWf
                   (⊢ixP ⊢sTy (⊢nsuc (⊢nsuc (⊢var (there (there here)))))))
            (⊢lam ty-Nat
              (⊢imethsRowCons dn dj dD dI dC dM
                (⊢imethsAppK
                   {dd = snd (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) }
                   {u = fst (snd (var (vs (vs (vs (vs (vs (vs vz))))))))}
                   dIH dn dD dI dM (⊢nsuc dj))))))))
  where
    dn  = ⊢var (there (there (there (there here))))
    dD  = ⊢var (there (there (there here)))
    dI  = ⊢var (there (there here))
    dM  = ⊢var (there here)
    dj  = ⊢var here
    dC  = ⊢fst (⊢var (there (there (there (there (there (there here)))))))
    dIH = ⊢ihHere
            {D = KnotD} {I = IPair}
            {σ = iext (isingle (var (vs (vs (vs (vs (vs (vs (vs vz)))))))))
                      (fst (var (vs (vs (vs (vs (vs (vs vz)))))))) }
            {j = pair sIDesc (snd (var (vs vz)))}
            (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sIDesc) iι)
            {q = snd (var (vs (vs (vs (vs (vs (vs vz)))))))} {M = imethsTyMotK}
            (⊢ihSkipρ
               {D = KnotD} {I = IPair}
               {σ = isingle (var (vs (vs (vs (vs (vs (vs (vs vz))))))))}
               {j = pair sICon (nsuc nzero)}
               (iρ (pair sIDesc (snd (var (vs vz))))
                 (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sIDesc) iι))
               {q = var (vs (vs (vs (vs (vs (vs vz))))))} {M = imethsTyMotK}
               (⊢var (there (there (there (there (there here)))))))

------------------------------------------------------------------------
-- ★ THE TUPLE AND THE WRAPPERS.
------------------------------------------------------------------------

MID48 : IDesc
MID48 = cdRest (cdTake 48 KnotD)

MID47' : IDesc
MID47' = cIDesc-cons ◂ MID48

mispl47 : Split KnotD 47 MID47'
mispl47 = splTake spl-nil (cdTake 47 KnotD)

miwf48 : IDescWfFrom KnotD IPair MID48
miwf48 = idwfDrop (spl-step mispl47) KnotWf

imethsTyTail : {Γ : Cx} → RTm Γ
imethsTyTail = methsFrom (cdTake 5 MID48) imethsTyJunk unit

⊢imethsTyTail : {Γ : Ctx} →
                Γ ⊢ imethsTyTail
                  ∷ imethsTyFrom KnotD IPair imethsTyMotK 48 MID48
⊢imethsTyTail =
  ⊢methsFrom KnotD IPair 48 (cdTake 5 MID48) KnotWf miwf48 (spl-step mispl47)
             ⊢IPair ⊢imethsTyMotK (λ {k} {C} wC _ _ → ⊢imethsTyJunk k C wC)
             unit ⊢unit

imethsTyMid47 : {Γ : Cx} → RTm Γ
imethsTyMid47 = pair imethsTyCons imethsTyTail

⊢imethsTyMid47 : {Γ : Ctx} →
                 Γ ⊢ imethsTyMid47
                   ∷ imethsTyFrom KnotD IPair imethsTyMotK 47 MID47'
⊢imethsTyMid47 =
  ⊢methsCons KnotD IPair 47 {C = cIDesc-cons} MID48 KnotWf miwf48
             (spl-step mispl47) ⊢IPair ⊢imethsTyMotK
             ⊢imethsTyCons ⊢imethsTyTail

imethsTyMethsK : {Γ : Cx} → RTm Γ
imethsTyMethsK = methsFrom (cdTake 47 KnotD) imethsTyJunk imethsTyMid47

⊢imethsTyMethsK : {Γ : Ctx} →
                  Γ ⊢ imethsTyMethsK ∷ imethsTy KnotD IPair imethsTyMotK KnotD
⊢imethsTyMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 47 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢imethsTyMotK (λ {k} {C} wC _ _ → ⊢imethsTyJunk k C wC)
             imethsTyMid47 ⊢imethsTyMid47

imethsTyFromK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
imethsTyFromK n D I M j E =
  app (app (app (app (app (ielim KnotD (pair sIDesc n) imethsTyMethsK E) n) D) I) M) j

⊢imethsTyFromK : {Γ : Ctx} {n D I M j E : RTm ⌊ Γ ⌋} →
                 Γ ⊢ n ∷ Nat → Γ ⊢ D ∷ K (pair sIDesc n) →
                 Γ ⊢ I ∷ K (pair sTy nzero) →
                 Γ ⊢ M ∷ K (pair sTy (nsuc (nsuc n))) → Γ ⊢ j ∷ Nat →
                 Γ ⊢ E ∷ K (pair sIDesc n) →
                 Γ ⊢ imethsTyFromK n D I M j E ∷ K (pair sTy n)
-- ⚠ `dd`/`u` PINNED — they occur only under `iinst`, which is DEFINED
--   and so not injective.  `⊢methsTyFromK` and `⊢iihTyK` did not need it;
--   the difference is that both of those have a passenger whose type
--   mentions the index directly, and this motive's do not.
⊢imethsTyFromK {n = n} {E = E} dn dD dI dM dj dE =
  ⊢imethsAppK {dd = n} {u = E}
              (⊢ielim KnotWf ⊢imethsTyMotK (⊢ixP ⊢sIDesc dn) ⊢imethsTyMethsK dE)
              dn dD dI dM dj

-- ★ `imethsTy D I M E = imethsTyFrom D I M zero E`.
imethsTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
imethsTyK n D I M E = imethsTyFromK n D I M nzero E

⊢imethsTyK : {Γ : Ctx} {n D I M E : RTm ⌊ Γ ⌋} →
             Γ ⊢ n ∷ Nat → Γ ⊢ D ∷ K (pair sIDesc n) →
             Γ ⊢ I ∷ K (pair sTy nzero) →
             Γ ⊢ M ∷ K (pair sTy (nsuc (nsuc n))) →
             Γ ⊢ E ∷ K (pair sIDesc n) →
             Γ ⊢ imethsTyK n D I M E ∷ K (pair sTy n)
⊢imethsTyK dn dD dI dM dE = ⊢imethsTyFromK dn dD dI dM ⊢nzero dE
