------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `iconS` AND `iatCon`, THE OBJECT LEVEL.
--
--     iconS k i vz          = icon k (var vz)
--     iconS k i (vs vz)     = renTm vs i
--     iconS k i (vs (vs x)) = var (vs x)
--
-- ⚠⚠ THREE Var CASES, TWO LEVELS DEEP — and a nested eliminator is NOT
--   what it costs.  `iconS` FACTORS:
--
--       iconS k i x  ≡  subTm (icS k) (extS (single i) x)
--
--   where `icS k` is `conS` with `icon` for `con`.  Checked on all three:
--
--     vz        `extS (single i) vz = var vz`,  `icS k vz = icon k (var vz)`
--     vs vz     `extS … = w i`,                 and `icS k ∘ vs = var ∘ vs`
--                                               leaves `w i` alone
--     vs (vs y) `extS … = var (vs y)`,          likewise untouched
--
--   ⇒ the object level is `subTmAtK` of a `conSK`-clone over `extNK` of
--     `singleK` — three functions that already exist — instead of a
--     `Var`-eliminator whose `vs` method eliminates again.
--
-- ★ AND THE CLONE IS ONE TOKEN.  `iconSVz` is `Knot/ConS.conSVz` with
--   `Tm-conK`/`⊢Tm-conKv` replaced by `Tm-iconK`/`⊢Tm-iconKv`; the ford
--   transport that row pays (`cVar-vz` Fords its DEPTH) is identical, so
--   the motive, the junk row and the whole `vs` row are IMPORTED from
--   `Knot/ConS` rather than copied.
--
-- ⬜ OWED, and stated here because the factorisation is the thing to
--   check: `iconS k i x ≡ subTm (icS k) (extS (single i) x)` is a
--   three-case `Var` induction at the SPEC level, and the adequacy of
--   `iconSK` goes through it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IConS where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; fst; snd; pair; nsuc
        ; ICon; IDesc; εwkTy; IMu; unit; ielim; Nat; _◂_; renTm
        ; ⌜IMu⌝; jsub; Π; app )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢fst; ⊢nsuc; ty-IMu; ty-Π; ty-Nat; IConWf; imethTy
        ; imethsTy; imethsTyFrom; ⊢unit; ⊢ielim; ⊢lam; ⊢app; ⊢jsub; ⊢⌜IMu⌝
        ; βsnd; ξ-pairʳ )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢methsFrom; ⊢methsCons; idwfDrop
        ; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; sTy; ⊢sTy; sVar; ⊢sVar; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cVar-vzWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz; tagVar-vs )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-iconK; Tm-varK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-iconKv; ⊢Tm-varKv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; ⊢Var-vzKt )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( symN; ⊢symN )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Wk using ( towerA )
open import normalizer.Syntax.Types using ( cong )
open import DirectedHoTT.Spec.Typing using ( wk-single )
-- ★ EVERYTHING SHARED WITH `conS` IS IMPORTED, NOT COPIED.
open import DirectedHoTT.Examples.Knot.ConS
  using ( conSMotK; ⊢conSMotK; conSJunk; ⊢conSJunk; conSVs; ⊢conSVs )
open import DirectedHoTT.Examples.Knot.Single using ( singleK; ⊢singleK )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK; ⊢extNK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTyAtK; ⊢subTyAtK; subTmAtK; ⊢subTmAtK )

------------------------------------------------------------------------
-- ★★★ `vz ↦ icon k (var vz)` — `Knot/ConS.conSVz` with `icon` for `con`.
------------------------------------------------------------------------

iconSVz : {Γ : Cx} → RTm Γ
iconSVz = lam (lam (lam (lam
  (Tm-iconK (var vz)
    (Tm-varK
      (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
            (symN (snd (var (vs (vs (vs vz)))))
                  (fst (snd (snd (var (vs (vs vz)))))))
            (Var-vzK (fst (var (vs (vs vz)))))))))))

⊢iconSVz : {Γ : Ctx} →
           Γ ⊢ iconSVz ∷ imethTy KnotD IPair tagVar-vz cVar-vz conSMotK
⊢iconSVz =
  ⊢methLam KnotD IPair tagVar-vz cVar-vz KnotWf cVar-vzWf ⊢IPair ⊢conSMotK
    (⊢lam ty-Nat
      (⊢Tm-iconKv _ dsi (⊢var here) (⊢Tm-varKv _ dsi tx)))
  where
    dp   = ⊢var (there (there here))
    dsi  = ⊢snd (⊢var (there (there (there here))))
    dm   = elAsNat (⊢fst dp)
    deq  = ⊢symN dsi (⊢nsuc dm) (fordAs (⊢fst (⊢snd (⊢snd dp))))
    tx   = fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                         (natAsEl (⊢nsuc dm)) (natAsEl dsi) deq
                         (toMu (⊢Var-vzKt dm)))

------------------------------------------------------------------------
-- ★ THE TUPLE — the SAME 51 junk rows and the SAME `vs` row as `conS`.
------------------------------------------------------------------------

ID51 : IDesc
ID51 = cdRest (cdTake 51 KnotD)

isp51 : Split KnotD 51 ID51
isp51 = splTake spl-nil (cdTake 51 KnotD)

iconSTail : {Γ : Cx} → RTm Γ
iconSTail = pair iconSVz (pair conSVs unit)

⊢iconSTail : {Γ : Ctx} →
             Γ ⊢ iconSTail ∷ imethsTyFrom KnotD IPair conSMotK 51 ID51
⊢iconSTail =
  ⊢methsCons KnotD IPair 51 {C = cVar-vz} _ KnotWf
             (idwfDrop (spl-step isp51) KnotWf) (spl-step isp51)
             ⊢IPair ⊢conSMotK ⊢iconSVz
    (⊢methsCons KnotD IPair 52 {C = cVar-vs} _ KnotWf
                (idwfDrop (spl-step (spl-step isp51)) KnotWf)
                (spl-step (spl-step isp51))
                ⊢IPair ⊢conSMotK ⊢conSVs ⊢unit)

iconSMeths : {Γ : Cx} → RTm Γ
iconSMeths = methsFrom (cdTake 51 KnotD) conSJunk iconSTail

⊢iconSMeths : {Γ : Ctx} → Γ ⊢ iconSMeths ∷ imethsTy KnotD IPair conSMotK KnotD
⊢iconSMeths =
  ⊢methsFrom KnotD IPair 0 (cdTake 51 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢conSMotK (λ {k} {C} wC _ _ → ⊢conSJunk k C wC)
             iconSTail ⊢iconSTail

------------------------------------------------------------------------
-- ★ `icS k` — the ONE-LEVEL substitution, then the composition.
------------------------------------------------------------------------

iconSSK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
iconSSK i x k = app (ielim KnotD i iconSMeths x) k

⊢iconSSK : {Γ : Ctx} {i x k : RTm ⌊ Γ ⌋} →
           Γ ⊢ i ∷ εwkTy IPair → Γ ⊢ x ∷ K i → Γ ⊢ k ∷ Nat →
           Γ ⊢ iconSSK i x k ∷ K (pair sTm (snd i))
⊢iconSSK {i = i} {x = x} {k = k} di dx dk =
  ⊢-cast (cong (λ z → K (pair sTm (snd z))) (towerA k x i))
    (⊢app (⊢ielim KnotWf ⊢conSMotK di ⊢iconSMeths dx) dk)

icSK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
icSK n k = lam (iconSSK (pair sVar (nsuc (renTm vs n))) (var vz) (renTm vs k))

⊢icSK : {Γ : Ctx} {n k : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat →
        Γ ⊢ icSK n k ∷ SubTy (nsuc n) (nsuc n)
⊢icSK {n = n} {k = k} dn dk =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢nsuc dn)))
       (muFwd (ξ-pairʳ (βsnd _ _))
         (⊢iconSSK (⊢ixP ⊢sVar (⊢nsuc (⊢wk dn))) (⊢var here) (⊢wk dk)))

------------------------------------------------------------------------
-- ★★★ `iconS k i = icS k ∘ extS (single i)` — the factorisation, built.
-- ⚠ `iconS` LOWERS (`Sub ((Γ ∙) ∙) (Γ ∙)`), and that is `extS (single i)`
--   doing it; `icS k` neither raises nor lowers, exactly as `conS` does
--   not.  So the two depths of the `subTmAtK` are both `nsuc n`.
-- ⚠ EVERYTHING IS WEAKENED past the `lam`'s own binder.
------------------------------------------------------------------------

iconSK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
iconSK n k i =
  lam (subTmAtK (nsuc (renTm vs n)) (nsuc (renTm vs n))
                (icSK (renTm vs n) (renTm vs k))
                (app (extNK (nsuc (renTm vs n)) (renTm vs n)
                            (singleK (renTm vs n) (renTm vs i)))
                     (var vz)))

⊢iconSK : {Γ : Ctx} {n k i : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat → Γ ⊢ i ∷ K (pair sTm n) →
          Γ ⊢ iconSK n k i ∷ SubTy (nsuc (nsuc n)) (nsuc n)
⊢iconSK {n = n} dn dk di =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢nsuc (⊢nsuc dn))))
    (⊢subTmAtK (⊢nsuc (⊢wk dn)) (⊢nsuc (⊢wk dn))
               (⊢icSK (⊢wk dn) (⊢wk dk))
               -- ⚠ APPLYING A `SubTy` LEAVES A `wk-single`.  Its
               --   codomain is `K (pair sTm (renTm vs n))`, so `⊢app`
               --   substitutes the argument into a WEAKENED `n` and the
               --   round trip has to be cancelled.  `⊢extNK`'s own body
               --   pays the identical cast.
               (⊢-cast (cong (λ z → K (pair sTm (nsuc z)))
                             (wk-single {v = var vz} (renTm vs n)))
                 (⊢app (⊢extNK (⊢nsuc (⊢wk dn)) (⊢wk dn)
                               (⊢singleK (⊢wk dn) (⊢wk di)))
                       (⊢var here))))

------------------------------------------------------------------------
-- ★ `iatCon k i M = subTy (iconS k i) M` — the motive re-based at the
--   INDEXED constructor.  ⚠ Unlike `atCon`, the substitution LOWERS, so
--   the two depths differ: `nsuc (nsuc n)` down to `nsuc n`.
------------------------------------------------------------------------

iatConK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
iatConK n k i M = subTyAtK (nsuc (nsuc n)) (nsuc n) (iconSK n k i) M

⊢iatConK : {Γ : Ctx} {n k i M : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat → Γ ⊢ i ∷ K (pair sTm n) →
           Γ ⊢ M ∷ K (pair sTy (nsuc (nsuc n))) →
           Γ ⊢ iatConK n k i M ∷ K (pair sTy (nsuc n))
⊢iatConK dn dk di dM =
  ⊢subTyAtK (⊢nsuc (⊢nsuc dn)) (⊢nsuc dn) (⊢iconSK dn dk di) dM
