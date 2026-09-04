------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `conS` AND `atCon`, OBJECT-LEVEL.
--
--     conS k vz     = con k (var vz)
--     conS k (vs x) = var (vs x)
--     atCon k M     = subTy (conS k) M
--
-- ★★★ `atCon k M` IS THE MOTIVE RE-BASED AT THE PAYLOAD BINDER — the
--   move that makes tupled methods type WITHOUT η (gate 5c), and the
--   last piece `methTy` needs after `payTy` and `ihTy`.
--
-- ★ SHAPE: `Knot/Nrs`'s, MINUS the raising.  `nrs` sends a variable at
--   `n` to a term at `nsuc n`; `conS` stays put — `Sub (Γ ∙) (Γ ∙)` —
--   so every `nsuc` in `Knot/Nrs`'s two `Var` rows disappears and the
--   transport lands where it was built.  ⇒ the SIMPLEST of the three
--   `Var`-eliminators (`single` lowers, `nrs` raises, `conS` neither).
--
-- ⚠ AND THE TAG RIDES AS A `Π Nat` PASSENGER, `Knot/LookupD`'s move: it
--   is used in ONE row and must be available in all 53.
--
-- ★★ `towerA` A FOURTH TIME.  `⊢conSSK`'s descent — `iinst` twice, then
--   one `⊢app` — is `subTm (single k) (subTm (extS (single x))
--   (subTm (extS² (single i)) (var (vs (vs vz)))))`, which is `towerA`
--   on the nose.  A motive with ONE passenger reading `⟨i⟩` in the
--   result has exactly that shape, whatever the passenger is.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.ConS where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; fst; snd; pair; nsuc
        ; ICon; IDesc; εwkTy; IMu; unit; ielim; Σ'; Nat; _◂_; renTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢nsuc; ty-IMu; IConWf; imethTy; imethsTy; imethsTyFrom
        ; ⊢unit; ⊢ielim; IDescWfFrom; ⊢lam; βsnd; ξ-nsuc; ξ-pairʳ )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢methsFrom; ⊢methsCons; imethsTyFrom-wf; idwfDrop
        ; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-nzeroK; Tm-varK; Tm-nsucK )
open import DirectedHoTT.Examples.Knot.CtorsV
  using ( ⊢Tm-nzeroKv; ⊢Tm-varKv; ⊢Tm-nsucKv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK; ⊢Var-vzKt; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.Desc using ( cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Wf using ( cVar-vzWf; cVar-vsWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz; tagVar-vs )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( symN; ⊢symN )
open import DirectedHoTT.Lib.IdSuc using ( predN; ⊢fordPredN )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Lib.Monus using ( predTm; ⊢pred )
open import DirectedHoTT.Spec.Syntax using ( ⌜IMu⌝; jsub )
open import DirectedHoTT.Spec.Typing using ( ⊢jsub; ⊢⌜IMu⌝; ⊢fst )
open import DirectedHoTT.Examples.Knot.Sorts using ( sVar; ⊢sVar )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Spec.Typing using ( wk-single )
open import normalizer.Syntax.Types using ( cong )

open import DirectedHoTT.Spec.Syntax using ( Π; app )
open import DirectedHoTT.Spec.Typing using ( ty-Π; ty-Nat; ⊢app; ⊢nsuc )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-conK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-conKv )
open import DirectedHoTT.Lib.Wk using ( towerA )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTyAtK; ⊢subTyAtK )
open import DirectedHoTT.Examples.Knot.Sorts using ( sTy )
open import normalizer.Syntax.Types using ( sym )

------------------------------------------------------------------------
-- ★ THE MOTIVE.  The tag rides; the answer sits at the Var's own depth.
------------------------------------------------------------------------

conSMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
conSMotK = Π Nat (IMu KnotD IPair (pair sTm (snd (var (vs (vs vz))))))

⊢conSMotK : {Γ : Ctx} →
            ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty conSMotK
⊢conSMotK =
  ty-Π ty-Nat (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢var (there (there here))))))

------------------------------------------------------------------------
-- ★ THE 51 UNREACHABLE ROWS.
------------------------------------------------------------------------

conSJunk : {Γ : Cx} → RTm Γ
conSJunk = lam (lam (lam (lam Tm-nzeroK)))

⊢conSJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
            IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
            Γ ⊢ conSJunk ∷ imethTy KnotD IPair k C conSMotK
⊢conSJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢conSMotK
    (⊢lam ty-Nat
      (⊢Tm-nzeroKv _ (⊢snd (⊢var (there (there (there here)))))))

------------------------------------------------------------------------
-- ★★★ `vz ↦ con k (var vz)`.  ⚠ SAME FORD TRANSPORT AS `Knot/Nrs`'s
--   `vz` row and it lands ONE `nsuc` lower: the row's `m` and the
--   ambient `snd ⟨i⟩` agree only through the row's depth ford.
------------------------------------------------------------------------

conSVz : {Γ : Cx} → RTm Γ
conSVz = lam (lam (lam (lam
  (Tm-conK (var vz)
    (Tm-varK
      (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
            (symN (snd (var (vs (vs (vs vz)))))
                  (fst (snd (snd (var (vs (vs vz)))))))
            (Var-vzK (fst (var (vs (vs vz)))))))))))

⊢conSVz : {Γ : Ctx} →
          Γ ⊢ conSVz ∷ imethTy KnotD IPair tagVar-vz cVar-vz conSMotK
⊢conSVz =
  ⊢methLam KnotD IPair tagVar-vz cVar-vz KnotWf cVar-vzWf ⊢IPair ⊢conSMotK
    (⊢lam ty-Nat
      (⊢Tm-conKv _ dsi (⊢var here) (⊢Tm-varKv _ dsi tx)))
  where
    dp   = ⊢var (there (there here))
    dsi  = ⊢snd (⊢var (there (there (there here))))
    dm   = elAsNat (⊢fst dp)
    deq  = ⊢symN dsi (⊢nsuc dm) (fordAs (⊢fst (⊢snd (⊢snd dp))))
    tx   = fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                         (natAsEl (⊢nsuc dm)) (natAsEl dsi) deq
                         (toMu (⊢Var-vzKt dm)))

------------------------------------------------------------------------
-- ★★★ `vs x ↦ var (vs x)` — the variable REBUILT, not weakened.  ⚠ `k`
--   is unused in this row; `conS` touches the tag only at `vz`.
------------------------------------------------------------------------

conSVs : {Γ : Cx} → RTm Γ
conSVs = lam (lam (lam (lam
  (Tm-varK
    (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
          (symN (snd (var (vs (vs (vs vz)))))
                (fst (snd (snd (snd (var (vs (vs vz))))))))
          (Var-vsK (fst (var (vs (vs vz)))) (fst (snd (var (vs (vs vz)))))))))))

⊢conSVs : {Γ : Ctx} →
          Γ ⊢ conSVs ∷ imethTy KnotD IPair tagVar-vs cVar-vs conSMotK
⊢conSVs =
  ⊢methLam KnotD IPair tagVar-vs cVar-vs KnotWf cVar-vsWf ⊢IPair ⊢conSMotK
    (⊢lam ty-Nat (⊢Tm-varKv _ dsi tx))
  where
    dp   = ⊢var (there (there here))
    dsi  = ⊢snd (⊢var (there (there (there here))))
    dm   = elAsNat (⊢fst dp)
    dx   = ⊢fst (⊢snd dp)
    deq  = ⊢symN dsi (⊢nsuc dm) (fordAs (⊢fst (⊢snd (⊢snd (⊢snd dp)))))
    tx   = fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                         (natAsEl (⊢nsuc dm)) (natAsEl dsi) deq
                         (toMu (⊢Var-vsKt dm dx)))

------------------------------------------------------------------------
-- ★★★ THE TUPLE — `Knot/Nrs`'s assembly exactly.
------------------------------------------------------------------------

conSTail : {Γ : Cx} → RTm Γ
conSTail = pair conSVz (pair conSVs unit)

CD51 : IDesc
CD51 = cdRest (cdTake 51 KnotD)

csp51 : Split KnotD 51 CD51
csp51 = splTake spl-nil (cdTake 51 KnotD)

⊢conSTail : {Γ : Ctx} →
            Γ ⊢ conSTail ∷ imethsTyFrom KnotD IPair conSMotK 51 CD51
⊢conSTail =
  ⊢methsCons KnotD IPair 51 {C = cVar-vz} _ KnotWf
             (idwfDrop (spl-step csp51) KnotWf) (spl-step csp51)
             ⊢IPair ⊢conSMotK ⊢conSVz
    (⊢methsCons KnotD IPair 52 {C = cVar-vs} _ KnotWf
                (idwfDrop (spl-step (spl-step csp51)) KnotWf)
                (spl-step (spl-step csp51))
                ⊢IPair ⊢conSMotK ⊢conSVs ⊢unit)

conSMeths : {Γ : Cx} → RTm Γ
conSMeths = methsFrom (cdTake 51 KnotD) conSJunk conSTail

⊢conSMeths : {Γ : Ctx} → Γ ⊢ conSMeths ∷ imethsTy KnotD IPair conSMotK KnotD
⊢conSMeths =
  ⊢methsFrom KnotD IPair 0 (cdTake 51 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢conSMotK (λ {k} {C} wC _ _ → ⊢conSJunk k C wC)
             conSTail ⊢conSTail

------------------------------------------------------------------------
-- ★★ THE ELIMINATOR, THEN THE SUBSTITUTION, THEN `atCon`.
------------------------------------------------------------------------

conSSK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
conSSK i x k = app (ielim KnotD i conSMeths x) k

⊢conSSK : {Γ : Ctx} {i x k : RTm ⌊ Γ ⌋} →
          Γ ⊢ i ∷ εwkTy IPair → Γ ⊢ x ∷ K i → Γ ⊢ k ∷ Nat →
          Γ ⊢ conSSK i x k ∷ K (pair sTm (snd i))
⊢conSSK {i = i} {x = x} {k = k} di dx dk =
  ⊢-cast (cong (λ z → K (pair sTm (snd z))) (towerA k x i))
    (⊢app (⊢ielim KnotWf ⊢conSMotK di ⊢conSMeths dx) dk)

conSK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
conSK n k = lam (conSSK (pair sVar (nsuc (renTm vs n))) (var vz) (renTm vs k))

⊢conSK : {Γ : Ctx} {n k : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat →
         Γ ⊢ conSK n k ∷ SubTy (nsuc n) (nsuc n)
⊢conSK {n = n} {k = k} dn dk =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢nsuc dn)))
       (muFwd (ξ-pairʳ (βsnd _ _))
         (⊢conSSK (⊢ixP ⊢sVar (⊢nsuc (⊢wk dn))) (⊢var here) (⊢wk dk)))

-- ★★★ `atCon k M` — and it is `subTy` at a substitution that neither
--   raises nor lowers, so BOTH depths are `nsuc n`.
atConK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
atConK n k M = subTyAtK (nsuc n) (nsuc n) (conSK n k) M

⊢atConK : {Γ : Ctx} {n k M : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat → Γ ⊢ M ∷ K (pair sTy (nsuc n)) →
          Γ ⊢ atConK n k M ∷ K (pair sTy (nsuc n))
⊢atConK dn dk dM = ⊢subTyAtK (⊢nsuc dn) (⊢nsuc dn) (⊢conSK dn dk) dM
