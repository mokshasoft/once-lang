------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `single u`, OBJECT-LEVEL.
--
-- `singleK n u : SubTy (nsuc n) n` — the substitution that replaces the
-- top variable by `u` and leaves the rest alone:
--
--     vz    ↦ u
--     vs y  ↦ var y
--
-- ⚠ IT IS WHAT `β` NEEDS.  `β : app (lam t) u ⟶ subTm (single u) t`, and
--   `subTmK` has existed since 2026-08-29 — what was missing is the
--   SUBSTITUTION IT IS APPLIED TO.  Seven judgement rows wait on this
--   one (`β`, `natrec-suc`, `⊢app`, `⊢pair`, `⊢snd`, `⊢jsub`, `⊢natrec`).
--
-- ★★ AND IT IS SMALL NOW ONLY BECAUSE THE MACHINERY IS SHARED.  Before
--   `iatCon-wf` every new object-level function copied the whole method
--   tuple; this one uses `Lib/IPay`'s `⊢methLam` for each method's three
--   generic binders and `⊢methsFrom` for the tuple, and writes only what
--   is ITS OWN: one motive and one real method.
--
-- ★ THE MOTIVE IS `Π A A` AT THE PREDECESSOR DEPTH, which is why 52 of
--   the 53 rows are the IDENTITY: `lam (var vz)` inhabits `Π A A` at
--   every index, with nothing index-specific to say.  Only `cVar-vs`
--   does real work — it returns `var y` for the field it carries.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Single where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; app; pair; fst; snd; unit
        ; nsuc; Π; IMu; Nat; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; ⌜IMu⌝; jsub; ielim; isingle; εwkTy; renTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢lam; ⊢app; ⊢pair; ⊢unit; ⊢conv; ty-Π; ty-IMu; ty-Nat
        ; IConWf; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTy; imethsTyFrom; ⊢ielim; ⊢snd; ⊢fst )
open import DirectedHoTT.Lib.IMeths using ( CDesc; cdTake; cdRest; cdPos; methsFrom )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam; ⊢methsFrom; imethsTyFrom-wf
                                        ; Split; spl-nil )
open import DirectedHoTT.Lib.Monus using ( predTm; ⊢pred )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sTm; sVar; ⊢sTm; ⊢sVar; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cVar-vsWf )
open import DirectedHoTT.Examples.Knot.Desc using ( cVar-vs )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vs )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-varK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-varKv )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs )
open import DirectedHoTT.Lib.ArithComm using ( symN; ⊢symN )
open import DirectedHoTT.Lib.IdSuc using ( predN; ⊢fordPredN )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Spec.Typing using ( ⊢jsub; ⊢⌜IMu⌝ )

------------------------------------------------------------------------
-- ★ THE MOTIVE.  At index `i` the answer is a function from a term at
--   `pred (snd i)` to a term at `pred (snd i)` — so at a `Var` index
--   `(sVar , nsuc d)` it is `Tm d → Tm d`, which is what a `single`
--   must deliver once its variable is consumed.
------------------------------------------------------------------------

singleMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
singleMotK =
  Π (IMu KnotD IPair (pair sTm (predTm (snd (var (vs vz))))))
    (IMu KnotD IPair (pair sTm (predTm (snd (var (vs (vs vz))))))) 

⊢singleMotK : {Γ : Ctx} →
              ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty singleMotK
⊢singleMotK =
  ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢pred (⊢snd (⊢var (there here))))))
       (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢pred (⊢snd (⊢var (there (there here)))))))

------------------------------------------------------------------------
-- ★★★ THE IDENTITY METHOD — and it serves 52 of the 53 rows.
--
-- ⚠ COMPARE `Knot/SubMot`'s `⊢constMeth` BEFORE `⊢methLam`: eighteen
--   lines of `⊢lam`/`ipayTy-wf`/`iihTy-wf` and two `ipayTy-ren` casts,
--   copied per customer.  Here the prologue is one call and what is left
--   is the motive's own binder and `⊢var here`.
------------------------------------------------------------------------

singleId : {Γ : Cx} → RTm Γ
singleId = lam (lam (lam (lam (var vz))))

⊢singleId : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
            IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
            Γ ⊢ singleId ∷ imethTy KnotD IPair k C singleMotK
⊢singleId k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢singleMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢pred (⊢snd (⊢var (there (there here)))))))
          (⊢var here))

------------------------------------------------------------------------
-- ★★★ THE ONE REAL METHOD — `vs y ↦ var y`.
--
-- ⚠ IT PAYS THE SAME FORD TRANSPORT `Knot/SubMot`'s `extVs` does, for
--   the same reason: `cVar-vs` Fords its DEPTH, so the field it carries
--   is a `Var` at `d` while the motive asks for one at
--   `predTm (snd ⟨i⟩)`.  Those agree only through the row's own depth
--   ford, inverted (`⊢symN`) and stepped down (`⊢fordPredN`).
--
-- ★ AND IT IS THE ONLY ROW THAT DOES ANYTHING.  The other 52 are
--   `singleId` — which is why this function is small even though the
--   knot has 53 constructors.
------------------------------------------------------------------------

singleVs : {Γ : Cx} → RTm Γ
singleVs =
  lam (lam (lam (lam
    (Tm-varK (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                   (symN (predTm (snd (var (vs (vs (vs vz))))))
                         (predN (snd (var (vs (vs (vs vz)))))
                                (fst (snd (snd (snd (var (vs (vs vz)))))))))
                   (fst (snd (var (vs (vs vz))))))))))

⊢singleVs : {Γ : Ctx} →
            Γ ⊢ singleVs ∷ imethTy KnotD IPair tagVar-vs cVar-vs singleMotK
⊢singleVs =
  ⊢methLam KnotD IPair tagVar-vs cVar-vs KnotWf cVar-vsWf ⊢IPair ⊢singleMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢pred (⊢snd (⊢var (there (there here)))))))
          (⊢Tm-varKv _ dsi tx))
  where
    dp  = ⊢var (there (there here))
    dm  = elAsNat (⊢fst dp)
    dsi = ⊢pred (⊢snd (⊢var (there (there (there here)))))
    deq = ⊢symN (⊢pred (⊢snd (⊢var (there (there (there here))))))
                dm
                (⊢fordPredN (⊢snd (⊢var (there (there (there here)))))
                            dm
                            (fordAs (⊢fst (⊢snd (⊢snd (⊢snd dp))))))
    tx  = fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                        (natAsEl dm) (natAsEl dsi) deq
                        (toMu (⊢fst (⊢snd dp))))

------------------------------------------------------------------------
-- ★★★ THE TUPLE — 51 computed rows, then `cVar-vz` and `cVar-vs`.
--
-- ⚠ `cVar-vz` TAKES THE IDENTITY TOO.  Its own field is the ford; there
--   is no variable left to look up, so `λ u. u` is exactly right — the
--   substitution returns what it was given.  Only `cVar-vs` walks.
------------------------------------------------------------------------

singleTail : {Γ : Cx} → RTm Γ
singleTail = pair singleId (pair singleVs unit)

singleMethsK : {Γ : Cx} → RTm Γ
singleMethsK = methsFrom (cdTake 51 KnotD) singleId singleTail

------------------------------------------------------------------------
-- ★★★ `single`, AS AN ELIMINATOR — and then as a substitution.
--
--     singleSK i x : Tm (pred (snd i)) → Tm (pred (snd i))
--     singleK n u  : SubTy (nsuc n) n
------------------------------------------------------------------------

singleSK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
singleSK i x = ielim KnotD i singleMethsK x

singleK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
singleK n u = lam (app (singleSK (pair sVar (nsuc (renTm vs n))) (var vz))
                       (renTm vs u))
