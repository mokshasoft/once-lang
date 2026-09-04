------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `ipayTy`'s MOTIVE, JUNK ROW AND THE THREE
-- ABSTRACT LEMMAS its rows are built from.
--
--     ipayTy D I σ iι       = Unit
--     ipayTy D I σ (iρ j C) = Σ' (IMu D I (subTm σ j)) (ipayTy D I (extS σ) C)
--     ipayTy D I σ (iκ κ C) = Σ' (El (subTm σ κ))      (ipayTy D I (extS σ) C)
--
-- ★★★ THE ENVIRONMENT IS WHAT MAKES THIS DIFFERENT FROM `Knot/PayTy`.
--   `payTy` recurses with its arguments UNCHANGED and pays a `wkK` on
--   the answer.  Here `extS σ` grows BOTH ends — source and target — so
--   the recursive answer arrives at depth `n+1` ALREADY, which is
--   exactly what `Σ'`'s second component wants.  ⇒ NO `wkK` on the
--   answer at all; the weakening moved into the substitution.
--
-- ★★ FOUR PASSENGERS RIDE IN THE MOTIVE: `n`, `σ`, `D`, `I`.  Only `σ`
--   and `n` actually change, but a free variable of `Γ` cannot be used —
--   `⊢methLam` fixes the motive at a `Γ` the wrapper does not get to
--   choose — so all four ride.  `Knot/LookupD` rides one ℕ for the same
--   reason and its header records it.
--
-- ⚠ AND THE ORDER OF THE FOUR IS NOT FREE.  `σ`'s type mentions `⟨i⟩`,
--   and every Π binder BEFORE it adds one rung to the descent tower the
--   wrapper must climb (`Lib/Wk`'s `towerA`/`towerJ`).  ⇒ put `σ`
--   as early as its dependency on `n` allows — SECOND — and the tower is
--   two rungs instead of four.  `D` and `I` mention no `⟨i⟩`, so they
--   cost nothing wherever they sit.
--
-- ★ THE `iι` ROW IS THE JUNK ROW.  `ipayTy … iι = Unit` and the junk
--   answer is `Unit`, so `cICon-i` needs no method of its own: rows 49
--   and 50 are the only real ones, and they are ADJACENT.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IPayTyMot where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IDesc; εwkTy; IMu; app; fst; iρ; iκ; iι
        ; ⌜Id⌝; ⌜Nat⌝; isingle; iext; unit; _◂_; ielim; nzero; nsuc; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢fst; ⊢lam; ⊢app; ⊢unit; ⊢nzero; ⊢nsuc
        ; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim
        ; ξ-pairʳ; βsnd; done; step; single; wk-single; iinst )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import normalizer.Syntax.Types using ( cong; trans; sym )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ; ⊢methsFrom; ⊢methsCons
        ; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Lib.ICast using ( muFwd; muBwd* )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sTm; ⊢sTm; sICon; ⊢sICon
        ; sIDesc; ⊢sIDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cICon-rho; cICon-kap )
open import DirectedHoTT.Examples.Knot.Wf
  using ( KnotWf; cICon-rhoWf; cICon-kapWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagICon-rho; tagICon-kap )
open import DirectedHoTT.Examples.Knot.Ctors
  using ( Ty-UnitK; Ty-SgK; Ty-IMuK; Ty-ElK )
open import DirectedHoTT.Examples.Knot.CtorsV
  using ( ⊢Ty-UnitKv; ⊢Ty-SgKv; ⊢Ty-IMuKv; ⊢Ty-ElKv )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy; ty-SubTy; subBwd )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkKat )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK; ⊢extNK )
open import DirectedHoTT.Lib.Wk using ( towerA; towerJ )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK; ⊢subTmAtK )

------------------------------------------------------------------------
-- ★ THE MOTIVE.  `⟨i⟩` is `var (vs vz)`; only the `σ` domain reads it.
------------------------------------------------------------------------

ipayTyMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
ipayTyMotK =
  Π Nat
   (Π (SubTy (snd (var (vs (vs vz)))) (var vz))
    (Π (IMu KnotD IPair (pair sIDesc (var (vs vz))))
     (Π (IMu KnotD IPair (pair sTy nzero))
        (IMu KnotD IPair (pair sTy (var (vs (vs (vs vz))))))))) 

⊢ipayTyMotK : {Γ : Ctx} →
              ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty ipayTyMotK
⊢ipayTyMotK =
  ty-Π ty-Nat
   (ty-Π (ty-SubTy (⊢snd (⊢var (there (there here)))) (⊢var here))
    (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var (there here))))
     (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTy ⊢nzero))
        (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★ THE JUNK ROW — and for `cICon-i` it is the RIGHT answer, not junk.
------------------------------------------------------------------------

ipayTyJunk : {Γ : Cx} → RTm Γ
ipayTyJunk = lam (lam (lam (lam (lam (lam (lam Ty-UnitK))))))

⊢ipayTyJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
              IConWf KnotD IPair (◇ ▹ IPair) C →
              Γ ⊢ ipayTyJunk ∷ imethTy KnotD IPair k C ipayTyMotK
⊢ipayTyJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢ipayTyMotK
    (⊢lam ty-Nat
      (⊢lam (ty-SubTy (⊢snd (⊢var (there (there (there here))))) (⊢var here))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var (there here))))
          (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTy ⊢nzero))
            (⊢Ty-UnitKv _ (⊢var (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★★★ EVERYTHING HEAVY IS STATED AT **ABSTRACT** PIECES, AND THAT IS
--   NOT A STYLE CHOICE — IT IS WHAT MAKES THE MODULE CHECK.
--
-- ⚠⚠ MEASURED.  The row's structure alone (concrete tag, concrete
--   `cICon-rho`, junk body) is 9.7s / 0.8 GB.  Inlining ONE HALF of the
--   answer — `Ty-IMuK D I (subTmAtK …)` — takes it to 20.6s / 2.5 GB,
--   and both halves OOM-KILL at the 5.5 GB cap, with `-c` too.
--
--   The reason is `agda-cost-is-elaborated-term-size`: `subTmAtK`,
--   `extNK` and `wkK` each expand to an `ielim` over a 53-METHOD tuple,
--   and `⊢Ty-SgKv`/`⊢Ty-IMuKv` mention their arguments inside
--   `wk-single`/`sub-w` equations — so every occurrence is re-normalised
--   in a proof TYPE.  Naming the derivation at abstract `RTm`s puts a
--   `Def` between the two: the equations are elaborated ONCE, against
--   variables, and the call site only instantiates.
--
-- ★★★ AND THE ABSTRACTION PAYS TWICE.  `⊢ipayAppK` is the descent
--   through the motive's four Π binders — and it is the SAME lemma the
--   WRAPPER needs, exactly as `⊢motAppK` serves both `Knot/SubMot`'s
--   rows and `Knot/SubApp`'s `⊢subAtK`.  ⇒ the tower is climbed once in
--   the module, not once per customer.
------------------------------------------------------------------------

-- ★ applying the motive's four passengers to an IH (or to an `ielim`).
⊢ipayAppK : {Γ : Ctx} {dd u h n sb DD II : RTm ⌊ Γ ⌋} →
            Γ ⊢ h ∷ iinst (pair sICon dd) u ipayTyMotK →
            Γ ⊢ n ∷ Nat → Γ ⊢ sb ∷ SubTy dd n →
            Γ ⊢ DD ∷ K (pair sIDesc n) → Γ ⊢ II ∷ K (pair sTy nzero) →
            Γ ⊢ app (app (app (app h n) sb) DD) II ∷ K (pair sTy n)
⊢ipayAppK {dd = dd} {u = u} {n = n} {sb = sb} {DD = DD} {II = II}
          dh dn dsb dD dI =
  ⊢-cast (cong (λ z → K (pair sTy z)) (towerJ II DD sb n))
    (⊢app (⊢app (⊢app (⊢app dh dn)
                      (⊢-cast (cong (λ z → SubTy (snd z) n)
                                    (sym (towerA n u (pair sICon dd))))
                              (subBwd (βsnd sICon dd) dsb)))
                (⊢-cast (cong (λ z → K (pair sIDesc z))
                              (sym (wk-single {v = sb} n)))
                        dD))
          dI)

-- ★ the `iρ` clause's answer: `Σ' (IMu D I (subTm σ j)) <rest>`.
⊢ipayRowρ : {Γ : Ctx} {n dd sb DD II j rest : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ dd ∷ Nat → Γ ⊢ sb ∷ SubTy dd n →
            Γ ⊢ DD ∷ K (pair sIDesc n) → Γ ⊢ II ∷ K (pair sTy nzero) →
            Γ ⊢ j ∷ K (pair sTm dd) → Γ ⊢ rest ∷ K (pair sTy (nsuc n)) →
            Γ ⊢ Ty-SgK (Ty-IMuK DD II (subTmAtK dd n sb j)) rest
              ∷ K (pair sTy n)
⊢ipayRowρ dn ddd dsb dD dI dj drest =
  ⊢Ty-SgKv _ dn (⊢Ty-IMuKv _ dn dD dI (⊢subTmAtK ddd dn dsb dj)) drest

-- ★ the `iκ` clause's answer: `Σ' (El (subTm σ κ)) <rest>`.
⊢ipayRowκ : {Γ : Ctx} {n dd sb j rest : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ dd ∷ Nat → Γ ⊢ sb ∷ SubTy dd n →
            Γ ⊢ j ∷ K (pair sTm dd) → Γ ⊢ rest ∷ K (pair sTy (nsuc n)) →
            Γ ⊢ Ty-SgK (Ty-ElK (subTmAtK dd n sb j)) rest ∷ K (pair sTy n)
⊢ipayRowκ dn ddd dsb dj drest =
  ⊢Ty-SgKv _ dn (⊢Ty-ElKv _ dn (⊢subTmAtK ddd dn dsb dj)) drest
