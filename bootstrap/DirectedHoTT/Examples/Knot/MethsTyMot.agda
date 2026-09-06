------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `methsTyFrom`'s MOTIVE, JUNK ROW AND DESCENT.
--
-- ⚠ THE ROWS THEMSELVES ARE NOT HERE, and that is `Knot/IPayTyMot`'s
--   MEASURED rule, not tidiness: inlining one half of a row's answer took
--   that module 9.7s → 20.6s, and both halves OOM-KILLED at 5.5 GB.
--   Naming the descent at ABSTRACT `RTm`s elaborates its equations once,
--   against variables; a call site then only instantiates.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.MethsTyMot where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IMu; εwkTy; app; unit; ielim; nzero; nsuc; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢lam; ⊢app; ⊢nzero; ⊢nsuc
        ; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; ξ-pairʳ; βsnd; done; step; single; wk-single; iinst )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import normalizer.Syntax.Types using ( cong; trans; sym )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Lib.Wk using ( towerA; towerJ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sDesc; ⊢sDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-UnitK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Ty-UnitKv )

------------------------------------------------------------------------
-- ★★★ THE MOTIVE, AND ITS ARGUMENT ORDER IS THE WHOLE DESIGN.
--
--     methsTyFrom D M j dnil    = Unit
--     methsTyFrom D M j (C ◃ E) = Σ' (methTy D j C M)
--                                    (renTy vs (methsTyFrom D M (suc j) E))
--
-- ⚠⚠ `n` IS A Π ARGUMENT, NOT `snd ⟨i⟩`, AND THAT IS WHAT KEEPS THE
--   TOWER AT FOUR RUNGS.  `Lib/Wk` says of `towerA`/`towerJ`: "these are
--   iterates of one lemma and want INDEXING, not listing.  Two rungs is
--   where it stops being worth it."  A motive whose RESULT reads the
--   index needs one rung per Π binder before it — three passengers would
--   put the result at `var (vs⁴ vz)` and demand a FIFTH rung nobody has.
--   Reading the FIRST Π binder instead pins the result at `var (vs³ vz)`,
--   which is exactly `towerJ`.  ★ `Knot/IPayTyMot` found this first and
--   its header states the rule: "put `σ` as early as its dependency on
--   `n` allows — SECOND — and the tower is [short]".
------------------------------------------------------------------------

methsTyMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
methsTyMotK =
  Π Nat                                                        -- n
   (Π (IMu KnotD IPair (pair sDesc (var vz)))                   -- D
    (Π (IMu KnotD IPair (pair sTy (nsuc (var (vs vz)))))        -- M
     (Π Nat                                                     -- j
        (IMu KnotD IPair (pair sTy (var (vs (vs (vs vz)))))))))

⊢methsTyMotK : {Γ : Ctx} →
               ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty methsTyMotK
⊢methsTyMotK =
  ty-Π ty-Nat
   (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢var here)))
    (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢nsuc (⊢var (there here)))))
     (ty-Π ty-Nat
        (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★ THE JUNK ROW — and for `cDesc-nil` it is the RIGHT answer, not junk:
--   `methsTyFrom D M j dnil = Unit`.
-- ⚠ 3 + #passengers lams, the same count `Knot/IPayTyMot`'s has.
------------------------------------------------------------------------

methsTyJunk : {Γ : Cx} → RTm Γ
methsTyJunk = lam (lam (lam (lam (lam (lam (lam Ty-UnitK))))))

⊢methsTyJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
               IConWf KnotD IPair (◇ ▹ IPair) C →
               Γ ⊢ methsTyJunk ∷ imethTy KnotD IPair k C methsTyMotK
⊢methsTyJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢methsTyMotK
    (⊢lam ty-Nat
      (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢var here)))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢nsuc (⊢var (there here)))))
          (⊢lam ty-Nat
            (⊢Ty-UnitKv _ (⊢var (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★★★ THE DESCENT THROUGH THE FOUR Π BINDERS, ONCE — and it is the
--   wrapper too, exactly as `⊢ipayAppK` is.
------------------------------------------------------------------------

⊢methsAppK : {Γ : Ctx} {dd u h n DD MM j : RTm ⌊ Γ ⌋} →
             Γ ⊢ h ∷ iinst (pair sDesc dd) u methsTyMotK →
             Γ ⊢ n ∷ Nat → Γ ⊢ DD ∷ K (pair sDesc n) →
             Γ ⊢ MM ∷ K (pair sTy (nsuc n)) → Γ ⊢ j ∷ Nat →
             Γ ⊢ app (app (app (app h n) DD) MM) j ∷ K (pair sTy n)
⊢methsAppK {dd = dd} {u = u} {n = n} {DD = DD} {MM = MM} {j = j}
           dh dn dD dM dj =
  ⊢-cast (cong (λ z → K (pair sTy z)) (towerJ j MM DD n))
    -- ⚠ NO CAST ON `D`.  Its domain reads `var vz` — the FIRST Π binder —
    --   and `extS σ vz = var vz` definitionally at every rung, so the two
    --   `iinst` substitutions slide past and `single n` finishes it.
    --   ★ This is the dividend of reading a Π binder instead of the index:
    --     `Knot/IPayTyMot` needed `towerA` here because its `σ` domain
    --     mentions `snd ⟨i⟩` as well.
    (⊢app (⊢app (⊢app (⊢app dh dn) dD)
                (⊢-cast (cong (λ z → K (pair sTy (nsuc z)))
                              (sym (wk-single {v = DD} n)))
                        dM))
          dj)
