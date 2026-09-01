------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `pwBody`, OBJECT-LEVEL.
--
--     pwBody (⌜Π⌝ γ δ)     = δ
--     pwBody (⌜Hom⌝ C a b) = ⌜Hom⌝ (pwBody C) (app (w a) vz) (app (w b) vz)
--     pwBody t             = renTm vs t
--
-- ★★★ IT IS **WEAKENING WITH TWO ROWS OVERRIDDEN**, and that is the whole
--   design.  The eliminator runs over all 53 rows — `Ty` and `Var` ones
--   too — so the motive must be SORT-PRESERVING, which is `Lib/IWk`'s
--   `Mot D I = IMu D I (sh ⟨i⟩)` exactly; and the default clause
--   `renTm vs t` IS `wkK`'s method.  ⇒ only `⌜Π⌝` (row 20) and `⌜Hom⌝`
--   (row 22) are this module's own work.
--
-- ⚠ WHICH IS WHY `Lib/IWk` GREW `wkdTake`.  `decDesc` classifies as far
--   as it can and walks straight past row 20; a customer that is
--   weakening EXCEPT somewhere needs to stop the walk where IT says.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.PwBody where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; fst; snd; pair; nsuc
        ; ⌜IMu⌝; ⌜Nat⌝; jsub; IDesc; ICon; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢fst; ⊢snd; ⊢nsuc; ⊢jsub; ⊢⌜IMu⌝; imethTy
        ; βfst; βsnd; ξ-nsuc; ξ-pairˡ; ξ-pairʳ )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Lib.IWk
  using ( Mot; iwkMethsFrom; ⊢iwkMethsFrom; wkdTake; decDesc; wkdRest
        ; imethsTyFromMot-wf; wfDrop; splDrop )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( symN; ⊢symN )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cTm-cPi; cTm-cHom )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cTm-cPiWf; cTm-cHomWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagTm-cPi; tagTm-cHom )
open import DirectedHoTT.Examples.Knot.Wk
  using ( ⊢MotK; wkK; ⊢wkK; wkTail; ⊢wkTail; ⊢shIPair )
open import DirectedHoTT.Examples.Knot.Pw
  using ( D20; D21; D22; D23; spl20; spl21; spl22; spl23 )
open import DirectedHoTT.Lib.IPay using ( idwfDrop; Split; spl-nil )
open import DirectedHoTT.Spec.Typing using ( imethsTy; imethsTyFrom; ⊢pair; ⊢ielim )
open import DirectedHoTT.Spec.Syntax using ( ielim )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast; ren-ty )
open import normalizer.Syntax.Types using ( sym )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Lib.IWk using ( sh )
open import DirectedHoTT.Spec.Typing using ( wk-single )
open import DirectedHoTT.Spec.Syntax using ( Σ'; Nat )
open import normalizer.Syntax.Types using ( cong )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-cHomK; Tm-appK; Tm-varK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-cHomKv; ⊢Tm-appKv; ⊢Tm-varKv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; ⊢Var-vzKt )

------------------------------------------------------------------------
-- ★★ `⌜Π⌝` — RETURN THE CODOMAIN, and pay the row's SORT FORD.
--
-- The row is
--     iρ (sTm , snd ⟨i⟩) (iρ (sTm , nsuc (snd ⟨i⟩)) (iκ (⌜Id⌝ ⌜Nat⌝ (fst ⟨i⟩) sTm) iι))
-- so `δ` already sits at `nsuc (snd ⟨i⟩)` — the depth the motive wants.
-- ⚠ WHAT DOES NOT MATCH IS THE **SORT**: the motive asks for
--   `sh ⟨i⟩ = (fst ⟨i⟩ , nsuc (snd ⟨i⟩))` and `δ` is at `sTm`.  Those
--   agree only through the row's own ford, and a ford is PROPOSITIONAL —
--   so this is `jsub`, not `ixConv`, which converts along a REDUCTION.
--
-- ★ payload = (γ , (δ , (ford , unit))), so `δ = fst (snd p)` and the
--   ford is `fst (snd (snd p))`.
------------------------------------------------------------------------

pwPi : {Γ : Cx} → RTm Γ
pwPi =
  lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair
             (pair (var vz) (nsuc (snd (var (vs (vs (vs vz))))))))
          (symN (fst (var (vs (vs vz)))) (fst (snd (snd (var (vs vz))))))
          (fst (snd (var (vs vz)))))))

⊢pwPi : {Γ : Ctx} →
        Γ ⊢ pwPi ∷ imethTy KnotD IPair tagTm-cPi cTm-cPi (Mot KnotD IPair)
⊢pwPi =
  ⊢methLam KnotD IPair tagTm-cPi cTm-cPi KnotWf cTm-cPiWf ⊢IPair ⊢MotK
    (fromMu (⊢jsub dmot (natAsEl ⊢sTm) (natAsEl dfi) dsym
                   (toMu (⊢fst (⊢snd dp)))))
  where
    dix  = ⊢var (there (there here))
    dp   = ⊢var (there here)
    dfi  = ⊢fst dix
    dmot = ⊢⌜IMu⌝ KnotWf (⊢ixP (elAsNat (⊢var here))
                               (⊢nsuc (⊢snd (⊢var (there (there (there here)))))))
    dsym = ⊢symN dfi ⊢sTm (fordAs (⊢fst (⊢snd (⊢snd dp))))

------------------------------------------------------------------------
-- ★★★ `⌜Hom⌝` — THE ROW THAT RECURSES, and the only real work here.
--
--     pwBody (⌜Hom⌝ C a b) = ⌜Hom⌝ (pwBody C) (app (w a) vz) (app (w b) vz)
--
-- ⚠ THREE DIFFERENT SOURCES IN ONE TERM: the code comes from the **IH**
--   (`pwBody C`, already computed), the endpoints from the **PAYLOAD**
--   (weakened, then applied to the new variable).  A fold that only ever
--   read its IH tuple could not write this row.
--
-- ⚠ AND EVERY PIECE ARRIVES AT `sh (sTm , d)` RATHER THAN
--   `(sTm , nsuc d)` — `sh` is a projection pair, so each needs the same
--   two β-steps (`βfst`, `βsnd`).  That is the `WK` post the emitter's
--   table already applies to `⊢wkK`; here it is written out.
------------------------------------------------------------------------

-- ⚠ THE THREE BINDERS, BY NAME.  Inside a method body `⊢methLam` has
--   bound the index, the payload and the IH tuple, in that order, so
--   `var vz` is the IH and `var (vs (vs vz))` the index.  Writing the
--   de Bruijn spines inline is how the first version of this term ended
--   up unbalanced.
pwIx pwPay pwIH : {Γ : Cx} → RTm (Γ ∙ ∙ ∙)
pwIx  = var (vs (vs vz))
pwPay = var (vs vz)
pwIH  = var vz

-- the row's depth `d`, and one application `app (w x) vz` at `nsuc d`
pwDep : {Γ : Cx} → RTm (Γ ∙ ∙ ∙)
pwDep = snd pwIx

pwApp : {Γ : Cx} → RTm (Γ ∙ ∙ ∙) → RTm (Γ ∙ ∙ ∙)
pwApp x = Tm-appK (wkK (pair sTm pwDep) x) (Tm-varK (Var-vzK pwDep))

pwHom : {Γ : Cx} → RTm Γ
pwHom =
  lam (lam (lam
    (jsub (⌜IMu⌝ KnotD IPair (pair (var vz) (nsuc (snd (var (vs (vs (vs vz))))))))
          (symN (fst pwIx) (fst (snd (snd (snd pwPay)))))
          (Tm-cHomK (fst pwIH)
                    (pwApp (fst (snd pwPay)))
                    (pwApp (fst (snd (snd pwPay))))))))

⊢pwHom : {Γ : Ctx} →
         Γ ⊢ pwHom ∷ imethTy KnotD IPair tagTm-cHom cTm-cHom (Mot KnotD IPair)
⊢pwHom =
  ⊢methLam KnotD IPair tagTm-cHom cTm-cHom KnotWf cTm-cHomWf ⊢IPair ⊢MotK
    (fromMu (⊢jsub dmot (natAsEl ⊢sTm) (natAsEl dfi) dsym
                   (toMu (⊢Tm-cHomKv _ (⊢nsuc dd) dihC dapa dapb))))
  where
    dix  = ⊢var (there (there here))
    dp   = ⊢var (there here)
    dih  = ⊢var here
    dd   = ⊢snd dix
    dfi  = ⊢fst dix
    -- ★ the two β-steps, once — every component needs them.
    shred : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {d : RTm ⌊ Γ ⌋} →
            Γ ⊢ t ∷ K (pair (fst (pair sTm d)) (nsuc (snd (pair sTm d)))) →
            Γ ⊢ t ∷ K (pair sTm (nsuc d))
    shred x = muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _))) (muFwd (ξ-pairˡ (βfst _ _)) x)
    dihC = shred (⊢fst dih)
    da   = ⊢fst (⊢snd dp)
    db   = ⊢fst (⊢snd (⊢snd dp))
    -- ⚠ INLINED, NOT A LOCAL `dap`.  A `where`-bound helper with an
    --   implicit term argument left `_t` unsolved at both call sites —
    --   the payload projection is not determined by the RESULT type.
    dapa = ⊢Tm-appKv _ (⊢nsuc dd) (shred (⊢wkK (⊢ixP ⊢sTm dd) da))
                     (⊢Tm-varKv _ (⊢nsuc dd) (⊢Var-vzKt dd))
    dapb = ⊢Tm-appKv _ (⊢nsuc dd) (shred (⊢wkK (⊢ixP ⊢sTm dd) db))
                     (⊢Tm-varKv _ (⊢nsuc dd) (⊢Var-vzKt dd))
    dmot = ⊢⌜IMu⌝ KnotWf (⊢ixP (elAsNat (⊢var here))
                               (⊢nsuc (⊢snd (⊢var (there (there (there here)))))))
    dsym = ⊢symN dfi ⊢sTm (fordAs (⊢fst (⊢snd (⊢snd (⊢snd dp)))))

------------------------------------------------------------------------
-- ★★★ THE TUPLE — WEAKENING'S WALK, INTERRUPTED TWICE.
--
--     rows  0–19   `decDesc`-computed (weakening)
--     row   20     `pwPi`      ← override
--     row   21     computed    (`⌜Σ⌝` takes the default)
--     row   22     `pwHom`     ← override
--     rows  23–50  computed, then `wkTail`'s two `Var` rows
--
-- ⚠ ROW 21 IS NOT WRITTEN OUT.  Extracting its `WkCon` from
--   `decCon vz cTm-cSg` would need the `nothing` case discharged; a
--   ONE-ROW bounded walk (`wkdTake 1 D21`) computes the very same method
--   and needs no such thing.
------------------------------------------------------------------------

pwBodyMethsK : {Γ : Cx} → RTm Γ
pwBodyMethsK =
  iwkMethsFrom 0 (wkdTake 20 KnotD)
    (pair pwPi
      (iwkMethsFrom 21 (wkdTake 1 D21)
        (pair pwHom
          (iwkMethsFrom 23 (decDesc D23) wkTail))))

⊢pwBodyMethsK : {Γ : Ctx} →
                Γ ⊢ pwBodyMethsK ∷ imethsTy KnotD IPair (Mot KnotD IPair) KnotD
⊢pwBodyMethsK =
  ⊢iwkMethsFrom KnotD IPair (wkdTake 20 KnotD) spl-nil KnotWf KnotWf
                ⊢IPair ⊢shIPair _
    (⊢pair (ren-ty (imethsTyFromMot-wf KnotD IPair 21 D21 KnotWf
                      (idwfDrop spl21 KnotWf) ⊢IPair ⊢shIPair) there)
           ⊢pwPi
           (⊢-cast (sym (wk-singleTy {v = pwPi}
                           (imethsTyFrom KnotD IPair (Mot KnotD IPair) 21 D21)))
             (⊢iwkMethsFrom KnotD IPair (wkdTake 1 D21) spl21 KnotWf
                            (idwfDrop spl21 KnotWf) ⊢IPair ⊢shIPair _
               (⊢pair (ren-ty (imethsTyFromMot-wf KnotD IPair 23 D23 KnotWf
                                 (idwfDrop spl23 KnotWf) ⊢IPair ⊢shIPair) there)
                      ⊢pwHom
                      (⊢-cast (sym (wk-singleTy {v = pwHom}
                                      (imethsTyFrom KnotD IPair (Mot KnotD IPair) 23 D23)))
                        (⊢iwkMethsFrom KnotD IPair (decDesc D23) spl23 KnotWf
                                       (idwfDrop spl23 KnotWf) ⊢IPair ⊢shIPair
                                       wkTail ⊢wkTail))))))

------------------------------------------------------------------------
-- ★★ `pwBody`, AS AN ELIMINATOR.  Same shape as `wkK` — the motive is
--   the same, so the result index is `sh ⟨i⟩` and the cast is `wkK`'s.
------------------------------------------------------------------------

pwBodyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
pwBodyK i t = ielim KnotD i pwBodyMethsK t

-- ★ SAME CAST AS `⊢wkK` — same motive, so the same `wk-single` round
--   trip on the result index.
⊢pwBodyK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
           Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ pwBodyK i t ∷ K (sh i)
⊢pwBodyK {i = i} di dt =
  ⊢-cast (cong (λ z → K (sh z)) (wk-single i))
         (⊢ielim KnotWf ⊢MotK di ⊢pwBodyMethsK dt)
