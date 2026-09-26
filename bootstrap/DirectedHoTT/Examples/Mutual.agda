------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ A MUTUAL FAMILY, AS ONE TAGGED DESCRIPTION.
--
-- Two sorts that mention each other:
--
--        ι   :                 Ty          arr : Ty → Ty → Ty
--        c   :                 Tm          ann : Tm → Ty → Tm
--                                                      ↑ THE KNOT
--
-- ★ WHY THIS FILE EXISTS.  PLAN-INDEXED §5 item 7 (dogfooding proper)
--   is gated on `RTm` being a KERNEL TYPE, and `RTm` is not one family
--   but a knot of six that reference each other — `RTm ↔ RTy ↔ Desc ↔
--   DCon`, `IDesc ↔ ICon ↔ RTm`, `Var`.  §12 closed the part of that
--   which needed a KERNEL ROW (`icw-imu`, a field whose type is another
--   family).  This file settles the part that does not:
--
--   ⇒ **MUTUALITY NEEDS NO KERNEL CHANGE AT ALL.**  It is an ENCODING:
--     one description over a TAG-EXTENDED index, `0 = Ty`, `1 = Tm`.
--     Cross-sort references become `tρ` at a CONSTANT index, and each
--     constructor's fixed target is Forded exactly as `Vec`'s is.
--
-- ⚠ THIS IS A NEGATIVE RESULT ABOUT SCOPE, and that is its value.  The
--   knot looked like it might need mutual DESCRIPTIONS — a second
--   kernel construct, with its own nine-module cascade.  It does not.
--   `ielim` over the tagged family IS mutual induction: one motive
--   quantified over the tag, one method per constructor of either sort,
--   and the IH at a cross-sort field is the recursor at the OTHER tag.
--
-- ⚠ WHAT IT DOES NOT SETTLE: the tag here is a NUMERAL, so the family
--   is inhabited only at `0` and `1` and nothing rules out a stray
--   index.  That costs nothing — no constructor targets any other tag,
--   so `TT 2` is empty for the same reason `Vec`'s off-index cases are
--   (see `Examples/Vec.no-cons-at-zero`).  A tight two-element tag
--   would need `Bool` in `U`, which buys no theorem here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Mutual where
open import normalizer.Syntax.Types using ( _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-nsuc )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Dₗ; conₗ; methₗ; selF; selF-β; nth-z; nth-s; MethK
        ; PerK; []ₘ; _∷ₘ_; ⊢methₗ )
open import DirectedHoTT.Lib.Tel

------------------------------------------------------------------------
-- 0. The index CODE: THE SORT TAG.  `0` is the type sort, `1` the term sort.
------------------------------------------------------------------------

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

sortTy sortTm : {Γ : Cx} → RTm Γ
sortTy = nzero
sortTm = nsuc nzero

⊢sTy : {Γ : Ctx} → Γ ⊢ nzero ∷ El ⌜Nat⌝
⊢sTy = toI ⊢nzero

⊢sTm' : {Γ : Ctx} → Γ ⊢ sortTm ∷ El ⌜Nat⌝
⊢sTm' = toI (⊢nsuc ⊢nzero)

------------------------------------------------------------------------
-- 1. THE DESCRIPTION — four constructors across two sorts, as
--    telescopes over the tag `s` (`var vz`).
--
-- ⚠ EVERY recursive field sits at a CLOSED tag (`0` or `1`), never at a
--   function of the ambient one; each constructor's fixed target is a
--   constant, so it FORDS (D074: computed targets ford explicitly).
------------------------------------------------------------------------

sortIs : {Γ : Cx} → RTm (Γ ∙) → Tel (Γ ∙)
sortIs s = tσ (⌜Id⌝ ⌜Nat⌝ (var vz) s) tι

baseT arrT cT annT : {Γ : Cx} → Tel (Γ ∙)
baseT = sortIs sortTy                                     -- ι   : Ty
arrT  = tρ sortTy (tρ sortTy (sortIs sortTy))             -- arr : Ty → Ty → Ty
cT    = sortIs sortTm                                     -- c   : Tm
-- ★★★ ann : Tm → Ty → Tm — THE CROSS-SORT FIELD: one `tρ` at each tag
annT  = tρ sortTm (tρ sortTy (sortIs sortTm))

TTs : {Γ : Cx} → Tels (Γ ∙) 4
TTs = baseT ∷ᵗ arrT ∷ᵗ cT ∷ᵗ annT ∷ᵗ []ᵗ

TTD : {Γ : Cx} → RTm Γ
TTD = Dₗ ⌜ TTs ⌝ₛ

TT : {Γ : Cx} → RTm Γ → RTy Γ
TT s = IMu ⌜Nat⌝ TTD s

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS.
------------------------------------------------------------------------

sortOK : {Γ : Ctx} {i s : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El ⌜Nat⌝ → Γ ⊢ s ∷ El ⌜Nat⌝ →
         TelOK Γ ⌜Nat⌝ (tσ (⌜Id⌝ ⌜Nat⌝ i s) tι)
sortOK di ds = ok-σ (⊢⌜Id⌝ ⊢⌜Nat⌝ di ds) ok-ι

module _ {Γ : Ctx} where
  private
    v : (Γ ▹ El ⌜Nat⌝) ⊢ var vz ∷ El ⌜Nat⌝
    v = ⊢var here

  baseOK : TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ baseT
  baseOK = sortOK v ⊢sTy

  arrOK : TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ arrT
  arrOK = ok-ρ ⊢sTy (ok-ρ ⊢sTy (sortOK v ⊢sTy))

  cOK : TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ cT
  cOK = sortOK v ⊢sTm'

  annOK : TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ annT
  annOK = ok-ρ ⊢sTm' (ok-ρ ⊢sTy (sortOK v ⊢sTm'))

TTOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ TTs
TTOK = baseOK ∷ᵒ arrOK ∷ᵒ cOK ∷ᵒ annOK ∷ᵒ []ᵒ

⊢TTD : {Γ : Ctx} → Γ ⊢ TTD ∷ DescF ⌜Nat⌝
⊢TTD = ⊢Dₜ ⊢⌜Nat⌝ TTOK

------------------------------------------------------------------------
-- 3. THE CONSTRUCTORS, across both sorts.  ⚠ ALL indices CLOSED — no
--    weakening appears anywhere, the encoding's dividend over `Scoped`.
------------------------------------------------------------------------

tbase tc : {Γ : Cx} → RTm Γ
tbase = conₗ zero (pair (idrefl ⌜Nat⌝ sortTy) unit)
tc    = conₗ (suc (suc zero)) (pair (idrefl ⌜Nat⌝ sortTm) unit)

tarr tann : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
tarr a b = conₗ (suc zero) (pair a (pair b (pair (idrefl ⌜Nat⌝ sortTy) unit)))
tann t a = conₗ (suc (suc (suc zero))) (pair t (pair a (pair (idrefl ⌜Nat⌝ sortTm) unit)))

module _ {Γ : Ctx} where
  private
    refl' : {s : RTm ⌊ Γ ⌋} → Γ ⊢ s ∷ El ⌜Nat⌝ → Γ ⊢ idrefl ⌜Nat⌝ s ∷ El (⌜Id⌝ ⌜Nat⌝ s s)
    refl' {s} ds = ⊢conv (⊢idrefl ⊢⌜Nat⌝ ds) (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ s s)))
    ford : {s : RTm ⌊ Γ ⌋} → Γ ⊢ s ∷ El ⌜Nat⌝ →
           Γ ⊢ pair (idrefl ⌜Nat⌝ s) unit ∷ El (dpay ⌜Nat⌝ TTD ⌜ tσ (⌜Id⌝ ⌜Nat⌝ s s) tι ⌝ᵗ)
    ford ds = ⊢payσ ⊢⌜Nat⌝ ⊢TTD (sortOK ds ds) (refl' ds) (⊢payι ⊢⌜Nat⌝ ⊢TTD ⊢unit)

  ⊢tbase : Γ ⊢ tbase ∷ TT sortTy
  ⊢tbase = ⊢conₜ ⊢⌜Nat⌝ TTOK nthᵗ-z ⊢sTy (ford ⊢sTy)

  ⊢tc : Γ ⊢ tc ∷ TT sortTm
  ⊢tc = ⊢conₜ ⊢⌜Nat⌝ TTOK (nthᵗ-s (nthᵗ-s nthᵗ-z)) ⊢sTm' (ford ⊢sTm')

  ⊢tarr : {a b : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ TT sortTy → Γ ⊢ b ∷ TT sortTy → Γ ⊢ tarr a b ∷ TT sortTy
  ⊢tarr da db =
    ⊢conₜ ⊢⌜Nat⌝ TTOK (nthᵗ-s nthᵗ-z) ⊢sTy
      (⊢payρ ⊢⌜Nat⌝ ⊢TTD (ok-ρ ⊢sTy (ok-ρ ⊢sTy (sortOK ⊢sTy ⊢sTy))) da
        (⊢payρ ⊢⌜Nat⌝ ⊢TTD (ok-ρ ⊢sTy (sortOK ⊢sTy ⊢sTy)) db (ford ⊢sTy)))

  -- ★★★ THE CROSS-SORT CONSTRUCTOR: a `Tm` field and a `Ty` field
  ⊢tann : {t a : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ TT sortTm → Γ ⊢ a ∷ TT sortTy → Γ ⊢ tann t a ∷ TT sortTm
  ⊢tann dt da =
    ⊢conₜ ⊢⌜Nat⌝ TTOK (nthᵗ-s (nthᵗ-s (nthᵗ-s nthᵗ-z))) ⊢sTm'
      (⊢payρ ⊢⌜Nat⌝ ⊢TTD (ok-ρ ⊢sTm' (ok-ρ ⊢sTy (sortOK ⊢sTm' ⊢sTm'))) dt
        (⊢payρ ⊢⌜Nat⌝ ⊢TTD (ok-ρ ⊢sTy (sortOK ⊢sTm' ⊢sTm')) da (ford ⊢sTm')))

-- `c : ι` — the smallest term that uses both sorts.
annCι : {Γ : Cx} → RTm Γ
annCι = tann tc tbase

⊢annCι : ◇ ⊢ annCι ∷ TT sortTm
⊢annCι = ⊢tann ⊢tc ⊢tbase

------------------------------------------------------------------------
-- 4. ★★★ MUTUAL INDUCTION IS ONE `ielim`.
--
-- `depth : TT s → Nat`, one motive (`Nat`, constant), one method per
-- constructor OF EITHER SORT.  ⚠ `mann` deliberately reads its SECOND
-- hypothesis — the one at the `Ty` field — so the recursion CROSSES
-- SORTS: the method reached at tag `1` consumes the recursor's result at
-- tag `0`, from the same method tuple.
------------------------------------------------------------------------

mι marr mc mann : {Γ : Cx} → RTm Γ
mι   = lam (lam (lam (nsuc nzero)))
marr = lam (lam (lam (nsuc (fst (var vz)))))
mc   = lam (lam (lam (nsuc nzero)))
mann = lam (lam (lam (nsuc (fst (snd (var vz))))))

TTMs : {Γ : Cx} → Cons Γ 4
TTMs = mι ∷ marr ∷ mc ∷ mann ∷ []

depth : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
depth s t = ielim TTD s (methₗ TTMs) t

module _ {Γ : Ctx} where
  ⊢mι : Γ ⊢ mι ∷ MethK ⌜Nat⌝ TTD Nat ⌜ baseT ⌝ᵗ zero
  ⊢mι = ⊢methT {T = baseT} {s = conₗ zero (var (vs vz))} ⊢⌜Nat⌝ ⊢TTD ty-Nat baseOK (⊢nsuc ⊢nzero)

  ⊢marr : Γ ⊢ marr ∷ MethK ⌜Nat⌝ TTD Nat ⌜ arrT ⌝ᵗ (suc zero)
  ⊢marr = ⊢methT {T = arrT} {s = conₗ (suc zero) (var (vs vz))} ⊢⌜Nat⌝ ⊢TTD ty-Nat arrOK
            (⊢nsuc (⊢fst (⊢var here)))

  ⊢mc : Γ ⊢ mc ∷ MethK ⌜Nat⌝ TTD Nat ⌜ cT ⌝ᵗ (suc (suc zero))
  ⊢mc = ⊢methT {T = cT} {s = conₗ (suc (suc zero)) (var (vs vz))} ⊢⌜Nat⌝ ⊢TTD ty-Nat cOK (⊢nsuc ⊢nzero)

  -- ★★★ the cross-sort method: `fst (snd h)` is the recursor's value at the OTHER TAG
  ⊢mann : Γ ⊢ mann ∷ MethK ⌜Nat⌝ TTD Nat ⌜ annT ⌝ᵗ (suc (suc (suc zero)))
  ⊢mann = ⊢methT {T = annT} {s = conₗ (suc (suc (suc zero))) (var (vs vz))} ⊢⌜Nat⌝ ⊢TTD ty-Nat annOK
            (⊢nsuc (⊢fst (⊢snd (⊢var here))))

  perTT : PerK Γ ⌜Nat⌝ TTD Nat (selF ⌜ TTs ⌝ₛ) zero TTMs
  perTT = (selF-β {Cs = ⌜ TTs ⌝ₛ} nth-z , ⊢mι)
       ∷ₘ ((selF-β {Cs = ⌜ TTs ⌝ₛ} (nth-s nth-z) , ⊢marr)
       ∷ₘ ((selF-β {Cs = ⌜ TTs ⌝ₛ} (nth-s (nth-s nth-z)) , ⊢mc)
       ∷ₘ ((selF-β {Cs = ⌜ TTs ⌝ₛ} (nth-s (nth-s (nth-s nth-z))) , ⊢mann) ∷ₘ []ₘ)))

  ⊢depth : {s t : RTm ⌊ Γ ⌋} → Γ ⊢ s ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ TT s → Γ ⊢ depth s t ∷ Nat
  ⊢depth ds dt =
    ⊢ielim ⊢⌜Nat⌝ ⊢TTD ty-Nat (⊢methₗ ⊢⌜Nat⌝ (allD (⊢wk ⊢⌜Nat⌝) TTOK) ty-Nat perTT) ds dt

------------------------------------------------------------------------
-- 5. ★★★ …AND IT RUNS ACROSS THE SORTS.
--
-- `depth 1 (ann c ι) ⟶* 2`.  The recursor is entered at tag `1` and the
-- hypotheses' SECOND component re-enters it at tag `0`, with the SAME
-- method tuple: a mutual recursion, and the kernel never learned the word.
------------------------------------------------------------------------

depth-base : {Γ : Cx} → depth {Γ} sortTy tbase ⟶* nsuc nzero
depth-base =
  ⟶*-trans (ιT {T = baseT} (nth-⌜⌝ {Ts = TTs} nthᵗ-z) nth-z)
    (step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) (step (β _ _) done)))

depth-annCι : {Γ : Cx} → depth {Γ} sortTm annCι ⟶* nsuc (nsuc nzero)
depth-annCι =
  ⟶*-trans (ιT {T = annT} (nth-⌜⌝ {Ts = TTs} (nthᵗ-s (nthᵗ-s (nthᵗ-s nthᵗ-z))))
                          (nth-s (nth-s (nth-s nth-z))))
    (step (ξ-appˡ (ξ-appˡ (β _ _)))
    (step (ξ-appˡ (β _ _))
    (step (β _ _)
    -- project the SECOND hypothesis — the one at the other tag
    (⟶*-nsuc
      (step (ξ-fst (βsnd _ _))
      (step (βfst _ _)
      (step (ξ-ielimᵗ (ξ-fst (βsnd _ _)))
      (step (ξ-ielimᵗ (βfst _ _))
      -- ★★★ HERE: the recursor fires again, at tag 0, on `ι`
        depth-base))))))))
