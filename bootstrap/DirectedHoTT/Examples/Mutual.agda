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
--   ⇒ **MUTUALITY NEEDS NO KERNEL CHANGE AT ALL.**  It is ONE family
--     over `Σ (s : Fin 2) Unit`, presented BY FIBRES OVER THE SORT
--     (`Lib/Sorted`, D074): the fibre over `(s , _)` is sort `s`'s
--     constructors.  No constructor carries a sort equation — the sort
--     is where the constructor LIVES, not something it proves.
--     Cross-sort references are `tρ` at the other sort's index.
--
-- ★ `ielim` over the family IS mutual induction: the one method splits
--   the index and selects the sort (`⊢methₛ`); each sort's methods are
--   typed at `pair (tag s) j`, where the fibre computes; the hypothesis
--   at a cross-sort field is the recursor at the OTHER sort.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Mutual where
open import normalizer.Syntax.Types using ( _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-nsuc )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Metatheory.Premises using ( mot-ren; ⊢wkD )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; conₗ; tag; selF-β; nth-sub; nth-z; nth-s; lt-z; lt-s; AllD; _∷ᵈ_; []ᵈ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.Sorted
open import DirectedHoTT.Lib.TelAt
open import DirectedHoTT.Lib.TelFold using ( sizeAlg )
open import DirectedHoTT.Lib.TelFoldS using ( sortFolds; ⊢foldₛ )

------------------------------------------------------------------------
-- 0. THE INDEX: a sort, and nothing else (`J = ⌜Unit⌝`).
--    `0` is the type sort, `1` the term sort.
------------------------------------------------------------------------

I : {Γ : Cx} → RTm Γ
I = SortI ⌜Unit⌝ 2

⊢J : {Γ : Ctx} → (Γ ▹ El (⌜Fin⌝ 2)) ⊢ ⌜Unit⌝ ∷ U
⊢J = ⊢⌜Unit⌝

⊢u : {Γ : Ctx} → Γ ⊢ unit ∷ El ⌜Unit⌝
⊢u = ⊢conv ⊢unit (csymᵀ (credᵀ El-⌜Unit⌝))

sTy sTm : {Γ : Cx} → RTm Γ
sTy = pair (tag 0) unit
sTm = pair (tag 1) unit

⊢sTy ⊢sTm : {Γ : Ctx} → Γ ⊢ pair (tag 0) unit ∷ El I
⊢sTy = ⊢ixₛ ⊢J lt-z ⊢u
⊢sTm = ⊢sTy

⊢sTm' : {Γ : Ctx} → Γ ⊢ sTm ∷ El I
⊢sTm' = ⊢ixₛ ⊢J (lt-s lt-z) ⊢u

------------------------------------------------------------------------
-- 1. THE FAMILY — two constructor lists, one per sort.
------------------------------------------------------------------------

baseT arrT cT annT : {Γ : Cx} → Tel (Γ ∙)
baseT = tι                              -- ι   : Ty
arrT  = tρ sTy (tρ sTy tι)              -- arr : Ty → Ty → Ty
cT    = tι                              -- c   : Tm
annT  = tρ sTm (tρ sTy tι)              -- ★ ann : Tm → Ty → Tm, THE CROSS-SORT FIELD

TyTs TmTs : {Γ : Cx} → Tels (Γ ∙) 2
TyTs = baseT ∷ᵗ arrT ∷ᵗ []ᵗ
TmTs = cT ∷ᵗ annT ∷ᵗ []ᵗ

TTss : {Γ : Cx} → STels (Γ ∙) 2
TTss = TyTs ∷ˢᵗ TmTs ∷ˢᵗ []ˢᵗ

TTD : {Γ : Cx} → RTm Γ
TTD = Dₛₜ TTss

TT : {Γ : Cx} → RTm Γ → RTy Γ
TT s = IMu I TTD s

module _ {Γ : Ctx} where
  arrOK : TelOK (Γ ▹ El I) I arrT
  arrOK = ok-ρ ⊢sTy (ok-ρ ⊢sTy ok-ι)

  annOK : TelOK (Γ ▹ El I) I annT
  annOK = ok-ρ ⊢sTm' (ok-ρ ⊢sTy ok-ι)

TTOK : {Γ : Ctx} → AllSOK Γ I TTss
TTOK = (ok-ι ∷ᵒ arrOK ∷ᵒ []ᵒ) ∷ˢᵒ (ok-ι ∷ᵒ annOK ∷ᵒ []ᵒ) ∷ˢᵒ []ˢᵒ

⊢TTD : {Γ : Ctx} → Γ ⊢ TTD ∷ DescF I
⊢TTD = ⊢Dₛₜ ⊢J TTOK

------------------------------------------------------------------------
-- 2. THE CONSTRUCTORS — no sort equation anywhere: the index IS the sort.
------------------------------------------------------------------------

tbase tc : {Γ : Cx} → RTm Γ
tbase = conₗ zero unit
tc    = conₗ zero unit

tarr tann : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
tarr a b = conₗ (suc zero) (pair a (pair b unit))
tann t a = conₗ (suc zero) (pair t (pair a unit))

module _ {Γ : Ctx} where
  private
    ι₀ : Γ ⊢ unit ∷ El (dpay I TTD ⌜ tι ⌝ᵗ)
    ι₀ = ⊢payι (⊢SortI ⊢J) ⊢TTD ⊢unit

  ⊢tbase : Γ ⊢ tbase ∷ TT sTy
  ⊢tbase = ⊢conₛₜ ⊢J TTOK nthˢᵗ-z nthᵗ-z ⊢u ι₀

  ⊢tc : Γ ⊢ tc ∷ TT sTm
  ⊢tc = ⊢conₛₜ ⊢J TTOK (nthˢᵗ-s nthˢᵗ-z) nthᵗ-z ⊢u ι₀

  ⊢tarr : {a b : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ TT sTy → Γ ⊢ b ∷ TT sTy → Γ ⊢ tarr a b ∷ TT sTy
  ⊢tarr da db =
    ⊢conₛₜ ⊢J TTOK nthˢᵗ-z (nthᵗ-s nthᵗ-z) ⊢u
      (⊢payρ (⊢SortI ⊢J) ⊢TTD (ok-ρ ⊢sTy (ok-ρ ⊢sTy ok-ι)) da
        (⊢payρ (⊢SortI ⊢J) ⊢TTD (ok-ρ ⊢sTy ok-ι) db ι₀))

  -- ★★★ THE CROSS-SORT CONSTRUCTOR: a `Tm` field and a `Ty` field
  ⊢tann : {t a : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ TT sTm → Γ ⊢ a ∷ TT sTy → Γ ⊢ tann t a ∷ TT sTm
  ⊢tann dt da =
    ⊢conₛₜ ⊢J TTOK (nthˢᵗ-s nthˢᵗ-z) (nthᵗ-s nthᵗ-z) ⊢u
      (⊢payρ (⊢SortI ⊢J) ⊢TTD (ok-ρ ⊢sTm' (ok-ρ ⊢sTy ok-ι)) dt
        (⊢payρ (⊢SortI ⊢J) ⊢TTD (ok-ρ ⊢sTy ok-ι) da ι₀))

-- `c : ι` — the smallest term that uses both sorts.
annCι : {Γ : Cx} → RTm Γ
annCι = tann tc tbase

⊢annCι : ◇ ⊢ annCι ∷ TT sTm
⊢annCι = ⊢tann ⊢tc ⊢tbase

------------------------------------------------------------------------
-- 3. ★★★ MUTUAL INDUCTION IS ONE `ielim`.
--
-- `depth : TT s → Nat`, one method per constructor OF EITHER SORT, each
-- at its sort's index.  ⚠ `mann` reads its SECOND hypothesis — the one
-- at the `Ty` field — so the recursion CROSSES SORTS.
------------------------------------------------------------------------

mι marr mc mann : {Γ : Cx} → RTm Γ
mι   = lam (lam (nsuc nzero))
marr = lam (lam (nsuc (fst (var vz))))
mc   = lam (lam (nsuc nzero))
mann = lam (lam (nsuc (fst (snd (var vz)))))

-- one method per sort: the constructors' methods, at `(tag s , j)`
TTEs : {Γ : Cx} → Cons Γ 2
TTEs = lam (methAt (mι ∷ marr ∷ [])) ∷ lam (methAt (mc ∷ mann ∷ [])) ∷ []

depth : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
depth s t = ielim TTD s (methAt TTEs) t

module _ {Γ : Ctx} where
  -- ★ each method against its normal forms at `(tag s , j)` (`entₛ`)
  perTy : PerKAt (Γ ▹ El ⌜Unit⌝) (renTm vs I) (renTm vs TTD) Nat (ιₛ 0) _ zero (mι ∷ marr ∷ [])
  perTy = entₛ ⊢J TTOK ty-Nat nthˢᵗ-z nthᵗ-z (⊢nsuc ⊢nzero)
       ∷ₐ entₛ ⊢J TTOK ty-Nat nthˢᵗ-z (nthᵗ-s nthᵗ-z) (⊢nsuc (⊢fst (⊢var here)))
       ∷ₐ []ₐ

  -- sort 1 (Tm); `mann` reads the recursor at the OTHER sort
  perTm : PerKAt (Γ ▹ El ⌜Unit⌝) (renTm vs I) (renTm vs TTD) Nat (ιₛ 1) _ zero (mc ∷ mann ∷ [])
  perTm = entₛ ⊢J TTOK ty-Nat (nthˢᵗ-s nthˢᵗ-z) nthᵗ-z (⊢nsuc ⊢nzero)
       ∷ₐ entₛ ⊢J TTOK ty-Nat (nthˢᵗ-s nthˢᵗ-z) (nthᵗ-s nthᵗ-z) (⊢nsuc (⊢fst (⊢snd (⊢var here))))
       ∷ₐ []ₐ

  ⊢depthM : Γ ⊢ methAt TTEs ∷ MethTy I TTD Nat
  ⊢depthM =
    ⊢methₛ ⊢J ⊢TTD ty-Nat
      (⊢sortMeth ⊢J (allSD (⊢SortI ⊢J) TTOK) ty-Nat (nth-⌜⌝ₛₛ {Tss = TTss} nthˢᵗ-z) perTy
       ∷ₚ (⊢sortMeth ⊢J (allSD (⊢SortI ⊢J) TTOK) ty-Nat (nth-⌜⌝ₛₛ {Tss = TTss} (nthˢᵗ-s nthˢᵗ-z)) perTm
       ∷ₚ []ₚ))

  ⊢depth : {s t : RTm ⌊ Γ ⌋} → Γ ⊢ s ∷ El I → Γ ⊢ t ∷ TT s → Γ ⊢ depth s t ∷ Nat
  ⊢depth ds dt = ⊢ielim (⊢SortI ⊢J) ⊢TTD ty-Nat ⊢depthM ds dt

  -- ★ and `size`, the library fold — a sorted family folds like a flat one
  ⊢sizeM : Γ ⊢ methAt (sortFolds sizeAlg (TTss {⌊ Γ ⌋})) ∷ MethTy I TTD Nat
  ⊢sizeM = ⊢foldₛ sizeAlg ⊢J TTOK

------------------------------------------------------------------------
-- 4. ★★★ …AND IT RUNS ACROSS THE SORTS.
--
-- `depth 1 (ann c ι) ⟶* 2`: entered at sort `1`, the hypotheses' second
-- component re-enters the recursor at sort `0` with the same method.
------------------------------------------------------------------------

depth-base : {Γ : Cx} → depth {Γ} sTy tbase ⟶* nsuc nzero
depth-base =
  ⟶*-trans (ιₛT {Tss = TTss} nthˢᵗ-z nthᵗ-z nth-z nth-z)
    (step (ξ-appˡ (β _ _)) (step (β _ _) done))

depth-annCι : {Γ : Cx} → depth {Γ} sTm annCι ⟶* nsuc (nsuc nzero)
depth-annCι =
  ⟶*-trans (ιₛT {Tss = TTss} (nthˢᵗ-s nthˢᵗ-z) (nthᵗ-s nthᵗ-z) (nth-s nth-z) (nth-s nth-z))
    (step (ξ-appˡ (β _ _))
    (step (β _ _)
    (⟶*-nsuc
      (step (ξ-fst (βsnd _ _))
      (step (βfst _ _)
      (step (ξ-ielimᵗ (ξ-fst (βsnd _ _)))
      (step (ξ-ielimᵗ (βfst _ _))
      -- ★★★ HERE: the recursor fires again, at sort 0, on `ι`
        depth-base)))))))
