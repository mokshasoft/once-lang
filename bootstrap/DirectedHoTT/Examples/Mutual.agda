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
--     Cross-sort references become `iρ` at a CONSTANT index, and each
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
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; U; El; Π; Σ'; Unit; Nat; IMu
        ; RTm; var; lam; app; pair; fst; snd; unit; nzero; nsuc
        ; ⌜Nat⌝; ⌜Id⌝; idrefl; icon; ielim
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; ilookupD; _∈ID_; hereID; thereID
        ; ipayTy; isingle; iext; ifields; sel )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _∋_∷_; here; there
        ; _⟶_; _⟶*_; done; step
        ; β; βfst; βsnd; ξ-appˡ; ξ-fst; ξ-snd; ξ-nsuc
        ; ξ-ielimⁱ; ξ-ielimᵗ; ι-ielim
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ; credᵀ
        ; _⟶ᵀ_; El-⌜Nat⌝; El-⌜Id⌝
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢conv
        ; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢idrefl
        ; ⊢icon; ⊢ielim
        ; _⊢ty_; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-Π; ty-IMu
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; ICodeWf; icw-clo; icw-ford
        ; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTy )

------------------------------------------------------------------------
-- 0. The index: THE SORT TAG.  `0` is the type sort, `1` the term sort.
------------------------------------------------------------------------

INat : RTy ε
INat = El ⌜Nat⌝

elNat : {Γ : Cx} → El (⌜Nat⌝ {Γ}) ≅ᵀ Nat
elNat = credᵀ El-⌜Nat⌝

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ elNat)

fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d elNat

sortTy sortTm : {Γ : Cx} → RTm Γ
sortTy = nzero
sortTm = nsuc nzero

------------------------------------------------------------------------
-- 1. THE DESCRIPTION — four constructors across two sorts.
--
-- ⚠ EVERY recursive field sits at a CLOSED index (`0` or `1`), never at
--   a function of the ambient one.  That is what makes mutuality easier
--   than `Scoped`'s binder shift, not harder: `renTm vs nzero = nzero`,
--   so none of `Scoped`'s `wk-single` plumbing appears below.
------------------------------------------------------------------------

-- ι : Ty                       — forded to the type sort
ιC : ICon (ε ∙)
ιC = iκ (⌜Id⌝ ⌜Nat⌝ (var vz) sortTy) iι

-- arr : Ty → Ty → Ty
arrC : ICon (ε ∙)
arrC = iρ sortTy (iρ sortTy (iκ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTy) iι))

-- c : Tm
cC : ICon (ε ∙)
cC = iκ (⌜Id⌝ ⌜Nat⌝ (var vz) sortTm) iι

-- ★★★ ann : Tm → Ty → Tm — THE CROSS-SORT FIELD.  Field 1 recurses at
--   tag 1, field 2 at tag 0: one `iρ` each, at different constant
--   indices, in the SAME constructor.
annC : ICon (ε ∙)
annC = iρ sortTm (iρ sortTy (iκ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTm) iι))

TTD : IDesc
TTD = ιC ◂ (arrC ◂ (cC ◂ (annC ◂ inil)))

TT : {Γ : Cx} → RTm Γ → RTy Γ
TT s = IMu TTD INat s

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS.
------------------------------------------------------------------------

ιWf : IConWf TTD INat (◇ ▹ INat) ιC
ιWf = iwf-κ (⌜Id⌝ ⌜Nat⌝ (var vz) sortTy)
            (icw-ford ⌜Nat⌝ (var vz) sortTy)
            (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var here) (toI ⊢nzero))
            iwf-ι

arrWf : IConWf TTD INat (◇ ▹ INat) arrC
arrWf =
  iwf-ρ sortTy (toI ⊢nzero)
   (iwf-ρ sortTy (toI ⊢nzero)
    (iwf-κ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTy)
           (icw-ford ⌜Nat⌝ (var (vs (vs vz))) sortTy)
           (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var (there (there here))) (toI ⊢nzero))
           iwf-ι))

cWf : IConWf TTD INat (◇ ▹ INat) cC
cWf = iwf-κ (⌜Id⌝ ⌜Nat⌝ (var vz) sortTm)
            (icw-ford ⌜Nat⌝ (var vz) sortTm)
            (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var here) (toI (⊢nsuc ⊢nzero)))
            iwf-ι

annWf : IConWf TTD INat (◇ ▹ INat) annC
annWf =
  iwf-ρ sortTm (toI (⊢nsuc ⊢nzero))
   (iwf-ρ sortTy (toI ⊢nzero)
    (iwf-κ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTm)
           (icw-ford ⌜Nat⌝ (var (vs (vs vz))) sortTm)
           (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var (there (there here))) (toI (⊢nsuc ⊢nzero)))
           iwf-ι))

TTWf : IDescWf INat TTD
TTWf = idwf-cons ιWf (idwf-cons arrWf (idwf-cons cWf (idwf-cons annWf idwf-nil)))

------------------------------------------------------------------------
-- 3. THE CONSTRUCTORS — `⊢icon`, four times, across both sorts.
------------------------------------------------------------------------

tι tc : {Γ : Cx} → RTm Γ
tι = icon zero (pair (idrefl ⌜Nat⌝ sortTy) unit)
tc = icon (suc (suc zero)) (pair (idrefl ⌜Nat⌝ sortTm) unit)

tarr tann : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
tarr a b = icon (suc zero)
                (pair a (pair b (pair (idrefl ⌜Nat⌝ sortTy) unit)))
tann t a = icon (suc (suc (suc zero)))
                (pair t (pair a (pair (idrefl ⌜Nat⌝ sortTm) unit)))

reflSTy : {Γ : Ctx} →
          Γ ⊢ idrefl ⌜Nat⌝ sortTy ∷ El (⌜Id⌝ ⌜Nat⌝ sortTy sortTy)
reflSTy = ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI ⊢nzero))
                (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ sortTy sortTy)))

reflSTm : {Γ : Ctx} →
          Γ ⊢ idrefl ⌜Nat⌝ sortTm ∷ El (⌜Id⌝ ⌜Nat⌝ sortTm sortTm)
reflSTm = ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI (⊢nsuc ⊢nzero)))
                (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ sortTm sortTm)))

⊢tι : ◇ ⊢ tι ∷ TT sortTy
⊢tι = ⊢icon TTWf hereID (toI ⊢nzero) (⊢pair ty-Unit reflSTy ⊢unit)

⊢tc : ◇ ⊢ tc ∷ TT sortTm
⊢tc = ⊢icon TTWf (thereID (thereID hereID)) (toI (⊢nsuc ⊢nzero))
        (⊢pair ty-Unit reflSTm ⊢unit)

-- the `⊢ty` tails.  ⚠ ALL CLOSED — no weakening appears anywhere here,
--   which is the encoding's practical dividend over `Scoped`'s shift.
tyFordTy : {Γ : Ctx} → Γ ⊢ty Σ' (El (⌜Id⌝ ⌜Nat⌝ sortTy sortTy)) Unit
tyFordTy = ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI ⊢nzero) (toI ⊢nzero))) ty-Unit

tyFordTm : {Γ : Ctx} → Γ ⊢ty Σ' (El (⌜Id⌝ ⌜Nat⌝ sortTm sortTm)) Unit
tyFordTm = ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢nsuc ⊢nzero))
                                     (toI (⊢nsuc ⊢nzero)))) ty-Unit

tyArr₂ : {Γ : Ctx} →
         Γ ⊢ty Σ' (IMu TTD INat sortTy)
                  (Σ' (El (⌜Id⌝ ⌜Nat⌝ sortTy sortTy)) Unit)
tyArr₂ = ty-Σ (ty-IMu TTWf (toI ⊢nzero)) tyFordTy

tyAnn₂ : {Γ : Ctx} →
         Γ ⊢ty Σ' (IMu TTD INat sortTy)
                  (Σ' (El (⌜Id⌝ ⌜Nat⌝ sortTm sortTm)) Unit)
tyAnn₂ = ty-Σ (ty-IMu TTWf (toI ⊢nzero)) tyFordTm

⊢tarr : {a b : RTm ε} →
        ◇ ⊢ a ∷ TT sortTy → ◇ ⊢ b ∷ TT sortTy → ◇ ⊢ tarr a b ∷ TT sortTy
⊢tarr da db =
  ⊢icon TTWf (thereID hereID) (toI ⊢nzero)
    (⊢pair tyArr₂ da (⊢pair tyFordTy db (⊢pair ty-Unit reflSTy ⊢unit)))

-- ★★★ THE CROSS-SORT CONSTRUCTOR: a `Tm` field and a `Ty` field, in one
--   `⊢icon`, from one description.
⊢tann : {t a : RTm ε} →
        ◇ ⊢ t ∷ TT sortTm → ◇ ⊢ a ∷ TT sortTy → ◇ ⊢ tann t a ∷ TT sortTm
⊢tann dt da =
  ⊢icon TTWf (thereID (thereID (thereID hereID))) (toI (⊢nsuc ⊢nzero))
    (⊢pair tyAnn₂ dt (⊢pair tyFordTm da (⊢pair ty-Unit reflSTm ⊢unit)))

-- `c : ι` — the smallest term that uses both sorts.
annCι : {Γ : Cx} → RTm Γ
annCι = tann tc tι

⊢annCι : ◇ ⊢ annCι ∷ TT sortTm
⊢annCι = ⊢tann ⊢tc ⊢tι

------------------------------------------------------------------------
-- 4. ★★★ MUTUAL INDUCTION IS ONE `ielim`.
--
-- `depth : TT s → Nat`, one motive (`Nat`, constant), one method per
-- constructor OF EITHER SORT.  ⚠ `mann` deliberately reads its SECOND
-- IH — the one at the `Ty` field — so the recursion CROSSES SORTS: the
-- method reached at tag `1` consumes the recursor's result at tag `0`,
-- from the same method tuple.  That is what "mutual induction" means,
-- and nothing in the kernel had to learn it.
------------------------------------------------------------------------

mι marr mc mann ms : {Γ : Cx} → RTm Γ
mι   = lam (lam (lam (nsuc nzero)))
marr = lam (lam (lam (nsuc (fst (var vz)))))
mc   = lam (lam (lam (nsuc nzero)))
mann = lam (lam (lam (nsuc (fst (snd (var vz))))))
ms   = pair mι (pair marr (pair mc (pair mann unit)))

depth : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
depth s t = ielim TTD s ms t

-- the four payload types, under the method's index binder
tyPayΙ : {Γ : Ctx} →
         (Γ ▹ El ⌜Nat⌝) ⊢ty Σ' (El (⌜Id⌝ ⌜Nat⌝ (var vz) sortTy)) Unit
tyPayΙ = ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var here) (toI ⊢nzero))) ty-Unit

tyPayC : {Γ : Ctx} →
         (Γ ▹ El ⌜Nat⌝) ⊢ty Σ' (El (⌜Id⌝ ⌜Nat⌝ (var vz) sortTm)) Unit
tyPayC = ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var here) (toI (⊢nsuc ⊢nzero))))
              ty-Unit

tyPayArr : {Γ : Ctx} →
           (Γ ▹ El ⌜Nat⌝) ⊢ty
           Σ' (IMu TTD INat sortTy)
              (Σ' (IMu TTD INat sortTy)
                  (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTy)) Unit))
tyPayArr =
  ty-Σ (ty-IMu TTWf (toI ⊢nzero))
    (ty-Σ (ty-IMu TTWf (toI ⊢nzero))
      (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var (there (there here))) (toI ⊢nzero)))
            ty-Unit))

tyPayAnn : {Γ : Ctx} →
           (Γ ▹ El ⌜Nat⌝) ⊢ty
           Σ' (IMu TTD INat sortTm)
              (Σ' (IMu TTD INat sortTy)
                  (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTm)) Unit))
tyPayAnn =
  ty-Σ (ty-IMu TTWf (toI (⊢nsuc ⊢nzero)))
    (ty-Σ (ty-IMu TTWf (toI ⊢nzero))
      (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var (there (there here)))
                                 (toI (⊢nsuc ⊢nzero))))
            ty-Unit))

tyIH₀ : {Γ : Ctx} → Γ ⊢ty Unit
tyIH₀ = ty-Unit

tyIH₂ : {Γ : Ctx} → Γ ⊢ty Σ' Nat (Σ' Nat Unit)
tyIH₂ = ty-Σ ty-Nat (ty-Σ ty-Nat ty-Unit)

⊢mι : {Γ : Ctx} →
      Γ ⊢ mι ∷ Π (El ⌜Nat⌝)
                 (Π (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var vz) sortTy)) Unit)
                    (Π Unit Nat))
⊢mι = ⊢lam (ty-El ⊢⌜Nat⌝)
        (⊢lam tyPayΙ (⊢lam ty-Unit (⊢nsuc ⊢nzero)))

⊢mc : {Γ : Ctx} →
      Γ ⊢ mc ∷ Π (El ⌜Nat⌝)
                 (Π (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var vz) sortTm)) Unit)
                    (Π Unit Nat))
⊢mc = ⊢lam (ty-El ⊢⌜Nat⌝)
        (⊢lam tyPayC (⊢lam ty-Unit (⊢nsuc ⊢nzero)))

⊢marr : {Γ : Ctx} →
        Γ ⊢ marr ∷
        Π (El ⌜Nat⌝)
          (Π (Σ' (IMu TTD INat sortTy)
                 (Σ' (IMu TTD INat sortTy)
                     (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTy)) Unit)))
             (Π (Σ' Nat (Σ' Nat Unit)) Nat))
⊢marr = ⊢lam (ty-El ⊢⌜Nat⌝)
          (⊢lam tyPayArr (⊢lam tyIH₂ (⊢nsuc (⊢fst (⊢var here)))))

-- ★★★ the cross-sort method: `fst (snd ih)` is the recursor's value at
--   the OTHER TAG.
⊢mann : {Γ : Ctx} →
        Γ ⊢ mann ∷
        Π (El ⌜Nat⌝)
          (Π (Σ' (IMu TTD INat sortTm)
                 (Σ' (IMu TTD INat sortTy)
                     (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTm)) Unit)))
             (Π (Σ' Nat (Σ' Nat Unit)) Nat))
⊢mann = ⊢lam (ty-El ⊢⌜Nat⌝)
          (⊢lam tyPayAnn (⊢lam tyIH₂ (⊢nsuc (⊢fst (⊢snd (⊢var here))))))

tyΠmarr : {Γ : Ctx} →
          Γ ⊢ty Π (El ⌜Nat⌝)
                  (Π (Σ' (IMu TTD INat sortTy)
                         (Σ' (IMu TTD INat sortTy)
                             (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTy))
                                 Unit)))
                     (Π (Σ' Nat (Σ' Nat Unit)) Nat))
tyΠmarr = ty-Π (ty-El ⊢⌜Nat⌝) (ty-Π tyPayArr (ty-Π tyIH₂ ty-Nat))

tyΠmc : {Γ : Ctx} →
        Γ ⊢ty Π (El ⌜Nat⌝)
                (Π (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var vz) sortTm)) Unit)
                   (Π Unit Nat))
tyΠmc = ty-Π (ty-El ⊢⌜Nat⌝) (ty-Π tyPayC (ty-Π ty-Unit ty-Nat))

tyΠmann : {Γ : Ctx} →
          Γ ⊢ty Π (El ⌜Nat⌝)
                  (Π (Σ' (IMu TTD INat sortTm)
                         (Σ' (IMu TTD INat sortTy)
                             (Σ' (El (⌜Id⌝ ⌜Nat⌝ (var (vs (vs vz))) sortTm))
                                 Unit)))
                     (Π (Σ' Nat (Σ' Nat Unit)) Nat))
tyΠmann = ty-Π (ty-El ⊢⌜Nat⌝) (ty-Π tyPayAnn (ty-Π tyIH₂ ty-Nat))

⊢ms : ◇ ⊢ ms ∷ imethsTy TTD INat Nat TTD
⊢ms =
  ⊢pair (ty-Σ tyΠmarr (ty-Σ tyΠmc (ty-Σ tyΠmann ty-Unit))) ⊢mι
    (⊢pair (ty-Σ tyΠmc (ty-Σ tyΠmann ty-Unit)) ⊢marr
      (⊢pair (ty-Σ tyΠmann ty-Unit) ⊢mc
        (⊢pair ty-Unit ⊢mann ⊢unit)))

⊢depth : {s t : RTm ε} →
         ◇ ⊢ s ∷ El ⌜Nat⌝ → ◇ ⊢ t ∷ TT s → ◇ ⊢ depth s t ∷ Nat
⊢depth ds dt = ⊢ielim TTWf ty-Nat ds ⊢ms dt

------------------------------------------------------------------------
-- 5. ★★★ …AND IT RUNS ACROSS THE SORTS.
--
-- `depth 1 (ann c ι) ⟶* 2`.  Step 13 is the whole point: the recursor
-- was entered at tag `1` (`sortTm`) and the IH tuple's SECOND component
-- re-entered it at tag `0` (`sortTy`), with the SAME method tuple.  A
-- mutual recursion, and the kernel never learned the word.
------------------------------------------------------------------------

annPay ιPay annIHs msT1 msT2 msT3 : {Γ : Cx} → RTm Γ
annPay = pair tc (pair tι (pair (idrefl ⌜Nat⌝ sortTm) unit))
ιPay   = pair (idrefl ⌜Nat⌝ sortTy) unit
msT1   = pair marr (pair mc (pair mann unit))
msT2   = pair mc (pair mann unit)
msT3   = pair mann unit
annIHs = pair (ielim TTD sortTm ms (fst annPay))
              (pair (ielim TTD sortTy ms (fst (snd annPay))) unit)

depth-annCι : {Γ : Cx} → depth {Γ} sortTm annCι ⟶* nsuc (nsuc nzero)
depth-annCι =
  step (ι-ielim TTD sortTm ms (suc (suc (suc zero))) annPay)
  -- select the fourth method: three `βsnd`, then `βfst`
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (ξ-fst (ξ-snd (ξ-snd (βsnd mι msT1)))))))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (ξ-fst (ξ-snd (βsnd marr msT2))))))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (ξ-fst (βsnd mc msT3)))))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst mann unit))))
  -- apply it to the index, the payload and the IHs
  (step (ξ-appˡ (ξ-appˡ (β (lam (lam (nsuc (fst (snd (var vz)))))) sortTm)))
  (step (ξ-appˡ (β (lam (nsuc (fst (snd (var vz))))) annPay))
  (step (β (nsuc (fst (snd (var vz)))) annIHs)
  -- project the SECOND IH — the one at the other tag
  (step (ξ-nsuc (ξ-fst (βsnd (ielim TTD sortTm ms (fst annPay))
                             (pair (ielim TTD sortTy ms
                                     (fst (snd annPay))) unit))))
  (step (ξ-nsuc (βfst (ielim TTD sortTy ms (fst (snd annPay))) unit))
  (step (ξ-nsuc (ξ-ielimᵗ (ξ-fst (βsnd tc (pair tι (pair (idrefl ⌜Nat⌝ sortTm)
                                                         unit))))))
  (step (ξ-nsuc (ξ-ielimᵗ (βfst tι (pair (idrefl ⌜Nat⌝ sortTm) unit))))
  -- ★★★ HERE: the recursor fires again, at tag 0, on `ι`
  (step (ξ-nsuc (ι-ielim TTD sortTy ms zero ιPay))
  (step (ξ-nsuc (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst mι msT1)))))
  (step (ξ-nsuc (ξ-appˡ (ξ-appˡ (β (lam (lam (nsuc nzero))) sortTy))))
  (step (ξ-nsuc (ξ-appˡ (β (lam (nsuc nzero)) ιPay)))
  (step (ξ-nsuc (β (nsuc nzero) unit)) done))))))))))))))))
