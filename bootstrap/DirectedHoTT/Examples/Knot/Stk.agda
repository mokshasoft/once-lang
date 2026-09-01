------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `stkA?`, OBJECT-LEVEL.
--
--     stkA? ⌜base⌝ = ⌜Σ⌝ = ⌜Id⌝ = ⌜Unit⌝ = ⌜Mu⌝ = ⌜Nat⌝ = ⌜IMu⌝ = true
--     stkA? (⌜Hom⌝ C a b) = stkA? C
--     stkA? _             = false
--
-- ⚠ `tr-J-Hom` reads `stkA? c₁ ≡ true` as a PREMISE.
--
-- ★★★ THE METHODS ARE `Knot/Pw`'s, UNCHANGED.  Same constant-`Nat`
--   motive, and the three shapes a predicate needs — `0`, `1`, and
--   "forward the first IH" — are exactly `pwZero`, `stkOne` and
--   `pwHom`.  What differs between `pw?` and `stkA?` is only WHICH ROWS
--   get which, so only the table below is new.
--
-- ★★ AND THE TABLE IS A PATTERN MATCH ON THE TAG, not a segmented tuple.
--   `pw?` had two ADJACENT overrides and segmenting was shorter; these
--   are EIGHT SCATTERED ones (19, 21, 22, 26, 37, 38, 39, 40 of 53) and
--   segmenting would need eight `imethsTyFrom-wf` runs.  ⇒ `methsAt`,
--   whose per-row method is a function of the tag — the customer it was
--   built for.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Stk where
open import normalizer.Syntax.Types using ( _≡_; refl; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; lam; nzero; nsuc; Nat; ICon; IDesc; εwkTy
        ; ilookupD; _∈ID_; pair; _◂_; unit; ielim; Σ'; var; vz; vs; fst; snd )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; ⊢nzero; ⊢nsuc; ty-Nat; IConWf; imethTy
        ; imethsTyFrom; IDescWfFrom; imethsTy; ⊢unit; ⊢ielim
        ; ⊢var; here; there; ⊢fst; ⊢snd )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢methsFrom; ⊢methsCons; imethsTyFrom-wf; idwfDrop
        ; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; cdPos; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair; sTm; ⊢sTm; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cTm-cbase; cTm-cSg; cTm-cId; cTm-cHom; cTm-cNat )
open import DirectedHoTT.Examples.Knot.Wf
  using ( KnotWf; cTm-cHomWf; cTm-cbaseWf; cTm-cSgWf; cTm-cIdWf; cTm-cNatWf )
open import DirectedHoTT.Examples.Knot.Pw using ( pwZero; ⊢pwZero; pwHom; ⊢pwHom )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagTm-cbase; tagTm-cSg; tagTm-cHom; tagTm-cId
        ; tagTm-cNat; tagTm-cMu; tagTm-cIMu; tagTm-cUnit )

------------------------------------------------------------------------
-- ⚠⚠ THE TAGS ARE POSITIONS, so the table below is written in NUMERALS
--   and these `refl`s are what tie the numerals to the names.  A row
--   inserted into `KNOT` shifts every tag after it, and without these
--   the table would go on typechecking while pointing at the WRONG ROWS
--   — a silent mis-selection, not an error.
------------------------------------------------------------------------

_ : tagTm-cbase ≡ 19
_ = refl
_ : tagTm-cSg ≡ 21
_ = refl
_ : tagTm-cHom ≡ 22
_ = refl
_ : tagTm-cId ≡ 26
_ = refl
_ : tagTm-cNat ≡ 37
_ = refl
_ : tagTm-cMu ≡ 38
_ = refl
_ : tagTm-cIMu ≡ 39
_ = refl
_ : tagTm-cUnit ≡ 40
_ = refl

------------------------------------------------------------------------
-- ★ the `true` method — `Knot/Pw`'s `pwOne` at an ABSTRACT row.
------------------------------------------------------------------------

stkOne : {Γ : Cx} → RTm Γ
stkOne = lam (lam (lam (nsuc nzero)))

⊢stkOne : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
          IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
          Γ ⊢ stkOne ∷ imethTy KnotD IPair k C Nat
⊢stkOne k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ty-Nat (⊢nsuc ⊢nzero)

------------------------------------------------------------------------
-- ★★★ THE TUPLE — SIX CONSTANT RUNS AND FOUR SINGLE OVERRIDES.
--
-- ⚠⚠ A TAG TABLE WAS TRIED FIRST AND AGDA REFUSES IT: matching on the
--   numeral `21` is `LiteralTooBig` (literals expand to `suc` patterns,
--   and the cap is 20).  Seven of the eight override rows are above it.
--   ⇒ `methsAt`, which this was to be the customer for, STILL has none —
--     recorded rather than retro-justified, again.
--
-- ★ Rows 37–40 are CONTIGUOUS (`⌜Nat⌝ ⌜Mu⌝ ⌜IMu⌝ ⌜Unit⌝ all `true`), so
--   they are one `methsFrom` run rather than four rungs.
------------------------------------------------------------------------

D19 D20 D21 D22 D23 D26 D27 D37 D38 D41 : IDesc
D41 = cdRest (cdTake 41 KnotD)
D38 = cdRest (cdTake 38 KnotD)
D37 = cdRest (cdTake 37 KnotD)
D27 = cdRest (cdTake 27 KnotD)
D26 = cdRest (cdTake 26 KnotD)
D23 = cdRest (cdTake 23 KnotD)
D22 = cdRest (cdTake 22 KnotD)
D21 = cdRest (cdTake 21 KnotD)
D20 = cdRest (cdTake 20 KnotD)
D19 = cdRest (cdTake 19 KnotD)

sp19 : Split KnotD 19 D19
sp19 = splTake spl-nil (cdTake 19 KnotD)
sp20 : Split KnotD 20 D20
sp20 = spl-step sp19
sp21 : Split KnotD 21 D21
sp21 = spl-step sp20
sp22 : Split KnotD 22 D22
sp22 = spl-step sp21
sp23 : Split KnotD 23 D23
sp23 = spl-step sp22
sp26 : Split KnotD 26 D26
sp26 = splTake spl-nil (cdTake 26 KnotD)
sp27 : Split KnotD 27 D27
sp27 = spl-step sp26
sp37 : Split KnotD 37 D37
sp37 = splTake spl-nil (cdTake 37 KnotD)
sp38 : Split KnotD 38 D38
sp38 = spl-step sp37
sp41 : Split KnotD 41 D41
sp41 = splTake spl-nil (cdTake 41 KnotD)

wf : {E : IDesc} {j : ℕ} → Split KnotD j E → IDescWfFrom KnotD IPair E
wf sp = idwfDrop sp KnotWf

-- ⚠ `C` IS EXPLICIT.  `imethTy` is a DEFINED function and not injective,
--   so unifying `imethTy … j _C Nat` against a method's concrete type
--   makes Agda unfold and the meta never solves —
--   `pin-implicits-on-defined-set-types`.
cons : {Γ : Ctx} (j : ℕ) (C : ICon (ε ∙)) (E : IDesc) {m tl : RTm ⌊ Γ ⌋} →
       Split KnotD (suc j) E →
       Γ ⊢ m ∷ imethTy KnotD IPair j C Nat →
       Γ ⊢ tl ∷ imethsTyFrom KnotD IPair Nat (suc j) E →
       Γ ⊢ pair m tl ∷ imethsTyFrom KnotD IPair Nat j (C ◂ E)
cons j C E sp = ⊢methsCons KnotD IPair j {C = C} E KnotWf (wf sp) sp ⊢IPair ty-Nat

-- ⚠ `tl` IS EXPLICIT ONLY.  Declaring it implicit as well left an
--   unsolvable meta at every call site — the implicit one is never
--   determined because the explicit one shadows it in the type.
run : {Γ : Ctx} (j : ℕ) (n : ℕ) (E : IDesc) {m : RTm ⌊ Γ ⌋} →
      Split KnotD j E →
      ({k : ℕ} {C : ICon (ε ∙)} → IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
         k ∈ID KnotD → ilookupD KnotD k ≡ C → Γ ⊢ m ∷ imethTy KnotD IPair k C Nat) →
      (tl : RTm ⌊ Γ ⌋) →
      Γ ⊢ tl ∷ imethsTyFrom KnotD IPair Nat (cdPos (cdTake n E) j) (cdRest (cdTake n E)) →
      Γ ⊢ methsFrom (cdTake n E) m tl ∷ imethsTyFrom KnotD IPair Nat j E
run j n E sp dm tl dtl =
  ⊢methsFrom KnotD IPair j (cdTake n E) KnotWf (wf sp) sp ⊢IPair ty-Nat dm tl dtl

------------------------------------------------------------------------
-- ★★★ `stkA?` — the tuple, then the eliminator.
--
--   0–18  false · 19 TRUE · 20 false · 21 TRUE · 22 IH · 23–25 false
--   26 TRUE · 27–36 false · 37–40 TRUE · 41–52 false
------------------------------------------------------------------------

stkAMeths : {Γ : Cx} → RTm Γ
stkAMeths =
  methsFrom (cdTake 19 KnotD) pwZero
    (pair stkOne
      (methsFrom (cdTake 1 D20) pwZero
        (pair stkOne
          (pair pwHom
            (methsFrom (cdTake 3 D23) pwZero
              (pair stkOne
                (methsFrom (cdTake 10 D27) pwZero
                  (methsFrom (cdTake 4 D37) stkOne
                    (methsFrom (cdTake 12 D41) pwZero unit)))))))))

⊢stkAMeths : {Γ : Ctx} → Γ ⊢ stkAMeths ∷ imethsTy KnotD IPair Nat KnotD
⊢stkAMeths =
  run 0 19 KnotD spl-nil (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
   (cons 19 cTm-cbase D20 sp20 (⊢stkOne 19 cTm-cbase cTm-cbaseWf)
    (run 20 1 D20 sp20 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
     (cons 21 cTm-cSg D22 sp22 (⊢stkOne 21 cTm-cSg cTm-cSgWf)
      (cons 22 cTm-cHom D23 sp23 ⊢pwHom
       (run 23 3 D23 sp23 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
        (cons 26 cTm-cId D27 sp27 (⊢stkOne 26 cTm-cId cTm-cIdWf)
         (run 27 10 D27 sp27 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
          (run 37 4 D37 sp37 (λ {k} {C} wC _ _ → ⊢stkOne k C wC) _
           (run 41 12 D41 sp41 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) unit ⊢unit)))))))))

stkAK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
stkAK i t = ielim KnotD i stkAMeths t

⊢stkAK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
         Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ stkAK i t ∷ Nat
⊢stkAK di dt = ⊢ielim KnotWf ty-Nat di ⊢stkAMeths dt

------------------------------------------------------------------------
-- ★★★ `stkC?` — `stkA?` WITH ONE ROW FLIPPED, and a CROSS-CALL.
--
--     stkC? ⌜Nat⌝         = false   ← the only row that differs
--     stkC? (⌜Hom⌝ C a b) = stkA? C ← NOT its own IH
--
-- ⚠ THE `⌜Hom⌝` ROW IS NOT A RECURSION.  `stkC?` calls `stkA?`, so its
--   method cannot read the IH tuple — it applies `stkAK` to the PAYLOAD's
--   first field, at that field's own index.  Same move `pwBody`'s
--   `⌜Hom⌝` row makes for its endpoints, and the reason a plain fold
--   cannot express either.
------------------------------------------------------------------------

stkCHom : {Γ : Cx} → RTm Γ
stkCHom = lam (lam (lam (stkAK (pair sTm (snd (var (vs (vs vz)))))
                               (fst (var (vs vz))))))

⊢stkCHom : {Γ : Ctx} →
           Γ ⊢ stkCHom ∷ imethTy KnotD IPair tagTm-cHom cTm-cHom Nat
⊢stkCHom =
  ⊢methLam KnotD IPair tagTm-cHom cTm-cHom KnotWf cTm-cHomWf ⊢IPair ty-Nat
    (⊢stkAK (⊢ixP ⊢sTm (⊢snd (⊢var (there (there here)))))
            (⊢fst (⊢var (there here))))

-- ⚠ ROWS 37–40 ARE NO LONGER ONE RUN: `⌜Nat⌝` (37) is `false` for
--   `stkC?` while 38–40 stay `true`, so the contiguous block splits.
stkCMeths : {Γ : Cx} → RTm Γ
stkCMeths =
  methsFrom (cdTake 19 KnotD) pwZero
    (pair stkOne
      (methsFrom (cdTake 1 D20) pwZero
        (pair stkOne
          (pair stkCHom
            (methsFrom (cdTake 3 D23) pwZero
              (pair stkOne
                (methsFrom (cdTake 10 D27) pwZero
                  (pair pwZero
                    (methsFrom (cdTake 3 D38) stkOne
                      (methsFrom (cdTake 12 D41) pwZero unit))))))))))

⊢stkCMeths : {Γ : Ctx} → Γ ⊢ stkCMeths ∷ imethsTy KnotD IPair Nat KnotD
⊢stkCMeths =
  run 0 19 KnotD spl-nil (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
   (cons 19 cTm-cbase D20 sp20 (⊢stkOne 19 cTm-cbase cTm-cbaseWf)
    (run 20 1 D20 sp20 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
     (cons 21 cTm-cSg D22 sp22 (⊢stkOne 21 cTm-cSg cTm-cSgWf)
      (cons 22 cTm-cHom D23 sp23 ⊢stkCHom
       (run 23 3 D23 sp23 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
        (cons 26 cTm-cId D27 sp27 (⊢stkOne 26 cTm-cId cTm-cIdWf)
         (run 27 10 D27 sp27 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
          (cons 37 cTm-cNat D38 sp38 (⊢pwZero 37 cTm-cNat cTm-cNatWf)
           (run 38 3 D38 sp38 (λ {k} {C} wC _ _ → ⊢stkOne k C wC) _
            (run 41 12 D41 sp41 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) unit ⊢unit))))))))))

stkCK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
stkCK i t = ielim KnotD i stkCMeths t

⊢stkCK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
         Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ stkCK i t ∷ Nat
⊢stkCK di dt = ⊢ielim KnotWf ty-Nat di ⊢stkCMeths dt

------------------------------------------------------------------------
-- ★★★ `flat?` — TWO OVERRIDES, and the third customer of the scaffolding.
--
--     flat? ⌜base⌝        = true
--     flat? (⌜Hom⌝ c a b) = stkC? c
--     flat? _             = false
--
-- ⚠ `⊢ap` reads `flat? cA ≡ true`.  Its `⌜Hom⌝ row is the SAME cross-call
--   shape as `stkC?`'s — one function calling another at a payload field,
--   which no plain fold expresses.
------------------------------------------------------------------------

flatHom : {Γ : Cx} → RTm Γ
flatHom = lam (lam (lam (stkCK (pair sTm (snd (var (vs (vs vz)))))
                               (fst (var (vs vz))))))

⊢flatHom : {Γ : Ctx} →
           Γ ⊢ flatHom ∷ imethTy KnotD IPair tagTm-cHom cTm-cHom Nat
⊢flatHom =
  ⊢methLam KnotD IPair tagTm-cHom cTm-cHom KnotWf cTm-cHomWf ⊢IPair ty-Nat
    (⊢stkCK (⊢ixP ⊢sTm (⊢snd (⊢var (there (there here)))))
            (⊢fst (⊢var (there here))))

flatMeths : {Γ : Cx} → RTm Γ
flatMeths =
  methsFrom (cdTake 19 KnotD) pwZero
    (pair stkOne
      (methsFrom (cdTake 2 D20) pwZero
        (pair flatHom
          (methsFrom (cdTake 30 D23) pwZero unit))))

⊢flatMeths : {Γ : Ctx} → Γ ⊢ flatMeths ∷ imethsTy KnotD IPair Nat KnotD
⊢flatMeths =
  run 0 19 KnotD spl-nil (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
   (cons 19 cTm-cbase D20 sp20 (⊢stkOne 19 cTm-cbase cTm-cbaseWf)
    (run 20 2 D20 sp20 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) _
     (cons 22 cTm-cHom D23 sp23 ⊢flatHom
      (run 23 30 D23 sp23 (λ {k} {C} wC _ _ → ⊢pwZero k C wC) unit ⊢unit))))

flatK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
flatK i t = ielim KnotD i flatMeths t

⊢flatK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
         Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ flatK i t ∷ Nat
⊢flatK di dt = ⊢ielim KnotWf ty-Nat di ⊢flatMeths dt
