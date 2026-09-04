------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `pw?`, OBJECT-LEVEL.
--
--     pw? (⌜Π⌝ γ δ)     = true
--     pw? (⌜Hom⌝ C a b) = pw? C
--     pw? _             = false
--
-- ⚠ IT IS A **PREMISE**, which is why it has to exist here at all:
--   `hrefl-pw` and `tr-pw` both read `pw? C ≡ true`, and a rule whose
--   premise names a function the object level does not have cannot be
--   emitted.  Two reduction rows wait on this one.
--
-- ★★ THE MOTIVE IS CONSTANT `Nat` — booleans as `0`/`1`.  `Knot/Sz` is
--   the template: a constant motive needs no index-dependency, so the
--   eliminator's type is just `K i → Nat` and `⊢ielim` lands there with
--   no cast.
--
-- ★ AND ONLY TWO OF 53 ROWS DO ANYTHING.  `⌜Π⌝` answers `1`, `⌜Hom⌝`
--   forwards its first IH, everything else answers `0`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Pw where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; sym )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; fst; nzero; nsuc; Nat
        ; ICon; IDesc; εwkTy; pair; unit; ielim; Σ'; _◂_ )
open import DirectedHoTT.Lib.Wk using ( wk-singleTy )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; ren-ty )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢nzero; ⊢nsuc; ⊢fst; ty-Nat; IConWf; imethTy
        ; imethsTyFrom; imethsTy; ⊢pair; ⊢unit; ⊢ielim; IDescWfFrom )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢methsFrom; imethsTyFrom-wf; idwfDrop; splTake
        ; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( CDesc; cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cTm-cPi; cTm-cSg; cTm-cHom )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cTm-cPiWf; cTm-cSgWf; cTm-cHomWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagTm-cPi; tagTm-cSg; tagTm-cHom )

------------------------------------------------------------------------
-- ★ THE THREE METHODS.  `imethTy` binds exactly three things — index,
--   payload, IH tuple — and a CONSTANT motive adds none of its own, so
--   every method is three `lam`s and a `Nat`.
------------------------------------------------------------------------

pwZero : {Γ : Cx} → RTm Γ
pwZero = lam (lam (lam nzero))

⊢pwZero : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
          IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
          Γ ⊢ pwZero ∷ imethTy KnotD IPair k C Nat
⊢pwZero k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ty-Nat ⊢nzero

pwOne : {Γ : Cx} → RTm Γ
pwOne = lam (lam (lam (nsuc nzero)))

⊢pwOne : {Γ : Ctx} → Γ ⊢ pwOne ∷ imethTy KnotD IPair tagTm-cPi cTm-cPi Nat
⊢pwOne =
  ⊢methLam KnotD IPair tagTm-cPi cTm-cPi KnotWf cTm-cPiWf ⊢IPair ty-Nat
           (⊢nsuc ⊢nzero)

-- ★★ THE ONE ROW THAT RECURSES.  `⌜Hom⌝ C a b` has THREE recursive
--   fields, so its IH tuple is a right-nested Σ of three `Nat`s; `pw?`
--   reads the FIRST — the code `C` — and ignores the endpoints.
pwHom : {Γ : Cx} → RTm Γ
pwHom = lam (lam (lam (fst (var vz))))

⊢pwHom : {Γ : Ctx} → Γ ⊢ pwHom ∷ imethTy KnotD IPair tagTm-cHom cTm-cHom Nat
⊢pwHom =
  ⊢methLam KnotD IPair tagTm-cHom cTm-cHom KnotWf cTm-cHomWf ⊢IPair ty-Nat
           (⊢fst (⊢var here))

------------------------------------------------------------------------
-- ★★★ THE TUPLE — IN SEGMENTS, and that is what avoids the hard part.
--
-- `⌜Π⌝`, `⌜Σ'⌝` and `⌜Hom⌝` are rows 20, 21 and 22 of 53: the overrides
-- sit in the MIDDLE, so `cdTake`-prefix-plus-tail cannot reach them in
-- one go.  ⇒ three constant runs with the special rows supplied BETWEEN
-- them, each at a CONCRETE row.
--
-- ⚠⚠ THE ALTERNATIVE WAS A PER-ROW METHOD FUNCTION indexed by the tag,
--   and it is worse HERE: its typing must case on `eqℕ k tagTm-cPi` and
--   then transport `C` along `ilookupD D k ≡ C` to make the payload and
--   IH types concrete.  Segmenting needs no equation at all — every
--   method is written where its row is already known.
--   ⇒ `build-dont-transport`, at the tuple level.
------------------------------------------------------------------------

D23 : IDesc
D23 = cdRest (cdTake 23 KnotD)

spl23 : Split KnotD 23 D23
spl23 = splTake spl-nil (cdTake 23 KnotD)

wf23 : IDescWfFrom KnotD IPair D23
wf23 = idwfDrop spl23 KnotWf

-- ★ the last 30 rows, all `0`.
pwTail : {Γ : Cx} → RTm Γ
pwTail = methsFrom (cdTake 30 D23) pwZero unit

⊢pwTail : {Γ : Ctx} →
          Γ ⊢ pwTail ∷ imethsTyFrom KnotD IPair Nat 23 D23
⊢pwTail =
  ⊢methsFrom KnotD IPair 23 (cdTake 30 D23) KnotWf wf23 spl23
             ⊢IPair ty-Nat (λ {k} {C} wC _ _ → ⊢pwZero k C wC)
             unit ⊢unit

------------------------------------------------------------------------
-- ★★ THE THREE SPECIAL ROWS, then the leading run of 20.
------------------------------------------------------------------------

-- ⚠⚠ EVERY SEGMENT IS A **NAMED** DESCRIPTION, and each is built from
--   the next rather than as `cdRest (cdTake n KnotD)`.
--
--   The first version left these as `_` for `imethsTyFrom-wf` to solve
--   and OOM-KILLED — with `-c` too, so it was volume and not the
--   collector.  Each meta makes Agda re-normalise a `cdTake`/`cdRest`
--   against a 53-row description, once per occurrence, and there are
--   six.  ⇒ `pin-implicits-on-defined-set-types`: a `Def` is shared, a
--   meta is re-solved.
D22 : IDesc
D22 = cTm-cHom ◂ D23

D21 : IDesc
D21 = cTm-cSg ◂ D22

D20 : IDesc
D20 = cTm-cPi ◂ D21

spl20 : Split KnotD 20 D20
spl20 = splTake spl-nil (cdTake 20 KnotD)

spl21 : Split KnotD 21 D21
spl21 = spl-step spl20

spl22 : Split KnotD 22 D22
spl22 = spl-step spl21

pwMid : {Γ : Cx} → RTm Γ
pwMid = pair pwOne (pair pwZero (pair pwHom pwTail))

⊢pwMid : {Γ : Ctx} → Γ ⊢ pwMid ∷ imethsTyFrom KnotD IPair Nat 20 D20
⊢pwMid =
  ⊢pair (ren-ty (imethsTyFrom-wf KnotD IPair 21 D21 KnotWf
                   (idwfDrop spl21 KnotWf) spl21 ⊢IPair ty-Nat) there)
        ⊢pwOne
        (⊢-cast (sym (wk-singleTy {v = pwOne}
                        (imethsTyFrom KnotD IPair Nat 21 D21)))
          (⊢pair (ren-ty (imethsTyFrom-wf KnotD IPair 22 D22 KnotWf
                            (idwfDrop spl22 KnotWf) spl22 ⊢IPair ty-Nat) there)
                 (⊢pwZero tagTm-cSg cTm-cSg cTm-cSgWf)
                 (⊢-cast (sym (wk-singleTy {v = pwZero}
                                 (imethsTyFrom KnotD IPair Nat 22 D22)))
                   (⊢pair (ren-ty (imethsTyFrom-wf KnotD IPair 23 D23 KnotWf
                                     wf23 spl23 ⊢IPair ty-Nat) there)
                          ⊢pwHom
                          (⊢-cast (sym (wk-singleTy {v = pwHom}
                                          (imethsTyFrom KnotD IPair Nat 23 D23)))
                                  ⊢pwTail)))))

------------------------------------------------------------------------
-- ★★★ `pw?` — the whole tuple, and the eliminator.
------------------------------------------------------------------------

pwMethsK : {Γ : Cx} → RTm Γ
pwMethsK = methsFrom (cdTake 20 KnotD) pwZero pwMid

⊢pwMethsK : {Γ : Ctx} → Γ ⊢ pwMethsK ∷ imethsTy KnotD IPair Nat KnotD
⊢pwMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 20 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ty-Nat (λ {k} {C} wC _ _ → ⊢pwZero k C wC)
             pwMid ⊢pwMid

-- ★ NO CAST — the motive is constant, so `iinst i t Nat` IS `Nat`.
pwK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
pwK i t = ielim KnotD i pwMethsK t

⊢pwK : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
       Γ ⊢ i ∷ Σ' Nat Nat → Γ ⊢ t ∷ K i → Γ ⊢ pwK i t ∷ Nat
⊢pwK di dt = ⊢ielim KnotWf ty-Nat di ⊢pwMethsK dt
