------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `Ctx` AS ITS OWN INDEXED FAMILY.
--
--     ◇   :                            Ctx 0
--     _▹_ : Ctx m → RTy m            → Ctx (suc m)
--
-- ★★ WHY IT IS NOT AN 8th SORT OF THE KNOT, which is what this file
--   replaces.  The seven families in `KnotD` are ONE mutual recursion in
--   `Spec/Syntax`.  `Ctx` is not among them: `_▹_` carries an
--   `RTy ⌊ Γ ⌋`, so it DEPENDS on the syntax and the syntax never
--   depends back.  A one-directional dependency is a STRATUM, not a
--   member, and `Examples/Knot/WkEmp` is what it costs to pretend
--   otherwise — see `Negative/WkEmp` and `HANDOFF-2026-08-27` §A′.
--
-- ★ AND THE INDEX MEANT TWO THINGS.  `KnotD`'s second component is the
--   AMBIENT SCOPE a term lives in — a parameter.  A context's depth is
--   its OWN LENGTH — a measure of the datum.  Sharing one slot between
--   them is what forced `Knot/Map` to grow a THIRD signature shape for
--   `⊢enCtx` (`len ⌊ u ⌋`, read off the argument, where every other sort
--   either carries a `Cx` or takes the depth as a parameter).
--
-- ⇒ SO THE INDEX HERE IS A BARE DEPTH, AND THERE IS NO TAG FORD.  That
--   is the visible saving and it is not an edit-count one: the tag ford
--   was a distinction `Ctx` does not have.  Per row this drops one of
--   the two `Id` fields, the `pair`-index machinery (`⊢ixP` on the
--   ambient, `fordFst`, `βfst`) and five of the fourteen `num-ren` /
--   `num-sub` chains `_▹_` needed as sort 7.
--
-- ★★★ THE ONE THING THAT WAS UNTESTED, AND IT IS THE `RTy` FIELD.  Its
--   TYPE is a member of ANOTHER family, so it is a κ field carrying a
--   `⌜IMu⌝` CODE — `icw-imu`, PLAN-INDEXED §12 — and its index mentions
--   a BOUND FIELD (`m`), which no existing use does:
--
--     `Examples/Scoped.varC`    foreign `IMu` κ field, at the AMBIENT
--     `Examples/DepIx.islamC`   …at a COMPUTED index (`nsuc (fst ⟨i⟩)`)
--     `Examples/DepIx`'s ford   a κ code mentioning a BOUND field
--     HERE                      all three at once
--
--   ⚠ Fording could not do this job: it turns a computed INDEX into a
--   constraint, and never makes a field's TYPE a family.  Both
--   mechanisms are in `_▹_`, three lines apart, doing different jobs.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.CtxD where
open import normalizer.Syntax.Types using ( _≡_; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; Var
        ; RTy; RTm; El; Unit; Nat; Σ'; IMu
        ; var; pair; unit; nzero; nsuc; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; idrefl; icon
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_; _∈ID_; hereID; thereID
        ; Ren; Sub; renTm; subTm; extS )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv
        ; ⊢pair; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢idrefl; ⊢icon
        ; ty-El; ty-Unit; ty-Σ; ty-IMu
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; IDescWf; idwf-nil; idwf-cons
        ; _≅ᵀ_; csymᵀ; credᵀ; El-⌜Id⌝; El-⌜IMu⌝ )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢-cast; ⊢wk )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; ⊢sTy; toI; fromI; ⊢ixP; num; ⊢num; num-ren; num-sub )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-NatK; ⊢Ty-NatK )
open import DirectedHoTT.Examples.Knot.Map using ( enTy; ⊢enTy )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )
open import DirectedHoTT.Examples.Knot.Build using ( ⊢numAt; kCast )

------------------------------------------------------------------------
-- 0. THE INDEX — a bare DEPTH.  `El ⌜Nat⌝` and not `Nat`, for
--    `Examples/Scoped`'s reason: the decode removes a conversion from
--    every `ty-IMu` obligation.
------------------------------------------------------------------------

INat : RTy ε
INat = El ⌜Nat⌝

------------------------------------------------------------------------
-- 1. THE DESCRIPTION.  ⚠ `◇` Fords the depth to `0` and `_▹_` to
--    `suc m` — `Examples/Scoped`'s `Fin` shape exactly, plus the one
--    field `Fin` has no analogue of.
------------------------------------------------------------------------

-- ◇ : Ctx 0
cCtx-emp : ICon (ε ∙)
cCtx-emp = iκ (⌜Id⌝ ⌜Nat⌝ (var vz) nzero) iι

-- _▹_ : Ctx m → RTy m → Ctx (suc m)
cCtx-ext : ICon (ε ∙)
cCtx-ext =
  iκ ⌜Nat⌝
   (iρ (var vz)
    (iκ (⌜IMu⌝ KnotD IPair (pair sTy (var (vs vz))))
     (iκ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs (vs vz)))) (nsuc (var (vs (vs vz)))))
      iι)))

CtxD : IDesc
CtxD = cCtx-emp ◂ (cCtx-ext ◂ inil)

CtxK : {Γ : Cx} → RTm Γ → RTy Γ
CtxK d = IMu CtxD INat d

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS.  ★★★ The `icw-imu` row is the third line of
--    `cCtx-extWf` and it is the whole point of the file.
------------------------------------------------------------------------

cCtx-empWf : IConWf CtxD INat (◇ ▹ INat) cCtx-emp
cCtx-empWf =
  iwf-κ (⌜Id⌝ ⌜Nat⌝ (var vz) nzero)
        (icw-ford ⌜Nat⌝ (var vz) nzero)
        (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var here) (toI ⊢nzero))
        iwf-ι

cCtx-extWf : IConWf CtxD INat (◇ ▹ INat) cCtx-ext
cCtx-extWf =
  iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
   (iwf-ρ (var vz) (⊢var here)
    -- ★★★ a field whose TYPE is a member of the KNOT, at an index built
    --   from the BOUND depth.  Fording cannot express this; `icw-imu` is
    --   what §12 added for it.
    (iwf-κ (⌜IMu⌝ KnotD IPair (pair sTy (var (vs vz))))
           (icw-imu (pair sTy (var (vs vz))) KnotWf)
           (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (there here)))))
     (iwf-κ (⌜Id⌝ ⌜Nat⌝ (var (vs (vs (vs vz)))) (nsuc (var (vs (vs vz)))))
            (icw-ford ⌜Nat⌝ (var (vs (vs (vs vz)))) (nsuc (var (vs (vs vz)))))
            (⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var (there (there (there here))))
                          (toI (⊢nsuc (fromI (⊢var (there (there here)))))))
            iwf-ι)))

CtxWf : IDescWf INat CtxD
CtxWf = idwf-cons cCtx-empWf (idwf-cons cCtx-extWf idwf-nil)

------------------------------------------------------------------------
-- 3. THE TWO CONVERSIONS.  ⚠ NOTE WHAT IS ABSENT: there is no `fordFst`
--    here.  A pair index needs `fst`/`snd` to STEP before a ford can be
--    read; a bare depth does not.
------------------------------------------------------------------------

toKn : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
       Γ ⊢ t ∷ K i → Γ ⊢ t ∷ El (⌜IMu⌝ KnotD IPair i)
toKn d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

reflId : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ Nat → Γ ⊢ idrefl ⌜Nat⌝ t ∷ El (⌜Id⌝ ⌜Nat⌝ t t)
reflId {t = t} d =
  ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI d))
        (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ t t)))

------------------------------------------------------------------------
-- 4. THE SMART CONSTRUCTORS, at an abstract depth `num n`.
------------------------------------------------------------------------

Ctx-empK : {Γ : Cx} → RTm Γ
Ctx-empK = icon zero (pair (idrefl ⌜Nat⌝ nzero) unit)

⊢Ctx-empK : {Δ : Ctx} → Δ ⊢ Ctx-empK ∷ CtxK (num 0)
⊢Ctx-empK =
  ⊢icon CtxWf hereID (toI ⊢nzero)
    (⊢pair ty-Unit (reflId ⊢nzero) ⊢unit)

Ctx-extK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
Ctx-extK m g a =
  icon (suc zero) (pair m (pair g (pair a (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))

⊢Ctx-extK : {Δ : Ctx} (n : ℕ) {g a : RTm ⌊ Δ ⌋} →
            Δ ⊢ g ∷ CtxK (num n) →
            Δ ⊢ a ∷ K (pair sTy (num n)) →
            Δ ⊢ Ctx-extK (num n) g a ∷ CtxK (num (suc n))
⊢Ctx-extK n {g = g} {a = a} dg da =
  ⊢icon CtxWf (thereID hereID) (toI (⊢num (suc n)))
    -- level 0 — the bound depth `m`
    (⊢pair (ty-Σ (ty-IMu CtxWf (⊢var here))
             (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (there here))))))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢numAt (suc n) r3))
                              (toI (⊢nsuc (fromI (⊢var (there (there here))))))))
                     ty-Unit)))
           (toI (⊢num n))
    -- level 1 — the `Ctx` child.  Its index COMPUTES to `num n`.
      (⊢pair (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (⊢numAt n q1))))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢numAt (suc n) s31))
                              (toI (⊢nsuc (⊢numAt n w2)))))
                     ty-Unit))
             dg
    -- level 2 — ★ THE FOREIGN `IMu` FIELD.  One `kCast`, as sort 7's
    --   `RTy` field also cost; the `toKn` is the κ-code conversion.
        (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢numAt (suc n) s32))
                              (toI (⊢nsuc (⊢numAt n f32)))))
                     ty-Unit)
               (toKn (kCast (sym q2) da))
    -- level 3 — the DEPTH ford, THE ONLY FORD THIS ROW HAS
          (⊢pair ty-Unit
                 (⊢-cast (cong₂ (λ z w → El (⌜Id⌝ ⌜Nat⌝ z (nsuc w)))
                                (sym s33) (sym f33))
                         (reflId (⊢nsuc (⊢num n))))
                 ⊢unit))))
  where
    r3 : renTm vs (renTm vs (renTm vs (num (suc n)))) ≡ num (suc n)
    r3 = trans (cong (renTm vs) (trans (cong (renTm vs) (num-ren vs (suc n))) (num-ren vs (suc n)))) (num-ren vs (suc n))
    s31 : subTm (extS (extS (single (num n)))) (renTm vs (renTm vs (renTm vs (num (suc n))))) ≡ num (suc n)
    s31 = trans (cong (subTm (extS (extS (single (num n))))) r3) (num-sub (extS (extS (single (num n)))) (suc n))
    s32 : subTm (extS (single g)) (subTm (extS (extS (single (num n)))) (renTm vs (renTm vs (renTm vs (num (suc n)))))) ≡ num (suc n)
    s32 = trans (cong (subTm (extS (single g))) s31) (num-sub (extS (single g)) (suc n))
    s33 : subTm (single a) (subTm (extS (single g)) (subTm (extS (extS (single (num n)))) (renTm vs (renTm vs (renTm vs (num (suc n))))))) ≡ num (suc n)
    s33 = trans (cong (subTm (single a)) s32) (num-sub (single a) (suc n))

    q1 : renTm vs (num n) ≡ num n
    q1 = num-ren vs n
    q2 : subTm (single g) (renTm vs (num n)) ≡ num n
    q2 = trans (cong (subTm (single g)) q1) (num-sub (single g) n)

    w2 : renTm vs (renTm vs (num n)) ≡ num n
    w2 = trans (cong (renTm vs) (num-ren vs n)) (num-ren vs n)
    f32 : subTm (extS (single g)) (renTm vs (renTm vs (num n))) ≡ num n
    f32 = trans (cong (subTm (extS (single g))) w2) (num-sub (extS (single g)) n)
    f33 : subTm (single a) (subTm (extS (single g)) (renTm vs (renTm vs (num n)))) ≡ num n
    f33 = trans (cong (subTm (single a)) f32) (num-sub (single a) n)

------------------------------------------------------------------------
-- 5. ★★ AND IT IS INHABITED — `◇ ▹ Nat`, encoded, at depth 1.
--
-- ⚠ THE SAME TERM `Examples/Knot/WkEmp` FABRICATED.  There it was the
--   answer a weakening invented out of nothing; here it is an ordinary
--   inhabitant, built from its parts.  That is the difference the fork
--   was about.
------------------------------------------------------------------------

ctx1 : {Γ : Cx} → RTm Γ
ctx1 = Ctx-extK (num 0) Ctx-empK Ty-NatK

⊢ctx1 : ◇ ⊢ ctx1 ∷ CtxK (num 1)
⊢ctx1 = ⊢Ctx-extK 0 ⊢Ctx-empK (⊢Ty-NatK 0)

------------------------------------------------------------------------
-- 6. ★★★ THE ADEQUACY MAP — and for a HAND-WRITTEN family it is also
--    the COVERAGE CHECK.
--
-- `Knot/Wf` needs `tools/gen-knot.py`'s `verify()` because a GENERATED
-- table and a GENERATED map would omit a row in BOTH at once, silently.
-- Here the table is hand-written and so is the map, so Agda does the
-- job: `agda-coverage-checks-functions-not-datatypes` cuts the other
-- way for once — a missing `Ctx` constructor makes `enCtx` INCOMPLETE,
-- which is an error.
--
-- ⚠ AND THE DEPTH IS `len ⌊ u ⌋`, READ OFF THE ARGUMENT.  As sort 7 this
--   was an anomaly — it needed a third signature shape in `Knot/Map`,
--   where every other sort either carries a `Cx` or takes the depth as a
--   parameter.  Here it is simply what a context's index IS.
------------------------------------------------------------------------

enCtx : {Γ' : Cx} → Ctx → RTm Γ'
⊢enCtx : {Δ : Ctx} (u : Ctx) → Δ ⊢ enCtx u ∷ CtxK (num (len ⌊ u ⌋))

enCtx ◇       = Ctx-empK
enCtx (Γ ▹ A) = Ctx-extK (num (len ⌊ Γ ⌋)) (enCtx Γ) (enTy A)

⊢enCtx ◇       = ⊢Ctx-empK
⊢enCtx (Γ ▹ A) = ⊢Ctx-extK (len ⌊ Γ ⌋) (⊢enCtx Γ) (⊢enTy A)

------------------------------------------------------------------------
-- 7. ★★ `_▹_` AT A **VARIABLE** DEPTH.
--
-- ⚠ §4's smart constructors are at `num n` — a NUMERAL — because their
--   customer is the adequacy map, whose depths are `len ⌊ Γ ⌋`.  A
--   JUDGEMENT's constructor telescope is the other case: its depth is a
--   bound `iκ ⌜Nat⌝` field, i.e. a VARIABLE.
--
-- ★ AND IT IS THE CHEAP CASE.  Renaming and substitution COMPUTE on a
--   variable, so every `num-ren`/`num-sub` chain §4 needed collapses to
--   `refl`: the nine equations vanish, the `kCast` vanishes, and the
--   `⊢-cast` on the depth ford vanishes with them.  `Knot/Build`'s route
--   (c), and the two forms are siblings — neither subsumes the other.
------------------------------------------------------------------------

⊢Ctx-extKv : {Δ : Ctx} {x : Var ⌊ Δ ⌋} {g a : RTm ⌊ Δ ⌋} →
             Δ ⊢ var x ∷ Nat →
             Δ ⊢ g ∷ CtxK (var x) →
             Δ ⊢ a ∷ K (pair sTy (var x)) →
             Δ ⊢ Ctx-extK (var x) g a ∷ CtxK (nsuc (var x))
⊢Ctx-extKv {x = x} {g = g} {a = a} dx dg da =
  ⊢icon CtxWf (thereID hereID) (toI (⊢nsuc dx))
    (⊢pair (ty-Σ (ty-IMu CtxWf (⊢var here))
             (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (there here))))))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢nsuc (⊢wk (⊢wk (⊢wk dx)))))
                              (toI (⊢nsuc (fromI (⊢var (there (there here))))))))
                     ty-Unit)))
           (toI dx)
      (⊢pair (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (⊢wk dx))))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢nsuc (⊢wk (⊢wk dx))))
                              (toI (⊢nsuc (⊢wk (⊢wk dx))))))
                     ty-Unit))
             dg
        (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢nsuc (⊢wk dx)))
                              (toI (⊢nsuc (⊢wk dx)))))
                     ty-Unit)
               (toKn da)
          (⊢pair ty-Unit (reflId (⊢nsuc dx)) ⊢unit))))
