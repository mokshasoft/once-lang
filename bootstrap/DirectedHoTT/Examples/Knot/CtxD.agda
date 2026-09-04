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
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; wk-single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv
        ; ⊢pair; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢idrefl; ⊢icon
        ; ty-El; ty-Unit; ty-Σ; ty-IMu
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; IDescWf; idwf-nil; idwf-cons
        ; _≅ᵀ_; csymᵀ; credᵀ; El-⌜Id⌝; El-⌜IMu⌝ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; ⊢wk )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; ⊢sTy; toI; fromI; ⊢ixP; num; ⊢num )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-NatK; ⊢Ty-NatK )
open import DirectedHoTT.Examples.Knot.Map using ( enTy; ⊢enTy )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )
open import DirectedHoTT.Examples.Knot.Build using ( kCast; tmCast )
open import DirectedHoTT.Lib.Wk using ( w; sub-w²; sub-w-single )

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
-- 4. THE SMART CONSTRUCTORS, at an ARBITRARY depth TERM.
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

-- ★★★ `_▹_` AT AN ARBITRARY DEPTH — the ONE proof of this row.
--
-- ⚠⚠ IT REPLACES TWO SIBLINGS, and the note that said it could not.
--   §7 used to argue that the `num n` form and the `var x` form were
--   siblings "neither subsuming the other", because renaming and
--   substitution COMPUTE on a variable and are the IDENTITY on a
--   numeral — two different reasons the four field-substitutions
--   vanish, neither covering the other.  That is true about the
--   REASONS and false about the LEMMA: at an arbitrary `d` the
--   substitutions do not vanish, they DESCEND, and the descent is
--   `Knot/Build`'s rung 5 (`⊢Var-vsKt`) — the same four rungs over a
--   four-field telescope.  Both siblings are then instances.
--
-- ★ AND `⊢natrec` IS WHAT FORCED IT.  Its premise extends the context
--   TWICE — `(Γ ▹ Nat) ▹ M` — so the outer extension sits at
--   `nsuc (var x)`, which is neither a numeral nor a variable.  ONE
--   generated call site in the whole judgement family needs this; the
--   other nine are at a variable.
--
-- ★ `rtA` IS GENERIC IN BOTH TERMS, per `abstract-the-substituted-terms`
--   — one lemma reused at three different pairs, not one per position.
------------------------------------------------------------------------

⊢Ctx-extKt : {Δ : Ctx} {d : RTm ⌊ Δ ⌋} {g a : RTm ⌊ Δ ⌋} →
             Δ ⊢ d ∷ Nat →
             Δ ⊢ g ∷ CtxK d →
             Δ ⊢ a ∷ K (pair sTy d) →
             Δ ⊢ Ctx-extK d g a ∷ CtxK (nsuc d)
⊢Ctx-extKt {Δ = Δ} {d = d} {g = g} {a = a} dx dg da =
  ⊢icon CtxWf (thereID hereID) (toI (⊢nsuc dx))
    (⊢pair (ty-Σ (ty-IMu CtxWf (⊢var here))
             (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (there here))))))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢nsuc (⊢wk (⊢wk (⊢wk dx)))))
                              (toI (⊢nsuc (fromI (⊢var (there (there here))))))))
                     ty-Unit)))
           (toI dx)
      (⊢pair (ty-Σ (ty-El (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy dw1)))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢nsuc dw2))
                              (toI (⊢nsuc dw2'))))
                     ty-Unit))
             dg
        (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢nsuc dw3))
                              (toI (⊢nsuc dw3'))))
                     ty-Unit)
               (toKn (kCast (sym (wk-single {v = g} d)) da))
          (⊢pair ty-Unit (⊢-cast eqFord (reflId (⊢nsuc dx))) ⊢unit))))
  where
    rtA : (v X : RTm ⌊ Δ ⌋) → subTm (extS (single v)) (w (w X)) ≡ w X
    rtA v X = sub-w-single X

    rt₂ : (X : RTm ⌊ Δ ⌋) →
          subTm (extS (extS (single d))) (w (w (w X))) ≡ w (w X)
    rt₂ X = trans (sub-w² {σ = single d} (w X))
                  (cong (λ z → w (w z)) (wk-single {v = d} X))

    dw1 : _
    dw1 = ⊢wk dx
    dw2 : _
    dw2 = tmCast (sym (rt₂ d)) (⊢wk (⊢wk dx))
    dw2' : _
    dw2' = ⊢wk (⊢wk dx)
    rt₃ : (X : RTm ⌊ Δ ⌋) →
          subTm (extS (single g)) (subTm (extS (extS (single d))) (w (w (w X))))
            ≡ w X
    rt₃ X = trans (cong (subTm (extS (single g))) (rt₂ X)) (rtA g X)

    dw3 : _
    dw3 = tmCast (sym (rt₃ d)) (⊢wk dx)
    dw3' : _
    dw3' = tmCast (sym (rtA g d)) (⊢wk dx)

    rt₄ : (X : RTm ⌊ Δ ⌋) →
          subTm (single a)
                (subTm (extS (single g))
                       (subTm (extS (extS (single d))) (w (w (w X)))))
            ≡ X
    rt₄ X = trans (cong (subTm (single a)) (rt₃ X)) (wk-single {v = a} X)

    rt₄ᵣ : (X : RTm ⌊ Δ ⌋) →
           subTm (single a) (subTm (extS (single g)) (w (w X))) ≡ X
    rt₄ᵣ X = trans (cong (subTm (single a)) (rtA g X)) (wk-single {v = a} X)

    eqFord : _
    eqFord = cong₂ (λ z₁ z₂ → El (⌜Id⌝ ⌜Nat⌝ z₁ (nsuc z₂)))
                   (sym (rt₄ (nsuc d))) (sym (rt₄ᵣ d))


⊢Ctx-extK : {Δ : Ctx} (n : ℕ) {g a : RTm ⌊ Δ ⌋} →
            Δ ⊢ g ∷ CtxK (num n) →
            Δ ⊢ a ∷ K (pair sTy (num n)) →
            Δ ⊢ Ctx-extK (num n) g a ∷ CtxK (num (suc n))
⊢Ctx-extK n = ⊢Ctx-extKt (⊢num n)

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
-- 7. `_▹_` AT A **VARIABLE** DEPTH — kept as a NAME, not a proof.
--
-- ⚠ §4's `⊢Ctx-extK` is at `num n` because its customer is the adequacy
--   map, whose depths are `len ⌊ Γ ⌋`.  A JUDGEMENT's constructor
--   telescope is the other case: its depth is a bound `iκ ⌜Nat⌝` field,
--   i.e. a VARIABLE.  Both are now one line over `⊢Ctx-extKt`; the two
--   signatures survive because ten call sites read better at them and
--   because they say which shape their caller is in.
------------------------------------------------------------------------

⊢Ctx-extKv : {Δ : Ctx} {x : Var ⌊ Δ ⌋} {g a : RTm ⌊ Δ ⌋} →
             Δ ⊢ var x ∷ Nat →
             Δ ⊢ g ∷ CtxK (var x) →
             Δ ⊢ a ∷ K (pair sTy (var x)) →
             Δ ⊢ Ctx-extK (var x) g a ∷ CtxK (nsuc (var x))
⊢Ctx-extKv = ⊢Ctx-extKt
