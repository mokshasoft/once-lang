------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★ THE KNOT IS INHABITED.
--
-- ⚠⚠ WITHOUT THIS FILE, `Knot/Wf` IS
--   `verification-that-covers-less-than-it-claims`.  A description can
--   be well-formed and have NO CLOSED INHABITANT at any index —
--   `Examples/Vec.no-cons-at-zero` is that hazard proved on purpose, and
--   `Examples/PairIx` §3 exists for the same reason.  `KnotWf` says the
--   WF judgement accepts 53 rows; it does not say anything lives at one.
--
-- ★ WHAT IS BUILT, chosen to cover every encoding decision the generator
--   makes and not one row more:
--
--     kNat    `Nat`, sort 0        — a FORD-ONLY row (no fields at all)
--     kvz     `vz`, sort 6         — the DEPTH-FORDED row, the only
--                                    shape in the table that constrains
--                                    the second component
--     kvar    `var v`, sort 1      — a CROSS-SORT field (1 ← 6)
--     klam    `lam b`, sort 1      — the BINDER: depth PUSHED
--     kdk     `dκ`, sort 3         — a field PINNED AT DEPTH 0 beside a
--                                    same-depth one, i.e. `RTy ε`
--
--   and then `kid = klam (kvar kvz) : K (1, 0)` — the encoding of
--   `lam (var vz)`, closed, at depth zero.  That is the smallest term
--   that uses the binder, the scope-safe variable and two sorts at once.
--
-- ⚠ THE PROJECTIONS ARE WHAT THIS COSTS, exactly as §14 priced them.  At
--   a concrete index `pair t d` a field's type still reads
--   `fst (pair t d)` / `snd (pair t d)`, and `fst`/`snd` are TERM
--   FORMERS stepping by `βfst`/`βsnd` — not definitional projections.
--   So every constraint field needs `ξ-El (ξ-⌜Id⌝ˡ …)` and every
--   recursive field whose index mentions the ambient needs `ξ-IMu`.
--   Boilerplate, and the reason a field pinned at a LITERAL index
--   (`dκ`'s first) needs no conversion at all.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Terms where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; RTm; El; Unit; Nat; Σ'; IMu
        ; var; pair; fst; snd; unit; nzero; nsuc; ⌜Nat⌝; ⌜Id⌝; idrefl; icon )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv
        ; ⊢pair; ⊢fst; ⊢snd; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢idrefl
        ; ⊢icon
        ; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-IMu
        ; _⟶_; βfst; βsnd; ξ-pairʳ; ξ-nsuc
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; credᵀ
        ; El-⌜Id⌝; ξ-El; ξ-IMu; ξ-⌜Id⌝ˡ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sDCon; sVar; ⊢sTy; ⊢sTm; ⊢sDCon; ⊢sVar
        ; toI; fromI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagTy-Nat; tagTm-var; tagTm-lam; tagDCon-i; tagDCon-kap; tagVar-vz
        ; memTy-Nat; memTm-var; memTm-lam; memDCon-i; memDCon-kap; memVar-vz )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )

------------------------------------------------------------------------
-- 0. THE FOUR THINGS EVERY ROW NEEDS.
------------------------------------------------------------------------

-- move a term along a reduction OF THE INDEX
ixConv : {Γ : Ctx} {t i i' : RTm ⌊ Γ ⌋} →
         i ⟶ i' → Γ ⊢ t ∷ K i' → Γ ⊢ t ∷ K i
ixConv r d = ⊢conv d (csymᵀ (credᵀ (ξ-IMu r)))

-- the SORT ford at a concrete index: `fst (pair t d)` must STEP first
fordFst : {Γ : Ctx} {t d : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat →
          Γ ⊢ idrefl ⌜Nat⌝ t ∷ El (⌜Id⌝ ⌜Nat⌝ (fst (pair t d)) t)
fordFst {t = t} {d = d} dt =
  ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI dt))
    (csymᵀ (ctrnᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βfst t d))))
                  (credᵀ (El-⌜Id⌝ ⌜Nat⌝ t t))))

-- …and the DEPTH ford, the same one step lower
fordSnd : {Γ : Ctx} {t d : RTm ⌊ Γ ⌋} → Γ ⊢ d ∷ Nat →
          Γ ⊢ idrefl ⌜Nat⌝ d ∷ El (⌜Id⌝ ⌜Nat⌝ (snd (pair t d)) d)
fordSnd {t = t} {d = d} dd =
  ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI dd))
    (csymᵀ (ctrnᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βsnd t d))))
                  (credᵀ (El-⌜Id⌝ ⌜Nat⌝ d d))))

tyFordFst : {Γ : Ctx} {t d : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ d ∷ Nat →
            Γ ⊢ty Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (pair t d)) t)) Unit
tyFordFst dt dd =
  ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP dt dd))) (toI dt))) ty-Unit

------------------------------------------------------------------------
-- ⚠ EVERY WITNESS BELOW IS AT A **CONCRETE** INDEX, and that is forced,
--   not stylistic.  At an abstract depth `d` the payload's tail types
--   read `subTm (single a) (w (pair s d))`, and `subTm (single a) (w d)`
--   is `wk-single` — PROPOSITIONAL, not definitional — so a
--   depth-polymorphic witness pays a transport per field for nothing.
--   At a numeral the whole index computes and every one of them
--   vanishes.  `Examples/PairIx` §3 is at concrete indices for exactly
--   this reason, and so is `Examples/Scoped`'s `⊢fz`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. `Nat`, sort 0 — the FORD-ONLY shape.  32 of the 53 rows look
--    exactly like this modulo their tag, so one witness settles them.
------------------------------------------------------------------------

kNat : {Γ : Cx} → RTm Γ
kNat = icon tagTy-Nat (pair (idrefl ⌜Nat⌝ sTy) unit)

⊢kNat : {Γ : Ctx} → Γ ⊢ kNat ∷ K (pair sTy nzero)
⊢kNat = ⊢icon KnotWf memTy-Nat (⊢ixP ⊢sTy ⊢nzero)
          (⊢pair ty-Unit (fordFst ⊢sTy) ⊢unit)

------------------------------------------------------------------------
-- 2. `vz`, sort 6 — ★★ THE DEPTH-FORDED ROW.
--
-- ⚠ THE ONLY SHAPE IN THE TABLE THAT CONSTRAINS THE SECOND COMPONENT.
--   `vz : Var (Γ ∙)` exists only at `suc m`, so it binds an `m : Nat`
--   and Fords the depth against `suc m` — Fording used exactly as
--   `Scoped`'s `Fin` uses it, and the reason §14's rule is "Ford the
--   COMPONENT, not the pair": BOTH components can need it, and they
--   need it INDEPENDENTLY.
------------------------------------------------------------------------

kvz : {Γ : Cx} → RTm Γ
kvz = icon tagVar-vz
        (pair nzero
          (pair (idrefl ⌜Nat⌝ sVar) (pair (idrefl ⌜Nat⌝ (nsuc nzero)) unit)))

⊢kvz : {Γ : Ctx} → Γ ⊢ kvz ∷ K (pair sVar (nsuc nzero))
⊢kvz =
  ⊢icon KnotWf memVar-vz (⊢ixP ⊢sVar (⊢nsuc ⊢nzero))
    (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                          (toI (⊢fst (⊢ixP ⊢sVar (⊢nsuc ⊢nzero)))) (toI ⊢sVar)))
                 (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                (toI (⊢snd (⊢ixP ⊢sVar (⊢nsuc ⊢nzero))))
                                (toI (⊢nsuc (fromI (⊢var (there here)))))))
                       ty-Unit))
           (toI ⊢nzero)
           (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                 (toI (⊢snd (⊢ixP ⊢sVar (⊢nsuc ⊢nzero))))
                                 (toI (⊢nsuc ⊢nzero))))
                        ty-Unit)
                  (fordFst ⊢sVar)
                  (⊢pair ty-Unit (fordSnd (⊢nsuc ⊢nzero)) ⊢unit)))

------------------------------------------------------------------------
-- 3. `var`, sort 1 — a CROSS-SORT field (a term whose child is a `Var`),
--    and `lam` — ★ THE BINDER, whose field's depth is `suc` of the
--    ambient's second component.
------------------------------------------------------------------------

kvar klam : {Γ : Cx} → RTm Γ → RTm Γ
kvar v = icon tagTm-var (pair v (pair (idrefl ⌜Nat⌝ sTm) unit))
klam b = icon tagTm-lam (pair b (pair (idrefl ⌜Nat⌝ sTm) unit))

⊢kvar : {Γ : Ctx} {v : RTm ⌊ Γ ⌋} →
        Γ ⊢ v ∷ K (pair sVar (nsuc nzero)) →
        Γ ⊢ kvar v ∷ K (pair sTm (nsuc nzero))
⊢kvar dv =
  ⊢icon KnotWf memTm-var (⊢ixP ⊢sTm (⊢nsuc ⊢nzero))
    (⊢pair (tyFordFst ⊢sTm (⊢nsuc ⊢nzero))
           (ixConv (ξ-pairʳ (βsnd sTm (nsuc nzero))) dv)
           (⊢pair ty-Unit (fordFst ⊢sTm) ⊢unit))

-- ★★★ THE BINDER.  The field's index is `pair 1 (suc (snd (pair 1 0)))`
--   — the ambient's SECOND component, pushed.
⊢klam : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} →
        Γ ⊢ b ∷ K (pair sTm (nsuc nzero)) → Γ ⊢ klam b ∷ K (pair sTm nzero)
⊢klam db =
  ⊢icon KnotWf memTm-lam (⊢ixP ⊢sTm ⊢nzero)
    (⊢pair (tyFordFst ⊢sTm ⊢nzero)
           (ixConv (ξ-pairʳ (ξ-nsuc (βsnd sTm nzero))) db)
           (⊢pair ty-Unit (fordFst ⊢sTm) ⊢unit))

------------------------------------------------------------------------
-- 4. `dι` / `dκ`, sort 3 — ★ A FIELD PINNED AT DEPTH 0.
--
-- `dκ : RTy ε → DCon → DCon` carries an `RTy` AT THE EMPTY CONTEXT, so
-- its index is the LITERAL `pair 0 0` while the sibling `DCon` field
-- rides at the ambient depth.  ⚠ Note the asymmetry in what they cost:
-- the literal one needs NO conversion, the riding one needs `βsnd`.
-- That is the whole reason the closed sorts are left depth-degenerate
-- rather than Forded to 0 — the pin is expressible per-field, for free.
------------------------------------------------------------------------

kdi : {Γ : Cx} → RTm Γ
kdi = icon tagDCon-i (pair (idrefl ⌜Nat⌝ sDCon) unit)

kdk : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
kdk a c = icon tagDCon-kap
            (pair a (pair c (pair (idrefl ⌜Nat⌝ sDCon) unit)))

⊢kdi : {Γ : Ctx} → Γ ⊢ kdi ∷ K (pair sDCon nzero)
⊢kdi = ⊢icon KnotWf memDCon-i (⊢ixP ⊢sDCon ⊢nzero)
         (⊢pair ty-Unit (fordFst ⊢sDCon) ⊢unit)

⊢kdk : {Γ : Ctx} {a c : RTm ⌊ Γ ⌋} →
       Γ ⊢ a ∷ K (pair sTy nzero) → Γ ⊢ c ∷ K (pair sDCon nzero) →
       Γ ⊢ kdk a c ∷ K (pair sDCon nzero)
⊢kdk da dc =
  ⊢icon KnotWf memDCon-kap (⊢ixP ⊢sDCon ⊢nzero)
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sDCon (⊢snd (⊢ixP ⊢sDCon ⊢nzero))))
                 (tyFordFst ⊢sDCon ⊢nzero))
           da
           (⊢pair (tyFordFst ⊢sDCon ⊢nzero)
                  (ixConv (ξ-pairʳ (βsnd sDCon nzero)) dc)
                  (⊢pair ty-Unit (fordFst ⊢sDCon) ⊢unit)))

------------------------------------------------------------------------
-- 5. ★★★ `lam (var vz)`, ENCODED — closed, at depth zero.
------------------------------------------------------------------------

kid : {Γ : Cx} → RTm Γ
kid = klam (kvar kvz)

⊢kid : ◇ ⊢ kid ∷ K (pair sTm nzero)
⊢kid = ⊢klam (⊢kvar ⊢kvz)

-- …and a `DCon` over it, so the depth-0 pin is exercised at a real term.
kdcon : {Γ : Cx} → RTm Γ
kdcon = kdk kNat kdi

⊢kdcon : ◇ ⊢ kdcon ∷ K (pair sDCon nzero)
⊢kdcon = ⊢kdk ⊢kNat ⊢kdi
