------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE PER-FIELD RULE FOR OBJECT-LEVEL
-- WEAKENING, at the rows that bracket the table.
--
-- `PLAN-JUDGEMENT` step 2 needs `renTy vs` as an `ielim` over the knot
-- returning a KNOT ELEMENT, at the uniform motive
--
--     M(i,t) = K (pair (fst ⟨i⟩) (nsuc (snd ⟨i⟩)))
--
-- ⚠⚠ AND `Lib/IFold`'s SHAPE DOES NOT REACH IT.  A fold into a CONSTANT
--   motive takes the IH at every `iρ`.  A weakening does not — which is
--   the whole content of this file, and the one thing that had to be
--   settled before 53 methods are computed from the description.
--
-- ★ THREE ROWS, CHOSEN TO BRACKET EVERY CASE:
--
--     cTy-Nat     FORD-ONLY          — is the tag ford free?
--     cTm-lam     RIDING index       — does the IH land where the
--                                      rebuilt row wants it?
--     cDCon-kap   a LITERAL-PINNED field beside a RIDING one — ★ THE
--                                      ROW THE RULE IS ABOUT
--
--   (`cVar-vs`, the depth-Forded shape, is §5.)
--
-- ★★★ THE RULE, and `cDCon-kap` is where it bites.  `dκ : RTy ε → DCon
--   → DCon` pins its first field at the LITERAL index `pair sTy nzero`.
--   Its IH therefore lands at `K (pair sTy (nsuc nzero))` — depth ONE —
--   while the rebuilt row still wants depth ZERO.  So that field takes
--   the **ORIGINAL FIELD** out of the payload and IGNORES its IH, while
--   its sibling `DCon` field, whose index RIDES the ambient, takes the
--   IH.  Two `iρ` fields, one row, opposite treatments.
--
--   ⇒ the choice is a function of whether the field's index expression
--     MENTIONS THE AMBIENT — which is decidable on `ICon`'s raw `RTm`
--     indices, so a generic `Lib/IWk` can compute it.
--
-- ★★★ RESULT: ALL FOUR ROWS TYPE, AT ONE MOTIVE, AND THE COSTS ARE:
--
--     the tag ford        FREE — `βfst` takes the shifted constraint to
--                         the field the method was handed (`unFst`).
--     a RIDING field      the IH, moved FORWARD off the eliminator's
--                         index and BACKWARD onto the row's.  Conversions
--                         only — no transport.
--     a PINNED field      the ORIGINAL field; its IH is never named.
--     a DEPTH-FORDED row  the riding case PLUS one `congS`, i.e. one
--                         `jsub` — ⚠ in `cVar-vz`/`cVar-vs` ONLY.
--
-- ★★ AND THE TABLE, COUNTED BY SHAPE (measured off `gen-knot.py`'s
--   KNOT, not estimated — `verification-that-covers-less-than-it-claims`
--   applies to census numbers too):
--
--     53   rows
--     13   FORD-ONLY rows — no fields at all beside the tag ford
--     77   RIDING recursive fields — the common case, IH everywhere
--      4   rows with a PINNED-index recursive field, and they are:
--            cTy-IMu, cTm-cIMu, cDCon-kap   `RTy ε`      at `pair sTy 0`
--            cIDesc-cons                    `ICon (ε ∙)` at `pair sICon 1`
--      2   DEPTH-FORDED rows — `cVar-vz`, `cVar-vs`
--
--   ⇒ the ORIGINAL-field rule has FOUR customers and the transport has
--     TWO.  Everything else is the riding case.
--
-- ⚠ SCOPE, STATED HONESTLY.  FOUR methods are built, chosen to bracket
--   the table.  The 53-method fold is NOT built and neither is the
--   `Lib/IWk` that would compute them; what is established is that no
--   row shape needs a treatment other than these four, and what each
--   costs.
--
-- ⚠ AND THE ONE HELPER `Knot/Terms` COULD NOT SUPPLY IS `tyFordAt`.
--   `tyFordFst` was written for a CONCRETE index and reuses one
--   derivation as BOTH the pair's first component and the `⌜Id⌝`'s right
--   endpoint.  In a METHOD the index is abstract, so those differ:
--   `fst ⟨i⟩` against the row's literal tag.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.WkRows where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs
        ; RTy; RTm; El; Unit; Nat; Σ'
        ; var; pair; fst; snd; unit; nzero; nsuc; ⌜Nat⌝; ⌜Id⌝; icon; lam
        ; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢lam
        ; ⊢pair; ⊢fst; ⊢snd; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢icon
        ; ty-El; ty-Unit; ty-Σ; ty-IMu
        ; imethTy
        ; _⟶_; βfst; βsnd; ξ-pairˡ; ξ-pairʳ; ξ-nsuc
        ; _≅ᵀ_; csymᵀ; credᵀ; ξ-El; ξ-IMu; ξ-⌜Id⌝ˡ )
open import DirectedHoTT.Lib.ArithComm using ( congS; ⊢congS; elIdN )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; sTm; sDCon; sVar; ⊢sTy; ⊢sTm; ⊢sDCon; ⊢sVar
        ; toI; fromI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cTy-Nat; cTm-lam; cDCon-kap; cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagTy-Nat; tagTm-lam; tagDCon-kap; tagVar-vz; tagVar-vs
        ; memTy-Nat; memTm-lam; memDCon-kap; memVar-vz; memVar-vs )

------------------------------------------------------------------------
-- 0. MOVING ALONG A REDUCTION OF THE INDEX, both ways.
--
-- ⚠ BOTH DIRECTIONS ARE NEEDED, and that is the shape of every method
--   here.  The IH arrives at an index the ELIMINATOR built; the rebuilt
--   row wants one the DESCRIPTION built.  They have the same normal form
--   and neither is the other, so a method goes FORWARD from the IH and
--   BACKWARD into the row.
------------------------------------------------------------------------

ixBack : {Γ : Ctx} {t i i' : RTm ⌊ Γ ⌋} →
         i ⟶ i' → Γ ⊢ t ∷ K i' → Γ ⊢ t ∷ K i
ixBack r d = ⊢conv d (csymᵀ (credᵀ (ξ-IMu r)))

ixFwd : {Γ : Ctx} {t i i' : RTm ⌊ Γ ⌋} →
        i ⟶ i' → Γ ⊢ t ∷ K i → Γ ⊢ t ∷ K i'
ixFwd r d = ⊢conv d (credᵀ (ξ-IMu r))

-- ★ THE TAG FORD IS FREE, and this is why: at the shifted index the
--   constraint reads `fst (pair (fst ⟨i⟩) …) ≡ s`, and `βfst` takes that
--   to `fst ⟨i⟩ ≡ s` — the field the method was HANDED.  No new witness,
--   no transport; one conversion.
unFst : {Γ : Ctx} {a b s t : RTm ⌊ Γ ⌋} →
        Γ ⊢ t ∷ El (⌜Id⌝ ⌜Nat⌝ a s) →
        Γ ⊢ t ∷ El (⌜Id⌝ ⌜Nat⌝ (fst (pair a b)) s)
unFst {a = a} {b = b} d =
  ⊢conv d (csymᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βfst a b)))))

-- …and the TYPE of that ford, at the shifted index.
--
-- ⚠ NOT `Knot/Terms.tyFordFst`, which was written for a CONCRETE index
--   and so reuses one derivation as BOTH the pair's first component and
--   the `⌜Id⌝`'s right endpoint.  Here they differ: the component is
--   `fst ⟨i⟩`, abstract, and the endpoint is the row's literal sort tag.
--   That is the one place a method over an ABSTRACT index needs its own
--   helper.
tyFordAt : {Γ : Ctx} {a b s : RTm ⌊ Γ ⌋} →
           Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ s ∷ Nat →
           Γ ⊢ty Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (pair a b)) s)) Unit
tyFordAt da db ds =
  ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP da db))) (toI ds))) ty-Unit

------------------------------------------------------------------------
-- 1. THE MOTIVE — the uniform shift.
------------------------------------------------------------------------

wkMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
wkMot = K (pair (fst (var (vs vz))) (nsuc (snd (var (vs vz)))))

⊢wkMot : {Γ : Ctx} → ((Γ ▹ εwkTy IPair) ▹ K (var vz)) ⊢ty wkMot
⊢wkMot = ty-IMu KnotWf (⊢ixP (⊢fst (⊢var (there here)))
                             (⊢nsuc (⊢snd (⊢var (there here)))))

------------------------------------------------------------------------
-- 2. `cTy-Nat` — THE FORD-ONLY SHAPE.  32 rows look like this.
------------------------------------------------------------------------

tyPayNat : {Γ : Ctx} → (Γ ▹ Σ' Nat Nat) ⊢ty
           Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var vz)) sTy)) Unit
tyPayNat = ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var here))) (toI ⊢sTy)))
                ty-Unit

wkTyNat : {Γ : Cx} → RTm Γ
wkTyNat = lam (lam (lam (icon tagTy-Nat (pair (fst (var (vs vz))) unit))))

⊢wkTyNat : {Γ : Ctx} →
           Γ ⊢ wkTyNat ∷ imethTy KnotD IPair tagTy-Nat cTy-Nat wkMot
⊢wkTyNat =
  ⊢lam ⊢IPair
    (⊢lam tyPayNat
      (⊢lam ty-Unit
        (⊢icon KnotWf memTy-Nat
               (⊢ixP (⊢fst (⊢var (there (there here))))
                     (⊢nsuc (⊢snd (⊢var (there (there here))))))
               (⊢pair ty-Unit
                      (unFst (⊢fst (⊢var (there here))))
                      ⊢unit))))

------------------------------------------------------------------------
-- 3. `cTm-lam` — THE RIDING INDEX, under a BINDER.
--
-- ★ The IH lands EXACTLY where the rebuilt row wants it, and that is
--   `Examples/WkTm`'s result restated over a pair index: weakening at
--   the OUTSIDE shifts uniformly, so under `lam` the body's IH is the
--   same function one index up.  What it costs is conversions, not
--   transports.
------------------------------------------------------------------------

tyPayLam : {Γ : Ctx} → (Γ ▹ Σ' Nat Nat) ⊢ty
           Σ' (K (pair sTm (nsuc (snd (var vz)))))
             (Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var (vs vz))) sTm)) Unit)
tyPayLam =
  ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢nsuc (⊢snd (⊢var here)))))
    (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (there here)))) (toI ⊢sTm)))
          ty-Unit)

tyIHLam : {Γ : Ctx} →
          ((Γ ▹ Σ' Nat Nat) ▹
            Σ' (K (pair sTm (nsuc (snd (var vz)))))
              (Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var (vs vz))) sTm)) Unit)) ⊢ty _
tyIHLam =
  ty-Σ (ty-IMu KnotWf
         (⊢ixP (⊢fst (⊢ixP ⊢sTm (⊢nsuc (⊢snd (⊢var (there here))))))
               (⊢nsuc (⊢snd (⊢ixP ⊢sTm (⊢nsuc (⊢snd (⊢var (there here)))))))))
       ty-Unit

wkTmLam : {Γ : Cx} → RTm Γ
wkTmLam =
  lam (lam (lam
    (icon tagTm-lam (pair (fst (var vz))
                          (pair (fst (snd (var (vs vz)))) unit)))))

⊢wkTmLam : {Γ : Ctx} →
           Γ ⊢ wkTmLam ∷ imethTy KnotD IPair tagTm-lam cTm-lam wkMot
⊢wkTmLam =
  ⊢lam ⊢IPair
    (⊢lam tyPayLam
      (⊢lam tyIHLam
        (⊢icon KnotWf memTm-lam
               (⊢ixP (⊢fst (⊢var (there (there here))))
                     (⊢nsuc (⊢snd (⊢var (there (there here))))))
               -- ⚠ TWO THINGS AT ONCE, AND BOTH BIT.  `⊢pair`'s B lives
               --   one binder DEEPER than the components beside it, and
               --   the ford it describes is at the SHIFTED index — so its
               --   left endpoint is `fst (pair …)`, not `fst ⟨i⟩`.
               --   `Knot/Terms.tyFordFst` is exactly that shape.
               (⊢pair (tyFordAt (⊢fst (⊢var (there (there (there here)))))
                                (⊢nsuc (⊢snd (⊢var (there (there (there here))))))
                                ⊢sTm)
                      -- ★ THE IH, moved forward off the eliminator's
                      --   index and backward onto the row's.
                      (ixBack (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
                        (ixFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
                          (ixFwd (ξ-pairˡ (βfst _ _)) (⊢fst (⊢var here)))))
                      (⊢pair ty-Unit
                             (unFst (⊢fst (⊢snd (⊢var (there here)))))
                             ⊢unit)))))

------------------------------------------------------------------------
-- 4. ★★★ `cDCon-kap` — THE ROW THE RULE IS ABOUT.
--
--     dκ : RTy ε → DCon → DCon
--
-- TWO `iρ` fields, and they must be treated OPPOSITELY:
--
--   field 0, `RTy ε`, is pinned at the LITERAL index `pair sTy nzero`.
--     Its IH lands at `K (pair sTy (nsuc nzero))` — depth ONE — and the
--     rebuilt row still wants depth ZERO.  ⇒ take the **ORIGINAL FIELD**
--     out of the payload; the IH is unusable and is simply not named.
--
--   field 1, `DCon`, RIDES the ambient.  ⇒ take the **IH**.
--
-- ⇒ THAT IS THE PER-FIELD RULE, and it is why `Lib/IFold`'s shape does
--   not reach a weakening: a fold into a constant motive can take the IH
--   everywhere, and this cannot.
------------------------------------------------------------------------

tyPayKap : {Γ : Ctx} → (Γ ▹ Σ' Nat Nat) ⊢ty
           Σ' (K (pair sTy nzero))
             (Σ' (K (pair sDCon (snd (var (vs vz)))))
               (Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDCon)) Unit))
tyPayKap =
  ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTy ⊢nzero))
    (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sDCon (⊢snd (⊢var (there here)))))
      (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (there (there here)))))
                                 (toI ⊢sDCon)))
            ty-Unit))

tyIHKap : {Γ : Ctx} →
          ((Γ ▹ Σ' Nat Nat) ▹
            Σ' (K (pair sTy nzero))
              (Σ' (K (pair sDCon (snd (var (vs vz)))))
                (Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDCon)) Unit)))
          ⊢ty _
tyIHKap =
  ty-Σ (ty-IMu KnotWf
         (⊢ixP (⊢fst (⊢ixP ⊢sTy ⊢nzero)) (⊢nsuc (⊢snd (⊢ixP ⊢sTy ⊢nzero)))))
    (ty-Σ (ty-IMu KnotWf
            (⊢ixP (⊢fst (⊢ixP ⊢sDCon (⊢snd (⊢var (there (there here))))))
                  (⊢nsuc (⊢snd (⊢ixP ⊢sDCon
                                 (⊢snd (⊢var (there (there here)))))))))
          ty-Unit)

wkDkap : {Γ : Cx} → RTm Γ
wkDkap =
  lam (lam (lam
    (icon tagDCon-kap
      (pair (fst (var (vs vz)))                      -- ★ THE ORIGINAL FIELD
        (pair (fst (snd (var vz)))                   -- …and the IH beside it
          (pair (fst (snd (snd (var (vs vz))))) unit))))))

⊢wkDkap : {Γ : Ctx} →
          Γ ⊢ wkDkap ∷ imethTy KnotD IPair tagDCon-kap cDCon-kap wkMot
⊢wkDkap =
  ⊢lam ⊢IPair
    (⊢lam tyPayKap
      (⊢lam tyIHKap
        (⊢icon KnotWf memDCon-kap
               (⊢ixP (⊢fst (⊢var (there (there here))))
                     (⊢nsuc (⊢snd (⊢var (there (there here))))))
          (⊢pair (ty-Σ (ty-IMu KnotWf
                         (⊢ixP ⊢sDCon
                           (⊢snd (⊢ixP (⊢fst (⊢var (there (there (there here)))))
                                       (⊢nsuc (⊢snd (⊢var (there (there (there here))))))))))
                       (tyFordAt (⊢fst (⊢var (there (there (there (there here))))))
                                 (⊢nsuc (⊢snd (⊢var (there (there (there (there here)))))))
                                 ⊢sDCon))
                 -- ★★★ THE ORIGINAL FIELD.  Its IH is at depth 1 and this
                 --   row wants depth 0, so the IH is never named.
                 (⊢fst (⊢var (there here)))
            (⊢pair (tyFordAt (⊢fst (⊢var (there (there (there here)))))
                             (⊢nsuc (⊢snd (⊢var (there (there (there here))))))
                             ⊢sDCon)
                   -- …and its sibling takes the IH.
                   (ixBack (ξ-pairʳ (βsnd _ _))
                     (ixFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
                       (ixFwd (ξ-pairˡ (βfst _ _)) (⊢fst (⊢snd (⊢var here))))))
              (⊢pair ty-Unit
                     (unFst (⊢fst (⊢snd (⊢snd (⊢var (there here))))))
                     ⊢unit))))))

------------------------------------------------------------------------
-- 5. `cVar-vs` — THE DEPTH-FORDED SHAPE, and the one transport.
--
--     vs : Var Γ → Var (Γ ∙)
--
-- ⚠ ITS TARGET DEPTH IS CONSTRAINED, so it holds `snd ⟨i⟩ ≡ suc m` and
--   the rebuilt row needs `snd ⟨i'⟩ ≡ suc m'` at the BUMPED `m' = suc m`.
--   `βsnd` takes `snd ⟨i'⟩` to `nsuc (snd ⟨i⟩)`, so what is left is
--   exactly `cong nsuc` on the ford it was handed — `Lib/ArithComm.congS`,
--   which is a `jsub`.
--
-- ★ ONE TRANSPORT, IN THIS ROW AND `cVar-vz` ONLY — 2 of the 53, not 53.
--   And the recursive field still takes its IH: the child sits at `m` and
--   the IH at `nsuc m`, which is the new `m'`.  ⇒ a depth-Forded row is
--   the RIDING case plus one `congS`, not a third treatment.
------------------------------------------------------------------------

tyPayVs : {Γ : Ctx} → (Γ ▹ Σ' Nat Nat) ⊢ty
          Σ' (El ⌜Nat⌝)
            (Σ' (K (pair sVar (var vz)))
              (Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sVar))
                (Σ' (El (⌜Id⌝ ⌜Nat⌝ (snd (var (vs (vs (vs vz)))))
                                    (nsuc (var (vs (vs vz)))))) Unit)))
tyPayVs =
  ty-Σ (ty-El ⊢⌜Nat⌝)
    (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (fromI (⊢var here))))
      (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (there (there here)))))
                                 (toI ⊢sVar)))
        (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                       (toI (⊢snd (⊢var (there (there (there here))))))
                       (toI (⊢nsuc (fromI (⊢var (there (there here))))))))
              ty-Unit)))

tyIHVs : {Γ : Ctx} →
         ((Γ ▹ Σ' Nat Nat) ▹
           Σ' (El ⌜Nat⌝)
             (Σ' (K (pair sVar (var vz)))
               (Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sVar))
                 (Σ' (El (⌜Id⌝ ⌜Nat⌝ (snd (var (vs (vs (vs vz)))))
                                     (nsuc (var (vs (vs vz)))))) Unit))))
         ⊢ty _
tyIHVs =
  ty-Σ (ty-IMu KnotWf
         (⊢ixP (⊢fst (⊢ixP ⊢sVar (fromI (⊢fst (⊢var here)))))
               (⊢nsuc (⊢snd (⊢ixP ⊢sVar (fromI (⊢fst (⊢var here))))))))
       ty-Unit

wkVarVs : {Γ : Cx} → RTm Γ
wkVarVs =
  lam (lam (lam
    (icon tagVar-vs
      (pair (nsuc (fst (var (vs vz))))                 -- m' := suc m
        (pair (fst (var vz))                            -- the IH
          (pair (fst (snd (snd (var (vs vz)))))         -- the tag ford
            (pair (congS (snd (var (vs (vs vz))))       -- ★ THE TRANSPORT
                         (fst (snd (snd (snd (var (vs vz)))))))
                  unit)))))))

⊢wkVarVs : {Γ : Ctx} →
           Γ ⊢ wkVarVs ∷ imethTy KnotD IPair tagVar-vs cVar-vs wkMot
⊢wkVarVs =
  ⊢lam ⊢IPair
    (⊢lam tyPayVs
      (⊢lam tyIHVs
        (⊢icon KnotWf memVar-vs
               (⊢ixP (⊢fst (⊢var (there (there here))))
                     (⊢nsuc (⊢snd (⊢var (there (there here))))))
          (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (fromI (⊢var here))))
                   (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                  (toI (⊢fst (⊢ixP
                                     (⊢fst (⊢var (there (there (there (there here))))))
                                     (⊢nsuc (⊢snd (⊢var (there (there (there (there here)))))))))) 
                                  (toI ⊢sVar)))
                     (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                    (toI (⊢snd (⊢ixP
                                       (⊢fst (⊢var (there (there (there (there (there here)))))))
                                       (⊢nsuc (⊢snd (⊢var (there (there (there (there (there here))))))))))) 
                                    (toI (⊢nsuc (fromI (⊢var (there (there here))))))))
                           ty-Unit)))
                 (toI (⊢nsuc (fromI (⊢fst (⊢var (there here))))))
            (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                  (toI (⊢fst (⊢ixP
                                     (⊢fst (⊢var (there (there (there here)))))
                                     (⊢nsuc (⊢snd (⊢var (there (there (there here))))))))) 
                                  (toI ⊢sVar)))
                     (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                    (toI (⊢snd (⊢ixP
                                       (⊢fst (⊢var (there (there (there (there here))))))
                                       (⊢nsuc (⊢snd (⊢var (there (there (there (there here))))))))))
                                    (toI (⊢nsuc (⊢nsuc (fromI (⊢fst (⊢var (there (there (there here)))))))))))
                           ty-Unit))
                   -- the child still takes its IH: it sits at `m` and the
                   -- IH at `nsuc m`, which IS the bumped `m'`.
                   (ixFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
                     (ixFwd (ξ-pairˡ (βfst _ _)) (⊢fst (⊢var here))))
              (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                    (toI (⊢snd (⊢ixP
                                       (⊢fst (⊢var (there (there (there here)))))
                                       (⊢nsuc (⊢snd (⊢var (there (there (there here)))))))))
                                    (toI (⊢nsuc (⊢nsuc (fromI (⊢fst (⊢var (there (there here))))))))))
                           ty-Unit)
                     (unFst (⊢fst (⊢snd (⊢snd (⊢var (there here))))))
                (⊢pair ty-Unit
                       -- ★★★ THE TRANSPORT.  `snd ⟨i'⟩ ⟶ nsuc (snd ⟨i⟩)`
                       --   by `βsnd`, and the rest is `cong nsuc` on the
                       --   ford this row was handed.
                       (⊢conv (⊢conv (⊢congS (⊢snd (⊢var (there (there here))))
                                             (⊢nsuc (fromI (⊢fst (⊢var (there here)))))
                                             (⊢conv (⊢fst (⊢snd (⊢snd (⊢snd (⊢var (there here))))))
                                                    (elIdN _ _)))
                                     (csymᵀ (elIdN _ _)))
                              (csymᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βsnd _ _))))))
                       ⊢unit)))))))

------------------------------------------------------------------------
-- 6. ⚠ WHAT A GENERIC `Lib/IWk` STILL HAS TO DECIDE.
--
-- Nothing above is generic: each method names its own row.  The step
-- `Lib/ISz` took for `sz` — compute the method from the `ICon` and the
-- tuple from the `IDesc` — needs ONE predicate these four rows have now
-- pinned down:
--
--     does this field's index expression MENTION THE AMBIENT?
--
--       yes  ⇒ take the IH   (`cTm-lam`'s body, `cDCon-kap`'s `DCon`,
--                             `cVar-vs`'s `Var`)
--       no   ⇒ take the ORIGINAL field  — four rows, listed in the
--                             header's census; `cDCon-kap` is the one
--                             built here and `cIDesc-cons` is the only
--                             one pinned at a NON-ZERO literal
--
-- ⚠ IT IS A PREDICATE ON RAW `RTm` INDICES, not on the `ICon`
--   constructor — `iρ` covers both cases, one row apart.  That is the
--   whole reason `Lib/IFold`'s shape does not reach a weakening, stated
--   as the thing to implement.
--
-- ★ AND THE DEPTH FORDS ARE NOT A THIRD CASE.  `cVar-vs` is the riding
--   case plus a `congS` on the ford it already holds, and the two rows
--   that need it are exactly the two whose target depth is constrained —
--   which `IConWf` already distinguishes, via `icw-ford`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 7. `cVar-vz` — the OTHER depth-Forded row, and the last method the
--    knot's weakening was missing.
--
-- ★ STRICTLY EASIER THAN §5.  Same shape minus the recursive field: bump
--   the bound `m`, pass the tag ford through, `congS` the depth ford.
--   No IH at all — `iihTy` is `Unit` here, because `cVar-vz` has no `iρ`.
------------------------------------------------------------------------

tyPayVz : {Γ : Ctx} → (Γ ▹ Σ' Nat Nat) ⊢ty
          Σ' (El ⌜Nat⌝)
            (Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var (vs vz))) sVar))
              (Σ' (El (⌜Id⌝ ⌜Nat⌝ (snd (var (vs (vs vz))))
                                  (nsuc (var (vs vz))))) Unit))
tyPayVz =
  ty-Σ (ty-El ⊢⌜Nat⌝)
    (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (there here)))) (toI ⊢sVar)))
      (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                     (toI (⊢snd (⊢var (there (there here)))))
                     (toI (⊢nsuc (fromI (⊢var (there here)))))))
            ty-Unit))

wkVarVz : {Γ : Cx} → RTm Γ
wkVarVz =
  lam (lam (lam
    (icon tagVar-vz
      (pair (nsuc (fst (var (vs vz))))                  -- m' := suc m
        (pair (fst (snd (var (vs vz))))                 -- the tag ford
          (pair (congS (snd (var (vs (vs vz))))         -- ★ THE TRANSPORT
                       (fst (snd (snd (var (vs vz))))))
                unit))))))

⊢wkVarVz : {Γ : Ctx} →
           Γ ⊢ wkVarVz ∷ imethTy KnotD IPair tagVar-vz cVar-vz wkMot
⊢wkVarVz =
  ⊢lam ⊢IPair
    (⊢lam tyPayVz
      (⊢lam ty-Unit
        (⊢icon KnotWf memVar-vz
               (⊢ixP (⊢fst (⊢var (there (there here))))
                     (⊢nsuc (⊢snd (⊢var (there (there here))))))
          (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                (toI (⊢fst (⊢ixP
                                   (⊢fst (⊢var (there (there (there here)))))
                                   (⊢nsuc (⊢snd (⊢var (there (there (there here)))))))))
                                (toI ⊢sVar)))
                       (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                      (toI (⊢snd (⊢ixP
                                         (⊢fst (⊢var (there (there (there (there here))))))
                                         (⊢nsuc (⊢snd (⊢var (there (there (there (there here))))))))))
                                      (toI (⊢nsuc (fromI (⊢var (there here)))))))
                             ty-Unit))
                 (toI (⊢nsuc (fromI (⊢fst (⊢var (there here))))))
            (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                  (toI (⊢snd (⊢ixP
                                     (⊢fst (⊢var (there (there (there here)))))
                                     (⊢nsuc (⊢snd (⊢var (there (there (there here)))))))))
                                  (toI (⊢nsuc (⊢nsuc (fromI (⊢fst (⊢var (there (there here))))))))))
                         ty-Unit)
                   (unFst (⊢fst (⊢snd (⊢var (there here)))))
              (⊢pair ty-Unit
                     (⊢conv (⊢conv (⊢congS (⊢snd (⊢var (there (there here))))
                                           (⊢nsuc (fromI (⊢fst (⊢var (there here)))))
                                           (⊢conv (⊢fst (⊢snd (⊢snd (⊢var (there here)))))
                                                  (elIdN _ _)))
                                   (csymᵀ (elIdN _ _)))
                            (csymᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βsnd _ _))))))
                     ⊢unit))))))
