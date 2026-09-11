------------------------------------------------------------------------
-- OCP-0009 · KNOT — `selK`, the object-level method selector.
--
--     sel : ℕ → RTm Γ → RTm Γ          -- `Spec/Syntax:974`
--     sel zero    ms = fst ms
--     sel (suc k) ms = sel k (snd ms)
--
-- ★★★ IT OPERATES ON RAW TERMS.  `fst`/`snd` here are RTm CONSTRUCTORS,
--   not meta-level projections, so `sel k ms` BUILDS the term
--   `fst (snd … (snd ms))` and its type is just "a term at depth n" —
--   CONSTANT in `k`.  ⇒ the `natrec` motive is constant, and none of
--   `imethTy`/`ipayTy`/`iihTy` is involved.
--
-- ⚠ I first sized this as needing a motive `k ↦ imethsTyFrom … (drop k E)`
--   and therefore an object-level IDesc `drop`.  That was reading `sel`'s
--   cost off WHERE IT IS USED (method tuples) instead of off its own
--   TYPE.  Same error shape as sizing a fold by its sort's constructor
--   count instead of its method bodies.
--
-- ★ `sel k ms = fst (snd^k ms)`, and `natrec z s k` iterates `s` on the
--   IH (`var vz`, per `Lib/Monus.monusTm`), so the term is one `natrec`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Sel where

open import DirectedHoTT.Spec.Syntax using ( Cx; RTm; var; vz; vs; natrec; pair; Nat; renTm; nzero )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢natrec; ⊢var; here; ty-IMu; wk-single )
open import normalizer.Syntax.Types using ( cong; sym )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import DirectedHoTT.Lib.Wk using ( nrs-w )
open import DirectedHoTT.Examples.Knot.Sorts using ( sTm; ⊢sTm; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-fstKv; ⊢Tm-sndKv )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )

selK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
selK k ms = Tm-fstK (natrec ms (Tm-sndK (var vz)) k)

⊢selK : {Γ : Ctx} {n k ms : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat → Γ ⊢ ms ∷ K (pair sTm n) →
        Γ ⊢ selK k ms ∷ K (pair sTm n)
⊢selK {n = n} {k = k} dn dk dms =
  ⊢Tm-fstKv n dn
    (⊢-cast (cong (λ z → K (pair sTm z)) (wk-single {v = k} n))
      (⊢natrec {M = K (pair sTm (renTm vs n))}
               (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢wk dn)))
               (⊢-cast (sym (cong (λ z → K (pair sTm z)) (wk-single {v = nzero} n))) dms)
               (⊢-cast (sym (cong (λ z → K (pair sTm z)) (nrs-w n)))
                       (⊢Tm-sndKv _ (⊢wk (⊢wk dn)) (⊢var here)))
               dk))

------------------------------------------------------------------------
-- ★★★ AND ITS ADEQUACY, straight away — `selK ⟨k⟩ ⌈ms⌉ ⟶* ⌈ sel k ms ⌉`.
--
-- ⚠ `sel` and the `natrec` ASSOCIATE THE OTHER WAY.  `sel (suc k) ms =
--   sel k (snd ms)` peels from the INSIDE; `natrec` builds `Tm-sndK` on
--   the OUTSIDE of the IH.  Both are `Tm-sndK^k`, so one 2-line
--   induction bridges them — that is `snds-out` below.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( sel )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; step; done; natrec-zero; natrec-suc )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-icon; ⟶*-pairˡ; ⟶*-natrecⁿ )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import DirectedHoTT.Examples.Knot.Map using ( enTm )
open import normalizer.Syntax.Types using ( _≡_; refl; trans )

-- ★ `snd` applied k times, associated as `sel` does.
sndsK : {Γ : Cx} → ℕ → RTm Γ → RTm Γ
sndsK zero    X = X
sndsK (suc k) X = sndsK k (Tm-sndK X)

-- ⚠ the bridge: the `natrec` grows OUTWARD, `sndsK` inward.
snds-out : {Γ : Cx} (k : ℕ) (X : RTm Γ) → Tm-sndK (sndsK k X) ≡ sndsK k (Tm-sndK X)
snds-out zero    X = refl
snds-out (suc k) X = snds-out k (Tm-sndK X)

-- ★ reducing inside `Tm-fstK`'s argument.
inFst : {Γ : Cx} {a a' : RTm Γ} → a ⟶* a' → Tm-fstK a ⟶* Tm-fstK a'
inFst r = ⟶*-icon (⟶*-pairˡ r)

natrec-snds : {Γ : Cx} (k : ℕ) (X : RTm Γ) →
              natrec X (Tm-sndK (var vz)) (num k) ⟶* sndsK k X
natrec-snds zero    X = step (natrec-zero _ _) done
natrec-snds (suc k) X =
  step (natrec-suc _ _ _) done
  » ⟶*-castᵣ (snds-out k X) (⟶*-icon (⟶*-pairˡ (natrec-snds k X)))

selK-agree : {Γ Θ : Cx} (k : ℕ) (ms : RTm Γ) →
             selK (num k) (enTm {Γ} {Θ} ms) ⟶* enTm {Γ} {Θ} (sel k ms)
selK-agree k ms = ⟶*-castᵣ (en-sel k ms) (inFst (natrec-snds k (enTm ms)))
  where
    -- ★ `enTm` commutes with `sel` into `Tm-fstK`/`sndsK` — and it is
    --   DEFINITIONAL at each step, because `sndsK` was associated to
    --   match `sel`'s own recursion.
    en-sel : {Γ Θ : Cx} (k : ℕ) (t : RTm Γ) →
             Tm-fstK (sndsK k (enTm {Γ} {Θ} t)) ≡ enTm {Γ} {Θ} (sel k t)
    en-sel zero    t = refl
    en-sel (suc k) t = en-sel k (DirectedHoTT.Spec.Syntax.snd t)
