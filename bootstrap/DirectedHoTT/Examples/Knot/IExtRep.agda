------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `iextK` AGREES WITH `iext`.
--
--     iext-Represents : Represents (iext σ t)
--                                  (iextK ⌈|Δ|⌉ ⌈|Γ|⌉ s ⌈t⌉)
--
-- Discharges the ledger's `iextK` entry by the route it named — the
-- factorisation `iext σ t ≡ single t ∘ extS σ`, which `iextK`'s body IS,
-- spelled out — composed out of three DISCHARGED agreements
-- (`extS-Represents`, `sub-agree`, `single-Represents`).
--
-- ★ AND FIVE NATURALITY LEMMAS THAT WERE THE REAL CONTENT.  See
--   `IHS-ATTEMPTS.md` §2/§4 for the two attempts that found them.
--
-- ⚠ ATTEMPT 2's FINDING (`IHS-ATTEMPTS.md` §2): `subTm` does NOT
--   distribute into `extNK`'s or `singleK`'s arguments — both build a
--   `lam`, so the β's substitution goes UNDER the binder and the
--   arguments are weakened twice.  ⇒ pushing the β through owes
--   SUBSTITUTION-NATURALITY for each.
--
-- ★ AND THE CASCADE IS OWED DOWNSTREAM ANYWAY: `Knot/IihsRho` calls
--   `subTmAtK` inside a seven-lam body, so `subMethsK-sub` is on the
--   path to `iihsK` whatever route `iextK` takes.  That is what decided
--   it against changing `iextK`'s definition.
--
-- ★ EVERY PIECE HAS A TEMPLATE in `Knot/SubNat` / `Knot/SubSpec`:
--     singleMethsK-sub ← extMethsK-sub   (`methsFrom-sub`, closed leaves)
--     singleSK-sub     ← extSK-sub
--     singleK-sub      ← extNK-sub
--     give-sub         ← renGive-sub     (`pickTm` case split, 3 tests)
--     subMethsK-sub    ← renMethsK-sub   (`isubMeths-sub`)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IExtRep where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; Sub; iext; Var; vz; vs; var; app; lam; pair; subTm
        ; renTm; extS; nsuc; ielim; unit )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; β; single; wk-single )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castₗ; ⟶*-castᵣ )
open import DirectedHoTT.Lib.Wk using ( w; sub-w )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Lib.IMeths using ( cdTake; methsFrom; methsFrom-sub )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ; ⟶*-ielimᵗ )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans; sym )
open import DirectedHoTT.Examples.Knot.Sorts using ( len; sVar; sTm )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enVar )
open import DirectedHoTT.Examples.Knot.IExt using ( iextK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTmAtK )
open import DirectedHoTT.Examples.Knot.Single
  using ( singleK; singleSK; singleMethsK; singleId; singleTail )
open import DirectedHoTT.Examples.Knot.SubMot
  using ( extNK; subMethsK; subDescK; giveK; subVarM; subVzM; subVsM )
open import DirectedHoTT.Examples.Knot.SubNat using ( extNK-sub; app₂-cong₃ )
open import DirectedHoTT.Examples.Knot.SubAgree using ( Represents; single-Represents )
open import DirectedHoTT.Examples.Knot.SubExt using ( extS-Represents )
open import DirectedHoTT.Examples.Knot.SubAgreeTie using ( sub-agree )
import DirectedHoTT.Lib.ISub as IS
open import DirectedHoTT.Examples.Knot.SubMot using ( sortMap; decStableK; fordMapK )
open import DirectedHoTT.Examples.Knot.SubNat using ( fordMapK-sub )
open IS.Sub extNK sortMap decStableK fordMapK
open import DirectedHoTT.Lib.IFold using ( eqℕ )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )

------------------------------------------------------------------------
-- ★ STEP 1 — `singleMethsK` is substitution-stable.
--   `extMethsK-sub`'s three lines; both leaves are CLOSED lam-terms.
------------------------------------------------------------------------

singleMethsK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) →
                   subTm τ (singleMethsK {Γ}) ≡ singleMethsK {Δ}
singleMethsK-sub τ = methsFrom-sub (cdTake 51 KnotD) τ singleId singleTail

singleSK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (i k : RTm Γ) →
               subTm τ (singleSK i k) ≡ singleSK (subTm τ i) (subTm τ k)
singleSK-sub τ i k =
  cong (λ z → ielim KnotD (subTm τ i) z (subTm τ k)) (singleMethsK-sub τ)

-- ★ `extNK-sub`'s proof, one program over.
singleK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (n u : RTm Γ) →
              subTm τ (singleK n u) ≡ singleK (subTm τ n) (subTm τ u)
singleK-sub τ n u = cong lam (cong₂ app h1 (sub-w {σ = τ} u))
  where
    h1 : subTm (extS τ) (singleSK (pair sVar (nsuc (w n))) (var vz))
         ≡ singleSK (pair sVar (nsuc (w (subTm τ n)))) (var vz)
    h1 = trans (singleSK-sub (extS τ) (pair sVar (nsuc (w n))) (var vz))
               (cong (λ z → singleSK (pair sVar (nsuc z)) (var vz)) (sub-w {σ = τ} n))


------------------------------------------------------------------------
-- ★ STEP 2 — `subMethsK` is substitution-stable.
--   `renMethsK-sub`'s two lines: the `give` case split, then
--   `Lib/ISub.isubMeths-sub`.
--
-- ⚠ `pickTm` MUST BE SPLIT — a meta-level `if` on a decidable tag test
--   is stuck with `k` abstract, and `refl` would prove nothing.  Each of
--   the four leaves is a CLOSED lam-term.  `Knot/SubSpec.renGive-sub`
--   says the same, verbatim.
------------------------------------------------------------------------

give-sub : GiveSub (λ {Γ} k → giveK {Γ} k)
give-sub τ k with eqℕ k 11
... | true  = refl
... | false with eqℕ k 51
...   | true  = refl
...   | false with eqℕ k 52
...     | true  = refl
...     | false = refl

subMethsK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) →
                subTm τ (subMethsK {Γ}) ≡ subMethsK {Δ}
subMethsK-sub τ = isubMeths-sub extNK-sub fordMapK-sub give-sub τ subDescK 0

-- ★ …AND THEREFORE `subTmAtK` IS NATURAL.  `subTmAtK dd m σ t =
--   app (app (ielim KnotD (pair sTm dd) subMethsK t) m) σ`, so
--   everything but the tuple distributes definitionally.
subTmAtK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (dd m σ t : RTm Γ) →
               subTm τ (subTmAtK dd m σ t)
               ≡ subTmAtK (subTm τ dd) (subTm τ m) (subTm τ σ) (subTm τ t)
subTmAtK-sub τ dd m σ t =
  app₂-cong₃ (cong (λ z → ielim KnotD (pair sTm (subTm τ dd)) z (subTm τ t))
                   (subMethsK-sub τ))
             refl refl

------------------------------------------------------------------------
-- ★★★ STEP 3 — `iextK`'s β LAW, ONCE.
--
-- ★ `Knot/SubSpec.extNK-vz` is the precedent for putting the β
--   bookkeeping in ONE lemma instead of at every call site — which is
--   why `extS-Represents` is three lines.  This is that, generic in the
--   variable, so it serves both clauses.
------------------------------------------------------------------------

cong₃' : {Γ : Cx} {a a' b b' c c' : RTm Γ}
         (f : RTm Γ → RTm Γ → RTm Γ → RTm Γ) →
         a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃' f refl refl refl = refl

iextK-app : {Γ : Cx} (dd n σ t a : RTm Γ) →
            app (iextK dd n σ t) a
            ⟶* subTmAtK (nsuc n) n (singleK n t) (app (extNK dd n σ) a)
iextK-app dd n σ t a = step (β _ _) (⟶*-castₗ eq done)
  where
    eS : subTm (single a) (singleK (w n) (w t)) ≡ singleK n t
    eS = trans (singleK-sub (single a) (w n) (w t))
               (cong₂ singleK (wk-single {v = a} n) (wk-single {v = a} t))
    eE : subTm (single a) (extNK (w dd) (w n) (w σ)) ≡ extNK dd n σ
    eE = trans (extNK-sub (single a) (w dd) (w n) (w σ))
               (cong₃' extNK (wk-single {v = a} dd) (wk-single {v = a} n)
                             (wk-single {v = a} σ))
    eq : subTm (single a)
           (subTmAtK (nsuc (w n)) (w n) (singleK (w n) (w t))
                     (app (extNK (w dd) (w n) (w σ)) (var vz)))
         ≡ subTmAtK (nsuc n) n (singleK n t) (app (extNK dd n σ) a)
    eq = trans (subTmAtK-sub (single a) (nsuc (w n)) (w n) (singleK (w n) (w t))
                             (app (extNK (w dd) (w n) (w σ)) (var vz)))
               (cong₃' (λ nn s1 s2 → subTmAtK (nsuc nn) nn s1 (app s2 a))
                       (wk-single {v = a} n) eS eE)

-- ★ `Knot/IExtAgree.⟶*-subTyAtK` at the TERM sort.
⟶*-subTmAtK : {Γ : Cx} {dd m σ t t' : RTm Γ} →
              t ⟶* t' → subTmAtK dd m σ t ⟶* subTmAtK dd m σ t'
⟶*-subTmAtK h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ h))

------------------------------------------------------------------------
-- ★★★ STEP 4 — THE AGREEMENT, and now it IS `single-Represents`'s three
--   lines: the ledger's route (`iext σ t ≡ single t ∘ extS σ`) composed
--   out of three DISCHARGED agreements.
--
--     iext σ t vz     = t       iext σ t (vs x) = σ x
------------------------------------------------------------------------

iext-Represents : {S T Θ : Cx} {σ : Sub S T} {s : RTm Θ} (t : RTm T) →
                  Represents σ s →
                  Represents {Γ = S ∙} {Δ = T}
                             (iext σ t)
                             (iextK (num (len S)) (num (len T)) s (enTm t))
iext-Represents {S} {T} t h vz =
  iextK-app (num (len S)) (num (len T)) _ (enTm t) (enVar {S ∙} vz)
  » ⟶*-subTmAtK (extS-Represents (num (len S)) h vz)
  » sub-agree (single-Represents (num (len T))) (var vz)
iext-Represents {S} {T} {σ = σ} t h (vs x) =
  -- ⚠ the ONE cast: `extS σ (vs x)` is `renTm vs (σ x)`, and `single t`
  --   takes that back — an EQUALITY (`wk-single`), not a reduction.
  ⟶*-castᵣ (cong enTm (wk-single {v = t} (σ x)))
    (iextK-app (num (len S)) (num (len T)) _ (enTm t) (enVar {S ∙} (vs x))
     » ⟶*-subTmAtK (extS-Represents (num (len S)) h (vs x))
     » sub-agree (single-Represents (num (len T))) (renTm vs (σ x)))
