------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `Lib/IFold.scopeAt` AT A SECOND DESCRIPTION.
--
-- `Examples/ScopedSz` and `Examples/ScopedDepth` are the check that
-- `Lib/ISz` and `Lib/IDepth` are generic in the description rather than
-- secretly about the knot.  This is the same check for the THIRD `pick`,
-- and it also exhibits the hazard that `pick` exists to avoid — in four
-- rows rather than fifty-three.
--
-- ★★★ THE HAZARD ROW IS ONE LINE:
--
--        box : Tm 0 → Tm n      -- a CLOSED subterm, embedded at any n
--
--   the shape of `Mu : Desc → RTy Γ` and `dκ : RTy ε → DCon → DCon`.  A
--   subterm at a FIXED depth restarts the scope, so a variable bound
--   inside it is not a variable of the ambient context — but a fold that
--   compares raw LEVELS cannot tell, because the encoding of a
--   description's own `vz` is the same node an ambient `vz` produces.
--   That is exactly how `occK` came to be unfaithful (`OCC-ATTEMPTS.md`
--   §35), and `Knot/PickScope` is this file's counterpart for `KnotD`.
--
-- ★ AND THE POINT IS THAT NO RE-INDEXING WAS NEEDED.  `Examples/Scoped`'s
--   index is a BARE DEPTH — no sort component at all — and the
--   distinction is still there: an ambient child's index MENTIONS the
--   index variable, a scope-restarting child's is a closed NUMERAL.  If
--   it survives at a bare depth it survives a fortiori at `Σ' Nat Nat`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.ScopeHazard where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; var; vz; vs; nzero; nsuc; ⌜IMu⌝; IMu
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_ )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⊢nzero; ⊢nsuc; ⊢var; here; there; ⊢⌜IMu⌝
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ; icw-imu
        ; IDescWf; idwf-cons; idwf-nil )
open import DirectedHoTT.Spec.Variance using ( 𝔹; true; false )
open import DirectedHoTT.Lib.IFold using ( Maybeℕ; noℕ; someℕ; numVal; scopeAt )
open import DirectedHoTT.Examples.Scoped
  using ( INat; toI; fromI; varC; lamC; appC; FinD; FinWf )

------------------------------------------------------------------------
-- 1. THE HAZARD ROW — a recursive field at a CLOSED index.
------------------------------------------------------------------------
boxC : ICon (ε ∙)
boxC = iρ nzero iι

TmHD : IDesc
TmHD = varC ◂ (lamC ◂ (appC ◂ (boxC ◂ inil)))

TmH : {Γ : Cx} → RTm Γ → RTy Γ
TmH n = IMu TmHD INat n

------------------------------------------------------------------------
-- 2. IT IS WELL-FORMED — a closed index is perfectly legal, which is
--    why no TYPE catches this and an adequacy proof had to.
--
-- ⚠ COST DATUM: `IConWf D I Δ C` is indexed by the WHOLE description, so
--   ADDING ONE ROW invalidates every existing row's well-formedness
--   proof.  `Examples/Scoped`'s `varWf`/`lamWf`/`appWf` cannot be reused
--   and are re-proved verbatim here.  A description is not extensible in
--   place — a real data point for "descriptions as VALUES".
------------------------------------------------------------------------
varWfH : IConWf TmHD INat (◇ ▹ INat) varC
varWfH = iwf-κ (⌜IMu⌝ FinD INat (var vz))
               (icw-imu (var vz) FinWf)
               (⊢⌜IMu⌝ FinWf (⊢var here))
               iwf-ι

lamWfH : IConWf TmHD INat (◇ ▹ INat) lamC
lamWfH = iwf-ρ (nsuc (var vz)) (toI (⊢nsuc (fromI (⊢var here)))) iwf-ι

appWfH : IConWf TmHD INat (◇ ▹ INat) appC
appWfH = iwf-ρ (var vz) (⊢var here)
          (iwf-ρ (var (vs vz)) (⊢var (there here)) iwf-ι)

boxWfH : IConWf TmHD INat (◇ ▹ INat) boxC
boxWfH = iwf-ρ nzero (toI ⊢nzero) iwf-ι

TmHWf : IDescWf INat TmHD
TmHWf = idwf-cons varWfH (idwf-cons lamWfH (idwf-cons appWfH
        (idwf-cons boxWfH idwf-nil)))

------------------------------------------------------------------------
-- 3. ★★★ AND `scopeAt` SEPARATES THEM, at a BARE-DEPTH index.
--
--    `app`  children   ⟨n⟩          mentions the index variable  → keep
--    `lam`  child      nsuc ⟨n⟩     mentions it, shifted         → keep
--    `box`  child      nzero        a CLOSED NUMERAL             → SKIP
------------------------------------------------------------------------
chk-app₁ : numVal {ε ∙} (var vz)          ≡ noℕ
chk-app₁ = refl

chk-app₂ : numVal {(ε ∙) ∙} (var (vs vz)) ≡ noℕ
chk-app₂ = refl

chk-lam  : numVal {ε ∙} (nsuc (var vz))   ≡ noℕ
chk-lam  = refl

chk-box  : numVal {ε ∙} nzero             ≡ someℕ zero
chk-box  = refl

-- …and through `pick` itself.
pick-app : scopeAt {𝔹} {ε ∙} true (var vz)        ≡ true
pick-app = refl

pick-lam : scopeAt {𝔹} {ε ∙} true (nsuc (var vz)) ≡ true
pick-lam = refl

pick-box : scopeAt {𝔹} {ε ∙} true nzero           ≡ false
pick-box = refl
