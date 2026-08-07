------------------------------------------------------------------------
-- OCP-0009 — BRANCH (0,0), SHARED DATA:  context, the two recursor
-- arguments as raw terms, and their expected types.
--
-- ⚠ SPLIT FOUR WAYS, like (S,S).  At the ℕ carrier this branch was ONE
--   module at 39s / 2.1 GB.  Adding the carrier slot to Γ₅ multiplied the
--   elaborated term by ~6 (measured: the ⊢lexZZrec1 fragment alone went
--   11.5s / 0.90 GB → 43s / 4.14 GB), because every stored implicit type
--   that used to be the single node `Nat` is now `El (var (vs⁸ vz))`, and
--   `Π Nat Nat` is now `Π (El (var (vs⁹ vz))) Nat`.  Three derivations in
--   one module no longer fit under the 5.5 GB cap.
--
-- ★ Terms and types stay cheap; it is the DERIVATIONS that are expensive,
--   so they get a module each and this file is shared.
--
-- ctx after the three ⊢lams: vz=lt, vs=le, vs²=x, vs³=n₂, vs⁴=stp,
--                            vs⁵=μ₂, vs⁶=μ₁, vs⁷=cP, vs⁸=A
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexZZData where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; _∋_∷_; here; there )
open import poc.OCP0009.NbEPDirDBExamplesLex
  using ( Γ₅; REC1T; REC2T; REC2Tbody; REC2Tbody2 )

-- the context after the three `⊢lam`s (x, le : μ₁ x ≤ 0, lt : μ₂ x ≤ n₂)
ΓZZ : Ctx
ΓZZ =
  (((Γ₅ ▹ Nat) ▹ subTy (single nzero) (El (var (vs (vs (vs (vs (vs (vs vz)))))))))
     ▹ subTy (extS (single nzero))
         (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var vz)) nzero))
     ▹ subTy (extS (extS (single nzero)))
         (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz)))
                  (var (vs (vs vz))))

-- ★ THE CARRIER at ΓZZ, as a `Def`: the `x` binder of every recursor
--   argument.  At the ℕ carrier this was the nullary constructor `Nat`.
AZZ : RTy ⌊ ΓZZ ⌋
AZZ = El (var (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))

------------------------------------------------------------------------
-- ★ HOISTED LOOKUPS.  `there` stores BOTH the looked-up type A and the
--   binder type B at EVERY level, so an inline `there⁹ here` embeds a copy
--   of `LStepT` — and hence of `REC1T`/`REC2T`, both of which grew with the
--   carrier.  Naming the lookup pays that once per (context, variable)
--   instead of once per occurrence.  MEASURED: 4.14 GB → 3.60 GB on
--   `⊢lexZZrec1`.
------------------------------------------------------------------------

∋A : ΓZZ ∋ vs (vs (vs (vs (vs (vs (vs (vs vz))))))) ∷ U
∋A = there (there (there (there (there (there (there (there here)))))))

-- ctx: vz=y, vs=lt, vs²=le, vs³=x, vs⁴=n₂, vs⁵=stp, vs⁶=μ₂, vs⁷=μ₁,
--      vs⁸=cP, vs⁹=A   — shared by rec₁ and rec₂
∋μ₁¹ : (ΓZZ ▹ AZZ) ∋ vs (vs (vs (vs (vs (vs (vs vz)))))) ∷
       Π (El (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) Nat
∋μ₁¹ = there (there (there (there (there (there (there here))))))

lexZZrec1 : RTm ⌊ ΓZZ ⌋
lexZZrec1 =
  lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz)))))))

REC1TZZ : RTy ⌊ ΓZZ ⌋
REC1TZZ =
  subTy (single (var (vs (vs vz))))
    (renTy (extR vs) (renTy (extR vs) (renTy (extR vs)
      (renTy (extR vs) (renTy (extR vs) REC1T)))))

-- ★★ rec₂ IS PEELED, ONE `⊢lam` PER MODULE.  MEASURED at the generic
--   carrier: each `⊢lam` layer costs ~2.5–3 GB, so all three plus
--   `⊢strong-base'` in one module OOMs against the 5.5 GB cap, and even
--   two do (`+RTS -c` does not save either).  At the ℕ carrier all THREE
--   of this branch's derivations fit in ONE 2.1 GB module — that is the
--   whole price of the generic carrier.
--
-- The recipe, per peel: name the sub-term (`…in`, `…in2`), get its
-- expected type from Agda with the probe technique (a deliberately wrong
-- `⊢nzero` in the derivation slot prints it in full), and name that too.
-- Every peeled type has the shape
--     subTy (extSⁱ σ) (subTy (extSʲ σ') (renTy (extRᵏ vs)⁵ REC2Tbodyⁿ)).
lexZZrec2in2 : RTm ((⌊ ΓZZ ⌋ ∙) ∙)
lexZZrec2in2 =
  lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))

lexZZrec2in : RTm (⌊ ΓZZ ⌋ ∙)
lexZZrec2in = lam lexZZrec2in2

lexZZrec2 : RTm ⌊ ΓZZ ⌋
lexZZrec2 = lam lexZZrec2in

-- `le : μ₁ y ≤ μ₁ x`, the second binder of rec₂ — the REDUCED form of what
-- `⊢lam` puts in the context (Agda's own is the unreduced `subTy` chain).
HOMleZZ : RTy ⌊ ΓZZ ▹ AZZ ⌋
HOMleZZ =
  Hom Nat (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var vz))
          (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs (vs vz)))))

-- the expected types of `lexZZrec2in` / `lexZZrec2in2`, READ OFF Agda
REC2TZZin : RTy ⌊ ΓZZ ▹ AZZ ⌋
REC2TZZin =
  subTy (extS (single lexZZrec1))
    (subTy (extS (extS (single (var (vs (vs vz))))))
      (renTy (extR (extR (extR vs))) (renTy (extR (extR (extR vs)))
        (renTy (extR (extR (extR vs))) (renTy (extR (extR (extR vs)))
          (renTy (extR (extR (extR vs))) REC2Tbody))))))

REC2TZZin2 : RTy ⌊ (ΓZZ ▹ AZZ) ▹ HOMleZZ ⌋
REC2TZZin2 =
  subTy (extS (extS (single lexZZrec1)))
    (subTy (extS (extS (extS (single (var (vs (vs vz)))))))
      (renTy (extR (extR (extR (extR vs)))) (renTy (extR (extR (extR (extR vs))))
        (renTy (extR (extR (extR (extR vs)))) (renTy (extR (extR (extR (extR vs))))
          (renTy (extR (extR (extR (extR vs)))) REC2Tbody2))))))

-- ★ note `single lexZZrec1`: the argument type of `rec₂` depends on the
--   rec₁ TERM, so the split has to name the term as well as the derivation.
REC2TZZ : RTy ⌊ ΓZZ ⌋
REC2TZZ =
  subTy (single lexZZrec1)
    (subTy (extS (single (var (vs (vs vz)))))
      (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs))
        (renTy (extR (extR vs)) (renTy (extR (extR vs)) REC2T))))))
