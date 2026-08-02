------------------------------------------------------------------------
-- OCP-0009 · W2 eliminator — DONE-WHEN DEMOS for `tr`, both motives in
--                            the BASE judgment.
--
-- HISTORY.  This module began (stage 1, 2026-08-01) as the STAGED
-- judgment `_⊢ᵗ_∷_`: base typing plus a general-`PosC`-motive `⊢tr`,
-- with its own subject reduction (`srᵗ`) — the staging isolated the
-- eliminator while `SpikeTrLR` answered how `fund` could discharge it.
-- Stage 2 merged the COMPOSITION motive into the base judgment
-- (`⊢tr`, motive pinned `⌜Hom⌝ c a (var vz)`).  Stage 3 re-keyed the J
-- rules on `⌜Hom⌝`-headed MOTIVES — at a `var` motive a path can never
-- be a typed `hrefl`, so the un-keyed rules were never typed-exercised,
-- and the keying makes those configurations permanently stuck, which
-- dissolved SpikeTrLR's taut obstruction — and merged the TAUTOLOGICAL
-- motive too (`⊢trU`, ambient pinned `U`).  Both motives now have `sr`
-- (`NbEPDirDBSubj`) and `fund` (`NbEPDirDBFund`); the staged judgment
-- is RETIRED, and this module keeps the done-when demos:
--
--   * `⊢trans-base`   — `trans` INTERNALLY: a path transported along a
--                       path at the `⌜Hom⌝` composition motive;
--   * `⊢trans-base-red` — the J-equation computes it back to the
--                       original path, typing preserved (`sr`);
--   * ★ `trans-wnorm = refl` — the fundamental theorem NORMALIZES it:
--                       `wnorm` computes the J-step;
--   * `⊢univ-base`    — DIRECTED UNIVALENCE: transport at the
--                       tautological motive along a universe path;
--   * ★ `univ-wnorm = refl` — `wnorm` computes taut-then-β down to the
--                       payload;
--   * `no-sym-tr`     — the internal `no-sym` regression, syntactic
--                       half: `sym`'s motive code fails `PosC`, so the
--                       composition rule cannot even be stated at it
--                       (`SpikeNoSym` holds the semantic half).
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBTr where

open import normalizer.Syntax.Types
  using ( _≡_; refl )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; El; Hom
        ; RTm; var; lam; app; ⌜base⌝; ⌜Hom⌝; hrefl; tr
        ; subTm )
open import poc.OCP0009.NbEPDirDBVar
  using ( PosC; sym-code; sym-code-not-posc )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶_; β
        ; tr-J-base; tr-taut
        ; El-⌜base⌝; El-⌜Hom⌝; Hom-U
        ; credᵀ; csymᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢conv
        ; ⊢⌜base⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢trU; ty-El; ty-base
        ; ⊢ctx_; c-◇; c-▹ )
open import poc.OCP0009.NbEPDirDBSubj using ( sr )
open import poc.OCP0009.NbEPDirDBLR using ( WN )
open import poc.OCP0009.NbEPDirDBFund using ( wnorm )

private
  Γ₁ : Ctx
  Γ₁ = ◇ ▹ El ⌜base⌝

  x₁ : RTm (ε ∙)
  x₁ = var vz

  ⊢x₁ : Γ₁ ⊢ x₁ ∷ El ⌜base⌝
  ⊢x₁ = ⊢var here

  ⊢idpath : Γ₁ ⊢ hrefl ⌜base⌝ x₁ ∷ Hom (El ⌜base⌝) x₁ x₁
  ⊢idpath = ⊢hrefl ⊢⌜base⌝ ⊢x₁

  -- the composition motive: paths-from-`x₁`, `⌜Hom⌝ ⌜base⌝ (x₁ ↑) (var vz)`
  compM : RTm ((ε ∙) ∙)
  compM = ⌜Hom⌝ ⌜base⌝ (var (vs vz)) (var vz)

------------------------------------------------------------------------
-- ★ `trans`, INTERNALLY — the composition motive.
------------------------------------------------------------------------

trans-tr : RTm (ε ∙)
trans-tr = tr compM (hrefl ⌜base⌝ x₁) (hrefl ⌜base⌝ x₁)

⊢trans-base : Γ₁ ⊢ trans-tr ∷ El (subTm (single x₁) compM)
⊢trans-base =
  ⊢tr ⊢⌜base⌝ (⊢var (there here)) (⊢var here) refl refl
      ⊢x₁ ⊢x₁ ⊢idpath
      (⊢conv (⊢hrefl ⊢⌜base⌝ ⊢x₁)
             (csymᵀ (credᵀ (El-⌜Hom⌝ ⌜base⌝ x₁ x₁))))

-- the J-equation computes the composite along an identity path back to
-- the original path — typing preserved.
trans-tr-J : trans-tr ⟶ hrefl ⌜base⌝ x₁
trans-tr-J = tr-J-base ⌜base⌝ (var (vs vz)) (var vz) x₁ (hrefl ⌜base⌝ x₁)

⊢trans-base-red : Γ₁ ⊢ hrefl ⌜base⌝ x₁ ∷ El (subTm (single x₁) compM)
⊢trans-base-red = sr ⊢trans-base trans-tr-J

-- ★ the fundamental theorem normalizes it: the J-equation, computed.
trans-wnorm : WN.nfm (wnorm (c-▹ c-◇ (ty-El ⊢⌜base⌝)) ⊢trans-base)
            ≡ hrefl ⌜base⌝ x₁
trans-wnorm = refl

------------------------------------------------------------------------
-- ★ DIRECTED UNIVALENCE COMPUTES — the tautological motive (`⊢trU`):
-- transport along a universe path is application; taut then β, two
-- steps to the payload.
------------------------------------------------------------------------

univ-tr : RTm (ε ∙)
univ-tr = tr (var vz) (lam (var vz)) (var vz)

⊢univ-base : (◇ ▹ base) ⊢ univ-tr ∷ El ⌜base⌝
⊢univ-base =
  ⊢trU ⊢⌜base⌝ ⊢⌜base⌝
       (⊢conv (⊢lam (ty-El ⊢⌜base⌝) (⊢var here))
              (csymᵀ (credᵀ (Hom-U ⌜base⌝ ⌜base⌝))))
       (⊢conv (⊢var here) (csymᵀ (credᵀ El-⌜base⌝)))

univ-tr-taut : univ-tr ⟶ app (lam (var vz)) (var (vz {ε}))
univ-tr-taut = tr-taut (var vz) (var vz)

univ-tr-β : app (lam (var vz)) (var (vz {ε})) ⟶ var vz
univ-tr-β = β (var vz) (var vz)

⊢univ-red : (◇ ▹ base) ⊢ var vz ∷ El ⌜base⌝
⊢univ-red = sr (sr ⊢univ-base univ-tr-taut) univ-tr-β

-- ★ the fundamental theorem normalizes it: taut-then-β, computed.
univ-wnorm : WN.nfm (wnorm (c-▹ c-◇ ty-base) ⊢univ-base) ≡ var vz
univ-wnorm = refl

------------------------------------------------------------------------
-- ★ the internal `no-sym` regression, syntactic half.
------------------------------------------------------------------------

no-sym-tr : PosC vz sym-code → (∀ {P : Set} → P)
no-sym-tr = sym-code-not-posc
