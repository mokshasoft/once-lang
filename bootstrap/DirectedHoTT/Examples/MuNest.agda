------------------------------------------------------------------------
-- OCP-0009 · INDUCTIVE TYPES — ★ NESTED DATATYPES, end to end.
--
-- ⚠ WHAT THIS FILE IS FOR: a description whose σ-FIELD IS ANOTHER
--   DATATYPE.  A field must be `El c` for a CODE `c`, so nesting needs a
--   code for a datatype: `⌜IMu⌝ I D i` (§12's code-in-`U` decision).
--
-- ★ THE CHAIN, every link a real derivation:
--
--     ⊢ℕcode      : Γ ⊢ ⌜IMu⌝ ⌜Unit⌝ NatD unit ∷ U   -- ℕ is a CODE
--     WrapOK      : a telescope `tσ ℕcode tι` is well-formed
--     ⊢wrap       : `wrap zero : Wrap`                -- …and INHABITED
--     ⊢unwrap     : the eliminator at the nested type, whose method
--                   READS the nested field (`⊢payHyp`)
--     unwrap-wrap : …and it COMPUTES
--
-- ★ Levitated (D072): ℕ and `Wrap` are ordinary families over `⌜Unit⌝`,
--   written as constructor telescopes (`Lib/Tel`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.MuNest where
open import normalizer.Syntax.Types using ( _,_; sym; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Dₗ; conₗ; methₗ; selF; selF-β; nth-z; MethK; PerK; []ₘ; _∷ₘ_; ⊢methₗ )
open import DirectedHoTT.Lib.Tel

⊢u : {Γ : Ctx} → Γ ⊢ unit ∷ El ⌜Unit⌝
⊢u = ⊢conv ⊢unit (csymᵀ (credᵀ El-⌜Unit⌝))

fromEl : {Γ : Ctx} {I D i t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El (⌜IMu⌝ I D i) → Γ ⊢ t ∷ IMu I D i
fromEl d = ⊢conv d (credᵀ El-⌜IMu⌝)

-- ★★ THE ONE STEP THAT IS NOT BOOKKEEPING: a field's declared type is
--   the code's DECODE, which REDUCES to the family but is not it.
toEl : {Γ : Ctx} {I D i t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ IMu I D i → Γ ⊢ t ∷ El (⌜IMu⌝ I D i)
toEl d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

------------------------------------------------------------------------
-- 1. ℕ — the INNER datatype — and its code.
------------------------------------------------------------------------

NatTs : {Γ : Cx} → Tels (Γ ∙) 2
NatTs = tι ∷ᵗ tρ unit tι ∷ᵗ []ᵗ

NatD : {Γ : Cx} → RTm Γ
NatD = Dₗ ⌜ NatTs ⌝ₛ

NatOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Unit⌝) ⌜Unit⌝ NatTs
NatOK = ok-ι ∷ᵒ ok-ρ ⊢u ok-ι ∷ᵒ []ᵒ

⊢NatD : {Γ : Ctx} → Γ ⊢ NatD ∷ DescF ⌜Unit⌝
⊢NatD = ⊢Dₜ ⊢⌜Unit⌝ NatOK

NatT : {Γ : Cx} → RTy Γ
NatT = IMu ⌜Unit⌝ NatD unit

ty-NatT : {Γ : Ctx} → Γ ⊢ty NatT
ty-NatT = ty-IMu ⊢⌜Unit⌝ ⊢NatD ⊢u

`ℕcode : {Γ : Cx} → RTm Γ
`ℕcode = ⌜IMu⌝ ⌜Unit⌝ NatD unit

⊢ℕcode : {Γ : Ctx} → Γ ⊢ `ℕcode ∷ U
⊢ℕcode = ⊢⌜IMu⌝ ⊢⌜Unit⌝ ⊢NatD ⊢u

`zero : {Γ : Cx} → RTm Γ
`zero = conₗ zero unit

⊢zero : {Γ : Ctx} → Γ ⊢ `zero ∷ NatT
⊢zero = ⊢conₜ ⊢⌜Unit⌝ NatOK nthᵗ-z ⊢u (⊢payι ⊢⌜Unit⌝ ⊢NatD ⊢unit)

------------------------------------------------------------------------
-- 2. ★★★ THE NESTED DESCRIPTION.  One constructor, one field, and that
--    field's type is ANOTHER DATATYPE.
------------------------------------------------------------------------

wrapT : {Γ : Cx} → Tel (Γ ∙)
wrapT = tσ `ℕcode tι

WrapTs : {Γ : Cx} → Tels (Γ ∙) 1
WrapTs = wrapT ∷ᵗ []ᵗ

WrapD : {Γ : Cx} → RTm Γ
WrapD = Dₗ ⌜ WrapTs ⌝ₛ

wrapOK : {Γ : Ctx} → TelOK (Γ ▹ El ⌜Unit⌝) ⌜Unit⌝ wrapT
wrapOK = ok-σ ⊢ℕcode ok-ι

WrapOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Unit⌝) ⌜Unit⌝ WrapTs
WrapOK = wrapOK ∷ᵒ []ᵒ

⊢WrapD : {Γ : Ctx} → Γ ⊢ WrapD ∷ DescF ⌜Unit⌝
⊢WrapD = ⊢Dₜ ⊢⌜Unit⌝ WrapOK

Wrap : {Γ : Cx} → RTy Γ
Wrap = IMu ⌜Unit⌝ WrapD unit

------------------------------------------------------------------------
-- 3. AN INHABITANT.  `wrap zero : Wrap` — the field must be a genuine
--    ℕ, crossed into the code's decode by `toEl`.
------------------------------------------------------------------------

`wrap : {Γ : Cx} → RTm Γ → RTm Γ
`wrap n = conₗ zero (pair n unit)

⊢wrap : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ NatT → Γ ⊢ `wrap n ∷ Wrap
⊢wrap dn = ⊢conₜ ⊢⌜Unit⌝ WrapOK nthᵗ-z ⊢u
             (⊢payσ ⊢⌜Unit⌝ ⊢WrapD (ok-σ ⊢ℕcode ok-ι) (toEl dn) (⊢payι ⊢⌜Unit⌝ ⊢WrapD ⊢unit))

⊢wrap-zero : ◇ ⊢ `wrap `zero ∷ Wrap
⊢wrap-zero = ⊢wrap ⊢zero

------------------------------------------------------------------------
-- 4. ★★★ ELIMINATING A NESTED VALUE — and watching it COMPUTE.
--
-- `unwrap : Wrap → ℕ`.  ⚠ The nested ℕ is a σ-field, a PARAMETER, so it
--   owes NO hypothesis (`IhN` is `Unit`); the method reads it out of the
--   PAYLOAD instead, at the payload's normal form (`⊢payHyp`).
------------------------------------------------------------------------

mwrap : {Γ : Cx} → RTm Γ
mwrap = lam (lam (lam (fst (var (vs vz)))))

WrapMs : {Γ : Cx} → Cons Γ 1
WrapMs = mwrap ∷ []

unwrap : {Γ : Cx} → RTm Γ → RTm Γ
unwrap w = ielim WrapD unit (methₗ WrapMs) w

module _ {Γ : Ctx} where
  ⊢mwrap : Γ ⊢ mwrap ∷ MethK ⌜Unit⌝ WrapD NatT ⌜ wrapT ⌝ᵗ zero
  ⊢mwrap = ⊢methT {T = wrapT} {s = conₗ zero (var (vs vz))} ⊢⌜Unit⌝ ⊢WrapD ty-NatT wrapOK
             (fromEl (⊢fst (⊢payHyp {I = ⌜Unit⌝} {D = WrapD} {M = NatT} {T = wrapT})))

  perWrap : PerK Γ ⌜Unit⌝ WrapD NatT (selF ⌜ WrapTs ⌝ₛ) zero WrapMs
  perWrap = (selF-β {Cs = ⌜ WrapTs ⌝ₛ} nth-z , ⊢mwrap) ∷ₘ []ₘ

  -- ★ the eliminator at a NESTED datatype, fully typed
  ⊢unwrap : {w : RTm ⌊ Γ ⌋} → Γ ⊢ w ∷ Wrap → Γ ⊢ unwrap w ∷ NatT
  ⊢unwrap dw =
    ⊢ielim ⊢⌜Unit⌝ ⊢WrapD ty-NatT (⊢methₗ ⊢⌜Unit⌝ (allD (⊢wk ⊢⌜Unit⌝) WrapOK) ty-NatT perWrap) ⊢u dw

-- ★★ …and it COMPUTES: ι, the method's three β, one projection.
--   ⚠ The payload is substituted UNDER the hypotheses' binder, so the
--   field comes back as `n` weakened-then-instantiated: one `wk-single`.
unwrap-wrap : {Γ : Cx} {n : RTm Γ} → unwrap (`wrap n) ⟶* n
unwrap-wrap {n = n} =
  ⟶*-trans (ιT {T = wrapT} (nth-⌜⌝ {Ts = WrapTs} nthᵗ-z) nth-z)
    (step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) (step (β _ _) (step (βfst _ _)
      (subst (λ t → t ⟶* n) (sym (wk-single n)) done)))))

------------------------------------------------------------------------
-- 5. THE NEXT RUNG — the construction iterates: `Wrap` has a code too.
------------------------------------------------------------------------

`Wrapcode : {Γ : Cx} → RTm Γ
`Wrapcode = ⌜IMu⌝ ⌜Unit⌝ WrapD unit

⊢Wrapcode : {Γ : Ctx} → Γ ⊢ `Wrapcode ∷ U
⊢Wrapcode = ⊢⌜IMu⌝ ⊢⌜Unit⌝ ⊢WrapD ⊢u

Wrap²Ts : {Γ : Cx} → Tels (Γ ∙) 1
Wrap²Ts = tσ `Wrapcode tι ∷ᵗ []ᵗ

Wrap²OK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Unit⌝) ⌜Unit⌝ Wrap²Ts
Wrap²OK = ok-σ ⊢Wrapcode ok-ι ∷ᵒ []ᵒ

⊢wrap² : ◇ ⊢ `wrap (`wrap `zero) ∷ IMu ⌜Unit⌝ (Dₗ ⌜ Wrap²Ts ⌝ₛ) unit
⊢wrap² = ⊢conₜ ⊢⌜Unit⌝ Wrap²OK nthᵗ-z ⊢u
           (⊢payσ ⊢⌜Unit⌝ (⊢Dₜ ⊢⌜Unit⌝ Wrap²OK) (ok-σ ⊢Wrapcode ok-ι) (toEl ⊢wrap-zero)
                  (⊢payι ⊢⌜Unit⌝ (⊢Dₜ ⊢⌜Unit⌝ Wrap²OK) ⊢unit))
