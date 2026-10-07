-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — the SIGNATURE-FREE part of the judgements: the
-- substitutions the rules plug in, typed contexts, variable lookup.
--
-- Split out of `Spec/Typing` by PLAN-REF (D082): reduction depends on the
-- signature (δ reads a body from it), typing on the signature AND the names
-- a derivation may use.  What depends on neither lives here, so it is ONE
-- Agda type/function for every signature — a transport across a signature
-- extension never has to convert it.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Base where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam; app
        ; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap
        ; Id; ⌜Id⌝; idrefl; jsub
        ; Unit; Nat; unit; nzero; nsuc; natrec; extS; ⌜Nat⌝; ⌜Unit⌝
        ; Ren; extR; Sub; subTy; subTm; renTy; renTm
        ; subTy-subTy; subTy-cong; renTy-subTy; subTm-renTm; subTm-id
        ; εwkTy; εwk-ren; εwk-sub; εwkTm
        ; IMu; Desc; DIh; Fin; ⌜IMu⌝; ⌜Fin⌝; con; ielim; dι; dσ; dρ; dpay; dih
        ; fzero; fsuc; fcase; fcase0; psplit; ref; Defs; _<ˢ_ )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; occTm; pw?; stkC?; stkA?; flat?; pwBody; pwShift
        ; NoNatC; nnc-base; nnc-Unit; nnc-Π; nnc-Σ; nnc-Hom; nnc-Id )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Single substitution (what β and dependent `app` plug in).
------------------------------------------------------------------------

single : RTm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x


-- ★ A `single` CANCELS A WEAKENING.  Two lines, used ~60 times across the
--   tree.  Lives HERE because `single` does; its other two ingredients
--   (`subTm-renTm`, `subTm-id`) are in `…Pi`.
--
-- ⚠ IT LIVED IN `…LR` — the 6269-line logical relation — until 2026-08-19,
--   because that is where it was first needed.  ⚠ THE PROBLEM IS NOT that a
--   library depended on metatheory: SN and canonicity ARE properties of the
--   kernel and a library may legitimately depend on them.  The problem is
--   that `wk-single` is not metatheory at all — it is SYNTAX, and reaching
--   into the normalisation proof to fetch it makes every user pay for a
--   6000-line development to get two lines.  `…LR` re-exports it, so its
--   ~50 importers are unaffected.
wk-single : {Γ : Cx} {v : RTm Γ} (t : RTm Γ) →
            subTm (single v) (renTm vs t) ≡ t
wk-single t = trans (subTm-renTm t) (subTm-id t)
-- ★ WF-axis stage A: the successor-instance substitution — reads the
-- motive M (over Γ, number) at `nsuc` of the number, in the recursor's
-- step context (Γ, number, IH).
nrs : Sub (Γ ∙) ((Γ ∙) ∙)
nrs vz     = nsuc (var (vs vz))
nrs (vs x) = var (vs (vs x))

-- ★ the two-binder instantiation `psplit`'s rule plugs in: the inner
--   binder gets `y`, the outer `x`.
single2 : RTm Γ → RTm Γ → Sub ((Γ ∙) ∙) Γ
single2 x y vz          = y
single2 x y (vs vz)     = x
single2 x y (vs (vs x')) = var x'

-- ★ `psplit`'s motive re-based at the two halves, and `fcase`'s at a
--   successor tag.
pairS : Sub (Γ ∙) ((Γ ∙) ∙)
pairS vz     = pair (var (vs vz)) (var vz)
pairS (vs x) = var (vs (vs x))

fsucS : Sub (Γ ∙) (Γ ∙)
fsucS vz     = fsuc (var vz)
fsucS (vs x) = var (vs x)

------------------------------------------------------------------------
-- ★★ THE ELIMINATOR'S TYPES (levitated, one-telescope form).
--
-- ⚠ THE MOTIVE IS TWO-SLOT: `M : RTy ((Γ ∙) ∙)`, a family over the INDEX
--   (outer) and the SCRUTINEE (inner).
------------------------------------------------------------------------

-- instantiate the two-slot motive at index `j` and scrutinee `t`
iinst : RTm Γ → RTm Γ → RTy ((Γ ∙) ∙) → RTy Γ
iinst j t M = subTy (single t) (subTy (extS (single j)) M)

-- the motive, after the method's three binders (i, p, h), at index `i`
--   and scrutinee `con p`
methS : Sub ((Γ ∙) ∙) (((Γ ∙) ∙) ∙)
methS vz          = con (var (vs vz))
methS (vs vz)     = var (vs (vs vz))
methS (vs (vs x)) = var (vs (vs (vs x)))

-- the base context weakened past two binders, the motive's own two kept
wk2M : RTy ((Γ ∙) ∙) → RTy ((((Γ ∙) ∙) ∙) ∙)
wk2M M = renTy (extR (extR (λ x → vs (vs x)))) M

-- ★★ D074: a description is FIBRED — a family of telescopes over the
--   index, `D : Π (El I) (Desc I)` (Chapman–Dagand–McBride–Morris).
DescF : RTm Γ → RTy Γ
DescF I = Π (El I) (Desc (renTm vs I))

-- ★★ THE ONE METHOD (SPIKE-LEVITATION S3/S4): at every index `i`, for the
--   payload `p` of the telescope AT `i` (`D i`) and its hypotheses `h`,
--   the motive at `con p`.  The payload is passed WHOLE — no η (gate 5c).
MethTy : RTm Γ → RTm Γ → RTy ((Γ ∙) ∙) → RTy Γ
MethTy I D M =
  Π (El I)
    (Π (El (dpay (renTm vs I) (renTm vs D) (app (renTm vs D) (var vz))))
       (Π (DIh (renTm vs (renTm vs D)) (wk2M M) (app (renTm vs (renTm vs D)) (var (vs vz))) (var vz))
          (subTy methS M)))

-- The top-two-variable SWAP renaming — what `tr-pw` uses to move the
-- `⌜Π⌝`-codomain code under the new lambda: the Π-binder becomes the new
-- outer variable, the (necessarily absent, per `PosC`) old transported
-- variable maps onto the new one.  A RENAMING, not a substitution — the
-- commutation lemmas downstream stay in the renaming fragment.
swp : Ren ((Γ ∙) ∙) ((Γ ∙) ∙)
swp vz          = vs vz
swp (vs vz)     = vz
swp (vs (vs x)) = vs (vs x)


infixr 4 _,,_
record _×_ (P Q : Set) : Set where
  constructor _,,_
  field π₁ : P
        π₂ : Q

------------------------------------------------------------------------
-- Typed contexts (telescopes of types) and their underlying de Bruijn depth.
------------------------------------------------------------------------

data Ctx : Set
⌊_⌋ : Ctx → Cx

data Ctx where
  ◇   : Ctx
  _▹_ : (Γ : Ctx) → RTy ⌊ Γ ⌋ → Ctx

⌊ ◇ ⌋     = ε
⌊ Γ ▹ A ⌋ = ⌊ Γ ⌋ ∙

------------------------------------------------------------------------
-- Variable typing (looked-up types are weakened into the deeper context).
------------------------------------------------------------------------

infix 3 _∋_∷_
data _∋_∷_ : (Γ : Ctx) → Var ⌊ Γ ⌋ → RTy ⌊ Γ ⌋ → Set where
  here  : ∀ {Γ} {A : RTy ⌊ Γ ⌋} → (Γ ▹ A) ∋ vz ∷ renTy vs A
  there : ∀ {Γ} {A B : RTy ⌊ Γ ⌋} {x} →
          Γ ∋ x ∷ A → (Γ ▹ B) ∋ vs x ∷ renTy vs A

