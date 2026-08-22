------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES, WF-AXIS STAGE C + D: THE ORDER TYPE IS SMALL,
-- AND FALSE INEQUALITIES ARE USABLE.
--
-- Stage B showed the order COMPUTES (`NbEPDirDBExamplesOrd`).  What
-- stages C and D add is that it computes *as a first-class type*:
--
--   ★ stage C — `Nat`, `Unit` and the ORDER TYPE have CODES, so they
--     live in `U` and can be the motive of a transport or the domain
--     of a Π.  Before stage C, `Hom Nat m n` was a type you could
--     form but not quantify over.
--   ★ stage D — `base` has an ELIMINATOR, so a false inequality is no
--     longer merely uninhabited-in-the-metatheory: it is a term you
--     can USE.  That is what makes the impossible branch of a
--     well-founded recursion writable INSIDE the language.
--
--   ★ `nat-small` / `unit-small` — the datatype codes typecheck at `U`
--   ★ `order-small`   — ★ THE ONE STAGE C BOUGHT: `1 ≤ 2` has a CODE
--   ★ `le-decodes`    — …and that code decodes to `Unit`
--   ★ `lt-decodes`    — …while the FALSE one decodes to `base`
--   ★ `from-false`    — ★ THE ONE STAGE D BOUGHT: ex falso on it
--   ★ `no-tr-at-Nat`  — the negative control: `⊢tr`'s stage-C premise
--                       really does exclude a bare ⌜Nat⌝ motive
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Small where
open import normalizer.Syntax.Types using ( _≡_; refl; ⊥ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; ⌜Hom⌝; ⌜Nat⌝; ⌜Unit⌝; absurd
        ; unit; nzero; nsuc )
open import DirectedHoTT.Spec.Variance using ( NoNatC )
open import DirectedHoTT.Spec.Typing
  using ( _⟶ᵀ_
        ; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜Hom⌝; ξ-Homᵀ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ
        ; Ctx; ◇; ⌊_⌋
        ; _⊢_∷_; ⊢conv; ⊢unit; ⊢nzero; ⊢nsuc
        ; ⊢⌜Nat⌝; ⊢⌜Unit⌝; ⊢⌜Hom⌝; ⊢absurd )
open import DirectedHoTT.Metatheory.Injectivity using ( _⟶ᵀ*_; doneᵀ; stepᵀ; red→≅ᵀ )

n1 n2 : {Γ : Cx} → RTm Γ
n1 = nsuc nzero
n2 = nsuc (nsuc nzero)

⊢n1 : {Γ : Ctx} → Γ ⊢ n1 ∷ El ⌜Nat⌝
⊢n1 = ⊢conv (⊢nsuc ⊢nzero) (csymᵀ (credᵀ El-⌜Nat⌝))

⊢n2 : {Γ : Ctx} → Γ ⊢ n2 ∷ El ⌜Nat⌝
⊢n2 = ⊢conv (⊢nsuc (⊢nsuc ⊢nzero)) (csymᵀ (credᵀ El-⌜Nat⌝))

------------------------------------------------------------------------
-- 1. STAGE C: the datatypes are SMALL — they have codes at `U`.
------------------------------------------------------------------------

nat-small : {Γ : Ctx} → Γ ⊢ ⌜Nat⌝ ∷ U
nat-small = ⊢⌜Nat⌝

unit-small : {Γ : Ctx} → Γ ⊢ ⌜Unit⌝ ∷ U
unit-small = ⊢⌜Unit⌝

------------------------------------------------------------------------
-- 2. ★ AND SO IS THE ORDER.  `1 ≤ 2` is not merely a type one can
--    form — it has a CODE, so it can be quantified over, be a Π
--    domain, or be a transport motive.  This is the thing stage C
--    bought, and it is why the WF axis can talk about `m ≤ n` as data.
------------------------------------------------------------------------

le-code : {Γ : Cx} → RTm Γ
le-code = ⌜Hom⌝ ⌜Nat⌝ n1 n2

lt-code : {Γ : Cx} → RTm Γ
lt-code = ⌜Hom⌝ ⌜Nat⌝ n2 n1

order-small : {Γ : Ctx} → Γ ⊢ le-code ∷ U
order-small = ⊢⌜Hom⌝ ⊢⌜Nat⌝ ⊢n1 ⊢n2

------------------------------------------------------------------------
-- 3. The codes DECODE the way stage B's types reduce: the true
--    inequality to `Unit`, the false one to `base`.  Two extra steps
--    on the front (`El-⌜Hom⌝`, then `El-⌜Nat⌝` under the ambient) and
--    then it is stage B verbatim.
------------------------------------------------------------------------

le-decodes : {Γ : Cx} → El (le-code {Γ}) ⟶ᵀ* Unit
le-decodes =
  stepᵀ (El-⌜Hom⌝ _ _ _)
    (stepᵀ (ξ-Homᵀ El-⌜Nat⌝)
      (stepᵀ (Hom-Nat-ss _ _)
        (stepᵀ (Hom-Nat-z _) doneᵀ)))

lt-decodes : {Γ : Cx} → El (lt-code {Γ}) ⟶ᵀ* base
lt-decodes =
  stepᵀ (El-⌜Hom⌝ _ _ _)
    (stepᵀ (ξ-Homᵀ El-⌜Nat⌝)
      (stepᵀ (Hom-Nat-ss _ _)
        (stepᵀ (Hom-Nat-sz _) doneᵀ)))

-- the order proof is still literally `unit`, now at the DECODED code.
⊢le : {Γ : Ctx} → Γ ⊢ unit ∷ El le-code
⊢le = ⊢conv ⊢unit (csymᵀ (red→≅ᵀ le-decodes))

------------------------------------------------------------------------
-- 4. ★★ STAGE D: FROM A FALSE INEQUALITY, ANYTHING.
--
-- `2 ≤ 1` decodes to `base`, so a hypothesis of that type IS a
-- hypothesis of the empty type — and `absurd` turns it into a term of
-- any small type.  Note what this is NOT: it is not `consistency`,
-- which says no CLOSED such hypothesis exists.  This works in an OPEN
-- context, where the hypothesis is a variable, and that is exactly the
-- situation inside the impossible branch of a well-founded recursion.
--
-- Before stage D the branch was refutable only meta-theoretically;
-- now it is a term.
------------------------------------------------------------------------

from-false : {Γ : Ctx} {h : RTm ⌊ Γ ⌋} →
             Γ ⊢ h ∷ Hom Nat n2 n1 →
             Γ ⊢ absurd ⌜Nat⌝ h ∷ El ⌜Nat⌝
from-false d =
  ⊢absurd ⊢⌜Nat⌝
    (⊢conv d (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) (stepᵀ (Hom-Nat-sz _) doneᵀ))))

-- …and it lands in ANY small type, not just `Nat`: here the order
-- type itself, which is the shape a WF recursion actually needs (the
-- impossible branch must produce the recursion's own motive).
from-false-anywhere : {Γ : Ctx} {h : RTm ⌊ Γ ⌋} →
                      Γ ⊢ h ∷ Hom Nat n2 n1 →
                      Γ ⊢ absurd le-code h ∷ El le-code
from-false-anywhere d =
  ⊢absurd order-small
    (⊢conv d (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) (stepᵀ (Hom-Nat-sz _) doneᵀ))))

------------------------------------------------------------------------
-- 5. THE NEGATIVE CONTROL.  `⊢tr` gained a `NoNatC c` premise in stage
--    C, and it really does exclude a BARE ⌜Nat⌝ motive: `NoNatC` has
--    no ⌜Nat⌝ constructor, so the premise is unsatisfiable there.
--
--    ⚠ Read this together with `SpikeNatJ`: the exclusion is exactly
--    one code wide.  `⌜Hom⌝ ⌜Nat⌝ a b` — a hom OVER the ordered type —
--    IS J-able and does fire, which is what the `stkA?`/`stkC?` split
--    fixed.  Ordered types are not J-able; homs over them are.
------------------------------------------------------------------------

no-tr-at-Nat : {Γ : Cx} → NoNatC (⌜Nat⌝ {Γ}) → ⊥
no-tr-at-Nat ()

-- …whereas the hom OVER it satisfies nothing of the sort and needs no
-- exclusion: it is an ordinary stable code.  (That `⌜Hom⌝ ⌜Nat⌝ 1 2`
-- is J-able is `SpikeNatJ.stuck-steps`.)
