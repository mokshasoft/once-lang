------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ SPIKE: CAN AN `ielim` PRODUCE AN ELEMENT OF
-- ITS OWN FAMILY AT A **SHIFTED INDEX**?
--
-- HANDOFF-2026-08-26 step A, second half — the gate on the judgement
-- layer.  `_∋_∷_`'s `here` is
--
--     here : (Γ ▹ A) ∋ vz ∷ renTy vs A
--
-- so its index mentions `renTy`, a FUNCTION of an encoded term.  For the
-- judgement to be describable, weakening must EXIST object-level: an
-- `ielim` returning a KNOT ELEMENT at a different index.  `Lib/IFold`
-- does not reach it — that folds into a CONSTANT `Nat` motive, and this
-- needs a motive that MOVES THE INDEX.
--
-- ★ THE SMALLEST THING WITH BOTH FEATURES is `wkFin : Fin n → Fin (suc n)`
--   over `Examples/Scoped`'s `Fin`: two constructors, and
--
--     M(i, t) = Fin (suc ⟨i⟩)
--
--   is a motive that mentions the INDEX slot and lands in the family
--   being eliminated.
--
-- ★ D074 (fibred): a method sees the INDEX `i` it is at, so the
--   `fzero` case needs NO ford at all — the answer is `fzero` at `i`
--   (`ffz i : Fin (suc i)`), read straight off the fibre.
--
-- ⚠ THE SECOND CONSTRUCTOR IS WHERE IT BITES.  `fsuc`'s field `k` sits
--   at `m`, known to relate to `i` only through its FORD `suc m ≡ i` —
--   an `Id`, PROPOSITIONAL — so using the IH (at `suc m`) where the
--   answer needs `Fin i` is a TRANSPORT, not a conversion: Fording's
--   debt, called in once per forded recursive field.
--
-- ★★★ RESULT: IT WORKS, AND THE TRANSPORT IS ONE FORWARD `⊢jsub`
--   (`jsub (⌜IMu⌝ ⌜Nat⌝ FinD ⟨-⟩) ford ih : Fin i` — no `sym`, since
--   the ford already points at the fibre).  ⚠ IT WORKS ONLY BECAUSE
--   `⌜IMu⌝` IS A CODE: `⊢jsub` transports along a CODE family.
--
-- ⇒ OBJECT-LEVEL RENAMING OVER AN ENCODED INDEXED FAMILY IS FEASIBLE.
--   The judgement layer's gate is open; what remains is BULK plus the
--   same transport once per Forded recursive field.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.WkFin where
open import normalizer.Syntax.Types using ( _,_; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; conₗ; methₗ; selF; selF-β; nth-z; nth-s; MethK; PerK; []ₘ; _∷ₘ_; ⊢methₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ )
open import DirectedHoTT.Examples.Scoped
  using ( FinTs; FinD; ⊢FinD; FinOK; FinI; fzeroT; fsucT; fzeroOK; fsucOK
        ; ffz; ffs; ⊢ffz; ⊢ffs; ⊢isuc; toI )

-- `El (⌜IMu⌝ ⌜Nat⌝ FinD n) ≅ᵀ Fin n`
fromFin : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El (⌜IMu⌝ ⌜Nat⌝ FinD n) → Γ ⊢ t ∷ FinI n
fromFin d = ⊢conv d (credᵀ El-⌜IMu⌝)

toFin : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ FinI n → Γ ⊢ t ∷ El (⌜IMu⌝ ⌜Nat⌝ FinD n)
toFin d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

------------------------------------------------------------------------
-- 1. ★★★ THE MOTIVE THAT MOVES THE INDEX:  M(i, t) = Fin (suc i).
------------------------------------------------------------------------

wkMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
wkMot = FinI (nsuc (var (vs vz)))

⊢wkMot : {Γ : Ctx} → ((Γ ▹ El ⌜Nat⌝) ▹ FinI (var vz)) ⊢ty wkMot
⊢wkMot = ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢isuc (⊢var (there here)))

------------------------------------------------------------------------
-- 2. THE METHODS.  In the method context (`HypCtx`): `v₂` the index,
--    `v₁` the payload, `v₀` the hypotheses.
------------------------------------------------------------------------

v₀ v₁ v₂ : {Γ : Cx} → RTm (((Γ ∙) ∙) ∙)
v₀ = var vz
v₁ = var (vs vz)
v₂ = var (vs (vs vz))

-- `fzero`: the answer is `fzero` AT THE FIBRE — no ford consulted.
mfz : {Γ : Cx} → RTm Γ
mfz = lam (lam (lam (ffz v₂)))

-- ★★★ `fsuc`: transport the IH (at `suc m`) along the ford (`suc m ≡ i`).
fordOf ihOf : {Γ : Cx} → RTm (((Γ ∙) ∙) ∙)
fordOf = fst (snd (snd v₁))
ihOf   = fst v₀

trFin : {Γ : Cx} → RTm (((Γ ∙) ∙) ∙)
trFin = jsub (⌜IMu⌝ ⌜Nat⌝ FinD (var vz)) fordOf ihOf

mfs : {Γ : Cx} → RTm Γ
mfs = lam (lam (lam (ffs v₂ trFin)))

WkMs : {Γ : Cx} → Cons Γ 2
WkMs = mfz ∷ mfs ∷ []

module _ {Γ : Ctx} where
  private
    HZ = HypCtx Γ ⌜Nat⌝ FinD wkMot fzeroT
    HS = HypCtx Γ ⌜Nat⌝ FinD wkMot fsucT

  ⊢mfz : Γ ⊢ mfz ∷ MethK ⌜Nat⌝ FinD wkMot ⌜ fzeroT ⌝ᵗ zero
  ⊢mfz = ⊢methT {T = fzeroT} {s = conₗ zero (var (vs vz))} ⊢⌜Nat⌝ ⊢FinD ⊢wkMot fzeroOK
           (⊢ffz (⊢var (there (there here))))

  -- the pieces of the `fsuc` body, each at its own named type
  ⊢idx : HS ⊢ v₂ ∷ El ⌜Nat⌝
  ⊢idx = ⊢var (there (there here))

  ⊢pay : HS ⊢ v₁ ∷ PayN ⟨ (λ x → vs (vs x)) ⟩ᵣ fsucT ⌜Nat⌝ FinD
  ⊢pay = ⊢payHyp {I = ⌜Nat⌝} {D = FinD} {M = wkMot} {T = fsucT}

  ⊢m : HS ⊢ fst v₁ ∷ El ⌜Nat⌝
  ⊢m = ⊢fst ⊢pay

  ⊢ford : HS ⊢ fordOf ∷ Id (El ⌜Nat⌝) (nsuc (fst v₁)) v₂
  ⊢ford = ⊢conv (⊢fst (⊢snd (⊢snd ⊢pay))) (credᵀ (El-⌜Id⌝ ⌜Nat⌝ _ _))

  ⊢ih : HS ⊢ ihOf ∷ El (⌜IMu⌝ ⌜Nat⌝ FinD (nsuc (fst v₁)))
  ⊢ih = toFin (⊢fst (⊢var here))

  ⊢trF : HS ⊢ trFin ∷ FinI v₂
  ⊢trF = fromFin (⊢jsub (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢var here)) (⊢isuc ⊢m) ⊢idx ⊢ford ⊢ih)

  ⊢mfs : Γ ⊢ mfs ∷ MethK ⌜Nat⌝ FinD wkMot ⌜ fsucT ⌝ᵗ (suc zero)
  ⊢mfs = ⊢methT {T = fsucT} {s = conₗ (suc zero) (var (vs vz))}
           ⊢⌜Nat⌝ ⊢FinD ⊢wkMot fsucOK (⊢ffs ⊢idx ⊢trF)

  perWk : PerK Γ ⌜Nat⌝ FinD wkMot (selF ⌜ FinTs ⌝ₛ) zero WkMs
  perWk = (selF-β {Cs = ⌜ FinTs ⌝ₛ} nth-z , ⊢mfz)
       ∷ₘ ((selF-β {Cs = ⌜ FinTs ⌝ₛ} (nth-s nth-z) , ⊢mfs) ∷ₘ []ₘ)

------------------------------------------------------------------------
-- 3. ★★★ OBJECT-LEVEL WEAKENING: `Fin n → Fin (suc n)`, by `ielim`.
------------------------------------------------------------------------

wkFinTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkFinTm n k = ielim FinD n (methₗ WkMs) k

-- ⚠ ONE `wk-single`: `iinst n k M` weakens the index past the scrutinee
--   binder and substitutes it back — the residue every two-slot motive pays.
⊢wkFinTm : {Γ : Ctx} {n k : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ k ∷ FinI n → Γ ⊢ wkFinTm n k ∷ FinI (nsuc n)
⊢wkFinTm {n = n} dn dk =
  ⊢-cast (cong (λ z → FinI (nsuc z)) (wk-single n))
    (⊢ielim ⊢⌜Nat⌝ ⊢FinD ⊢wkMot (⊢methₗ ⊢⌜Nat⌝ (allD (⊢wk ⊢⌜Nat⌝) FinOK) ⊢wkMot perWk) dn dk)

------------------------------------------------------------------------
-- 4. ★★ …AND IT COMPUTES.  `fz : Fin 1` weakens to `fzero` at index 2:
--    ι, then the method's three β — and the fibre hands the method its
--    index, so the answer is literally `ffz 1`.
------------------------------------------------------------------------

wk-fz : {Γ : Cx} → wkFinTm {Γ} (nsuc nzero) (ffz nzero) ⟶* ffz (nsuc nzero)
wk-fz =
  ⟶*-trans (ιT {T = fzeroT} (nth-⌜⌝ {Ts = FinTs} nthᵗ-z) nth-z)
    (step (ξ-appˡ (ξ-appˡ (β _ _))) (step (ξ-appˡ (β _ _)) (step (β _ _) done)))

-- ★★ AND THE TRANSPORT COMPUTES: at a concrete `fsuc` the ford IS an
--   `idrefl`, so the `jsub` fires once and the IH passes through.
transport-fires : {Γ : Cx} (d : RTm (Γ ∙)) (x e : RTm Γ) →
                  jsub d (idrefl ⌜Nat⌝ x) e ⟶* e
transport-fires d x e = step (jsub-refl d ⌜Nat⌝ x e) done
