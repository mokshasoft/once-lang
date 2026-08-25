------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ A FAMILY INDEXED BY A PAIR.
--
--        K : (sort, depth) → Set
--
--        kbase :                        K (0, d)      -- a TYPE
--        kvar  :                        K (1, d)      -- a TERM
--        klam  : K (1, suc d)         → K (1, d)      -- DEPTH shifts
--        kann  : K (1, d) → K (0, d)  → K (1, d)      -- SORT crosses
--
-- ★ WHY THIS FILE EXISTS.  §13 settled that mutual sorts are one
--   description over a tagged index, and §12 settled nested families.
--   Both were measured at `I = El ⌜Nat⌝`, and so is EVERY OTHER EXAMPLE
--   in the development.  The real `RTm` knot cannot be: its index is a
--   sort tag AND a context depth, and `RTy`-at-the-same-depth is a
--   FUNCTION OF THE AMBIENT INDEX in one component while the other is
--   held fixed.  Whether `I` may be a `Σ'` at all was therefore an
--   untested assumption underneath §13's plan.
--
--   ⇒ IT MAY.  `I : RTy ε` is a raw TYPE, not a code, so nothing here
--     needs `⌜Σ⌝` at all (one does exist, with `El-⌜Σ⌝`; it is simply
--     not on this path).
--
-- ★★ THE TRICK THAT MAKES IT CHEAP: **FORD THE COMPONENT, NOT THE
--   PAIR.**  A constructor fixes only its SORT, so its constraint is
--   `Id Nat (fst ⟨i⟩) t` — an `Id` at `Nat`.  Fording the whole index
--   would instead need `Id (Σ' Nat Nat) ⟨i⟩ (pair t d)`, which forces
--   you to PIN `d` — and `d` is exactly the component that must stay
--   free.  `iι` already targets the ambient `i`, so the depth simply
--   RIDES: unconstrained, unmentioned, and costing nothing.
--
-- ⚠ WHAT THIS COSTS, stated plainly: the index is now a term with
--   PROJECTIONS in it (`snd ⟨i⟩`), and `fst`/`snd` are TERM FORMERS
--   that reduce by `βfst`/`βsnd` — not definitional projections.  So a
--   recursive field's index does not simplify until the ambient index
--   is a concrete `pair`, and every reduction chain below pays two
--   extra steps per projection.  That is a chain-length cost, not a
--   typing one.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.PairIx where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; U; El; Π; Σ'; Unit; Nat; IMu
        ; RTm; var; lam; app; pair; fst; snd; unit; nzero; nsuc
        ; ⌜Nat⌝; ⌜Id⌝; idrefl; icon; ielim
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_
        ; ilookupD; _∈ID_; hereID; thereID
        ; ipayTy; isingle; iext; ifields; sel )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _∋_∷_; here; there
        ; _⟶_; _⟶*_; done; step
        ; β; βfst; βsnd; ξ-appˡ; ξ-fst; ξ-snd; ξ-nsuc; ξ-pairˡ; ξ-pairʳ
        ; ξ-ielimⁱ; ξ-ielimᵗ; ι-ielim
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ; credᵀ
        ; _⟶ᵀ_; El-⌜Nat⌝; El-⌜Id⌝; ξ-El; ξ-IMu; ξ-⌜Id⌝ˡ
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢conv
        ; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢idrefl
        ; ⊢icon; ⊢ielim
        ; _⊢ty_; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-Π; ty-IMu
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; ICodeWf; icw-clo; icw-ford
        ; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTy )

------------------------------------------------------------------------
-- 0. The index type: A PAIR.  ⚠ `Σ' Nat Nat`, NOT `El` of a code —
--    there is no `⌜Σ⌝`, and `ty-IMu`/`⌜IMu⌝` never ask for one.
------------------------------------------------------------------------

IPair : RTy ε
IPair = Σ' Nat Nat

sTy sTm : {Γ : Cx} → RTm Γ
sTy = nzero
sTm = nsuc nzero

-- the ambient index, and its two components, at one binder in
ix : {Γ : Cx} → RTm (Γ ∙)
ix = var vz

-- `Γ ⊢ i ∷ IPair → Γ ⊢ fst i ∷ El ⌜Nat⌝`, the conversion each ford eats
toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

------------------------------------------------------------------------
-- 1. THE DESCRIPTION.
--
-- ⚠ READ THE INDICES.  `klam`'s field is at `pair 1 (suc (snd ⟨i⟩))` —
--   SAME sort, depth PUSHED.  `kann`'s second field is at
--   `pair 0 (snd ⟨i⟩)` — OTHER sort, depth HELD.  Those two lines are
--   the whole shape of `RTm ↔ RTy` under a binder, and they are the
--   reason a single-`Nat` index would not have done: one component has
--   to move while the other stays.
------------------------------------------------------------------------

kbaseC : ICon (ε ∙)
kbaseC = iκ (⌜Id⌝ ⌜Nat⌝ (fst ix) sTy) iι

kvarC : ICon (ε ∙)
kvarC = iκ (⌜Id⌝ ⌜Nat⌝ (fst ix) sTm) iι

klamC : ICon (ε ∙)
klamC =
  iρ (pair sTm (nsuc (snd ix)))
   (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs vz))) sTm) iι)

kannC : ICon (ε ∙)
kannC =
  iρ (pair sTm (snd ix))
   (iρ (pair sTy (snd (var (vs vz))))
    (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sTm) iι))

KD : IDesc
KD = kbaseC ◂ (kvarC ◂ (klamC ◂ (kannC ◂ inil)))

K : {Γ : Cx} → RTm Γ → RTy Γ
K i = IMu KD IPair i

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS.  ⚠ `εwkTy (Σ' Nat Nat) = Σ' Nat Nat` — the index
--    type is closed, so no weakening appears in any premise.
------------------------------------------------------------------------

kbaseWf : IConWf KD IPair (◇ ▹ IPair) kbaseC
kbaseWf =
  iwf-κ (⌜Id⌝ ⌜Nat⌝ (fst ix) sTy)
        (icw-ford ⌜Nat⌝ (fst ix) sTy)
        (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var here))) (toI ⊢nzero))
        iwf-ι

kvarWf : IConWf KD IPair (◇ ▹ IPair) kvarC
kvarWf =
  iwf-κ (⌜Id⌝ ⌜Nat⌝ (fst ix) sTm)
        (icw-ford ⌜Nat⌝ (fst ix) sTm)
        (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var here))) (toI (⊢nsuc ⊢nzero)))
        iwf-ι

-- ★★★ the binder row: the recursive field's index is a PAIR TERM whose
--   second component is `suc` of the ambient's second component.
klamWf : IConWf KD IPair (◇ ▹ IPair) klamC
klamWf =
  iwf-ρ (pair sTm (nsuc (snd ix)))
        (⊢pair ty-Nat (⊢nsuc ⊢nzero) (⊢nsuc (⊢snd (⊢var here))))
   (iwf-κ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs vz))) sTm)
          (icw-ford ⌜Nat⌝ (fst (var (vs vz))) sTm)
          (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (there here))))
                        (toI (⊢nsuc ⊢nzero)))
          iwf-ι)

-- ★★★ the cross-sort row: FIRST component changes, SECOND is held.
kannWf : IConWf KD IPair (◇ ▹ IPair) kannC
kannWf =
  iwf-ρ (pair sTm (snd ix))
        (⊢pair ty-Nat (⊢nsuc ⊢nzero) (⊢snd (⊢var here)))
   (iwf-ρ (pair sTy (snd (var (vs vz))))
          (⊢pair ty-Nat ⊢nzero (⊢snd (⊢var (there here))))
    (iwf-κ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sTm)
           (icw-ford ⌜Nat⌝ (fst (var (vs (vs vz)))) sTm)
           (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (there (there here)))))
                         (toI (⊢nsuc ⊢nzero)))
           iwf-ι))

KWf : IDescWf IPair KD
KWf = idwf-cons kbaseWf (idwf-cons kvarWf (idwf-cons klamWf
        (idwf-cons kannWf idwf-nil)))

------------------------------------------------------------------------
-- 3. INHABITATION — ⚠ THE PART THAT MAKES §2 MEAN SOMETHING.
--
-- A description can be well-formed and still have no closed inhabitant
-- at any index (`Examples/Vec.no-cons-at-zero` is that hazard proved on
-- purpose).  So §2 alone would be `verification-that-covers-less-than-
-- it-claims`: it says the WF judgement accepts a pair index, not that
-- anything lives at one.  Below, four closed terms do.
--
-- ⚠ THIS IS WHERE THE PROJECTIONS GET PAID FOR.  At a concrete index
--   `pair t d` the payload types still read `fst (pair t d)` and
--   `snd (pair t d)`: `fst`/`snd` are TERM FORMERS that step by
--   `βfst`/`βsnd`, not definitional projections.  Every such spot needs
--   an explicit conversion — `ξ-El`/`ξ-⌜Id⌝ˡ` for a constraint field,
--   `ξ-IMu` for a recursive one.  Both congruences already existed;
--   `ξ-IMu` is there for `ielim`'s retyping (see its note in `Typing`),
--   and this file is its second customer.
------------------------------------------------------------------------

⊢ixP : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
       Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ pair a b ∷ Σ' Nat Nat
⊢ixP da db = ⊢pair ty-Nat da db

⊢ixTm₀ : {Γ : Ctx} → Γ ⊢ pair sTm nzero ∷ Σ' Nat Nat
⊢ixTm₀ = ⊢ixP (⊢nsuc ⊢nzero) ⊢nzero

⊢ixTy₀ : {Γ : Ctx} → Γ ⊢ pair sTy nzero ∷ Σ' Nat Nat
⊢ixTy₀ = ⊢ixP ⊢nzero ⊢nzero

-- convert along a reduction OF THE INDEX
ixConv : {Γ : Ctx} {t i i' : RTm ⌊ Γ ⌋} →
         i ⟶ i' → Γ ⊢ t ∷ K i' → Γ ⊢ t ∷ K i
ixConv r d = ⊢conv d (csymᵀ (credᵀ (ξ-IMu r)))

-- the Fording witness at a concrete index: `fst (pair t d)` must first
-- STEP to `t`, hence `ξ-El (ξ-⌜Id⌝ˡ (βfst …))`.
fordAt : {Γ : Ctx} {t d : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ Nat →
         Γ ⊢ idrefl ⌜Nat⌝ t ∷ El (⌜Id⌝ ⌜Nat⌝ (fst (pair t d)) t)
fordAt {t = t} {d = d} dt =
  ⊢conv (⊢idrefl ⊢⌜Nat⌝ (toI dt))
    (csymᵀ (ctrnᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βfst t d))))
                  (credᵀ (El-⌜Id⌝ ⌜Nat⌝ t t))))

tyFordAt : {Γ : Ctx} {t d : RTm ⌊ Γ ⌋} →
           Γ ⊢ t ∷ Nat → Γ ⊢ d ∷ Nat →
           Γ ⊢ty Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (pair t d)) t)) Unit
tyFordAt {t = t} {d = d} dt dd =
  ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢ixP dt dd))) (toI dt))) ty-Unit

kbase kvar : {Γ : Cx} → RTm Γ
kbase = icon zero (pair (idrefl ⌜Nat⌝ sTy) unit)
kvar  = icon (suc zero) (pair (idrefl ⌜Nat⌝ sTm) unit)

klam : {Γ : Cx} → RTm Γ → RTm Γ
klam b = icon (suc (suc zero)) (pair b (pair (idrefl ⌜Nat⌝ sTm) unit))

kann : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
kann t a = icon (suc (suc (suc zero)))
                (pair t (pair a (pair (idrefl ⌜Nat⌝ sTm) unit)))

⊢kbase₀ : ◇ ⊢ kbase ∷ K (pair sTy nzero)
⊢kbase₀ = ⊢icon KWf hereID ⊢ixTy₀
            (⊢pair ty-Unit (fordAt ⊢nzero) ⊢unit)

⊢kvar₀ : ◇ ⊢ kvar ∷ K (pair sTm nzero)
⊢kvar₀ = ⊢icon KWf (thereID hereID) ⊢ixTm₀
           (⊢pair ty-Unit (fordAt (⊢nsuc ⊢nzero)) ⊢unit)

-- ★★★ THE BINDER.  The field's index is `pair 1 (suc (snd (pair 1 0)))`
--   — the ambient's SECOND component, pushed.  `ixConv` reduces the
--   projection away, and `ξ-pairʳ`/`ξ-nsuc` are how the step gets under
--   the pair.
⊢klam₀ : {b : RTm ε} →
         ◇ ⊢ b ∷ K (pair sTm (nsuc nzero)) → ◇ ⊢ klam b ∷ K (pair sTm nzero)
⊢klam₀ db =
  ⊢icon KWf (thereID (thereID hereID)) ⊢ixTm₀
    (⊢pair (tyFordAt (⊢nsuc ⊢nzero) ⊢nzero)
           (ixConv (ξ-pairʳ (ξ-nsuc (βsnd sTm nzero))) db)
           (⊢pair ty-Unit (fordAt (⊢nsuc ⊢nzero)) ⊢unit))

-- ★★★ THE CROSS-SORT CONSTRUCTOR: first component changes (1 → 0),
--   second is held.  Both fields convert through the SAME `βsnd`.
⊢kann₀ : {t a : RTm ε} →
         ◇ ⊢ t ∷ K (pair sTm nzero) → ◇ ⊢ a ∷ K (pair sTy nzero) →
         ◇ ⊢ kann t a ∷ K (pair sTm nzero)
⊢kann₀ dt da =
  ⊢icon KWf (thereID (thereID (thereID hereID))) ⊢ixTm₀
    (⊢pair (ty-Σ (ty-IMu KWf (⊢ixP ⊢nzero (⊢snd ⊢ixTm₀)))
                 (tyFordAt (⊢nsuc ⊢nzero) ⊢nzero))
           (ixConv (ξ-pairʳ (βsnd sTm nzero)) dt)
           (⊢pair (tyFordAt (⊢nsuc ⊢nzero) ⊢nzero)
                  (ixConv (ξ-pairʳ (βsnd sTm nzero)) da)
                  (⊢pair ty-Unit (fordAt (⊢nsuc ⊢nzero)) ⊢unit)))

-- `ann (λ. var) base` — a term that uses the binder AND both sorts.
kterm : {Γ : Cx} → RTm Γ
kterm = kann (klam kvar) kbase

⊢kterm : ◇ ⊢ kterm ∷ K (pair sTm nzero)
⊢kterm = ⊢kann₀ (⊢klam₀ ⊢kvar₁) ⊢kbase₀
  where
    ⊢kvar₁ : ◇ ⊢ kvar ∷ K (pair sTm (nsuc nzero))
    ⊢kvar₁ = ⊢icon KWf (thereID hereID) (⊢ixP (⊢nsuc ⊢nzero) (⊢nsuc ⊢nzero))
               (⊢pair ty-Unit (fordAt (⊢nsuc ⊢nzero)) ⊢unit)

------------------------------------------------------------------------
-- 4. AND `ielim` WORKS THERE.  ⚠ THE POINT OF THIS SECTION.
--
-- §5 item 7 does not want a pair-indexed family for its own sake — it
-- wants `sz : RTm → Nat` to be DEFINABLE, and `sz` is an `ielim`.  So
-- what has to hold is not just that a pair index TYPES, but that the
-- recursor accepts a motive over one.  It does: the motive is constant
-- (`Nat`), and the index binder each method carries is now bound at
-- `Σ' Nat Nat` rather than `El ⌜Nat⌝` — the only visible difference.
------------------------------------------------------------------------

mbase mvar mlam mann ms : {Γ : Cx} → RTm Γ
mbase = lam (lam (lam (nsuc nzero)))
mvar  = lam (lam (lam (nsuc nzero)))
mlam  = lam (lam (lam (nsuc (fst (var vz)))))
mann  = lam (lam (lam (nsuc (fst (snd (var vz))))))
ms    = pair mbase (pair mvar (pair mlam (pair mann unit)))

dep : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
dep i t = ielim KD i ms t

tyIH₁ : {Γ : Ctx} → Γ ⊢ty Σ' Nat Unit
tyIH₁ = ty-Σ ty-Nat ty-Unit

tyIH₂ : {Γ : Ctx} → Γ ⊢ty Σ' Nat (Σ' Nat Unit)
tyIH₂ = ty-Σ ty-Nat (ty-Σ ty-Nat ty-Unit)

-- ⚠ the index binder is at `Σ' Nat Nat` now — `⊢var here` still gives
--   the ambient index, and `⊢fst`/`⊢snd` take it apart.
tyPayBase : {Γ : Ctx} →
            (Γ ▹ Σ' Nat Nat) ⊢ty
            Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var vz)) sTy)) Unit
tyPayBase =
  ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var here))) (toI ⊢nzero))) ty-Unit

tyPayVar : {Γ : Ctx} →
           (Γ ▹ Σ' Nat Nat) ⊢ty
           Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var vz)) sTm)) Unit
tyPayVar =
  ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var here)))
                            (toI (⊢nsuc ⊢nzero)))) ty-Unit

tyPayLam : {Γ : Ctx} →
           (Γ ▹ Σ' Nat Nat) ⊢ty
           Σ' (IMu KD IPair (pair sTm (nsuc (snd (var vz)))))
              (Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var (vs vz))) sTm)) Unit)
tyPayLam =
  ty-Σ (ty-IMu KWf (⊢ixP (⊢nsuc ⊢nzero) (⊢nsuc (⊢snd (⊢var here)))))
    (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (there here))))
                               (toI (⊢nsuc ⊢nzero)))) ty-Unit)

tyPayAnn : {Γ : Ctx} →
           (Γ ▹ Σ' Nat Nat) ⊢ty
           Σ' (IMu KD IPair (pair sTm (snd (var vz))))
              (Σ' (IMu KD IPair (pair sTy (snd (var (vs vz)))))
                  (Σ' (El (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sTm)) Unit))
tyPayAnn =
  ty-Σ (ty-IMu KWf (⊢ixP (⊢nsuc ⊢nzero) (⊢snd (⊢var here))))
    (ty-Σ (ty-IMu KWf (⊢ixP ⊢nzero (⊢snd (⊢var (there here)))))
      (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (there (there here)))))
                                 (toI (⊢nsuc ⊢nzero)))) ty-Unit))

tyΠbase tyΠvar tyΠlam tyΠann : {Γ : Ctx} → Γ ⊢ty _
tyΠbase = ty-Π (ty-Σ ty-Nat ty-Nat) (ty-Π tyPayBase (ty-Π ty-Unit ty-Nat))
tyΠvar  = ty-Π (ty-Σ ty-Nat ty-Nat) (ty-Π tyPayVar  (ty-Π ty-Unit ty-Nat))
tyΠlam  = ty-Π (ty-Σ ty-Nat ty-Nat) (ty-Π tyPayLam  (ty-Π tyIH₁ ty-Nat))
tyΠann  = ty-Π (ty-Σ ty-Nat ty-Nat) (ty-Π tyPayAnn  (ty-Π tyIH₂ ty-Nat))

⊢ms : ◇ ⊢ ms ∷ imethsTy KD IPair Nat KD
⊢ms =
  ⊢pair (ty-Σ tyΠvar (ty-Σ tyΠlam (ty-Σ tyΠann ty-Unit)))
        (⊢lam (ty-Σ ty-Nat ty-Nat)
          (⊢lam tyPayBase (⊢lam ty-Unit (⊢nsuc ⊢nzero))))
    (⊢pair (ty-Σ tyΠlam (ty-Σ tyΠann ty-Unit))
           (⊢lam (ty-Σ ty-Nat ty-Nat)
             (⊢lam tyPayVar (⊢lam ty-Unit (⊢nsuc ⊢nzero))))
      (⊢pair (ty-Σ tyΠann ty-Unit)
             (⊢lam (ty-Σ ty-Nat ty-Nat)
               (⊢lam tyPayLam (⊢lam tyIH₁ (⊢nsuc (⊢fst (⊢var here))))))
        (⊢pair ty-Unit
               (⊢lam (ty-Σ ty-Nat ty-Nat)
                 (⊢lam tyPayAnn
                   (⊢lam tyIH₂ (⊢nsuc (⊢fst (⊢snd (⊢var here)))))))
               ⊢unit)))

⊢dep : {i t : RTm ε} → ◇ ⊢ i ∷ Σ' Nat Nat → ◇ ⊢ t ∷ K i → ◇ ⊢ dep i t ∷ Nat
⊢dep di dt = ⊢ielim KWf ty-Nat di ⊢ms dt

-- …and it FIRES at a pair index.
basePay msT1 : {Γ : Cx} → RTm Γ
basePay = pair (idrefl ⌜Nat⌝ sTy) unit
msT1    = pair mvar (pair mlam (pair mann unit))

dep-base : {Γ : Cx} → dep {Γ} (pair sTy nzero) kbase ⟶* nsuc nzero
dep-base =
  step (ι-ielim KD (pair sTy nzero) ms zero basePay)
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst mbase msT1))))
  (step (ξ-appˡ (ξ-appˡ (β (lam (lam (nsuc nzero))) (pair sTy nzero))))
  (step (ξ-appˡ (β (lam (nsuc nzero)) basePay))
  (step (β (nsuc nzero) unit) done))))
