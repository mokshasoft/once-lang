------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ A SYNTAX AS A DESCRIPTION, inside the
-- kernel, LEVITATED and FIBRED: the λ-calculus scoped by CONTEXT DEPTH,
--
--        var : Fin n      → Tm n
--        lam : Tm (suc n) → Tm n        ← the binding shape
--        app : Tm n → Tm n → Tm n
--
-- written as a constructor list of TELESCOPES OVER THE INDEX (`Lib/Tel`)
-- with index code `⌜Nat⌝`, `Fin` itself a family over the same code, and
-- `size` a FOLD (`Lib/TelFold`) — no per-constructor method, no
-- per-constructor typing, and a two-line computation.
--
-- ★★ D074, SEEN FROM A SYNTAX.  A description is FIBRED
--   (`D : Π (El I) (Desc I)`): each constructor telescope sees the index
--   `n` it lands at.  So `lam`'s recursive field is simply `tρ (suc n)`,
--   `var`'s field is `Fin n`, and there is NO index equation anywhere —
--   the targets are INPUTS.  (The one-telescope `Desc I` form made every
--   constructor bind `n` and end with `n ≡ i`, and every index-dependent
--   consumer pay a transport per recursive field.)
--
-- ★ `Fin`'s targets are COMPUTED (`suc m`), so it FORDS, explicitly: each
--   constructor ends with an `⌜Id⌝` field.  Both mechanisms, one file
--   apart — Fording is a choice a family makes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Scoped where
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-nsuc )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Sugar using ( conₗ; methₗ; Dₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.TelFold using ( sizeAlg; foldMs; ⊢foldE; fold-ι )

------------------------------------------------------------------------
-- 0. The index CODE: context depth.  `El ⌜Nat⌝` decodes to `Nat`.
------------------------------------------------------------------------

INat : {Γ : Cx} → RTy Γ
INat = El ⌜Nat⌝

toI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
toI d = ⊢conv d (csymᵀ (credᵀ El-⌜Nat⌝))

fromI : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Nat
fromI d = ⊢conv d (credᵀ El-⌜Nat⌝)

-- `suc` of an index, as an index
⊢isuc : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ nsuc t ∷ El ⌜Nat⌝
⊢isuc d = toI (⊢nsuc (fromI d))

-- an index equation, as a code, and its canonical proof
⊢Eq : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ b ∷ El ⌜Nat⌝ → Γ ⊢ ⌜Id⌝ ⌜Nat⌝ a b ∷ U
⊢Eq = ⊢⌜Id⌝ ⊢⌜Nat⌝

⊢eqrefl : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Nat⌝ → Γ ⊢ idrefl ⌜Nat⌝ a ∷ El (⌜Id⌝ ⌜Nat⌝ a a)
⊢eqrefl {a = a} da = ⊢conv (⊢idrefl ⊢⌜Nat⌝ da) (csymᵀ (credᵀ (El-⌜Id⌝ ⌜Nat⌝ a a)))

------------------------------------------------------------------------
-- 1. `Fin` — a family over the same index code, FORDED (explicitly).
--
--        fzero : (m : Nat) →          suc m ≡ n → Fin n
--        fsuc  : (m : Nat) → Fin m →  suc m ≡ n → Fin n
------------------------------------------------------------------------

fzeroT fsucT : {Γ : Cx} → Tel (Γ ∙)
fzeroT = tσ ⌜Nat⌝ (tσ (⌜Id⌝ ⌜Nat⌝ (nsuc (var vz)) (var (vs vz))) tι)
fsucT  = tσ ⌜Nat⌝ (tρ (var vz) (tσ (⌜Id⌝ ⌜Nat⌝ (nsuc (var vz)) (var (vs vz))) tι))

FinTs : {Γ : Cx} → Tels (Γ ∙) 2
FinTs = fzeroT ∷ᵗ fsucT ∷ᵗ []ᵗ

FinD : {Γ : Cx} → RTm Γ
FinD = Dₗ ⌜ FinTs ⌝ₛ

FinI : {Γ : Cx} → RTm Γ → RTy Γ
FinI n = IMu ⌜Nat⌝ FinD n

fzeroOK : {Γ : Ctx} → TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ fzeroT
fzeroOK = ok-σ ⊢⌜Nat⌝ (ok-σ (⊢Eq (⊢isuc (⊢var here)) (⊢var (there here))) ok-ι)

fsucOK : {Γ : Ctx} → TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ fsucT
fsucOK = ok-σ ⊢⌜Nat⌝ (ok-ρ (⊢var here) (ok-σ (⊢Eq (⊢isuc (⊢var here)) (⊢var (there here))) ok-ι))

FinOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ FinTs
FinOK = fzeroOK ∷ᵒ fsucOK ∷ᵒ []ᵒ

⊢FinD : {Γ : Ctx} → Γ ⊢ FinD ∷ DescF ⌜Nat⌝
⊢FinD = ⊢Dₜ ⊢⌜Nat⌝ FinOK

ffz : {Γ : Cx} → RTm Γ → RTm Γ
ffz m = conₗ zero (pair m (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))

ffs : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
ffs m k = conₗ (suc zero) (pair m (pair k (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))

module _ {Γ : Ctx} {m : RTm ⌊ Γ ⌋} (dm : Γ ⊢ m ∷ El ⌜Nat⌝) where
  private
    dn = ⊢isuc dm
    -- the target, carried under `m`'s binder and instantiated back
    r = subTm (single m) (renTm vs (nsuc m))
    dr : Γ ⊢ r ∷ El ⌜Nat⌝
    dr = subst (λ x → Γ ⊢ x ∷ El ⌜Nat⌝) (sym (wk-single (nsuc m))) dn
    deq : Γ ⊢ idrefl ⌜Nat⌝ (nsuc m) ∷ El (⌜Id⌝ ⌜Nat⌝ (nsuc m) r)
    deq = subst (λ x → Γ ⊢ idrefl ⌜Nat⌝ (nsuc m) ∷ El (⌜Id⌝ ⌜Nat⌝ (nsuc m) x))
                (sym (wk-single (nsuc m))) (⊢eqrefl dn)
    tail = ⊢payσ ⊢⌜Nat⌝ ⊢FinD (ok-σ (⊢Eq dn dr) ok-ι) deq (⊢payι ⊢⌜Nat⌝ ⊢FinD ⊢unit)

  ⊢ffz : Γ ⊢ ffz m ∷ FinI (nsuc m)
  ⊢ffz = ⊢conₜ ⊢⌜Nat⌝ FinOK nthᵗ-z dn
           (⊢payσ ⊢⌜Nat⌝ ⊢FinD (ok-σ ⊢⌜Nat⌝ (ok-σ (⊢Eq (⊢isuc (⊢var here)) (⊢wk dn)) ok-ι)) dm tail)

  ⊢ffs : {k : RTm ⌊ Γ ⌋} → Γ ⊢ k ∷ FinI m → Γ ⊢ ffs m k ∷ FinI (nsuc m)
  ⊢ffs dk = ⊢conₜ ⊢⌜Nat⌝ FinOK (nthᵗ-s nthᵗ-z) dn
              (⊢payσ ⊢⌜Nat⌝ ⊢FinD
                     (ok-σ ⊢⌜Nat⌝ (ok-ρ (⊢var here) (ok-σ (⊢Eq (⊢isuc (⊢var here)) (⊢wk dn)) ok-ι))) dm
                (⊢payρ ⊢⌜Nat⌝ ⊢FinD (ok-ρ dm (ok-σ (⊢Eq dn dr) ok-ι)) dk tail))

------------------------------------------------------------------------
-- 2. THE SYNTAX — telescopes over the index `n` (`var vz`).  No field
--    binds `n`, no telescope ends with an equation: the targets are
--    the fibres' own.
------------------------------------------------------------------------

varT lamT appT : {Γ : Cx} → Tel (Γ ∙)
varT = tσ (⌜IMu⌝ ⌜Nat⌝ FinD (var vz)) tι          -- a variable: `Fin n`
lamT = tρ (nsuc (var vz)) tι                      -- ★ the body, at `suc n`
appT = tρ (var vz) (tρ (var vz) tι)               -- function and argument, at `n`

TmTs : {Γ : Cx} → Tels (Γ ∙) 3
TmTs = varT ∷ᵗ lamT ∷ᵗ appT ∷ᵗ []ᵗ

TmD : {Γ : Cx} → RTm Γ
TmD = Dₗ ⌜ TmTs ⌝ₛ

Tm : {Γ : Cx} → RTm Γ → RTy Γ
Tm n = IMu ⌜Nat⌝ TmD n

varOK : {Γ : Ctx} → TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ varT
varOK = ok-σ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢var here)) ok-ι

lamOK : {Γ : Ctx} → TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ lamT
lamOK = ok-ρ (⊢isuc (⊢var here)) ok-ι

appOK : {Γ : Ctx} → TelOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ appT
appOK = ok-ρ (⊢var here) (ok-ρ (⊢var here) ok-ι)

TmOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ TmTs
TmOK = varOK ∷ᵒ lamOK ∷ᵒ appOK ∷ᵒ []ᵒ

⊢TmD : {Γ : Ctx} → Γ ⊢ TmD ∷ DescF ⌜Nat⌝
⊢TmD = ⊢Dₜ ⊢⌜Nat⌝ TmOK

------------------------------------------------------------------------
-- 3. THE TERM FORMERS.  The index is the TYPE's, not the term's.
------------------------------------------------------------------------

tvar : {Γ : Cx} → RTm Γ → RTm Γ
tvar k = conₗ zero (pair k unit)

tlam : {Γ : Cx} → RTm Γ → RTm Γ
tlam b = conₗ (suc zero) (pair b unit)

tapp : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
tapp f a = conₗ (suc (suc zero)) (pair f (pair a unit))

module _ {Γ : Ctx} {n : RTm ⌊ Γ ⌋} (dn : Γ ⊢ n ∷ El ⌜Nat⌝) where

  ⊢tvar : {k : RTm ⌊ Γ ⌋} → Γ ⊢ k ∷ FinI n → Γ ⊢ tvar k ∷ Tm n
  ⊢tvar dk =
    ⊢conₜ ⊢⌜Nat⌝ TmOK nthᵗ-z dn
      (⊢payσ ⊢⌜Nat⌝ ⊢TmD (ok-σ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD dn) ok-ι)
             (⊢conv dk (csymᵀ (credᵀ El-⌜IMu⌝))) (⊢payι ⊢⌜Nat⌝ ⊢TmD ⊢unit))

  -- ★★★ THE BINDING CONSTRUCTOR.  Its recursive field is at `suc n`.
  ⊢tlam : {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Tm (nsuc n) → Γ ⊢ tlam b ∷ Tm n
  ⊢tlam db =
    ⊢conₜ ⊢⌜Nat⌝ TmOK (nthᵗ-s nthᵗ-z) dn
      (⊢payρ ⊢⌜Nat⌝ ⊢TmD (ok-ρ (⊢isuc dn) ok-ι) db (⊢payι ⊢⌜Nat⌝ ⊢TmD ⊢unit))

  ⊢tapp : {f a : RTm ⌊ Γ ⌋} → Γ ⊢ f ∷ Tm n → Γ ⊢ a ∷ Tm n → Γ ⊢ tapp f a ∷ Tm n
  ⊢tapp df da =
    ⊢conₜ ⊢⌜Nat⌝ TmOK (nthᵗ-s (nthᵗ-s nthᵗ-z)) dn
      (⊢payρ ⊢⌜Nat⌝ ⊢TmD (ok-ρ dn (ok-ρ dn ok-ι)) df
        (⊢payρ ⊢⌜Nat⌝ ⊢TmD (ok-ρ dn ok-ι) da (⊢payι ⊢⌜Nat⌝ ⊢TmD ⊢unit)))

-- `fz : Fin 1` — the de Bruijn variable `0`, at depth 1.
fz : {Γ : Cx} → RTm Γ
fz = ffz nzero

-- `λ x. x` at depth 0.  ⚠ THE SCOPE CHECK IS IN THE TYPE: the bound
--   occurrence sits at depth `suc zero`, so its `Fin` must be `FinI 1`.
idTm : {Γ : Cx} → RTm Γ
idTm = tlam (tvar fz)

⊢idTm : {Γ : Ctx} → Γ ⊢ idTm ∷ Tm nzero
⊢idTm = ⊢tlam z (⊢tvar (⊢isuc z) (⊢ffz z))
  where z = toI ⊢nzero

------------------------------------------------------------------------
-- 4. `size : Tm n → Nat` — the library FOLD at (0, +, suc)
--    (`Lib/TelFold.sizeAlg`; `Examples/ScopedDepth` is (0, max, suc)).
--
-- ★ The method tuple is COMPUTED from the telescopes: `var` has no
--   recursive field (↦ 1), `lam` one (↦ suc of it), `app` two
--   (↦ suc of their sum).  `lam`'s IH is the fold run at `suc n` — the
--   SHIFTED index — and the fold never had to be told.
------------------------------------------------------------------------

msize : {Γ : Cx} → RTm Γ
msize = methₗ (foldMs sizeAlg TmTs)

size : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
size n t = ielim TmD n msize t

⊢msize : {Γ : Ctx} → Γ ⊢ msize ∷ MethTy ⌜Nat⌝ TmD Nat
⊢msize = ⊢foldE sizeAlg ⊢⌜Nat⌝ TmOK

⊢size : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ t ∷ Tm n → Γ ⊢ size n t ∷ Nat
⊢size dn dt = ⊢ielim ⊢⌜Nat⌝ ⊢TmD ty-Nat ⊢msize dn dt

------------------------------------------------------------------------
-- 5. ★★★ …AND IT RUNS UNDER THE BINDER.
------------------------------------------------------------------------

-- `size 1 (var 0) ⟶* 1` — a leaf: the fold's ι IS the answer.
size-var : {Γ : Cx} → size {Γ} (nsuc nzero) (tvar fz) ⟶* nsuc nzero
size-var = fold-ι sizeAlg {Ts = TmTs} nthᵗ-z

-- ★★★ `size 0 (λx. x) ⟶* 2`: ι, then the hypothesis — the fold called
--   again at `suc 0`, the SHIFTED index, which the fibre computed — projected out.
size-id : {Γ : Cx} → size {Γ} nzero idTm ⟶* nsuc (nsuc nzero)
size-id =
  ⟶*-trans (fold-ι sizeAlg {Ts = TmTs} (nthᵗ-s nthᵗ-z))
    (⟶*-nsuc
      (step (βfst _ _)
      (step (ξ-ielimᵗ (βfst _ _))
        size-var)))
