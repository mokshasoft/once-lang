------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ A SYNTAX AS A DESCRIPTION, inside the
-- kernel, LEVITATED: the λ-calculus scoped by CONTEXT DEPTH,
--
--        var : (n : Nat) → Fin n      → Tm n
--        lam : (n : Nat) → Tm (suc n) → Tm n        ← the binding shape
--        app : (n : Nat) → Tm n → Tm n → Tm n
--
-- written as a constructor list of TELESCOPES (`Lib/Tel`) over the index
-- code `⌜Nat⌝`, with `Fin` itself a family over the same code, and
-- `size` a FOLD (`Lib/TelFold`) — no per-constructor method, no
-- per-constructor typing, and a two-line computation.
--
-- ★ WHAT CHANGED FROM THE `IDesc` VERSION, and why it is the maths:
--   · every constructor BINDS its index `n` and ends at `dι n` — Fording.
--     A description is `Desc I`, not `I → Desc I`: the target index is a
--     FIELD EQUATION, so `lam`'s recursive field at `suc n` is just a
--     `tρ (nsuc n)` after the `tσ` that binds `n`;
--   · `var`'s field of FAMILY type is an ordinary `tσ` whose code is
--     `⌜IMu⌝ ⌜Nat⌝ FinD n` — there is no separate `icw-imu` well-formedness:
--     the code types by `⊢⌜IMu⌝`, like any other code;
--   · `dρ` binds nothing (A-math as GRAMMAR): after `lam`'s recursive
--     field, `n` is still `var vz`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Scoped where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-nsuc )
open import DirectedHoTT.Lib.Sugar using ( conₗ; methₗ; Dₗ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
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

-- the index equation every constructor ends with, at `refl`
⊢irefl : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El ⌜Nat⌝ → Γ ⊢ idrefl ⌜Nat⌝ t ∷ Id (El ⌜Nat⌝) t t
⊢irefl d = ⊢idrefl ⊢⌜Nat⌝ d

------------------------------------------------------------------------
-- 1. `Fin` — a family over the same index code.
--
--        fzero : (m : Nat) →          Fin (suc m)
--        fsuc  : (m : Nat) → Fin m →  Fin (suc m)
------------------------------------------------------------------------

fzeroT fsucT : {Γ : Cx} → Tel Γ
fzeroT = tσ ⌜Nat⌝ (tι (nsuc (var vz)))
fsucT  = tσ ⌜Nat⌝ (tρ (var vz) (tι (nsuc (var vz))))

FinTs : {Γ : Cx} → Tels Γ 2
FinTs = fzeroT ∷ᵗ fsucT ∷ᵗ []ᵗ

FinD : {Γ : Cx} → RTm Γ
FinD = Dₗ ⌜ FinTs ⌝ₛ

FinI : {Γ : Cx} → RTm Γ → RTy Γ
FinI n = IMu ⌜Nat⌝ FinD n

fzeroOK : {Γ : Ctx} → TelOK Γ ⌜Nat⌝ fzeroT
fzeroOK = ok-σ ⊢⌜Nat⌝ (ok-ι (⊢isuc (⊢var here)))

fsucOK : {Γ : Ctx} → TelOK Γ ⌜Nat⌝ fsucT
fsucOK = ok-σ ⊢⌜Nat⌝ (ok-ρ (⊢var here) (ok-ι (⊢isuc (⊢var here))))

FinOK : {Γ : Ctx} → AllOK Γ ⌜Nat⌝ FinTs
FinOK = fzeroOK ∷ᵒ fsucOK ∷ᵒ []ᵒ

⊢FinD : {Γ : Ctx} → Γ ⊢ FinD ∷ Desc ⌜Nat⌝
⊢FinD = ⊢Dₜ ⊢⌜Nat⌝ FinOK

ffz : {Γ : Cx} → RTm Γ → RTm Γ
ffz m = conₗ zero (pair m (idrefl ⌜Nat⌝ (nsuc m)))

ffs : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
ffs m k = conₗ (suc zero) (pair m (pair k (idrefl ⌜Nat⌝ (nsuc m))))

module _ {Γ : Ctx} where

  ⊢ffz : {m : RTm ⌊ Γ ⌋} → Γ ⊢ m ∷ El ⌜Nat⌝ → Γ ⊢ ffz m ∷ FinI (nsuc m)
  ⊢ffz dm = ⊢conₜ ⊢⌜Nat⌝ FinOK nthᵗ-z dn
              (⊢payσ ⊢⌜Nat⌝ ⊢FinD dn fzeroOK dm (⊢payι ⊢⌜Nat⌝ ⊢FinD dn (⊢irefl dn)))
    where dn = ⊢isuc dm

  ⊢ffs : {m k : RTm ⌊ Γ ⌋} → Γ ⊢ m ∷ El ⌜Nat⌝ → Γ ⊢ k ∷ FinI m → Γ ⊢ ffs m k ∷ FinI (nsuc m)
  ⊢ffs dm dk = ⊢conₜ ⊢⌜Nat⌝ FinOK (nthᵗ-s nthᵗ-z) dn
                 (⊢payσ ⊢⌜Nat⌝ ⊢FinD dn fsucOK dm
                   (⊢payρ ⊢⌜Nat⌝ ⊢FinD dn (ok-ρ dm (ok-ι dn)) dk
                     (⊢payι ⊢⌜Nat⌝ ⊢FinD dn (⊢irefl dn))))
    where dn = ⊢isuc dm

------------------------------------------------------------------------
-- 2. THE SYNTAX.
------------------------------------------------------------------------

varT lamT appT : {Γ : Cx} → Tel Γ
varT = tσ ⌜Nat⌝ (tσ (⌜IMu⌝ ⌜Nat⌝ FinD (var vz)) (tι (var (vs vz))))
lamT = tσ ⌜Nat⌝ (tρ (nsuc (var vz)) (tι (var vz)))
appT = tσ ⌜Nat⌝ (tρ (var vz) (tρ (var vz) (tι (var vz))))

TmTs : {Γ : Cx} → Tels Γ 3
TmTs = varT ∷ᵗ lamT ∷ᵗ appT ∷ᵗ []ᵗ

TmD : {Γ : Cx} → RTm Γ
TmD = Dₗ ⌜ TmTs ⌝ₛ

Tm : {Γ : Cx} → RTm Γ → RTy Γ
Tm n = IMu ⌜Nat⌝ TmD n

varOK : {Γ : Ctx} → TelOK Γ ⌜Nat⌝ varT
varOK = ok-σ ⊢⌜Nat⌝ (ok-σ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD (⊢var here)) (ok-ι (⊢var (there here))))

lamOK : {Γ : Ctx} → TelOK Γ ⌜Nat⌝ lamT
lamOK = ok-σ ⊢⌜Nat⌝ (ok-ρ (⊢isuc (⊢var here)) (ok-ι (⊢var here)))

appOK : {Γ : Ctx} → TelOK Γ ⌜Nat⌝ appT
appOK = ok-σ ⊢⌜Nat⌝ (ok-ρ (⊢var here) (ok-ρ (⊢var here) (ok-ι (⊢var here))))

TmOK : {Γ : Ctx} → AllOK Γ ⌜Nat⌝ TmTs
TmOK = varOK ∷ᵒ lamOK ∷ᵒ appOK ∷ᵒ []ᵒ

⊢TmD : {Γ : Ctx} → Γ ⊢ TmD ∷ Desc ⌜Nat⌝
⊢TmD = ⊢Dₜ ⊢⌜Nat⌝ TmOK

------------------------------------------------------------------------
-- 3. THE TERM FORMERS.  Each carries its index and ends at `refl`.
------------------------------------------------------------------------

tvar : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
tvar n k = conₗ zero (pair n (pair k (idrefl ⌜Nat⌝ n)))

tlam : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
tlam n b = conₗ (suc zero) (pair n (pair b (idrefl ⌜Nat⌝ n)))

tapp : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
tapp n f a = conₗ (suc (suc zero)) (pair n (pair f (pair a (idrefl ⌜Nat⌝ n))))

module _ {Γ : Ctx} {n : RTm ⌊ Γ ⌋} (dn : Γ ⊢ n ∷ El ⌜Nat⌝) where

  ⊢tvar : {k : RTm ⌊ Γ ⌋} → Γ ⊢ k ∷ FinI n → Γ ⊢ tvar n k ∷ Tm n
  ⊢tvar dk =
    ⊢conₜ ⊢⌜Nat⌝ TmOK nthᵗ-z dn
      (⊢payσ ⊢⌜Nat⌝ ⊢TmD dn varOK dn
        (⊢payσ ⊢⌜Nat⌝ ⊢TmD dn (ok-σ (⊢⌜IMu⌝ ⊢⌜Nat⌝ ⊢FinD dn) (ok-ι (⊢wk dn)))
               (⊢conv dk (csymᵀ (credᵀ El-⌜IMu⌝)))
               (⊢payι ⊢⌜Nat⌝ ⊢TmD dn
                 -- the index went under `k`'s binder and came back out
                 (⊢-cast (cong (λ x → Id (El ⌜Nat⌝) x n) (sym (wk-single n))) (⊢irefl dn)))))

  -- ★★★ THE BINDING CONSTRUCTOR: its recursive field is at `suc n`.
  ⊢tlam : {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Tm (nsuc n) → Γ ⊢ tlam n b ∷ Tm n
  ⊢tlam db =
    ⊢conₜ ⊢⌜Nat⌝ TmOK (nthᵗ-s nthᵗ-z) dn
      (⊢payσ ⊢⌜Nat⌝ ⊢TmD dn lamOK dn
        (⊢payρ ⊢⌜Nat⌝ ⊢TmD dn (ok-ρ (⊢isuc dn) (ok-ι dn)) db
          (⊢payι ⊢⌜Nat⌝ ⊢TmD dn (⊢irefl dn))))

  ⊢tapp : {f a : RTm ⌊ Γ ⌋} → Γ ⊢ f ∷ Tm n → Γ ⊢ a ∷ Tm n → Γ ⊢ tapp n f a ∷ Tm n
  ⊢tapp df da =
    ⊢conₜ ⊢⌜Nat⌝ TmOK (nthᵗ-s (nthᵗ-s nthᵗ-z)) dn
      (⊢payσ ⊢⌜Nat⌝ ⊢TmD dn appOK dn
        (⊢payρ ⊢⌜Nat⌝ ⊢TmD dn (ok-ρ dn (ok-ρ dn (ok-ι dn))) df
          (⊢payρ ⊢⌜Nat⌝ ⊢TmD dn (ok-ρ dn (ok-ι dn)) da
            (⊢payι ⊢⌜Nat⌝ ⊢TmD dn (⊢irefl dn)))))

-- `λ x. x` at depth 0.  ⚠ THE SCOPE CHECK IS IN THE TYPE: the bound
--   occurrence sits at depth 1, so its `Fin` must be `FinI 1`.
idTm : {Γ : Cx} → RTm Γ
idTm = tlam nzero (tvar (nsuc nzero) (ffz nzero))

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
size-var : {Γ : Cx} → size {Γ} (nsuc nzero) (tvar (nsuc nzero) (ffz nzero)) ⟶* nsuc nzero
size-var = fold-ι sizeAlg nthᵗ-z

-- ★★★ `size 0 (λx. x) ⟶* 2`: ι, then the hypothesis — the fold called
--   again at `suc (fst p)`, the SHIFTED index — projected out.
size-id : {Γ : Cx} → size {Γ} nzero idTm ⟶* nsuc (nsuc nzero)
size-id =
  ⟶*-trans (fold-ι sizeAlg (nthᵗ-s nthᵗ-z))
    (⟶*-nsuc
      (step (βfst _ _)
      (step (ξ-ielimⁱ (ξ-nsuc (βfst _ _)))
      (step (ξ-ielimᵗ (ξ-fst (βsnd _ _)))
      (step (ξ-ielimᵗ (βfst _ _))
        size-var)))))
