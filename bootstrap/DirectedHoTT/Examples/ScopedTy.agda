------------------------------------------------------------------------
-- PROBE — `Examples/Scoped.agda`'s TWIN, indexed by CONTEXT AND TYPE.
--
--   Scoped (baseline):  Tm n            -- index: a DEPTH (one ℕ)
--   here   (probe):     Tm (Γ , A)      -- index: a CONTEXT and a TYPE
--
--     lam : Tm (Γ , A) B → Tm Γ (A ⇒ B)
--     app : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
--
-- ★★ D074 (fibred descriptions).  Each constructor telescope sees the
--   index `(Γ , T)` it lands at:
--
--     `app`  target IS the ambient              ⇒ NO ford, one σ for A
--     `lam`  target's TYPE is `A ⇒ B` (computed) ⇒ ford the TYPE component
--            only; the CONTEXT rides (`fst i`), exactly `PairIx`'s trick
--
--   ⇒ `lam` is σ A, σ B, ρ (A ∷ fst i , B), and ONE `⌜Id⌝` on `snd i`.
--   The one-telescope form needed a σ for Γ as well and forded the whole
--   pair (five fields, 2026-09-23 measurement); the fibre removes the
--   context field and half the equation.
--
-- ★ The two auxiliary datatypes are ordinary families over `⌜Unit⌝`
--   (D072: one datatype former).  §6 is `ScopedTySz`, folded in: the
--   library `size` fold over a STRUCTURAL pair index.
--
-- ⚠ No constructor has a base case (no `var`), so the family is EMPTY:
--   this file is a probe of the INDEX, and inhabits nothing closed.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.ScopedTy where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin; base )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; red→≅ᵀ; ⟶ᵀ*-IMu )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; exts-wk-tm )
open import DirectedHoTT.Lib.Sugar using ( conₗ; methₗ; Dₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.TelFold using ( sizeAlg; foldMs; ⊢foldE )

------------------------------------------------------------------------
-- 1. THE TWO AUXILIARY DATATYPES, as families over `⌜Unit⌝`.
------------------------------------------------------------------------

⊢u : {Γ : Ctx} → Γ ⊢ unit ∷ El ⌜Unit⌝
⊢u = ⊢conv ⊢unit (csymᵀ (credᵀ El-⌜Unit⌝))

fromEl : {Γ : Ctx} {I D i t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El (⌜IMu⌝ I D i) → Γ ⊢ t ∷ IMu I D i
fromEl d = ⊢conv d (credᵀ El-⌜IMu⌝)

toEl : {Γ : Ctx} {I D i t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ IMu I D i → Γ ⊢ t ∷ El (⌜IMu⌝ I D i)
toEl d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

-- Ty ::= base | Ty ⇒ Ty
TyTs : {Γ : Cx} → Tels (Γ ∙) 2
TyTs = tι ∷ᵗ tρ unit (tρ unit tι) ∷ᵗ []ᵗ

TyD : {Γ : Cx} → RTm Γ
TyD = Dₗ ⌜ TyTs ⌝ₛ

⌜Ty⌝ : {Γ : Cx} → RTm Γ
⌜Ty⌝ = ⌜IMu⌝ ⌜Unit⌝ TyD unit

TyOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Unit⌝) ⌜Unit⌝ TyTs
TyOK = ok-ι ∷ᵒ ok-ρ ⊢u (ok-ρ ⊢u ok-ι) ∷ᵒ []ᵒ

⊢TyD : {Γ : Ctx} → Γ ⊢ TyD ∷ DescF ⌜Unit⌝
⊢TyD = ⊢Dₜ ⊢⌜Unit⌝ TyOK

⊢⌜Ty⌝ : {Γ : Ctx} → Γ ⊢ ⌜Ty⌝ ∷ U
⊢⌜Ty⌝ = ⊢⌜IMu⌝ ⊢⌜Unit⌝ ⊢TyD ⊢u

base : {Γ : Cx} → RTm Γ
base = conₗ zero unit

arrow : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
arrow a b = conₗ (suc zero) (pair a (pair b unit))

⊢base : {Γ : Ctx} → Γ ⊢ base ∷ El ⌜Ty⌝
⊢base = toEl (⊢conₜ ⊢⌜Unit⌝ TyOK nthᵗ-z ⊢u (⊢payι ⊢⌜Unit⌝ ⊢TyD ⊢unit))

⊢arrow : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ El ⌜Ty⌝ → Γ ⊢ b ∷ El ⌜Ty⌝ → Γ ⊢ arrow a b ∷ El ⌜Ty⌝
⊢arrow da db =
  toEl (⊢conₜ ⊢⌜Unit⌝ TyOK (nthᵗ-s nthᵗ-z) ⊢u
         (⊢payρ ⊢⌜Unit⌝ ⊢TyD (ok-ρ ⊢u (ok-ρ ⊢u ok-ι)) (fromEl da)
           (⊢payρ ⊢⌜Unit⌝ ⊢TyD (ok-ρ ⊢u ok-ι) (fromEl db) (⊢payι ⊢⌜Unit⌝ ⊢TyD ⊢unit))))

-- Ctx ::= nil | Ty ∷ Ctx
CxTs : {Γ : Cx} → Tels (Γ ∙) 2
CxTs = tι ∷ᵗ tσ ⌜Ty⌝ (tρ unit tι) ∷ᵗ []ᵗ

CxD : {Γ : Cx} → RTm Γ
CxD = Dₗ ⌜ CxTs ⌝ₛ

⌜Cxt⌝ : {Γ : Cx} → RTm Γ
⌜Cxt⌝ = ⌜IMu⌝ ⌜Unit⌝ CxD unit

CxOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜Unit⌝) ⌜Unit⌝ CxTs
CxOK = ok-ι ∷ᵒ ok-σ ⊢⌜Ty⌝ (ok-ρ ⊢u ok-ι) ∷ᵒ []ᵒ

⊢CxD : {Γ : Ctx} → Γ ⊢ CxD ∷ DescF ⌜Unit⌝
⊢CxD = ⊢Dₜ ⊢⌜Unit⌝ CxOK

⊢⌜Cxt⌝ : {Γ : Ctx} → Γ ⊢ ⌜Cxt⌝ ∷ U
⊢⌜Cxt⌝ = ⊢⌜IMu⌝ ⊢⌜Unit⌝ ⊢CxD ⊢u

nilC : {Γ : Cx} → RTm Γ
nilC = conₗ zero unit

consC : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
consC a g = conₗ (suc zero) (pair a (pair g unit))

⊢nilC : {Γ : Ctx} → Γ ⊢ nilC ∷ El ⌜Cxt⌝
⊢nilC = toEl (⊢conₜ ⊢⌜Unit⌝ CxOK nthᵗ-z ⊢u (⊢payι ⊢⌜Unit⌝ ⊢CxD ⊢unit))

⊢consC : {Γ : Ctx} {a g : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ El ⌜Ty⌝ → Γ ⊢ g ∷ El ⌜Cxt⌝ → Γ ⊢ consC a g ∷ El ⌜Cxt⌝
⊢consC da dg =
  toEl (⊢conₜ ⊢⌜Unit⌝ CxOK (nthᵗ-s nthᵗ-z) ⊢u
         (⊢payσ ⊢⌜Unit⌝ ⊢CxD (ok-σ ⊢⌜Ty⌝ (ok-ρ ⊢u ok-ι)) da
           (⊢payρ ⊢⌜Unit⌝ ⊢CxD (ok-ρ ⊢u ok-ι) (fromEl dg) (⊢payι ⊢⌜Unit⌝ ⊢CxD ⊢unit))))

------------------------------------------------------------------------
-- 2. THE INDEX — a pair of them, as a CODE.
------------------------------------------------------------------------

⌜I⌝ : {Γ : Cx} → RTm Γ
⌜I⌝ = ⌜Σ⌝ ⌜Cxt⌝ ⌜Ty⌝

⊢⌜I⌝ : {Γ : Ctx} → Γ ⊢ ⌜I⌝ ∷ U
⊢⌜I⌝ = ⊢⌜Σ⌝ ⊢⌜Cxt⌝ ⊢⌜Ty⌝

elΣI : {Γ : Cx} → El (⌜I⌝ {Γ}) ≅ᵀ Σ' (El ⌜Cxt⌝) (El ⌜Ty⌝)
elΣI = credᵀ (El-⌜Σ⌝ _ _)

⊢ixP : {Γ : Ctx} {g a : RTm ⌊ Γ ⌋} →
       Γ ⊢ g ∷ El ⌜Cxt⌝ → Γ ⊢ a ∷ El ⌜Ty⌝ → Γ ⊢ pair g a ∷ El ⌜I⌝
⊢ixP dg da = ⊢conv (⊢pair (ty-El ⊢⌜Ty⌝) dg da) (csymᵀ elΣI)

⊢fstI : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El ⌜I⌝ → Γ ⊢ fst i ∷ El ⌜Cxt⌝
⊢fstI di = ⊢fst (⊢conv di elΣI)

⊢sndI : {Γ : Ctx} {i : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El ⌜I⌝ → Γ ⊢ snd i ∷ El ⌜Ty⌝
⊢sndI di = ⊢snd (⊢conv di elΣI)

------------------------------------------------------------------------
-- 3. ★★★ THE SYNTAX — telescopes over the index `i`, stated through
--    two tails GENERIC IN THE INDEX TERM (`appR`, `lamR`), so each
--    constructor below instantiates them at the index the pending
--    substitution leaves, with one `wk-single`-style cast of the INDEX
--    derivation and nothing else.
------------------------------------------------------------------------

-- app, after `A`: the function at `(fst i , A ⇒ snd i)`, the argument at `(fst i , A)`
appR : {Δ : Cx} → RTm Δ → RTm Δ → Tel Δ
appR I A = tρ (pair (fst I) (arrow A (snd I))) (tρ (pair (fst I) A) tι)

-- lam, after `A` and `B`: the body at `(A ∷ fst i , B)`, then the ford on the TYPE
lamR : {Δ : Cx} → RTm Δ → RTm Δ → RTm Δ → Tel Δ
lamR I A B = tρ (pair (consC A (fst I)) B) (tσ (⌜Id⌝ ⌜Ty⌝ (snd I) (arrow A B)) tι)

appT lamT : {Γ : Cx} → Tel (Γ ∙)
appT = tσ ⌜Ty⌝ (appR (var (vs vz)) (var vz))
lamT = tσ ⌜Ty⌝ (tσ ⌜Ty⌝ (lamR (var (vs (vs vz))) (var (vs vz)) (var vz)))

TmTs : {Γ : Cx} → Tels (Γ ∙) 2
TmTs = appT ∷ᵗ lamT ∷ᵗ []ᵗ

TmD : {Γ : Cx} → RTm Γ
TmD = Dₗ ⌜ TmTs ⌝ₛ

Tm : {Γ : Cx} → RTm Γ → RTy Γ
Tm i = IMu ⌜I⌝ TmD i

------------------------------------------------------------------------
-- 4. WELL-FORMEDNESS — of the tails at any index, then of the syntax.
------------------------------------------------------------------------

module _ {Γ : Ctx} {I A : RTm ⌊ Γ ⌋} (dI : Γ ⊢ I ∷ El ⌜I⌝) (dA : Γ ⊢ A ∷ El ⌜Ty⌝) where
  appR₂OK : TelOK Γ ⌜I⌝ (tρ (pair (fst I) A) tι)
  appR₂OK = ok-ρ (⊢ixP (⊢fstI dI) dA) ok-ι

  appROK : TelOK Γ ⌜I⌝ (appR I A)
  appROK = ok-ρ (⊢ixP (⊢fstI dI) (⊢arrow dA (⊢sndI dI))) appR₂OK

  ⊢lamEq : {B : RTm ⌊ Γ ⌋} → Γ ⊢ B ∷ El ⌜Ty⌝ → Γ ⊢ ⌜Id⌝ ⌜Ty⌝ (snd I) (arrow A B) ∷ U
  ⊢lamEq dB = ⊢⌜Id⌝ ⊢⌜Ty⌝ (⊢sndI dI) (⊢arrow dA dB)

  lamROK : {B : RTm ⌊ Γ ⌋} → Γ ⊢ B ∷ El ⌜Ty⌝ → TelOK Γ ⌜I⌝ (lamR I A B)
  lamROK dB = ok-ρ (⊢ixP (⊢consC dA (⊢fstI dI)) dB) (ok-σ (⊢lamEq dB) ok-ι)

appOK : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} → Γ ⊢ I ∷ El ⌜I⌝ → TelOK Γ ⌜I⌝ (tσ ⌜Ty⌝ (appR (renTm vs I) (var vz)))
appOK dI = ok-σ ⊢⌜Ty⌝ (appROK (⊢wk dI) (⊢var here))

lamOK : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} → Γ ⊢ I ∷ El ⌜I⌝ →
        TelOK Γ ⌜I⌝ (tσ ⌜Ty⌝ (tσ ⌜Ty⌝ (lamR (renTm vs (renTm vs I)) (var (vs vz)) (var vz))))
lamOK dI = ok-σ ⊢⌜Ty⌝ (ok-σ ⊢⌜Ty⌝ (lamROK (⊢wk (⊢wk dI)) (⊢var (there here)) (⊢var here)))

TmOK : {Γ : Ctx} → AllOK (Γ ▹ El ⌜I⌝) ⌜I⌝ TmTs
TmOK = appOK (⊢var here) ∷ᵒ lamOK (⊢var here) ∷ᵒ []ᵒ

⊢TmD : {Γ : Ctx} → Γ ⊢ TmD ∷ DescF ⌜I⌝
⊢TmD = ⊢Dₜ ⊢⌜I⌝ TmOK

------------------------------------------------------------------------
-- 5. THE TERM FORMERS, at EVERY index.
--
-- ⚠ The one cost the fibre does not remove: the pending substitution
--   leaves the index under the σ-binders as `subTm (single a) (renTm vs i)`,
--   which is `i` only PROPOSITIONALLY (`wk-single`).  The tails being
--   generic in the index term, that is one `subst` of the INDEX
--   derivation per constructor, and the rest is `βfst`/`βsnd`.
------------------------------------------------------------------------

tapp : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
tapp a f x = conₗ zero (pair a (pair f (pair x unit)))

tlam : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
tlam a b t = conₗ (suc zero) (pair a (pair b (pair t (pair (idrefl ⌜Ty⌝ (arrow a b)) unit))))

-- convert along a reduction OF THE INDEX
ixConv : {Γ : Ctx} {t i i' : RTm ⌊ Γ ⌋} → i ⟶* i' → Γ ⊢ t ∷ Tm i' → Γ ⊢ t ∷ Tm i
ixConv r d = ⊢conv d (csymᵀ (red→≅ᵀ (⟶ᵀ*-IMu r)))

module _ {Γ : Ctx} {g : RTm ⌊ Γ ⌋} (dg : Γ ⊢ g ∷ El ⌜Cxt⌝) where

  ⊢tapp : {a b f x : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Ty⌝ → Γ ⊢ b ∷ El ⌜Ty⌝ →
          Γ ⊢ f ∷ Tm (pair g (arrow a b)) → Γ ⊢ x ∷ Tm (pair g a) →
          Γ ⊢ tapp a f x ∷ Tm (pair g b)
  ⊢tapp {a} {b} {f} {x} da db df dx =
    ⊢conₜ ⊢⌜I⌝ TmOK nthᵗ-z di
      (⊢payσ ⊢⌜I⌝ ⊢TmD (appOK di) da
        (subst (λ J → Γ ⊢ pair f (pair x unit) ∷ El (dpay ⌜I⌝ TmD ⌜ appR J a ⌝ᵗ)) (sym (wk-single {v = a} i))
          (⊢payρ ⊢⌜I⌝ ⊢TmD (appROK di da)
                 (ixConv (⟶*-trans (⟶*-pairˡ (step (βfst g b) done))
                                   (⟶*-pairʳ (⟶*-con (⟶*-pairʳ (⟶*-pairʳ
                                     (⟶*-pairˡ (step (βsnd g b) done))))))) df)
            (⊢payρ ⊢⌜I⌝ ⊢TmD (appR₂OK di da)
                   (ixConv (⟶*-pairˡ (step (βfst g b) done)) dx)
                   (⊢payι ⊢⌜I⌝ ⊢TmD ⊢unit)))))
    where i = pair g b
          di = ⊢ixP dg db

  -- ★★★ THE BINDING CONSTRUCTOR: the body at `(A ∷ Γ , B)`, the type forded.
  ⊢tlam : {a b t : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ El ⌜Ty⌝ → Γ ⊢ b ∷ El ⌜Ty⌝ →
          Γ ⊢ t ∷ Tm (pair (consC a g) b) → Γ ⊢ tlam a b t ∷ Tm (pair g (arrow a b))
  ⊢tlam {a} {b} {t} da db dt =
    ⊢conₜ ⊢⌜I⌝ TmOK (nthᵗ-s nthᵗ-z) di
      (⊢payσ ⊢⌜I⌝ ⊢TmD (lamOK di) da
        (⊢payσ ⊢⌜I⌝ ⊢TmD (ok-σ ⊢⌜Ty⌝ (lamROK dI₁ (⊢wk da) (⊢var here))) db
          (subst (λ A' → Γ ⊢ lamP ∷ El (dpay ⌜I⌝ TmD ⌜ lamR (subTm (single b) I₁) A' b ⌝ᵗ))
                 (sym (wk-single {v = b} a))
          (subst (λ J → Γ ⊢ lamP ∷ El (dpay ⌜I⌝ TmD ⌜ lamR J a b ⌝ᵗ)) e₂
            (⊢payρ ⊢⌜I⌝ ⊢TmD (lamROK di da db)
                   (ixConv (⟶*-pairˡ (⟶*-con (⟶*-pairʳ (⟶*-pairʳ
                             (⟶*-pairˡ (step (βfst g (arrow a b)) done)))))) dt)
              (⊢payσ ⊢⌜I⌝ ⊢TmD (ok-σ (⊢lamEq di da db) ok-ι)
                     (⊢conv (⊢idrefl ⊢⌜Ty⌝ (⊢arrow da db))
                            (csymᵀ (ctrnᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ (βsnd g (arrow a b)))))
                                          (credᵀ (El-⌜Id⌝ ⌜Ty⌝ _ _)))))
                     (⊢payι ⊢⌜I⌝ ⊢TmD ⊢unit)))))))
    where
      i = pair g (arrow a b)
      lamP = pair t (pair (idrefl ⌜Ty⌝ (arrow a b)) unit)
      di = ⊢ixP dg (⊢arrow da db)
      I₁ = subTm (extS (single a)) (renTm vs (renTm vs i))
      e₁ : renTm vs i ≡ I₁
      e₁ = sym (trans (exts-wk-tm (single a) (renTm vs i)) (cong (renTm vs) (wk-single {v = a} i)))
      dI₁ : (Γ ▹ El ⌜Ty⌝) ⊢ I₁ ∷ El ⌜I⌝
      dI₁ = subst (λ J → (Γ ▹ El ⌜Ty⌝) ⊢ J ∷ El ⌜I⌝) e₁ (⊢wk di)
      e₂ : i ≡ subTm (single b) I₁
      e₂ = trans (sym (wk-single {v = b} i)) (cong (subTm (single b)) e₁)

------------------------------------------------------------------------
-- 6. THE FOLD, over a STRUCTURAL index (was `ScopedTySz`).
--
-- ★ `KNOT-LESSONS` §2.1: the Knot's fold pain was index BOOKKEEPING —
--   a binder is `+1` and the fold must count.  Here the index is a
--   context and a type, and the library fold is ONE line: the method
--   tuple is computed from the telescopes and never looks at the index.
------------------------------------------------------------------------

msize : {Γ : Cx} → RTm Γ
msize = methₗ (foldMs sizeAlg TmTs)

size : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
size i t = ielim TmD i msize t

⊢size : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} → Γ ⊢ i ∷ El ⌜I⌝ → Γ ⊢ t ∷ Tm i → Γ ⊢ size i t ∷ Nat
⊢size di dt = ⊢ielim ⊢⌜I⌝ ⊢TmD ty-Nat (⊢foldE sizeAlg ⊢⌜I⌝ TmOK) di dt
