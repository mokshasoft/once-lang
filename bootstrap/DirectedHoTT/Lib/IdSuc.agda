------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `nsuc` IS INJECTIVE ON `IdN`, OBJECT-LEVEL.
--
--     injSucN : IdN (nsuc a) (nsuc b) → IdN a b
--
-- ★ WHY THE JUDGEMENT LAYER NEEDS IT.  `Examples/Scoped`'s `Fin` rows
--   are FORDED: `fzero`/`fsuc` both constrain the ambient index by
--   `⟨j⟩ ≡ nsuc m`.  So eliminating a `Fin (nsuc i)` hands each method a
--   ford at ITS OWN generic `j`, and the method has no way to learn
--   `m ≡ i` — which is exactly what `extS`'s `fsuc` case needs in order
--   to apply a `σ : Fin i → Tm n` to the field it was given.
--
-- ⚠⚠ AND A CONSTANT MOTIVE CANNOT DODGE IT.  The connection `j = nsuc i`
--   exists only where the eliminator is APPLIED; inside a method `j` is
--   a bound variable.  That is the whole reason this lemma is needed and
--   not merely convenient.
--
-- ★ IT IS NOT AN AXIOM — it is a CONGRUENCE plus a REDUCTION.
--   `predTm` congruence along the equation gives
--   `IdN (predTm (nsuc a)) (predTm (nsuc b))`, and `pred-suc` reduces
--   both endpoints, which is a CONVERSION of the `Id` type
--   (`⟶ᵀ*-Idˡ`/`⟶ᵀ*-Idʳ`) rather than any new principle.
--
-- ⚠ SO IT COSTS A `natrec` PER USE.  `predTm m = natrec nzero (var (vs
--   vz)) m` — cheap, but not free, and `extS` uses it once per `fsuc`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IdSuc where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; var; vz; vs; nsuc; jsub; El; Id; ⌜Nat⌝; ⌜Id⌝; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢conv; ⊢var; here; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢jsub
        ; csymᵀ; ctrnᵀ; wk-single; ⊢nsuc )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Wk using ( w )
open import DirectedHoTT.Lib.Strong using ( natAsEl; elAsNat )
open import DirectedHoTT.Lib.Monus using ( predTm; ⊢pred; pred-suc )
open import DirectedHoTT.Lib.ArithComm using ( IdN; reflN; ⊢reflN; elIdN )

------------------------------------------------------------------------
-- 1. `predTm` RESPECTS `IdN` — the same `jsub` call as `symN`, at the
--    motive `λ z. IdN (predTm a) (predTm z)`.
------------------------------------------------------------------------

predN : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
predN a p = jsub (⌜Id⌝ ⌜Nat⌝ (w (predTm a)) (predTm (var vz))) p
                 (reflN (predTm a))

⊢predN : {Γ : Ctx} {a b p : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ p ∷ IdN a b →
         Γ ⊢ predN a p ∷ IdN (predTm a) (predTm b)
⊢predN {a = a} {b = b} da db dp =
  ⊢conv (⊢-cast (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ z (predTm b)))
                      (wk-single {v = b} (predTm a)))
                (⊢jsub dd (natAsEl da) (natAsEl db) dp de))
        (elIdN (predTm a) (predTm b))
  where
    dd = ⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢wk (⊢pred da))) (natAsEl (⊢pred (elAsNat (⊢var here))))
    de = ⊢-cast (sym (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ z (predTm a)))
                           (wk-single {v = a} (predTm a))))
                (⊢conv (⊢reflN (⊢pred da)) (csymᵀ (elIdN (predTm a) (predTm a))))

------------------------------------------------------------------------
-- 2. ★★★ AND THEREFORE `nsuc` IS INJECTIVE.
--
-- ⚠ THE TERM IS THE SAME `predN`; only its TYPE moves, by reducing both
--   endpoints.  So this is a CONVERSION, not a transport — the term
--   carries no coercion at runtime.
--
-- ★ AND THE CONVERSION IS LOAD-BEARING, CHECKED RATHER THAN ASSUMED:
--   deleting it gives `rc=42`, restoring it `rc=0`.  ⚠ Compiling WITH a
--   cast proves nothing on its own (`control-a-cast-with-refl`: an
--   unnecessary cast compiles fine) — the evidence has to be that
--   removing it FAILS.
------------------------------------------------------------------------

injSucN : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
injSucN a p = predN (nsuc a) p

⊢injSucN : {Γ : Ctx} {a b p : RTm ⌊ Γ ⌋} →
           Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat →
           Γ ⊢ p ∷ IdN (nsuc a) (nsuc b) →
           Γ ⊢ injSucN a p ∷ IdN a b
⊢injSucN {a = a} {b = b} da db dp =
  ⊢conv (⊢predN (⊢nsuc da) (⊢nsuc db) dp)
        (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ (pred-suc a)))
               (red→≅ᵀ (⟶ᵀ*-Idʳ (pred-suc b))))

------------------------------------------------------------------------
-- 3. ★ THE SHAPE THE FORD ACTUALLY COMES IN.
--
-- A Forded row constrains the AMBIENT index: `⟨j⟩ ≡ nsuc m`, with `j` a
-- bound variable and `m` a field.  Neither side is a `nsuc` of anything
-- known, so `injSucN` does not apply — what is wanted is
-- `predTm ⟨j⟩ ≡ m`, which is `predN` with only the RIGHT endpoint
-- reduced.
--
-- ⚠ THIS IS THE FORM `Fin`'s AND THE KNOT'S `Var` ROWS BOTH TAKE.
--   `Examples/Scoped`'s `fzeroC`/`fsucC` ford `⟨j⟩ ≡ nsuc m`; the knot's
--   `cVar-vz`/`cVar-vs` ford `snd ⟨i⟩ ≡ nsuc m`.  Same lemma serves both.
------------------------------------------------------------------------

⊢fordPredN : {Γ : Ctx} {j m p : RTm ⌊ Γ ⌋} →
             Γ ⊢ j ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ p ∷ IdN j (nsuc m) →
             Γ ⊢ predN j p ∷ IdN (predTm j) m
⊢fordPredN {m = m} dj dm dp =
  ⊢conv (⊢predN dj (⊢nsuc dm) dp) (red→≅ᵀ (⟶ᵀ*-Idʳ (pred-suc m)))
