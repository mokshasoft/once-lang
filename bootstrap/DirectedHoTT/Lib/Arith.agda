------------------------------------------------------------------------
-- OCP-0009 — ARITHMETIC FOR gcd: `+` IS MONOTONE IN ITS SECOND ARGUMENT.
--
-- `NbEPDirDBExamplesPairLib`'s header deferred gcd because "gcd's descent needs
-- monotonicity of `+` under `≤` and its strict form — a real arithmetic
-- development".  This is the tractable half of that development, and the
-- point of the file is to establish exactly WHERE the line falls.
--
-- ★★ THE ASYMMETRY, and it decides everything downstream.
--
--     plusTm m n = natrec n (nsuc (var vz)) m        -- recurses on `m`
--
--   so `plusTm c x` is STUCK on `c` and TRANSPARENT in `x`.  Therefore:
--
--     * monotone in the SECOND (base) argument — `x < y ⇒ c + x < c + y`
--       — is a five-line `natrec` on `c`, proved below.  The step case is
--       LITERALLY THE IH, because `Hom Nat (nsuc u) (nsuc v)` REDUCES to
--       `Hom Nat u v` (`Hom-Nat-ss`).  Same shape as `⊢le-refl`.
--
--     * monotone in the FIRST (recursed) argument — `x < y ⇒ x + c < y + c`
--       — ⛔ IS NOT AVAILABLE THIS WAY.  For open `x`, `y` both sides are
--       stuck, and `<` is a COMPUTING `Hom Nat` rather than an inductive
--       family, so there is nothing to induct on.  It needs commutativity
--       of `+`, which needs `Id`/`J` and the two standard lemmas.
--
-- ⚠ WHY THAT MATTERS FOR gcd.  Subtractive Euclid changes the FIRST
--   component in one branch and the SECOND in the other:
--
--       gcd (a , b) = gcd (a ∸ b , b)   if a > b
--       gcd (a , b) = gcd (a , b ∸ a)   if b > a
--
--   so whichever way round the measure `a + b` is written, ONE branch
--   lands in the base position (cheap, this file) and the other in the
--   recursed position (needs commutativity).  Swapping the recursive call
--   to keep the changing component in the base does not help: `gcd` is
--   symmetric, but swapping changes BOTH components at once.
--
--   ⇒ gcd through `⊢amrecΠ` is blocked on `plus`-commutativity, and that
--     is the next concrete task — NOT on anything about the combinator.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Arith where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong₂ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; Hom; Nat
        ; RTm; var; nzero; nsuc; natrec
        ; renTy; renTm; subTy; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ty-Nat; ty-Hom
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; Hom-Nat-ss
        ; ξ-nsuc; ξ-Homˡ; ξ-Homʳ; natrec-zero; natrec-suc; wk-single )
open import DirectedHoTT.Metatheory.RedCong using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Wk using ( w; nrs-w )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )

------------------------------------------------------------------------
-- ⚠ THE MOTIVE MUST BE BOUND-EXPLICIT, exactly as `LibAmrec`'s `aAuxB`.
--   Writing it inline leaves a `subTm (single n) (w x)` residue that is
--   `wk-single` — PROPOSITIONAL, not definitional — at all three of the
--   natrec's boundaries.  Naming the body and stating `mot-at`/`mot-s`
--   pays it once each instead.
------------------------------------------------------------------------

plusMonoB : {Γ : Cx} (x y c : RTm Γ) → RTy Γ
plusMonoB x y c = Hom Nat (nsuc (plusTm c x)) (plusTm c y)

plusMonoMot : {Γ : Cx} (x y : RTm Γ) → RTy (Γ ∙)
plusMonoMot x y = plusMonoB (w x) (w y) (var vz)

⊢plusMonoMot : {Γ : Ctx} {x y : RTm ⌊ Γ ⌋} →
               Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat → (Γ ▹ Nat) ⊢ty plusMonoMot x y
⊢plusMonoMot dx dy =
  ty-Hom ty-Nat (⊢nsuc (⊢plus (⊢var here) (⊢wk dx)))
                (⊢plus (⊢var here) (⊢wk dy))

mot-at : {Γ : Cx} (x y n : RTm Γ) →
         subTy (single n) (plusMonoMot x y) ≡ plusMonoB x y n
mot-at x y n =
  cong₂ (λ a b → Hom Nat (nsuc (plusTm n a)) (plusTm n b))
        (wk-single {v = n} x) (wk-single {v = n} y)

mot-s : {Γ : Cx} (x y : RTm Γ) →
        subTy nrs (plusMonoMot x y)
      ≡ plusMonoB (w (w x)) (w (w y)) (nsuc (var (vs vz)))
mot-s x y =
  cong₂ (λ a b → Hom Nat (nsuc (plusTm (nsuc (var (vs vz))) a))
                         (plusTm (nsuc (var (vs vz))) b))
        (nrs-w x) (nrs-w y)

------------------------------------------------------------------------
-- ★★ THE LEMMA.  `c + x < c + y` from `x < y`, by `natrec` on `c`.
--
--   c = 0      both `plusTm nzero _` peel by `natrec-zero`, leaving the
--              hypothesis itself;
--   c = suc c' both peel by `natrec-suc` to `nsuc (…)`, and then
--              `Hom Nat (nsuc u) (nsuc v) ⟶ᵀ Hom Nat u v` leaves exactly
--              the IH.  ★ The step is `var vz` — nothing is built.
--
-- ⚠ THE WITNESS IS THE ORDER PROOF ITSELF, threaded: `natrec p (var vz) c`.
--   `+`'s monotonicity carries no computational content here, because the
--   ORDER is what reduces.
------------------------------------------------------------------------

plusMonoTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
plusMonoTm p c = natrec p (var vz) c

⊢plus-mono : {Γ : Ctx} {x y c p : RTm ⌊ Γ ⌋} →
             Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat → Γ ⊢ c ∷ Nat →
             Γ ⊢ p ∷ Hom Nat (nsuc x) y →                    -- x < y
             Γ ⊢ plusMonoTm p c ∷ plusMonoB x y c            -- c+x < c+y
⊢plus-mono {x = x} {y = y} {c = c} dx dy dc dp =
  ⊢-cast (mot-at x y c) (⊢natrec (⊢plusMonoMot dx dy) zB sB dc)
  where
    zB = ⊢-cast (sym (mot-at x y nzero))
           (⊢conv dp
             (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Homˡ (ξ-nsuc (natrec-zero _ _)))
                              (stepᵀ (ξ-Homʳ (natrec-zero _ _)) doneᵀ)))))
    sB = ⊢-cast (sym (mot-s x y))
           (⊢conv (⊢var here)
             (csymᵀ (ctrnᵀ (red→≅ᵀ (stepᵀ (ξ-Homˡ (ξ-nsuc (natrec-suc _ _ _)))
                                     (stepᵀ (ξ-Homʳ (natrec-suc _ _ _)) doneᵀ)))
                           (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ)))))
