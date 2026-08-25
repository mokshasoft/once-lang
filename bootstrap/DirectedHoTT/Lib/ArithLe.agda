------------------------------------------------------------------------
-- OCP-0009 — `+` IS MONOTONE IN BOTH ARGUMENTS, NON-STRICTLY.
--
-- ★ WHY THIS EXISTS AND WHY IT IS NOT `LibArith`'s LEMMA.  `⊢plus-mono`
--   and `⊢plus-mono-l` are STRICT: they take `x < y` to `c+x < c+y` resp.
--   `x+c < y+c`, because that is the shape gcd's DESCENT needs — the
--   recursive call's measure must strictly drop.  gcd's `StepExt` needs
--   the other shape.  Its two recursive leaves get their certificate at
--   `suc k' + suc n'`, the measure written in the SPLIT variables, and
--   have to move it to `fst a + snd a`, the measure of the original
--   carrier, along `suc k' ≤ fst a` and `suc n' ≤ snd a`.  Both ends are
--   `≤`, so both monotonicities have to be `≤`, and neither strict lemma
--   gives one: `c+x < c+y` is strictly stronger than what holds here and
--   strictly weaker than what is needed (the `nsuc` lands on the wrong
--   side of `plusTm`, which recurses on its FIRST argument).
--
-- ★ THE WITNESS IS UNCHANGED.  `plusMonoTm p c = natrec p (var vz) c` is
--   the term for the strict lemma AND for this one — the order proof is
--   what reduces and `+`'s monotonicity carries no computational content,
--   so only the TYPE differs.  That is why this module is short.
--
-- ⚠ The `L` (recursed-argument) version goes through commutativity, for
--   exactly the reason `NbEPDirDBLibArithComm`'s header gives: `plusTm` is
--   stuck in its first argument and `≤` is not an inductive family, so
--   there is no direct induction.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.ArithLe where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; Hom; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; ordtr
        ; renTy; renTm; subTy; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢ordtr; ⊢unit; Hom-Nat-z
        ; ty-Nat; ty-Hom
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; Hom-Nat-ss
        ; ξ-Homˡ; ξ-Homʳ; natrec-zero; natrec-suc; wk-single )
open import DirectedHoTT.Metatheory.Injectivity using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Wk using ( w; nrs-w )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Arith using ( plusMonoTm )
open import DirectedHoTT.Lib.ArithComm
  using ( IdN; commTm; ⊢comm; congS; ⊢congS; trHomˡ; ⊢trHomˡ; trHomʳ; ⊢trHomʳ
        ; plus0Tm; ⊢plus0 )

------------------------------------------------------------------------
-- ★ `x ≤ y  ⇒  c + x ≤ c + y`, by `natrec` on the recursed argument.
--
--   c = 0      both sides peel by `natrec-zero`, leaving the hypothesis;
--   c = suc c' both peel by `natrec-suc` to `nsuc (…)`, and the successor
--              is then stripped from BOTH endpoints at once — see the
--              note on `Hom-Nat-ss'` below — leaving exactly the IH.
--
-- ⚠ THE MOTIVE IS BOUND-EXPLICIT, same reason as `LibArith`'s: written
--   inline it leaves a `wk-single` residue at all three boundaries.
------------------------------------------------------------------------

plusLeB : {Γ : Cx} (x y c : RTm Γ) → RTy Γ
plusLeB x y c = Hom Nat (plusTm c x) (plusTm c y)

plusLeMot : {Γ : Cx} (x y : RTm Γ) → RTy (Γ ∙)
plusLeMot x y = plusLeB (w x) (w y) (var vz)

⊢plusLeMot : {Γ : Ctx} {x y : RTm ⌊ Γ ⌋} →
             Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat → (Γ ▹ Nat) ⊢ty plusLeMot x y
⊢plusLeMot dx dy =
  ty-Hom ty-Nat (⊢plus (⊢var here) (⊢wk dx)) (⊢plus (⊢var here) (⊢wk dy))

le-at : {Γ : Cx} (x y n : RTm Γ) →
        subTy (single n) (plusLeMot x y) ≡ plusLeB x y n
le-at x y n =
  cong₂ (λ a b → Hom Nat (plusTm n a) (plusTm n b))
        (wk-single {v = n} x) (wk-single {v = n} y)

le-s : {Γ : Cx} (x y : RTm Γ) →
       subTy nrs (plusLeMot x y)
     ≡ plusLeB (w (w x)) (w (w y)) (nsuc (var (vs vz)))
le-s x y =
  cong₂ (λ a b → Hom Nat (plusTm (nsuc (var (vs vz))) a)
                         (plusTm (nsuc (var (vs vz))) b))
        (nrs-w x) (nrs-w y)

⊢plus-le : {Γ : Ctx} {x y c p : RTm ⌊ Γ ⌋} →
           Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat → Γ ⊢ c ∷ Nat →
           Γ ⊢ p ∷ Hom Nat x y →                       -- x ≤ y
           Γ ⊢ plusMonoTm p c ∷ plusLeB x y c          -- c+x ≤ c+y
⊢plus-le {x = x} {y = y} {c = c} dx dy dc dp =
  ⊢-cast (le-at x y c) (⊢natrec (⊢plusLeMot dx dy) zB sB dc)
  where
    zB = ⊢-cast (sym (le-at x y nzero))
           (⊢conv dp
             (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Homˡ (natrec-zero _ _))
                              (stepᵀ (ξ-Homʳ (natrec-zero _ _)) doneᵀ)))))
    sB = ⊢-cast (sym (le-s x y))
           (⊢conv (⊢var here)
             (csymᵀ (ctrnᵀ (red→≅ᵀ (stepᵀ (ξ-Homˡ (natrec-suc _ _ _))
                                     (stepᵀ (ξ-Homʳ (natrec-suc _ _ _)) doneᵀ)))
                           (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ)))))

------------------------------------------------------------------------
-- ★ …and in the RECURSED argument, by commutativity.  Literal clone of
--   `⊢plus-mono-l`: the same three transports, the same order.
------------------------------------------------------------------------

plusLeLB : {Γ : Cx} (x y c : RTm Γ) → RTy Γ
plusLeLB x y c = Hom Nat (plusTm x c) (plusTm y c)

plusLeLTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
-- ⚠ NO `congS` HERE, unlike `plusMonoLTm`.  The strict version transports
--   an endpoint of the shape `nsuc (plusTm c x)`, so its `Id` has to be
--   pushed under the successor first; the non-strict endpoint IS the sum,
--   and `⊢comm` already speaks about it.  One transport cheaper.
plusLeLTm x y c p =
  trHomʳ (plusTm x c) (commTm y c)
    (trHomˡ (plusTm c y) (commTm x c)
      (plusMonoTm p c))

⊢plus-le-l : {Γ : Ctx} {x y c p : RTm ⌊ Γ ⌋} →
             Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat → Γ ⊢ c ∷ Nat →
             Γ ⊢ p ∷ Hom Nat x y →
             Γ ⊢ plusLeLTm x y c p ∷ plusLeLB x y c
⊢plus-le-l {x = x} {y = y} {c = c} dx dy dc dp =
  ⊢trHomʳ (⊢plus dc dy) (⊢plus dy dc) (⊢plus dx dc)
          (⊢comm dy dc)
          (⊢trHomˡ (⊢plus dc dx) (⊢plus dx dc) (⊢plus dc dy)
                   (⊢comm dx dc)
                   (⊢plus-le dx dy dc dp))

------------------------------------------------------------------------
-- ★★★ THE ONE THE CALLER ACTUALLY WANTS: BOTH ARGUMENTS AT ONCE.
--
--     x ≤ x'   y ≤ y'   ⇒   x + y ≤ x' + y'
--
--   by `x + y ≤ x + y' ≤ x' + y'` — the base argument first (cheap), then
--   the recursed one (commutativity) — composed with `⊢ordtr`.
--
-- ⚠ THE MIDPOINT `x + y'` IS IN THE TERM.  `ordtr` carries all three
--   endpoints, so a caller reading this witness sees the whole chain; do
--   not try to hide it behind an inferred metavariable.
------------------------------------------------------------------------

plusLe₂Tm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
plusLe₂Tm x x' y y' p q =
  ordtr (plusTm x y) (plusTm x y') (plusTm x' y')
        (plusMonoTm q x) (plusLeLTm x x' y' p)

⊢plus-le₂ : {Γ : Ctx} {x x' y y' p q : RTm ⌊ Γ ⌋} →
            Γ ⊢ x ∷ Nat → Γ ⊢ x' ∷ Nat → Γ ⊢ y ∷ Nat → Γ ⊢ y' ∷ Nat →
            Γ ⊢ p ∷ Hom Nat x x' →                     -- x ≤ x'
            Γ ⊢ q ∷ Hom Nat y y' →                     -- y ≤ y'
            Γ ⊢ plusLe₂Tm x x' y y' p q
              ∷ Hom Nat (plusTm x y) (plusTm x' y')    -- x+y ≤ x'+y'
⊢plus-le₂ dx dx' dy dy' dp dq =
  ⊢ordtr (⊢plus dx dy) (⊢plus dx dy') (⊢plus dx' dy')
         (⊢plus-le dy dy' dx dq)
         (⊢plus-le-l dx dx' dy' dp)

------------------------------------------------------------------------
-- ★ `x ≤ x + y` — A SUMMAND IS BOUNDED BY THE SUM.
--
-- ⚠ WHY IT IS NOT `⊢plus-le` AT `x := 0`.  It is, ALMOST: `⊢plus-le` at
--   `x := 0` gives `c + 0 ≤ c + y`, and `plusTm` recurses on its FIRST
--   argument, so `c + 0` is STUCK for open `c` — `0 + n ⟶ n` is free and
--   `n + 0 ≡ n` is the induction.  One `trHomˡ` along `⊢plus0` closes the
--   gap, and that is the whole content of this lemma.
--
-- ★ ITS CUSTOMER is a STRUCTURAL DESCENT: a node's measure is the sum of
--   its children's, so "a child is smaller than its parent" is exactly
--   `x ≤ x + y` under one `nsuc`.  `Examples/ScopedSize` is the first.
--
-- ⚠ `0 ≤ n` IS `unit`, not an induction — `Hom Nat` COMPUTES, and
--   `Hom-Nat-z` discards the right endpoint outright.
------------------------------------------------------------------------

⊢le-zero : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} → Γ ⊢ unit ∷ Hom Nat nzero n
⊢le-zero {n = n} = ⊢conv ⊢unit (csymᵀ (red→≅ᵀ (stepᵀ (Hom-Nat-z n) doneᵀ)))

leSumTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
leSumTm x y = trHomˡ (plusTm x y) (plus0Tm x) (plusMonoTm unit x)

⊢le-sum : {Γ : Ctx} {x y : RTm ⌊ Γ ⌋} →
          Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat →
          Γ ⊢ leSumTm x y ∷ Hom Nat x (plusTm x y)
⊢le-sum dx dy =
  ⊢trHomˡ (⊢plus dx ⊢nzero) dx (⊢plus dx dy) (⊢plus0 dx)
          (⊢plus-le ⊢nzero dy dx ⊢le-zero)
