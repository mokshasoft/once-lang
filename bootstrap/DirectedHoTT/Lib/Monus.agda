------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — TRUNCATED SUBTRACTION AND PREDECESSOR.
--
-- ★ WHY THIS MODULE EXISTS.  `…LibArithMonus` — the monus arithmetic the
--   WF layer and gap A's equation 4 are built on — needs `predTm`/
--   `monusTm` and their reduction laws, so a LIBRARY was importing an
--   EXAMPLE.  These are the primitives; `…ExamplesDiv` keeps `m ∸ n ≤ m`,
--   the descent certificates, and `div` itself.
--
-- ⚠ `…ExamplesDiv` re-exports this module `public`, so every existing
--   importer keeps working unchanged; only `Lib*` importers were
--   repointed.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Monus where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst; ⊥ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; ordtr; ⌜Hom⌝; ⌜Nat⌝
        ; renTy; subTy; Π; lam; app )
open import DirectedHoTT.Spec.Typing
  using ( _⟶_; _⟶*_; done; step; natrec-zero; natrec-suc; ξ-nsuc
        ; _⟶ᵀ_; El-⌜Hom⌝; El-⌜Nat⌝; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢unit; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢ordtr; ⊢⌜Hom⌝; ⊢⌜Nat⌝
        ; _⊢ty_; ty-El; ty-Nat; ty-Π; ty-Hom
        ; ⊢lam; ⊢app; nrs; wk-single )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-natrecⁿ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Strong
  using ( El-homNat; natAsEl; ⊢le-refl; ⊢le-suc; reflTm )

------------------------------------------------------------------------
-- 1. OBJECT-LANGUAGE ARITHMETIC.
--
--    `natrec z s n` binds the NUMBER then the IH in `s`, so inside `s`
--    the number is `var (vs vz)` and the IH is `var vz`.
------------------------------------------------------------------------

-- pred 0 = 0 ; pred (suc k) = k   — the step returns the NUMBER.
predTm : {Γ : Cx} → RTm Γ → RTm Γ
predTm m = natrec nzero (var (vs vz)) m

-- m ∸ 0 = m ; m ∸ (suc k) = pred (m ∸ k)  — the step preds the IH.
monusTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
monusTm m n = natrec m (predTm (var vz)) n

⊢pred : {Γ : Ctx} {m : RTm ⌊ Γ ⌋} → Γ ⊢ m ∷ Nat → Γ ⊢ predTm m ∷ Nat
⊢pred dm = ⊢natrec ty-Nat ⊢nzero (⊢var (there here)) dm

⊢monus : {Γ : Ctx} {m n : RTm ⌊ Γ ⌋} →
         Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ monusTm m n ∷ Nat
⊢monus dm dn = ⊢natrec ty-Nat dm (⊢pred (⊢var here)) dn

------------------------------------------------------------------------
-- 2. THE TWO COMPUTATION RULES, as reductions.
--
--    ⚠ `pred (suc n)` does NOT reduce to `n` definitionally for an OPEN
--      `n`: `natrec-suc` leaves `subTm (single …) (renTm vs n)`, and
--      collapsing that is `wk-single`.  One `subst`, once.
------------------------------------------------------------------------

pred-zero : {Γ : Cx} → predTm {Γ} nzero ⟶* nzero
pred-zero = step (natrec-zero _ _) done

pred-suc : {Γ : Cx} (n : RTm Γ) → predTm (nsuc n) ⟶* n
pred-suc n =
  subst (λ z → predTm (nsuc n) ⟶* z) (wk-single n)
        (step (natrec-suc _ _ _) done)

monus-zero : {Γ : Cx} (m : RTm Γ) → monusTm m nzero ⟶* m
monus-zero m = step (natrec-zero _ _) done

-- m ∸ (suc k) ⟶* pred (m ∸ k).
-- ★ NO `wk-single` here, unlike `pred-suc`: `predTm`'s body mentions the
--   scrutinee only, so `subTm σ (predTm t) = predTm (subTm σ t)` holds
--   DEFINITIONALLY and the step lands on the nose.
monus-suc : {Γ : Cx} (m k : RTm Γ) → monusTm m (nsuc k) ⟶* predTm (monusTm m k)
monus-suc m k = step (natrec-suc _ _ _) done

------------------------------------------------------------------------
-- 3. `pred m ≤ m`.
--
--    ★ the successor branch is `⊢le-suc` — `pred (suc k) ≤ suc k` IS
--      `k ≤ suc k` once `pred` computes.  No new induction.
------------------------------------------------------------------------

-- lift a term reduction into the LEFT endpoint of a hom.
homˡ* : {Γ : Cx} {A : RTy Γ} {t t' u : RTm Γ} →
        t ⟶* t' → Hom A t u ⟶ᵀ* Hom A t' u
homˡ* done       = doneᵀ
homˡ* (step r q) = stepᵀ (ξ-Homˡ r) (homˡ* q)

predMot : {Γ : Cx} → RTy (Γ ∙)
predMot = El (⌜Hom⌝ ⌜Nat⌝ (predTm (var vz)) (var vz))

⊢predMot : {Γ : Ctx} → (Γ ▹ Nat) ⊢ty predMot
⊢predMot =
  ty-El (⊢⌜Hom⌝ ⊢⌜Nat⌝ (natAsEl (⊢pred (⊢var here))) (natAsEl (⊢var here)))

⊢pred-le : {Γ : Ctx} {m : RTm ⌊ Γ ⌋} →
           Γ ⊢ m ∷ Nat →
           Γ ⊢ natrec unit (reflTm (var (vs vz))) m ∷ Hom Nat (predTm m) m
⊢pred-le {m = m} dm =
  ⊢conv (⊢natrec ⊢predMot zB sB dm) (red→≅ᵀ (El-homNat (predTm m) m))
  where
    zB : {Γ : Ctx} → Γ ⊢ unit ∷ El (⌜Hom⌝ ⌜Nat⌝ (predTm nzero) nzero)
    zB = ⊢conv ⊢unit
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans (El-homNat (predTm nzero) nzero)
                            (⟶ᵀ*-trans (homˡ* pred-zero)
                                       (stepᵀ (Hom-Nat-z nzero) doneᵀ)))))

    sB : {Γ : Ctx} →
         ((Γ ▹ Nat) ▹ predMot) ⊢ reflTm (var (vs vz))
           ∷ El (⌜Hom⌝ ⌜Nat⌝ (predTm (nsuc (var (vs vz))))
                             (nsuc (var (vs vz))))
    sB = ⊢conv (⊢le-suc (⊢var (there here)))
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans
             (El-homNat (predTm (nsuc (var (vs vz)))) (nsuc (var (vs vz))))
             (homˡ* (pred-suc (var (vs vz)))))))
