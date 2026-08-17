------------------------------------------------------------------------
-- OCP-0009 — gcd's TWO DESCENTS, at the measure `μ (a , b) = a + b`.
--
-- ★ THE SHAPE.  Subtractive Euclid changes a different component in each
--   branch, so the two descents use the two DIFFERENT monotonicities:
--
--     a > b :  (a ∸ b) + b  <  a + b     `⊢plus-mono-l`  (recursed arg)
--     a ≤ b :  a + (b ∸ a)  <  a + b     `⊢plus-mono`    (base arg)
--
--   That is the whole reason commutativity had to be proved: one of the
--   two is unreachable without it (`NbEPDirDBLibArith`'s header).
--
-- ★★ AND THE STRICT MONUS FACT IS AN INDUCTION ON `b`, NOT `⊢monus-le`.
--   `⊢monus-le` is stated for a `Var` — deliberately, so its motive's
--   `renTm vs` computes — and gcd needs it at `nsuc k'`, which is not a
--   variable.  ⚠ Rather than generalise it (the header warns that an
--   arbitrary term puts a stuck `renTm vs m` in the motive and every
--   obligation then needs a renaming lemma), it is cheaper to prove the
--   STRICT statement directly:
--
--       suc a ∸ suc b  ≤  a
--
--   by `natrec` on `b`, where the step is `⊢pred-le` composed with the IH
--   by `⊢ordtr` and the base is two `monus` reductions then `pred-suc`.
--   ★ Both branches of gcd instantiate this same lemma, swapped.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibArithMonus where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; Hom; Nat
        ; RTm; var; nzero; nsuc; natrec; ordtr; unit
        ; renTm; subTy; subTm; Sub; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢ordtr; ty-Nat; ty-Hom
        ; _≅ᵀ_; csymᵀ; Hom-Nat-ss
        ; _⟶_; _⟶*_; done; step; ξ-natrecⁿ )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; nrs-w; sub-w² )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBExamplesDiv
  using ( predTm; ⊢pred; ⊢pred-le; monusTm; ⊢monus
        ; monus-zero; monus-suc; pred-suc; homˡ* )
open import poc.OCP0009.NbEPDirDBLibArith using ( plusMonoB; plusMonoTm; ⊢plus-mono )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( plusMonoLB; plusMonoLTm; ⊢plus-mono-l )

------------------------------------------------------------------------
-- lifting a reduction into `pred`'s scrutinee
------------------------------------------------------------------------

pred* : {Γ : Cx} {t t' : RTm Γ} → t ⟶* t' → predTm t ⟶* predTm t'
pred* done       = done
pred* (step r q) = step (ξ-natrecⁿ r) (pred* q)

------------------------------------------------------------------------
-- ★★ `suc a ∸ suc b ≤ a`, by induction on `b`.
------------------------------------------------------------------------

monusLtB : {Γ : Cx} (a b : RTm Γ) → RTy Γ
monusLtB a b = Hom Nat (monusTm (nsuc a) (nsuc b)) a

⊢monusLtMot : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ Nat →
              (Γ ▹ Nat) ⊢ty monusLtB (w a) (var vz)
⊢monusLtMot da =
  ty-Hom ty-Nat (⊢monus (⊢nsuc (⊢wk da)) (⊢nsuc (⊢var here))) (⊢wk da)

mlt-at : {Γ : Cx} (a k : RTm Γ) →
         subTy (single k) (monusLtB (w a) (var vz)) ≡ monusLtB a k
mlt-at a k =
  cong (λ z → Hom Nat (monusTm (nsuc z) (nsuc k)) z) (wk-single {v = k} a)

mlt-s : {Γ : Cx} (a : RTm Γ) →
        subTy nrs (monusLtB (w a) (var vz))
      ≡ monusLtB (w (w a)) (nsuc (var (vs vz)))
mlt-s a =
  cong (λ z → Hom Nat (monusTm (nsuc z) (nsuc (nsuc (var (vs vz))))) z) (nrs-w a)

-- the base's reduction chain: `suc a ∸ suc 0 ⟶* a`
mlt-chain : {Γ : Cx} (a : RTm Γ) → monusTm (nsuc a) (nsuc nzero) ⟶* a
mlt-chain a =
  ⟶*-trans (monus-suc (nsuc a) nzero)
    (⟶*-trans (pred* (monus-zero (nsuc a))) (pred-suc a))

monusLtTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
monusLtTm a b =
  natrec (reflTm a)
         (ordtr (predTm U) U (w (w a))
                (natrec unit (reflTm (var (vs vz))) U)
                (var vz))
         b
  where
    U : RTm _
    U = monusTm (nsuc (w (w a))) (nsuc (var (vs vz)))

⊢monusLt : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
           Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat →
           Γ ⊢ monusLtTm a b ∷ monusLtB a b
⊢monusLt {a = a} {b = b} da db =
  ⊢-cast (mlt-at a b) (⊢natrec (⊢monusLtMot da) zB sB db)
  where
    zB = ⊢-cast (sym (mlt-at a nzero))
           (⊢conv (⊢le-refl da) (csymᵀ (red→≅ᵀ (homˡ* (mlt-chain a)))))
    sB = ⊢-cast (sym (mlt-s a))
           (⊢conv (⊢ordtr (⊢pred dU) dU dA (⊢pred-le dU) (⊢var here))
                  (csymᵀ (red→≅ᵀ (homˡ* (monus-suc (nsuc (w (w a)))
                                                   (nsuc (var (vs vz))))))))
      where
        dA = ⊢wk (⊢wk da)
        dU = ⊢monus (⊢nsuc dA) (⊢nsuc (⊢var (there here)))

------------------------------------------------------------------------
-- ★ the STRICT form the descents want: `suc a ∸ suc b < suc a`.
--   One `Hom-Nat-ss` peel away from the above.
------------------------------------------------------------------------

⊢monusLt' : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
            Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat →
            Γ ⊢ monusLtTm a b
              ∷ Hom Nat (nsuc (monusTm (nsuc a) (nsuc b))) (nsuc a)
⊢monusLt' da db =
  ⊢conv (⊢monusLt da db) (csymᵀ (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ)))

------------------------------------------------------------------------
-- ★★★ THE TWO DESCENTS.
--
--   ⚠ Both are stated at `suc a` / `suc b`, which is exactly the form the
--     step function has after splitting BOTH components — and it must
--     split both, because `a ∸ b < a` is false at `a = 0`.
------------------------------------------------------------------------

-- a > b : recurse at (a ∸ b , b).  The FIRST component changes, so this
-- is the recursed-argument monotonicity — the one commutativity bought.
⊢desc-left : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
             Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat →
             Γ ⊢ plusMonoLTm (monusTm (nsuc a) (nsuc b)) (nsuc a) (nsuc b)
                             (monusLtTm a b)
               ∷ plusMonoLB (monusTm (nsuc a) (nsuc b)) (nsuc a) (nsuc b)
⊢desc-left da db =
  ⊢plus-mono-l (⊢monus (⊢nsuc da) (⊢nsuc db)) (⊢nsuc da) (⊢nsuc db)
               (⊢monusLt' da db)

-- a ≤ b : recurse at (a , b ∸ a).  The SECOND component changes, so this
-- is the cheap base-argument monotonicity.
⊢desc-right : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
              Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat →
              Γ ⊢ plusMonoTm (monusLtTm b a) (nsuc a)
                ∷ plusMonoB (monusTm (nsuc b) (nsuc a)) (nsuc b) (nsuc a)
⊢desc-right da db =
  ⊢plus-mono (⊢monus (⊢nsuc db) (⊢nsuc da)) (⊢nsuc db) (⊢nsuc da)
             (⊢monusLt' db da)

------------------------------------------------------------------------
-- ★ SUBSTITUTION-NATURALITY, as for the templates in `…LibArithComm`.
--   ⚠ `monusLtTm` hides `w (w a)` in FOUR places (once directly, three
--   times inside `U`), so this is one `sub-w²` and one rewrite — the same
--   distribute-then-rewrite shape as `commTm-sub`.
------------------------------------------------------------------------

reflTm-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (m : RTm Γ) →
             subTm σ (reflTm m) ≡ reflTm (subTm σ m)
reflTm-sub m = refl

monusLtTm-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (a b : RTm Γ) →
                subTm σ (monusLtTm a b) ≡ monusLtTm (subTm σ a) (subTm σ b)
monusLtTm-sub {σ = σ} a b = rewriteA (sub-w² {σ = σ} a)
  where
    A2 : RTm _
    A2 = subTm (extS (extS σ)) (w (w a))

    rewriteA : {u : RTm _} → A2 ≡ u →
               natrec (reflTm (subTm σ a))
                 (ordtr (predTm (monusTm (nsuc A2) (nsuc (var (vs vz)))))
                        (monusTm (nsuc A2) (nsuc (var (vs vz)))) A2
                        (natrec unit (reflTm (var (vs vz)))
                                (monusTm (nsuc A2) (nsuc (var (vs vz)))))
                        (var vz))
                 (subTm σ b)
             ≡ natrec (reflTm (subTm σ a))
                 (ordtr (predTm (monusTm (nsuc u) (nsuc (var (vs vz)))))
                        (monusTm (nsuc u) (nsuc (var (vs vz)))) u
                        (natrec unit (reflTm (var (vs vz)))
                                (monusTm (nsuc u) (nsuc (var (vs vz)))))
                        (var vz))
                 (subTm σ b)
    rewriteA refl = refl
