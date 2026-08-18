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

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; Hom; Nat; El; Π; base
        ; RTm; var; nzero; nsuc; natrec; ordtr; unit; lam; app; absurd
        ; renTm; subTy; subTm; Sub; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢ordtr; ty-Nat; ty-Hom
        ; _≅ᵀ_; csymᵀ; Hom-Nat-ss; Hom-Nat-sz; ⊢absurd
        ; _⟶_; _⟶*_; done; step; ξ-natrecⁿ )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; nrs-w; sub-w; sub-w² )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBExamplesDiv
  using ( predTm; ⊢pred; ⊢pred-le; monusTm; ⊢monus
        ; monus-zero; monus-suc; pred-suc; pred-zero; homˡ* )
open import poc.OCP0009.NbEPDirDBLibArith using ( plusMonoB; plusMonoTm; ⊢plus-mono )
open import poc.OCP0009.NbEPDirDBLibArithComm
  using ( plusMonoLB; plusMonoLTm; ⊢plus-mono-l
        ; IdN; ⊢tyIdN; elIdN; reflN; ⊢reflN; transN; ⊢transN )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( natAsEl )
open import poc.OCP0009.NbEPDirDBLibPair using ( asN )
open import poc.OCP0009.NbEPDirDBPi using ( jsub; ⌜Id⌝; ⌜Nat⌝; idrefl )
open import poc.OCP0009.NbEPDirDBType
  using ( ⊢jsub; ⊢⌜Id⌝; ⊢⌜Nat⌝; ⊢idrefl; ty-Id; ty-El; ty-Π; ⊢lam; ⊢app )

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

------------------------------------------------------------------------
-- ★★★★ THE PROPOSITIONAL BRIDGE — PIECE 1: `cong` FOR `pred`.
--
-- ⚠ WHY IT IS NEEDED.  Equation 4 needs `a ≤ b → monus a b ≡ 0`, and
--   `monusTm` recurses on its SECOND argument through `predTm`.  So every
--   inductive step has to move an identity under a `predTm`, which is a
--   congruence — and this kernel derives congruences by `jsub`, exactly as
--   `congS` does for `nsuc`.  This is `congS` with `nsuc` → `predTm`.
--
-- ⚠ NOT the `⌜Π⌝`-family transport that is banned elsewhere: that ban is
--   about a Π-VALUED family, and this family is `⌜Id⌝ ⌜Nat⌝ … …`, the same
--   shape `congS`/`symN`/`transN` already use safely.
------------------------------------------------------------------------

congPred : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
congPred a p = jsub (⌜Id⌝ ⌜Nat⌝ (predTm (w a)) (predTm (var vz))) p
                    (reflN (predTm a))

⊢congPred : {Γ : Ctx} {a b p : RTm ⌊ Γ ⌋} →
            Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ p ∷ IdN a b →
            Γ ⊢ congPred a p ∷ IdN (predTm a) (predTm b)
⊢congPred {a = a} {b = b} da db dp =
  ⊢conv (⊢-cast (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ (predTm z) (predTm b)))
                      (wk-single {v = b} a))
                (⊢jsub dd (natAsEl da) (natAsEl db) dp de))
        (elIdN (predTm a) (predTm b))
  where
    dd = ⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢pred (⊢wk da)))
                      (natAsEl (⊢pred (asN (⊢var here))))
    de = ⊢-cast (sym (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ (predTm z) (predTm a)))
                           (wk-single {v = a} a)))
                (⊢conv (⊢reflN (⊢pred da))
                       (csymᵀ (elIdN (predTm a) (predTm a))))

------------------------------------------------------------------------
-- ★★ PIECE 2 — `0 ∸ b ≡ 0`, by induction on `b`.
--
-- `monusTm` recurses on its SECOND argument, so this is the base fact the
-- bridge needs at `a = 0`: a variable `b` never lets `natrec` fire, and an
-- INTERNAL induction is the only way to reach it.
------------------------------------------------------------------------

monus0B : {Γ : Cx} (b : RTm Γ) → RTy Γ
monus0B b = IdN (monusTm nzero b) nzero

⊢monus0Mot : {Γ : Ctx} → (Γ ▹ Nat) ⊢ty monus0B (var vz)
⊢monus0Mot = ⊢tyIdN (⊢monus ⊢nzero (⊢var here)) ⊢nzero

monus0Tm : {Γ : Cx} → RTm Γ → RTm Γ
monus0Tm b = natrec (reflN nzero)
                    (congPred (monusTm nzero (var (vs vz))) (var vz))
                    b

⊢monus0 : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat →
          Γ ⊢ monus0Tm b ∷ monus0B b
⊢monus0 {b = b} db = ⊢natrec ⊢monus0Mot zB sB db
  where
    -- b := 0 :  0 ∸ 0 ⟶* 0, so `refl` after rewriting the left endpoint
    zB = ⊢conv (⊢reflN ⊢nzero)
               (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ (monus-zero nzero))))
    -- b := suc k :  0 ∸ suc k ⟶* pred (0 ∸ k), and the IH gives 0 ∸ k ≡ 0
    sB = ⊢conv (⊢conv (⊢congPred (⊢monus ⊢nzero (⊢var (there here))) ⊢nzero
                                 (⊢var here))
                      (red→≅ᵀ (⟶ᵀ*-Idʳ (pred-zero))))
               (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ (monus-suc nzero (var (vs vz))))))

------------------------------------------------------------------------
-- ★★ PIECE 3 — `suc a ∸ suc b ≡ a ∸ b`, by induction on `b`.
--
-- ⚠ THE STEP THE BRIDGE TURNS ON.  `Hom Nat` computes, so `suc a ≤ suc b`
--   CONVERTS to `a ≤ b` (`Hom-Nat-ss`) — the order side of the induction is
--   free.  The `monus` side is not: `monusTm` recurses on its second
--   argument, so peeling a `suc` off BOTH arguments is a real induction,
--   and this is it.
------------------------------------------------------------------------

monusSSB : {Γ : Cx} (a b : RTm Γ) → RTy Γ
monusSSB a b = IdN (monusTm (nsuc a) (nsuc b)) (monusTm a b)

⊢monusSSMot : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ Nat →
              (Γ ▹ Nat) ⊢ty monusSSB (w a) (var vz)
⊢monusSSMot da =
  ⊢tyIdN (⊢monus (⊢nsuc (⊢wk da)) (⊢nsuc (⊢var here)))
         (⊢monus (⊢wk da) (⊢var here))

mss-at : {Γ : Cx} (a k : RTm Γ) →
         subTy (single k) (monusSSB (w a) (var vz)) ≡ monusSSB a k
mss-at a k =
  cong (λ z → IdN (monusTm (nsuc z) (nsuc k)) (monusTm z k)) (wk-single {v = k} a)

mss-s : {Γ : Cx} (a : RTm Γ) →
        subTy nrs (monusSSB (w a) (var vz))
      ≡ monusSSB (w (w a)) (nsuc (var (vs vz)))
mss-s a =
  cong (λ z → IdN (monusTm (nsuc z) (nsuc (nsuc (var (vs vz)))))
                  (monusTm z (nsuc (var (vs vz)))))
       (nrs-w a)

monusSSTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
monusSSTm a b =
  natrec (reflN a)
         (congPred (monusTm (nsuc (w (w a))) (nsuc (var (vs vz)))) (var vz))
         b

⊢monusSS : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat →
           Γ ⊢ monusSSTm a b ∷ monusSSB a b
⊢monusSS {a = a} {b = b} da db =
  ⊢-cast (mss-at a b) (⊢natrec (⊢monusSSMot da) zB sB db)
  where
    -- b := 0 :  suc a ∸ suc 0 ⟶* a  and  a ∸ 0 ⟶* a, so both sides are `a`
    zB = ⊢-cast (sym (mss-at a nzero))
           (⊢conv (⊢conv (⊢reflN da)
                         (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ (monus-zero a)))))
                  (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ (mlt-chain a)))))
    -- b := suc k :  both sides peel one `pred`, and the IH bridges them
    sB = ⊢-cast (sym (mss-s a))
           (⊢conv (⊢conv (⊢congPred dL dR (⊢var here))
                         (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ (monus-suc dA' dK')))))
                  (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ (monus-suc (nsuc dA') (nsuc dK'))))))
      where
        dA  = ⊢wk (⊢wk da)
        dA' = w (w a)
        dK' = var (vs vz)
        dL  = ⊢monus (⊢nsuc dA) (⊢nsuc (⊢var (there here)))
        dR  = ⊢monus dA (⊢var (there here))

------------------------------------------------------------------------
-- ★★★★★ PIECE 4 — THE BRIDGE: `a ≤ b → a ∸ b ≡ 0`.
--
-- ⭐ WHY THE ORDER PREMISE AND NOT `Id (a ∸ b) 0`.  `Hom Nat` COMPUTES:
--
--     Hom Nat 0       n        ⟶ᵀ Unit          (0 ≤ n, trivially)
--     Hom Nat (suc m) 0        ⟶ᵀ base          (suc m ≤ 0, absurd)
--     Hom Nat (suc m) (suc n)  ⟶ᵀ Hom Nat m n   (inversion, FREE)
--
--   so the three cases of this induction are exactly the three rules, and
--   inversion and ex-falso cost a CONVERSION rather than a lemma each.  An
--   `Id`-on-`monus` premise would need both proved, and would leak
--   `monusTm`'s recursion scheme into gcd's statement.
--
-- ⚠ THE INDUCTION IS ON `a`, WITH `b` QUANTIFIED INTERNALLY.  It has to be:
--   the `suc`/`suc` case needs the IH at a DIFFERENT `b`, so `b` cannot be
--   a meta-level parameter fixed outside.
------------------------------------------------------------------------

-- the inner goal, once `a` is a successor and `b` is bound
monusLeB : {Γ : Cx} (a : RTm Γ) → RTy Γ
monusLeB a = Π Nat (Π (Hom Nat (w a) (var vz))
                      (IdN (monusTm (w (w a)) (var (vs vz))) nzero))

⊢monusLeMot : {Γ : Ctx} → (Γ ▹ Nat) ⊢ty monusLeB (var vz)
⊢monusLeMot =
  ty-Π ty-Nat
    (ty-Π (ty-Hom ty-Nat (⊢var (there here)) (⊢var here))
          (⊢tyIdN (⊢monus (⊢var (there (there here))) (⊢var (there here)))
                  ⊢nzero))

-- ★ the two branches, as their own Defs (one big term per Def)

monusLeZ : {Γ : Cx} → RTm Γ
monusLeZ = lam (lam (monus0Tm (var (vs vz))))

⊢monusLeZ : {Γ : Ctx} → Γ ⊢ monusLeZ ∷ monusLeB nzero
⊢monusLeZ =
  ⊢lam ty-Nat
    (⊢lam (ty-Hom ty-Nat ⊢nzero (⊢var here))
          (⊢monus0 (⊢var (there here))))

-- ★★ THE INNER SPLIT.  At `a := suc k` the certificate decides `b`:
--    `suc k ≤ 0` is `base` (absurd), `suc k ≤ suc j` IS `k ≤ j`.

-- the inner motive: `b` fresh, `k` reachable past (b, ih)
leC : {Γ : Cx} → RTy ((((Γ ∙) ∙) ∙) ∙)
leC = Π (Hom Nat (nsuc (var (vs (vs (vs vz))))) (var vz))
        (IdN (monusTm (nsuc (var (vs (vs (vs (vs vz)))))) (var (vs vz))) nzero)

⊢leC : {Γ : Ctx} → ((((Γ ▹ Nat) ▹ monusLeB (var vz)) ▹ Nat) ▹ Nat) ⊢ty leC
⊢leC = ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢var (there (there (there here))))) (⊢var here))
            (⊢tyIdN (⊢monus (⊢nsuc (⊢var (there (there (there (there here))))))
                            (⊢var (there here)))
                    ⊢nzero)

monusLeS : {Γ : Cx} → RTm ((Γ ∙) ∙)
monusLeS =
  lam (natrec (lam (absurd (⌜Id⌝ ⌜Nat⌝ (monusTm (nsuc (var (vs (vs (vs vz))))) nzero)
                                       nzero)
                           (var vz)))
              (lam (transN (monusTm (nsuc (var (vs (vs (vs (vs (vs vz)))))))
                                    (nsuc (var (vs (vs vz)))))
                           (monusSSTm (var (vs (vs (vs (vs (vs vz))))))
                                      (var (vs (vs vz))))
                           (app (app (var (vs (vs (vs (vs vz)))))
                                     (var (vs (vs vz))))
                                (var vz))))
              (var vz))

monusLeTm : {Γ : Cx} → RTm Γ → RTm Γ
monusLeTm a = natrec monusLeZ monusLeS a

⊢monusLe : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ Nat →
           Γ ⊢ monusLeTm a ∷ monusLeB a
⊢monusLe {a = a} da = ⊢natrec ⊢monusLeMot ⊢monusLeZ sB da
  where
    sB = ⊢lam ty-Nat (⊢natrec ⊢leC zBr sBr (⊢var here))
      where
        -- b := 0 :  `suc k ≤ 0` reduces to `base`, so the branch is absurd
        zBr = ⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢var (there (there here)))) ⊢nzero)
                   (⊢conv (⊢absurd dCode dBase) (elIdN _ _))
          where
            dCode = ⊢⌜Id⌝ ⊢⌜Nat⌝
                      (natAsEl (⊢monus (⊢nsuc (⊢var (there (there (there here)))))
                                       ⊢nzero))
                      (natAsEl ⊢nzero)
            dBase = ⊢conv (⊢var here) (red→≅ᵀ (stepᵀ (Hom-Nat-sz _) doneᵀ))
        -- b := suc j :  `suc k ≤ suc j` IS `k ≤ j`, so the IH applies at j
        -- ⚠ THE DOMAIN AND THE BODY SIT EITHER SIDE OF THE `lam`, so `k` and
        --   `j` need DIFFERENT indices in the two positions — one binder
        --   apart.  Sharing one derivation between them is the trap.
        sBr = ⊢lam (ty-Hom ty-Nat (⊢nsuc dKᵈ) (⊢nsuc dJᵈ))
                   (⊢transN dLHS dMID ⊢nzero (⊢monusSS dK' dJ) dIHapp)
          where
            -- domain side (before `c` is bound)
            dKᵈ  = ⊢var (there (there (there (there here))))
            dJᵈ  = ⊢var (there here)
            -- body side (after `c` is bound)
            dK'  = ⊢var (there (there (there (there (there here)))))
            dJ   = ⊢var (there (there here))
            dIH  = ⊢var (there (there (there (there here))))
            dLHS = ⊢monus (⊢nsuc dK') (⊢nsuc dJ)
            dMID = ⊢monus dK' dJ
            dCer = ⊢conv (⊢var here) (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ))
            dIHapp = ⊢app (⊢app dIH dJ) dCer

------------------------------------------------------------------------
-- ★★ NON-VACUITY FOR THE BRIDGE — `a ∸ a ≡ 0`, at a VARIABLE `a`.
--
-- ⚠ THIS FILE'S OWN POST-MORTEM is the reason it is here: two lemmas were
--   `--safe`, hole-free and green, and VACUOUS, because their premise could
--   not be satisfied where they were stated.  `⊢monusLe` is a `Π` over the
--   certificate, so the question is whether ANY certificate exists at a
--   variable.  It does — `⊢le-refl` — and this is the witness.
--
-- ⭐ CONTRAST WITH THE `⟶*` PREMISE IT REPLACES.  `monusTm (nsuc a)
--   (nsuc b) ⟶* nzero` forces BOTH arguments ground (a variable never
--   reduces).  `Hom Nat a b` is inhabited at variables.  That difference is
--   exactly why equation 4 was unreachable and is now approachable.
------------------------------------------------------------------------

monusSelfTm : {Γ : Cx} → RTm Γ → RTm Γ
monusSelfTm a = app (app (monusLeTm a) a) (reflTm a)

-- ⚠ TWO PEELS.  Applying a `Π`-quantified motive at `b := a` leaves the
--   motive's DOUBLE weakening of `a` to cancel, plus the bound `b` slot.
--   `sub-w` then `wk-single` for the first; `wk-single` alone for the
--   second, since `extS σ (vs v)` is already `w (σ v)` definitionally.
mself-peel : {Γ : Cx} (a : RTm Γ) →
             subTm (single (reflTm a)) (subTm (extS (single a)) (w (w a))) ≡ a
mself-peel a =
  trans (cong (subTm (single (reflTm a)))
              (trans (sub-w {σ = single a} (w a))
                     (cong w (wk-single {v = a} a))))
        (wk-single {v = reflTm a} a)

mself-at : {Γ : Cx} (a : RTm Γ) →
           subTy (single (reflTm a))
                 (subTy (extS (single a))
                        (IdN (monusTm (w (w a)) (var (vs vz))) nzero))
         ≡ IdN (monusTm a a) nzero
mself-at a = cong₂ (λ x y → IdN (monusTm x y) nzero)
                   (mself-peel a) (wk-single {v = reflTm a} a)

⊢monusSelf : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ Nat →
             Γ ⊢ monusSelfTm a ∷ IdN (monusTm a a) nzero
⊢monusSelf {a = a} da =
  ⊢-cast (mself-at a) (⊢app (⊢app (⊢monusLe da) da) dRefl)
  where
    -- the certificate slot is `Hom Nat (w a) (var vz)` under `single a`,
    -- so reflexivity needs the same one-step peel
    dRefl = ⊢-cast (sym (cong (λ z → Hom Nat z a) (wk-single {v = a} a)))
                   (⊢le-refl da)
