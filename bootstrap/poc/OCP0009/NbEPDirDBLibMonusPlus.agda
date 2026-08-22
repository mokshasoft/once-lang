------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — `monusPlus`:  a ∸ b ≡ suc p  ⟹  a ≡ (suc p) + b.
--
-- ⚠⚠ WHY ITS OWN MODULE, AND IT IS A MEASUREMENT.  Kept inside
--   `…LibDvdArith` the file reached 929 lines and Agda was OOM-KILLED
--   (exit 143, uncontended, NO error message — the tell for an OOM rather
--   than a type error).  `monusPlus` is a `natrec` inside a `natrec` whose
--   motive Π-binds a carrier, a predecessor AND an equation, so the
--   elaborated term is large; that module already carried eight other
--   internal inductions.  Split out, both check.
--
-- ⭐ ONE BIG TERM PER MODULE, once the term is big enough — the same lever
--   that took `leaf₃s` from an OOM to 10s and `split2` to 4.8s.
--
-- ★ WHY THE PREMISE IS AN EQUATION AND NOT AN ORDER.  gcd's `a > b` branch
--   has NO `Hom Nat b a` in scope — a `natrec` branch carries no evidence
--   about its scrutinee (`GAP-B-LAYER2-PLAN.md` §2).  What the
--   inspect-encoded split DOES hand over is exactly `a ∸ b ≡ suc p`, so
--   that is the premise this lemma takes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibMonusPlus where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs
        ; RTy; El; Id; Nat; Π; lam; app; absurd
        ; RTm; var; nzero; nsuc; natrec; ⌜Id⌝; ⌜Nat⌝
        ; subTy; subTm; renTy; renTm; Ren; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ty-Nat; ty-Π
        ; csymᵀ; ξ-Idʳ; natrec-suc; wk-single )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ; ⟶ᵀ*-Idˡ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLibWk
  using ( w; nrs-w; sub-w; cong₃; ren-w²; ren-w³ )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus
  using ( predTm; monusTm; ⊢pred; ⊢monus; monus-zero; monus-suc )
open import poc.OCP0009.NbEPDirDBLibArithComm
  using ( IdN; ⊢tyIdN; congS; ⊢congS; symN; ⊢symN; transN; ⊢transN
        ; plus0Tm; ⊢plus0; plusSTm; ⊢plusS )
open import poc.OCP0009.NbEPDirDBLibDvdArith
  using ( zmTm; ⊢zero-monus; pmTm; ⊢pred-monus; noConfTm; exFalsoN )

------------------------------------------------------------------------
-- ★★★★ 8.  `monusPlus`'s STATEMENT, AND THE ONE PEEL ITS IH NEEDS.
--
-- The lemma to come is
--
--     ∀ b a p.  a ∸ b ≡ suc p  →  a ≡ (suc p) + b
--
-- proved by `natrec` on `b` with `a`, `p` and the equation `Π`-bound in
-- the motive.  ⚠ THREE Π's MEAN THREE `subTy`s AT EVERY IH USE, and
-- inlining them is where this kind of proof drowns.  `mpUse` pays them
-- ONCE, so the induction's two branches read like the paper proof.
--
-- ★ Everything below peels by `wk-single`/`sub-w` alone: `monusTm` and
--   `plusTm` both distribute through `subTm` definitionally (see §4), so
--   the only propositional steps are the weakenings the Π's introduced.
------------------------------------------------------------------------

mpAt : {Γ : Cx} (b : RTm Γ) → RTy Γ
mpAt b =
  Π Nat
    (Π Nat
      (Π (IdN (monusTm (var (vs vz)) (w (w b))) (nsuc (var vz)))
         (IdN (var (vs (vs vz)))
              (plusTm (nsuc (var (vs vz))) (w (w (w b)))))))

⊢mpAt : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat → Γ ⊢ty mpAt b
⊢mpAt db =
  ty-Π ty-Nat
    (ty-Π ty-Nat
      (ty-Π (⊢tyIdN (⊢monus (⊢var (there here)) (⊢wk (⊢wk db)))
                    (⊢nsuc (⊢var here)))
            (⊢tyIdN (⊢var (there (there here)))
                    (⊢plus (⊢nsuc (⊢var (there here)))
                           (⊢wk (⊢wk (⊢wk db)))))))

mpUse : {Γ : Ctx} {b h a p e : RTm ⌊ Γ ⌋} →
        Γ ⊢ h ∷ mpAt b →
        Γ ⊢ a ∷ Nat → Γ ⊢ p ∷ Nat →
        Γ ⊢ e ∷ IdN (monusTm a b) (nsuc p) →
        Γ ⊢ app (app (app h a) p) e ∷ IdN a (plusTm (nsuc p) b)
mpUse {b = b} {a = a} {p = p} {e = e} dh da dp de =
  -- ⭐ `peel₂` already normalises the domain, so `de` goes straight in —
  --   no cast on the argument.
  ⊢-cast peel₃ (⊢app (⊢-cast peel₂ (⊢app (⊢-cast peel₁ (⊢app dh da)) dp)) de)
  where
    -- ⚠ EVERY TYPE HERE IS WRITTEN OUT.  `cong₂`'s source cannot be
    --   inferred through a `subTy` of a `Π`, and leaving it to Agda turns
    --   the whole chain into unsolved metas.  (Cost of learning that: one
    --   round.)  Same rule as pinning `subren`'s implicits.

    -- the ambient `b`, pushed under one / two extra binders
    b¹ : subTm (extS (single a)) (w (w b)) ≡ w b
    b¹ = trans (sub-w {σ = single a} (w b)) (cong w (wk-single {v = a} b))

    b² : subTm (extS (extS (single a))) (w (w (w b))) ≡ w (w b)
    b² = trans (sub-w {σ = extS (single a)} (w (w b))) (cong w b¹)

    peel₁ : subTy (single a)
              (Π Nat (Π (IdN (monusTm (var (vs vz)) (w (w b))) (nsuc (var vz)))
                        (IdN (var (vs (vs vz)))
                             (plusTm (nsuc (var (vs vz))) (w (w (w b)))))))
          ≡ Π Nat (Π (IdN (monusTm (w a) (w b)) (nsuc (var vz)))
                     (IdN (w (w a))
                          (plusTm (nsuc (var (vs vz))) (w (w b)))))
    peel₁ =
      cong₂ (λ u v → Π Nat (Π (IdN (monusTm (w a) u) (nsuc (var vz)))
                              (IdN (w (w a))
                                   (plusTm (nsuc (var (vs vz))) v))))
            b¹ b²

    domEq : subTy (single p) (IdN (monusTm (w a) (w b)) (nsuc (var vz)))
          ≡ IdN (monusTm a b) (nsuc p)
    domEq = cong₂ (λ u v → IdN (monusTm u v) (nsuc p))
                  (wk-single {v = p} a) (wk-single {v = p} b)

    bodyEq : subTy (extS (single p))
               (IdN (w (w a)) (plusTm (nsuc (var (vs vz))) (w (w b))))
           ≡ IdN (w a) (plusTm (nsuc (w p)) (w b))
    bodyEq =
      cong₂ (λ u v → IdN u (plusTm (nsuc (w p)) v))
            (trans (sub-w {σ = single p} (w a)) (cong w (wk-single {v = p} a)))
            (trans (sub-w {σ = single p} (w b)) (cong w (wk-single {v = p} b)))

    peel₂ : subTy (single p)
              (Π (IdN (monusTm (w a) (w b)) (nsuc (var vz)))
                 (IdN (w (w a)) (plusTm (nsuc (var (vs vz))) (w (w b)))))
          ≡ Π (IdN (monusTm a b) (nsuc p))
              (IdN (w a) (plusTm (nsuc (w p)) (w b)))
    peel₂ = cong₂ Π domEq bodyEq

    peel₃ : subTy (single e) (IdN (w a) (plusTm (nsuc (w p)) (w b)))
          ≡ IdN a (plusTm (nsuc p) b)
    peel₃ = cong₃ (λ u v x → IdN u (plusTm (nsuc v) x))
                  (wk-single {v = e} a) (wk-single {v = e} p)
                  (wk-single {v = e} b)

------------------------------------------------------------------------
-- ★★★★★★ 9.  `monusPlus` — `a ∸ b ≡ suc p  ⟹  a ≡ (suc p) + b`.
--
-- ★ OUTER `natrec` on `b`; INNER `natrec` on `a` in the successor branch.
--   Four leaves, and each is one line of ordinary arithmetic once the
--   right lemma is in hand:
--
--     b = 0                   `monus-zero` + `⊢plus0`
--     b = suc b', a = 0       `zero-monus` + `exFalsoN`      (absurd)
--     b = suc b', a = suc a'  `pred-monus` + the IH + `⊢plusS`
--
-- ⚠ THE INNER INDUCTION IS ON A **VARIABLE**, so it needs no `inspect`.
--   Only gcd's split on `a ∸ b` does (see `GAP-B-LAYER2-PLAN.md` §2), and
--   that is what this lemma's `a ∸ b ≡ suc p` premise is FOR: it is
--   exactly the equation the inspect-encoded split hands over.
------------------------------------------------------------------------

-- ★ the motive under a renaming — the OUTER IH arrives five binders deep,
--   and `renTy` does NOT distribute through `mpAt` definitionally
--   (`w (w b)` needs `ren-w²`).
mpAt-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (b : RTm Γ) →
           renTy ρ (mpAt b) ≡ mpAt (renTm ρ b)
mpAt-ren {ρ = ρ} b =
  cong₂ (λ u v → Π Nat (Π Nat (Π (IdN (monusTm (var (vs vz)) u) (nsuc (var vz)))
                                 (IdN (var (vs (vs vz)))
                                      (plusTm (nsuc (var (vs vz))) v)))))
        (ren-w² {ρ = ρ} b) (ren-w³ {ρ = ρ} b)

mpAt-w⁵ : {Γ : Cx} (b : RTm Γ) →
          renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (mpAt b)))))
        ≡ mpAt (w (w (w (w (w b)))))
mpAt-w⁵ b =
  trans (cong (λ T → renTy vs (renTy vs (renTy vs (renTy vs T))))
              (mpAt-ren {ρ = vs} b))
    (trans (cong (λ T → renTy vs (renTy vs (renTy vs T)))
                 (mpAt-ren {ρ = vs} (w b)))
      (trans (cong (λ T → renTy vs (renTy vs T))
                   (mpAt-ren {ρ = vs} (w (w b))))
        (trans (cong (renTy vs) (mpAt-ren {ρ = vs} (w (w (w b)))))
               (mpAt-ren {ρ = vs} (w (w (w (w b))))))))

mpAt-w⁶ : {Γ : Cx} (b : RTm Γ) →
          renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (renTy vs (mpAt b))))))
        ≡ mpAt (w (w (w (w (w (w b))))))
mpAt-w⁶ b =
  trans (cong (λ T → renTy vs (renTy vs (renTy vs (renTy vs (renTy vs T)))))
              (mpAt-ren {ρ = vs} b))
        (mpAt-w⁵ (w b))

-- ★ the INNER motive: `a` is the scrutinee, the equation is Π-bound.
mpInner : {Γ : Cx} (b' p : RTm Γ) → RTy (Γ ∙)
mpInner b' p =
  Π (IdN (monusTm (var vz) (nsuc (w b'))) (nsuc (w p)))
    (IdN (var (vs vz)) (plusTm (nsuc (w (w p))) (nsuc (w (w b')))))

⊢mpInner : {Γ : Ctx} {b' p : RTm ⌊ Γ ⌋} →
           Γ ⊢ b' ∷ Nat → Γ ⊢ p ∷ Nat → (Γ ▹ Nat) ⊢ty mpInner b' p
⊢mpInner db' dp =
  ty-Π (⊢tyIdN (⊢monus (⊢var here) (⊢nsuc (⊢wk db'))) (⊢nsuc (⊢wk dp)))
       (⊢tyIdN (⊢var (there here))
               (⊢plus (⊢nsuc (⊢wk (⊢wk dp))) (⊢nsuc (⊢wk (⊢wk db')))))

mpInner-at : {Γ : Cx} (b' p a : RTm Γ) →
             subTy (single a) (mpInner b' p)
           ≡ Π (IdN (monusTm a (nsuc b')) (nsuc p))
               (IdN (w a) (plusTm (nsuc (w p)) (nsuc (w b'))))
mpInner-at b' p a =
  cong₂ Π
    (cong₂ (λ u v → IdN (monusTm a (nsuc u)) (nsuc v))
           (wk-single {v = a} b') (wk-single {v = a} p))
    (cong₂ (λ u v → IdN (w a) (plusTm (nsuc u) (nsuc v)))
           (trans (sub-w {σ = single a} (w p)) (cong w (wk-single {v = a} p)))
           (trans (sub-w {σ = single a} (w b')) (cong w (wk-single {v = a} b'))))

mpInner-s : {Γ : Cx} (b' p : RTm Γ) →
            subTy nrs (mpInner b' p)
          ≡ Π (IdN (monusTm (nsuc (var (vs vz))) (nsuc (w (w b'))))
                   (nsuc (w (w p))))
              (IdN (nsuc (var (vs (vs vz))))
                   (plusTm (nsuc (w (w (w p)))) (nsuc (w (w (w b'))))))
mpInner-s b' p =
  cong₂ Π
    (cong₂ (λ u v → IdN (monusTm (nsuc (var (vs vz))) (nsuc u)) (nsuc v))
           (nrs-w b') (nrs-w p))
    (cong₂ (λ u v → IdN (nsuc (var (vs (vs vz))))
                        (plusTm (nsuc u) (nsuc v)))
           (trans (sub-w {σ = nrs} (w p)) (cong w (nrs-w p)))
           (trans (sub-w {σ = nrs} (w b')) (cong w (nrs-w b'))))

-- ★ the outer motive's own peel: `mpAt` at the scrutinee.
mpAt-at : {Γ : Cx} (b : RTm Γ) →
          subTy (single b) (mpAt {Γ ∙} (var vz)) ≡ mpAt b
mpAt-at b = refl

mpAt-s : {Γ : Cx} →
         subTy nrs (mpAt {Γ ∙} (var vz))
       ≡ mpAt {(Γ ∙) ∙} (nsuc (var (vs vz)))
mpAt-s = refl

------------------------------------------------------------------------
-- ★★★ THE THREE LEAVES, AS TOP-LEVEL LEMMAS AT AN ARBITRARY CONTEXT.
--
-- ⚠⚠ THIS FACTORING IS FORCED, AND IT IS MEASURED.  Written inline inside
--   the two `natrec` branches, `⊢mpS` was OOM-KILLED (exit 143,
--   uncontended, no error message) even ALONE in this module.  Hoisting
--   each leaf to a top-level lemma whose arguments are `RTm`s puts its
--   body behind a `Def`, so the term-traversal phases walk a REFERENCE
--   instead of the whole derivation.
--
-- ⭐ `check.sh`'s own header prescribes exactly this ("split derivations
--   into top-level lemmas whose implicits are `RTm`s and whose bodies sit
--   behind a `Def`, the `⊢strong-base'` pattern") — and note it is a
--   STRONGER lever than splitting modules: splitting alone did NOT fix it.
------------------------------------------------------------------------

-- ★ b = 0.  `a ∸ 0 ⟶ a`, and the goal's `suc p + 0` reduces to
--   `suc (p + 0)`, which `⊢plus0` closes.  No induction.
mpBaseTm : {Γ : Cx} (a p eq : RTm Γ) → RTm Γ
mpBaseTm a p eq =
  transN a eq (symN (nsuc (plusTm p nzero))
                    (congS (plusTm p nzero) (plus0Tm p)))

⊢mpBase : {Γ : Ctx} {a p eq : RTm ⌊ Γ ⌋} →
          Γ ⊢ a ∷ Nat → Γ ⊢ p ∷ Nat →
          Γ ⊢ eq ∷ IdN (monusTm a nzero) (nsuc p) →
          Γ ⊢ mpBaseTm a p eq ∷ IdN a (plusTm (nsuc p) nzero)
⊢mpBase {a = a} da dp deq =
  ⊢conv (⊢transN da (⊢nsuc dp) (⊢nsuc (⊢plus dp ⊢nzero))
           (⊢conv deq (red→≅ᵀ (⟶ᵀ*-Idˡ (monus-zero a))))
           (⊢symN (⊢nsuc (⊢plus dp ⊢nzero)) (⊢nsuc dp)
                  (⊢congS (⊢plus dp ⊢nzero) dp (⊢plus0 dp))))
        (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Idʳ (natrec-suc _ _ _)) doneᵀ)))

-- ★ b = suc b', a = 0.  `zero-monus` makes the premise `0 ≡ suc p`.
mpZeroTm : {Γ : Cx} (p b' eq : RTm Γ) → RTm Γ
mpZeroTm p b' eq =
  absurd (⌜Id⌝ ⌜Nat⌝ nzero (plusTm (nsuc p) (nsuc b')))
         (noConfTm (transN nzero
                     (symN (monusTm nzero (nsuc b')) (zmTm (nsuc b'))) eq))

⊢mpZero : {Γ : Ctx} {p b' eq : RTm ⌊ Γ ⌋} →
          Γ ⊢ p ∷ Nat → Γ ⊢ b' ∷ Nat →
          Γ ⊢ eq ∷ IdN (monusTm nzero (nsuc b')) (nsuc p) →
          Γ ⊢ mpZeroTm p b' eq ∷ IdN nzero (plusTm (nsuc p) (nsuc b'))
⊢mpZero dp db' deq =
  exFalsoN dp ⊢nzero (⊢plus (⊢nsuc dp) (⊢nsuc db'))
    (⊢transN ⊢nzero (⊢monus ⊢nzero (⊢nsuc db')) (⊢nsuc dp)
       (⊢symN (⊢monus ⊢nzero (⊢nsuc db')) ⊢nzero (⊢zero-monus (⊢nsuc db')))
       deq)

-- ★★ b = suc b', a = suc a'.  `pred-monus` steps the premise down, the
--    OUTER IH fires at `(a' , p)`, and `⊢plusS` re-associates the goal.
mpStepEq : {Γ : Cx} (a' b' eq : RTm Γ) → RTm Γ
mpStepEq a' b' eq =
  transN (monusTm a' b')
         (symN (predTm (monusTm (nsuc a') b')) (pmTm a' b')) eq

mpStepTm : {Γ : Cx} (a' p b' ih eq : RTm Γ) → RTm Γ
mpStepTm a' p b' ih eq =
  transN (nsuc a')
    (congS a' (app (app (app ih a') p) (mpStepEq a' b' eq)))
    (symN (plusTm (nsuc p) (nsuc b')) (plusSTm b' (nsuc p)))

⊢mpStep : {Γ : Ctx} {a' p b' ih eq : RTm ⌊ Γ ⌋} →
          Γ ⊢ a' ∷ Nat → Γ ⊢ p ∷ Nat → Γ ⊢ b' ∷ Nat →
          Γ ⊢ ih ∷ mpAt b' →
          Γ ⊢ eq ∷ IdN (monusTm (nsuc a') (nsuc b')) (nsuc p) →
          Γ ⊢ mpStepTm a' p b' ih eq ∷ IdN (nsuc a') (plusTm (nsuc p) (nsuc b'))
⊢mpStep {a' = a'} {b' = b'} da' dp db' dih deq =
  ⊢transN (⊢nsuc da') (⊢nsuc (⊢plus (⊢nsuc dp) db'))
          (⊢plus (⊢nsuc dp) (⊢nsuc db'))
    (⊢congS da' (⊢plus (⊢nsuc dp) db') (mpUse {b = b'} dih da' dp dEq₂))
    (⊢symN (⊢plus (⊢nsuc dp) (⊢nsuc db')) (⊢nsuc (⊢plus (⊢nsuc dp) db'))
           (⊢plusS db' (⊢nsuc dp)))
  where
    dEq₂ = ⊢transN (⊢monus da' db') (⊢pred (⊢monus (⊢nsuc da') db'))
                   (⊢nsuc dp)
                   (⊢symN (⊢pred (⊢monus (⊢nsuc da') db'))
                          (⊢monus da' db') (⊢pred-monus da' db'))
                   (⊢conv deq (red→≅ᵀ (⟶ᵀ*-Idˡ (monus-suc (nsuc a') b'))))

------------------------------------------------------------------------
-- the two `natrec` branches — now thin, because the leaves are `Def`s
------------------------------------------------------------------------

mpZTm : {Γ : Cx} → RTm Γ
mpZTm = lam (lam (lam (mpBaseTm (var (vs (vs vz))) (var (vs vz)) (var vz))))

⊢mpZ : {Γ : Ctx} → Γ ⊢ mpZTm ∷ mpAt nzero
⊢mpZ =
  ⊢lam ty-Nat
    (⊢lam ty-Nat
      (⊢lam (⊢tyIdN (⊢monus (⊢var (there here)) ⊢nzero) (⊢nsuc (⊢var here)))
            (⊢mpBase (⊢var (there (there here))) (⊢var (there here))
                     (⊢var here))))

-- ⚠ THE BRANCH TERMS ARE DEPTH-SPECIFIC, and their signatures must say so.
--   Slots at the inner ZERO leaf: [0] eq [1] p [2] a [3] IH [4] b'
mpSZTm : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙)
mpSZTm = mpZeroTm (var (vs vz)) (var (vs (vs (vs (vs vz))))) (var vz)

--   …and at the inner SUCCESSOR leaf:
--   [0] eq [1] innerIH [2] a' [3] p [4] a [5] IH [6] b'
mpSSTm : {Γ : Cx} → RTm (Γ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
mpSSTm = mpStepTm (var (vs (vs vz))) (var (vs (vs (vs vz))))
                  (var (vs (vs (vs (vs (vs (vs vz)))))))
                  (var (vs (vs (vs (vs (vs vz))))))
                  (var vz)

mpSTm : {Γ : Cx} → RTm (Γ ∙ ∙)
mpSTm = lam (lam (natrec (lam mpSZTm) (lam mpSSTm) (var (vs vz))))

⊢mpS : {Γ : Ctx} →
       ((Γ ▹ Nat) ▹ mpAt (var vz)) ⊢ mpSTm ∷ mpAt (nsuc (var (vs vz)))
⊢mpS = ⊢lam ty-Nat (⊢lam ty-Nat inner)
  where
    A  = var (vs vz)
    P  = var vz
    B' = var (vs (vs (vs vz)))

    dA  = ⊢var (there here)
    dP  = ⊢var here
    dB' = ⊢var (there (there (there here)))

    zA = ⊢-cast (sym (mpInner-at B' P nzero))
           (⊢lam (⊢tyIdN (⊢monus ⊢nzero (⊢nsuc dB')) (⊢nsuc dP))
                 (⊢mpZero (⊢var (there here))
                          (⊢var (there (there (there (there here)))))
                          (⊢var here)))

    sA = ⊢-cast (sym (mpInner-s B' P))
           (⊢lam (⊢tyIdN (⊢monus (⊢nsuc (⊢var (there here)))
                                 (⊢nsuc (⊢var (there (there (there (there (there here)))))))) 
                         (⊢nsuc (⊢var (there (there here)))))
                 (⊢mpStep (⊢var (there (there here)))
                          (⊢var (there (there (there here))))
                          (⊢var (there (there (there (there (there (there here)))))))
                          (⊢-cast (mpAt-w⁶ (var vz))
                                  (⊢var (there (there (there (there (there here)))))))
                          (⊢var here)))

    inner = ⊢-cast (mpInner-at B' P A)
              (⊢natrec (⊢mpInner dB' dP) zA sA dA)

------------------------------------------------------------------------
-- ★★★★★★ …AND THE LEMMA.
------------------------------------------------------------------------

mpTm : {Γ : Cx} → RTm Γ → RTm Γ
mpTm b = natrec mpZTm mpSTm b

⊢monusPlus : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat →
             Γ ⊢ mpTm b ∷ mpAt b
⊢monusPlus {b = b} db =
  ⊢-cast (mpAt-at b) (⊢natrec (⊢mpAt (⊢var here)) ⊢mpZ ⊢mpS db)

-- ★ the form a client calls: from `a ∸ b ≡ suc p`, get `a ≡ suc p + b`.
monusPlus : {Γ : Ctx} {a b p e : RTm ⌊ Γ ⌋} →
            Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ p ∷ Nat →
            Γ ⊢ e ∷ IdN (monusTm a b) (nsuc p) →
            Γ ⊢ app (app (app (mpTm b) a) p) e ∷ IdN a (plusTm (nsuc p) b)
monusPlus {b = b} da db dp de = mpUse {b = b} (⊢monusPlus db) da dp de
