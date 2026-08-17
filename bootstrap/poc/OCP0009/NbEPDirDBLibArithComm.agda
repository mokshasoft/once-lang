------------------------------------------------------------------------
-- OCP-0009 — COMMUTATIVITY OF `+`, and the `Id`-at-`Nat` kit it needs.
--
-- ⚠ WHY.  `NbEPDirDBLibArith` proves `+` monotone in its BASE argument and shows
--   that the RECURSED argument is unreachable that way — `plusTm` recurses
--   on its first argument, so for open `x`,`y` both sides are stuck, and
--   `<` is a COMPUTING `Hom Nat` rather than an inductive family, so there
--   is nothing to induct on.  gcd needs BOTH (its two branches change
--   different components), and commutativity is what bridges them.
--
-- ★ THE KIT IS FOUR `jsub`s.  The kernel's `⊢jsub` is TRANSPORT — carry a
--   CODE family `d` along an `Id` — not full `J`, and transport is all
--   that is wanted here.  Each of `cong nsuc`, `sym` and `trans` is the
--   same call with a different `d`:
--
--     cong nsuc   d = ⌜Id⌝ ⌜Nat⌝ (nsuc (w a)) (nsuc (var vz))
--     sym         d = ⌜Id⌝ ⌜Nat⌝ (var vz)     (w a)
--     trans       d = ⌜Id⌝ ⌜Nat⌝ (w a)        (var vz)
--
-- ⚠ EVERY `Id` HERE IS AT `El ⌜Nat⌝`, NOT AT `Nat` — `⊢idrefl` and
--   `⊢jsub` are CODE-indexed (`Γ ⊢ c ∷ U → … ∷ Id (El c) t t`), the same
--   forcing that makes the WF library's motive a code (`WF-LIBRARY.md`
--   D4).  So `natAsEl`/`asN` cross in and out, and `El-⌜Id⌝` converts the
--   `jsub` result back to an `Id`.  That is the whole overhead.
--
-- ⚠ AND EVERY `jsub` PAYS ONE `wk-single`: the family `d` mentions the
--   ambient endpoint as `w a`, and `subTm (single _)` undoes that only
--   PROPOSITIONALLY.  One `⊢-cast` per call, twice per lemma (the input
--   `e` and the output).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibArithComm where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Id; Nat; Hom
        ; RTm; var; nzero; nsuc; natrec; idrefl; jsub; ⌜Id⌝; ⌜Nat⌝; ⌜Hom⌝
        ; renTm; subTy; subTm; Sub; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢idrefl; ⊢jsub; ⊢⌜Id⌝; ⊢⌜Nat⌝; ⊢⌜Hom⌝
        ; ty-Id; ty-El; ty-Nat
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; El-⌜Id⌝
        ; ξ-Idˡ; ξ-Idʳ; ξ-nsuc; natrec-zero; natrec-suc )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; nrs-w; sub-w; sub-w² )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( natAsEl; El-homNat )
open import poc.OCP0009.NbEPDirDBLibArith using ( plusMonoB; plusMonoTm; ⊢plus-mono )
open import poc.OCP0009.NbEPDirDBLibPair using ( asN )

------------------------------------------------------------------------
-- `Id` at `Nat`, and its code twin
------------------------------------------------------------------------

IdN : {Γ : Cx} → RTm Γ → RTm Γ → RTy Γ
IdN a b = Id (El ⌜Nat⌝) a b

⊢tyIdN : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ty IdN a b
⊢tyIdN da db = ty-Id (ty-El ⊢⌜Nat⌝) (natAsEl da) (natAsEl db)

-- `El (⌜Id⌝ ⌜Nat⌝ a b) ≅ᵀ IdN a b` — the one reduction every `jsub` needs
elIdN : {Γ : Cx} (a b : RTm Γ) → El (⌜Id⌝ ⌜Nat⌝ a b) ≅ᵀ IdN a b
elIdN a b = red→≅ᵀ (stepᵀ (El-⌜Id⌝ _ _ _) doneᵀ)

reflN : {Γ : Cx} → RTm Γ → RTm Γ
reflN a = idrefl ⌜Nat⌝ a

⊢reflN : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ Nat → Γ ⊢ reflN a ∷ IdN a a
⊢reflN da = ⊢idrefl ⊢⌜Nat⌝ (natAsEl da)

------------------------------------------------------------------------
-- ★ cong nsuc
------------------------------------------------------------------------

congS : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
congS a p = jsub (⌜Id⌝ ⌜Nat⌝ (nsuc (w a)) (nsuc (var vz))) p (reflN (nsuc a))

⊢congS : {Γ : Ctx} {a b p : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ p ∷ IdN a b →
         Γ ⊢ congS a p ∷ IdN (nsuc a) (nsuc b)
⊢congS {a = a} {b = b} da db dp =
  ⊢conv (⊢-cast (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ (nsuc z) (nsuc b))) (wk-single {v = b} a))
                (⊢jsub dd (natAsEl da) (natAsEl db) dp de))
        (elIdN (nsuc a) (nsuc b))
  where
    dd = ⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢nsuc (⊢wk da)))
                      (natAsEl (⊢nsuc (asN (⊢var here))))
    de = ⊢-cast (sym (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ (nsuc z) (nsuc a)))
                           (wk-single {v = a} a)))
                (⊢conv (⊢reflN (⊢nsuc da)) (csymᵀ (elIdN (nsuc a) (nsuc a))))

------------------------------------------------------------------------
-- ★ sym and trans — the same call, other families
------------------------------------------------------------------------

symN : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
symN a p = jsub (⌜Id⌝ ⌜Nat⌝ (var vz) (w a)) p (reflN a)

⊢symN : {Γ : Ctx} {a b p : RTm ⌊ Γ ⌋} →
        Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ p ∷ IdN a b →
        Γ ⊢ symN a p ∷ IdN b a
⊢symN {a = a} {b = b} da db dp =
  ⊢conv (⊢-cast (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ b z)) (wk-single {v = b} a))
                (⊢jsub dd (natAsEl da) (natAsEl db) dp de))
        (elIdN b a)
  where
    dd = ⊢⌜Id⌝ ⊢⌜Nat⌝ (⊢var here) (natAsEl (⊢wk da))
    de = ⊢-cast (sym (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ a z)) (wk-single {v = a} a)))
                (⊢conv (⊢reflN da) (csymᵀ (elIdN a a)))

transN : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
transN a p q = jsub (⌜Id⌝ ⌜Nat⌝ (w a) (var vz)) q p

⊢transN : {Γ : Ctx} {a b c p q : RTm ⌊ Γ ⌋} →
          Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ c ∷ Nat →
          Γ ⊢ p ∷ IdN a b → Γ ⊢ q ∷ IdN b c →
          Γ ⊢ transN a p q ∷ IdN a c
⊢transN {a = a} {b = b} {c = c} da db dc dp dq =
  ⊢conv (⊢-cast (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ z c)) (wk-single {v = c} a))
                (⊢jsub dd (natAsEl db) (natAsEl dc) dq de))
        (elIdN a c)
  where
    dd = ⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢wk da)) (⊢var here)
    de = ⊢-cast (sym (cong (λ z → El (⌜Id⌝ ⌜Nat⌝ z b)) (wk-single {v = b} a)))
                (⊢conv dp (csymᵀ (elIdN a b)))

------------------------------------------------------------------------
-- ★ 1.  `m + 0 = m`.  ⚠ `plusTm` recurses on its FIRST argument, so
--   `0 + n ⟶ n` is FREE and `m + 0` is the one that needs an induction.
--   The motive mentions no ambient term, so — uniquely among the three —
--   it needs no `mot-at`/`mot-s`.
------------------------------------------------------------------------

plus0B : {Γ : Cx} (m : RTm Γ) → RTy Γ
plus0B m = IdN (plusTm m nzero) m

⊢plus0Mot : {Γ : Ctx} → (Γ ▹ Nat) ⊢ty plus0B (var vz)
⊢plus0Mot = ⊢tyIdN (⊢plus (⊢var here) ⊢nzero) (⊢var here)

plus0Tm : {Γ : Cx} → RTm Γ → RTm Γ
plus0Tm m = natrec (reflN nzero) (congS (plusTm (var (vs vz)) nzero) (var vz)) m

⊢plus0 : {Γ : Ctx} {m : RTm ⌊ Γ ⌋} → Γ ⊢ m ∷ Nat → Γ ⊢ plus0Tm m ∷ plus0B m
⊢plus0 dm = ⊢natrec ⊢plus0Mot zB sB dm
  where
    zB = ⊢conv (⊢reflN ⊢nzero)
           (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Idˡ (natrec-zero _ _)) doneᵀ)))
    sB = ⊢conv (⊢congS (⊢plus (⊢var (there here)) ⊢nzero) (⊢var (there here))
                       (⊢var here))
           (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Idˡ (natrec-suc _ _ _)) doneᵀ)))

------------------------------------------------------------------------
-- ★ 2.  `m + suc n = suc (m + n)`.  ⚠ `n` is AMBIENT, so the motive is
--   bound-explicit and pays `mot-at`/`mot-s` — the house pattern.
------------------------------------------------------------------------

plusSB : {Γ : Cx} (n m : RTm Γ) → RTy Γ
plusSB n m = IdN (plusTm m (nsuc n)) (nsuc (plusTm m n))

⊢plusSMot : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ Nat →
            (Γ ▹ Nat) ⊢ty plusSB (w n) (var vz)
⊢plusSMot dn =
  ⊢tyIdN (⊢plus (⊢var here) (⊢nsuc (⊢wk dn)))
         (⊢nsuc (⊢plus (⊢var here) (⊢wk dn)))

psMot-at : {Γ : Cx} (n k : RTm Γ) →
           subTy (single k) (plusSB (w n) (var vz)) ≡ plusSB n k
psMot-at n k =
  cong (λ z → IdN (plusTm k (nsuc z)) (nsuc (plusTm k z))) (wk-single {v = k} n)

psMot-s : {Γ : Cx} (n : RTm Γ) →
          subTy nrs (plusSB (w n) (var vz))
        ≡ plusSB (w (w n)) (nsuc (var (vs vz)))
psMot-s n =
  cong (λ z → IdN (plusTm (nsuc (var (vs vz))) (nsuc z))
                  (nsuc (plusTm (nsuc (var (vs vz))) z)))
       (nrs-w n)

plusSTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
plusSTm n m =
  natrec (reflN (nsuc n))
         (congS (plusTm (var (vs vz)) (nsuc (w (w n)))) (var vz))
         m

⊢plusS : {Γ : Ctx} {n m : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ plusSTm n m ∷ plusSB n m
⊢plusS {n = n} {m = m} dn dm =
  ⊢-cast (psMot-at n m) (⊢natrec (⊢plusSMot dn) zB sB dm)
  where
    zB = ⊢-cast (sym (psMot-at n nzero))
           (⊢conv (⊢reflN (⊢nsuc dn))
             (csymᵀ (ctrnᵀ (red→≅ᵀ (stepᵀ (ξ-Idˡ (natrec-zero _ _)) doneᵀ))
                           (red→≅ᵀ (stepᵀ (ξ-Idʳ (ξ-nsuc (natrec-zero _ _))) doneᵀ)))))
    sB = ⊢-cast (sym (psMot-s n))
           (⊢conv (⊢congS (⊢plus (⊢var (there here)) (⊢nsuc (⊢wk (⊢wk dn))))
                          (⊢nsuc (⊢plus (⊢var (there here)) (⊢wk (⊢wk dn))))
                          (⊢var here))
             (csymᵀ (ctrnᵀ (red→≅ᵀ (stepᵀ (ξ-Idˡ (natrec-suc _ _ _)) doneᵀ))
                           (red→≅ᵀ (stepᵀ (ξ-Idʳ (ξ-nsuc (natrec-suc _ _ _))) doneᵀ)))))

------------------------------------------------------------------------
-- ★★ 3.  COMMUTATIVITY.  `m + n = n + m`, by `natrec` on `m`, using 1 in
--    the base and 2 in the step.  ⚠ The step's right-hand side `n + suc m'`
--    is STUCK (n is open) — that is exactly why 2 is needed, and exactly
--    why the recursed-argument monotonicity was unreachable directly.
------------------------------------------------------------------------

commB : {Γ : Cx} (n m : RTm Γ) → RTy Γ
commB n m = IdN (plusTm m n) (plusTm n m)

⊢commMot : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} → Γ ⊢ n ∷ Nat →
           (Γ ▹ Nat) ⊢ty commB (w n) (var vz)
⊢commMot dn =
  ⊢tyIdN (⊢plus (⊢var here) (⊢wk dn)) (⊢plus (⊢wk dn) (⊢var here))

cmMot-at : {Γ : Cx} (n k : RTm Γ) →
           subTy (single k) (commB (w n) (var vz)) ≡ commB n k
cmMot-at n k =
  cong (λ z → IdN (plusTm k z) (plusTm z k)) (wk-single {v = k} n)

cmMot-s : {Γ : Cx} (n : RTm Γ) →
          subTy nrs (commB (w n) (var vz))
        ≡ commB (w (w n)) (nsuc (var (vs vz)))
cmMot-s n =
  cong (λ z → IdN (plusTm (nsuc (var (vs vz))) z) (plusTm z (nsuc (var (vs vz)))))
       (nrs-w n)

commTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
commTm n m =
  natrec (symN (plusTm n nzero) (plus0Tm n))
         (transN (nsuc (plusTm (var (vs vz)) (w (w n))))
                 (congS (plusTm (var (vs vz)) (w (w n))) (var vz))
                 (symN (plusTm (w (w n)) (nsuc (var (vs vz))))
                       (plusSTm (var (vs vz)) (w (w n)))))
         m

⊢comm : {Γ : Ctx} {n m : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ Nat → Γ ⊢ m ∷ Nat → Γ ⊢ commTm n m ∷ commB n m
⊢comm {n = n} {m = m} dn dm =
  ⊢-cast (cmMot-at n m) (⊢natrec (⊢commMot dn) zB sB dm)
  where
    zB = ⊢-cast (sym (cmMot-at n nzero))
           (⊢conv (⊢symN (⊢plus dn ⊢nzero) dn (⊢plus0 dn))
             (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Idˡ (natrec-zero _ _)) doneᵀ))))
    sB = ⊢-cast (sym (cmMot-s n))
           (⊢conv (⊢transN (⊢nsuc (⊢plus dm' dn''))
                           (⊢nsuc (⊢plus dn'' dm'))
                           (⊢plus dn'' (⊢nsuc dm'))
                           (⊢congS (⊢plus dm' dn'') (⊢plus dn'' dm') (⊢var here))
                           (⊢symN (⊢plus dn'' (⊢nsuc dm'))
                                  (⊢nsuc (⊢plus dn'' dm'))
                                  (⊢plusS dm' dn'')))
             (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Idˡ (natrec-suc _ _ _)) doneᵀ))))
      where
        dm'  = ⊢var (there here)
        dn'' = ⊢wk (⊢wk dn)

------------------------------------------------------------------------
-- ★★ TRANSPORTING A `Hom Nat` ALONG AN `Id`.
--
-- Two more `jsub`s, one per endpoint.  ⚠ The family is a `⌜Hom⌝` CODE and
-- the result comes out as `El (⌜Hom⌝ …)`, so `El-homNat` converts back —
-- the same code-indexing tax the `Id` kit pays above.
------------------------------------------------------------------------

homN : {Γ : Cx} (a b : RTm Γ) → El (⌜Hom⌝ ⌜Nat⌝ a b) ≅ᵀ Hom Nat a b
homN a b = red→≅ᵀ (El-homNat a b)

trHomˡ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
trHomˡ u p h = jsub (⌜Hom⌝ ⌜Nat⌝ (var vz) (w u)) p h

⊢trHomˡ : {Γ : Ctx} {a b u p h : RTm ⌊ Γ ⌋} →
          Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ u ∷ Nat →
          Γ ⊢ p ∷ IdN a b → Γ ⊢ h ∷ Hom Nat a u →
          Γ ⊢ trHomˡ u p h ∷ Hom Nat b u
⊢trHomˡ {a = a} {b = b} {u = u} da db du dp dh =
  ⊢conv (⊢-cast (cong (λ z → El (⌜Hom⌝ ⌜Nat⌝ b z)) (wk-single {v = b} u))
                (⊢jsub dd (natAsEl da) (natAsEl db) dp de))
        (homN b u)
  where
    dd = ⊢⌜Hom⌝ ⊢⌜Nat⌝ (⊢var here) (natAsEl (⊢wk du))
    de = ⊢-cast (sym (cong (λ z → El (⌜Hom⌝ ⌜Nat⌝ a z)) (wk-single {v = a} u)))
                (⊢conv dh (csymᵀ (homN a u)))

trHomʳ : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
trHomʳ t p h = jsub (⌜Hom⌝ ⌜Nat⌝ (w t) (var vz)) p h

⊢trHomʳ : {Γ : Ctx} {a b t p h : RTm ⌊ Γ ⌋} →
          Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ t ∷ Nat →
          Γ ⊢ p ∷ IdN a b → Γ ⊢ h ∷ Hom Nat t a →
          Γ ⊢ trHomʳ t p h ∷ Hom Nat t b
⊢trHomʳ {a = a} {b = b} {t = t} da db dt dp dh =
  ⊢conv (⊢-cast (cong (λ z → El (⌜Hom⌝ ⌜Nat⌝ z b)) (wk-single {v = b} t))
                (⊢jsub dd (natAsEl da) (natAsEl db) dp de))
        (homN t b)
  where
    dd = ⊢⌜Hom⌝ ⊢⌜Nat⌝ (natAsEl (⊢wk dt)) (⊢var here)
    de = ⊢-cast (sym (cong (λ z → El (⌜Hom⌝ ⌜Nat⌝ z a)) (wk-single {v = a} t)))
                (⊢conv dh (csymᵀ (homN t a)))

------------------------------------------------------------------------
-- ★★★ THE PAYOFF: `+` IS MONOTONE IN ITS RECURSED ARGUMENT TOO.
--
--   `SpikeArith.⊢plus-mono` gives `c + x < c + y`; commutativity moves
--   both endpoints across, and `x + c < y + c` is what gcd's first branch
--   needs.  ⚠ THIS IS THE LEMMA THAT WAS UNREACHABLE DIRECTLY — see
--   `NbEPDirDBLibArith`'s header for why (`plusTm` is stuck in its first
--   argument and `<` is not an inductive family).
------------------------------------------------------------------------

plusMonoLB : {Γ : Cx} (x y c : RTm Γ) → RTy Γ
plusMonoLB x y c = Hom Nat (nsuc (plusTm x c)) (plusTm y c)

plusMonoLTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
plusMonoLTm x y c p =
  trHomʳ (nsuc (plusTm x c)) (commTm y c)
    (trHomˡ (plusTm c y) (congS (plusTm c x) (commTm x c))
      (plusMonoTm p c))

⊢plus-mono-l : {Γ : Ctx} {x y c p : RTm ⌊ Γ ⌋} →
               Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat → Γ ⊢ c ∷ Nat →
               Γ ⊢ p ∷ Hom Nat (nsuc x) y →
               Γ ⊢ plusMonoLTm x y c p ∷ plusMonoLB x y c
⊢plus-mono-l {x = x} {y = y} {c = c} dx dy dc dp =
  ⊢trHomʳ (⊢plus dc dy) (⊢plus dy dc) (⊢nsuc (⊢plus dx dc))
          (⊢comm dy dc)
          (⊢trHomˡ (⊢nsuc (⊢plus dc dx)) (⊢nsuc (⊢plus dx dc)) (⊢plus dc dy)
                   (⊢congS (⊢plus dc dx) (⊢plus dx dc) (⊢comm dx dc))
                   (⊢plus-mono dx dy dc dp))

------------------------------------------------------------------------
-- ★★★ SUBSTITUTION-NATURALITY FOR THE ARITHMETIC TEMPLATES.
--
-- ⚠ WHY THESE EXIST.  `HANDOFF-2026-08-15` recorded that "substitution
--   naturality for every arithmetic template" was NOT on gap A's path.
--   That was true of the LIBRARY half and false of the last mile: gcd's
--   recursive equation has to TYPE the certificate the reduction hands
--   over, and that certificate is `plusMonoLTm …` under eight
--   substitutions.  `subTm σ (plusMonoLTm x y c p)` is NOT
--   `plusMonoLTm (subTm σ x) …` definitionally, because `plusMonoLTm`
--   unfolds through `trHomʳ`/`trHomˡ`/`congS`/`commTm`, each of which hides
--   a `w`, and `subTm (extS σ) (w t)` vs `w (subTm σ t)` is `sub-w`.
--
-- ★ Each one is ONE `sub-w` (or `sub-w²`) under a `cong`.  They are
--   library lemmas: general, reusable, and paid once.
------------------------------------------------------------------------

reflN-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (a : RTm Γ) →
            subTm σ (reflN a) ≡ reflN (subTm σ a)
reflN-sub a = refl

congS-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (a p : RTm Γ) →
            subTm σ (congS a p) ≡ congS (subTm σ a) (subTm σ p)
congS-sub {σ = σ} a p =
  cong (λ u → jsub (⌜Id⌝ ⌜Nat⌝ (nsuc u) (nsuc (var vz)))
                   (subTm σ p) (reflN (nsuc (subTm σ a))))
       (sub-w {σ = σ} a)

symN-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (a p : RTm Γ) →
           subTm σ (symN a p) ≡ symN (subTm σ a) (subTm σ p)
symN-sub {σ = σ} a p =
  cong (λ u → jsub (⌜Id⌝ ⌜Nat⌝ (var vz) u) (subTm σ p) (reflN (subTm σ a)))
       (sub-w {σ = σ} a)

transN-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (a p q : RTm Γ) →
             subTm σ (transN a p q) ≡ transN (subTm σ a) (subTm σ p) (subTm σ q)
transN-sub {σ = σ} a p q =
  cong (λ u → jsub (⌜Id⌝ ⌜Nat⌝ u (var vz)) (subTm σ q) (subTm σ p))
       (sub-w {σ = σ} a)

trHomˡ-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (u p h : RTm Γ) →
             subTm σ (trHomˡ u p h) ≡ trHomˡ (subTm σ u) (subTm σ p) (subTm σ h)
trHomˡ-sub {σ = σ} u p h =
  cong (λ z → jsub (⌜Hom⌝ ⌜Nat⌝ (var vz) z) (subTm σ p) (subTm σ h))
       (sub-w {σ = σ} u)

trHomʳ-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (t p h : RTm Γ) →
             subTm σ (trHomʳ t p h) ≡ trHomʳ (subTm σ t) (subTm σ p) (subTm σ h)
trHomʳ-sub {σ = σ} t p h =
  cong (λ z → jsub (⌜Hom⌝ ⌜Nat⌝ z (var vz)) (subTm σ p) (subTm σ h))
       (sub-w {σ = σ} t)

plus0Tm-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (m : RTm Γ) →
              subTm σ (plus0Tm m) ≡ plus0Tm (subTm σ m)
plus0Tm-sub {σ = σ} m =
  cong (λ s → natrec (reflN nzero) s (subTm σ m))
       (congS-sub {σ = extS (extS σ)} (plusTm (var (vs vz)) nzero) (var vz))

plusSTm-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (n m : RTm Γ) →
              subTm σ (plusSTm n m) ≡ plusSTm (subTm σ n) (subTm σ m)
plusSTm-sub {σ = σ} n m =
  cong (λ s → natrec (reflN (nsuc (subTm σ n))) s (subTm σ m))
       (trans (congS-sub {σ = extS (extS σ)}
                         (plusTm (var (vs vz)) (nsuc (w (w n)))) (var vz))
              (cong (λ u → congS (plusTm (var (vs vz)) (nsuc u)) (var vz))
                    (sub-w² {σ = σ} n)))

-- ⚠ the big one: `commTm`'s successor branch carries `w (w n)` FOUR times,
--   through a `transN`, a `congS` and two `symN`s.
commTm-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (n m : RTm Γ) →
             subTm σ (commTm n m) ≡ commTm (subTm σ n) (subTm σ m)
commTm-sub {σ = σ} n m = cong₂ⁿ zEq (trans sEq₁ (rewriteN (sub-w² {σ = σ} n)))
  where
    -- the successor branch's `w (w n)`, still under the substitution
    N2 : RTm _
    N2 = subTm (extS (extS σ)) (w (w n))

    cong₂ⁿ : {z z' : RTm _} {s s' : RTm _} → z ≡ z' → s ≡ s' →
             natrec z s (subTm σ m) ≡ natrec z' s' (subTm σ m)
    cong₂ⁿ refl refl = refl

    congT : {a a' p p' q q' : RTm _} → a ≡ a' → p ≡ p' → q ≡ q' →
            transN a p q ≡ transN a' p' q'
    congT refl refl refl = refl

    zEq = trans (symN-sub {σ = σ} (plusTm n nzero) (plus0Tm n))
                (cong (symN (plusTm (subTm σ n) nzero)) (plus0Tm-sub {σ = σ} n))

    -- ⚠ STAGE 1: distribute the substitution into EVERY template.  Doing
    --   only `transN-sub` leaves `congS`/`symN`/`plusSTm` still wrapped, and
    --   the rewrite in stage 2 then has nothing to match.
    sEq₁ = trans (transN-sub {σ = extS (extS σ)}
                             (nsuc (plusTm (var (vs vz)) (w (w n))))
                             (congS (plusTm (var (vs vz)) (w (w n))) (var vz))
                             (symN (plusTm (w (w n)) (nsuc (var (vs vz))))
                                   (plusSTm (var (vs vz)) (w (w n)))))
                 (congT refl
                        (congS-sub {σ = extS (extS σ)}
                                   (plusTm (var (vs vz)) (w (w n))) (var vz))
                        (trans (symN-sub {σ = extS (extS σ)}
                                         (plusTm (w (w n)) (nsuc (var (vs vz))))
                                         (plusSTm (var (vs vz)) (w (w n))))
                               (cong (symN (plusTm N2 (nsuc (var (vs vz)))))
                                     (plusSTm-sub {σ = extS (extS σ)}
                                                  (var (vs vz)) (w (w n))))))

    -- STAGE 2: now `N2` occurs four times and one rewrite closes it.
    rewriteN : {u : RTm _} → N2 ≡ u →
               transN (nsuc (plusTm (var (vs vz)) N2))
                      (congS (plusTm (var (vs vz)) N2) (var vz))
                      (symN (plusTm N2 (nsuc (var (vs vz))))
                            (plusSTm (var (vs vz)) N2))
             ≡ transN (nsuc (plusTm (var (vs vz)) u))
                      (congS (plusTm (var (vs vz)) u) (var vz))
                      (symN (plusTm u (nsuc (var (vs vz))))
                            (plusSTm (var (vs vz)) u))
    rewriteN refl = refl

plusMonoTm-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (p c : RTm Γ) →
                 subTm σ (plusMonoTm p c) ≡ plusMonoTm (subTm σ p) (subTm σ c)
plusMonoTm-sub p c = refl

-- ★★★ …and the one gap A actually needs.
plusMonoLTm-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (x y c p : RTm Γ) →
                  subTm σ (plusMonoLTm x y c p)
                ≡ plusMonoLTm (subTm σ x) (subTm σ y) (subTm σ c) (subTm σ p)
plusMonoLTm-sub {σ = σ} x y c p =
  trans (trHomʳ-sub {σ = σ} (nsuc (plusTm x c)) (commTm y c)
                    (trHomˡ (plusTm c y) (congS (plusTm c x) (commTm x c))
                            (plusMonoTm p c)))
        (cong₂ᵗ (commTm-sub {σ = σ} y c)
                (trans (trHomˡ-sub {σ = σ} (plusTm c y)
                                   (congS (plusTm c x) (commTm x c))
                                   (plusMonoTm p c))
                       (cong (λ z → trHomˡ (plusTm (subTm σ c) (subTm σ y)) z
                                           (plusMonoTm (subTm σ p) (subTm σ c)))
                             (trans (congS-sub {σ = σ} (plusTm c x) (commTm x c))
                                    (cong (congS (plusTm (subTm σ c) (subTm σ x)))
                                          (commTm-sub {σ = σ} x c))))))
  where
    cong₂ᵗ : {u u' h h' : RTm _} → u ≡ u' → h ≡ h' →
             trHomʳ (nsuc (plusTm (subTm σ x) (subTm σ c))) u h
           ≡ trHomʳ (nsuc (plusTm (subTm σ x) (subTm σ c))) u' h'
    cong₂ᵗ refl refl = refl
