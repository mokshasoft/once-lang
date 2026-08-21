------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — THE ARITHMETIC GAP B's LAYER 2 NEEDS.
--
-- ★ WHY A NEW MODULE.  `…LibArithComm` has `m + 0`, `m + suc n` and
--   commutativity; `…LibMul` has `*` and its two computation rules.
--   Neither has ASSOCIATIVITY, and nothing anywhere has right
--   distributivity — which is what the divisibility spec turns on:
--
--       d ∣ x  →  d ∣ y  →  d ∣ (x + y)
--
--   unfolds to `x ≡ j * d`, `y ≡ k * d` ⊢ `x + y ≡ (j + k) * d`, i.e.
--   exactly `(j + k) * d ≡ j * d + k * d`.
--
-- ⚠ AND `dvd-plus` IS NOT OPTIONAL BOOKKEEPING — IT IS THE WHOLE REASON
--   THE MOTIVE MUST BE A CONJUNCTION.  gcd's `a > b` branch recurses at
--   `(a ∸ b , b)`, so the IH gives `d ∣ (a ∸ b)`; reaching `d ∣ a` needs
--   `a ≡ (a ∸ b) + b` AND the second conjunct `d ∣ b`.  Neither
--   `gcd ∣ a` nor `gcd ∣ b` is provable alone by this recursion.
--
-- ★ EVERY PROOF HERE IS INTERNAL — a `natrec` over the object language,
--   with the motive an `IdN`.  The house pattern from `…LibArithComm`:
--   ambient arguments make the motive bound-explicit, so each pays its own
--   `mot-at`/`mot-s` peel.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibDvdArith where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs
        ; RTy; El; Id; Nat
        ; RTm; var; nzero; nsuc; natrec; idrefl; jsub; ⌜Id⌝; ⌜Nat⌝
        ; pair; fst; snd
        ; subTy; subTm; renTy; renTm; Ren; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢idrefl; ⊢jsub; ⊢⌜Id⌝; ⊢⌜Nat⌝
        ; ty-Id; ty-El; ty-Nat
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; El-⌜Id⌝
        ; ξ-Idˡ; ξ-Idʳ; ξ-nsuc; ξ-natrecⁿ; natrec-zero; natrec-suc
        ; _⟶*_; step; done )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-natrecⁿ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; nrs-w; ren-sub; sub-w )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibStrong using ( natAsEl )
open import poc.OCP0009.NbEPDirDBLibPair using ( asN )
open import poc.OCP0009.NbEPDirDBLibArithComm
  using ( IdN; ⊢tyIdN; elIdN; reflN; ⊢reflN; congS; ⊢congS
        ; symN; ⊢symN; transN; ⊢transN )
open import poc.OCP0009.NbEPDirDBLibMul using ( mulTm; ⊢mul; mulTm-sub )
open import poc.OCP0009.NbEPDirDBLibDvd
  using ( dvdT; dvd-intro; dvd-wit; dvd-eq )

------------------------------------------------------------------------
-- ★ 0.  CONGRUENCE IN `+`'s SECOND SLOT.
--
-- ⚠ `congS` covers `nsuc`; nothing covers `+`.  The step of
--   distributivity rewrites UNDER `d + ·`, so it is needed there and
--   nowhere earlier.  Same `jsub` shape as `congS`, other family.
------------------------------------------------------------------------

congPR : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
congPR d x p =
  jsub (⌜Id⌝ ⌜Nat⌝ (w (plusTm d x)) (plusTm (w d) (var vz)))
       p (reflN (plusTm d x))

⊢congPR : {Γ : Ctx} {d x y p : RTm ⌊ Γ ⌋} →
          Γ ⊢ d ∷ Nat → Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat →
          Γ ⊢ p ∷ IdN x y →
          Γ ⊢ congPR d x p ∷ IdN (plusTm d x) (plusTm d y)
⊢congPR {d = d} {x = x} {y = y} dd dx dy dp =
  ⊢conv (⊢-cast famAt (⊢jsub dfam (natAsEl dx) (natAsEl dy) dp de))
        (elIdN (plusTm d x) (plusTm d y))
  where
    dfam = ⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢wk (⊢plus dd dx)))
                        (natAsEl (⊢plus (⊢wk dd) (asN (⊢var here))))

    -- the family at an ARBITRARY endpoint — one `wk-single` per slot
    peel : (v : RTm ⌊ _ ⌋) →
           subTm (single v) (⌜Id⌝ ⌜Nat⌝ (w (plusTm d x)) (plusTm (w d) (var vz)))
         ≡ ⌜Id⌝ ⌜Nat⌝ (plusTm d x) (plusTm d v)
    peel v = cong₂ (λ u t → ⌜Id⌝ ⌜Nat⌝ u (plusTm t v))
                   (wk-single {v = v} (plusTm d x))
                   (wk-single {v = v} d)

    famAt = cong El (peel y)
    de    = ⊢-cast (sym (cong El (peel x)))
                   (⊢conv (⊢reflN (⊢plus dd dx))
                          (csymᵀ (elIdN (plusTm d x) (plusTm d x))))

------------------------------------------------------------------------
-- ★★ 1.  ASSOCIATIVITY — `(a + b) + c = a + (b + c)`, by `natrec` on `a`.
--
-- ⭐ BOTH BRANCHES ARE ONE REDUCTION EACH ON THE RIGHT AND TWO ON THE
--   LEFT, and the asymmetry is structural: the left has `a` under TWO
--   `plusTm`s, so the inner one has to fire first (`ξ-natrecⁿ`) before the
--   outer can.  Nothing here needs `+ 0` or commutativity.
------------------------------------------------------------------------

assocB : {Γ : Cx} (b c a : RTm Γ) → RTy Γ
assocB b c a = IdN (plusTm (plusTm a b) c) (plusTm a (plusTm b c))

⊢assocMot : {Γ : Ctx} {b c : RTm ⌊ Γ ⌋} →
            Γ ⊢ b ∷ Nat → Γ ⊢ c ∷ Nat →
            (Γ ▹ Nat) ⊢ty assocB (w b) (w c) (var vz)
⊢assocMot db dc =
  ⊢tyIdN (⊢plus (⊢plus (⊢var here) (⊢wk db)) (⊢wk dc))
         (⊢plus (⊢var here) (⊢plus (⊢wk db) (⊢wk dc)))

asMot-at : {Γ : Cx} (b c k : RTm Γ) →
           subTy (single k) (assocB (w b) (w c) (var vz)) ≡ assocB b c k
asMot-at b c k =
  cong₂ (λ u v → IdN (plusTm (plusTm k u) v) (plusTm k (plusTm u v)))
        (wk-single {v = k} b) (wk-single {v = k} c)

asMot-s : {Γ : Cx} (b c : RTm Γ) →
          subTy nrs (assocB (w b) (w c) (var vz))
        ≡ assocB (w (w b)) (w (w c)) (nsuc (var (vs vz)))
asMot-s b c =
  cong₂ (λ u v → IdN (plusTm (plusTm (nsuc (var (vs vz))) u) v)
                     (plusTm (nsuc (var (vs vz))) (plusTm u v)))
        (nrs-w b) (nrs-w c)

assocTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
assocTm b c a =
  natrec (reflN (plusTm b c))
         (congS (plusTm (plusTm (var (vs vz)) (w (w b))) (w (w c))) (var vz))
         a

⊢assoc : {Γ : Ctx} {a b c : RTm ⌊ Γ ⌋} →
         Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ c ∷ Nat →
         Γ ⊢ assocTm b c a ∷ assocB b c a
⊢assoc {a = a} {b = b} {c = c} da db dc =
  ⊢-cast (asMot-at b c a) (⊢natrec (⊢assocMot db dc) zB sB da)
  where
    zB = ⊢-cast (sym (asMot-at b c nzero))
           (⊢conv (⊢reflN (⊢plus db dc))
             (csymᵀ (ctrnᵀ
               (red→≅ᵀ (stepᵀ (ξ-Idˡ (ξ-natrecⁿ (natrec-zero _ _))) doneᵀ))
               (red→≅ᵀ (stepᵀ (ξ-Idʳ (natrec-zero _ _)) doneᵀ)))))

    sB = ⊢-cast (sym (asMot-s b c))
           (⊢conv (⊢congS (⊢plus (⊢plus dA dB) dC)
                          (⊢plus dA (⊢plus dB dC))
                          (⊢var here))
             (csymᵀ (ctrnᵀ
               (red→≅ᵀ (stepᵀ (ξ-Idˡ (ξ-natrecⁿ (natrec-suc _ _ _)))
                        (stepᵀ (ξ-Idˡ (natrec-suc _ _ _)) doneᵀ)))
               (red→≅ᵀ (stepᵀ (ξ-Idʳ (natrec-suc _ _ _)) doneᵀ)))))
      where
        dA = ⊢var (there here)
        dB = ⊢wk (⊢wk db)
        dC = ⊢wk (⊢wk dc)

------------------------------------------------------------------------
-- ★ 0b.  …AND IN `+`'s FIRST SLOT.  `dvd-plus` rewrites BOTH summands,
--   so both congruences are needed; distributivity needs only the second.
------------------------------------------------------------------------

congPL : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
congPL y x p =
  jsub (⌜Id⌝ ⌜Nat⌝ (w (plusTm x y)) (plusTm (var vz) (w y)))
       p (reflN (plusTm x y))

⊢congPL : {Γ : Ctx} {y x x' p : RTm ⌊ Γ ⌋} →
          Γ ⊢ y ∷ Nat → Γ ⊢ x ∷ Nat → Γ ⊢ x' ∷ Nat →
          Γ ⊢ p ∷ IdN x x' →
          Γ ⊢ congPL y x p ∷ IdN (plusTm x y) (plusTm x' y)
⊢congPL {y = y} {x = x} {x' = x'} dy dx dx' dp =
  ⊢conv (⊢-cast (cong El (peel x')) (⊢jsub dfam (natAsEl dx) (natAsEl dx') dp de))
        (elIdN (plusTm x y) (plusTm x' y))
  where
    dfam = ⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢wk (⊢plus dx dy)))
                        (natAsEl (⊢plus (asN (⊢var here)) (⊢wk dy)))

    peel : (v : RTm ⌊ _ ⌋) →
           subTm (single v) (⌜Id⌝ ⌜Nat⌝ (w (plusTm x y)) (plusTm (var vz) (w y)))
         ≡ ⌜Id⌝ ⌜Nat⌝ (plusTm x y) (plusTm v y)
    peel v = cong₂ (λ u t → ⌜Id⌝ ⌜Nat⌝ u (plusTm v t))
                   (wk-single {v = v} (plusTm x y))
                   (wk-single {v = v} y)

    de = ⊢-cast (sym (cong El (peel x)))
                (⊢conv (⊢reflN (⊢plus dx dy))
                       (csymᵀ (elIdN (plusTm x y) (plusTm x y))))

------------------------------------------------------------------------
-- ★★★ 2.  RIGHT DISTRIBUTIVITY — `(j + k) * d = j * d + k * d`, by
--   `natrec` on `j`.
--
-- ⭐ THE STEP IS WHERE ASSOCIATIVITY IS SPENT, and it is the only place.
--   After both sides reduce the goal is
--
--       d + ((j + k) * d)   ≡   (d + j * d) + k * d
--
--   The IH rewrites under `d + ·` (`congPR`) and associativity closes the
--   bracket.  ⚠ Note the reduction counts differ per side and per branch —
--   `mulTm` and `plusTm` both recurse on their FIRST argument, so which of
--   the two fires first is forced by which one holds the scrutinee.
------------------------------------------------------------------------

distB : {Γ : Cx} (k d j : RTm Γ) → RTy Γ
distB k d j = IdN (mulTm (plusTm j k) d) (plusTm (mulTm j d) (mulTm k d))

⊢distMot : {Γ : Ctx} {k d : RTm ⌊ Γ ⌋} →
           Γ ⊢ k ∷ Nat → Γ ⊢ d ∷ Nat →
           (Γ ▹ Nat) ⊢ty distB (w k) (w d) (var vz)
⊢distMot dk dd =
  ⊢tyIdN (⊢mul (⊢plus (⊢var here) (⊢wk dk)) (⊢wk dd))
         (⊢plus (⊢mul (⊢var here) (⊢wk dd)) (⊢mul (⊢wk dk) (⊢wk dd)))

-- ⚠ `plusTm` DISTRIBUTES THROUGH `subTm` DEFINITIONALLY and `mulTm` DOES
--   NOT.  `plusTm m n = natrec n (nsuc (var vz)) m` keeps `n` at depth 0,
--   so a substitution just walks in; `mulTm m n = natrec nzero
--   (plusTm (w (w n)) (var vz)) m` buries `n` under TWO weakenings, and
--   `mulTm-sub` is what pushes past them.  ⇒ the `assocB` peels above are
--   plain `wk-single`s; these are not.  (Cost of missing it: one round.)
dsMot-at : {Γ : Cx} (k d j : RTm Γ) →
           subTy (single j) (distB (w k) (w d) (var vz)) ≡ distB k d j
dsMot-at k d j =
  cong₂ IdN
    (trans (mulTm-sub {σ = single j} (plusTm (var vz) (w k)) (w d))
           (cong₂ (λ u v → mulTm (plusTm j u) v)
                  (wk-single {v = j} k) (wk-single {v = j} d)))
    (cong₂ plusTm
      (trans (mulTm-sub {σ = single j} (var vz) (w d))
             (cong (mulTm j) (wk-single {v = j} d)))
      (trans (mulTm-sub {σ = single j} (w k) (w d))
             (cong₂ mulTm (wk-single {v = j} k) (wk-single {v = j} d))))

dsMot-s : {Γ : Cx} (k d : RTm Γ) →
          subTy nrs (distB (w k) (w d) (var vz))
        ≡ distB (w (w k)) (w (w d)) (nsuc (var (vs vz)))
dsMot-s k d =
  cong₂ IdN
    (trans (mulTm-sub {σ = nrs} (plusTm (var vz) (w k)) (w d))
           (cong₂ (λ u v → mulTm (plusTm (nsuc (var (vs vz))) u) v)
                  (nrs-w k) (nrs-w d)))
    (cong₂ plusTm
      (trans (mulTm-sub {σ = nrs} (var vz) (w d))
             (cong (mulTm (nsuc (var (vs vz)))) (nrs-w d)))
      (trans (mulTm-sub {σ = nrs} (w k) (w d))
             (cong₂ mulTm (nrs-w k) (nrs-w d))))

-- ★★ `mulTm`'s SUCCESSOR COMPUTATION RULE.  ⚠ `…LibMul` has `mul-zero`
--   and NOT this one, and the gap is real: `mul (suc m) n ⟶ n + m * n`
--   holds by `natrec`'s own reduction, but the REDUCT is not syntactically
--   `plusTm n (mulTm m n)` — `n` sits under the two binders `natrec-suc`
--   introduces, so the substitution has to be pushed past both.
--   ⭐ CONTRAST `plusTm`: its step branch is `nsuc (var vz)`, which mentions
--   nothing ambient, so ITS successor rule IS definitional and no lemma
--   exists or is needed.  That asymmetry is why `assocB` needed no peels
--   and `distB` needs three.
--
-- ⇒ CONSOLIDATION DEBT: `mul-suc` and `mulTm-ren` belong in `…LibMul`,
--   beside `mul-zero` and `mulTm-sub`.  Kept here to leave that module's
--   clients untouched mid-task.
mul-suc : {Γ : Cx} (m n : RTm Γ) → mulTm (nsuc m) n ⟶* plusTm n (mulTm m n)
mul-suc m n =
  subst (λ t → mulTm (nsuc m) n ⟶* t) peel
        (step (natrec-suc nzero (plusTm (w (w n)) (var vz)) m) done)
  where
    inner : subTm (extS (single m)) (w (w n)) ≡ w n
    inner = trans (sub-w {σ = single m} (w n)) (cong w (wk-single {v = m} n))

    peel = trans (cong (λ t → subTm (single (mulTm m n))
                                (natrec (var vz) (nsuc (var vz)) t))
                       inner)
                 (cong (λ t → natrec (mulTm m n) (nsuc (var vz)) t)
                       (wk-single {v = mulTm m n} n))

-- ⚠ AND `renTm` DOES NOT DISTRIBUTE THROUGH `mulTm` EITHER, for the same
--   reason — so the IH VARIABLE's type needs its own peel.  `assocB` got
--   away without one because `plusTm` renames definitionally; the moment a
--   `mulTm` is in the motive, `⊢var here` no longer has the shape the
--   branch wants.  ⭐ A renaming IS a substitution (`ren-sub`), so
--   `mulTm-sub` supplies this too — no second induction.
mulTm-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (m n : RTm Γ) →
            renTm ρ (mulTm m n) ≡ mulTm (renTm ρ m) (renTm ρ n)
mulTm-ren {ρ = ρ} m n =
  trans (ren-sub (mulTm m n))
    (trans (mulTm-sub {σ = λ v → var (ρ v)} m n)
           (cong₂ mulTm (sym (ren-sub m)) (sym (ren-sub n))))

dsMot-wk : {Γ : Cx} (k d : RTm Γ) →
           renTy vs (distB (w k) (w d) (var vz))
         ≡ distB (w (w k)) (w (w d)) (var (vs vz))
dsMot-wk k d =
  cong₂ IdN
    (mulTm-ren {ρ = vs} (plusTm (var vz) (w k)) (w d))
    (cong₂ plusTm (mulTm-ren {ρ = vs} (var vz) (w d))
                  (mulTm-ren {ρ = vs} (w k) (w d)))

distTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
distTm k d j =
  natrec (reflN (mulTm k d)) sTm j
  where
    J  = var (vs vz)
    K  = w (w k)
    D  = w (w d)
    sTm = transN (plusTm D (mulTm (plusTm J K) D))
                 (congPR D (mulTm (plusTm J K) D) (var vz))
                 (symN (plusTm (plusTm D (mulTm J D)) (mulTm K D))
                       (assocTm (mulTm J D) (mulTm K D) D))

⊢dist : {Γ : Ctx} {j k d : RTm ⌊ Γ ⌋} →
        Γ ⊢ j ∷ Nat → Γ ⊢ k ∷ Nat → Γ ⊢ d ∷ Nat →
        Γ ⊢ distTm k d j ∷ distB k d j
⊢dist {j = j} {k = k} {d = d} dj dk dd =
  ⊢-cast (dsMot-at k d j) (⊢natrec (⊢distMot dk dd) zB sB dj)
  where
    zB = ⊢-cast (sym (dsMot-at k d nzero))
           (⊢conv (⊢reflN (⊢mul dk dd))
             (csymᵀ (ctrnᵀ
               (red→≅ᵀ (stepᵀ (ξ-Idˡ (ξ-natrecⁿ (natrec-zero _ _))) doneᵀ))
               (red→≅ᵀ (stepᵀ (ξ-Idʳ (ξ-natrecⁿ (natrec-zero _ _)))
                        (stepᵀ (ξ-Idʳ (natrec-zero _ _)) doneᵀ))))))

    sB = ⊢-cast (sym (dsMot-s k d))
           (⊢conv (⊢transN dL dMid dR
                     (⊢congPR dD dX dY dIH)
                     (⊢symN (⊢plus (⊢plus dD (⊢mul dJ dD)) (⊢mul dK dD)) dMid
                            (⊢assoc dD (⊢mul dJ dD) (⊢mul dK dD))))
             (csymᵀ (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Idˡ redL))
                           (red→≅ᵀ (⟶ᵀ*-Idʳ redR)))))
      where
        dIH = ⊢-cast (dsMot-wk k d) (⊢var here)

        -- ⚠ `⟶*`-VALUED, NOT A ξ-CHAIN OF SINGLE STEPS.  `mul-suc` is a
        --   `⟶*` because its reduct needs a peel, so the whole side has to
        --   be assembled at `⟶*` and lifted once by `⟶ᵀ*-Id·`.
        redL = ⟶*-trans (step (ξ-natrecⁿ (natrec-suc _ _ _)) done)
                        (mul-suc (plusTm (var (vs vz)) (w (w k))) (w (w d)))
        redR = ⟶*-natrecⁿ (mul-suc (var (vs vz)) (w (w d)))
        dJ = ⊢var (there here)
        dK = ⊢wk (⊢wk dk)
        dD = ⊢wk (⊢wk dd)
        dX = ⊢mul (⊢plus dJ dK) dD
        dY = ⊢plus (⊢mul dJ dD) (⊢mul dK dD)
        dL   = ⊢plus dD dX
        dMid = ⊢plus dD dY
        dR   = ⊢plus (⊢plus dD (⊢mul dJ dD)) (⊢mul dK dD)

------------------------------------------------------------------------
-- ★★★★★ 3.  DIVISIBILITY IS CLOSED UNDER `+`.  GAP B's WORKHORSE.
--
--   d ∣ x  and  d ∣ y   ⟹   d ∣ (x + y)
--
-- ★ The witness is the SUM of the two witnesses, and the equation is
--   `congPL` then `congPR` then distributivity backwards — three rewrites
--   and no induction, because the induction is `⊢dist`'s.
------------------------------------------------------------------------

dvdSumEq : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
dvdSumEq d x y hx hy =
  transN (plusTm x y)
    (transN (plusTm x y)
       (congPL y x (snd hx))
       (congPR (mulTm (fst hx) d) y (snd hy)))
    (symN (mulTm (plusTm (fst hx) (fst hy)) d)
          (distTm (fst hy) d (fst hx)))

dvdSum : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
dvdSum d x y hx hy =
  pair (plusTm (fst hx) (fst hy)) (dvdSumEq d x y hx hy)

⊢dvd-plus : {Γ : Ctx} {d x y hx hy : RTm ⌊ Γ ⌋} →
            Γ ⊢ d ∷ Nat → Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat →
            Γ ⊢ hx ∷ dvdT d x → Γ ⊢ hy ∷ dvdT d y →
            Γ ⊢ dvdSum d x y hx hy ∷ dvdT d (plusTm x y)
⊢dvd-plus {d = d} {x = x} {y = y} {hx = hx} {hy = hy} dd dx dy dhx dhy =
  dvd-intro dd (⊢plus dx dy) (⊢plus djx djy) eq
  where
    djx = dvd-wit dhx
    djy = dvd-wit dhy

    dMx = ⊢mul djx dd
    dMy = ⊢mul djy dd

    dA  = ⊢plus dx dy
    dB  = ⊢plus dMx dy
    dC  = ⊢plus dMx dMy
    dD  = ⊢mul (⊢plus djx djy) dd

    t1  = ⊢congPL dy dx dMx (dvd-eq dhx)
    t2  = ⊢congPR dMx dy dMy (dvd-eq dhy)
    t3  = ⊢symN dD dC (⊢dist djx djy dd)

    eq  = ⊢transN dA dC dD (⊢transN dA dB dC t1 t2) t3
