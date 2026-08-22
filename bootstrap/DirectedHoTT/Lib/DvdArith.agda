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
module DirectedHoTT.Lib.DvdArith where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs
        ; RTy; El; Id; Nat; U; Unit; base; Π; lam; app; ⌜Unit⌝; ⌜base⌝; unit
        ; ⌜Σ⌝; Sub
        ; RTm; var; nzero; nsuc; natrec; idrefl; jsub; ⌜Id⌝; ⌜Nat⌝
        ; pair; fst; snd; absurd
        ; subTy; subTm; renTy; renTm; Ren; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢idrefl; ⊢jsub; ⊢⌜Id⌝; ⊢⌜Nat⌝
        ; ty-Id; ty-El; ty-Nat; ty-U; ty-Π
        ; ⊢⌜Unit⌝; ⊢⌜base⌝; ⊢unit; ⊢absurd; ⊢lam; ⊢app; El-⌜Unit⌝; El-⌜base⌝; ξ-El
        ; ⊢⌜Σ⌝; ⊢pair; ⊢fst; ⊢snd; El-⌜Σ⌝; El-⌜Nat⌝; ξ-Σˡ; ξ-Σʳ
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; El-⌜Id⌝
        ; ξ-Idˡ; ξ-Idʳ; ξ-nsuc; ξ-natrecⁿ; natrec-zero; natrec-suc
        ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; ξ-⌜Id⌝ʳ; ξ-⌜Id⌝ˡ
        ; _⟶*_; step; done; wk-single )
open import DirectedHoTT.Metatheory.Injectivity
  using ( red→≅ᵀ; stepᵀ; doneᵀ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ; _⟶ᵀ*_; ⟶ᵀ*-El )
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶*-trans; ⟶*-natrecⁿ; ⟶*-natrecᶻ; ⟶*-natrecˢ; ⟶*-ren )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Wk
  using ( w; nrs-w; ren-sub; sub-w; cong₃; ren-w²; ren-w³; ren-w )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Strong using ( natAsEl; elAsNat )
open import DirectedHoTT.Lib.Pair using ( asN )
open import DirectedHoTT.Lib.ArithComm
  using ( IdN; ⊢tyIdN; elIdN; reflN; ⊢reflN; congS; ⊢congS
        ; symN; ⊢symN; transN; ⊢transN
        ; plus0B; plus0Tm; ⊢plus0; plusSB; plusSTm; ⊢plusS )
open import DirectedHoTT.Lib.Mul
  using ( mulTm; ⊢mul; mulTm-sub; mul-zero; mul-suc; mulTm-ren )
open import DirectedHoTT.Lib.Dvd
  using ( dvdT; dvd-intro; dvd-wit; dvd-eq; dvdCode; ⊢dvdCode )
open import DirectedHoTT.Lib.Monus
  using ( predTm; monusTm; ⊢pred; ⊢monus; pred-suc; monus-zero; monus-suc )

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
-- (`mul-suc`/`mulTm-ren` moved to `…LibMul`, beside `mul-zero` and
--  `mulTm-sub`.  `mul-zero`/`mul-suc` are a PAIR and were split across
--  two modules; nothing in either is divisibility content.)

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

------------------------------------------------------------------------
-- ★ 4.  CONGRUENCE FOR `pred`.  Same `jsub` shape again; the monus
--   lemmas below both rewrite under a `predTm`.
--
-- ⭐ `monusTm m n = natrec m (predTm (var vz)) n` recurses on its SECOND
--   argument and keeps `m` at depth 0, so — unlike `mulTm` — it peels
--   through `subTm`/`renTm` DEFINITIONALLY.  Everything below is therefore
--   free of `-sub`/`-ren` bookkeeping.  ⚠ `predTm (nsuc n)` is still NOT
--   definitionally `n` (`pred-suc` carries the `wk-single`).
------------------------------------------------------------------------

congPd : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
congPd x p =
  jsub (⌜Id⌝ ⌜Nat⌝ (w (predTm x)) (predTm (var vz))) p (reflN (predTm x))

⊢congPd : {Γ : Ctx} {x y p : RTm ⌊ Γ ⌋} →
          Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat → Γ ⊢ p ∷ IdN x y →
          Γ ⊢ congPd x p ∷ IdN (predTm x) (predTm y)
⊢congPd {x = x} {y = y} dx dy dp =
  ⊢conv (⊢-cast (cong El (peel y)) (⊢jsub dfam (natAsEl dx) (natAsEl dy) dp de))
        (elIdN (predTm x) (predTm y))
  where
    dfam = ⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl (⊢wk (⊢pred dx)))
                        (natAsEl (⊢pred (asN (⊢var here))))

    peel : (v : RTm ⌊ _ ⌋) →
           subTm (single v) (⌜Id⌝ ⌜Nat⌝ (w (predTm x)) (predTm (var vz)))
         ≡ ⌜Id⌝ ⌜Nat⌝ (predTm x) (predTm v)
    peel v = cong (λ u → ⌜Id⌝ ⌜Nat⌝ u (predTm v))
                  (wk-single {v = v} (predTm x))

    de = ⊢-cast (sym (cong El (peel x)))
                (⊢conv (⊢reflN (⊢pred dx))
                       (csymᵀ (elIdN (predTm x) (predTm x))))

------------------------------------------------------------------------
-- ★★ 5.  `0 ∸ b = 0`.  The motive mentions no ambient term, so — like
--   `plus0B` — it needs no `mot-at`/`mot-s`.
------------------------------------------------------------------------

zmB : {Γ : Cx} (b : RTm Γ) → RTy Γ
zmB b = IdN (monusTm nzero b) nzero

⊢zmMot : {Γ : Ctx} → (Γ ▹ Nat) ⊢ty zmB (var vz)
⊢zmMot = ⊢tyIdN (⊢monus ⊢nzero (⊢var here)) ⊢nzero

zmTm : {Γ : Cx} → RTm Γ → RTm Γ
zmTm b = natrec (reflN nzero)
                (congPd (monusTm nzero (var (vs vz))) (var vz))
                b

⊢zero-monus : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat →
              Γ ⊢ zmTm b ∷ zmB b
⊢zero-monus db = ⊢natrec ⊢zmMot zB sB db
  where
    zB = ⊢conv (⊢reflN ⊢nzero)
           (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Idˡ (natrec-zero _ _)) doneᵀ)))

    -- ⚠ THE TWO SIDES MOVE IN OPPOSITE DIRECTIONS.  The goal's LEFT
    --   endpoint steps DOWN to the branch's subject (`monus-suc`), while
    --   the branch's own RIGHT endpoint `pred 0` steps down to the goal's
    --   `0`.  ⇒ `ctrnᵀ` with one `csymᵀ`, not two reductions the same way.
    sB = ⊢conv (⊢congPd (⊢monus ⊢nzero (⊢var (there here))) ⊢nzero (⊢var here))
           (ctrnᵀ (red→≅ᵀ (stepᵀ (ξ-Idʳ (natrec-zero _ _)) doneᵀ))
                  (csymᵀ (red→≅ᵀ (stepᵀ (ξ-Idˡ (natrec-suc _ _ _)) doneᵀ))))

------------------------------------------------------------------------
-- ★★ 6.  `pred (suc a ∸ b) = a ∸ b`.
--
-- ⚠ THIS IS WHAT SUPPLIES `suc a ∸ suc b = a ∸ b`, WHICH IS **NOT**
--   DEFINITIONAL.  `monusTm` recurses on its SECOND argument, so
--   `suc a ∸ suc b` unfolds to `pred (suc a ∸ b)` — the successor on the
--   LEFT never meets a `natrec` at all.  Every `∸` step in `monusPlus`
--   goes through this lemma.
------------------------------------------------------------------------

pmB : {Γ : Cx} (a b : RTm Γ) → RTy Γ
pmB a b = IdN (predTm (monusTm (nsuc a) b)) (monusTm a b)

⊢pmMot : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ Nat →
         (Γ ▹ Nat) ⊢ty pmB (w a) (var vz)
⊢pmMot da =
  ⊢tyIdN (⊢pred (⊢monus (⊢nsuc (⊢wk da)) (⊢var here)))
         (⊢monus (⊢wk da) (⊢var here))

pmMot-at : {Γ : Cx} (a b : RTm Γ) →
           subTy (single b) (pmB (w a) (var vz)) ≡ pmB a b
pmMot-at a b =
  cong (λ u → IdN (predTm (monusTm (nsuc u) b)) (monusTm u b))
       (wk-single {v = b} a)

pmMot-s : {Γ : Cx} (a : RTm Γ) →
          subTy nrs (pmB (w a) (var vz))
        ≡ pmB (w (w a)) (nsuc (var (vs vz)))
pmMot-s a =
  cong (λ u → IdN (predTm (monusTm (nsuc u) (nsuc (var (vs vz)))))
                  (monusTm u (nsuc (var (vs vz)))))
       (nrs-w a)

pmTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
pmTm a b =
  natrec (reflN a)
         (congPd (predTm (monusTm (nsuc (w (w a))) (var (vs vz)))) (var vz))
         b

⊢pred-monus : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} →
              Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat →
              Γ ⊢ pmTm a b ∷ pmB a b
⊢pred-monus {a = a} {b = b} da db =
  ⊢-cast (pmMot-at a b) (⊢natrec (⊢pmMot da) zB sB db)
  where
    -- ⚠ TWO STEPS ON THE LEFT: `suc a ∸ 0` has to reach `suc a` before
    --   `pred` can fire, and `pred-suc` itself is `⟶*` (it carries a
    --   `wk-single`).  ⇒ assemble at `⟶*` and lift once.
    zB = ⊢-cast (sym (pmMot-at a nzero))
           (⊢conv (⊢reflN da)
             (csymᵀ (ctrnᵀ
               (red→≅ᵀ (⟶ᵀ*-Idˡ (⟶*-trans (⟶*-natrecⁿ (monus-zero (nsuc a)))
                                           (pred-suc a))))
               (red→≅ᵀ (⟶ᵀ*-Idʳ (monus-zero a))))))

    sB = ⊢-cast (sym (pmMot-s a))
           (⊢conv (⊢congPd (⊢pred (⊢monus (⊢nsuc dA) dB'))
                           (⊢monus dA dB')
                           (⊢var here))
             (csymᵀ (ctrnᵀ
               (red→≅ᵀ (stepᵀ (ξ-Idˡ (ξ-natrecⁿ (natrec-suc _ _ _))) doneᵀ))
               (red→≅ᵀ (stepᵀ (ξ-Idʳ (natrec-suc _ _ _)) doneᵀ)))))
      where
        dA  = ⊢wk (⊢wk da)
        dB' = ⊢var (there here)

------------------------------------------------------------------------
-- ★★★ 7.  NO CONFUSION FOR `Nat` — `0 ≡ suc p` IS ABSURD, INTERNALLY.
--
-- ★ THE FAMILY IS A `natrec` INTO `U`: `λn. natrec ⌜Unit⌝ ⌜base⌝ n`.
--   `⊢natrec`'s motive is an `RTy`, and `ty-U` says `U` is one, so the
--   large elimination needed here is already in the kernel — no new rule.
--
-- ⚠ WHY IT IS NEEDED AT ALL.  `monusPlus`'s leaf `a = 0, b = suc b'` gets
--   `0 ∸ suc b' ≡ suc p`, and `zero-monus` turns that into `0 ≡ suc p`.
--   The kernel's `Id` has no injectivity or disjointness built in, so the
--   contradiction has to be TRANSPORTED to `base` and eliminated there.
------------------------------------------------------------------------

nfam : {Γ : Cx} → RTm (Γ ∙)
nfam = natrec ⌜Unit⌝ ⌜base⌝ (var vz)

⊢nfam : {Γ : Ctx} → (Γ ▹ El ⌜Nat⌝) ⊢ nfam ∷ U
⊢nfam = ⊢natrec ty-U ⊢⌜Unit⌝ ⊢⌜base⌝ (elAsNat (⊢var here))

noConfTm : {Γ : Cx} → RTm Γ → RTm Γ
noConfTm e = jsub nfam e unit

⊢noConf : {Γ : Ctx} {p e : RTm ⌊ Γ ⌋} →
          Γ ⊢ p ∷ Nat → Γ ⊢ e ∷ IdN nzero (nsuc p) →
          Γ ⊢ noConfTm e ∷ base
⊢noConf dp de =
  ⊢conv (⊢jsub ⊢nfam (natAsEl ⊢nzero) (natAsEl (⊢nsuc dp)) de dunit)
        (red→≅ᵀ (stepᵀ (ξ-El (natrec-suc _ _ _)) (stepᵀ El-⌜base⌝ doneᵀ)))
  where
    dunit = ⊢conv ⊢unit
              (csymᵀ (red→≅ᵀ (stepᵀ (ξ-El (natrec-zero _ _))
                              (stepᵀ El-⌜Unit⌝ doneᵀ))))

-- ★ …and the ex-falso a client actually calls: any `IdN` follows.
exFalsoN : {Γ : Ctx} {p e x y : RTm ⌊ Γ ⌋} →
           Γ ⊢ p ∷ Nat → Γ ⊢ x ∷ Nat → Γ ⊢ y ∷ Nat →
           Γ ⊢ e ∷ IdN nzero (nsuc p) →
           Γ ⊢ absurd (⌜Id⌝ ⌜Nat⌝ x y) (noConfTm e) ∷ IdN x y
exFalsoN {x = x} {y = y} dp dx dy de =
  ⊢conv (⊢absurd (⊢⌜Id⌝ ⊢⌜Nat⌝ (natAsEl dx) (natAsEl dy)) (⊢noConf dp de))
        (elIdN x y)

------------------------------------------------------------------------
-- ⇒ `monusPlus` — ITS STATEMENT, ITS IH-APPLICATION AND ITS PROOF — LIVES
--   IN `…LibMonusPlus`.
--
-- ⚠⚠ AND THAT IS A MEASUREMENT, NOT TIDINESS.  With it here the module was
--   929 lines and Agda was OOM-KILLED (exit 143, uncontended, no error
--   message).  `monusPlus` is a `natrec` inside a `natrec` whose motive
--   Π-binds three things; the elaborated term is large, and this module
--   already carries eight other internal inductions.
--
-- ⭐ Same lever as `leaf₃s` and `split2` before it: ONE BIG TERM PER
--   MODULE once the term is big enough.  See `agda-cost-is-elaborated-term-size`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★ 10.  THE TWO DIVISIBILITY FACTS THE BASE CASES NEED.
--
-- ⚠ `…LibDvd`'s header calls both "one-liners" and defines NEITHER.  They
--   are one-liners only once `mul-zero`/`mul-suc` and `⊢plus0` are in
--   hand, which is why they land here rather than there.
--
-- ★ `d ∣ 0` takes the witness 0; `d ∣ d` takes 1, and `1 * d` reduces to
--   `d + 0`, which `⊢plus0` closes.  ⭐ This is exactly the orientation
--   `…LibDvd` chose `n ≡ k * d` for: with `d * k` BOTH would be stuck at
--   the variable `d`.
------------------------------------------------------------------------

⊢dvd-zero : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} → Γ ⊢ d ∷ Nat →
            Γ ⊢ pair nzero (reflN nzero) ∷ dvdT d nzero
⊢dvd-zero {d = d} dd =
  dvd-intro dd ⊢nzero ⊢nzero
    (⊢conv (⊢reflN ⊢nzero)
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ (mul-zero d)))))

⊢dvd-refl : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} → Γ ⊢ d ∷ Nat →
            Γ ⊢ pair (nsuc nzero) (symN (plusTm d nzero) (plus0Tm d))
              ∷ dvdT d d
⊢dvd-refl {d = d} dd =
  dvd-intro dd dd (⊢nsuc ⊢nzero)
    (⊢conv (⊢symN (⊢plus dd ⊢nzero) dd (⊢plus0 dd))
           (csymᵀ (red→≅ᵀ (⟶ᵀ*-Idʳ oneMul))))
  where
    -- `1 * d ⟶* d + 0`
    oneMul = ⟶*-trans (mul-suc nzero d) (⟶*-natrecᶻ (mul-zero d))

------------------------------------------------------------------------
-- ★★★ 11.  THE CONJUNCTIVE MOTIVE, AS A CODE — AND ITS NATURALITY.
--
-- ⚠ THE MOTIVE OF gcd's SPEC MUST BE A CONJUNCTION (GAP-B-LAYER2-PLAN §1):
--   the `a > b` branch's IH gives `d ∣ (a ∸ b)`, and reaching `d ∣ a`
--   needs `monusPlus` AND the second conjunct.  Neither half is provable
--   alone by this recursion.
--
-- ★ It is a CODE because `amrec-ind`'s motive lives in `U` — that
--   constraint is what `⊢dvdCode` was built to clear.
--
-- ⚠ AND THE NATURALITY LAWS ARE NOT FREE: `dvdCode` contains a `mulTm`,
--   which commutes with neither `subTm` nor `renTm` definitionally.
------------------------------------------------------------------------

QCode : {Γ : Cx} (u₁ u₂ v : RTm Γ) → RTm Γ
QCode u₁ u₂ v = ⌜Σ⌝ (dvdCode v u₁) (w (dvdCode v u₂))

⊢QCode : {Γ : Ctx} {u₁ u₂ v : RTm ⌊ Γ ⌋} →
         Γ ⊢ u₁ ∷ Nat → Γ ⊢ u₂ ∷ Nat → Γ ⊢ v ∷ Nat →
         Γ ⊢ QCode u₁ u₂ v ∷ U
⊢QCode d1 d2 dv = ⊢⌜Σ⌝ (⊢dvdCode dv d1) (⊢wk (⊢dvdCode dv d2))

dvdCode-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (d n : RTm Γ) →
              subTm σ (dvdCode d n) ≡ dvdCode (subTm σ d) (subTm σ n)
dvdCode-sub {σ = σ} d n =
  cong₂ (λ u v → ⌜Σ⌝ ⌜Nat⌝ (⌜Id⌝ ⌜Nat⌝ u v))
        (sub-w {σ = σ} n)
        (trans (mulTm-sub {σ = extS σ} (var vz) (w d))
               (cong (mulTm (var vz)) (sub-w {σ = σ} d)))

dvdCode-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (d n : RTm Γ) →
              renTm ρ (dvdCode d n) ≡ dvdCode (renTm ρ d) (renTm ρ n)
dvdCode-ren {ρ = ρ} d n =
  cong₂ (λ u v → ⌜Σ⌝ ⌜Nat⌝ (⌜Id⌝ ⌜Nat⌝ u v))
        (ren-w {ρ = ρ} n)
        (trans (mulTm-ren {ρ = extR ρ} (var vz) (w d))
               (cong (mulTm (var vz)) (ren-w {ρ = ρ} d)))

QCode-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (u₁ u₂ v : RTm Γ) →
            subTm σ (QCode u₁ u₂ v)
          ≡ QCode (subTm σ u₁) (subTm σ u₂) (subTm σ v)
QCode-sub {σ = σ} u₁ u₂ v =
  cong₂ ⌜Σ⌝ (dvdCode-sub v u₁)
            (trans (sub-w {σ = σ} (dvdCode v u₂))
                   (cong w (dvdCode-sub v u₂)))

QCode-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'} (u₁ u₂ v : RTm Γ) →
            renTm ρ (QCode u₁ u₂ v)
          ≡ QCode (renTm ρ u₁) (renTm ρ u₂) (renTm ρ v)
QCode-ren {ρ = ρ} u₁ u₂ v =
  cong₂ ⌜Σ⌝ (dvdCode-ren v u₁)
            (trans (ren-w {ρ = ρ} (dvdCode v u₂))
                   (cong w (dvdCode-ren v u₂)))

------------------------------------------------------------------------
-- ★★★★ 12.  THE MOTIVE'S INTERFACE — INTRO AND THE TWO PROJECTIONS.
--
-- ⚠ `amrec-ind` states everything in terms of `El <code>`, while every
--   divisibility lemma above is stated at the TYPE `dvdT`.  These three
--   are the bridge, and each pays the same decode: `⌜Σ⌝`, then `⌜Nat⌝` in
--   the first component and `⌜Id⌝` in the second.
--
-- ★ Factored out for the reason `monusPlus` taught: the four leaves of
--   `IndStep` each use them, and inlining the decode four times is how a
--   derivation gets big enough to OOM.
------------------------------------------------------------------------

El-dvd : {Γ : Cx} (d n : RTm Γ) → El (dvdCode d n) ⟶ᵀ* dvdT d n
El-dvd d n =
  stepᵀ (El-⌜Σ⌝ _ _)
    (stepᵀ (ξ-Σˡ El-⌜Nat⌝)
      (stepᵀ (ξ-Σʳ (El-⌜Id⌝ _ _ _)) doneᵀ))

⊢Q-intro : {Γ : Ctx} {u₁ u₂ v h₁ h₂ : RTm ⌊ Γ ⌋} →
           Γ ⊢ u₂ ∷ Nat → Γ ⊢ v ∷ Nat →
           Γ ⊢ h₁ ∷ dvdT v u₁ → Γ ⊢ h₂ ∷ dvdT v u₂ →
           Γ ⊢ pair h₁ h₂ ∷ El (QCode u₁ u₂ v)
⊢Q-intro {u₁ = u₁} {u₂ = u₂} {v = v} {h₁ = h₁} d2 dv dh1 dh2 =
  ⊢conv (⊢pair (ty-El (⊢wk (⊢dvdCode dv d2)))
               (⊢conv dh1 (csymᵀ (red→≅ᵀ (El-dvd v u₁))))
               (⊢-cast (sym (cong El (wk-single {v = h₁} (dvdCode v u₂))))
                       (⊢conv dh2 (csymᵀ (red→≅ᵀ (El-dvd v u₂))))))
        (csymᵀ (red→≅ᵀ (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ)))

⊢Q-fst : {Γ : Ctx} {u₁ u₂ v h : RTm ⌊ Γ ⌋} →
         Γ ⊢ h ∷ El (QCode u₁ u₂ v) → Γ ⊢ fst h ∷ dvdT v u₁
⊢Q-fst {u₁ = u₁} {v = v} dh =
  ⊢conv (⊢fst (⊢conv dh (red→≅ᵀ (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ))))
        (red→≅ᵀ (El-dvd v u₁))

⊢Q-snd : {Γ : Ctx} {u₁ u₂ v h : RTm ⌊ Γ ⌋} →
         Γ ⊢ h ∷ El (QCode u₁ u₂ v) → Γ ⊢ snd h ∷ dvdT v u₂
⊢Q-snd {u₂ = u₂} {v = v} {h = h} dh =
  ⊢conv (⊢-cast (cong El (wk-single {v = fst h} (dvdCode v u₂)))
                (⊢snd (⊢conv dh (red→≅ᵀ (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ)))))
        (red→≅ᵀ (El-dvd v u₂))

------------------------------------------------------------------------
-- ★★ 13.  DIVISIBILITY TRANSPORTS ALONG AN EQUATION.
--
-- ⚠ BOTH of gcd's recursive leaves end the same way: `⊢dvd-plus` proves
--   `v ∣ ((x ∸ y) + y)` and the cancellation says that sum IS `x`.  Moving
--   the divisibility across is `⊢jsub` at the family `λn. dvdCode v n` —
--   available precisely because `dvdT` was given a CODE.
------------------------------------------------------------------------

dvdCongTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
dvdCongTm d h p = jsub (dvdCode (w d) (var vz)) p h

⊢dvd-cong : {Γ : Ctx} {d n n' h p : RTm ⌊ Γ ⌋} →
            Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ n' ∷ Nat →
            Γ ⊢ p ∷ IdN n n' → Γ ⊢ h ∷ dvdT d n →
            Γ ⊢ dvdCongTm d h p ∷ dvdT d n'
⊢dvd-cong {d = d} {n = n} {n' = n'} dd dn dn' dp dh =
  ⊢conv (⊢-cast (cong El (peel n'))
          (⊢jsub (⊢dvdCode (⊢wk dd) (asN (⊢var here)))
                 (natAsEl dn) (natAsEl dn') dp
                 (⊢-cast (sym (cong El (peel n)))
                         (⊢conv dh (csymᵀ (red→≅ᵀ (El-dvd d n)))))))
        (red→≅ᵀ (El-dvd d n'))
  where
    peel : (v : RTm ⌊ _ ⌋) →
           subTm (single v) (dvdCode (w d) (var vz)) ≡ dvdCode d v
    peel v = trans (dvdCode-sub {σ = single v} (w d) (var vz))
                   (cong (λ u → dvdCode u v) (wk-single {v = v} d))

------------------------------------------------------------------------
-- ★★★ 14.  THE MOTIVE'S VALUE SLOT REDUCES.
--
-- ⚠ WHY THIS IS NEEDED AND IS NOT FREE.  Every leaf of gcd's `IndStep`
--   proves the spec of a REDUCED value (`fst x`, `suc b'`, an IH call),
--   while the split motive states it of the UNREDUCED `app f ih`.  With an
--   `Id`-valued motive (`…GcdStepExt`'s `eqG`) `idOfRed` bridges that; with
--   a CODE-valued one there is no such bridge, so the reduction has to be
--   pushed all the way into the code.
--
-- ⭐ AND IT GOES, because the kernel has ξ-rules INSIDE the code formers
--   (`ξ-⌜Σ⌝ˡ`, `ξ-⌜Σ⌝ʳ`, `ξ-⌜Id⌝ʳ`).  ⚠ The value lands under
--   `mulTm (var vz) (w d)`, i.e. in the STEP branch of `mulTm`'s `natrec`
--   as `w (w d)` — hence `⟶*-natrecˢ` over `⟶*-natrecⁿ` over two
--   `⟶*-ren vs`.  That chain is the whole of `mulTm-red`.
------------------------------------------------------------------------

⟶*-⌜Σ⌝ˡ : {Γ : Cx} {c c' : RTm Γ} {d : RTm (Γ ∙)} →
          c ⟶* c' → ⌜Σ⌝ c d ⟶* ⌜Σ⌝ c' d
⟶*-⌜Σ⌝ˡ done       = done
⟶*-⌜Σ⌝ˡ (step r p) = step (ξ-⌜Σ⌝ˡ r) (⟶*-⌜Σ⌝ˡ p)

⟶*-⌜Σ⌝ʳ : {Γ : Cx} {c : RTm Γ} {d d' : RTm (Γ ∙)} →
          d ⟶* d' → ⌜Σ⌝ c d ⟶* ⌜Σ⌝ c d'
⟶*-⌜Σ⌝ʳ done       = done
⟶*-⌜Σ⌝ʳ (step r p) = step (ξ-⌜Σ⌝ʳ r) (⟶*-⌜Σ⌝ʳ p)

⟶*-⌜Id⌝ʳ : {Γ : Cx} {c a b b' : RTm Γ} →
           b ⟶* b' → ⌜Id⌝ c a b ⟶* ⌜Id⌝ c a b'
⟶*-⌜Id⌝ʳ done       = done
⟶*-⌜Id⌝ʳ (step r p) = step (ξ-⌜Id⌝ʳ r) (⟶*-⌜Id⌝ʳ p)

mulTm-red : {Γ : Cx} {n n' : RTm Γ} (m : RTm Γ) →
            n ⟶* n' → mulTm m n ⟶* mulTm m n'
mulTm-red m r = ⟶*-natrecˢ (⟶*-natrecⁿ (⟶*-ren vs (⟶*-ren vs r)))

dvdCode-red : {Γ : Cx} {d d' : RTm Γ} (n : RTm Γ) →
              d ⟶* d' → dvdCode d n ⟶* dvdCode d' n
dvdCode-red n r = ⟶*-⌜Σ⌝ʳ (⟶*-⌜Id⌝ʳ (mulTm-red (var vz) (⟶*-ren vs r)))

QCode-red : {Γ : Cx} {v v' : RTm Γ} (u₁ u₂ : RTm Γ) →
            v ⟶* v' → QCode u₁ u₂ v ⟶* QCode u₁ u₂ v'
QCode-red u₁ u₂ r =
  ⟶*-trans (⟶*-⌜Σ⌝ˡ (dvdCode-red u₁ r))
           (⟶*-⌜Σ⌝ʳ (⟶*-ren vs (dvdCode-red u₂ r)))

-- ★ …and therefore a TYPE conversion, which is what a leaf needs.
QCode-conv : {Γ : Cx} {v v' : RTm Γ} (u₁ u₂ : RTm Γ) →
             v ⟶* v' → El (QCode u₁ u₂ v) ≅ᵀ El (QCode u₁ u₂ v')
QCode-conv u₁ u₂ r = red→≅ᵀ (⟶ᵀ*-El (QCode-red u₁ u₂ r))

-- ★ …and the two COMPONENT slots reduce too.  ⚠ The recursive leaves need
--   this and the value-slot version is not enough: `indPWElim` hands back
--   `QCode (fst PAIR) (snd PAIR) …`, and the goal states the components as
--   the projections' REDUCTS.  ⚠ A component sits in `⌜Id⌝`'s LEFT slot
--   (as `w n`), not under the `mulTm` — hence `ξ-⌜Id⌝ˡ`, one `⟶*-ren`,
--   and no `natrec` congruence at all.
⟶*-⌜Id⌝ˡ : {Γ : Cx} {c a a' b : RTm Γ} →
           a ⟶* a' → ⌜Id⌝ c a b ⟶* ⌜Id⌝ c a' b
⟶*-⌜Id⌝ˡ done       = done
⟶*-⌜Id⌝ˡ (step r p) = step (ξ-⌜Id⌝ˡ r) (⟶*-⌜Id⌝ˡ p)

dvdCode-redN : {Γ : Cx} {n n' : RTm Γ} (d : RTm Γ) →
               n ⟶* n' → dvdCode d n ⟶* dvdCode d n'
dvdCode-redN d r = ⟶*-⌜Σ⌝ʳ (⟶*-⌜Id⌝ˡ (⟶*-ren vs r))

QCode-redU : {Γ : Cx} {u₁ u₁' u₂ u₂' : RTm Γ} (v : RTm Γ) →
             u₁ ⟶* u₁' → u₂ ⟶* u₂' →
             QCode u₁ u₂ v ⟶* QCode u₁' u₂' v
QCode-redU v r₁ r₂ =
  ⟶*-trans (⟶*-⌜Σ⌝ˡ (dvdCode-redN v r₁))
           (⟶*-⌜Σ⌝ʳ (⟶*-ren vs (dvdCode-redN v r₂)))

QCode-convU : {Γ : Cx} {u₁ u₁' u₂ u₂' : RTm Γ} (v : RTm Γ) →
              u₁ ⟶* u₁' → u₂ ⟶* u₂' →
              El (QCode u₁ u₂ v) ≅ᵀ El (QCode u₁' u₂' v)
QCode-convU v r₁ r₂ = red→≅ᵀ (⟶ᵀ*-El (QCode-redU v r₁ r₂))
