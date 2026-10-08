-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.CLabelsUnique — plan 0.107 §8 step 4: THE LABELS A
-- FRAGMENT DEFINES (`c-label`s and closure-body entries) ARE PAIRWISE DISTINCT.
--
-- `LabelsUnique` proves it for the THUNK labels (closure bodies, the cata
-- marker); `LabelScope` gives every mentioned label a counter WINDOW. What no
-- module said is that two `c-label` definitions inside one fragment differ —
-- the fact `as` needs (`AsmWF.defined-once`): a label defined twice does not
-- assemble. Same shape as `LabelsUnique`: the counter is a fresh-name supply,
-- each emitter mints its own labels at fixed offsets ABOVE or BELOW its
-- children's windows, and the children's windows are disjoint.
--
-- Stated over INDICES (`List ℕ`): the symbol a label renders to recovers its
-- index (`Adequacy.ImageUnique`), so distinct indices are what the file needs.
------------------------------------------------------------------------

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.CLabelsUnique (o : CanonicalName) where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; <⇒≢; n≤1+n; m≤m+n; <-≤-trans; +-suc; +-assoc; +-cancelʳ-≡; n<1+n; ≤-reflexive; +-identityʳ; +-comm; +-monoʳ-<; +-monoʳ-≤)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ) renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Once.CCC.Label using (LabelId; ℓ)
open import Once.CCC.Machine.SMCore

open import Once.CCC.Codegen.LabelDefs

------------------------------------------------------------------------
-- THE CASE SHAPE: a branch's labels `k` (entry of the second arm) and
-- `suc k` (the join) around two arms whose windows sit above them — `case`,
-- the functor walks' `⊕`, and the re-suspension pass's `Sum` all emit it.
------------------------------------------------------------------------

case-dst : ∀ {k m hi F G} → suc (suc k) ≤ m → Dst F → Dst G → Win (suc (suc k)) m F → Win m hi G
         → Dst (G ++ (k ∷ (F ++ (suc k ∷ []))))
case-dst {k} {m} {hi} {F} {G} ssk≤m dF dG wF wG = dst-++ dG mid djG
  where
    k<ssk : k < suc (suc k)
    k<ssk = ≤-trans (n<1+n k) (n≤1+n (suc k))
    mid  : Dst (k ∷ (F ++ (suc k ∷ [])))
    mid  = All-++⁺ (fresh-below k<ssk wF) (<⇒≢ (n<1+n k) ∷ [])
         ∷ dst-++ dF ([] ∷ []) (All-map (λ {x} ne → (λ eq → ne (sym eq)) ∷ []) (fresh-below (n<1+n (suc k)) wF))
    djG : Dj G (k ∷ (F ++ (suc k ∷ [])))
    djG = All-map (λ {g} p →
            (λ eq → <⇒≢ (<-≤-trans k<ssk (≤-trans ssk≤m (proj₁ p))) (sym eq))
            ∷ All-++⁺ (fresh-above (proj₁ p) wF)
                      ((λ eq → <⇒≢ (<-≤-trans (n<1+n (suc k)) (≤-trans ssk≤m (proj₁ p))) (sym eq)) ∷ []))
          wG

case-win : ∀ {k m hi F G} → suc (suc k) ≤ m → m ≤ hi → Win (suc (suc k)) m F → Win m hi G
         → Win k hi (G ++ (k ∷ (F ++ (suc k ∷ []))))
case-win {k} {m} {hi} ssk≤m m≤hi wF wG =
  All-++⁺ (win-weaken (≤-trans (n≤1+n k) (≤-trans (n≤1+n (suc k)) ssk≤m)) ≤-refl wG)
    ((≤-refl , k<hi)
     ∷ All-++⁺ (win-weaken (≤-trans (n≤1+n k) (n≤1+n (suc k))) m≤hi wF)
               ((n≤1+n k , sk<hi) ∷ []))
  where
    sk<hi : suc k < hi
    sk<hi = ≤-trans ssk≤m m≤hi
    k<hi : k < hi
    k<hi = ≤-trans (n≤1+n (suc k)) sk<hi

------------------------------------------------------------------------
-- The functor walks and the re-suspension pass: each a functor induction.
------------------------------------------------------------------------

open import Once.Type using (Functor; K; Id; _⊕_; _⊗_)
open import Once.IRTy using (WellFormedFI; wf-K; wf-Id; wf-Prod; wf-Sum)
open import Once.CCC.Codegen.IRToTrace o
  using (visit-walk; rebuild-walk; lsize; resuspend-layer)
open import Once.CCC.Codegen.LabelRange o using (resuspend-label-mono)

private
  -- `ss lb + a + b` is `lb + lsize (F ⊕ G)` when `a`, `b` are the two sizes
  arith⊕ : ∀ (lb a b : ℕ) → suc (suc lb) + a + b ≡ lb + suc (suc (a + b))
  arith⊕ lb a b = trans (+-assoc (suc (suc lb)) a b) (sym (trans (+-suc lb (suc (a + b))) (cong suc (+-suc lb (a + b)))))

  win-hi : ∀ {lo hi hi′ xs} → hi ≡ hi′ → Win lo hi xs → Win lo hi′ xs
  win-hi refl w = w

  -- the shape-generic case step, at sizes `a` (second arm `F`) and `b` (first, `G`)
  case-step : ∀ (lb a b : ℕ) {F G}
            → Dst F × Win (suc (suc lb)) (suc (suc lb) + a) F
            → Dst G × Win (suc (suc lb) + a) (suc (suc lb) + a + b) G
            → Dst (G ++ (lb ∷ (F ++ (suc lb ∷ [])))) × Win lb (lb + suc (suc (a + b))) (G ++ (lb ∷ (F ++ (suc lb ∷ []))))
  case-step lb a b (dF , wF) (dG , wG) =
    case-dst (m≤m+n _ a) dF dG wF wG
    , win-hi (arith⊕ lb a b) (case-win (m≤m+n _ a) (m≤m+n _ b) wF wG)

  -- two consecutive windows
  seq-step : ∀ (lb a b : ℕ) {F G}
           → Dst F × Win lb (lb + a) F → Dst G × Win (lb + a) (lb + a + b) G
           → Dst (F ++ G) × Win lb (lb + (a + b)) (F ++ G)
  seq-step lb a b (dF , wF) (dG , wG) =
    dst-++ dF dG (dj-win wF wG ≤-refl)
    , win-hi (+-assoc lb a b) (All-++⁺ (win-weaken ≤-refl (m≤m+n _ b) wF) (win-weaken (m≤m+n lb a) ≤-refl wG))

visit-cl : ∀ (F : Functor) (todo tv tb s lb : ℕ)
         → Dst (clabs (visit-walk todo tv tb F s lb)) × Win lb (lb + lsize F) (clabs (visit-walk todo tv tb F s lb))
visit-cl (K _)   todo tv tb s lb = [] , []
visit-cl Id      todo tv tb s lb = [] , []
visit-cl (F ⊕ G) todo tv tb s lb =
  subst (λ z → Dst z × Win lb (lb + lsize (F ⊕ G)) z) (sym eq)
    (case-step lb (lsize F) (lsize G)
      (visit-cl F todo tv tb (s + 4) (suc (suc lb)))
      (visit-cl G todo tv tb (s + 4) (suc (suc lb) + lsize F)))
  where
    vF = visit-walk todo tv tb F (s + 4) (suc (suc lb))
    vG = visit-walk todo tv tb G (s + 4) (suc (suc lb) + lsize F)
    eq : clabs (visit-walk todo tv tb (F ⊕ G) s lb) ≡ clabs vG ++ (lb ∷ (clabs vF ++ (suc lb ∷ [])))
    eq = trans (clabs-++ vG _) (cong (λ z → clabs vG ++ (lb ∷ z)) (clabs-++ vF _))
visit-cl (F ⊗ G) todo tv tb s lb =
  subst (λ z → Dst z × Win lb (lb + lsize (F ⊗ G)) z) (sym eq)
    (seq-step lb (lsize F) (lsize G)
      (visit-cl F todo tv tb (s + 4) lb)
      (visit-cl G todo tv tb (s + 4) (lb + lsize F)))
  where
    vF = visit-walk todo tv tb F (s + 4) lb
    vG = visit-walk todo tv tb G (s + 4) (lb + lsize F)
    eq : clabs (visit-walk todo tv tb (F ⊗ G) s lb) ≡ clabs vF ++ clabs vG
    eq = clabs-++ vF _

rebuild-cl : ∀ (F : Functor) (val tv tb s lb : ℕ)
           → Dst (clabs (rebuild-walk val tv tb F s lb)) × Win lb (lb + lsize F) (clabs (rebuild-walk val tv tb F s lb))
rebuild-cl (K _)   val tv tb s lb = [] , []
rebuild-cl Id      val tv tb s lb = [] , []
rebuild-cl (F ⊕ G) val tv tb s lb =
  subst (λ z → Dst z × Win lb (lb + lsize (F ⊕ G)) z) (sym eq)
    (case-step lb (lsize F) (lsize G)
      (rebuild-cl F val tv tb (s + 4) (suc (suc lb)))
      (rebuild-cl G val tv tb (s + 4) (suc (suc lb) + lsize F)))
  where
    rF = rebuild-walk val tv tb F (s + 4) (suc (suc lb))
    rG = rebuild-walk val tv tb G (s + 4) (suc (suc lb) + lsize F)
    eq : clabs (rebuild-walk val tv tb (F ⊕ G) s lb) ≡ clabs rG ++ (lb ∷ (clabs rF ++ (suc lb ∷ [])))
    eq = trans (clabs-++ rG _) (cong (λ z → clabs rG ++ (lb ∷ z)) (clabs-++ rF _))
rebuild-cl (F ⊗ G) val tv tb s lb =
  subst (λ z → Dst z × Win lb (lb + lsize (F ⊗ G)) z) (sym eq)
    (seq-swap (rebuild-cl F val tv tb (s + 4) lb) (rebuild-cl G val tv tb (s + 4) (lb + lsize F)))
  where
    rF = rebuild-walk val tv tb F (s + 4) lb
    rG = rebuild-walk val tv tb G (s + 4) (lb + lsize F)
    eq : clabs (rebuild-walk val tv tb (F ⊗ G) s lb) ≡ clabs rG ++ clabs rF
    eq = trans (clabs-++ rG _) (cong (clabs rG ++_) (trans (clabs-++ rF _) (++-identityʳ (clabs rF))))
    seq-swap : Dst (clabs rF) × Win lb (lb + lsize F) (clabs rF)
             → Dst (clabs rG) × Win (lb + lsize F) (lb + lsize F + lsize G) (clabs rG)
             → Dst (clabs rG ++ clabs rF) × Win lb (lb + lsize (F ⊗ G)) (clabs rG ++ clabs rF)
    seq-swap (dF , wF) (dG , wG) =
      dst-++ dG dF (dj-sym (dj-win wF wG ≤-refl))
      , win-hi (+-assoc lb (lsize F) (lsize G))
          (All-++⁺ (win-weaken (m≤m+n lb (lsize F)) ≤-refl wG) (win-weaken ≤-refl (m≤m+n _ (lsize G)) wF))

-- the re-suspension pass: labels in `[l, l′)`, distinct
rs-label : ∀ (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F) → ℕ
rs-label n l lbl env wf = proj₁ (proj₂ (resuspend-layer n l lbl env wf))

rs-trace : ∀ (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F) → AbstractTrace
rs-trace n l lbl env wf = proj₂ (proj₂ (resuspend-layer n l lbl env wf))

resusp-cl : ∀ (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
          → Dst (clabs (rs-trace n l lbl env wf)) × Win l (rs-label n l lbl env wf) (clabs (rs-trace n l lbl env wf))
resusp-cl n l lbl env (wf-K _) = [] , []
resusp-cl n l lbl env wf-Id    = [] , []
resusp-cl n l lbl env (wf-Prod wfF wfG) =
  subst (λ z → Dst z × Win l l3 z) (sym eq)
    (dst-++ (proj₁ iF) (proj₁ iG) (dj-win (proj₂ iF) (proj₂ iG) ≤-refl)
    , All-++⁺ (win-weaken ≤-refl (resuspend-label-mono n2 l2 lbl env wfG) (proj₂ iF))
              (win-weaken (resuspend-label-mono (suc (suc (suc n))) l lbl env wfF) ≤-refl (proj₂ iG)))
  where
    n2 = proj₁ (resuspend-layer (suc (suc (suc n))) l lbl env wfF)
    l2 = rs-label (suc (suc (suc n))) l lbl env wfF
    l3 = rs-label n2 l2 lbl env wfG
    tF = rs-trace (suc (suc (suc n))) l lbl env wfF
    tG = rs-trace n2 l2 lbl env wfG
    iF = resusp-cl (suc (suc (suc n))) l lbl env wfF
    iG = resusp-cl n2 l2 lbl env wfG
    eq : clabs (rs-trace n l lbl env (wf-Prod wfF wfG)) ≡ clabs tF ++ clabs tG
    eq = trans (clabs-++ tF _) (cong (clabs tF ++_) (trans (clabs-++ tG _) (++-identityʳ (clabs tG))))
resusp-cl n l lbl env (wf-Sum wfF wfG) =
  subst (λ z → Dst z × Win l l3 z) (sym eq)
    (case-dst ssl≤l2 (proj₁ iF) (proj₁ iG) (proj₂ iF) (proj₂ iG)
    , case-win ssl≤l2 (resuspend-label-mono n2 l2 lbl env wfG) (proj₂ iF) (proj₂ iG))
  where
    n2 = proj₁ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
    l2 = rs-label (suc (suc (suc n))) (suc (suc l)) lbl env wfF
    l3 = rs-label n2 l2 lbl env wfG
    tF = rs-trace (suc (suc (suc n))) (suc (suc l)) lbl env wfF
    tG = rs-trace n2 l2 lbl env wfG
    iF = resusp-cl (suc (suc (suc n))) (suc (suc l)) lbl env wfF
    iG = resusp-cl n2 l2 lbl env wfG
    ssl≤l2 : suc (suc l) ≤ l2
    ssl≤l2 = resuspend-label-mono (suc (suc (suc n))) (suc (suc l)) lbl env wfF
    eq : clabs (rs-trace n l lbl env (wf-Sum wfF wfG)) ≡ clabs tG ++ (l ∷ (clabs tF ++ (suc l ∷ [])))
    eq = trans (clabs-++ (tG ++ _) _)
           (cong₂ _++_ (trans (clabs-++ tG _) (++-identityʳ (clabs tG)))
                       (cong (l ∷_) (trans (clabs-++ (tF ++ _) _)
                                           (cong (_++ (suc l ∷ [])) (trans (clabs-++ tF _) (++-identityʳ (clabs tF)))))))


------------------------------------------------------------------------
-- THE INDUCTION over `ir-to-trace'`: a fragment's trace labels and block
-- labels are each distinct, disjoint from each other, and inside the
-- fragment's counter window `[l, label-of)`.
------------------------------------------------------------------------

open import Once.IR using (IR; id; _∘_; ⟨_,_⟩; fst; snd; inl; inr; case; terminal; initial;
  curry; apply; In; out-μ; Cata; Out; in-ν; Ana; SigOp; Call; const)
open import Once.IRTy using (fits-int; fits-float; ⌈_⌉F)
open import Once.SigOp.Info using (SigOpInfo; sem)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Codegen.IRToTrace o
  using (ir-to-trace'; sigop-code; cata-dispatch; cata-strategy; CataStrategy;
         strat-const; strat-nat; strat-linear; strat-branching)
open import Once.CCC.Codegen.LabelRange o using (label-of; label-mono; cata-label-of)
open import Once.CCC.Codegen.LabelScope o using (trace-of)
open import Once.CCC.Codegen.SlotBudget o using (bodies-of)
open import Data.List.Relation.Unary.All using (all?)
open import Data.List.Relation.Unary.AllPairs using (allPairs?)
open import Data.Nat using (_≟_; _<?_)
open import Relation.Nullary.Decidable using (toWitness; ¬?; True)
open import Data.Nat.Properties using (+-monoˡ-<; m≤n+m)

Facts : List ℕ → List ℕ → Set
Facts T Bl = Dst T × Dst Bl × Dj T Bl

module _ {A B} (ir : IR A B) (n l : ℕ) where
  TL BL : List ℕ
  TL = clabs (trace-of (ir-to-trace' n l ir))
  BL = clabs (blocks-layout (bodies-of (ir-to-trace' n l ir)))

  HI : ℕ
  HI = label-of (ir-to-trace' n l ir)

FragP : ℕ → ℕ → List ℕ → List ℕ → Set
FragP lo hi T Bl = Facts T Bl × Win lo hi T × Win lo hi Bl

Frag : ∀ {A B} (ir : IR A B) (n l : ℕ) → Set
Frag ir n l = FragP l (HI ir n l) (TL ir n l) (BL ir n l)

private
  transport : ∀ {T T′ Bl Bl′ : List ℕ} {P : List ℕ → List ℕ → Set} → T ≡ T′ → Bl ≡ Bl′ → P T′ Bl′ → P T Bl
  transport refl refl f = f

  bl-++ : ∀ (xs ys : List (LabelId × ℕ × AbstractTrace))
        → clabs (blocks-layout (xs ++ ys)) ≡ clabs (blocks-layout xs) ++ clabs (blocks-layout ys)
  bl-++ xs ys = trans (cong clabs (blocks-layout-++ xs ys)) (clabs-++ (blocks-layout xs) (blocks-layout ys))

  -- two children at consecutive windows
  seq-frag : ∀ {lo m hi A C B D} → Facts A C → Facts B D
           → Win lo m A → Win lo m C → Win m hi B → Win m hi D → Facts (A ++ B) (C ++ D)
  seq-frag (dA , dC , jAC) (dB , dD , jBD) wA wC wB wD =
    dst-++ dA dB (dj-win wA wB ≤-refl)
    , dst-++ dC dD (dj-win wC wD ≤-refl)
    , dj-++ˡ (dj-++ʳ jAC (dj-win wA wD ≤-refl)) (dj-++ʳ (dj-sym (dj-win wC wB ≤-refl)) jBD)

  seq-win : ∀ {lo m hi A B} → lo ≤ m → m ≤ hi → Win lo m A → Win m hi B → Win lo hi (A ++ B)
  seq-win lo≤m m≤hi wA wB = All-++⁺ (win-weaken ≤-refl m≤hi wA) (win-weaken lo≤m ≤-refl wB)

  -- everything at or above `k` misses a window below `k`
  above-dj : ∀ {lo k xs ys} → Win lo k xs → All (k ≤_) ys → Dj xs ys
  above-dj []         ay = []
  above-dj (px ∷ pxs) ay = All-map (λ py eq → <⇒≢ (<-≤-trans (proj₂ px) py) eq) ay ∷ above-dj pxs ay

  -- a cata: skeleton labels `S1`, `E` at or above `l1`; the algebra's below
  cata-gen : ∀ {lo l1 S1 E A C} → Dst (S1 ++ E) → All (l1 ≤_) (S1 ++ E)
           → Facts A C → Win lo l1 A → Win lo l1 C → Facts (S1 ++ (A ++ E)) C
  cata-gen {S1 = S1} {E} {A} {C} dSE aSE (dA , dC , jAC) wA wC =
    dst-++ dS1 (dst-++ dA dE (above-dj wA aE)) (dj-++ʳ (dj-sym (above-dj wA aS1)) jS1E)
    , dC
    , dj-++ˡ (dj-sym (above-dj wC aS1)) (dj-++ˡ jAC (dj-sym (above-dj wC aE)))
    where
      sp = dst-split S1 E dSE
      dS1 = proj₁ sp ; dE = proj₁ (proj₂ sp) ; jS1E = proj₂ (proj₂ sp)
      aS1 = ++⁻ˡ S1 aSE ; aE = ++⁻ʳ S1 aSE

  -- …whose window: the skeleton's `[l1, hi)`, the algebra's `[lo, l1)`
  cata-win : ∀ {lo l1 hi S1 E A} → lo ≤ l1 → l1 ≤ hi → Win l1 hi (S1 ++ E) → Win lo l1 A → Win lo hi (S1 ++ (A ++ E))
  cata-win {S1 = S1} lo≤l1 l1≤hi wSE wA =
    All-++⁺ (win-weaken lo≤l1 ≤-refl (++⁻ˡ S1 wSE))
            (All-++⁺ (win-weaken ≤-refl l1≤hi wA) (win-weaken lo≤l1 ≤-refl (++⁻ʳ S1 wSE)))

------------------------------------------------------------------------
-- Concrete skeleton offsets.
------------------------------------------------------------------------

sucs : ℕ → ℕ → ℕ
sucs zero    l = l
sucs (suc k) l = suc (sucs k l)

private
  sucs-+ : ∀ (k l : ℕ) → sucs k l ≡ k + l
  sucs-+ zero    l = refl
  sucs-+ (suc k) l = cong suc (sucs-+ k l)

  sucs-dst : ∀ (l : ℕ) {ks} → Dst ks → Dst (map (λ k → sucs k l) ks)
  sucs-dst l []         = []
  sucs-dst l (px ∷ pxs) = all-map′ px ∷ sucs-dst l pxs
    where
      all-map′ : ∀ {x xs} → All (x ≢_) xs → All (λ y → sucs x l ≢ y) (map (λ k → sucs k l) xs)
      all-map′ []        = []
      all-map′ {x} {y ∷ ys} (p ∷ ps) =
        (λ eq → p (+-cancelʳ-≡ l x y (trans (sym (sucs-+ x l)) (trans eq (sucs-+ y l))))) ∷ all-map′ ps

  -- the offsets below `Kb`, at `l`, lie in `[l, sucs Kb l)`
  sucs-win : ∀ (l Kb : ℕ) {ks} → All (_< Kb) ks → Win l (sucs Kb l) (map (λ k → sucs k l) ks)
  sucs-win l Kb []         = []
  sucs-win l Kb {k ∷ ks} (p ∷ ps) =
    (subst (l ≤_) (sym (sucs-+ k l)) (m≤n+m l k) , subst₂ _<_ (sym (sucs-+ k l)) (sym (sucs-+ Kb l)) (+-monoˡ-< l p))
    ∷ sucs-win l Kb ps

-- concrete offset lists are checked by computation
offsets-dst : ∀ (ks : List ℕ) {_ : True (allPairs? (λ x y → ¬? (x ≟ y)) ks)} → Dst ks
offsets-dst ks {w} = toWitness w

offsets-below : ∀ (Kb : ℕ) (ks : List ℕ) {_ : True (all? (_<? Kb) ks)} → All (_< Kb) ks
offsets-below Kb ks {w} = toWitness w

------------------------------------------------------------------------
-- The cata skeletons
------------------------------------------------------------------------


CataOK : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace) (ab : List (LabelId × ℕ × AbstractTrace)) (lo : ℕ) → Set
CataOK st bb n1 l1 at ab lo =
  Facts (clabs (proj₂ (proj₂ (cata-dispatch st bb n1 l1 at)))) (clabs (blocks-layout ab))
  × Win lo (cata-label-of (cata-dispatch st bb n1 l1 at)) (clabs (proj₂ (proj₂ (cata-dispatch st bb n1 l1 at))))

private
  -- a strategy whose skeleton offsets `ks` (with the algebra spliced after `S1`)
  -- are concrete, below `Kb`
  sucs-cata : ∀ (l1 Kb : ℕ) (ks : List ℕ) (S1 E : List ℕ) → S1 ++ E ≡ map (λ k → sucs k l1) ks
            → Dst ks → All (_< Kb) ks
            → ∀ {lo A C} → lo ≤ l1 → Facts A C → Win lo l1 A → Win lo l1 C
            → Facts (S1 ++ (A ++ E)) C × Win lo (sucs Kb l1) (S1 ++ (A ++ E))
  sucs-cata l1 Kb ks S1 E eq dks bks {lo} lo≤l1 f wA wC =
    cata-gen {S1 = S1} {E = E} (subst Dst (sym eq) (sucs-dst l1 dks))
             (subst (All (l1 ≤_)) (sym eq) (All-map proj₁ (sucs-win l1 Kb bks))) f wA wC
    , cata-win {S1 = S1} {E = E} lo≤l1 (subst (l1 ≤_) (sym (sucs-+ Kb l1)) (m≤n+m l1 Kb))
               (subst (Win l1 (sucs Kb l1)) (sym eq) (sucs-win l1 Kb bks)) wA

cata-frag : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace) (ab : List (LabelId × ℕ × AbstractTrace)) {lo}
          → lo ≤ l1 → Facts (clabs at) (clabs (blocks-layout ab)) → Win lo l1 (clabs at) → Win lo l1 (clabs (blocks-layout ab))
          → CataOK st bb n1 l1 at ab lo
cata-frag strat-const bb n1 l1 at ab {lo} lo≤l1 f wA wC =
  subst (λ T → Facts T (clabs (blocks-layout ab)) × Win lo (l1 + 2) T)
    (sym (cong (l1 ∷_) (clabs-++ at _)))
    ( cata-gen {S1 = l1 ∷ []} {E = l1 + 1 ∷ []} (((λ eq → <⇒≢ l1<l1+1 eq) ∷ []) ∷ [] ∷ [])
               (≤-refl ∷ m≤m+n l1 1 ∷ []) f wA wC
    , cata-win {S1 = l1 ∷ []} {E = l1 + 1 ∷ []} lo≤l1 (m≤m+n l1 2)
               ((≤-refl , ≤-trans l1<l1+1 (+-monoʳ-≤ l1 (s≤s z≤n)))
                ∷ (m≤m+n l1 1 , +-monoʳ-< l1 (s≤s (s≤s z≤n))) ∷ []) wA )
  where
    l1<l1+1 : l1 < l1 + 1
    l1<l1+1 = subst (_< l1 + 1) (+-identityʳ l1) (+-monoʳ-< l1 (s≤s z≤n))
cata-frag strat-nat bb n1 l1 at ab {lo} lo≤l1 f wA wC =
  subst (λ T → Facts T (clabs (blocks-layout ab)) × Win lo (sucs 8 l1) T)
    (sym (cong (S1 ++_) (clabs-++ at _)))
    (sucs-cata l1 8 ks S1 (sucs 7 l1 ∷ []) refl (offsets-dst ks) (offsets-below 8 ks) lo≤l1 f wA wC)
  where
    ks = 0 ∷ 2 ∷ 3 ∷ 1 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ []
    S1 = l1 ∷ sucs 2 l1 ∷ sucs 3 l1 ∷ sucs 1 l1 ∷ sucs 4 l1 ∷ sucs 5 l1 ∷ sucs 6 l1 ∷ []
cata-frag strat-linear bb n1 l1 at ab {lo} lo≤l1 f wA wC =
  subst (λ T → Facts T (clabs (blocks-layout ab)) × Win lo (sucs 6 l1) T)
    (sym (cong (S1 ++_) (clabs-++ at _)))
    (sucs-cata l1 6 ks S1 (sucs 5 l1 ∷ []) refl (offsets-dst ks) (offsets-below 6 ks) lo≤l1 f wA wC)
  where
    ks = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
    S1 = l1 ∷ sucs 1 l1 ∷ sucs 2 l1 ∷ sucs 3 l1 ∷ sucs 4 l1 ∷ []
cata-frag (strat-branching F) bb n1 l1 at ab {lo} lo≤l1 f wA wC =
  subst (λ T → Facts T (clabs (blocks-layout ab)) × Win lo (BLb + 2) T)
    (sym (cong (l1 ∷_) eq))
    ( cata-gen {S1 = S1} {E = E ∷ []} dSE aSE f wA wC
    , cata-win {S1 = S1} {E = E ∷ []} lo≤l1 (≤-trans (m≤m+n l1 4) (≤-trans 4≤V (≤-trans V≤R (m≤m+n BLb 2)))) wSE wA )
  where
    lF = lsize F
    vw = visit-walk n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4)
    rw = rebuild-walk (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4 + lF)
    V  = clabs vw
    R  = clabs rw
    BLb = l1 + 4 + lF + lF
    E  = BLb + 1
    REST = V ++ (suc l1 ∷ (l1 + 2) ∷ (R ++ ((l1 + 3) ∷ BLb ∷ [])))
    S1 = l1 ∷ REST

    shape : ∀ (V R A Es : List ℕ) (b c d t : ℕ)
          → (V ++ (b ∷ c ∷ (R ++ []))) ++ (d ∷ t ∷ (A ++ Es)) ≡ (V ++ (b ∷ c ∷ (R ++ (d ∷ t ∷ [])))) ++ (A ++ Es)
    shape V R A Es b c d t =
      trans (++-assoc V _ _)
        (trans (cong (λ z → V ++ (b ∷ c ∷ z)) (trans (cong (_++ (d ∷ t ∷ (A ++ Es))) (++-identityʳ R))
                                                       (sym (++-assoc R (d ∷ t ∷ []) (A ++ Es)))))
               (sym (++-assoc V _ _)))

    eq : clabs ((vw ++ _) ++ _) ≡ REST ++ (clabs at ++ (E ∷ []))
    eq = trans (clabs-++ (vw ++ _) _)
           (trans (cong₂ _++_ (trans (clabs-++ vw _) (cong (λ z → V ++ (suc l1 ∷ (l1 + 2) ∷ z)) (clabs-++ rw _)))
                              (cong (λ z → (l1 + 3) ∷ BLb ∷ z) (clabs-++ at _)))
                  (shape V R (clabs at) (E ∷ []) (suc l1) (l1 + 2) (l1 + 3) BLb))

    -- the windows, in numeric order
    lt : ∀ {i j} → i < j → l1 + i < l1 + j
    lt = +-monoʳ-< l1
    w1 : Win (l1 + 1) (l1 + 2) (suc l1 ∷ [])
    w1 = (≤-reflexive (+-comm l1 1) , subst (_< l1 + 2) (+-comm l1 1) (lt (s≤s (s≤s z≤n)))) ∷ []
    w2 : Win (l1 + 2) (l1 + 3) ((l1 + 2) ∷ [])
    w2 = (≤-refl , lt (s≤s (s≤s (s≤s z≤n)))) ∷ []
    w3 : Win (l1 + 3) (l1 + 4) ((l1 + 3) ∷ [])
    w3 = (≤-refl , lt (s≤s (s≤s (s≤s (s≤s z≤n))))) ∷ []
    wV : Win (l1 + 4) (l1 + 4 + lF) V
    wV = proj₂ (visit-cl F n1 (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4))
    wR : Win (l1 + 4 + lF) BLb R
    wR = proj₂ (rebuild-cl F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4 + lF))
    wT : Win BLb (BLb + 1) (BLb ∷ [])
    wT = (≤-refl , subst (_< BLb + 1) (+-identityʳ BLb) (+-monoʳ-< BLb (s≤s z≤n))) ∷ []
    wE : Win (BLb + 1) (BLb + 2) (E ∷ [])
    wE = (≤-refl , +-monoʳ-< BLb (s≤s (s≤s z≤n))) ∷ []
    dV = proj₁ (visit-cl F n1 (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4))
    dR = proj₁ (rebuild-cl F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4 + lF))

    4≤V  : l1 + 4 ≤ l1 + 4 + lF
    4≤V  = m≤m+n (l1 + 4) lF
    V≤R  : l1 + 4 + lF ≤ BLb
    V≤R  = m≤m+n (l1 + 4 + lF) lF
    k≤4 : ∀ {k} → k ≤ 4 → l1 + k ≤ l1 + 4
    k≤4 = +-monoʳ-≤ l1
    BL≤ : BLb ≤ BLb + 1
    BL≤ = m≤m+n BLb 1

    one : ∀ {x xs} → Dj (x ∷ []) xs → All (x ≢_) xs
    one (p ∷ []) = p

    D0 : Dst ((l1 + 3) ∷ BLb ∷ [])
    D0 = one (dj-win w3 wT (≤-trans (k≤4 ≤-refl) (≤-trans 4≤V V≤R))) ∷ [] ∷ []
    D1 : Dst (R ++ ((l1 + 3) ∷ BLb ∷ []))
    D1 = dst-++ dR D0 (dj-++ʳ (dj-sym (dj-win w3 wR (≤-trans (k≤4 ≤-refl) 4≤V))) (dj-win wR wT ≤-refl))
    D2 : Dst ((l1 + 2) ∷ (R ++ ((l1 + 3) ∷ BLb ∷ [])))
    D2 = All-++⁺ (one (dj-win w2 wR (≤-trans (k≤4 (s≤s (s≤s (s≤s z≤n)))) 4≤V)))
                 (one (dj-win w2 w3 ≤-refl) ++ᴬ one (dj-win w2 wT (≤-trans (k≤4 (s≤s (s≤s (s≤s z≤n)))) (≤-trans 4≤V V≤R))))
         ∷ D1
      where _++ᴬ_ : ∀ {x y ys} → All (x ≢_) (y ∷ []) → All (x ≢_) ys → All (x ≢_) (y ∷ ys)
            (p ∷ []) ++ᴬ ps = p ∷ ps
    D3 : Dst (suc l1 ∷ (l1 + 2) ∷ (R ++ ((l1 + 3) ∷ BLb ∷ [])))
    D3 = (one (dj-win w1 w2 ≤-refl) ++ᴬ
          All-++⁺ (one (dj-win w1 wR (≤-trans (k≤4 (s≤s (s≤s z≤n))) 4≤V)))
                  (one (dj-win w1 w3 (+-monoʳ-≤ l1 (s≤s (s≤s z≤n))))
                   ++ᴬ one (dj-win w1 wT (≤-trans (k≤4 (s≤s (s≤s z≤n))) (≤-trans 4≤V V≤R)))))
         ∷ D2
      where _++ᴬ_ : ∀ {x y ys} → All (x ≢_) (y ∷ []) → All (x ≢_) ys → All (x ≢_) (y ∷ ys)
            (p ∷ []) ++ᴬ ps = p ∷ ps
    D4 : Dst REST
    D4 = dst-++ dV D3
           (dj-++ʳ (dj-sym (dj-win w1 wV (k≤4 (s≤s (s≤s z≤n)))))
             (dj-++ʳ (dj-sym (dj-win w2 wV (k≤4 (s≤s (s≤s (s≤s z≤n))))))
               (dj-++ʳ (dj-win wV wR ≤-refl)
                 (dj-++ʳ (dj-sym (dj-win w3 wV ≤-refl)) (dj-win wV wT V≤R)))))
    1≤ : ∀ {k} → 1 ≤ k → l1 + 1 ≤ l1 + k
    1≤ = +-monoʳ-≤ l1
    toBL : ∀ {k} → k ≤ 4 → l1 + k ≤ BLb
    toBL k≤ = ≤-trans (k≤4 k≤) (≤-trans 4≤V V≤R)
    wREST : Win (l1 + 1) (BLb + 1) REST
    wREST = All-++⁺ (win-weaken (1≤ (s≤s z≤n)) (≤-trans V≤R BL≤) wV)
              (All-++⁺ (win-weaken ≤-refl (≤-trans (toBL (s≤s (s≤s z≤n))) BL≤) w1)
                (All-++⁺ (win-weaken (1≤ (s≤s z≤n)) (≤-trans (toBL (s≤s (s≤s (s≤s z≤n)))) BL≤) w2)
                  (All-++⁺ (win-weaken (≤-trans (1≤ (s≤s z≤n)) 4≤V) BL≤ wR)
                    (All-++⁺ (win-weaken (1≤ (s≤s z≤n)) (≤-trans (toBL (s≤s (s≤s (s≤s (s≤s z≤n))))) BL≤) w3)
                             (win-weaken (≤-trans (1≤ (s≤s z≤n)) (toBL (s≤s (s≤s (s≤s (s≤s z≤n)))))) ≤-refl wT)))))
    l1<1 : l1 < l1 + 1
    l1<1 = subst (_< l1 + 1) (+-identityʳ l1) (lt (s≤s z≤n))
    wS1 : Win l1 (BLb + 1) S1
    wS1 = (≤-refl , ≤-trans l1<1 (≤-trans (toBL (s≤s z≤n)) BL≤)) ∷ win-weaken (m≤m+n l1 1) ≤-refl wREST
    dSE : Dst (S1 ++ (E ∷ []))
    dSE = dst-++ (fresh-below l1<1 wREST ∷ D4) ([] ∷ []) (dj-win wS1 wE ≤-refl)
    wSE : Win l1 (BLb + 2) (S1 ++ (E ∷ []))
    wSE = All-++⁺ (win-weaken ≤-refl (+-monoʳ-≤ BLb (s≤s z≤n)) wS1)
                  (win-weaken (≤-trans (m≤m+n l1 4) (≤-trans 4≤V (≤-trans V≤R BL≤))) ≤-refl wE)
    aSE : All (l1 ≤_) (S1 ++ (E ∷ []))
    aSE = All-map proj₁ wSE

------------------------------------------------------------------------
-- THE THEOREM
------------------------------------------------------------------------

open import Once.CCC.Codegen.LabelRange o using (cata-label-mono)

private
  sig-frag : ∀ {A B} (si : SigOpInfo A B) (n l : ℕ) (m : Maybe CmpOp) → FragP l l (clabs (sigop-code si n m)) []
  sig-frag si n l nothing  = ([] , [] , []) , [] , []
  sig-frag si n l (just _) = ([] , [] , []) , [] , []

  none : ∀ {lo hi} → FragP lo hi [] []
  none = ([] , [] , []) , [] , []

frag : ∀ {A B} (ir : IR A B) (n l : ℕ) → Frag ir n l
frag id       n l = none
frag fst      n l = none
frag snd      n l = none
frag terminal n l = none
frag initial  n l = none
frag (g ∘ f)  n l =
  transport {P = FragP l l2} (clabs-++ (trace-of Xf) _) (bl-++ (bodies-of Xf) _)
    ( seq-frag (proj₁ Ff) (proj₁ Fg) (proj₁ (proj₂ Ff)) (proj₂ (proj₂ Ff)) (proj₁ (proj₂ Fg)) (proj₂ (proj₂ Fg))
    , seq-win (label-mono f n l) (label-mono g n1 l1) (proj₁ (proj₂ Ff)) (proj₁ (proj₂ Fg))
    , seq-win (label-mono f n l) (label-mono g n1 l1) (proj₂ (proj₂ Ff)) (proj₂ (proj₂ Fg)) )
  where
    Xf = ir-to-trace' n l f
    n1 = proj₁ Xf
    l1 = label-of Xf
    l2 = HI g n1 l1
    Ff = frag f n l
    Fg = frag g n1 l1
frag ⟨ f , g ⟩ n l =
  transport {P = FragP l l2}
    (trans (clabs-++ (trace-of Xf) _) (cong (TL f n4 l ++_) (trans (clabs-++ (trace-of Xg) _) (++-identityʳ _))))
    (bl-++ (bodies-of Xf) _)
    ( seq-frag (proj₁ Ff) (proj₁ Fg) (proj₁ (proj₂ Ff)) (proj₂ (proj₂ Ff)) (proj₁ (proj₂ Fg)) (proj₂ (proj₂ Fg))
    , seq-win (label-mono f n4 l) (label-mono g n1 l1) (proj₁ (proj₂ Ff)) (proj₁ (proj₂ Fg))
    , seq-win (label-mono f n4 l) (label-mono g n1 l1) (proj₂ (proj₂ Ff)) (proj₂ (proj₂ Fg)) )
  where
    n4 = suc (suc (suc (suc n)))
    Xf = ir-to-trace' n4 l f
    n1 = proj₁ Xf
    l1 = label-of Xf
    Xg = ir-to-trace' n1 l1 g
    l2 = HI g n1 l1
    Ff = frag f n4 l
    Fg = frag g n1 l1
frag (curry b) n l =
  transport {P = FragP l l2} refl
    (cong (l ∷_) (trans (clabs-++ (trace-of Xb ++ _) _) (cong (_++ BL b 0 ssl) (trans (clabs-++ (trace-of Xb) _) (++-identityʳ _)))))
    ( ([] , (fresh-below l<ssl wX ∷ dX) , [])
    , []
    , ((≤-refl , <-≤-trans l<ssl (label-mono b 0 ssl)) ∷ win-weaken (≤-trans (n≤1+n l) (n≤1+n (suc l))) ≤-refl wX) )
  where
    ssl = suc (suc l)
    Xb = ir-to-trace' 0 ssl b
    l2 = HI b 0 ssl
    Fb = frag b 0 ssl
    dX = dst-++ (proj₁ (proj₁ Fb)) (proj₁ (proj₂ (proj₁ Fb))) (proj₂ (proj₂ (proj₁ Fb)))
    wX = All-++⁺ (proj₁ (proj₂ Fb)) (proj₂ (proj₂ Fb))
    l<ssl : l < ssl
    l<ssl = ≤-trans (n<1+n l) (n≤1+n (suc l))
frag apply n l = none
frag (SigOp si) n l = sig-frag si n l (cmp-of (sem si))
frag (Call _) n l = none
frag (const fits-int _)   n l = none
frag (const fits-float _) n l = none
frag inl n l = none
frag inr n l = none
frag (case f g) n l =
  transport {P = FragP l l2}
    (trans (clabs-++ (trace-of Xg) _) (cong (λ z → TL g n1 l1 ++ (l ∷ z)) (clabs-++ (trace-of Xf) _)))
    (bl-++ (bodies-of Xf) _)
    ( ( case-dst ssl≤l1 dTf dTg wTf wTg
      , dst-++ dBf dBg (dj-win wBf wBg ≤-refl)
      , dj-++ˡ (dj-++ʳ (dj-sym (dj-win wBf wTg ≤-refl)) jg)
               (All-++⁺ (fresh-below l<ssl wBf) (fresh-below (<-≤-trans l<ssl ssl≤l1) wBg)
                ∷ dj-++ˡ (dj-++ʳ jf (dj-win wTf wBg ≤-refl))
                         (All-++⁺ (fresh-below (n<1+n (suc l)) wBf)
                                  (fresh-below (<-≤-trans (n<1+n (suc l)) ssl≤l1) wBg) ∷ [])) )
    , case-win ssl≤l1 (label-mono g n1 l1) wTf wTg
    , seq-win (≤-trans (≤-trans (n≤1+n l) (n≤1+n (suc l))) ssl≤l1) (label-mono g n1 l1)
              (win-weaken (≤-trans (n≤1+n l) (n≤1+n (suc l))) ≤-refl wBf) wBg )
  where
    ssl = suc (suc l)
    Xf = ir-to-trace' n ssl f
    n1 = proj₁ Xf
    l1 = label-of Xf
    Xg = ir-to-trace' n1 l1 g
    l2 = HI g n1 l1
    ssl≤l1 : ssl ≤ l1
    ssl≤l1 = label-mono f n ssl
    l<ssl : l < ssl
    l<ssl = ≤-trans (n<1+n l) (n≤1+n (suc l))
    Ff = frag f n ssl
    Fg = frag g n1 l1
    dTf = proj₁ (proj₁ Ff) ; dBf = proj₁ (proj₂ (proj₁ Ff)) ; jf = proj₂ (proj₂ (proj₁ Ff))
    dTg = proj₁ (proj₁ Fg) ; dBg = proj₁ (proj₂ (proj₁ Fg)) ; jg = proj₂ (proj₂ (proj₁ Fg))
    wTf = proj₁ (proj₂ Ff) ; wBf = proj₂ (proj₂ Ff)
    wTg = proj₁ (proj₂ Fg) ; wBg = proj₂ (proj₂ Fg)
frag (In _)     n l = none
frag (out-μ _)  n l = none
frag (Cata {F} _ alg) n l =
  proj₁ cf , proj₂ cf , win-weaken ≤-refl (cata-label-mono st (proj₁ XA) n (label-of XA) (trace-of XA)) (proj₂ (proj₂ FA))
  where
    XA = ir-to-trace' 0 l alg
    st = cata-strategy ⌈ F ⌉F
    FA = frag alg 0 l
    cf = cata-frag st (proj₁ XA) n (label-of XA) (trace-of XA) (bodies-of XA) (label-mono alg 0 l)
           (proj₁ FA) (proj₁ (proj₂ FA)) (proj₂ (proj₂ FA))
frag (Out _)    n l = none
frag (in-ν _)   n l = ([] , ([] ∷ []) , []) , [] , ((≤-refl , n<1+n l) ∷ [])
frag (Ana wf c) n l =
  transport {P = FragP l l3} refl (cong (l ∷_) eq)
    ( ([] , (fresh-below (n<1+n l) wAll ∷ dB) , [])
    , []
    , ((≤-refl , <-≤-trans (n<1+n l) (≤-trans (label-mono c 1 (suc l)) l2≤l3)) ∷ win-weaken (n≤1+n l) ≤-refl wAll) )
  where
    Xc = ir-to-trace' 1 (suc l) c
    ct = trace-of Xc
    l2 = label-of Xc
    rt = rs-trace (proj₁ Xc) l2 (ℓ o l) 0 wf
    l3 = rs-label (proj₁ Xc) l2 (ℓ o l) 0 wf
    l2≤l3 : l2 ≤ l3
    l2≤l3 = resuspend-label-mono (proj₁ Xc) l2 (ℓ o l) 0 wf
    Fc = frag c 1 (suc l)
    dCT = proj₁ (proj₁ Fc) ; dCB = proj₁ (proj₂ (proj₁ Fc)) ; jC = proj₂ (proj₂ (proj₁ Fc))
    wCT = proj₁ (proj₂ Fc) ; wCB = proj₂ (proj₂ Fc)
    dRT = proj₁ (resusp-cl (proj₁ Xc) l2 (ℓ o l) 0 wf)
    wRT = proj₂ (resusp-cl (proj₁ Xc) l2 (ℓ o l) 0 wf)
    dB : Dst ((clabs ct ++ clabs rt) ++ BL c 1 (suc l))
    dB = dst-++ (dst-++ dCT dRT (dj-win wCT wRT ≤-refl)) dCB (dj-++ˡ jC (dj-sym (dj-win wCB wRT ≤-refl)))
    wAll : Win (suc l) l3 ((clabs ct ++ clabs rt) ++ BL c 1 (suc l))
    wAll = All-++⁺ (All-++⁺ (win-weaken ≤-refl l2≤l3 wCT) (win-weaken (label-mono c 1 (suc l)) ≤-refl wRT))
                   (win-weaken ≤-refl l2≤l3 wCB)
    eq : clabs (((mov-to-output ∷ store-at-slot 0 ∷ (ct ++ rt)) ++ _) ++ _) ≡ (clabs ct ++ clabs rt) ++ BL c 1 (suc l)
    eq = trans (clabs-++ ((ct ++ rt) ++ _) _)
               (cong (_++ BL c 1 (suc l)) (trans (clabs-++ (ct ++ rt) _) (trans (++-identityʳ _) (clabs-++ ct rt))))

-- …and so a fragment's label definitions, trace then blocks, are distinct.
frag-dst : ∀ {A B} (ir : IR A B) (n l : ℕ) → Dst (TL ir n l ++ BL ir n l)
frag-dst ir n l = dst-++ (proj₁ (proj₁ (frag ir n l))) (proj₁ (proj₂ (proj₁ (frag ir n l)))) (proj₂ (proj₂ (proj₁ (frag ir n l))))

------------------------------------------------------------------------
-- …AND A FRAGMENT DEFINES NO FUNCTION ENTRY: `c-entry (e-fn _)` is only
-- ever a table entry's head (`ProgramImage.fn-image`), never inside a unit.
------------------------------------------------------------------------


private
  nf-bl : ∀ (xs ys : List (LabelId × ℕ × AbstractTrace))
        → NoFn (blocks-layout xs) → NoFn (blocks-layout ys) → NoFn (blocks-layout (xs ++ ys))
  nf-bl xs ys hx hy = subst NoFn (sym (blocks-layout-++ xs ys)) (nf (blocks-layout xs) (blocks-layout ys) hx hy)

visit-nf : ∀ (F : Functor) (todo tv tb s lb : ℕ) → NoFn (visit-walk todo tv tb F s lb)
visit-nf (K _)   todo tv tb s lb = refl
visit-nf Id      todo tv tb s lb = refl
visit-nf (F ⊕ G) todo tv tb s lb =
  nf (visit-walk todo tv tb G (s + 4) (suc (suc lb) + lsize F)) _ (visit-nf G todo tv tb (s + 4) (suc (suc lb) + lsize F))
     (nf (visit-walk todo tv tb F (s + 4) (suc (suc lb))) _ (visit-nf F todo tv tb (s + 4) (suc (suc lb))) refl)
visit-nf (F ⊗ G) todo tv tb s lb =
  nf (visit-walk todo tv tb F (s + 4) lb) _ (visit-nf F todo tv tb (s + 4) lb) (visit-nf G todo tv tb (s + 4) (lb + lsize F))

rebuild-nf : ∀ (F : Functor) (val tv tb s lb : ℕ) → NoFn (rebuild-walk val tv tb F s lb)
rebuild-nf (K _)   val tv tb s lb = refl
rebuild-nf Id      val tv tb s lb = refl
rebuild-nf (F ⊕ G) val tv tb s lb =
  nf (rebuild-walk val tv tb G (s + 4) (suc (suc lb) + lsize F)) _ (rebuild-nf G val tv tb (s + 4) (suc (suc lb) + lsize F))
     (nf (rebuild-walk val tv tb F (s + 4) (suc (suc lb))) _ (rebuild-nf F val tv tb (s + 4) (suc (suc lb))) refl)
rebuild-nf (F ⊗ G) val tv tb s lb =
  nf (rebuild-walk val tv tb G (s + 4) (lb + lsize F)) _ (rebuild-nf G val tv tb (s + 4) (lb + lsize F))
     (nf (rebuild-walk val tv tb F (s + 4) lb) _ (rebuild-nf F val tv tb (s + 4) lb) refl)

resusp-nf : ∀ (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F) → NoFn (rs-trace n l lbl env wf)
resusp-nf n l lbl env (wf-K _) = refl
resusp-nf n l lbl env wf-Id    = refl
resusp-nf n l lbl env (wf-Prod wfF wfG) =
  nf (rs-trace (suc (suc (suc n))) l lbl env wfF) _ (resusp-nf (suc (suc (suc n))) l lbl env wfF)
     (nf (rs-trace (proj₁ (resuspend-layer (suc (suc (suc n))) l lbl env wfF)) (rs-label (suc (suc (suc n))) l lbl env wfF) lbl env wfG) _
         (resusp-nf (proj₁ (resuspend-layer (suc (suc (suc n))) l lbl env wfF)) (rs-label (suc (suc (suc n))) l lbl env wfF) lbl env wfG) refl)
resusp-nf n l lbl env (wf-Sum wfF wfG) =
  nf (tG ++ _) _ (nf tG _ (resusp-nf n2 l2 lbl env wfG) refl)
     (nf (tF ++ _) _ (nf tF _ (resusp-nf (suc (suc (suc n))) (suc (suc l)) lbl env wfF) refl) refl)
  where
    n2 = proj₁ (resuspend-layer (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
    l2 = rs-label (suc (suc (suc n))) (suc (suc l)) lbl env wfF
    tF = rs-trace (suc (suc (suc n))) (suc (suc l)) lbl env wfF
    tG = rs-trace n2 l2 lbl env wfG

private
  cata-nf : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace) → NoFn at
          → NoFn (proj₂ (proj₂ (cata-dispatch st bb n1 l1 at)))
  cata-nf strat-const  bb n1 l1 at h = nf at _ h refl
  cata-nf strat-nat    bb n1 l1 at h = nf at _ h refl
  cata-nf strat-linear bb n1 l1 at h = nf at _ h refl
  cata-nf (strat-branching F) bb n1 l1 at h =
    nf (vw ++ _) _ (nf vw _ (visit-nf F n1 (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4))
                           (nf rw _ (rebuild-nf F (n1 + 2) (n1 + 4) (n1 + 5) (n1 + 7) (l1 + 4 + lsize F)) refl))
                   (nf at _ h refl)
    where
      vw = visit-walk n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4)
      rw = rebuild-walk (n1 + 2) (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4 + lsize F)

  sig-nf : ∀ {A B} (si : SigOpInfo A B) (n : ℕ) (m : Maybe CmpOp) → NoFn (sigop-code si n m)
  sig-nf si n nothing  = refl
  sig-nf si n (just _) = refl

frag-nf : ∀ {A B} (ir : IR A B) (n l : ℕ)
        → NoFn (trace-of (ir-to-trace' n l ir)) × NoFn (blocks-layout (bodies-of (ir-to-trace' n l ir)))
frag-nf id       n l = refl , refl
frag-nf fst      n l = refl , refl
frag-nf snd      n l = refl , refl
frag-nf terminal n l = refl , refl
frag-nf initial  n l = refl , refl
frag-nf (g ∘ f)  n l =
  nf (trace-of Xf) _ (proj₁ (frag-nf f n l)) (proj₁ (frag-nf g _ _))
  , nf-bl (bodies-of Xf) _ (proj₂ (frag-nf f n l)) (proj₂ (frag-nf g _ _))
  where Xf = ir-to-trace' n l f
frag-nf ⟨ f , g ⟩ n l =
  nf (trace-of Xf) _ (proj₁ (frag-nf f _ l)) (nf (trace-of (ir-to-trace' (proj₁ Xf) (label-of Xf) g)) _ (proj₁ (frag-nf g _ _)) refl)
  , nf-bl (bodies-of Xf) _ (proj₂ (frag-nf f _ l)) (proj₂ (frag-nf g _ _))
  where Xf = ir-to-trace' (suc (suc (suc (suc n)))) l f
frag-nf (curry b) n l =
  refl , nf (trace-of Xb ++ _) _ (nf (trace-of Xb) _ (proj₁ (frag-nf b 0 _)) refl) (proj₂ (frag-nf b 0 _))
  where Xb = ir-to-trace' 0 (suc (suc l)) b
frag-nf apply n l = refl , refl
frag-nf (SigOp si) n l = sig-nf si n (cmp-of (sem si)) , refl
frag-nf (Call _) n l = refl , refl
frag-nf (const fits-int _)   n l = refl , refl
frag-nf (const fits-float _) n l = refl , refl
frag-nf inl n l = refl , refl
frag-nf inr n l = refl , refl
frag-nf (case f g) n l =
  nf (trace-of (ir-to-trace' (proj₁ Xf) (label-of Xf) g)) _ (proj₁ (frag-nf g _ _))
     (nf (trace-of Xf) _ (proj₁ (frag-nf f _ _)) refl)
  , nf-bl (bodies-of Xf) _ (proj₂ (frag-nf f _ _)) (proj₂ (frag-nf g _ _))
  where Xf = ir-to-trace' n (suc (suc l)) f
frag-nf (In _)     n l = refl , refl
frag-nf (out-μ _)  n l = refl , refl
frag-nf (Cata {F} _ alg) n l =
  cata-nf (cata-strategy ⌈ F ⌉F) (proj₁ XA) n (label-of XA) (trace-of XA) (proj₁ (frag-nf alg 0 l))
  , proj₂ (frag-nf alg 0 l)
  where XA = ir-to-trace' 0 l alg
frag-nf (Out _)    n l = refl , refl
frag-nf (in-ν _)   n l = refl , refl
frag-nf (Ana wf c) n l =
  refl , nf ((ct ++ rt) ++ _) _ (nf (ct ++ rt) _ (nf ct rt (proj₁ (frag-nf c 1 (suc l))) (resusp-nf (proj₁ Xc) (label-of Xc) (ℓ o l) 0 wf)) refl)
                                 (proj₂ (frag-nf c 1 (suc l)))
  where
    Xc = ir-to-trace' 1 (suc l) c
    ct = trace-of Xc
    rt = rs-trace (proj₁ Xc) (label-of Xc) (ℓ o l) 0 wf
