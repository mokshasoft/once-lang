-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.ThunkScope — CONTAINMENT FOR THE *THUNK* NAMESPACE.
--
-- `LabelScope` bounds every `once`-namespace label an emitted fragment
-- MENTIONS. It says nothing about `c-thunk`: `once-label-of`
-- (LabelScope.agda:83-89) sends `c-thunk` to `nothing`, because the two are
-- different provenances (D082) — jump targets versus body entries.
--
-- `entry-no-thunks` needs the other one. `find-thunk` scans for `c-thunk`
-- markers, so "no earlier marker carries this block's label" is a fact about
-- THUNK labels, and nothing in the tree bounded them.
--
-- THE TRACE CHANNEL IS NEARLY EMPTY, which is what makes this tractable.
-- `curry`, `Ana` and `in-ν` put their bodies in the BLOCKS list; their emitted
-- traces carry `instr-load-code-addr`, not `c-thunk` (LabelScope's own comment
-- at :566-569 notes the same asymmetry from the `once` side). The ONLY emitted
-- `c-thunk` is `cata-body`'s (IRToTrace.agda:262-267), spliced inline for all
-- four cata strategies.
--
-- So every other constructor is discharged by a DECIDER — `CataIRSlotStable`'s
-- `all-stable?-sound refl` idiom — rather than by a hand-written `All` of
-- vacuous witnesses, one per instruction.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

module Once.CCC.Codegen.ThunkScope (o : CanonicalName) where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; suc; _≤_; _<_; s≤s; z≤n; _+_)
import Data.Nat as ℕ
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n⇒m≤1+n; m≤m+n; +-suc; +-identityʳ; ≤-reflexive; n≤1+n; +-monoʳ-≤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)

open import Once.CCC.Label using (LabelId; module LabelId)
open LabelId using (idx)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-thunk)
open import Once.IRTy using (fits-int; fits-float)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.IR using (IR)
import Once.IR as IRm
open IRm.IR
open import Once.IRTy using (⌈_⌉F; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod)
open import Once.Spec.Type using (K; Id; _⊕_; _⊗_)
open import Once.Spec.Type using (Fun)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Machine.MuRep using (MuRep; mu-box; mu-unit; mu-ptr; mu-rep)
open import Once.CCC.Codegen.IRToTrace o using (sigop-code; ir-to-trace'; cata-dispatch; cata-strategy; CataStrategy; strat-const; strat-box; strat-branching; lsize; fsize; cata-body; cata-call-setup; cata-call; cata-call-box; in-trace; out-trace; cata-br-I₁; cata-br-I₂; visit-walk; rebuild-walk; push2; pop2; wrap-sum; resuspend-layer;
  cata-call-from; inj-trace; env-entry; getμ)
open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; put; put-k; get; get-k; kind; lkind; lsz;
  put-All; put-k-All; get-All; get-k-All)
open import Once.CCC.Codegen.Size using (size)
open import Once.IRTy using (IRTy; IRFunctor; ⟦_⟧TI; ν-type) renaming (_+_ to _+ᵀ_)
open import Once.CCC.Machine.SMCore using (mov-to-output; load-at)
open import Once.CCC.Codegen.LabelRange o using (label-of; label-mono; cata-label-of; cata-label-mono; resuspend-label-mono)
open import Once.CCC.Codegen.LabelScope o using (trace-of; cata-trace-of)
open import Once.CCC.Codegen.SlotBudget o using (bodies-of)
open import Once.CCC.Label using (ℓ)

module Scope {FS : FrameSemantics} where
  open FlatMachine {FS} using (thunk-of?)

  ------------------------------------------------------------------------
  -- The predicate, and its decider.
  ------------------------------------------------------------------------

  -- A record for `LabelIn`'s reason: at a use site the goal must keep the
  -- INSTRUCTION rigid, which a reducing function would not.
  record ThunkIn (lo hi : ℕ) (i : AbstractInstr) : Set where
    constructor mkThunkIn
    field in-range : ∀ (m : LabelId) → thunk-of? i ≡ just m → (lo ≤ idx m) × (idx m < hi)
  open ThunkIn public

  ThunksIn : ℕ → ℕ → AbstractTrace → Set
  ThunksIn lo hi = All (ThunkIn lo hi)

  -- THE DECIDER, defined THROUGH `thunk-of?` rather than by pattern-matching
  -- the 31 `AbstractInstr` constructors. That is what makes the soundness proof
  -- two cases instead of 31: `with thunk-of? i` splits on the RESULT, and the
  -- catch-all never has to reduce on an abstract instruction.
  is-none : Maybe LabelId → Bool
  is-none (just _) = false
  is-none nothing  = true

  no-thunk? : AbstractInstr → Bool
  no-thunk? i = is-none (thunk-of? i)

  all-no-thunk? : AbstractTrace → Bool
  all-no-thunk? []       = true
  all-no-thunk? (i ∷ is) = no-thunk? i ∧ all-no-thunk? is

  no-thunk?-sound : ∀ (i : AbstractInstr) → no-thunk? i ≡ true → thunk-of? i ≡ nothing
  no-thunk?-sound i eq with thunk-of? i
  ... | nothing = refl

  -- An instruction that is not a marker is in EVERY range, vacuously.
  thunk-none-in : ∀ {lo hi} (i : AbstractInstr) → thunk-of? i ≡ nothing → ThunkIn lo hi i
  thunk-none-in i eq = mkThunkIn λ m teq → ⊥-elim (none≢just (trans (sym eq) teq))
    where
      none≢just : ∀ {m : LabelId} → (nothing {A = LabelId}) ≡ just m → ⊥
      none≢just ()

  -- …so a thunk-free trace is, at any range. This is the one-liner every
  -- non-cata clause of the induction below uses: `all-no-thunk-in _ refl`.
  all-no-thunk-in : ∀ {lo hi} (t : AbstractTrace) → all-no-thunk? t ≡ true → ThunksIn lo hi t
  all-no-thunk-in []       _  = []
  all-no-thunk-in (i ∷ is) eq = go (no-thunk? i) refl eq
    where
      go : ∀ (b : Bool) → no-thunk? i ≡ b → (b ∧ all-no-thunk? is) ≡ true
         → ∀ {lo hi} → ThunksIn lo hi (i ∷ is)
      go true  beq eqs = thunk-none-in i (no-thunk?-sound i beq) ∷ all-no-thunk-in is eqs
      go false _   ()

  ------------------------------------------------------------------------
  -- THE RANGE-FREE FORM. "This fragment mints NO marker at all" is stronger
  -- than any window, and it is what the label-LIST reasoning downstream needs:
  -- a window says where a marker would be, `NoThunkT` says there is none, so
  -- `thunk-labels` of such a fragment is literally `[]`.
  --
  -- The recursive walks are stated HERE rather than at `ThunksIn`, and the
  -- windowed form is derived — otherwise the same induction gets written twice.
  ------------------------------------------------------------------------

  NoThunkT : AbstractTrace → Set
  NoThunkT = All (λ i → thunk-of? i ≡ nothing)

  nt-dec : ∀ (t : AbstractTrace) → all-no-thunk? t ≡ true → NoThunkT t
  nt-dec []       _  = []
  nt-dec (i ∷ is) eq = go (no-thunk? i) refl eq
    where
      go : ∀ (b : Bool) → no-thunk? i ≡ b → (b ∧ all-no-thunk? is) ≡ true → NoThunkT (i ∷ is)
      go true  beq eqs = no-thunk?-sound i beq ∷ nt-dec is eqs
      go false _   ()

  ts-from-nt : ∀ {lo hi} {t} → NoThunkT t → ThunksIn lo hi t
  ts-from-nt []         = []
  ts-from-nt (px ∷ pxs) = thunk-none-in _ px ∷ ts-from-nt pxs

  -- plan 0.123 B.4 α: the layout code mints no marker, whatever the type.
  put-nt : ∀ X s b o′ → NoThunkT (put X s b o′)
  put-nt X s b o′ = put-All X s b o′ refl refl refl (λ _ → refl) (λ _ → refl)

  put-k-nt : ∀ kd n s b o′ → NoThunkT (put-k kd n s b o′)
  put-k-nt kd n s b o′ = put-k-All kd n s b o′ refl refl refl (λ _ → refl) (λ _ → refl)

  get-nt : ∀ X k → NoThunkT (get X k)
  get-nt X k = get-All X k (λ _ → refl) (λ _ → refl)

  get-k-nt : ∀ kd n k → NoThunkT (get-k kd n k)
  get-k-nt kd n k = get-k-All kd n k (λ _ → refl) (λ _ → refl)

  getμ-nt : ∀ G k → NoThunkT (getμ G k)
  getμ-nt G k = get-k-nt (lkind G word) (lsz G 1) k

  wrap-nt : ∀ tag pk ps ss s → NoThunkT (wrap-sum tag pk ps ss s)
  wrap-nt tag pk ps ss s =
    refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ ++⁺ (put-k-nt pk ps s (suc s) 1) (refl ∷ [])

  inj-nt : ∀ t P S n → NoThunkT (inj-trace t P S n)
  inj-nt t P S n =
    refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ ++⁺ (put-nt P n (suc n) 1) (refl ∷ [])

  call-nt : ∀ i0 E lk ls cl k ev pr → thunk-of? i0 ≡ nothing → NoThunkT (cata-call-from i0 E lk ls cl k ev pr)
  call-nt i0 E lk ls cl k ev pr e0 =
    e0 ∷ refl ∷ refl ∷ refl ∷
    ++⁺ (put-nt E ev pr 0)
        (++⁺ (put-k-nt lk ls k pr (size E)) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))

  setup-nt : ∀ E cl k ev bl → NoThunkT (cata-call-setup E cl k ev bl)
  setup-nt E cl k ev bl =
    ++⁺ (get-nt E 0) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ [])

  entry-nt : ∀ kd E A → NoThunkT (proj₂ (env-entry kd E A))
  entry-nt word E A = []
  entry-nt flat E A =
    refl ∷ refl ∷ refl ∷ refl ∷ refl ∷
    ++⁺ (get-nt A 1)
        (refl ∷ refl ∷ refl ∷
         ++⁺ (put-nt E 1 3 0) (++⁺ (put-nt A 2 3 (size E)) (refl ∷ refl ∷ [])))

  -- Range weakening, `ls-weaken`'s twin (LabelScope.agda:126).
  ts-weaken : ∀ {lo lo' hi hi'} {t} → lo' ≤ lo → hi ≤ hi' → ThunksIn lo hi t → ThunksIn lo' hi' t
  ts-weaken lo≤ hi≤ = All-map (λ ti → mkThunkIn λ m teq →
      (≤-trans lo≤ (proj₁ (in-range ti m teq)) , ≤-trans (proj₂ (in-range ti m teq)) hi≤))

  -- THE CATA DISPATCH'S OWN MARKER RANGE — `cata-label-mono`'s twin.
  --
  -- `at` is the ALGEBRA's trace and may itself carry markers (a nested `Cata`),
  -- so its bound has to arrive as a HYPOTHESIS: the first statement of this
  -- omitted it and was therefore unprovable, not merely unproved.
  ------------------------------------------------------------------------
  -- THE RE-SUSPENSION PASS EMITS NO MARKER (D199).
  --
  -- It is branches, loads, stores and the `once` join labels; the suspension
  -- it builds carries a CODE ADDRESS (`instr-load-code-addr`), not a
  -- `c-thunk` — the block entry it points at was minted by `Ana` itself. Same
  -- induction `resuspend-label-mono` runs over `WellFormedFI`.
  ------------------------------------------------------------------------
  resuspend-nt : ∀ (H : IRFunctor) (E A : IRTy) (n l : ℕ) (lbl : LabelId) (env : ℕ) {F} (wf : WellFormedFI F)
               → NoThunkT (proj₂ (proj₂ (resuspend-layer H E A n l lbl env wf)))
  resuspend-nt H E A n l lbl env (wf-K _) = []
  resuspend-nt H E A n l lbl env wf-Id    =
    refl ∷ refl ∷
    ++⁺ (get-nt E 0)
        (refl ∷ refl ∷ refl ∷
         ++⁺ (put-nt E (suc n) (suc (suc n)) 0)
             (++⁺ (put-nt A n (suc (suc n)) (size E))
                  (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ [])))
  resuspend-nt H E A n l lbl env (wf-Prod {F} {G} wfF wfG) =
    refl ∷ refl ∷
    ++⁺ (get-nt (⟦ F ⟧TI A) 0)
        (++⁺ (resuspend-nt H E A (suc (suc (suc (suc n)))) l lbl env wfF)
             (refl ∷ refl ∷
              ++⁺ (get-nt (⟦ G ⟧TI A) (size (⟦ F ⟧TI A)))
                  (++⁺ (resuspend-nt H E A (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG)
                       (refl ∷ refl ∷ refl ∷
                        ++⁺ (put-nt (⟦ F ⟧TI (ν-type H)) (suc (suc n)) (suc n) 0)
                            (++⁺ (put-nt (⟦ G ⟧TI (ν-type H)) (suc (suc (suc n))) (suc n) (size (⟦ F ⟧TI (ν-type H))))
                                 (refl ∷ []))))))
    where RF = resuspend-layer H E A (suc (suc (suc (suc n)))) l lbl env wfF
  -- each arm is `restore ∷ get ++ t ++ (6 rows) ++ put ++ (1 row)`
  resuspend-nt H E A n l lbl env (wf-Sum {F} {G} wfF wfG) =
    refl ∷ refl ∷ refl ∷
    ++⁺ (refl ∷ ++⁺ (get-nt (⟦ G ⟧TI A) 1)
                    (++⁺ (resuspend-nt H E A (proj₁ RF) (proj₁ (proj₂ RF)) lbl env wfG)
                         (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷
                          ++⁺ (put-nt (⟦ G ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1) (refl ∷ []))))
        (refl ∷ refl ∷
         ++⁺ (refl ∷ ++⁺ (get-nt (⟦ F ⟧TI A) 1)
                         (++⁺ (resuspend-nt H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF)
                              (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷
                               ++⁺ (put-nt (⟦ F ⟧TI (ν-type H)) (suc (suc n)) (suc n) 1) (refl ∷ []))))
             (refl ∷ []))
    where
      RF = resuspend-layer H E A (suc (suc (suc n))) (suc (suc l)) lbl env wfF

  ------------------------------------------------------------------------
  -- THE COMPILE-TIME FUNCTOR WALKS. These recurse on `F`, so no decider closes
  -- them — they need the same structural induction `visit-walk-ff` runs.
  -- Neither emits a `c-thunk`: both are loads, stores, branches and the `once`
  -- join labels (D082 — a different provenance entirely).
  ------------------------------------------------------------------------
  visit-walk-nt : ∀ (todoSlot tv tb : ℕ) (F : Fun 0) (s lb : ℕ)
                → NoThunkT (visit-walk todoSlot tv tb F s lb)
  visit-walk-nt todoSlot tv tb (K _)   s lb = []
  visit-walk-nt todoSlot tv tb Id      s lb =
    refl ∷ nt-dec (push2 todoSlot tv tb) refl
  visit-walk-nt todoSlot tv tb (F ⊕ G) s lb =
    refl ∷
    ++⁺ (getμ-nt G 1)
        (refl ∷
         ++⁺ (visit-walk-nt todoSlot tv tb G (s + 4) (suc (suc lb) + lsize F))
             (refl ∷ refl ∷
              ++⁺ (getμ-nt F 1)
                  (refl ∷
                   ++⁺ (visit-walk-nt todoSlot tv tb F (s + 4) (suc (suc lb)))
                       (refl ∷ []))))
  visit-walk-nt todoSlot tv tb (F ⊗ G) s lb =
    refl ∷ refl ∷
    ++⁺ (getμ-nt F 0)
        (refl ∷
         ++⁺ (visit-walk-nt todoSlot tv tb F (s + 4) lb)
             (refl ∷
              ++⁺ (getμ-nt G (lsz F 1))
                  (refl ∷ visit-walk-nt todoSlot tv tb G (s + 4) (lb + lsize F))))

  rebuild-walk-nt : ∀ (valSlot tv tb : ℕ) (ck : Kind) (cs : ℕ) (F : Fun 0) (s lb : ℕ)
                  → NoThunkT (rebuild-walk valSlot tv tb ck cs F s lb)
  rebuild-walk-nt valSlot tv tb ck cs (K _)   s lb = refl ∷ []
  rebuild-walk-nt valSlot tv tb ck cs Id      s lb = nt-dec (pop2 valSlot) refl
  rebuild-walk-nt valSlot tv tb ck cs (F ⊕ G) s lb =
    refl ∷
    ++⁺ (getμ-nt G 1)
        (refl ∷
         ++⁺ (rebuild-walk-nt valSlot tv tb ck cs G (s + 4) (suc (suc lb) + lsize F))
             (++⁺ (wrap-nt 1 (lkind G ck) (lsz G cs) (lsz (F ⊕ G) cs) s)
                  (refl ∷ refl ∷
                   ++⁺ (getμ-nt F 1)
                       (refl ∷
                        ++⁺ (rebuild-walk-nt valSlot tv tb ck cs F (s + 4) (suc (suc lb)))
                            (++⁺ (wrap-nt 0 (lkind F ck) (lsz F cs) (lsz (F ⊕ G) cs) s)
                                 (refl ∷ []))))))
  rebuild-walk-nt valSlot tv tb ck cs (F ⊗ G) s lb =
    refl ∷ refl ∷
    ++⁺ (getμ-nt G (lsz F 1))
        (refl ∷
         ++⁺ (rebuild-walk-nt valSlot tv tb ck cs G (s + 4) (lb + lsize F))
             (refl ∷ refl ∷
              ++⁺ (getμ-nt F 0)
                  (refl ∷
                   ++⁺ (rebuild-walk-nt valSlot tv tb ck cs F (s + 4) lb)
                       (refl ∷ refl ∷ refl ∷
                        ++⁺ (put-k-nt (lkind F ck) (lsz F cs) (suc s) (s + 3) 0)
                            (++⁺ (put-k-nt (lkind G ck) (lsz G cs) (s + 2) (s + 3) (lsz F cs))
                                 (refl ∷ []))))))

  -- `cata-br-I₁` splices both walks between literal, marker-free chunks.
  br-I₁-nt : ∀ (ck : Kind) (cs : ℕ) (F : Fun 0) (n1 l1 : ℕ) → NoThunkT (cata-br-I₁ ck cs F n1 l1)
  br-I₁-nt ck cs F n1 l1 =
    refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ 
    ++⁺ (nt-dec (push2 n1 (n1 + 4) (n1 + 5)) refl)
        (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ 
         ++⁺ (nt-dec (push2 (suc n1) (n1 + 4) (n1 + 5)) refl)
             (refl ∷ refl ∷ 
              ++⁺ (visit-walk-nt n1 (n1 + 4) (n1 + 5) F (n1 + 7) (l1 + 4))
                  (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ 
                   ++⁺ (rebuild-walk-nt (n1 + 2) (n1 + 4) (n1 + 5) ck cs F (n1 + 7) (l1 + 4 + lsize F))
                       (refl ∷ []))))

  cata-thunks-in : ∀ (E A : IRTy) (G : Fun 0) (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace) {lo : ℕ}
                 → lo ≤ l1
                 → ThunksIn lo l1 at
                 → ThunksIn lo (cata-label-of (cata-dispatch E A G st bb n1 l1 at))
                              (cata-trace-of (cata-dispatch E A G st bb n1 l1 at))

  -- The marker `cata-body` splices, at `ℓ o l1`: `idx (ℓ o l1)` is `l1`
  -- definitionally, so it sits at the bottom of the window.
  body-marker-in : ∀ (l1 bb : ℕ) {lo hi : ℕ} → lo ≤ l1 → l1 < hi
                 → ThunkIn lo hi (instr-ctrl (c-thunk (ℓ o l1) bb))
  body-marker-in l1 bb lo≤ l<hi = mkThunkIn λ m teq → helper m teq
    where
      helper : ∀ m → thunk-of? (instr-ctrl (c-thunk (ℓ o l1) bb)) ≡ just m
             → _ × _
      helper .(ℓ o l1) refl = (lo≤ , l<hi)

  -- Suc-tower abbreviations: the Nat and linear skeletons index their slots
  -- and labels as `suc`-towers rather than `+` (IRToTrace.agda:377-380), and
  -- spelling them out inline is unreadable.
  s² s³ s⁴ s⁵ s⁶ s⁷ s⁸ s⁹ : ℕ → ℕ
  s² m = suc (suc m)
  s³ m = suc (s² m)
  s⁴ m = suc (s³ m)
  s⁵ m = suc (s⁴ m)
  s⁶ m = suc (s⁵ m)
  s⁷ m = suc (s⁶ m)
  s⁸ m = suc (s⁷ m)
  s⁹ m = suc (s⁸ m)

  -- `m < m + 2` — the `+`-shaped window strat-const and strat-branching use.
  m<m+2 : ∀ (m : ℕ) → m < m + 2
  m<m+2 m = ≤-trans (≤-reflexive (trans (cong suc (sym (+-identityʳ m)))
                                        (sym (+-suc m 0))))
                    (+-monoʳ-≤ m (s≤s z≤n))

  -- THE ONLY EMITTED MARKER. `cata-body bl el bb at` is
  -- `c-jmp ∷ c-thunk (ℓ o bl) bb ∷ (at ++ c-ret ∷ c-label ∷ [])` — one marker,
  -- carrying the body label, and the algebra's own trace in the middle.
  cata-body-in : ∀ (bl el bb : ℕ) (at : AbstractTrace) {lo hi : ℕ}
               → lo ≤ bl → bl < hi → ThunksIn lo hi at
               → ThunksIn lo hi (cata-body bl el bb at)
  cata-body-in bl el bb at lo≤ bl<hi ats =
    thunk-none-in _ refl ∷ body-marker-in bl bb lo≤ bl<hi
    ∷ ++⁺ ats (thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ [])


  ------------------------------------------------------------------------
  -- THE INDUCTION. Mirrors `labels-in` (LabelScope.agda:546) for the other
  -- namespace. Every clause whose emitted trace holds no marker is
  -- `all-no-thunk-in _ refl`; the cata strategies are where a marker lives.
  ------------------------------------------------------------------------

  -- Plan 0.108: a comparison's lowering is straight-line, thunk-free.
  sigop-thunks : ∀ {A B} (si : SigOpInfo A B) (n l : ℕ) (m : Maybe CmpOp)
               → ThunksIn l l (sigop-code si n m)
  sigop-thunks si n l nothing  = all-no-thunk-in _ refl
  sigop-thunks si n l (just _) = all-no-thunk-in _ refl

  -- D366: `In`'s three shapes and `out-μ`'s carry no marker.
  in-nt : ∀ {lo hi} (r : MuRep) (n : ℕ) → ThunksIn lo hi (in-trace r n)
  in-nt mu-box  n = all-no-thunk-in _ refl
  in-nt mu-unit n = all-no-thunk-in _ refl
  in-nt mu-ptr  n = all-no-thunk-in _ refl

  out-nt : ∀ {lo hi} (r : MuRep) → ThunksIn lo hi (out-trace r)
  out-nt mu-box  = all-no-thunk-in _ refl
  out-nt mu-unit = all-no-thunk-in _ refl
  out-nt mu-ptr  = all-no-thunk-in _ refl

  thunks-in : ∀ {A B} (ir : IR A B) (n l : ℕ)
            → ThunksIn l (label-of (ir-to-trace' n l ir)) (trace-of (ir-to-trace' n l ir))
  thunks-in id n l = all-no-thunk-in _ refl
  thunks-in (fst {A} {B}) n l = ts-from-nt (get-nt A 0)
  thunks-in (snd {A} {B}) n l = ts-from-nt (get-nt B (size A))
  thunks-in (inl {A} {B}) n l = ts-from-nt (inj-nt 0 A (A +ᵀ B) n)
  thunks-in (inr {A} {B}) n l = ts-from-nt (inj-nt 1 B (A +ᵀ B) n)
  thunks-in terminal   n l = all-no-thunk-in _ refl
  thunks-in initial    n l = all-no-thunk-in _ refl
  thunks-in (apply {A} {B}) n l =
    ts-from-nt (++⁺ (get-nt A 1)
                    (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷
                     ++⁺ (put-nt A n (suc (suc n)) 1) (refl ∷ refl ∷ refl ∷ [])))
  thunks-in (curry b)  n l = all-no-thunk-in _ refl
  thunks-in (In {F} x)    n l = in-nt (mu-rep F) n
  thunks-in (out-μ {F} x) n l = out-nt (mu-rep F)
  thunks-in (Out x)    n l = all-no-thunk-in _ refl
  thunks-in (in-ν x)   n l = all-no-thunk-in _ refl
  -- `const` splits on its `FitsInRegI` witness (IRToTrace.agda:958-959), so
  -- the trace only reduces once that is matched.
  thunks-in (const fits-int   v) n l = all-no-thunk-in _ refl
  thunks-in (const fits-float v) n l = all-no-thunk-in _ refl
  thunks-in (SigOp x)  n l = sigop-thunks x n l (cmp-of (sem x))
  thunks-in (Call _)  n l = all-no-thunk-in _ refl
  thunks-in (Ana x c)  n l = all-no-thunk-in _ refl
  -- the loop mints only `c-label`s; the round sits above its two.
  thunks-in (Iter {E} {A} {B} b) n l =
    ++⁺ (ts-from-nt (get-nt E 0))
        (thunk-none-in _ refl ∷ thunk-none-in _ refl ∷
         ++⁺ (ts-weaken (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) ≤-refl (thunks-in b _ _))
             (ts-from-nt (refl ∷ refl ∷
                          ++⁺ (get-nt A 1)
                              (refl ∷ refl ∷ refl ∷
                               ++⁺ (put-nt E (suc n) (suc (suc (suc n))) 0)
                                   (++⁺ (put-nt A (suc (suc n)) (suc (suc (suc n))) (size E))
                                        (refl ∷ refl ∷ refl ∷ refl ∷ get-nt B 1))))))
  thunks-in (g ∘ f)    n l =
    ++⁺ (ts-weaken ≤-refl (label-mono g _ _) (thunks-in f n l))
        (thunk-none-in _ refl ∷ ts-weaken (label-mono f n l) ≤-refl (thunks-in g _ _))
  thunks-in (⟨_,_⟩ {A} {B} {C} f g) n l =
    thunk-none-in _ refl ∷ thunk-none-in _ refl ∷
    ++⁺ (ts-weaken ≤-refl (label-mono g _ _) (thunks-in f _ l))
        (thunk-none-in _ refl ∷ thunk-none-in _ refl ∷
         ++⁺ (ts-weaken (label-mono f _ l) ≤-refl (thunks-in g _ _))
             (ts-from-nt (refl ∷ refl ∷ refl ∷
                          ++⁺ (put-nt B (suc n) (suc (suc (suc n))) 0)
                              (++⁺ (put-nt C (suc (suc n)) (suc (suc (suc n))) (size B)) (refl ∷ [])))))
  -- `case` mints only `c-label`s, so every marker slot here is thunk-free; the
  -- structure is `labels-in`'s (LabelScope.agda:586) with the range witnesses
  -- replaced by vacuous ones.
  thunks-in (case {A} {B} f g) n l =
    thunk-none-in _ refl ∷
    ++⁺ (ts-from-nt (get-nt B 1))
        (thunk-none-in _ refl ∷
         ++⁺ (ts-weaken (≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) (label-mono f n (suc (suc l)))) ≤-refl (thunks-in g _ _))
             (thunk-none-in _ refl ∷ thunk-none-in _ refl ∷
              ++⁺ (ts-from-nt (get-nt A 1))
                  (thunk-none-in _ refl ∷
                   ++⁺ (ts-weaken (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) (label-mono g _ _) (thunks-in f n (suc (suc l))))
                       (thunk-none-in _ refl ∷ []))))
  -- THE ONE CONSTRUCTOR THAT EMITS A MARKER. `cata-body` (IRToTrace.agda:262-267)
  -- splices `c-thunk (ℓ o body-label) bb` inline, for all four strategies, so
  -- this is the only clause with real content — and it needs the per-strategy
  -- range arithmetic `cata-label-mono` (LabelRange.agda:77) already does for the
  -- `once` namespace. Named separately for that reason.
  thunks-in (Cata {F} x {E} {A} a) n l =
    cata-thunks-in E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F)
                   (proj₁ (ir-to-trace' 0 l a)) n
                   (proj₁ (proj₂ (ir-to-trace' 0 l a)))
                   (trace-of (ir-to-trace' 0 l a))
                   (label-mono a 0 l)
                   (thunks-in a 0 l)

  ------------------------------------------------------------------------
  -- THE BLOCKS CHANNEL.
  --
  -- `curry`, `Ana` and `in-ν` mint their bodies HERE rather than into the
  -- trace, so this is where their labels live. The shape is
  -- `SlotBudget.blocks-below` (:1316) — a structural walk returning `All` over
  -- `bodies-of` — which is the model the trace channel did not have.
  --
  -- A block is in range when BOTH its entry label and every marker in its body
  -- are: the label is what `find-thunk` will match, the body's markers are what
  -- a LATER block's scan must miss.
  ------------------------------------------------------------------------

  BlockThunksIn : ℕ → ℕ → (LabelId × ℕ × AbstractTrace) → Set
  BlockThunksIn lo hi (lbl , _ , t) = ((lo ≤ idx lbl) × (idx lbl < hi)) × ThunksIn lo hi t

  bts-weaken : ∀ {lo lo' hi hi'} (b : LabelId × ℕ × AbstractTrace) → lo' ≤ lo → hi ≤ hi'
             → BlockThunksIn lo hi b → BlockThunksIn lo' hi' b
  bts-weaken (lbl , _ , t) lo≤ hi≤ ((a , c) , ts) =
    ((≤-trans lo≤ a , ≤-trans c hi≤) , ts-weaken lo≤ hi≤ ts)

  blocks-thunks-in : ∀ {A B} (ir : IR A B) (n l : ℕ)
                   → All (BlockThunksIn l (label-of (ir-to-trace' n l ir)))
                         (bodies-of (ir-to-trace' n l ir))
  blocks-thunks-in id       n l = []
  blocks-thunks-in fst      n l = []
  blocks-thunks-in snd      n l = []
  blocks-thunks-in terminal n l = []
  blocks-thunks-in initial  n l = []
  blocks-thunks-in inl      n l = []
  blocks-thunks-in inr      n l = []
  blocks-thunks-in apply    n l = []
  blocks-thunks-in (In _)    n l = []
  blocks-thunks-in (out-μ _) n l = []
  blocks-thunks-in (Out _)   n l = []
  blocks-thunks-in (SigOp _)  n l = []
  blocks-thunks-in (Call _)  n l = []
  blocks-thunks-in (const fits-int   v) n l = []
  blocks-thunks-in (const fits-float v) n l = []
  blocks-thunks-in (g ∘ f)  n l =
    ++⁺ (All-map (λ {b} → bts-weaken b ≤-refl (label-mono g _ _)) (blocks-thunks-in f n l))
        (All-map (λ {b} → bts-weaken b (label-mono f n l) ≤-refl) (blocks-thunks-in g _ _))
  blocks-thunks-in ⟨ f , g ⟩ n l =
    ++⁺ (All-map (λ {b} → bts-weaken b ≤-refl (label-mono g _ _)) (blocks-thunks-in f _ l))
        (All-map (λ {b} → bts-weaken b (label-mono f _ l) ≤-refl) (blocks-thunks-in g _ _))
  blocks-thunks-in (case f g) n l =
    ++⁺ (All-map (λ {b} → bts-weaken b (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) (label-mono g _ _))
                 (blocks-thunks-in f n (suc (suc l))))
        (All-map (λ {b} → bts-weaken b (≤-trans (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) (label-mono f n (suc (suc l)))) ≤-refl)
                 (blocks-thunks-in g _ _))
  blocks-thunks-in (Iter b) n l =
    All-map (λ {bk} → bts-weaken bk (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) ≤-refl) (blocks-thunks-in b _ _)
  -- The window widens to the DISPATCH's outgoing counter, not the algebra's.
  blocks-thunks-in (Cata {F} _ {E} {A} alg) n l =
    All-map (λ {b} → bts-weaken b ≤-refl
              (cata-label-mono E A ⌈ F ⌉F (cata-strategy ⌈ F ⌉F)
                               (proj₁ (ir-to-trace' 0 l alg)) n
                               (proj₁ (proj₂ (ir-to-trace' 0 l alg)))
                               (trace-of (ir-to-trace' 0 l alg))))
            (blocks-thunks-in alg 0 l)
  -- THE THREE THAT MINT. Each puts its entry at `ℓ o l` — `idx (ℓ o l)` is `l`
  -- definitionally — so the label sits at the BOTTOM of its own window, and the
  -- body's markers come from the trace-channel induction.
  blocks-thunks-in (curry {E} {A} b) n l =
    ((≤-refl , ≤-trans (m≤n⇒m≤1+n ≤-refl) (label-mono b _ (suc (suc l))))
      , ++⁺ (ts-from-nt (entry-nt (kind E) E A))
            (ts-weaken (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) ≤-refl (thunks-in b _ (suc (suc l)))))
    ∷ All-map (λ {b} → bts-weaken b (m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)) ≤-refl)
              (blocks-thunks-in b _ (suc (suc l)))
  -- `in-ν`'s block is the singleton `mov-to-output ∷ []` — no markers at all.
  blocks-thunks-in (in-ν _) n l =
    ((≤-refl , ≤-refl) , all-no-thunk-in _ refl) ∷ []
  blocks-thunks-in (Ana {F} wf {E} {A} c) n l =
    ((≤-refl , ≤-trans (label-mono c 1 (suc l))
                 (resuspend-label-mono F E A (proj₁ (ir-to-trace' 1 (suc l) c))
                                       (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c)))
                                       (ℓ o l) 0 wf))
      , ++⁺ (ts-from-nt (nt-dec (AbstractInstr.mov-to-output ∷ AbstractInstr.store-at-slot 0 ∷ []) refl)) (++⁺ (ts-weaken (m≤n⇒m≤1+n ≤-refl)
               (resuspend-label-mono F E A (proj₁ (ir-to-trace' 1 (suc l) c))
                                     (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c)))
                                     (ℓ o l) 0 wf)
               (thunks-in c 1 (suc l)))
            (ts-from-nt (resuspend-nt F E A (proj₁ (ir-to-trace' 1 (suc l) c))
                                      (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c)))
                                      (ℓ o l) 0 wf))))
    ∷ All-map (λ {b} → bts-weaken b (m≤n⇒m≤1+n ≤-refl)
                (resuspend-label-mono F E A (proj₁ (ir-to-trace' 1 (suc l) c))
                                      (proj₁ (proj₂ (ir-to-trace' 1 (suc l) c)))
                                      (ℓ o l) 0 wf))
              (blocks-thunks-in c 1 (suc l))
  -- Every strategy ends the same way: a thunk-free skeleton (`cata-call-setup`,
  -- the `cata-call`s and the `I` fragments carry no `c-thunk`) followed by ONE
  -- `cata-body`, whose marker is the body label. So the four clauses differ
  -- only in how the prelude is bracketed and in the label arithmetic.
  cata-thunks-in E A G strat-const bb n1 l1 at lo≤ ats =
    ++⁺ (ts-from-nt (setup-nt E n1 (n1 + 1) (n1 + 2) l1))
        (++⁺ (ts-from-nt (call-nt mov-to-output E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3) refl))
             (cata-body-in l1 (l1 + 1) bb at lo≤ (m<m+2 l1)
                (ts-weaken ≤-refl (m≤m+n l1 2) ats)))
  cata-thunks-in E A G strat-box bb n1 l1 at lo≤ ats =
    ++⁺ (ts-from-nt (setup-nt E n1 (n1 + 1) (n1 + 2) l1))
        (++⁺ (ts-from-nt (call-nt (load-at 0) E (lkind G word) (lsz G 1) n1 (n1 + 1) (n1 + 2) (n1 + 3) refl))
             (cata-body-in l1 (l1 + 1) bb at lo≤ (m<m+2 l1)
                (ts-weaken ≤-refl (m≤m+n l1 2) ats)))
  cata-thunks-in E A G (strat-branching F) bb n1 l1 at lo≤ ats =
    ++⁺ (ts-from-nt (setup-nt E B (B + 1) (B + 2) L))
        (++⁺ (ts-from-nt (br-I₁-nt (kind A) (size A) F n1 l1))
             (++⁺ (ts-from-nt (call-nt mov-to-output E (lkind F (kind A)) (lsz F (size A)) B (B + 1) (B + 2) (B + 3) refl))
                  (++⁺ (all-no-thunk-in (cata-br-I₂ n1 l1) refl)
                       (cata-body-in L (L + 1) bb at
                          (≤-trans lo≤ low) (m<m+2 L)
                          (ts-weaken ≤-refl (cata-label-mono E A G (strat-branching F) bb n1 l1 at) ats)))))
    where
      B : ℕ
      B = n1 + 7 + (4 ℕ.* fsize F) + 4
      L : ℕ
      L = l1 + 4 + lsize F + lsize F
      low : l1 ≤ L
      low = ≤-trans (m≤m+n l1 4)
              (≤-trans (m≤m+n (l1 + 4) (lsize F))
                       (m≤m+n (l1 + 4 + lsize F) (lsize F)))

