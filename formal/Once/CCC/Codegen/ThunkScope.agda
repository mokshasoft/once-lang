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

open import Once.CanonicalName using (CanonicalName)

module Once.CCC.Codegen.ThunkScope (o : CanonicalName) where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; suc; _≤_; _<_; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-step)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Empty using (⊥; ⊥-elim)

open import Once.CCC.Label using (LabelId; idx)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-thunk)
open import Once.IRTy using (FitsInRegI; fits-int; fits-float)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.IR using (IR)
import Once.IR as IRm
open IRm.IR
open import Once.IRTy using (⌈_⌉F)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace'; cata-dispatch; cata-strategy; CataStrategy; resuspend-layer)
open import Once.CCC.Codegen.LabelRange o using (label-of; label-mono; cata-label-of; cata-label-mono; resuspend-label-mono)
open import Once.CCC.Codegen.LabelScope o using (trace-of; cata-trace-of)
open import Once.CCC.Codegen.SlotBudget o using (bodies-of)
open import Once.CCC.Label using (ℓ)
open import Data.List.Relation.Unary.All.Properties using (++⁺)

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

  -- Range weakening, `ls-weaken`'s twin (LabelScope.agda:126).
  ts-weaken : ∀ {lo lo' hi hi'} {t} → lo' ≤ lo → hi ≤ hi' → ThunksIn lo hi t → ThunksIn lo' hi' t
  ts-weaken lo≤ hi≤ = All-map (λ ti → mkThunkIn λ m teq →
      (≤-trans lo≤ (proj₁ (in-range ti m teq)) , ≤-trans (proj₂ (in-range ti m teq)) hi≤))

  -- The cata dispatch's own marker range — the `cata-label-mono` twin.
  postulate
    cata-thunks-in : ∀ (st : CataStrategy) (bb n1 l1 : ℕ) (at : AbstractTrace)
                   → ThunksIn l1 (cata-label-of (cata-dispatch st bb n1 l1 at))
                                 (cata-trace-of (cata-dispatch st bb n1 l1 at))

  ------------------------------------------------------------------------
  -- THE INDUCTION. Mirrors `labels-in` (LabelScope.agda:546) for the other
  -- namespace. Every clause whose emitted trace holds no marker is
  -- `all-no-thunk-in _ refl`; the cata strategies are where a marker lives.
  ------------------------------------------------------------------------

  thunks-in : ∀ {A B} (ir : IR A B) (n l : ℕ)
            → ThunksIn l (label-of (ir-to-trace' n l ir)) (trace-of (ir-to-trace' n l ir))
  thunks-in id n l = all-no-thunk-in _ refl
  thunks-in fst        n l = all-no-thunk-in _ refl
  thunks-in snd        n l = all-no-thunk-in _ refl
  thunks-in inl        n l = all-no-thunk-in _ refl
  thunks-in inr        n l = all-no-thunk-in _ refl
  thunks-in terminal   n l = all-no-thunk-in _ refl
  thunks-in initial    n l = all-no-thunk-in _ refl
  thunks-in apply      n l = all-no-thunk-in _ refl
  thunks-in (curry b)  n l = all-no-thunk-in _ refl
  thunks-in (In x)     n l = all-no-thunk-in _ refl
  thunks-in (out-μ x)  n l = all-no-thunk-in _ refl
  thunks-in (Out x)    n l = all-no-thunk-in _ refl
  thunks-in (in-ν x)   n l = all-no-thunk-in _ refl
  -- `const` splits on its `FitsInRegI` witness (IRToTrace.agda:958-959), so
  -- the trace only reduces once that is matched.
  thunks-in (const fits-int   v) n l = all-no-thunk-in _ refl
  thunks-in (const fits-float v) n l = all-no-thunk-in _ refl
  thunks-in (SigOp x)  n l = all-no-thunk-in _ refl
  thunks-in (Ana x c)  n l = all-no-thunk-in _ refl
  thunks-in (g ∘ f)    n l =
    ++⁺ (ts-weaken ≤-refl (label-mono g _ _) (thunks-in f n l))
        (thunk-none-in _ refl ∷ ts-weaken (label-mono f n l) ≤-refl (thunks-in g _ _))
  thunks-in ⟨ f , g ⟩  n l =
    thunk-none-in _ refl ∷ thunk-none-in _ refl ∷
    ++⁺ (ts-weaken ≤-refl (label-mono g _ _) (thunks-in f _ l))
        (thunk-none-in _ refl ∷ thunk-none-in _ refl ∷
         ++⁺ (ts-weaken (label-mono f _ l) ≤-refl (thunks-in g _ _))
             (thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ thunk-none-in _ refl ∷
              thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ thunk-none-in _ refl ∷
              thunk-none-in _ refl ∷ []))
  -- `case` mints only `c-label`s, so every marker slot here is thunk-free; the
  -- structure is `labels-in`'s (LabelScope.agda:586) with the range witnesses
  -- replaced by vacuous ones.
  thunks-in (case f g) n l =
    ++⁺ (thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ [])
        (++⁺ (ts-weaken (≤-trans (≤-step (≤-step ≤-refl)) (label-mono f n (suc (suc l)))) ≤-refl (thunks-in g _ _))
             (++⁺ (thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ thunk-none-in _ refl ∷ [])
                  (++⁺ (ts-weaken (≤-step (≤-step ≤-refl)) (label-mono g _ _) (thunks-in f n (suc (suc l))))
                       (thunk-none-in _ refl ∷ []))))
  -- THE ONE CONSTRUCTOR THAT EMITS A MARKER. `cata-body` (IRToTrace.agda:262-267)
  -- splices `c-thunk (ℓ o body-label) bb` inline, for all four strategies, so
  -- this is the only clause with real content — and it needs the per-strategy
  -- range arithmetic `cata-label-mono` (LabelRange.agda:77) already does for the
  -- `once` namespace. Named separately for that reason.
  thunks-in (Cata {F} x a) n l =
    ts-weaken (label-mono a 0 l) ≤-refl
      (cata-thunks-in (cata-strategy ⌈ F ⌉F)
                   (proj₁ (ir-to-trace' 0 l a)) n
                   (proj₁ (proj₂ (ir-to-trace' 0 l a)))
                   (trace-of (ir-to-trace' 0 l a)))
  thunks-in (Para x a) n l = all-no-thunk-in _ refl
  thunks-in (Hylo x y a t) n l = all-no-thunk-in _ refl
  thunks-in (Fuse x y a t) n l = all-no-thunk-in _ refl

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
  blocks-thunks-in (Para _ _) n l = []
  blocks-thunks-in (SigOp _)  n l = []
  blocks-thunks-in (const fits-int   v) n l = []
  blocks-thunks-in (const fits-float v) n l = []
  blocks-thunks-in (Hylo _ _ _ _) n l = []
  blocks-thunks-in (Fuse _ _ _ _) n l = []
  blocks-thunks-in (g ∘ f)  n l =
    ++⁺ (All-map (λ {b} → bts-weaken b ≤-refl (label-mono g _ _)) (blocks-thunks-in f n l))
        (All-map (λ {b} → bts-weaken b (label-mono f n l) ≤-refl) (blocks-thunks-in g _ _))
  blocks-thunks-in ⟨ f , g ⟩ n l =
    ++⁺ (All-map (λ {b} → bts-weaken b ≤-refl (label-mono g _ _)) (blocks-thunks-in f _ l))
        (All-map (λ {b} → bts-weaken b (label-mono f _ l) ≤-refl) (blocks-thunks-in g _ _))
  blocks-thunks-in (case f g) n l =
    ++⁺ (All-map (λ {b} → bts-weaken b (≤-step (≤-step ≤-refl)) (label-mono g _ _))
                 (blocks-thunks-in f n (suc (suc l))))
        (All-map (λ {b} → bts-weaken b (≤-trans (≤-step (≤-step ≤-refl)) (label-mono f n (suc (suc l)))) ≤-refl)
                 (blocks-thunks-in g _ _))
  -- The window widens to the DISPATCH's outgoing counter, not the algebra's.
  blocks-thunks-in (Cata {F} _ alg) n l =
    All-map (λ {b} → bts-weaken b ≤-refl
              (cata-label-mono (cata-strategy ⌈ F ⌉F)
                               (proj₁ (ir-to-trace' 0 l alg)) n
                               (proj₁ (proj₂ (ir-to-trace' 0 l alg)))
                               (trace-of (ir-to-trace' 0 l alg))))
            (blocks-thunks-in alg 0 l)
  -- THE THREE THAT MINT. Each puts its entry at `ℓ o l` — `idx (ℓ o l)` is `l`
  -- definitionally — so the label sits at the BOTTOM of its own window, and the
  -- body's markers come from the trace-channel induction.
  blocks-thunks-in (curry b) n l =
    ((≤-refl , ≤-trans (≤-step ≤-refl) (label-mono b 0 (suc (suc l))))
      , ts-weaken (≤-step (≤-step ≤-refl)) ≤-refl (thunks-in b 0 (suc (suc l))))
    ∷ All-map (λ {b} → bts-weaken b (≤-step (≤-step ≤-refl)) ≤-refl)
              (blocks-thunks-in b 0 (suc (suc l)))
  -- `in-ν`'s block is the singleton `mov-to-output ∷ []` — no markers at all.
  blocks-thunks-in (in-ν _) n l =
    ((≤-refl , ≤-refl) , all-no-thunk-in _ refl) ∷ []
  blocks-thunks-in (Ana wf c) n l =
    ((≤-refl , ≤-trans (label-mono c 0 (suc l))
                 (resuspend-label-mono (proj₁ (ir-to-trace' 0 (suc l) c))
                                       (proj₁ (proj₂ (ir-to-trace' 0 (suc l) c)))
                                       (ℓ o l) wf))
      , ++⁺ (ts-weaken (≤-step ≤-refl)
               (resuspend-label-mono (proj₁ (ir-to-trace' 0 (suc l) c))
                                     (proj₁ (proj₂ (ir-to-trace' 0 (suc l) c)))
                                     (ℓ o l) wf)
               (thunks-in c 0 (suc l)))
            resusp-free)
    ∷ All-map (λ {b} → bts-weaken b (≤-step ≤-refl)
                (resuspend-label-mono (proj₁ (ir-to-trace' 0 (suc l) c))
                                      (proj₁ (proj₂ (ir-to-trace' 0 (suc l) c)))
                                      (ℓ o l) wf))
              (blocks-thunks-in c 0 (suc l))
    where
      -- The re-suspension pass emits no `c-thunk` — it is branches, loads and
      -- the join labels (D199). Named rather than proved here: it is an
      -- induction over `WellFormedFI`, the same shape `resuspend-label-mono`
      -- already walks for the `once` namespace.
      postulate
        resusp-free : ∀ {lo hi} → ThunksIn lo hi
          (proj₂ (proj₂ (resuspend-layer (proj₁ (ir-to-trace' 0 (suc l) c))
                                         (proj₁ (proj₂ (ir-to-trace' 0 (suc l) c)))
                                         (ℓ o l) wf)))
