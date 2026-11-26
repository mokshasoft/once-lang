-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.RoomReserve — the start's reserve is invisible to all but
-- the start (D491 stage 4).
--
-- The room-check pass sets the start's reserve (`RoomChecks.reserve`) to the
-- depth of the start's segment. Nothing else reads it: not the flat machine
-- (the start runs `do-thunk b` whatever it reserves), not the pass's measure
-- (the start's kind spends nothing and owns nothing), not the scans (the start
-- is neither a label nor an entry). One view says so (`re-same`: an
-- instruction is the start, or `re` keeps it), and every fact below is that
-- view, instance by instance (`re-inv`), lifted to traces.
------------------------------------------------------------------------

module Once.CCC.Codegen.RoomReserve where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; sym)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Machine.SMCore
  using ( AbstractInstr; AbstractTrace; Room
        ; mov-to-output; mov-to-input; load-indirect; load-indirect-suc; load-from-slot; store-at-slot
        ; store-indirect; store-indirect-suc; lea-slot; restore-input; instr-alloc-stack; instr-dealloc-stack
        ; instr-reclaim-to; instr-push-frame; instr-pop-frame; instr-call-closure; worklist-init
        ; worklist-push; worklist-pop; worklist-check; instr-sigop; instr-load-const; instr-load-code-addr
        ; instr-save-closure-reg; instr-load-tag-lit; instr-alloc-heap; instr-reg-op; instr-ctrl
        ; instr-free-heap; load-at; store-at; addr-at; instr-room
        ; c-label; c-jmp; c-branch-tag-zero; c-entry; c-ret; c-call-fn; c-start; c-leave )
open import Once.CCC.Codegen.StackDepth using (Depths; Owner; own; owner-from; before-from)
open import Once.CCC.Codegen.RoomChecks
  using (re; reserve; room?; strip; max-entry; entry-frame; spend; boundary?; stretch; checks; till-check; r0; _⊕ʳ_)

------------------------------------------------------------------------
-- THE VIEW: the start, or kept
------------------------------------------------------------------------
StartAt : AbstractInstr → Set
StartAt i = Σ ℕ (λ b → Σ ℕ (λ r → i ≡ instr-ctrl (c-start b r)))

re-same : ∀ (n : ℕ) (i : AbstractInstr) → StartAt i ⊎ re n i ≡ i
re-same n mov-to-output                   = inj₂ refl
re-same n mov-to-input                    = inj₂ refl
re-same n load-indirect                   = inj₂ refl
re-same n load-indirect-suc               = inj₂ refl
re-same n (load-from-slot _)              = inj₂ refl
re-same n (store-at-slot _)               = inj₂ refl
re-same n store-indirect                  = inj₂ refl
re-same n store-indirect-suc              = inj₂ refl
re-same n (lea-slot _)                    = inj₂ refl
re-same n (restore-input _)               = inj₂ refl
re-same n (instr-alloc-stack _)           = inj₂ refl
re-same n (instr-dealloc-stack _)         = inj₂ refl
re-same n (instr-reclaim-to _)            = inj₂ refl
re-same n (instr-push-frame _)            = inj₂ refl
re-same n instr-pop-frame                 = inj₂ refl
re-same n instr-call-closure              = inj₂ refl
re-same n (worklist-init _)               = inj₂ refl
re-same n (worklist-push _)               = inj₂ refl
re-same n (worklist-pop _)                = inj₂ refl
re-same n (worklist-check _)              = inj₂ refl
re-same n (instr-sigop _)                 = inj₂ refl
re-same n (instr-load-const _ _)          = inj₂ refl
re-same n (instr-load-code-addr _)        = inj₂ refl
re-same n instr-save-closure-reg          = inj₂ refl
re-same n (instr-load-tag-lit _)          = inj₂ refl
re-same n (instr-alloc-heap _)            = inj₂ refl
re-same n (instr-reg-op _)                = inj₂ refl
re-same n (instr-free-heap _)             = inj₂ refl
re-same n (load-at _)                     = inj₂ refl
re-same n (store-at _)                    = inj₂ refl
re-same n (addr-at _)                     = inj₂ refl
re-same n (AbstractInstr.load-rec _)      = inj₂ refl
re-same n (AbstractInstr.store-rec _)     = inj₂ refl
re-same n (instr-room _)                  = inj₂ refl
re-same n (instr-ctrl (c-label _))        = inj₂ refl
re-same n (instr-ctrl (c-jmp _))          = inj₂ refl
re-same n (instr-ctrl (c-branch-tag-zero _)) = inj₂ refl
re-same n (instr-ctrl (c-entry _ _))      = inj₂ refl
re-same n (instr-ctrl (c-ret _))          = inj₂ refl
re-same n (instr-ctrl (c-call-fn _))      = inj₂ refl
re-same n (instr-ctrl c-leave)            = inj₂ refl
re-same n (instr-ctrl (c-start b r))      = inj₁ (b , r , refl)

-- WHAT DOES NOT READ THE RESERVE does not see `re`
re-inv : ∀ {ℓ : Level} {X : Set ℓ} (g : AbstractInstr → X)
       → (∀ b r r′ → g (instr-ctrl (c-start b r)) ≡ g (instr-ctrl (c-start b r′)))
       → ∀ (n : ℕ) (i : AbstractInstr) → g (re n i) ≡ g i
re-inv g h n i = go i (re-same n i)
  where
    go : ∀ (j : AbstractInstr) → StartAt j ⊎ re n j ≡ j → g (re n j) ≡ g j
    go .(instr-ctrl (c-start b r)) (inj₁ (b , r , refl)) = h b n r
    go j                           (inj₂ e)              = cong g e

-- what is not a start was not changed
re-keep : ∀ (n : ℕ) (y x : AbstractInstr) → re n y ≡ x → (∀ b r → x ≡ instr-ctrl (c-start b r) → ⊥) → y ≡ x
re-keep n y x e ns = go y (re-same n y) e
  where
    go : ∀ (z : AbstractInstr) → StartAt z ⊎ re n z ≡ z → re n z ≡ x → z ≡ x
    go .(instr-ctrl (c-start b r)) (inj₁ (b , r , refl)) e′ = ⊥-elim (ns b n (sym e′))
    go z                           (inj₂ s)              e′ = trans (sym s) e′

-- …and what is a start was one (with its own reserve)
private
  start-back′ : ∀ (n : ℕ) (z : AbstractInstr) (b rsv : ℕ) → StartAt z ⊎ re n z ≡ z → re n z ≡ instr-ctrl (c-start b rsv)
              → Σ ℕ (λ r′ → z ≡ instr-ctrl (c-start b r′))
  start-back′ n .(instr-ctrl (c-start b′ r′)) b rsv (inj₁ (b′ , r′ , refl)) refl = r′ , refl
  start-back′ n z                             b rsv (inj₂ s)                 e    = rsv , trans (sym s) e

start-back : ∀ (n : ℕ) (y : AbstractInstr) (b rsv : ℕ) → re n y ≡ instr-ctrl (c-start b rsv)
           → Σ ℕ (λ r′ → y ≡ instr-ctrl (c-start b r′))
start-back n y b rsv e = start-back′ n y b rsv (re-same n y) e

-- setting twice is setting once
re-twice : ∀ (n m : ℕ) (i : AbstractInstr) → re n (re m i) ≡ re n i
re-twice n m i = re-inv (re n) (λ _ _ _ → refl) m i

-- the instance list
re-room? : ∀ n i → room? (re n i) ≡ room? i
re-room? = re-inv room? (λ _ _ _ → refl)

re-boundary? : ∀ n i → boundary? (re n i) ≡ boundary? i
re-boundary? = re-inv boundary? (λ _ _ _ → refl)

re-own : ∀ (o : Owner) n i → own o (re n i) ≡ own o i
re-own o = re-inv (own o) (λ _ _ _ → refl)

re-spend : ∀ (T : Depths) (o : Owner) n i → spend T o (re n i) ≡ spend T o i
re-spend T o = re-inv (spend T o) (λ _ _ _ → refl)

re-entry-frame : ∀ n i → entry-frame (re n i) ≡ entry-frame i
re-entry-frame = re-inv entry-frame (λ _ _ _ → refl)

------------------------------------------------------------------------
-- LIFTED TO TRACES
------------------------------------------------------------------------
reserve-twice : ∀ (n m : ℕ) (t : AbstractTrace) → reserve n (reserve m t) ≡ reserve n t
reserve-twice n m []      = refl
reserve-twice n m (i ∷ t) = cong₂ _∷_ (re-twice n m i) (reserve-twice n m t)

reserve-drop : ∀ (n k : ℕ) (t : AbstractTrace) → drop k (reserve n t) ≡ reserve n (drop k t)
reserve-drop n zero    t       = refl
reserve-drop n (suc k) []      = refl
reserve-drop n (suc k) (i ∷ t) = reserve-drop n k t

max-entry-reserve : ∀ (n : ℕ) (t : AbstractTrace) → max-entry (reserve n t) ≡ max-entry t
max-entry-reserve n []      = refl
max-entry-reserve n (i ∷ t) = cong₂ Data.Nat._⊔_ (re-entry-frame n i) (max-entry-reserve n t)
  where import Data.Nat

owner-from-reserve : ∀ (n : ℕ) (o : Owner) (t : AbstractTrace) (pc : ℕ) → owner-from o (reserve n t) pc ≡ owner-from o t pc
owner-from-reserve n o []      pc      = refl
owner-from-reserve n o (i ∷ t) zero    = re-own o n i
owner-from-reserve n o (i ∷ t) (suc pc) =
  trans (cong (λ o′ → owner-from o′ (reserve n t) pc) (re-own o n i)) (owner-from-reserve n (own o i) t pc)

before-from-reserve : ∀ (n : ℕ) (o : Owner) (t : AbstractTrace) (pc : ℕ) → before-from o (reserve n t) pc ≡ before-from o t pc
before-from-reserve n o []      pc      = refl
before-from-reserve n o (i ∷ t) zero    = refl
before-from-reserve n o (i ∷ t) (suc pc) =
  trans (cong (λ o′ → before-from o′ (reserve n t) pc) (re-own o n i)) (before-from-reserve n (own o i) t pc)

-- (what a stretch spends is the same)
stretch-reserve : ∀ (n : ℕ) (T : Depths) (o : Owner) (t : AbstractTrace) → stretch T o (reserve n t) ≡ stretch T o t
stretch-reserve n T o []      = refl
stretch-reserve n T o (i ∷ t) =
  trans (cong₂ (λ o′ b → spend T o′ (re n i) ⊕ʳ (if b then r0 else stretch T o′ (reserve n t))) (re-own o n i) (re-boundary? n i))
        (cong₂ (λ s x → s ⊕ʳ (if boundary? i then r0 else x)) (re-spend T (own o i) n i) (stretch-reserve n T (own o i) t))

-- (…and so is what follows a check)
till-reserve : ∀ (n : ℕ) (T : Depths) (o : Owner) (t : AbstractTrace) → till-check T o (reserve n t) ≡ till-check T o t
till-reserve n T o []      = refl
till-reserve n T o (i ∷ t) =
  trans (cong₂ (λ o′ b → if b then r0 else spend T o′ (re n i) ⊕ʳ till-check T o′ (reserve n t)) (re-own o n i) (re-room? n i))
        (cong₂ (λ s x → if room? i then r0 else s ⊕ʳ x) (re-spend T (own o i) n i) (till-reserve n T (own o i) t))

-- THE PASS COMMUTES WITH THE RESERVE: checks go where they went, with the same `k`
private
  if-reserve : ∀ (n : ℕ) (b : Bool) (k : Room) (C : AbstractTrace)
             → (if b then instr-room k ∷ reserve n C else reserve n C) ≡ reserve n (if b then instr-room k ∷ C else C)
  if-reserve n true  k C = refl
  if-reserve n false k C = refl

checks-reserve : ∀ (n : ℕ) (T : Depths) (o : Owner) (t : AbstractTrace) → checks T o (reserve n t) ≡ reserve n (checks T o t)
checks-reserve n T o []      = refl
checks-reserve n T o (i ∷ t) =
  cong (re n i ∷_)
    (trans (cong₂ (λ o′ b → if b then instr-room (stretch T o′ (reserve n t)) ∷ checks T o′ (reserve n t) else checks T o′ (reserve n t))
                  (re-own o n i) (re-boundary? n i))
    (trans (cong₂ (λ k C → if boundary? i then instr-room k ∷ C else C)
                  (stretch-reserve n T (own o i) t) (checks-reserve n T (own o i) t))
           (if-reserve n (boundary? i) (stretch T (own o i) t) (checks T (own o i) t))))

-- …and reading the pass's input back off its output
private
  strip-if : ∀ (n : ℕ) (b : Bool) (i : AbstractInstr) (S : AbstractTrace)
           → (if b then reserve n S else re n i ∷ reserve n S) ≡ reserve n (if b then S else i ∷ S)
  strip-if n true  i S = refl
  strip-if n false i S = refl

strip-reserve : ∀ (n : ℕ) (t : AbstractTrace) → strip (reserve n t) ≡ reserve n (strip t)
strip-reserve n []      = refl
strip-reserve n (i ∷ t) =
  trans (cong₂ (λ b S → if b then S else re n i ∷ S) (re-room? n i) (strip-reserve n t))
        (strip-if n (room? i) i (strip t))

NoRoom-reserve : ∀ (n : ℕ) (t : AbstractTrace) → All (λ i → room? i ≡ false) t → All (λ i → room? i ≡ false) (reserve n t)
NoRoom-reserve n []      []       = []
NoRoom-reserve n (i ∷ t) (e ∷ a) = trans (re-room? n i) e ∷ NoRoom-reserve n t a

-- a property of every instruction that does not read the reserve
All-reserve : ∀ {P : AbstractInstr → Set} (n : ℕ) (t : AbstractTrace)
            → (∀ i → P i → P (re n i)) → All P t → All P (reserve n t)
All-reserve n []      h []       = []
All-reserve n (i ∷ t) h (p ∷ a) = h i p ∷ All-reserve n t h a

------------------------------------------------------------------------
-- THE MACHINE: it fetches the instruction with the reserve set, finds every
-- label and entry where it was, and steps as without it
------------------------------------------------------------------------
module ReserveRun {FS : FrameSemantics} where
  open FlatMachine {FS}
    using (fetch; flat-exec-instr; FlatState; label-of?; entry-of?; fl-go; fl-at; fl-label-match
          ; ft-go; ft-at; ft-match; find-label; find-entry)
  open import Once.CCC.Label using (LabelId; _≡ᵇᴵ_; EntryId; _≡ᵇᴱ_)

  fetch-reserve : ∀ (n : ℕ) (t : AbstractTrace) (j : ℕ) → fetch (reserve n t) j ≡ mmap (re n) (fetch t j)
  fetch-reserve n []      j       = refl
  fetch-reserve n (i ∷ t) zero    = refl
  fetch-reserve n (i ∷ t) (suc j) = fetch-reserve n t j

  -- what the image with the reserve set holds, the image held — unless it is the start
  fetch-back : ∀ (n : ℕ) (t : AbstractTrace) (j : ℕ) {x : AbstractInstr} → fetch (reserve n t) j ≡ just x
             → Σ AbstractInstr (λ y → fetch t j ≡ just y × re n y ≡ x)
  fetch-back n []      j       ()
  fetch-back n (i ∷ t) zero    refl = i , refl , refl
  fetch-back n (i ∷ t) (suc j) f    = fetch-back n t j f

  fetch-under : ∀ (n : ℕ) (t : AbstractTrace) (j : ℕ) {x : AbstractInstr} → fetch (reserve n t) j ≡ just x
              → (∀ b r → x ≡ instr-ctrl (c-start b r) → ⊥) → fetch t j ≡ just x
  fetch-under n t j {x} f ns = go (fetch-back n t j f)
    where
      go : Σ AbstractInstr (λ y → fetch t j ≡ just y × re n y ≡ x) → fetch t j ≡ just x
      go (y , fy , ey) = trans fy (cong just (re-keep n y x ey ns))

  exec-re : ∀ (n : ℕ) (i : AbstractInstr) (P : AbstractTrace) (fs : FlatState)
          → flat-exec-instr (re n i) P fs ≡ flat-exec-instr i P fs
  exec-re n i P fs = re-inv (λ j → flat-exec-instr j P fs) (λ _ _ _ → refl) n i

  fl-go-reserve : ∀ (n : ℕ) (t : AbstractTrace) (m : LabelId) (a : ℕ) → fl-go (reserve n t) m a ≡ fl-go t m a
  fl-at-reserve : ∀ (n : ℕ) (ml : Maybe LabelId) (t : AbstractTrace) (m : LabelId) (a : ℕ) → fl-at ml (reserve n t) m a ≡ fl-at ml t m a
  fl-lm-reserve : ∀ (n : ℕ) (c : Bool) (t : AbstractTrace) (m : LabelId) (a : ℕ) → fl-label-match c (reserve n t) m a ≡ fl-label-match c t m a
  fl-go-reserve n []      m a = refl
  fl-go-reserve n (i ∷ t) m a =
    trans (cong (λ ml → fl-at ml (reserve n t) m a) (re-inv label-of? (λ _ _ _ → refl) n i)) (fl-at-reserve n (label-of? i) t m a)
  fl-at-reserve n (just l) t m a = fl-lm-reserve n (l ≡ᵇᴵ m) t m a
  fl-at-reserve n nothing  t m a = fl-go-reserve n t m (suc a)
  fl-lm-reserve n true  t m a = refl
  fl-lm-reserve n false t m a = fl-go-reserve n t m (suc a)

  find-label-reserve : ∀ (n : ℕ) (t : AbstractTrace) (m : LabelId) → find-label (reserve n t) m ≡ find-label t m
  find-label-reserve n t m = fl-go-reserve n t m 0

  ft-go-reserve : ∀ (n : ℕ) (t : AbstractTrace) (e : EntryId) (a : ℕ) → ft-go (reserve n t) e a ≡ ft-go t e a
  ft-at-reserve : ∀ (n : ℕ) (me : Maybe EntryId) (t : AbstractTrace) (e : EntryId) (a : ℕ) → ft-at me (reserve n t) e a ≡ ft-at me t e a
  ft-m-reserve  : ∀ (n : ℕ) (c : Bool) (t : AbstractTrace) (e : EntryId) (a : ℕ) → ft-match c (reserve n t) e a ≡ ft-match c t e a
  ft-go-reserve n []      e a = refl
  ft-go-reserve n (i ∷ t) e a =
    trans (cong (λ me → ft-at me (reserve n t) e a) (re-inv entry-of? (λ _ _ _ → refl) n i)) (ft-at-reserve n (entry-of? i) t e a)
  ft-at-reserve n (just l) t e a = ft-m-reserve n (l ≡ᵇᴱ e) t e a
  ft-at-reserve n nothing  t e a = ft-go-reserve n t e (suc a)
  ft-m-reserve n true  t e a = refl
  ft-m-reserve n false t e a = ft-go-reserve n t e (suc a)

  find-entry-reserve : ∀ (n : ℕ) (t : AbstractTrace) (e : EntryId) → find-entry (reserve n t) e ≡ find-entry t e
  find-entry-reserve n t e = ft-go-reserve n t e 0

------------------------------------------------------------------------
-- MEMBERSHIP, for an instruction that is not the start
------------------------------------------------------------------------
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

re-fix : ∀ (n : ℕ) (i : AbstractInstr) → (∀ b r → i ≡ instr-ctrl (c-start b r) → ⊥) → re n i ≡ i
re-fix n i ns = go i (re-same n i) ns
  where
    go : ∀ (j : AbstractInstr) → StartAt j ⊎ re n j ≡ j → (∀ b r → j ≡ instr-ctrl (c-start b r) → ⊥) → re n j ≡ j
    go .(instr-ctrl (c-start b r)) (inj₁ (b , r , refl)) ns′ = ⊥-elim (ns′ b r refl)
    go j                           (inj₂ s)              ns′ = s

∈-reserve : ∀ (n : ℕ) {i : AbstractInstr} (t : AbstractTrace) → (∀ b r → i ≡ instr-ctrl (c-start b r) → ⊥)
          → i ∈ t → i ∈ reserve n t
∈-reserve n {i} (x ∷ t) ns (here e)  = here (trans e (sym (re-fix n x (λ b r e′ → ns b r (trans e e′)))))
∈-reserve n {i} (x ∷ t) ns (there m) = there (∈-reserve n t ns m)

∈-reserve-back : ∀ (n : ℕ) {i : AbstractInstr} (t : AbstractTrace) → (∀ b r → i ≡ instr-ctrl (c-start b r) → ⊥)
               → i ∈ reserve n t → i ∈ t
∈-reserve-back n {i} (x ∷ t) ns (here e)  = here (sym (re-keep n x i (sym e) ns))
∈-reserve-back n {i} (x ∷ t) ns (there m) = there (∈-reserve-back n t ns m)
