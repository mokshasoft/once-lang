-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandEmitted — the expansion of an image is an image
-- the arch layer runs (D468/D470, plan 0.146 B1.6 item 3c4).
--
-- What the arch layer reads of a program (`RunContext.Emitted`) holds of the
-- expansion when it holds of the primitive program: everything the expansion
-- fetches is a primitive instruction's own, or of an alloc's, a free's or the
-- start's code (`fetch-inv`), and that code is the arch layer's (record words
-- below `rec-size`: a class's head word is `3 + c`, `c < count C ≤ 61`), has
-- no start, no call, no entry and no code word; the entries, the functions
-- and the code words are found where the pc map puts them (`ft-exp`).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandEmitted {FS : FrameSemantics} where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Empty
import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (fetch)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; exp-view; ExpView; ev-alloc; ev-free; ev-start; ev-same)

------------------------------------------------------------------------
-- A fetch from an append: from its left part, or past it
------------------------------------------------------------------------

fetch-split : ∀ (xs ys : AbstractTrace) k {j} → fetch (xs ++ ys) k ≡ just j
            → (fetch xs k ≡ just j) ⊎ (Σ ℕ λ k′ → (k ≡ length xs + k′) × (fetch ys k′ ≡ just j))
fetch-split []       ys k       e = inj₂ (k , refl , e)
fetch-split (x ∷ xs) ys zero    e = inj₁ e
fetch-split (x ∷ xs) ys (suc k) e = up (fetch-split xs ys k e)
  where
    up : ∀ {j} → (fetch xs k ≡ just j) ⊎ (Σ ℕ λ k′ → (k ≡ length xs + k′) × (fetch ys k′ ≡ just j))
       → (fetch (x ∷ xs) (suc k) ≡ just j) ⊎ (Σ ℕ λ k′ → (suc k ≡ length (x ∷ xs) + k′) × (fetch ys k′ ≡ just j))
    up (inj₁ f)             = inj₁ f
    up (inj₂ (k′ , eq , f)) = inj₂ (k′ , cong suc eq , f)

------------------------------------------------------------------------
-- ★ What the expansion fetches: an instruction of some primitive one's expansion
------------------------------------------------------------------------

module _ (C : Classes) where

  record From (s : ℕ) (P : AbstractTrace) (k : ℕ) (j : AbstractInstr) : Set where
    constructor from
    field
      n   : ℕ
      i   : AbstractInstr
      r   : ℕ
      f-P : fetch P n ≡ just i
      f-k : k ≡ off C s P n + r
      f-e : fetch (expand-at C (n + s) i) r ≡ just j

  fetch-inv : ∀ s P k {j} → fetch (expand-from C s P) k ≡ just j → From s P k j
  fetch-inv s []      k ()
  fetch-inv s (x ∷ P) k {j} e = by (fetch-split (expand-at C s x) (expand-from C (suc s) P) k e)
    where
      by : (fetch (expand-at C s x) k ≡ just j)
           ⊎ (Σ ℕ λ k′ → (k ≡ length (expand-at C s x) + k′) × (fetch (expand-from C (suc s) P) k′ ≡ just j))
         → From s (x ∷ P) k j
      by (inj₁ f) = from 0 x k refl refl f
      by (inj₂ (k′ , eq , f)) = shift (fetch-inv (suc s) P k′ f)
        where
          shift : From (suc s) P k′ j → From s (x ∷ P) k j
          shift (from n i r fP fk fe) =
            from (suc n) i r fP
              (trans eq (trans (cong (length (expand-at C s x) +_) fk)
                               (sym (Data.Nat.Properties.+-assoc (length (expand-at C s x)) (off C (suc s) P n) r))))
              (subst (λ z → fetch (expand-at C z i) r ≡ just j) (Data.Nat.Properties.+-suc n s) fe)

------------------------------------------------------------------------
-- The expansion's own code: its instructions' kinds
------------------------------------------------------------------------

open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Maybe.Properties using (just-injective)
open import Once.CCC.Label using (LabelId)

all-fetch : ∀ {Q : AbstractInstr → Set} (xs : AbstractTrace) r {j} → All Q xs → fetch xs r ≡ just j → Q j
all-fetch []       r       []       ()
all-fetch (x ∷ xs) zero    (q ∷ _)  refl = q
all-fetch (x ∷ xs) (suc r) (_ ∷ qs) e    = all-fetch xs r qs e

data GenCtrl : FlatCtrl → Set where
  gc-br  : ∀ s → GenCtrl (c-branch-tag-zero (lb-bump s))
  gc-jmp : ∀ s → GenCtrl (c-jmp (lb-done s))
  gc-lbl : ∀ l → GenCtrl (c-label l)

data Gen : AbstractInstr → Set where
  g-out   : Gen mov-to-output
  g-in    : Gen mov-to-input
  g-srec  : ∀ w → RecW w → Gen (store-rec w)
  g-lrec  : ∀ w → RecW w → Gen (load-rec w)
  g-lat0  : Gen (load-at 0)
  g-sat0  : Gen (store-at 0)
  g-tag0  : Gen (instr-load-tag-lit 0)
  g-alloc : ∀ n → 1 ≤ n → Gen (instr-alloc-heap n)
  g-ctrl  : ∀ c → GenCtrl c → Gen (instr-ctrl c)

module Code (C : Classes) (small : 3 + count C ≤ rec-size) (in-range : ∀ k → cls C k < count C) (fits : ∀ k → k ≤ bsz C k) where
  open import Data.Nat.Properties using (<-≤-trans; ≤-trans; +-monoʳ-<; ≤-<-trans; m≤m+n)

  head< : ∀ c → c < count C → RecW (head-word c)
  head< c lt = <-≤-trans (+-monoʳ-< 3 lt) small

  w1 : RecW w-s1
  w1 = s≤s (s≤s z≤n)
  w2 : RecW w-s2
  w2 = s≤s (s≤s (s≤s z≤n))

  alloc-gen : ∀ site k → 1 ≤ k → All Gen (alloc-code C site k)
  alloc-gen site k one =
    g-out ∷ g-srec _ w1 ∷ g-lrec _ hl ∷ g-in ∷ g-ctrl _ (gc-br site) ∷ g-lat0 ∷ g-srec _ hl
    ∷ g-out ∷ g-srec _ w2 ∷ g-lrec _ w1 ∷ g-in ∷ g-lrec _ w2 ∷ g-ctrl _ (gc-jmp site) ∷ g-ctrl _ (gc-lbl _)
    ∷ g-lrec _ w1 ∷ g-in ∷ g-alloc _ (≤-trans one (fits k)) ∷ g-ctrl _ (gc-lbl _) ∷ []
    where hl = head< (cls C k) (in-range k)

  free-gen : ∀ k → All Gen (free-code C k)
  free-gen k = g-srec _ w1 ∷ g-lrec _ hl ∷ g-sat0 ∷ g-out ∷ g-srec _ hl ∷ g-lrec _ w1 ∷ []
    where hl = head< (cls C k) (in-range k)

  heads-gen : ∀ c → c ≤ count C → All Gen (heads C c)
  heads-gen zero    _  = []
  heads-gen (suc c) le = g-srec _ (head< c le) ∷ heads-gen c (≤-trans (m≤m+n c 1′) (sub le))
    where
      1′ = 1
      sub : suc c ≤ count C → c + 1 ≤ count C
      sub le′ = subst (_≤ count C) (sym (Data.Nat.Properties.+-comm c 1)) le′

  setup-gen : All Gen (setup C)
  setup-gen = g-srec _ w1 ∷ g-out ∷ g-srec _ w2 ∷ g-alloc 1 (s≤s z≤n)
            ∷ ++⁺ (heads-gen (count C) Data.Nat.Properties.≤-refl)
                  (g-in ∷ g-tag0 ∷ g-sat0 ∷ g-lrec _ w2 ∷ g-in ∷ g-lrec _ w1 ∷ [])

  -- ★ an instruction of one primitive instruction's expansion: that one itself
  -- (kept, or the start, at its offset 0), or of the expansion's own code
  Kept : ℕ → AbstractInstr → Set
  Kept s i = (expand-at C s i ≡ i ∷ []) ⊎ (Σ ℕ λ b → i ≡ instr-ctrl (c-start b))

  gen-of : ∀ s i r {j} → (∀ n → i ≡ instr-alloc-heap n → 1 ≤ n) → fetch (expand-at C s i) r ≡ just j
         → ((r ≡ 0) × (j ≡ i) × Kept s i) ⊎ Gen j
  gen-of s i r {j} am e = by (exp-view C s i) e
    where
      by : ExpView C s i → fetch (expand-at C s i) r ≡ just j → ((r ≡ 0) × (j ≡ i) × Kept s i) ⊎ Gen j
      by (ev-alloc k) f = inj₂ (all-fetch (alloc-code C s k) r (alloc-gen s k (am k refl)) f)
      by (ev-free k)  f = inj₂ (all-fetch (free-code C k) r (free-gen k) f)
      by (ev-start b) f = st r f
        where
          st : ∀ r′ → fetch (instr-ctrl (c-start b) ∷ setup C) r′ ≡ just j → ((r′ ≡ 0) × (j ≡ instr-ctrl (c-start b)) × Kept s (instr-ctrl (c-start b))) ⊎ Gen j
          st zero    f′ = inj₁ (refl , sym (just-injective f′) , inj₂ (b , refl))
          st (suc r′) f′ = inj₂ (all-fetch (setup C) r′ setup-gen f′)
      by (ev-same eq) f = sm r (subst (λ xs → fetch xs r ≡ just j) eq f)
        where
          sm : ∀ r′ → fetch (i ∷ []) r′ ≡ just j → ((r′ ≡ 0) × (j ≡ i) × Kept s i) ⊎ Gen j
          sm zero    f′ = inj₁ (refl , sym (just-injective f′) , inj₁ eq)
          sm (suc r′) ()

  ------------------------------------------------------------------------
  -- ★ A property of every expanded instruction: the kept ones' and the code's
  ------------------------------------------------------------------------

  open import Once.CCC.Machine.FrameFree using (ImageI)
  open import Once.CCC.Machine.AllocMin using (AllocMinI)
  import Data.List.Relation.Unary.All as All′

  gen-image : ∀ {j} → Gen j → ImageI j
  gen-image g-out = _
  gen-image g-in = _
  gen-image (g-srec w lt) = lt
  gen-image (g-lrec w lt) = lt
  gen-image g-lat0 = _
  gen-image g-sat0 = _
  gen-image g-tag0 = _
  gen-image (g-alloc n _) = _
  gen-image (g-ctrl _ (gc-br s)) = _
  gen-image (g-ctrl _ (gc-jmp s)) = _
  gen-image (g-ctrl _ (gc-lbl l)) = _

  gen-alloc : ∀ {j} → Gen j → AllocMinI j
  gen-alloc g-out = _
  gen-alloc g-in = _
  gen-alloc (g-srec w lt) = _
  gen-alloc (g-lrec w lt) = _
  gen-alloc g-lat0 = _
  gen-alloc g-sat0 = _
  gen-alloc g-tag0 = _
  gen-alloc (g-alloc n one) = one
  gen-alloc (g-ctrl _ (gc-br s)) = _
  gen-alloc (g-ctrl _ (gc-jmp s)) = _
  gen-alloc (g-ctrl _ (gc-lbl l)) = _

  exp-all : ∀ {Q : AbstractInstr → Set} → (∀ {j} → Gen j → Q j) → (∀ i → ImageI i → AllocMinI i → Q i)
          → ∀ s P → All ImageI P → All AllocMinI P → All Q (expand-from C s P)
  exp-all gq kq s []      []         []         = []
  exp-all {Q} gq kq s (x ∷ P) (ix ∷ is) (ax ∷ as) = ++⁺ (one (exp-view C s x) ix ax) (exp-all gq kq (suc s) P is as)
    where
      one : ExpView C s x → ImageI x → AllocMinI x → All Q (expand-at C s x)
      one (ev-alloc k) _ a = All′.map gq (alloc-gen s k a)
      one (ev-free k)  _ _ = All′.map gq (free-gen k)
      one (ev-start b) i a = kq _ i a ∷ All′.map gq setup-gen
      one (ev-same eq) i a = subst (All Q) (sym eq) (kq x i a ∷ [])

  ------------------------------------------------------------------------
  -- ★ The expansion of an emitted program is emitted
  ------------------------------------------------------------------------

  open import Once.Spec.Name using (CanonicalName)
  open import Once.CCC.FrameSemantics using (module FrameSemantics)
  open import Once.CCC.Codegen.AllocExpandPc {FS} using (fetch-exp; off-suc; ft-exp)
  open FlatMachine {FS} using (find-fn; find-thunk; find-entry)
  open import Once.CCC.Label using (EntryId; e-fn; e-thunk)

  module Em (o : CanonicalName) (slot-size : ℕ) (word-eq : FrameSemantics.frame-word FS ≡ slot-size) where
    open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq using (Emitted; module Emitted; GuardAt)

    off0 : ∀ P → off C 0 P 0 ≡ 0
    off0 []      = refl
    off0 (_ ∷ _) = refl

    module _ (P : AbstractTrace) (em : Emitted P) where
      open Emitted em
      E = expand C P

      -- a kept instruction is fetched at its mapped pc
      kept-at : ∀ n x → fetch P n ≡ just x → fetch (expand-at C (n + 0) x) 0 ≡ just x → fetch E (off C 0 P n) ≡ just x
      kept-at n x f k = subst (λ q → fetch E q ≡ just x) (Data.Nat.Properties.+-identityʳ _) (fetch-exp C 0 P n x f 0 x k)

      -- what the expansion fetches, classified
      Cls : ℕ → AbstractInstr → Set
      Cls k j = Σ ℕ λ n → (fetch P n ≡ just j) × (k ≡ off C 0 P n) × Kept (n + 0) j

      classify : ∀ k {j} → fetch E k ≡ just j → Cls k j ⊎ Gen j
      classify k {j} e = go (fetch-inv C 0 P k e)
        where
          go : From C 0 P k j → Cls k j ⊎ Gen j
          go (from n i r fP fk fe) = pick (gen-of (n + 0) i r (λ m eq → subst AllocMinI eq (all-fetch P n em-alloc fP)) fe)
            where
              pick : ((r ≡ 0) × (j ≡ i) × Kept (n + 0) i) ⊎ Gen j → Cls k j ⊎ Gen j
              pick (inj₁ (refl , refl , kp)) = inj₁ (n , fP , trans fk (Data.Nat.Properties.+-identityʳ _) , kp)
              pick (inj₂ g) = inj₂ g

      found : ∀ (e : EntryId) j → find-entry P e ≡ just j → find-entry E e ≡ just (0 + off C 0 P j)
      found e j f = trans (ft-exp C 0 P e 0) (cong (Data.Maybe.map (λ p → 0 + off C 0 P p)) f)

      emitted : Emitted E
      emitted = record
        { em-budget = em-budget
        ; em-zero = subst (λ q → fetch E q ≡ just (instr-ctrl (c-start em-budget))) (off0 P) (kept-at 0 _ em-zero refl)
        ; em-start = start
        ; em-image = exp-all gen-image (λ i ii _ → ii) 0 P em-image em-alloc
        ; em-alloc = exp-all gen-alloc (λ i _ ai → ai) 0 P em-image em-alloc
        ; em-calls = calls
        ; em-code = code
        ; em-guard = guard
        }
        where
          no-gen-start : ∀ {b} → Gen (instr-ctrl (c-start b)) → Data.Empty.⊥
          no-gen-start (g-ctrl _ ())
          start : ∀ k b → fetch E k ≡ just (instr-ctrl (c-start b)) → k ≡ 0
          start k b e = by (classify k e)
            where
              by : Cls k (instr-ctrl (c-start b)) ⊎ Gen (instr-ctrl (c-start b)) → k ≡ 0
              by (inj₁ (n , fP , refl , _)) = trans (cong (off C 0 P) (em-start n b fP)) (off0 P)
              by (inj₂ g) = Data.Empty.⊥-elim (no-gen-start g)
          calls : ∀ k f → fetch E k ≡ just (instr-ctrl (c-call-fn f)) → Σ ℕ (λ j → find-fn E f ≡ just j)
          calls k f e = by (classify k e)
            where
              by : Cls k (instr-ctrl (c-call-fn f)) ⊎ Gen (instr-ctrl (c-call-fn f)) → Σ ℕ (λ j → find-fn E f ≡ just j)
              by (inj₁ (n , fP , _ , _)) = let (j , fj) = em-calls n f fP in _ , found (e-fn f) j fj
              by (inj₂ (g-ctrl _ ()))
          code : ∀ p (ℓ : LabelId) → fetch E p ≡ just (instr-load-code-addr ℓ) → Σ ℕ (λ j → find-thunk E ℓ ≡ just j)
          code p ℓ e = by (classify p e)
            where
              by : Cls p (instr-load-code-addr ℓ) ⊎ Gen (instr-load-code-addr ℓ) → Σ ℕ (λ j → find-thunk E ℓ ≡ just j)
              by (inj₁ (n , fP , _ , _)) = let (j , fj) = em-code n ℓ fP in _ , found (e-thunk ℓ) j fj
              by (inj₂ ())
          guard : GuardAt E
          guard p ℓ bb e = by (classify p e)
            where
              Res = Σ ℕ (λ q → (p ≡ suc q)
                      × ((Σ LabelId (λ m → fetch E q ≡ just (instr-ctrl (c-jmp m))))
                         ⊎ (Σ ℕ (λ b → fetch E q ≡ just (instr-ctrl (c-ret b))))
                         ⊎ (fetch E q ≡ just (instr-ctrl c-leave))))
              step : ∀ q x → fetch P q ≡ just x → fetch (expand-at C (q + 0) x) 0 ≡ just x
                   → length (expand-at C (q + 0) x) ≡ 1 → p ≡ off C 0 P (suc q) → p ≡ suc (off C 0 P q)
              step q x f k l pe = trans pe (trans (off-suc C 0 P q x f) (trans (cong (off C 0 P q +_) l) (Data.Nat.Properties.+-comm _ 1)))
              by : Cls p (instr-ctrl (c-entry ℓ bb)) ⊎ Gen (instr-ctrl (c-entry ℓ bb)) → Res
              by (inj₂ (g-ctrl _ ()))
              by (inj₁ (n , fP , refl , _)) = from-img (em-guard n ℓ bb fP)
                where
                  from-img : Σ ℕ (λ q → (n ≡ suc q)
                               × ((Σ LabelId (λ m → fetch P q ≡ just (instr-ctrl (c-jmp m))))
                                  ⊎ (Σ ℕ (λ b → fetch P q ≡ just (instr-ctrl (c-ret b))))
                                  ⊎ (fetch P q ≡ just (instr-ctrl c-leave)))) → Res
                  from-img (q , refl , inj₁ (m , f)) = off C 0 P q , step q _ f refl refl refl , inj₁ (m , kept-at q _ f refl)
                  from-img (q , refl , inj₂ (inj₁ (b , f))) = off C 0 P q , step q _ f refl refl refl , inj₂ (inj₁ (b , kept-at q _ f refl))
                  from-img (q , refl , inj₂ (inj₂ f)) = off C 0 P q , step q _ f refl refl refl , inj₂ (inj₂ (kept-at q _ f refl))

  ------------------------------------------------------------------------
  -- ★ The expansion calls the ops the program calls (its own code calls none)
  ------------------------------------------------------------------------

  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Once.SigOp.Info using (SigOpInfo)

  private
    no-gen-sig : ∀ {A B} {si : SigOpInfo A B} → Gen (instr-sigop si) → Data.Empty.⊥
    no-gen-sig ()

  exp-sig : ∀ s P → All AllocMinI P → ∀ {A B} (si : SigOpInfo A B) → instr-sigop si ∈ expand-from C s P → instr-sigop si ∈ P
  exp-sig s []      []        si ()
  exp-sig s (x ∷ P) (ax ∷ as) si m = by (∈-++⁻ (expand-at C s x) m)
    where
      at : ExpView C s x → AllocMinI x → instr-sigop si ∈ expand-at C s x → instr-sigop si ∈ (x ∷ P)
      at (ev-alloc k) one m′ = Data.Empty.⊥-elim (no-gen-sig (All′.lookup (alloc-gen s k one) m′))
      at (ev-free k)  _ m′ = Data.Empty.⊥-elim (no-gen-sig (All′.lookup (free-gen k) m′))
      at (ev-start b) _ (here ())
      at (ev-start b) _ (there m′) = Data.Empty.⊥-elim (no-gen-sig (All′.lookup setup-gen m′))
      at (ev-same eq) _ m′ = in-one (subst (instr-sigop si ∈_) eq m′)
        where in-one : instr-sigop si ∈ (x ∷ []) → instr-sigop si ∈ (x ∷ P)
              in-one (here e) = here e
              in-one (there ())
      by : (instr-sigop si ∈ expand-at C s x) ⊎ (instr-sigop si ∈ expand-from C (suc s) P) → instr-sigop si ∈ (x ∷ P)
      by (inj₁ m′) = at (exp-view C s x) ax m′
      by (inj₂ m′) = there (exp-sig (suc s) P as si m′)

------------------------------------------------------------------------
-- The room checks add checks only
------------------------------------------------------------------------

open import Once.CCC.Codegen.RoomChecks using (room-checks; room-checks-def; checks; boundary?; stretch; pick)
open import Once.CCC.Codegen.StackDepth using (own; o-start)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Once.SigOp.Info using (SigOpInfo)

checks-sig : ∀ T o t {A B} (si : SigOpInfo A B) → instr-sigop si ∈ checks T o t → instr-sigop si ∈ t
checks-sig T o []      si ()
checks-sig T o (i ∷ t) si (here e) = here e
checks-sig T o (i ∷ t) si (there m) = there (by (boundary? i) m)
  where
    by : ∀ b → instr-sigop si ∈ (if b then instr-room (stretch T (own o i) t) ∷ checks T (own o i) t else checks T (own o i) t)
       → instr-sigop si ∈ t
    by true  (here ())
    by true  (there m′) = checks-sig T (own o i) t si m′
    by false m′ = checks-sig T (own o i) t si m′

room-sig : ∀ t {A B} (si : SigOpInfo A B) → instr-sigop si ∈ room-checks t → instr-sigop si ∈ t
room-sig t si m = checks-sig (pick t) o-start t si (subst (instr-sigop si ∈_) (room-checks-def t) m)

∈-checks : ∀ T o t {i} → i ∈ t → i ∈ checks T o t
∈-checks T o (x ∷ t) (here e) = here e
∈-checks T o (x ∷ t) {i} (there m) = there (by (boundary? x))
  where
    by : ∀ b → i ∈ (if b then instr-room (stretch T (own o x) t) ∷ checks T (own o x) t else checks T (own o x) t)
    by true  = there (∈-checks T (own o x) t m)
    by false = ∈-checks T (own o x) t m

∈-room : ∀ t {i} → i ∈ t → i ∈ room-checks t
∈-room t m = subst (_ ∈_) (sym (room-checks-def t)) (∈-checks (pick t) o-start t m)
