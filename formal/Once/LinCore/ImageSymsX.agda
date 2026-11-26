-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageSymsX — the allocator's expansion of an image keeps its
-- file's symbols well formed (D470/D472, plan 0.146 B1.6 item 3c4).
--
-- What the expansion holds is a kept instruction of the image's, or of an
-- alloc's, a free's or the start's code (`in-exp`). Its labels are the image's
-- and each alloc site's two (`alloc-label`), told apart by owner and index;
-- its entries are the image's.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Data.Nat using (ℕ)

module Once.LinCore.ImageSymsX
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Data.Nat using (zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All
import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (LabelId; EntryId; module LabelId)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.LinCore.LabelsC fmt ans bw using (module LabsC)

module X {FS : FrameSemantics} (C : Classes) where
  open FlatMachine {FS} using (fetch; label-of?; entry-of?)
  open LabsC {FS} using (Labs; lab; Labs-++; Ents; ent; Ents-++)
  open import Once.CCC.Codegen.AllocExpandPc {FS} using (off; exp-view; ExpView; ev-alloc; ev-free; ev-start; ev-same)

  ------------------------------------------------------------------------
  -- ★ What the expansion holds
  ------------------------------------------------------------------------

  data InExp (s : ℕ) (P : AbstractTrace) (i : AbstractInstr) : Set where
    in-kept  : i ∈ P → (∀ k → i ≡ instr-alloc-heap k → ⊥) → (∀ k → i ≡ instr-free-heap k → ⊥) → InExp s P i
    in-alloc : ∀ n k → fetch P n ≡ just (instr-alloc-heap k) → i ∈ alloc-code C (n + s) k → InExp s P i
    in-free  : ∀ k → i ∈ free-code C k → InExp s P i
    in-setup : i ∈ setup C → InExp s P i

  in-exp : ∀ s P {i} → i ∈ expand-from C s P → InExp s P i
  in-exp s []      ()
  in-exp s (x ∷ P) {i} m = by (∈-++⁻ (expand-at C s x) m)
    where
      at : ExpView C s x → i ∈ expand-at C s x → InExp s (x ∷ P) i
      at (ev-alloc k) m′ = in-alloc 0 k refl m′
      at (ev-free k)  m′ = in-free k m′
      at (ev-start b _) (here refl) = in-kept (here refl) (λ _ ()) (λ _ ())
      at (ev-start b _) (there m′)  = in-setup m′
      at (ev-same eq) m′ = one (subst (i ∈_) eq m′)
        where
          one : i ∈ (x ∷ []) → InExp s (x ∷ P) i
          one (here refl) = in-kept (here refl) (λ k e → not-alloc k e) (λ k e → not-free k e)
            where
              not-alloc : ∀ k → x ≡ instr-alloc-heap k → ⊥
              not-alloc k refl = len (cong Data.List.length eq)
                where len : 18 ≡ 1 → ⊥
                      len ()
              not-free : ∀ k → x ≡ instr-free-heap k → ⊥
              not-free k refl = len (cong Data.List.length eq)
                where len : 6 ≡ 1 → ⊥
                      len ()
          one (there ())
      up : InExp (suc s) P i → InExp s (x ∷ P) i
      up (in-kept m′ na nf) = in-kept (there m′) na nf
      up (in-alloc n k f m′) = in-alloc (suc n) k f (subst (λ z → i ∈ alloc-code C z k) (Data.Nat.Properties.+-suc n s) m′)
      up (in-free k m′) = in-free k m′
      up (in-setup m′) = in-setup m′
      by : (i ∈ expand-at C s x) ⊎ (i ∈ expand-from C (suc s) P) → InExp s (x ∷ P) i
      by (inj₁ m′) = at (exp-view C s x) m′
      by (inj₂ m′) = up (in-exp (suc s) P m′)

  -- …and an alloc's code is in it, whole
  alloc-in : ∀ s P n k → fetch P n ≡ just (instr-alloc-heap k) → ∀ {i} → i ∈ alloc-code C (n + s) k → i ∈ expand-from C s P
  alloc-in s []      n       k () m
  alloc-in s (x ∷ P) zero    k refl m = ∈-++⁺ˡ m
  alloc-in s (x ∷ P) (suc n) k f {i} m =
    ∈-++⁺ʳ (expand-at C s x) (alloc-in (suc s) P n k f (subst (λ z → i ∈ alloc-code C z k) (sym (Data.Nat.Properties.+-suc n s)) m))

  -- …and so is every kept instruction
  kept-in : ∀ s P {i} → i ∈ P → (∀ k → i ≡ instr-alloc-heap k → ⊥) → (∀ k → i ≡ instr-free-heap k → ⊥) → i ∈ expand-from C s P
  kept-in s (x ∷ P) (here refl) na nf = ∈-++⁺ˡ (head-in (exp-view C s x))
    where
      head-in : ExpView C s x → x ∈ expand-at C s x
      head-in (ev-alloc k) = ⊥-elim (na k refl)
      head-in (ev-free k)  = ⊥-elim (nf k refl)
      head-in (ev-start b _) = here refl
      head-in (ev-same eq) = subst (x ∈_) (sym eq) (here refl)
  kept-in s (x ∷ P) (there m) na nf = ∈-++⁺ʳ (expand-at C s x) (kept-in (suc s) P m na nf)

  ------------------------------------------------------------------------
  -- ★ Its labels: the image's, and a later site's two
  ------------------------------------------------------------------------

  open FlatMachine {FS} using (label-of?-sound)
  open import Once.CCC.Codegen.AllocExpandPc {FS} using (site-of)

  lab-mem : ∀ t {m} → m ∈ Labs t → instr-ctrl (c-label m) ∈ t
  lab-mem (x ∷ t) {m} p = go (label-of? x) refl p
    where
      go : ∀ mo → label-of? x ≡ mo → m ∈ LabsC.lab {FS} mo (Labs t) → instr-ctrl (c-label m) ∈ (x ∷ t)
      go (just l) e (here refl) = here (sym (label-of?-sound x m e))
      go (just l) e (there q)   = there (lab-mem t q)
      go nothing  e q           = there (lab-mem t q)

  mem-lab : ∀ t {m} → instr-ctrl (c-label m) ∈ t → m ∈ Labs t
  mem-lab (x ∷ t) (here refl) = here refl
  mem-lab (x ∷ t) {m} (there p) = go (label-of? x) (mem-lab t p)
    where go : ∀ mo → m ∈ Labs t → m ∈ LabsC.lab {FS} mo (Labs t)
          go (just _) q = there q
          go nothing  q = q

  private
    -- a code's labels, by a property of each of its instructions
    LabQ : (LabelId → Set) → AbstractInstr → Set
    LabQ Q i = ∀ m → i ≡ instr-ctrl (c-label m) → Q m

    no : ∀ {Q} {i} → (∀ m → i ≡ instr-ctrl (c-label m) → ⊥) → LabQ Q i
    no f m e = ⊥-elim (f m e)

    heads-q : ∀ {Q} c → All (LabQ Q) (heads C c)
    heads-q zero    = []
    heads-q (suc c) = no (λ _ ()) ∷ heads-q c

    setup-q : ∀ {Q} → All (LabQ Q) (setup C)
    setup-q = no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ())
            ∷ Data.List.Relation.Unary.All.Properties.++⁺ (heads-q (count C))
                (no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ [])

    free-q : ∀ {Q} k → All (LabQ Q) (free-code C k)
    free-q k = no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ []

    alloc-q : ∀ site k → All (LabQ (λ m → SiteL m site)) (alloc-code C site k)
    alloc-q site k =
      no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ (λ { .(lb-bump site) refl → 0 , z≤n , refl })
      ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ no (λ _ ()) ∷ (λ { .(lb-done site) refl → 1 , s≤s z≤n , refl }) ∷ []

    no-lab-setup : ∀ {m} → instr-ctrl (c-label m) ∈ setup C → ⊥
    no-lab-setup {m} p = Data.List.Relation.Unary.All.lookup (setup-q {λ _ → ⊥}) p m refl

    no-lab-free : ∀ k {m} → instr-ctrl (c-label m) ∈ free-code C k → ⊥
    no-lab-free k {m} p = Data.List.Relation.Unary.All.lookup (free-q {λ _ → ⊥} k) p m refl

    -- an alloc's code defines its site's two labels
    alloc-labs : ∀ site k {m} → instr-ctrl (c-label m) ∈ alloc-code C site k → SiteL m site
    alloc-labs site k {m} p = Data.List.Relation.Unary.All.lookup (alloc-q site k) p m refl

  labs-in : ∀ s P {m} → m ∈ Labs (expand-from C s P) → (m ∈ Labs P) ⊎ (Σ ℕ λ s′ → (s ≤ s′) × SiteL m s′)
  labs-in s P {m} p = by (in-exp s P (lab-mem (expand-from C s P) p))
    where
      by : InExp s P (instr-ctrl (c-label m)) → (m ∈ Labs P) ⊎ (Σ ℕ λ s′ → (s ≤ s′) × SiteL m s′)
      by (in-kept q _ _) = inj₁ (mem-lab P q)
      by (in-alloc n k f q) = inj₂ (n + s , Data.Nat.Properties.m≤n+m s n , alloc-labs (n + s) k q)
      by (in-free k q) = ⊥-elim (no-lab-free k q)
      by (in-setup q) = ⊥-elim (no-lab-setup q)

  ------------------------------------------------------------------------
  -- ★ …each once, and its entries the image's
  ------------------------------------------------------------------------

  private
    labs-empty : ∀ t → (∀ {m} → instr-ctrl (c-label m) ∈ t → ⊥) → Labs t ≡ []
    labs-empty t f = go (Labs t) refl
      where go : ∀ l → Labs t ≡ l → l ≡ []
            go []      _ = refl
            go (m ∷ _) e = ⊥-elim (f (lab-mem t (subst (m ∈_) (sym e) (here refl))))

    owner≢ : ∀ {m} s b → ImgL m → m ≢ alloc-label s b
    owner≢ s b img e = img (cong LabelId.owner e)

    bump≢done : ∀ s → lb-bump s ≢ lb-done s
    bump≢done s e = Data.Nat.Properties.<-irrefl (cong LabelId.idx e) (Data.Nat.Properties.n<1+n (s + s))

  labs-dst : ∀ s P → AllPairs _≢_ (Labs P) → (∀ {m} → m ∈ Labs P → ImgL m) → AllPairs _≢_ (Labs (expand-from C s P))
  labs-dst s []      _  _   = []
  labs-dst s (x ∷ P) ap img =
    subst (AllPairs _≢_) (sym (Labs-++ (expand-at C s x) rest)) (by (exp-view C s x) (label-of? x) refl ap img)
    where
      rest = expand-from C (suc s) P
      -- a site's label is none of a later one's, nor an image label
      later-fork : ∀ b → b ≤ 1 → (∀ {m} → m ∈ Labs P → ImgL m) → ∀ m′
                 → (m′ ∈ Labs P) ⊎ (Σ ℕ λ s′ → (suc s ≤ s′) × SiteL m′ s′) → alloc-label s b ≡ m′ → ⊥
      later-fork b bb imgP m′ (inj₁ q) e = imgP q (cong LabelId.owner (sym e))
      later-fork b bb imgP .(alloc-label s′ b′) (inj₂ (s′ , le , (b′ , bb′ , refl))) e =
        Data.Nat.Properties.<-irrefl (site-of C s s′ b b′ bb bb′ (cong LabelId.idx e)) le
      later : ∀ b → b ≤ 1 → (∀ {m} → m ∈ Labs P → ImgL m) → All (alloc-label s b ≢_) (Labs rest)
      later b bb imgP = Data.List.Relation.Unary.All.tabulate λ {m′} p e → later-fork b bb imgP m′ (labs-in (suc s) P p) e
      by : ExpView C s x → ∀ mo → label-of? x ≡ mo → AllPairs _≢_ (LabsC.lab {FS} mo (Labs P))
         → (∀ {m} → m ∈ LabsC.lab {FS} mo (Labs P) → ImgL m)
         → AllPairs _≢_ (Labs (expand-at C s x) ++ Labs rest)
      by v (just l) e (hd ∷ apP) imgM = by′ v
        where
          imgP : ∀ {m} → m ∈ Labs P → ImgL m
          imgP q = imgM (there q)
          IH = labs-dst (suc s) P apP imgP
          by′ : ExpView C s x → AllPairs _≢_ (Labs (expand-at C s x) ++ Labs rest)
          by′ (ev-alloc k) = ⊥-elim (lbl≢ (label-of?-sound x l e)) where lbl≢ : x ≡ instr-ctrl (c-label l) → ⊥ ; lbl≢ ()
          by′ (ev-free k)  = ⊥-elim (lbl≢ (label-of?-sound x l e)) where lbl≢ : x ≡ instr-ctrl (c-label l) → ⊥ ; lbl≢ ()
          by′ (ev-start b _) = ⊥-elim (lbl≢ (label-of?-sound x l e)) where lbl≢ : x ≡ instr-ctrl (c-label l) → ⊥ ; lbl≢ ()
          by′ (ev-same eq) = subst (λ z → AllPairs _≢_ (Labs z ++ Labs rest)) (sym eq) (subst (λ mo → AllPairs _≢_ (LabsC.lab {FS} mo [] ++ Labs rest)) (sym e) (cross ∷ IH))
            where
              kept-fork : ∀ m′ → (m′ ∈ Labs P) ⊎ (Σ ℕ λ s′ → (suc s ≤ s′) × SiteL m′ s′) → l ≡ m′ → ⊥
              kept-fork m′ (inj₁ q) e″ = Data.List.Relation.Unary.All.lookup hd q e″
              kept-fork .(alloc-label s′ b′) (inj₂ (s′ , _ , (b′ , _ , refl))) e″ = owner≢ s′ b′ (imgM (here refl)) e″
              cross : All (l ≢_) (Labs rest)
              cross = Data.List.Relation.Unary.All.tabulate λ {m′} p e′ → kept-fork m′ (labs-in (suc s) P p) e′
      by v nothing e apP imgM = by′ v
        where
          IH = labs-dst (suc s) P apP imgM
          by′ : ExpView C s x → AllPairs _≢_ (Labs (expand-at C s x) ++ Labs rest)
          by′ (ev-alloc k) = (bump≢done s ∷ later 0 z≤n imgM) ∷ (later 1 (s≤s z≤n) imgM ∷ IH)
          by′ (ev-free k)  = IH
          by′ (ev-start b _) = subst (λ z → AllPairs _≢_ (z ++ Labs rest)) (sym (labs-empty (setup C) no-lab-setup)) IH
          by′ (ev-same eq) = subst (λ z → AllPairs _≢_ (Labs z ++ Labs rest)) (sym eq) (subst (λ mo → AllPairs _≢_ (LabsC.lab {FS} mo [] ++ Labs rest)) (sym e) IH)

  -- an instruction list with no entry has none
  private
    ents-none : ∀ (t : AbstractTrace) → All (λ i → entry-of? i ≡ nothing) t → Ents t ≡ []
    ents-none []      []       = refl
    ents-none (x ∷ t) (e ∷ es) = trans (cong (λ mo → LabsC.ent {FS} mo (Ents t)) e) (ents-none t es)

    heads-ne : ∀ c → All (λ i → entry-of? i ≡ nothing) (heads C c)
    heads-ne zero    = []
    heads-ne (suc c) = refl ∷ heads-ne c

    setup-ne : All (λ i → entry-of? i ≡ nothing) (setup C)
    setup-ne = refl ∷ refl ∷ refl ∷ refl
             ∷ Data.List.Relation.Unary.All.Properties.++⁺ (heads-ne (count C)) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ [])

  -- ★ its entries are the image's
  ents-exp : ∀ s P → Ents (expand-from C s P) ≡ Ents P
  ents-exp s []      = refl
  ents-exp s (x ∷ P) = trans (Ents-++ (expand-at C s x) (expand-from C (suc s) P)) (by (exp-view C s x))
    where
      IH = ents-exp (suc s) P
      by : ExpView C s x → Ents (expand-at C s x) ++ Ents (expand-from C (suc s) P) ≡ Ents (x ∷ P)
      by (ev-alloc k) = trans (cong (_++ Ents (expand-from C (suc s) P))
                                (ents-none (alloc-code C s k) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))) IH
      by (ev-free k)  = trans (cong (_++ Ents (expand-from C (suc s) P)) (ents-none (free-code C k) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []))) IH
      by (ev-start b rsv) = trans (cong (_++ Ents (expand-from C (suc s) P)) (ents-none (instr-ctrl (c-start b rsv) ∷ setup C) (refl ∷ setup-ne))) IH
      by (ev-same eq) = trans (cong (λ z → Ents z ++ Ents (expand-from C (suc s) P)) eq) (go (entry-of? x))
        where go : ∀ mo → LabsC.ent {FS} mo [] ++ Ents (expand-from C (suc s) P) ≡ LabsC.ent {FS} mo (Ents P)
              go (just e) = cong (e ∷_) IH
              go nothing  = IH
