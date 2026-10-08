-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ImageUnique — plan 0.107 §8 step 4: EVERY SYMBOL A FILE
-- DEFINES IS DEFINED ONCE (`AsmWF.defined-once`).
--
-- Were `ImageWF.prog-unique` / `lib-unique`, postulates. The argument:
--   * the image's definitions are the `labelSym` of its defined LABELS;
--   * a label's `key` — a counter label's index, a function entry's symbol —
--     is recovered from its symbol (`LabelSymbols.sym-key`), so distinct keys
--     mean distinct symbols;
--   * the counter labels are pairwise distinct: each unit's by
--     `CLabelsUnique.frag`, across units by their disjoint counter windows;
--   * the function entries are the table's, whose symbols the extractor's guard
--     keeps distinct (`NameClash.program-no-clash`), and no unit defines one
--     (`CLabelsUnique.frag-nf`);
--   * the heap, `_start` and the arith blocks are separated from all of these
--     by their characters.
------------------------------------------------------------------------

module Once.Adequacy.ImageUnique where

open import Data.List using (List; []; _∷_; _++_; map)
import Data.List
import Data.List.Relation.Unary.All
import Data.String
import Data.Nat
import Data.Digit
import Data.List.Properties
import Once.Arith.Machine.IR
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming ()
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Nat using (ℕ)
import Data.Maybe
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.CanonicalName using (CanonicalName; canonical)
open import Once.CCC.Label using (Label; once; callee; e-thunk; e-fn; labelSym)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Codegen.ImageSymbols using (instr-defs; adefs)
open import Once.CCC.Codegen.LabelDefs using (Dst; clab-of; cl-at; clabs; fdef-of; fdefs)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Adequacy.LabelSymbols using (key; DefL; d-once; d-callee; keys→syms)

------------------------------------------------------------------------
-- The defined labels
------------------------------------------------------------------------

ilab : AbstractInstr → List Label
ilab (instr-ctrl (c-label m))   = once m ∷ []
ilab (instr-ctrl (c-entry e _)) = callee e ∷ []
{-# CATCHALL #-}
ilab _                          = []

dlabs : AbstractTrace → List Label
dlabs []       = []
dlabs (i ∷ is) = ilab i ++ dlabs is

lefts : List (ℕ ⊎ String) → List ℕ
lefts []            = []
lefts (inj₁ k ∷ xs) = k ∷ lefts xs
lefts (inj₂ _ ∷ xs) = lefts xs

rights : List (ℕ ⊎ String) → List String
rights []            = []
rights (inj₁ _ ∷ xs) = rights xs
rights (inj₂ s ∷ xs) = s ∷ rights xs

private
  lefts-++ : ∀ (xs ys : List (ℕ ⊎ String)) → lefts (xs ++ ys) ≡ lefts xs ++ lefts ys
  lefts-++ []            ys = refl
  lefts-++ (inj₁ k ∷ xs) ys = cong (k ∷_) (lefts-++ xs ys)
  lefts-++ (inj₂ _ ∷ xs) ys = lefts-++ xs ys

  rights-++ : ∀ (xs ys : List (ℕ ⊎ String)) → rights (xs ++ ys) ≡ rights xs ++ rights ys
  rights-++ []            ys = refl
  rights-++ (inj₁ _ ∷ xs) ys = rights-++ xs ys
  rights-++ (inj₂ s ∷ xs) ys = cong (s ∷_) (rights-++ xs ys)

-- per instruction: its definitions are its labels' symbols…
idefs : ∀ (i : AbstractInstr) → instr-defs i ≡ map labelSym (ilab i)
idefs (instr-ctrl (c-label m)) = refl
idefs (instr-ctrl (c-entry (e-thunk m) _)) = refl
idefs (instr-ctrl (c-entry (e-fn f) _)) = refl
idefs (instr-ctrl (c-jmp _)) = refl
idefs (instr-ctrl (c-branch-scratch-zero _)) = refl
idefs (instr-ctrl (c-branch-tag-zero _)) = refl
idefs (instr-ctrl (c-ret _)) = refl
idefs (instr-ctrl (c-call-fn _)) = refl
idefs (instr-ctrl (c-start _)) = refl
idefs mov-to-output = refl
idefs mov-to-input = refl
idefs load-indirect = refl
idefs load-indirect-suc = refl
idefs (load-from-slot _) = refl
idefs (store-at-slot _) = refl
idefs store-indirect = refl
idefs store-indirect-suc = refl
idefs (lea-slot _) = refl
idefs (restore-input _) = refl
idefs (instr-alloc-stack _) = refl
idefs (instr-dealloc-stack _) = refl
idefs (instr-reclaim-to _) = refl
idefs (instr-push-frame _) = refl
idefs instr-pop-frame = refl
idefs instr-call-closure = refl
idefs (worklist-init _) = refl
idefs (worklist-push _) = refl
idefs (worklist-pop _) = refl
idefs (worklist-check _) = refl
idefs (instr-sigop _) = refl
idefs (instr-load-const _ _) = refl
idefs (instr-load-code-addr _) = refl
idefs instr-save-closure-reg = refl
idefs (instr-load-tag-lit _) = refl
idefs (instr-case-on-tag _ _) = refl
idefs (instr-alloc-heap _) = refl
idefs (instr-loop _) = refl
idefs (instr-reg-op _) = refl
idefs (lea-indexed _) = refl

-- …its labels are definitions…
idefl : ∀ (i : AbstractInstr) → All DefL (ilab i)
idefl (instr-ctrl (c-label m)) = d-once ∷ []
idefl (instr-ctrl (c-entry (e-thunk m) _)) = d-callee ∷ []
idefl (instr-ctrl (c-entry (e-fn f) _)) = d-callee ∷ []
idefl (instr-ctrl (c-jmp _)) = []
idefl (instr-ctrl (c-branch-scratch-zero _)) = []
idefl (instr-ctrl (c-branch-tag-zero _)) = []
idefl (instr-ctrl (c-ret _)) = []
idefl (instr-ctrl (c-call-fn _)) = []
idefl (instr-ctrl (c-start _)) = []
idefl mov-to-output = []
idefl mov-to-input = []
idefl load-indirect = []
idefl load-indirect-suc = []
idefl (load-from-slot _) = []
idefl (store-at-slot _) = []
idefl store-indirect = []
idefl store-indirect-suc = []
idefl (lea-slot _) = []
idefl (restore-input _) = []
idefl (instr-alloc-stack _) = []
idefl (instr-dealloc-stack _) = []
idefl (instr-reclaim-to _) = []
idefl (instr-push-frame _) = []
idefl instr-pop-frame = []
idefl instr-call-closure = []
idefl (worklist-init _) = []
idefl (worklist-push _) = []
idefl (worklist-pop _) = []
idefl (worklist-check _) = []
idefl (instr-sigop _) = []
idefl (instr-load-const _ _) = []
idefl (instr-load-code-addr _) = []
idefl instr-save-closure-reg = []
idefl (instr-load-tag-lit _) = []
idefl (instr-case-on-tag _ _) = []
idefl (instr-alloc-heap _) = []
idefl (instr-loop _) = []
idefl (instr-reg-op _) = []
idefl (lea-indexed _) = []

-- …its counter labels are `clab-of`'s, its function entries `fdef-of`'s.
ileft : ∀ (i : AbstractInstr) → lefts (map key (ilab i)) ≡ cl-at (clab-of i) []
ileft (instr-ctrl (c-label m)) = refl
ileft (instr-ctrl (c-entry (e-thunk m) _)) = refl
ileft (instr-ctrl (c-entry (e-fn f) _)) = refl
ileft (instr-ctrl (c-jmp _)) = refl
ileft (instr-ctrl (c-branch-scratch-zero _)) = refl
ileft (instr-ctrl (c-branch-tag-zero _)) = refl
ileft (instr-ctrl (c-ret _)) = refl
ileft (instr-ctrl (c-call-fn _)) = refl
ileft (instr-ctrl (c-start _)) = refl
ileft mov-to-output = refl
ileft mov-to-input = refl
ileft load-indirect = refl
ileft load-indirect-suc = refl
ileft (load-from-slot _) = refl
ileft (store-at-slot _) = refl
ileft store-indirect = refl
ileft store-indirect-suc = refl
ileft (lea-slot _) = refl
ileft (restore-input _) = refl
ileft (instr-alloc-stack _) = refl
ileft (instr-dealloc-stack _) = refl
ileft (instr-reclaim-to _) = refl
ileft (instr-push-frame _) = refl
ileft instr-pop-frame = refl
ileft instr-call-closure = refl
ileft (worklist-init _) = refl
ileft (worklist-push _) = refl
ileft (worklist-pop _) = refl
ileft (worklist-check _) = refl
ileft (instr-sigop _) = refl
ileft (instr-load-const _ _) = refl
ileft (instr-load-code-addr _) = refl
ileft instr-save-closure-reg = refl
ileft (instr-load-tag-lit _) = refl
ileft (instr-case-on-tag _ _) = refl
ileft (instr-alloc-heap _) = refl
ileft (instr-loop _) = refl
ileft (instr-reg-op _) = refl
ileft (lea-indexed _) = refl

iright : ∀ (i : AbstractInstr) → rights (map key (ilab i)) ≡ map once-symbol-path (fdef-of i)
iright (instr-ctrl (c-label m)) = refl
iright (instr-ctrl (c-entry (e-thunk m) _)) = refl
iright (instr-ctrl (c-entry (e-fn f) _)) = refl
iright (instr-ctrl (c-jmp _)) = refl
iright (instr-ctrl (c-branch-scratch-zero _)) = refl
iright (instr-ctrl (c-branch-tag-zero _)) = refl
iright (instr-ctrl (c-ret _)) = refl
iright (instr-ctrl (c-call-fn _)) = refl
iright (instr-ctrl (c-start _)) = refl
iright mov-to-output = refl
iright mov-to-input = refl
iright load-indirect = refl
iright load-indirect-suc = refl
iright (load-from-slot _) = refl
iright (store-at-slot _) = refl
iright store-indirect = refl
iright store-indirect-suc = refl
iright (lea-slot _) = refl
iright (restore-input _) = refl
iright (instr-alloc-stack _) = refl
iright (instr-dealloc-stack _) = refl
iright (instr-reclaim-to _) = refl
iright (instr-push-frame _) = refl
iright instr-pop-frame = refl
iright instr-call-closure = refl
iright (worklist-init _) = refl
iright (worklist-push _) = refl
iright (worklist-pop _) = refl
iright (worklist-check _) = refl
iright (instr-sigop _) = refl
iright (instr-load-const _ _) = refl
iright (instr-load-code-addr _) = refl
iright instr-save-closure-reg = refl
iright (instr-load-tag-lit _) = refl
iright (instr-case-on-tag _ _) = refl
iright (instr-alloc-heap _) = refl
iright (instr-loop _) = refl
iright (instr-reg-op _) = refl
iright (lea-indexed _) = refl

adefs-labs : ∀ (t : AbstractTrace) → adefs t ≡ map labelSym (dlabs t)
adefs-labs []       = refl
adefs-labs (i ∷ is) = trans (cong₂ _++_ (idefs i) (adefs-labs is)) (sym (map-++ labelSym (ilab i) (dlabs is)))

dlabs-def : ∀ (t : AbstractTrace) → All DefL (dlabs t)
dlabs-def []       = []
dlabs-def (i ∷ is) = All-++⁺ (idefl i) (dlabs-def is)

private
  cl-at-++ : ∀ (m : _) (xs : List ℕ) → cl-at m xs ≡ cl-at m [] ++ xs
  cl-at-++ (Data.Maybe.just k) xs = refl
  cl-at-++ Data.Maybe.nothing  xs = refl

keys-lefts : ∀ (t : AbstractTrace) → lefts (map key (dlabs t)) ≡ clabs t
keys-lefts []       = refl
keys-lefts (i ∷ is) =
  trans (cong lefts (map-++ key (ilab i) (dlabs is)))
    (trans (lefts-++ (map key (ilab i)) _)
      (trans (cong₂ _++_ (ileft i) (keys-lefts is)) (sym (cl-at-++ (clab-of i) (clabs is)))))

keys-rights : ∀ (t : AbstractTrace) → rights (map key (dlabs t)) ≡ map once-symbol-path (fdefs t)
keys-rights []       = refl
keys-rights (i ∷ is) =
  trans (cong rights (map-++ key (ilab i) (dlabs is)))
    (trans (rights-++ (map key (ilab i)) _)
      (trans (cong₂ _++_ (iright i) (keys-rights is)) (sym (map-++ once-symbol-path (fdef-of i) (fdefs is)))))

------------------------------------------------------------------------
-- Distinct keys, from distinct counters and distinct entries
------------------------------------------------------------------------

lr-dst : ∀ (xs : List (ℕ ⊎ String)) → Dst (lefts xs) → AllPairs _≢_ (rights xs) → AllPairs _≢_ xs
lr-dst []            _          _          = []
lr-dst (inj₁ k ∷ xs) (pk ∷ pks) pr         = fresh₁ xs pk ∷ lr-dst xs pks pr
  where
    fresh₁ : ∀ ys → All (k ≢_) (lefts ys) → All (inj₁ k ≢_) ys
    fresh₁ []            _        = []
    fresh₁ (inj₁ j ∷ ys) (p ∷ ps) = (λ eq → p (inj₁-inj eq)) ∷ fresh₁ ys ps
      where inj₁-inj : ∀ {a b : ℕ} → inj₁ {B = String} a ≡ inj₁ b → a ≡ b
            inj₁-inj refl = refl
    fresh₁ (inj₂ _ ∷ ys) ps       = (λ ()) ∷ fresh₁ ys ps
lr-dst (inj₂ s ∷ xs) pl         (ps ∷ pss) = fresh₂ xs ps ∷ lr-dst xs pl pss
  where
    fresh₂ : ∀ ys → All (s ≢_) (rights ys) → All (inj₂ s ≢_) ys
    fresh₂ []            _        = []
    fresh₂ (inj₁ _ ∷ ys) ps′      = (λ ()) ∷ fresh₂ ys ps′
    fresh₂ (inj₂ t ∷ ys) (p ∷ ps′) = (λ eq → p (inj₂-inj eq)) ∷ fresh₂ ys ps′
      where inj₂-inj : ∀ {a b : String} → inj₂ {A = ℕ} a ≡ inj₂ b → a ≡ b
            inj₂-inj refl = refl

open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to AP-map⁺)

-- THE BRIDGE: a trace whose counter labels and function entries are distinct
-- defines every symbol once.
adefs-unique : ∀ (t : AbstractTrace) → Dst (clabs t) → AllPairs _≢_ (map once-symbol-path (fdefs t))
             → AllPairs _≢_ (adefs t)
adefs-unique t dc df =
  subst (AllPairs _≢_) (sym (adefs-labs t))
    (AP-map⁺ (keys→syms (dlabs-def t)
      (AP-map⁻ (lr-dst (map key (dlabs t)) (subst Dst (sym (keys-lefts t)) dc)
                       (subst (AllPairs _≢_) (sym (keys-rights t)) df)))))
  where
    AP-map⁻ : ∀ {xs : List Label} → AllPairs _≢_ (map key xs) → AllPairs (λ x y → key x ≢ key y) xs
    AP-map⁻ {[]}     []         = []
    AP-map⁻ {x ∷ xs} (px ∷ pxs) = all-map⁻ px ∷ AP-map⁻ pxs
      where all-map⁻ : ∀ {ys : List Label} → All (key x ≢_) (map key ys) → All (λ y → key x ≢ key y) ys
            all-map⁻ {[]}     []       = []
            all-map⁻ {y ∷ ys} (p ∷ ps) = p ∷ all-map⁻ ps

------------------------------------------------------------------------
-- THE IMAGE: its units sit in disjoint windows of the one counter.
------------------------------------------------------------------------

open import Data.Nat using (suc; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n<1+n; n≤1+n)
open import Once.Denotation.Program using (IRFun; IRProgram)
open Once.Denotation.Program.IRProgram using (main; table)
open Once.Denotation.Program.IRFun using (fbody; fname)
open import Once.CCC.Codegen.ProgramImage using (fns-image; fn-image; fn-next; top-done; program-image)
open import Once.CCC.Codegen.LabelDefs using (Win; dst-++; dj-win; win-weaken; fresh-above; clabs-++; nf)
import Once.CCC.Codegen.CLabelsUnique as CLU
import Once.CCC.Codegen.IRToTrace as IT
import Once.CCC.Codegen.LabelRange as LR
import Once.CCC.Codegen.LabelScope as LSc

fns-end : ℕ → List IRFun → ℕ
fns-end l []       = l
fns-end l (e ∷ es) = fns-end (fn-next l e) es

private
  unit-cl : ∀ (e : IRFun) (l : ℕ)
          → clabs (fn-image l e) ≡ CLU.TL (fname e) (fbody e) 0 l ++ CLU.BL (fname e) (fbody e) 0 l
  unit-cl e l = clabs-++ (LSc.trace-of (fname e) (IT.ir-to-trace' (fname e) 0 l (fbody e))) _

  unit-nf : ∀ (e : IRFun) (l : ℕ) → fdefs (fn-image l e) ≡ fname e ∷ []
  unit-nf e l = cong (fname e ∷_) (nf (LSc.trace-of (fname e) (IT.ir-to-trace' (fname e) 0 l (fbody e))) _
                                     (proj₁ (CLU.frag-nf (fname e) (fbody e) 0 l)) (proj₂ (CLU.frag-nf (fname e) (fbody e) 0 l)))

fns-end-≥ : ∀ (l : ℕ) (es : List IRFun) → l ≤ fns-end l es
fns-end-≥ l []       = ≤-refl
fns-end-≥ l (e ∷ es) = ≤-trans (LR.label-mono (fname e) (fbody e) 0 l) (fns-end-≥ (fn-next l e) es)

fns-cl : ∀ (l : ℕ) (es : List IRFun) → Dst (clabs (fns-image l es)) × Win l (fns-end l es) (clabs (fns-image l es))
fns-cl l []       = [] , []
fns-cl l (e ∷ es) =
  subst (λ z → Dst z × Win l (fns-end l (e ∷ es)) z) (sym eq)
    ( dst-++ dU (proj₁ rest) (dj-win wU (proj₂ rest) ≤-refl)
    , All-++⁺ (win-weaken ≤-refl (fns-end-≥ (fn-next l e) es) wU)
              (win-weaken (LR.label-mono (fname e) (fbody e) 0 l) ≤-refl (proj₂ rest)) )
  where
    o = fname e
    F = CLU.frag o (fbody e) 0 l
    dU = CLU.frag-dst o (fbody e) 0 l
    wU : Win l (fn-next l e) (CLU.TL o (fbody e) 0 l ++ CLU.BL o (fbody e) 0 l)
    wU = All-++⁺ (proj₁ (proj₂ F)) (proj₂ (proj₂ F))
    rest = fns-cl (fn-next l e) es
    eq : clabs (fns-image l (e ∷ es)) ≡ (CLU.TL o (fbody e) 0 l ++ CLU.BL o (fbody e) 0 l) ++ clabs (fns-image (fn-next l e) es)
    eq = trans (clabs-++ (fn-image l e) _) (cong (_++ clabs (fns-image (fn-next l e) es)) (unit-cl e l))

fns-fdefs : ∀ (l : ℕ) (es : List IRFun) → fdefs (fns-image l es) ≡ Data.List.map fname es
fns-fdefs l []       = refl
fns-fdefs l (e ∷ es) =
  trans (fdefs-++ (fn-image l e) _) (trans (cong (_++ fdefs (fns-image (fn-next l e) es)) (unit-nf e l))
                                           (cong (fname e ∷_) (fns-fdefs (fn-next l e) es)))
  where
    fdefs-++ : ∀ (x y : AbstractTrace) → fdefs (x ++ y) ≡ fdefs x ++ fdefs y
    fdefs-++ []       y = refl
    fdefs-++ (i ∷ is) y = trans (cong (fdef-of i ++_) (fdefs-++ is y)) (sym (++-assoc (fdef-of i) (fdefs is) (fdefs y)))

-- the program image: `_start`, `main`'s unit ending in the silent stop, the table
image-cl : ∀ (o : CanonicalName) (q : IRProgram) → Dst (clabs (program-image o q))
image-cl o q =
  subst Dst (sym eq)
    (dst-++ dM (proj₁ FS) (dj-win wM (proj₂ FS) ≤-refl))
  where
    X  = IT.ir-to-trace' o 0 0 (main q)
    nM = LR.label-of o X
    F  = CLU.frag o (main q) 0 0
    dT = proj₁ (proj₁ F) ; dB = proj₁ (proj₂ (proj₁ F)) ; jTB = proj₂ (proj₂ (proj₁ F))
    wT = proj₁ (proj₂ F) ; wB = proj₂ (proj₂ F)
    TL = CLU.TL o (main q) 0 0
    BL = CLU.BL o (main q) 0 0
    dM : Dst (TL ++ (nM ∷ BL))
    dM = dst-++ dT (fresh-above ≤-refl wB ∷ dB)
           (Data.List.Relation.Unary.All.zipWith (λ (p , q′) → p ∷ q′)
             (Data.List.Relation.Unary.All.map (λ {x} w eq → Data.Nat.Properties.<⇒≢ (proj₂ w) eq) wT , jTB))
    wM : Win 0 (suc nM) (TL ++ (nM ∷ BL))
    wM = All-++⁺ (win-weaken ≤-refl (n≤1+n nM) wT)
                 ((Data.Nat.z≤n , n<1+n nM) ∷ win-weaken ≤-refl (n≤1+n nM) wB)
    FS = fns-cl (suc nM) (table q)
    eq : clabs (program-image o q) ≡ (TL ++ (nM ∷ BL)) ++ clabs (fns-image (suc nM) (table q))
    eq = trans (clabs-++ (link-top (top-done o q) (IT.ir-to-unit o (main q))) _)
               (cong (_++ clabs (fns-image (suc nM) (table q))) (clabs-++ (LSc.trace-of o X) _))

image-fdefs : ∀ (o : CanonicalName) (q : IRProgram) → fdefs (program-image o q) ≡ Data.List.map fname (table q)
image-fdefs o q =
  trans (fdefs-++′ (link-top (top-done o q) (IT.ir-to-unit o (main q))) _)
        (cong (_++ fdefs (fns-image (suc (IT.ir-next-label o 0 (main q))) (table q)))
              (nf (LSc.trace-of o X) _ (proj₁ (CLU.frag-nf o (main q) 0 0)) (proj₂ (CLU.frag-nf o (main q) 0 0)))
         ∙ fns-fdefs (suc (IT.ir-next-label o 0 (main q))) (table q))
  where
    X = IT.ir-to-trace' o 0 0 (main q)
    _∙_ : ∀ {a b c : List CanonicalName} → a ≡ b → b ≡ c → a ≡ c
    _∙_ = trans
    fdefs-++′ : ∀ (x y : AbstractTrace) → fdefs (x ++ y) ≡ fdefs x ++ fdefs y
    fdefs-++′ []       y = refl
    fdefs-++′ (i ∷ is) y = trans (cong (fdef-of i ++_) (fdefs-++′ is y)) (sym (++-assoc (fdef-of i) (fdefs is) (fdefs y)))

------------------------------------------------------------------------
-- The table's entries: distinct symbols, each an identifier's (D249 guard).
------------------------------------------------------------------------

open import Data.Bool using (true; false; if_then_else_)
import Data.Bool

open import Data.Maybe using (nothing)
open import Data.List using (reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to AP-++⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any.Properties
open import Once.Parser using (extractFunctions-go; funsOf; emittedNames)
open import Once.Parser.Module.Core using (Module; mkModule)
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Target.SymbolInjective using (ValidIdent)
open import Once.Adequacy.NameClash using (guard-true; namesDistinct-sound; allValidIdentB-sound; map-allpairs-own; ce-syms; ∧-elimˡ; ∧-elimʳ)
import Once.Compile as C

record TableNames (T : List IRFun) : Set where
  field
    names : List String
    syms≡ : Data.List.map (λ e → once-symbol-path (fname e)) T ≡ reverse (Data.List.map once-symbol-own names)
    dist  : AllPairs _≢_ (Data.List.map once-symbol-own names)
    valid : All ValidIdent names

private
  sym-of : IRFun → String
  sym-of e = once-symbol-path (fname e)

  tbl-go : ∀ (cfs : List C.CompiledFun) (acc : List IRFun)
         → Data.List.map sym-of (C.tableOf-go cfs acc) ≡ reverse (C.emittedSyms cfs) ++ Data.List.map sym-of acc
  tbl-go []         acc = refl
  tbl-go (cf ∷ cfs) acc =
    trans (tbl-go cfs (C.irFunOf cf ∷ acc))
      (trans (sym (++-assoc (reverse (C.emittedSyms cfs)) (once-symbol-path (C.CompiledFun.cfName cf) ∷ []) _))
             (cong (_++ Data.List.map sym-of acc) (sym (unfold-reverse _ (C.emittedSyms cfs)))))

  no-names : TableNames []
  no-names = record { names = [] ; syms≡ = refl ; dist = [] ; valid = [] }

table-names : ∀ (m : Module) → TableNames (C.moduleTable m)
table-names (mkModule ds) with C.extractFunctions (C.extractAliases (mkModule ds)) (mkModule ds) in efeq
... | inj₁ _ = no-names
... | inj₂ es with C.compileEntries C.Heap false C.emptyCScope es in caeq
...   | inj₁ _ = no-names
...   | inj₂ cfs = record
        { names = emittedNames (funsOf es)
        ; syms≡ = trans (trans (tbl-go cfs []) (++-identityʳ _)) (cong reverse (ce-syms false C.emptyCScope es cfs caeq))
        ; dist  = map-allpairs-own _ (namesDistinct-sound _ (∧-elimˡ guard)) (allValidIdentB-sound _ (∧-elimʳ guard))
        ; valid = allValidIdentB-sound _ (∧-elimʳ guard)
        }
  where
    guard = guard-true (extractFunctions-go (C.extractAliases (mkModule ds)) ds nothing) efeq

-- distinctness survives reversal
ap-reverse : ∀ {xs : List String} → AllPairs _≢_ xs → AllPairs _≢_ (reverse xs)
ap-reverse {[]}     []         = []
ap-reverse {x ∷ xs} (px ∷ pxs) =
  subst (AllPairs _≢_) (sym (unfold-reverse x xs))
    (AP-++⁺ (ap-reverse pxs) ([] ∷ []) (rev-all (Data.List.Relation.Unary.All.map (λ ne eq → ne (sym eq)) px)))
  where
    rev-all : ∀ {ys : List String} → All (_≢ x) ys → All (λ y → All (y ≢_) (x ∷ [])) (reverse ys)
    rev-all {ys} a = Data.List.Relation.Unary.All.tabulate
      (λ {y} y∈ → (λ eq → Data.List.Relation.Unary.All.lookup a (rev-∈ y∈) eq) ∷ [])
      where
        rev-∈ : ∀ {y} → y ∈ reverse ys → y ∈ ys
        rev-∈ = Data.List.Relation.Unary.Any.Properties.reverse⁻

------------------------------------------------------------------------
-- Characters: what separates the heap, `_start`, the counters, the entries
-- and the arith blocks.
------------------------------------------------------------------------

open import Data.Char using (Char; isDigit)
open import Data.String using (toList) renaming (_++_ to _++ˢ_)
open import Data.String.Unsafe using (toList-++)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
open import Data.Nat.Show using (charsInBase)
open import Data.Digit using (toDigits)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Product using (Σ-syntax)
open import Once.CCC.Label using (showLabelId)
open import Once.Target.Symbol using (once-prefix; join-us; mangle-component)
open import Once.Target.SymbolInjective
  using (charsInBase-all-digits; HeadNotDigit; digit-prefix-unique; zencL; zencL-inj; zencL-vic; toList-mangle; ValidIdentChars)
open import Once.CCC.Codegen.ImageSymbols using (heap-symbol)

private
  hd : List Char → Char
  hd []      = ' '
  hd (c ∷ _) = c

  shd : String → Char
  shd s = hd (toList s)

  once-hd : ∀ (n : LabelId) → shd (labelSym (once n)) ≡ '.'
  once-hd n = cong hd (toList-++ ".Lonce_" (showLabelId n))

  thunk-hd : ∀ (n : LabelId) → shd (labelSym (callee (e-thunk n))) ≡ '.'
  thunk-hd n = cong hd (toList-++ ".L_thunk_" (showLabelId n))

  osp-hd : ∀ (cn : CanonicalName) → shd (once-symbol-path cn) ≡ 'o'
  osp-hd cn = cong hd (toList-++ once-prefix (join-us (Data.List.map mangle-component (Once.CanonicalName.parts cn))))

  hd≢ : ∀ {s t : String} {a b : Char} → shd s ≡ a → shd t ≡ b → a ≢ b → s ≢ t
  hd≢ hs ht a≢b refl = a≢b (trans (sym hs) ht)

  -- the decimal length prefix is never empty
  map-nil : ∀ {A B : Set} (f : A → B) (xs : List A) → Data.List.map f xs ≡ [] → xs ≡ []
  map-nil f []       _  = refl
  map-nil f (_ ∷ _)  ()

  cib-ne : ∀ (n : ℕ) → charsInBase 10 n ≢ []
  cib-ne Data.Nat.zero    ()
  cib-ne (Data.Nat.suc k) eq =
    0≢s (trans (sym (cong Data.Digit.fromDigits ds≡[])) (proj₂ (toDigits 10 (Data.Nat.suc k))))
    where
      ds = proj₁ (toDigits 10 (Data.Nat.suc k))
      rds≡[] : reverse ds ≡ []
      rds≡[] = map-nil _ (reverse ds) eq
      ds≡[] : ds ≡ []
      ds≡[] = trans (sym (Data.List.Properties.reverse-involutive ds)) (cong reverse rds≡[])
      0≢s : ∀ {m} → 0 ≢ Data.Nat.suc m
      0≢s ()

  cib-head-digit : ∀ (n : ℕ) (rest : List Char) → isDigit (hd (charsInBase 10 n ++ rest)) ≡ true
  cib-head-digit n rest = go (charsInBase 10 n) refl (charsInBase-all-digits n)
    where
      go : ∀ (cs : List Char) → charsInBase 10 n ≡ cs → All (λ c → isDigit c ≡ true) cs → isDigit (hd (cs ++ rest)) ≡ true
      go []      e _       = ⊥-elim (cib-ne n e)
      go (c ∷ _) e (d ∷ _) = d

-- the heap is no canonical name's symbol
heap≢osp : ∀ (cn : CanonicalName) → heap-symbol ≢ once-symbol-path cn
heap≢osp cn eq = body (Once.CanonicalName.parts cn) (trans (cong toList eq) (toList-osp cn))
  where
    toList-osp : ∀ (cn : CanonicalName) → toList (once-symbol-path cn)
               ≡ 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ toList (join-us (Data.List.map mangle-component (Once.CanonicalName.parts cn)))
    toList-osp cn = toList-++ once-prefix (join-us (Data.List.map mangle-component (Once.CanonicalName.parts cn)))
    body : ∀ (ps : List String) → toList heap-symbol ≡ 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ toList (join-us (Data.List.map mangle-component ps)) → ⊥
    body [] ()
    body (p ∷ ps) e = false≢true (trans (cong (λ z → isDigit (hd z)) (peel e)) (digitRHS ps))
      where
        ∷-inj : ∀ {a b : Char} {as bs : List Char} → a ∷ as ≡ b ∷ bs → as ≡ bs
        ∷-inj refl = refl
        peel : toList heap-symbol ≡ 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ toList (join-us (Data.List.map mangle-component (p ∷ ps)))
             → toList "heap_base" ≡ toList (join-us (Data.List.map mangle-component (p ∷ ps)))
        peel e = ∷-inj (∷-inj (∷-inj (∷-inj (∷-inj e))))
        false≢true : false ≡ true → ⊥
        false≢true ()
        L = Data.List.length (zencL (toList p))
        mangle-shape : toList (mangle-component p) ≡ charsInBase 10 L ++ zencL (toList p)
        mangle-shape = toList-mangle p
        digitRHS : ∀ (qs : List String) → isDigit (hd (toList (join-us (Data.List.map mangle-component (p ∷ qs))))) ≡ true
        digitRHS []       = subst (λ z → isDigit (hd z) ≡ true) (sym mangle-shape) (cib-head-digit L (zencL (toList p)))
        digitRHS (q ∷ qs) =
          subst (λ z → isDigit (hd z) ≡ true)
                (sym (trans (toList-++ (mangle-component p) R) (trans (cong (_++ toList R) mangle-shape) (++-assoc (charsInBase 10 L) _ (toList R)))))
                (cib-head-digit L _)
          where R = "_" ++ˢ join-us (Data.List.map mangle-component (q ∷ qs))

-- an identifier's symbol is no arith block's (a block name has a `.`)
own≢block : ∀ (x d : String) → ValidIdent x → once-symbol-own x ≢ once-symbol-own ("arith.block." ++ˢ d)
own≢block x d vx eq = not-valid (subst ValidIdentChars tl≡ vx)
  where
    bn = "arith.block." ++ˢ d
    ∷-inj : ∀ {a b : Char} {as bs : List Char} → a ∷ as ≡ b ∷ bs → as ≡ bs
    ∷-inj refl = refl
    sym-shape : ∀ (y : String) → toList (once-symbol-own y)
              ≡ 'o' ∷ 'n' ∷ 'c' ∷ 'e' ∷ '_' ∷ (charsInBase 10 (Data.List.length (zencL (toList y))) ++ zencL (toList y))
    sym-shape y = trans (toList-++ once-prefix (mangle-component y)) (cong ('o' ∷_) (cong ('n' ∷_) (cong ('c' ∷_)
                    (cong ('e' ∷_) (cong ('_' ∷_) (toList-mangle y))))))
    body≡ : charsInBase 10 (Data.List.length (zencL (toList x))) ++ zencL (toList x)
          ≡ charsInBase 10 (Data.List.length (zencL (toList bn))) ++ zencL (toList bn)
    body≡ = ∷-inj (∷-inj (∷-inj (∷-inj (∷-inj (trans (sym (sym-shape x)) (trans (cong toList eq) (sym-shape bn)))))))
    hnd-x : HeadNotDigit (zencL (toList x))
    hnd-x = let (h , t , e , nd) = zencL-vic vx in subst HeadNotDigit (sym e) nd
    bn-chars : toList bn ≡ 'a' ∷ 'r' ∷ 'i' ∷ 't' ∷ 'h' ∷ '.' ∷ 'b' ∷ 'l' ∷ 'o' ∷ 'c' ∷ 'k' ∷ '.' ∷ toList d
    bn-chars = toList-++ "arith.block." d
    hnd-bn : HeadNotDigit (zencL (toList bn))
    hnd-bn = subst (λ z → HeadNotDigit (zencL z)) (sym bn-chars) refl
    tl≡ : toList x ≡ toList bn
    Lx = Data.List.length (zencL (toList x))
    Lb = Data.List.length (zencL (toList bn))
    tl≡ = zencL-inj (toList x) (toList bn)
            (proj₂ (digit-prefix-unique (charsInBase 10 Lx) (charsInBase 10 Lb) (zencL (toList x)) (zencL (toList bn))
                      (charsInBase-all-digits Lx) (charsInBase-all-digits Lb) hnd-x hnd-bn body≡))
    not-valid : ValidIdentChars (toList bn) → ⊥
    not-valid v = dot (subst ValidIdentChars bn-chars v)
      where
        dot : ValidIdentChars ('a' ∷ 'r' ∷ 'i' ∷ 't' ∷ 'h' ∷ '.' ∷ 'b' ∷ 'l' ∷ 'o' ∷ 'c' ∷ 'k' ∷ '.' ∷ toList d) → ⊥
        dot (_ , (_ ∷ _ ∷ _ ∷ _ ∷ () ∷ _))

------------------------------------------------------------------------
-- The block table: distinct (deduplicated), and every symbol a block name's.
------------------------------------------------------------------------

open import Once.Arith.Machine.IR using (ArithBlock)
open Once.Arith.Machine.IR.ArithBlock using (block-body)
open import Once.Arith.SigOp.Block using (block-digest)
import Data.Bool.ListAction as BLA

BlockSym : String → Set
BlockSym s = Σ[ d ∈ String ] (s ≡ once-symbol-own ("arith.block." ++ˢ d))

private
  ==-false : ∀ {x s : String} → (x Data.String.== s) ≡ false → x ≢ s
  ==-false {x} {s} e eq with x ≟ˢ s
  ... | yes _ = case e of λ ()
    where open import Function using (case_of_)
  ... | no ne = ne eq

  any-false : ∀ {s : String} (seen : List String) → BLA.any (λ x → x Data.String.== s) seen ≡ false → All (_≢ s) seen
  any-false []       _ = []
  any-false {s} (x ∷ xs) e = ==-false (∨-falseˡ e) ∷ any-false xs (∨-falseʳ e)
    where
      ∨-falseˡ : ∀ {a b} → (a Data.Bool.∨ b) ≡ false → a ≡ false
      ∨-falseˡ {false} e = refl
      ∨-falseʳ : ∀ {a b} → (a Data.Bool.∨ b) ≡ false → b ≡ false
      ∨-falseʳ {false} e = e

  DD : List String → List (String × ArithBlock) → Set
  DD seen xs = AllPairs _≢_ (Data.List.map proj₁ xs) × All (λ q → All (_≢ proj₁ q) seen) xs

  dedup-dd : ∀ (seen : List String) (xs : List (String × ArithBlock)) → DD seen (C.dedup-go seen xs)
  dedup-step : ∀ (seen : List String) (s : String) (b : ArithBlock) (bs : List (String × ArithBlock)) (r : _)
             → BLA.any (λ x → x Data.String.== s) seen ≡ r
             → DD seen (if r then C.dedup-go seen bs else (s , b) ∷ C.dedup-go (s ∷ seen) bs)
  dedup-dd seen []             = [] , []
  dedup-dd seen ((s , b) ∷ bs) = dedup-step seen s b bs _ refl
  dedup-step seen s b bs true  _ = dedup-dd seen bs
  dedup-step seen s b bs false e =
    let (ap , al) = dedup-dd (s ∷ seen) bs
    in (head-fresh (C.dedup-go (s ∷ seen) bs) al ∷ ap)
       , (any-false {s = s} seen e ∷ Data.List.Relation.Unary.All.map (λ {q} → tl {q}) al)
    where
      tl : ∀ {q : String × ArithBlock} → All (_≢ proj₁ q) (s ∷ seen) → All (_≢ proj₁ q) seen
      tl (_ ∷ rest) = rest
      head-fresh : ∀ (ys : List (String × ArithBlock)) → All (λ q → All (_≢ proj₁ q) (s ∷ seen)) ys
                 → All (s ≢_) (Data.List.map proj₁ ys)
      head-fresh []       []             = []
      head-fresh (_ ∷ ys) ((p ∷ _) ∷ ps) = p ∷ head-fresh ys ps

  dedup-⊆ : ∀ {P : String → Set} (seen : List String) (xs : List (String × ArithBlock))
          → All (λ q → P (proj₁ q)) xs → All (λ q → P (proj₁ q)) (C.dedup-go seen xs)
  dedup-⊆-step : ∀ {P : String → Set} (seen : List String) (s : String) (b : ArithBlock) (bs : List (String × ArithBlock)) (r : _)
               → P s → All (λ q → P (proj₁ q)) bs
               → All (λ q → P (proj₁ q)) (if r then C.dedup-go seen bs else (s , b) ∷ C.dedup-go (s ∷ seen) bs)
  dedup-⊆ seen []             []       = []
  dedup-⊆ seen ((s , b) ∷ bs) (p ∷ ps) = dedup-⊆-step seen s b bs _ p ps
  dedup-⊆-step seen s b bs true  p ps = dedup-⊆ seen bs ps
  dedup-⊆-step seen s b bs false p ps = p ∷ dedup-⊆ (s ∷ seen) bs ps

  tag : ArithBlock → String × ArithBlock
  tag b = C.block-symbol b , b

  tagged : ∀ (bs : List ArithBlock) → All (λ q → BlockSym (proj₁ q)) (Data.List.map tag bs)
  tagged []       = []
  tagged (b ∷ bs) = (block-digest (block-body b) , refl) ∷ tagged bs

  fsts : ∀ {P : String → Set} (xs : List (String × ArithBlock)) → All (λ q → P (proj₁ q)) xs → All P (Data.List.map proj₁ xs)
  fsts []       []       = []
  fsts (_ ∷ xs) (p ∷ ps) = p ∷ fsts xs ps

blocks-unique : ∀ (bs : List ArithBlock) → AllPairs _≢_ (C.block-syms bs)
blocks-unique bs = proj₁ (dedup-dd [] (Data.List.map tag bs))

blocks-sym : ∀ (bs : List ArithBlock) → All BlockSym (C.block-syms bs)
blocks-sym bs = fsts (C.dedup-blocks (Data.List.map tag bs)) (dedup-⊆ [] (Data.List.map tag bs) (tagged bs))

------------------------------------------------------------------------
-- What an image's definition is: a counter label's (`.`-headed) or a
-- function entry's.
------------------------------------------------------------------------

import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.All using (tabulate; lookup)
open import Data.List.Relation.Unary.All.Properties using () renaming (map⁺ to All-map⁺)

private
  rights-∈ : ∀ {s : String} (xs : List (ℕ ⊎ String)) → inj₂ s ∈ xs → s ∈ rights xs
  rights-∈ (inj₁ _ ∷ xs) (here ())
  rights-∈ (inj₁ _ ∷ xs) (there m) = rights-∈ xs m
  rights-∈ (inj₂ _ ∷ xs) (here refl) = here refl
  rights-∈ (inj₂ _ ∷ xs) (there m) = there (rights-∈ xs m)

DefClass : List CanonicalName → String → Set
DefClass fs s = (shd s ≡ '.') ⊎ (s ∈ Data.List.map once-symbol-path fs)

adefs-class : ∀ (t : AbstractTrace) → All (DefClass (fdefs t)) (adefs t)
adefs-class t = subst (All (DefClass (fdefs t))) (sym (adefs-labs t)) (All-map⁺ (tabulate cls))
  where
    cls : ∀ {x : Label} → x ∈ dlabs t → DefClass (fdefs t) (labelSym x)
    cls {once n} _ = inj₁ (once-hd n)
    cls {callee (e-thunk n)} _ = inj₁ (thunk-hd n)
    cls {callee (e-fn f)} x∈ =
      inj₂ (subst (once-symbol-path f ∈_) (keys-rights t) (rights-∈ (Data.List.map key (dlabs t)) (∈-map⁺ key x∈)))
    cls {Label.sigop s k} x∈ = ⊥-elim (no-sigop (lookup (dlabs-def t) x∈))
      where no-sigop : DefL (Label.sigop s k) → ⊥
            no-sigop ()

------------------------------------------------------------------------
-- THE THEOREMS
------------------------------------------------------------------------

open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Properties using (map-∘)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
open import Once.Denotation.Program using (irProgram)
open import Once.Adequacy.ImageWF using (prog-defs; lib-defs)

private
  rt-names : ∀ (T : List IRFun) → Data.List.map fname (C.rewrite-table T) ≡ Data.List.map fname T
  rt-names []       = refl
  rt-names (e ∷ es) = cong (fname e ∷_) (rt-names es)

  -- the function entries of an image whose table is `T`'s, read through the guard
  module Entries (T : List IRFun) (tn : TableNames T) where
    open TableNames tn
    EF : List String
    EF = Data.List.map once-symbol-path (Data.List.map fname (C.rewrite-table T))
    EF≡ : EF ≡ reverse (Data.List.map once-symbol-own names)
    EF≡ = trans (cong (Data.List.map once-symbol-path) (rt-names T)) (trans (sym (map-∘ T)) syms≡)
    EF-dist : AllPairs _≢_ EF
    EF-dist = subst (AllPairs _≢_) (sym EF≡) (ap-reverse dist)
    EF-own : ∀ {s} → s ∈ EF → Σ[ x ∈ String ] (ValidIdent x × s ≡ once-symbol-own x)
    EF-own {s} s∈ with ∈-map⁻ once-symbol-own (AnyP.reverse⁻ {xs = Data.List.map once-symbol-own names} (subst (s ∈_) EF≡ s∈))
    ... | x , x∈ , refl = x , lookup valid x∈ , refl

  -- …and so the definitions, the blocks, the heap and `_start` are apart.
  module Apart (fs : List CanonicalName) (T : List IRFun) (tn : TableNames T)
               (fs≡ : Data.List.map once-symbol-path fs ≡ Entries.EF T tn) where
    open Entries T tn
    toEF : ∀ {s} → s ∈ Data.List.map once-symbol-path fs → s ∈ EF
    toEF = subst (_ ∈_) fs≡

    def≢blk : ∀ {s t} → DefClass fs s → BlockSym t → s ≢ t
    def≢blk (inj₁ h) (d , refl) = hd≢ h (osp-hd (canonical (("arith.block." ++ˢ d) ∷ []))) (λ ())
    def≢blk (inj₂ s∈) (d , refl) with EF-own (toEF s∈)
    ... | x , vx , refl = own≢block x d vx

    heap≢def : ∀ {s} → DefClass fs s → heap-symbol ≢ s
    heap≢def (inj₁ h) = hd≢ refl h (λ ())
    heap≢def (inj₂ s∈) with EF-own (toEF s∈)
    ... | x , _ , refl = heap≢osp (canonical (x ∷ []))

    heap≢blk : ∀ {t} → BlockSym t → heap-symbol ≢ t
    heap≢blk (d , refl) = heap≢osp (canonical (("arith.block." ++ˢ d) ∷ []))

    start≢def : ∀ {s} → DefClass fs s → "_start" ≢ s
    start≢def (inj₁ h) = hd≢ refl h (λ ())
    start≢def (inj₂ s∈) with EF-own (toEF s∈)
    ... | x , _ , refl = hd≢ refl (osp-hd (canonical (x ∷ []))) (λ ())

    start≢blk : ∀ {t} → BlockSym t → "_start" ≢ t
    start≢blk (d , refl) = hd≢ refl (osp-hd (canonical (("arith.block." ++ˢ d) ∷ []))) (λ ())

    defs++blocks : ∀ (D B : List String) → All (DefClass fs) D → All BlockSym B
                 → AllPairs _≢_ D → AllPairs _≢_ B → AllPairs _≢_ (D ++ B)
    defs++blocks D B cD cB uD uB =
      AP-++⁺ uD uB (Data.List.Relation.Unary.All.map (λ {s} cs → Data.List.Relation.Unary.All.map (def≢blk cs) cB) cD)

    heap-fresh : ∀ (D B : List String) → All (DefClass fs) D → All BlockSym B → All (heap-symbol ≢_) (D ++ B)
    heap-fresh D B cD cB = All-++⁺ (Data.List.Relation.Unary.All.map heap≢def cD) (Data.List.Relation.Unary.All.map heap≢blk cB)

    start-fresh : ∀ (D B : List String) → All (DefClass fs) D → All BlockSym B → All ("_start" ≢_) (D ++ B)
    start-fresh D B cD cB = All-++⁺ (Data.List.Relation.Unary.All.map start≢def cD) (Data.List.Relation.Unary.All.map start≢blk cB)

-- THE PROGRAM (was `ImageWF.prog-unique`, a postulate).
prog-unique : ∀ (m : Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Unique (prog-defs (irProgram (C.moduleTable m) ir))
prog-unique m ir =
  ((λ ()) ∷ heap-fresh D B cD cB) ∷ start-fresh D B cD cB ∷ defs++blocks D B cD cB uD (blocks-unique (C.program-blocks p))
  where
    T  = C.moduleTable m
    tn = table-names m
    p  = irProgram T ir
    q  = C.rewrite-program p
    img = C.image-of p
    fs = fdefs img
    fs≡ : Data.List.map once-symbol-path fs ≡ Entries.EF T tn
    fs≡ = cong (Data.List.map once-symbol-path) (image-fdefs C.entry-owner q)
    open Apart fs T tn fs≡
    D = adefs img
    B = C.block-syms (C.program-blocks p)
    cD = adefs-class img
    cB = blocks-sym (C.program-blocks p)
    uD = adefs-unique img (image-cl C.entry-owner q) (subst (AllPairs _≢_) (sym fs≡) (Entries.EF-dist T tn))

-- THE LIBRARY (was `ImageWF.lib-unique`, a postulate).
lib-unique : ∀ (m : Module) → Unique (lib-defs m)
lib-unique m =
  heap-fresh D B cD cB ∷ defs++blocks D B cD cB uD (blocks-unique (C.lib-blocks T))
  where
    T  = C.moduleTable m
    tn = table-names m
    img = C.lib-image T
    fs = fdefs img
    fs≡ : Data.List.map once-symbol-path fs ≡ Entries.EF T tn
    fs≡ = cong (Data.List.map once-symbol-path) (fns-fdefs 0 (C.rewrite-table T))
    open Apart fs T tn fs≡
    D = adefs img
    B = C.block-syms (C.lib-blocks T)
    cD = adefs-class img
    cB = blocks-sym (C.lib-blocks T)
    uD = adefs-unique img (proj₁ (fns-cl 0 (C.rewrite-table T))) (subst (AllPairs _≢_) (sym fs≡) (Entries.EF-dist T tn))
