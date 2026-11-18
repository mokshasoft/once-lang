-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ImageUnique — plan 0.107 §8 step 4: EVERY SYMBOL A FILE
-- DEFINES IS DEFINED ONCE (`AsmWF.defined-once`).
--
-- Were `ImageWF.prog-unique` / `lib-unique`, postulates (master's image, deleted with it in plan
-- 0.146 step 4, D462: the linear core's image is `LinCore.ImageSyms`). What is left is generic: the
-- defined labels of a trace, the table's names, the arith blocks' symbols. The argument was:
--   * the image's definitions are the `labelSym` of its defined LABELS;
--   * a label's `key` — a counter label's index, a function entry's symbol —
--     is recovered from its symbol (`LabelSymbols.sym-key`), so distinct keys
--     mean distinct symbols;
--   * the counter labels are pairwise distinct: each unit's by
--     `CLabelsUnique.frag`, across units by their disjoint counter windows;
--   * the function entries are the table's, whose symbols the extractor's guard
--     keeps distinct (`NameClash.program-no-clash`), and no unit defines one
--     (`CLabelsUnique.frag-nf`);
--   * the entry (`once_main`) and the arith blocks are separated from all of these
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

open import Once.Spec.Name using (CanonicalName; canonical)
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
idefs (instr-ctrl (c-branch-tag-zero _)) = refl
idefs (instr-ctrl (c-ret _)) = refl
idefs (instr-ctrl (c-call-fn _)) = refl
idefs (instr-ctrl (c-start _)) = refl
idefs (instr-ctrl c-leave) = refl
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
idefs (instr-free-heap _) = refl
idefs (load-at _) = refl
idefs (store-at _) = refl
idefs (addr-at _) = refl
idefs (instr-room _) = refl
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
idefs (instr-alloc-heap _) = refl
idefs (instr-reg-op _) = refl

-- …its labels are definitions…
idefl : ∀ (i : AbstractInstr) → All DefL (ilab i)
idefl (instr-ctrl (c-label m)) = d-once ∷ []
idefl (instr-ctrl (c-entry (e-thunk m) _)) = d-callee ∷ []
idefl (instr-ctrl (c-entry (e-fn f) _)) = d-callee ∷ []
idefl (instr-ctrl (c-jmp _)) = []
idefl (instr-ctrl (c-branch-tag-zero _)) = []
idefl (instr-ctrl (c-ret _)) = []
idefl (instr-ctrl (c-call-fn _)) = []
idefl (instr-ctrl (c-start _)) = []
idefl (instr-ctrl c-leave) = []
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
idefl (instr-free-heap _) = []
idefl (load-at _) = []
idefl (store-at _) = []
idefl (addr-at _) = []
idefl (instr-room _) = []
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
idefl (instr-alloc-heap _) = []
idefl (instr-reg-op _) = []

-- …its counter labels are `clab-of`'s, its function entries `fdef-of`'s.
ileft : ∀ (i : AbstractInstr) → lefts (map key (ilab i)) ≡ cl-at (clab-of i) []
ileft (instr-ctrl (c-label m)) = refl
ileft (instr-ctrl (c-entry (e-thunk m) _)) = refl
ileft (instr-ctrl (c-entry (e-fn f) _)) = refl
ileft (instr-ctrl (c-jmp _)) = refl
ileft (instr-ctrl (c-branch-tag-zero _)) = refl
ileft (instr-ctrl (c-ret _)) = refl
ileft (instr-ctrl (c-call-fn _)) = refl
ileft (instr-ctrl (c-start _)) = refl
ileft (instr-ctrl c-leave) = refl
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
ileft (instr-free-heap _) = refl
ileft (load-at _) = refl
ileft (store-at _) = refl
ileft (addr-at _) = refl
ileft (instr-room _) = refl
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
ileft (instr-alloc-heap _) = refl
ileft (instr-reg-op _) = refl

iright : ∀ (i : AbstractInstr) → rights (map key (ilab i)) ≡ map once-symbol-path (fdef-of i)
iright (instr-ctrl (c-label m)) = refl
iright (instr-ctrl (c-entry (e-thunk m) _)) = refl
iright (instr-ctrl (c-entry (e-fn f) _)) = refl
iright (instr-ctrl (c-jmp _)) = refl
iright (instr-ctrl (c-branch-tag-zero _)) = refl
iright (instr-ctrl (c-ret _)) = refl
iright (instr-ctrl (c-call-fn _)) = refl
iright (instr-ctrl (c-start _)) = refl
iright (instr-ctrl c-leave) = refl
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
iright (instr-free-heap _) = refl
iright (load-at _) = refl
iright (store-at _) = refl
iright (addr-at _) = refl
iright (instr-room _) = refl
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
iright (instr-alloc-heap _) = refl
iright (instr-reg-op _) = refl

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

open import Data.Nat using (suc; _≤_)
open import Once.Denotation.Program using (IRFun; IRProgram)
open Once.Denotation.Program.IRFun using (fbody; fname)

------------------------------------------------------------------------
-- The table's entries: distinct symbols, each an identifier's (D249 guard).
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false; if_then_else_)
import Data.Bool

open import Data.Maybe using (nothing)
open import Data.List using (reverse)
open import Data.List.Properties using (unfold-reverse)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to AP-++⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any.Properties
open import Once.Parser using (extractFunctions-go; funsOf; emittedNames)
open import Once.Parser.Module.Core using (Resolved; resolved)
open import Once.Spec.Surface.Syntax using (Module; mkModule)
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Target.SymbolInjective using (ValidName)
open import Once.Adequacy.NameClash using (guard-true; namesDistinct-sound; allValidNameB-sound; map-allpairs-own; ce-syms; ∧-elimˡ; ∧-elimʳ)
import Once.Compile as C
import Once.IR as IR
import Once.Parser as Parser

record TableNames (T : List IRFun) : Set where
  field
    names : List String
    syms≡ : Data.List.map (λ e → once-symbol-path (fname e)) T ≡ reverse (Data.List.map once-symbol-own names)
    dist  : AllPairs _≢_ (Data.List.map once-symbol-own names)
    valid : All ValidName names

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

-- At either build: the optimizer keeps every function's name (plan 0.39).
table-names-at : ∀ (doOpt : Bool) (m : Resolved) → TableNames (C.tableOfResult (C.compileResolvedModule IR.Heap doOpt m))
table-names-at doOpt (resolved (mkModule ds) is) with Parser.extractFunctions (resolved (mkModule ds) is) in efeq
... | inj₁ _ = no-names
... | inj₂ es with C.compileEntries IR.Heap doOpt C.emptyCScope es in caeq
...   | inj₁ _ = no-names
...   | inj₂ cfs = record
        { names = emittedNames (funsOf es)
        ; syms≡ = trans (trans (tbl-go cfs []) (++-identityʳ _)) (cong reverse (ce-syms doOpt C.emptyCScope es cfs caeq))
        ; dist  = map-allpairs-own _ (namesDistinct-sound _ (∧-elimˡ guard)) (allValidNameB-sound _ (∧-elimʳ guard))
        ; valid = allValidNameB-sound _ (∧-elimʳ guard)
        }
  where
    guard = guard-true (Parser.thenExtract (Parser.sigsAdjacent ds nothing) (extractFunctions-go (Parser.sigsFirst ds is) nothing)) efeq

table-names : ∀ (m : Resolved) → TableNames (C.moduleTable m)
table-names = table-names-at false

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
-- Characters: what separates the program's entry, the counters, the entries
-- and the arith blocks.
------------------------------------------------------------------------

open import Data.Char using (Char; isDigit)
open import Data.String using (toList) renaming (_++_ to _++ˢ_)
open import Once.Postulates using (toList-++)
import Data.String.Properties as Str
open import Data.Nat.Show using (charsInBase)
open import Data.Digit using (toDigits)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Product using (Σ-syntax)
open import Once.CCC.Label using (showLabelId)
open import Once.Target.Symbol using (once-prefix; join-us; mangle-component)
open import Once.Target.SymbolInjective
  using (charsInBase-all-digits; HeadNotDigit; digit-prefix-unique; zencL; zencL-inj; zencL-vic; toList-mangle; NameChars)
open import Once.CCC.Codegen.ImageSymbols using (entry-symbol)
open import Once.Target.SymbolFresh using (letter≢osp)

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
  osp-hd cn = cong hd (toList-++ once-prefix (join-us (Data.List.map mangle-component (Once.Spec.Name.CanonicalName.parts cn))))

  hd≢ : ∀ {s t : String} {a b : Char} → shd s ≡ a → shd t ≡ b → a ≢ b → s ≢ t
  hd≢ hs ht a≢b refl = a≢b (trans (sym hs) ht)


-- the entry is no canonical name's symbol (`SymbolFresh`: the prefix, then a letter)
entry≢osp : ∀ (cn : CanonicalName) → entry-symbol ≢ once-symbol-path cn
entry≢osp = letter≢osp entry-symbol 'm' (toList "ain") refl refl

-- a definition's symbol is no arith block's (a block name has a `.` and a letter)
own≢block : ∀ (x d : String) → ValidName x → once-symbol-own x ≢ once-symbol-own ("arith.block." ++ˢ d)
own≢block x d vx eq = not-valid (subst NameChars tl≡ vx)
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
    not-valid : NameChars (toList bn) → ⊥
    not-valid v = dot (subst NameChars bn-chars v)
      where
        dot : NameChars ('a' ∷ 'r' ∷ 'i' ∷ 't' ∷ 'h' ∷ '.' ∷ 'b' ∷ 'l' ∷ 'o' ∷ 'c' ∷ 'k' ∷ '.' ∷ toList d) → ⊥
        dot (inj₁ (_ , (_ ∷ _ ∷ _ ∷ _ ∷ () ∷ _)))
        dot (inj₂ (() ∷ _))

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
  ==-false {x} {s} e eq with x Str.≟ s
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
-- plan 0.135 S3: THE TABLE'S NAMES ARE DISTINCT (`LinkedProgram`'s last
-- component, what `find-fn` resolving a linked call to ITS entry needs). The
-- symbols are distinct (the extractor guard), and equal names give equal
-- symbols. At either build: the optimizer keeps every function's name.
------------------------------------------------------------------------

open import Once.Denotation.Program using (NamesDistinct)

private
  ap-unmap : ∀ {xs : List IRFun}
           → AllPairs _≢_ (Data.List.map (λ e → once-symbol-path (fname e)) xs)
           → NamesDistinct xs
  ap-unmap {[]}     []         = []
  ap-unmap {x ∷ xs} (px ∷ pxs) = all-un xs px ∷ ap-unmap pxs
    where
      all-un : ∀ (ys : List IRFun) → All (once-symbol-path (fname x) ≢_) (Data.List.map (λ e → once-symbol-path (fname e)) ys)
             → All (λ y → fname x ≢ fname y) ys
      all-un []       []       = []
      all-un (y ∷ ys) (n ∷ ns) = (λ eq → n (cong once-symbol-path eq)) ∷ all-un ys ns

names-distinct-at : ∀ (T : List IRFun) → TableNames T → NamesDistinct T
names-distinct-at T tn =
  ap-unmap (subst (AllPairs _≢_) (sym (TableNames.syms≡ tn)) (ap-reverse (TableNames.dist tn)))

table-names-distinct : ∀ (m : Resolved) → NamesDistinct (C.moduleTable m)
table-names-distinct m = names-distinct-at (C.moduleTable m) (table-names m)
