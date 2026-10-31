-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FnLayout — plan 0.135 S4 for the program's
-- FUNCTIONS: every table entry is where the image puts it (`EntryAt`).
--
-- The image is `main`'s unit and then the entries, each its `e-fn` marker
-- followed by its linked unit. Two facts about the WHOLE image settle every
-- scan: its counter labels are distinct (`ImageUnique.image-cl`), and the only
-- function markers are the entries', whose names are distinct. So for an
-- entry with prefix `P` before it:
--   * the call scan misses `P` (no marker there names it) and hits the entry;
--   * a label its body defines is defined nowhere in `P`, so the jump scan
--     stops inside the body (`entry-head`, `BlockLabels.block-head` for an
--     `e-fn` marker);
--   * its blocks are `BlockLayout.blocks-at`/`BlockLabels.labels-all` behind
--     the body, with the misses read off the same distinctness.
-- Everything is then extended over the entries after it (the prefix laws).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
module Once.Adequacy.ArchCorrectness.FnLayout (o : CanonicalName) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head) renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties using (++⁻ʳ) renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.IR using (IR)
open import Once.IRTy using (Unit)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (LabelId; module LabelId; EntryId; e-thunk; e-fn; _≡ᵇᴱ_; ≡ᵇᴱ-refl; ≡ᵇᴱ-true)
open LabelId using (idx)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; instr-ctrl; c-entry; c-thunk; c-ret; c-start; block-layout; blocks-layout; link-top)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Codegen.BlockLayout using (module Layout)
import Once.CCC.Codegen.BlockLabels as BLs
open import Once.CCC.Codegen.LabelDefs using (Dst; dst-split; clab-of; cl-at; clabs; clabs-++; fdef-of; fdefs; NoFn; nf)
open import Once.Denotation.Program using (IRFun; IRProgram; irProgram; NamesDistinct)
open Once.Denotation.Program.IRFun using (fname; fbody)
open import Once.CCC.Codegen.ProgramImage using (program-image; fns-image; fn-image; fn-next)
import Once.CCC.Codegen.IRToTrace as IT
import Once.CCC.Codegen.CLabelsUnique as CLU
import Once.CCC.Codegen.LabelScope as LSc
import Once.CCC.Codegen.IRObsCorrect.Interface as Iface
import Once.CCC.Codegen.IRObsCorrect.BlockCall as BCall
open import Once.Adequacy.ImageUnique using (image-cl; fn-unit-nf)
open import Once.Adequacy.ArchCorrectness.FnRuns using (module FnRunsC)

module FnLayoutC {FS : FrameSemantics} where

  open FlatMachine {FS}
    using (fetch; fetch-++-left; find-label; find-thunk; find-fn; ft-go; ft-at; ft-match; entry-of?; entry-of?-sound;
           thunk-of?; label-of?; fl-go-++-miss; ft-go-++-miss; ft-go-prefix)
  open FlatStepsAPI {FS} using (fl-go-prefix; fl-go-shift)
  open Layout {FS} using (Span; fetch-skip; span-head; span-shift; MissBefore; blocks-at; NoThunk; NoThunks; missBefore-from)
  open BLs.Labels o {FS} using (BodyLabels; labels-all; found-clab; clabs-miss; cl-head; cl-tail; just-inj; clab-fetch)
  open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
  open Resolve {FS} using (NoLabel; no-label-miss)
  open FnRunsC {FS} using (EntryAt)

  ------------------------------------------------------------------------
  -- One entry's parts.
  ------------------------------------------------------------------------

  -- body text, marker budget and blocks of `e`'s unit at counter `l`
  body : IRFun → ℕ → AbstractTrace
  body e l = Iface.Core.emitted (fname e) [] {FS} 0 l (fbody e)

  bud : IRFun → ℕ → ℕ
  bud e l = IT.ir-stack-budget-from (fname e) l (fbody e)

  bks : IRFun → ℕ → List (LabelId × ℕ × AbstractTrace)
  bks e l = Iface.Core.blocks (fname e) [] {FS} 0 l (fbody e)

  -- the entry's head: marker, body, return
  hd : IRFun → ℕ → AbstractTrace
  hd e l = BCall.BlockCallC.entry-layout (fname e) [] {FS} (e-fn (fname e)) (bud e l) (body e l)

  fn-split : ∀ (e : IRFun) (l : ℕ) → fn-image l e ≡ hd e l ++ blocks-layout (bks e l)
  fn-split e l = cong (instr-ctrl (c-entry (e-fn (fname e)) (bud e l)) ∷_)
                      (sym (++-assoc (body e l) (instr-ctrl (c-ret (bud e l)) ∷ []) (blocks-layout (bks e l))))

  ------------------------------------------------------------------------
  -- The call scan.
  ------------------------------------------------------------------------

  -- a prefix none of whose markers names `f` is missed
  no-fn-miss : ∀ (f : CanonicalName) (X : AbstractTrace) (i : ℕ) → All (_≢ f) (fdefs X) → ft-go X (e-fn f) i ≡ nothing
  no-fn-miss f []      i _ = refl
  no-fn-miss f (x ∷ X) i h = go (entry-of? x) refl
    where
      tl : All (_≢ f) (fdefs X)
      tl = ++⁻ʳ (fdef-of x) h

      go : ∀ (mo : Maybe EntryId) → entry-of? x ≡ mo → ft-at mo X (e-fn f) i ≡ nothing
      go nothing  _  = no-fn-miss f X (suc i) tl
      go (just m) eq = mt (m ≡ᵇᴱ e-fn f) refl
        where
          not-f : m ≢ e-fn f
          not-f me = head h′ refl
            where
              sh = entry-of?-sound x (e-fn f) (trans eq (cong just me))
              h′ : All (_≢ f) (f ∷ fdefs X)
              h′ = subst (λ y → All (_≢ f) (fdefs (y ∷ X))) (proj₂ sh) h
          mt : ∀ (bb : Bool) → (m ≡ᵇᴱ e-fn f) ≡ bb → ft-match bb X (e-fn f) i ≡ nothing
          mt true  be = ⊥-elim (not-f (≡ᵇᴱ-true m (e-fn f) be))
          mt false _  = no-fn-miss f X (suc i) tl

  fn-hit : ∀ (f : CanonicalName) (b : ℕ) (rest : AbstractTrace) (i : ℕ)
         → ft-go (instr-ctrl (c-entry (e-fn f) b) ∷ rest) (e-fn f) i ≡ just i
  fn-hit f b rest i rewrite ≡ᵇᴱ-refl (e-fn f) = refl

  ------------------------------------------------------------------------
  -- The jump scan, for an entry's own body (`BlockLabels.block-head` with an
  -- `e-fn` marker, which defines no counter label).
  ------------------------------------------------------------------------

  entry-head : ∀ (pre : AbstractTrace) (f : CanonicalName) (b : ℕ) (t rest : AbstractTrace)
             → All (λ x → All (x ≢_) (clabs (t ++ instr-ctrl (c-ret b) ∷ rest))) (clabs pre)
             → ∀ (m : LabelId) (k : ℕ) → find-label t m ≡ just k
             → find-label (pre ++ instr-ctrl (c-entry (e-fn f) b) ∷ (t ++ instr-ctrl (c-ret b) ∷ rest)) m
               ≡ just (k + suc (length pre + 0))
  entry-head pre f b t rest dj m k eq =
    trans (fl-go-++-miss pre (instr-ctrl (c-entry (e-fn f) b) ∷ bd) m 0
             (no-label-miss m pre 0 (clabs-miss m pre (All-map past dj))))
          (trans (fl-go-shift bd m (suc (length pre + 0)) 0)
                 (cong (map (_+ suc (length pre + 0))) found))
    where
      bd : AbstractTrace
      bd = t ++ instr-ctrl (c-ret b) ∷ rest
      found : find-label bd m ≡ just k
      found = subst (λ z → find-label z m ≡ just k) (++-assoc t (instr-ctrl (c-ret b) ∷ []) rest)
                (fl-go-prefix (t ++ instr-ctrl (c-ret b) ∷ []) rest m 0 k
                  (fl-go-prefix t (instr-ctrl (c-ret b) ∷ []) m 0 k eq))
      past : ∀ {x} → All (x ≢_) (clabs bd) → x ≢ idx m
      past h = found-clab bd m k found h

  ------------------------------------------------------------------------
  -- No earlier thunk marker carries a block's label.
  ------------------------------------------------------------------------

  thunk-clab : ∀ (i : AbstractInstr) (m : LabelId) → thunk-of? i ≡ just m → clab-of i ≡ just (idx m)
  thunk-clab (instr-ctrl (c-entry (e-thunk m) b)) .m refl = refl

  nothunk-from : ∀ (lbl : LabelId) (X : AbstractTrace) → All (_≢ idx lbl) (clabs X) → NoThunk lbl X
  nothunk-from lbl []       _ = []
  nothunk-from lbl (i ∷ is) h = go (clab-of i) refl h
    where
      go : ∀ (mo : Maybe ℕ) → clab-of i ≡ mo → All (_≢ idx lbl) (cl-at mo (clabs is)) → NoThunk lbl (i ∷ is)
      go (just k) e (p ∷ ps) = (λ te → p (just-inj (trans (sym e) (thunk-clab i lbl te)))) ∷ nothunk-from lbl is ps
      go nothing  e ps       = (λ te → nj (trans (sym e) (thunk-clab i lbl te))) ∷ nothunk-from lbl is ps
        where nj : ∀ {k : ℕ} → nothing ≡ just k → ⊥
              nj ()

  dst-nothunks : ∀ (pre : AbstractTrace) (bs : List (LabelId × ℕ × AbstractTrace))
               → Dst (clabs (pre ++ blocks-layout bs)) → NoThunks pre bs
  dst-nothunks pre []                   _ = tt
  dst-nothunks pre ((lbl , b , t) ∷ bs) d =
    nothunk-from lbl pre (All-map (λ h → head h) dj)
    , dst-nothunks (pre ++ block-layout (lbl , b , t)) bs (subst Dst eqn d)
    where
      d′ : Dst (clabs pre ++ clabs (blocks-layout ((lbl , b , t) ∷ bs)))
      d′ = subst Dst (clabs-++ pre _) d
      dj = proj₂ (proj₂ (dst-split (clabs pre) _ d′))
      eqn : clabs (pre ++ blocks-layout ((lbl , b , t) ∷ bs)) ≡ clabs ((pre ++ block-layout (lbl , b , t)) ++ blocks-layout bs)
      eqn = cong clabs (sym (++-assoc pre (block-layout (lbl , b , t)) (blocks-layout bs)))

  ------------------------------------------------------------------------
  -- ONE ENTRY, behind a prefix `P` and before a rest `R`.
  ------------------------------------------------------------------------

  entry-at : ∀ (P : AbstractTrace) (l : ℕ) (e : IRFun) (R : AbstractTrace)
           → Dst (clabs (P ++ fn-image l e ++ R))
           → All (_≢ fname e) (fdefs P)
           → EntryAt (P ++ fn-image l e ++ R) e
  entry-at P l e R d fr = record
    { lab    = l
    ; ent    = length P + 0
    ; found  = trans (ft-go-++-miss P (fn-image l e ++ R) (e-fn f) 0 (no-fn-miss f P 0 fr))
                     (fn-hit f (bud e l) _ (length P + 0))
    ; span   = span-shift P (fn-image l e ++ R) (hd e l) 0
                 (subst (λ z → Span z 0 (hd e l)) (sym split-R) (span-head (hd e l) (blocks-layout (bks e l) ++ R)))
    ; labels = λ m k eq → subst (λ z → find-label z m ≡ just (k + suc (length P + 0))) (sym prog-eq)
                              (entry-head P f (bud e l) t (blocks-layout bs ++ R) dj-body m k eq)
    ; blks   = blocks-final
    }
    where
      f = fname e
      t = body e l
      bs = bks e l

      split-R : fn-image l e ++ R ≡ hd e l ++ (blocks-layout bs ++ R)
      split-R = trans (cong (_++ R) (fn-split e l)) (++-assoc (hd e l) (blocks-layout bs) R)

      -- the whole program, regrouped
      T₁ : AbstractTrace
      T₁ = P ++ hd e l
      prog≡ : P ++ fn-image l e ++ R ≡ (T₁ ++ blocks-layout bs) ++ R
      prog≡ = trans (cong (P ++_) split-R)
                (trans (sym (++-assoc P (hd e l) (blocks-layout bs ++ R)))
                       (sym (++-assoc T₁ (blocks-layout bs) R)))

      -- the program with the body's text in front of everything after it
      prog-eq : P ++ fn-image l e ++ R
              ≡ P ++ instr-ctrl (c-entry (e-fn f) (bud e l)) ∷ (t ++ instr-ctrl (c-ret (bud e l)) ∷ (blocks-layout bs ++ R))
      prog-eq = cong (λ z → P ++ instr-ctrl (c-entry (e-fn f) (bud e l)) ∷ z)
                     (++-assoc t (instr-ctrl (c-ret (bud e l)) ∷ blocks-layout bs) R)

      -- the labels the prefix defines are not the body's
      dj-body : All (λ x → All (x ≢_) (clabs (t ++ instr-ctrl (c-ret (bud e l)) ∷ (blocks-layout bs ++ R)))) (clabs P)
      dj-body = proj₂ (proj₂ (dst-split (clabs P) _
                  (subst Dst (trans (cong clabs prog-eq) (clabs-++ P _)) d)))

      -- the blocks, behind `T₁`, then extended over `R`
      dT : Dst (clabs (T₁ ++ blocks-layout bs))
      dT = proj₁ (dst-split (clabs (T₁ ++ blocks-layout bs)) (clabs R)
                   (subst Dst (trans (cong clabs prog≡) (clabs-++ (T₁ ++ blocks-layout bs) R)) d))

      miss : MissBefore T₁ bs
      miss = missBefore-from T₁ bs (dst-nothunks T₁ bs dT)

      placed = blocks-at T₁ bs miss
      labeled = labels-all T₁ bs miss (subst Dst (clabs-++ T₁ (blocks-layout bs)) dT)

      combine : ∀ (cs : List (LabelId × ℕ × AbstractTrace))
              → All (λ blk → ∃[ j ] ((find-thunk (T₁ ++ blocks-layout bs) (proj₁ blk) ≡ just j)
                                     × Span (T₁ ++ blocks-layout bs) j (block-layout blk))) cs
              → All (BodyLabels (T₁ ++ blocks-layout bs)) cs
              → Iface.Core.BlocksAt (fname e) [] {FS} (P ++ fn-image l e ++ R) cs
      combine []        []                  []          = []
      combine (blk ∷ cs) ((j , feq , sp) ∷ r) (lb ∷ lbs) =
        subst (λ z → Iface.Core.BlockAt (fname e) [] {FS} z blk) (sym prog≡)
          ( j
          , ft-go-prefix (T₁ ++ blocks-layout bs) R (e-thunk (proj₁ blk)) 0 j feq
          , (λ k i eq → fetch-++-left (T₁ ++ blocks-layout bs) R (k + j) i (sp k i eq))
          , (λ m k eq → fl-go-prefix (T₁ ++ blocks-layout bs) R m 0 (k + suc j) (lb j feq m k eq)) )
        ∷ combine cs r lbs

      blocks-final : Iface.Core.BlocksAt (fname e) [] {FS} (P ++ fn-image l e ++ R) bs
      blocks-final = combine bs placed labeled


  ------------------------------------------------------------------------
  -- THE WALK over the entries, the prefix growing by each.
  ------------------------------------------------------------------------

  entries : ∀ (P : AbstractTrace) (l : ℕ) (es : List IRFun)
          → Dst (clabs (P ++ fns-image l es))
          → All (λ e → All (_≢ fname e) (fdefs P)) es
          → NamesDistinct es
          → All (EntryAt (P ++ fns-image l es)) es
  entries P l []       _ _          _          = []
  entries P l (e ∷ es) d (fe ∷ fes) (ne ∷ nes) =
    entry-at P l e (fns-image (fn-next l e) es) d fe
    ∷ All-map (λ {e′} ea → subst (λ z → EntryAt z e′) assoc ea)
        (entries (P ++ fn-image l e) (fn-next l e) es (subst Dst (cong clabs (sym assoc)) d) fresh nes)
    where
      assoc : (P ++ fn-image l e) ++ fns-image (fn-next l e) es ≡ P ++ fn-image l e ++ fns-image (fn-next l e) es
      assoc = ++-assoc P (fn-image l e) (fns-image (fn-next l e) es)

      fdefs-++ : ∀ (x y : AbstractTrace) → fdefs (x ++ y) ≡ fdefs x ++ fdefs y
      fdefs-++ []       y = refl
      fdefs-++ (i ∷ is) y = trans (cong (fdef-of i ++_) (fdefs-++ is y)) (sym (++-assoc (fdef-of i) (fdefs is) (fdefs y)))

      fresh : All (λ e′ → All (_≢ fname e′) (fdefs (P ++ fn-image l e))) es
      fresh = go es fes ne
        where
          go : ∀ (xs : List IRFun) → All (λ e′ → All (_≢ fname e′) (fdefs P)) xs
             → All (λ e′ → fname e ≢ fname e′) xs
             → All (λ e′ → All (_≢ fname e′) (fdefs (P ++ fn-image l e))) xs
          go []       []         []         = []
          go (x ∷ xs) (fx ∷ fxs) (nx ∷ nxs) =
            subst (λ z → All (_≢ fname x) z) (sym (trans (fdefs-++ P (fn-image l e)) (cong (fdefs P ++_) (fn-unit-nf e l))))
                  (All-++⁺ fx (nx ∷ []))
            ∷ go xs fxs nxs

  ------------------------------------------------------------------------
  -- THE IMAGE: `main`'s unit behind the start, then the table.
  ------------------------------------------------------------------------

  image-entries : ∀ (tbl : List IRFun) (ir : IR Unit Unit) → NamesDistinct tbl
                → All (EntryAt (program-image o (irProgram tbl ir))) tbl
  image-entries tbl ir nd =
    entries P₀ (suc (IT.ir-next-label o 0 ir)) tbl (image-cl o (irProgram tbl ir)) (none tbl) nd
    where
      P₀ : AbstractTrace
      P₀ = instr-ctrl (c-start (IT.ir-stack-budget o ir)) ∷ link-top (IT.ir-to-unit o ir)

      X = IT.ir-to-trace' o 0 0 ir
      nf₀ : fdefs P₀ ≡ []
      nf₀ = nf (LSc.trace-of o X) _ (proj₁ (CLU.frag-nf o ir 0 0)) (proj₂ (CLU.frag-nf o ir 0 0))

      none : ∀ (xs : List IRFun) → All (λ e → All (_≢ fname e) (fdefs P₀)) xs
      none []       = []
      none (x ∷ xs) = subst (All (_≢ fname x)) (sym nf₀) [] ∷ none xs

  ------------------------------------------------------------------------
  -- plan 0.135 S3: THE CLOSURE-BODY MARKERS ARE UNIQUE (`ThunksUnique`, for a
  -- `Cata`'s call of its inline algebra). A marker's label index is in `clabs`,
  -- so two at different places would repeat it.
  ------------------------------------------------------------------------

  thunks-unique-of : ∀ (t : AbstractTrace) → Dst (clabs t) → Iface.Core.ThunksUnique o [] {FS} t
  thunks-unique-of []       d p       q       lbl b b′ () _
  thunks-unique-of (x ∷ xs) d zero    zero    lbl b b′ e₁ e₂ = refl
  thunks-unique-of (x ∷ xs) (h ∷ d) zero (suc q) lbl b b′ refl e₂ =
    ⊥-elim (clab-fetch {P = idx lbl ≢_} xs q _ (idx lbl) e₂ refl h refl)
  thunks-unique-of (x ∷ xs) (h ∷ d) (suc p) zero lbl b b′ e₁ refl =
    ⊥-elim (clab-fetch {P = idx lbl ≢_} xs p _ (idx lbl) e₁ refl h refl)
  thunks-unique-of (x ∷ xs) d (suc p) (suc q) lbl b b′ e₁ e₂ =
    cong suc (thunks-unique-of xs (dtail (clab-of x) (clabs xs) d) p q lbl b b′ e₁ e₂)
    where
      dtail : ∀ (mo : Maybe ℕ) (r : List ℕ) → Dst (cl-at mo r) → Dst r
      dtail (just k) r (_ ∷ d′) = d′
      dtail nothing  r d′       = d′
