-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Rebuild   (plan 0.135 S3, cata M4 stage B)
--
-- THE REBUILD WALK (`IRToTrace.rebuild-walk val tv tb (kind C) (size C) ⌈ G ⌉F s lb`),
-- by induction on the sub-functor `G`: from `Input1` holding a valid word for
-- the node's sublayer `v : ⟦ ⟦ G ⟧TI (μ-type F) ⟧` and the value stack
-- holding `vs` with `fillI G v vs ≡ just (l , rest)`, the run ends with
-- `Output` holding a VALID word for `l : ⟦ ⟦ G ⟧TI C ⟧` (`WordAt`: its
-- register form, what `FlatPut.put` takes) and the value stack holding
-- `rest`, as a `Walk`:
--
--   K      `mov-to-output`: the node's own word for it (its validity is the
--          node's, carried along)
--   Id     `pop2 val`: the popped result
--   ⊗      the right part first (read at the words after the left part's,
--          D375), rebuilt at `s+4`, its word stashed at `s+2`; the left part
--          (word 0); a fresh flat pair, both parts `put` (`Build.BuildPair`)
--   ⊕      branch on the tag as `visit-walk` does; the payload (word 1)
--          rebuilt at `s+4`, then a fresh flat sum block (`Build.BuildSum`).
--
-- Everything the walk writes is a slot in `[s , s + 4·fsize G)` (or `val`)
-- and a block it allocated, so whatever was live at its start reads the
-- same at its end (`Walk.seg`), every word built is valid at the end, and
-- every slot below `s` or from `u ≥ s + 4·fsize G` on other than `val` is
-- kept (`KR s`; the upper window is the cata's call slots, as in `Visit`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Rebuild (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Layout o tbl using (lsz-eq)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Visit o tbl using (module CataVisitC; su-l; su-r)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Build o tbl using (module CataBuildC; pair-text; Arm; arm-l; arm-r; arm-ty; arm-tag; lkind-gen; lsz-gen)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Layer o
  using (fillI; fill-K; fill-Id; fill-inl; fill-inr; fill-pair; module FillPair)
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.IRObsCorrect.CaseShape o tbl using (module ShapeC)
open import Once.CCC.Codegen.IRToTrace o using (rebuild-walk; lsize; pop2; wrap-sum; fsize; getμ)
open import Once.CCC.Codegen.FlatLayout using (Kind; kind; lkind; lsz; get; get-k; get-i; get-one; put-k; kind-skind; size-ssize)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.LabelScope o using (rebuild-ls; wrap-sum-ls; put-k-ls)
open import Once.CCC.Codegen.LabelSeg using (LabelsIn; li-lab; li-none; ls-weaken)
open import Once.CCC.Codegen.LabelResolve o using (module Resolve)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue; readReg; Output; Input1
        ; SV-Ptr; SV-Tag; sv-as-loc; sucLoc; offsetLoc; store-at-slot; restore-input; load-from-slot; mov-to-input; mov-to-output
        ; instr-alloc-heap; instr-ctrl; c-branch-tag-zero; c-jmp; c-label; writeReg-preserves)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot; nhw-restore-input)
open import Once.CCC.Label using (ℓ; LabelId; module LabelId)
open LabelId using (idx)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; wf-K; wf-Id; wf-Sum; wf-Prod; ⟦_⟧TI; ⌈_⌉F; μ-type)
import Once.IRTy as I
open import Data.Product using (Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Nat using (s≤s; z≤n; _*_; _⊔_)
open import Data.Nat.Properties using (+-cancelˡ-≡; +-monoʳ-<)
open import Relation.Nullary using (¬_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

-- the ends of a `⊗` and a `⊕` rebuild, as the run reaches them
prod-end-r : ∀ (e a c b : ℕ) → e + (a + (4 + (c + (4 + b)))) ≡ (4 + (c + (4 + (a + e)))) + b
prod-end-r = solve 4 (λ e a c b → e :+ (a :+ (con 4 :+ (c :+ (con 4 :+ b))))
                                  := (con 4 :+ (c :+ (con 4 :+ (a :+ e)))) :+ b) refl

sum-end-r : ∀ (wl vl wr vr b : ℕ) → suc (wl + (vl + (4 + (wr + (vr + (3 + b)))))) ≡ (3 + (vr + (wr + (4 + (vl + (wl + 1)))))) + b
sum-end-r = solve 5 (λ wl vl wr vr b → con 1 :+ (wl :+ (vl :+ (con 4 :+ (wr :+ (vr :+ (con 3 :+ b))))))
                                       := (con 3 :+ (vr :+ (wr :+ (con 4 :+ (vl :+ (wl :+ con 1)))))) :+ b) refl

module CataRebuildC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStepsC {FS}
  open CataStackC {FS}
  open CataWalkC {FS}
  open CataBuildC {FS} using (module BuildPair; module BuildSum; arm-val)
  open CataVisitC {FS} using (PtrTo; module PtrTo; sum-ptr; prod-ptr; place→word; restore-bk; bk-id; kp-set; cell-kp; live-off
                             ; get-fetch; ngi; lgi)
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem; offset-zero)
  open ShapeC {FS} using (tag-inl; tag-inr; payload-l; payload-r)
  open Resolve {FS} using (NoLabel; fl-hit; noLabel-outside; found-in-window)
  open FlatStepsAPI {FS} using (flat-tag-branch-yes; flat-tag-branch-not)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)

  ------------------------------------------------------------------------
  -- THE WALK.
  ------------------------------------------------------------------------
  ne+ : ∀ (s : ℕ) {a b : ℕ} → a ≢ b → s + a ≢ s + b
  ne+ s ne e = ne (+-cancelˡ-≡ s _ _ e)

  sx : ∀ (s : ℕ) → suc s ≡ s + 1
  sx s = sym (+-comm s 1)

  below : ∀ {j s : ℕ} (k : ℕ) → j < s → j ≢ s + k
  below {s = s} k j<s e = <-irrefl e (<-≤-trans j<s (m≤m+n s k))

  below-suc : ∀ {j s : ℕ} → j < s → j ≢ suc s
  below-suc {s = s} j<s e = <-irrefl e (≤-trans j<s (n≤1+n s))

  below0 : ∀ {j s : ℕ} → j < s → j ≢ s
  below0 j<s e = <-irrefl e j<s

  -- a level's four own slots `s … s+3` sit below `u`
  su4 : ∀ (s k u : ℕ) → s + 4 * suc k ≤ u → s + 4 ≤ u
  su4 s k u p = ≤-trans (m≤m+n (s + 4) (4 * k)) (subst (_≤ u) (eq s k) p)
    where eq : ∀ (s k : ℕ) → s + 4 * suc k ≡ (s + 4) + 4 * k
          eq = solve 2 (λ s k → s :+ (con 4 :* (con 1 :+ k)) := (s :+ con 4) :+ (con 4 :* k)) refl

  module Rebuild (prog : AbstractTrace) (F : IRFunctor) (C : IRTy) (n val tv tb : ℕ) (sn : HeapLocation) (u : ℕ)
                 (n≤val : n ≤ val) where

    VE : ElemP ⟦ C ⟧
    VE = ValE prog C

    ck = kind C
    cs = size C

    RW : ∀ {G} → WellFormedFI G → ℕ → ℕ → AbstractTrace
    RW {G} wG s lb = rebuild-walk val tv tb ck cs ⌈ G ⌉F s lb

    -- a node's sublayer is read at its flat offsets (`getμ`): one `get` row
    getμ-one : ∀ (G : IRFunctor) k → getμ ⌈ G ⌉F k ≡ get-i (⟦ G ⟧TI (μ-type F)) k ∷ []
    getμ-one G k = trans (cong₂ (λ kd sz → get-k kd sz k) (sym (lkind-gen G (μ-type F))) (sym (lsz-gen G (μ-type F))))
                         (get-one _ k)

    KR : ℕ → ℕ → Set
    KR s j = ((j < s) ⊎ (u ≤ j)) × (j ≢ val)

    kr-up : ∀ s j → KR s j → KR (s + 4) j
    kr-up s j (inj₁ j<s , a) = inj₁ (<-≤-trans j<s (m≤m+n s 4)) , a
    kr-up s j (inj₂ u≤j , a) = inj₂ u≤j , a

    -- a kept slot is none of a level's own four
    nk : ∀ {s j : ℕ} (k : ℕ) → k < 4 → s + 4 ≤ u → (j < s) ⊎ (u ≤ j) → j ≢ s + k
    nk {s} k k<4 s4 (inj₁ j<s) = below k j<s
    nk {s} k k<4 s4 (inj₂ u≤j) refl = <-irrefl refl (<-≤-trans (+-monoʳ-< s k<4) (≤-trans s4 u≤j))

    nk0 : ∀ {s j : ℕ} → s + 4 ≤ u → (j < s) ⊎ (u ≤ j) → j ≢ s
    nk0 {s} s4 w e = nk 0 (s≤s z≤n) s4 w (trans e (sym (+-identityʳ s)))
    nk1 : ∀ {s j : ℕ} → s + 4 ≤ u → (j < s) ⊎ (u ≤ j) → j ≢ suc s
    nk1 {s} s4 w e = nk 1 (s≤s (s≤s z≤n)) s4 w (trans e (sx s))
    nk2 : ∀ {s j : ℕ} → s + 4 ≤ u → (j < s) ⊎ (u ≤ j) → j ≢ s + 2
    nk2 s4 w = nk 2 (s≤s (s≤s (s≤s z≤n))) s4 w
    nk3 : ∀ {s j : ℕ} → s + 4 ≤ u → (j < s) ⊎ (u ≤ j) → j ≢ s + 3
    nk3 s4 w = nk 3 (s≤s (s≤s (s≤s (s≤s z≤n)))) s4 w

    up : ∀ {s k} → k < s → k < s + 4
    up {s} p = <-≤-trans p (m≤m+n s 4)

    InWord : ∀ (A : IRTy) → ⟦ A ⟧ → FlatState → Set
    InWord A v σ = WordAt prog (falloc σ) A v (readReg (regs (floc σ)) Input1) (floc σ)

    -- what a rebuild leaves: the built word in Output, the rest of the value stack
    -- (over the allocator and memory, not the state, so a pc-only step keeps it on the nose)
    record RQs (A : IRTy) (l : ⟦ A ⟧) (rest : List ⟦ C ⟧) (a : AllocState {FS}) (st : LocState FS) : Set where
      field
        out   : WordAt prog a A l (readReg (regs st) Output) st
        stack : StackAt VE a st val sn rest

    RQ : (A : IRTy) → ⟦ A ⟧ → List ⟦ C ⟧ → FlatState → Set
    RQ A l rest τ = RQs A l rest (falloc τ) (floc τ)

    RebuildT : ∀ {G} → WellFormedFI G → Set
    RebuildT {G} wG =
      ∀ (s lb : ℕ) (σ : FlatState) (v : ⟦ ⟦ G ⟧TI (μ-type F) ⟧) (vs : List ⟦ C ⟧) (l : ⟦ ⟦ G ⟧TI C ⟧) (rest : List ⟦ C ⟧)
      → fillI wG (μ-type F) C v vs ≡ just (l , rest)
      → n ≤ s → val < s → s + 4 * fsize ⌈ G ⌉F ≤ u
      → SpanAt prog (fpc σ) (RW wG s lb)
      → LabelsAt prog (fpc σ) (RW wG s lb)
      → halted (floc σ) ≡ false
      → InWord (⟦ G ⟧TI (μ-type F)) v σ
      → StackAt VE (falloc σ) (floc σ) val sn vs
      → Walk prog n (KR s) σ (length (RW wG s lb) + fpc σ) (RQ (⟦ G ⟧TI C) l rest)

    no-label-in : ∀ {lo hi} (m : LabelId) (t : AbstractTrace) {lo′ hi′ : ℕ} (u : AbstractTrace) (j : ℕ)
                → LabelsIn lo hi t → LabelsIn lo′ hi′ u → find-label u m ≡ just j
                → (hi′ ≤ lo) ⊎ (hi ≤ lo′) → Resolve.NoLabel {FS} m t
    no-label-in m t u j lt lu eq (inj₁ h) =
      noLabel-outside m t lt (λ w → <-irrefl refl (<-≤-trans (proj₂ (found-in-window u m j eq lu)) (≤-trans h (proj₁ w))))
    no-label-in m t u j lt lu eq (inj₂ h) =
      noLabel-outside m t lt (λ w → <-irrefl refl (<-≤-trans (proj₂ w) (≤-trans h (proj₁ (found-in-window u m j eq lu)))))

    ----------------------------------------------------------------------
    -- K: the node's own word.  Id: pop a result.
    ----------------------------------------------------------------------
    rebuild-K : ∀ {A} {b : I.IsBaseTypeI A} → RebuildT (wf-K b)
    rebuild-K {A} {b} s lb σ x vs l rest eq n≤s val<s su span la nh wd st =
      subst₂ (λ l′ r′ → Walk prog n (KR s) σ (suc (fpc σ)) (RQ A l′ r′)) (sym (proj₁ fk)) (sym (proj₂ fk))
        (walk-q σ mov-to-output refl nh (span 0 _ refl) tt nhw-mov-to-output refl tt tt refl tt bk-id
          (record { out = subst (λ z → WordAt prog (falloc u1) _ x z (floc u1)) (sym (out-movout (floc σ) (falloc σ))) (word-tr kp1 wd)
                  ; stack = stack-keep val-tr kp1 (exec-abstract-preserves-frame mov-to-output (floc σ) (falloc σ))
                              (sl-keep mov-to-output (floc σ) (falloc σ) _ val nhw-mov-to-output refl) st }))
      where
        fk = fill-K {A = A} {b = b} {X = μ-type F} {C = C} {x = x} {vs = vs} {l = l} {rest = rest} eq
        u1 = St mov-to-output σ
        kp1 : Kp (falloc σ) (floc σ) (falloc u1) (floc u1)
        kp1 = kp-q mov-to-output σ nhw-mov-to-output refl tt tt bk-id

    rebuild-Id : RebuildT wf-Id
    rebuild-Id s lb σ t vs l rest eq n≤s val<s su span la nh wd st =
      walk-post w (record { out = subst (λ z → WordAt prog (falloc τ) C l z (floc τ)) (sym (Popped.out p)) (Popped.elem p)
                          ; stack = Popped.stack p })
      where
        st′ : StackAt VE (falloc σ) (floc σ) val sn (l ∷ rest)
        st′ = subst (StackAt VE (falloc σ) (floc σ) val sn) (fill-Id {X = μ-type F} {C = C} {t = t} {vs = vs} eq) st
        w : Walk prog n (KR s) σ (5 + fpc σ) (Popped VE val sn l rest)
        w = pop-walk (λ j kj → proj₂ kj) (pop2-run VE val-tr prog n val sn σ l rest span nh n≤val st′)
        τ = Walk.τ w
        p = Walk.post w

    ----------------------------------------------------------------------
    -- ⊗: the right part (after the left part's words), stashed at `s+2`;
    -- the left part (word 0); a fresh flat pair.
    ----------------------------------------------------------------------
    module ProdC {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (iha : RebuildT a) (ihb : RebuildT b)
                 (s lb : ℕ) (σ : FlatState) (x : ⟦ ⟦ G ⟧TI (μ-type F) ⟧) (y : ⟦ ⟦ H ⟧TI (μ-type F) ⟧)
                 (vs : List ⟦ C ⟧) (l : ⟦ ⟦ G ⟧TI C ⟧ × ⟦ ⟦ H ⟧TI C ⟧) (rest : List ⟦ C ⟧)
                 (eq : fillI (wf-Prod a b) (μ-type F) C (x , y) vs ≡ just (l , rest))
                 (n≤s : n ≤ s) (val<s : val < s)
                 (su : s + 4 * suc (fsize ⌈ G ⌉F + fsize ⌈ H ⌉F) ≤ u)
                 (span : SpanAt prog (fpc σ) (RW (wf-Prod a b) s lb))
                 (la : LabelsAt prog (fpc σ) (RW (wf-Prod a b) s lb))
                 (nh : halted (floc σ) ≡ false)
                 (wd : InWord (⟦ G ⟧TI (μ-type F) I.* ⟦ H ⟧TI (μ-type F)) (x , y) σ)
                 (st : StackAt VE (falloc σ) (floc σ) val sn vs) where

      fp = fill-pair {a = a} {b} {μ-type F} {C} {x} {y} {vs} {l} {rest} eq
      midl = FillPair.mid fp

      base = fpc σ
      lF = lsize ⌈ G ⌉F
      lH = lsize ⌈ H ⌉F
      Y₁ = ⟦ G ⟧TI (μ-type F)
      Y₂ = ⟦ H ⟧TI (μ-type F)
      Z₁ = ⟦ G ⟧TI C
      Z₂ = ⟦ H ⟧TI C

      pre : AbstractTrace
      pre = mov-to-output ∷ store-at-slot s ∷ get-i Y₂ (size Y₁) ∷ mov-to-input ∷ []
      VB = RW b (s + 4) (lb + lF)
      mid : AbstractTrace
      mid = store-at-slot (s + 2) ∷ restore-input s ∷ get-i Y₁ 0 ∷ mov-to-input ∷ []
      VA = RW a (s + 4) lb
      epi = pair-text (suc s) (s + 2) (s + 3) Z₁ Z₂
      T3 = mid ++ (VA ++ epi)

      -- the text, with its reads as rows and its build at the IR's types
      txt : AbstractTrace → AbstractTrace → ℕ → Kind → ℕ → Kind → ℕ → ℕ → AbstractTrace
      txt gH gG N kG sG kH sH oH =
        (mov-to-output ∷ store-at-slot s ∷ []) ++ gH ++ (mov-to-input ∷ []) ++ VB ++
        (store-at-slot (s + 2) ∷ restore-input s ∷ []) ++ gG ++ (mov-to-input ∷ []) ++ VA ++
        (store-at-slot (suc s) ∷ instr-alloc-heap N ∷ store-at-slot (s + 3) ∷ []) ++
        put-k kG sG (suc s) (s + 3) 0 ++ put-k kH sH (s + 2) (s + 3) oH ++ (load-from-slot (s + 3) ∷ [])

      txt-eq : ∀ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ g₁ g₂ h₁ h₂}
             → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ → f₁ ≡ f₂ → g₁ ≡ g₂ → h₁ ≡ h₂
             → txt a₁ b₁ c₁ d₁ e₁ f₁ g₁ h₁ ≡ txt a₂ b₂ c₂ d₂ e₂ f₂ g₂ h₂
      txt-eq refl refl refl refl refl refl refl refl = refl

      shape : RW (wf-Prod a b) s lb ≡ pre ++ VB ++ T3
      shape = txt-eq (trans (getμ-one H (lsz ⌈ G ⌉F 1)) (cong (λ k → get-i Y₂ k ∷ []) (sym (lsz-gen G (μ-type F)))))
                     (getμ-one G 0)
                     (cong (2 ⊔_) (sym (cong₂ _+_ (lsz-gen G C) (lsz-gen H C))))
                     (sym (lkind-gen G C)) (sym (lsz-gen G C)) (sym (lkind-gen H C)) (sym (lsz-gen H C)) (sym (lsz-gen G C))

      span′ : SpanAt prog base (pre ++ VB ++ T3)
      span′ = subst (SpanAt prog base) shape span
      la′ : LabelsAt prog base (pre ++ VB ++ T3)
      la′ = subst (LabelsAt prog base) shape la

      pt = prod-ptr wd
      hl = PtrTo.hl pt
      lv = PtrTo.live pt
      pv = decomposePairWF (PtrTo.val pt)

      val≢s : val ≢ s
      val≢s = below0 val<s
      s4u : s + 4 ≤ u
      s4u = su4 s (fsize ⌈ G ⌉F + fsize ⌈ H ⌉F) u su
      n≤s4 : n ≤ s + 4
      n≤s4 = ≤-trans n≤s (m≤m+n s 4)
      s<s4 : s < s + 4
      s<s4 = subst (λ z → suc s ≤ z) (+-comm 4 s) (s≤s (m≤n+m s 3))
      s2<s4 : s + 2 < s + 4
      s2<s4 = +-monoʳ-< s (s≤s (s≤s (s≤s z≤n)))

      SP1 = span-drop prog pre {VB ++ T3} base span′
      SPB = span-take prog VB {T3} (4 + base) SP1
      SP2 = span-drop prog VB {T3} (4 + base) SP1
      SP3 = span-drop prog mid {VA ++ epi} (length VB + (4 + base)) SP2
      SPA = span-take prog VA {epi} (4 + (length VB + (4 + base))) SP3
      SP4 = span-drop prog VA {epi} (4 + (length VB + (4 + base))) SP3

      nl-pre : ∀ m → Resolve.NoLabel {FS} m pre
      nl-pre m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ ngi Y₂ (size Y₁) m ∷ᴬ (λ ()) ∷ᴬ []ᴬ
      nl-mid : ∀ m → Resolve.NoLabel {FS} m mid
      nl-mid m = (λ ()) ∷ᴬ (λ ()) ∷ᴬ ngi Y₁ 0 m ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      ls-epi : ∀ {lo hi} → LabelsIn lo hi epi
      ls-epi = li-none refl ∷ᴬ li-none refl ∷ᴬ li-none refl ∷ᴬ
               ++⁺ (put-k-ls (kind Z₁) (size Z₁) (suc s) (s + 3) 0)
                   (++⁺ (put-k-ls (kind Z₂) (size Z₂) (s + 2) (s + 3) (size Z₁)) (li-none refl ∷ᴬ []ᴬ))

      ls-T3 : LabelsIn lb (lb + lF) T3
      ls-T3 = li-none refl ∷ᴬ li-none refl ∷ᴬ lgi Y₁ 0 ∷ᴬ li-none refl ∷ᴬ
              ++⁺ (rebuild-ls ck cs ⌈ G ⌉F val tv tb (s + 4) lb) ls-epi

      LA1 = labels-drop prog pre {VB ++ T3} base la′ (λ m j _ → nl-pre m)
      LAB = labels-take prog VB {T3} (4 + base) LA1
      LA2 = labels-drop prog VB {T3} (4 + base) LA1
              (λ m j e → no-label-in m VB T3 j (rebuild-ls ck cs ⌈ H ⌉F val tv tb (s + 4) (lb + lF)) ls-T3 e (inj₁ ≤-refl))
      LA3 = labels-drop prog mid {VA ++ epi} (length VB + (4 + base)) LA2 (λ m j _ → nl-mid m)
      LAA = labels-take prog VA {epi} (4 + (length VB + (4 + base))) LA3

      -- rows 1-2: the pair stashed at `s`
      p1 = St mov-to-output σ
      p2 = St (store-at-slot s) p1

      f₀ = current-frame (falloc σ)

      out1 : readReg (regs (floc p1)) Output ≡ SV-Ptr (AtDynamic hl)
      out1 = trans (out-movout (floc σ) (falloc σ)) (PtrTo.eq pt)
      in1 : readReg (regs (floc p1)) Input1 ≡ SV-Ptr (AtDynamic hl)
      in1 = trans (writeReg-preserves (regs (floc σ)) Output Input1 (readReg (regs (floc σ)) Input1) (λ ())) (PtrTo.eq pt)
      cf1 : current-frame (falloc p1) ≡ f₀
      cf1 = exec-abstract-preserves-frame mov-to-output (floc σ) (falloc σ)
      nh1 = exec-abstract-preserves-halted-WF mov-to-output (floc σ) (falloc σ) nh tt
      nh2 = exec-abstract-preserves-halted-WF (store-at-slot s) (floc p1) (falloc p1) nh1 tt
      slot2 : readLoc (floc p2) (AtStack f₀ s) ≡ just (SV-Ptr (AtDynamic hl))
      slot2 = trans (sl-same s (floc p1) (falloc p1) f₀ cf1) (cong just out1)
      in2 : readReg (regs (floc p2)) Input1 ≡ SV-Ptr (AtDynamic hl)
      in2 = trans (reg-store s (floc p1) (falloc p1) Input1) in1

      w12 : Walk prog n (KR s) σ (suc (fpc p1)) (λ _ → ⊤)
      w12 = walk-∘ {prog} {n} {KR s} {σ}
              (walk-q {Q = λ _ → ⊤} σ mov-to-output refl nh (span′ 0 _ refl) tt nhw-mov-to-output refl tt tt refl tt bk-id tt)
              (walk-st p1 (store-at-slot s) refl nh1 (span′ 1 _ refl) nh2 refl tt (seg-store s p1 refl n≤s) bk-id
                 (λ j kj → sl-other s j (floc p1) (falloc p1) _ (nk0 s4u (proj₁ kj))) tt)

      kp2 : Kp (falloc σ) (floc σ) (falloc p2) (floc p2)
      kp2 = walk-kp w12

      -- row 3: the right part, at the words after the left part's
      cell₂ : CellAt {prog = prog} (falloc p2) Y₂ y (offsetLoc (AtDynamic hl) (size Y₁)) (floc p2)
      cell₂ = cell-kp kp2 y _ (live-off (size Y₁) lv) (PairValidWF.snd-cell pv)

      g₂ : GetOut {prog = prog} Y₂ y p2
      g₂ = get-run Y₂ (size Y₁) p2 (AtDynamic hl) nh2 (get-fetch {prog} {fpc p2} Y₂ (size Y₁) (span′ 2 _ refl)) in2
             (proj₁ kp2 _ lv) cell₂

      p3 = setOut p2 (GetOut.out g₂)
      p4 = St mov-to-input p3

      nh4 : halted (floc p4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF mov-to-input (floc p3) (falloc p3) nh2 tt
      cf4 : current-frame (falloc p4) ≡ f₀
      cf4 = trans (exec-abstract-preserves-frame mov-to-input (floc p3) (falloc p3)) cf1

      pre-walk : Walk prog n (KR s) σ (fpc p4) (λ _ → ⊤)
      pre-walk = walk-∘ {prog} {n} {KR s} {σ} w12 (walk-∘ {prog} {n} {KR s} {p2} (get-walk {Q = λ _ → ⊤} p2 g₂ nh2 tt)
                   (walk-q p3 mov-to-input refl nh2 (span′ 3 _ refl) tt nhw-mov-to-input refl tt tt refl tt bk-id tt))

      kp4 : Kp (falloc σ) (floc σ) (falloc p4) (floc p4)
      kp4 = walk-kp pre-walk

      keep4 : ∀ j → j ≢ s → readLoc (floc p4) (AtStack f₀ j) ≡ readLoc (floc σ) (AtStack f₀ j)
      keep4 j j≢s =
        trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ j nhw-mov-to-input refl)
        (trans (out-mem p2 (GetOut.out g₂) (AtStack f₀ j))
        (trans (sl-other s j (floc p1) (falloc p1) f₀ j≢s)
               (sl-keep mov-to-output (floc σ) (falloc σ) f₀ j nhw-mov-to-output refl)))

      slot4 : readLoc (floc p4) (AtStack f₀ s) ≡ just (SV-Ptr (AtDynamic hl))
      slot4 = trans (sl-keep mov-to-input (floc p3) (falloc p3) f₀ s nhw-mov-to-input refl)
              (trans (out-mem p2 (GetOut.out g₂) (AtStack f₀ s)) slot2)

      wd4 : InWord Y₂ y p4
      wd4 = subst (λ z → WordAt prog (falloc p4) Y₂ y z (floc p4)) (sym (in-movin (floc p3) (falloc p3)))
              (word-tr (kp-q mov-to-input p3 nhw-mov-to-input refl tt tt bk-id) (place→word (GetOut.place g₂)))

      -- the right part
      wb : Walk prog n (KR (s + 4)) p4 (length VB + fpc p4) (RQ Z₂ (proj₂ l) midl)
      wb = ihb (s + 4) (lb + lF) p4 y vs (proj₂ l) midl (FillPair.right fp) n≤s4 (up val<s) (su-r s (fsize ⌈ G ⌉F) (fsize ⌈ H ⌉F) u su) SPB LAB nh4
             wd4 (stack-keep val-tr kp4 cf4 (keep4 val val≢s) st)

      wpb : Walk prog n (KR s) σ (length VB + fpc p4) (RQ Z₂ (proj₂ l) midl)
      wpb = walk-∘ {prog} {n} {KR s} {σ} pre-walk (walk-K (kr-up s) wb)

      τb = Walk.τ wb
      kpb : Kp (falloc σ) (floc σ) (falloc τb) (floc τb)
      kpb = walk-kp wpb
      wR = readReg (regs (floc τb)) Output
      fb = current-frame (falloc τb)

      slot-b : readLoc (floc τb) (AtStack fb s) ≡ just (SV-Ptr (AtDynamic hl))
      slot-b = trans (cong (λ f → readLoc (floc τb) (AtStack f s)) (Walk.cf wb))
               (trans (Walk.slots wb s (inj₁ s<s4 , λ e → val≢s (sym e))) (trans (cong (λ f → readLoc (floc p4) (AtStack f s)) cf4) slot4))

      -- rows: the right word to `s+2`, the pair back, the left part (word 0) into Input1
      m1 = St (store-at-slot (s + 2)) τb
      m2 = St (restore-input s) m1

      s≢s2 : s ≢ s + 2
      s≢s2 e = ne+ s (λ ()) (trans (+-identityʳ s) e)

      slot-m1 : readLoc (floc m1) (AtStack (current-frame (falloc m1)) s) ≡ just (SV-Ptr (AtDynamic hl))
      slot-m1 = trans (sl-other (s + 2) s (floc τb) (falloc τb) fb s≢s2) slot-b
      s2-m1 : readLoc (floc m1) (AtStack fb (s + 2)) ≡ just wR
      s2-m1 = sl-same (s + 2) (floc τb) (falloc τb) fb refl
      in-m2 : readReg (regs (floc m2)) Input1 ≡ SV-Ptr (AtDynamic hl)
      in-m2 = in-restore s (floc m1) (falloc m1) _ slot-m1
      kpm1 : Kp (falloc τb) (floc τb) (falloc m1) (floc m1)
      kpm1 = seg-kp (seg-store {falloc τb} {0} (s + 2) τb refl z≤n) bk-id
      bk-m2 = restore-bk s (floc m1) (falloc m1) slot-m1
      kpm2 : Kp (falloc τb) (floc τb) (falloc m2) (floc m2)
      kpm2 = kp-∘ kpm1 (kp-q (restore-input s) m1 nhw-restore-input refl tt tt bk-m2)
      nh-m1 = exec-abstract-preserves-halted-WF (store-at-slot (s + 2)) (floc τb) (falloc τb) (Walk.nh wb) tt
      nh-m2 = exec-abstract-preserves-halted-WF (restore-input s) (floc m1) (falloc m1) nh-m1 (_ , slot-m1)

      fm : ∀ (k : ℕ) {i : AbstractInstr} → fetch mid k ≡ just i → fetch prog (k + fpc τb) ≡ just i
      fm k {i} e = subst (λ z → fetch prog (k + z) ≡ just i) (sym (Walk.pc wb)) (SP2 k i (fetch-++-left mid (VA ++ epi) k i e))

      kpbm2 = kp-∘ kpb kpm2

      cell₁ : CellAt {prog = prog} (falloc m2) Y₁ x (offsetLoc (AtDynamic hl) 0) (floc m2)
      cell₁ = subst (λ z → CellAt {prog = prog} (falloc m2) Y₁ x z (floc m2)) (sym (offset-zero (AtDynamic hl)))
                (cell-kp kpbm2 x (AtDynamic hl) lv (PairValidWF.fst-cell pv))

      g₁ : GetOut {prog = prog} Y₁ x m2
      g₁ = get-run Y₁ 0 m2 (AtDynamic hl) nh-m2 (get-fetch {prog} {fpc m2} Y₁ 0 (fm 2 refl)) in-m2 (proj₁ kpbm2 _ lv) cell₁

      m3 = setOut m2 (GetOut.out g₁)
      m4 = St mov-to-input m3

      nh-m4 : halted (floc m4) ≡ false
      nh-m4 = exec-abstract-preserves-halted-WF mov-to-input (floc m3) (falloc m3) nh-m2 tt

      kp-m4 = kp-q mov-to-input m3 nhw-mov-to-input refl tt tt bk-id
      kpm : Kp (falloc τb) (floc τb) (falloc m4) (floc m4)
      kpm = kp-∘ kpm2 (kp-∘ (kp-set m2 (GetOut.out g₁)) kp-m4)
      cfm : current-frame (falloc m4) ≡ fb
      cfm = trans (exec-abstract-preserves-frame mov-to-input (floc m3) (falloc m3))
                  (exec-abstract-preserves-frame (restore-input s) (floc m1) (falloc m1))
      slm : ∀ j → j ≢ s + 2 → readLoc (floc m4) (AtStack fb j) ≡ readLoc (floc τb) (AtStack fb j)
      slm j ne = trans (sl-keep mov-to-input (floc m3) (falloc m3) _ j nhw-mov-to-input refl)
                 (trans (out-mem m2 (GetOut.out g₁) (AtStack fb j))
                 (trans (sl-keep (restore-input s) (floc m1) (falloc m1) _ j nhw-restore-input refl)
                        (sl-other (s + 2) j (floc τb) (falloc τb) fb ne)))
      s2-m4 : readLoc (floc m4) (AtStack fb (s + 2)) ≡ just wR
      s2-m4 = trans (sl-keep mov-to-input (floc m3) (falloc m3) _ (s + 2) nhw-mov-to-input refl)
              (trans (out-mem m2 (GetOut.out g₁) (AtStack fb (s + 2)))
              (trans (sl-keep (restore-input s) (floc m1) (falloc m1) _ (s + 2) nhw-restore-input refl) s2-m1))

      wd-m4 : InWord Y₁ x m4
      wd-m4 = subst (λ z → WordAt prog (falloc m4) Y₁ x z (floc m4)) (sym (in-movin (floc m3) (falloc m3)))
                (word-tr kp-m4 (place→word (GetOut.place g₁)))

      mid-walk : Walk prog n (KR s) τb (fpc m4) (λ _ → ⊤)
      mid-walk =
        walk-∘ {prog} {n} {KR s} {τb}
          (walk-st {Q = λ _ → ⊤} τb (store-at-slot (s + 2)) refl (Walk.nh wb) (fm 0 refl) nh-m1 refl tt
                  (seg-store (s + 2) τb refl (≤-trans n≤s (m≤m+n s 2))) bk-id
                  (λ j kj → sl-other (s + 2) j (floc τb) (falloc τb) _ (nk2 s4u (proj₁ kj))) tt)
        (walk-∘ {prog} {n} {KR s} {m1}
          (walk-q {Q = λ _ → ⊤} m1 (restore-input s) refl nh-m1 (fm 1 refl) (_ , slot-m1) nhw-restore-input refl tt tt refl tt bk-m2 tt)
        (walk-∘ {prog} {n} {KR s} {m2} (get-walk {Q = λ _ → ⊤} m2 g₁ nh-m2 tt)
                (walk-q m3 mov-to-input refl nh-m2 (fm 3 refl) tt nhw-mov-to-input refl tt tt refl tt bk-id tt)))

      SPA′ : SpanAt prog (fpc m4) VA
      SPA′ = subst (λ z → SpanAt prog (suc (suc (suc (suc z)))) VA) (sym (Walk.pc wb)) SPA
      LAA′ : LabelsAt prog (fpc m4) VA
      LAA′ = subst (λ z → LabelsAt prog (suc (suc (suc (suc z)))) VA) (sym (Walk.pc wb)) LAA

      -- the left part
      wa : Walk prog n (KR (s + 4)) m4 (length VA + fpc m4) (RQ Z₁ (proj₁ l) rest)
      wa = iha (s + 4) lb m4 x midl (proj₁ l) rest (FillPair.left fp) n≤s4 (up val<s) (su-l s (fsize ⌈ G ⌉F) (fsize ⌈ H ⌉F) u su) SPA′ LAA′ nh-m4
             wd-m4 (stack-keep val-tr kpm cfm (slm val (below 2 val<s)) (RQs.stack (Walk.post wb)))

      wma : Walk prog n (KR s) τb (length VA + fpc m4) (RQ Z₁ (proj₁ l) rest)
      wma = walk-∘ {prog} {n} {KR s} {τb} mid-walk (walk-K (kr-up s) wa)

      τa = Walk.τ wa

      s2-a : readLoc (floc τa) (AtStack (current-frame (falloc τa)) (s + 2)) ≡ just wR
      s2-a = trans (cong (λ f → readLoc (floc τa) (AtStack f (s + 2))) (Walk.cf wa))
             (trans (Walk.slots wa (s + 2) (inj₁ s2<s4 , λ e → below 2 val<s (sym e)))
                    (trans (cong (λ f → readLoc (floc m4) (AtStack f (s + 2))) cfm) s2-m4))

      SPE : SpanAt prog (fpc τa) epi
      SPE = subst (λ z → SpanAt prog z epi)
              (sym (trans (Walk.pc wa) (cong (λ z → length VA + suc (suc (suc (suc z)))) (Walk.pc wb)))) SP4

      s2≢s1 : s + 2 ≢ suc s
      s2≢s1 e = ne+ s (λ ()) (trans e (sx s))
      s3≢s2 : s + 3 ≢ s + 2
      s3≢s2 = ne+ s (λ ())
      s3≢s1 : s + 3 ≢ suc s
      s3≢s1 e = ne+ s (λ ()) (trans e (sx s))

      -- the fresh pair
      module E = BuildPair {prog} n (suc s) (s + 2) (s + 3) Z₁ Z₂ τa {proj₁ l} {proj₂ l} wR SPE (Walk.nh wa)
                   (≤-trans n≤s (n≤1+n s)) (≤-trans n≤s (m≤m+n s 3)) s2≢s1 s3≢s1 s3≢s2
                   (RQs.out (Walk.post wa)) (word-tr (walk-kp wma) (RQs.out (Walk.post wb))) s2-a

      we : Walk prog n (KR s) τa (length epi + fpc τa)
              (λ τ′ → WordAt prog (falloc τ′) (Z₁ I.* Z₂) (proj₁ l , proj₂ l) (readReg (regs (floc τ′)) Output) (floc τ′))
      we = E.walk (λ j kj → nk1 s4u (proj₁ kj) , nk3 s4u (proj₁ kj))

      all = walk-∘ {prog} {n} {KR s} {σ} wpb (walk-∘ {prog} {n} {KR s} {τb} wma we)

      τe = Walk.τ we

      stack-e : StackAt VE (falloc τe) (floc τe) val sn rest
      stack-e = stack-keep val-tr (walk-kp we) (Walk.cf we)
                  (E.slots val (below-suc val<s) (below 3 val<s)) (RQs.stack (Walk.post wa))

      len-eq : length (RW (wf-Prod a b) s lb) ≡ 4 + (length VB + (4 + (length VA + length epi)))
      len-eq = trans (cong length shape) (cong (4 +_) (trans (length-++ VB {T3}) (cong (λ z → length VB + (4 + z)) (length-++ VA {epi}))))

      end-eq : length epi + fpc τa ≡ length (RW (wf-Prod a b) s lb) + base
      end-eq = trans (cong (length epi +_) (trans (Walk.pc wa) (cong (λ z → length VA + suc (suc (suc (suc z)))) (Walk.pc wb))))
                     (trans (prod-end-r (length epi) (length VA) (length VB) base) (cong (_+ base) (sym len-eq)))

      result : Walk prog n (KR s) σ (length (RW (wf-Prod a b) s lb) + base) (RQ (Z₁ I.* Z₂) l rest)
      result = walk-pc end-eq (walk-post all (record { out = Walk.post we ; stack = stack-e }))

    ----------------------------------------------------------------------
    -- ⊕: branch on the tag, rebuild the payload, wrap it in a fresh flat sum block, join.
    ----------------------------------------------------------------------
    module SumC {G H : IRFunctor} (a : WellFormedFI G) (b : WellFormedFI H) (iha : RebuildT a) (ihb : RebuildT b)
                (s lb : ℕ) (σ : FlatState) (vs : List ⟦ C ⟧) (rest : List ⟦ C ⟧)
                (n≤s : n ≤ s) (val<s : val < s)
                (su : s + 4 * suc (fsize ⌈ G ⌉F + fsize ⌈ H ⌉F) ≤ u)
                (span : SpanAt prog (fpc σ) (RW (wf-Sum a b) s lb))
                (la : LabelsAt prog (fpc σ) (RW (wf-Sum a b) s lb))
                (nh : halted (floc σ) ≡ false)
                (st : StackAt VE (falloc σ) (floc σ) val sn vs) where

      base = fpc σ
      lF = lsize ⌈ G ⌉F
      lH = lsize ⌈ H ⌉F
      ssl = suc (suc lb)
      Y₁ = ⟦ G ⟧TI (μ-type F)
      Y₂ = ⟦ H ⟧TI (μ-type F)
      Z₁ = ⟦ G ⟧TI C
      Z₂ = ⟦ H ⟧TI C

      pre : AbstractTrace
      pre = instr-ctrl (c-branch-tag-zero (ℓ o lb)) ∷ get-i Y₂ 1 ∷ mov-to-input ∷ []
      VR = RW b (s + 4) (ssl + lF)
      WR = wrap-sum 1 (kind Z₂) (size Z₂) (size (Z₁ I.+ Z₂)) s
      mid : AbstractTrace
      mid = instr-ctrl (c-jmp (ℓ o (suc lb))) ∷ instr-ctrl (c-label (ℓ o lb)) ∷ get-i Y₁ 1 ∷ mov-to-input ∷ []
      VL = RW a (s + 4) ssl
      WL = wrap-sum 0 (kind Z₁) (size Z₁) (size (Z₁ I.+ Z₂)) s
      post : AbstractTrace
      post = instr-ctrl (c-label (ℓ o (suc lb))) ∷ []
      R4 = WL ++ post
      R3 = VL ++ R4
      R2 = mid ++ R3
      R1 = WR ++ R2

      -- the text, with its reads as rows and its wraps at the IR's types
      txt : AbstractTrace → AbstractTrace → Kind → ℕ → Kind → ℕ → ℕ → AbstractTrace
      txt gH gG kH sH kG sG ss =
        (instr-ctrl (c-branch-tag-zero (ℓ o lb)) ∷ []) ++ gH ++ (mov-to-input ∷ []) ++ VR ++
        wrap-sum 1 kH sH ss s ++
        (instr-ctrl (c-jmp (ℓ o (suc lb))) ∷ instr-ctrl (c-label (ℓ o lb)) ∷ []) ++ gG ++ (mov-to-input ∷ []) ++ VL ++
        wrap-sum 0 kG sG ss s ++ post

      txt-eq : ∀ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ g₁ g₂}
             → a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ → f₁ ≡ f₂ → g₁ ≡ g₂
             → txt a₁ b₁ c₁ d₁ e₁ f₁ g₁ ≡ txt a₂ b₂ c₂ d₂ e₂ f₂ g₂
      txt-eq refl refl refl refl refl refl refl = refl

      shape : RW (wf-Sum a b) s lb ≡ pre ++ VR ++ R1
      shape = txt-eq (getμ-one H 1) (getμ-one G 1)
                     (sym (lkind-gen H C)) (sym (lsz-gen H C)) (sym (lkind-gen G C)) (sym (lsz-gen G C))
                     (sym (cong suc (cong₂ _⊔_ (lsz-gen G C) (lsz-gen H C))))

      span′ : SpanAt prog base (pre ++ VR ++ R1)
      span′ = subst (SpanAt prog base) shape span
      la′ : LabelsAt prog base (pre ++ VR ++ R1)
      la′ = subst (LabelsAt prog base) shape la

      n≤s4 : n ≤ s + 4
      n≤s4 = ≤-trans n≤s (m≤m+n s 4)

      P₁ = length VR + (3 + base)
      P₂ = length WR + P₁
      P₃ = 4 + P₂
      Y₀ = length VL + P₃
      P₅ = length WL + Y₀

      SP1 = span-drop prog pre {VR ++ R1} base span′
      SPR = span-take prog VR {R1} (3 + base) SP1
      SP2 = span-drop prog VR {R1} (3 + base) SP1
      SPWR = span-take prog WR {R2} P₁ SP2
      SP3 = span-drop prog WR {R2} P₁ SP2
      SP4 = span-drop prog mid {R3} P₂ SP3
      SPL = span-take prog VL {R4} P₃ SP4
      SP5 = span-drop prog VL {R4} P₃ SP4
      SPWL = span-take prog WL {post} Y₀ SP5
      SP6 = span-drop prog WL {post} Y₀ SP5

      slb<hi : suc lb < ssl + lF
      slb<hi = m≤m+n ssl lF
      lb<hi : lb < ssl + lF
      lb<hi = ≤-trans (n≤1+n (suc lb)) (m≤m+n ssl lF)

      ls-VR = rebuild-ls ck cs ⌈ H ⌉F val tv tb (s + 4) (ssl + lF)
      ls-VL = rebuild-ls ck cs ⌈ G ⌉F val tv tb (s + 4) ssl

      ls-post : LabelsIn (suc lb) ssl post
      ls-post = li-lab refl ≤-refl ≤-refl ∷ᴬ []ᴬ

      ls-R4 : LabelsIn (suc lb) ssl R4
      ls-R4 = ++⁺ (wrap-sum-ls (suc lb) ssl 0 (kind Z₁) (size Z₁) (size (Z₁ I.+ Z₂)) s) ls-post

      ls-R3 : LabelsIn (suc lb) (ssl + lF) R3
      ls-R3 = ++⁺ (ls-weaken (n≤1+n (suc lb)) ≤-refl ls-VL) (ls-weaken ≤-refl (m≤m+n ssl lF) ls-R4)

      ls-R2 : LabelsIn lb (ssl + lF) R2
      ls-R2 = li-lab refl (n≤1+n lb) slb<hi ∷ᴬ li-lab refl ≤-refl lb<hi ∷ᴬ lgi Y₁ 1 ∷ᴬ li-none refl ∷ᴬ
              ls-weaken (n≤1+n lb) ≤-refl ls-R3

      ls-R1 : LabelsIn lb (ssl + lF) R1
      ls-R1 = ++⁺ (wrap-sum-ls lb (ssl + lF) 1 (kind Z₂) (size Z₂) (size (Z₁ I.+ Z₂)) s) ls-R2

      nl-pre : ∀ m → Resolve.NoLabel {FS} m pre
      nl-pre m = (λ ()) ∷ᴬ ngi Y₂ 1 m ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      idx-of : Maybe LabelId → ℕ
      idx-of (just l) = idx l
      idx-of nothing  = 0

      nl-mid : ∀ m j → find-label R3 m ≡ just j → Resolve.NoLabel {FS} m mid
      nl-mid m j eq = (λ ()) ∷ᴬ (λ e → <-irrefl refl (subst (λ z → suc z ≤ idx m) (cong idx-of e) (proj₁ (found-in-window R3 m j eq ls-R3))))
                      ∷ᴬ ngi Y₁ 1 m ∷ᴬ (λ ()) ∷ᴬ []ᴬ

      LA1 = labels-drop prog pre {VR ++ R1} base la′ (λ m j _ → nl-pre m)
      LAR = labels-take prog VR {R1} (3 + base) LA1
      LA2 = labels-drop prog VR {R1} (3 + base) LA1 (λ m j e → no-label-in m VR R1 j ls-VR ls-R1 e (inj₁ ≤-refl))
      LA3 = labels-drop prog WR {R2} P₁ LA2
              (λ m j e → no-label-in m WR R2 j (wrap-sum-ls 0 0 1 (kind Z₂) (size Z₂) (size (Z₁ I.+ Z₂)) s) ls-R2 e (inj₂ z≤n))
      LA4 = labels-drop prog mid {R3} P₂ LA3 nl-mid
      LAL = labels-take prog VL {R4} P₃ LA4
      LA5 = labels-drop prog VL {R4} P₃ LA4 (λ m j e → no-label-in m VL R4 j ls-VL ls-R4 e (inj₁ ≤-refl))
      LA6 = labels-drop prog WL {post} Y₀ LA5
              (λ m j e → no-label-in m WL post j (wrap-sum-ls 0 0 0 (kind Z₁) (size Z₁) (size (Z₁ I.+ Z₂)) s) ls-post e (inj₂ z≤n))

      J₁ = 1 + P₂
      J  = 0 + P₅

      inl-tgt : find-label prog (ℓ o lb) ≡ just J₁
      inl-tgt = LA3 (ℓ o lb) 1 (fl-hit (ℓ o lb) _ 1)

      join-tgt : find-label prog (ℓ o (suc lb)) ≡ just J
      join-tgt = LA6 (ℓ o (suc lb)) 0 (fl-hit (ℓ o (suc lb)) [] 0)

      len-eq : length (RW (wf-Sum a b) s lb) ≡ 3 + (length VR + (length WR + (4 + (length VL + (length WL + 1)))))
      len-eq = trans (cong length shape)
                 (cong (3 +_) (trans (length-++ VR {R1}) (cong (length VR +_) (trans (length-++ WR {R2})
                   (cong (λ z → length WR + (4 + z)) (trans (length-++ VL {R4}) (cong (length VL +_) (length-++ WL {post}))))))))

      end-eq : suc P₅ ≡ length (RW (wf-Sum a b) s lb) + base
      end-eq = trans (sum-end-r (length WL) (length VL) (length WR) (length VR) base) (cong (_+ base) (sym len-eq))

      s4u : s + 4 ≤ u
      s4u = su4 s (fsize ⌈ G ⌉F + fsize ⌈ H ⌉F) u su

      ks : ∀ j → KR s j → (j ≢ s) × (j ≢ suc s)
      ks j kj = nk0 s4u (proj₁ kj) , nk1 s4u (proj₁ kj)

      -- the payload's two rows (its read at word 1, then into Input1)
      module Unpack {A : IRTy} (v : ⟦ A ⟧) (q0 : FlatState) (hl : HeapLocation)
                    (nh0 : halted (floc q0) ≡ false)
                    (in0 : readReg (regs (floc q0)) Input1 ≡ SV-Ptr (AtDynamic hl))
                    (lv0 : Live (falloc q0) (AtDynamic hl))
                    (cell : CellAt {prog = prog} (falloc q0) A v (offsetLoc (AtDynamic hl) 1) (floc q0))
                    (st0 : StackAt VE (falloc q0) (floc q0) val sn vs)
                    (f1 : fetch prog (fpc q0) ≡ just (get-i A 1))
                    (f2 : fetch prog (suc (fpc q0)) ≡ just mov-to-input) where
        g : GetOut {prog = prog} A v q0
        g = get-run A 1 q0 (AtDynamic hl) nh0 (get-fetch {prog} {fpc q0} A 1 f1) in0 lv0 cell
        q1 = setOut q0 (GetOut.out g)
        q2 = St mov-to-input q1
        nh2 : halted (floc q2) ≡ false
        nh2 = exec-abstract-preserves-halted-WF mov-to-input (floc q1) (falloc q1) nh0 tt
        kp-q2 = kp-q mov-to-input q1 nhw-mov-to-input refl tt tt bk-id
        kp2 : Kp (falloc q0) (floc q0) (falloc q2) (floc q2)
        kp2 = kp-∘ (kp-set q0 (GetOut.out g)) kp-q2
        cf2 : current-frame (falloc q2) ≡ current-frame (falloc q0)
        cf2 = exec-abstract-preserves-frame mov-to-input (floc q1) (falloc q1)
        wd2 : InWord A v q2
        wd2 = subst (λ z → WordAt prog (falloc q2) A v z (floc q2)) (sym (in-movin (floc q1) (falloc q1)))
                (word-tr kp-q2 (place→word (GetOut.place g)))
        st2 : StackAt VE (falloc q2) (floc q2) val sn vs
        st2 = stack-keep val-tr kp2 cf2
                (trans (sl-keep mov-to-input (floc q1) (falloc q1) _ val nhw-mov-to-input refl)
                       (out-mem q0 (GetOut.out g) (AtStack _ val))) st0
        walk : Walk prog n (KR s) q0 (fpc q2) (λ _ → ⊤)
        walk = walk-∘ {prog} {n} {KR s} {q0} (get-walk {Q = λ _ → ⊤} q0 g nh0 tt)
                      (walk-q q1 mov-to-input refl nh0 f2 tt nhw-mov-to-input refl tt tt refl tt bk-id tt)

      -- the payload rebuilt (a walk to `τp`), then wrapped
      module Wrap (r : Arm) (lp : ⟦ arm-ty r Z₁ Z₂ ⟧) (τp : FlatState)
                  (nhp : halted (floc τp) ≡ false)
                  (spw : SpanAt prog (fpc τp) (wrap-sum (arm-tag r) (kind (arm-ty r Z₁ Z₂)) (size (arm-ty r Z₁ Z₂)) (size (Z₁ I.+ Z₂)) s))
                  (rq : RQ (arm-ty r Z₁ Z₂) lp rest τp) where
        module W = BuildSum {prog} n r Z₁ Z₂ s τp spw nhp n≤s (RQs.out rq)
        ww : Walk prog n (KR s) τp (length W.T + fpc τp)
                  (λ τ′ → WordAt prog (falloc τ′) (Z₁ I.+ Z₂) (arm-val r lp) (readReg (regs (floc τ′)) Output) (floc τ′))
        ww = W.walk ks
        τw = Walk.τ ww
        post-w : RQ (Z₁ I.+ Z₂) (arm-val r lp) rest τw
        post-w = record
          { out = Walk.post ww
          ; stack = stack-keep val-tr (walk-kp ww) (Walk.cf ww) (W.slots val (below0 val<s) (below-suc val<s)) (RQs.stack rq) }
        walk : Walk prog n (KR s) τp (length W.T + fpc τp) (RQ (Z₁ I.+ Z₂) (arm-val r lp) rest)
        walk = walk-post ww post-w

      -- `inr`
      module Inr (y : ⟦ Y₂ ⟧) (l₂ : ⟦ Z₂ ⟧)
                 (fy : fillI b (μ-type F) C y vs ≡ just (l₂ , rest))
                 (wd : InWord (Y₁ I.+ Y₂) (inj₂ y) σ) where
        pt = sum-ptr wd

        cond : tag-test (flat-read-tag (floc σ)) ≡ just false
        cond = tag-inr (PtrTo.val pt) (PtrTo.eq pt)

        q0 = record σ { fpc = suc base }
        w0 : Walk prog n (KR s) σ (suc base) (λ _ → ⊤)
        w0 = walk-ctrl σ (instr-ctrl (c-branch-tag-zero (ℓ o lb))) (suc base) nh (span′ 0 _ refl)
               (flat-tag-branch-not prog σ (ℓ o lb) cond) refl tt tt

        module U = Unpack y q0 (PtrTo.hl pt) nh (PtrTo.eq pt) (PtrTo.live pt) (payload-r (PtrTo.val pt)) st (span′ 1 _ refl) (span′ 2 _ refl)

        wR : Walk prog n (KR (s + 4)) U.q2 (length VR + fpc U.q2) (RQ Z₂ l₂ rest)
        wR = ihb (s + 4) (ssl + lF) U.q2 y vs l₂ rest fy n≤s4 (up val<s) (su-r s (fsize ⌈ G ⌉F) (fsize ⌈ H ⌉F) u su) SPR LAR U.nh2 U.wd2 U.st2

        τR = Walk.τ wR

        module Wp = Wrap arm-r l₂ τR (Walk.nh wR) (subst (λ z → SpanAt prog z WR) (sym (Walk.pc wR)) SPWR) (Walk.post wR)

        τW = Walk.τ Wp.walk

        pcW : fpc τW ≡ P₂
        pcW = trans (Walk.pc Wp.walk) (cong (length WR +_) (Walk.pc wR))

        wj : Walk prog n (KR s) τW J (RQ (Z₁ I.+ Z₂) (inj₂ l₂) rest)
        wj = walk-ctrl τW (instr-ctrl (c-jmp (ℓ o (suc lb)))) J (Walk.nh Wp.walk)
               (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-jmp (ℓ o (suc lb))))) (sym pcW) (SP3 0 _ refl))
               (cong (λ mj → do-jump mj τW) join-tgt) refl tt (Walk.post Wp.walk)

        wl : Walk prog n (KR s) (record τW { fpc = J }) (suc J) (RQ (Z₁ I.+ Z₂) (inj₂ l₂) rest)
        wl = walk-ctrl (record τW { fpc = J }) (instr-ctrl (c-label (ℓ o (suc lb)))) (suc J) (Walk.nh Wp.walk)
               (SP6 0 _ refl) refl refl tt (Walk.post Wp.walk)

        result : Walk prog n (KR s) σ (length (RW (wf-Sum a b) s lb) + base) (RQ (Z₁ I.+ Z₂) (inj₂ l₂) rest)
        result = walk-pc end-eq
          (walk-∘ {prog} {n} {KR s} {σ} w0 (walk-∘ {prog} {n} {KR s} {q0} U.walk
            (walk-∘ {prog} {n} {KR s} {U.q2} (walk-K (kr-up s) wR) (walk-∘ {prog} {n} {KR s} {τR} Wp.walk
              (walk-∘ {prog} {n} {KR s} {τW} wj wl)))))

      -- `inl`
      module Inl (x : ⟦ Y₁ ⟧) (l₁ : ⟦ Z₁ ⟧)
                 (fx : fillI a (μ-type F) C x vs ≡ just (l₁ , rest))
                 (wd : InWord (Y₁ I.+ Y₂) (inj₁ x) σ) where
        pt = sum-ptr wd

        cond : tag-test (flat-read-tag (floc σ)) ≡ just true
        cond = tag-inl (PtrTo.val pt) (PtrTo.eq pt)

        i1 = record σ { fpc = J₁ }
        w0 : Walk prog n (KR s) σ J₁ (λ _ → ⊤)
        w0 = walk-ctrl σ (instr-ctrl (c-branch-tag-zero (ℓ o lb))) J₁ nh (span′ 0 _ refl)
               (trans (flat-tag-branch-yes prog σ (ℓ o lb) cond) (cong (λ mj → do-jump mj σ) inl-tgt)) refl tt tt

        i2 = record i1 { fpc = suc J₁ }
        w1 : Walk prog n (KR s) i1 (suc J₁) (λ _ → ⊤)
        w1 = walk-ctrl i1 (instr-ctrl (c-label (ℓ o lb))) (suc J₁) nh (SP3 1 _ refl) refl refl tt tt

        module U = Unpack x i2 (PtrTo.hl pt) nh (PtrTo.eq pt) (PtrTo.live pt) (payload-l (PtrTo.val pt)) st (SP3 2 _ refl) (SP3 3 _ refl)

        wL : Walk prog n (KR (s + 4)) U.q2 (length VL + fpc U.q2) (RQ Z₁ l₁ rest)
        wL = iha (s + 4) ssl U.q2 x vs l₁ rest fx n≤s4 (up val<s) (su-l s (fsize ⌈ G ⌉F) (fsize ⌈ H ⌉F) u su) SPL LAL U.nh2 U.wd2 U.st2

        τL = Walk.τ wL

        module Wp = Wrap arm-l l₁ τL (Walk.nh wL) (subst (λ z → SpanAt prog z WL) (sym (Walk.pc wL)) SPWL) (Walk.post wL)

        τW = Walk.τ Wp.walk

        pcW : fpc τW ≡ P₅
        pcW = trans (Walk.pc Wp.walk) (cong (length WL +_) (Walk.pc wL))

        wl : Walk prog n (KR s) τW (suc (fpc τW)) (RQ (Z₁ I.+ Z₂) (inj₁ l₁) rest)
        wl = walk-ctrl τW (instr-ctrl (c-label (ℓ o (suc lb)))) (suc (fpc τW)) (Walk.nh Wp.walk)
               (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-label (ℓ o (suc lb))))) (sym pcW) (SP6 0 _ refl))
               refl refl tt (Walk.post Wp.walk)

        result : Walk prog n (KR s) σ (length (RW (wf-Sum a b) s lb) + base) (RQ (Z₁ I.+ Z₂) (inj₁ l₁) rest)
        result = walk-pc (trans (cong suc pcW) end-eq)
          (walk-∘ {prog} {n} {KR s} {σ} w0 (walk-∘ {prog} {n} {KR s} {i1} w1 (walk-∘ {prog} {n} {KR s} {i2} U.walk
            (walk-∘ {prog} {n} {KR s} {U.q2} (walk-K (kr-up s) wL) (walk-∘ {prog} {n} {KR s} {τL} Wp.walk wl)))))

    ----------------------------------------------------------------------
    -- THE WALK, by induction on the functor.
    ----------------------------------------------------------------------
    rebuild : ∀ {G} (wG : WellFormedFI G) → RebuildT wG
    rebuild (wf-K b) = rebuild-K {b = b}
    rebuild wf-Id = rebuild-Id
    rebuild (wf-Prod a b) s lb σ (x , y) vs l rest eq n≤s val<s su span la nh wd st =
      ProdC.result a b (rebuild a) (rebuild b) s lb σ x y vs l rest eq n≤s val<s su span la nh wd st
    rebuild (wf-Sum a b) s lb σ (inj₁ x) vs l rest eq n≤s val<s su span la nh wd st =
      subst (λ z → Walk prog n (KR s) σ (length (RW (wf-Sum a b) s lb) + fpc σ) (RQ _ z rest)) (sym (proj₁ (proj₂ fi)))
        (SumC.Inl.result a b (rebuild a) (rebuild b) s lb σ vs rest n≤s val<s su span la nh st x (proj₁ fi) (proj₂ (proj₂ fi)) wd)
      where fi = fill-inl {a = a} {b} {μ-type F} {C} {x} {vs} {l} {rest} eq
    rebuild (wf-Sum a b) s lb σ (inj₂ y) vs l rest eq n≤s val<s su span la nh wd st =
      subst (λ z → Walk prog n (KR s) σ (length (RW (wf-Sum a b) s lb) + fpc σ) (RQ _ z rest)) (sym (proj₁ (proj₂ fi)))
        (SumC.Inr.result a b (rebuild a) (rebuild b) s lb σ vs rest n≤s val<s su span la nh st y (proj₁ fi) (proj₂ (proj₂ fi)) wd)
      where fi = fill-inr {a = a} {b} {μ-type F} {C} {y} {vs} {l} {rest} eq
