-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.StepLocal — plan 0.146 B1.4b (D417, step 3): the LOCAL step
-- theorem — an image step that stays in its root's code, against the flat
-- code at its point.
--
-- A root (the start code, a block) is lowered once at its frame
-- `φ = frameOf root`; its code lies in the program (`R`). At a path `s` into
-- it, `Here s m fs`: the flat pc is the point's address, the run has not
-- stopped, and the configuration `m` is in the frame (`CfgW`). Each step
-- whose next code is the path's successor moves `Here` along, by its
-- `LowerSim*` lemma, in the steps that lemma counts, keeping what `Keep`
-- says and the heap counter where the image's is.
--
-- The frame fits each step needs come from the frame itself: every code
-- inside the root reaches no further than the root (`sub-peak`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.Nat.Properties using (+-comm; +-assoc; ≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; m≤n+m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.StepLocal
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.ImagePt fmt ans bw using (Sub; whole; next; left; right; eleft; eright; body)
open import Once.LinCore.LowAt fmt ans bw using (Inside; in-trans; in-r; module At)
open import Once.LinCore.PointAt fmt ans bw using (module Fetch)
import Once.LinCore.Moves

------------------------------------------------------------------------
-- 1. ★ A CODE INSIDE A ROOT REACHES NO FURTHER THAN THE ROOT.
------------------------------------------------------------------------

infix 4 _≤²_
_≤²_ : ℕ × ℕ → ℕ × ℕ → Set
x ≤² y = proj₁ x ≤ proj₁ y × proj₂ x ≤ proj₂ y

≤²-refl : ∀ {x} → x ≤² x
≤²-refl = ≤-refl , ≤-refl

≤²-trans : ∀ {x y z} → x ≤² y → y ≤² z → x ≤² z
≤²-trans (a , b) (c , d) = ≤-trans a c , ≤-trans b d

-- the three parts of `a ⊔² (b ⊔² c)`
private
  hd : ∀ a b c → a ≤ a ⊔ (b ⊔ c)
  hd a b c = m≤m⊔n a (b ⊔ c)

  md : ∀ a b c → b ≤ a ⊔ (b ⊔ c)
  md a b c = ≤-trans (m≤m⊔n b c) (m≤n⊔m a (b ⊔ c))

  tl′ : ∀ a b c → c ≤ a ⊔ (b ⊔ c)
  tl′ a b c = ≤-trans (m≤n⊔m b c) (m≤n⊔m a (b ⊔ c))

hd² : ∀ x y z → x ≤² x ⊔² y ⊔² z
hd² x y z = hd (proj₁ x) (proj₁ y) (proj₁ z) , hd (proj₂ x) (proj₂ y) (proj₂ z)

md² : ∀ x y z → y ≤² x ⊔² y ⊔² z
md² x y z = md (proj₁ x) (proj₁ y) (proj₁ z) , md (proj₂ x) (proj₂ y) (proj₂ z)

tl² : ∀ x y z → z ≤² x ⊔² y ⊔² z
tl² x y z = tl′ (proj₁ x) (proj₁ y) (proj₁ z) , tl′ (proj₂ x) (proj₂ y) (proj₂ z)

-- a code's shape is within its peak
at-peak : ∀ {sh T} (c : Codeᴵ sh T) → (envW sh , opW sh) ≤² peakC c
at-peak end           = ≤²-refl
at-peak (i ⨾ c)       = hd² _ (peakI i) (peakC c)
at-peak (case c₁ c₂)  = hd² _ (peakC c₁) (peakC c₂)
at-peak (ecase c₁ c₂) = hd² _ (peakC c₁) (peakC c₂)
at-peak halted        = ≤²-refl

-- ★ every path's code within the root's peak
sub-peak : ∀ {sh U sh′ U′} {root : Codeᴵ sh U} {c : Codeᴵ sh′ U′} → Sub root c → peakC c ≤² peakC root
sub-peak whole = ≤²-refl
sub-peak (next {s = s} {i = i} {k} p) = ≤²-trans (tl² (at s) (peakI i) (peakC k)) (sub-peak p)
sub-peak (left {Es} {A} {B} {S} {c₁ = c₁} {c₂} p) =
  ≤²-trans (md² (at (Es ∣ (A ⊕t B) ∷ S)) (peakC c₁) (peakC c₂)) (sub-peak p)
sub-peak (right {Es} {A} {B} {S} {c₁ = c₁} {c₂} p) =
  ≤²-trans (tl² (at (Es ∣ (A ⊕t B) ∷ S)) (peakC c₁) (peakC c₂)) (sub-peak p)
sub-peak (eleft {E₁} {E₂} {Es} {S} {c₁ = c₁} {c₂} p) =
  ≤²-trans (md² (at ((E₁ ⊕t E₂) ∷ Es ∣ S)) (peakC c₁) (peakC c₂)) (sub-peak p)
sub-peak (eright {E₁} {E₂} {Es} {S} {c₁ = c₁} {c₂} p) =
  ≤²-trans (tl² (at ((E₁ ⊕t E₂) ∷ Es ∣ S)) (peakC c₁) (peakC c₂)) (sub-peak p)
sub-peak (body {E} {Es} {A} {B} {S} {b = b} {k} p) =
  ≤²-trans (md² (at (E ∷ Es ∣ A ∷ S)) (peakC b) (peakC k)) (sub-peak p)

------------------------------------------------------------------------
-- 2. ★ HERE: at a path of a root, in its frame.
------------------------------------------------------------------------

module Loc {FS : FrameSemantics} (U : Univ)
           (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
           (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS)
           (prog : AbstractTrace)
           {sh₀ U₀} (root : Codeᴵ sh₀ U₀) (j : ℕ)
           (L₀ : At.Low U ncty ldConst (frameOf root) j root)
           (R : Inside prog (At.code U ncty ldConst (frameOf root) j L₀)) where

  φ : Frame
  φ = frameOf root

  open At U ncty ldConst φ j
  open Lowering U ncty ldConst
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open CfgW
  open Fetch {FS} using (in-seg)
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ; slot; Keep; k-halt; Ran; r-keep; r-pc; r-next; ran-refl; ranS; MovedS)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open LocState using (heapMem)
  open FlatStepsAPI {FS} using (FlatSteps; [])

  -- the code at a path, inside the program, at its prefix's length
  lowAt : ∀ {sh U′} {c : Codeᴵ sh U′} → Sub root c → Low c
  lowAt s = L (sub-low L₀ s)

  here-in : ∀ {sh U′} {c : Codeᴵ sh U′} (s : Sub root c) → Inside prog (code (lowAt s))
  here-in s = in-trans R (ins (sub-low L₀ s))

  pos : ∀ {sh U′} {c : Codeᴵ sh U′} → Sub root c → ℕ
  pos s = length (proj₁ (here-in s))

  -- ★ at a path, in the frame
  record Here {sh U′} {c : Codeᴵ sh U′} (s : Sub root c) (m : Cfg sh) (fs : FlatState) : Set where
    field
      h-pc  : fpc fs ≡ pos s
      h-run : LocState.halted (floc fs) ≡ false
      h-cfg : CfgW (heapMem (floc fs)) (slot fs) φ m
  open Here

  seg-at : ∀ {sh U′} {c : Codeᴵ sh U′} (s : Sub root c) {m fs} → Here s m fs → Seg prog (fpc fs) (code (lowAt s))
  seg-at s H = subst (λ z → Seg prog z _) (sym (h-pc H)) (in-seg (here-in s))

  -- the frame holds every shape the root reaches
  fits : ∀ {sh U′} {c : Codeᴵ sh U′} → Sub root c → peakC c ≤² (EP φ , OP φ)
  fits s = sub-peak s

  shape-fits : ∀ {sh U′} {c : Codeᴵ sh U′} → Sub root c → envW sh ≤ EP φ × opW sh ≤ OP φ
  shape-fits {c = c} s = ≤²-trans (at-peak c) (fits s)

  ins-fits : ∀ {sa sb V} {i : Insᴵ sa sb} {k : Codeᴵ sb V} → Sub root (i ⨾ k) → peakI i ≤² (EP φ , OP φ)
  ins-fits {sa} {i = i} {k} s = ≤²-trans (md² (at sa) (peakI i) (peakC k)) (fits s)

  -- a configuration of the next code's shape, in the frame
  cfgK : ∀ {sa sb V} {i : Insᴵ sa sb} {k : Codeᴵ sb V} → Sub root (i ⨾ k)
       → ∀ {rd sm} {m : Cfg sb} → EnvW rd sm (Cfg.envs m) → StkW rd sm φ (Cfg.opds m) → CfgW rd sm φ m
  cfgK s ev st = record { c-env = ev ; c-stk = st ; c-efit = proj₁ (shape-fits (next s)) ; c-sfit = proj₂ (shape-fits (next s)) }

  ----------------------------------------------------------------------
  -- 3. ★ A STRAIGHT STEP: the instruction's code, then the next path.
  ----------------------------------------------------------------------

  -- the instruction's code at a path
  insC : ∀ {sa sb V} {i : Insᴵ sa sb} {k : Codeᴵ sb V} → Sub root (i ⨾ k) → AbstractTrace
  insC {i = i} s = proj₁ (lowI φ j (lm (lowAt s)) i (proj₁ (lcin (lowAt s))))

  pos-next : ∀ {sa sb V} {i : Insᴵ sa sb} {k : Codeᴵ sb V} (s : Sub root (i ⨾ k)) → pos (next s) ≡ pos s + length (insC s)
  pos-next s =
    let pR = proj₁ R ; pS = proj₁ (ins (sub-low L₀ s)) in
    trans (length-++ pR) (trans (cong (length pR +_) (length-++ pS))
      (sym (trans (cong (_+ length (insC s)) (length-++ pR)) (+-assoc (length pR) (length pS) (length (insC s))))))

  -- what a step's lemma gives: its steps, the next configuration, a straight run
  Gives : ∀ {s′} → (fs : FlatState) → ℕ → ℕ → Cfg s′ → Set
  Gives fs N a m′ = Σ FlatState λ fs′ → FlatSteps prog N fs fs′ × CfgW (heapMem (floc fs′)) (slot fs′) φ m′ × Ran N a fs fs′

  -- what the local theorem gives
  Moved : ∀ {s′ V} {k : Codeᴵ s′ V} → Sub root k → FlatState → ℕ → Cfg s′ → Set
  Moved s′ fs a m′ = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps prog N fs fs′ × Here s′ m′ fs′ × Keep fs fs′
                     × AllocState.next-heap-ref (falloc fs′) ≡ a + AllocState.next-heap-ref (falloc fs)

  straight : ∀ {sa sb V} {i : Insᴵ sa sb} {k : Codeᴵ sb V} (s : Sub root (i ⨾ k)) {m : Cfg sa} {m′ : Cfg sb} {fs} (H : Here s m fs)
           → (N a : ℕ) → N ≡ length (insC s)
           → (Seg prog (fpc fs) (insC s) → LocState.halted (floc fs) ≡ false → CfgW (heapMem (floc fs)) (slot fs) φ m → Gives fs N a m′)
           → Moved (next s) fs a m′
  straight s {fs = fs} H N a eN sim = finish (sim (Seg-++ˡ prog (fpc fs) (insC s) _ (seg-at s H)) (h-run H) (h-cfg H))
    where
      finish : Gives fs N a _ → Moved (next s) fs a _
      finish (fs′ , st , C′ , Rn) =
        N , fs′ , st ,
        record { h-pc  = trans (r-pc Rn) (trans (cong (N +_) (h-pc H)) (trans (+-comm N (pos s))
                           (trans (cong (pos s +_) eN) (sym (pos-next s)))))
               ; h-run = trans (k-halt (r-keep Rn)) (h-run H)
               ; h-cfg = C′ }
        , r-keep Rn , r-next Rn

  -- an instruction with no code: the same state, the next configuration
  empty : ∀ {sa sb V} {i : Insᴵ sa sb} {k : Codeᴵ sb V} (s : Sub root (i ⨾ k)) {m : Cfg sa} {m′ : Cfg sb} {fs} (H : Here s m fs)
        → insC s ≡ []
        → (CfgW (heapMem (floc fs)) (slot fs) φ m → CfgW (heapMem (floc fs)) (slot fs) φ m′)
        → Moved (next s) fs 0 m′
  empty s {fs = fs} H e f = straight s H 0 0 (sym (cong length e)) (λ _ _ C → fs , [] , f C , ran-refl)

  ----------------------------------------------------------------------
  -- 4. ★ THE STEPS WITH NO CODE.
  ----------------------------------------------------------------------

  private
    toB : ∀ {x} → x ≤ OP φ → x ≤ budget φ
    toB le = ≤-trans le (m≤n+m (OP φ) (EP φ))

  st-unpair : ∀ {Es A B S V} {k : Codeᴵ (Es ∣ A ∷ B ∷ S) V} (s : Sub root (unpair ⨾ k))
                {es : Slots Es} {a : MV A} {b : MV B} {os : Stk S} {fs}
            → Here s (es ∥ mpair a b ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ a ∷ˢ b ∷ˢ os)
  st-unpair s H = empty s H refl (λ C → cfgK s (c-env C) (unpair-W (toB (proj₂ (shape-fits (next s)))) (c-stk C)))

  st-pair : ∀ {Es A B S V} {k : Codeᴵ (Es ∣ (A ⊗t B) ∷ S) V} (s : Sub root (pair ⨾ k))
              {es : Slots Es} {a : MV A} {b : MV B} {os : Stk S} {fs}
          → Here s (es ∥ a ∷ˢ b ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mpair a b ∷ˢ os)
  st-pair s H = empty s H refl (λ C → cfgK s (c-env C) (pair-W (toB (c-sfit C)) (c-stk C)))

  st-unit : ∀ {Es S V} {k : Codeᴵ (Es ∣ One ∷ S) V} (s : Sub root (unit ⨾ k)) {es : Slots Es} {os : Stk S} {fs}
          → Here s (es ∥ os) fs → Moved (next s) fs 0 (es ∥ mone ∷ˢ os)
  st-unit s H = empty s H refl (λ C → cfgK s (c-env C) (unit-W (c-stk C)))

  st-untag : ∀ {Es l X A S V} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) V} (s : Sub root (untag {l = l} ⨾ k))
               {es : Slots Es} {x : MV X} {a : MV A} {os : Stk S} {fs}
           → Here s (es ∥ mpair (mct x) a ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mpair x a ∷ˢ os)
  st-untag s H = empty s H refl (λ C → cfgK s (c-env C) (untag-W (c-stk C)))

  st-untag₁ : ∀ {Es l X S V} {k : Codeᴵ (Es ∣ X ∷ S) V} (s : Sub root (untag₁ {l = l} ⨾ k))
                {es : Slots Es} {x : MV X} {os : Stk S} {fs}
            → Here s (es ∥ mct x ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ x ∷ˢ os)
  st-untag₁ s H = empty s H refl (λ C → cfgK s (c-env C) (untag₁-W (c-stk C)))

  st-tag₁ : ∀ {Es l X S V} {k : Codeᴵ (Es ∣ Ct l X ∷ S) V} (s : Sub root (tag₁ ⨾ k))
              {es : Slots Es} {x : MV X} {os : Stk S} {fs}
          → Here s (es ∥ x ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mct x ∷ˢ os)
  st-tag₁ s H = empty s H refl (λ C → cfgK s (c-env C) (tag₁-W (c-stk C)))

  st-elift : ∀ {Es S V} {k : Codeᴵ (One ∷ Es ∣ S) V} (s : Sub root (elift ⨾ k)) {es : Slots Es} {os : Stk S} {fs}
           → Here s (es ∥ os) fs → Moved (next s) fs 0 (vw mone es ∥ os)
  st-elift s H = empty s H refl (λ C → cfgK s (elift-W (c-env C)) (c-stk C))

  st-epop : ∀ {E Es S V} {k : Codeᴵ (Es ∣ S) V} (s : Sub root (epop ⨾ k)) {e : MV E} {es : Slots Es} {os : Stk S} {fs}
          → Here s (vw e es ∥ os) fs → Moved (next s) fs 0 (es ∥ os)
  st-epop s H = empty s H refl (λ C → cfgK s (epop-W (c-env C)) (c-stk C))

  ----------------------------------------------------------------------
  -- 5. ★ THE MOVES, each by its `LowerSim` lemma.
  ----------------------------------------------------------------------

  private
    len-++3 : ∀ (x y z : AbstractTrace) → length (x ++ y ++ z) ≡ length x + (length y + length z)
    len-++3 x y z = trans (length-++ x) (cong (length x +_) (length-++ y))

    -- a view step's move, as a straight run
    viaS : ∀ {sb} {m′ : Cfg sb} {fs a b n}
         → Σ FlatState (λ fs′ → FlatSteps prog (Once.LinCore.Moves.ln {FS} n) fs fs′
                                × CfgW (heapMem (floc fs′)) (slot fs′) φ m′ × MovedS fs fs′ a b n)
         → Gives fs (Once.LinCore.Moves.ln {FS} n) 0 m′
    viaS (fs′ , st , C′ , M) = fs′ , st , C′ , ranS M

  st-swap : ∀ {Es A B S V} {k : Codeᴵ (Es ∣ B ∷ A ∷ S) V} (s : Sub root (swap ⨾ k))
              {es : Slots Es} {a : MV A} {b : MV B} {os : Stk S} {fs}
          → Here s (es ∥ a ∷ˢ b ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ b ∷ˢ a ∷ˢ os)
  st-swap {A = A} {B} {S} s {fs = fs} H =
    let t = Tp φ (A ∷ B ∷ S) in
    straight s H _ 0
      (sym (trans (len-++3 (mvSS t (t ∸ wsz A) (wsz A)) (mvSS (t + wsz A) t (wsz B)) (mvSS (t ∸ wsz A) (t + wsz B) (wsz A)))
                  (cong₂ _+_ (len-mvSS t (t ∸ wsz A) (wsz A))
                    (cong₂ _+_ (len-mvSS (t + wsz A) t (wsz B)) (len-mvSS (t ∸ wsz A) (t + wsz B) (wsz A))))))
      (λ sg h C → swap-sim prog fs φ sg h C (proj₂ (ins-fits s)))

  st-elend : ∀ {E Es X A S V} {k : Codeᴵ ((E ⊗t X) ∷ E ∷ Es ∣ A ∷ S) V} (s : Sub root (elend ⨾ k))
               {es : Slots (E ∷ Es)} {x : MV X} {a : MV A} {os : Stk S} {fs}
           → Here s (es ∥ mpair x a ∷ˢ os) fs → Moved (next s) fs 0 (ln (see es) x es ∥ a ∷ˢ os)
  st-elend {E} {Es} {X} {A} {S} s {fs = fs} H =
    let e = ws Es ; wE = wsz E in
    straight s H _ 0
      (sym (trans (length-++ (mvSS e (e + wE) wE) {mvSS (Tp φ ((X ⊗t A) ∷ S)) (e + wE + wE) (wsz X)})
                  (cong₂ _+_ (len-mvSS e (e + wE) wE) (len-mvSS (Tp φ ((X ⊗t A) ∷ S)) (e + wE + wE) (wsz X)))))
      (λ sg h C → elend-sim prog fs φ sg h C (proj₁ (shape-fits (next s))))

  st-eunlend : ∀ {E Es X B S V} {k : Codeᴵ (E ∷ Es ∣ (X ⊗t B) ∷ S) V} (s : Sub root (eunlend ⨾ k))
                 {e : MV E} {x : MV X} {es : Slots (E ∷ Es)} {w : MV B} {os : Stk S} {fs}
             → Here s (ln e x es ∥ w ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mpair x w ∷ˢ os)
  st-eunlend {X = X} s {fs = fs} H =
    straight s H _ 0 (sym (len-mvSS _ _ (wsz X)))
      (λ sg h C → eunlend-sim prog fs φ sg h C (proj₂ (shape-fits (next s))))

  st-efst : ∀ {E₁ E₂ Es S V} {k : Codeᴵ (E₁ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S) V} (s : Sub root (efst ⨾ k))
              {es : Slots ((E₁ ⊗t E₂) ∷ Es)} {os : Stk S} {e₁ : MV E₁} {e₂ : MV E₂} {fs}
          → see es ≡ mpair e₁ e₂ → Here s (es ∥ os) fs → Moved (next s) fs 0 (vw e₁ es ∥ os)
  st-efst {E₁} s {fs = fs} eq H =
    straight s H _ 0 (sym (len-mvSS _ _ (wsz E₁)))
      (λ sg h C → viaS (efst-sim prog fs φ eq sg h C (proj₁ (shape-fits (next s)))))

  st-esnd : ∀ {E₁ E₂ Es S V} {k : Codeᴵ (E₂ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S) V} (s : Sub root (esnd ⨾ k))
              {es : Slots ((E₁ ⊗t E₂) ∷ Es)} {os : Stk S} {e₁ : MV E₁} {e₂ : MV E₂} {fs}
          → see es ≡ mpair e₁ e₂ → Here s (es ∥ os) fs → Moved (next s) fs 0 (vw e₂ es ∥ os)
  st-esnd {E₂ = E₂} s {fs = fs} eq H =
    straight s H _ 0 (sym (len-mvSS _ _ (wsz E₂)))
      (λ sg h C → viaS (esnd-sim prog fs φ eq sg h C (proj₁ (shape-fits (next s)))))

  st-eapp : ∀ {l X Es S V} {k : Codeᴵ (X ∷ Ct l X ∷ Es ∣ S) V} (s : Sub root (eapp ⨾ k))
              {es : Slots (Ct l X ∷ Es)} {os : Stk S} {x : MV X} {fs}
          → see es ≡ mct x → Here s (es ∥ os) fs → Moved (next s) fs 0 (vw x es ∥ os)
  st-eapp {X = X} s {fs = fs} eq H =
    straight s H _ 0 (sym (len-mvSS _ _ (wsz X)))
      (λ sg h C → viaS (eapp-sim prog fs φ eq sg h C (proj₁ (shape-fits (next s)))))

  st-eword : ∀ {b Es S V} {k : Codeᴵ (Bt b ∷ Es ∣ Bt b ∷ S) V} (s : Sub root (eword ⨾ k))
               {es : Slots (Bt b ∷ Es)} {os : Stk S} {x : ⟦ b ⟧b} {fs}
           → see es ≡ mbase x → Here s (es ∥ mone ∷ˢ os) fs → Moved (next s) fs 0 (es ∥ mbase x ∷ˢ os)
  st-eword s {fs = fs} eq H =
    straight s H _ 0 refl
      (λ sg h C → viaS (eword-sim prog fs φ eq sg h C (proj₂ (shape-fits (next s)))))

  st-eout : ∀ {F Es S V} {k : Codeᴵ (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S) V} (s : Sub root (eout ⨾ k))
              {es : Slots (μt F ∷ Es)} {os : Stk S} {i} {v : MV (LF∙ F (μt F))} {fs}
          → see es ≡ mmu i v → Here s (es ∥ os) fs → Moved (next s) fs 0 (vw v es ∥ os)
  st-eout {F} s {fs = fs} eq H =
    straight s H _ 0 (sym (cong suc (len-mvPS _ _ (wsz (LF∙ F (μt F))))))
      (λ sg h C → eout-sim prog fs φ eq sg h C (proj₁ (shape-fits (next s))))

  st-eoutq : ∀ {F Es S V} {k : Codeᴵ (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S) V} (s : Sub root (eoutq ⨾ k))
               {es : Slots (μt F ∷ Es)} {os : Stk S} {i} {v : MV (LF∙ F (μt F))} {fs}
           → see es ≡ mmu i v → Here s (es ∥ os) fs → Moved (next s) fs 0 (vw v es ∥ os)
  st-eoutq {F} s {fs = fs} eq H =
    straight s H _ 0 (sym (cong suc (len-mvPS _ _ (wsz (LF∙ F (μt F))))))
      (λ sg h C → eout-sim prog fs φ eq sg h C (proj₁ (shape-fits (next s))))
