-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Jumps — plan 0.146 B1.7 step 3 (D461): ★ EVERY JUMP OF THE
-- IMAGE NAMES A LABEL THE IMAGE DEFINES (what the file's well-formedness
-- reads of its local symbols, `AsmWF.resolved`).
--
-- Only a `case`, an `ecase` and a loop jump (`c-branch-tag-zero`, `c-jmp`),
-- each to a label it defines itself — the loop's round ends in the jump back
-- to its dispatch, which the loop defines. Every other lowering is JUMP-FREE
-- (`NoJ`, as `Labels.NoLabels` is label-free: each proof the same `refl`).
-- So a code's jumps name its own labels or its `fin`'s (`Cov`), and a
-- block's, a trampoline's and the start's code are closed.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
import Data.List.Relation.Unary.All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
import Once.Spec.Type as ST
open import Once.SigOp.Info using (module SigOpInfo)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (LabelId)

module Once.LinCore.Jumps
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Image fmt bw
open import Once.LinCore.Keys fmt bw
open import Once.LinCore.Layout fmt bw
open import Once.LinCore.Lower fmt bw
open import Once.LinCore.LabelsC fmt ans bw using (module LabsC)

------------------------------------------------------------------------
-- 1. THE LABEL A JUMP NAMES.
------------------------------------------------------------------------

jump-of : AbstractInstr → Maybe LabelId
jump-of (instr-ctrl (c-jmp l))             = just l
jump-of (instr-ctrl (c-branch-tag-zero l)) = just l
{-# CATCHALL #-}
jump-of _                                  = nothing

jmp : Maybe LabelId → List LabelId → List LabelId
jmp (just l) r = l ∷ r
jmp nothing  r = r

Jmps : AbstractTrace → List LabelId
Jmps []       = []
Jmps (x ∷ xs) = jmp (jump-of x) (Jmps xs)

Jmps-++ : ∀ xs ys → Jmps (xs ++ ys) ≡ Jmps xs ++ Jmps ys
Jmps-++ []       ys = refl
Jmps-++ (x ∷ xs) ys = go (jump-of x)
  where
    go : ∀ mo → jmp mo (Jmps (xs ++ ys)) ≡ jmp mo (Jmps xs) ++ Jmps ys
    go (just l) = cong (l ∷_) (Jmps-++ xs ys)
    go nothing  = Jmps-++ xs ys

-- code that jumps nowhere
NoJ : AbstractTrace → Set
NoJ = All (λ x → jump-of x ≡ nothing)

nj : ∀ xs {ys} → NoJ xs → NoJ ys → NoJ (xs ++ ys)
nj xs p q = ++⁺ p q

Jmps-nj : ∀ {xs} → NoJ xs → Jmps xs ≡ []
Jmps-nj {[]}     []      = refl
Jmps-nj {x ∷ xs} (e ∷ p) = go (jump-of x) e
  where
    go : ∀ mo → mo ≡ nothing → jmp mo (Jmps xs) ≡ []
    go nothing refl = Jmps-nj p

------------------------------------------------------------------------
-- 2. THE LOWERING'S JUMP-FREE PARTS (`Labels.NoLabels`, for jumps).
------------------------------------------------------------------------

mvSS-nj : ∀ a b n → NoJ (mvSS a b n)
mvSS-nj a b zero    = []
mvSS-nj a b (suc n) = refl ∷ refl ∷ mvSS-nj (suc a) (suc b) n

mvSSd-nj : ∀ a b n → NoJ (mvSSd a b n)
mvSSd-nj a b zero    = []
mvSSd-nj a b (suc n) = refl ∷ refl ∷ mvSSd-nj a b n

mvPS-nj : ∀ o b n → NoJ (mvPS o b n)
mvPS-nj o b zero    = []
mvPS-nj o b (suc n) = refl ∷ refl ∷ mvPS-nj (suc o) (suc b) n

mvSP-nj : ∀ a o n → NoJ (mvSP a o n)
mvSP-nj a o zero    = []
mvSP-nj a o (suc n) = refl ∷ refl ∷ mvSP-nj (suc a) (suc o) n

stores-nj : ∀ b n → NoJ (stores b n)
stores-nj b zero    = []
stores-nj b (suc n) = refl ∷ stores-nj (suc b) n

module Free (U : Univ)
            (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
            (ldConst : ∀ {b} → Lit b → AbstractInstr)
            (ld-nj : ∀ {b} (v : Lit b) → jump-of (ldConst v) ≡ nothing) where
  open In U
  open Lowering U ncty ldConst

  header-nj : ∀ w jb jc jf → NoJ (header w jb jc jf)
  header-nj w jb jc jf = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

  argIn-nj : ∀ {A} (b : ST.Base ST.∅ₖ A) bot w → jump-of (argIn b bot w) ≡ nothing
  argIn-nj (ST.b-var {i = ()} _) bot w
  argIn-nj ST.b-Unit    bot w = refl
  argIn-nj ST.b-Void    bot w = refl
  argIn-nj ST.b-Int     bot w = refl
  argIn-nj ST.b-Float   bot w = refl
  argIn-nj (ST.b-* _ _) bot w = refl
  argIn-nj (ST.b-+ _ _) bot w = refl

  answer-nj : ∀ {B} (b : ST.Base ST.∅ₖ B) bot → NoJ (answer b bot)
  answer-nj (ST.b-var {i = ()} _) bot
  answer-nj ST.b-Unit    bot = []
  answer-nj ST.b-Void    bot = []
  answer-nj ST.b-Int     bot = refl ∷ []
  answer-nj ST.b-Float   bot = refl ∷ []
  answer-nj (ST.b-* _ _) bot = []
  answer-nj (ST.b-+ _ _) bot = []

  ansDst-nj : ∀ {B} (b : ST.Base ST.∅ₖ B) bot w → NoJ (ansDst b bot w)
  ansDst-nj (ST.b-var {i = ()} _) bot w
  ansDst-nj ST.b-Unit    bot w = []
  ansDst-nj ST.b-Void    bot w = []
  ansDst-nj ST.b-Int     bot w = []
  ansDst-nj ST.b-Float   bot w = []
  ansDst-nj (ST.b-* _ _) bot w = refl ∷ []
  ansDst-nj (ST.b-+ _ _) bot w = refl ∷ []

  lowOp-nj : ∀ s m bot → NoJ (lowOp s m bot)
  lowOp-nj s nothing  bot =
    argIn-nj (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ refl
    ∷ nj (ansDst (SigOpInfo.conB (info s)) bot (wsz ⌜ scod s ⌝)) (ansDst-nj (SigOpInfo.conB (info s)) bot (wsz ⌜ scod s ⌝))
         (refl ∷ answer-nj (SigOpInfo.conB (info s)) bot)
  lowOp-nj s (just o) bot = argIn-nj (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

  cell-nj : ∀ w jb jc jf a o d → NoJ (header w jb jc jf ++ mvSP a o w ++ mov-to-output ∷ store-at-slot d ∷ [])
  cell-nj w jb jc jf a o d = nj (header w jb jc jf) (header-nj w jb jc jf) (nj (mvSP a o w) (mvSP-nj a o w) (refl ∷ refl ∷ []))

  lowP-nj : ∀ {Γ} (ds : Defs Γ) {A B} (g : LTm Γ A B) φ S (p : PrimIn ds g) → NoJ (lowP ds g φ S p)
  lowP-nj ds lid φ S p          = []
  lowP-nj ds (_ ∘l _) φ S p     = []
  lowP-nj ds (_ ⊗l _) φ S p     = []
  lowP-nj ds ρl φ S p           = []
  lowP-nj ds ρl⁻ φ S p          = []
  lowP-nj ds lul φ S p          = []
  lowP-nj ds lul⁻ φ S p         = []
  lowP-nj ds lassoc φ S p       = []
  lowP-nj ds lassoc⁻ φ S p      = []
  lowP-nj ds (lswap {A = A} {B = B}) φ S p =
    let t = Tp φ (A ∷ B ∷ S) ; wA = wsz A ; wB = wsz B ; tmp = t ∸ wA
    in nj (mvSS t tmp wA) (mvSS-nj t tmp wA) (nj (mvSS (t + wA) t wB) (mvSS-nj (t + wA) t wB) (mvSS-nj tmp (t + wB) wA))
  lowP-nj ds dup φ S p          = []
  lowP-nj ds drop φ S p         = []
  lowP-nj ds (linl {A = A} {B = B}) φ S p =
    let bot = Tp φ S ; M = wsz A ⊔ wsz B
    in nj (mvSS (bot ∸ wsz A) (bot ∸ M) (wsz A)) (mvSS-nj (bot ∸ wsz A) (bot ∸ M) (wsz A))
          (refl ∷ refl ∷ stores-nj (bot ∸ (M ∸ wsz A)) (M ∸ wsz A))
  lowP-nj ds (linr {A = A} {B = B}) φ S p =
    let bot = Tp φ S ; M = wsz A ⊔ wsz B
    in nj (mvSS (bot ∸ wsz B) (bot ∸ M) (wsz B)) (mvSS-nj (bot ∸ wsz B) (bot ∸ M) (wsz B))
          (refl ∷ refl ∷ stores-nj (bot ∸ (M ∸ wsz B)) (M ∸ wsz B))
  lowP-nj ds (lcase _ _) φ S p  = []
  lowP-nj ds lzero φ S p        = []
  lowP-nj ds (lIn {F = F}) φ S p =
    let bot = Tp φ S ; wL = wsz (LF∙ F (μt F))
    in refl ∷ refl ∷ nj (mvSP (bot ∸ wL) 0 wL) (mvSP-nj (bot ∸ wL) 0 wL) (refl ∷ refl ∷ [])
  lowP-nj ds (lOutμ {F = F}) φ S p =
    let bot = Tp φ S ; wL = wsz (LF∙ F (μt F))
    in refl ∷ nj (mvPS 0 (bot ∸ wL) wL) (mvPS-nj 0 (bot ∸ wL) wL) (refl ∷ [])
  lowP-nj ds (lcata _ _) φ S p  = []
  lowP-nj ds (lclo _ _) φ S p   = []
  lowP-nj ds (lapp _) φ S p     = []
  lowP-nj ds (lend _) φ S p     = []
  lowP-nj ds (blift _) φ S p    = []
  lowP-nj ds bcopy φ S p        = []
  lowP-nj ds (llam {X = X} b γ) φ S (kb , x) =
    cell-nj (wsz X) (idx kb) (idx (inC x)) (idx (inF x)) (Tp φ S ∸ wsz X) hdr (Tp φ S ∸ 1)
  lowP-nj ds (llamω {X = X} b γ) φ S (kb , x) =
    cell-nj (wsz X) (idx kb) (idx (inC x)) (idx (inF x)) (Tp φ S ∸ wsz X) hdr (Tp φ S ∸ 1)
  lowP-nj ds lev φ S p          = []
  lowP-nj ds (lunf {F = F} {S = S₀}) φ S (n , o) =
    cell-nj (wsz (cty (F , S₀))) (idx (inO o n)) (idx (inC (ncty n))) (idx (inF (ncty n))) (Tp φ S ∸ wsz (cty (F , S₀))) hdr (Tp φ S ∸ 1)
  lowP-nj ds lout φ S p         = []
  lowP-nj ds (lconst v) φ S p   = ld-nj v ∷ refl ∷ []
  lowP-nj ds (lop s) φ S p      = lowOp-nj s (cmpOf s) (Tp φ S)
  lowP-nj ds (liter _ _) φ S p  = []

  NotLoop : ∀ {sh sh′} → Insᴵ sh sh′ → Set
  NotLoop (loop _) = ⊥
  {-# CATCHALL #-}
  NotLoop _        = ⊤

  lowI-nj : ∀ φ j m {sh sh′} (i : Insᴵ sh sh′) (ei : IIn i) → NotLoop i → NoJ (proj₁ (lowI φ j m i ei))
  lowI-nj φ j m unpair ei _  = []
  lowI-nj φ j m pair ei _    = []
  lowI-nj φ j m unit ei _    = []
  lowI-nj φ j m untag ei _   = []
  lowI-nj φ j m untag₁ ei _  = []
  lowI-nj φ j m tag₁ ei _    = []
  lowI-nj φ j m elift ei _   = []
  lowI-nj φ j m epop ei _    = []
  lowI-nj φ j m stuck ei _   = []
  lowI-nj φ j m (swap {A = A} {B} {S}) ei _ =
    let t = Tp φ (A ∷ B ∷ S) ; wA = wsz A ; wB = wsz B ; tmp = t ∸ wA
    in nj (mvSS t tmp wA) (mvSS-nj t tmp wA) (nj (mvSS (t + wA) t wB) (mvSS-nj (t + wA) t wB) (mvSS-nj tmp (t + wB) wA))
  lowI-nj φ j m (prim ds {S = S} g) ei _ = lowP-nj ds g φ S ei
  lowI-nj φ j m (elend {E} {Es} {X} {A} {S}) ei _ =
    let e = ws Es ; wE = wsz E
    in nj (mvSS e (e + wE) wE) (mvSS-nj e (e + wE) wE) (mvSS-nj (Tp φ ((X ⊗t A) ∷ S)) (e + wE + wE) (wsz X))
  lowI-nj φ j m (eunlend {E} {Es} {X} {B} {S}) ei _ =
    let e = ws Es ; wE = wsz E in mvSS-nj (e + wE + wE) (Tp φ (B ∷ S) ∸ wsz X) (wsz X)
  lowI-nj φ j m (efst {E₁} {E₂} {Es}) ei _ = mvSS-nj (ws Es) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₁)
  lowI-nj φ j m (esnd {E₁} {E₂} {Es}) ei _ = mvSS-nj (ws Es + wsz E₁) (ws Es + wsz (E₁ ⊗t E₂)) (wsz E₂)
  lowI-nj φ j m (eout {F} {Es}) ei _  = refl ∷ mvPS-nj 0 (suc (ws Es)) (wsz (LF∙ F (μt F)))
  lowI-nj φ j m (eoutq {F} {Es}) ei _ = refl ∷ mvPS-nj 0 (suc (ws Es)) (wsz (LF∙ F (μt F)))
  lowI-nj φ j m (eapp {l} {X} {Es}) ei _ = mvSS-nj (ws Es) (ws Es + wsz X) (wsz X)
  lowI-nj φ j m (eword {b} {Es} {S}) ei _ = mvSS-nj (ws Es) (Tp φ S ∸ 1) 1
  lowI-nj φ j m (call {bsig nothing A B} κ) ei _  = refl ∷ refl ∷ refl ∷ []
  lowI-nj φ j m (call {bsig (just E) A B} κ) ei _ = refl ∷ refl ∷ refl ∷ refl ∷ []
  lowI-nj φ j m icall ei _   = refl ∷ refl ∷ refl ∷ refl ∷ []
  lowI-nj φ j m icallω ei _  = refl ∷ refl ∷ refl ∷ refl ∷ []
  lowI-nj φ j m (iobs ds) ei _ = refl ∷ refl ∷ refl ∷ refl ∷ []
  lowI-nj φ j m ccopy ei _   = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
  lowI-nj φ j m ncopy ei _   = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
  lowI-nj φ j m cfree ei _   = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
  lowI-nj φ j m nfree ei _   = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
  lowI-nj φ j m open1 ei _   = []
  lowI-nj φ j m openω ei _   = []
  lowI-nj φ j m nopen ei _   = []
  lowI-nj φ j m copen ei _   = []
  lowI-nj φ j m reclose ei _ = []
  lowI-nj φ j m fopen ei _   = []
  lowI-nj φ j m (loop c) ei ()

  private
    cA : ∀ w → jump-of (contentsAddr w) ≡ nothing
    cA zero    = refl
    cA (suc w) = refl

  -- ★ a trampoline jumps nowhere
  tramp-nj : ∀ {σ} j (κ : Key σ) → NoJ (tramp j κ)
  tramp-nj j (kbody1 {X = X} {A = A} {B = B} ds b γ) =
    let wX = wsz X ; wA = wsz A ; wB = wsz B ; M = (wX + wA) ⊔ wB ; Mc = suc wA ⊔ wB ; a = M ∸ (wX + wA)
    in refl ∷ refl ∷ refl ∷ refl ∷ nj (mvPS hdr a wX) (mvPS-nj hdr a wX)
         (refl ∷ nj (mvPS (Mc ∸ wA) (a + wX) wA) (mvPS-nj (Mc ∸ wA) (a + wX) wA)
           (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ nj (mvSP (M ∸ wB) (Mc ∸ wB) wB) (mvSP-nj (M ∸ wB) (Mc ∸ wB) wB) (refl ∷ [])))
  tramp-nj j (kbodyω {X = X} ds b γ) = refl ∷ refl ∷ cA (wsz X) ∷ refl ∷ refl ∷ refl ∷ []
  tramp-nj j (kobs ds F S) =
    let wP = wsz (cty (F , S)) ; wL = wsz (LF∙ F (Nu F)) ; M = wP ⊔ wL ; Mc = 1 ⊔ wL
    in refl ∷ refl ∷ refl ∷ refl ∷ nj (mvPS hdr (M ∸ wP) wP) (mvPS-nj hdr (M ∸ wP) wP)
         (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ nj (mvSP (M ∸ wL) (Mc ∸ wL) wL) (mvSP-nj (M ∸ wL) (Mc ∸ wL) wL) (refl ∷ []))
  tramp-nj j (kcopy T₀) =
    let w = wsz T₀
    in refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ cA w ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl
       ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl
       ∷ nj (mvSP 0 hdr w) (mvSP-nj 0 hdr w) (refl ∷ refl ∷ refl ∷ refl ∷ [])
  tramp-nj j (kfree T₀) =
    let w = wsz T₀
    in refl ∷ refl ∷ refl ∷ nj (mvPS hdr 0 w) (mvPS-nj hdr 0 w) (refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ [])
  tramp-nj j (kfold ds F alg) = []
  tramp-nj j (ktr1 ds b γ) = []
  tramp-nj j (ktrω ds b γ) = []
  tramp-nj j (ktro ds F S) = []
  tramp-nj j (ktrc X C)    = []
  tramp-nj j (ktrf X C)    = []

  view-nj : ∀ t φ → NoJ (view-in t φ)
  view-nj nothing  φ = []
  view-nj (just E) φ = refl ∷ mvPS-nj 0 0 (wsz E)

------------------------------------------------------------------------
-- 3. ★ A CODE'S JUMPS NAME ITS OWN LABELS OR ITS `fin`'s.
------------------------------------------------------------------------

module Closed {FS : FrameSemantics} where
  open LabsC {FS} using (Labs; Labs-++)

  -- every jump of `xs` names a label of `L` or one of `E`
  Cov : List LabelId → List LabelId → AbstractTrace → Set
  Cov L E xs = All (λ l → l ∈ L ⊎ l ∈ E) (Jmps xs)

  cov-nj : ∀ {L E xs} → NoJ xs → Cov L E xs
  cov-nj {L} {E} {xs} p = subst (All (λ l → l ∈ L ⊎ l ∈ E)) (sym (Jmps-nj p)) []

  -- more labels cover as much
  widenL : ∀ {L L′ E : List LabelId} → (∀ {l} → l ∈ L → l ∈ L′) → ∀ {ls : List LabelId} → All (λ l → l ∈ L ⊎ l ∈ E) ls → All (λ l → l ∈ L′ ⊎ l ∈ E) ls
  widenL sub = Data.List.Relation.Unary.All.map (λ { (inj₁ p) → inj₁ (sub p) ; (inj₂ q) → inj₂ q })

  -- one stretch, then the next: each covered by its own labels
  cov-++ : ∀ {E} xs ys → Cov (Labs xs) E xs → Cov (Labs ys) E ys → Cov (Labs (xs ++ ys)) E (xs ++ ys)
  cov-++ {E} xs ys cx cy =
    subst (All (λ l → l ∈ Labs (xs ++ ys) ⊎ l ∈ E)) (sym (Jmps-++ xs ys))
      (++⁺ (widenL (λ {l} p → subst (l ∈_) (sym (Labs-++ xs ys)) (∈-++⁺ˡ p)) cx)
           (widenL (λ {l} p → subst (l ∈_) (sym (Labs-++ xs ys)) (∈-++⁺ʳ (Labs xs) p)) cy))

  -- two stretches covered by the same labels
  cov-app : ∀ {L E} xs ys → Cov L E xs → Cov L E ys → Cov L E (xs ++ ys)
  cov-app {L} {E} xs ys cx cy = subst (All (λ l → l ∈ L ⊎ l ∈ E)) (sym (Jmps-++ xs ys)) (++⁺ cx cy)

  -- a stretch's labels are its whole's
  in-pre : ∀ xs ys {l} → l ∈ Labs xs → l ∈ Labs (xs ++ ys)
  in-pre xs ys {l} p = subst (l ∈_) (sym (Labs-++ xs ys)) (∈-++⁺ˡ p)

  in-suf : ∀ xs ys {l} → l ∈ Labs ys → l ∈ Labs (xs ++ ys)
  in-suf xs ys {l} p = subst (l ∈_) (sym (Labs-++ xs ys)) (∈-++⁺ʳ (Labs xs) p)

  module C (U : Univ)
           (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nj : ∀ {b} (v : Lit b) → jump-of (ldConst v) ≡ nothing) where
    open In U
    open Lowering U ncty ldConst
    open Free U ncty ldConst ld-nj

    -- ★ a branch: the test names the label `L₁` the code defines further on
    branch-cov : ∀ {E} (P₀ : AbstractTrace) L₁ (M₁ M₂ l₂ l₁ : AbstractTrace) → NoJ P₀ → NoJ M₁ → NoJ M₂
           → Cov (Labs l₂) E l₂ → Cov (Labs l₁) E l₁
           → Cov (Labs (P₀ ++ instr-ctrl (c-branch-tag-zero L₁) ∷ M₁ ++ l₂ ++ instr-ctrl (c-label L₁) ∷ M₂ ++ l₁)) E
                 (P₀ ++ instr-ctrl (c-branch-tag-zero L₁) ∷ M₁ ++ l₂ ++ instr-ctrl (c-label L₁) ∷ M₂ ++ l₁)
    branch-cov {E} P₀ L₁ M₁ M₂ l₂ l₁ p₀ m₁ m₂ c₂ c₁ =
      cov-app P₀ _ (cov-nj p₀)
        (cov-app (instr-ctrl (c-branch-tag-zero L₁) ∷ M₁) _
          (subst (All (λ l → l ∈ W ⊎ l ∈ E)) (sym (cong (L₁ ∷_) (Jmps-nj m₁))) (inj₁ (upW (in-suf l₂ R (here refl))) ∷ []))
          (cov-app l₂ R (widenL (λ p → upW (in-pre l₂ R p)) c₂)
            (cov-app (instr-ctrl (c-label L₁) ∷ M₂) l₁ (subst (All (λ l → l ∈ W ⊎ l ∈ E)) (sym (Jmps-nj m₂)) [])
              (widenL (λ p → upW (in-suf l₂ R (in-suf (instr-ctrl (c-label L₁) ∷ M₂) l₁ p))) c₁))))
      where
        R = instr-ctrl (c-label L₁) ∷ M₂ ++ l₁
        W = Labs (P₀ ++ instr-ctrl (c-branch-tag-zero L₁) ∷ M₁ ++ l₂ ++ R)
        -- from the code after the test to the whole
        upW : ∀ {l} → l ∈ Labs (l₂ ++ R) → l ∈ W
        upW p = in-suf P₀ _ (in-suf (instr-ctrl (c-branch-tag-zero L₁) ∷ M₁) (l₂ ++ R) p)

    private
      plain : ∀ φ j m {sh sh′} (i : Insᴵ sh sh′) (ei : IIn i) → NotLoop i → ∀ {E} → Cov (Labs (proj₁ (lowI φ j m i ei))) E (proj₁ (lowI φ j m i ei))
      plain φ j m i ei nl = cov-nj (lowI-nj φ j m i ei nl)

    mutual
      -- ★ an instruction's code is closed: it jumps only to labels it defines
      lowI-cov : ∀ φ j m {sh sh′} (i : Insᴵ sh sh′) (ei : IIn i) → ∀ {E} → Cov (Labs (proj₁ (lowI φ j m i ei))) E (proj₁ (lowI φ j m i ei))
      lowI-cov φ j m i@unpair ei  = plain φ j m i ei tt
      lowI-cov φ j m i@pair ei    = plain φ j m i ei tt
      lowI-cov φ j m i@unit ei    = plain φ j m i ei tt
      lowI-cov φ j m i@untag ei   = plain φ j m i ei tt
      lowI-cov φ j m i@untag₁ ei  = plain φ j m i ei tt
      lowI-cov φ j m i@tag₁ ei    = plain φ j m i ei tt
      lowI-cov φ j m i@elift ei   = plain φ j m i ei tt
      lowI-cov φ j m i@epop ei    = plain φ j m i ei tt
      lowI-cov φ j m i@stuck ei   = plain φ j m i ei tt
      lowI-cov φ j m i@swap ei    = plain φ j m i ei tt
      lowI-cov φ j m i@(prim ds g) ei = plain φ j m i ei tt
      lowI-cov φ j m i@elend ei   = plain φ j m i ei tt
      lowI-cov φ j m i@eunlend ei = plain φ j m i ei tt
      lowI-cov φ j m i@efst ei    = plain φ j m i ei tt
      lowI-cov φ j m i@esnd ei    = plain φ j m i ei tt
      lowI-cov φ j m i@eout ei    = plain φ j m i ei tt
      lowI-cov φ j m i@eoutq ei   = plain φ j m i ei tt
      lowI-cov φ j m i@eapp ei    = plain φ j m i ei tt
      lowI-cov φ j m i@eword ei   = plain φ j m i ei tt
      lowI-cov φ j m i@(call {bsig nothing A B} κ) ei  = plain φ j m i ei tt
      lowI-cov φ j m i@(call {bsig (just E) A B} κ) ei = plain φ j m i ei tt
      lowI-cov φ j m i@icall ei   = plain φ j m i ei tt
      lowI-cov φ j m i@icallω ei  = plain φ j m i ei tt
      lowI-cov φ j m i@(iobs ds) ei = plain φ j m i ei tt
      lowI-cov φ j m i@ccopy ei   = plain φ j m i ei tt
      lowI-cov φ j m i@ncopy ei   = plain φ j m i ei tt
      lowI-cov φ j m i@cfree ei   = plain φ j m i ei tt
      lowI-cov φ j m i@nfree ei   = plain φ j m i ei tt
      lowI-cov φ j m i@open1 ei   = plain φ j m i ei tt
      lowI-cov φ j m i@openω ei   = plain φ j m i ei tt
      lowI-cov φ j m i@nopen ei   = plain φ j m i ei tt
      lowI-cov φ j m i@copen ei   = plain φ j m i ei tt
      lowI-cov φ j m i@reclose ei = plain φ j m i ei tt
      lowI-cov φ j m i@fopen ei   = plain φ j m i ei tt
      -- ★ the loop: its round jumps back to the dispatch `Ld`, the dispatch to the exit `Li` and the head `Lh`
      lowI-cov φ j m (loop {E} {Es} {A} {B} {S} c) eb {E′} =
        cov-app (instr-ctrl (c-label Lh) ∷ body) Td
          (Data.List.Relation.Unary.All.map round (lowC-cov φ j (suc (suc (suc m))) (instr-ctrl (c-jmp Ld) ∷ []) c eb))
          (subst (All (λ l → l ∈ W ⊎ l ∈ E′)) (sym jT) (inj₁ Li∈ ∷ inj₁ (here refl) ∷ []))
        where
          Lh = jl j m ; Ld = jl j (suc m) ; Li = jl j (suc (suc m))
          t = Tp φ ((B ⊕t A) ∷ S) ; bot = Tp φ S
          MA = mvSSd (suc t) (bot ∸ wsz A) (wsz A) ; MB = mvSSd (suc t) (bot ∸ wsz B) (wsz B)
          body = proj₁ (lowC φ j (suc (suc (suc m))) (instr-ctrl (c-jmp Ld) ∷ []) c eb)
          Td = instr-ctrl (c-label Ld) ∷ lea-slot t ∷ mov-to-input ∷ instr-ctrl (c-branch-tag-zero Li)
              ∷ MA ++ instr-ctrl (c-jmp Lh) ∷ instr-ctrl (c-label Li) ∷ MB
          W = Labs (instr-ctrl (c-label Lh) ∷ body ++ Td)
          Li∈ : Li ∈ W
          Li∈ = in-suf (instr-ctrl (c-label Lh) ∷ body) Td (there (in-suf MA (instr-ctrl (c-jmp Lh) ∷ instr-ctrl (c-label Li) ∷ MB) (here refl)))
          round : ∀ {l} → l ∈ Labs body ⊎ l ∈ Ld ∷ [] → l ∈ W ⊎ l ∈ E′
          round (inj₁ p)         = inj₁ (in-pre (instr-ctrl (c-label Lh) ∷ body) Td (there p))
          round (inj₂ (here refl)) = inj₁ (in-suf (instr-ctrl (c-label Lh) ∷ body) Td (here refl))
          jT : Jmps Td ≡ Li ∷ Lh ∷ []
          jT = cong (Li ∷_) (trans (Jmps-++ MA (instr-ctrl (c-jmp Lh) ∷ instr-ctrl (c-label Li) ∷ MB))
                                  (cong₂ _++_ (Jmps-nj (mvSSd-nj (suc t) (bot ∸ wsz A) (wsz A))) (cong (Lh ∷_) (Jmps-nj (mvSSd-nj (suc t) (bot ∸ wsz B) (wsz B))))))

      -- ★ a code's jumps name its labels or its `fin`'s
      lowC-cov : ∀ φ j m fin {sh T} (c : Codeᴵ sh T) (ev : CIn c) → Cov (Labs (proj₁ (lowC φ j m fin c ev))) (Jmps fin) (proj₁ (lowC φ j m fin c ev))
      lowC-cov φ j m fin end ev    = Data.List.Relation.Unary.All.tabulate inj₂
      lowC-cov φ j m fin halted ev = []
      lowC-cov φ j m fin (i ⨾ c) (ei , ec) =
        cov-++ (proj₁ (lowI φ j m i ei)) (proj₁ (lowC φ j (proj₂ (lowI φ j m i ei)) fin c ec))
          (lowI-cov φ j m i ei) (lowC-cov φ j (proj₂ (lowI φ j m i ei)) fin c ec)
      lowC-cov φ j m fin (case {Es} {A} {B} {S} c₁ c₂) (e₁ , e₂) =
        let t = Tp φ ((A ⊕t B) ∷ S) ; bot = Tp φ S
            l₂ = lowC φ j (suc m) fin c₂ e₂
        in branch-cov (lea-slot t ∷ mov-to-input ∷ []) (jl j m) (mvSSd (suc t) (bot ∸ wsz B) (wsz B)) (mvSSd (suc t) (bot ∸ wsz A) (wsz A))
             (proj₁ l₂) (proj₁ (lowC φ j (proj₂ l₂) fin c₁ e₁)) (refl ∷ refl ∷ []) (mvSSd-nj _ _ _) (mvSSd-nj _ _ _)
             (lowC-cov φ j (suc m) fin c₂ e₂) (lowC-cov φ j (proj₂ l₂) fin c₁ e₁)
      lowC-cov φ j m fin (ecase {E₁} {E₂} {Es} c₁ c₂) (e₁ , e₂) =
        let e = ws Es ; nb = e + wsz (E₁ ⊕t E₂)
            l₂ = lowC φ j (suc m) fin c₂ e₂
        in branch-cov (lea-slot e ∷ mov-to-input ∷ []) (jl j m) (mvSS (suc e) nb (wsz E₂)) (mvSS (suc e) nb (wsz E₁))
             (proj₁ l₂) (proj₁ (lowC φ j (proj₂ l₂) fin c₁ e₁)) (refl ∷ refl ∷ []) (mvSS-nj _ _ _) (mvSS-nj _ _ _)
             (lowC-cov φ j (suc m) fin c₂ e₂) (lowC-cov φ j (proj₂ l₂) fin c₁ e₁)
