-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ImageGuard — plan 0.146 B1.6: ★ NOTHING FALLS INTO AN ENTRY
-- (`Emitted.em-guard`, D454).
--
-- An entry of the image (a block's, a trampoline's) is preceded by an
-- instruction that does not fall through: a jump, a return, or the
-- program's leave. As a relation between neighbours (`Linked`, stdlib): `R x
-- y` = "if `y` is an entry, `x` is a guard". The lowered code holds no entry
-- (`LabelsC`'s `Ok.ne`), so it is linked whatever its order; what precedes a
-- block is the code before it, which ENDS in a guard: a code ends in its
-- `fin` (a block's `c-ret`, the start's `c-leave`) or, halted, in `c-leave`
-- (D454, `Lower.lowC`); a block in its own code's end; a trampoline in its
-- `c-ret`.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_)
open import Data.List using (List; []; _∷_; _++_; last; head)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Linked using (Linked; []; [-]; _∷_)
import Data.List.Relation.Unary.Linked.Properties
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Binary.Connected using (Connected; just; just-nothing; nothing-just; nothing)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (LabelId; EntryId)
open import Once.CCC.Machine.SMCore

module Once.LinCore.ImageGuard
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Image fmt bw
open import Once.LinCore.Keys fmt bw
open Univ using (tys; nus)
open import Once.LinCore.Layout fmt bw
open import Once.LinCore.Lower fmt bw
open import Once.LinCore.MoveCode using (mvPS; mvSP; mvSS; mvSSd)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.LabelsC fmt ans bw using (module LabsC)

------------------------------------------------------------------------
-- 1. ENTRIES, GUARDS, AND THE RELATION BETWEEN NEIGHBOURS.
------------------------------------------------------------------------

data IsEntry : AbstractInstr → Set where
  is-entry : ∀ {ℓ b} → IsEntry (instr-ctrl (c-entry ℓ b))

-- an instruction that does not fall through
data GuardI : AbstractInstr → Set where
  g-jmp   : ∀ {m} → GuardI (instr-ctrl (c-jmp m))
  g-ret   : ∀ {b} → GuardI (instr-ctrl (c-ret b))
  g-leave : GuardI (instr-ctrl c-leave)

R : AbstractInstr → AbstractInstr → Set
R x y = IsEntry y → GuardI x

-- a code that ends in a guard (a data type, so that its index is injective:
-- `last` is not)
data LastG (xs : AbstractTrace) : Set where
  lg : ∀ {x} → last xs ≡ just x → GuardI x → LastG xs

infixr 5 ▸_
▸_ : ∀ {x ys} → LastG ys → LastG (x ∷ ys)
▸_ {ys = []}     (lg () _)
▸_ {ys = y ∷ ys} (lg e g) = lg e g

lastG-cat : ∀ xs {ys} → LastG ys → LastG (xs ++ ys)
lastG-cat []       g = g
lastG-cat (x ∷ xs) g = ▸ lastG-cat xs g

ends-ret : ∀ {b} → LastG (instr-ctrl (c-ret b) ∷ [])
ends-ret = lg refl g-ret

-- after a guard, anything
con-g : ∀ {x} → GuardI x → ∀ my → Connected R (just x) my
con-g g (just y) = just (λ _ → g)
con-g g nothing  = just-nothing

con-last : ∀ {xs} → LastG xs → ∀ ys → Connected R (last xs) (head ys)
con-last {xs} (lg e g) ys = subst (λ z → Connected R z (head ys)) (sym e) (con-g g (head ys))

------------------------------------------------------------------------
-- 2. ★ ON A MACHINE: code without entries, the lowering's ends.
------------------------------------------------------------------------

module G {FS : FrameSemantics} where
  open FlatMachine {FS} using (entry-of?; fetch)
  open NoLabels {FS} using (NoLab; mark-e; mvSS-nl; mvSSd-nl; mvPS-nl; mvSP-nl; module Free)
  open LabsC {FS} using (Ents; ent; Ok; module Ok; module C)

  NE : AbstractInstr → Set
  NE x = entry-of? x ≡ nothing

  ne-not : ∀ {y} → NE y → IsEntry y → ⊥
  ne-not e is-entry = j≢n e
    where j≢n : ∀ {e′ : EntryId} → _≡_ {A = Maybe EntryId} (just e′) nothing → ⊥
          j≢n ()

  nl→ne : ∀ {xs} → NoLab xs → All NE xs
  nl→ne = Data.List.Relation.Unary.All.map (λ {x} e → mark-e x e)

  ents→ne : ∀ xs → Ents xs ≡ [] → All NE xs
  ents→ne []       _ = []
  ents→ne (x ∷ xs) e = ne-go (entry-of? x) refl e
    where ne-go : ∀ mo → entry-of? x ≡ mo → ent mo (Ents xs) ≡ [] → All NE (x ∷ xs)
          ne-go nothing  ex e′ = ex ∷ ents→ne xs e′
          ne-go (just _) ex ()

  -- an entry, then code without entries
  lk-cons : ∀ x {xs} → All NE xs → Linked R (x ∷ xs)
  lk-cons x []         = [-]
  lk-cons x (ny ∷ nys) = (λ ie → ⊥-elim (ne-not ny ie)) ∷ lk-cons _ nys

  module L (U : Univ)
           (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing) where
    open In U
    open Lowering U ncty ldConst
    open C U ncty ldConst ld-nl using (lowC-ok)
    open Free U ncty ldConst ld-nl using (TrampShape; tramp-nl; view-nl)

    -- the lowered code holds no entry
    lowC-ne : ∀ φ j m fin → NoLab fin → ∀ {sh T} (c : Codeᴵ sh T) (ev : CIn c) → All NE (proj₁ (lowC φ j m fin c ev))
    lowC-ne φ j m fin nf c ev = ents→ne _ (Ok.ne (proj₂ (lowC-ok φ j m fin nf c ev)))

    -- ★ the lowered code ends as its `fin` does, or, halted, in `c-leave`
    lowC-last : ∀ φ j m fin → LastG fin → ∀ {sh T} (c : Codeᴵ sh T) (ev : CIn c) → LastG (proj₁ (lowC φ j m fin c ev))
    lowC-last φ j m fin g end ev    = g
    lowC-last φ j m fin g halted ev = lg refl g-leave
    lowC-last φ j m fin g (i ⨾ c) (ei , ec) =
      lastG-cat (proj₁ (lowI φ j m i ei)) (lowC-last φ j (proj₂ (lowI φ j m i ei)) fin g c ec)
    lowC-last φ j m fin g (case {Es} {A} {B} {S} c₁ c₂) (e₁ , e₂) =
      let t = Tp φ ((A ⊕t B) ∷ S) ; bot = Tp φ S ; l₂ = lowC φ j (suc m) fin c₂ e₂
      in ▸ ▸ ▸ lastG-cat (mvSSd (suc t) (bot ∸ wsz B) (wsz B))
           (lastG-cat (proj₁ l₂) (▸ lastG-cat (mvSSd (suc t) (bot ∸ wsz A) (wsz A)) (lowC-last φ j (proj₂ l₂) fin g c₁ e₁)))
    lowC-last φ j m fin g (ecase {E₁} {E₂} {Es} c₁ c₂) (e₁ , e₂) =
      let e = ws Es ; nb = e + wsz (E₁ ⊕t E₂) ; l₂ = lowC φ j (suc m) fin c₂ e₂
      in ▸ ▸ ▸ lastG-cat (mvSS (suc e) nb (wsz E₂))
           (lastG-cat (proj₁ l₂) (▸ lastG-cat (mvSS (suc e) nb (wsz E₁)) (lowC-last φ j (proj₂ l₂) fin g c₁ e₁)))

    -- ★ a block: its entry, then no entry; it ends in its `c-ret` (or a halt's `c-leave`)
    lowBlock-lk : ∀ {σ} j (κ : Key σ) (ev : CIn (blockᴵ κ)) → Linked R (lowBlock j κ ev)
    lowBlock-lk {bsig t A B} j κ ev =
      let φ = frameOf (blockᴵ κ) ; M = wsz A ⊔ wsz B
      in lk-cons _ (refl ∷ refl ∷ refl ∷ ++⁺ (nl→ne (mvPS-nl (M ∸ wsz A) (Tp φ (A ∷ [])) (wsz A)))
                     (++⁺ (nl→ne (view-nl t φ))
                       (lowC-ne φ j 0 _ (refl ∷ ++⁺ (mvSP-nl (Tp φ (B ∷ [])) (M ∸ wsz B) (wsz B)) (refl ∷ [])) (blockᴵ κ) ev)))

    lowBlock-last : ∀ {σ} j (κ : Key σ) (ev : CIn (blockᴵ κ)) → LastG (lowBlock j κ ev)
    lowBlock-last {bsig t A B} j κ ev =
      let φ = frameOf (blockᴵ κ) ; M = wsz A ⊔ wsz B
      in ▸ ▸ ▸ ▸ lastG-cat (mvPS (M ∸ wsz A) (Tp φ (A ∷ [])) (wsz A))
           (lastG-cat (view-in t φ)
             (lowC-last φ j 0 _ (▸ lastG-cat (mvSP (Tp φ (B ∷ [])) (M ∸ wsz B) (wsz B)) ends-ret) (blockᴵ κ) ev))

    -- ★ a trampoline: none, or one that ends in its `c-ret`
    tramp-last : ∀ {σ} j (κ : Key σ) → tramp j κ ≡ [] ⊎ LastG (tramp j κ)
    tramp-last j (kbody1 {X = X} {A = A} {B = B} ds b γ) =
      let wX = wsz X ; wA = wsz A ; wB = wsz B ; M = (wX + wA) ⊔ wB ; Mc = suc wA ⊔ wB ; a = M ∸ (wX + wA)
      in inj₂ (▸ ▸ ▸ ▸ lastG-cat (mvPS hdr a wX) (▸ lastG-cat (mvPS (Mc ∸ wA) (a + wX) wA)
               (▸ ▸ ▸ ▸ ▸ ▸ lastG-cat (mvSP (M ∸ wB) (Mc ∸ wB) wB) ends-ret)))
    tramp-last j (kbodyω ds b γ) = inj₂ (lg refl g-ret)
    tramp-last j (kobs ds F S) =
      let wP = wsz (cty (F , S)) ; wL = wsz (LF∙ F (Nu F)) ; M = wP ⊔ wL ; Mc = 1 ⊔ wL
      in inj₂ (▸ ▸ ▸ ▸ lastG-cat (mvPS hdr (M ∸ wP) wP) (▸ ▸ ▸ ▸ ▸ ▸ lastG-cat (mvSP (M ∸ wL) (Mc ∸ wL) wL) ends-ret))
    tramp-last j (kcopy T₀) =
      inj₂ (▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ ▸ lastG-cat (mvSP 0 hdr (wsz T₀)) (lg refl g-ret))
    tramp-last j (kfree T₀) = inj₂ (▸ ▸ ▸ lastG-cat (mvPS hdr 0 (wsz T₀)) (lg refl g-ret))
    tramp-last j (kfold ds F alg) = inj₁ refl
    tramp-last j (ktr1 ds b γ) = inj₁ refl
    tramp-last j (ktrω ds b γ) = inj₁ refl
    tramp-last j (ktro ds F S) = inj₁ refl
    tramp-last j (ktrc X C)    = inj₁ refl
    tramp-last j (ktrf X C)    = inj₁ refl

    lk-tr : ∀ {j xs ys} → TrampShape j xs → (xs ≡ [] ⊎ LastG xs) → Linked R ys → Linked R (xs ++ ys)
    lk-tr (inj₁ refl) _ l = l
    lk-tr (inj₂ (b , r , refl , nl)) (inj₁ ()) l
    lk-tr {ys = ys} (inj₂ (b , r , refl , nl)) (inj₂ g) l =
      Data.List.Relation.Unary.Linked.Properties.++⁺ (lk-cons _ (nl→ne nl)) (con-last g ys) l

    -- ★ the blocks: each one's entry follows a guard
    blocks-lk : ∀ (ks : List AKey) (ev : ∀ {κ} → κ ∈ ks → BIn κ) j → Linked R (blocksOf ks ev j)
    blocks-lk []             ev j = []
    blocks-lk ((σ , κ) ∷ ks) ev j =
      Data.List.Relation.Unary.Linked.Properties.++⁺ (lowBlock-lk j κ (ev (here refl)))
        (con-last (lowBlock-last j κ (ev (here refl))) (tramp j κ ++ blocksOf ks (λ q → ev (there q)) (suc j)))
        (lk-tr (tramp-nl j κ) (tramp-last j κ) (blocks-lk ks (λ q → ev (there q)) (suc j)))

  ----------------------------------------------------------------------
  -- 3. ★ THE IMAGE.
  ----------------------------------------------------------------------

  -- neighbours in a linked trace
  linked-at : ∀ {xs} (l : Linked R xs) q {x y} → fetch xs q ≡ just x → fetch xs (suc q) ≡ just y → R x y
  linked-at []      q       ()   _
  linked-at [-]     zero    refl ()
  linked-at [-]     (suc q) ()   _
  linked-at (r ∷ l) zero    refl refl = r
  linked-at (r ∷ l) (suc q) ex   ey   = linked-at l q ex ey

  fetch-pred : ∀ xs q {y} → fetch xs (suc q) ≡ just y → Σ AbstractInstr λ x → fetch xs q ≡ just x
  fetch-pred []       q       ()
  fetch-pred (x ∷ xs) zero    _ = x , refl
  fetch-pred (x ∷ xs) (suc q) e = fetch-pred xs q e

  module Img {Γ} (ds : Defs Γ) (f : LTm Γ One One)
             (ldConst : ∀ {b} → Lit b → AbstractInstr)
             (ld-nl : ∀ {b} (v : Lit b) → NoLabels.mark {FS} (ldConst v) ≡ nothing) where
    open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
    open Program ds f using (U; blocks-in; start-in)
    open Program ds f using (ncty)
    open Program′ ds f ldConst
    open Lowering U ncty ldConst
    open L U ncty ldConst ld-nl

    main = compᴵ ds f {[]} {[]} end
    φ₀ = frameOf main

    image-lk : Linked R image
    image-lk =
      Data.List.Relation.Unary.Linked.Properties.++⁺
        {xs = instr-ctrl (c-start (fbudget φ₀)) ∷ proj₁ (lowC φ₀ j₀ 0 (instr-ctrl c-leave ∷ []) main (start-in {[]} {[]} tt))}
        (lk-cons _ (lowC-ne φ₀ j₀ 0 _ (refl ∷ []) main (start-in {[]} {[]} tt)))
        (con-last (▸ lowC-last φ₀ j₀ 0 _ (lg refl g-leave) main (start-in {[]} {[]} tt)) (blocksOf (allK U) blocks-in 0))
        (blocks-lk (allK U) blocks-in 0)

    -- ★ `Emitted.em-guard`: an entry follows a jump, a return or the leave
    em-guard : ∀ p (ℓ : EntryId) (bb : ℕ) → fetch image p ≡ just (instr-ctrl (c-entry ℓ bb))
             → Σ ℕ (λ q → (p ≡ suc q)
                   × ((Σ LabelId (λ m → fetch image q ≡ just (instr-ctrl (c-jmp m))))
                      ⊎ (Σ ℕ (λ b → fetch image q ≡ just (instr-ctrl (c-ret b))))
                      ⊎ (fetch image q ≡ just (instr-ctrl c-leave))))
    em-guard zero    ℓ bb ()
    em-guard (suc q) ℓ bb e =
      q , refl , to-sum (proj₂ (fetch-pred image q e)) (linked-at image-lk q (proj₂ (fetch-pred image q e)) e is-entry)
      where
        to-sum : ∀ {x} → fetch image q ≡ just x → GuardI x
               → (Σ LabelId (λ m → fetch image q ≡ just (instr-ctrl (c-jmp m))))
                 ⊎ (Σ ℕ (λ b → fetch image q ≡ just (instr-ctrl (c-ret b))))
                 ⊎ (fetch image q ≡ just (instr-ctrl c-leave))
        to-sum ex g-jmp   = inj₁ (_ , ex)
        to-sum ex g-ret   = inj₂ (inj₁ (_ , ex))
        to-sum ex g-leave = inj₂ (inj₂ ex)
