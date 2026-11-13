-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.CallStep — plan 0.146 B1.4b (D417, step 3): ★ A CALL, in
-- the image.
--
-- At a path `s` of a root, `call κ ⨾ k` lowers to the caller's argument
-- area into `Input1` and the call of `nameOf (idx p)`, where `p` is the
-- membership the call was lowered with; the image's block `p` is there
-- (`image-fn`), its entry, saves and prologue first (`lowBlock`). The flat
-- run goes `Here` at `s` to `Here` at the callee's start, in the callee's
-- frame, and what the return needs is `Called`: the return pc the address
-- of `k`, the caller's frame saved and every slot of it kept, the callee's
-- first save slot the caller's area, the heap counter and the old heap
-- kept.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_)
open import Data.Nat.Properties using (+-comm; +-suc; ≤-refl; ≤-trans; m≤n+m)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (false)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.CallStep
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; see; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.Keys fmt ans bw
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Lower fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.LowerSimF fmt ans bw using (module SimF)
open import Once.LinCore.ImagePt fmt ans bw using (Sub; whole; next)
open import Once.LinCore.LowAt fmt ans bw using (Inside; in-trans; in-l; module At)
open import Once.LinCore.Labels fmt ans bw using (module NoLabels)
open import Once.LinCore.EntriesI fmt ans bw using (module ImgE)
open import Once.LinCore.PointAt fmt ans bw using (module Ctl; module Fetch)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
open import Once.LinCore.KeysRun fmt ans bw using (module ProgramRun)
import Once.LinCore.Moves

------------------------------------------------------------------------
-- 1. WHAT A CALL LEAVES FOR ITS RETURN.
------------------------------------------------------------------------

module Frames {FS : FrameSemantics} where
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; fret)
  open import Once.LinCore.LowerSimE {FS} using (callee-frame)
  open import Once.LinCore.Moves {FS} using (slot; Old)

  -- the return pc `r`, the callee's budget `b`, its first save slot `sv`, the caller's area `area`
  record Called (fs fs′ : FlatState) (r b sv area : ℕ) : Set where
    field
      cd-ret    : fret fs′ ≡ r ∷ fret fs
      cd-saved  : AllocState.saved-frames (falloc fs′)
                  ≡ (AllocState.current-frame (falloc fs) , AllocState.frame-slots (falloc fs)) ∷ AllocState.saved-frames (falloc fs)
      cd-frame  : AllocState.current-frame (falloc fs′) ≡ callee-frame (AllocState.current-frame (falloc fs)) b
      cd-others : ∀ f′ x → ¬ callee-frame (AllocState.current-frame (falloc fs)) b ≡ f′
                → LocState.stackMem (floc fs′) f′ x ≡ LocState.stackMem (floc fs) f′ x
      cd-area   : slot fs′ sv ≡ just (SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) area))
      cd-next   : AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs)
      cd-old    : Old (AllocState.next-heap-ref (falloc fs)) fs fs′

------------------------------------------------------------------------
-- 2. ★ THE CALL, from any root of the image to a block.
------------------------------------------------------------------------

module Calls {FS : FrameSemantics} {Γ} (ds : Defs Γ) (f : LTm Γ One One)
             (ldConst : ∀ {b} → ⟦ b ⟧b → AbstractInstr)
             (ld-nl : ∀ {b} (v : ⟦ b ⟧b) → NoLabels.mark {FS} (ldConst v) ≡ nothing)
             (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Ctl {FS} ds f ldConst ld-nl using (L₀ᵇ; block-root; blockFin)
  open Program ds f using (U; blocks-in)
  open ProgramRun ds f using (ncty)
  open Program′ ds f ldConst using (image)
  open In U
  open Lowering U ncty ldConst
  open ImgE {FS} ds f ldConst ld-nl using (image-at; image-fn)
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf using (len-mvPS; ≤∸; slots-frame; topW)
  open SimF {FS} U wordOf using (enter-n; enter-j; leave)
  open Fetch {FS} using (in-seg)
  open Frames {FS}
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc; fret)
  open FlatStepsAPI {FS} using (FlatSteps; FlatSteps-++)
  open import Once.LinCore.LowerSimE {FS}
    using (CallIn; call-in; call-in-v; callee-frame; callee-≢; ci-frame; ci-saved; ci-ret; ci-pc; ci-in; ci-s₁; ci-s₂; ci-other; ci-heap; ci-next; ci-halt; CallOut; co-pc; co-halt)
  open import Once.LinCore.Moves {FS}
    using (Seg; Seg-++ˡ; slot; Ran; r-keep; r-pc; r-next; r-old; k-halt; k-ret; k-saved; k-frame; k-other)

  -- a block's code, inside the image
  blockR : ∀ {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) → Inside image (At.code U ncty ldConst (frameOf (blockᴵ κ)) (idx p) (L₀ᵇ κ p))
  blockR {κ = κ} p = in-trans (in-trans (image-at p) (in-l _ _)) (block-root (idx p) κ (blocks-in p))

  -- the callee, at its block's root
  module K {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = Loc {FS} U ncty ldConst wordOf image (blockᴵ κ) (idx p) (L₀ᵇ κ p) (blockR p)

  private
    sv-ne : ∀ n → ¬ n ≡ suc n
    sv-ne n ()

    shuffle : ∀ x p → x + suc (suc (suc (suc p))) ≡ p + suc (suc (suc (suc x)))
    shuffle = solve-∀

    -- the callee's start: past the entry, its saves and the argument's copy
    start-len : ∀ (P X : AbstractTrace) a b c d → length (((P ++ []) ++ (a ∷ b ∷ c ∷ d ∷ (X ++ []))) ++ []) ≡ length P + suc (suc (suc (suc (length X))))
    start-len P X a b c d =
      trans (cong length (++-identityʳ ((P ++ []) ++ (a ∷ b ∷ c ∷ d ∷ (X ++ [])))))
        (trans (cong (λ z → length (z ++ (a ∷ b ∷ c ∷ d ∷ (X ++ [])))) (++-identityʳ P))
          (trans (length-++ P) (cong (λ z → length P + suc (suc (suc (suc z)))) (cong length (++-identityʳ X)))))

    -- the caller's argument, at its area's offset
    area-at : ∀ B wA wB s → wA + s ≤ B → wB + s ≤ B → ((wA ⊔ wB) ∸ wA) + ((B ∸ s) ∸ (wA ⊔ wB)) ≡ B ∸ (wA + s)
    area-at B wA wB s le₁ le₂ = trans (+-comm ((wA ⊔ wB) ∸ wA) _)
      (trans (sym (Data.Nat.Properties.+-∸-assoc ((B ∸ s) ∸ (wA ⊔ wB)) (Data.Nat.Properties.m≤m⊔n wA wB)))
        (trans (cong (_∸ wA) (Data.Nat.Properties.m∸n+n≡m M≤))
          (trans (Data.Nat.Properties.∸-+-assoc B s wA) (cong (B ∸_) (+-comm s wA)))))
      where
        import Data.Nat.Properties
        M≤ : wA ⊔ wB ≤ B ∸ s
        M≤ = Data.Nat.Properties.⊔-lub (≤∸ wA s B le₁) (≤∸ wB s B le₂)


  ----------------------------------------------------------------------
  -- the block's code, by its parts (no view read)
  ----------------------------------------------------------------------

  module Callee {A B} {κ : Key (bsig nothing A B)} (p : (bsig nothing A B , κ) ∈ allK U) where
    φ′ : Frame
    φ′ = frameOf (blockᴵ κ)
    q : ℕ
    q = length (proj₁ (image-at p))
    M : ℕ
    M = wsz A ⊔ wsz B
    dst : ℕ
    dst = budget φ′ ∸ ws (A ∷ [])
    argMv : AbstractTrace
    argMv = mvPS (M ∸ wsz A) dst (wsz A)
    body : AbstractTrace
    body = proj₁ (lowC φ′ (idx p) 0 (blockFin κ) (blockᴵ κ) (blocks-in p))
    entry : AbstractTrace
    entry = instr-ctrl (c-entry (e-fn (nameOf (idx p))) (fbudget φ′)) ∷ store-at-slot (sv₂ φ′) ∷ mov-to-output ∷ store-at-slot (sv₁ φ′) ∷ []

    whole-seg : Seg image q (entry ++ ((argMv ++ ([] ++ body)) ++ tramp (idx p) κ))
    whole-seg = in-seg (image-at p)

    entry-seg : Seg image q entry
    entry-seg = Seg-++ˡ image q entry ((argMv ++ ([] ++ body)) ++ tramp (idx p) κ) whole-seg

    arg-seg : Seg image (suc (suc (suc (suc q)))) argMv
    arg-seg = Seg-++ˡ image _ argMv ([] ++ body)
                (Seg-++ˡ image _ (argMv ++ ([] ++ body)) (tramp (idx p) κ)
                  (proj₂ (proj₂ (proj₂ (proj₂ whole-seg)))))

    -- the callee's start
    start-pos : K.pos p whole ≡ q + suc (suc (suc (suc (Once.LinCore.Moves.ln {FS} (wsz A)))))
    start-pos = trans (start-len (proj₁ (image-at p)) argMv _ _ _ _)
                  (cong (λ z → q + suc (suc (suc (suc z)))) (len-mvPS (M ∸ wsz A) dst (wsz A)))

  private
    seg-join : ∀ {pc} (xs ys : AbstractTrace) → Seg image pc xs → Seg image (pc + length xs) ys → Seg image pc (xs ++ ys)
    seg-join {pc} []       ys tt       s = subst (λ z → Seg image z ys) (Data.Nat.Properties.+-identityʳ pc) s
      where import Data.Nat.Properties
    seg-join {pc} (x ∷ xs) ys (e , sx) s = e , seg-join {suc pc} xs ys sx (subst (λ z → Seg image z ys) (+-suc pc (length xs)) s)

    start-len-v : ∀ (P X V : AbstractTrace) a b c d
                → length (((P ++ []) ++ (a ∷ b ∷ c ∷ d ∷ (X ++ V))) ++ []) ≡ length P + suc (suc (suc (suc (length X + length V))))
    start-len-v P X V a b c d =
      trans (cong length (++-identityʳ ((P ++ []) ++ (a ∷ b ∷ c ∷ d ∷ (X ++ V)))))
        (trans (cong (λ z → length (z ++ (a ∷ b ∷ c ∷ d ∷ (X ++ V)))) (++-identityʳ P))
          (trans (length-++ P) (cong (λ z → length P + suc (suc (suc (suc z)))) (length-++ X))))

    shuffle-v : ∀ x y p → (x + suc y) + suc (suc (suc (suc p))) ≡ p + suc (suc (suc (suc (x + suc y))))
    shuffle-v = solve-∀

  -- the code of a block that reads the caller's top view, by its parts
  module CalleeV {E A B} {κ : Key (bsig (just E) A B)} (p : (bsig (just E) A B , κ) ∈ allK U) where
    φ′ : Frame
    φ′ = frameOf (blockᴵ κ)
    q : ℕ
    q = length (proj₁ (image-at p))
    M : ℕ
    M = wsz A ⊔ wsz B
    dst : ℕ
    dst = budget φ′ ∸ ws (A ∷ [])
    argMv : AbstractTrace
    argMv = mvPS (M ∸ wsz A) dst (wsz A)
    viewMv : AbstractTrace
    viewMv = restore-input (sv₂ φ′) ∷ mvPS 0 0 (wsz E)
    body : AbstractTrace
    body = proj₁ (lowC φ′ (idx p) 0 (blockFin κ) (blockᴵ κ) (blocks-in p))
    entry : AbstractTrace
    entry = instr-ctrl (c-entry (e-fn (nameOf (idx p))) (fbudget φ′)) ∷ store-at-slot (sv₂ φ′) ∷ mov-to-output ∷ store-at-slot (sv₁ φ′) ∷ []

    whole-seg : Seg image q (entry ++ ((argMv ++ (viewMv ++ body)) ++ tramp (idx p) κ))
    whole-seg = in-seg (image-at p)

    entry-seg : Seg image q entry
    entry-seg = Seg-++ˡ image q entry ((argMv ++ (viewMv ++ body)) ++ tramp (idx p) κ) whole-seg

    pro-seg : Seg image (suc (suc (suc (suc q)))) (argMv ++ viewMv)
    pro-seg =
      let s₀ = Seg-++ˡ image _ (argMv ++ (viewMv ++ body)) (tramp (idx p) κ) (proj₂ (proj₂ (proj₂ (proj₂ whole-seg)))) in
      seg-join argMv viewMv (Seg-++ˡ image _ argMv (viewMv ++ body) s₀)
        (Seg-++ˡ image _ viewMv body (Once.LinCore.Moves.Seg-++ʳ {FS} image _ argMv (viewMv ++ body) s₀))

    start-pos : K.pos p whole ≡ q + suc (suc (suc (suc (Once.LinCore.Moves.ln {FS} (wsz A) + suc (Once.LinCore.Moves.ln {FS} (wsz E))))))
    start-pos = trans (start-len-v (proj₁ (image-at p)) argMv viewMv _ _ _ _)
                  (cong (λ z → q + suc (suc (suc (suc z))))
                    (cong₂ _+_ (len-mvPS (M ∸ wsz A) dst (wsz A)) (cong suc (len-mvPS 0 0 (wsz E)))))

  -- ★ THE CALL of a block that reads no view
  module From {sh₀ U₀} (root : Codeᴵ sh₀ U₀) (j : ℕ)
              (L₀ : At.Low U ncty ldConst (frameOf root) j root)
              (R : Inside image (At.code U ncty ldConst (frameOf root) j L₀)) where
    module C = Loc {FS} U ncty ldConst wordOf image root j L₀ R
    module CA = At U ncty ldConst (frameOf root) j
    open Loc.Here

    -- the membership the call was lowered with
    callee : ∀ {σ Es S V} {κ : Key σ} {k : Codeᴵ (top σ ⊳ Es ∣ cod σ ∷ S) V} → Sub root (call κ ⨾ k) → (σ , κ) ∈ allK U
    callee s = proj₁ (CA.lcin (C.lowAt s))

    -- what the call leaves
    Into : ∀ {A B Es S V} {κ : Key (bsig nothing A B)} {k : Codeᴵ (Es ∣ B ∷ S) V} → Sub root (call κ ⨾ k) → MV A → FlatState → Set
    Into {A} {B} {S = S} {κ = κ} s a fs =
      Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
        × K.Here (callee s) whole ([]ᵉ ∥ a ∷ˢ []ˢ) fs′
        × Called fs fs′ (C.pos (next s)) (fbudget (frameOf (blockᴵ κ))) (sv₁ (frameOf (blockᴵ κ))) (Tp C.φ S ∸ (wsz A ⊔ wsz B))

    call-n : ∀ {A B Es S V} {κ : Key (bsig nothing A B)} {k : Codeᴵ (Es ∣ B ∷ S) V} (s : Sub root (call κ ⨾ k))
               {es : Slots Es} {a : MV A} {os : Stk S} {fs}
           → C.Here s (es ∥ a ∷ˢ os) fs → Into s a fs
    call-n {A} {B} {Es} {S} {κ = κ} s {es} {a} {os} {fs} H = with-arg (Rel.CfgW.c-stk (h-cfg H))
      where
        p = callee s
        open Callee p
        b = fbudget φ′
        area = Tp C.φ S ∸ M
        cf = AllocState.current-frame (falloc fs)
        seg : Seg image (fpc fs) (lea-slot area ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ [])
        seg = Seg-++ˡ image (fpc fs) (lea-slot area ∷ mov-to-input ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ []) _ (C.seg-at s H)
        fitsB : ws (A ∷ S) ≤ budget C.φ
        fitsB = ≤-trans (Rel.CfgW.c-sfit (h-cfg H)) (m≤n+m (OP C.φ) (EP C.φ))
        fitsB′ : ws (B ∷ S) ≤ budget C.φ
        fitsB′ = ≤-trans (proj₂ (C.shape-fits (next s))) (m≤n+m (OP C.φ) (EP C.φ))
        with-arg : StkW (LocState.heapMem (floc fs)) (slot fs) C.φ (a ∷ˢ os) → Into s a fs
        with-arg ((wa , pa , sa) , _) =
          fin (call-in image fs area (nameOf (idx p)) (e-fn (nameOf (idx p))) q b (sv₁ φ′) (sv₂ φ′)
                 (sv-ne (budget φ′)) seg (image-fn p) entry-seg (h-run H))
          where
            fin : Σ FlatState (λ fs₁ → FlatSteps image 7 fs fs₁
                    × CallIn fs fs₁ area b (sv₁ φ′) (sv₂ φ′) q (suc (suc (suc (fpc fs)))) (SV-Ptr (AtStack cf area)))
                → Into s a fs
            fin (fs₁ , st₁ , CI) = fin₂ (enter-n image fs₁ φ′ cf area (M ∸ wsz A) wa ne₁ (ci-in CI) pa₁ sa₁ seg₂ h₁
                                           (proj₂ (K.shape-fits p whole)))
              where
                ne₁ : ¬ AllocState.current-frame (falloc fs₁) ≡ cf
                ne₁ e′ = callee-≢ cf b (trans (sym (ci-frame CI)) e′)
                h₁ : LocState.halted (floc fs₁) ≡ false
                h₁ = trans (ci-halt CI) (h-run H)
                pa₁ : VW (LocState.heapMem (floc fs₁)) a wa
                pa₁ = subst (λ r → VW r a wa) (sym (ci-heap CI)) pa
                sa₁ : SlotsAt (LocState.stackMem (floc fs₁) cf) ((M ∸ wsz A) + area) wa
                sa₁ = slots-frame {LocState.stackMem (floc fs) cf} {LocState.stackMem (floc fs₁) cf} wa
                        (λ k _ → ci-other CI cf (k + ((M ∸ wsz A) + area)) (callee-≢ cf b))
                        (subst (λ z → SlotsAt (LocState.stackMem (floc fs) cf) z wa)
                           (sym (area-at (budget C.φ) (wsz A) (wsz B) (ws S) fitsB fitsB′)) sa)
                seg₂ : Seg image (fpc fs₁) argMv
                seg₂ = subst (λ z → Seg image z argMv) (sym (ci-pc CI)) arg-seg
                fin₂ : Σ FlatState (λ fs₂ → FlatSteps image (Once.LinCore.Moves.ln {FS} (wsz A)) fs₁ fs₂
                         × CfgW (LocState.heapMem (floc fs₂)) (slot fs₂) φ′ ([]ᵉ ∥ a ∷ˢ []ˢ)
                         × Ran (Once.LinCore.Moves.ln {FS} (wsz A)) 0 (AllocState.next-heap-ref (falloc fs₁)) fs₁ fs₂
                         × (∀ x → budget φ′ ≤ x → slot fs₂ x ≡ slot fs₁ x))
                     → Into s a fs
                fin₂ (fs₂ , st₂ , C₂ , Rn , top) =
                  _ , fs₂ , FlatSteps-++ st₁ st₂ ,
                  record { h-pc  = trans (r-pc Rn) (trans (cong (Once.LinCore.Moves.ln {FS} (wsz A) +_) (ci-pc CI))
                                     (trans (shuffle _ q) (sym start-pos)))
                         ; h-run = trans (k-halt (r-keep Rn)) h₁
                         ; h-cfg = C₂ } ,
                  record { cd-ret    = trans (k-ret (r-keep Rn)) (trans (ci-ret CI)
                                         (cong (_∷ fret fs) (trans (cong (λ z → suc (suc (suc z))) (h-pc H))
                                           (trans (+-comm 3 (C.pos s)) (sym (C.pos-next s))))))
                         ; cd-saved  = trans (k-saved (r-keep Rn)) (ci-saved CI)
                         ; cd-frame  = trans (k-frame (r-keep Rn)) (ci-frame CI)
                         ; cd-others = λ f′ x ne → trans (k-other (r-keep Rn) f′ x (λ e′ → ne (trans (sym (ci-frame CI)) (sym e′))))
                                                         (ci-other CI f′ x ne)
                         ; cd-area   = trans (top (sv₁ φ′) ≤-refl)
                                         (subst (λ g → LocState.stackMem (floc fs₁) g (sv₁ φ′) ≡ just (SV-Ptr (AtStack cf area)))
                                                (sym (ci-frame CI)) (ci-s₁ CI))
                         ; cd-next   = trans (r-next Rn) (ci-next CI)
                         ; cd-old    = λ hl lt → trans (r-old Rn hl (subst (_ <_) (sym (ci-next CI)) lt)) (cong (λ h → h hl) (ci-heap CI)) }

    -- ★ THE CALL of a block that reads the caller's top view
    IntoV : ∀ {E A B Es S V} {κ : Key (bsig (just E) A B)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V} → Sub root (call κ ⨾ k)
          → Slots (E ∷ Es) → MV A → FlatState → Set
    IntoV {E} {A} {B} {S = S} {κ = κ} s es a fs =
      Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′
        × K.Here (callee s) whole (vw (see es) []ᵉ ∥ a ∷ˢ []ˢ) fs′
        × Called fs fs′ (C.pos (next s)) (fbudget (frameOf (blockᴵ κ))) (sv₁ (frameOf (blockᴵ κ))) (Tp C.φ S ∸ (wsz A ⊔ wsz B))

    call-v : ∀ {E A B Es S V} {κ : Key (bsig (just E) A B)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) V} (s : Sub root (call κ ⨾ k))
               {es : Slots (E ∷ Es)} {a : MV A} {os : Stk S} {fs}
           → C.Here s (es ∥ a ∷ˢ os) fs → IntoV s es a fs
    call-v {E} {A} {B} {Es} {S} {κ = κ} s {es} {a} {os} {fs} H =
      with-arg (Rel.CfgW.c-stk (h-cfg H)) (topW es (Rel.CfgW.c-env (h-cfg H)))
      where
        p = callee s
        open CalleeV p
        b = fbudget φ′
        area = Tp C.φ S ∸ M
        cf = AllocState.current-frame (falloc fs)
        seg : Seg image (fpc fs) (lea-slot area ∷ mov-to-input ∷ lea-slot (ws Es) ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ [])
        seg = Seg-++ˡ image (fpc fs) (lea-slot area ∷ mov-to-input ∷ lea-slot (ws Es) ∷ instr-ctrl (c-call-fn (nameOf (idx p))) ∷ []) _
                (C.seg-at s H)
        fitsB : ws (A ∷ S) ≤ budget C.φ
        fitsB = ≤-trans (Rel.CfgW.c-sfit (h-cfg H)) (m≤n+m (OP C.φ) (EP C.φ))
        fitsB′ : ws (B ∷ S) ≤ budget C.φ
        fitsB′ = ≤-trans (proj₂ (C.shape-fits (next s))) (m≤n+m (OP C.φ) (EP C.φ))
        with-arg : StkW (LocState.heapMem (floc fs)) (slot fs) C.φ (a ∷ˢ os)
                 → Σ (List W) (λ w → VW (LocState.heapMem (floc fs)) (see es) w × SlotsAt (slot fs) (ws Es) w)
                 → IntoV s es a fs
        with-arg ((wa , pa , sa) , _) (we , pe , se) =
          fin (call-in-v image fs area (ws Es) (nameOf (idx p)) (e-fn (nameOf (idx p))) q b (sv₁ φ′) (sv₂ φ′)
                 (sv-ne (budget φ′)) seg (image-fn p) entry-seg (h-run H))
          where
            fin : Σ FlatState (λ fs₁ → FlatSteps image 8 fs fs₁
                    × CallIn fs fs₁ area b (sv₁ φ′) (sv₂ φ′) q (suc (suc (suc (suc (fpc fs))))) (SV-Ptr (AtStack cf (ws Es))))
                → IntoV s es a fs
            fin (fs₁ , st₁ , CI) =
              fin₂ (enter-j image fs₁ φ′ cf area (M ∸ wsz A) (ws Es) (sv₂ φ′) we wa ne₁ (ci-in CI) sv₂-at
                      (Data.Nat.Properties.n≤1+n (budget φ′)) pa₁ sa₁ pe₁ se₁ seg₂ h₁
                      (proj₁ (K.shape-fits p whole)) (proj₂ (K.shape-fits p whole)))
              where
                import Data.Nat.Properties
                ne₁ : ¬ AllocState.current-frame (falloc fs₁) ≡ cf
                ne₁ e′ = callee-≢ cf b (trans (sym (ci-frame CI)) e′)
                h₁ : LocState.halted (floc fs₁) ≡ false
                h₁ = trans (ci-halt CI) (h-run H)
                kept : ∀ x → LocState.stackMem (floc fs₁) cf x ≡ LocState.stackMem (floc fs) cf x
                kept x = ci-other CI cf x (callee-≢ cf b)
                sv₂-at : slot fs₁ (sv₂ φ′) ≡ just (SV-Ptr (AtStack cf (ws Es)))
                sv₂-at = subst (λ g → LocState.stackMem (floc fs₁) g (sv₂ φ′) ≡ just (SV-Ptr (AtStack cf (ws Es))))
                           (sym (ci-frame CI)) (ci-s₂ CI)
                pa₁ : VW (LocState.heapMem (floc fs₁)) a wa
                pa₁ = subst (λ r → VW r a wa) (sym (ci-heap CI)) pa
                pe₁ : VW (LocState.heapMem (floc fs₁)) (see es) we
                pe₁ = subst (λ r → VW r (see es) we) (sym (ci-heap CI)) pe
                sa₁ : SlotsAt (LocState.stackMem (floc fs₁) cf) ((M ∸ wsz A) + area) wa
                sa₁ = slots-frame {LocState.stackMem (floc fs) cf} {LocState.stackMem (floc fs₁) cf} wa
                        (λ k _ → kept (k + ((M ∸ wsz A) + area)))
                        (subst (λ z → SlotsAt (LocState.stackMem (floc fs) cf) z wa)
                           (sym (area-at (budget C.φ) (wsz A) (wsz B) (ws S) fitsB fitsB′)) sa)
                se₁ : SlotsAt (LocState.stackMem (floc fs₁) cf) (ws Es) we
                se₁ = slots-frame {LocState.stackMem (floc fs) cf} {LocState.stackMem (floc fs₁) cf} we (λ k _ → kept (k + ws Es)) se
                seg₂ : Seg image (fpc fs₁) (argMv ++ viewMv)
                seg₂ = subst (λ z → Seg image z (argMv ++ viewMv)) (sym (ci-pc CI)) pro-seg
                nE = Once.LinCore.Moves.ln {FS} (wsz A) + suc (Once.LinCore.Moves.ln {FS} (wsz E))
                fin₂ : Σ FlatState (λ fs₂ → FlatSteps image nE fs₁ fs₂
                         × CfgW (LocState.heapMem (floc fs₂)) (slot fs₂) φ′ (vw (see es) []ᵉ ∥ a ∷ˢ []ˢ)
                         × Ran nE 0 (AllocState.next-heap-ref (falloc fs₁)) fs₁ fs₂
                         × (∀ x → budget φ′ ≤ x → slot fs₂ x ≡ slot fs₁ x))
                     → IntoV s es a fs
                fin₂ (fs₂ , st₂ , C₂ , Rn , top) =
                  _ , fs₂ , FlatSteps-++ st₁ st₂ ,
                  record { h-pc  = trans (r-pc Rn) (trans (cong (nE +_) (ci-pc CI))
                                     (trans (shuffle-v _ _ q) (sym start-pos)))
                         ; h-run = trans (k-halt (r-keep Rn)) h₁
                         ; h-cfg = C₂ } ,
                  record { cd-ret    = trans (k-ret (r-keep Rn)) (trans (ci-ret CI)
                                         (cong (_∷ fret fs) (trans (cong (λ z → suc (suc (suc (suc z)))) (h-pc H))
                                           (trans (+-comm 4 (C.pos s)) (sym (C.pos-next s))))))
                         ; cd-saved  = trans (k-saved (r-keep Rn)) (ci-saved CI)
                         ; cd-frame  = trans (k-frame (r-keep Rn)) (ci-frame CI)
                         ; cd-others = λ f′ x ne → trans (k-other (r-keep Rn) f′ x (λ e′ → ne (trans (sym (ci-frame CI)) (sym e′))))
                                                         (ci-other CI f′ x ne)
                         ; cd-area   = trans (top (sv₁ φ′) ≤-refl)
                                         (subst (λ g → LocState.stackMem (floc fs₁) g (sv₁ φ′) ≡ just (SV-Ptr (AtStack cf area)))
                                                (sym (ci-frame CI)) (ci-s₁ CI))
                         ; cd-next   = trans (r-next Rn) (ci-next CI)
                         ; cd-old    = λ hl lt → trans (r-old Rn hl (subst (_ <_) (sym (ci-next CI)) lt)) (cong (λ h → h hl) (ci-heap CI)) }

    -- ★ THE RETURN: at the callee's `end` (its way out, `blockFin`), back to
    -- the caller after the call, the result on its stack
    module KA {σ} {κ : Key σ} (p : (σ , κ) ∈ allK U) = At U ncty ldConst (frameOf (blockᴵ κ)) (idx p)

    return : ∀ {t A B Es S V} {κ : Key (bsig t A B)} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) V} (s : Sub root (call κ ⨾ k))
            (e : Sub (blockᴵ κ) (end {sh = t ⊳ [] ∣ B ∷ []}))
            {e′ : Slots (t ⊳ [])} {b : MV B} {es : Slots (t ⊳ Es)} {os : Stk S} {fs}
            (cfc : FrameSemantics.Frame FS) (rest : List ℕ) (sv : List (FrameSemantics.Frame FS × ℕ)) (sl : ℕ)
        → KA.lfin {p = callee s} (K.lowAt (callee s) e) ≡ blockFin κ
        → K.Here (callee s) e (e′ ∥ b ∷ˢ []ˢ) fs
        → fret fs ≡ C.pos (next s) ∷ rest → AllocState.saved-frames (falloc fs) ≡ (cfc , sl) ∷ sv
        → ¬ cfc ≡ AllocState.current-frame (falloc fs)
        → slot fs (sv₁ (frameOf (blockᴵ κ))) ≡ just (SV-Ptr (AtStack cfc (Tp C.φ S ∸ (wsz A ⊔ wsz B))))
        → EnvW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) es
        → StkW (LocState.heapMem (floc fs)) (LocState.stackMem (floc fs) cfc) C.φ os
        → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × C.Here (next s) (es ∥ b ∷ˢ os) fs′
            × CallOut fs fs′ cfc (Tp C.φ S ∸ (wsz A ⊔ wsz B)) (budget (frameOf (blockᴵ κ)) ∸ ws (B ∷ []))
                      ((wsz A ⊔ wsz B) ∸ wsz B) (wsz B) (C.pos (next s)) rest sv sl
    return {t} {A} {B} {Es} {S} {κ = κ} s e {e′} {b} {es} {os} {fs} cfc rest sv sl lf H hret hsv ne ep ev st =
      with-res (Rel.CfgW.c-stk (K.Here.h-cfg {p = callee s} H))
      where
        import Data.Nat.Properties
        p = callee s
        φ′ = frameOf (blockᴵ κ)
        M = wsz A ⊔ wsz B
        fitA : ws (A ∷ S) ≤ OP C.φ
        fitA = proj₂ (C.shape-fits s)
        fitB : ws (B ∷ S) ≤ OP C.φ
        fitB = proj₂ (C.shape-fits (next s))
        fitM : M + ws S ≤ OP C.φ
        fitM = Data.Nat.Properties.≤-trans (Data.Nat.Properties.≤-reflexive (Data.Nat.Properties.+-distribʳ-⊔ (ws S) (wsz A) (wsz B)))
                 (Data.Nat.Properties.⊔-lub fitA fitB)
        seg : Seg image (fpc fs) (restore-input (budget φ′) ∷ mvSP (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B)
                                   ++ instr-ctrl (c-ret (fbudget φ′)) ∷ [])
        seg = subst (Seg image (fpc fs)) lf (K.seg-at p e H)
        with-res : StkW (LocState.heapMem (floc fs)) (slot fs) φ′ (b ∷ˢ []ˢ)
                 → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × C.Here (next s) (es ∥ b ∷ˢ os) fs′
                     × CallOut fs fs′ cfc (Tp C.φ S ∸ M) (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B) (C.pos (next s)) rest sv sl
        with-res ((wb , pb , sb) , _) =
          fin (leave image fs C.φ φ′ cfc (Tp C.φ S ∸ M) M (fbudget φ′) (C.pos (next s)) rest sv sl
                 {es = es} {os = os} {b = b} wb hret hsv ne ep pb sb ev st refl
                 (Data.Nat.Properties.m≤n⊔m (wsz A) (wsz B)) fitM (proj₁ (C.shape-fits (next s))) fitB seg
                 (K.Here.h-run {p = callee s} H))
          where
            fin : Σ FlatState (λ fs′ → FlatSteps image (suc (Once.LinCore.Moves.ln {FS} (wsz B) + 1)) fs fs′
                    × CfgW (LocState.heapMem (floc fs′)) (slot fs′) C.φ (es ∥ b ∷ˢ os)
                    × CallOut fs fs′ cfc (Tp C.φ S ∸ M) (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B) (C.pos (next s)) rest sv sl)
                → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps image N fs fs′ × C.Here (next s) (es ∥ b ∷ˢ os) fs′
                    × CallOut fs fs′ cfc (Tp C.φ S ∸ M) (budget φ′ ∸ ws (B ∷ [])) (M ∸ wsz B) (wsz B) (C.pos (next s)) rest sv sl
            fin (fs′ , st′ , C′ , CO) =
              _ , fs′ , st′ ,
              record { h-pc = co-pc CO ; h-run = trans (co-halt CO) (K.Here.h-run {p = callee s} H) ; h-cfg = C′ } ,
              CO
