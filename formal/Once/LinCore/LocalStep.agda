-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.LocalStep — plan 0.146 B1.4b (D436, step 3): ★ THE LOCAL
-- STEP THEOREM.
--
-- Every image step that stays in its root's code (`Local`: not a call, a
-- return, a loop's turn, a dispatch through a cell, a trampoline's cell
-- part, nor a SigOp — `lop`'s lemma is still owed) takes the flat machine,
-- `Here` at its path, to `Here` at the next path (`succ`), in the steps its
-- lowering takes, keeping what `Keep` says, with the flat heap counter the
-- image's.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; suc; _≤_; _+_)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module Once.LinCore.LocalStep
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; ⟦_⟧b; Lit)
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Code fmt bw using (Sh; _∣_; Stk; _∷ˢ_; Slots; Cfg; _∥_)
open import Once.LinCore.Image fmt bw
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.Keys fmt bw
open Univ using (tys; nus)
open import Once.LinCore.Layout fmt bw using (Frame; frameOf; budget)
open import Once.LinCore.ImagePt fmt ans bw using (Sub; next; left; right; eleft; eright)
open import Once.LinCore.LowAt fmt ans bw using (Inside; module At)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
open import Once.LinCore.StepPrim fmt ans bw using (module Prims)
-- which steps are local: by the code's head
open import Once.LinCore.StepKinds fmt ans bw using (NotOp; Local; LocalC; Motive; LocalCases; local-elim)
open import Once.LinCore.HeldI fmt ans bw using (InvI)
open import Once.LinCore.FreshI fmt ans bw using (module Cells)
open import Once.LinCore.LowerSim fmt ans bw using (module Sim)
open import Once.LinCore.Free using (Weave; cmap-weave; w-run; w-tmp)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Relation.Nullary using (¬_)
open import Data.Sum using ([_,_]′)
open import Once.LinCore.SizedI fmt ans bw using (WSC)
open import Once.LinCore.LiveRun fmt ans bw using (LiveId; FreshAl; StepFx; kt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _++_)
open import Once.LinCore.Held fmt ans bw using (Owned; own; held)
open import Data.Nat using (z≤n; s≤s; _<_)
open import Data.Nat.Properties using (m≤n+m; ≰⇒>; ≤-refl)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
import Level

------------------------------------------------------------------------
-- ★ THE THEOREM, at a root.
------------------------------------------------------------------------

module Steps {FS : FrameSemantics} (U : Univ)
             (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ Univ.cts U)
             (ldConst : ∀ {b} → Lit b → AbstractInstr)
             (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS)
             (prog : AbstractTrace)
             {sh₀ U₀} (root : Codeᴵ sh₀ U₀) (j : ℕ)
             (L₀ : At.Low U ncty ldConst (frameOf root) j root)
             (R : Inside prog (At.code U ncty ldConst (frameOf root) j L₀)) where

  open Loc {FS} U ncty ldConst wordOf prog root j L₀ R
  open Prims {FS} U ncty ldConst wordOf prog root j L₀ R
  open Cells {FS} U wordOf using (apart-top; fresh-cfg)
  open Sim {FS} U wordOf using (cntE; cntS)
  open At U ncty ldConst φ j using (module Low)
  open Low using (lfin; lcin)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc; falloc; fpc)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Once.LinCore.Moves {FS} using (Keep; module Keep; Old; slot; keep-widen; old-widen)

  -- a constant's loader puts its word in `Output` (the image's `ldConst`'s contract)
  LdOk : Set
  LdOk = ∀ {b} (v : Lit b) (fs : FlatState)
       → FlatMachine.flat-exec-instr {FS} (ldConst v) prog fs
         ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (wordOf (lit v)) } ; fpc = suc (fpc fs) }

  -- what a local step gives: the flat steps, `Here` at the next path, the
  -- frames kept, the heap counter the image's
  -- (D471: and the flat run freed only blocks of the step's frees; a
  -- record, so the trace is an index unification can read)

  -- D506: blocks written in place are blocks of cells the next configuration holds
  Held : ∀ {sh} → Cfg sh → List ℕ → Set
  Held m′ wl = ∀ {q} → q ∈ wl → Σ Id λ i → serial i ≡ q × 1 ≤ Owned m′ i

  -- the old blocks as they were, but the frees and the writes (D506)
  OldH : ∀ {sh} → Cfg sh → ℕ → List ℕ → FlatState → FlatState → Set
  OldH m′ lo fl fs fs′ = Σ (List ℕ) λ wl → Held m′ wl × Old lo (wl ++ fl) fs fs′

  Out : ∀ {sh U′} {c : Codeᴵ sh U′} → Sub root c → FlatState → ℕ → Cfg sh → Trace → Set
  Out s′ fs n′ m′ t = Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps prog N fs fs′ × Here s′ m′ fs′ × StepFx t fs fs′
                    × AllocState.next-heap-ref (falloc fs′) ≡ n′ × OldH m′ (AllocState.next-heap-ref (falloc fs)) (freesOf t) fs fs′
                    × (∀ x → budget φ ≤ x → slot fs′ x ≡ slot fs x)

  -- ★ what a local step needs of where it starts: nothing held at or past the
  -- counter; the cells' invariant; every held cell's block live at its id's
  -- size (D471); every held id well-sized; nothing at or past the counter freed
  record LocPre {sh U′ T} (m : Cfg sh) (r : Ret U′ T) (n : ℕ) (fs : FlatState) : Set where
    field
      lp-fresh : Fresh m fs
      lp-heap  : Id → ℕ
      lp-inv   : InvI m r n lp-heap
      lp-live  : ∀ i → 1 ≤ cntE (Cfg.envs m) i + cntS (Cfg.opds m) i → LiveId (falloc fs) i
      lp-ws    : WSC m
      lp-fal   : FreshAl (falloc fs)
  open LocPre

  private
    out0 : ∀ {sh U′} {c : Codeᴵ sh U′} {s′ : Sub root c} {fs n m′ fl t} → Moved s′ fs [] fl m′
         → (∀ {q} → q ∈ fl → q ∈ freesOf t) → (∀ {q} → q ∈ fl → q < AllocState.next-heap-ref (falloc fs))
         → (∀ i → ¬ alloc i ∈ t)
         → AllocState.next-heap-ref (falloc fs) ≡ n → Out s′ fs n m′ t
    out0 {fs = fs} {fl = fl} {t = t} (N , fs′ , st , H′ , K , nx′ , _ , o , tp) sub bl na nx =
      N , fs′ , st , H′ , kt fl K sub bl (inj₂ na) (λ i m → ⊥-elim (na i m)) , trans nx′ nx , ([] , (λ ()) , old-widen {lo = AllocState.next-heap-ref (falloc fs)} {fl = fl} {fl′ = freesOf t} {fs = fs} {fs′ = fs′} sub o) , tp

    -- a step with no events
    out00 : ∀ {sh U′} {c : Codeᴵ sh U′} {s′ : Sub root c} {fs n m′} → Moved s′ fs [] [] m′
          → AllocState.next-heap-ref (falloc fs) ≡ n → Out s′ fs n m′ []
    out00 {fs = fs} (N , fs′ , st , H′ , K , nx′ , _ , o , tp) nx = N , fs′ , st , H′ , kt [] K (λ ()) (λ ()) (inj₁ refl) (λ _ ()) , trans nx′ nx , ([] , (λ ()) , old-widen {lo = AllocState.next-heap-ref (falloc fs)} {fl = []} {fl′ = []} {fs = fs} {fs′ = fs′} (λ ()) o) , tp

    -- ★ D506: a step with no events writing in place blocks of cells it still holds
    outW : ∀ {sh U′} {c : Codeᴵ sh U′} {s′ : Sub root c} {fs n m′ wl} → Moved′ s′ fs [] [] wl m′ → Held m′ wl
         → AllocState.next-heap-ref (falloc fs) ≡ n → Out s′ fs n m′ []
    outW {fs = fs} {wl = wl} (N , fs′ , st , H′ , K , nx′ , _ , o , tp) hd nx =
      N , fs′ , st , H′ , kt [] K (λ ()) (λ ()) (inj₁ refl) (λ _ ()) , trans nx′ nx , (wl , hd , o) , tp

    -- a step allocating one cell, at the counter (a fresh block: not freed)
    out1 : ∀ {sh U′} {c : Codeᴵ sh U′} {s′ : Sub root c} {fs n m′ k} → Moved s′ fs (k ∷ []) [] m′
         → FreshAl (falloc fs)
         → AllocState.next-heap-ref (falloc fs) ≡ n → Out s′ fs (suc n) m′ (alloc (k , n) ∷ [])
    out1 {fs = fs} (N , fs′ , st , H′ , K , nx′ , (b , _) , o , tp) F nx =
      N , fs′ , st , H′ , kt [] K (λ ()) (λ ()) (inj₁ refl) fresh-sz , trans nx′ (cong suc nx) , ([] , (λ ()) , old-widen {lo = AllocState.next-heap-ref (falloc fs)} {fl = []} {fl′ = []} {fs = fs} {fs′ = fs′} (λ ()) o) , tp
      where
        nx₀ = AllocState.next-heap-ref (falloc fs)
        unfreed : ∀ bb → AllocState.freed (falloc fs′) nx₀ ≡ bb → AllocState.freed (falloc fs′) nx₀ ≡ false
        unfreed false e = e
        unfreed true  e = by (Keep.k-unfr K nx₀ e)
          where
            by : AllocState.freed (falloc fs) nx₀ ≡ true ⊎ nx₀ ∈ [] → AllocState.freed (falloc fs′) nx₀ ≡ false
            by (inj₁ e′) = ⊥-elim (t≢f (trans (sym e′) (F nx₀ ≤-refl)))
              where t≢f : true ≡ false → ⊥
                    t≢f ()
            by (inj₂ ())
        fresh-sz : ∀ i → alloc i ∈ alloc (_ , _) ∷ [] → LiveId (falloc fs′) i
        fresh-sz i (here refl) = subst (λ z → AllocState.block-size (falloc fs′) z ≡ _) nx b
                               , subst (λ z → AllocState.freed (falloc fs′) z ≡ false) nx (unfreed _ refl)
        fresh-sz i (there ())

    -- temporaries woven in free no block of the run's
    out-weave : ∀ {sh U′} {c : Codeᴵ sh U′} {s′ : Sub root c} {fs n m′ t ts t′} → Weave tmp t ts t′
              → Out s′ fs n m′ t → Out s′ fs n m′ t′
    out-weave {fs = fs} {t = t} {t′ = t′} w (N , fs′ , st , H′ , kt fl K sub bl sh B , nx , (wl , hd , o) , tp) =
      N , fs′ , st , H′ , kt fl K (λ {q} m → subst (q ∈_) (sym (cmap-weave evFree (λ _ → refl) w)) (sub m)) bl
                             ([ (λ e → inj₁ (trans (cmap-weave evFree (λ _ → refl) w) e)) , (λ na → inj₂ (λ i m → na i (unweave w m))) ]′ sh)
                             (λ i m → B i (unweave w m)) , nx
      , (wl , hd , subst (λ z → Old (AllocState.next-heap-ref (falloc fs)) (wl ++ z) fs fs′) (sym (cmap-weave evFree (λ _ → refl) w)) o) , tp
      where
        unweave : ∀ {t ts t′ i} → Weave tmp t ts t′ → alloc i ∈ t′ → alloc i ∈ t
        unweave (w-run w′) (here e) = here e
        unweave (w-run w′) (there m) = there (unweave w′ m)
        unweave (w-tmp w′) (here ())
        unweave (w-tmp w′) (there m) = unweave w′ m

    -- a held cell is below the counter
    held-below : ∀ {sh U′ T} {m : Cfg sh} {r : Ret U′ T} {n h} → InvI m r n h
               → ∀ i → 1 ≤ cntE (Cfg.envs m) i + cntS (Cfg.opds m) i → serial i < n
    held-below inv i p = ≰⇒> (λ le → zero1 (subst₂ (λ a b → 1 ≤ a + b) (proj₁ (fresh-cfg inv i le)) (proj₂ (fresh-cfg inv i le)) p))
      where zero1 : 1 ≤ 0 → ⊥
            zero1 ()

    -- a drop allocates nothing
    drop-na : ∀ {A} (v : MV A) i → ¬ alloc i ∈ freeAll v
    drop-na mone        i ()
    drop-na (mpair a b) i m = [ drop-na a i , drop-na b i ]′ (∈-++⁻ (freeAll a) m)
    drop-na (minl a)    i m = drop-na a i m
    drop-na (minr b)    i m = drop-na b i m
    drop-na (mbase x)   i ()
    drop-na (mmu j v)   i (there m) = drop-na v i m
    drop-na (mct x)     i m = drop-na x i m
    drop-na (mfn j c x) i (there m) = drop-na x i m
    drop-na (mnu j p)   i (there m) = drop-na p i m

    -- the top cell's count, at least one
    top1 : ∀ a i {b} c → 1 ≤ a + ((δ i i + b) + c)
    top1 a i {b} c = subst (λ d → 1 ≤ a + ((d + b) + c)) (sym (δ-same i)) (≤-trans (s≤s z≤n) (m≤n+m (suc (b + c)) a))
      where open import Data.Nat.Properties using (≤-trans)

  -- ★ a primitive, by its run
  prim-step : ∀ {Γ} {ds : Defs Γ} {Es A B S V} {g : LTm Γ A B} {k : Codeᴵ (Es ∣ B ∷ S) V} (s : Sub root (prim ds g ⨾ k))
                {es : Slots Es} {os : Stk S} {v : MV A} {w : MV B} {n n′ t fs} {U′ T} {r : Ret U′ T}
            → LdOk → Run ds g mone v n (gives w n′) t → NotOp g
            → Here s (es ∥ v ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n → LocPre (es ∥ v ∷ˢ os) r n fs
            → Out (next s) fs n′ (es ∥ w ∷ˢ os) t
  prim-step s ld r-ρ      _ H nx fr = out00 (st-ρ s H) nx
  prim-step s ld r-ρ⁻     _ H nx fr = out00 (st-ρ⁻ s H) nx
  prim-step s ld r-λ      _ H nx fr = out00 (st-λ s H) nx
  prim-step s ld r-λ⁻     _ H nx fr = out00 (st-λ⁻ s H) nx
  prim-step s ld r-α      _ H nx fr = out00 (st-α s H) nx
  prim-step s ld r-α⁻     _ H nx fr = out00 (st-α⁻ s H) nx
  prim-step s ld r-swap   _ H nx fr = out00 (st-lswap s H) nx
  prim-step s ld r-dist₁  _ H nx fr = out00 (st-ldist s H) nx
  prim-step s ld r-dist₂  _ H nx fr = out00 (st-ldist s H) nx
  prim-step s ld (r-drop {v = v}) _ H nx fr = out0 (st-drop s H) (λ ()) (λ ()) (drop-na v) nx
  prim-step s ld r-inl    _ H nx fr = out00 (st-inl s H) nx
  prim-step s ld r-inr    _ H nx fr = out00 (st-inr s H) nx
  prim-step s ld r-In     _ H refl fr = out1 (st-in s H (lp-fresh fr) (lp-fal fr _ Data.Nat.Properties.≤-refl)) (lp-fal fr) refl
  prim-step s {es = es} {os = os} ld (r-Outμ {i = i}) _ H nx fr =
    out0 (st-out s H (live-top (lp-live fr i (top1 (cntE es i) i (cntS os i))) (proj₁ (proj₁ (proj₂ (lp-ws fr)))))
                     (apart-top (lp-inv fr)))
         (λ m → m) (λ { (here refl) → subst (serial i <_) (sym nx) (held-below (lp-inv fr) i (top1 (cntE es i) i (cntS os i))) ; (there ()) })
         (λ _ → λ { (here ()) ; (there ()) }) nx
    where
      live-top : ∀ {a b c} → a ≡ b × c ≡ false → b ≡ _ → a ≡ _ × c ≡ false
      live-top (e , f) eb = trans e eb , f
  prim-step s ld r-clo    _ H nx fr = out00 (st-clo s H) nx
  prim-step s ld r-lam    _ H refl fr = out1 (st-lam s H (lp-fresh fr) (lp-fal fr _ Data.Nat.Properties.≤-refl)) (lp-fal fr) refl
  prim-step s ld r-lamω   _ H refl fr = out1 (st-lamω s H (lp-fresh fr) (lp-fal fr _ Data.Nat.Properties.≤-refl)) (lp-fal fr) refl
  prim-step s ld r-lamωᶜ  _ H refl fr = out1 (st-lamωᶜ s H (lp-fresh fr) (lp-fal fr _ Data.Nat.Properties.≤-refl)) (lp-fal fr) refl
  prim-step s ld r-unf    _ H refl fr = out1 (st-unf s H (lp-fresh fr) (lp-fal fr _ Data.Nat.Properties.≤-refl)) (lp-fal fr) refl
  prim-step s {fs = fs} ld (r-const {v = v}) _ H nx fr = out00 (st-const s (ld v fs) H) nx
  prim-step s ld (r-op _) () H nx fr
  prim-step s ld (r-tmp r w _) no H nx fr = out-weave w (prim-step s ld r no H nx fr)
  -- not primitives: no lowering evidence
  prim-step s ld r-id               _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-∘ _ _)          _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-⊗ _ _)          _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld r-dup              _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-case₁ _)        _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-case₂ _)        _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-app _ _)        _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-cata _ _)       _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-cata-reuse _ _) _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-cata-late _ _)  _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-lend _)         _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-lift _)         _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld r-copy             _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-ev _)           _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-evωᶜ _)         _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-evω _)          _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-nout _)         _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))
  prim-step s ld (r-iter _ _)       _ H nx fr = ⊥-elim (proj₁ (lcin (lowAt s)))

  -- the next path of a local step
  -- the next path of a local step, and what stays: the return stack, the way out
  record Succ {T sh U sh′ U′} {c : Codeᴵ sh U} {c′ : Codeᴵ sh′ U′} (r : Ret U T) (r′ : Ret U′ T) (s : Sub root c) : Set₁ where
    field
      sub   : Sub root c′
      carry : ∀ (P : ∀ {V} → AbstractTrace → Ret V T → Set) → P (lfin (lowAt s)) r → P (lfin (lowAt sub)) r′

  -- by the step's constructor (the split is StepKinds')
  SuccM : ∀ {T} → Motive {Level.suc Level.zero} {T}
  SuccM {c = c} {r = r} {c′ = c′} {r′ = r′} _ = (s : Sub root c) → Succ {c′ = c′} r r′ s

  succ-cases : ∀ {T} → LocalCases {Level.suc Level.zero} {T}
  succ-cases = record
    { P        = SuccM
    ; unpair′  = λ s → record { sub = next s ; carry = λ P x → x }
    ; pair′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; swap′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; xchg′    = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; unit′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; prim′    = λ _ _ s → record { sub = next s ; carry = λ P x → x }
    ; untag′   = λ s → record { sub = next s ; carry = λ P x → x }
    ; untag₁′  = λ s → record { sub = next s ; carry = λ P x → x }
    ; tag₁′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; case₁′   = λ s → record { sub = left s ; carry = λ P x → x }
    ; case₂′   = λ s → record { sub = right s ; carry = λ P x → x }
    ; elend′   = λ s → record { sub = next s ; carry = λ P x → x }
    ; eunlend′ = λ s → record { sub = next s ; carry = λ P x → x }
    ; elift′   = λ s → record { sub = next s ; carry = λ P x → x }
    ; efst′    = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; esnd′    = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; eout′    = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; eoutq′   = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; ecase₁′  = λ _ s → record { sub = eleft s ; carry = λ P x → x }
    ; ecase₂′  = λ _ s → record { sub = eright s ; carry = λ P x → x }
    ; eapp′    = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; epop′    = λ s → record { sub = next s ; carry = λ P x → x }
    ; eword′   = λ _ s → record { sub = next s ; carry = λ P x → x }
    ; oncify′  = λ s → record { sub = next s ; carry = λ P x → x }
    }

  succ′ : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
        → (st : StepI c r m n t c′ r′ m′ n′) → Local st → (s : Sub root c) → Succ {c′ = c′} r r′ s
  succ′ st l = local-elim succ-cases st l

  succ : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
       → (st : StepI c r m n t c′ r′ m′ n′) → Local st → Sub root c → Sub root c′
  succ st l s = Succ.sub (succ′ st l s)

  -- ★ D505/D506: the exchange — the node's block written in place, a cell the next
  -- configuration still holds (the top of the stack)
  xchg-step : ∀ {Es F L S V} {e : LF∙ F (μt F) ≡ L} {k : Codeᴵ (Es ∣ μt F ∷ L ∷ S) V} (s : Sub root (xchg e ⨾ k))
                {es : Slots Es} {x x′ : MV (μt F)} {a a′ : MV L} {os : Stk S} {n fs} {U′ T} {r : Ret U′ T}
            → Xchg e x a x′ a′
            → Here s (es ∥ x ∷ˢ a ∷ˢ os) fs → AllocState.next-heap-ref (falloc fs) ≡ n → LocPre (es ∥ x ∷ˢ a ∷ˢ os) r n fs
            → Out (next s) fs n (es ∥ x′ ∷ˢ a′ ∷ˢ os) []
  xchg-step {e = refl} s {es = es} {os = os} (xg {i = i} {v} {w}) H nx fr =
    outW (st-xchg s H lv (subst (serial i <_) (sym nx) (held-below (lp-inv fr) i top)) (apart-top (lp-inv fr)))
         (λ { (here refl) → i , refl , top1 (own es i) i (held (v ∷ˢ os) i) ; (there ()) }) nx
    where
      top = top1 (cntE es i) i (cntS (w ∷ˢ os) i)
      lv = trans (proj₁ (lp-live fr i top)) (proj₁ (proj₁ (proj₂ (lp-ws fr)))) , proj₂ (lp-live fr i top)

  -- what a local step owes: from `Here` at its path, `Here` at the next
  StepM : ∀ {T} → Motive {Level.zero} {T}
  StepM {c = c} {r = r} {m = m} {n = n} {t = t} {m′ = m′} {n′ = n′} st =
    (l : LocalC c) (s : Sub root c) {fs : FlatState} → Here s m fs → AllocState.next-heap-ref (falloc fs) ≡ n → LocPre m r n fs
    → Out (succ st l s) fs n′ m′ t

  step-cases : ∀ {T} → LdOk → Labelled → LocalCases {Level.zero} {T}
  step-cases ld lab = record
    { P        = StepM
    ; unpair′  = λ _ s H nx fr → out00 (st-unpair s H) nx
    ; pair′    = λ _ s H nx fr → out00 (st-pair s H) nx
    ; swap′    = λ _ s H nx fr → out00 (st-swap s H) nx
    ; xchg′    = λ g _ s H nx fr → xchg-step s g H nx fr
    ; unit′    = λ _ s H nx fr → out00 (st-unit s H) nx
    ; prim′    = λ run no _ s H nx fr → prim-step s ld run no H nx fr
    ; untag′   = λ _ s H nx fr → out00 (st-untag s H) nx
    ; untag₁′  = λ _ s H nx fr → out00 (st-untag₁ s H) nx
    ; tag₁′    = λ _ s H nx fr → out00 (st-tag₁ s H) nx
    ; case₁′   = λ _ s H nx fr → out00 (st-case₁ lab s H) nx
    ; case₂′   = λ _ s H nx fr → out00 (st-case₂ s H) nx
    ; elend′   = λ _ s H nx fr → out00 (st-elend s H) nx
    ; eunlend′ = λ _ s H nx fr → out00 (st-eunlend s H) nx
    ; elift′   = λ _ s H nx fr → out00 (st-elift s H) nx
    ; efst′    = λ eq _ s H nx fr → out00 (st-efst s eq H) nx
    ; esnd′    = λ eq _ s H nx fr → out00 (st-esnd s eq H) nx
    ; eout′    = λ eq _ s H nx fr → out0 (st-eout s eq H) (λ ()) (λ ()) (λ _ → λ { (here ()) ; (there ()) }) nx
    ; eoutq′   = λ eq _ s H nx fr → out00 (st-eoutq s eq H) nx
    ; ecase₁′  = λ eq _ s H nx fr → out00 (st-ecase₁ lab s eq H) nx
    ; ecase₂′  = λ eq _ s H nx fr → out00 (st-ecase₂ s eq H) nx
    ; eapp′    = λ eq _ s H nx fr → out00 (st-eapp s eq H) nx
    ; epop′    = λ _ s H nx fr → out00 (st-epop s H) nx
    ; eword′   = λ eq _ s H nx fr → out00 (st-eword s eq H) nx
    ; oncify′  = λ _ s H nx fr → out00 (st-oncify s H) nx
    }

  -- ★ THE LOCAL STEP THEOREM
  local-step : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′} {fs}
             → LdOk → Labelled
             → (st : StepI c r m n t c′ r′ m′ n′) (l : Local st) (s : Sub root c)
             → Here s m fs → AllocState.next-heap-ref (falloc fs) ≡ n → LocPre m r n fs
             → Out (succ st l s) fs n′ m′ t
  local-step ld lab st l s H nx fr = local-elim (step-cases ld lab) st l l s H nx fr
