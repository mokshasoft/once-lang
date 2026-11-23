-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ExpandSimCall — the arch's theorem for the
-- allocator as a call (D480, plan 0.146 §5 item 8 c).
--
-- The call mode is the expansion of the OUTLINED image (`AllocExpand.outline`):
-- its allocations and frees called in place, their primitive routines after the
-- start, jumped over. The outlined image is emitted (`OutlineEmitted`), its run
-- never faults and shows what the image's shows (`AllocOutline.Out.Run`), so the
-- expansion's theorem (`ExpandSim`) applies to it unchanged: the arch runs the
-- call mode's code, room-checked, with the program's trace.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
open import Once.Adequacy.ArchCorrectness.Interface using (ArchSim; module ArchSim; FlatShows)
open import Once.Target.Backend using (Backend)

module Once.Adequacy.ArchCorrectness.ExpandSimCall (o : CanonicalName) {B : Backend} (A : ArchSim o B) where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (LabelId; module LabelId; e-fn)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.Denotation.Program using (IRProgram)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.CCC.FrameSemantics using (fs-numerics; module FrameSemantics)
open import Once.Adequacy.MachineTrace using (module Machine)
open import Once.Denotation.ProgramTrace using (⟦_⟧IRᵗ)

open ArchSim A
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (Sound; _∷_; [])
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq
  using (Emitted; module Emitted; RunAt; mkRunAt; module RunAt; reach-start; reach-step; run-sound)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunWF o FS slot-size word-eq
  using (run-step-pc-pos; start-at-zero; run-link-at-thunk)
open import Once.CCC.Codegen.AllocOutline {FS} using (module Out; NotR; RouI; ri-a; ri-f; rou; site-same; SiteView; sv-alloc; sv-free; sv-same; site-view)
open import Once.Adequacy.ArchCorrectness.OutlineEmitted o FS slot-size word-eq using (emitted)
import Once.Adequacy.ArchCorrectness.ExpandSim

module _ (C : Classes) (small : 3 + count C ≤ rec-size)
         (in-range : ∀ k → cls C k < count C) (fits : ∀ k → k ≤ bsz C k)
         (q : IRProgram) (b : ℕ) (T : AbstractTrace) (env : String → Maybe (Backend.Payload B))
         (ks : List ℕ) (Sz : ℕ → Set)
         (uniform  : ∀ k k′ → Sz k → Sz k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′)
         where
  open Out ks b T

  module _ -- the image's
           (em     : Emitted P) (snd : Sound P start)
           (ks-pos : ∀ k → k ∈ ks → 1 ≤ k)
           (ks-sz  : ∀ k → k ∈ ks → Sz k)
           (sz     : ∀ q′ k → (fetch T q′ ≡ just (instr-alloc-heap k)) ⊎ (fetch T q′ ≡ just (instr-free-heap k)) → k ∈ ks)
           (nj     : ∀ q′ i m → fetch T q′ ≡ just i → (i ≡ instr-ctrl (c-jmp m)) ⊎ (i ≡ instr-ctrl (c-branch-tag-zero m)) → ¬ skip-label ≡ m)
           (nc     : ∀ q′ i f → fetch T q′ ≡ just i → i ≡ instr-ctrl (c-call-fn f) → NotR (e-fn f))
           (img    : ∀ n m → fetch P n ≡ just (instr-ctrl (c-label m)) → ImgL m)
           (jmp-lbl : ∀ n m → fetch P n ≡ just (instr-ctrl (c-jmp m)) → ImgL m)
           (br-lbl : ∀ n m → fetch P n ≡ just (instr-ctrl (c-branch-tag-zero m)) → ImgL m)
           (no-lrec : ∀ n k → fetch P n ≡ just (load-rec k) → ⊥)
           (no-srec : ∀ n k → fetch P n ≡ just (store-rec k) → ⊥)
           where
    private
      just-inj : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
      just-inj refl = refl

      skip-img : ImgL skip-label
      skip-img ()

      -- the image's run: reached, past its start
      Good : FlatState → Set
      Good fs = RunAt P fs × (fpc fs ≡ 0 → ⊥)

      g-step : ∀ {fs i} → Good fs → LocState.halted (floc fs) ≡ false → fetch P (fpc fs) ≡ just i → Good (flat-exec-instr i P fs)
      g-step {fs} {i} (r , _) h f = mkRunAt (RunAt.run-em r) (reach-step i fs (RunAt.run-reach r) f h) , run-step-pc-pos P fs i r f

      g-ns : ∀ {fs} → Good fs → ¬ fetch P (fpc fs) ≡ just (instr-ctrl (c-start b))
      g-ns {fs} (r , ns) f = ns (start-at-zero P (fpc fs) b (RunAt.run-em r) f)

      g-link : ∀ {fs i} → Good fs → fetch P (fpc fs) ≡ just i → (∀ e bb → ¬ i ≡ instr-ctrl (c-entry e bb)) → flink fs ≡ nothing
      g-link {fs} {i} (r , _) f ne = lk (flink fs) refl
        where lk : ∀ m → flink fs ≡ m → flink fs ≡ nothing
              lk nothing  e = e
              lk (just x) e = let (ℓ , bb , f′) = run-link-at-thunk P fs r e in ⊥-elim (ne ℓ bb (just-inj (trans (sym f) f′)))

      g-nf : ∀ {fs i} → Good fs → LocState.halted (floc fs) ≡ false → fetch P (fpc fs) ≡ just i
           → LocState.faulted (floc (flat-exec-instr i P fs)) ≡ false
      g-nf (r , _) h f = run-sound r ((h , f) ∷ [])

      module R = Run Good g-step g-ns g-link g-nf sz nj nc

      r₀ : RunAt P start
      r₀ = mkRunAt em (reach-start start entry-like refl snd)

      G₁ : Good (flat-exec-instr (instr-ctrl (c-start b)) P start)
      G₁ = mkRunAt em (reach-step (instr-ctrl (c-start b)) start (RunAt.run-reach r₀) refl refl) , (λ ())

      -- the outlined image: emitted, its run sound
      em′ : Emitted P′
      em′ = emitted ks b T em ks-pos sz nc

      snd′ : Sound P′ start
      snd′ = R.sound-start start refl refl refl refl G₁ (run-sound r₀ ((refl , refl) ∷ []))

      -- its instructions, by where
      lab′ : ∀ (pred : LabelId → Set) → pred skip-label
           → (∀ n m → fetch P n ≡ just (instr-ctrl (c-label m)) → pred m)
           → ∀ n m → fetch P′ n ≡ just (instr-ctrl (c-label m)) → pred m
      lab′ pred ps pP n m f = go (where-P′ n _ f)
        where go : WhereP′ n (instr-ctrl (c-label m)) → pred m
              go (w-start _ ())
              go (w-jmp _ ())
              go (w-rou j _ r) = ⊥-elim (no (rou ks j _ r))
                where no : RouI ks (instr-ctrl (c-label m)) → ⊥
                      no ()
              go (w-lab _ refl) = ps
              go (w-own q′ i′ _ ft ei) = pP (suc q′) m (trans ft (cong just (site-same ei (λ f ()))))

      jmp′ : ∀ (pred : LabelId → Set) → pred skip-label
           → (∀ n m → fetch P n ≡ just (instr-ctrl (c-jmp m)) → pred m)
           → ∀ n m → fetch P′ n ≡ just (instr-ctrl (c-jmp m)) → pred m
      jmp′ pred ps pP n m f = go (where-P′ n _ f)
        where go : WhereP′ n (instr-ctrl (c-jmp m)) → pred m
              go (w-start _ ())
              go (w-jmp _ refl) = ps
              go (w-rou j _ r) = ⊥-elim (no (rou ks j _ r))
                where no : RouI ks (instr-ctrl (c-jmp m)) → ⊥
                      no ()
              go (w-lab _ ())
              go (w-own q′ i′ _ ft ei) = pP (suc q′) m (trans ft (cong just (site-same ei (λ f ()))))

      br′ : ∀ n m → fetch P′ n ≡ just (instr-ctrl (c-branch-tag-zero m)) → ImgL m
      br′ n m f = go (where-P′ n _ f)
        where go : WhereP′ n (instr-ctrl (c-branch-tag-zero m)) → ImgL m
              go (w-start _ ())
              go (w-jmp _ ())
              go (w-rou j _ r) = ⊥-elim (no (rou ks j _ r))
                where no : RouI ks (instr-ctrl (c-branch-tag-zero m)) → ⊥
                      no ()
              go (w-lab _ ())
              go (w-own q′ i′ _ ft ei) = br-lbl (suc q′) m (trans ft (cong just (site-same ei (λ f ()))))

      no-lrec′ : ∀ n k → fetch P′ n ≡ just (load-rec k) → ⊥
      no-lrec′ n k f = go (where-P′ n _ f)
        where go : WhereP′ n (load-rec k) → ⊥
              go (w-start _ ())
              go (w-jmp _ ())
              go (w-rou j _ r) = no (rou ks j _ r)
                where no : RouI ks (load-rec k) → ⊥
                      no ()
              go (w-lab _ ())
              go (w-own q′ i′ _ ft ei) = no-lrec (suc q′) k (trans ft (cong just (site-same ei (λ f ()))))

      no-srec′ : ∀ n k → fetch P′ n ≡ just (store-rec k) → ⊥
      no-srec′ n k f = go (where-P′ n _ f)
        where go : WhereP′ n (store-rec k) → ⊥
              go (w-start _ ())
              go (w-jmp _ ())
              go (w-rou j _ r) = no (rou ks j _ r)
                where no : RouI ks (store-rec k) → ⊥
                      no ()
              go (w-lab _ ())
              go (w-own q′ i′ _ ft ei) = no-srec (suc q′) k (trans ft (cong just (site-same ei (λ f ()))))

      -- a called site is no allocation and no free (those are calls)
      no-alloc : ∀ k x → ¬ instr-alloc-heap k ≡ site-call x
      no-alloc k x e = nope (site-view x) e
        where nope : ∀ {y} → SiteView y → ¬ instr-alloc-heap k ≡ site-call y
              nope (sv-alloc k′) ()
              nope (sv-free k′)  ()
              nope {y} (sv-same s) e′ = clash (subst (λ z → site-call z ≡ z) (sym (trans e′ s)) s)
                where clash : ¬ site-call (instr-alloc-heap k) ≡ instr-alloc-heap k
                      clash ()

      no-free : ∀ k x → ¬ instr-free-heap k ≡ site-call x
      no-free k x e = nope (site-view x) e
        where nope : ∀ {y} → SiteView y → ¬ instr-free-heap k ≡ site-call y
              nope (sv-alloc k′) ()
              nope (sv-free k′)  ()
              nope {y} (sv-same s) e′ = clash (subst (λ z → site-call z ≡ z) (sym (trans e′ s)) s)
                where clash : ¬ site-call (instr-free-heap k) ≡ instr-free-heap k
                      clash ()

      -- its allocations and frees: the routines', at the sizes of `ks`
      sz-alloc′ : ∀ n k → fetch P′ n ≡ just (instr-alloc-heap k) → Sz k
      sz-alloc′ n k f = go (where-P′ n _ f)
        where go : WhereP′ n (instr-alloc-heap k) → Sz k
              go (w-start _ ())
              go (w-jmp _ ())
              go (w-rou j _ r) = of (rou ks j _ r)
                where of : RouI ks (instr-alloc-heap k) → Sz k
                      of (ri-a .k m) = ks-sz k m
              go (w-lab _ ())
              go (w-own q′ i′ _ ft ei) = ⊥-elim (no-alloc k i′ ei)

      sz-free′ : ∀ n k → fetch P′ n ≡ just (instr-free-heap k) → Sz k
      sz-free′ n k f = go (where-P′ n _ f)
        where go : WhereP′ n (instr-free-heap k) → Sz k
              go (w-start _ ())
              go (w-jmp _ ())
              go (w-rou j _ r) = of (rou ks j _ r)
                where of : RouI ks (instr-free-heap k) → Sz k
                      of (ri-f .k m) = ks-sz k m
              go (w-lab _ ())
              go (w-own q′ i′ _ ft ei) = ⊥-elim (no-free k i′ ei)

    module ES = Once.Adequacy.ArchCorrectness.ExpandSim o A

    -- ★★ THE ARCH RUNS THE CALL MODE, room-checked, with the program's trace: the
    -- outlined image's expansion, by the expansion's own theorem, from the outlined
    -- run that shows what the image's shows
    sim-call : ArithTable (room-checks (expand C P′)) env → FlatShows FS P start q
             → Machine.trace (δ env (compile (room-checks (expand C P′)))) init ⊑ᵗ⟨ _≡_ ⟩ ⟦ just q ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
    sim-call tb fl =
      ES.sim-exp C small in-range fits q b (skip ks ++ map site-call T) env Sz uniform
        sz-alloc′ sz-free′ (lab′ ImgL skip-img img) (jmp′ ImgL skip-img jmp-lbl) br′ no-lrec′ no-srec′ em′ snd′ tb shows′
      where
        shows′ : FlatShows FS P′ start q
        shows′ k = let (N , e , c) = fl k ; (m , ee , ec) = R.start-ev start refl refl refl G₁ N
                   in m , trans ee e , λ z → Data.Nat.Properties.≤-trans (c z) ec
