-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.CopyRun — plan 0.157 S2 step 4 (D501): ★ THE IMAGE OF A
-- COPY-FREE PROGRAM NEVER COPIES CELLS.
--
-- `KeysRun`'s twin. A key is GOOD when its block calls no copy of cells: a
-- body, a fold or a trampoline over copy-free terms (`CopyFree.CF`), an
-- observation whose layer does not branch, a copy at a type without cells
-- (words), any free — never a closure's copy trampoline (`ktrc`). Code is good
-- when it calls only good keys, never copies a closure or a ν (`ccopy`,
-- `ncopy`: the only ways into `ktrc`), and builds only copy-free closures and
-- ν's. Every step of the image keeps good code, return stack and values
-- (given `KeysRun`'s invariant for the lent calls, D498), so a run from a
-- copy-free program's start never calls a cell copy.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Data.Nat using (ℕ)

module Once.LinCore.CopyRun
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Once.LinCore.Core fmt
open import Once.LinCore.Code fmt bw using (Sh; _∣_)
open import Once.LinCore.Image fmt bw
open import Once.LinCore.CopyFree fmt
open import Once.LinCore.CopyCode fmt bw

------------------------------------------------------------------------
-- 4. ★ GOOD VALUES, RETURN STACK, CONFIGURATION — and every step keeps them.
------------------------------------------------------------------------

open import Once.LinCore.Flat using (funit; fvoid; fw; _f*_; _f+_)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Code fmt bw using (Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)
open BSig using (top)
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; done; _⟫_; start)
open import Once.LinCore.Keys fmt bw
open Univ using (tys; nus; cts; lct)
import Once.LinCore.KeysRun
open import Data.List.Membership.Propositional using (_∈_)

module Keep′ (U : Univ) where
  open Good (lct U)
  open In U using (CIn; PrimIn; BIn)
  open Once.LinCore.KeysRun.Keep fmt ans bw U using (RIn; MIn)

  LamC : ∀ {k g X A B} → Lam k g X A B → Set
  LamC (c1 ds b γ) = CFD (lct U) ds × CF (lct U) b
  LamC (cω ds b γ) = CFD (lct U) ds × CF (lct U) b
  LamC (cωᶜ {g = g} {X = X} {A} {B} ds b₀ γ) =
    CFD (lct U) ds × CF (lct U) b₀ × (T (not (lct U (Fn many g A B))) ⊎ NC X)

  VC : ∀ {A} → MV A → Set
  VC mone                  = ⊤
  VC (mpair a b)           = VC a × VC b
  VC (minl a)              = VC a
  VC (minr b)              = VC b
  VC (mbase x)             = ⊤
  VC (mmu i v)             = VC v
  VC (mct x)               = VC x
  VC (mfn i lam x)         = LamC lam × VC x
  VC (mnu {F} {S} i p)     = T (not (coCopies F)) × VC p

  SC : ∀ {S} → Stk S → Set
  SC []ˢ       = ⊤
  SC (v ∷ˢ os) = VC v × SC os

  EC : ∀ {Es} → Slots Es → Set
  EC []ᵉ          = ⊤
  EC (vw e es)    = VC e × EC es
  EC (ln e x es)  = VC e × VC x × EC es

  MC : ∀ {sh} → Cfg sh → Set
  MC (es ∥ os) = EC es × SC os

  RC : ∀ {U′ T} → Ret U′ T → Set
  RC []ʳ             = ⊤
  RC (frm k es os r) = CC k × EC es × SC os × RC r
  RC (k ∷ⁱ r)        = CC k × RC r

  see-c : ∀ {E Es} (es : Slots (E ∷ Es)) → EC es → VC (see es)
  see-c (vw e es)   (v , _)     = v
  see-c (ln e x es) (v , w , _) = v , w

  topv-c : ∀ t {Es} (es : Slots (t ⊳ Es)) → EC es → EC (topv t es)
  topv-c nothing  es E = tt
  topv-c (just X) es E = see-c es E , tt

  seen-c : ∀ {E Es} {es : Slots (E ∷ Es)} {v : MV E} → see es ≡ v → EC es → VC v
  seen-c {es = es} eq E = subst VC eq (see-c es E)

  tag-c : ∀ {l X} F (x : MV (LF∙ F X)) → VC x → VC (tag {l = l} F x)
  tag-c Idf      x            v = v
  tag-c Kone     x            v = v
  tag-c Kzero    ()
  tag-c (Kb b)   x            v = v
  tag-c (Kμ G)   x            v = v
  tag-c (G ⊕f H) (minl x)     v = tag-c G x v
  tag-c (G ⊕f H) (minr x)     v = tag-c H x v
  tag-c (G ⊗f H) (mpair x x′) (v , v′) = tag-c G x v , tag-c H x′ v′

  vc-subst : ∀ {A B} (e : A ≡ B) (x : MV A) → VC x → VC (subst MV e x)
  vc-subst refl x p = p

  mvF-c : ∀ a (y : ⟦ a ⟧f) → VC (mvF a y)
  mvF-c funit    y        = tt
  mvF-c fvoid    ()
  mvF-c (fw b)   y        = tt
  mvF-c (a f* b) (x , y)  = mvF-c a x , mvF-c b y
  mvF-c (a f+ b) (inj₁ x) = mvF-c a x
  mvF-c (a f+ b) (inj₂ y) = mvF-c b y

  -- ★ a `prim` of a copy-free term builds copy-free closures and non-branching ν's
  prim-c : ∀ {Γ} {ds : Defs Γ} {E A B} {g : Tm Γ E A B} {e v w n n′ t}
         → Run ds g e v n (gives w n′) t → PrimIn ds g → CFD (lct U) ds → CF (lct U) g → VC v → VC w
  prim-c (r-tmp run _ _) p d c v = prim-c run p d c v
  prim-c r-ρ   p d c (a , _)        = a
  prim-c r-ρ⁻  p d c a              = a , tt
  prim-c r-λ   p d c (_ , a)        = a
  prim-c r-λ⁻  p d c a              = tt , a
  prim-c r-α   p d c ((a , b) , e)  = a , (b , e)
  prim-c r-α⁻  p d c (a , (b , e))  = (a , b) , e
  prim-c r-swap p d c (a , b)       = b , a
  prim-c r-drop p d c v             = tt
  prim-c r-inl p d c a              = a
  prim-c r-dist₁ p d c v            = v
  prim-c r-dist₂ p d c v            = v
  prim-c r-inr p d c b              = b
  prim-c r-In  p d c v              = v
  prim-c r-Outμ p d c v             = v
  prim-c (r-clo {F = F} {x = x}) p d c v = tag-c F x v
  prim-c r-lam  p d c v             = (d , c) , v
  prim-c r-lamω p d c v             = (d , c) , v
  prim-c r-lamωᶜ p d (cb , o) v     = (d , cb , o) , v
  prim-c r-unf  p d c v             = c , v
  prim-c r-const p d c v            = tt
  prim-c (r-op {s = s} {y = y} _) p d c v = mvF-c (scod s) y
  prim-c r-id () d c v
  prim-c (r-∘ _ _) () d c v
  prim-c (r-⊗ _ _) () d c v
  prim-c r-dup () d c v
  prim-c (r-case₁ _) () d c v
  prim-c (r-case₂ _) () d c v
  prim-c (r-app _ _) () d c v
  prim-c (r-cata _ _) () d c v
  prim-c (r-cata-reuse _ _) () d c v
  prim-c (r-lend _) () d c v
  prim-c (r-lift _) () d c v
  prim-c (r-fst _) () d c v
  prim-c (r-snd _) () d c v
  prim-c (r-caseE₁ _) () d c v
  prim-c (r-caseE₂ _) () d c v
  prim-c (r-out _) () d c v
  prim-c r-copy () d c v
  prim-c (r-bapp _ _) () d c v
  prim-c (r-ev _) () d c v
  prim-c (r-bev _) () d c v
  prim-c (r-nout _) () d c v
  prim-c (r-iter _ _) () d c v

  -- a lent call of a closure owning its environment: at a lent-called type (`KeysRun`), so its
  -- environment has no cells (`CF`'s `llamωᶜ`), so its lent entry copies words only
  good-cin : ∀ {Γ g X A B} {ds : Defs Γ} (b₀ : Tm Γ One (X ⊗t A) B) → lct U (Fn many g A B) ≡ true
           → CFD (lct U) ds × CF (lct U) b₀ × (T (not (lct U (Fn many g A B))) ⊎ NC X)
           → CFD (lct U) ds × CF (lct U) (cin b₀)
  good-cin b₀ e (d , c , inj₁ t) = ⊥-elim (subst (λ b → T (not b)) e t)
  good-cin b₀ e (d , c , inj₂ n) = d , cf-cin (lct U) b₀ n c

  -- ★ EVERY STEP KEEPS THE CODE, THE RETURN STACK AND THE VALUES GOOD
  -- (`KeysRun.keep`, case for case; its `CIn` for a prim's and a lent call's facts)
  keep′ : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m m′ n n′ t}
        → StepI c r m n t c′ r′ m′ n′ → CIn c → CC c → RC r → MC m → CC c′ × RC r′ × MC m′
  keep′ i-unpair K (_ , ck) R (E , (a , b) , os) = ck , R , E , a , b , os
  keep′ i-pair   K (_ , ck) R (E , a , b , os)   = ck , R , E , (a , b) , os
  keep′ i-swap   K (_ , ck) R (E , a , b , os)   = ck , R , E , b , a , os
  keep′ (i-xchg {e = e} (xg {v = v} {w = w})) K (_ , ck) R (E , a , b , os) = ck , R , E , vc-subst (sym e) w b , vc-subst e v a , os
  keep′ i-unit   K (_ , ck) R (E , os)           = ck , R , E , tt , os
  keep′ (i-prim run) (p , _) ((d , c) , ck) R (E , v , os) = ck , R , E , prim-c run p d c v , os
  keep′ (i-opend _) K (_ , ck) R (E , v , os)    = tt , R , E , os
  keep′ i-untag  K (_ , ck) R (E , (x , a) , os) = ck , R , E , (x , a) , os
  keep′ (i-oncify {lam = cω ds b γ}) K (_ , ck) R (E , (((d , c) , vx) , va) , os) =
    ck , R , E , (((d , cf-ownω (lct U) b c) , vx) , va) , os
  keep′ (i-oncify {lam = cωᶜ ds b₀ γ}) K (_ , ck) R (E , (((d , c , o) , vx) , va) , os) =
    ck , R , E , (((d , c) , vx) , va) , os
  keep′ i-untag₁ K (_ , ck) R (E , x , os)       = ck , R , E , x , os
  keep′ i-tag₁   K (_ , ck) R (E , x , os)       = ck , R , E , x , os
  keep′ i-case₁  K (c₁ , _) R (E , a , os)       = c₁ , R , E , a , os
  keep′ i-case₂  K (_ , c₂) R (E , b , os)       = c₂ , R , E , b , os
  keep′ (i-elend {es = es}) K (_ , ck) R (E , (x , a) , os) = ck , R , (see-c es E , x , E) , a , os
  keep′ i-eunlend K (_ , ck) R ((e , x , E) , w , os)       = ck , R , E , (x , w) , os
  keep′ i-elift  K (_ , ck) R (E , os)           = ck , R , (tt , E) , os
  keep′ (i-efst eq) K (_ , ck) R (E , os)        = ck , R , (proj₁ (seen-c eq E) , E) , os
  keep′ (i-esnd eq) K (_ , ck) R (E , os)        = ck , R , (proj₂ (seen-c eq E) , E) , os
  keep′ (i-eout eq) K (_ , ck) R (E , os)        = ck , R , (seen-c eq E , E) , os
  keep′ (i-eoutq eq) K (_ , ck) R (E , os)       = ck , R , (seen-c eq E , E) , os
  keep′ (i-ecase₁ eq) K (c₁ , _) R (E , os)      = c₁ , R , (seen-c eq E , E) , os
  keep′ (i-ecase₂ eq) K (_ , c₂) R (E , os)      = c₂ , R , (seen-c eq E , E) , os
  keep′ (i-eapp eq) K (_ , ck) R (E , os)        = ck , R , (seen-c eq E , E) , os
  keep′ i-epop   K (_ , ck) R ((_ , E) , os)     = ck , R , E , os
  keep′ (i-eword _) K (_ , ck) R (E , _ , os)    = ck , R , E , tt , os
  -- ★ a call: a good key's block is good code
  keep′ (i-call {σ = σ} {κ = κ} {es = es}) K (g , ck) R (E , a , os) =
    block-c κ g , (ck , E , os , R) , topv-c (top σ) es E , a , tt
  keep′ i-ret    K _ (ck , E , os , R) (_ , b , _) = ck , R , E , b , os
  keep′ i-reti   K _ (ck , R) M                  = ck , R , M
  keep′ i-loop   K (cb , ck) R M                 = cb , ((ck , cb , ck) , R) , M
  -- ★ a dispatch: the trampoline the cell names calls a block its closure keeps good
  keep′ (i-icall {lam = c1 ds b γ}) K (_ , ck) R (E , ((l , x) , a) , os) =
    (tt , l , tt) , (ck , E , os , R) , tt , ((l , x) , a) , tt
  keep′ (i-icallω {lam = cω ds b γ} {es = es} eq) K (_ , ck) R (E , a , os) =
    (tt , proj₁ (seen-c eq E) , tt , tt) , (ck , E , os , R) , (see-c es E , tt) , a , tt
  keep′ (i-icallω {lam = cωᶜ ds b₀ γ} {es = es} eq) (lc , _) (_ , ck) R (E , a , os) =
    (tt , good-cin b₀ lc (proj₁ (seen-c eq E)) , tt , tt) , (ck , E , os , R) , (see-c es E , tt) , a , tt
  keep′ i-iobs K (_ , ck) R (E , (n , p) , os) = (tt , (tt , n) , tt) , (ck , E , os , R) , tt , (n , p) , tt
  -- ★ good code never copies a closure or a ν
  keep′ (i-ccopy eq) K (() , _) R M
  keep′ (i-ncopy eq) K (() , _) R M
  keep′ i-cfree K (_ , ck) R (E , (l , x) , os) = (tt , tt , tt) , (ck , E , os , R) , tt , (l , x) , tt
  keep′ i-nfree K (_ , ck) R (E , (n , p) , os) = (tt , tt , tt) , (ck , E , os , R) , tt , (n , p) , tt
  -- a trampoline's cell part
  keep′ i-open1  K (_ , ck) R (E , ((l , x) , a) , os) = ck , R , E , (x , a) , os
  keep′ (i-openω eq) K (_ , ck) R (E , os)       = ck , R , (proj₂ (seen-c eq E) , E) , os
  keep′ i-nopen  K (_ , ck) R (E , (n , p) , os) = ck , R , E , p , os
  keep′ (i-copen eq) K (_ , ck) R (E , os)       = ck , R , (proj₂ (seen-c eq E) , E) , os
  keep′ (i-copenν eq) K (_ , ck) R (E , os)      = ck , R , (proj₂ (seen-c eq E) , E) , os
  keep′ (i-reclose eq) K (_ , ck) R (E , x′ , os)  = ck , R , E , (proj₁ (seen-c eq E) , x′) , os
  keep′ (i-recloseν eq) K (_ , ck) R (E , p′ , os) = ck , R , E , (proj₁ (seen-c eq E) , p′) , os
  keep′ i-fopen  K (_ , ck) R (E , (l , x) , os) = ck , R , E , x , os
  keep′ i-fopenν K (_ , ck) R (E , (n , p) , os) = ck , R , E , p , os

  module Steps′ (blk : ∀ {κ} → κ ∈ allK U → BIn κ)
                (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ cts U) where
    open Once.LinCore.KeysRun.Keep.Steps fmt ans bw U blk ncty using (keep)

    keeps′ : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m m′ n n′ t}
           → StepsI c r m n t c′ r′ m′ n′ → CIn c → RIn r → MIn m → CC c → RC r → MC m → CC c′ × RC r′ × MC m′
    keeps′ done C R M Cc Rc Mc = Cc , Rc , Mc
    keeps′ (s ⟫ st) C R M Cc Rc Mc =
      let (C₂ , R₂ , M₂) = keep s C R M ; (Cc₂ , Rc₂ , Mc₂) = keep′ s C Cc Rc Mc in keeps′ st C₂ R₂ M₂ Cc₂ Rc₂ Mc₂

------------------------------------------------------------------------
-- 5. ★★ A COPY-FREE PROGRAM'S IMAGE NEVER COPIES CELLS: every configuration
-- it reaches is good, so it never calls a copy at a type with cells and never
-- copies a closure or a ν (the only ways into `ktrc`).
------------------------------------------------------------------------

module ProgramCopy {Γ} (ds : Defs Γ) (f : LTm Γ One One) where
  open Program ds f
  open Keep′ U
  open Good (lct U)
  open Steps′ blocks-in ncty

  module _ (d : CFD (lct U) ds) (c : CF (lct U) f) where

    good-always : ∀ {sh U′} {c′ : Codeᴵ sh U′} {r′ : Ret U′ (One ∷ [] ∣ One ∷ [])} {m′ n′ mt}
                → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 0 mt c′ r′ m′ n′
                → CC c′ × RC r′ × MC m′
    good-always st = keeps′ st (start-in tt) tt ((tt , tt) , tt , tt) (comp-c ds f d c tt) tt ((tt , tt) , tt , tt)

    -- ★ no step of the run calls a copy of a value with cells
    no-cell-copy : ∀ {A Es S U′} {k : Codeᴵ (A ∷ Es ∣ A ∷ S) U′} {r′ m′ n′ mt}
                 → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 0 mt (call (kcopy A) ⨾ k) r′ m′ n′
                 → NC A
    no-cell-copy st = proj₁ (proj₁ (good-always st))

    -- ★ nor copies a closure or a ν
    no-ccopy : ∀ {Es k g A B S U′} {c′ : Codeᴵ (Fn k g A B ∷ Es ∣ Fn k g A B ∷ S) U′} {r′ m′ n′ mt}
             → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 0 mt (ccopy ⨾ c′) r′ m′ n′ → ⊥
    no-ccopy st = proj₁ (proj₁ (good-always st))

    no-ncopy : ∀ {Es F S U′} {c′ : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S) U′} {r′ m′ n′ mt}
             → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 0 mt (ncopy ⨾ c′) r′ m′ n′ → ⊥
    no-ncopy st = proj₁ (proj₁ (good-always st))
