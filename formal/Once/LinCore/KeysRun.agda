-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.KeysRun — plan 0.146 B1.4b, part 1 (the run): the image of a
-- program STAYS INSIDE its finite universe (`Keys`).
--
-- A cell's code word is its `Lam`; a ν's cell holds its coalgebra and seed.
-- What the image will call through them (`icall`, `ccopy`, `cfree`, `iobs`,
-- …) is named by the cell, not by the code, so the invariant is on values
-- too: every closure's body and environment type, every ν's seed, are in the
-- universe. Every step keeps it (`keep`): the code, the return stack and the
-- configuration. So the lowering may number `allK` into labels and every
-- call it ever makes lands on a block it emitted.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.KeysRun
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; []ˢ; _∷ˢ_; Slots; []ᵉ; vw; ln; see; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw
open import Once.LinCore.ImageSim fmt ans bw using (StepsI; done; _⟫_; start)
open import Once.LinCore.Keys fmt ans bw

module Keep (U : Univ) where
  open In U

  ----------------------------------------------------------------------
  -- 1. VALUES INSIDE: their closures' code and environment types, their
  -- ν's seeds.
  ----------------------------------------------------------------------

  LamIn : ∀ {k g X A B} → Lam k g X A B → Set
  LamIn (c1 {X = X} ds b γ) = (_ , kbody1 ds b γ) ∈ allK U × X ∈ tys U
  LamIn (cω {X = X} ds b γ) = (_ , kbodyω ds b γ) ∈ allK U × X ∈ tys U

  lam-X : ∀ {k g X A B} (lam : Lam k g X A B) → LamIn lam → X ∈ tys U
  lam-X (c1 ds b γ) (_ , x) = x
  lam-X (cω ds b γ) (_ , x) = x

  VIn : ∀ {A} → MV A → Set
  VIn mone                  = ⊤
  VIn (mpair a b)           = VIn a × VIn b
  VIn (minl a)              = VIn a
  VIn (minr b)              = VIn b
  VIn (mbase x)             = ⊤
  VIn (mmu i v)             = VIn v
  VIn (mct x)               = VIn x
  VIn (mfn i lam x)         = LamIn lam × VIn x
  VIn (mnu {F} {S} i p)     = (F , S) ∈ nus U × VIn p

  SIn : ∀ {S} → Stk S → Set
  SIn []ˢ       = ⊤
  SIn (v ∷ˢ os) = VIn v × SIn os

  EIn : ∀ {Es} → Slots Es → Set
  EIn []ᵉ          = ⊤
  EIn (vw e es)    = VIn e × EIn es
  EIn (ln e x es)  = VIn e × VIn x × EIn es

  MIn : ∀ {sh} → Cfg sh → Set
  MIn (es ∥ os) = EIn es × SIn os

  -- a saved frame: its continuation and its configuration
  RIn : ∀ {U′ T} → Ret U′ T → Set
  RIn []ʳ             = ⊤
  RIn (frm k es os r) = CIn k × EIn es × SIn os × RIn r
  RIn (k ∷ⁱ r)        = CIn k × RIn r

  see-in : ∀ {E Es} (es : Slots (E ∷ Es)) → EIn es → VIn (see es)
  see-in (vw e es)   (v , _)     = v
  see-in (ln e x es) (v , w , _) = v , w

  -- a called block's frame sees the caller's top view
  topv-in : ∀ t {Es} (es : Slots (t ⊳ Es)) → EIn es → EIn (topv t es)
  topv-in nothing  es E = tt
  topv-in (just X) es E = see-in es E , tt

  -- what a view sees, through an equation
  seen : ∀ {E Es} {es : Slots (E ∷ Es)} {v : MV E} → see es ≡ v → EIn es → VIn v
  seen {es = es} eq E = subst VIn eq (see-in es E)

  tag-in : ∀ {l X} F (x : MV (LF∙ F X)) → VIn x → VIn (tag {l = l} F x)
  tag-in Idf      x            v = v
  tag-in Kone     x            v = v
  tag-in Kzero    ()
  tag-in (Kb b)   x            v = v
  tag-in (Kμ G)   x            v = v
  tag-in (G ⊕f H) (minl x)     v = tag-in G x v
  tag-in (G ⊕f H) (minr x)     v = tag-in H x v
  tag-in (G ⊗f H) (mpair x x′) (v , v′) = tag-in G x v , tag-in H x′ v′

  mvF-in : ∀ a (y : ⟦ a ⟧f) → VIn (mvF a y)
  mvF-in funit    y        = tt
  mvF-in fvoid    ()
  mvF-in (fw b)   y        = tt
  mvF-in (a f* b) (x , y)  = mvF-in a x , mvF-in b y
  mvF-in (a f+ b) (inj₁ x) = mvF-in a x
  mvF-in (a f+ b) (inj₂ y) = mvF-in b y

  -- ★ a `prim` keeps its operand inside: a closure or a ν it builds is named
  prim-in : ∀ {Γ} {ds : Defs Γ} {E A B} {g : Tm Γ E A B} {e v w n n′ t}
          → Run ds g e v n (gives w n′) t → PrimIn ds g → VIn v → VIn w
  prim-in (r-tmp run _ _) p v = prim-in run p v
  prim-in r-ρ   p (a , _)        = a
  prim-in r-ρ⁻  p a              = a , tt
  prim-in r-λ   p (_ , a)        = a
  prim-in r-λ⁻  p a              = tt , a
  prim-in r-α   p ((a , b) , c)  = a , (b , c)
  prim-in r-α⁻  p (a , (b , c))  = (a , b) , c
  prim-in r-swap p (a , b)       = b , a
  prim-in r-drop p v             = tt
  prim-in r-inl p a              = a
  prim-in r-inr p b              = b
  prim-in r-In  p v              = v
  prim-in r-Outμ p v             = v
  prim-in (r-clo {F = F} {x = x}) p v = tag-in F x v
  prim-in r-lam  p v             = p , v
  prim-in r-lamω p v             = p , v
  prim-in r-unf  p v             = p , v
  prim-in r-const p v            = tt
  prim-in (r-op {s = s} {y = y} _) p v = mvF-in (scod s) y
  prim-in r-id () v
  prim-in (r-∘ _ _) () v
  prim-in (r-⊗ _ _) () v
  prim-in r-dup () v
  prim-in (r-case₁ _) () v
  prim-in (r-case₂ _) () v
  prim-in (r-app _ _) () v
  prim-in (r-cata _ _) () v
  prim-in (r-cata-reuse _ _) () v
  prim-in (r-lend _) () v
  prim-in (r-lift _) () v
  prim-in (r-fst _) () v
  prim-in (r-snd _) () v
  prim-in (r-caseE₁ _) () v
  prim-in (r-caseE₂ _) () v
  prim-in (r-out _) () v
  prim-in r-copy () v
  prim-in (r-bapp _ _) () v
  prim-in (r-ev _) () v
  prim-in (r-bev _) () v
  prim-in (r-nout _) () v
  prim-in (r-iter _ _) () v

  ----------------------------------------------------------------------
  -- 2. ★ EVERY STEP STAYS INSIDE (given the universe's blocks are, and a
  -- ν's cell type is among its types).
  ----------------------------------------------------------------------

  module Steps (blk : ∀ {κ} → κ ∈ allK U → BIn κ)
               (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U) where

    keep : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m m′ n n′ t}
         → StepI c r m n t c′ r′ m′ n′ → CIn c → RIn r → MIn m → CIn c′ × RIn r′ × MIn m′
    keep i-unpair (_ , ck) R (E , (a , b) , os) = ck , R , E , a , b , os
    keep i-pair   (_ , ck) R (E , a , b , os)   = ck , R , E , (a , b) , os
    keep i-swap   (_ , ck) R (E , a , b , os)   = ck , R , E , b , a , os
    keep i-unit   (_ , ck) R (E , os)           = ck , R , E , tt , os
    keep (i-prim run) (p , ck) R (E , v , os)   = ck , R , E , prim-in run p v , os
    keep (i-opend _) (_ , ck) R (E , v , os)    = tt , R , E , os
    keep i-untag  (_ , ck) R (E , (x , a) , os) = ck , R , E , (x , a) , os
    keep i-untag₁ (_ , ck) R (E , x , os)       = ck , R , E , x , os
    keep i-tag₁   (_ , ck) R (E , x , os)       = ck , R , E , x , os
    keep i-case₁  (c₁ , _) R (E , a , os)       = c₁ , R , E , a , os
    keep i-case₂  (_ , c₂) R (E , b , os)       = c₂ , R , E , b , os
    keep (i-elend {es = es}) (_ , ck) R (E , (x , a) , os) = ck , R , (see-in es E , x , E) , a , os
    keep i-eunlend (_ , ck) R ((e , x , E) , w , os)       = ck , R , E , (x , w) , os
    keep i-elift  (_ , ck) R (E , os)           = ck , R , (tt , E) , os
    keep (i-efst eq) (_ , ck) R (E , os)        = ck , R , (proj₁ (seen eq E) , E) , os
    keep (i-esnd eq) (_ , ck) R (E , os)        = ck , R , (proj₂ (seen eq E) , E) , os
    keep (i-eout eq) (_ , ck) R (E , os)        = ck , R , (seen eq E , E) , os
    keep (i-eoutq eq) (_ , ck) R (E , os)       = ck , R , (seen eq E , E) , os
    keep (i-ecase₁ eq) (c₁ , _) R (E , os)      = c₁ , R , (seen eq E , E) , os
    keep (i-ecase₂ eq) (_ , c₂) R (E , os)      = c₂ , R , (seen eq E , E) , os
    keep (i-eapp eq) (_ , ck) R (E , os)        = ck , R , (seen eq E , E) , os
    keep i-epop   (_ , ck) R ((_ , E) , os)     = ck , R , E , os
    keep (i-eword _) (_ , ck) R (E , _ , os)    = ck , R , E , tt , os
    keep (i-call {σ = σ} {es = es}) (κ , ck) R (E , a , os) = blk κ , (ck , E , os , R) , topv-in (top σ) es E , a , tt
    keep i-ret    _ (ck , E , os , R) (_ , b , _) = ck , R , E , b , os
    keep i-reti   _ (ck , R) M                  = ck , R , M
    keep i-loop   (cb , ck) R M                 = cb , ((ck , cb , ck) , R) , M
    keep i-icall  (_ , ck) R (E , ((l , x) , a) , os) = (proj₁ l , ck) , R , E , (x , a) , os
    keep (i-icallω eq) (_ , ck) R (E , os) with seen eq E
    ... | (l , x) = (proj₁ l , tt , ck) , R , (x , E) , os
    keep (i-iobs {ds = ds} {F = F} {S = S}) (o , ck) R (E , (n , p) , os) = (inO o n , ck) , R , E , p , os
    keep (i-ccopy1 eq) (_ , ck) R (E , _ , os) with seen eq E
    ... | (l , x) = (inC (proj₂ l) , tt , l , ck) , R , (x , E) , tt , os
    keep (i-ccopyω eq) (_ , ck) R (E , _ , os) with seen eq E
    ... | (l , x) = (inC (proj₂ l) , tt , l , ck) , R , (x , E) , tt , os
    keep (i-ncopy eq) (_ , ck) R (E , _ , os) with seen eq E
    ... | (n , p) = (inC (ncty n) , tt , n , ck) , R , (p , E) , tt , os
    keep (i-cfree {lam = lam}) (_ , ck) R (E , (l , x) , os) = (inF (lam-X lam l) , ck) , R , E , x , os
    keep i-nfree  (_ , ck) R (E , (n , p) , os) = (inF (ncty n) , ck) , R , E , p , os

    keeps : ∀ {T sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m m′ n n′ t}
          → StepsI c r m n t c′ r′ m′ n′ → CIn c → RIn r → MIn m → CIn c′ × RIn r′ × MIn m′
    keeps done C R M = C , R , M
    keeps (s ⟫ st) C R M with keep s C R M
    ... | (C′ , R′ , M′) = keeps st C′ R′ M′

------------------------------------------------------------------------
-- 3. ★ A PROGRAM'S IMAGE STAYS INSIDE ITS UNIVERSE, at every configuration
-- it reaches: the code, the return stack and every value.
------------------------------------------------------------------------

module ProgramRun {Γ} (ds : Defs Γ) (f : LTm Γ One One) where
  open Program ds f
  open Keep U public

  ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U
  ncty n = ∈-++⁺ʳ (cmap subs (ts g₀)) (∈-cmap⁺ (ns g₀) n (here refl))

  open Steps blocks-in ncty public

  inside : ∀ {sh U′} {c′ : Codeᴵ sh U′} {r′ : Ret U′ (One ∷ [] ∣ One ∷ [])} {m′ n′ mt}
         → StepsI (compᴵ ds f end) ([]ʳ {T = One ∷ [] ∣ One ∷ []}) start 0 mt c′ r′ m′ n′
         → CIn c′ × RIn r′ × MIn m′
  inside st = keeps st (start-in tt) tt ((tt , tt) , tt , tt)
