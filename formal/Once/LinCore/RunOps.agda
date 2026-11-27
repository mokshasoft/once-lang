-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.RunOps — plan 0.146 B1.5 (D450): A RUN'S OPS ARE ITS
-- PROGRAM'S. A run of a term whose ops (and whose table's) all satisfy `D`,
-- on values whose closures' bodies are such terms, cuts only at a `D` op
-- (`Spends.CutsIn D`), and gives such values. By recursion on the run: the
-- terms it runs are subterms, a label's body (the table's), or a closure's
-- body (a value's, built from a subterm); a ν's observation runs `obsT`,
-- which names no op.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.RunOps (fmt : TargetNum) (ans : FFIAnswers) (bw : Base → ℕ) where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (funit; fvoid; fw; _f*_; _f+_; Base)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Keys fmt bw using (Got; _⊹_; ∅; k!; t!; ps; tmGot; defsGot)
open import Once.LinCore.Image fmt bw using (kbody1)
open import Once.LinCore.Spends fmt ans bw using (CutsIn; CutsInM)
open import Once.LinCore.Total fmt ans bw using (_~_; ~one; ~pair; ~inl; ~inr; ~base; ~mu; ~ct; ~fn; ~nu; copy-~)

module _ (D : Sig → Set) where
  -- a collection's ops are D's
  Ok : Got → Set
  Ok G = ∀ {s} → s ∈ ps G → D s

  okˡ : ∀ {G H} → Ok (G ⊹ H) → Ok G
  okˡ k m = k (∈-++⁺ˡ m)

  okʳ : ∀ {G H} → Ok (G ⊹ H) → Ok H
  okʳ {G} k m = k (∈-++⁺ʳ (ps G) m)

  -- (D480: a kept owned body's lent form runs its ops and no others)
  ok-cin : ∀ {Γ} (ds : Defs Γ) {X A B} (b₀ : Tm Γ One (X ⊗t A) B) → Ok (tmGot ds b₀) → Ok (tmGot ds (cin b₀))
  ok-cin ds b₀ k m = go (∈-++⁻ (ps (tmGot ds b₀)) m)
    where
      go : ∀ {s} → (s ∈ ps (tmGot ds b₀)) ⊎ (s ∈ []) → D s
      go (inj₁ p) = k p
      go (inj₂ ())

  -- (sealed: evidence in types, performance-patterns A3, A8)
  opaque
   ok-⊹ : ∀ G H → Ok G → Ok H → Ok (G ⊹ H)
   ok-⊹ G H a b m = go (∈-++⁻ (ps G) m)
     where
       go : ∀ {s} → (s ∈ ps G) ⊎ (s ∈ ps H) → D s
       go (inj₁ p) = a p
       go (inj₂ p) = b p

   -- (D493: a body's owned form runs its ops and no others)
   ok-own : ∀ {Γ} (ds : Defs Γ) {X A B} {b : Tm Γ X A B} (o : Own b) → Ok (tmGot ds b) → Ok (tmGot ds (ownT o))
   ok-own ds {X} {A} {B} {b} o-bg k =
     ok-⊹ (tmGot ds (lul {A = B} {E = One} ∘l (drop {A = X} ⊗l lid {A = B}))) (tmGot ds b) (λ ()) k
   ok-own ds o-ev k = λ ()
   ok-own ds {X₁ ⊗t X₂} {A} (o-fst {f = f} o) k =
     ok-⊹ (tmGot ds (ownT o)) (tmGot ds ((ρl ∘l (lid {A = X₁} ⊗l drop {A = X₂})) ⊗l lid {A = A} {E = One})) (ok-own ds o k) (λ ())
   ok-own ds {X₁ ⊗t X₂} {A} (o-snd {f = f} o) k =
     ok-⊹ (tmGot ds (ownT o)) (tmGot ds ((lul ∘l (drop {A = X₁} ⊗l lid {A = X₂})) ⊗l lid {A = A} {E = One})) (ok-own ds o k) (λ ())
   ok-own ds (o-split {f = f} {g = g} p q) k =
     ok-⊹ (tmGot ds (ownT p)) (tmGot ds (ownT q) ⊹ ∅) (ok-own ds p (okˡ {tmGot ds f} {tmGot ds g} k))
       (ok-⊹ (tmGot ds (ownT q)) ∅ (ok-own ds q (okʳ {tmGot ds f} {tmGot ds g} k)) (λ ()))
   ok-own ds (o-case {f = f} {g = g} p q) k =
     ok-⊹ (tmGot ds (ownT p) ⊹ tmGot ds (ownT q)) ∅
       (ok-⊹ (tmGot ds (ownT p)) (tmGot ds (ownT q)) (ok-own ds p (okˡ {tmGot ds f} {tmGot ds g} k)) (ok-own ds q (okʳ {tmGot ds f} {tmGot ds g} k)))
       (λ ())

  -- a term with its table
  TmOK : ∀ {Γ} → Defs Γ → ∀ {E A B} → Tm Γ E A B → Set
  TmOK ds t = Ok (tmGot ds t) × Ok (defsGot ds)

  LamOk : ∀ {k g X A B} → Lam k g X A B → Set
  LamOk (c1 ds b γ) = TmOK ds b
  LamOk (cω ds b γ) = TmOK ds b
  LamOk (cωᶜ ds b₀ γ) = TmOK ds b₀

  VOk : ∀ {A} → MV A → Set
  VOk mone          = ⊤
  VOk (mpair a b)   = VOk a × VOk b
  VOk (minl a)      = VOk a
  VOk (minr b)      = VOk b
  VOk (mbase x)     = ⊤
  VOk (mmu i v)     = VOk v
  VOk (mct x)       = VOk x
  VOk (mfn i lam x) = LamOk lam × VOk x
  VOk (mnu i p)     = VOk p

  OutOK : ∀ {B} → Outcome B → Set
  OutOK (gives w _) = VOk w
  OutOK (stop _)    = ⊤

  -- a copy has its original's closures
  vok-~ : ∀ {A} {a a′ : MV A} → a ~ a′ → VOk a′ → VOk a
  vok-~ ~one          v        = tt
  vok-~ (~pair p q)   (a , b)  = vok-~ p a , vok-~ q b
  vok-~ (~inl p)      a        = vok-~ p a
  vok-~ (~inr p)      b        = vok-~ p b
  vok-~ ~base         v        = tt
  vok-~ (~mu p)       v        = vok-~ p v
  vok-~ (~ct p)       v        = vok-~ p v
  vok-~ (~fn p)       (l , x)  = l , vok-~ p x
  vok-~ (~nu p)       v        = vok-~ p v

  tag-ok : ∀ {l X} F (x : MV (LF∙ F X)) → VOk x → VOk (tag {l = l} F x)
  tag-ok Idf      x            v        = v
  tag-ok Kone     x            v        = v
  tag-ok Kzero    ()
  tag-ok (Kb b)   x            v        = v
  tag-ok (Kμ G)   x            v        = v
  tag-ok (G ⊕f H) (minl x)     v        = tag-ok G x v
  tag-ok (G ⊕f H) (minr x)     v        = tag-ok H x v
  tag-ok (G ⊗f H) (mpair x x′) (v , v′) = tag-ok G x v , tag-ok H x′ v′

  mvF-ok : ∀ a (y : ⟦ a ⟧f) → VOk (mvF a y)
  mvF-ok funit    y        = tt
  mvF-ok fvoid    ()
  mvF-ok (fw b)   y        = tt
  mvF-ok (a f* b) (x , y)  = mvF-ok a x , mvF-ok b y
  mvF-ok (a f+ b) (inj₁ x) = mvF-ok a x
  mvF-ok (a f+ b) (inj₂ y) = mvF-ok b y

  either : ∀ {s} xs {ys} → s ∈ xs ++ ys → (s ∈ xs → D s) → (s ∈ ys → D s) → D s
  either xs m l r = sel (∈-++⁻ xs m)
    where
      sel : _ → _
      sel (inj₁ a) = l a
      sel (inj₂ b) = r b

  -- a label's body, from its table
  BodyOK : ∀ {Γ σ} → Defs Γ → Body Γ σ → Set
  BodyOK ds (b1 b γ) = Ok (tmGot ds b)
  BodyOK ds (bω b γ) = Ok (tmGot ds b)

  private
    here-ok : ∀ {Γ σ} (ds : Defs Γ) (b : Body Γ σ) → Ok (defsGot (ds ▸ b)) → Ok (defsGot ds) × BodyOK ds b
    here-ok ds (b1 b γ) k = (λ m → k (∈-++⁺ˡ m)) , (λ m → k (∈-++⁺ʳ (ps (defsGot ds)) m))
    here-ok ds (bω b γ) k = (λ m → k (∈-++⁺ˡ m)) , (λ m → k (∈-++⁺ʳ (ps (defsGot ds)) m))

  look-ok : ∀ {Γ Δ l σ} {ds : Defs Γ} {p : Γ ∋[ l ] σ} {ds′ : Defs Δ} {b : Body Δ σ}
          → Look ds p ds′ b → Ok (defsGot ds) → Ok (defsGot ds′) × BodyOK ds′ b
  look-ok (lk-here {ds = ds} {b = b}) k = here-ok ds b k
  look-ok (lk-there {ds = ds} {c = b1 _ _} l) k = look-ok l (λ m → k (∈-++⁺ˡ m))
  look-ok (lk-there {ds = ds} {c = bω _ _} l) k = look-ok l (λ m → k (∈-++⁺ˡ m))

  -- the observation's code names no op
  strL-ok : ∀ {Γ} (ds : Defs Γ) F G S → Ok (tmGot ds (strL F G S))
  strL-ok ds F Idf      S ()
  strL-ok ds F Kone     S ()
  strL-ok ds F Kzero    S ()
  strL-ok ds F (Kb b)   S ()
  strL-ok ds F (Kμ G)   S ()
  strL-ok ds F (G ⊕f H) S m = either (ps (tmGot ds (strL F G S))) m (strL-ok ds F G S) (strL-ok ds F H S)
  strL-ok ds F (G ⊗f H) S m = either (ps (tmGot ds (strL F G S))) m (strL-ok ds F G S) (strL-ok ds F H S)

  mapNu-ok : ∀ {Γ} (ds : Defs Γ) F G S → Ok (tmGot ds (mapNu F G S))
  mapNu-ok ds F Idf      S ()
  mapNu-ok ds F Kone     S ()
  mapNu-ok ds F Kzero    S ()
  mapNu-ok ds F (Kb b)   S ()
  mapNu-ok ds F (Kμ G)   S ()
  mapNu-ok ds F (G ⊕f H) S m = either (ps (tmGot ds (mapNu F G S))) m (mapNu-ok ds F G S) (mapNu-ok ds F H S)
  mapNu-ok ds F (G ⊗f H) S m = either (ps (tmGot ds (mapNu F G S))) m (mapNu-ok ds F G S) (mapNu-ok ds F H S)

  obsT-ok : ∀ {Γ} (ds : Defs Γ) F S → Ok (tmGot ds (obsT F S))
  obsT-ok ds F S m =
    either (ps (tmGot ds (mapNu F F S))) m (mapNu-ok ds F F S)
      (λ m′ → either (ps (tmGot ds (strL F F S))) m′ (strL-ok ds F F S) (λ ()))

  -- ★★ a run of D's ops on D's values cuts only at D's ops, and gives D's values
  mutual
    run-ok : ∀ {Γ} {ds : Defs Γ} {E A B} {f : Tm Γ E A B} {e v n o t} (r : Run ds f e v n o t)
           → TmOK ds f → VOk e → VOk v → CutsIn D r × OutOK o
    run-ok r-id _ ek vk = tt , vk
    run-ok {ds = ds} (r-∘ {f = f} {g = g} rg (go-on rf)) (tf , td) ek vk =
      let (c₁ , ou) = run-ok rg (okʳ {tmGot ds f} {tmGot ds g} tf , td) ek vk
          (c₂ , ow) = run-ok rf (okˡ {tmGot ds f} {tmGot ds g} tf , td) ek ou
      in (c₁ , c₂) , ow
    run-ok {ds = ds} (r-∘ {f = f} {g = g} rg stopped) (tf , td) ek vk =
      proj₁ (run-ok rg (okʳ {tmGot ds f} {tmGot ds g} tf , td) ek vk) , tt
    run-ok {ds = ds} (r-⊗ {f = f} {g = g} rf (go-on (fm-gives rg))) (tf , td) ek (va , vc) =
      let (c₁ , oa) = run-ok rf (okˡ {tmGot ds f} {tmGot ds g} tf , td) ek va
          (c₂ , oc) = run-ok rg (okʳ {tmGot ds f} {tmGot ds g} tf , td) ek vc
      in (c₁ , c₂) , (oa , oc)
    run-ok {ds = ds} (r-⊗ {f = f} {g = g} rf (go-on (fm-stop rg))) (tf , td) ek (va , vc) =
      (proj₁ (run-ok rf (okˡ {tmGot ds f} {tmGot ds g} tf , td) ek va) , proj₁ (run-ok rg (okʳ {tmGot ds f} {tmGot ds g} tf , td) ek vc)) , tt
    run-ok {ds = ds} (r-⊗ {f = f} {g = g} rf stopped) (tf , td) ek (va , vc) =
      proj₁ (run-ok rf (okˡ {tmGot ds f} {tmGot ds g} tf , td) ek va) , tt
    run-ok r-ρ _ ek (va , _) = tt , va
    run-ok r-ρ⁻ _ ek va = tt , (va , tt)
    run-ok r-λ _ ek (_ , va) = tt , va
    run-ok r-λ⁻ _ ek va = tt , (tt , va)
    run-ok r-α _ ek ((a , b) , c) = tt , (a , (b , c))
    run-ok r-α⁻ _ ek (a , (b , c)) = tt , ((a , b) , c)
    run-ok r-swap _ ek (a , b) = tt , (b , a)
    run-ok (r-dup {v = v} {n}) _ ek vk = tt , (vk , vok-~ (copy-~ v n) vk)
    run-ok r-drop _ ek vk = tt , tt
    run-ok r-inl _ ek vk = tt , vk
    run-ok r-dist₁ _ ek vk = tt , vk
    run-ok r-dist₂ _ ek vk = tt , vk
    run-ok r-inr _ ek vk = tt , vk
    run-ok {ds = ds} (r-case₁ {f = f} {g = g} r) (tf , td) ek vk = run-ok r (okˡ {tmGot ds f} {tmGot ds g} tf , td) ek vk
    run-ok {ds = ds} (r-case₂ {f = f} {g = g} r) (tf , td) ek vk = run-ok r (okʳ {tmGot ds f} {tmGot ds g} tf , td) ek vk
    run-ok r-In _ ek vk = tt , vk
    run-ok r-Outμ _ ek vk = tt , vk
    run-ok (r-clo {F = F} {x = x}) _ ek vk = tt , tag-ok F x vk
    run-ok (r-app {b = b} q r) (_ , td) ek (vx , va) =
      let (td′ , tb) = look-ok q td in run-ok r (tb , td′) tt (vx , va)
    run-ok {ds = ds} (r-cata {F = F} {alg = alg} rm (go-on ra)) (tf , td) ek vk =
      let (c₁ , ou) = map-ok rm (tf , td) ek vk
          (c₂ , ow) = run-ok ra (tf , td) ek ou
      in (c₁ , c₂) , ow
    run-ok (r-cata rm stopped) tm ek vk = proj₁ (map-ok rm tm ek vk) , tt
    run-ok {ds = ds} (r-cata-reuse {F = F} {g = g} rm (go-on (fm-gives rg))) (tf , td) ek vk =
      tt , proj₂ (run-ok rg (tf , td) ek (proj₂ (map-ok rm (tf , td) ek vk)))
    run-ok (r-cata-reuse rm (go-on (fm-stop rg))) tm ek vk = tt , tt
    run-ok (r-cata-reuse rm stopped) tm ek vk = tt , tt
    run-ok (r-lend (fm-gives r)) tm ek (vx , va) = let (c , ow) = run-ok r tm (ek , vx) va in c , (vx , ow)
    run-ok (r-lend (fm-stop r)) tm ek (vx , va) = proj₁ (run-ok r tm (ek , vx) va) , tt
    run-ok (r-lift r) tm ek vk = run-ok r tm tt vk
    run-ok (r-fst r) tm (e₁ , e₂) vk = run-ok r tm e₁ vk
    run-ok (r-snd r) tm (e₁ , e₂) vk = run-ok r tm e₂ vk
    run-ok {ds = ds} (r-caseE₁ {f = f} {g = g} r) (tf , td) ek vk = run-ok r (okˡ {tmGot ds f} {tmGot ds g} tf , td) ek vk
    run-ok {ds = ds} (r-caseE₂ {f = f} {g = g} r) (tf , td) ek vk = run-ok r (okʳ {tmGot ds f} {tmGot ds g} tf , td) ek vk
    run-ok (r-out r) tm ek vk = run-ok r tm ek vk
    run-ok (r-copy {e = e} {n}) _ ek vk = tt , vok-~ (copy-~ e n) ek
    run-ok (r-bapp q r) (_ , td) ek vk = let (td′ , tb) = look-ok q td in run-ok r (tb , td′) ek vk
    run-ok {ds = ds} (r-lam {X = X} {b = b}) (tf , td) ek vk = tt , ((tf , td) , vk)
    run-ok {ds = ds} (r-lamω {X = X} {b = b} {γ = γ}) (tf , td) ek vk = tt , ((okˡ {tmGot ds b} {k! (_ , kbody1 ds (ownω b) (own-gdb b γ))} tf , td) , vk)
    run-ok {ds = ds} (r-lamωᶜ {X = X} {b₀ = b₀} {γ = γ}) (tf , td) ek vk = tt , ((okˡ {tmGot ds b₀} {k! (_ , kbody1 ds b₀ γ)} tf , td) , vk)
    run-ok (r-ev r) _ ek ((lk , vx) , va) = run-ok r lk tt (vx , va)
    run-ok (r-bev r) _ (lk , vx) va = run-ok r lk vx va
    run-ok {ds = ds} (r-bevᶜ {ds′ = ds′} {b₀ = b₀} r) _ ((ok₀ , td) , vx) va = run-ok r (ok-cin ds′ b₀ ok₀ , td) vx va
    run-ok (r-evωᶜ r) _ ek ((lk , vx) , va) = run-ok r lk tt (vx , va)
    run-ok (r-evω {ds′ = ds′} {b = b} r) _ ek (((ok₀ , td) , vx) , va) = run-ok r (subst (λ t → Ok (tmGot ds′ t)) (sym (ownω-≡ b)) (ok-own ds′ (ownOf b) ok₀) , td) tt (vx , va)
    run-ok r-unf _ ek vk = tt , vk
    run-ok {ds = ds} (r-nout {F = F} {S = S} r) (_ , td) ek vk = run-ok r (obsT-ok ds F S , td) tt vk
    run-ok r-const _ ek vk = tt , tt
    run-ok (r-op {s = s} {y = y} p) _ ek vk = tt , mvF-ok (scod s) y
    run-ok (r-opend {w = halted} p) _ ek vk = tt , tt
    run-ok (r-opend {w = exhausted} p) (tf , _) ek vk = tf (here refl) , tt
    run-ok (r-iter r (go-on done)) tm ek vk = run-ok r tm ek vk
    run-ok (r-iter r (go-on (again rn))) tm ek vk =
      let (c₁ , oa) = run-ok r tm ek vk
          (c₂ , ow) = run-ok rn tm ek oa
      in (c₁ , c₂) , ow
    run-ok (r-iter r stopped) tm ek vk = proj₁ (run-ok r tm ek vk) , tt
    run-ok r-exh _ ek vk = tt , tt
    run-ok (r-cut r q) tm ek vk = proj₁ (run-ok r tm ek vk) , tt
    run-ok (r-tmp r w p) tm ek vk = run-ok r tm ek vk

    map-ok : ∀ {Γ} {ds : Defs Γ} {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t}
             (rm : RunMap ds F alg e G x n o t) → TmOK ds (lcata F alg) → VOk e → VOk x → CutsInM D rm × OutOK o
    map-ok (m-id r) tm ek vx = run-ok r tm ek vx
    map-ok m-one tm ek vx = tt , vx
    map-ok m-b tm ek vx = tt , vx
    map-ok m-μ tm ek vx = tt , vx
    map-ok (m-inl (fm-gives r)) tm ek vx = map-ok r tm ek vx
    map-ok (m-inl (fm-stop r)) tm ek vx = proj₁ (map-ok r tm ek vx) , tt
    map-ok (m-inr (fm-gives r)) tm ek vx = map-ok r tm ek vx
    map-ok (m-inr (fm-stop r)) tm ek vx = proj₁ (map-ok r tm ek vx) , tt
    map-ok (m-pair r (go-on (fm-gives r′))) tm ek (va , vb) =
      let (c₁ , oy) = map-ok r tm ek va
          (c₂ , oy′) = map-ok r′ tm ek vb
      in (c₁ , c₂) , (oy , oy′)
    map-ok (m-pair r (go-on (fm-stop r′))) tm ek (va , vb) = (proj₁ (map-ok r tm ek va) , proj₁ (map-ok r′ tm ek vb)) , tt
    map-ok (m-pair r stopped) tm ek (va , vb) = proj₁ (map-ok r tm ek va) , tt
