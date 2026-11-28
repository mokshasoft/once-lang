-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Frame — the event semantics' FRAME RULE and NoLeak (split
-- off `Events` for the module time cap, D507): a run frees only what it
-- owns, leaves the lent frame as it was, and a whole program that returns
-- ends with the empty heap; each block allocated is freed exactly once.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _≤_; _<_; z≤n; s≤s; _≟_)
open import Relation.Nullary using (Dec)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; n≤1+n; m∸n≤m; m∸n+n≡m; n≤0⇒n≡0; ≤-antisym; m≤m+n; m≤n+m; <⇒≢)
import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; foldl)
open import Data.List.Properties using (foldl-++; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Once.LinCore.Free
  using (_≼_; []≼; ∷≼; Weave; w-[]; w-run; w-tmp; Along)
open import Once.LinCore.Free using (cmap-++; cmap-≼; cmap-weave; cmap-nil; foldl-weave; Along-++; Along-≼; Along-weave)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (subst; _≢_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.Spec.Word using (Carrier)
import Once.IR.Semantics.Value Carrier Carrier as Val
open import Once.LinCore.Flat using (Base; FTy; funit; fvoid; fw; _f*_; _f+_)

module Once.LinCore.Frame
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (funit; fvoid; fw; _f*_; _f+_; Base; Lit)
open import Once.IR.Semantics.Trace using (T; ret; call; halt; CallOp; HaltOp)
open import Once.IR.Semantics.Iterative using (T∞; return∞; bindBlock; iterBlock)
open import Once.LinCore.NbEPLinCore fmt ans
open Sem using (Lᶜ; travC; Lg)
open import Once.LinCore.Bisim fmt ans using (Bl; ≈ret; ≈step; ≈call; ≈halt; module _≈_; pair-drop; ownω-≈)
open _≈_ using (block≈)
open import Once.LinCore.Grade fmt ans using (blk-coh; obs-coh)
open import Once.LinCore.Values fmt bw
open import Once.LinCore.Events fmt ans bw
open Pre

-- the arithmetic `Events` keeps to itself
private
  +0 : ∀ x → x + 0 ≡ x
  +0 = solve-∀
  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc = solve-∀
  comm : ∀ a b → a + b ≡ b + a
  comm = solve-∀
  ≤0 : ∀ {m} → m ≤ 0 → m ≡ 0
  ≤0 z≤n = refl

  -- two exchanges in a row are one
  chain : ∀ P U H₁ W V H → P + U ≡ H₁ + W → H₁ + V ≡ H + U → P + V ≡ H + W
  chain P U H₁ W V H e₁ e₂ = Data.Nat.Properties.+-cancelʳ-≡ U (P + V) (H + W) begin′
    where
      r1 : ∀ P V U → (P + V) + U ≡ (P + U) + V
      r1 = solve-∀
      r2 : ∀ H₁ W V → (H₁ + W) + V ≡ (H₁ + V) + W
      r2 = solve-∀
      r3 : ∀ H U W → (H + U) + W ≡ (H + W) + U
      r3 = solve-∀
      begin′ : (P + V) + U ≡ (H + W) + U
      begin′ = trans (r1 P V U) (trans (cong (_+ V) e₁) (trans (r2 H₁ W V) (trans (cong (_+ W) e₂) (r3 H U W))))

  -- the halves of a pair, exchanged one after the other
  chain⊗ : ∀ P B H₁ B′ A H A′ → P + B ≡ H₁ + B′ → H₁ + A ≡ H + A′ → P + (A + B) ≡ H + (A′ + B′)
  chain⊗ P B H₁ B′ A H A′ e₁ e₂ =
    trans (r1 P A B) (trans (cong (_+ A) e₁) (trans (r2 H₁ B′ A) (trans (cong (_+ B′) e₂) (r3 H A′ B′))))
    where
      r1 : ∀ P A B → P + (A + B) ≡ (P + B) + A
      r1 = solve-∀
      r2 : ∀ H₁ B′ A → (H₁ + B′) + A ≡ (H₁ + A) + B′
      r2 = solve-∀
      r3 : ∀ H A′ B′ → (H + A′) + B′ ≡ H + (A′ + B′)
      r3 = solve-∀

exchange-map : ∀ {E A F} {alg : Tm Γ E (LF∙ F A) A} {e : MV E} {G x n o t} → RunMap ds F alg e G x n o t
             → ∀ {h r} → Pre h n x r → Lent e r → OK t h × Post t h (cnt x) o

------------------------------------------------------------------------
-- ★ The theorem.
------------------------------------------------------------------------

private
  -- one cell allocated at the counter, holding `V`
  alloc1 : ∀ {h n A} {v : MV A} {r} k (V : Heap) → Pre h n v r
         → OK (alloc (k , n) ∷ []) h × (∀ i → play (alloc (k , n) ∷ []) h i + V i ≡ h i + (δ (k , n) i + V i))
  alloc1 {h} {n} k V pre = (((λ j e → above pre j (≤-reflexive (sym e))) , tt) , λ i → assoc (h i) (δ (k , n) i) (V i))

  -- the precondition after the first event freed cell `j`
  pre-free : ∀ {h n A B} {v : MV A} {v′ : MV B} {r} j → Pre h n v r → (∀ i → step (free j) h i ≤ 1)
           → (∀ i → cnt v′ i + r i ≤ step (free j) h i) → Pre (step (free j) h) n v′ r
  pre-free {h} j pre le′ sb′ = record
    { le1 = le′
    ; above = λ i le → ≤0 (subst (step (free j) h i ≤_) (above pre i le) (m∸n≤m (h i) (δ j i)))
    ; sub = sb′ }

  -- the left half of a pair, its right half in the frame
  pre-l : ∀ {h n A B} {a : MV A} {c : MV B} {r} → Pre h n (mpair a c) r → Pre h n a (λ i → cnt c i + r i)
  pre-l {h} {a = a} {c} {r} pre = record
    { le1 = le1 pre ; above = above pre
    ; sub = λ i → subst (_≤ h i) (assoc (cnt a i) (cnt c i) (r i)) (sub pre i) }

  -- then the right half, the left half's result in the frame
  pre-r : ∀ {h n A B} {a′ : MV A} {c : MV B} {r} → Pre h n a′ (λ i → cnt c i + r i) → Pre h n c (λ i → cnt a′ i + r i)
  pre-r {h} {a′ = a′} {c} {r} pre = record
    { le1 = le1 pre ; above = above pre
    ; sub = λ i → subst (_≤ h i) (sw (cnt a′ i) (cnt c i) (r i)) (sub pre i) }
    where sw : ∀ A′ B R → A′ + (B + R) ≡ B + (A′ + R)
          sw = solve-∀

  -- a reused cell in the frame, beside the node's contents
  pre-reuse : ∀ {h n F} {j} {v : MV (LF∙ F (μt F))} {r} → Pre h n (mmu j v) r → Pre h n v (λ i → δ j i + r i)
  pre-reuse {h} {j = j} {v} {r} pre = record
    { le1 = le1 pre ; above = above pre
    ; sub = λ i → subst (_≤ h i) (sw (δ j i) (cnt v i) (r i)) (sub pre i) }
    where sw : ∀ D V R → (D + V) + R ≡ V + (D + R)
          sw = solve-∀

  -- a frame that grows keeps what is lent
  lent-w : ∀ {C r : Heap} (K : Heap) → (∀ i → 1 ≤ C i → 1 ≤ r i) → ∀ i → 1 ≤ C i → 1 ≤ K i + r i
  lent-w {r = r} K lent i p = ≤-trans (lent i p) (m≤n+m (r i) (K i))

exchange : ∀ {E A B} {f : Tm Γ E A B} {e v o n t} → Run ds f e v n o t → ∀ {h r} → Pre h n v r → Lent e r
         → OK t h × Post t h (cnt v) o
exchange r-id pre lent = (tt , λ i → refl)
exchange (r-∘ {v = v} {t₁ = t₁} {t₂} rg (go-on {u = u} {o = o} rf)) {h} pre lent =
  let (okg , eqg) = exchange rg pre lent
      (okf , eqf) = exchange rf (post rg pre okg eqg) lent
  in (OK-++ t₁ t₂ h okg okf , seqP o t₁ t₂ h (cnt v) (cnt u) eqg eqf)
exchange (r-∘ {t₁ = t₁} rg stopped) {h} pre lent = (OK-++ t₁ [] h (fst (exchange rg pre lent)) tt , tt)
exchange (r-⊗ {a = a} {c} {t₁ = t₁} {t₂} rf (go-on {u = a′} (fm-gives {u = c′} rg))) {h} {r} pre lent =
  let (oka , eqa) = exchange rf (pre-l pre) (lent-w (cnt c) lent)
      (okb , eqb) = exchange rg (pre-r {a′ = a′} {c} {r} (post rf (pre-l pre) oka eqa)) (lent-w (cnt a′) lent)
  in ( OK-++ t₁ t₂ h oka okb
     , λ i → trans (cong (λ x → x i + (cnt a i + cnt c i)) (play-++ t₁ t₂ h))
               (chain⊗ (play t₂ (play t₁ h) i) (cnt c i) (play t₁ h i) (cnt c′ i) (cnt a i) (h i) (cnt a′ i) (eqb i) (eqa i)) )
exchange (r-⊗ {c = c} {t₁ = t₁} rf stopped) {h} pre lent =
  (OK-++ t₁ [] h (fst (exchange rf (pre-l pre) (lent-w (cnt c) lent))) tt , tt)
exchange (r-⊗ {c = c} {t₁ = t₁} {t₂} rf (go-on {u = a′} (fm-stop rg))) {h} {r} pre lent =
  let (oka , eqa) = exchange rf (pre-l pre) (lent-w (cnt c) lent)
  in ( OK-++ t₁ t₂ h oka (fst (exchange rg (pre-r {a′ = a′} {c} {r} (post rf (pre-l pre) oka eqa)) (lent-w (cnt a′) lent)))
     , tt )
exchange (r-ρ {a = a}) {h} pre lent = (tt , λ i → cong (h i +_) (+0 (cnt a i)))
exchange (r-ρ⁻ {a = a}) {h} pre lent = (tt , λ i → cong (h i +_) (sym (+0 (cnt a i))))
exchange r-λ pre lent = (tt , λ i → refl)
exchange r-λ⁻ pre lent = (tt , λ i → refl)
exchange (r-α {a = a} {b} {c}) {h} pre lent = (tt , λ i → cong (h i +_) (assoc (cnt a i) (cnt b i) (cnt c i)))
exchange (r-α⁻ {a = a} {b} {c}) {h} pre lent = (tt , λ i → cong (h i +_) (sym (assoc (cnt a i) (cnt b i) (cnt c i))))
exchange (r-swap {a = a} {b}) {h} pre lent = (tt , λ i → cong (h i +_) (comm (cnt a i) (cnt b i)))
exchange (r-dup {v = v} {n}) {h} pre lent =
  let (ok , eq) = copy-ok v n h (above pre) in (ok , λ i → trans (cong (_+ cnt v i) (eq i)) (r4 (h i) (cnt (fst (copy v n)) i) (cnt v i)))
  where r4 : ∀ H C V → (H + C) + V ≡ H + (V + C)
        r4 = solve-∀
exchange (r-drop {v = v}) {h} {r} pre lent =
  let (ok , eq) = free-ok v h r (le1 pre) (sub pre) in (ok , λ i → trans (eq i) (sym (+0 (h i))))
exchange r-inl pre lent = (tt , λ i → refl)
exchange r-dist₁ pre lent = (tt , λ i → refl)
exchange r-dist₂ pre lent = (tt , λ i → refl)
exchange r-inr pre lent = (tt , λ i → refl)
exchange (r-case₁ r) pre lent = exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange (r-case₂ r) pre lent = exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange (r-In {F = F} {v = v}) pre lent = alloc1 (szμ F) (cnt v) pre
exchange (r-Outμ {v = v} {i = j}) {h} {r} pre lent =
  let (hj , _ , _ , back) = free-step j (cnt v) h r (le1 pre) (sub pre) in ((hj , tt) , λ i → trans (r5 (step (free j) h i) (δ j i) (cnt v i)) (cong (_+ cnt v i) (back i)))
  where r5 : ∀ P D V → P + (D + V) ≡ (P + D) + V
        r5 = solve-∀
-- ★ D424: a closure is its environment: building one is no event, and
-- applying one is running its body on the environment and the argument.
-- D425: so is a ν, built (`lana`) or observed (`lobs`): no event of its own
exchange (r-clo {F = F} {x = x}) {h} pre lent = (tt , λ i → cong (h i +_) (sym (cnt-tag F x i)))
exchange (r-app q r) pre lent =
  exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent₀
exchange (r-cata {i = j} {v} {t₁ = t₁} {t₂} rm (go-on {u = u} {o = o} ra)) {h} {r} pre lent =
  let (hj , le′ , sb′ , back) = free-step j (cnt v) h r (le1 pre) (sub pre)
      (okm , eqm) = exchange-map rm {step (free j) h} {r} (pre-free {v′ = v} j pre le′ sb′) lent
      (oka , eqa) = exchange ra (post-gen {v = v} {w = u} {t = t₁} {r = r} (mono-map rm) (below-map rm) (pre-free {v′ = v} j pre le′ sb′) okm eqm) lent
  in ( (hj , OK-++ t₁ t₂ (step (free j) h) okm oka)
     , freeP o j (t₁ ++ t₂) h (cnt v) back (seqP o t₁ t₂ (step (free j) h) (cnt v) (cnt u) eqm eqa) )
exchange (r-cata {i = j} {v} {t₁ = t₁} rm stopped) {h} {r} pre lent =
  let (hj , le′ , sb′ , back) = free-step j (cnt v) h r (le1 pre) (sub pre)
  in ((hj , OK-++ t₁ [] _ (fst (exchange-map rm {step (free j) h} {r} (pre-free {v′ = v} j pre le′ sb′) lent)) tt) , tt)

-- ★ D507: the node sits in the frame while it is folded (as A8's), then is freed
exchange (r-cata-late {i = j} {v} {t₁ = t₁} {t₂} rm (go-on {u = u} {o = gives w n′} ra)) {h} {r} pre lent =
  let pre′ = pre-reuse pre
      lent′ = lent-w (δ j) lent
      (okm , eqm) = exchange-map rm pre′ lent′
      pre₁ = post-gen {v = v} {w = u} {t = t₁} {r = λ i → δ j i + r i} (mono-map rm) (below-map rm) pre′ okm eqm
      (oka , eqa) = exchange ra pre₁ lent′
      pre₂ = post-gen {v = u} {w = w} {t = t₂} {r = λ i → δ j i + r i} (mono ra) (below ra) pre₁ oka eqa
      h₂ = play t₂ (play t₁ h)
      (hj , _ , _ , back) = free-step j (cnt w) h₂ r (le1 pre₂) (λ i → subst (_≤ h₂ i) (sw (cnt w i) (δ j i) (r i)) (sub pre₂ i))
      eq₁₂ = seqP (gives w n′) t₁ t₂ h (cnt v) (cnt u) eqm eqa
  in ( OK-++ (t₁ ++ t₂) (free j ∷ []) h (OK-++ t₁ t₂ h okm oka) (subst (λ g → OK (free j ∷ []) g) (sym (play-++ t₁ t₂ h)) (hj , tt))
     , λ i → trans (cong (λ z → z i + (δ j i + cnt v i)) (play-++ (t₁ ++ t₂) (free j ∷ []) h))
               (trans (cong (λ g → step (free j) g i + (δ j i + cnt v i)) (play-++ t₁ t₂ h))
                 (trans (ra3 (step (free j) h₂ i) (δ j i) (cnt v i))
                   (trans (cong (_+ cnt v i) (back i))
                     (trans (cong (λ g → g i + cnt v i) (sym (play-++ t₁ t₂ h))) (eq₁₂ i))))) )
  where sw : ∀ W D R → W + (D + R) ≡ (D + W) + R
        sw = solve-∀
        ra3 : ∀ S D V → S + (D + V) ≡ (S + D) + V
        ra3 = solve-∀
exchange (r-cata-late {i = j} {v} {t₁ = t₁} {t₂} rm (go-on {u = u} {o = stop y} ra)) {h} {r} pre lent =
  let pre′ = pre-reuse pre
      lent′ = lent-w (δ j) lent
      (okm , eqm) = exchange-map rm pre′ lent′
      pre₁ = post-gen {v = v} {w = u} {t = t₁} {r = λ i → δ j i + r i} (mono-map rm) (below-map rm) pre′ okm eqm
  in (subst (λ t → OK t h) (sym (++-identityʳ (t₁ ++ t₂))) (OK-++ t₁ t₂ h okm (fst (exchange ra pre₁ lent′))) , tt)
exchange (r-cata-late {i = j} {t₁ = t₁} rm stopped) {h} pre lent =
  (subst (λ t → OK t h) (sym (trans (++-identityʳ (t₁ ++ [])) (++-identityʳ t₁))) (fst (exchange-map rm (pre-reuse pre) (lent-w (δ j) lent))) , tt)

-- ★ A8: the reused cell sits in the frame while the node is folded and rebuilt
exchange (r-cata-reuse {i = j} {v} {t₁ = t₁} {t₂} rm (go-on {u = u} (fm-gives {u = u′} rg))) {h} {r} pre lent =
  let (okm , eqm) = exchange-map rm (pre-reuse pre) (lent-w (δ j) lent)
      (okg , eqg) = exchange rg (post-gen {v = v} {w = u} {t = t₁} {r = λ i → δ j i + r i} (mono-map rm) (below-map rm) (pre-reuse pre) okm eqm)
                             (lent-w (δ j) lent)
  in ( OK-++ t₁ t₂ h okm okg
     , λ i → trans (cong (λ z → z i + (δ j i + cnt v i)) (play-++ t₁ t₂ h))
               (trans (r12 (play t₂ (play t₁ h) i) (δ j i) (cnt v i))
                 (trans (cong (_+ δ j i) (chain (play t₂ (play t₁ h) i) (cnt u i) (play t₁ h i) (cnt u′ i) (cnt v i) (h i) (eqg i) (eqm i)))
                   (r13 (h i) (cnt u′ i) (δ j i)))) )
  where r12 : ∀ P D V → P + (D + V) ≡ (P + V) + D
        r12 = solve-∀
        r13 : ∀ H W D → (H + W) + D ≡ H + (D + W)
        r13 = solve-∀
exchange (r-cata-reuse {i = j} {t₁ = t₁} rm stopped) {h} pre lent =
  (OK-++ t₁ [] h (fst (exchange-map rm (pre-reuse pre) (lent-w (δ j) lent))) tt , tt)
exchange (r-cata-reuse {i = j} {v} {t₁ = t₁} {t₂} rm (go-on {u = u} (fm-stop rg))) {h} {r} pre lent =
  let (okm , eqm) = exchange-map rm (pre-reuse pre) (lent-w (δ j) lent)
  in ( OK-++ t₁ t₂ h okm
         (fst (exchange rg (post-gen {v = v} {w = u} {t = t₁} {r = λ i → δ j i + r i} (mono-map rm) (below-map rm) (pre-reuse pre) okm eqm)
                           (lent-w (δ j) lent)))
     , tt )
-- ★ A2: the body reads `x` from the frame; `x`'s cells are neither freed nor copied
exchange (r-lend {e = e} {x} {a} (fm-gives {u = w} r)) {h} {rf} pre lent =
  let (ok , eq) = exchange r {h} {λ i → cnt x i + rf i}
                    record { le1 = le1 pre ; above = above pre
                           ; sub = λ i → subst (_≤ h i) (sw (cnt x i) (cnt a i) (rf i)) (sub pre i) }
                    (lent-pair e x lent)
  in (ok , λ i → trans (r10 _ (cnt x i) (cnt a i)) (trans (cong (_+ cnt x i) (eq i)) (r11 (h i) (cnt w i) (cnt x i))))
  where sw : ∀ E A R → (E + A) + R ≡ A + (E + R)
        sw = solve-∀
        r10 : ∀ P E A → P + (E + A) ≡ (P + A) + E
        r10 = solve-∀
        r11 : ∀ H W E → (H + W) + E ≡ H + (E + W)
        r11 = solve-∀
exchange (r-lend {e = e} {x} {a} (fm-stop r)) {h} {rf} pre lent =
  ( fst (exchange r {h} {λ i → cnt x i + rf i}
           record { le1 = le1 pre ; above = above pre
                  ; sub = λ i → subst (_≤ h i) (sw (cnt x i) (cnt a i) (rf i)) (sub pre i) }
           (lent-pair e x lent))
  , tt )
  where sw : ∀ E A R → (E + A) + R ≡ A + (E + R)
        sw = solve-∀
exchange (r-lift r) pre lent = exchange r pre lent₀
exchange (r-fst {e₁ = e₁} {e₂} r) pre lent = exchange r pre (λ i p → lent i (≤-trans p (m≤m+n (cnt e₁ i) (cnt e₂ i))))
exchange (r-snd {e₁ = e₁} {e₂} r) pre lent = exchange r pre (λ i p → lent i (≤-trans p (m≤n+m (cnt e₂ i) (cnt e₁ i))))
exchange (r-caseE₁ r) pre lent = exchange r pre lent
exchange (r-caseE₂ r) pre lent = exchange r pre lent
exchange (r-out {i = i} {v} {a} {o} {t = t} r) {h} pre lent =
  let (ok , eq) = exchange r pre (λ j p → lent j (≤-trans p (m≤n+m (cnt v j) (δ i j))))
  in ((peek-live {a = a} {e = mmu i v} pre lent i (subst (λ x → 1 ≤ x + cnt v i) (sym (δ-same i)) (s≤s z≤n)) , ok) , peekP o i t h (cnt a) eq)
exchange (r-copy {e = e} {n}) {h} pre lent =
  let (ok , eq) = copy-ok e n h (above pre) in (ok , λ i → trans (+0 _) (eq i))
-- ★ D424: a lent closure is its lent environment, lent on to the body
exchange (r-bapp q r) pre lent = exchange r pre lent
-- ★ D428 part 3: building a closure allocates its cell, holding the environment
exchange (r-lam {X = X} {x = x}) pre lent = alloc1 (szc X) (cnt x) pre
exchange (r-lamω {X = X} {x = x}) pre lent = alloc1 (szc X) (cnt x) pre
-- applying a one-shot closure frees its cell; the body takes the environment
-- and the argument, and reads nothing lent
exchange (r-ev {i = j} {x} {a} {o} {t = t} r) {h} {rf} pre lent =
  let (hj , le′ , sb′ , back) = free-step j (λ k → cnt x k + cnt a k) h rf (le1 pre)
                                  (λ k → subst (λ z → z + rf k ≤ h k) (assoc (δ j k) (cnt x k) (cnt a k)) (sub pre k))
      (ok , po) = exchange r (pre-free {v′ = mpair x a} j pre le′ sb′) lent₀
  in ( (hj , ok)
     , postV o (free j ∷ t) h (λ k → sym (assoc (δ j k) (cnt x k) (cnt a k)))
         (freeP o j t h (λ k → cnt x k + cnt a k) back po) )
-- ★ building a ν allocates its cell, holding coalgebra and seed; observing one
-- frees the cell, and `obsT` takes both, reading nothing lent
exchange (r-unf {F = F} {S} {p = p}) pre lent = alloc1 (szν F S) (cnt p) pre
exchange (r-nout {i = j} {p} {o} {t = t} r) {h} {rf} pre lent =
  let (hj , le′ , sb′ , back) = free-step j (cnt p) h rf (le1 pre) (sub pre)
      (ok , po) = exchange r (pre-free {v′ = p} j pre le′ sb′) lent₀
  in ((hj , ok) , freeP o j t h (cnt p) back po)
-- applying a lent many-use closure reads its live cell, lends the environment on
exchange (r-bev {ds′ = ds′} {b = b} {γ = γ} {i = i} {x} {a} {o} {t = t} r) {h} pre lent =
  let (ok , eq) = exchange r pre (λ j p → lent j (≤-trans p (m≤n+m (cnt x j) (δ i j))))
  in ( (peek-live {a = a} {e = mfn i (cω ds′ b γ) x} pre lent i (subst (λ z → 1 ≤ z + cnt x i) (sym (δ-same i)) (s≤s z≤n)) , ok)
     , peekP o i t h (cnt a) eq )
exchange (r-evω {i = j} {x} {a} {o} {t = t} r) {h} {rf} pre lent =
  let (hj , le′ , sb′ , back) = free-step j (λ k → cnt x k + cnt a k) h rf (le1 pre)
                                  (λ k → subst (λ z → z + rf k ≤ h k) (assoc (δ j k) (cnt x k) (cnt a k)) (sub pre k))
      (ok , po) = exchange r (pre-free {v′ = mpair x a} j pre le′ sb′) lent₀
  in ( (hj , ok)
     , postV o (free j ∷ t) h (λ k → sym (assoc (δ j k) (cnt x k) (cnt a k)))
         (freeP o j t h (λ k → cnt x k + cnt a k) back po) )
exchange (r-lamωᶜ {X = X} {x = x}) pre lent = alloc1 (szc X) (cnt x) pre
exchange (r-evωᶜ {i = j} {x} {a} {o} {t = t} r) {h} {rf} pre lent =
  let (hj , le′ , sb′ , back) = free-step j (λ k → cnt x k + cnt a k) h rf (le1 pre)
                                  (λ k → subst (λ z → z + rf k ≤ h k) (assoc (δ j k) (cnt x k) (cnt a k)) (sub pre k))
      (ok , po) = exchange r (pre-free {v′ = mpair x a} j pre le′ sb′) lent₀
  in ( (hj , ok)
     , postV o (free j ∷ t) h (λ k → sym (assoc (δ j k) (cnt x k) (cnt a k)))
         (freeP o j t h (λ k → cnt x k + cnt a k) back po) )
exchange (r-bevᶜ {ds′ = ds′} {b₀ = b} {γ = γ} {i = i} {x} {a} {o} {t = t} r) {h} pre lent =
  let (ok , eq) = exchange r pre (λ j p → lent j (≤-trans p (m≤n+m (cnt x j) (δ i j))))
  in ( (peek-live {a = a} {e = mfn i (cωᶜ ds′ b γ) x} pre lent i (subst (λ z → 1 ≤ z + cnt x i) (sym (δ-same i)) (s≤s z≤n)) , ok)
     , peekP o i t h (cnt a) eq )
exchange r-const pre lent = (tt , λ i → refl)
exchange (r-op {s = s} {x = x} {y = y} p) {h} pre lent =
  ( op-OK p h
  , λ i → trans (cong (λ g → g i + cnt x i) (op-play p h))
                (trans (cong (h i +_) (cnt-flat (sdom s) x i)) (sym (cong (h i +_) (cnt-flat (scod s) (mvF (scod s) y) i)))) )
exchange (r-opend p) {h} pre lent = (op-OK p h , tt)
exchange (r-iter {a = a} {t₁ = t₁} r (go-on done)) {h} pre lent =
  let (ok , eq) = exchange r pre lent in (OK-++ t₁ [] h ok tt , λ i → trans (cong (λ z → z i + cnt a i) (play-++ t₁ [] h)) (eq i))
exchange (r-iter {a = a} {t₁ = t₁} {t₂} r (go-on (again {a = a′} {o = o} rn))) {h} pre lent =
  let (ok₁ , eq₁) = exchange r pre lent
      (ok₂ , eq₂) = exchange rn (post-gen {v = a} {w = a′} {t = t₁} (mono r) (below r) pre ok₁ eq₁) lent
  in (OK-++ t₁ t₂ h ok₁ ok₂ , seqP o t₁ t₂ h (cnt a) (cnt a′) eq₁ eq₂)
exchange (r-iter {t₁ = t₁} r stopped) {h} pre lent = (OK-++ t₁ [] h (fst (exchange r pre lent)) tt , tt)
exchange r-exh pre lent = (tt , tt)
exchange (r-cut r q) pre lent = (OK-≼ q (fst (exchange r pre lent)) , tt)
-- ★ A13: temporaries are not the run's cells: the claim is the run's
exchange (r-tmp {v = v} {o = o} r w p) {h} pre lent =
  let (ok , po) = exchange r pre lent in (OK-weave w h ok , post-weave o w h (cnt v) po)

exchange-map (m-id r) pre lent = exchange r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map m-one pre lent = (tt , λ i → refl)
exchange-map m-b pre lent = (tt , λ i → refl)
exchange-map m-μ pre lent = (tt , λ i → refl)
exchange-map (m-inl (fm-gives r)) pre lent = exchange-map r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map (m-inl (fm-stop r)) pre lent = exchange-map r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map (m-inr (fm-gives r)) pre lent = exchange-map r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map (m-inr (fm-stop r)) pre lent = exchange-map r record { le1 = le1 pre ; above = above pre ; sub = sub pre } lent
exchange-map (m-pair {x = x} {x′} {t₁ = t₁} {t₂} r (go-on {u = y} (fm-gives {u = y′} r′))) {h} {rf} pre lent =
  let (ok₁ , eq₁) = exchange-map r (pre-l pre) (lent-w (cnt x′) lent)
      (ok₂ , eq₂) = exchange-map r′ (pre-r {a′ = y} {x′} {rf} (post-gen {v = x} {w = y} {t = t₁} {r = λ i → cnt x′ i + rf i} (mono-map r) (below-map r) (pre-l pre) ok₁ eq₁))
                                 (lent-w (cnt y) lent)
  in ( OK-++ t₁ t₂ h ok₁ ok₂
     , λ i → trans (cong (λ z → z i + (cnt x i + cnt x′ i)) (play-++ t₁ t₂ h))
               (chain⊗ (play t₂ (play t₁ h) i) (cnt x′ i) (play t₁ h i) (cnt y′ i) (cnt x i) (h i) (cnt y i) (eq₂ i) (eq₁ i)) )
exchange-map (m-pair {x′ = x′} {t₁ = t₁} r stopped) {h} pre lent =
  (OK-++ t₁ [] h (fst (exchange-map r (pre-l pre) (lent-w (cnt x′) lent))) tt , tt)
exchange-map (m-pair {x = x} {x′} {t₁ = t₁} {t₂} r (go-on {u = y} (fm-stop r′))) {h} {rf} pre lent =
  let (ok₁ , eq₁) = exchange-map r (pre-l pre) (lent-w (cnt x′) lent)
  in ( OK-++ t₁ t₂ h ok₁
         (fst (exchange-map r′ (pre-r {a′ = y} {x′} {rf} (post-gen {v = x} {w = y} {t = t₁} {r = λ i → cnt x′ i + rf i} (mono-map r) (below-map r) (pre-l pre) ok₁ eq₁))
                               (lent-w (cnt y) lent)))
     , tt )

-- ★ NoLeak, for a run that returns: a whole program, from the empty heap,
-- frees every cell it allocated, exactly once, and frees nothing else.
noleak : ∀ {f : LTm Γ One One} {n n′ t} → Run ds f mone mone n (gives mone n′) t
       → OK t (λ _ → 0) × (∀ i → play t (λ _ → 0) i ≡ 0)
noleak run =
  let (ok , eq) = exchange run {λ _ → 0} {λ _ → 0}
                    record { le1 = λ _ → z≤n ; above = λ _ _ → refl ; sub = λ _ → z≤n } lent₀
  in (ok , λ i → trans (sym (+0 _)) (eq i))

------------------------------------------------------------------------
-- 6. ★ LIFETIMES: each block allocated is freed exactly once (the user's
--    invariant, 2026-11-08).
--
-- Stated per block, on the trace itself: the events on a block `i` are
-- lifetimes, one after another — `alloc i` (born), any number of reads
-- (`peek i`), exactly one `free i` (died) — and nothing on `i` outside them.
-- `Life dead k dead` is the language (born read* died)*. Double free, free of
-- a stranger and read of a dead cell are its consequences.
--
-- It is not proved rule by rule. The rules are proved with COUNTS (`OK`, a
-- block's count checked before every event; `exchange`), because counts add
-- up and so compose under `∘l`, `⊗l` and the frame. `life` turns legal counts
-- into lifetimes once, for every trace, by induction on the trace.
------------------------------------------------------------------------

data Kind : Set where
  born read died : Kind

-- what an event does to block `i`
kd : Kind → ∀ {P : Set} → Dec P → List Kind
kd k (yes _) = k ∷ []
kd k (no _)  = []

kind : Id → Ev → List Kind
kind i (alloc j) = kd born (j ≟ᵢ i)
kind i (free j)  = kd died (j ≟ᵢ i)
kind i (peek j)  = kd read (j ≟ᵢ i)
kind i (io _ _ _) = []
kind i (stp _ _)  = []
kind i (tmp _)    = []

-- the events on block `i`, in order: a homomorphism of free monoids
on : Id → Trace → List Kind
on i = concatMap (kind i)

data St : Set where
  dead live : St

-- `Life s k s′`: from state `s`, the events `k` are lifetimes, ending in `s′`
data Life : St → List Kind → St → Set where
  done  : ∀ {s} → Life s [] s
  birth : ∀ {k s} → Life live k s → Life dead (born ∷ k) s
  use   : ∀ {k s} → Life live k s → Life live (read ∷ k) s
  death : ∀ {k s} → Life dead k s → Life live (died ∷ k) s

st : ℕ → St
st zero    = dead
st (suc _) = live

-- legal counts are lifetimes, on every trace
life : ∀ t h i → OK t h → h i ≤ 1 → Life (st (h i)) (on i t) (st (play t h i))
life []            h i _        _  = done
life (alloc j ∷ t) h i (p′ , ok) le = at (j ≟ᵢ i)
  where
    p = p′ j refl
    h′ = step (alloc j) h
    at : (d : Dec (j ≡ i)) → Life (st (h i)) (kd born d ++ on i t) (st (play t h′ i))
    at (yes q) =
      subst (λ k → Life (st (h k)) (born ∷ on k t) (st (play t h′ k))) q
        (let z = st (play t h′ j) ; e = trans (cong (_+ δ j j) p) (δ-same j) in
         subst (λ x → Life x (born ∷ on j t) z) (cong st (sym p))
               (birth (subst (λ x → Life (st x) (on j t) z) e
                             (life t h′ j ok (subst (_≤ 1) (sym e) ≤-refl)))))
    at (no ne) =
      let z = st (play t h′ i) ; e = trans (cong (h i +_) (δ-≢ ne)) (+0 (h i)) in
      subst (λ x → Life (st x) (on i t) z) e (life t h′ i ok (subst (_≤ 1) (sym e) le))
life (free j ∷ t)  h i (p , ok) le = at (j ≟ᵢ i)
  where
    h′ = step (free j) h
    at : (d : Dec (j ≡ i)) → Life (st (h i)) (kd died d ++ on i t) (st (play t h′ i))
    at (yes q) =
      subst (λ k → Life (st (h k)) (died ∷ on k t) (st (play t h′ k))) q
        (let z = st (play t h′ j) ; e = cong₂ _∸_ p (δ-same j) in
         subst (λ x → Life x (died ∷ on j t) z) (cong st (sym p))
               (death (subst (λ x → Life (st x) (on j t) z) e
                             (life t h′ j ok (subst (_≤ 1) (sym e) z≤n)))))
    at (no ne) =
      let z = st (play t h′ i) ; e = cong (h i ∸_) (δ-≢ ne) in
      subst (λ x → Life (st x) (on i t) z) e (life t h′ i ok (subst (_≤ 1) (sym e) le))
life (peek j ∷ t)  h i (p , ok) le = at (j ≟ᵢ i)
  where
    at : (d : Dec (j ≡ i)) → Life (st (h i)) (kd read d ++ on i t) (st (play t h i))
    at (yes q) =
      subst (λ k → Life (st (h k)) (read ∷ on k t) (st (play t h k))) q
        (let z = st (play t h j) in
         subst (λ x → Life x (read ∷ on j t) z) (cong st (sym p))
               (use (subst (λ x → Life x (on j t) z) (cong st p)
                           (life t h j ok (subst (λ k → h k ≤ 1) (sym q) le)))))
    at (no _) = life t h i ok le
life (io _ _ _ ∷ t) h i (_ , ok) le = life t h i ok le
life (stp _ _ ∷ t)  h i (_ , ok) le = life t h i ok le
life (tmp _ ∷ t)    h i (_ , ok) le = life t h i ok le

-- ★ the invariant, for a whole program that returns: every block it
-- allocates is freed exactly once, read only in between, and none is open at
-- the end
lifetimes : ∀ {f : LTm Γ One One} {n′ t} → Run ds f mone mone 0 (gives mone n′) t → ∀ i → Life dead (on i t) dead
lifetimes {t = t} run i =
  let (ok , empty) = noleak run in subst (λ x → Life dead (on i t) (st x)) (empty i) (life t (λ _ → 0) i ok z≤n)

-- ★ the exit exception: a run that stops (a halt, or the memory running out)
-- from an input with no cells has the same lifetimes, except that a block's
-- last one may be open: the block is live at the exit
lifetimes-exit : ∀ {A B} {f : LTm Γ A B} {a : MV A} {y t} → (∀ i → cnt a i ≡ 0) → Run ds f mone a 0 (stop y) t
               → ∀ i → Σ St (λ s → Life dead (on i t) s)
lifetimes-exit {a = a} {t = t} no-cells run i =
  ( _ , life t (λ _ → 0) i
          (fst (exchange run {λ _ → 0} {λ _ → 0}
                  record { le1 = λ _ → z≤n ; above = λ _ _ → refl
                         ; sub = λ i → subst (_≤ 0) (sym (trans (+0 (cnt a i)) (no-cells i))) z≤n } lent₀))
          z≤n )
