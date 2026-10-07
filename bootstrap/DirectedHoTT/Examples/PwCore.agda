-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ Pw IN THE CORE (PLAN-BIDI §3g, P3): a
-- `SigExtend` segment over `Examples/SigMeth`.
--
-- The convoy `#PwC`, the index `#PwJ`, the rows as the fibre method's
-- LEAVES `#PwL` (kcPi, kcHom; every other constructor the empty row), the
-- description `#PwD` on `SigMeth.#methD`, and `⌜Pw⌝` as `#Pw`.  The kcHom
-- row weakens by `SigMeth.#trav`, whose normal form IS the Knot's `wk`.
-- ★ `#PwD` has EXACTLY the normal form of the Knot's generated
--   `Knot/Pw.PwF.DF` (`Examples/NbEPwAgree`).
--
-- ⚠ Needs the COMPACTING COLLECTOR (`+RTS -c`): 84.5 s / 4.25 GB
--   (2026-10-06, after `decTo` compares BY NAMES, `Algorithm/EraName`;
--   144 s / 4.9 GB after CheckA's syntactic fast path; before that the
--   checker ran out of memory on the 52-branch rows cascade).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.PwCore where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc; _-_; _+_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; vz; vs )
open import DirectedHoTT.Metatheory.Signature using ( WfSig )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Algorithm.SigBuild using ( module SigExtend )
import DirectedHoTT.Examples.SigMeth as Base

private
  pattern v₀ = var vz
  V : {Γ : Cx} → ℕ → STm Γ
  V {ε}    _       = unit
  V {Γ ∙}  zero    = var vz
  V {Γ ∙}  (suc k) = renTmˢ vs (V {Γ} k)
  lenC : Cx → ℕ
  lenC ε     = 0
  lenC (Γ ∙) = suc (lenC Γ)
  L : {Γ : Cx} → ℕ → STm Γ
  L {Γ} ℓ = V {Γ} (lenC Γ - suc ℓ)
  T TT : Set
  T  = {Γ : Cx} → STm Γ
  TT = {Γ : Cx} → STy Γ
  _·_ : {Γ : Cx} → STm Γ → List (STm Γ) → STm Γ
  f · []       = f
  f · (x ∷ xs) = app f x · xs
  infixl 9 _·_
  λ⁺ : {Γ : Cx} → ℕ → T → STm Γ
  λ⁺ zero    b = b
  λ⁺ (suc k) b = lam □ᵀ (λ⁺ k b)
  app³ : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  app³ f a b c = app (app (app f a) b) c
  fsucⁿ : ℕ → T → T
  fsucⁿ zero    x = x
  fsucⁿ (suc i) x = fsuc □ (fsucⁿ i x)
  tag : ℕ → T
  tag k = fsucⁿ k (fzero □)
  n₂ : T
  n₂ = nsuc (nsuc nzero)

  -- ★ a dependent case cascade: the leaf list in order, the motive at
  --   depth i over the scrutinee's LEVEL; a leaf is given its first level
  fcases : (P : ℕ → ℕ → TT) → ℕ → List (ℕ → T) → {Γ : Cx} → STm Γ → STm Γ
  fcases P i []       {Γ} x = fcase0 □ᵀ x
  fcases P i (l ∷ ls) {Γ} x = fcase □ (P i (lenC Γ)) x (l (lenC Γ)) (fcases P (suc i) ls (L (lenC Γ)))

  rep : {A : Set} → ℕ → A → List A → List A
  rep zero    a xs = xs
  rep (suc k) a xs = a ∷ rep k a xs

  -- the base's entries
  #SI #Sig #tel #SD #KΣ #methD #trav #rVF #rWK #rV0 #rNK : ℕ
  #SI = 0 ; #Sig = 6 ; #tel = 13 ; #SD = 15 ; #KΣ = 21 ; #methD = 24
  #trav = 32 ; #rVF = 33 ; #rWK = 34 ; #rV0 = 35 ; #rNK = 37

-- this segment's entries
#PwC #PwJ #PwL #PwD #Pw : ℕ
#PwC = 42 ; #PwJ = 43 ; #PwL = 44 ; #PwD = 45 ; #Pw = 46

private
  -- the Knot's signature, closed
  SI₂ : T
  SI₂ = app (ref #SI) n₂
  SD₂ : T
  SD₂ = app³ (ref #SD) n₂ (tag 1) (ref #KΣ)
  KΣ : T
  KΣ = ref #KΣ
  PAY : {Γ : Cx} → STm Γ → STy Γ
  PAY D = El (dpay SI₂ SD₂ D)
  G0 : (s j : T) → T
  G0 s j = lam □ᵀ (app (app (app (app (app (ref #tel) n₂) (tag 1)) s) (app (snd (app KΣ s)) v₀)) (pair □ᵀ □ᵀ s j))
  J C : T
  J = ref #PwJ
  C = ref #PwC
  R : T → TT
  R i = Π (El (app C i)) (Desc J)

  -- Knot syntax: a term of depth d, its constructors, its weakening
  TmC : {Γ : Cx} → STm Γ → STm Γ
  TmC d = ⌜IMu⌝ SI₂ SD₂ (pair □ᵀ □ᵀ (tag 1) d)
  knode : ℕ → List T → T
  knode k as = con □ □ □ (pair □ᵀ □ᵀ (tag k) (fields as))
    where fields : List T → T
          fields []       = unit
          fields (a ∷ as) = pair □ᵀ □ᵀ a (fields as)
  kvar0 : T
  kvar0 = knode 0 (fzero □ ∷ [])
  kapp kcHom : List T → T
  kapp = knode 2
  kcHom = knode 11
  WK : (j t : T) → T
  WK j t = ref #trav · (n₂ ∷ tag 1 ∷ KΣ ∷ ref #rVF ∷ ref #rWK ∷ ref #rV0 ∷ ref #rNK
                        ∷ tag 1 ∷ j ∷ t ∷ nsuc j ∷ lam □ᵀ (fsuc □ v₀) ∷ [])

  -- ★ the rows: λ j p h c. (a row: its premises as one alternative)
  none : ℕ → T
  none b = λ⁺ 4 (dσ □ (⌜Fin⌝ nzero) (lam □ᵀ (fcase0 □ᵀ v₀)))
  one : (ℕ → T) → ℕ → T
  one X b = λ⁺ 4 (dσ □ (⌜Fin⌝ (nsuc nzero)) (lam □ᵀ (fcase □ (Desc J) v₀ (X b) (fcase0 □ᵀ v₀))))
  -- [j b, p b+1, h b+2, c b+3, the alternative b+4]
  -- kcPi: the code is its own codomain
  cPi : ℕ → T
  cPi b = dσ □ (⌜Id⌝ (TmC (nsuc (L b))) (L (b + 3)) (fst (snd (L (b + 1))))) (lam □ᵀ (dι □))
  -- kcHom: the ambient's body, then the equation
  cHom : ℕ → T
  cHom b = dσ □ (TmC (nsuc j))
             (lam □ᵀ (dρ □ (pair □ᵀ □ᵀ (pair □ᵀ □ᵀ (tag 1) j) (pair □ᵀ □ᵀ (fst p) E0))
                          (dσ □ (⌜Id⌝ (TmC (nsuc j)) c (kcHom (E0 ∷ kapp (WK j (fst (snd p)) ∷ kvar0 ∷ [])
                                                              ∷ kapp (WK j (fst (snd (snd p))) ∷ kvar0 ∷ []) ∷ [])))
                               (lam □ᵀ (dι □)))))
    where
    j p c E0 : T
    j = L b ; p = L (b + 1) ; c = L (b + 3) ; E0 = L (b + 5)

  -- the cascades' motives: over sort s (level y) / constructor k (level y)
  PS : ℕ → ℕ → TT
  PS i y = Π (Fin (fst (app KΣ S))) (Π Nat
             (Π (PAY (app (G0 S (L (y + 2))) (L (y + 1))))
                (Π (DIh SI₂ SD₂ (R (L (y + 4))) (app (G0 S (L (y + 2))) (L (y + 1))) (L (y + 3)))
                   (R (pair □ᵀ □ᵀ S (L (y + 2)))))))
    where S : T
          S = fsucⁿ i (L y)
  PK : T → ℕ → ℕ → TT
  PK S i y = Π Nat (Π (PAY (app (G0 S (L (y + 1))) K))
                (Π (DIh SI₂ SD₂ (R (L (y + 3))) (app (G0 S (L (y + 1))) K) (L (y + 2)))
                   (R (pair □ᵀ □ᵀ S (L (y + 1))))))
    where K : T
          K = fsucⁿ i (L y)
  sortLeaf : T → List (ℕ → T) → ℕ → T
  sortLeaf S rows b = lam □ᵀ (fcases (PK S) 0 rows v₀)

ty-PwC ty-PwJ ty-PwL ty-PwD ty-Pw : STy ε
tm-PwC tm-PwJ tm-PwL tm-PwD tm-Pw : STm ε
-- the convoy: the body, one binder deeper
ty-PwC = Π (El SI₂) U
tm-PwC = lam □ᵀ (TmC (nsuc (snd v₀)))
-- the index: (i , t , c)
ty-PwJ = U
tm-PwJ = ⌜Σ⌝ SI₂ (⌜Σ⌝ (⌜IMu⌝ SI₂ SD₂ v₀) (app C (var (vs vz))))
-- ★ the rows, as the method's leaves: kcPi and kcHom, every other constructor none
ty-PwL = Π (Fin n₂) (PS 0 0)
tm-PwL = lam □ᵀ (fcases PS 0 (sortLeaf (tag 0) (rep 13 none [])
                              ∷ sortLeaf (tag 1) (rep 9 none (one cPi ∷ none ∷ one cHom ∷ rep 27 none [])) ∷ []) v₀)
-- ★ the description: the fibre of the subject, the convoy applied
ty-PwD = Π (El J) (Desc J)
tm-PwD = lam □ᵀ (app (ielim □ SD₂ (Π (El (app C (var (vs vz)))) (Desc J)) (fst v₀)
                             (ref #methD · (n₂ ∷ tag 1 ∷ KΣ ∷ J ∷ C ∷ ref #PwL ∷ [])) (fst (snd v₀)))
                      (snd (snd v₀)))
-- ⌜Pw⌝ d t u
ty-Pw = Π Nat (Π (El (TmC v₀)) (Π (El (TmC (nsuc (var (vs vz))))) U))
tm-Pw = λ⁺ 3 (⌜IMu⌝ J (ref #PwD) (pair □ᵀ □ᵀ (pair □ᵀ □ᵀ (tag 1) (L 0)) (pair □ᵀ □ᵀ (L 1) (L 2))))

private
  at : {A : Set} → A → List A → ℕ → A
  at d []       _       = d
  at d (x ∷ xs) zero    = x
  at d (x ∷ xs) (suc k) = at d xs k
tys : ℕ → STy ε
tys = at Unit (ty-PwC ∷ ty-PwJ ∷ ty-PwL ∷ ty-PwD ∷ ty-Pw ∷ [])
tms : ℕ → STm ε
tms = at unit (tm-PwC ∷ tm-PwJ ∷ tm-PwL ∷ tm-PwD ∷ tm-Pw ∷ [])

open SigExtend Base.S Base.abody Base.wf 5 tys tms 1000 public

wf : WfSig S
wf = fromJust wfSig _
