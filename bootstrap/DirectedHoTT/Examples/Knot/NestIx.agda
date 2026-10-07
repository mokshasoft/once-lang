-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — the CONVOY of a nested case on a SUBJECT FIELD (D077:
-- "a nested pattern is a nested case"): β's `app (lam t) u` cases on the
-- application's first field, `ordtr (nsuc a) nzero …` on three fields in
-- turn.  Each nested case is a `Lib/SynPat` case whose convoy carries the
-- judgement's TARGET and every payload met so far (the subject's, then
-- each pattern's) — a STACK, all at the scrutinee's own depth (a subject
-- field under a binder Fords instead, D078):
--
--     NC S st  =  Σ (target : K S d) (PS st d)
--     PS ((s , sh) ∷ st) d  =  Σ (payload sh at (s , d)) (PS st d)
--
-- Typed once, generic in the stack; read through its normal form `PSV`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Examples.Knot.NestIx (𝒮 : Defs) (wf : WfK 𝒮) where



open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮) hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢wk; ⊢-cast; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-Σˡ; ⟶ᵀ*-Σʳ; ⟶ᵀ*-IMu; ⟶*-pairʳ )
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( tag; Lt; lt-z; lt-s; tag-sub; v₀; v₁; _,ₚ_ )
open import DirectedHoTT.Lib.SynView 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( PayV; payV-red; payV-ix; PayV-sub )
open import DirectedHoTT.Lib.Tel 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- 1. The stack and its code.
------------------------------------------------------------------------

data Stk : Set where
  []ˢ   : Stk
  _,_∷ˢ_ : ℕ → Shape → Stk → Stk

data StkOK : Stk → Set where
  []ᵒ  : StkOK []ˢ
  ok∷ : {s : ℕ} {sh : Shape} {st : Stk} → Lt s 2 → ShOK 2 sh → StkOK st → StkOK (s , sh ∷ˢ st)

PS : Stk → RTm Δ → RTm Δ
PS []ˢ d = ⌜Unit⌝
PS (s , sh ∷ˢ st) d = ⌜Σ⌝ (dpay (SI 2) KD ⌜ tel sh ((tag s) ,ₚ d) ⌝ᵗ) (PS st (renTm vs d))

private
  σ-cong : (K K' X X' : RTm Δ) (Y Y' : RTm (Δ ∙)) → K ≡ K' → X ≡ X' → Y ≡ Y' →
           ⌜Σ⌝ (dpay (SI 2) K X) Y ≡ ⌜Σ⌝ (dpay (SI 2) K' X') Y'
  σ-cong K K' X X' Y Y' refl refl refl = refl

PS-sub : (σ : Sub Δ Θ) (st : Stk) (d : RTm Δ) → subTm σ (PS st d) ≡ PS st (subTm σ d)
PS-sub σ []ˢ d = refl
PS-sub σ (s , sh ∷ˢ st) d =
  σ-cong _ _ _ _ _ _ (SD-sub σ KSig)
         (trans (sub-tel σ sh ((tag s) ,ₚ d)) (cong (λ z → ⌜ tel sh (z ,ₚ (subTm σ d)) ⌝ᵗ) (tag-sub σ s)))
         (trans (PS-sub (extS σ) st (renTm vs d)) (cong (PS st) (wkS σ d)))

⊢PS : {Ξ : Ctx} {st : Stk} {d : RTm ⌊ Ξ ⌋} → StkOK st → Ξ ⊢ d ∷ El ⌜Nat⌝ → Ξ ⊢ PS st d ∷ U
⊢PS []ᵒ dd = ⊢⌜Unit⌝
⊢PS (ok∷ lt shok okst) dd = ⊢⌜Σ⌝ (⊢dpay ⊢SI ⊢KD (⊢tel ⊢SI (telOK shok (⊢ix lt dd)))) (⊢PS okst (⊢wk dd))

------------------------------------------------------------------------
-- 2. Its normal form, and the depth read off an index.
------------------------------------------------------------------------

PSV : Stk → RTm Δ → RTy Δ
PSV []ˢ d = Unit
PSV (s , sh ∷ˢ st) d = Σ' (PayV sh ((tag s) ,ₚ d) (SI 2) (SD KSig)) (PSV st (renTm vs d))

PS-red : (st : Stk) (d : RTm Δ) → El (PS st d) ⟶ᵀ* PSV st d
PS-red []ˢ d = stepᵀ El-⌜Unit⌝ doneᵀ
PS-red (s , sh ∷ˢ st) d =
  stepᵀ (El-⌜Σ⌝ _ _) (⟶ᵀ*-trans (⟶ᵀ*-Σˡ (payV-red sh ((tag s) ,ₚ d) (SI 2) (SD KSig))) (⟶ᵀ*-Σʳ (PS-red st (renTm vs d))))

PSV-ix : (st : Stk) (a j : RTm Δ) → PSV st (snd (a ,ₚ j)) ⟶ᵀ* PSV st j
PSV-ix []ˢ a j = doneᵀ
PSV-ix (s , sh ∷ˢ st) a j =
  ⟶ᵀ*-trans (⟶ᵀ*-Σˡ (payV-ix sh (tag s) a j (SI 2) (SD KSig))) (⟶ᵀ*-Σʳ (PSV-ix st (renTm vs a) (renTm vs j)))

PSV-sub : (σ : Sub Δ Θ) (st : Stk) (d : RTm Δ) → subTy σ (PSV st d) ≡ PSV st (subTm σ d)
PSV-sub σ []ˢ d = refl
PSV-sub σ (s , sh ∷ˢ st) d =
  cong₂ Σ' (trans (PayV-sub σ sh ((tag s) ,ₚ d) (SI 2) (SD KSig))
                  (cong₂ (λ t D → PayV sh (t ,ₚ (subTm σ d)) (SI 2) D) (tag-sub σ s) (SD-sub σ KSig)))
           (trans (PSV-sub (extS σ) st (renTm vs d)) (cong (PSV st) (wkS σ d)))

-- the stack's head and tail
module _ {Ξ : Ctx} {s : ℕ} {sh : Shape} {st : Stk} {d v : RTm ⌊ Ξ ⌋} where
  ⊢psHd : Ξ ⊢ v ∷ PSV (s , sh ∷ˢ st) d → Ξ ⊢ fst v ∷ PayV sh ((tag s) ,ₚ d) (SI 2) (SD KSig)
  ⊢psHd dv = ⊢fst dv

  ⊢psTl : Ξ ⊢ v ∷ PSV (s , sh ∷ˢ st) d → Ξ ⊢ snd v ∷ PSV st d
  ⊢psTl dv = ⊢-cast (trans (PSV-sub (single (fst v)) st (renTm vs d)) (cong (PSV st) (wk-cancel-tm (fst v) d))) (⊢snd dv)

  ⊢psMk : {a w : RTm ⌊ Ξ ⌋} → Ξ ⊢ a ∷ PayV sh ((tag s) ,ₚ d) (SI 2) (SD KSig) → Ξ ⊢ w ∷ PSV st d →
          (Ξ ▹ PayV sh ((tag s) ,ₚ d) (SI 2) (SD KSig)) ⊢ty PSV st (renTm vs d) →
          Ξ ⊢ pair a w ∷ PSV (s , sh ∷ˢ st) d
  ⊢psMk {a} {w} da dw ty = ⊢pair ty da (⊢-cast (sym (trans (PSV-sub (single a) st (renTm vs d)) (cong (PSV st) (wk-cancel-tm a d)))) dw)

------------------------------------------------------------------------
-- 3. ★ THE CONVOY over the scrutinee's index: the target, then the stack.
------------------------------------------------------------------------

NC : ℕ → Stk → RTm (Δ ∙)
NC S st = ⌜Σ⌝ (⌜IMu⌝ (SI 2) KD ((tag S) ,ₚ (snd v₀))) (PS st (snd v₁))

NC-sub : (S : ℕ) (st : Stk) (σ : Sub Δ Θ) → subTm (extS σ) (NC {Δ} S st) ≡ NC S st
NC-sub {Δ} {Θ} S st σ =
  c3 (SD-sub (extS σ) KSig) (tag-sub (extS σ) S) (PS-sub (extS (extS σ)) st (snd v₁))
  where
    c3 : {K K' T T' : RTm (Θ ∙)} {P P' : RTm ((Θ ∙) ∙)} → K ≡ K' → T ≡ T' → P ≡ P' →
         ⌜Σ⌝ (⌜IMu⌝ (SI 2) K (T ,ₚ (snd v₀))) P ≡ ⌜Σ⌝ (⌜IMu⌝ (SI 2) K' (T' ,ₚ (snd v₀))) P'
    c3 refl refl refl = refl

⊢NC : {S : ℕ} {st : Stk} → Lt S 2 → StkOK st → {Γ : Ctx} → (Γ ▹ El (SI 2)) ⊢ NC S st ∷ U
⊢NC lt okst = ⊢⌜Σ⌝ (⊢⌜IMu⌝ ⊢SI ⊢KD (⊢ix lt (⊢depth (⊢var here)))) (⊢PS okst (⊢depth (⊢var (there here))))

NCat : ℕ → Stk → RTm Δ → RTm Δ
NCat S st i = subTm (single i) (NC S st)

module _ {Ξ : Ctx} {j : RTm ⌊ Ξ ⌋} (S s₀ : ℕ) (st : Stk) where
  private
    ix : RTm ⌊ Ξ ⌋
    ix = pair (tag s₀) j
    B : RTm (⌊ Ξ ⌋ ∙)
    B = PS st (snd (renTm vs ix))
    eNC : NCat S st ix ≡ ⌜Σ⌝ (⌜IMu⌝ (SI 2) KD ((tag S) ,ₚ (snd ix))) B
    eNC = c3 (SD-sub (single ix) KSig) (tag-sub (single ix) S) (PS-sub (extS (single ix)) st (snd v₁))
      where
        c3 : {K K' T T' : RTm ⌊ Ξ ⌋} {P P' : RTm (⌊ Ξ ⌋ ∙)} → K ≡ K' → T ≡ T' → P ≡ P' →
             ⌜Σ⌝ (⌜IMu⌝ (SI 2) K (T ,ₚ (snd ix))) P ≡ ⌜Σ⌝ (⌜IMu⌝ (SI 2) K' (T' ,ₚ (snd ix))) P'
        c3 refl refl refl = refl
    eB : (x : RTm ⌊ Ξ ⌋) → subTy (single x) (El B) ≡ El (PS st (snd ix))
    eB x = trans (cong El (PS-sub (single x) st (snd (renTm vs ix))))
                 (cong (λ z → El (PS st (snd z))) (wk-cancel-tm x ix))
    tgtR : El (⌜IMu⌝ (SI 2) KD ((tag S) ,ₚ (snd ix))) ⟶ᵀ* K S j
    tgtR = stepᵀ El-⌜SK⌝ (⟶ᵀ*-SK (step (βsnd (tag s₀) j) done))
    stkR : El (PS st (snd ix)) ⟶ᵀ* PSV st j
    stkR = ⟶ᵀ*-trans (PS-red st (snd ix)) (PSV-ix st (tag s₀) j)
    dΣ : {c : RTm ⌊ Ξ ⌋} → Ξ ⊢ c ∷ El (NCat S st ix) → Ξ ⊢ c ∷ Σ' (El (⌜IMu⌝ (SI 2) KD ((tag S) ,ₚ (snd ix)))) (El B)
    dΣ {c} dc = ⊢conv (⊢-cast {Ξ} {c} {El (NCat S st ix)} {El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD ((tag S) ,ₚ (snd ix))) B)} (cong El eNC) dc)
                      (credᵀ (El-⌜Σ⌝ _ _))

  -- ⚠ the EXPORTED types spell the index `pair (tag s₀) j` out, never the
  --   private `ix`: `NCat` is reducible, so a caller's `NCat S st (pair …)`
  --   against `NCat S st ix` is not a syntactic match, and at a CONCRETE
  --   stack Agda substitutes through the whole closed `NC S st` code on
  --   both sides — measured 1.4 s per call, ~390 s of `Knot/Red` (2026-09-30).

  -- the target
  ⊢ncTgt : {c : RTm ⌊ Ξ ⌋} → Ξ ⊢ c ∷ El (NCat S st ((tag s₀) ,ₚ j)) → Ξ ⊢ fst c ∷ K S j
  ⊢ncTgt dc = ⊢conv (⊢fst (dΣ dc)) (red→≅ᵀ tgtR)

  -- the stack
  ⊢ncStk : {c : RTm ⌊ Ξ ⌋} → Ξ ⊢ c ∷ El (NCat S st ((tag s₀) ,ₚ j)) → Ξ ⊢ snd c ∷ PSV st j
  ⊢ncStk {c} dc = ⊢conv (⊢-cast {Ξ} {snd c} {subTy (single (fst c)) (El B)} (eB (fst c)) (⊢snd (dΣ dc))) (red→≅ᵀ stkR)

  -- …and a convoy from them
  ⊢ncMk : {X v : RTm ⌊ Ξ ⌋} → Lt s₀ 2 → StkOK st → Ξ ⊢ j ∷ El ⌜Nat⌝ →
          Ξ ⊢ X ∷ K S j → Ξ ⊢ v ∷ PSV st j → Ξ ⊢ pair X v ∷ El (NCat S st ((tag s₀) ,ₚ j))
  ⊢ncMk {X} {v} lt okst dj dX dv =
    ⊢-cast {Ξ} {pair X v} {El (⌜Σ⌝ (⌜IMu⌝ (SI 2) KD ((tag S) ,ₚ (snd ix))) B)} {El (NCat S st ix)} (cong El (sym eNC))
      (⊢conv (⊢pair tyB (⊢conv dX (csymᵀ (red→≅ᵀ tgtR)))
                        (⊢-cast {Ξ} {v} {El (PS st (snd ix))} {subTy (single X) (El B)} (sym (eB X)) (⊢conv dv (csymᵀ (red→≅ᵀ stkR)))))
             (csymᵀ (credᵀ (El-⌜Σ⌝ _ _))))
    where
      tyB : (Ξ ▹ El (⌜IMu⌝ (SI 2) KD ((tag S) ,ₚ (snd ix)))) ⊢ty El B
      tyB = ty-El (⊢PS okst (⊢depth (⊢wk (⊢ix lt dj))))

------------------------------------------------------------------------
-- 4. Stack values BUILT at the code (the tails' well-formedness is the
--    code's), read through the normal form.
------------------------------------------------------------------------

⊢psNil : {Ξ : Ctx} {d : RTm ⌊ Ξ ⌋} → Ξ ⊢ unit ∷ El (PS {⌊ Ξ ⌋} []ˢ d)
⊢psNil = ⊢conv ⊢unit (csymᵀ (credᵀ El-⌜Unit⌝))

⊢psCons : {Ξ : Ctx} {s : ℕ} {sh : Shape} {st : Stk} {d a w : RTm ⌊ Ξ ⌋} → StkOK st → Ξ ⊢ d ∷ El ⌜Nat⌝ →
          Ξ ⊢ a ∷ PayV sh ((tag s) ,ₚ d) (SI 2) (SD KSig) → Ξ ⊢ w ∷ El (PS st d) → Ξ ⊢ pair a w ∷ El (PS (s , sh ∷ˢ st) d)
⊢psCons {Ξ} {s} {sh} {st} {d} {a} {w} okst dd da dw =
  ⊢conv (⊢pair (ty-El (⊢PS okst (⊢wk dd)))
               (⊢conv da (csymᵀ (red→≅ᵀ (payV-red sh ((tag s) ,ₚ d) (SI 2) (SD KSig)))))
               (⊢-cast {Ξ} {w} {El (PS st d)} {subTy (single a) (El (PS st (renTm vs d)))}
                       (sym (trans (cong El (PS-sub (single a) st (renTm vs d))) (cong (λ z → El (PS st z)) (wk-cancel-tm a d)))) dw))
        (csymᵀ (credᵀ (El-⌜Σ⌝ _ _)))

⊢ncMkC : {Ξ : Ctx} {j X v : RTm ⌊ Ξ ⌋} (S s₀ : ℕ) (st : Stk) → Lt s₀ 2 → StkOK st → Ξ ⊢ j ∷ El ⌜Nat⌝ →
         Ξ ⊢ X ∷ K S j → Ξ ⊢ v ∷ El (PS st j) → Ξ ⊢ pair X v ∷ El (NCat S st ((tag s₀) ,ₚ j))
⊢ncMkC S s₀ st lt okst dj dX dv = ⊢ncMk S s₀ st lt okst dj dX (⊢conv dv (red→≅ᵀ (PS-red st _)))
