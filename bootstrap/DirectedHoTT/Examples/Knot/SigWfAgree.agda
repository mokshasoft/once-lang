-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★ THE DEFINITION CONTEXT'S FORMATION IS FAITHFUL
-- (PLAN-REF K4, second half): at the quoted ambient signature,
--
--     enWfK : WfK 𝒮 → Θ ⊢ _ ∷ El (⌜WfK⌝ q𝒮)
--     decWfK : ◇ ⊢ k ∷ El (⌜WfK⌝ q𝒮) → WfK 𝒮
--
-- Entry m is read at the bound m — `Spec.Typing 𝒮 m`, the names below it —
-- by the K5 layer at `𝓃 = m` (`TypingAgree`, `Exact`, imported UNAPPLIED:
-- one instance per entry).  `⌜WfUpTo⌝ q (k+1)` computes to the pair
-- `⌜WfUpTo⌝ q k × ⌜EntryOK⌝ q k` (`WfUpTo-suc`), which needs the codes
-- natural in the signature and the bound (`⌜EntryOK⌝-sub`).
--
-- Stated at `q𝒮` as the K5 decoders are: the Knot's judgements decode to
-- the kernel's over the AMBIENT signature.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
open import DirectedHoTT.Spec.Base hiding ( _,,_; _×_ )
module DirectedHoTT.Examples.Knot.SigWfAgree (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; Σ; _,_; _×_; tt )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.SigWf using ( WfUpTo )
import DirectedHoTT.Spec.Typing as Ty
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮)
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( red→≅ᵀ; _⟶ᵀ*_; stepᵀ; doneᵀ; ⟶ᵀ*-El; ⟶ᵀ*-IMu; ⟶ᵀ*-trans; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-trans; ⟶*-natrecⁿ )
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢-cast; ⊢wk; wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using ( wk-sub )
open import DirectedHoTT.Lib.NatCode 𝒮 (Defs.size 𝒮) using ( toI )
open import DirectedHoTT.Lib.NatNum 𝒮 (Defs.size 𝒮) using ( num; ⊢num )
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( SD-sub )
open import DirectedHoTT.Examples.Knot.Sig 𝒮 wf using ( KSig )
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf using ( dep; quoteTy; quoteTm )
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( quoteCtx )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; JT-sub; tyIx; tmIx )
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf core using ( D⊢; FIBMₒ; FIBMₒ-sub )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( tAt; typesQ; bodiesQ )
open import DirectedHoTT.Examples.Knot.QuoteSig 𝒮 wf using ( q𝒮; ⊢q𝒮; typesQ-at; bodiesQ-at; sizeQ-at )
open import DirectedHoTT.Examples.Knot.SigWf 𝒮 wf core
import DirectedHoTT.Examples.Knot.TypingAgree as TA
import DirectedHoTT.Examples.Knot.Exact as EX

private
  variable
    Δ Θ : Cx

------------------------------------------------------------------------
-- 1. The codes are natural in the signature and the bound
------------------------------------------------------------------------

D⊢-sub : (σ : Sub Δ Θ) (t : RTm Δ) → subTm σ (D⊢ t) ≡ D⊢ (subTm σ t)
D⊢-sub σ t = cong₂ (λ K F → lam (app (ielim K (fst (var vz)) F (fst (snd (var vz)))) (snd (snd (var vz)))))
                   (SD-sub (extS σ) KSig)
                   (trans (FIBMₒ-sub (extS σ) (renTm vs t)) (cong FIBMₒ (wk-sub σ t)))

⌜EntryTy⌝-sub : (σ : Sub Δ Θ) (q m : RTm Δ) → subTm σ (⌜EntryTy⌝ q m) ≡ ⌜EntryTy⌝ (subTm σ q) (subTm σ m)
⌜EntryTy⌝-sub σ q m = cong₂ (λ J D → ⌜IMu⌝ J D (tyIx (dep ε) (quoteCtx ◇) (typesQ (subTm σ q) (subTm σ m))))
                            (JT-sub σ) (D⊢-sub σ (tAt q m))

⌜EntryTm⌝-sub : (σ : Sub Δ Θ) (q m : RTm Δ) → subTm σ (⌜EntryTm⌝ q m) ≡ ⌜EntryTm⌝ (subTm σ q) (subTm σ m)
⌜EntryTm⌝-sub σ q m = cong₂ (λ J D → ⌜IMu⌝ J D (tmIx (dep ε) (quoteCtx ◇) (bodiesQ (subTm σ q) (subTm σ m)) (typesQ (subTm σ q) (subTm σ m))))
                            (JT-sub σ) (D⊢-sub σ (tAt q m))

⌜EntryOK⌝-sub : (σ : Sub Δ Θ) (q m : RTm Δ) → subTm σ (⌜EntryOK⌝ q m) ≡ ⌜EntryOK⌝ (subTm σ q) (subTm σ m)
⌜EntryOK⌝-sub σ q m = cong₂ ⌜Σ⌝ (⌜EntryTy⌝-sub σ q m)
                              (trans (wk-sub σ (⌜EntryTm⌝ q m)) (cong (renTm vs) (⌜EntryTm⌝-sub σ q m)))

------------------------------------------------------------------------
-- 2. ★ One step of the recursion: the entries below k+1 are those below
--    k, and entry k
------------------------------------------------------------------------

WfUpTo-suc : (q n : RTm Δ) → ⌜WfUpTo⌝ q (nsuc n) ⟶ ⌜Σ⌝ (⌜WfUpTo⌝ q n) (renTm vs (⌜EntryOK⌝ q n))
WfUpTo-suc q n = subst' EQ (natrec-suc ⌜Unit⌝ (⌜Σ⌝ (var vz) (renTm vs E)) n)
  where
  W : RTm _
  W = ⌜WfUpTo⌝ q n
  E : RTm _
  E = ⌜EntryOK⌝ (renTm vs (renTm vs q)) (var (vs vz))
  subst' : {X Y : RTm _} → X ≡ Y → ⌜WfUpTo⌝ q (nsuc n) ⟶ ⌜Σ⌝ W X → ⌜WfUpTo⌝ q (nsuc n) ⟶ ⌜Σ⌝ W Y
  subst' refl r = r
  -- the entry under the step's binders, instantiated at n and the hypothesis
  inner : subTm (single W) (subTm (extS (single n)) E) ≡ ⌜EntryOK⌝ q n
  inner = trans (cong (subTm (single W))
                      (trans (⌜EntryOK⌝-sub (extS (single n)) (renTm vs (renTm vs q)) (var (vs vz)))
                             (cong (λ Q → ⌜EntryOK⌝ Q (renTm vs n))
                                   (trans (wk-sub (single n) (renTm vs q)) (cong (renTm vs) (wk-cancel-tm n q))))))
                (trans (⌜EntryOK⌝-sub (single W) (renTm vs q) (renTm vs n))
                       (cong₂ ⌜EntryOK⌝ (wk-cancel-tm W q) (wk-cancel-tm W n)))
  EQ : subTm (extS (single W)) (subTm (extS (extS (single n))) (renTm vs E)) ≡ renTm vs (⌜EntryOK⌝ q n)
  EQ = trans (cong (subTm (extS (single W))) (wk-sub (extS (single n)) E))
             (trans (wk-sub (single W) (subTm (extS (single n)) E)) (cong (renTm vs) inner))

------------------------------------------------------------------------
-- 3. A non-dependent pair of codes, both ways
------------------------------------------------------------------------

private
  pairΣ : {Ξ : Ctx} {A B a b : RTm ⌊ Ξ ⌋} → Ξ ⊢ B ∷ U → Ξ ⊢ a ∷ El A → Ξ ⊢ b ∷ El B →
          Ξ ⊢ pair a b ∷ El (⌜Σ⌝ A (renTm vs B))
  pairΣ {Ξ} {A} {B} {a} dB da db =
    ⊢conv (⊢pair (ty-El (⊢wk {Ξ} {El A} {B} {U} dB)) da (⊢-cast (cong El (sym (wk-cancel-tm a B))) db))
          (csymᵀ (credᵀ (El-⌜Σ⌝ A (renTm vs B))))

  halves : {A B k : RTm ε} → ◇ ⊢ k ∷ El (⌜Σ⌝ A (renTm vs B)) → (◇ ⊢ fst k ∷ El A) × (◇ ⊢ snd k ∷ El B)
  halves {A} {B} {k} dk = ⊢fst d , ⊢-cast (cong El (wk-cancel-tm (fst k) B)) (⊢snd d)
    where d = ⊢conv dk (credᵀ (El-⌜Σ⌝ A (renTm vs B)))

  -- the step, as a conversion of types
  sucᵀ : (q n : RTm Δ) → El (⌜WfUpTo⌝ q (nsuc n)) ⟶ᵀ* El (⌜Σ⌝ (⌜WfUpTo⌝ q n) (renTm vs (⌜EntryOK⌝ q n)))
  sucᵀ q n = ⟶ᵀ*-El (step (WfUpTo-suc q n) done)

  -- an entry's two judgements: the Knot index computes to the quoted one
  tyᵀ : (N : ℕ) → El (⌜EntryTy⌝ (q𝒮 {Δ}) (num N)) ⟶ᵀ* IMu JT (D⊢ (tAt q𝒮 (num N))) (tyIx (dep ε) (quoteCtx ◇) (quoteTy (Defs.type 𝒮 N)))
  tyᵀ N = stepᵀ El-⌜IMu⌝ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-pairˡ (typesQ-at 𝒮 N))))

  tmᵀ : (N : ℕ) → El (⌜EntryTm⌝ (q𝒮 {Δ}) (num N)) ⟶ᵀ* IMu JT (D⊢ (tAt q𝒮 (num N)))
                    (tmIx (dep ε) (quoteCtx ◇) (quoteTm (Defs.body 𝒮 N)) (quoteTy (Defs.type 𝒮 N)))
  tmᵀ N = stepᵀ El-⌜IMu⌝ (⟶ᵀ*-IMu (⟶*-pairʳ (⟶*-trans (⟶*-pairˡ (bodiesQ-at 𝒮 N)) (⟶*-pairʳ (⟶*-pairʳ (typesQ-at 𝒮 N))))))

  ⊢N : {Ξ : Ctx} (N : ℕ) → Ξ ⊢ num N ∷ El ⌜Nat⌝
  ⊢N N = toI (⊢num N)

------------------------------------------------------------------------
-- 4. ★ Decoding: an inhabitant is the kernel's formation, entry by entry
------------------------------------------------------------------------

decEntry : (N : ℕ) {k : RTm ε} → ◇ ⊢ k ∷ El (⌜EntryOK⌝ q𝒮 (num N)) → Ty.EntryOK 𝒮 N N
decEntry N dk = Ty.entryOK (EX.exactTy 𝒮 wf core N ◇ (Defs.type 𝒮 N) (⊢conv (Σ.fst h) (red→≅ᵀ (tyᵀ N))))
                           (EX.exactTm 𝒮 wf core N ◇ (Defs.body 𝒮 N) (Defs.type 𝒮 N) (⊢conv (Σ.snd h) (red→≅ᵀ (tmᵀ N))))
  where h = halves dk

decWf : (N : ℕ) {k : RTm ε} → ◇ ⊢ k ∷ El (⌜WfUpTo⌝ q𝒮 (num N)) → WfUpTo 𝒮 N
decWf zero    dk = tt
decWf (suc N) dk = decWf N (Σ.fst h) , decEntry N (Σ.snd h)
  where h = halves (⊢conv dk (red→≅ᵀ (sucᵀ q𝒮 (num N))))

decWfK : {k : RTm ε} → ◇ ⊢ k ∷ El (⌜WfK⌝ q𝒮) → WfK 𝒮
decWfK dk = decWf (Defs.size 𝒮) (⊢conv dk (red→≅ᵀ (⟶ᵀ*-El (⟶*-natrecⁿ (sizeQ-at 𝒮)))))

------------------------------------------------------------------------
-- 5. ★ Encoding: the kernel's formation is an inhabitant
------------------------------------------------------------------------

enEntry : (N : ℕ) → Ty.EntryOK 𝒮 N N → {Θ : Ctx} → Σ (RTm ⌊ Θ ⌋) (λ k → Θ ⊢ k ∷ El (⌜EntryOK⌝ q𝒮 (num N)))
enEntry N e {Θ} =
  pair (Σ.fst T) (Σ.fst B) , pairΣ (⊢⌜EntryTm⌝ ⊢q𝒮 (⊢N N)) (⊢conv (Σ.snd T) (csymᵀ (red→≅ᵀ (tyᵀ N)))) (⊢conv (Σ.snd B) (csymᵀ (red→≅ᵀ (tmᵀ N))))
  where
  T = TA.enTy 𝒮 wf core N (Ty.okTy e) {Θ}
  B = TA.enTm 𝒮 wf core N (Ty.okBody e) {Θ}

enWf : (N : ℕ) → WfUpTo 𝒮 N → {Θ : Ctx} → Σ (RTm ⌊ Θ ⌋) (λ k → Θ ⊢ k ∷ El (⌜WfUpTo⌝ q𝒮 (num N)))
enWf zero    _ = unit , ⊢conv ⊢unit (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans (⟶ᵀ*-El (step (natrec-zero ⌜Unit⌝ _) done)) (stepᵀ El-⌜Unit⌝ doneᵀ))))
enWf (suc N) (w , e) {Θ} =
  pair (Σ.fst W) (Σ.fst E) , ⊢conv (pairΣ (⊢⌜EntryOK⌝ ⊢q𝒮 (⊢N N)) (Σ.snd W) (Σ.snd E)) (csymᵀ (red→≅ᵀ (sucᵀ q𝒮 (num N))))
  where
  W = enWf N w {Θ}
  E = enEntry N e {Θ}

enWfK : WfK 𝒮 → {Θ : Ctx} → Σ (RTm ⌊ Θ ⌋) (λ k → Θ ⊢ k ∷ El (⌜WfK⌝ q𝒮))
enWfK w {Θ} = Σ.fst K , ⊢conv (Σ.snd K) (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (⟶*-natrecⁿ (sizeQ-at 𝒮)))))
  where K = enWf (Defs.size 𝒮) w {Θ}
