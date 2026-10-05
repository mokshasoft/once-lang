-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ THE LIB'S `Sig`, WRITTEN IN THE CORE.
--                        (PLAN-BIDI S7b step 3, the spike)
--
-- `Lib/Syn`'s signatures and their decoder `SD`, as core definitions
-- checked by `Algorithm/SigBuild` — no derivation written.  A signature
-- is a FINITE MAP, so it is represented as one (Fin-indexed functions):
--
--     Fld   n = Σ (t : Fin 3). case t of  rec ↦ Fin n × Nat   (sort, binders)
--                                         nat ↦ Unit
--                                         cls ↦ Fin n          (sort)
--     Shape n = Σ (b : Fin 2). case b of  fields ↦ Σ (len : Nat). Fin len → Fld n
--                                         var    ↦ Unit
--     Sig   n = Fin n → Σ (c : Nat). Fin c → Shape n
--
-- So selection is APPLICATION, a list fold is `natrec` on its length
-- (head `fs fzero`, tail `λ y. fs (fsuc y)`), and the arities `⌜Fin⌝ c`
-- are TERMS — what S7b step 2 (`Fin` indexed by a Nat term) bought.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.SigCore where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( ε; _∙; vz; vs )
open import DirectedHoTT.Metatheory.Signature using ( WfSig )
open import DirectedHoTT.Algorithm.Surface

private
  pattern v₀ = var vz
  pattern v₁ = var (vs vz)
  pattern v₂ = var (vs (vs vz))
  pattern v₃ = var (vs (vs (vs vz)))
  pattern v₄ = var (vs (vs (vs (vs vz))))
  pattern v₅ = var (vs (vs (vs (vs (vs vz)))))
  pattern v₆ = var (vs (vs (vs (vs (vs (vs vz))))))
  pattern v₇ = var (vs (vs (vs (vs (vs (vs (vs vz)))))))
  pattern v₈ = var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))
  pattern v₉ = var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))
  pattern v₁₀ = var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))

  -- numerals
  n₁ n₂ n₃ : {Γ : _} → STm Γ
  n₁ = nsuc nzero
  n₂ = nsuc n₁
  n₃ = nsuc n₂

  wk : {Γ : _} → STm Γ → STm _
  wk = renTmˢ vs

------------------------------------------------------------------------
-- The entries.
------------------------------------------------------------------------

pattern #SI    = 0      -- the index code: a sort and a depth
pattern #add   = 1      -- k + d
pattern #FlC   = 2      -- a field's payload code, by its tag
pattern #Fld   = 3
pattern #ShC   = 4      -- a shape's payload code, by its tag
pattern #Shape = 5
pattern #Sig   = 6
pattern #tel   = 7      -- a shape's telescope at an index
pattern #tabD  = 8      -- a table of descriptions, as a case cascade
pattern #SD    = 9      -- ★ the decoder
pattern #lamΣ  = 10     -- a test signature: the scoped λ-calculus

private
  SIc : {Γ : _} → STm Γ → STm Γ
  SIc n = app (ref #SI) n
  FlC ShC : {Γ : _} → STm Γ → STm Γ → STm Γ
  FlC n t = app (app (ref #FlC) n) t
  ShC n b = app (app (ref #ShC) n) b

  ----------------------------------------------------------------------
  -- ★ the telescope of a shape, in context [n , sh , i]
  ----------------------------------------------------------------------

  -- a field list's cons step, in context [n , sh , i , p , m , ih , fs]
  CONS : STm ((((((ε ∙) ∙) ∙) ∙) ∙) ∙)
  CONS = lam □ᵀ (app (fcase □ MOTD (fst (app v₀ (fzero □))) REC NC) (snd (app v₀ (fzero □))))
    where
      -- the rest of the list: ih at the tail `λ y. fs (fsuc y)`
      rest : STm _
      rest = app v₁ (lam □ᵀ (app v₁ (fsuc □ v₀)))
      -- motive over the field's tag t: its payload, to a Desc
      MOTD : STy _
      MOTD = Π (El (FlC v₇ v₀)) (Desc (SIc v₈))
      -- rec s k ↦ a recursive position at (s , k + depth)
      REC : STm _
      REC = lam (Σ' (Fin v₆) Nat) (dρ □ (pair □ᵀ □ᵀ (fst v₀) (app (app (ref #add) (snd v₀)) (snd v₅))) (wk rest))
      -- nat ↦ a natural field ; cls s ↦ a closed subterm at (s , 0)
      NC : STm _
      NC = fcase □ MOTD' v₀ (lam □ᵀ (dσ □ ⌜Nat⌝ (lam □ᵀ (wk (wk (wk rest))))))
             (fcase □ MOTD'' v₀ (lam □ᵀ (dρ □ (pair □ᵀ □ᵀ v₀ nzero) (wk (wk (wk rest)))))
               (fcase0 □ᵀ v₀))
        where
          MOTD' MOTD'' : STy _
          MOTD'  = Π (El (FlC v₈ (fsuc □ v₀))) (Desc (SIc v₉))
          MOTD'' = Π (El (FlC v₉ (fsuc □ (fsuc □ v₀)))) (Desc (SIc v₁₀))

  TEL : STm (((ε ∙) ∙) ∙)
  TEL = app (fcase □ MOT (fst v₁) FIELDS VAR) (snd v₁)
    where
      -- motive over the shape's tag b: its payload, to a Desc
      MOT : STy _
      MOT = Π (El (ShC v₃ v₀)) (Desc (SIc v₄))
      -- fields: fold the list (natrec on its length)
      FIELDS : STm _
      FIELDS = lam (Σ' Nat (Π (Fin v₀) (El (app (ref #Fld) v₄)))) (app (natrec MOTF (lam □ᵀ (dι □)) CONS (fst v₀)) (snd v₀))
        where
          MOTF : STy _
          MOTF = Π (Π (Fin v₀) (El (app (ref #Fld) v₅))) (Desc (SIc v₅))
      -- var ↦ a variable of the depth (snd i)
      VAR : STm _
      VAR = lam □ᵀ (dσ □ (⌜Fin⌝ (snd v₂)) (lam □ᵀ (dι □)))

interleaved mutual
  tys : ℕ → STy ε
  tms : ℕ → STm ε

  -- SI n = Σ (s : Fin n) Nat
  tys #SI = Π Nat U
  tms #SI = lam □ᵀ (⌜Σ⌝ (⌜Fin⌝ v₀) ⌜Nat⌝)

  -- add k d = k + d (by recursion on k)
  tys #add = Π Nat (Π Nat Nat)
  tms #add = lam □ᵀ (lam □ᵀ (natrec □ᵀ v₀ (nsuc v₀) v₁))

  -- FlC n t: rec ↦ Fin n × Nat ; nat ↦ Unit ; cls ↦ Fin n
  tys #FlC = Π Nat (Π (Fin n₃) U)
  tms #FlC = lam □ᵀ (lam □ᵀ
               (fcase □ □ᵀ v₀ (⌜Σ⌝ (⌜Fin⌝ v₁) ⌜Nat⌝)
                 (fcase □ □ᵀ v₀ ⌜Unit⌝
                   (fcase □ □ᵀ v₀ (⌜Fin⌝ v₃) (fcase0 □ᵀ v₀)))))

  tys #Fld = Π Nat U
  tms #Fld = lam □ᵀ (⌜Σ⌝ (⌜Fin⌝ n₃) (FlC v₁ v₀))

  -- ShC n b: fields ↦ Σ (len : Nat). Fin len → Fld n ; var ↦ Unit
  tys #ShC = Π Nat (Π (Fin n₂) U)
  tms #ShC = lam □ᵀ (lam □ᵀ
               (fcase □ □ᵀ v₀ (⌜Σ⌝ ⌜Nat⌝ (⌜Π⌝ (⌜Fin⌝ v₀) (app (ref #Fld) v₃)))
                 (fcase □ □ᵀ v₀ ⌜Unit⌝ (fcase0 □ᵀ v₀))))

  tys #Shape = Π Nat U
  tms #Shape = lam □ᵀ (⌜Σ⌝ (⌜Fin⌝ n₂) (ShC v₁ v₀))

  -- Sig n = Fin n → Σ (c : Nat). Fin c → Shape n
  tys #Sig = Π Nat U
  tms #Sig = lam □ᵀ (⌜Π⌝ (⌜Fin⌝ v₀) (⌜Σ⌝ ⌜Nat⌝ (⌜Π⌝ (⌜Fin⌝ v₀) (app (ref #Shape) v₃))))

  -- ★ tel n sh i : Desc (SI n) — a shape's telescope at the index i
  tys #tel = Π Nat (Π (El (app (ref #Shape) v₀)) (Π (El (SIc v₁)) (Desc (SIc v₂))))
  tms #tel = lam □ᵀ (lam □ᵀ (lam □ᵀ TEL))

  -- tabD n c f = λ k. case k of 0 ↦ f 0 ; suc k' ↦ tabD (λ y. f (suc y)) k' —
  --   so a table of descriptions IS the Lib's `selF` cascade (`Lib/Sugar.sel`)
  tys #tabD = Π Nat (Π Nat (Π (Π (Fin v₀) (Desc (SIc v₂))) (Π (Fin v₁) (Desc (SIc v₃)))))
  tms #tabD = lam □ᵀ (lam □ᵀ (natrec MT
                (lam □ᵀ (lam □ᵀ (fcase0 □ᵀ v₀)))
                (lam □ᵀ (lam □ᵀ (fcase □ □ᵀ v₀ (app v₁ (fzero □))
                                   (app (app v₃ (lam □ᵀ (app v₃ (fsuc □ v₀)))) v₀))))
                v₀))
    where
      MT : STy _
      MT = Π (Π (Fin v₀) (Desc (SIc v₃))) (Π (Fin v₁) (Desc (SIc v₄)))

  -- ★ SD n sg i : Desc (SI n) — the Lib's `Dₛ`: per sort its constructor
  --   table (`Dσ`), selected by the sort tag; mapped FIRST, then tabulated
  tys #SD = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (El (SIc v₁)) (Desc (SIc v₂))))
  tms #SD = lam □ᵀ (lam □ᵀ (lam □ᵀ
              (app (app (app (app (ref #tabD) v₂) v₂) (lam □ᵀ PERSORT)) (fst v₀))))
    where
      -- context n , sg , i , s
      PERSORT : STm _
      PERSORT = dσ □ (⌜Fin⌝ (fst (app v₂ v₀)))
                  (app (app (app (ref #tabD) v₃) (fst (app v₂ v₀)))
                       (lam □ᵀ (app (app (app (ref #tel) v₄) (app (snd (app v₃ v₁)) v₀)) v₂)))

  -- ★ TEST: the scoped λ-calculus, one sort:  var | lam (rec 0 1) | app (rec 0 0) (rec 0 0)
  tys #lamΣ = El (app (ref #Sig) n₁)
  tms #lamΣ = lam □ᵀ (pair □ᵀ □ᵀ n₃ (lam (Fin n₃)
                (fcase □ □ᵀ v₀ VARSH (fcase □ □ᵀ v₀ LAMSH (fcase □ □ᵀ v₀ APPSH (fcase0 □ᵀ v₀))))))
    where
      REC : {Γ : _} → STm Γ → STm Γ → STm Γ
      REC s k = pair (Fin n₃) (El (FlC n₁ v₀)) (fzero □) (pair (Fin n₁) Nat s k)
      FIELDS : {Γ : _} → STm Γ → STm Γ → STm Γ
      FIELDS len fs = pair (Fin n₂) (El (ShC n₁ v₀)) (fzero □)
                        (pair Nat (Π (Fin v₀) (El (app (ref #Fld) n₁))) len fs)
      VARSH LAMSH APPSH : {Γ : _} → STm Γ
      VARSH = pair (Fin n₂) (El (ShC n₁ v₀)) (fsuc □ (fzero □)) unit
      LAMSH = FIELDS n₁ (lam (Fin n₁) (REC (fzero □) n₁))
      APPSH = FIELDS n₂ (lam (Fin n₂) (REC (fzero □) nzero))

  tys _ = Unit
  tms _ = unit

open import DirectedHoTT.Algorithm.SigBuild 11 tys tms 1000 public

open import normalizer.Syntax.Types using ( _≡_; refl; _×_; _,_ )
open import DirectedHoTT.Spec.Signature using ( Sig )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Algorithm.Eval using ( eval; nfd; out )
open import DirectedHoTT.Lib.NatNum using ( num )
import DirectedHoTT.Lib.Syn as L

-- ★ the core is well-formed: the checker's output, nothing written
wf : WfSig S
wf = fromJust wfSig _

------------------------------------------------------------------------
-- ★ FAITHFULNESS: the core decoder at the test signature HAS THE SAME
--   NORMAL FORM as the Lib's `SD` at the Lib's signature.
------------------------------------------------------------------------

private
  nfOf : R.RTm ε → R.RTm ε
  nfOf t with eval 100000 t
  ... | nfd u _ _ = u
  ... | out u _   = u

  libΣ : L.Sig 1
  libΣ = (L.vʰ L.∷ˢʰ (L.rec 0 1 L.∷ʰ L.[]ʰ) L.∷ˢʰ (L.rec 0 0 L.∷ʰ L.rec 0 0 L.∷ʰ L.[]ʰ) L.∷ˢʰ L.[]ˢʰ) L.∷ᵍ L.[]ᵍ

  coreD : R.RTm ε
  coreD = R.app (R.app (Sig.body S #SD) (num 1)) (Sig.body S #lamΣ)

sd-faithful : nfOf coreD ≡ nfOf (L.SD libΣ)
sd-faithful = refl

-- …and both sides REACHED their normal forms (not the fuel's end)
private
  open import Agda.Builtin.Bool using ( Bool; true; false )
  normal? : R.RTm ε → Bool
  normal? t with eval 100000 t
  ... | nfd _ _ _ = true
  ... | out _ _   = false

sd-normal : (normal? coreD ≡ true) × (normal? (L.SD libΣ) ≡ true)
sd-normal = refl , refl
