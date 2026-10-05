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
-- The entries.  The decoder's pieces are NAMED (`#telV` … `#tel`), so a
-- generic program can follow the decoder in lockstep (its motives mention
-- the same terms).
------------------------------------------------------------------------

pattern #SI    = 0      -- the index code: a sort and a depth
pattern #add   = 1      -- k + d
pattern #FlC   = 2      -- a field's payload code, by its tag
pattern #Fld   = 3
pattern #ShC   = 4      -- a shape's payload code, by its tag
pattern #Shape = 5
pattern #Sig   = 6
pattern #telV  = 7      -- the variable's telescope
pattern #dRec  = 8      -- one field's telescope, by kind
pattern #dNat  = 9
pattern #dCls  = 10
pattern #telF  = 11     -- one field, by its tag
pattern #telFs = 12     -- a field list (natrec on its length)
pattern #tel   = 13     -- ★ a shape's telescope at an index
pattern #tabD  = 14     -- a table of descriptions as a case cascade
pattern #SDℓ   = 15     -- the decoder in the Lib's form (map, then tabulate)
pattern #SD    = 16     -- ★ the decoder: select, then map
pattern #lamΣ  = 17     -- a test signature: the scoped λ-calculus

private
  SIc : {Γ : _} → STm Γ → STm Γ
  SIc n = app (ref #SI) n
  Dt : {Γ : _} → STm Γ → STy Γ
  Dt n = Desc (SIc n)
  FlC ShC : {Γ : _} → STm Γ → STm Γ → STm Γ
  FlC n t = app (app (ref #FlC) n) t
  ShC n b = app (app (ref #ShC) n) b
  FldT : {Γ : _} → STm Γ → STy Γ
  FldT n = El (app (ref #Fld) n)

  -- telF's body, in context [n , i , f , rest]: a case on the field's tag
  TELF : STm ((((ε ∙) ∙) ∙) ∙)
  TELF = app (fcase □ (Π (El (FlC v₄ v₀)) (Dt v₅)) (fst v₁)
                (lam (Σ' (Fin v₃) Nat) (app (app (app (app (ref #dRec) v₄) v₃) v₀) v₁))
                (fcase □ (Π (El (FlC v₅ (fsuc □ v₀))) (Dt v₆)) v₀
                   (lam □ᵀ (app (app (ref #dNat) v₅) v₂))
                   (fcase □ (Π (El (FlC v₆ (fsuc □ (fsuc □ v₀)))) (Dt v₇)) v₀
                      (lam (Fin v₅) (app (app (app (ref #dCls) v₆) v₀) v₃))
                      (fcase0 □ᵀ v₀))))
             (snd v₁)

  -- telFs's body, in context [n , i , len]: natrec on the length
  TELFS : STm (((ε ∙) ∙) ∙)
  TELFS = natrec (Π (Π (Fin v₀) (FldT v₄)) (Dt v₄)) (lam □ᵀ (dι □))
            (lam □ᵀ (app (app (app (app (ref #telF) v₅) v₄) (app v₀ (fzero □)))
                         (app v₁ (lam □ᵀ (app v₁ (fsuc □ v₀))))))
            v₀

  -- tel's body, in context [n , sh , i]: a case on the shape's tag
  TEL : STm (((ε ∙) ∙) ∙)
  TEL = app (fcase □ (Π (El (ShC v₃ v₀)) (Dt v₄)) (fst v₁)
               (lam (Σ' Nat (Π (Fin v₀) (FldT v₄))) (app (app (app (app (ref #telFs) v₃) v₁) (fst v₀)) (snd v₀)))
               (lam □ᵀ (app (app (ref #telV) v₄) v₂)))
            (snd v₁)

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

  -- the variable: a Fin of the depth
  tys #telV = Π Nat (Π (El (SIc v₀)) (Dt v₁))
  tms #telV = lam □ᵀ (lam □ᵀ (dσ □ (⌜Fin⌝ (snd v₀)) (lam □ᵀ (dι □))))

  -- rec (s , k): a recursive position at (s , k + depth)
  tys #dRec = Π Nat (Π (El (SIc v₀)) (Π (Σ' (Fin v₁) Nat) (Π (Dt v₂) (Dt v₃))))
  tms #dRec = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ
                (dρ □ (pair □ᵀ □ᵀ (fst v₁) (app (app (ref #add) (snd v₁)) (snd v₂))) v₀))))

  -- nat: a natural field
  tys #dNat = Π Nat (Π (Dt v₀) (Dt v₁))
  tms #dNat = lam □ᵀ (lam □ᵀ (dσ □ ⌜Nat⌝ (lam □ᵀ v₁)))

  -- cls s: a closed subterm, at (s , 0)
  tys #dCls = Π Nat (Π (Fin v₀) (Π (Dt v₁) (Dt v₂)))
  tms #dCls = lam □ᵀ (lam □ᵀ (lam □ᵀ (dρ □ (pair □ᵀ □ᵀ v₁ nzero) v₀)))

  tys #telF = Π Nat (Π (El (SIc v₀)) (Π (FldT v₁) (Π (Dt v₂) (Dt v₃))))
  tms #telF = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ TELF)))

  tys #telFs = Π Nat (Π (El (SIc v₀)) (Π Nat (Π (Π (Fin v₀) (FldT v₃)) (Dt v₃))))
  tms #telFs = lam □ᵀ (lam □ᵀ (lam □ᵀ TELFS))

  -- ★ tel n sh i : Desc (SI n)
  tys #tel = Π Nat (Π (El (app (ref #Shape) v₀)) (Π (El (SIc v₁)) (Dt v₂)))
  tms #tel = lam □ᵀ (lam □ᵀ (lam □ᵀ TEL))

  -- tabD n c f = λ k. case k of 0 ↦ f 0 ; suc k' ↦ tabD (λ y. f (suc y)) k' —
  --   a table of descriptions IS the Lib's `selF` cascade (`Lib/Sugar.sel`)
  tys #tabD = Π Nat (Π Nat (Π (Π (Fin v₀) (Dt v₂)) (Π (Fin v₁) (Dt v₃))))
  tms #tabD = lam □ᵀ (lam □ᵀ (natrec (Π (Π (Fin v₀) (Dt v₃)) (Π (Fin v₁) (Dt v₄)))
                (lam □ᵀ (lam □ᵀ (fcase0 □ᵀ v₀)))
                (lam □ᵀ (lam □ᵀ (fcase □ □ᵀ v₀ (app v₁ (fzero □))
                                   (app (app v₃ (lam □ᵀ (app v₃ (fsuc □ v₀)))) v₀))))
                v₀))

  -- the decoder in the Lib's form: per sort its constructor table, mapped
  --   FIRST, then tabulated — the Lib's `Dₛ` normal form, exactly
  tys #SDℓ = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (El (SIc v₁)) (Dt v₂)))
  tms #SDℓ = lam □ᵀ (lam □ᵀ (lam □ᵀ
              (app (app (app (app (ref #tabD) v₂) v₂)
                   (lam □ᵀ (dσ □ (⌜Fin⌝ (fst (app v₂ v₀)))
                              (app (app (app (ref #tabD) v₃) (fst (app v₂ v₀)))
                                   (lam □ᵀ (app (app (app (ref #tel) v₄) (app (snd (app v₃ v₁)) v₀)) v₂))))))
                   (fst v₀))))

  -- ★ SD n sg i : the sort's table SELECTED by application, then mapped —
  --   at a variable constructor k its fibre is `tel n (sg s k) i` (what a
  --   generic program over the signature needs)
  tys #SD = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (El (SIc v₁)) (Dt v₂)))
  tms #SD = lam □ᵀ (lam □ᵀ (lam □ᵀ
              (dσ □ (⌜Fin⌝ (fst (app v₁ (fst v₀))))
                    (lam □ᵀ (app (app (app (ref #tel) v₃) (app (snd (app v₂ (fst v₁))) v₀)) v₁)))))

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

open import DirectedHoTT.Algorithm.SigBuild 18 tys tms 1000 public

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
-- ★ FAITHFULNESS, by normal forms (both sides REACH theirs: `normal?`).
------------------------------------------------------------------------

private
  open import Agda.Builtin.Bool using ( Bool; true; false )
  open import DirectedHoTT.Lib.Sugar using ( tag )
  open import DirectedHoTT.Lib.Tel using ( ⌜_⌝ᵗ )

  nfOf : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ
  nfOf t with eval 100000 t
  ... | nfd u _ _ = u
  ... | out u _   = u

  normal? : {Γ : R.Cx} → R.RTm Γ → Bool
  normal? t with eval 100000 t
  ... | nfd _ _ _ = true
  ... | out _ _   = false

  -- an entry, as a kernel reference
  ⟪_⟫ : {Γ : R.Cx} → ℕ → R.RTm Γ
  ⟪ d ⟫ = R.ref d (Sig.body S d)

  -- the Lib's λ-calculus: the same three shapes
  shV shL shA : L.Shape
  shV = L.vʰ
  shL = L.rec 0 1 L.∷ʰ L.[]ʰ
  shA = L.rec 0 0 L.∷ʰ L.rec 0 0 L.∷ʰ L.[]ʰ

  libΣ : L.Sig 1
  libΣ = (shV L.∷ˢʰ shL L.∷ˢʰ shA L.∷ˢʰ L.[]ˢʰ) L.∷ᵍ L.[]ᵍ

  -- the index (sort 0 , a variable depth)
  ix : R.RTm (ε R.∙)
  ix = R.pair R.fzero (R.var vz)

  -- the core's telescope of constructor k, and the Lib's
  coreTel libTel : ℕ → L.Shape → R.RTm (ε R.∙)
  coreTel k _  = R.app (R.app (R.app ⟪ #tel ⟫ (num 1)) (R.app (R.snd (R.app ⟪ #lamΣ ⟫ R.fzero)) (tag k))) ix
  libTel  _ sh = ⌜ L.tel sh ix ⌝ᵗ

-- (1) the Lib-form decoder IS the Lib's `SD`
sdℓ-faithful : nfOf {ε} (R.app (R.app ⟪ #SDℓ ⟫ (num 1)) ⟪ #lamΣ ⟫) ≡ nfOf (L.SD libΣ)
sdℓ-faithful = refl

-- (2) the decoder: the arity, and every constructor's telescope
sd-arity : nfOf {ε} (R.fst (R.app ⟪ #lamΣ ⟫ R.fzero)) ≡ num 3
sd-arity = refl

sd-faithful : (nfOf (coreTel 0 shV) ≡ nfOf (libTel 0 shV)) × ((nfOf (coreTel 1 shL) ≡ nfOf (libTel 1 shL))
            × (nfOf (coreTel 2 shA) ≡ nfOf (libTel 2 shA)))
sd-faithful = refl , (refl , refl)

sd-normal : (normal? (coreTel 0 shV) ≡ true) × ((normal? (coreTel 1 shL) ≡ true) × ((normal? (coreTel 2 shA) ≡ true)
          × (normal? {ε} (R.app (R.app ⟪ #SDℓ ⟫ (num 1)) ⟪ #lamΣ ⟫) ≡ true)))
sd-normal = refl , (refl , (refl , refl))
