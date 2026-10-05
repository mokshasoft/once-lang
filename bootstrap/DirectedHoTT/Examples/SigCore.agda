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
open import DirectedHoTT.Spec.Syntax using () renaming ( _∙ to _R∙ )
open import DirectedHoTT.Metatheory.Signature using ( WfSig )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Examples.Knot.Sig using ( KSig; KD )

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
pattern #lift  = 18     -- an environment, under a binder
pattern #lifts = 19     -- …under k binders
pattern #rnF   = 20     -- ★ renaming, one field (lockstep with telF)
pattern #rnFs  = 21     --   a field list (lockstep with telFs)
pattern #rnSh  = 22     --   a shape (lockstep with tel)
pattern #rnM   = 23     --   the method
pattern #ren   = 24     -- ★ RENAMING, generic in the signature
pattern #KΣ    = 25     -- ★ the Knot's signature, quoted

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

  wk² wk³ wk⁴ : {Γ : _} → STm Γ → STm _
  wk² t = wk (wk t)
  wk³ t = wk (wk² t)
  wk⁴ t = wk (wk³ t)

  -- ★ a variable by its position (contexts are concrete in the entries)
  V : {Γ : _} → ℕ → STm Γ
  V {ε}     _       = unit
  V {Γ R∙}  zero    = var vz
  V {Γ R∙}  (suc k) = wk (V {Γ} k)

  -- ★ telF's body as a GENERATOR — the field's tag t and payload q apart, so
  --   a generic program's convoy motive is literally the same term
  tfBody : {Γ : _} (n i t q rest : STm Γ) → STm Γ
  tfBody n i t q rest =
    app (fcase □ (Π (El (FlC (wk n) v₀)) (Dt (wk² n))) t
           (lam (Σ' (Fin n) Nat) (app (app (app (app (ref #dRec) (wk n)) (wk i)) v₀) (wk rest)))
           (fcase □ (Π (El (FlC (wk² n) (fsuc □ v₀))) (Dt (wk³ n))) v₀
              (lam □ᵀ (app (app (ref #dNat) (wk² n)) (wk² rest)))
              (fcase □ (Π (El (FlC (wk³ n) (fsuc □ (fsuc □ v₀)))) (Dt (wk⁴ n))) v₀
                 (lam (Fin (wk² n)) (app (app (app (ref #dCls) (wk³ n)) v₀) (wk³ rest)))
                 (fcase0 □ᵀ v₀))))
        q

  TELF : STm ((((ε ∙) ∙) ∙) ∙)
  TELF = tfBody v₃ v₂ (fst v₁) (snd v₁) v₀

  -- telFs's body, in context [n , i , len]: natrec on the length
  TELFS : STm (((ε ∙) ∙) ∙)
  TELFS = natrec (Π (Π (Fin v₀) (FldT v₄)) (Dt v₄)) (lam □ᵀ (dι □))
            (lam □ᵀ (app (app (app (app (ref #telF) v₅) v₄) (app v₀ (fzero □)))
                         (app v₁ (lam □ᵀ (app v₁ (fsuc □ v₀))))))
            v₀

  -- ★ tel's body as a generator (shape tag b, payload x)
  tBody : {Γ : _} (n i b x : STm Γ) → STm Γ
  tBody n i b x =
    app (fcase □ (Π (El (ShC (wk n) v₀)) (Dt (wk² n))) b
           (lam (Σ' Nat (Π (Fin v₀) (FldT (wk² n)))) (app (app (app (app (ref #telFs) (wk n)) (wk i)) (fst v₀)) (snd v₀)))
           (lam □ᵀ (app (app (ref #telV) (wk² n)) (wk² i))))
        x

  TEL : STm (((ε ∙) ∙) ∙)
  TEL = tBody v₂ v₀ (fst v₁) (snd v₁)

  ----------------------------------------------------------------------
  -- ★ the traversal's types (generators; n , sg at the current context)
  ----------------------------------------------------------------------
  SDA : {Γ : _} → STm Γ → STm Γ → STm Γ
  SDA n sg = app (app (ref #SD) n) sg
  MU : {Γ : _} → STm Γ → STm Γ → STm Γ → STy Γ
  MU n sg j = IMu (SIc n) (SDA n sg) j
  -- the motive M(i , t) = Π e. (Fin (snd i) → Fin e) → Syn (fst i) e
  TMy : {Γ : _} → STm Γ → STm Γ → STy ((Γ R∙) R∙)
  TMy n sg = Π Nat (Π (Π (Fin (snd v₂)) (Fin v₁)) (MU (wk⁴ n) (wk⁴ sg) (pair □ᵀ □ᵀ (fst v₃) v₁)))
  PAYf : {Γ : _} → STm Γ → STm Γ → STm Γ → STy Γ
  PAYf n sg C = El (dpay (SIc n) (SDA n sg) C)
  DIhf : {Γ : _} → STm Γ → STm Γ → STm Γ → STm Γ → STy Γ
  DIhf n sg C p = DIh (SIc n) (SDA n sg) (TMy n sg) C p
  TFe : {Γ : _} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  TFe n i f rest = app (app (app (app (ref #telF) n) i) f) rest
  TFs : {Γ : _} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  TFs n i len fs = app (app (app (app (ref #telFs) n) i) len) fs
  TELe : {Γ : _} → STm Γ → STm Γ → STm Γ → STm Γ
  TELe n sh i = app (app (app (ref #tel) n) sh) i
  ADD : {Γ : _} → STm Γ → STm Γ → STm Γ
  ADD a b = app (app (ref #add) a) b
  -- the index (fst i , e)
  IX : {Γ : _} → STm Γ → STm Γ → STm Γ
  IX i e = pair □ᵀ □ᵀ (fst i) e
  lams : {Γ : _} → ℕ → STm Γ → STm Γ
  lams = λ _ t → t


-- SI n = Σ (s : Fin n) Nat
ty-SI : STy ε
ty-SI = Π Nat U
tm-SI : STm ε
tm-SI = lam □ᵀ (⌜Σ⌝ (⌜Fin⌝ v₀) ⌜Nat⌝)

-- add k d = k + d (by recursion on k)
ty-add : STy ε
ty-add = Π Nat (Π Nat Nat)
tm-add : STm ε
tm-add = lam □ᵀ (lam □ᵀ (natrec □ᵀ v₀ (nsuc v₀) v₁))

-- FlC n t: rec ↦ Fin n × Nat ; nat ↦ Unit ; cls ↦ Fin n
ty-FlC : STy ε
ty-FlC = Π Nat (Π (Fin n₃) U)
tm-FlC : STm ε
tm-FlC = lam □ᵀ (lam □ᵀ
             (fcase □ □ᵀ v₀ (⌜Σ⌝ (⌜Fin⌝ v₁) ⌜Nat⌝)
               (fcase □ □ᵀ v₀ ⌜Unit⌝
                 (fcase □ □ᵀ v₀ (⌜Fin⌝ v₃) (fcase0 □ᵀ v₀)))))

ty-Fld : STy ε
ty-Fld = Π Nat U
tm-Fld : STm ε
tm-Fld = lam □ᵀ (⌜Σ⌝ (⌜Fin⌝ n₃) (FlC v₁ v₀))

-- ShC n b: fields ↦ Σ (len : Nat). Fin len → Fld n ; var ↦ Unit
ty-ShC : STy ε
ty-ShC = Π Nat (Π (Fin n₂) U)
tm-ShC : STm ε
tm-ShC = lam □ᵀ (lam □ᵀ
             (fcase □ □ᵀ v₀ (⌜Σ⌝ ⌜Nat⌝ (⌜Π⌝ (⌜Fin⌝ v₀) (app (ref #Fld) v₃)))
               (fcase □ □ᵀ v₀ ⌜Unit⌝ (fcase0 □ᵀ v₀))))

ty-Shape : STy ε
ty-Shape = Π Nat U
tm-Shape : STm ε
tm-Shape = lam □ᵀ (⌜Σ⌝ (⌜Fin⌝ n₂) (ShC v₁ v₀))

-- Sig n = Fin n → Σ (c : Nat). Fin c → Shape n
ty-Sig : STy ε
ty-Sig = Π Nat U
tm-Sig : STm ε
tm-Sig = lam □ᵀ (⌜Π⌝ (⌜Fin⌝ v₀) (⌜Σ⌝ ⌜Nat⌝ (⌜Π⌝ (⌜Fin⌝ v₀) (app (ref #Shape) v₃))))

-- the variable: a Fin of the depth
ty-telV : STy ε
ty-telV = Π Nat (Π (El (SIc v₀)) (Dt v₁))
tm-telV : STm ε
tm-telV = lam □ᵀ (lam □ᵀ (dσ □ (⌜Fin⌝ (snd v₀)) (lam □ᵀ (dι □))))

-- rec (s , k): a recursive position at (s , k + depth)
ty-dRec : STy ε
ty-dRec = Π Nat (Π (El (SIc v₀)) (Π (Σ' (Fin v₁) Nat) (Π (Dt v₂) (Dt v₃))))
tm-dRec : STm ε
tm-dRec = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ
              (dρ □ (pair □ᵀ □ᵀ (fst v₁) (app (app (ref #add) (snd v₁)) (snd v₂))) v₀))))

-- nat: a natural field
ty-dNat : STy ε
ty-dNat = Π Nat (Π (Dt v₀) (Dt v₁))
tm-dNat : STm ε
tm-dNat = lam □ᵀ (lam □ᵀ (dσ □ ⌜Nat⌝ (lam □ᵀ v₁)))

-- cls s: a closed subterm, at (s , 0)
ty-dCls : STy ε
ty-dCls = Π Nat (Π (Fin v₀) (Π (Dt v₁) (Dt v₂)))
tm-dCls : STm ε
tm-dCls = lam □ᵀ (lam □ᵀ (lam □ᵀ (dρ □ (pair □ᵀ □ᵀ v₁ nzero) v₀)))

ty-telF : STy ε
ty-telF = Π Nat (Π (El (SIc v₀)) (Π (FldT v₁) (Π (Dt v₂) (Dt v₃))))
tm-telF : STm ε
tm-telF = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ TELF)))

ty-telFs : STy ε
ty-telFs = Π Nat (Π (El (SIc v₀)) (Π Nat (Π (Π (Fin v₀) (FldT v₃)) (Dt v₃))))
tm-telFs : STm ε
tm-telFs = lam □ᵀ (lam □ᵀ (lam □ᵀ TELFS))

-- ★ tel n sh i : Desc (SI n)
ty-tel : STy ε
ty-tel = Π Nat (Π (El (app (ref #Shape) v₀)) (Π (El (SIc v₁)) (Dt v₂)))
tm-tel : STm ε
tm-tel = lam □ᵀ (lam □ᵀ (lam □ᵀ TEL))

-- tabD n c f = λ k. case k of 0 ↦ f 0 ; suc k' ↦ tabD (λ y. f (suc y)) k' —
--   a table of descriptions IS the Lib's `selF` cascade (`Lib/Sugar.sel`)
ty-tabD : STy ε
ty-tabD = Π Nat (Π Nat (Π (Π (Fin v₀) (Dt v₂)) (Π (Fin v₁) (Dt v₃))))
tm-tabD : STm ε
tm-tabD = lam □ᵀ (lam □ᵀ (natrec (Π (Π (Fin v₀) (Dt v₃)) (Π (Fin v₁) (Dt v₄)))
              (lam □ᵀ (lam □ᵀ (fcase0 □ᵀ v₀)))
              (lam □ᵀ (lam □ᵀ (fcase □ □ᵀ v₀ (app v₁ (fzero □))
                                 (app (app v₃ (lam □ᵀ (app v₃ (fsuc □ v₀)))) v₀))))
              v₀))

-- the decoder in the Lib's form: per sort its constructor table, mapped
--   FIRST, then tabulated — the Lib's `Dₛ` normal form, exactly
ty-SDℓ : STy ε
ty-SDℓ = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (El (SIc v₁)) (Dt v₂)))
tm-SDℓ : STm ε
tm-SDℓ = lam □ᵀ (lam □ᵀ (lam □ᵀ
            (app (app (app (app (ref #tabD) v₂) v₂)
                 (lam □ᵀ (dσ □ (⌜Fin⌝ (fst (app v₂ v₀)))
                            (app (app (app (ref #tabD) v₃) (fst (app v₂ v₀)))
                                 (lam □ᵀ (app (app (app (ref #tel) v₄) (app (snd (app v₃ v₁)) v₀)) v₂))))))
                 (fst v₀))))

-- ★ SD n sg i : the sort's table SELECTED by application, then mapped —
--   at a variable constructor k its fibre is `tel n (sg s k) i` (what a
--   generic program over the signature needs)
ty-SD : STy ε
ty-SD = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (El (SIc v₁)) (Dt v₂)))
tm-SD : STm ε
tm-SD = lam □ᵀ (lam □ᵀ (lam □ᵀ
            (dσ □ (⌜Fin⌝ (fst (app v₁ (fst v₀))))
                  (lam □ᵀ (app (app (app (ref #tel) v₃) (app (snd (app v₂ (fst v₁))) v₀)) v₁)))))

-- ★ TEST: the scoped λ-calculus, one sort:  var | lam (rec 0 1) | app (rec 0 0) (rec 0 0)
ty-lamΣ : STy ε
ty-lamΣ = El (app (ref #Sig) n₁)
tm-lamΣ : STm ε
tm-lamΣ = lam □ᵀ (pair □ᵀ □ᵀ n₃ (lam (Fin n₃)
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

-- lift d e ρ = λ x. case x of 0 ↦ 0 ; suc y ↦ suc (ρ y)
ty-lift : STy ε
ty-lift = Π Nat (Π Nat (Π (Π (Fin v₁) (Fin v₁)) (Π (Fin (nsuc v₂)) (Fin (nsuc v₂)))))
tm-lift : STm ε
tm-lift = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (fcase □ □ᵀ v₀ (fzero □) (fsuc □ (app v₂ v₀))))))

-- lifts k d e ρ : Fin (k + d) → Fin (k + e)
ty-lifts : STy ε
ty-lifts = Π Nat (Π Nat (Π Nat (Π (Π (Fin v₁) (Fin v₁)) (Π (Fin (ADD v₃ v₂)) (Fin (ADD v₄ v₂))))))
tm-lifts : STm ε
tm-lifts = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ
               (natrec (Π (Fin (ADD v₀ v₃)) (Fin (ADD v₁ v₃))) v₀
                       (app (app (app (ref #lift) (ADD v₁ v₄)) (ADD v₁ v₃)) v₀) v₃))))

-- ★ one field, renamed: [n sg i e ρ f ri re r p h] ↦ the payload at (fst i , e)
ty-rnF : STy ε
ty-rnF = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (El (SIc v₁)) (Π Nat (Π (Π (Fin (snd v₁)) (Fin v₁))
           (Π (FldT v₄) (Π (Dt v₅) (Π (Dt v₆)
           (Π (Π (PAYf v₇ v₆ v₁) (Π (DIhf v₈ v₇ v₂ v₀) (PAYf v₉ v₈ v₂)))
           (Π (PAYf v₈ v₇ (TFe v₈ v₆ v₃ v₂))
           (Π (DIhf (V 9) v₈ (TFe (V 9) v₇ v₄ v₃) v₀)
              (PAYf (V 10) (V 9) (TFe (V 10) (IX v₈ v₇) v₅ v₃))))))))))))
tm-rnF : STm ε
tm-rnF = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ
             (app (app (app (fcase □ MOT (fst (V 5)) B0 B12) (snd (V 5))) (V 1)) (V 0))))))))))))
  where
    -- motive over the tag t: [… h t]
    MOT : STy _
    MOT = Π (El (FlC (V 11) (V 0)))
            (Π (PAYf (V 12) (V 11) (tfBody (V 12) (V 10) (V 1) (V 0) (V 6)))
               (Π (DIhf (V 13) (V 12) (tfBody (V 13) (V 11) (V 2) (V 1) (V 7)) (V 0))
                  (PAYf (V 14) (V 13) (tfBody (V 14) (IX (V 12) (V 11)) (V 3) (V 2) (V 7)))))
    -- rec (s , k): the hypothesis at (k + e) through the k-fold lifted ρ
    B0 : STm _
    B0 = lam □ᵀ (lam □ᵀ (lam □ᵀ
           (pair □ᵀ □ᵀ (app (app (fst (V 0)) (ADD (snd (V 2)) (V 10)))
                            (app (app (app (app (ref #lifts) (snd (V 2))) (snd (V 11))) (V 10)) (V 9)))
                       (app (app (V 5) (snd (V 1))) (snd (V 0))))))
    B12 : STm _
    B12 = fcase □ MOT' (V 0)
            (lam □ᵀ (lam □ᵀ (lam □ᵀ (pair □ᵀ □ᵀ (fst (V 1)) (app (app (V 6) (snd (V 1))) (V 0))))))
            (fcase □ MOT'' (V 0)
               (lam □ᵀ (lam □ᵀ (lam □ᵀ (pair □ᵀ □ᵀ (fst (V 1)) (app (app (V 7) (snd (V 1))) (snd (V 0)))))))
               (fcase0 □ᵀ (V 0)))
      where
        MOT' MOT'' : STy _
        MOT' = Π (El (FlC (V 12) (fsuc □ (V 0))))
                 (Π (PAYf (V 13) (V 12) (tfBody (V 13) (V 11) (fsuc □ (V 1)) (V 0) (V 7)))
                    (Π (DIhf (V 14) (V 13) (tfBody (V 14) (V 12) (fsuc □ (V 2)) (V 1) (V 8)) (V 0))
                       (PAYf (V 15) (V 14) (tfBody (V 15) (IX (V 13) (V 12)) (fsuc □ (V 3)) (V 2) (V 8)))))
        MOT'' = Π (El (FlC (V 13) (fsuc □ (fsuc □ (V 0)))))
                  (Π (PAYf (V 14) (V 13) (tfBody (V 14) (V 12) (fsuc □ (fsuc □ (V 1))) (V 0) (V 8)))
                     (Π (DIhf (V 15) (V 14) (tfBody (V 15) (V 13) (fsuc □ (fsuc □ (V 2))) (V 1) (V 9)) (V 0))
                        (PAYf (V 16) (V 15) (tfBody (V 16) (IX (V 14) (V 13)) (fsuc □ (fsuc □ (V 3))) (V 2) (V 9)))))

-- ★ a field list, renamed: natrec on its length, in lockstep with telFs
ty-rnFs : STy ε
ty-rnFs = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (El (SIc v₁)) (Π Nat (Π (Π (Fin (snd v₁)) (Fin v₁))
            (Π Nat (Π (Π (Fin v₀) (FldT v₆))
            (Π (PAYf v₆ v₅ (TFs v₆ v₄ v₁ v₀))
            (Π (DIhf v₇ v₆ (TFs v₇ v₅ v₂ v₁) v₀)
               (PAYf v₈ v₇ (TFs v₈ (IX v₆ v₅) v₃ v₂))))))))))
tm-rnFs : STm ε
tm-rnFs = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (natrec MOTN ZN SN (V 0)))))))
  where
    MOTN : STy _
    MOTN = Π (Π (Fin (V 0)) (FldT (V 7)))
             (Π (PAYf (V 7) (V 6) (TFs (V 7) (V 5) (V 1) (V 0)))
                (Π (DIhf (V 8) (V 7) (TFs (V 8) (V 6) (V 2) (V 1)) (V 0))
                   (PAYf (V 9) (V 8) (TFs (V 9) (IX (V 7) (V 6)) (V 3) (V 2)))))
    ZN : STm _
    ZN = lam □ᵀ (lam □ᵀ (lam □ᵀ unit))
    -- [… m ih] then fs p h: the head field through rnF, the tail through ih
    SN : STm _
    SN = lam □ᵀ (lam □ᵀ (lam □ᵀ
           (app (app (app (app (app (app (app (app (app (app (app (ref #rnF) (V 10)) (V 9)) (V 8)) (V 7)) (V 6))
                      (app (V 2) (fzero □)))
                      (TFs (V 10) (V 8) (V 4) TAIL))
                      (TFs (V 10) (IX (V 8) (V 7)) (V 4) TAIL))
                      (lam □ᵀ (lam □ᵀ (app (app (app (V 5) (lam □ᵀ (app (V 5) (fsuc □ (V 0))))) (V 1)) (V 0)))))
                 (V 1))
            (V 0))))
      where
        TAIL : STm _
        TAIL = lam □ᵀ (app (V 3) (fsuc □ (V 0)))

-- ★ a shape, renamed: a case on its tag, in lockstep with tel
ty-rnSh : STy ε
ty-rnSh = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (El (SIc v₁)) (Π Nat (Π (Π (Fin (snd v₁)) (Fin v₁))
            (Π (El (app (ref #Shape) v₄))
            (Π (PAYf v₅ v₄ (TELe v₅ v₀ v₃))
            (Π (DIhf v₆ v₅ (TELe v₆ v₁ v₄) v₀)
               (PAYf v₇ v₆ (TELe v₇ v₂ (IX v₅ v₄))))))))))
tm-rnSh : STm ε
tm-rnSh = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ
              (app (app (app (fcase □ MOTS (fst (V 2)) BF BV) (snd (V 2))) (V 1)) (V 0)))))))))
  where
    MOTS : STy _
    MOTS = Π (El (ShC (V 8) (V 0)))
             (Π (PAYf (V 9) (V 8) (tBody (V 9) (V 7) (V 1) (V 0)))
                (Π (DIhf (V 10) (V 9) (tBody (V 10) (V 8) (V 2) (V 1)) (V 0))
                   (PAYf (V 11) (V 10) (tBody (V 11) (IX (V 9) (V 8)) (V 3) (V 2)))))
    -- fields: the list, renamed
    BF : STm _
    BF = lam □ᵀ (lam □ᵀ (lam □ᵀ
           (app (app (app (app (app (app (app (app (app (ref #rnFs) (V 10)) (V 9)) (V 8)) (V 7)) (V 6))
                (fst (V 2))) (snd (V 2))) (V 1)) (V 0))))
    -- var: the variable, renamed
    BV : STm _
    BV = lam □ᵀ (lam □ᵀ (lam □ᵀ (pair □ᵀ □ᵀ (app (V 7) (fst (V 1))) unit)))

-- ★ the method: rebuild the node at (fst i , e), constructor and shape kept
ty-rnM : STy ε
ty-rnM = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (El (SIc v₁))
           (Π (PAYf v₂ v₁ (app (SDA v₂ v₁) v₀)) (Π (DIhf v₃ v₂ (app (SDA v₃ v₂) v₁) v₀)
              (Π Nat (Π (Π (Fin (snd (V 3))) (Fin (V 1))) (MU (V 6) (V 5) (IX (V 4) (V 1)))))))))
tm-rnM : STm ε
tm-rnM = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ
             (con □ □ □ (pair □ᵀ □ᵀ (fst (V 3))
                (app (app (app (app (app (app (app (app (ref #rnSh) (V 6)) (V 5)) (V 4)) (V 1)) (V 0))
                      (app (snd (app (V 5) (fst (V 4)))) (fst (V 3)))) (snd (V 3))) (V 2))))))))))

-- ★ ren n sg s d t e ρ : the term t of sort s, renamed from depth d to e
ty-ren : STy ε
ty-ren = Π Nat (Π (El (app (ref #Sig) v₀)) (Π (Fin v₁) (Π Nat (Π (MU v₃ v₂ (pair □ᵀ □ᵀ v₁ v₀))
           (Π Nat (Π (Π (Fin v₂) (Fin v₁)) (MU (V 6) (V 5) (pair □ᵀ □ᵀ (V 4) (V 1)))))))))
tm-ren : STm ε
tm-ren = lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ (lam □ᵀ
             (app (app (ielim □ (SDA (V 6) (V 5)) (TMy (V 6) (V 5)) (pair □ᵀ □ᵀ (V 4) (V 3))
                                (app (app (ref #rnM) (V 6)) (V 5)) (V 2))
                       (V 1)) (V 0))))))))



------------------------------------------------------------------------
-- ★ QUOTING a Lib signature into core data (an Agda-level generator):
--   lists become case cascades over a `Fin`, lengths numerals.
------------------------------------------------------------------------

private
  open import Agda.Builtin.List using ( List; []; _∷_ )
  import DirectedHoTT.Lib.Syn as LS

  numS tagS : {Γ : _} → ℕ → STm Γ
  numS zero    = nzero
  numS (suc k) = nsuc (numS k)
  tagS zero    = fzero □
  tagS (suc k) = fsuc □ (tagS k)

  Closed : Set
  Closed = {Γ : _} → STm Γ

  len : {A : Set} → List A → ℕ
  len []       = 0
  len (_ ∷ xs) = suc (len xs)

  -- the k-th element at the tag v₀: a cascade of cases
  casc : {Γ : _} → List Closed → STm (Γ R∙)
  casc []       = fcase0 □ᵀ v₀
  casc (x ∷ xs) = fcase □ □ᵀ v₀ x (casc xs)

  qFld : ℕ → LS.Fld → Closed
  qFld n (LS.rec s k) = pair (Fin n₃) (El (FlC (numS n) v₀)) (fzero □) (pair (Fin (numS n)) Nat (tagS s) (numS k))
  qFld n LS.nat       = pair (Fin n₃) (El (FlC (numS n) v₀)) (fsuc □ (fzero □)) unit
  qFld n (LS.cls s)   = pair (Fin n₃) (El (FlC (numS n) v₀)) (fsuc □ (fsuc □ (fzero □))) (tagS s)

  data ShV : Set where
    fields : List LS.Fld → ShV
    var'   : ShV

  view : LS.Shape → ShV
  view LS.[]ʰ       = fields []
  view (f LS.∷ʰ sh) with view sh
  ... | fields fs = fields (f ∷ fs)
  ... | var'      = var'                       -- not well-formed (`ShOK`)
  view LS.vʰ        = var'

  mapL : {A B : Set} → (A → B) → List A → List B
  mapL f []       = []
  mapL f (x ∷ xs) = f x ∷ mapL f xs

  qShape : ℕ → LS.Shape → Closed
  qShape n sh with view sh
  ... | fields fs = pair (Fin n₂) (El (ShC (numS n) v₀)) (fzero □)
                      (pair Nat (Π (Fin v₀) (FldT (numS n))) (numS (len fs))
                            (lam (Fin (numS (len fs))) (casc (mapL (qFld n) fs))))
  ... | var'      = pair (Fin n₂) (El (ShC (numS n) v₀)) (fsuc □ (fzero □)) unit

  shapes : {c : ℕ} → LS.Shapes c → List LS.Shape
  shapes LS.[]ˢʰ        = []
  shapes (sh LS.∷ˢʰ shs) = sh ∷ shapes shs

  sorts : {m : ℕ} → LS.Sig m → List (List LS.Shape)
  sorts LS.[]ᵍ         = []
  sorts (shs LS.∷ᵍ sg) = shapes shs ∷ sorts sg

  qSort : ℕ → List LS.Shape → Closed
  qSort n shs = pair Nat (Π (Fin v₀) (El (app (ref #Shape) (numS n)))) (numS (len shs))
                     (lam (Fin (numS (len shs))) (casc (mapL (qShape n) shs)))

-- ★ ⌜ sg ⌝Σ : El (Sig n)
⌜_⌝Σ : {n : ℕ} → LS.Sig n → STm ε
⌜_⌝Σ {n} sg = lam (Fin (numS n)) (casc (mapL (qSort n) (sorts sg)))

ty-KΣ : STy ε
ty-KΣ = El (app (ref #Sig) n₂)
tm-KΣ : STm ε
tm-KΣ = ⌜ KSig ⌝Σ

-- the table, in entry order (`#SI` = 0 … `#ren` = 24)
private
  open import Agda.Builtin.List using ( List; []; _∷_ )
  at : {A : Set} → A → List A → ℕ → A
  at d []       _       = d
  at d (x ∷ xs) zero    = x
  at d (x ∷ xs) (suc k) = at d xs k

tys : ℕ → STy ε
tys = at Unit (ty-SI ∷ ty-add ∷ ty-FlC ∷ ty-Fld ∷ ty-ShC ∷ ty-Shape ∷ ty-Sig ∷ ty-telV ∷ ty-dRec ∷ ty-dNat ∷ ty-dCls ∷ ty-telF ∷ ty-telFs ∷ ty-tel ∷ ty-tabD ∷ ty-SDℓ ∷ ty-SD ∷ ty-lamΣ ∷ ty-lift ∷ ty-lifts ∷ ty-rnF ∷ ty-rnFs ∷ ty-rnSh ∷ ty-rnM ∷ ty-ren ∷ ty-KΣ ∷ [])

tms : ℕ → STm ε
tms = at unit (tm-SI ∷ tm-add ∷ tm-FlC ∷ tm-Fld ∷ tm-ShC ∷ tm-Shape ∷ tm-Sig ∷ tm-telV ∷ tm-dRec ∷ tm-dNat ∷ tm-dCls ∷ tm-telF ∷ tm-telFs ∷ tm-tel ∷ tm-tabD ∷ tm-SDℓ ∷ tm-SD ∷ tm-lamΣ ∷ tm-lift ∷ tm-lifts ∷ tm-rnF ∷ tm-rnFs ∷ tm-rnSh ∷ tm-rnM ∷ tm-ren ∷ tm-KΣ ∷ [])

open import DirectedHoTT.Algorithm.SigBuild 26 tys tms 1000 public

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

------------------------------------------------------------------------
-- ★ RENAMING COMPUTES: weakening `ρ = λ x. fsuc x` (depth 1 → 2) on the
--   λ-calculus — a free variable moves, the bound one stays (the
--   environment is LIFTED under `lam`).
------------------------------------------------------------------------

private
  varK : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ
  varK x = R.con (R.pair R.fzero (R.pair x R.unit))
  lamK : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ
  lamK b = R.con (R.pair (R.fsuc R.fzero) (R.pair b R.unit))
  appK : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ → R.RTm Γ
  appK f a = R.con (R.pair (R.fsuc (R.fsuc R.fzero)) (R.pair f (R.pair a R.unit)))

  wk1 : {Γ : R.Cx} → R.RTm Γ → R.RTm Γ
  wk1 t = R.app (R.app (R.app (R.app (R.app (R.app (R.app ⟪ #ren ⟫ (num 1)) ⟪ #lamΣ ⟫) R.fzero) (num 1)) t)
                       (num 2)) (R.lam (R.fsuc (R.var vz)))

ren-var : nfOf {ε} (wk1 (varK R.fzero)) ≡ varK (R.fsuc R.fzero)
ren-var = refl

ren-lam : nfOf {ε} (wk1 (lamK (appK (varK R.fzero) (varK (R.fsuc R.fzero)))))
        ≡ lamK (appK (varK R.fzero) (varK (R.fsuc (R.fsuc R.fzero))))
ren-lam = refl

------------------------------------------------------------------------
-- ★★ THE KNOT'S DESCRIPTION, FROM THE CORE: the quoted Knot signature
--   decodes, constructor by constructor, to the Lib's telescopes — every
--   field kind (variable, binder, cross-sort, `nat`, `cls`), both sorts,
--   and the arities.  (The WHOLE `KD` by normal form does not fit the
--   type checker: OOM at the cgroup's cap after 4.7 min, 2026-10-05.)
------------------------------------------------------------------------

private
  open import DirectedHoTT.Examples.Knot.Sig using ( sh-kPi; sh-kFin; sh-kvar; sh-klam; sh-kref; sh-knatrec )

  ixK : ℕ → R.RTm (ε R.∙)
  ixK s = R.pair (tag s) (R.var vz)

  kTel : ℕ → ℕ → R.RTm (ε R.∙)
  kTel s k = R.app (R.app (R.app ⟪ #tel ⟫ (num 2)) (R.app (R.snd (R.app ⟪ #KΣ ⟫ (tag s))) (tag k))) (ixK s)

  lTel : ℕ → L.Shape → R.RTm (ε R.∙)
  lTel s sh = ⌜ L.tel sh (ixK s) ⌝ᵗ

kd-arity : (nfOf {ε} (R.fst (R.app ⟪ #KΣ ⟫ (tag 0))) ≡ num 13) × (nfOf {ε} (R.fst (R.app ⟪ #KΣ ⟫ (tag 1))) ≡ num 39)
kd-arity = refl , refl

kd-faithful : (nfOf (kTel 0 2) ≡ nfOf (lTel 0 sh-kPi)) × ((nfOf (kTel 0 12) ≡ nfOf (lTel 0 sh-kFin))
            × ((nfOf (kTel 1 0) ≡ nfOf (lTel 1 sh-kvar)) × ((nfOf (kTel 1 1) ≡ nfOf (lTel 1 sh-klam))
            × ((nfOf (kTel 1 38) ≡ nfOf (lTel 1 sh-kref)) × (nfOf (kTel 1 21) ≡ nfOf (lTel 1 sh-knatrec))))))
kd-faithful = refl , (refl , (refl , (refl , (refl , refl))))

kd-normal : (normal? (kTel 0 2) ≡ true) × ((normal? (kTel 1 38) ≡ true) × (normal? (kTel 1 21) ≡ true))
kd-normal = refl , (refl , refl)

------------------------------------------------------------------------
-- ★★ RENAMING AGREES WITH THE KERNEL: the core `ren` at the quoted Knot
--   signature, weakening by `fsuc`, IS the quotation of `renTm vs` — a
--   binder, an application, a variable crossing the binder, and a
--   definition reference (its `nat` index and its CLOSED body copied).
------------------------------------------------------------------------

private
  open import DirectedHoTT.Examples.Knot.Terms using ( quoteTm )

  -- the kernel term `λ. (x₀ x₁) (ref 0 0)` at depth 1
  tK : R.RTm (ε R.∙)
  tK = R.lam (R.app (R.app (R.var vz) (R.var (vs vz))) (R.ref 0 R.nzero))

  wkK : R.RTm ε → R.RTm ε
  wkK t = R.app (R.app (R.app (R.app (R.app (R.app (R.app ⟪ #ren ⟫ (num 2)) ⟪ #KΣ ⟫) (tag 1)) (num 1)) t)
                       (num 2)) (R.lam (R.fsuc (R.var vz)))

ren-knot : nfOf (wkK (quoteTm tK)) ≡ quoteTm (R.renTm vs tK)
ren-knot = refl
