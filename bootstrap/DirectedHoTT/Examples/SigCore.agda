-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ THE LIB'S `Sig`, WRITTEN IN THE CORE.
--                        (PLAN-BIDI S7b step 3)
--
-- ⚠ Needs the COMPACTING COLLECTOR (`+RTS -c`): the checker run `wf` peaks
--   at ~4.6 GB and is killed at the cap without it (2026-10-05).
--
-- `Lib/Syn`'s signatures, their decoder `SD` and the generic traversal's
-- FIELD steps (`Lib/SynTrav`) as core definitions checked by
-- `Algorithm/SigBuild` — no derivation written.  The traversal's method,
-- the traversal and its kits are the segment `Examples/SigMeth`.  A signature is a FINITE
-- MAP, so it is represented as one (Fin-indexed functions), with `vs` the
-- sort of the variables:
--
--     Fld   n        = Σ (t : Fin 3). rec ↦ Fin n × Nat ; nat ↦ Unit ; cls ↦ Fin n
--     Shape n vs s   = Σ (b : Fin 2). fields ↦ Σ len. Fin len → Fld n
--                                     var    ↦ Id (Fin n) vs s
--     Sig   n vs     = Π (s : Fin n). Σ (c : Nat). Fin c → Shape n vs s
--
-- ★ A variable shape carries `vs = s`: the Lib's `VarsAt` hypothesis, as
--   DATA of the signature (once, not per term).  The traversal's variable
--   case (`SigMeth`) transports the kit's node along it; at a concrete
--   signature it is `idrefl`, and the transport computes away.
--
-- ★ The decoder has the Lib's `SD` normal form EXACTLY (map, then
--   tabulate as a `fcase` cascade): so the core's `#SD … ⌜KSig⌝` is
--   CONVERTIBLE with the Knot's `KD`, and the Knot can move onto the core
--   one family at a time.  A generic program follows the decoder in
--   LOCKSTEP (`SigMeth`'s cascades); `tfBody`/`tBody` generate the
--   decoder's bodies that its convoy motives reuse.
--
-- Variables in the entries are written by LEVEL (`L ℓ`, position from the
-- root), so they do not shift under binders.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.SigCore where
open import Agda.Builtin.Nat using ( zero; suc; _-_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; vz; vs )
open import DirectedHoTT.Metatheory.Signature using ( WfSig )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Examples.Knot.Sig using ( KSig )

------------------------------------------------------------------------
-- Writing terms: levels, numerals.
------------------------------------------------------------------------

private
  pattern v₀ = var vz
  pattern v₁ = var (vs vz)
  pattern v₂ = var (vs (vs vz))
  pattern v₃ = var (vs (vs (vs vz)))
  pattern v₄ = var (vs (vs (vs (vs vz))))

  wk : {Γ : Cx} → STm Γ → STm (Γ ∙)
  wk = renTmˢ vs

  -- a variable by its de Bruijn index (contexts are concrete in the entries)
  V : {Γ : Cx} → ℕ → STm Γ
  V {ε}    _       = unit
  V {Γ ∙}  zero    = var vz
  V {Γ ∙}  (suc k) = wk (V {Γ} k)

  lenC : Cx → ℕ
  lenC ε       = 0
  lenC (Γ ∙)   = suc (lenC Γ)

  -- ★ a variable by its LEVEL
  L : {Γ : Cx} → ℕ → STm Γ
  L {Γ} ℓ = V {Γ} (lenC Γ - suc ℓ)

  -- context-polymorphic terms and types (generators' arguments)
  T : Set
  T = {Γ : Cx} → STm Γ
  TT : Set
  TT = {Γ : Cx} → STy Γ

  n₁ n₂ n₃ : T
  n₁ = nsuc nzero
  n₂ = nsuc n₁
  n₃ = nsuc n₂

  app² : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ
  app² f a b = app (app f a) b
  app³ : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  app³ f a b c = app (app² f a b) c
  app⁴ : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  app⁴ f a b c d = app (app³ f a b c) d
  -- application to a list of arguments
  _·_ : {Γ : Cx} → STm Γ → List (STm Γ) → STm Γ
  f · []       = f
  f · (x ∷ xs) = app f x · xs
  infixl 9 _·_

  -- k λs with holes for their domains
  λ⁺ : {Γ : Cx} → ℕ → T → STm Γ
  λ⁺ zero    b = b
  λ⁺ (suc k) b = lam □ᵀ (λ⁺ k b)

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
pattern #telV  = 7      -- the variable's telescope
pattern #dRec  = 8      -- one field's telescope, by kind
pattern #dNat  = 9
pattern #dCls  = 10
pattern #telF  = 11     -- one field, by its tag
pattern #telFs = 12     -- a field list (natrec on its length)
pattern #tel   = 13     -- ★ a shape's telescope at an index
pattern #tabD  = 14     -- a table of descriptions as a case cascade
pattern #SD    = 15     -- ★ the decoder: per sort its table, mapped, then tabulated
pattern #lift  = 16     -- an environment, under a binder
pattern #lifts = 17     -- …under k binders
pattern #rnF   = 18     -- ★ the traversal, one field (lockstep with telF)
pattern #rnFs  = 19     --   a field list (lockstep with telFs)
pattern #lamΣ  = 20     -- the scoped λ-calculus
pattern #KΣ    = 21     -- ★ the Knot's signature, quoted
-- the traversal's method, the traversal and its kits: `Examples/SigMeth`

------------------------------------------------------------------------
-- Generators.  Their T arguments are levels or closed terms.
------------------------------------------------------------------------

private
  SIc : {Γ : Cx} → STm Γ → STm Γ
  SIc n = app (ref #SI) n
  Dt : {Γ : Cx} → STm Γ → STy Γ
  Dt n = Desc (SIc n)
  FlC : {Γ : Cx} → STm Γ → STm Γ → STm Γ
  FlC n t = app² (ref #FlC) n t
  FldT : {Γ : Cx} → STm Γ → STy Γ
  FldT n = El (app (ref #Fld) n)
  ShC : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  ShC n v s b = app⁴ (ref #ShC) n v s b
  ShapeT : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STy Γ
  ShapeT n v s = El (app³ (ref #Shape) n v s)
  SigT : {Γ : Cx} → STm Γ → STm Γ → STy Γ
  SigT n v = El (app² (ref #Sig) n v)
  ADD : {Γ : Cx} → STm Γ → STm Γ → STm Γ
  ADD a b = app² (ref #add) a b
  IX : {Γ : Cx} → STm Γ → STm Γ → STm Γ
  IX i e = pair □ᵀ □ᵀ (fst i) e

  -- ★ telF's body: a case on the field's tag t, payload q
  tfBody : (n i : T) {Γ : Cx} (t q : STm Γ) (rest : T) → STm Γ
  tfBody n i t q rest =
    app (fcase □ (Π (El (FlC n v₀)) (Dt n)) t
           (lam (Σ' (Fin n) Nat) (app⁴ (ref #dRec) n i v₀ rest))
           (fcase □ (Π (El (FlC n (fsuc □ v₀))) (Dt n)) v₀
              (lam □ᵀ (app² (ref #dNat) n rest))
              (fcase □ (Π (El (FlC n (fsuc □ (fsuc □ v₀)))) (Dt n)) v₀
                 (lam (Fin n) (app³ (ref #dCls) n v₀ rest))
                 (fcase0 □ᵀ v₀))))
        q

  -- ★ tel's body: a case on the shape's tag b, payload x
  tBody : (n v s i : T) {Γ : Cx} (b x : STm Γ) → STm Γ
  tBody n v s i b x =
    app (fcase □ (Π (El (ShC n v s v₀)) (Dt n)) b
           (lam (Σ' Nat (Π (Fin v₀) (FldT n))) (app⁴ (ref #telFs) n i (fst v₀) (snd v₀)))
           (lam □ᵀ (app² (ref #telV) n i)))
        x

  -- the traversal's types; VF is the kit's code of values at a depth
  SDg : (n v sg : T) → T
  SDg n v sg = app³ (ref #SD) n v sg
  MUg : (n v sg : T) {Γ : Cx} → STm Γ → STy Γ
  MUg n v sg j = IMu (SIc n) (SDg n v sg) j
  EnvT : (VF : T) {Γ : Cx} → STm Γ → T → STy Γ
  EnvT VF d e = Π (Fin d) (El (app VF e))
  -- M(i , t) = Π e. Env (snd i) e → Syn (fst i) e
  TMg : (n v sg VF : T) {Γ : Cx} → STy ((Γ ∙) ∙)
  TMg n v sg VF = Π Nat (Π (Π (Fin (snd v₂)) (El (app VF v₁))) (MUg n v sg (pair □ᵀ □ᵀ (fst v₃) v₁)))
  PAYg : (n v sg : T) {Γ : Cx} → STm Γ → STy Γ
  PAYg n v sg C = El (dpay (SIc n) (SDg n v sg) C)
  DIhg : (n v sg VF : T) {Γ : Cx} → STm Γ → STm Γ → STy Γ
  DIhg n v sg VF C p = DIh (SIc n) (SDg n v sg) (TMg n v sg VF) C p
  WKt V0t : T → TT
  WKt VF = Π Nat (Π (El (app VF v₀)) (El (app VF (nsuc v₁))))
  V0t VF = Π Nat (El (app VF (nsuc v₀)))

  TFe : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  TFe n i f rest = app⁴ (ref #telF) n i f rest

  -- ★ the decoder's per-sort body (the table of sort s at index i), as a
  --   generator: `#SD` and the traversal use the SAME term
  persortG : (n v sg i : T) → T
  persortG n v sg i =
    lam □ᵀ (dσ □ (⌜Fin⌝ (fst (app sg v₀)))
                 (app³ (ref #tabD) n (fst (app sg v₀))
                       (lam □ᵀ (app⁴ (app (ref #tel) n) v v₁ (app (snd (app sg v₁)) v₀) i))))
  TFs : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  TFs n i len fs = app⁴ (ref #telFs) n i len fs

  -- a telescope of Π's
  Πˢ : List TT → TT → TT
  Πˢ []       B = B
  Πˢ (A ∷ As) B = Π A (Πˢ As B)

  _++_ : {A : Set} → List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
  infixr 5 _++_

  -- ★ the traversal's globals, by level
  N VS SG VF WK V0 : T
  N = L 0 ; VS = L 1 ; SG = L 2 ; VF = L 3 ; WK = L 4 ; V0 = L 5

  -- n , vs , sg , VF , WK , V0
  kit : List TT
  kit = Nat ∷ Fin N ∷ SigT N VS ∷ Π Nat U ∷ WKt VF ∷ V0t VF ∷ []

------------------------------------------------------------------------
-- ★ QUOTING a Lib signature into core data (an Agda-level generator):
--   lists become case cascades over a `Fin`, lengths numerals, and every
--   variable shape the proof `idrefl` (it sits at the sort `vs`).
------------------------------------------------------------------------

private
  import DirectedHoTT.Lib.Syn as LS

  numS tagS : ℕ → T
  numS zero    = nzero
  numS (suc k) = nsuc (numS k)
  tagS zero    = fzero □
  tagS (suc k) = fsuc □ (tagS k)

  len : {A : Set} → List A → ℕ
  len []       = 0
  len (_ ∷ xs) = suc (len xs)

  mapL : {A B : Set} → (A → B) → List A → List B
  mapL f []       = []
  mapL f (x ∷ xs) = f x ∷ mapL f xs

  -- the k-th element at the tag v₀: a cascade of cases
  casc : {Γ : Cx} → List T → STm (Γ ∙)
  casc []       = fcase0 □ᵀ v₀
  casc (x ∷ xs) = fcase □ □ᵀ v₀ x (casc xs)

  qFld : ℕ → LS.Fld → T
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

  -- a shape of sort s (n sorts, variables of sort v)
  qShape : ℕ → ℕ → ℕ → LS.Shape → T
  qShape n v s sh with view sh
  ... | fields fs = pair (Fin n₂) (El (ShC (numS n) (tagS v) (tagS s) v₀)) (fzero □)
                      (pair Nat (Π (Fin v₀) (FldT (numS n))) (numS (len fs))
                            (lam (Fin (numS (len fs))) (casc (mapL (qFld n) fs))))
  ... | var'      = pair (Fin n₂) (El (ShC (numS n) (tagS v) (tagS s) v₀)) (fsuc □ (fzero □))
                      (idrefl (⌜Fin⌝ (numS n)) (tagS v))

  shapes : {c : ℕ} → LS.Shapes c → List LS.Shape
  shapes LS.[]ˢʰ         = []
  shapes (sh LS.∷ˢʰ shs) = sh ∷ shapes shs

  sorts : {m : ℕ} → LS.Sig m → List (List LS.Shape)
  sorts LS.[]ᵍ         = []
  sorts (shs LS.∷ᵍ sg) = shapes shs ∷ sorts sg

  qSorts : ℕ → ℕ → ℕ → List (List LS.Shape) → List T
  qSorts n v s []           = []
  qSorts n v s (shs ∷ rest) =
    pair Nat (Π (Fin v₀) (ShapeT (numS n) (tagS v) (tagS s))) (numS (len shs))
         (lam (Fin (numS (len shs))) (casc (mapL (qShape n v s) shs)))
    ∷ qSorts n v (suc s) rest

private
  fsucs : {Γ : Cx} → ℕ → STm Γ → STm Γ
  fsucs zero    t = t
  fsucs (suc j) t = fsuc □ (fsucs j t)

  -- ★ the sort cascade's motive DEPENDS on the sort (a table's shapes are
  --   at it): level j of the cascade scrutinises a z with s = fsucʲ z
  cascS : ℕ → ℕ → {Γ : Cx} → ℕ → List T → STm (Γ ∙)
  cascS n v j []       = fcase0 □ᵀ v₀
  cascS n v j (x ∷ xs) =
    fcase □ (Σ' Nat (Π (Fin v₀) (ShapeT (numS n) (tagS v) (fsucs j v₂)))) v₀ x (cascS n v (suc j) xs)

-- ★ ⌜ sg ⌝Σ v : El (Sig n v) — variables of sort v
⌜_⌝Σ : {n : ℕ} → LS.Sig n → ℕ → STm ε
⌜_⌝Σ {n} sg v = lam (Fin (numS n)) (cascS n v 0 (qSorts n v 0 (sorts sg)))

-- the Lib's λ-calculus: var | lam (rec 0 1) | app (rec 0 0) (rec 0 0)
libΣ : LS.Sig 1
libΣ = (LS.vʰ LS.∷ˢʰ (LS.rec 0 1 LS.∷ʰ LS.[]ʰ) LS.∷ˢʰ (LS.rec 0 0 LS.∷ʰ LS.rec 0 0 LS.∷ʰ LS.[]ʰ) LS.∷ˢʰ LS.[]ˢʰ) LS.∷ᵍ LS.[]ᵍ

------------------------------------------------------------------------
-- The entries, written by level.
------------------------------------------------------------------------

ty-SI ty-add ty-FlC ty-Fld ty-ShC ty-Shape ty-Sig ty-telV ty-dRec ty-dNat ty-dCls ty-telF ty-telFs ty-tel
  ty-tabD ty-SD ty-lift ty-lifts ty-rnF ty-rnFs ty-lamΣ ty-KΣ : STy ε
tm-SI tm-add tm-FlC tm-Fld tm-ShC tm-Shape tm-Sig tm-telV tm-dRec tm-dNat tm-dCls tm-telF tm-telFs tm-tel
  tm-tabD tm-SD tm-lift tm-lifts tm-rnF tm-rnFs tm-lamΣ tm-KΣ : STm ε

ty-SI = Π Nat U
tm-SI = lam □ᵀ (⌜Σ⌝ (⌜Fin⌝ (L 0)) ⌜Nat⌝)

-- add k d = k + d
ty-add = Π Nat (Π Nat Nat)
tm-add = λ⁺ 2 (natrec □ᵀ (L 1) (nsuc v₀) (L 0))

-- FlC n t: rec ↦ Fin n × Nat ; nat ↦ Unit ; cls ↦ Fin n
ty-FlC = Π Nat (Π (Fin n₃) U)
tm-FlC = λ⁺ 2 (fcase □ □ᵀ (L 1) (⌜Σ⌝ (⌜Fin⌝ (L 0)) ⌜Nat⌝)
                (fcase □ □ᵀ v₀ ⌜Unit⌝ (fcase □ □ᵀ v₀ (⌜Fin⌝ (L 0)) (fcase0 □ᵀ v₀))))

ty-Fld = Π Nat U
tm-Fld = lam □ᵀ (⌜Σ⌝ (⌜Fin⌝ n₃) (FlC (L 0) v₀))

-- ShC n vs s b: fields ↦ Σ len. Fin len → Fld n ; var ↦ Id (Fin n) vs s
ty-ShC = Π Nat (Π (Fin v₀) (Π (Fin v₁) (Π (Fin n₂) U)))
tm-ShC = λ⁺ 4 (fcase □ □ᵀ (L 3) (⌜Σ⌝ ⌜Nat⌝ (⌜Π⌝ (⌜Fin⌝ v₀) (app (ref #Fld) (L 0))))
                (fcase □ □ᵀ v₀ (⌜Id⌝ (⌜Fin⌝ (L 0)) (L 1) (L 2)) (fcase0 □ᵀ v₀)))

ty-Shape = Π Nat (Π (Fin v₀) (Π (Fin v₁) U))
tm-Shape = λ⁺ 3 (⌜Σ⌝ (⌜Fin⌝ n₂) (ShC (L 0) (L 1) (L 2) v₀))

-- Sig n vs = Π (s : Fin n). Σ (c : Nat). Fin c → Shape n vs s
ty-Sig = Π Nat (Π (Fin v₀) U)
tm-Sig = λ⁺ 2 (⌜Π⌝ (⌜Fin⌝ (L 0)) (⌜Σ⌝ ⌜Nat⌝ (⌜Π⌝ (⌜Fin⌝ v₀) (app³ (ref #Shape) (L 0) (L 1) (L 2)))))

-- the variable: a Fin of the depth
ty-telV = Π Nat (Π (El (SIc v₀)) (Dt v₁))
tm-telV = λ⁺ 2 (dσ □ (⌜Fin⌝ (snd (L 1))) (lam □ᵀ (dι □)))

-- rec (s , k): a recursive position at (s , k + depth)
ty-dRec = Π Nat (Π (El (SIc v₀)) (Π (Σ' (Fin v₁) Nat) (Π (Dt v₂) (Dt v₃))))
tm-dRec = λ⁺ 4 (dρ □ (pair □ᵀ □ᵀ (fst (L 2)) (ADD (snd (L 2)) (snd (L 1)))) (L 3))

-- nat: a natural field
ty-dNat = Π Nat (Π (Dt v₀) (Dt v₁))
tm-dNat = λ⁺ 2 (dσ □ ⌜Nat⌝ (lam □ᵀ (L 1)))

-- cls s: a closed subterm, at (s , 0)
ty-dCls = Π Nat (Π (Fin v₀) (Π (Dt v₁) (Dt v₂)))
tm-dCls = λ⁺ 3 (dρ □ (pair □ᵀ □ᵀ (L 1) nzero) (L 2))

ty-telF = Π Nat (Π (El (SIc v₀)) (Π (FldT v₁) (Π (Dt v₂) (Dt v₃))))
tm-telF = λ⁺ 4 (tfBody (L 0) (L 1) (fst (L 2)) (snd (L 2)) (L 3))

ty-telFs = Π Nat (Π (El (SIc v₀)) (Π Nat (Π (Π (Fin v₀) (FldT v₃)) (Dt v₃))))
tm-telFs = λ⁺ 3 (natrec (Π (Π (Fin v₀) (FldT (L 0))) (Dt (L 0))) (lam □ᵀ (dι □))
                        (lam □ᵀ (TFe (L 0) (L 1) (app (L 5) (fzero □)) (app (L 4) (lam □ᵀ (app (L 5) (fsuc □ (L 6)))))))
                        (L 2))

-- ★ tel n vs s sh i : Desc (SI n)
ty-tel = Π Nat (Π (Fin v₀) (Π (Fin v₁) (Π (ShapeT v₂ v₁ v₀) (Π (El (SIc v₃)) (Dt v₄)))))
tm-tel = λ⁺ 5 (tBody (L 0) (L 1) (L 2) (L 4) (fst (L 3)) (snd (L 3)))

-- tabD n c f = λ k. case k of 0 ↦ f 0 ; suc k' ↦ tabD (λ y. f (suc y)) k'
ty-tabD = Π Nat (Π Nat (Π (Π (Fin v₀) (Dt v₂)) (Π (Fin v₁) (Dt v₃))))
tm-tabD = λ⁺ 2 (natrec (Π (Π (Fin v₀) (Dt (L 0))) (Π (Fin v₁) (Dt (L 0))))
                        (λ⁺ 2 (fcase0 □ᵀ (L 3)))
                        (λ⁺ 2 (fcase □ □ᵀ (L 5) (app (L 4) (fzero □)) (app² (L 3) (lam □ᵀ (app (L 4) (fsuc □ (L 7)))) (L 6))))
                        (L 1))

-- ★ SD n vs sg i : per sort its table (mapped), then tabulated — the Lib's form
ty-SD = Π Nat (Π (Fin v₀) (Π (SigT v₁ v₀) (Π (El (SIc v₂)) (Dt v₃))))
tm-SD = λ⁺ 4 (app (app³ (ref #tabD) (L 0) (L 0) (persortG (L 0) (L 1) (L 2) (L 3))) (fst (L 3)))

-- lift VF WK V0 d e σ = λ x. case x of 0 ↦ V0 e ; suc y ↦ WK e (σ y)
ty-lift = Π (Π Nat U) (Π (WKt (L 0)) (Π (V0t (L 0)) (Π Nat (Π Nat (Π (EnvT (L 0) (L 3) (L 4)) (EnvT (L 0) (nsuc (L 3)) (nsuc (L 4))))))))
tm-lift = λ⁺ 7 (fcase □ □ᵀ (L 6) (app (L 2) (L 4)) (app² (L 1) (L 4) (app (L 5) (L 7))))

-- lifts … k d e σ : Env (k + d) (k + e)
ty-lifts = Π (Π Nat U) (Π (WKt (L 0)) (Π (V0t (L 0)) (Π Nat (Π Nat (Π Nat
             (Π (EnvT (L 0) (L 4) (L 5)) (EnvT (L 0) (ADD (L 3) (L 4)) (ADD (L 3) (L 5)))))))))
tm-lifts = λ⁺ 7 (natrec (EnvT (L 0) (ADD (L 7) (L 4)) (ADD (L 7) (L 5))) (L 6)
                         (ref #lift · (L 0 ∷ L 1 ∷ L 2 ∷ ADD (L 7) (L 4) ∷ ADD (L 7) (L 5) ∷ L 8 ∷ []))
                         (L 3))

-- ★ one field: [kit… i e σ f ri re r p h] ↦ the payload at (fst i , e)
ty-rnF = Πˢ (kit ++ El (SIc N) ∷ Nat ∷ EnvT VF (snd (L 6)) (L 7) ∷ FldT N ∷ Dt N ∷ Dt N
                 ∷ Π (PAYg N VS SG (L 10)) (Π (DIhg N VS SG VF (L 10) (L 12)) (PAYg N VS SG (L 11)))
                 ∷ PAYg N VS SG (TFe N (L 6) (L 9) (L 10))
                 ∷ DIhg N VS SG VF (TFe N (L 6) (L 9) (L 10)) (L 13) ∷ [])
            (PAYg N VS SG (TFe N (IX (L 6) (L 7)) (L 9) (L 11)))
tm-rnF = λ⁺ 15 (app³ (fcase □ MOT (fst (L 9)) B0 B12) (snd (L 9)) (L 13) (L 14))
  where
    -- the convoy, over the field's tag t (L 15): payload q, p', h'
    MOT : {Γ : Cx} → STy (Γ ∙)
    MOT = Π (El (FlC N (L 15)))
            (Π (PAYg N VS SG (tfBody N (L 6) (L 15) (L 16) (L 10)))
               (Π (DIhg N VS SG VF (tfBody N (L 6) (L 15) (L 16) (L 10)) (L 17))
                  (PAYg N VS SG (tfBody N (IX (L 6) (L 7)) (L 15) (L 16) (L 11)))))
    -- rec (s , k): the hypothesis at k + e, through σ lifted k times
    B0 : T
    B0 = λ⁺ 3 (pair □ᵀ □ᵀ (app² (fst (L 17)) (ADD (snd (L 15)) (L 7))
                                (ref #lifts · (VF ∷ WK ∷ V0 ∷ snd (L 15) ∷ snd (L 6) ∷ L 7 ∷ L 8 ∷ [])))
                          (app² (L 12) (snd (L 16)) (snd (L 17))))
    B12 : T
    B12 = fcase □ MOT' (L 15)
            (λ⁺ 3 (pair □ᵀ □ᵀ (fst (L 17)) (app² (L 12) (snd (L 17)) (L 18))))          -- nat: copied
            (fcase □ MOT'' (L 16)
               (λ⁺ 3 (pair □ᵀ □ᵀ (fst (L 18)) (app² (L 12) (snd (L 18)) (snd (L 19)))))  -- cls: copied
               (fcase0 □ᵀ (L 17)))
      where
        MOT' MOT'' : {Γ : Cx} → STy (Γ ∙)
        MOT'  = Π (El (FlC N (fsuc □ (L 16))))
                  (Π (PAYg N VS SG (tfBody N (L 6) (fsuc □ (L 16)) (L 17) (L 10)))
                     (Π (DIhg N VS SG VF (tfBody N (L 6) (fsuc □ (L 16)) (L 17) (L 10)) (L 18))
                        (PAYg N VS SG (tfBody N (IX (L 6) (L 7)) (fsuc □ (L 16)) (L 17) (L 11)))))
        MOT'' = Π (El (FlC N (fsuc □ (fsuc □ (L 17)))))
                  (Π (PAYg N VS SG (tfBody N (L 6) (fsuc □ (fsuc □ (L 17))) (L 18) (L 10)))
                     (Π (DIhg N VS SG VF (tfBody N (L 6) (fsuc □ (fsuc □ (L 17))) (L 18) (L 10)) (L 19))
                        (PAYg N VS SG (tfBody N (IX (L 6) (L 7)) (fsuc □ (fsuc □ (L 17))) (L 18) (L 11)))))

-- ★ a field list: natrec on its length, in lockstep with telFs
ty-rnFs = Πˢ (kit ++ El (SIc N) ∷ Nat ∷ EnvT VF (snd (L 6)) (L 7) ∷ Nat ∷ Π (Fin (L 9)) (FldT N)
                  ∷ PAYg N VS SG (TFs N (L 6) (L 9) (L 10))
                  ∷ DIhg N VS SG VF (TFs N (L 6) (L 9) (L 10)) (L 11) ∷ [])
             (PAYg N VS SG (TFs N (IX (L 6) (L 7)) (L 9) (L 10)))
tm-rnFs = λ⁺ 10 (natrec MOTN (λ⁺ 3 unit) SN (L 9))
  where
    MOTN : {Γ : Cx} → STy (Γ ∙)
    MOTN = Π (Π (Fin (L 10)) (FldT N))
             (Π (PAYg N VS SG (TFs N (L 6) (L 10) (L 11)))
                (Π (DIhg N VS SG VF (TFs N (L 6) (L 10) (L 11)) (L 12))
                   (PAYg N VS SG (TFs N (IX (L 6) (L 7)) (L 10) (L 11)))))
    -- the tail of the field list fs (L 12)
    TAIL : T
    TAIL = lam □ᵀ (app (L 12) (fsuc □ v₀))
    -- [m ih] fs p h: the head through rnF, the tail through ih
    SN : T
    SN = λ⁺ 3 (ref #rnF · (N ∷ VS ∷ SG ∷ VF ∷ WK ∷ V0 ∷ L 6 ∷ L 7 ∷ L 8 ∷ app (L 12) (fzero □)
                           ∷ TFs N (L 6) (L 10) TAIL ∷ TFs N (IX (L 6) (L 7)) (L 10) TAIL
                           ∷ λ⁺ 2 (app³ (L 11) TAIL (L 15) (L 16)) ∷ L 13 ∷ L 14 ∷ []))

-- the signatures
ty-lamΣ = SigT n₁ (fzero □)
tm-lamΣ = ⌜ libΣ ⌝Σ 0
ty-KΣ = SigT n₂ (fsuc □ (fzero □))
tm-KΣ = ⌜ KSig ⌝Σ 1

------------------------------------------------------------------------
-- The table, in entry order.
------------------------------------------------------------------------

private
  at : {A : Set} → A → List A → ℕ → A
  at d []       _       = d
  at d (x ∷ xs) zero    = x
  at d (x ∷ xs) (suc k) = at d xs k

tys : ℕ → STy ε
tys = at Unit (ty-SI ∷ ty-add ∷ ty-FlC ∷ ty-Fld ∷ ty-ShC ∷ ty-Shape ∷ ty-Sig ∷ ty-telV ∷ ty-dRec ∷ ty-dNat ∷ ty-dCls
               ∷ ty-telF ∷ ty-telFs ∷ ty-tel ∷ ty-tabD ∷ ty-SD ∷ ty-lift ∷ ty-lifts ∷ ty-rnF ∷ ty-rnFs
               ∷ ty-lamΣ ∷ ty-KΣ ∷ [])

tms : ℕ → STm ε
tms = at unit (tm-SI ∷ tm-add ∷ tm-FlC ∷ tm-Fld ∷ tm-ShC ∷ tm-Shape ∷ tm-Sig ∷ tm-telV ∷ tm-dRec ∷ tm-dNat ∷ tm-dCls
               ∷ tm-telF ∷ tm-telFs ∷ tm-tel ∷ tm-tabD ∷ tm-SD ∷ tm-lift ∷ tm-lifts ∷ tm-rnF ∷ tm-rnFs
               ∷ tm-lamΣ ∷ tm-KΣ ∷ [])

open import DirectedHoTT.Algorithm.SigBuild using ( module SigBuild )
open SigBuild 22 tys tms 1000 public

open import normalizer.Syntax.Types using ( _≡_; refl; _×_; _,_ )
open import DirectedHoTT.Spec.Signature using ( Sig )
import DirectedHoTT.Spec.Syntax as R
open import DirectedHoTT.Algorithm.Eval using ( eval; nfd; out )
open import DirectedHoTT.Lib.NatNum using ( num )
import DirectedHoTT.Lib.Syn as L

-- ★ the core is well-formed: the checker's output, nothing written
wf : WfSig S
wf = fromJust wfSig _
