-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ THE KNOT'S FRAME IN THE CORE (PLAN-BIDI §3g,
-- P6): what every Knot family written as core entries shares.
--
-- · the Knot's signature, closed (`SI₂`, `SD₂`, `KΣ`), its payloads and
--   per-constructor telescopes (`PAY`, `G0`), its syntax (`TmC`, `knode`,
--   the constructor numbers in KSig's order) and its weakening (`WK`, the
--   core traversal `SigMeth.#trav` at the renaming kit);
-- · per FAMILY, given its index code `J` and convoy `C` (module `Family`):
--   the result family `R`, the empty row and a one-alternative row, the
--   two cascades' motives (`PS` over sorts, `PK` over constructors), the
--   rows entry from SPARSE tables (only a family's non-empty rows are
--   written), and the description `#methD`-applied to them.
--
-- A family's segment writes its rows and nothing else of this.  Extracted
-- from `Examples/PwCore` (P5's measurement: ~50 of its lines were frame).
--
-- Variables are written by LEVEL.  `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.KnotFrame where
open import normalizer.Syntax.Types using ( _×_; _,_ )
open import Agda.Builtin.Nat using ( zero; suc; _+_; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; vz; vs )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Algorithm.Surface.Notation
open import DirectedHoTT.Examples.SigCore using ( #SI; #tel; #SD; #KΣ )
open import DirectedHoTT.Examples.SigMeth using ( #methD; #trav; #rVF; #rWK; #rV0; #rNK )

------------------------------------------------------------------------
-- The Knot's signature, closed: two sorts (0 types, 1 terms).
------------------------------------------------------------------------

SI₂ : T
SI₂ = app (ref #SI) n₂
SD₂ : T
SD₂ = app³ (ref #SD) n₂ (tag 1) (ref #KΣ)
KΣ : T
KΣ = ref #KΣ

-- a payload at description D
PAY : {Γ : Cx} → STm Γ → STy Γ
PAY D = El (dpay SI₂ SD₂ D)

-- sort s's constructor telescope at depth j (the decoder's MAP form)
G0 : (s j : T) → T
G0 s j = lam □ᵀ (app (app (app (app (app (ref #tel) n₂) (tag 1)) s) (app (snd (app KΣ s)) v₀)) (pair □ᵀ □ᵀ s j))

------------------------------------------------------------------------
-- The Knot's syntax: terms of a depth, nodes, weakening.
------------------------------------------------------------------------

-- the code of terms of depth d
TmC : {Γ : Cx} → STm Γ → STm Γ
TmC d = ⌜IMu⌝ SI₂ SD₂ (pair □ᵀ □ᵀ (tag 1) d)

-- constructor k's node on its fields
knode : ℕ → List T → T
knode k as = con □ □ □ (pair □ᵀ □ᵀ (tag k) (fields as))
  where fields : List T → T
        fields []       = unit
        fields (a ∷ as) = pair □ᵀ □ᵀ a (fields as)

-- the constructors, numbered in KSig's order: sort 0 (13 type formers)…
pattern #kbase = 0  ; pattern #kU    = 1  ; pattern #kPi  = 2  ; pattern #kSg   = 3
pattern #kEl   = 4  ; pattern #kHom  = 5  ; pattern #kUnit = 6  ; pattern #kNat  = 7
pattern #kId   = 8  ; pattern #kIMu  = 9  ; pattern #kDesc = 10 ; pattern #kDIh  = 11
pattern #kFin  = 12
-- …and sort 1 (39 term formers)
pattern #kvar    = 0  ; pattern #klam    = 1  ; pattern #kapp    = 2  ; pattern #kpair  = 3
pattern #kabsurd = 4  ; pattern #kordtr  = 5  ; pattern #kfst    = 6  ; pattern #ksnd   = 7
pattern #kcbase  = 8  ; pattern #kcPi    = 9  ; pattern #kcSg    = 10 ; pattern #kcHom  = 11
pattern #khrefl  = 12 ; pattern #ktr     = 13 ; pattern #kap     = 14 ; pattern #kcId   = 15
pattern #kidrefl = 16 ; pattern #kjsub   = 17 ; pattern #kunit   = 18 ; pattern #knzero = 19
pattern #knsuc   = 20 ; pattern #knatrec = 21 ; pattern #kcon    = 22 ; pattern #kielim = 23
pattern #kdI     = 24 ; pattern #kdS     = 25 ; pattern #kdR     = 26 ; pattern #kdpay  = 27
pattern #kdih    = 28 ; pattern #kfzero  = 29 ; pattern #kfsuc   = 30 ; pattern #kfcase = 31
pattern #kfcase0 = 32 ; pattern #kpsplit = 33 ; pattern #kcNat   = 34 ; pattern #kcIMu  = 35
pattern #kcFin   = 36 ; pattern #kcUnit  = 37 ; pattern #kref    = 38
nTy nTm : ℕ
nTy = 13
nTm = 39

kvar0 : T
kvar0 = knode #kvar (fzero □ ∷ [])

-- weakening a term t of depth j (the core traversal at the renaming kit)
WK : (j t : T) → T
WK j t = ref #trav · (n₂ ∷ tag 1 ∷ KΣ ∷ ref #rVF ∷ ref #rWK ∷ ref #rV0 ∷ ref #rNK
                      ∷ tag 1 ∷ j ∷ t ∷ nsuc j ∷ lam □ᵀ (fsuc □ v₀) ∷ [])

------------------------------------------------------------------------
-- A side condition's premises (trivial convoy): fields of a payload at
-- level b+1, indices `(1 , j+k) , f p , tt`.
------------------------------------------------------------------------

Fld : Set
Fld = {Γ : Cx} → STm Γ → STm Γ

-- a side condition's index at depth `j + k`, code `f p`
ixAt : ℕ → Fld → ℕ → T
ixAt k f b = pair □ᵀ □ᵀ (pair □ᵀ □ᵀ (tag 1) (nsucⁿ k (L b))) (pair □ᵀ □ᵀ (f (L (b + 1))) unit)
  where nsucⁿ : ℕ → T → T
        nsucⁿ zero    x = x
        nsucⁿ (suc i) x = nsuc (nsucⁿ i x)

-- a premise: the family itself at a field of the payload, `k` binders deeper
recAt : ℕ → Fld → ℕ → T
recAt k f b = dρ □ (ixAt k f b) (dι □)

------------------------------------------------------------------------
-- ★ A FAMILY with index code J and convoy C: R i = El (C i) → Desc J.
------------------------------------------------------------------------

module Family (J C : T) where

  R : T → TT
  R i = Π (El (app C i)) (Desc J)

  -- ★ a row is `λ j p h c. <its alternatives>` with its first level b
  --   (j b, p b+1, h b+2, c b+3, the alternative b+4)
  none : ℕ → T
  none b = λ⁺ 4 (dσ □ (⌜Fin⌝ nzero) (lam □ᵀ (fcase0 □ᵀ v₀)))
  one : (ℕ → T) → ℕ → T
  one X b = λ⁺ 4 (dσ □ (⌜Fin⌝ (nsuc nzero)) (lam □ᵀ (fcase □ (Desc J) v₀ (X b) (fcase0 □ᵀ v₀))))
  -- the row with one alternative and no premise
  unconditional : ℕ → T
  unconditional = one (λ b → dι □)

  -- a premise: ANOTHER family of this index (description entry D) at a
  --   field of the payload, as a σ-field
  holds : ℕ → Fld → ℕ → T
  holds D f b = dσ □ (⌜IMu⌝ J (ref D) (ixAt 0 f b)) (lam □ᵀ (dι □))

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

  -- ★ a SPARSE table: constructor k's row if listed, else the empty row
  table : ℕ → List (ℕ × (ℕ → T)) → List (ℕ → T)
  table n spec = go 0 n
    where
    pick : ℕ → List (ℕ × (ℕ → T)) → ℕ → T
    pick k []              = none
    pick k ((k' , r) ∷ ks) = sel (k == k')
      where sel : Bool → ℕ → T
            sel true  = r
            sel false = pick k ks
    go : ℕ → ℕ → List (ℕ → T)
    go k zero    = []
    go k (suc m) = pick k spec ∷ go (suc k) m

  -- ★ the index: (i , t , c) — a sort-and-depth, a subject, its convoy
  ty-index : STy ε
  ty-index = U
  tm-index : STm ε
  tm-index = ⌜Σ⌝ SI₂ (⌜Σ⌝ (⌜IMu⌝ SI₂ SD₂ v₀) (app C (var (vs vz))))

  -- ★ the rows entry, from the two sorts' sparse tables
  ty-rows : STy ε
  ty-rows = Π (Fin n₂) (PS 0 0)
  tm-rows : List (ℕ × (ℕ → T)) → List (ℕ × (ℕ → T)) → STm ε
  tm-rows tys tms = lam □ᵀ (fcases PS 0 (sortLeaf (tag 0) (table nTy tys)
                                        ∷ sortLeaf (tag 1) (table nTm tms) ∷ []) v₀)

  -- ★ the description: the fibre of the subject, the convoy applied (the rows entry `rowsE`)
  ty-desc : STy ε
  ty-desc = Π (El J) (Desc J)
  tm-desc : ℕ → STm ε
  tm-desc rowsE = lam □ᵀ (app (ielim □ SD₂ (Π (El (app C (var (vs vz)))) (Desc J)) (fst v₀)
                                  (ref #methD · (n₂ ∷ tag 1 ∷ KΣ ∷ J ∷ C ∷ ref rowsE ∷ [])) (fst (snd v₀)))
                           (snd (snd v₀)))
