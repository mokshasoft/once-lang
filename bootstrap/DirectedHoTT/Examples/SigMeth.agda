-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★ METHODS BY CASCADES: the core's `methAt`, and
-- the generic TRAVERSAL on it.  A `SigExtend` segment over
-- `Examples/SigCore` (PLAN-BIDI §3g, the Pw POC's P1).
--
-- A method of the decoder's eliminator is written as the Lib writes it
-- (`Lib/MethAt.methAt`): split the index, a CASCADE over the sorts, split
-- the payload, a cascade over the constructors, a LEAF per constructor.
-- So a core program at `⌜KSig⌝` has the Lib's NORMAL FORM, and the Knot
-- can move onto the core one family at a time by conversion (as SigCore's
-- decoder has `KD`'s): `Examples/NbETravAgree` checks that `#trav` at the
-- Knot's signature IS the Knot's weakening, normal form for normal form.
--
-- ★ Leaves see the MAP form, results the TABULATED form.  The decoder
--   tabulates (a `fcase` cascade, the Lib's normal form), so at a
--   variable sort or constructor its description is stuck.  Each cascade
--   is a `natrec` over the table's length whose leaf at tag k is typed
--   at the map form (`G k`: a telescope, a `dσ`) and whose result is
--   typed at the tabulated form (`tabD G k`); a case on k turns one into
--   the other, so the two line up in LOCKSTEP.  At the identity
--   embedding the tabulated form IS the decoder.
-- ★ One cascade per RESULT KIND.  The motive is over the index only (the
--   uses are recursions, not inductions), and the core has no universe
--   code for `Desc`, so the result family is a parameter of the Agda-level
--   generator `Casc`, instantiated twice: Desc-valued (fibres: Pw) and
--   U-coded (programs: the traversal).
-- ★ A node is built through `#conAt`: the constructor at the map form,
--   by the same two cascades in the other direction (sorts, constructors).
--
-- Variables in the entries are written by LEVEL.  `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.SigMeth where
open import normalizer.Syntax.Types using ( _≡_; refl )
open import Agda.Builtin.Nat using ( zero; suc; _-_; _+_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; vz; vs )
open import DirectedHoTT.Metatheory.Signature using ( WfSig )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Algorithm.SigBuild using ( module SigExtend )
import DirectedHoTT.Examples.SigCore as Base

private
  pattern v₀ = var vz
  wk : {Γ : Cx} → STm Γ → STm (Γ ∙)
  wk = renTmˢ vs
  V : {Γ : Cx} → ℕ → STm Γ
  V {ε}    _       = unit
  V {Γ ∙}  zero    = var vz
  V {Γ ∙}  (suc k) = wk (V {Γ} k)
  lenC : Cx → ℕ
  lenC ε     = 0
  lenC (Γ ∙) = suc (lenC Γ)
  L : {Γ : Cx} → ℕ → STm Γ
  L {Γ} ℓ = V {Γ} (lenC Γ - suc ℓ)
  T TT : Set
  T  = {Γ : Cx} → STm Γ
  TT = {Γ : Cx} → STy Γ
  app² : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ
  app² f a b = app (app f a) b
  app³ : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  app³ f a b c = app (app² f a b) c
  app⁴ : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
  app⁴ f a b c d = app (app³ f a b c) d
  _·_ : {Γ : Cx} → STm Γ → List (STm Γ) → STm Γ
  f · []       = f
  f · (x ∷ xs) = app f x · xs
  infixl 9 _·_
  _++_ : {A : Set} → List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
  infixr 5 _++_
  λ⁺ : {Γ : Cx} → ℕ → T → STm Γ
  λ⁺ zero    b = b
  λ⁺ (suc k) b = lam □ᵀ (λ⁺ k b)
  Πˢ : List TT → TT → TT
  Πˢ []       B = B
  Πˢ (A ∷ As) B = Π A (Πˢ As B)

private
  -- the base's entries (Examples/SigCore)
  pattern #lamΣ = 20
  pattern #KΣ   = 21
  pattern #tel  = 13
  pattern #tabD = 14
  pattern #SD   = 15
private
  SIc : {Γ : Cx} → STm Γ → STm Γ
  SIc n = app (ref 0) n
  Dt : {Γ : Cx} → STm Γ → STy Γ
  Dt n = Desc (SIc n)
  SigT : {Γ : Cx} → STm Γ → STm Γ → STy Γ
  SigT n v = El (app² (ref 6) n v)
  N VS SG : T
  N = L 0 ; VS = L 1 ; SG = L 2
  SDN : T
  SDN = app³ (ref #SD) N VS SG
  TabApp : (m G : T) {Γ : Cx} → STm Γ → STm Γ
  TabApp m G k = app (app³ (ref #tabD) N m G) k
  PAY : {Γ : Cx} → STm Γ → STy Γ
  PAY D = El (dpay (SIc N) SDN D)

  -- the decoder's per-sort table at index i (SigCore's `persortG`)
  persortG : (i : T) → T
  persortG i =
    lam □ᵀ (dσ □ (⌜Fin⌝ (fst (app SG v₀)))
                 (app³ (ref #tabD) N (fst (app SG v₀))
                       (lam □ᵀ (app⁴ (app (ref #tel) N) VS (var (vs vz)) (app (snd (app SG (var (vs vz)))) v₀) i))))
  -- sort s's constructor table at (s , j): MAP form, and tabulated
  G0 GS : (s j : T) → T
  G0 s j = lam □ᵀ (app⁴ (app (ref #tel) N) VS s (app (snd (app SG s)) v₀) (pair □ᵀ □ᵀ s j))
  GS s j = app³ (ref #tabD) N (fst (app SG s)) (G0 s j)
  IXk : (E k j : T) → T
  IXk E k j = pair □ᵀ □ᵀ (app E k) j
  PSGe TABe : (m E k j : T) → T
  PSGe m E k j = app (persortG (IXk E k j)) (app E k)
  TABe m E k j = app (app³ (ref #tabD) N m (lam □ᵀ (app (persortG (IXk E k j)) (app E v₀)))) k

------------------------------------------------------------------------
-- ★ The cascades, for motive globals MG (after n vs sg) and a result
--   family R over the index.  `ab` is the first entry's absolute number.
------------------------------------------------------------------------
module Casc (ab : ℕ) (MG : List TT) (gs : List T) (R : T → TT) where
  len : {A : Set} → List A → ℕ
  len []       = 0
  len (_ ∷ xs) = suc (len xs)
  o : ℕ
  o = 3 + len MG
  G3 : List TT
  G3 = Nat ∷ Fin N ∷ SigT N VS ∷ MG
  ARGS : {Γ : Cx} → List (STm Γ)
  ARGS = N ∷ VS ∷ SG ∷ map gs
    where map : {Γ : Cx} → List T → List (STm Γ)
          map []       = []
          map (x ∷ xs) = x ∷ map xs

  -- the method type at description D and index I, first binder at level d
  MI : (D I : T) → ℕ → TT
  MI D I d = Π (PAY D) (Π (DIh (SIc N) SDN (R (L (suc d))) D (L d)) (R I))

  -- [k at b, j at b+1]
  SortT : (Dm : T → T → T → T → T) (m E : T) → ℕ → TT
  SortT Dm m E b = Π (Fin m) (Π Nat (MI (Dm m E (L b) (L (suc b))) (IXk E (L b) (L (suc b))) (suc (suc b))))

  -- ★ tabM … i m G F : the constructor cascade; leaves at the MAP table G,
  --   the result at the tabulated one
  ty-tabM : TT
  ty-tabM = Πˢ (G3 ++ El (SIc N) ∷ Nat ∷ Π (Fin (L (o + 1))) (Dt N)
                   ∷ Π (Fin (L (o + 1))) (MI (app (L (o + 2)) (L (o + 3))) (L o) (o + 4)) ∷ [])
               (Π (Fin (L (o + 1))) (MI (TabApp (L (o + 1)) (L (o + 2)) (L (o + 4))) (L o) (o + 5)))
  tm-tabM : T
  tm-tabM = λ⁺ (o + 2) (natrec MOT (λ⁺ 3 (fcase0 □ᵀ (L (o + 4))))
                (λ⁺ 3 (fcase □ (MI (TabApp (nsuc (L (o + 2))) (L (o + 4)) (L (o + 7))) (L o) (o + 8)) (L (o + 6))
                          (app (L (o + 5)) (fzero □))
                          (app³ (L (o + 3)) (lam □ᵀ (app (L (o + 4)) (fsuc □ (L (o + 8)))))
                                            (lam □ᵀ (app (L (o + 5)) (fsuc □ (L (o + 8))))) (L (o + 7)))))
                (L (o + 1)))
    where
    MOT : {Γ : Cx} → STy (Γ ∙)
    MOT = Π (Π (Fin (L (o + 2))) (Dt N))
            (Π (Π (Fin (L (o + 2))) (MI (app (L (o + 3)) (L (o + 4))) (L o) (o + 5)))
               (Π (Fin (L (o + 2))) (MI (TabApp (L (o + 2)) (L (o + 3)) (L (o + 5))) (L o) (o + 6))))

  -- ★ tabS … m E F : the sort cascade (leaves at the decoder's MAP form)
  ty-tabS : TT
  ty-tabS = Πˢ (G3 ++ Nat ∷ Π (Fin (L o)) (Fin N) ∷ SortT PSGe (L o) (L (o + 1)) (o + 2) ∷ [])
               (SortT TABe (L o) (L (o + 1)) (o + 3))
  tm-tabS : T
  tm-tabS = λ⁺ (o + 1) (natrec MOT (λ⁺ 3 (fcase0 □ᵀ (L (o + 3))))
                (λ⁺ 3 (fcase □ MOTK (L (o + 5)) (app (L (o + 4)) (fzero □))
                          (app³ (L (o + 2)) (lam □ᵀ (app (L (o + 3)) (fsuc □ (L (o + 7)))))
                                            (lam □ᵀ (app (L (o + 4)) (fsuc □ (L (o + 7))))) (L (o + 6)))))
                (L o))
    where
    MOT : {Γ : Cx} → STy (Γ ∙)
    MOT = Π (Π (Fin (L (o + 1))) (Fin N)) (Π (SortT PSGe (L (o + 1)) (L (o + 2)) (o + 3)) (SortT TABe (L (o + 1)) (L (o + 2)) (o + 4)))
    MOTK : {Γ : Cx} → STy (Γ ∙)
    MOTK = Π Nat (MI (TABe (nsuc (L (o + 1))) (L (o + 3)) (L (o + 6)) (L (o + 7))) (IXk (L (o + 3)) (L (o + 6)) (L (o + 7))) (o + 8))

  -- ★ meth … leaves : THE METHOD — split the index, the sort cascade, split
  --   the payload, the constructor cascade; at (s , k) the leaf
  --   `leaves s k j p h`, its payload at the constructor's own telescope
  LeafT : TT
  LeafT = Π (Fin N) (Π (Fin (fst (app SG (L o)))) (Π Nat
            (MI (app (G0 (L o) (L (o + 2))) (L (o + 1))) (pair □ᵀ □ᵀ (L o) (L (o + 2))) (o + 3))))
  ty-meth : TT
  ty-meth = Πˢ (G3 ++ LeafT ∷ []) (Π (El (SIc N)) (MI (app SDN (L (o + 1))) (L (o + 1)) (o + 2)))
  tm-meth : T
  tm-meth = λ⁺ (o + 1) (lam □ᵀ (psplit □ᵀ □ᵀ (MI (app SDN (L (o + 2))) (L (o + 2)) (o + 3))
                                  (app² (ref (suc ab) · (ARGS ++ N ∷ lam □ᵀ v₀ ∷ FS ∷ [])) (L (o + 2)) (L (o + 3)))
                                  (L (o + 1))))
    where
    -- [s o+4, j o+5, y o+6]
    FS : T
    FS = λ⁺ 3 (psplit □ᵀ □ᵀ PM
                 (app² (ref ab · (ARGS ++ pair □ᵀ □ᵀ (L (o + 4)) (L (o + 5)) ∷ fst (app SG (L (o + 4)))
                                        ∷ G0 (L (o + 4)) (L (o + 5)) ∷ FK ∷ []))
                       (L (o + 7)) (L (o + 8)))
                 (L (o + 6)))
      where
      PM : {Γ : Cx} → STy (Γ ∙)
      PM = Π (DIh (SIc N) SDN (R (L (o + 8))) (dσ □ (⌜Fin⌝ (fst (app SG (L (o + 4))))) (GS (L (o + 4)) (L (o + 5)))) (L (o + 7)))
             (R (pair □ᵀ □ᵀ (L (o + 4)) (L (o + 5))))
      -- [k o+9, p o+10, h o+11]
      FK : T
      FK = λ⁺ 3 (L o · (L (o + 4) ∷ L (o + 9) ∷ L (o + 5) ∷ L (o + 10) ∷ L (o + 11) ∷ []))

------------------------------------------------------------------------
-- ★ The traversal on the cascades: its motive as a CODE over the index,
--   its leaves SigCore's `FCONS` with the builder `λ q. con (k , q)`
------------------------------------------------------------------------
private
  pattern #telV  = 7
  pattern #telFs = 12
  pattern #rnFs  = 19

-- ★ this segment's entries
pattern #tabMD = 22     -- the Desc-valued cascades (fibres) …
pattern #tabSD = 23
pattern #methD = 24     --   … and their method
pattern #tabMU = 25     -- the U-coded cascades (programs) …
pattern #tabSU = 26
pattern #methU = 27     --   … and their method
pattern #rnL   = 31     -- the traversal's leaves
pattern #trav  = 32     -- ★ THE TRAVERSAL, generic in signature and kit
pattern #rVF   = 33     -- the renaming kit: values are variables
pattern #rWK   = 34
pattern #rV0   = 35
pattern #rNλ   = 36     --   its variable node, per signature
pattern #rNK   = 37
pattern #sVF   = 38     -- ★ the substitution kit: values are terms of sort vs
pattern #sWK   = 39     --   (weakening a value is renaming it)
pattern #sV0   = 40
pattern #sN    = 41
FldT : {Γ : Cx} → STm Γ → STy Γ
FldT n = El (app (ref 3) n)
ShC : {Γ : Cx} → STm Γ → STm Γ → STm Γ → STm Γ → STm Γ
ShC n v s b = app⁴ (ref 4) n v s b
tBody : (n v s i : T) {Γ : Cx} (b x : STm Γ) → STm Γ
tBody n v s i b x =
  app (fcase □ (Π (El (ShC n v s v₀)) (Dt n)) b
         (lam (Σ' Nat (Π (Fin v₀) (FldT n))) (app⁴ (ref #telFs) n i (fst v₀) (snd v₀)))
         (lam □ᵀ (app² (ref #telV) n i)))
      x
VF WK V0 NODE : T
VF = L 3 ; WK = L 4 ; V0 = L 5 ; NODE = L 6
WKt V0t : TT
WKt = Π Nat (Π (El (app VF v₀)) (El (app VF (nsuc (var (vs vz))))))
V0t = Π Nat (El (app VF (nsuc v₀)))
MU : {Γ : Cx} → STm Γ → STy Γ
MU j = IMu (SIc N) SDN j
NODEt : TT
NODEt = Π Nat (Π (El (app VF v₀)) (MU (pair □ᵀ □ᵀ VS (var (vs vz)))))
kit : List TT
kit = Nat ∷ Fin N ∷ SigT N VS ∷ Π Nat U ∷ WKt ∷ V0t ∷ []
-- M i = Π e. (Fin (snd i) → VF e) → Syn (fst i) e, as a code
TMc : T
TMc = lam □ᵀ (⌜Π⌝ ⌜Nat⌝ (⌜Π⌝ (⌜Π⌝ (⌜Fin⌝ (snd (var (vs vz)))) (app VF (var (vs vz))))
                             (⌜IMu⌝ (SIc N) SDN (pair □ᵀ □ᵀ (fst (var (vs (vs vz)))) (var (vs vz))))))
RT : T → TT
RT i = El (app (the (Π (El (SIc N)) U) TMc) i)

-- ★ the CONSTRUCTOR at the map form: conAt s k e q = con (k , q), its
--   payload at constructor k's own telescope.  At a variable sort the
--   decoder's tabulated form is stuck, so a con is built through the two
--   cascades that line the tabulation up (sorts, then constructors)
pattern #conK  = 28
pattern #conS  = 29
pattern #conAt = 30
ty-conK : TT
ty-conK = Πˢ (Nat ∷ Fin N ∷ SigT N VS ∷ Fin N ∷ Nat ∷ Nat ∷ Π (Fin (L 5)) (Dt N)
                ∷ Π (Fin (L 5)) (Π (PAY (TabApp (L 5) (L 6) (L 7))) (MU (pair □ᵀ □ᵀ (L 3) (L 4)))) ∷ [])
             (Π (Fin (L 5)) (Π (PAY (app (L 6) (L 8))) (MU (pair □ᵀ □ᵀ (L 3) (L 4)))))
tm-conK : T
tm-conK = λ⁺ 6 (natrec MOT (λ⁺ 3 (fcase0 □ᵀ (L 8)))
                  (λ⁺ 3 (fcase □ (Π (PAY (app (L 8) (L 11))) MUse) (L 10) (app (L 9) (fzero □))
                           (app³ (L 7) (lam □ᵀ (app (L 8) (fsuc □ (L 12)))) (lam □ᵀ (app (L 9) (fsuc □ (L 12)))) (L 11))))
                  (L 5))
  where
  MUse : TT
  MUse = MU (pair □ᵀ □ᵀ (L 3) (L 4))
  MOT : {Γ : Cx} → STy (Γ ∙)
  MOT = Π (Π (Fin (L 6)) (Dt N)) (Π (Π (Fin (L 6)) (Π (PAY (TabApp (L 6) (L 7) (L 8))) MUse))
          (Π (Fin (L 6)) (Π (PAY (app (L 7) (L 9))) MUse)))
ConT : (Dm : T → T → T → T → T) (m E : T) → ℕ → TT
ConT Dm m E b = Π (Fin m) (Π Nat (Π (PAY (Dm m E (L b) (L (suc b)))) (MU (IXk E (L b) (L (suc b))))))
ty-conS : TT
ty-conS = Πˢ (Nat ∷ Fin N ∷ SigT N VS ∷ Nat ∷ Π (Fin (L 3)) (Fin N) ∷ ConT TABe (L 3) (L 4) 5 ∷ [])
             (ConT PSGe (L 3) (L 4) 6)
tm-conS : T
tm-conS = λ⁺ 4 (natrec MOT (λ⁺ 3 (fcase0 □ᵀ (L 6)))
                  (λ⁺ 3 (fcase □ MOTK (L 8) (app (L 7) (fzero □))
                           (app³ (L 5) (lam □ᵀ (app (L 6) (fsuc □ (L 10)))) (lam □ᵀ (app (L 7) (fsuc □ (L 10)))) (L 9))))
                  (L 3))
  where
  MOT : {Γ : Cx} → STy (Γ ∙)
  MOT = Π (Π (Fin (L 4)) (Fin N)) (Π (ConT TABe (L 4) (L 5) 6) (ConT PSGe (L 4) (L 5) 7))
  MOTK : {Γ : Cx} → STy (Γ ∙)
  MOTK = Π Nat (Π (PAY (PSGe (nsuc (L 4)) (L 6) (L 9) (L 10))) (MU (IXk (L 6) (L 9) (L 10))))
ty-conAt : TT
ty-conAt = Πˢ (Nat ∷ Fin N ∷ SigT N VS ∷ Fin N ∷ Fin (fst (app SG (L 3))) ∷ Nat ∷ PAY (app (G0 (L 3) (L 5)) (L 4)) ∷ [])
              (MU (pair □ᵀ □ᵀ (L 3) (L 5)))
tm-conAt : T
tm-conAt = λ⁺ 7 (app² (ref #conK · (N ∷ VS ∷ SG ∷ L 3 ∷ L 5 ∷ fst (app SG (L 3)) ∷ G0 (L 3) (L 5) ∷ MKK ∷ [])) (L 4) (L 6))
  where
  MKS MKK : T
  MKS = λ⁺ 3 (con □ □ □ (L 11))
  MKK = λ⁺ 2 (app³ (ref #conS · (N ∷ VS ∷ SG ∷ N ∷ lam □ᵀ v₀ ∷ MKS ∷ [])) (L 3) (L 5) (pair □ᵀ □ᵀ (L 7) (L 8)))

-- ★ rnL kit… NODE s k j p h e σ : the leaf at constructor k of sort s
ty-rnL : TT
ty-rnL = Πˢ (kit ++ NODEt ∷ [])
            (Π (Fin N) (Π (Fin (fst (app SG (L 7)))) (Π Nat
               (Π (PAY (app (G0 (L 7) (L 9)) (L 8)))
                  (Π (DIh (SIc N) SDN (RT (L 11)) (app (G0 (L 7) (L 9)) (L 8)) (L 10))
                     (RT (pair □ᵀ □ᵀ (L 7) (L 9))))))))
tm-rnL : T
tm-rnL = λ⁺ 14 (app³ (app (fcase □ MOTM (fst SHk) FB VB) (snd SHk)) (L 10) (L 11) MK)
  where
  I' IXe : T
  I'  = pair □ᵀ □ᵀ (L 7) (L 9)
  IXe = pair □ᵀ □ᵀ (L 7) (L 12)
  SHk : T
  SHk = app (snd (app SG (L 7))) (L 8)
  MUse : TT
  MUse = MU IXe
  MK : T
  MK = lam □ᵀ (ref #conAt · (N ∷ VS ∷ SG ∷ L 7 ∷ L 8 ∷ L 12 ∷ v₀ ∷ []))
  -- over the shape's tag b (L 14)
  MOTM : {Γ : Cx} → STy (Γ ∙)
  MOTM = Π (El (ShC N VS (L 7) (L 14)))
           (Π (PAY (tBody N VS (L 7) I' (L 14) (L 15)))
              (Π (DIh (SIc N) SDN (RT (L 17)) (tBody N VS (L 7) I' (L 14) (L 15)) (L 16))
                 (Π (Π (PAY (tBody N VS (L 7) IXe (L 14) (L 15))) MUse) MUse)))
  FB : T
  FB = λ⁺ 4 (app (L 17) (ref #rnFs · (N ∷ VS ∷ SG ∷ VF ∷ WK ∷ V0 ∷ I' ∷ L 12 ∷ L 13
                                       ∷ fst (L 14) ∷ snd (L 14) ∷ L 15 ∷ L 16 ∷ [])))
  VB : T
  VB = fcase □ MOTV (L 14)
         (λ⁺ 4 (jsub □ᵀ □ □ (⌜IMu⌝ (SIc N) SDN (pair □ᵀ □ᵀ (L 19) (L 12))) (L 15)
                      (app² NODE (L 12) (app (L 13) (fst (L 16))))))
         (fcase0 □ᵀ (L 15))
    where
    MOTV : {Γ : Cx} → STy (Γ ∙)
    MOTV = Π (El (ShC N VS (L 7) (fsuc □ (L 15))))
             (Π (PAY (tBody N VS (L 7) I' (fsuc □ (L 15)) (L 16)))
                (Π (DIh (SIc N) SDN (RT (L 18)) (tBody N VS (L 7) I' (fsuc □ (L 15)) (L 16)) (L 17))
                   (Π (Π (PAY (tBody N VS (L 7) IXe (fsuc □ (L 15)) (L 16))) MUse) MUse)))

-- ★ trav kit… NODE s d t e σ : the term t of sort s, from depth d to e
ty-trav : TT
ty-trav = Πˢ (kit ++ NODEt ∷ Fin N ∷ Nat ∷ MU (pair □ᵀ □ᵀ (L 7) (L 8)) ∷ Nat
                   ∷ Π (Fin (L 8)) (El (app VF (L 10))) ∷ [])
              (MU (pair □ᵀ □ᵀ (L 7) (L 10)))
tm-trav : T
tm-trav = λ⁺ 12 (app² (ielim □ SDN (El (app TMc (var (vs vz)))) (pair □ᵀ □ᵀ (L 7) (L 8))
                          (ref #methU · (N ∷ VS ∷ SG ∷ TMc ∷ ref #rnL · (N ∷ VS ∷ SG ∷ VF ∷ WK ∷ V0 ∷ NODE ∷ []) ∷ []))
                          (L 9))
                    (L 10) (L 11))

-- the Desc-valued instance (fibres): globals J C, R i = El (C i) → Desc J
module CD = Casc #tabMD (U ∷ Π (El (SIc N)) U ∷ []) (L 3 ∷ L 4 ∷ []) (λ i → Π (El (app (L 4) i)) (Desc (L 3)))
-- the U-coded instance (programs): global M, R i = El (M i)
module CU = Casc #tabMU (Π (El (SIc N)) U ∷ []) (L 3 ∷ []) (λ i → El (app (L 3) i))

------------------------------------------------------------------------
-- The kits (moved from SigCore with the traversal).
------------------------------------------------------------------------
n₁ n₂ : T
n₁ = nsuc nzero
n₂ = nsuc n₁
NODEp : (n v sg vf : T) → TT
NODEp n v sg vf = Π Nat (Π (El (app vf v₀)) (IMu (SIc n) (app³ (ref #SD) n v sg) (pair □ᵀ □ᵀ v (var (vs vz)))))
WKp V0p : T → TT
WKp vf = Π Nat (Π (El (app vf v₀)) (El (app vf (nsuc (var (vs vz))))))
V0p vf = Π Nat (El (app vf (nsuc v₀)))

ty-rVF ty-rWK ty-rV0 ty-rNλ ty-rNK ty-sVF ty-sWK ty-sV0 ty-sN : STy ε
tm-rVF tm-rWK tm-rV0 tm-rNλ tm-rNK tm-sVF tm-sWK tm-sV0 tm-sN : STm ε
ty-rVF = Π Nat U
tm-rVF = lam □ᵀ (⌜Fin⌝ (L 0))
ty-rWK = WKp (ref #rVF)
tm-rWK = λ⁺ 2 (fsuc □ (L 1))
ty-rV0 = V0p (ref #rVF)
tm-rV0 = lam □ᵀ (fzero □)
-- …and its variable node, per signature (constructor 0 of the variable sort)
ty-rNλ = NODEp n₁ (fzero □) (ref #lamΣ) (ref #rVF)
tm-rNλ = λ⁺ 2 (con □ □ □ (pair □ᵀ □ᵀ (fzero □) (pair □ᵀ □ᵀ (L 1) unit)))
ty-rNK = NODEp n₂ (fsuc □ (fzero □)) (ref #KΣ) (ref #rVF)
tm-rNK = λ⁺ 2 (con □ □ □ (pair □ᵀ □ᵀ (fzero □) (pair □ᵀ □ᵀ (L 1) unit)))

-- ★ the substitution kit, generic in the signature (given its variable
--   node at the renaming kit): [n vs sg rN]
private
  rNt : TT
  rNt = NODEp N VS SG (ref #rVF)
  sVF : T
  sVF = app³ (ref #sVF) N VS SG

ty-sVF = Π Nat (Π (Fin v₀) (Π (SigT (var (vs vz)) v₀) (Π Nat U)))
tm-sVF = λ⁺ 4 (⌜IMu⌝ (SIc N) SDN (pair □ᵀ □ᵀ VS (L 3)))
ty-sWK = Πˢ (Nat ∷ Fin N ∷ SigT N VS ∷ rNt ∷ []) (WKp sVF)
tm-sWK = λ⁺ 6 (ref #trav · (N ∷ VS ∷ SG ∷ ref #rVF ∷ ref #rWK ∷ ref #rV0 ∷ L 3
                            ∷ VS ∷ L 4 ∷ L 5 ∷ nsuc (L 4) ∷ lam □ᵀ (fsuc □ (L 6)) ∷ []))
ty-sV0 = Πˢ (Nat ∷ Fin N ∷ SigT N VS ∷ rNt ∷ []) (V0p sVF)
tm-sV0 = λ⁺ 5 (app² (L 3) (nsuc (L 4)) (fzero □))
ty-sN = Πˢ (Nat ∷ Fin N ∷ SigT N VS ∷ []) (NODEp N VS SG sVF)
tm-sN = λ⁺ 5 (L 4)

------------------------------------------------------------------------
-- The table, in entry order (relative to the base's 22).
------------------------------------------------------------------------
private
  at : {A : Set} → A → List A → ℕ → A
  at d []       _       = d
  at d (x ∷ xs) zero    = x
  at d (x ∷ xs) (suc k) = at d xs k

tys : ℕ → STy ε
tys = at Unit (CD.ty-tabM ∷ CD.ty-tabS ∷ CD.ty-meth ∷ CU.ty-tabM ∷ CU.ty-tabS ∷ CU.ty-meth
               ∷ ty-conK ∷ ty-conS ∷ ty-conAt ∷ ty-rnL ∷ ty-trav
               ∷ ty-rVF ∷ ty-rWK ∷ ty-rV0 ∷ ty-rNλ ∷ ty-rNK ∷ ty-sVF ∷ ty-sWK ∷ ty-sV0 ∷ ty-sN ∷ [])
tms : ℕ → STm ε
tms = at unit (CD.tm-tabM ∷ CD.tm-tabS ∷ CD.tm-meth ∷ CU.tm-tabM ∷ CU.tm-tabS ∷ CU.tm-meth
               ∷ tm-conK ∷ tm-conS ∷ tm-conAt ∷ tm-rnL ∷ tm-trav
               ∷ tm-rVF ∷ tm-rWK ∷ tm-rV0 ∷ tm-rNλ ∷ tm-rNK ∷ tm-sVF ∷ tm-sWK ∷ tm-sV0 ∷ tm-sN ∷ [])

open SigExtend Base.S Base.abody Base.wf 20 tys tms 1000 public

-- ★ the segment is well-formed: the checker's output, nothing written
wf : WfSig S
wf = fromJust wfSig _
