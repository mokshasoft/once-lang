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
--   (2026-10-06, when references still carried their bodies; 144 s /
--   4.9 GB before that; before CheckA's syntactic fast path the checker
--   ran out of memory on the 52-branch rows cascade).  PLAN-REF: to
--   re-measure.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.PwCore where
open import normalizer.Syntax.Types using ( _≡_; refl; _,_ )
open import Agda.Builtin.Nat using ( zero; suc; _-_; _+_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; vz; vs; Defs )
open import DirectedHoTT.Metatheory.Signature using ( WfSig; wf→K )
open import DirectedHoTT.Spec.Signature using ( kernel )
open import DirectedHoTT.Spec.SigWf using ( WfK )
open import DirectedHoTT.Algorithm.Surface
open import DirectedHoTT.Algorithm.SigBuild using ( module SigExtend )
import DirectedHoTT.Examples.SigMeth as Base

open import DirectedHoTT.Algorithm.Surface.Notation
open import DirectedHoTT.Examples.KnotFrame

-- this segment's entries
#PwC #PwJ #PwL #PwD #Pw : ℕ
#PwC = 42 ; #PwJ = 43 ; #PwL = 44 ; #PwD = 45 ; #Pw = 46

private
  J C : T
  J = ref #PwJ
  C = ref #PwC
  open Family J C

  -- ★ the rows: λ j p h c. (a row: its premises as one alternative)
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
    kapp kcHom : List T → T
    kapp  = knode #kapp
    kcHom = knode #kcHom

ty-PwC ty-PwJ ty-PwL ty-PwD ty-Pw : STy ε
tm-PwC tm-PwJ tm-PwL tm-PwD tm-Pw : STm ε
-- the convoy: the body, one binder deeper
ty-PwC = Π (El SI₂) U
tm-PwC = lam □ᵀ (TmC (nsuc (snd v₀)))
-- the index: (i , t , c)
ty-PwJ = ty-index
tm-PwJ = tm-index
-- ★ the rows, as the method's leaves: kcPi and kcHom, every other constructor none
ty-PwL = ty-rows
tm-PwL = tm-rows [] ((#kcPi , one cPi) ∷ (#kcHom , one cHom) ∷ [])
-- ★ the description: the fibre of the subject, the convoy applied
ty-PwD = ty-desc
tm-PwD = tm-desc #PwL
-- ⌜Pw⌝ d t u
ty-Pw = Π Nat (Π (El (TmC v₀)) (Π (El (TmC (nsuc (var (vs vz))))) U))
tm-Pw = λ⁺ 3 (⌜IMu⌝ J (ref #PwD) (pair □ᵀ □ᵀ (pair □ᵀ □ᵀ (tag 1) (L 0)) (pair □ᵀ □ᵀ (L 1) (L 2))))

tys : ℕ → STy ε
tys = at Unit (ty-PwC ∷ ty-PwJ ∷ ty-PwL ∷ ty-PwD ∷ ty-Pw ∷ [])
tms : ℕ → STm ε
tms = at unit (tm-PwC ∷ tm-PwJ ∷ tm-PwL ∷ tm-PwD ∷ tm-Pw ∷ [])

open SigExtend Base.S Base.abody Base.wf 5 tys tms 1000 public

wf : WfSig S
wf = fromJust wfSig _

-- ★ PLAN-REF: the core as a KERNEL signature — what the Knot's codes cite
--   (`Knot/PwCore` is over any signature containing it)
Kc : Defs
Kc = kernel S

wfKc : WfK Kc
wfKc = wf→K S wf
