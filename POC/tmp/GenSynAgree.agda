-- SPIKE: the Knot link (SPIKE-GENERIC-SYNTAX S5, part 2): RENAMING AGREES,
-- generic in the signature.
--
-- `Knot/RenAgree` (generated) proves, one case per former of `Spec/Syntax`,
-- that the Knot's renaming traversal at a quoted term reduces to the
-- quotation of the renamed term. Each case is the same: `trav-con` at the
-- node, then one `fld-rec` per field. Here it is ONE induction over the
-- generic syntax's arguments, for every signature. A signature supplies its
-- object signature and a POSITION TABLE (`nG`, `nSh`, `nV`: where each sort,
-- constructor and the variable sit, `atᵍ`/`atʰ` per former).
--
-- The quotation is the one of `tmp.GenSynQuote`, rebuilt here over the
-- Lib's own `tag`/`conₗ`/`num` instances so that it meets `trav-con`'s
-- `conₗ` definitionally (those are signature-free but live in
-- parameterised modules: the move of signature-free data to a
-- non-parameterised module is the switch's job).

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.Base hiding ( _,,_; _×_ )
module tmp.GenSynAgree (𝒮 : Defs) (wf : WfK 𝒮) where
open import DirectedHoTT.Prelude using ( _≡_; refl; cong; trans; sym )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Scope
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮)
open import DirectedHoTT.Metatheory.RedCong 𝒮 using ( ⟶*-trans; ⟶*-appʳ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-con; ⟶*-fsuc )
open import DirectedHoTT.Lib.Syn 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.SynTrav 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( module Trav; Kit; module Kit )
open import DirectedHoTT.Lib.SynTravRed 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.SynTravM 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( VarsAt )
open import DirectedHoTT.Lib.SynRen 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf)
open import DirectedHoTT.Lib.Sugar 𝒮 (Defs.size 𝒮) (Entries.okᵂ 𝒮 wf) using ( tag; conₗ; tag-sub )
open import DirectedHoTT.Lib.NatNum 𝒮 (Defs.size 𝒮) using ( num )
import tmp.GenSyn as G
open import tmp.GenSynQuote using ( toℕ )

private
  subst₂ : {A B : Set} (P : A → B → Set) {a a′ : A} {b b′ : B} → a ≡ a′ → b ≡ b′ → P a b → P a′ b′
  subst₂ P refl refl x = x

-- the depth of a scope, as an object numeral
dep : Cx → {Θ : Cx} → RTm Θ
dep ε     = nzero
dep (Γ ∙) = nsuc (dep Γ)

dep-⋯ : (Γ : Cx) (k : ℕ) {Θ : Cx} → dep (Γ G.⋯ k) {Θ} ≡ nsucs k (dep Γ)
dep-⋯ Γ zero    = refl
dep-⋯ Γ (suc k) = cong nsuc (dep-⋯ Γ k)

module Agree (Σ : G.Sig) (sIx : G.Sort Σ → ℕ) where

  -- a field list's object shape
  toShape : List (G.Field (G.Sort Σ)) → Shape
  toShape []             = []ʰ
  toShape (G.rec s k ∷ fs) = rec (sIx s) k ∷ʰ toShape fs
  toShape (G.nat ∷ fs)   = nat ∷ʰ toShape fs

  -- what a signature supplies: its object signature and a position table
  record ObjSig : Set where
    field
      ix   : ∀ {s} → G.Con Σ s → ℕ
      vix  : ℕ
      nS   : ℕ
      osg  : Sig nS
      ok   : SigOK nS osg
      cnum : G.Sort Σ → ℕ
      shs  : (s : G.Sort Σ) → Shapes (cnum s)
      nG   : (s : G.Sort Σ) → NthG osg (sIx s) (shs s)
      nSh  : ∀ {s} (c : G.Con Σ s) → NthSh (shs s) (ix c) (toShape (G.fields Σ c))
      nV   : NthSh (shs (G.vsort Σ)) vix vʰ
      vok  : VarsAt osg (sIx (G.vsort Σ))

  module _ (O : ObjSig) where
    open ObjSig O
    open Ren ok {v = sIx (G.vsort Σ)} {kv = vix} (nG (G.vsort Σ)) nV vok

    -- the quotation, over the Lib's encoding pieces
    ⌜_⌝  : ∀ {s Γ} → G.Tm Σ s Γ → {Θ : Cx} → RTm Θ
    ⌜_⌝ᵃ : ∀ {fs Γ} → G.Args Σ Γ fs → {Θ : Cx} → RTm Θ
    ⌜ G.var x ⌝      = conₗ vix (pair (tag (toℕ x)) unit)
    ⌜ G.con c as ⌝   = conₗ (ix c) ⌜ as ⌝ᵃ
    ⌜ G.[] ⌝ᵃ        = unit
    ⌜ t G.∷ʳ as ⌝ᵃ   = pair ⌜ t ⌝ ⌜ as ⌝ᵃ
    ⌜ n G.∷ⁿ as ⌝ᵃ   = pair (num n) ⌜ as ⌝ᵃ

    module Agreeing
      (LIFT-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (Trav.LIFT ok renKit {Δ}) ≡ Trav.LIFT ok renKit)
      (NODE-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (Kit.NODE renKit {Δ}) ≡ Kit.NODE renKit)
      (V0-sub   : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (Kit.V0 renKit {Δ}) ≡ Kit.V0 renKit)
      (WK-sub   : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (Kit.WK renKit {Δ}) ≡ Kit.WK renKit)
      where
      module TR = TravRed ok renKit vok LIFT-sub NODE-sub
      module ER = EnvRed ok renKit V0-sub WK-sub
      open Trav ok renKit using ( LIFTS )
      open G.Trav Σ using ( renK; travA; extN ) renaming ( ren to renᵍ )

      ≡⟶* : ∀ {Γ} {a a′ b : RTm Γ} → a ≡ a′ → a′ ⟶* b → a ⟶* b
      ≡⟶* refl r = r

      fieldsOf : (fs : List (G.Field (G.Sort Σ))) → TR.Fields (toShape fs)
      fieldsOf []              = TR.f-nil
      fieldsOf (G.rec s k ∷ fs) = TR.f-cons
      fieldsOf (G.nat ∷ fs)    = TR.f-cons

      ------------------------------------------------------------------
      -- an environment REPRESENTS a renaming (as in `Knot/RenAgree`)
      ------------------------------------------------------------------

      RepR : ∀ {Γ Δ Θ} → (Var Γ → Var Δ) → RTm Θ → Set
      RepR {Γ} ρ f = (x : Var Γ) → app f (tag (toℕ x)) ⟶* tag (toℕ (ρ x))

      repR-lift : ∀ {Γ Δ Θ} {ρ : Var Γ → Var Δ} {f : RTm Θ} → RepR ρ f
                → RepR (G.Trav.ext Σ renK ρ) (ER.LIFT· (dep Δ) (dep Γ) f)
      repR-lift {Δ = Δ} r vz     = ⟶*-trans ER.lift-z (step (β fzero (dep Δ)) done)
      repR-lift         r (vs x) = ⟶*-trans ER.lift-s (step (ξ-appˡ (β _ _)) (step (β _ _) (⟶*-fsuc (r x))))

      liftsR : ∀ {Γ Δ Θ} (k : ℕ) {ρ : Var Γ → Var Δ} {f : RTm Θ} → RepR ρ f
             → RepR (extN renK k ρ) (LIFTS k (dep Δ) (dep Γ) f)
      liftsR zero    r = r
      liftsR {Γ} {Δ} (suc k) {ρ} {f} r =
        subst₂ (λ e d → RepR (extN renK (suc k) ρ) (ER.LIFT· e d (LIFTS k (dep Δ) (dep Γ) f)))
               (dep-⋯ Δ k) (dep-⋯ Γ k) (repR-lift (liftsR k r))

      ------------------------------------------------------------------
      -- ★★★ RENAMING AGREES: one induction, for every signature
      ------------------------------------------------------------------

      agree  : ∀ {s Γ Δ Θ} (t : G.Tm Σ s Γ) {ρ : Var Γ → Var Δ} {f : RTm Θ} → RepR ρ f
             → trav (sIx s) (dep Γ) ⌜ t ⌝ (dep Δ) f ⟶* ⌜ renᵍ ρ t ⌝
      agreeA : ∀ {fs Γ Δ Θ} (as : G.Args Σ Γ fs) {ρ : Var Γ → Var Δ} {f : RTm Θ} → RepR ρ f
             → TR.tpayT (toShape fs) ⌜ as ⌝ᵃ (dep Δ) f (dep Γ) ⟶* ⌜ travA renK ρ as ⌝ᵃ

      -- the variable: the kit's NODE builds `conₗ vix …`; at an ABSTRACT tag the
      -- substitutions β leaves on it are closed only propositionally (`tag-sub`)
      agree {Δ = Δ} (G.var x) {f = f} r =
        ⟶*-trans (TR.trav-var (nG (G.vsort Σ)) nV)
          (step (ξ-appˡ (β _ _)) (step (β _ _)
            (≡⟶* (cong (λ X → con (pair X (pair v unit))) EQ)
              (⟶*-con (⟶*-pairʳ (⟶*-pairˡ (⟶*-trans (⟶*-appʳ (step (βfst _ _) done)) (r x))))))))
        where
        v  = app f (fst (pair (tag (toℕ x)) unit))
        EQ = trans (cong (subTm (single v)) (tag-sub (extS (single (dep Δ))) vix)) (tag-sub (single v) vix)
      agree (G.con c as) r =
        ⟶*-trans (TR.trav-con (nG _) (nSh c) (fieldsOf (G.fields Σ c))) (⟶*-con (⟶*-pairʳ (agreeA as r)))

      agreeA G.[] r = done
      agreeA {Γ = Γ} {Δ} (G._∷ʳ_ {s = s} {k = k} t as) {ρ} {f} r =
        TR.fld-rec (subst₂ (λ d e → trav (sIx s) d ⌜ t ⌝ e (LIFTS k (dep Δ) (dep Γ) f) ⟶* ⌜ renᵍ (extN renK k ρ) t ⌝)
                           (dep-⋯ Γ k) (dep-⋯ Δ k) (agree t (liftsR k r)))
                   (agreeA as r)
      agreeA (n G.∷ⁿ as) r = TR.fld-nat (agreeA as r)
