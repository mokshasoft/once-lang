{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Views — what any derivation of a term former means,
-- in a restriction of the law's environment: its rule's clause, embedded in
-- `T∞` as a bind, its premises' environments again restrictions (`Res`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Views (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (Σ to Σ′)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; _·p_; positionGrade; mk-kind; 1≤1; 1≤ω)
open import Once.Spec.Type using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; _⟨_⟩; _*_; _+_; _⇒[_]_; Void)
open import Once.Spec.Context using (Ctx; ∅; []; _▸_; Usage; _∷_; _⊑ᵘ_; _⊑∷_; _+ᵘ_; _*ᵘ_; lookup; singleUse)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; toT∞; T∞; _≈_; _>>=∞_; return∞; bindᵍ; fmap)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Erase Σ using (toT∞-bindᵍ; toT∞-fmap; toT∞-bind)
open import Once.Metatheory.Bisim Σ using (≈-refl; ≈-sym; ≈-trans; ≈-bind; idˡ; assoc)
open import Once.Metatheory.Coherence.Relation Σ using (Related; Related-trans; Related-flip; Related-mono; ≈-Relatedˡ; ≈-Relatedʳ; bindRel)
open import Once.Metatheory.Coherence.Layer Σ using (Rel; rel; runs)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans)
open import Once.Metatheory.Coherence.Env Σ fmt S using (SlotAgree; Agree; restrict-∘)
open import Once.Metatheory.Coherence.Fundamental Σ u fmt S using (module FL)
open import Once.Metatheory.TermModel.Subst Σ S using (Thin; skip; keep; idθ; idθ-id; cid; cskip; ckeep; ren-⊢; θ*-id)
open import Once.Metatheory.TermModel.Ren Σ fmt S using (ThinAgree; module RenSem)
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-trans; ⊑ᵘ-≡)
open import Once.Metatheory.Laws.Tools Σ u fmt S

module Views {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
             {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Base δ sd σ r γ sγ public

  -- Related computations, of a type.
  _~_ : ∀ {A : Ty m} → T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ → T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ → Set
  _~_ {A} = Related (Same (A ⟨ σ ⟩))

  ~trans : ∀ {A : Ty m} {x y z : T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ} → _~_ {A} x y → _~_ {A} y z → _~_ {A} x z
  ~trans {A} = Related-trans (Same-trans (A ⟨ σ ⟩))

  -- The meaning of a derivation, embedded.
  ⟪_⟫ : ∀ {Ψa t A π} → Δ ⊩ Γ ⊢[ Ψa ] t ∷ A ! π → Env σ Γ Ψa → T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ
  ⟪_⟫ {π = π} d γa = toT∞ π (⟦ d ⟧ δ σ r γa)

  ⟪_⟫▸ : ∀ {Ψa q B t A π} → Δ ⊩ (Γ ▸ B) ⊢[ q ∷ Ψa ] t ∷ A ! π → Env σ Γ Ψa → Slot q ⟦ B ⟨ σ ⟩ ⟧ᵛ → T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ
  ⟪_⟫▸ {π = π} d γa v = toT∞ π (⟦ d ⟧ δ σ r (γa , v))

  ----------------------------------------------------------------------
  -- inl, inr
  ----------------------------------------------------------------------

  record InlView {Ψa A B B′ πs a} (ds : Δ ⊩ Γ ⊢[ Ψa ] inl B a ∷ A + B′ ! πs) (γa : Env σ Γ Ψa) : Set where
    constructor inlView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      da   : Δ ⊩ Γ ⊢[ Ψ₀ ] a ∷ A ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {A + B′} (⟪ ds ⟫ γa) (⟪ da ⟫ γ₀ >>=∞ λ x → return∞ (inj₁ x))

  viewInl : ∀ {Ψa A B B′ πs a} (ds : Δ ⊩ Γ ⊢[ Ψa ] inl B a ∷ A + B′ ! πs) {γa} → Res γa → InlView ds γa
  viewInl ds ra with peel ds | peelRel ds ra
  ... | peeled (⊢inl {π = π₀} da) P _ | p =
    inlView da (resR ra P) (≈-Relatedʳ (≈-sym (toT∞-fmap π₀ inj₁ (⟦ da ⟧ δ σ r (restrict σ P _)))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  record InrView {Ψa A A′ B πs b} (ds : Δ ⊩ Γ ⊢[ Ψa ] inr A b ∷ A′ + B ! πs) (γa : Env σ Γ Ψa) : Set where
    constructor inrView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      db   : Δ ⊩ Γ ⊢[ Ψ₀ ] b ∷ B ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {A′ + B} (⟪ ds ⟫ γa) (⟪ db ⟫ γ₀ >>=∞ λ x → return∞ (inj₂ x))

  viewInr : ∀ {Ψa A A′ B πs b} (ds : Δ ⊩ Γ ⊢[ Ψa ] inr A b ∷ A′ + B ! πs) {γa} → Res γa → InrView ds γa
  viewInr ds ra with peel ds | peelRel ds ra
  ... | peeled (⊢inr {π = π₀} db) P _ | p =
    inrView db (resR ra P) (≈-Relatedʳ (≈-sym (toT∞-fmap π₀ inj₂ (⟦ db ⟧ δ σ r (restrict σ P _)))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  ----------------------------------------------------------------------
  -- case
  ----------------------------------------------------------------------

  record CaseView {Ψa qℓ qr C π s l rr} (d : Δ ⊩ Γ ⊢[ Ψa ] case qℓ qr s l rr ∷ C ! π) (γa : Env σ Γ Ψa) : Set where
    constructor caseView
    field
      {Ψs Ψc} : Usage n
      {π₁ π₂} : Purity
      {A B}   : Ty m
      ds      : Δ ⊩ Γ ⊢[ Ψs ] s ∷ A + B ! π₁
      dl      : Δ ⊩ (Γ ▸ A) ⊢[ qℓ ∷ Ψc ] l ∷ C ! π₂
      dr      : Δ ⊩ (Γ ▸ B) ⊢[ qr ∷ Ψc ] rr ∷ C ! π₂
      {es ec} : Env σ Γ _
      rs      : Res {Ψs} es
      rc      : Res {Ψc} ec
      eq      : _~_ {C} (⟪ d ⟫ γa)
                  (⟪ ds ⟫ es >>=∞ [ (λ a → ⟪ dl ⟫▸ ec (slot qℓ a)) , (λ b → ⟪ dr ⟫▸ ec (slot qr b)) ]′)

  viewCase : ∀ {Ψa qℓ qr C π s l rr} (d : Δ ⊩ Γ ⊢[ Ψa ] case qℓ qr s l rr ∷ C ! π) {γa} → Res γa → CaseView d γa
  viewCase d ra with peel d | peelRel d ra
  ... | peeled (⊢case {Ψs = Ψs} {Ψc} {qℓ} {qr} {π₁} {π₂} ds dl dr) P _ | p =
    caseView ds dl dr (resL r₀) (resRt r₀)
      (≈-Relatedʳ (≈-trans (≈-bind (≈-refl _) λ { (inj₁ a) → ≈-refl _ ; (inj₂ b) → ≈-refl _ })
                           (≈-sym (toT∞-bindᵍ π₁ π₂ _ _)))
                  (runs p))
    where r₀ = resR ra P
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  ----------------------------------------------------------------------
  -- let
  ----------------------------------------------------------------------

  -- What a `let` at quantity `q` means: at `Zero` its right-hand side is not
  -- run; otherwise it runs, then the body with its value.
  LetSem : ∀ (q : Quantity) {Ψ₁ Ψ₂ A B π₁ π₂ e b} → T∞ ⟦ B ⟨ σ ⟩ ⟧ᵛ
         → Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁ → Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂ → Env σ Γ Ψ₂ → Set
  LetSem Zero {B = B} lhs de db eb = _~_ {B} lhs (⟪ db ⟫▸ eb tt)
  LetSem One  {Ψ₁} {B = B} lhs de db eb = Σ′ (Env σ Γ Ψ₁) λ ee → Res ee × _~_ {B} lhs (⟪ de ⟫ ee >>=∞ λ v → ⟪ db ⟫▸ eb v)
  LetSem Many {Ψ₁} {B = B} lhs de db eb = Σ′ (Env σ Γ Ψ₁) λ ee → Res ee × _~_ {B} lhs (⟪ de ⟫ ee >>=∞ λ v → ⟪ db ⟫▸ eb v)

  record LetView {Ψa q B π e b} (d : Δ ⊩ Γ ⊢[ Ψa ] let′ q e b ∷ B ! π) (γa : Env σ Γ Ψa) : Set where
    constructor letView
    field
      {Ψ₁ Ψ₂} : Usage n
      {π₁ π₂} : Purity
      {A}     : Ty m
      de      : Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁
      db      : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂
      {eb}    : Env σ Γ Ψ₂
      rb      : Res eb
      sem     : LetSem q (⟪ d ⟫ γa) de db eb

  viewLet : ∀ {Ψa q B π e b} (d : Δ ⊩ Γ ⊢[ Ψa ] let′ q e b ∷ B ! π) {γa} → Res γa → LetView d γa
  viewLet d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = Zero} {π₁} d₁ d₂) P _ | p =
    letView {π₁ = π₁} d₁ d₂ (resL (resR ra P)) (runs p)
  ... | peeled (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = One} {π₁} {π₂} d₁ d₂) P _ | p =
    letView d₁ d₂ (resL r₀) (ee , res1 (resRt r₀) ,
      ≈-Relatedʳ (≈-sym (toT∞-bindᵍ π₁ π₂ (⟦ d₁ ⟧ δ σ r ee) (λ v → ⟦ d₂ ⟧ δ σ r (envˡ σ Ψ₂ (One *ᵘ Ψ₁) γ₀ , v)))) (runs p))
    where γ₀ = restrict σ P γa
          r₀ = resR ra P
          ee = env*One σ Ψ₁ (envʳ σ Ψ₂ (One *ᵘ Ψ₁) γ₀)
  ... | peeled (⊢let {Ψ₁ = Ψ₁} {Ψ₂} {q = Many} {π₁} {π₂} d₁ d₂) P _ | p =
    letView d₁ d₂ (resL r₀) (ee , resω (resRt r₀) ,
      ≈-Relatedʳ (≈-sym (toT∞-bindᵍ π₁ π₂ (⟦ d₁ ⟧ δ σ r ee) (λ v → ⟦ d₂ ⟧ δ σ r (envˡ σ Ψ₂ (Many *ᵘ Ψ₁) γ₀ , v)))) (runs p))
    where γ₀ = restrict σ P γa
          r₀ = resR ra P
          ee = env*Many σ Ψ₁ (envʳ σ Ψ₂ (Many *ᵘ Ψ₁) γ₀)
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  ----------------------------------------------------------------------
  -- Running `e`, then `b` with its value, is what `let′ q e b` means — at
  -- `Zero` because then `e` is effect-free (`transfer`)
  ----------------------------------------------------------------------

  ~sym : ∀ {A : Ty m} {x y : T∞ ⟦ A ⟨ σ ⟩ ⟧ᵛ} → _~_ {A} x y → _~_ {A} y x
  ~sym {A} p = Related-mono (Same-sym (A ⟨ σ ⟩)) (Related-flip p)

  letEnd : ∀ q {Ψx ΨB Ψ₁ Ψ₂ A B πx πB π₁ π₂ e b} {lhs : T∞ ⟦ B ⟨ σ ⟩ ⟧ᵛ}
             (dx : Δ ⊩ Γ ⊢[ Ψx ] e ∷ A ! πx) {ex : Env σ Γ Ψx} → Res ex
         → (dB : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ ΨB ] b ∷ B ! πB) {eB : Env σ Γ ΨB} → Res eB
         → (de : Δ ⊩ Γ ⊢[ Ψ₁ ] e ∷ A ! positionGrade q π₁) (db : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂) {eb : Env σ Γ Ψ₂} → Res eb
         → LetSem q lhs de db eb
         → _~_ {B} (⟪ dx ⟫ ex >>=∞ λ x → ⟪ dB ⟫▸ eB (slot q x)) lhs
  letEnd Zero {A = A} {B} dx {ex} rx dB rB de db {eb} rb sem =
    ~trans {B} (≈-Relatedʳ (≈-sym (idˡ (⟦ px ⟧ δ σ r ex) (λ _ → ⟪ db ⟫▸ eb tt)))
                           (bindRel (runs (fl dx px rx rx)) (λ _ → runs (fl▸ dB db rB rb tt))))
               (~sym {B} sem)
    where px = transfer de dx
  letEnd One  {A = A} {B} dx rx dB rB de db rb (ee , re , eqR) =
    ~trans {B} (bindRel (runs (fl dx de rx re)) (λ sv → runs (fl▸ dB db rB rb (slotAgree σ {A} One One sv)))) (~sym {B} eqR)
  letEnd Many {A = A} {B} dx rx dB rB de db rb (ee , re , eqR) =
    ~trans {B} (bindRel (runs (fl dx de rx re)) (λ sv → runs (fl▸ dB db rB rb (slotAgree σ {A} Many Many sv)))) (~sym {B} eqR)

  ----------------------------------------------------------------------
  -- var
  ----------------------------------------------------------------------

  record VarView {Ψa i π} (dv : Δ ⊩ Γ ⊢[ Ψa ] var i ∷ lookup Γ i ! π) (γa : Env σ Γ Ψa) : Set where
    constructor varView
    field
      P  : singleUse i One ⊑ᵘ Ψa
      eq : _~_ {lookup Γ i} (⟪ dv ⟫ γa) (return∞ (lookupᵛ σ Γ i (restrict σ P γa)))

  viewVar : ∀ {Ψa i π} (dv : Δ ⊩ Γ ⊢[ Ψa ] var i ∷ lookup Γ i ! π) {γa} → Res γa → VarView dv γa
  viewVar dv ra with peel dv | peelRel dv ra
  ... | peeled (⊢var i) P _ | p = varView P (runs p)
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  -- A variable, read in a restriction of `γ`, returns `γ`'s value.
  varVal : ∀ {Ψa i π} (dv : Δ ⊩ Γ ⊢[ Ψa ] var i ∷ lookup Γ i ! π) {γa} → Res γa
         → Σ′ (singleUse i One ⊑ᵘ Ψ) λ P₀ → _~_ {lookup Γ i} (⟪ dv ⟫ γa) (return∞ (lookupᵛ σ Γ i (restrict σ P₀ γ)))
  varVal dv (res Pv refl) with viewVar dv (res Pv refl)
  ... | varView P eq = ⊑ᵘ-trans P Pv , substR (restrict-∘ σ P Pv γ) eq
    where
      substR : ∀ {x y} → x ≡ y → _~_ {lookup Γ _} (⟪ dv ⟫ _) (return∞ (lookupᵛ σ Γ _ x))
             → _~_ {lookup Γ _} (⟪ dv ⟫ _) (return∞ (lookupᵛ σ Γ _ y))
      substR refl q = q

------------------------------------------------------------------------
-- Under a binder: `var zero` returns the bound value
------------------------------------------------------------------------

readVar0 : ∀ {m} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
             {n} {Γ : Ctx m n} {A : Ty m} {Ψ₂ q π₂} {eb : Env σ Γ Ψ₂} {v : ⟦ A ⟨ σ ⟩ ⟧ᵛ}
             (se : SameEnv Σ fmt S σ (Γ ▸ A) (q ∷ Ψ₂) (eb , slot q v))
             (db : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] var zero ∷ A ! π₂)
           → Related (Same (A ⟨ σ ⟩)) (toT∞ π₂ (⟦ db ⟧ δ σ r (eb , slot q v))) (return∞ v)
readVar0 δ sd σ r {Γ = Γ} {A} {Ψ₂} {q} {eb = eb} {v} se db = go (V.viewVar db V.base)
  where
    module V = Views δ sd σ r {Γ = Γ ▸ A} {Ψ = q ∷ Ψ₂} (eb , slot q v) se
    go : V.VarView db (eb , slot q v) → Related (Same (A ⟨ σ ⟩)) (V.⟪ db ⟫ (eb , slot q v)) (return∞ v)
    go (V.varView (1≤1 ⊑∷ _) eq) = eq
    go (V.varView (1≤ω ⊑∷ _) eq) = eq

module AbsurdV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
               {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ

  record AbsurdView {Ψa A π e} (d : Δ ⊩ Γ ⊢[ Ψa ] absurd A e ∷ A ! π) (γa : Env σ Γ Ψa) : Set where
    constructor absurdView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      de   : Δ ⊩ Γ ⊢[ Ψ₀ ] e ∷ Void ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {A} (⟪ d ⟫ γa) (⟪ de ⟫ γ₀ >>=∞ λ ())

  viewAbsurd : ∀ {Ψa A π e} (d : Δ ⊩ Γ ⊢[ Ψa ] absurd A e ∷ A ! π) {γa} → Res γa → AbsurdView d γa
  viewAbsurd {A = A} d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢absurd {π = π₀} de) P _ | p =
    absurdView de (resR ra P)
      (≈-Relatedʳ (≈-trans (≈-bind (≈-refl _) λ ()) (≈-sym (toT∞-bind π₀ (⟦ de ⟧ δ σ r (restrict σ P γa)) ⊥-elim))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

module ProdV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
             {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ

  record PairView {Ψa A B π a b} (d : Δ ⊩ Γ ⊢[ Ψa ] pair a b ∷ A * B ! π) (γa : Env σ Γ Ψa) : Set where
    constructor pairView
    field
      {Ψ₁ Ψ₂} : Usage n
      {π₁ π₂} : Purity
      da      : Δ ⊩ Γ ⊢[ Ψ₁ ] a ∷ A ! π₁
      db      : Δ ⊩ Γ ⊢[ Ψ₂ ] b ∷ B ! π₂
      {ea}    : Env σ Γ Ψ₁
      {eb}    : Env σ Γ Ψ₂
      ra      : Res ea
      rb      : Res eb
      eq      : _~_ {A * B} (⟪ d ⟫ γa) (⟪ da ⟫ ea >>=∞ λ x → ⟪ db ⟫ eb >>=∞ λ y → return∞ (x , y))

  viewPair : ∀ {Ψa A B π a b} (d : Δ ⊩ Γ ⊢[ Ψa ] pair a b ∷ A * B ! π) {γa} → Res γa → PairView d γa
  viewPair d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢pair {Ψ₁ = Ψ₁} {Ψ₂} {π₁} {π₂} da db) P _ | p =
    pairView da db (resL r₀) (resRt r₀)
      (≈-Relatedʳ (≈-trans (≈-bind (≈-refl _) (λ x → ≈-sym (toT∞-fmap π₂ (λ y → x , y) (⟦ db ⟧ δ σ r eb))))
                           (≈-sym (toT∞-bindᵍ π₁ π₂ (⟦ da ⟧ δ σ r ea) (λ x → fmap π₂ (λ y → x , y) (⟦ db ⟧ δ σ r eb)))))
                  (runs p))
    where r₀ = resR ra P
          ea = envˡ σ Ψ₁ Ψ₂ (restrict σ P γa)
          eb = envʳ σ Ψ₁ Ψ₂ (restrict σ P γa)
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  record FstView {Ψa A π p} (d : Δ ⊩ Γ ⊢[ Ψa ] fst p ∷ A ! π) (γa : Env σ Γ Ψa) : Set where
    constructor fstView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      {B}  : Ty m
      dp   : Δ ⊩ Γ ⊢[ Ψ₀ ] p ∷ A * B ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {A} (⟪ d ⟫ γa) (⟪ dp ⟫ γ₀ >>=∞ λ v → return∞ (proj₁ v))

  viewFst : ∀ {Ψa A π p} (d : Δ ⊩ Γ ⊢[ Ψa ] fst p ∷ A ! π) {γa} → Res γa → FstView d γa
  viewFst d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢fst {π = π₀} dp) P _ | p =
    fstView dp (resR ra P) (≈-Relatedʳ (≈-sym (toT∞-fmap π₀ proj₁ (⟦ dp ⟧ δ σ r (restrict σ P γa)))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  record SndView {Ψa B π p} (d : Δ ⊩ Γ ⊢[ Ψa ] snd p ∷ B ! π) (γa : Env σ Γ Ψa) : Set where
    constructor sndView
    field
      {Ψ₀} : Usage n
      {π₀} : Purity
      {A}  : Ty m
      dp   : Δ ⊩ Γ ⊢[ Ψ₀ ] p ∷ A * B ! π₀
      {γ₀} : Env σ Γ Ψ₀
      r₀   : Res γ₀
      eq   : _~_ {B} (⟪ d ⟫ γa) (⟪ dp ⟫ γ₀ >>=∞ λ v → return∞ (proj₂ v))

  viewSnd : ∀ {Ψa B π p} (d : Δ ⊩ Γ ⊢[ Ψa ] snd p ∷ B ! π) {γa} → Res γa → SndView d γa
  viewSnd d {γa} ra with peel d | peelRel d ra
  ... | peeled (⊢snd {π = π₀} dp) P _ | p =
    sndView dp (resR ra P) (≈-Relatedʳ (≈-sym (toT∞-fmap π₀ proj₂ (⟦ dp ⟧ δ σ r (restrict σ P γa)))) (runs p))
  ... | peeled (⊢sub-use _ _) _ () | _
  ... | peeled (⊢sub-eff _ _) _ () | _

  -- An effect-free derivation returns: related to `return∞` of its value.
  pureRet : ∀ {Ψa Ψp t A π} (d : Δ ⊩ Γ ⊢[ Ψa ] t ∷ A ! π) (dp : Δ ⊩ Γ ⊢[ Ψp ] t ∷ A ! pure) {γa} (ra : Res γa)
          → _~_ {A} (⟪ d ⟫ γa) (return∞ (⟦ transfer dp d ⟧ δ σ r γa))
  pureRet d dp ra = runs (fl d (transfer dp d) ra ra)

------------------------------------------------------------------------
-- Weakening: `wk u` under a binder means what `u` means
------------------------------------------------------------------------

agree→thin : ∀ {m} (σ : TySub m 0) {n} (Γ : Ctx m n) {Ψ′ Ψ : Usage n} {γ′ : Env σ Γ Ψ′} {γ : Env σ Γ Ψ}
           → Agree σ Γ Ψ′ Ψ γ′ γ → ThinAgree σ (cid Γ) Ψ′ Ψ γ′ γ
agree→thin σ ∅       {[]}     {[]}     a        = tt
agree→thin σ (Γ ▸ A) {_ ∷ _}  {_ ∷ _}  (a , sv) = agree→thin σ Γ a , sv

module WkV {m : ℕ} {Δ : KCtx m} (δ : DefSem) (sd : SameDefs Σ fmt S δ) (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
           {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ) (sγ : SameEnv Σ fmt S σ Γ Ψ γ) where
  open Views δ sd σ r γ sγ

  wkRel : ∀ {A B q Ψ₂ Ψa π₂ πa t} (db : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψ₂ ] wk t ∷ B ! π₂) {eb : Env σ Γ Ψ₂} → Res eb
        → (v : Slot q ⟦ A ⟨ σ ⟩ ⟧ᵛ) (du : Δ ⊩ Γ ⊢[ Ψa ] t ∷ B ! πa) {γa : Env σ Γ Ψa} → Res γa
        → _~_ {B} (⟪ db ⟫▸ eb v) (⟪ du ⟫ γa)
  wkRel {A} {B} {q} {Ψa = Ψa} db {eb} rb v du {γa} ra =
    ~trans {B} (runs (FL.FL δ sd σ r r db D refl (agree rb rc , slotZ q v)))
               (runs (RenSem.renSem δ sd σ r (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip (cid Γ)) du
                        {γ′ = γc , tt} {γ = γa} (agree→thin σ Γ (agree rc ra))))
    where
      D = ren-⊢ (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip {A = A} (cid Γ)) du
      W = ⊑ᵘ-≡ (θ*-id Ψa)
      γc = restrict σ W γa
      rc : Res γc
      rc = resR ra W
      slotZ : ∀ q (v : Slot q ⟦ A ⟨ σ ⟩ ⟧ᵛ) → SlotAgree σ A q Zero v tt
      slotZ Zero v = tt
      slotZ One  v = tt
      slotZ Many v = tt
