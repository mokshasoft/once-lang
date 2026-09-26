-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.LetIsDef
--
-- Plan 0.94 D1 (§0, §4c): a `let` may become a top-level definition.
--
--     (Γ , x ∶ A) ⊢ b ∶ B ⨾ (q ∷ Ψ)     ⟹     Γ ⟨x ≝ e⟩ ⊢ b ∶ B ⨾ Ψ
--
-- `b` is the SAME term on both sides; only where `x` lives changes. On the
-- left `x` is a local (`t-var-local`, one use); on the right it is a top-level
-- definition whose body `e` is re-checked at each use
-- (`t-var-poly-instantiate-infer`, no local use). That is why the tail `Ψ` is
-- the same on both sides: the let's slot is simply DROPPED.
--
-- Premises, each one a condition a top-level definition needs anyway:
--   * `e` types in the context a top-level body sees — imports and definitions,
--     no locals. (Zero usage in Γ would NOT do: a local may occur inside an
--     erased argument, and such an `e` cannot leave Γ.)
--   * `x` is not already a local, an import or a definition, so it names the
--     new definition everywhere — including inside `cata`/`ana` algebras, which
--     are typed without locals and so see the definition but never the let.
--   * `A` is stated by a ground signature `s` (`extractGround s g ≡ A`) — the
--     signature the definition is written with.
--
-- The converse (def ⇒ let) is FALSE while algebras cannot capture locals
-- (`cata (\l -> x)` sees a definition `x` but not a let-bound one); that is
-- plan 0.101's, not a gap in this proof.
--
-- The proof is one mutual induction over the three judgments, carrying a
-- relation `LD` between the let-side and def-side contexts: the let slot
-- (`ld-let`), the new definition alone (`ld-top`, for an algebra's cleared
-- context) and any binders under either (`ld-under`).
------------------------------------------------------------------------
module Once.TypeCheck.LetIsDef where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃-syntax; _,_)
open import Data.String using (String)
open import Data.String.Properties as StrProp using ()
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Once.Type as T using (Type; PolyType; Ground; extractGround; Quantity)
open import Once.TypeCheck.Raw using (RawExpr; RVar)
open import Once.TypeCheck.Classify
  using (NamedCtx; mkCtx; Imports; PolyCtx; lookupLocal; lookupLocal-go; lookupImport;
         lookupPoly; lookupPolyPrefix; lookupPolyPrefix⇒lookupPoly; ctxWithImportsAndPolys;
         extendNamedCtx)
open import Once.TypeCheck.Context using (Ctx)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.TypeCheck.Judgment
open import Once.Surface.Context as SC using (Usage; SVar; zeroUsage; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)
open SC.Usage using () renaming (_∷_ to _∷ᵘ_)

-- A top-level definition, added to a context.
defineNamedCtx : NamedCtx → String → PolyType → RawExpr → NamedCtx
defineNamedCtx Γ x s e =
  mkCtx (NamedCtx.size Γ) (NamedCtx.named Γ) (NamedCtx.debruijn Γ) (NamedCtx.freshCounter Γ)
        (NamedCtx.imports Γ) ((x , s , e) List.∷ NamedCtx.polys Γ)
  where import Data.List as List

module Transfer
  (x : String) (A : Type) (e : RawExpr) (s : PolyType) (g : Ground s)
  (eqA : extractGround s g ≡ A)
  (imps : Imports) (P : PolyCtx)
  (noImp : lookupImport imps x ≡ nothing)
  (noPoly : lookupPoly P x ≡ nothing)
  (eD : ctxWithImportsAndPolys imps P ⊢ᶜ e ∶ A ⨾ zeroUsage)
  where

  open import Data.List using (List; _∷_)

  P′ : PolyCtx
  P′ = (x , s , e) ∷ P

  -- The let-side and def-side local contexts.
  data LD : ∀ {nL nD} → Ctx → SC.Ctx nL → Ctx → SC.Ctx nD → Set where
    ld-let   : ∀ {n} {G : Ctx} {Δ : SC.Ctx n}
             → lookupLocal-go x G Δ ≡ nothing
             → LD (extendCtx G x A) (Δ SC., A) G Δ
    ld-top   : ∀ {n} {G : Ctx} {Δ : SC.Ctx n} → LD G Δ G Δ
    ld-under : ∀ {nL nD} {GL : Ctx} {ΔL : SC.Ctx nL} {GD : Ctx} {ΔD : SC.Ctx nD}
               (y : String) (B : Type)
             → LD GL ΔL GD ΔD
             → LD (extendCtx GL y B) (ΔL SC., B) (extendCtx GD y B) (ΔD SC., B)

  -- The let's slot, dropped.
  drop : ∀ {nL nD GL ΔL GD ΔD} → LD {nL} {nD} GL ΔL GD ΔD → Usage nL → Usage nD
  drop (ld-let _) (q ∷ᵘ U) = U
  drop ld-top U = U
  drop (ld-under _ _ ld) (q ∷ᵘ U) = q ∷ᵘ drop ld U

  drop-zero : ∀ {nL nD GL ΔL GD ΔD} (ld : LD {nL} {nD} GL ΔL GD ΔD) → drop ld zeroUsage ≡ zeroUsage
  drop-zero (ld-let _) = refl
  drop-zero ld-top = refl
  drop-zero (ld-under _ _ ld) = cong (T.Zero ∷ᵘ_) (drop-zero ld)

  drop-+ : ∀ {nL nD GL ΔL GD ΔD} (ld : LD {nL} {nD} GL ΔL GD ΔD) (U₁ U₂ : Usage nL)
         → drop ld (U₁ +ᵘ U₂) ≡ drop ld U₁ +ᵘ drop ld U₂
  drop-+ (ld-let _) (_ ∷ᵘ _) (_ ∷ᵘ _) = refl
  drop-+ ld-top _ _ = refl
  drop-+ (ld-under _ _ ld) (q₁ ∷ᵘ U₁) (q₂ ∷ᵘ U₂) = cong (_ ∷ᵘ_) (drop-+ ld U₁ U₂)

  drop-* : ∀ {nL nD GL ΔL GD ΔD} (ld : LD {nL} {nD} GL ΔL GD ΔD) (q : Quantity) (U : Usage nL)
         → drop ld (q *ᵘ U) ≡ q *ᵘ drop ld U
  drop-* (ld-let _) q (_ ∷ᵘ _) = refl
  drop-* ld-top q _ = refl
  drop-* (ld-under _ _ ld) q (_ ∷ᵘ U) = cong (_ ∷ᵘ_) (drop-* ld q U)

  drop-⊔ : ∀ {nL nD GL ΔL GD ΔD} (ld : LD {nL} {nD} GL ΔL GD ΔD) (U₁ U₂ : Usage nL)
         → drop ld (U₁ ⊔ᵘ U₂) ≡ drop ld U₁ ⊔ᵘ drop ld U₂
  drop-⊔ (ld-let _) (_ ∷ᵘ _) (_ ∷ᵘ _) = refl
  drop-⊔ ld-top _ _ = refl
  drop-⊔ (ld-under _ _ ld) (q₁ ∷ᵘ U₁) (q₂ ∷ᵘ U₂) = cong (_ ∷ᵘ_) (drop-⊔ ld U₁ U₂)

  -- The usage shapes the rules conclude with.
  drop-z+M : ∀ {nL nD GL ΔL GD ΔD} (ld : LD {nL} {nD} GL ΔL GD ΔD) (U : Usage nL)
           → drop ld (zeroUsage +ᵘ (T.Many *ᵘ U)) ≡ zeroUsage +ᵘ (T.Many *ᵘ drop ld U)
  drop-z+M ld U = trans (drop-+ ld _ _) (cong₂ _+ᵘ_ (drop-zero ld) (drop-* ld T.Many U))

  drop-+* : ∀ {nL nD GL ΔL GD ΔD} (ld : LD {nL} {nD} GL ΔL GD ΔD) (U₁ : Usage nL) (q : Quantity) (U₂ : Usage nL)
          → drop ld (U₁ +ᵘ (q *ᵘ U₂)) ≡ drop ld U₁ +ᵘ (q *ᵘ drop ld U₂)
  drop-+* ld U₁ q U₂ = trans (drop-+ ld _ _) (cong (drop ld U₁ +ᵘ_) (drop-* ld q U₂))

  drop-+⊔ : ∀ {nL nD GL ΔL GD ΔD} (ld : LD {nL} {nD} GL ΔL GD ΔD) (U₀ U₁ U₂ : Usage nL)
          → drop ld (U₀ +ᵘ (U₁ ⊔ᵘ U₂)) ≡ drop ld U₀ +ᵘ (drop ld U₁ ⊔ᵘ drop ld U₂)
  drop-+⊔ ld U₀ U₁ U₂ = trans (drop-+ ld _ _) (cong (drop ld U₀ +ᵘ_) (drop-⊔ ld U₁ U₂))

  ----------------------------------------------------------------------
  -- Local lookup across the relation.
  data LocRel {nL nD GL ΔL GD ΔD} (ld : LD {nL} {nD} GL ΔL GD ΔD) (y : String)
       : Maybe (∃[ T ] ∃[ U ] SVar ΔL U T) → Maybe (∃[ T ] ∃[ U ] SVar ΔD U T) → Set where
    lr-none : LocRel ld y nothing nothing
    lr-both : ∀ {T U eV T′ U′ eV′} → T′ ≡ T → U′ ≡ drop ld U
            → LocRel ld y (just (T , U , eV)) (just (T′ , U′ , eV′))
    lr-let  : ∀ {T U eV} → y ≡ x → T ≡ A → drop ld U ≡ zeroUsage
            → LocRel ld y (just (T , U , eV)) nothing

  mk-let : ∀ {nL nD GL ΔL GD ΔD} {ld : LD {nL} {nD} GL ΔL GD ΔD} {y : String} {T U eV r}
         → r ≡ nothing → y ≡ x → T ≡ A → drop ld U ≡ zeroUsage
         → LocRel ld y (just (T , U , eV)) r
  mk-let refl a b c = lr-let a b c

  loc-tr : ∀ {nL nD GL ΔL GD ΔD} (ld : LD {nL} {nD} GL ΔL GD ΔD) (y : String)
         → LocRel ld y (lookupLocal-go y GL ΔL) (lookupLocal-go y GD ΔD)
  loc-tr (ld-top {G = G} {Δ = Δ}) y with lookupLocal-go y G Δ
  ... | nothing = lr-none
  ... | just _  = lr-both refl refl
  loc-tr (ld-let {G = G} {Δ = Δ} nx) y with y StrProp.≟ x
  ... | yes y≡x = mk-let (trans (cong (λ z → lookupLocal-go z G Δ) y≡x) nx) y≡x refl refl
  ... | no _ with lookupLocal-go y G Δ
  ...   | nothing = lr-none
  ...   | just (_ , _ , SC.svar i) = lr-both refl refl
  loc-tr (ld-under {GL = GL} {ΔL = ΔL} {GD = GD} {ΔD = ΔD} y′ B ld) y with y StrProp.≟ y′
  ... | yes _ = lr-both refl (cong (T.One ∷ᵘ_) (sym (drop-zero ld)))
  ... | no _ with lookupLocal-go y GL ΔL | lookupLocal-go y GD ΔD | loc-tr ld y
  ...   | nothing | nothing | lr-none = lr-none
  ...   | nothing | just _ | ()
  ...   | just (_ , _ , SC.svar i) | just (_ , _ , SC.svar j) | lr-both eT eU =
            lr-both eT (cong (T.Zero ∷ᵘ_) eU)
  ...   | just (_ , _ , SC.svar i) | nothing | lr-let a b c = lr-let a b (cong (T.Zero ∷ᵘ_) c)

  none-tr : ∀ {nL nD GL ΔL GD ΔD} {ld : LD {nL} {nD} GL ΔL GD ΔD} {y : String} {r₁ r₂}
          → LocRel ld y r₁ r₂ → r₁ ≡ nothing → r₂ ≡ nothing
  none-tr lr-none _ = refl
  none-tr (lr-both _ _) ()
  none-tr (lr-let _ _ _) ()

  -- The new definition is at the head of the definitions; every other name
  -- finds what it found before.
  lpp-head : lookupPolyPrefix P′ x ≡ just (s , e , P)
  lpp-head with x StrProp.≟ x
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  lpp-tr : ∀ (y : String) {s′ b pre} → lookupPolyPrefix P y ≡ just (s′ , b , pre)
         → lookupPolyPrefix P′ y ≡ just (s′ , b , pre)
  lpp-tr y lp with x StrProp.≟ y
  ... | no _ = lp
  ... | yes refl with trans (sym (lookupPolyPrefix⇒lookupPoly P x lp)) noPoly
  ...   | ()

  ----------------------------------------------------------------------
  -- The transfer.
  Lc : ∀ {n} → Ctx → SC.Ctx n → ℕ → NamedCtx
  Lc {n} G Δ fr = mkCtx n G Δ fr imps P
  Dc : ∀ {n} → Ctx → SC.Ctx n → ℕ → NamedCtx
  Dc {n} G Δ fr = mkCtx n G Δ fr imps P′

  var-tr : ∀ {nL nD GL ΔL GD ΔD fr} (ld : LD {nL} {nD} GL ΔL GD ΔD) (y : String) {T U eV} r₁ r₂
         → LocRel ld y r₁ r₂ → r₁ ≡ just (T , U , eV) → lookupLocal-go y GD ΔD ≡ r₂
         → Dc GD ΔD fr ⊢ᵢ RVar y ∶ T ⨾ drop ld U
  var-tr ld y _ _ lr-none () _
  var-tr ld y _ _ (lr-both eT eU) refl q = subst₂ (λ T U → _ ⊢ᵢ RVar y ∶ T ⨾ U) eT eU (t-var-local q)
  var-tr ld y _ _ (lr-let refl refl dz) refl q =
    subst (λ U → _ ⊢ᵢ RVar x ∶ A ⨾ U) (sym dz)
      (t-var-poly-instantiate-infer {g = g} q noImp lpp-head g (sym eqA) eD)

  cᵢ : ∀ {ctx b T U U′} → U ≡ U′ → ctx ⊢ᵢ b ∶ T ⨾ U → ctx ⊢ᵢ b ∶ T ⨾ U′
  cᵢ refl d = d
  cᶜ : ∀ {ctx b T U U′} → U ≡ U′ → ctx ⊢ᶜ b ∶ T ⨾ U → ctx ⊢ᶜ b ∶ T ⨾ U′
  cᶜ refl d = d
  cᵈ : ∀ {ctx b A′ π B U U′} → U ≡ U′ → ctx ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ U → ctx ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ U′
  cᵈ refl d = d

  mutual
    tr-i : ∀ {nL nD GL ΔL GD ΔD fr} (ld : LD {nL} {nD} GL ΔL GD ΔD) {b T U}
         → Lc GL ΔL fr ⊢ᵢ b ∶ T ⨾ U → Dc GD ΔD fr ⊢ᵢ b ∶ T ⨾ drop ld U
    tr-c : ∀ {nL nD GL ΔL GD ΔD fr} (ld : LD {nL} {nD} GL ΔL GD ΔD) {b T U}
         → Lc GL ΔL fr ⊢ᶜ b ∶ T ⨾ U → Dc GD ΔD fr ⊢ᶜ b ∶ T ⨾ drop ld U
    tr-d : ∀ {nL nD GL ΔL GD ΔD fr} (ld : LD {nL} {nD} GL ΔL GD ΔD) {b A′ π B U}
         → Lc GL ΔL fr ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ U → Dc GD ΔD fr ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ drop ld U

    tr-i ld (t-int n) = cᵢ (sym (drop-zero ld)) (t-int n)
    tr-i ld (t-float i f l p) = cᵢ (sym (drop-zero ld)) (t-float i f l p)
    tr-i ld (t-str t) = cᵢ (sym (drop-zero ld)) (t-str t)
    tr-i ld t-unit = cᵢ (sym (drop-zero ld)) t-unit
    tr-i ld t-unit-var = cᵢ (sym (drop-zero ld)) t-unit-var
    tr-i {GL = GL} {ΔL = ΔL} {GD = GD} {ΔD = ΔD} ld (t-var-local {x = y} eq) =
        var-tr ld y (lookupLocal-go y GL ΔL) (lookupLocal-go y GD ΔD) (loc-tr ld y) eq refl
    tr-i ld (t-var-qualified l c) = cᵢ (sym (drop-zero ld)) (t-var-qualified l c)
    tr-i ld (t-var-resolved ng l c) = cᵢ (sym (drop-zero ld)) (t-var-resolved ng l c)
    tr-i ld (t-var-import {x = y} ¬gw ln li c) = cᵢ (sym (drop-zero ld)) (t-var-import ¬gw (none-tr (loc-tr ld y) ln) li c)
    tr-i ld (t-var-poly-instantiate-infer {x = y} ln li lp gr eT body) =
        cᵢ (sym (drop-zero ld)) (t-var-poly-instantiate-infer (none-tr (loc-tr ld y) ln) li (lpp-tr y lp) gr eT body)
    tr-i ld (t-annot c) = t-annot (tr-c ld c)
    tr-i ld (t-pair d₁ d₂) = cᵢ (sym (drop-+ ld _ _)) (t-pair (tr-i ld d₁) (tr-i ld d₂))
    tr-i ld (t-neg d) = t-neg (tr-i ld d)
    tr-i ld (t-neg-float i f l p) = cᵢ (sym (drop-zero ld)) (t-neg-float i f l p)
    tr-i ld (t-let {x = y} {A = B} d₁ d₂) =
        cᵢ (sym (drop-+* ld _ _ _)) (t-let (tr-i ld d₁) (tr-i (ld-under y B ld) d₂))
    tr-i ld (t-case {xL = xL} {xR = xR} {A = AL} {B = AR} dS dL dR) =
        cᵢ (sym (drop-+⊔ ld _ _ _)) (t-case (tr-i ld dS) (tr-i (ld-under xL AL ld) dL) (tr-i (ld-under xR AR ld) dR))
    tr-i ld (t-binop-arith o d₁ d₂) = cᵢ (sym (drop-+ ld _ _)) (t-binop-arith o (tr-i ld d₁) (tr-i ld d₂))
    tr-i ld (t-binop-arith-float o d₁ d₂) = cᵢ (sym (drop-+ ld _ _)) (t-binop-arith-float o (tr-i ld d₁) (tr-i ld d₂))
    tr-i ld (t-binop-arith-float-il o d₁ d₂) = cᵢ (sym (drop-+ ld _ _)) (t-binop-arith-float-il o (tr-i ld d₁) (tr-i ld d₂))
    tr-i ld (t-binop-arith-float-ir o d₁ d₂) = cᵢ (sym (drop-+ ld _ _)) (t-binop-arith-float-ir o (tr-i ld d₁) (tr-i ld d₂))
    tr-i ld (t-binop-cmp o d₁ d₂) = cᵢ (sym (drop-+ ld _ _)) (t-binop-cmp o (tr-i ld d₁) (tr-i ld d₂))
    tr-i ld (t-id-app d) = cᵢ (sym (drop-z+M ld _)) (t-id-app (tr-i ld d))
    tr-i ld (t-fst-app d) = cᵢ (sym (drop-z+M ld _)) (t-fst-app (tr-i ld d))
    tr-i ld (t-snd-app d) = cᵢ (sym (drop-z+M ld _)) (t-snd-app (tr-i ld d))
    tr-i ld (t-terminal-app d) = cᵢ (sym (drop-z+M ld _)) (t-terminal-app (tr-i ld d))
    tr-i ld (t-apply-app-infer d) = cᵢ (sym (drop-z+M ld _)) (t-apply-app-infer (tr-i ld d))
    tr-i ld (t-apply-eff-app-infer d) = cᵢ (sym (drop-z+M ld _)) (t-apply-eff-app-infer (tr-i ld d))
    tr-i ld (t-Out-app-infer wf eq d) = cᵢ (sym (drop-z+M ld _)) (t-Out-app-infer wf eq (tr-i ld d))
    tr-i ld (t-app ah dF dX) = cᵢ (sym (drop-+* ld _ _ _)) (t-app ah (tr-i ld dF) (tr-c ld dX))
    tr-i ld (t-effApp ah dF dX) = cᵢ (sym (drop-+ ld _ _)) (t-effApp ah (tr-i ld dF) (tr-c ld dX))
    tr-i ld (t-app-spine ah dX dF) = cᵢ (sym (drop-+* ld _ _ _)) (t-app-spine ah (tr-i ld dX) (tr-d ld dF))
    tr-i ld (t-neg-void d) = t-neg-void (tr-i ld d)
    tr-i ld (t-case-void {xL = xL} {xR = xR} dS dL dR) =
      t-case-void (tr-i ld dS) (tr-i (ld-under xL T.Void ld) dL) (tr-i (ld-under xR T.Void ld) dR)
    tr-i ld (t-binop-void-l d₁ d₂) = t-binop-void-l (tr-i ld d₁) (tr-i ld d₂)
    tr-i ld (t-binop-void-r d₁ ¬v d₂) = cᵢ (sym (drop-+ ld _ _)) (t-binop-void-r (tr-i ld d₁) ¬v (tr-i ld d₂))
    tr-i ld (t-fst-app-void d) = cᵢ (sym (drop-z+M ld _)) (t-fst-app-void (tr-i ld d))
    tr-i ld (t-snd-app-void d) = cᵢ (sym (drop-z+M ld _)) (t-snd-app-void (tr-i ld d))
    tr-i ld (t-apply-app-void d) = cᵢ (sym (drop-z+M ld _)) (t-apply-app-void (tr-i ld d))
    tr-i ld (t-Out-app-void d) = cᵢ (sym (drop-z+M ld _)) (t-Out-app-void (tr-i ld d))
    tr-i ld (t-app-void ah dF dX) = t-app-void ah (tr-i ld dF) (tr-i ld dX)
    tr-c ld t-id-check = cᶜ (sym (drop-zero ld)) t-id-check
    tr-c ld t-fst-check = cᶜ (sym (drop-zero ld)) t-fst-check
    tr-c ld t-snd-check = cᶜ (sym (drop-zero ld)) t-snd-check
    tr-c ld t-terminal-morph-check = cᶜ (sym (drop-zero ld)) t-terminal-morph-check
    tr-c ld t-initial-morph-check = cᶜ (sym (drop-zero ld)) t-initial-morph-check
    tr-c ld t-inl-morph-check = cᶜ (sym (drop-zero ld)) t-inl-morph-check
    tr-c ld t-inr-morph-check = cᶜ (sym (drop-zero ld)) t-inr-morph-check
    tr-c ld (t-compose-check-g dg df) = cᶜ (sym (drop-+ ld _ _)) (t-compose-check-g (tr-d ld dg) (tr-c ld df))
    tr-c ld (t-compose-check-f wf p dg) = cᶜ (sym (drop-+ ld _ _)) (t-compose-check-f (tr-i ld wf) p (tr-c ld dg))
    tr-c ld (t-case-copair-check df dg) = cᶜ (sym (drop-+ ld _ _)) (t-case-copair-check (tr-c ld df) (tr-c ld dg))
    tr-c ld (t-pair-morph-check df dg) = cᶜ (sym (drop-+ ld _ _)) (t-pair-morph-check (tr-c ld df) (tr-c ld dg))
    tr-c ld (t-curry-check d) = t-curry-check (tr-c ld d)
    tr-c ld (t-cata-check wf dalg) = cᶜ (sym (drop-zero ld)) (t-cata-check wf (tr-c {GL = Context.∅} {ΔL = SC.∅} ld-top dalg))
    tr-c ld (t-ana-check wf dco) = cᶜ (sym (drop-zero ld)) (t-ana-check wf (tr-c {GL = Context.∅} {ΔL = SC.∅} ld-top dco))
    tr-c ld (t-sub d p) = t-sub (tr-i ld d) p
    tr-c ld (t-lam {x = y} {A = B} leq body) = t-lam leq (tr-c (ld-under y B ld) body)
    tr-c ld (t-pair-lit-check d₁ d₂) = cᶜ (sym (drop-+ ld _ _)) (t-pair-lit-check (tr-c ld d₁) (tr-c ld d₂))
    tr-c ld (t-In-app-check wf d) = cᶜ (sym (drop-z+M ld _)) (t-In-app-check wf (tr-c ld d))
    tr-c ld (t-apply-check d) = cᶜ (sym (drop-z+M ld _)) (t-apply-check (tr-i ld d))
    tr-c ld (t-inl-app-check d) = cᶜ (sym (drop-z+M ld _)) (t-inl-app-check (tr-c ld d))
    tr-c ld (t-inr-app-check d) = cᶜ (sym (drop-z+M ld _)) (t-inr-app-check (tr-c ld d))
    tr-c ld (t-initial-app-check d) = cᶜ (sym (drop-z+M ld _)) (t-initial-app-check (tr-c ld d))
    tr-c ld (t-var-poly-instantiate {x = y} ln li lp ¬g body) =
        cᶜ (sym (drop-zero ld)) (t-var-poly-instantiate (none-tr (loc-tr ld y) ln) li (lpp-tr y lp) ¬g body)
    tr-d ld (d-infer w sb gr) = d-infer (tr-i ld w) sb gr
    tr-d ld (d-lam {x = y} {A = B} leq body) = d-lam leq (tr-i (ld-under y B ld) body)
    tr-d ld (d-compose dg df) = cᵈ (sym (drop-+ ld _ _)) (d-compose (tr-d ld dg) (tr-d ld df))
    tr-d ld d-id = cᵈ (sym (drop-zero ld)) d-id
    tr-d ld d-fst = cᵈ (sym (drop-zero ld)) d-fst
    tr-d ld d-snd = cᵈ (sym (drop-zero ld)) d-snd
    tr-d ld d-terminal = cᵈ (sym (drop-zero ld)) d-terminal
    tr-d ld d-initial = cᵈ (sym (drop-zero ld)) d-initial
    tr-d ld (d-case df dg) = cᵈ (sym (drop-+ ld _ _)) (d-case (tr-d ld df) (tr-d ld dg))
    tr-d ld (d-pair df dg) = cᵈ (sym (drop-+ ld _ _)) (d-pair (tr-d ld df) (tr-d ld dg))
    tr-d ld (d-cata wf dalg) = cᵈ (sym (drop-zero ld)) (d-cata wf (tr-i {GL = Context.∅} {ΔL = SC.∅} ld-top dalg))

    tr-d ld d-fst-void = cᵈ (sym (drop-zero ld)) d-fst-void
    tr-d ld d-snd-void = cᵈ (sym (drop-zero ld)) d-snd-void
    tr-d ld (d-case-void df dg) = cᵈ (sym (drop-+ ld _ _)) (d-case-void (tr-d ld df) (tr-d ld dg))
    tr-d ld (d-cata-void dalg) = cᵈ (sym (drop-zero ld)) (d-cata-void (tr-i {GL = Context.∅} {ΔL = SC.∅} ld-top dalg))

------------------------------------------------------------------------
-- The theorem, in all three judgments.
------------------------------------------------------------------------

module _ {Γ : NamedCtx} {x : String} {A : Type} {e : RawExpr} {s : PolyType} {g : Ground s}
  (eqA : extractGround s g ≡ A)
  (noLocal : lookupLocal Γ x ≡ nothing)
  (noImp : lookupImport (NamedCtx.imports Γ) x ≡ nothing)
  (noPoly : lookupPoly (NamedCtx.polys Γ) x ≡ nothing)
  (eD : ctxWithImportsAndPolys (NamedCtx.imports Γ) (NamedCtx.polys Γ) ⊢ᶜ e ∶ A ⨾ zeroUsage)
  where
  private
    module Tr = Transfer x A e s g eqA (NamedCtx.imports Γ) (NamedCtx.polys Γ) noImp noPoly eD

  let⇒defᵢ : ∀ {b B q Ψ} → extendNamedCtx Γ x A ⊢ᵢ b ∶ B ⨾ (q ∷ᵘ Ψ)
           → defineNamedCtx Γ x s e ⊢ᵢ b ∶ B ⨾ Ψ
  let⇒defᵢ = Tr.tr-i (Tr.ld-let noLocal)

  let⇒defᶜ : ∀ {b B q Ψ} → extendNamedCtx Γ x A ⊢ᶜ b ∶ B ⨾ (q ∷ᵘ Ψ)
           → defineNamedCtx Γ x s e ⊢ᶜ b ∶ B ⨾ Ψ
  let⇒defᶜ = Tr.tr-c (Tr.ld-let noLocal)

  let⇒defᵈ : ∀ {b A′ π B q Ψ} → extendNamedCtx Γ x A ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ (q ∷ᵘ Ψ)
           → defineNamedCtx Γ x s e ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ Ψ
  let⇒defᵈ = Tr.tr-d (Tr.ld-let noLocal)
