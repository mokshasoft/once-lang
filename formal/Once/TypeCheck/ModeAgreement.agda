-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.ModeAgreement
--
-- Plan 0.94 C3: CHECKING AGREES WITH INFERENCE on usage. A term's usage is a
-- property of the term in its context, not of the mode (or the route) that
-- derived it: whenever two of the judgments `⊢ᵢ`, `⊢ᶜ`, `⊢ᵈ` derive the same
-- term — the checked and domain-given ones at the arrow the other determines —
-- they assign it the same usage. Synthesis is moreover UNIQUE (`ii`), and the
-- domain-given mode is EXACT (`dd`): its output is determined by its input.
--
-- Completeness needs this exactly where the elaborator's choice is not the
-- derivation's: compose's middle type (§10) is read from `g` first, so a
-- derivation built on `f`'s route (`t-compose-check-f`) meets an elaborator
-- that took `g`'s; the two agree on the result only because they agree on the
-- arms' usages.
--
-- One mutual induction over PAIRS of derivations of the same term. Most pairs
-- are impossible by the term's shape; the rest recurse on their premises. The
-- impossible ones that the unifier cannot see by itself are a builtin head
-- that would have to synthesize (it never does — `classifyAppHead` names it,
-- or `NotGenerator` excludes it) and premises that contradict each other.
------------------------------------------------------------------------
module Once.TypeCheck.ModeAgreement where

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.Type as T using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type;
  PolyType; PolyFunctor; Ground; GroundF; extractGround; extractGroundF;
  PUnit; PVoid; _P*_; _P+_; _P⇒[_]_; PEff; Pμ-type; Pν-type; PInt; PFloat; PStr; PBuffer; PTVar;
  PK; PId; _P⊕_; _P⊗_)
open import Once.Type.Sub using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe)
open import Once.TypeCheck.Raw as Raw using (RawExpr; RResolved; RApp; BinOp; isArithmeticOp; isComparisonOp)
open import Once.CanonicalName using (gen)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Judgment
import Once.Surface.Context as Surface
open Surface using (zeroUsage; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)

------------------------------------------------------------------------
-- Small facts
------------------------------------------------------------------------

private
  just≢nothing : ∀ {ℓ} {X : Set ℓ} {x : X} → just x ≡ nothing → ⊥
  just≢nothing ()

  cod-≡ : ∀ {A A′ B B′ : Type} {k k′} → (A ⇒[ k ] B) ≡ (A′ ⇒[ k′ ] B′) → B ≡ B′
  cod-≡ refl = refl

  arith-not-cmp : ∀ (op : BinOp) → isArithmeticOp op ≡ true → isComparisonOp op ≡ true → ⊥
  arith-not-cmp Raw.OpAdd refl ()
  arith-not-cmp Raw.OpSub refl ()
  arith-not-cmp Raw.OpMul refl ()
  arith-not-cmp Raw.OpDiv refl ()
  arith-not-cmp Raw.OpMod refl ()
  arith-not-cmp Raw.OpLt () _
  arith-not-cmp Raw.OpLe () _
  arith-not-cmp Raw.OpGt () _
  arith-not-cmp Raw.OpGe () _
  arith-not-cmp Raw.OpEq () _
  arith-not-cmp Raw.OpNe () _

-- `Ground` is built from `⊤` and `×`, so its projection cannot depend on the
-- witness.
mutual
  extractGroundF-irr : ∀ (F : PolyFunctor) (g g′ : GroundF F) → extractGroundF F g ≡ extractGroundF F g′
  extractGroundF-irr (PK A) g g′ = cong T.K (extractGround-irr A g g′)
  extractGroundF-irr PId _ _ = refl
  extractGroundF-irr (F P⊕ G) (gF , gG) (gF′ , gG′) =
    cong₂ T._⊕_ (extractGroundF-irr F gF gF′) (extractGroundF-irr G gG gG′)
  extractGroundF-irr (F P⊗ G) (gF , gG) (gF′ , gG′) =
    cong₂ T._⊗_ (extractGroundF-irr F gF gF′) (extractGroundF-irr G gG gG′)

  extractGround-irr : ∀ (A : PolyType) (g g′ : Ground A) → extractGround A g ≡ extractGround A g′
  extractGround-irr PUnit _ _ = refl
  extractGround-irr PVoid _ _ = refl
  extractGround-irr (A P* B) (gA , gB) (gA′ , gB′) = cong₂ _*_ (extractGround-irr A gA gA′) (extractGround-irr B gB gB′)
  extractGround-irr (A P+ B) (gA , gB) (gA′ , gB′) = cong₂ _+_ (extractGround-irr A gA gA′) (extractGround-irr B gB gB′)
  extractGround-irr (A P⇒[ q ] B) (gA , gB) (gA′ , gB′) =
    cong₂ (λ X Y → X ⇒[ T.mk-kind q T.pure ] Y) (extractGround-irr A gA gA′) (extractGround-irr B gB gB′)
  extractGround-irr (PEff A B) (gA , gB) (gA′ , gB′) =
    cong₂ (λ X Y → X ⇒[ T.mk-kind T.Many T.eff ] Y) (extractGround-irr A gA gA′) (extractGround-irr B gB gB′)
  extractGround-irr (Pμ-type F) g g′ = cong μ-type (extractGroundF-irr F g g′)
  extractGround-irr (Pν-type F) g g′ = cong ν-type (extractGroundF-irr F g g′)
  extractGround-irr PInt _ _ = refl
  extractGround-irr PFloat _ _ = refl
  extractGround-irr PStr _ _ = refl
  extractGround-irr PBuffer _ _ = refl
  extractGround-irr (PTVar _) () _

------------------------------------------------------------------------
-- The builtin heads never synthesize.
------------------------------------------------------------------------
noinf-id : ∀ {ctx : NamedCtx} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RResolved (gen "id") ∶ S ⨾ Ψ → ⊥
noinf-id (t-var-resolved (¬g ∷ _) _ _) = ¬g refl
noinf-fst : ∀ {ctx : NamedCtx} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RResolved (gen "fst") ∶ S ⨾ Ψ → ⊥
noinf-fst (t-var-resolved (_ ∷ ¬g ∷ _) _ _) = ¬g refl
noinf-snd : ∀ {ctx : NamedCtx} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RResolved (gen "snd") ∶ S ⨾ Ψ → ⊥
noinf-snd (t-var-resolved (_ ∷ _ ∷ ¬g ∷ _) _ _) = ¬g refl
noinf-terminal : ∀ {ctx : NamedCtx} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RResolved (gen "terminal") ∶ S ⨾ Ψ → ⊥
noinf-terminal (t-var-resolved (_ ∷ _ ∷ _ ∷ ¬g ∷ _) _ _) = ¬g refl
noinf-initial : ∀ {ctx : NamedCtx} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RResolved (gen "initial") ∶ S ⨾ Ψ → ⊥
noinf-initial (t-var-resolved (_ ∷ _ ∷ _ ∷ _ ∷ ¬g ∷ _) _ _) = ¬g refl
noinf-inl : ∀ {ctx : NamedCtx} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RResolved (gen "inl") ∶ S ⨾ Ψ → ⊥
noinf-inl (t-var-resolved (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ ¬g ∷ _) _ _) = ¬g refl
noinf-inr : ∀ {ctx : NamedCtx} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RResolved (gen "inr") ∶ S ⨾ Ψ → ⊥
noinf-inr (t-var-resolved (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ ¬g ∷ _) _ _) = ¬g refl
noinf-curry-app : ∀ {ctx : NamedCtx} {a : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RResolved (gen "curry")) a ∶ S ⨾ Ψ → ⊥
noinf-curry-app (t-app () _ _)
noinf-curry-app (t-effApp () _ _)
noinf-curry-app (t-app-spine () _ _)
noinf-cata-app : ∀ {ctx : NamedCtx} {a : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RResolved (gen "cata")) a ∶ S ⨾ Ψ → ⊥
noinf-cata-app (t-app () _ _)
noinf-cata-app (t-effApp () _ _)
noinf-cata-app (t-app-spine () _ _)
noinf-ana-app : ∀ {ctx : NamedCtx} {a : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RResolved (gen "ana")) a ∶ S ⨾ Ψ → ⊥
noinf-ana-app (t-app () _ _)
noinf-ana-app (t-effApp () _ _)
noinf-ana-app (t-app-spine () _ _)
noinf-In-app : ∀ {ctx : NamedCtx} {a : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RResolved (gen "In")) a ∶ S ⨾ Ψ → ⊥
noinf-In-app (t-app () _ _)
noinf-In-app (t-effApp () _ _)
noinf-In-app (t-app-spine () _ _)
noinf-inl-app : ∀ {ctx : NamedCtx} {a : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RResolved (gen "inl")) a ∶ S ⨾ Ψ → ⊥
noinf-inl-app (t-app () _ _)
noinf-inl-app (t-effApp () _ _)
noinf-inl-app (t-app-spine () _ _)
noinf-inr-app : ∀ {ctx : NamedCtx} {a : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RResolved (gen "inr")) a ∶ S ⨾ Ψ → ⊥
noinf-inr-app (t-app () _ _)
noinf-inr-app (t-effApp () _ _)
noinf-inr-app (t-app-spine () _ _)
noinf-initial-app : ∀ {ctx : NamedCtx} {a : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RResolved (gen "initial")) a ∶ S ⨾ Ψ → ⊥
noinf-initial-app (t-app () _ _)
noinf-initial-app (t-effApp () _ _)
noinf-initial-app (t-app-spine () _ _)
noinf-compose : ∀ {ctx : NamedCtx} {f g : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RApp (RResolved (gen "compose")) f) g ∶ S ⨾ Ψ → ⊥
noinf-compose (t-app () _ _)
noinf-compose (t-effApp () _ _)
noinf-compose (t-app-spine () _ _)
noinf-case : ∀ {ctx : NamedCtx} {f g : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RApp (RResolved (gen "case")) f) g ∶ S ⨾ Ψ → ⊥
noinf-case (t-app () _ _)
noinf-case (t-effApp () _ _)
noinf-case (t-app-spine () _ _)
noinf-pair : ∀ {ctx : NamedCtx} {f g : RawExpr} {S : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
  → ctx ⊢ᵢ RApp (RApp (RResolved (gen "pair")) f) g ∶ S ⨾ Ψ → ⊥
noinf-pair (t-app () _ _)
noinf-pair (t-effApp () _ _)
noinf-pair (t-app-spine () _ _)

------------------------------------------------------------------------
-- The agreement, one mutual induction over pairs of derivations.
------------------------------------------------------------------------

mutual
  -- Synthesis is unique.
  agree-ii : ∀ {ctx : NamedCtx} {e : RawExpr} {A A′ : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
           → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′ → A ≡ A′ × Ψ ≡ Ψ′

  -- Checking at one type: one usage.
  agree-cc : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
           → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ A ⨾ Ψ′ → Ψ ≡ Ψ′

  -- Checking agrees with inference.
  agree-ic : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
           → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ′ → Ψ ≡ Ψ′

  -- The domain-given mode agrees with checking at an arrow from its domain.
  agree-dc : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : T.Purity}
               {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
           → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′ → Ψ ≡ Ψ′

  -- A term that synthesizes is domain-given only through its synthesized arrow.
  agree-di : ∀ {ctx : NamedCtx} {e : RawExpr} {A B S : Type} {π : T.Purity}
               {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
           → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵢ e ∶ S ⨾ Ψ′
           → Σ[ A′ ∈ Type ] Σ[ π′ ∈ T.Purity ] (S ≡ (A′ ⇒[ T.mk-kind T.Many π′ ] B)) × π′ ⊑π π × Ψ ≡ Ψ′

  -- The domain-given mode is exact.
  agree-dd : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : T.Purity}
               {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
           → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B′ ⨾ Ψ′ → B ≡ B′ × Ψ ≡ Ψ′

  ----------------------------------------------------------------------
  -- agree-ii
  agree-ii (t-int _) (t-int _) = refl , refl
  agree-ii (t-float _ _ _ _) (t-float _ _ _ _) = refl , refl
  agree-ii (t-str _) (t-str _) = refl , refl
  agree-ii t-unit t-unit = refl , refl
  agree-ii t-unit-var t-unit-var = refl , refl
  agree-ii t-unit-var (t-var-resolved (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ ¬u ∷ _) _ _) = ⊥-elim (¬u refl)
  agree-ii (t-var-resolved (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ ¬u ∷ _) _ _) t-unit-var = ⊥-elim (¬u refl)
  agree-ii (t-var-resolved _ l _) (t-var-resolved _ l′ _) with trans (sym l) l′
  ... | refl = refl , refl
  agree-ii (t-var-qualified l _) (t-var-qualified l′ _) with trans (sym l) l′
  ... | refl = refl , refl
  agree-ii (t-var-local l) (t-var-local l′) with trans (sym l) l′
  ... | refl = refl , refl
  agree-ii (t-var-local l) (t-var-import _ ln _ _) = ⊥-elim (just≢nothing (trans (sym l) ln))
  agree-ii (t-var-local l) (t-var-poly-instantiate-infer ln _ _ _ _ _) = ⊥-elim (just≢nothing (trans (sym l) ln))
  agree-ii (t-var-import _ ln _ _) (t-var-local l) = ⊥-elim (just≢nothing (trans (sym l) ln))
  agree-ii (t-var-import _ _ i _) (t-var-import _ _ i′ _) with trans (sym i) i′
  ... | refl = refl , refl
  agree-ii (t-var-import _ _ i _) (t-var-poly-instantiate-infer _ inn _ _ _ _) = ⊥-elim (just≢nothing (trans (sym i) inn))
  agree-ii (t-var-poly-instantiate-infer ln _ _ _ _ _) (t-var-local l) = ⊥-elim (just≢nothing (trans (sym l) ln))
  agree-ii (t-var-poly-instantiate-infer _ inn _ _ _ _) (t-var-import _ _ i _) = ⊥-elim (just≢nothing (trans (sym i) inn))
  agree-ii (t-var-poly-instantiate-infer {schema = s} {g = g} _ _ p _ refl _)
           (t-var-poly-instantiate-infer {g = g′} _ _ p′ _ refl _) with trans (sym p) p′
  ... | refl = extractGround-irr s g g′ , refl
  agree-ii (t-annot c) (t-annot c′) = refl , agree-cc c c′
  agree-ii (t-pair a b) (t-pair a′ b′) with agree-ii a a′ | agree-ii b b′
  ... | refl , refl | refl , refl = refl , refl
  agree-ii (t-neg d) (t-neg d′) = refl , proj₂ (agree-ii d d′)
  agree-ii (t-neg ()) (t-neg-float _ _ _ _)
  agree-ii (t-neg-float _ _ _ _) (t-neg ())
  agree-ii (t-neg-float _ _ _ _) (t-neg-float _ _ _ _) = refl , refl
  agree-ii (t-let d₁ d₂) (t-let d₁′ d₂′) with agree-ii d₁ d₁′
  ... | refl , refl with agree-ii d₂ d₂′
  ...   | refl , refl = refl , refl
  agree-ii (t-case dS dL dR) (t-case dS′ dL′ dR′) with agree-ii dS dS′
  ... | refl , refl with agree-ii dL dL′ | agree-ii dR dR′
  ...   | refl , refl | refl , refl = refl , refl
  agree-ii (t-binop-arith _ d₁ d₂) (t-binop-arith _ d₁′ d₂′) with agree-ii d₁ d₁′ | agree-ii d₂ d₂′
  ... | refl , refl | refl , refl = refl , refl
  agree-ii (t-binop-arith _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-arith _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) with agree-ii d₂ d₂′
  ... | () , _
  agree-ii (t-binop-arith _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-arith {op = op} a _ _) (t-binop-cmp c _ _) = ⊥-elim (arith-not-cmp op a c)
  agree-ii (t-binop-arith-float _ d₁ d₂) (t-binop-arith _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-arith-float _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) with agree-ii d₁ d₁′ | agree-ii d₂ d₂′
  ... | refl , refl | refl , refl = refl , refl
  agree-ii (t-binop-arith-float _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-arith-float _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) with agree-ii d₂ d₂′
  ... | () , _
  agree-ii (t-binop-arith-float _ d₁ d₂) (t-binop-cmp _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-arith _ d₁′ d₂′) with agree-ii d₂ d₂′
  ... | () , _
  agree-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) with agree-ii d₁ d₁′ | agree-ii d₂ d₂′
  ... | refl , refl | refl , refl = refl , refl
  agree-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-arith-float-il _ d₁ d₂) (t-binop-cmp _ d₁′ d₂′) with agree-ii d₂ d₂′
  ... | () , _
  agree-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-arith _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) with agree-ii d₂ d₂′
  ... | () , _
  agree-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) with agree-ii d₁ d₁′ | agree-ii d₂ d₂′
  ... | refl , refl | refl , refl = refl , refl
  agree-ii (t-binop-arith-float-ir _ d₁ d₂) (t-binop-cmp _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-cmp {op = op} c _ _) (t-binop-arith a _ _) = ⊥-elim (arith-not-cmp op a c)
  agree-ii (t-binop-cmp _ d₁ d₂) (t-binop-arith-float _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-cmp _ d₁ d₂) (t-binop-arith-float-il _ d₁′ d₂′) with agree-ii d₂ d₂′
  ... | () , _
  agree-ii (t-binop-cmp _ d₁ d₂) (t-binop-arith-float-ir _ d₁′ d₂′) with agree-ii d₁ d₁′
  ... | () , _
  agree-ii (t-binop-cmp _ d₁ d₂) (t-binop-cmp _ d₁′ d₂′) with agree-ii d₁ d₁′ | agree-ii d₂ d₂′
  ... | refl , refl | refl , refl = refl , refl
  agree-ii (t-id-app d) (t-id-app d′) with agree-ii d d′
  ... | refl , refl = refl , refl
  agree-ii (t-fst-app d) (t-fst-app d′) with agree-ii d d′
  ... | refl , refl = refl , refl
  agree-ii (t-snd-app d) (t-snd-app d′) with agree-ii d d′
  ... | refl , refl = refl , refl
  agree-ii (t-terminal-app d) (t-terminal-app d′) with agree-ii d d′
  ... | refl , refl = refl , refl
  agree-ii (t-apply-app-infer d) (t-apply-app-infer d′) with agree-ii d d′
  ... | refl , refl = refl , refl
  agree-ii (t-apply-app-infer d) (t-apply-eff-app-infer d′) with agree-ii d d′
  ... | () , _
  agree-ii (t-apply-eff-app-infer d) (t-apply-app-infer d′) with agree-ii d d′
  ... | () , _
  agree-ii (t-apply-eff-app-infer d) (t-apply-eff-app-infer d′) with agree-ii d d′
  ... | refl , refl = refl , refl
  agree-ii (t-Out-app-infer _ refl d) (t-Out-app-infer _ refl d′) with agree-ii d d′
  ... | refl , refl = refl , refl
  agree-ii (t-id-app _) (t-app () _ _)
  agree-ii (t-app () _ _) (t-id-app _)
  agree-ii (t-id-app _) (t-effApp () _ _)
  agree-ii (t-effApp () _ _) (t-id-app _)
  agree-ii (t-id-app _) (t-app-spine () _ _)
  agree-ii (t-app-spine () _ _) (t-id-app _)
  agree-ii (t-fst-app _) (t-app () _ _)
  agree-ii (t-app () _ _) (t-fst-app _)
  agree-ii (t-fst-app _) (t-effApp () _ _)
  agree-ii (t-effApp () _ _) (t-fst-app _)
  agree-ii (t-fst-app _) (t-app-spine () _ _)
  agree-ii (t-app-spine () _ _) (t-fst-app _)
  agree-ii (t-snd-app _) (t-app () _ _)
  agree-ii (t-app () _ _) (t-snd-app _)
  agree-ii (t-snd-app _) (t-effApp () _ _)
  agree-ii (t-effApp () _ _) (t-snd-app _)
  agree-ii (t-snd-app _) (t-app-spine () _ _)
  agree-ii (t-app-spine () _ _) (t-snd-app _)
  agree-ii (t-terminal-app _) (t-app () _ _)
  agree-ii (t-app () _ _) (t-terminal-app _)
  agree-ii (t-terminal-app _) (t-effApp () _ _)
  agree-ii (t-effApp () _ _) (t-terminal-app _)
  agree-ii (t-terminal-app _) (t-app-spine () _ _)
  agree-ii (t-app-spine () _ _) (t-terminal-app _)
  agree-ii (t-apply-app-infer _) (t-app () _ _)
  agree-ii (t-app () _ _) (t-apply-app-infer _)
  agree-ii (t-apply-app-infer _) (t-effApp () _ _)
  agree-ii (t-effApp () _ _) (t-apply-app-infer _)
  agree-ii (t-apply-app-infer _) (t-app-spine () _ _)
  agree-ii (t-app-spine () _ _) (t-apply-app-infer _)
  agree-ii (t-apply-eff-app-infer _) (t-app () _ _)
  agree-ii (t-app () _ _) (t-apply-eff-app-infer _)
  agree-ii (t-apply-eff-app-infer _) (t-effApp () _ _)
  agree-ii (t-effApp () _ _) (t-apply-eff-app-infer _)
  agree-ii (t-apply-eff-app-infer _) (t-app-spine () _ _)
  agree-ii (t-app-spine () _ _) (t-apply-eff-app-infer _)
  agree-ii (t-Out-app-infer _ _ _) (t-app () _ _)
  agree-ii (t-app () _ _) (t-Out-app-infer _ _ _)
  agree-ii (t-Out-app-infer _ _ _) (t-effApp () _ _)
  agree-ii (t-effApp () _ _) (t-Out-app-infer _ _ _)
  agree-ii (t-Out-app-infer _ _ _) (t-app-spine () _ _)
  agree-ii (t-app-spine () _ _) (t-Out-app-infer _ _ _)
  agree-ii (t-app _ wF dX) (t-app _ wF′ dX′) with agree-ii wF wF′
  ... | refl , refl with agree-cc dX dX′
  ...   | refl = refl , refl
  agree-ii (t-app _ wF _) (t-effApp _ wF′ _) with agree-ii wF wF′
  ... | () , _
  agree-ii (t-effApp _ wF _) (t-app _ wF′ _) with agree-ii wF wF′
  ... | () , _
  agree-ii (t-effApp _ wF dX) (t-effApp _ wF′ dX′) with agree-ii wF wF′
  ... | refl , refl with agree-cc dX dX′
  ...   | refl = refl , refl
  agree-ii (t-app _ wF dX) (t-app-spine _ dX′ dF′) with agree-di dF′ wF
  ... | _ , _ , refl , ⊑-pure , refl with agree-ic dX′ dX
  ...   | refl = refl , refl
  agree-ii (t-app-spine _ dX dF) (t-app _ wF′ dX′) with agree-di dF wF′
  ... | _ , _ , refl , ⊑-pure , refl with agree-ic dX dX′
  ...   | refl = refl , refl
  agree-ii (t-effApp _ wF _) (t-app-spine _ _ dF′) with agree-di dF′ wF
  ... | _ , _ , refl , () , _
  agree-ii (t-app-spine _ _ dF) (t-effApp _ wF′ _) with agree-di dF wF′
  ... | _ , _ , refl , () , _
  agree-ii (t-app-spine _ dX dF) (t-app-spine _ dX′ dF′) with agree-ii dX dX′
  ... | refl , refl with agree-dd dF dF′
  ...   | refl , refl = refl , refl

  ----------------------------------------------------------------------
  -- agree-cc
  agree-cc (t-sub d _) c = agree-ic d c
  agree-cc c (t-sub d _) = sym (agree-ic d c)
  agree-cc t-id-check t-id-check = refl
  agree-cc t-fst-check t-fst-check = refl
  agree-cc t-snd-check t-snd-check = refl
  agree-cc t-terminal-morph-check t-terminal-morph-check = refl
  agree-cc t-initial-morph-check t-initial-morph-check = refl
  agree-cc t-inl-morph-check t-inl-morph-check = refl
  agree-cc t-inr-morph-check t-inr-morph-check = refl
  agree-cc (t-compose-check-g dg df) (t-compose-check-g dg′ df′) with agree-dd dg dg′
  ... | refl , refl = cong (_+ᵘ _) (agree-cc df df′)
  agree-cc (t-compose-check-g dg df) (t-compose-check-f wf _ dg′) =
    cong₂ _+ᵘ_ (sym (agree-ic wf df)) (agree-dc dg dg′)
  agree-cc (t-compose-check-f wf _ dg) (t-compose-check-g dg′ df′) =
    cong₂ _+ᵘ_ (agree-ic wf df′) (sym (agree-dc dg′ dg))
  agree-cc (t-compose-check-f wf _ dg) (t-compose-check-f wf′ _ dg′) with agree-ii wf wf′
  ... | refl , refl = cong (_ +ᵘ_) (agree-cc dg dg′)
  agree-cc (t-case-copair-check df dg) (t-case-copair-check df′ dg′) = cong₂ _+ᵘ_ (agree-cc df df′) (agree-cc dg dg′)
  agree-cc (t-pair-morph-check df dg) (t-pair-morph-check df′ dg′) = cong₂ _+ᵘ_ (agree-cc df df′) (agree-cc dg dg′)
  agree-cc (t-curry-check d) (t-curry-check d′) = agree-cc d d′
  agree-cc (t-cata-check _ _) (t-cata-check _ _) = refl
  agree-cc (t-ana-check _ _) (t-ana-check _ _) = refl
  agree-cc (t-lam _ b) (t-lam _ b′) with agree-cc b b′
  ... | refl = refl
  agree-cc (t-pair-lit-check a b) (t-pair-lit-check a′ b′) = cong₂ _+ᵘ_ (agree-cc a a′) (agree-cc b b′)
  agree-cc (t-In-app-check _ d) (t-In-app-check _ d′) = cong (λ Ψ → zeroUsage +ᵘ (T.Many *ᵘ Ψ)) (agree-cc d d′)
  agree-cc (t-apply-check d) (t-apply-check d′) = cong (λ Ψ → zeroUsage +ᵘ (T.Many *ᵘ Ψ)) (proj₂ (agree-ii d d′))
  agree-cc (t-inl-app-check d) (t-inl-app-check d′) = cong (λ Ψ → zeroUsage +ᵘ (T.Many *ᵘ Ψ)) (agree-cc d d′)
  agree-cc (t-inr-app-check d) (t-inr-app-check d′) = cong (λ Ψ → zeroUsage +ᵘ (T.Many *ᵘ Ψ)) (agree-cc d d′)
  agree-cc (t-initial-app-check d) (t-initial-app-check d′) = cong (λ Ψ → zeroUsage +ᵘ (T.Many *ᵘ Ψ)) (agree-cc d d′)
  agree-cc (t-var-poly-instantiate _ _ _ _ _) (t-var-poly-instantiate _ _ _ _ _) = refl

  ----------------------------------------------------------------------
  -- agree-ic
  agree-ic d (t-sub d′ _) = proj₂ (agree-ii d d′)
  agree-ic (t-pair a b) (t-pair-lit-check a′ b′) = cong₂ _+ᵘ_ (agree-ic a a′) (agree-ic b b′)
  agree-ic (t-apply-app-infer d) (t-apply-check d′) = cong (λ Ψ → zeroUsage +ᵘ (T.Many *ᵘ Ψ)) (proj₂ (agree-ii d d′))
  agree-ic (t-apply-eff-app-infer d) (t-apply-check d′) = cong (λ Ψ → zeroUsage +ᵘ (T.Many *ᵘ Ψ)) (proj₂ (agree-ii d d′))
  agree-ic (t-app () _ _) (t-apply-check _)
  agree-ic (t-effApp () _ _) (t-apply-check _)
  agree-ic (t-app-spine () _ _) (t-apply-check _)
  agree-ic (t-var-local l) (t-var-poly-instantiate ln _ _ _ _) = ⊥-elim (just≢nothing (trans (sym l) ln))
  agree-ic (t-var-import _ _ i _) (t-var-poly-instantiate _ inn _ _ _) = ⊥-elim (just≢nothing (trans (sym i) inn))
  agree-ic (t-var-poly-instantiate-infer _ _ p g _ _) (t-var-poly-instantiate _ _ p′ ¬g _) with trans (sym p) p′
  ... | refl = ⊥-elim (¬g g)
  agree-ic () (t-lam _ _)
  agree-ic d t-id-check = ⊥-elim (noinf-id d)
  agree-ic d t-fst-check = ⊥-elim (noinf-fst d)
  agree-ic d t-snd-check = ⊥-elim (noinf-snd d)
  agree-ic d t-terminal-morph-check = ⊥-elim (noinf-terminal d)
  agree-ic d t-initial-morph-check = ⊥-elim (noinf-initial d)
  agree-ic d t-inl-morph-check = ⊥-elim (noinf-inl d)
  agree-ic d t-inr-morph-check = ⊥-elim (noinf-inr d)
  agree-ic d (t-compose-check-g _ _) = ⊥-elim (noinf-compose d)
  agree-ic d (t-compose-check-f _ _ _) = ⊥-elim (noinf-compose d)
  agree-ic d (t-case-copair-check _ _) = ⊥-elim (noinf-case d)
  agree-ic d (t-pair-morph-check _ _) = ⊥-elim (noinf-pair d)
  agree-ic d (t-curry-check _) = ⊥-elim (noinf-curry-app d)
  agree-ic d (t-cata-check _ _) = ⊥-elim (noinf-cata-app d)
  agree-ic d (t-ana-check _ _) = ⊥-elim (noinf-ana-app d)
  agree-ic d (t-In-app-check _ _) = ⊥-elim (noinf-In-app d)
  agree-ic d (t-inl-app-check _) = ⊥-elim (noinf-inl-app d)
  agree-ic d (t-inr-app-check _) = ⊥-elim (noinf-inr-app d)
  agree-ic d (t-initial-app-check _) = ⊥-elim (noinf-initial-app d)

  ----------------------------------------------------------------------
  -- agree-dc
  agree-dc (d-infer w _ _) c = agree-ic w c
  agree-dc dd (t-sub d _) = proj₂ (proj₂ (proj₂ (proj₂ (agree-di dd d))))
  agree-dc (d-lam _ b) (t-lam _ b′) with agree-ic b b′
  ... | refl = refl
  agree-dc (d-compose dg df) (t-compose-check-g dg′ df′) with agree-dd dg dg′
  ... | refl , refl = cong (_+ᵘ _) (agree-dc df df′)
  agree-dc (d-compose dg df) (t-compose-check-f wf _ dg′) =
    cong₂ _+ᵘ_ (proj₂ (proj₂ (proj₂ (proj₂ (agree-di df wf))))) (agree-dc dg dg′)
  agree-dc d-id t-id-check = refl
  agree-dc d-fst t-fst-check = refl
  agree-dc d-snd t-snd-check = refl
  agree-dc d-terminal t-terminal-morph-check = refl
  agree-dc d-initial t-initial-morph-check = refl
  agree-dc (d-case df dg) (t-case-copair-check df′ dg′) = cong₂ _+ᵘ_ (agree-dc df df′) (agree-dc dg dg′)
  agree-dc (d-pair df dg) (t-pair-morph-check df′ dg′) = cong₂ _+ᵘ_ (agree-dc df df′) (agree-dc dg dg′)
  agree-dc (d-cata _ _) (t-cata-check _ _) = refl

  ----------------------------------------------------------------------
  -- agree-di
  agree-di (d-infer w _ g) d with agree-ii w d
  ... | refl , refl = _ , _ , refl , g , refl
  agree-di (d-lam _ _) ()
  agree-di (d-compose _ _) d = ⊥-elim (noinf-compose d)
  agree-di d-id d = ⊥-elim (noinf-id d)
  agree-di d-fst d = ⊥-elim (noinf-fst d)
  agree-di d-snd d = ⊥-elim (noinf-snd d)
  agree-di d-terminal d = ⊥-elim (noinf-terminal d)
  agree-di d-initial d = ⊥-elim (noinf-initial d)
  agree-di (d-case _ _) d = ⊥-elim (noinf-case d)
  agree-di (d-pair _ _) d = ⊥-elim (noinf-pair d)
  agree-di (d-cata _ _) d = ⊥-elim (noinf-cata-app d)

  ----------------------------------------------------------------------
  -- agree-dd
  agree-dd (d-infer w _ _) dd′ with agree-di dd′ w
  ... | _ , _ , refl , _ , refl = refl , refl
  agree-dd dd (d-infer w _ _) with agree-di dd w
  ... | _ , _ , refl , _ , refl = refl , refl
  agree-dd (d-lam _ b) (d-lam _ b′) with agree-ii b b′
  ... | refl , refl = refl , refl
  agree-dd (d-compose dg df) (d-compose dg′ df′) with agree-dd dg dg′
  ... | refl , refl with agree-dd df df′
  ...   | refl , refl = refl , refl
  agree-dd d-id d-id = refl , refl
  agree-dd d-fst d-fst = refl , refl
  agree-dd d-snd d-snd = refl , refl
  agree-dd d-terminal d-terminal = refl , refl
  agree-dd d-initial d-initial = refl , refl
  agree-dd (d-case df dg) (d-case df′ dg′) with agree-dd df df′ | agree-dd dg dg′
  ... | refl , refl | refl , refl = refl , refl
  agree-dd (d-pair df dg) (d-pair df′ dg′) with agree-dd df df′ | agree-dd dg dg′
  ... | refl , refl | refl , refl = refl , refl
  agree-dd (d-cata _ a) (d-cata _ a′) with cod-≡ (proj₁ (agree-ii a a′))
  ... | refl = refl , refl

------------------------------------------------------------------------
-- The two statements completeness consumes.
------------------------------------------------------------------------

-- An inferred term, checked at any type, has its inferred usage.
mode-agree-ic : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type}
                  {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
              → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ′ → Ψ ≡ Ψ′
mode-agree-ic = agree-ic

-- A domain-given term, checked at an arrow from the same domain, has its
-- domain-given usage.
mode-agree-dc : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : T.Purity}
                  {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
              → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ
              → ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′
              → Ψ ≡ Ψ′
mode-agree-dc = agree-dc
