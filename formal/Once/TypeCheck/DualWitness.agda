-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.DualWitness — the checker's witness while its consumers
-- move (plan 0.122 §2b-3, stage d): the compiler's derivation and the
-- Spec's witness, built together, one constructor per rule. It goes with
-- the compiler's judgment (stage f).
------------------------------------------------------------------------

module Once.TypeCheck.DualWitness where

open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Signature using (Signature)
import Once.Spec.Grade as LG
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Spec.Context as SCx
import Once.Spec.Surface.Syntax as SX
import Once.TypeCheck.View as TView
import Once.Internal.Type.Poly as TP
open import Once.Internal.Typing.Scope using (NamedCtx; Binding; Imports; PolyCtx; lookupImport; lookupPolyPrefix; extendNamedCtx)
open NamedCtx
import Once.Spec.Surface.Typing as SUT
import Once.TypeCheck.Scoped as Sc
open Sc using (Scoped; names; s-local; s-res; s-app; s-lam; s-let; s-pair; s-destruct; s-unit; s-int; s-float; s-annot; s-binop; s-neg)
import Once.TypeCheck.Witness as WM

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (trans; cong; cong₂)
open import Once.Spec.Name using (gen; own)
open import Once.Spec.Sub using (_<:_; _⊔_≔_)
open import Once.Internal.Name using (showCanonical; WordName)
open import Once.Internal.Type using (wk₀; none)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Type.Instance using (KindedInstance)
open import Once.Internal.Type.Schema using (kinded-instance)
open import Once.Internal.Context using (svar; _⊔ᵘ_)
open import Once.Internal.Syntax using (isArithmeticOp; isFloatArithmeticOp; isComparisonOp)
open import Once.Internal.Typing.Scope using (lookupLocal; classifyAppHead)
open import Once.Internal.Core.Decl using (⌜declS⌝)
open import Once.Type.Grade using (_≤qᵇ_)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Spec.Surface.Syntax using (OpAdd; OpSub; OpMul; OpDiv; OpMod; OpLt; OpLe; OpGt; OpGe; OpEq; OpNe; BinOp)
open import Data.Unit using (⊤)

open import Once.Internal.Typing
  using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; _⊢ᵈ_∶_⇒[_]↦_⨾_;
         t-int; t-float; t-unit; t-unit-var; t-var-local; t-var-resolved; t-var-own; t-var-import;
         t-var-poly-instantiate-infer; t-annot; t-pair; t-neg; t-neg-float; t-let; t-case;
         t-binop-arith; t-binop-arith-float; t-binop-arith-float-il; t-binop-arith-float-ir; t-binop-cmp;
         t-id-app; t-fst-app; t-snd-app; t-terminal-app; t-apply-app-infer; t-apply-eff-app-infer;
         t-Out-app-infer; t-Out-eff-app-infer; t-app; t-effApp; t-app-spine;
         t-id-check; t-fst-check; t-snd-check; t-terminal-morph-check; t-initial-morph-check; t-inl-morph-check;
         t-inr-morph-check; t-compose-check-g; t-compose-check-f; t-case-copair-check; t-pair-morph-check;
         t-curry-check; t-cata-check; t-ana-check; t-loop-check; t-sub; t-lam; t-pair-lit-check; t-In-app-check;
         t-apply-check; t-inl-app-check; t-inr-app-check; t-initial-app-check; t-var-poly-instantiate;
         d-infer; d-poly; d-lam; d-compose; d-id; d-fst; d-snd; d-terminal; d-initial; d-case; d-pair; d-cata)
open import Once.TypeCheck.SpecWitness

DI : ∀ {m} (ctx : NamedCtx m) → SX.Expr → ST.Ty m → SCx.Usage (size ctx) → Set
DI ctx e A Ψ = (ctx ⊢ᵢ e ∶ A ⨾ Ψ) × WI ctx e A Ψ

DC : ∀ {m} (ctx : NamedCtx m) → SX.Expr → ST.Ty m → SCx.Usage (size ctx) → Set
DC ctx e A Ψ = (ctx ⊢ᶜ e ∶ A ⨾ Ψ) × WC ctx e A Ψ

DD : ∀ {m} (ctx : NamedCtx m) → SX.Expr → ST.Ty m → LG.Purity → ST.Ty m → SCx.Usage (size ctx) → Set
DD ctx e A π B Ψ = (ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ) × WD ctx e A π B Ψ

module _ {m} {ctx : NamedCtx m} where

  private
    _⇒⟨_⟩_ : ST.Ty m → LG.Purity → ST.Ty m → ST.Ty m
    A ⇒⟨ π ⟩ B = A ST.⇒[ LG.mk-kind LG.Many π ] B
    infixr 30 _⇒⟨_⟩_
    Z = SCx.zeroUsage {size ctx}
    gn : String → SX.Expr
    gn g = SX.RResolved (gen g)

  dt-int : (n : ℤ) → DI ctx (SX.RInt n) ST.Int SCx.zeroUsage
  dt-int n = t-int n , wt-int n

  dt-float : ∀ i f l → DI ctx (SX.RFloat i f l) ST.Float SCx.zeroUsage
  dt-float i f l = t-float i f l , wt-float i f l

  dt-unit : DI ctx SX.RUnit ST.Unit SCx.zeroUsage
  dt-unit = t-unit , wt-unit

  dt-unit-var : DI ctx (SX.RResolved (gen "unit")) ST.Unit SCx.zeroUsage
  dt-unit-var = t-unit-var , wt-unit-var

  dt-var-local : ∀ {x A Ψ} {eV : Once.Internal.Context.SVar (debruijn ctx) Ψ A} → lookupLocal ctx x ≡ just (A , Ψ , eV) → DI ctx (SX.RVar x) A Ψ
  dt-var-local a0 = t-var-local a0 , wt-var-local a0

  dt-var-resolved : ∀ {cn T A} → Once.Spec.Name.NotGenerator cn → WordName cn → lookupImport (sig ctx) (showCanonical cn) ≡ just T → IsConcrete T → A ≡ wk₀ T → DI ctx (SX.RResolved cn) A SCx.zeroUsage
  dt-var-resolved a0 a1 a2 a3 a4 = t-var-resolved a0 a1 a2 a3 a4 , wt-var-resolved a0 a1 a2 a3 a4

  dt-var-own : ∀ {x T A} → lookupImport (sig ctx) x ≡ nothing → (lk : lookupImport (imports ctx) x ≡ just T) → A ≡ wk₀ T → DI ctx (SX.RResolved (own x)) A SCx.zeroUsage
  dt-var-own a0 lk a2 = t-var-own a0 lk a2 , wt-var-own a0 lk a2

  dt-var-import : ∀ {x T A} → ¬ Once.Spec.Name.GenWord x → lookupLocal ctx x ≡ nothing → lookupImport (imports ctx) x ≡ just T → IsConcrete T → A ≡ wk₀ T → DI ctx (SX.RVar x) A SCx.zeroUsage
  dt-var-import a0 a1 a2 a3 a4 = t-var-import a0 a1 a2 a3 a4 , wt-var-import a0 a1 a2 a3 a4

  dt-var-poly-instantiate-infer : ∀ {x T sc body prefix} {g : TP.Ground sc} → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix)) → TP.Ground sc → T ≡ TP.extractGround sc g → DI ctx (SX.RResolved (own x)) T SCx.zeroUsage
  dt-var-poly-instantiate-infer {g = g} a0 a1 lp a3 a4 = t-var-poly-instantiate-infer {g = g} a0 a1 lp a3 a4 , wt-var-poly-instantiate-infer {g = g} a0 a1 lp a3 a4

  dt-annot : ∀ {e T A Ψ} → DC ctx e A Ψ → A ≡ wk₀ T → DI ctx (SX.RAnnot e T) A Ψ
  dt-annot a0 a1 = t-annot (proj₁ a0) a1 , wt-annot (proj₂ a0) a1

  dt-pair : ∀ {a b A B Ψ₁ Ψ₂} → DI ctx a A Ψ₁ → DI ctx b B Ψ₂ → DI ctx (SX.RPair a b) (A ST.* B) (Ψ₁ SCx.+ᵘ Ψ₂)
  dt-pair a0 a1 = t-pair (proj₁ a0) (proj₁ a1) , wt-pair (proj₂ a0) (proj₂ a1)

  dt-neg : ∀ {e Ψ} → DI ctx e ST.Int Ψ → DI ctx (SX.RNeg e) ST.Int Ψ
  dt-neg a0 = t-neg (proj₁ a0) , wt-neg (proj₂ a0)

  dt-neg-float : ∀ i f l → DI ctx (SX.RNeg (SX.RFloat i f l)) ST.Float SCx.zeroUsage
  dt-neg-float i f l = t-neg-float i f l , wt-neg-float i f l

  dt-let : ∀ {x e₁ e₂ A B q Ψ₁ Ψ₂} → DI ctx e₁ A Ψ₁ → DI (extendNamedCtx ctx x A) e₂ B (q SCx.∷ Ψ₂) → DI ctx (SX.RLet x e₁ e₂) B (Ψ₂ SCx.+ᵘ (q SCx.*ᵘ Ψ₁))
  dt-let a0 a1 = t-let (proj₁ a0) (proj₁ a1) , wt-let (proj₂ a0) (proj₂ a1)

  dt-case : ∀ {e xl el xr er A B Cl Cr C ql qr Ψs Ψₗ Ψᵣ} → DI ctx e (A ST.+ B) Ψs → DI (extendNamedCtx ctx xl A) el Cl (ql SCx.∷ Ψₗ) → DI (extendNamedCtx ctx xr B) er Cr (qr SCx.∷ Ψᵣ) → Cl ⊔ Cr ≔ C → DI ctx (SX.RDestruct e xl el xr er) C (Ψs SCx.+ᵘ (Ψₗ ⊔ᵘ Ψᵣ))
  dt-case a0 a1 a2 a3 = t-case (proj₁ a0) (proj₁ a1) (proj₁ a2) a3 , wt-case (proj₂ a0) (proj₂ a1) (proj₂ a2) a3

  dt-binop-arith : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isArithmeticOp op ≡ true → DI ctx e₁ ST.Int Ψ₁ → DI ctx e₂ ST.Int Ψ₂ → DI ctx (SX.RBinOp op e₁ e₂) ST.Int (Ψ₁ SCx.+ᵘ Ψ₂)
  dt-binop-arith a0 a1 a2 = t-binop-arith a0 (proj₁ a1) (proj₁ a2) , wt-binop-arith a0 (proj₂ a1) (proj₂ a2)

  dt-binop-arith-float : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isFloatArithmeticOp op ≡ true → DI ctx e₁ ST.Float Ψ₁ → DI ctx e₂ ST.Float Ψ₂ → DI ctx (SX.RBinOp op e₁ e₂) ST.Float (Ψ₁ SCx.+ᵘ Ψ₂)
  dt-binop-arith-float a0 a1 a2 = t-binop-arith-float a0 (proj₁ a1) (proj₁ a2) , wt-binop-arith-float a0 (proj₂ a1) (proj₂ a2)

  dt-binop-arith-float-il : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isFloatArithmeticOp op ≡ true → DI ctx e₁ ST.Int Ψ₁ → DI ctx e₂ ST.Float Ψ₂ → DI ctx (SX.RBinOp op e₁ e₂) ST.Float (Ψ₁ SCx.+ᵘ Ψ₂)
  dt-binop-arith-float-il a0 a1 a2 = t-binop-arith-float-il a0 (proj₁ a1) (proj₁ a2) , wt-binop-arith-float-il a0 (proj₂ a1) (proj₂ a2)

  dt-binop-arith-float-ir : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isFloatArithmeticOp op ≡ true → DI ctx e₁ ST.Float Ψ₁ → DI ctx e₂ ST.Int Ψ₂ → DI ctx (SX.RBinOp op e₁ e₂) ST.Float (Ψ₁ SCx.+ᵘ Ψ₂)
  dt-binop-arith-float-ir a0 a1 a2 = t-binop-arith-float-ir a0 (proj₁ a1) (proj₁ a2) , wt-binop-arith-float-ir a0 (proj₂ a1) (proj₂ a2)

  dt-binop-cmp : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isComparisonOp op ≡ true → DI ctx e₁ ST.Int Ψ₁ → DI ctx e₂ ST.Int Ψ₂ → DI ctx (SX.RBinOp op e₁ e₂) (ST.Unit ST.+ ST.Unit) (Ψ₁ SCx.+ᵘ Ψ₂)
  dt-binop-cmp a0 a1 a2 = t-binop-cmp a0 (proj₁ a1) (proj₁ a2) , wt-binop-cmp a0 (proj₂ a1) (proj₂ a2)

  dt-id-app : ∀ {e T Ψ} → DI ctx e T Ψ → DI ctx (SX.RApp (SX.RResolved (gen "id")) e) T (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-id-app a0 = t-id-app (proj₁ a0) , wt-id-app (proj₂ a0)

  dt-fst-app : ∀ {e A B Ψ} → DI ctx e (A ST.* B) Ψ → DI ctx (SX.RApp (SX.RResolved (gen "fst")) e) A (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-fst-app a0 = t-fst-app (proj₁ a0) , wt-fst-app (proj₂ a0)

  dt-snd-app : ∀ {e A B Ψ} → DI ctx e (A ST.* B) Ψ → DI ctx (SX.RApp (SX.RResolved (gen "snd")) e) B (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-snd-app a0 = t-snd-app (proj₁ a0) , wt-snd-app (proj₂ a0)

  dt-terminal-app : ∀ {e T Ψ} → DI ctx e T Ψ → DI ctx (SX.RApp (SX.RResolved (gen "terminal")) e) ST.Unit (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-terminal-app a0 = t-terminal-app (proj₁ a0) , wt-terminal-app (proj₂ a0)

  dt-apply-app-infer : ∀ {e A B Ψ} → DI ctx e ((A ST.⇒[ LG.mk-kind LG.Many LG.pure ] B) ST.* A) Ψ → DI ctx (SX.RApp (SX.RResolved (gen "apply")) e) B (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-apply-app-infer a0 = t-apply-app-infer (proj₁ a0) , wt-apply-app-infer (proj₂ a0)

  dt-apply-eff-app-infer : ∀ {e A B Ψ π} {g : LG.EffGrade π} → DI ctx e ((A ST.⇒[ LG.mk-kind LG.Many π ] B) ST.* A) Ψ → DI ctx (SX.RApp (SX.RResolved (gen "apply")) e) (ST.Unit ST.⇒[ LG.mk-kind LG.Many π ] B) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-apply-eff-app-infer {g = g} a0 = t-apply-eff-app-infer {g = g} (proj₁ a0) , wt-apply-eff-app-infer {g = g} (proj₂ a0)

  dt-Out-app-infer : ∀ {e F C Ψ} → ST.WFFun (kinds ctx) F → ST.⟦ F ⟧F (ST.ν F LG.pureᶠ) ≡ C → DI ctx e (ST.ν F LG.pureᶠ) Ψ → DI ctx (SX.RApp (SX.RResolved (gen "Out")) e) C (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-Out-app-infer a0 a1 a2 = t-Out-app-infer a0 a1 (proj₁ a2) , wt-Out-app-infer a0 a1 (proj₂ a2)

  dt-Out-eff-app-infer : ∀ {e F C Ψ} → ST.WFFun (kinds ctx) F → ST.⟦ F ⟧F (ST.ν F LG.actᶠ) ≡ C → DI ctx e (ST.ν F LG.actᶠ) Ψ → DI ctx (SX.RApp (SX.RResolved (gen "Out")) e) (ST.Unit ST.⇒[ LG.mk-kind LG.Many LG.act ] C) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-Out-eff-app-infer a0 a1 a2 = t-Out-eff-app-infer a0 a1 (proj₁ a2) , wt-Out-eff-app-infer a0 a1 (proj₂ a2)

  dt-app : ∀ {f x A B q Ψ₁ Ψ₂} → classifyAppHead f ≡ nothing → DI ctx f (A ST.⇒[ LG.mk-kind q LG.pure ] B) Ψ₁ → DC ctx x A Ψ₂ → DI ctx (SX.RApp f x) B (Ψ₁ SCx.+ᵘ (q SCx.*ᵘ Ψ₂))
  dt-app a0 a1 a2 = t-app a0 (proj₁ a1) (proj₁ a2) , wt-app a0 (proj₂ a1) (proj₂ a2)

  dt-effApp : ∀ {f x A B Ψ₁ Ψ₂ π} {g : LG.EffGrade π} → classifyAppHead f ≡ nothing → DI ctx f (A ST.⇒[ LG.mk-kind LG.Many π ] B) Ψ₁ → DC ctx x A Ψ₂ → DI ctx (SX.RApp f x) (ST.Unit ST.⇒[ LG.mk-kind LG.Many π ] B) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  dt-effApp {g = g} a0 a1 a2 = t-effApp {g = g} a0 (proj₁ a1) (proj₁ a2) , wt-effApp {g = g} a0 (proj₂ a1) (proj₂ a2)

  dt-app-spine : ∀ {f x X T Ψ₁ Ψ₂} → classifyAppHead f ≡ nothing → DI ctx x X Ψ₂ → DD ctx f X LG.pure T Ψ₁ → DI ctx (SX.RApp f x) T (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  dt-app-spine a0 a1 a2 = t-app-spine a0 (proj₁ a1) (proj₁ a2) , wt-app-spine a0 (proj₂ a1) (proj₂ a2)

  dt-id-check : ∀ {T π} {u : LG.pure LG.⊑π π} → DC ctx (gn "id") (T ⇒⟨ π ⟩ T) Z
  dt-id-check {u = u} = t-id-check {u = u} , wt-id-check {u = u}

  dt-fst-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → DC ctx (gn "fst") ((A ST.* B) ⇒⟨ π ⟩ A) Z
  dt-fst-check {u = u} = t-fst-check {u = u} , wt-fst-check {u = u}

  dt-snd-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → DC ctx (gn "snd") ((A ST.* B) ⇒⟨ π ⟩ B) Z
  dt-snd-check {u = u} = t-snd-check {u = u} , wt-snd-check {u = u}

  dt-terminal-morph-check : ∀ {A π} {u : LG.pure LG.⊑π π} → DC ctx (gn "terminal") (A ⇒⟨ π ⟩ ST.Unit) Z
  dt-terminal-morph-check {u = u} = t-terminal-morph-check {u = u} , wt-terminal-morph-check {u = u}

  dt-initial-morph-check : ∀ {A π} {u : LG.pure LG.⊑π π} → DC ctx (gn "initial") (ST.Void ⇒⟨ π ⟩ A) Z
  dt-initial-morph-check {u = u} = t-initial-morph-check {u = u} , wt-initial-morph-check {u = u}

  dt-inl-morph-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → DC ctx (gn "inl") (A ⇒⟨ π ⟩ (A ST.+ B)) Z
  dt-inl-morph-check {u = u} = t-inl-morph-check {u = u} , wt-inl-morph-check {u = u}

  dt-inr-morph-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → DC ctx (gn "inr") (B ⇒⟨ π ⟩ (A ST.+ B)) Z
  dt-inr-morph-check {u = u} = t-inr-morph-check {u = u} , wt-inr-morph-check {u = u}

  dt-compose-check-g : ∀ {f g A B C π Ψ₁ Ψ₂} → DD ctx g A π B Ψ₂ → DC ctx f (B ⇒⟨ π ⟩ C) Ψ₁ → DC ctx (SX.RApp (SX.RApp (gn "compose") f) g) (A ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  dt-compose-check-g {g = g} a0 a1 = t-compose-check-g {g = g} (proj₁ a0) (proj₁ a1) , wt-compose-check-g {g = g} (proj₂ a0) (proj₂ a1)

  dt-compose-check-f : ∀ {f g A B C C′ π π′ Ψ₁ Ψ₂} → DI ctx f (B ⇒⟨ π′ ⟩ C′) Ψ₁ → (B ⇒⟨ π′ ⟩ C′) <: (B ⇒⟨ π ⟩ C) → DC ctx g (A ⇒⟨ π ⟩ B) Ψ₂ → DC ctx (SX.RApp (SX.RApp (gn "compose") f) g) (A ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  dt-compose-check-f {g = g} a0 a1 a2 = t-compose-check-f {g = g} (proj₁ a0) a1 (proj₁ a2) , wt-compose-check-f {g = g} (proj₂ a0) a1 (proj₂ a2)

  dt-case-copair-check : ∀ {f g A B C π Ψ₁ Ψ₂} → DC ctx f (A ⇒⟨ π ⟩ C) Ψ₁ → DC ctx g (B ⇒⟨ π ⟩ C) Ψ₂ → DC ctx (SX.RApp (SX.RApp (gn "case") f) g) ((A ST.+ B) ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ Ψ₂)
  dt-case-copair-check {g = g} a0 a1 = t-case-copair-check {g = g} (proj₁ a0) (proj₁ a1) , wt-case-copair-check {g = g} (proj₂ a0) (proj₂ a1)

  dt-pair-morph-check : ∀ {f g A B C π Ψ₁ Ψ₂} → DC ctx f (A ⇒⟨ π ⟩ B) Ψ₁ → DC ctx g (A ⇒⟨ π ⟩ C) Ψ₂ → DC ctx (SX.RApp (SX.RApp (gn "pair") f) g) (A ⇒⟨ π ⟩ (B ST.* C)) (Ψ₁ SCx.+ᵘ Ψ₂)
  dt-pair-morph-check {g = g} a0 a1 = t-pair-morph-check {g = g} (proj₁ a0) (proj₁ a1) , wt-pair-morph-check {g = g} (proj₂ a0) (proj₂ a1)

  dt-curry-check : ∀ {f A B C π₀ π Ψ} {u : LG.pure LG.⊑π π₀} → DC ctx f ((A ST.* B) ⇒⟨ π ⟩ C) Ψ → DC ctx (SX.RApp (gn "curry") f) (A ⇒⟨ π₀ ⟩ (B ⇒⟨ π ⟩ C)) Ψ
  dt-curry-check {u = u} a0 = t-curry-check {u = u} (proj₁ a0) , wt-curry-check {u = u} (proj₂ a0)

  dt-cata-check : ∀ {alg F A π Ψ} {u : LG.pure LG.⊑π π} → ST.WFFun (kinds ctx) F → DC ctx alg (ST.⟦ F ⟧F A ⇒⟨ π ⟩ A) Ψ → DC ctx (SX.RApp (gn "cata") alg) (ST.μ F ⇒⟨ π ⟩ A) (LG.Many SCx.*ᵘ Ψ)
  dt-cata-check {u = u} a0 a1 = t-cata-check {u = u} a0 (proj₁ a1) , wt-cata-check {u = u} a0 (proj₂ a1)

  dt-ana-check : ∀ {c F A π₀ φ Ψ} {u : LG.pure LG.⊑π π₀} {ua : π₀ LG.⊑π LG.act} → ST.WFFun (kinds ctx) F → DC ctx c (A ⇒⟨ LG.fin φ ⟩ ST.⟦ F ⟧F A) Ψ → DC ctx (SX.RApp (gn "ana") c) (A ⇒⟨ π₀ ⟩ ST.ν F φ) (LG.Many SCx.*ᵘ Ψ)
  dt-ana-check {u = u} {ua = ua} a0 a1 = t-ana-check {u = u} {ua = ua} a0 (proj₁ a1) , wt-ana-check {u = u} {ua = ua} a0 (proj₂ a1)

  dt-loop-check : ∀ {c A B Ψ} → DC ctx c (A ⇒⟨ LG.act ⟩ (B ST.+ A)) Ψ → DC ctx (SX.RApp (gn "ana") c) (A ⇒⟨ LG.eff ⟩ B) (LG.Many SCx.*ᵘ Ψ)
  dt-loop-check a0 = t-loop-check (proj₁ a0) , wt-loop-check (proj₂ a0)

  dt-sub : ∀ {e A B Ψ} → DI ctx e A Ψ → A <: B → DC ctx e B Ψ
  dt-sub a0 a1 = t-sub (proj₁ a0) a1 , wt-sub (proj₂ a0) a1

  dt-lam : ∀ {x body A B q q′ π Ψ} {u : LG.pure LG.⊑π π} → (q′ ≤qᵇ q) ≡ true → DC (extendNamedCtx ctx x A) body B (q′ SCx.∷ Ψ) → DC ctx (SX.RLam x body) (A ST.⇒[ LG.mk-kind q π ] B) Ψ
  dt-lam {u = u} a0 a1 = t-lam {u = u} a0 (proj₁ a1) , wt-lam {u = u} a0 (proj₂ a1)

  dt-pair-lit-check : ∀ {a b A B Ψ₁ Ψ₂} → DC ctx a A Ψ₁ → DC ctx b B Ψ₂ → DC ctx (SX.RPair a b) (A ST.* B) (Ψ₁ SCx.+ᵘ Ψ₂)
  dt-pair-lit-check a0 a1 = t-pair-lit-check (proj₁ a0) (proj₁ a1) , wt-pair-lit-check (proj₂ a0) (proj₂ a1)

  dt-In-app-check : ∀ {e F Ψ} → ST.WFFun (kinds ctx) F → DC ctx e (ST.⟦ F ⟧F (ST.μ F)) Ψ → DC ctx (SX.RApp (gn "In") e) (ST.μ F) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-In-app-check a0 a1 = t-In-app-check a0 (proj₁ a1) , wt-In-app-check a0 (proj₂ a1)

  dt-apply-check : ∀ {e A B Ψ} → DI ctx e ((A ⇒⟨ LG.pure ⟩ B) ST.* A) Ψ → DC ctx (SX.RApp (gn "apply") e) B (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-apply-check a0 = t-apply-check (proj₁ a0) , wt-apply-check (proj₂ a0)

  dt-inl-app-check : ∀ {e A B Ψ} → DC ctx e A Ψ → DC ctx (SX.RApp (gn "inl") e) (A ST.+ B) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-inl-app-check a0 = t-inl-app-check (proj₁ a0) , wt-inl-app-check (proj₂ a0)

  dt-inr-app-check : ∀ {e A B Ψ} → DC ctx e B Ψ → DC ctx (SX.RApp (gn "inr") e) (A ST.+ B) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-inr-app-check a0 = t-inr-app-check (proj₁ a0) , wt-inr-app-check (proj₂ a0)

  dt-initial-app-check : ∀ {e T Ψ} → DC ctx e ST.Void Ψ → DC ctx (SX.RApp (gn "initial") e) T (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  dt-initial-app-check a0 = t-initial-app-check (proj₁ a0) , wt-initial-app-check (proj₂ a0)

  dt-var-poly-instantiate : ∀ {x T sc body prefix} → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix)) → ¬ TP.Ground sc → KindedInstance (kinds ctx) sc T → DC ctx (SX.RResolved (own x)) T Z
  dt-var-poly-instantiate a0 a1 lp a3 a4 = t-var-poly-instantiate a0 a1 lp a3 a4 , wt-var-poly-instantiate a0 a1 lp a3 a4

  dd-infer : ∀ {g A A′ B π π′ Ψ} → DI ctx g (A′ ST.⇒[ LG.mk-kind LG.Many π′ ] B) Ψ → A <: A′ → π′ LG.⊑π π → DD ctx g A π B Ψ
  dd-infer {g = g} a0 a1 a2 = d-infer {g = g} (proj₁ a0) a1 a2 , wd-infer {g = g} (proj₂ a0) a1 a2

  dd-poly : ∀ {x A B π π′ sc sd sco body prefix} → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix)) → ¬ TP.Ground sc → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco → KindedInstance (kinds ctx) sc (A ST.⇒[ LG.mk-kind LG.Many π′ ] B) → π′ LG.⊑π π → DD ctx (SX.RResolved (own x)) A π B Z
  dd-poly a0 a1 lp a3 a4 a5 a6 a7 = d-poly a0 a1 lp a3 a4 a5 a6 a7 , wd-poly a0 a1 lp a3 a4 a5 a6 a7

  dd-lam : ∀ {x body A B q′ π Ψ} {u : LG.pure LG.⊑π π} → DI (extendNamedCtx ctx x A) body B (q′ SCx.∷ Ψ) → DD ctx (SX.RLam x body) A π B Ψ
  dd-lam {u = u} a0 = d-lam {u = u} (proj₁ a0) , wd-lam {u = u} (proj₂ a0)

  dd-compose : ∀ {f g A M B π Ψ₁ Ψ₂} → DD ctx g A π M Ψ₂ → DD ctx f M π B Ψ₁ → DD ctx (SX.RApp (SX.RApp (gn "compose") f) g) A π B (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  dd-compose {g = g} a0 a1 = d-compose {g = g} (proj₁ a0) (proj₁ a1) , wd-compose {g = g} (proj₂ a0) (proj₂ a1)

  dd-id : ∀ {A π} {u : LG.pure LG.⊑π π} → DD ctx (gn "id") A π A Z
  dd-id {u = u} = d-id {u = u} , wd-id {u = u}

  dd-fst : ∀ {A B π} {u : LG.pure LG.⊑π π} → DD ctx (gn "fst") (A ST.* B) π A Z
  dd-fst {u = u} = d-fst {u = u} , wd-fst {u = u}

  dd-snd : ∀ {A B π} {u : LG.pure LG.⊑π π} → DD ctx (gn "snd") (A ST.* B) π B Z
  dd-snd {u = u} = d-snd {u = u} , wd-snd {u = u}

  dd-terminal : ∀ {A π} {u : LG.pure LG.⊑π π} → DD ctx (gn "terminal") A π ST.Unit Z
  dd-terminal {u = u} = d-terminal {u = u} , wd-terminal {u = u}

  dd-initial : ∀ {π} {u : LG.pure LG.⊑π π} → DD ctx (gn "initial") ST.Void π ST.Void Z
  dd-initial {u = u} = d-initial {u = u} , wd-initial {u = u}

  dd-case : ∀ {f g A B Cf Cg C π Ψ₁ Ψ₂} → DD ctx f A π Cf Ψ₁ → DD ctx g B π Cg Ψ₂ → Cf ⊔ Cg ≔ C → DD ctx (SX.RApp (SX.RApp (gn "case") f) g) (A ST.+ B) π C (Ψ₁ SCx.+ᵘ Ψ₂)
  dd-case {g = g} a0 a1 a2 = d-case {g = g} (proj₁ a0) (proj₁ a1) a2 , wd-case {g = g} (proj₂ a0) (proj₂ a1) a2

  dd-pair : ∀ {f g A B C π Ψ₁ Ψ₂} → DD ctx f A π B Ψ₁ → DD ctx g A π C Ψ₂ → DD ctx (SX.RApp (SX.RApp (gn "pair") f) g) A π (B ST.* C) (Ψ₁ SCx.+ᵘ Ψ₂)
  dd-pair {g = g} a0 a1 = d-pair {g = g} (proj₁ a0) (proj₁ a1) , wd-pair {g = g} (proj₂ a0) (proj₂ a1)

  dd-cata : ∀ {alg F A π Ψ} {u : LG.pure LG.⊑π π} → ST.WFFun (kinds ctx) F → DI ctx alg (ST.⟦ F ⟧F A ST.⇒[ LG.mk-kind LG.Many π ] A) Ψ → DD ctx (SX.RApp (gn "cata") alg) (ST.μ F) π A (LG.Many SCx.*ᵘ Ψ)
  dd-cata {u = u} a0 a1 = d-cata {u = u} a0 (proj₁ a1) , wd-cata {u = u} a0 (proj₂ a1)
