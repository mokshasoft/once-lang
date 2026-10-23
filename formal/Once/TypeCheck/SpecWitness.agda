-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.SpecWitness — the checker's witness: the Spec's
-- derivation, in any table the scope is read through (plan 0.122 §2b-3,
-- stage d).
--
-- A checked expression's witness is, for every `Pack` of the scope — a
-- table of earlier definitions (`S`, `nm`, `inline`), a View of the
-- compiler's scope into it with what the Spec asks of the View, and the
-- scope's locals — the Spec's derivation of it with its usage (`TypeCheck.Witness`),
-- whose realization (`Denotation.RealizeS`) is the term the checker built
-- (plan 0.122 §5.6: what runs is the realization of the Spec's derivation).
-- One constructor per rule of the checker builds it from its premises'.
------------------------------------------------------------------------

module Once.TypeCheck.SpecWitness where

open import Data.Bool using (Bool; true; false)
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
import Once.Internal.Name
import Once.TypeCheck.Witness as WM
import Once.TypeCheck.Use as UM
import Once.Denotation.RealizeS as RS
open import Once.Surface.Syntax as SS using () renaming (Expr to SExpr)
open import Once.Denotation.SurfaceRefs using (InScope)
open import Once.Denotation.Program using (Linked)

------------------------------------------------------------------------
-- What the scope is read through
------------------------------------------------------------------------

record Pack {m} (ctx : NamedCtx m) : Set where
  field
    Sg     : Signature
    {s}    : ℕ
    S      : SC.Defs s
    nm     : Fin s → CanonicalName
    inline : Fin s → Bool
    V      : TView.View Sg S (imports ctx) (sig ctx) (polys ctx)
    -- a monomorphic definition in scope: its name; it is called
    h-imp  : ∀ {x T} (lk : lookupImport (imports ctx) x ≡ just T)
           → nm (TView.ImportAt.entryOf (TView.View.imported V lk)) ≡ canonical (x ∷ [])
    h-imp-call : ∀ {x T} (lk : lookupImport (imports ctx) x ≡ just T)
               → inline (TView.ImportAt.entryOf (TView.View.imported V lk)) ≡ false
    -- a telescope definition in scope: its name; no type variables exactly when its schema is ground
    h-poly : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
           → nm (TView.View.entry V lp) ≡ canonical (x ∷ [])
    -- …it is inlined
    h-poly-inline : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
                  → inline (TView.View.entry V lp) ≡ true
    h-ground : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
             → TP.Ground sc → SC.Schema.arity (S SC.!! TView.View.entry V lp) ≡ 0
    h-open : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
           → ¬ TP.Ground sc → 0 < SC.Schema.arity (S SC.!! TView.View.entry V lp)
    -- …and an arrow schema is an arrow, its codomain's variables in its domain
    h-arrow : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p)) {sd sco π′}
            → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
            → Σ[ X ∈ ST.Ty (SC.Schema.arity (S SC.!! TView.View.entry V lp)) ]
              Σ[ Y ∈ ST.Ty (SC.Schema.arity (S SC.!! TView.View.entry V lp)) ]
                (SC.Schema.type (S SC.!! TView.View.entry V lp) ≡ X ST.⇒[ LG.mk-kind LG.Many π′ ] Y)
                × (∀ i → ST.Occurs i Y → ST.Occurs i X)
    -- the scope's locals, as the Spec names them
    L      : SUT.Locals Sg S nm m (size ctx)
    lr     : Sc.Locals.LocalsOf Sg S nm (named ctx) (debruijn ctx) L
open Pack

-- A local bound inside the scope.
pack▸ : ∀ {m} {ctx : NamedCtx m} (x : String) (A : ST.Ty m) → Pack ctx → Pack (extendNamedCtx ctx x A)
pack▸ {ctx = ctx} x A P = record
  { Sg = Sg P ; S = S P ; nm = nm P ; inline = inline P ; V = V P
  ; h-imp = h-imp P ; h-imp-call = h-imp-call P ; h-poly = h-poly P ; h-poly-inline = h-poly-inline P ; h-ground = h-ground P ; h-open = h-open P ; h-arrow = h-arrow P
  ; L = SUT._▹_∶_ (L P) x A
  ; lr = Sc.Locals.lo-▸ (lr P) }

------------------------------------------------------------------------
-- The witnesses
------------------------------------------------------------------------

-- The checker's context is the Spec's locals' context.
shape-lo : ∀ {Sg s} {S : SC.Defs s} {nm} {Ok : Fin s → Set} {OkS : CanonicalName → ST.Type → Set} {m} {Δ : ST.KCtx m} {n Γn} {Γd : SCx.Ctx m n} {L}
         → Sc.Locals.LocalsOf Sg S nm Γn Γd L → UM.Shape Sg S nm Ok OkS Δ L Γd
shape-lo Sc.Locals.lo-∅      = UM.sh-∅
shape-lo (Sc.Locals.lo-▸ lo) = UM.sh-▸ (shape-lo lo)

-- The entries a reference may name: those the View finds.
OkOf : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) → Fin (s P) → Set
OkOf P = TView.InView (Sg P) (S P) (V P)

-- …and the declarations: those the scope's signature declares.
OkSOf : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) → CanonicalName → ST.Type → Set
OkSOf {ctx = ctx} P c T = lookupImport (sig ctx) (Once.Internal.Name.showCanonical c) ≡ just T

-- A witness's realization, in the checker's context.
module _ {m} {ctx : NamedCtx m} (P : Pack ctx) where
  private module R = RS (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (inline P) (kinds ctx)

  rz⇒ : ∀ {e A t Ψ} → WM.W⇒ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (L P) e A t Ψ → SExpr (debruijn ctx) Ψ A
  rz⇒ w = R.realize⇒ (shape-lo (lr P)) (proj₂ w)

  rz⇐ : ∀ {e A t Ψ} → WM.W⇐ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (L P) e A t Ψ → SExpr (debruijn ctx) Ψ A
  rz⇐ w = R.realize⇐ (shape-lo (lr P)) (proj₂ w)

  rz↦ : ∀ {e A π B t Ψ} → WM.W↦ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (L P) e A π B t Ψ
      → SExpr (debruijn ctx) Ψ (A ST.⇒[ LG.mk-kind LG.Many π ] B)
  rz↦ w = R.realize↦ (shape-lo (lr P)) (proj₂ w)

WI : ∀ {m} (ctx : NamedCtx m) → SX.Expr → (A : ST.Ty m) (Ψ : SCx.Usage (size ctx)) → SExpr (debruijn ctx) Ψ A → Set
WI ctx e A Ψ eE = InScope ctx eE × ((P : Pack ctx)
                → Σ[ t ∈ SC.Tm (S P) _ (size ctx) ] Σ[ w ∈ WM.W⇒ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (L P) e A t Ψ ] rz⇒ P w ≡ eE)

WC : ∀ {m} (ctx : NamedCtx m) → SX.Expr → (A : ST.Ty m) (Ψ : SCx.Usage (size ctx)) → SExpr (debruijn ctx) Ψ A → Set
WC ctx e A Ψ eE = InScope ctx eE × ((P : Pack ctx)
                → Σ[ t ∈ SC.Tm (S P) _ (size ctx) ] Σ[ w ∈ WM.W⇐ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (L P) e A t Ψ ] rz⇐ P w ≡ eE)

WD : ∀ {m} (ctx : NamedCtx m) → SX.Expr → (A : ST.Ty m) (π : LG.Purity) (B : ST.Ty m) (Ψ : SCx.Usage (size ctx))
   → SExpr (debruijn ctx) Ψ (A ST.⇒[ LG.mk-kind LG.Many π ] B) → Set
WD ctx e A π B Ψ eE = InScope ctx eE × ((P : Pack ctx)
                    → Σ[ t ∈ SC.Tm (S P) _ (size ctx) ] Σ[ w ∈ WM.W↦ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (L P) e A π B t Ψ ] rz↦ P w ≡ eE)

------------------------------------------------------------------------
-- The constructors, one per rule of the checker
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (trans; cong; cong₂)
open import Once.Spec.Name using (gen; own)
open import Once.Spec.Sub using (_<:_; _⊔_≔_; sub-arr)
open _⊔_≔_ using (left; right)
open import Once.Internal.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.Spec.Float.Decimal using (decimalOf; negate)
open import Once.IR as IR using (IR)
open import Once.IRTy using (IRTy; ⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Type.Grade using (≤q-Many)
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
open import Data.Unit using (⊤; tt)

-- A type of no variables is the same type under any substitution: the
-- compiler's weakening is the Spec's `↑`.
mutual
  sub0 : ∀ {m} (T : ST.Ty 0) (σ σ′ : ST.TySub 0 m) → T ST.⟨ σ ⟩ ≡ T ST.⟨ σ′ ⟩
  sub0 (ST.var ()) σ σ′
  sub0 ST.Unit  σ σ′ = refl
  sub0 ST.Void  σ σ′ = refl
  sub0 ST.Int   σ σ′ = refl
  sub0 ST.Float σ σ′ = refl
  sub0 (A ST.* B) σ σ′ = cong₂ ST._*_ (sub0 A σ σ′) (sub0 B σ σ′)
  sub0 (A ST.+ B) σ σ′ = cong₂ ST._+_ (sub0 A σ σ′) (sub0 B σ σ′)
  sub0 (A ST.⇒[ k ] B) σ σ′ = cong₂ (λ X Y → X ST.⇒[ k ] Y) (sub0 A σ σ′) (sub0 B σ σ′)
  sub0 (ST.μ F) σ σ′ = cong ST.μ (sub0F F σ σ′)
  sub0 (ST.ν F φ) σ σ′ = cong (λ G → ST.ν G φ) (sub0F F σ σ′)

  sub0F : ∀ {m} (F : ST.Fun 0) (σ σ′ : ST.TySub 0 m) → F ST.⟨ σ ⟩F ≡ F ST.⟨ σ′ ⟩F
  sub0F (ST.K A) σ σ′ = cong ST.K (sub0 A σ σ′)
  sub0F ST.Id σ σ′ = refl
  sub0F (F ST.⊕ G) σ σ′ = cong₂ ST._⊕_ (sub0F F σ σ′) (sub0F G σ σ′)
  sub0F (F ST.⊗ G) σ σ′ = cong₂ ST._⊗_ (sub0F F σ σ′) (sub0F G σ σ′)

wk₀≡↑ : ∀ {m} (T : ST.Type) → wk₀ {m} T ≡ T ST.⟨ (λ ()) ⟩
wk₀≡↑ T = sub0 T none (λ ())

-- The Spec's rules and the compiler's View, at a pack.
module At {m} {ctx : NamedCtx m} (P : Pack ctx) where
  open WM (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) public
  open Sc.Locals (Sg P) (S P) (nm P) public using (found)
  open RS (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (inline P) (kinds ctx) public using (realize⇒; realize⇐; realize↦; ref)
  module SU = SUT (Sg P) (S P) (nm P)

  sh = shape-lo {Ok = OkOf P} {OkS = OkSOf P} {Δ = kinds ctx} (lr P)
  private
    E = SExpr (debruijn ctx)

  -- A reference to a table entry: with no type variables, synthesized;
  refS : (d : Fin (s P)) → OkOf P d → {c : CanonicalName} → nm P d ≡ c → ∀ {sc} (e : S P SC.!! d ≡ sc) (τ : ST.TySub (SC.Schema.arity sc) m)
       → SC.Schema.arity (S P SC.!! d) ≡ 0
       → Σ[ t ∈ SC.Tm (S P) m (size ctx) ] Σ[ w ∈ W⇒ (L P) (SX.RResolved c) (SC.Schema.type sc ST.⟨ τ ⟩) t SCx.zeroUsage ]
           realize⇒ sh (proj₂ w) ≡ ref d (SC.Schema.type sc ST.⟨ τ ⟩) (inline P d)
  refS d ok ne refl τ ar = _ , w-def d {ok} ne τ ar , refl

  -- …with some, checked at the instance;
  refC : (d : Fin (s P)) → OkOf P d → {c : CanonicalName} → nm P d ≡ c → ∀ {sc} (e : S P SC.!! d ≡ sc) (τ : ST.TySub (SC.Schema.arity sc) m) (r : ST.Respects (SC.Schema.kinds sc) (kinds ctx) τ)
       → 0 < SC.Schema.arity (S P SC.!! d)
       → Σ[ t ∈ SC.Tm (S P) m (size ctx) ] Σ[ w ∈ W⇐ (L P) (SX.RResolved c) (SC.Schema.type sc ST.⟨ τ ⟩) t SCx.zeroUsage ]
           realize⇐ sh (proj₂ w) ≡ ref d (SC.Schema.type sc ST.⟨ τ ⟩) (inline P d)
  refC d ok ne refl τ r pos = _ , w-poly d {ok} ne pos τ r , refl

  -- …and an arrow given its domain.
  private
    ⇒-inj : ∀ {A B C D : ST.Ty m} {k} → (A ST.⇒[ k ] B) ≡ (C ST.⇒[ k ] D) → (A ≡ C) × (B ≡ D)
    ⇒-inj refl = refl , refl

  refD : (d : Fin (s P)) → OkOf P d → {c : CanonicalName} → nm P d ≡ c → ∀ {sc} (e : S P SC.!! d ≡ sc) (τ : ST.TySub (SC.Schema.arity sc) m) (r : ST.Respects (SC.Schema.kinds sc) (kinds ctx) τ)
       → 0 < SC.Schema.arity (S P SC.!! d)
       → ∀ {X Y : ST.Ty (SC.Schema.arity (S P SC.!! d))} {A B π′ π}
       → SC.Schema.type (S P SC.!! d) ≡ X ST.⇒[ LG.mk-kind LG.Many π′ ] Y → (∀ i → ST.Occurs i Y → ST.Occurs i X)
       → SC.Schema.type sc ST.⟨ τ ⟩ ≡ A ST.⇒[ LG.mk-kind LG.Many π′ ] B → (g : π′ LG.⊑π π)
       → Σ[ t ∈ SC.Tm (S P) m (size ctx) ] Σ[ w ∈ W↦ (L P) (SX.RResolved c) A π B t SCx.zeroUsage ]
           realize↦ sh (proj₂ w) ≡ SS.coerce (sub-arr {q = LG.Many} (<:-refl A) (<:-refl B) g) (ref d (A ST.⇒[ LG.mk-kind LG.Many π′ ] B) (inline P d))
  refD d ok ne refl τ r pos te occ q g =
    let parts = ⇒-inj (trans (sym (cong (ST._⟨ τ ⟩) te)) q) in _ , w-poly↦ d {ok} ne pos te occ τ r (proj₁ parts) (proj₂ parts) g , refl

  -- A monomorphic definition is called by its name, a telescope one inlined.
  ref-call : ∀ {T : ST.Ty m} (d : Fin (s P)) {x} → inline P d ≡ false → nm P d ≡ canonical (x ∷ [])
           → ref {Γ = debruijn ctx} d T (inline P d) ≡ SS.closure x
  ref-call d e n rewrite e | n = refl

  ref-poly : ∀ {T : ST.Ty m} (d : Fin (s P)) {x} → inline P d ≡ true → nm P d ≡ canonical (x ∷ [])
           → ref {Γ = debruijn ctx} d T (inline P d) ≡ SS.poly x T
  ref-poly d e n rewrite e | n = refl

  -- A head the compiler's general application rules take is one the Spec's take.
  private
    gen-head : ∀ {g} → g ∈ SU.specialGenerators → classifyAppHead (SX.RResolved (gen g)) ≡ nothing → ⊥
    gen-head (here refl) ()
    gen-head (there (here refl)) ()
    gen-head (there (there (here refl))) ()
    gen-head (there (there (there (here refl)))) ()
    gen-head (there (there (there (there (here refl))))) ()
    gen-head (there (there (there (there (there (here refl)))))) ()
    gen-head (there (there (there (there (there (there (here refl))))))) ()
    gen-head (there (there (there (there (there (there (there (here refl)))))))) ()
    gen-head (there (there (there (there (there (there (there (there (here refl))))))))) ()
    gen-head (there (there (there (there (there (there (there (there (there (here refl)))))))))) ()
    gen-head (there (there (there (there (there (there (there (there (there (there (here refl))))))))))) ()
    gen-head (there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))) ()
    gen-head (there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))) ()
    gen-head (there (there (there (there (there (there (there (there (there (there (there (there (there ()))))))))))))) _

  not-special : ∀ {f} → classifyAppHead f ≡ nothing → ¬ SU.SpecialHead f
  not-special e (SU.sh-gen g) = gen-head g e
  not-special () SU.sh-pair
  not-special () SU.sh-compose
  not-special () SU.sh-case

  -- the Spec's classification of a binary operator the compiler classifies
  arith-of : ∀ {op} → isArithmeticOp op ≡ true → Σ[ p ∈ SC.Prim ] SU.IntArith op p
  arith-of {OpAdd} _ = _ , SU.ia-add
  arith-of {OpSub} _ = _ , SU.ia-sub
  arith-of {OpMul} _ = _ , SU.ia-mul
  arith-of {OpDiv} _ = _ , SU.ia-div
  arith-of {OpMod} _ = _ , SU.ia-mod
  arith-of {OpLt} ()
  arith-of {OpLe} ()
  arith-of {OpGt} ()
  arith-of {OpGe} ()
  arith-of {OpEq} ()
  arith-of {OpNe} ()

  float-of : ∀ {op} → isFloatArithmeticOp op ≡ true → Σ[ p ∈ SC.Prim ] SU.FloatArith op p
  float-of {OpAdd} _ = _ , SU.fa-add
  float-of {OpSub} _ = _ , SU.fa-sub
  float-of {OpMul} _ = _ , SU.fa-mul
  float-of {OpDiv} _ = _ , SU.fa-div
  float-of {OpMod} ()
  float-of {OpLt} ()
  float-of {OpLe} ()
  float-of {OpGt} ()
  float-of {OpGe} ()
  float-of {OpEq} ()
  float-of {OpNe} ()

  cmp-of : ∀ {op} → isComparisonOp op ≡ true → Σ[ p ∈ SC.Prim ] SU.Compare op p
  cmp-of {OpLt} _ = _ , SU.cmp-lt
  cmp-of {OpLe} _ = _ , SU.cmp-le
  cmp-of {OpGt} _ = _ , SU.cmp-gt
  cmp-of {OpGe} _ = _ , SU.cmp-ge
  cmp-of {OpEq} _ = _ , SU.cmp-eq
  cmp-of {OpNe} _ = _ , SU.cmp-ne
  cmp-of {OpAdd} ()
  cmp-of {OpSub} ()
  cmp-of {OpMul} ()
  cmp-of {OpDiv} ()
  cmp-of {OpMod} ()

  -- A witness, retyped along an equation.
  retype⇒ : ∀ {e A B t Ψ} → A ≡ B → W⇒ (L P) e A t Ψ → W⇒ (L P) e B t Ψ
  retype⇒ refl w = w
  retype⇐ : ∀ {e A B t Ψ} → A ≡ B → W⇐ (L P) e A t Ψ → W⇐ (L P) e B t Ψ
  retype⇐ refl w = w

  retype↦ : ∀ {e A π B B′ t Ψ} → B ≡ B′ → W↦ (L P) e A π B t Ψ → W↦ (L P) e A π B′ t Ψ
  retype↦ refl w = w

  -- …and its realization, transported along it.
  rt⇒ : ∀ {e A B t Ψ} (p : A ≡ B) (w : W⇒ (L P) e A t Ψ) → realize⇒ sh (proj₂ (retype⇒ p w)) ≡ subst (E Ψ) p (realize⇒ sh (proj₂ w))
  rt⇒ refl w = refl
  rt⇐ : ∀ {e A B t Ψ} (p : A ≡ B) (w : W⇐ (L P) e A t Ψ) → realize⇐ sh (proj₂ (retype⇐ p w)) ≡ subst (E Ψ) p (realize⇐ sh (proj₂ w))
  rt⇐ refl w = refl

  -- Transport of a term along a type equation.
  subst-K : ∀ {Ψ A} (p : A ≡ A) (x : E Ψ A) → subst (E Ψ) p x ≡ x
  subst-K refl x = refl
  subst-twice : ∀ {Ψ A B} (p q : A ≡ B) (x : E Ψ B) → subst (E Ψ) q (subst (E Ψ) (sym p) x) ≡ x
  subst-twice refl refl x = refl
  subst-poly : ∀ {A B} (p : A ≡ B) {x} → subst (E SCx.zeroUsage) p (SS.poly x A) ≡ SS.poly x B
  subst-poly refl = refl

------------------------------------------------------------------------
-- Synthesis
------------------------------------------------------------------------

-- The term former of an operator the compiler classifies.
arithE : ∀ {m n} {Γ : SCx.Ctx m n} {Ψ₁ Ψ₂} (op : BinOp) → isArithmeticOp op ≡ true
       → SExpr Γ Ψ₁ ST.Int → SExpr Γ Ψ₂ ST.Int → SExpr Γ (Ψ₁ SCx.+ᵘ Ψ₂) ST.Int
arithE OpAdd _ = SS.add
arithE OpSub _ = SS.sub
arithE OpMul _ = SS.mul
arithE OpDiv _ = SS.div
arithE OpMod _ = SS.mod'
arithE OpLt ()
arithE OpLe ()
arithE OpGt ()
arithE OpGe ()
arithE OpEq ()
arithE OpNe ()

floatE : ∀ {m n} {Γ : SCx.Ctx m n} {Ψ₁ Ψ₂} (op : BinOp) → isFloatArithmeticOp op ≡ true
       → SExpr Γ Ψ₁ ST.Float → SExpr Γ Ψ₂ ST.Float → SExpr Γ (Ψ₁ SCx.+ᵘ Ψ₂) ST.Float
floatE OpAdd _ = SS.fadd
floatE OpSub _ = SS.fsub
floatE OpMul _ = SS.fmul
floatE OpDiv _ = SS.fdiv
floatE OpMod ()
floatE OpLt ()
floatE OpLe ()
floatE OpGt ()
floatE OpGe ()
floatE OpEq ()
floatE OpNe ()

cmpE : ∀ {m n} {Γ : SCx.Ctx m n} {Ψ₁ Ψ₂} (op : BinOp) → isComparisonOp op ≡ true
     → SExpr Γ Ψ₁ ST.Int → SExpr Γ Ψ₂ ST.Int → SExpr Γ (Ψ₁ SCx.+ᵘ Ψ₂) (ST.Unit ST.+ ST.Unit)
cmpE OpLt _ = SS.lt
cmpE OpLe _ = SS.le
cmpE OpGt _ = SS.gt
cmpE OpGe _ = SS.ge
cmpE OpEq _ = SS.eq
cmpE OpNe _ = SS.ne
cmpE OpAdd ()
cmpE OpSub ()
cmpE OpMul ()
cmpE OpDiv ()
cmpE OpMod ()

-- Their references: the operands'.
refs-arithE : ∀ {m} {ctx : NamedCtx m} {Ψ₁ Ψ₂} (op : BinOp) (ia : isArithmeticOp op ≡ true) {a : SExpr (debruijn ctx) Ψ₁ ST.Int} {b : SExpr (debruijn ctx) Ψ₂ ST.Int}
            → InScope ctx a → InScope ctx b → InScope ctx (arithE op ia a b)
refs-arithE OpAdd _ ra rb = ra , rb
refs-arithE OpSub _ ra rb = ra , rb
refs-arithE OpMul _ ra rb = ra , rb
refs-arithE OpDiv _ ra rb = ra , rb
refs-arithE OpMod _ ra rb = ra , rb
refs-arithE OpLt () ra rb
refs-arithE OpLe () ra rb
refs-arithE OpGt () ra rb
refs-arithE OpGe () ra rb
refs-arithE OpEq () ra rb
refs-arithE OpNe () ra rb

refs-floatE : ∀ {m} {ctx : NamedCtx m} {Ψ₁ Ψ₂} (op : BinOp) (fa : isFloatArithmeticOp op ≡ true) {a : SExpr (debruijn ctx) Ψ₁ ST.Float} {b : SExpr (debruijn ctx) Ψ₂ ST.Float}
            → InScope ctx a → InScope ctx b → InScope ctx (floatE op fa a b)
refs-floatE OpAdd _ ra rb = ra , rb
refs-floatE OpSub _ ra rb = ra , rb
refs-floatE OpMul _ ra rb = ra , rb
refs-floatE OpDiv _ ra rb = ra , rb
refs-floatE OpMod () ra rb
refs-floatE OpLt () ra rb
refs-floatE OpLe () ra rb
refs-floatE OpGt () ra rb
refs-floatE OpGe () ra rb
refs-floatE OpEq () ra rb
refs-floatE OpNe () ra rb

refs-cmpE : ∀ {m} {ctx : NamedCtx m} {Ψ₁ Ψ₂} (op : BinOp) (c : isComparisonOp op ≡ true) {a : SExpr (debruijn ctx) Ψ₁ ST.Int} {b : SExpr (debruijn ctx) Ψ₂ ST.Int}
          → InScope ctx a → InScope ctx b → InScope ctx (cmpE op c a b)
refs-cmpE OpLt _ ra rb = ra , rb
refs-cmpE OpLe _ ra rb = ra , rb
refs-cmpE OpGt _ ra rb = ra , rb
refs-cmpE OpGe _ ra rb = ra , rb
refs-cmpE OpEq _ ra rb = ra , rb
refs-cmpE OpNe _ ra rb = ra , rb
refs-cmpE OpAdd () ra rb
refs-cmpE OpSub () ra rb
refs-cmpE OpMul () ra rb
refs-cmpE OpDiv () ra rb
refs-cmpE OpMod () ra rb

-- A local's binder adds no reference.
ext-refs : ∀ {m} {ctx : NamedCtx m} {x A} {n} {Γ : SCx.Ctx m n} {Ψ B} {e : SExpr Γ Ψ B} → InScope (extendNamedCtx ctx x A) e → InScope ctx e
ext-refs r = r

-- An embedded morphism, retyped, is as call-free.
private
  Linked-substˡ : ∀ {X Y Z : IRTy} (eq : X ≡ Y) (ir : IR X Z) → Linked [] [] ir → Linked [] [] (subst (λ o → IR o Z) eq ir)
  Linked-substˡ refl ir l = l

  Linked-substʳ : ∀ {X Y Z : IRTy} (eq : Y ≡ Z) (ir : IR X Y) → Linked [] [] ir → Linked [] [] (subst (λ o → IR X o) eq ir)
  Linked-substʳ refl ir l = l

module _ {m} {ctx : NamedCtx m} (P : Pack ctx) where
  open At P

  -- The realization of an operator's rule is its term former.
  rz-arith : ∀ {op e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} (ia : isArithmeticOp op ≡ true)
             (w₁ : W⇒ (L P) e₁ ST.Int t₁ Ψ₁) (w₂ : W⇒ (L P) e₂ ST.Int t₂ Ψ₂)
           → realize⇒ sh (proj₂ (w-arith (proj₂ (arith-of ia)) w₁ w₂)) ≡ arithE op ia (realize⇒ sh (proj₂ w₁)) (realize⇒ sh (proj₂ w₂))
  rz-arith {OpAdd} ia w₁ w₂ = refl
  rz-arith {OpSub} ia w₁ w₂ = refl
  rz-arith {OpMul} ia w₁ w₂ = refl
  rz-arith {OpDiv} ia w₁ w₂ = refl
  rz-arith {OpMod} ia w₁ w₂ = refl
  rz-arith {OpLt} () w₁ w₂
  rz-arith {OpLe} () w₁ w₂
  rz-arith {OpGt} () w₁ w₂
  rz-arith {OpGe} () w₁ w₂
  rz-arith {OpEq} () w₁ w₂
  rz-arith {OpNe} () w₁ w₂

  rz-float : ∀ {op e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} (fa : isFloatArithmeticOp op ≡ true)
             (w₁ : W⇒ (L P) e₁ ST.Float t₁ Ψ₁) (w₂ : W⇒ (L P) e₂ ST.Float t₂ Ψ₂)
           → realize⇒ sh (proj₂ (w-arith-float (proj₂ (float-of fa)) w₁ w₂)) ≡ floatE op fa (realize⇒ sh (proj₂ w₁)) (realize⇒ sh (proj₂ w₂))
  rz-float {OpAdd} fa w₁ w₂ = refl
  rz-float {OpSub} fa w₁ w₂ = refl
  rz-float {OpMul} fa w₁ w₂ = refl
  rz-float {OpDiv} fa w₁ w₂ = refl
  rz-float {OpMod} () w₁ w₂
  rz-float {OpLt} () w₁ w₂
  rz-float {OpLe} () w₁ w₂
  rz-float {OpGt} () w₁ w₂
  rz-float {OpGe} () w₁ w₂
  rz-float {OpEq} () w₁ w₂
  rz-float {OpNe} () w₁ w₂

  rz-float-il : ∀ {op e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} (fa : isFloatArithmeticOp op ≡ true)
                (w₁ : W⇒ (L P) e₁ ST.Int t₁ Ψ₁) (w₂ : W⇒ (L P) e₂ ST.Float t₂ Ψ₂)
              → realize⇒ sh (proj₂ (w-arith-float-il (proj₂ (float-of fa)) w₁ w₂))
                ≡ floatE op fa (SS.i2f (realize⇒ sh (proj₂ w₁))) (realize⇒ sh (proj₂ w₂))
  rz-float-il {OpAdd} fa w₁ w₂ = refl
  rz-float-il {OpSub} fa w₁ w₂ = refl
  rz-float-il {OpMul} fa w₁ w₂ = refl
  rz-float-il {OpDiv} fa w₁ w₂ = refl
  rz-float-il {OpMod} () w₁ w₂
  rz-float-il {OpLt} () w₁ w₂
  rz-float-il {OpLe} () w₁ w₂
  rz-float-il {OpGt} () w₁ w₂
  rz-float-il {OpGe} () w₁ w₂
  rz-float-il {OpEq} () w₁ w₂
  rz-float-il {OpNe} () w₁ w₂

  rz-float-ir : ∀ {op e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} (fa : isFloatArithmeticOp op ≡ true)
                (w₁ : W⇒ (L P) e₁ ST.Float t₁ Ψ₁) (w₂ : W⇒ (L P) e₂ ST.Int t₂ Ψ₂)
              → realize⇒ sh (proj₂ (w-arith-float-ir (proj₂ (float-of fa)) w₁ w₂))
                ≡ floatE op fa (realize⇒ sh (proj₂ w₁)) (SS.i2f (realize⇒ sh (proj₂ w₂)))
  rz-float-ir {OpAdd} fa w₁ w₂ = refl
  rz-float-ir {OpSub} fa w₁ w₂ = refl
  rz-float-ir {OpMul} fa w₁ w₂ = refl
  rz-float-ir {OpDiv} fa w₁ w₂ = refl
  rz-float-ir {OpMod} () w₁ w₂
  rz-float-ir {OpLt} () w₁ w₂
  rz-float-ir {OpLe} () w₁ w₂
  rz-float-ir {OpGt} () w₁ w₂
  rz-float-ir {OpGe} () w₁ w₂
  rz-float-ir {OpEq} () w₁ w₂
  rz-float-ir {OpNe} () w₁ w₂

  rz-cmp : ∀ {op e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} (c : isComparisonOp op ≡ true)
           (w₁ : W⇒ (L P) e₁ ST.Int t₁ Ψ₁) (w₂ : W⇒ (L P) e₂ ST.Int t₂ Ψ₂)
         → realize⇒ sh (proj₂ (w-compare (proj₂ (cmp-of c)) w₁ w₂)) ≡ cmpE op c (realize⇒ sh (proj₂ w₁)) (realize⇒ sh (proj₂ w₂))
  rz-cmp {OpLt} c w₁ w₂ = refl
  rz-cmp {OpLe} c w₁ w₂ = refl
  rz-cmp {OpGt} c w₁ w₂ = refl
  rz-cmp {OpGe} c w₁ w₂ = refl
  rz-cmp {OpEq} c w₁ w₂ = refl
  rz-cmp {OpNe} c w₁ w₂ = refl
  rz-cmp {OpAdd} () w₁ w₂
  rz-cmp {OpSub} () w₁ w₂
  rz-cmp {OpMul} () w₁ w₂
  rz-cmp {OpDiv} () w₁ w₂
  rz-cmp {OpMod} () w₁ w₂

private
  cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (f : A → B → C → D)
        {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
  cong₃ f refl refl refl = refl

module _ {m} {ctx : NamedCtx m} where

  private
    E = SExpr (debruijn ctx)

  wt-int : (n : ℤ) → WI ctx (SX.RInt n) ST.Int SCx.zeroUsage (SS.int n)
  wt-int n = tt , λ P → let open At P in _ , w-int n , refl

  wt-float : ∀ i f l → WI ctx (SX.RFloat i f l) ST.Float SCx.zeroUsage (SS.float (decimalOf i f l))
  wt-float i f l = tt , λ P → let open At P in _ , w-float i f l , refl

  wt-unit : WI ctx SX.RUnit ST.Unit SCx.zeroUsage SS.unit
  wt-unit = tt , λ P → let open At P in _ , w-unit , refl

  wt-unit-var : WI ctx (SX.RResolved (gen "unit")) ST.Unit SCx.zeroUsage SS.unit
  wt-unit-var = tt , λ P → let open At P in _ , w-unit-g , refl

  wt-var-local : ∀ {x A Ψ} {eV : Once.Internal.Context.SVar (debruijn ctx) Ψ A}
               → lookupLocal ctx x ≡ just (A , Ψ , eV) → WI ctx (SX.RVar x) A Ψ (SS.svar→expr eV)
  wt-var-local {eV = svar i} lk = tt , λ P → let open At P in _ , w-var (found (lr P) i lk) , subst-K _ _

  wt-var-resolved : ∀ {cn T A} → Once.Spec.Name.NotGenerator cn → WordName cn
                  → lookupImport (sig ctx) (showCanonical cn) ≡ just T → (k : IsConcrete T) → (eq : A ≡ wk₀ T)
                  → WI ctx (SX.RResolved cn) A SCx.zeroUsage (subst (E SCx.zeroUsage) (sym eq) (SS.sigOp cn k))
  wt-var-resolved {cn} {T} ng wn lk k refl = lk , λ P → res P (TView.View.declares (V P) lk)
    where
      res : (P : Pack ctx) → TView.Declared (Sg P) (S P) (showCanonical cn) T
          → Σ[ t ∈ SC.Tm (S P) _ (size ctx) ] Σ[ w ∈ WM.W⇒ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (L P) (SX.RResolved cn) (wk₀ T) t SCx.zeroUsage ]
              rz⇒ P w ≡ SS.sigOp cn k
      res P (TView.declared h mem) =
        let open At P in
        let p = ⌜declS⌝ k h
            w = w-sigop {ok = lk} ng (mem wn refl) k h
        in _ , retype⇒ p w , trans (rt⇒ p w) (subst-twice (⌜declS⌝ k h) p _)

  wt-var-own : ∀ {x T A} → lookupImport (sig ctx) x ≡ nothing → (lk : lookupImport (imports ctx) x ≡ just T) → (eq : A ≡ wk₀ T)
             → WI ctx (SX.RResolved (own x)) A SCx.zeroUsage (subst (E SCx.zeroUsage) (sym eq) (SS.closure x))
  wt-var-own ns lk refl = (_ , lk , refl) , λ P → let open At P in
    let d = TView.ImportAt.entryOf (TView.View.imported (V P) lk)
        (t , w , r) = (refS d (TView.iv-imp lk refl) (h-imp P lk) (TView.ImportAt.mono (TView.View.imported (V P) lk)) none
                            (cong SC.Schema.arity (TView.ImportAt.mono (TView.View.imported (V P) lk))))
    in t , w , trans r (ref-call d (h-imp-call P lk) (h-imp P lk))

  wt-var-poly-instantiate-infer : ∀ {x T sc body prefix} {g : TP.Ground sc}
                                → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
                                → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix))
                                → TP.Ground sc → T ≡ TP.extractGround sc g
                                → WI ctx (SX.RResolved (own x)) T SCx.zeroUsage (SS.poly x T)
  wt-var-poly-instantiate-infer {sc = sc} {g = g} _ _ lp _ eq = (_ , lp , subst (KindedInstance (kinds ctx) sc) (sym eq) (ground-kinded {Δ = kinds ctx} sc g)) , λ P → let open At P in
    let ki = kinded-instance sc (ground-kinded {Δ = kinds ctx} sc g)
        d = TView.View.entry (V P) lp
        (t , w , r) = (refS d (TView.iv-poly lp refl) (h-poly P lp) (TView.View.entryIs (V P) lp) (proj₁ ki) (h-ground P lp g))
        p = trans (proj₂ (proj₂ ki)) (sym eq)
    in t , retype⇒ p w
       , trans (rt⇒ p w) (trans (cong (subst (E SCx.zeroUsage) p) (trans r (ref-poly d (h-poly-inline P lp) (h-poly P lp)))) (subst-poly p))

  wt-annot : ∀ {e T A Ψ eE} → WC ctx e A Ψ eE → A ≡ wk₀ T → WI ctx (SX.RAnnot e T) A Ψ eE
  wt-annot {T = T} w refl = proj₁ w , λ P → let open At P in
    let a = wk₀≡↑ T
        (_ , w′ , r) = proj₂ w P
    in _ , retype⇒ (sym a) (w-annot (retype⇐ a w′))
       , trans (rt⇒ (sym a) (w-annot (retype⇐ a w′))) (trans (cong (subst (E _) (sym a)) (rt⇐ a w′)) (trans (subst-back a _) r))
    where
      subst-back : ∀ {Ψ A B} (p : A ≡ B) (x : E Ψ A) → subst (E Ψ) (sym p) (subst (E Ψ) p x) ≡ x
      subst-back refl x = refl

  wt-pair : ∀ {a b A B Ψ₁ Ψ₂ aE bE} → WI ctx a A Ψ₁ aE → WI ctx b B Ψ₂ bE
          → WI ctx (SX.RPair a b) (A ST.* B) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.pair aE bE)
  wt-pair wa wb = (proj₁ wa , proj₁ wb) , λ P → let open At P in
    let (_ , ua , ra) = proj₂ wa P ; (_ , ub , rb) = proj₂ wb P in _ , w-pair ua ub , cong₂ SS.pair ra rb

  wt-neg : ∀ {e Ψ eE} → WI ctx e ST.Int Ψ eE → WI ctx (SX.RNeg e) ST.Int Ψ (SS.neg eE)
  wt-neg w = proj₁ w , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-neg u , cong SS.neg r

  wt-neg-float : ∀ i f l → WI ctx (SX.RNeg (SX.RFloat i f l)) ST.Float SCx.zeroUsage (SS.float (negate (decimalOf i f l)))
  wt-neg-float i f l = tt , λ P → let open At P in _ , w-neg-float i f l , refl

  wt-let : ∀ {x e₁ e₂ A B q Ψ₁ Ψ₂ e₁E e₂E} → WI ctx e₁ A Ψ₁ e₁E → WI (extendNamedCtx ctx x A) e₂ B (q SCx.∷ Ψ₂) e₂E
         → WI ctx (SX.RLet x e₁ e₂) B (Ψ₂ SCx.+ᵘ (q SCx.*ᵘ Ψ₁)) (SS.let' e₁E e₂E)
  wt-let {x = x} {A = A} {q = q} {e₂E = e₂E} w₁ w₂ = (proj₁ w₁ , ext-refs {ctx = ctx} {x = x} {A = A} {e = e₂E} (proj₁ w₂)) , λ P → let open At P in
    let (_ , u₁ , r₁) = proj₂ w₁ P ; (_ , u₂ , r₂) = proj₂ w₂ (pack▸ x A P) in _ , w-let q u₁ u₂ , cong₂ SS.let' r₁ r₂

  wt-case : ∀ {e xl el xr er A B Cl Cr C ql qr Ψs Ψₗ Ψᵣ sE lE rE}
          → WI ctx e (A ST.+ B) Ψs sE → WI (extendNamedCtx ctx xl A) el Cl (ql SCx.∷ Ψₗ) lE
          → WI (extendNamedCtx ctx xr B) er Cr (qr SCx.∷ Ψᵣ) rE
          → (j : Cl ⊔ Cr ≔ C)
          → WI ctx (SX.RDestruct e xl el xr er) C (Ψs SCx.+ᵘ (Ψₗ ⊔ᵘ Ψᵣ))
               (SS.case' sE (SS.coerce (<:ᶜ⇒<: (left j)) lE) (SS.coerce (<:ᶜ⇒<: (right j)) rE))
  wt-case {xl = xl} {xr = xr} {A = A} {B = B} {ql = ql} {qr = qr} {lE = lE} {rE = rE} ws wl wr j = (proj₁ ws , ext-refs {ctx = ctx} {x = xl} {A = A} {e = lE} (proj₁ wl) , ext-refs {ctx = ctx} {x = xr} {A = B} {e = rE} (proj₁ wr)) , λ P → let open At P in
    let (_ , us , rs) = proj₂ ws P ; (_ , ul , rl) = proj₂ wl (pack▸ xl A P) ; (_ , ur , rr) = proj₂ wr (pack▸ xr B P)
    in _ , w-case ql qr us ul ur j
       , cong₃ (λ a b c → SS.case' a (SS.coerce (<:ᶜ⇒<: (left j)) b) (SS.coerce (<:ᶜ⇒<: (right j)) c)) rs rl rr

  wt-binop-arith : ∀ {op e₁ e₂ Ψ₁ Ψ₂ e₁E e₂E} → (ia : isArithmeticOp op ≡ true) → WI ctx e₁ ST.Int Ψ₁ e₁E → WI ctx e₂ ST.Int Ψ₂ e₂E
                 → WI ctx (SX.RBinOp op e₁ e₂) ST.Int (Ψ₁ SCx.+ᵘ Ψ₂) (arithE op ia e₁E e₂E)
  wt-binop-arith {op} ia w₁ w₂ = refs-arithE {ctx = ctx} op ia (proj₁ w₁) (proj₁ w₂) , λ P → let open At P in
    let (_ , u₁ , r₁) = proj₂ w₁ P ; (_ , u₂ , r₂) = proj₂ w₂ P
    in _ , w-arith (proj₂ (arith-of ia)) u₁ u₂ , trans (rz-arith P ia u₁ u₂) (cong₂ (arithE op ia) r₁ r₂)

  wt-binop-arith-float : ∀ {op e₁ e₂ Ψ₁ Ψ₂ e₁E e₂E} → (fa : isFloatArithmeticOp op ≡ true) → WI ctx e₁ ST.Float Ψ₁ e₁E → WI ctx e₂ ST.Float Ψ₂ e₂E
                       → WI ctx (SX.RBinOp op e₁ e₂) ST.Float (Ψ₁ SCx.+ᵘ Ψ₂) (floatE op fa e₁E e₂E)
  wt-binop-arith-float {op} fa w₁ w₂ = refs-floatE {ctx = ctx} op fa (proj₁ w₁) (proj₁ w₂) , λ P → let open At P in
    let (_ , u₁ , r₁) = proj₂ w₁ P ; (_ , u₂ , r₂) = proj₂ w₂ P
    in _ , w-arith-float (proj₂ (float-of fa)) u₁ u₂ , trans (rz-float P fa u₁ u₂) (cong₂ (floatE op fa) r₁ r₂)

  wt-binop-arith-float-il : ∀ {op e₁ e₂ Ψ₁ Ψ₂ e₁E e₂E} → (fa : isFloatArithmeticOp op ≡ true) → WI ctx e₁ ST.Int Ψ₁ e₁E → WI ctx e₂ ST.Float Ψ₂ e₂E
                          → WI ctx (SX.RBinOp op e₁ e₂) ST.Float (Ψ₁ SCx.+ᵘ Ψ₂) (floatE op fa (SS.i2f e₁E) e₂E)
  wt-binop-arith-float-il {op} fa w₁ w₂ = refs-floatE {ctx = ctx} op fa (proj₁ w₁) (proj₁ w₂) , λ P → let open At P in
    let (_ , u₁ , r₁) = proj₂ w₁ P ; (_ , u₂ , r₂) = proj₂ w₂ P
    in _ , w-arith-float-il (proj₂ (float-of fa)) u₁ u₂ , trans (rz-float-il P fa u₁ u₂) (cong₂ (λ a b → floatE op fa (SS.i2f a) b) r₁ r₂)

  wt-binop-arith-float-ir : ∀ {op e₁ e₂ Ψ₁ Ψ₂ e₁E e₂E} → (fa : isFloatArithmeticOp op ≡ true) → WI ctx e₁ ST.Float Ψ₁ e₁E → WI ctx e₂ ST.Int Ψ₂ e₂E
                          → WI ctx (SX.RBinOp op e₁ e₂) ST.Float (Ψ₁ SCx.+ᵘ Ψ₂) (floatE op fa e₁E (SS.i2f e₂E))
  wt-binop-arith-float-ir {op} fa w₁ w₂ = refs-floatE {ctx = ctx} op fa (proj₁ w₁) (proj₁ w₂) , λ P → let open At P in
    let (_ , u₁ , r₁) = proj₂ w₁ P ; (_ , u₂ , r₂) = proj₂ w₂ P
    in _ , w-arith-float-ir (proj₂ (float-of fa)) u₁ u₂ , trans (rz-float-ir P fa u₁ u₂) (cong₂ (λ a b → floatE op fa a (SS.i2f b)) r₁ r₂)

  wt-binop-cmp : ∀ {op e₁ e₂ Ψ₁ Ψ₂ e₁E e₂E} → (c : isComparisonOp op ≡ true) → WI ctx e₁ ST.Int Ψ₁ e₁E → WI ctx e₂ ST.Int Ψ₂ e₂E
               → WI ctx (SX.RBinOp op e₁ e₂) (ST.Unit ST.+ ST.Unit) (Ψ₁ SCx.+ᵘ Ψ₂) (cmpE op c e₁E e₂E)
  wt-binop-cmp {op} c w₁ w₂ = refs-cmpE {ctx = ctx} op c (proj₁ w₁) (proj₁ w₂) , λ P → let open At P in
    let (_ , u₁ , r₁) = proj₂ w₁ P ; (_ , u₂ , r₂) = proj₂ w₂ P
    in _ , w-compare (proj₂ (cmp-of c)) u₁ u₂ , trans (rz-cmp P c u₁ u₂) (cong₂ (cmpE op c) r₁ r₂)

  -- A generator applied to a synthesizing argument.
  wt-id-app : ∀ {e T Ψ eE} → WI ctx e T Ψ eE
            → WI ctx (SX.RApp (SX.RResolved (gen "id")) e) T (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app IR.id eE)
  wt-id-app w = (tt , proj₁ w) , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-id-app u , cong (SS.morph-app IR.id) r

  wt-fst-app : ∀ {e A B Ψ eE} → WI ctx e (A ST.* B) Ψ eE
             → WI ctx (SX.RApp (SX.RResolved (gen "fst")) e) A (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app IR.fst eE)
  wt-fst-app w = (tt , proj₁ w) , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-fst-app u , cong (SS.morph-app IR.fst) r

  wt-snd-app : ∀ {e A B Ψ eE} → WI ctx e (A ST.* B) Ψ eE
             → WI ctx (SX.RApp (SX.RResolved (gen "snd")) e) B (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app IR.snd eE)
  wt-snd-app w = (tt , proj₁ w) , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-snd-app u , cong (SS.morph-app IR.snd) r

  wt-terminal-app : ∀ {e T Ψ eE} → WI ctx e T Ψ eE
                  → WI ctx (SX.RApp (SX.RResolved (gen "terminal")) e) ST.Unit (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app IR.terminal eE)
  wt-terminal-app w = (tt , proj₁ w) , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-terminal-app u , cong (SS.morph-app IR.terminal) r

  wt-apply-app-infer : ∀ {e A B Ψ eE} → WI ctx e ((A ST.⇒[ LG.mk-kind LG.Many LG.pure ] B) ST.* A) Ψ eE
                     → WI ctx (SX.RApp (SX.RResolved (gen "apply")) e) B (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app IR.apply eE)
  wt-apply-app-infer w = (tt , proj₁ w) , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-apply-app u , cong (SS.morph-app IR.apply) r

  wt-apply-eff-app-infer : ∀ {e A B Ψ π eE} {g : LG.EffGrade π} → WI ctx e ((A ST.⇒[ LG.mk-kind LG.Many π ] B) ST.* A) Ψ eE
                         → WI ctx (SX.RApp (SX.RResolved (gen "apply")) e) (ST.Unit ST.⇒[ LG.mk-kind LG.Many π ] B)
                              (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app (IR.curry (IR.apply IR.∘ IR.fst)) eE)
  wt-apply-eff-app-infer {g = g} w = ((tt , tt) , proj₁ w) , λ P → let open At P in
    let (_ , u , r) = proj₂ w P in _ , w-apply-eff-app g u , cong (SS.morph-app (IR.curry (IR.apply IR.∘ IR.fst))) r

  wt-Out-app-infer : ∀ {e F C Ψ eE} → (wf : ST.WFFun (kinds ctx) F) → (ce : ST.⟦ F ⟧F (ST.ν F LG.pureᶠ) ≡ C) → WI ctx e (ST.ν F LG.pureᶠ) Ψ eE
                   → WI ctx (SX.RApp (SX.RResolved (gen "Out")) e) C (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
                        (subst (E _) ce (SS.morph-app (subst (λ o → IR ⌊ ST.ν F LG.pureᶠ ⌋ o) (sym (⌊⟧T-commute F (ST.ν F LG.pureᶠ))) (IR.Out (wf-⌊⌋ wf))) eE))
  wt-Out-app-infer {F = F} wf refl w = (Linked-substʳ (sym (⌊⟧T-commute F (ST.ν F LG.pureᶠ))) (IR.Out (wf-⌊⌋ wf)) tt , proj₁ w) , λ P → let open At P in
    let (_ , u , r) = proj₂ w P
    in _ , w-Out-app wf u
       , cong (SS.morph-app (subst (λ o → IR ⌊ ST.ν F LG.pureᶠ ⌋ o) (sym (⌊⟧T-commute F (ST.ν F LG.pureᶠ))) (IR.Out (wf-⌊⌋ wf)))) r

  wt-Out-eff-app-infer : ∀ {e F C Ψ eE} → (wf : ST.WFFun (kinds ctx) F) → (ce : ST.⟦ F ⟧F (ST.ν F LG.actᶠ) ≡ C) → WI ctx e (ST.ν F LG.actᶠ) Ψ eE
                       → WI ctx (SX.RApp (SX.RResolved (gen "Out")) e) (ST.Unit ST.⇒[ LG.mk-kind LG.Many LG.act ] C)
                            (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
                            (subst (λ X → E _ (ST.Unit ST.⇒[ LG.mk-kind LG.Many LG.act ] X)) ce
                              (SS.morph-app (IR.curry (subst (λ o → IR ⌊ ST.ν F LG.actᶠ ⌋ o) (sym (⌊⟧T-commute F (ST.ν F LG.actᶠ))) (IR.Out (wf-⌊⌋ wf)) IR.∘ IR.fst)) eE))
  wt-Out-eff-app-infer {F = F} wf refl w = ((Linked-substʳ (sym (⌊⟧T-commute F (ST.ν F LG.actᶠ))) (IR.Out (wf-⌊⌋ wf)) tt , tt) , proj₁ w) , λ P → let open At P in
    let (_ , u , r) = proj₂ w P
    in _ , w-Out-act-app wf u
       , cong (SS.morph-app (IR.curry (subst (λ o → IR ⌊ ST.ν F LG.actᶠ ⌋ o) (sym (⌊⟧T-commute F (ST.ν F LG.actᶠ))) (IR.Out (wf-⌊⌋ wf)) IR.∘ IR.fst))) r

  -- Application: the head's type synthesized, the argument checked.
  wt-app : ∀ {f x A B q Ψ₁ Ψ₂ fE xE} → classifyAppHead f ≡ nothing
         → WI ctx f (A ST.⇒[ LG.mk-kind q LG.pure ] B) Ψ₁ fE → WC ctx x A Ψ₂ xE
         → WI ctx (SX.RApp f x) B (Ψ₁ SCx.+ᵘ (q SCx.*ᵘ Ψ₂)) (SS.app fE xE)
  wt-app nh wf wx = (proj₁ wf , proj₁ wx) , λ P → let open At P in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ux , rx) = proj₂ wx P in _ , w-app (not-special nh) uf ux , cong₂ SS.app rf rx

  wt-effApp : ∀ {f x A B Ψ₁ Ψ₂ π fE xE} {g : LG.EffGrade π} → classifyAppHead f ≡ nothing
            → WI ctx f (A ST.⇒[ LG.mk-kind LG.Many π ] B) Ψ₁ fE → WC ctx x A Ψ₂ xE
            → WI ctx (SX.RApp f x) (ST.Unit ST.⇒[ LG.mk-kind LG.Many π ] B) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) (SS.effApp {g = g} fE xE)
  wt-effApp {g = g} nh wf wx = (proj₁ wf , proj₁ wx) , λ P → let open At P in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ux , rx) = proj₂ wx P in _ , w-effApp (not-special nh) g uf ux , cong₂ (SS.effApp {g = g}) rf rx

  -- …or the argument's type synthesized and the head checked from that domain.
  wt-app-spine : ∀ {f x X T Ψ₁ Ψ₂ fE xE} → classifyAppHead f ≡ nothing
               → WI ctx x X Ψ₂ xE → WD ctx f X LG.pure T Ψ₁ fE
               → WI ctx (SX.RApp f x) T (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) (SS.app fE xE)
  wt-app-spine nh wx wf = (proj₁ wf , proj₁ wx) , λ P → let open At P in
    let (_ , ux , rx) = proj₂ wx P ; (_ , uf , rf) = proj₂ wf P in _ , w-app-spine (not-special nh) ux uf , cong₂ SS.app rf rx

------------------------------------------------------------------------
-- Checking
------------------------------------------------------------------------

module _ {m} {ctx : NamedCtx m} where

  private
    _⇒⟨_⟩_ : ST.Ty m → LG.Purity → ST.Ty m → ST.Ty m
    A ⇒⟨ π ⟩ B = A ST.⇒[ LG.mk-kind LG.Many π ] B
    infixr 30 _⇒⟨_⟩_
    Z = SCx.zeroUsage {size ctx}
    gn : String → SX.Expr
    gn g = SX.RResolved (gen g)
    E = SExpr (debruijn ctx)

  -- The generators as morphisms, at any grade.
  wt-id-check : ∀ {T π} {u : LG.pure LG.⊑π π} → WC ctx (gn "id") (T ⇒⟨ π ⟩ T) Z (SS.lift-morphism IR.id)
  wt-id-check = tt , λ P → let open At P in _ , w-id , refl
  wt-fst-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → WC ctx (gn "fst") ((A ST.* B) ⇒⟨ π ⟩ A) Z (SS.lift-morphism IR.fst)
  wt-fst-check = tt , λ P → let open At P in _ , w-fst , refl
  wt-snd-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → WC ctx (gn "snd") ((A ST.* B) ⇒⟨ π ⟩ B) Z (SS.lift-morphism IR.snd)
  wt-snd-check = tt , λ P → let open At P in _ , w-snd , refl
  wt-terminal-morph-check : ∀ {A π} {u : LG.pure LG.⊑π π} → WC ctx (gn "terminal") (A ⇒⟨ π ⟩ ST.Unit) Z (SS.lift-morphism IR.terminal)
  wt-terminal-morph-check = tt , λ P → let open At P in _ , w-terminal , refl
  wt-initial-morph-check : ∀ {A π} {u : LG.pure LG.⊑π π} → WC ctx (gn "initial") (ST.Void ⇒⟨ π ⟩ A) Z (SS.lift-morphism IR.initial)
  wt-initial-morph-check = tt , λ P → let open At P in _ , w-initial , refl
  wt-inl-morph-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → WC ctx (gn "inl") (A ⇒⟨ π ⟩ (A ST.+ B)) Z (SS.lift-morphism IR.inl)
  wt-inl-morph-check = tt , λ P → let open At P in _ , w-inl , refl
  wt-inr-morph-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → WC ctx (gn "inr") (B ⇒⟨ π ⟩ (A ST.+ B)) Z (SS.lift-morphism IR.inr)
  wt-inr-morph-check = tt , λ P → let open At P in _ , w-inr , refl

  -- `compose f g`: `g`'s codomain from its domain, or `f`'s type synthesized.
  wt-compose-check-g : ∀ {f g A B C π Ψ₁ Ψ₂ fE gE} → WD ctx g A π B Ψ₂ gE → WC ctx f (B ⇒⟨ π ⟩ C) Ψ₁ fE
                     → WC ctx (SX.RApp (SX.RApp (gn "compose") f) g) (A ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) (SS.comp' fE gE)
  wt-compose-check-g wg wf = (proj₁ wf , proj₁ wg) , λ P → let open At P in
    let (_ , ug , rg) = proj₂ wg P ; (_ , uf , rf) = proj₂ wf P in _ , w-compose-g ug uf , cong₂ SS.comp' rf rg

  wt-compose-check-f : ∀ {f g A B C C′ π π′ Ψ₁ Ψ₂ fE gE} → WI ctx f (B ⇒⟨ π′ ⟩ C′) Ψ₁ fE → (p : (B ⇒⟨ π′ ⟩ C′) <: (B ⇒⟨ π ⟩ C))
                     → WC ctx g (A ⇒⟨ π ⟩ B) Ψ₂ gE
                     → WC ctx (SX.RApp (SX.RApp (gn "compose") f) g) (A ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) (SS.comp' (SS.coerce p fE) gE)
  wt-compose-check-f wf p wg = (proj₁ wf , proj₁ wg) , λ P → let open At P in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P in _ , w-compose-f uf p ug , cong₂ (λ a b → SS.comp' (SS.coerce p a) b) rf rg

  wt-case-copair-check : ∀ {f g A B C π Ψ₁ Ψ₂ fE gE} → WC ctx f (A ⇒⟨ π ⟩ C) Ψ₁ fE → WC ctx g (B ⇒⟨ π ⟩ C) Ψ₂ gE
                       → WC ctx (SX.RApp (SX.RApp (gn "case") f) g) ((A ST.+ B) ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.copair' fE gE)
  wt-case-copair-check wf wg = (proj₁ wf , proj₁ wg) , λ P → let open At P in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P in _ , w-case′ uf ug , cong₂ SS.copair' rf rg

  wt-pair-morph-check : ∀ {f g A B C π Ψ₁ Ψ₂ fE gE} → WC ctx f (A ⇒⟨ π ⟩ B) Ψ₁ fE → WC ctx g (A ⇒⟨ π ⟩ C) Ψ₂ gE
                      → WC ctx (SX.RApp (SX.RApp (gn "pair") f) g) (A ⇒⟨ π ⟩ (B ST.* C)) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.fork' fE gE)
  wt-pair-morph-check wf wg = (proj₁ wf , proj₁ wg) , λ P → let open At P in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P in _ , w-pair′ uf ug , cong₂ SS.fork' rf rg

  wt-curry-check : ∀ {f A B C π₀ π Ψ eE} {u : LG.pure LG.⊑π π₀} → WC ctx f ((A ST.* B) ⇒⟨ π ⟩ C) Ψ eE
                 → WC ctx (SX.RApp (gn "curry") f) (A ⇒⟨ π₀ ⟩ (B ⇒⟨ π ⟩ C)) Ψ (SS.curry' eE)
  wt-curry-check w = proj₁ w , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-curry u , cong SS.curry' r

  wt-cata-check : ∀ {alg F A π Ψ eE} {u : LG.pure LG.⊑π π} → (wf : ST.WFFun (kinds ctx) F) → WC ctx alg (ST.⟦ F ⟧F A ⇒⟨ π ⟩ A) Ψ eE
                → WC ctx (SX.RApp (gn "cata") alg) (ST.μ F ⇒⟨ π ⟩ A) (LG.Many SCx.*ᵘ Ψ) (SS.cata wf eE)
  wt-cata-check wf w = proj₁ w , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-cata wf u , cong (SS.cata wf) r

  wt-ana-check : ∀ {c F A π₀ φ Ψ eE} {u : LG.pure LG.⊑π π₀} {ua : π₀ LG.⊑π LG.act} → (wf : ST.WFFun (kinds ctx) F)
               → WC ctx c (A ⇒⟨ LG.fin φ ⟩ ST.⟦ F ⟧F A) Ψ eE
               → WC ctx (SX.RApp (gn "ana") c) (A ⇒⟨ π₀ ⟩ ST.ν F φ) (LG.Many SCx.*ᵘ Ψ) (SS.ana wf eE)
  wt-ana-check {ua = ua} wf w = proj₁ w , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-ana ua wf u , cong (SS.ana wf) r

  wt-loop-check : ∀ {c A B Ψ eE} → WC ctx c (A ⇒⟨ LG.act ⟩ (B ST.+ A)) Ψ eE
                → WC ctx (SX.RApp (gn "ana") c) (A ⇒⟨ LG.eff ⟩ B) (LG.Many SCx.*ᵘ Ψ) (SS.loop eE)
  wt-loop-check w = proj₁ w , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-loop u , cong SS.loop r

  -- A synthesized type where a supertype is expected: its conversion.
  wt-sub : ∀ {e A B Ψ eE} → WI ctx e A Ψ eE → (p : A <: B) → WC ctx e B Ψ (SS.coerce p eE)
  wt-sub w p = proj₁ w , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-sub u p , cong (SS.coerce p) r

  wt-lam : ∀ {x body A B q q′ π Ψ eE} {u : LG.pure LG.⊑π π} → (≤p : (q′ ≤qᵇ q) ≡ true)
         → WC (extendNamedCtx ctx x A) body B (q′ SCx.∷ Ψ) eE
         → WC ctx (SX.RLam x body) (A ST.⇒[ LG.mk-kind q π ] B) Ψ (SS.lam q ≤p eE)
  wt-lam {x = x} {A = A} {eE = eE} ≤p w = ext-refs {ctx = ctx} {x = x} {A = A} {e = eE} (proj₁ w) , λ P → let open At P in
    let (_ , u , r) = proj₂ w (pack▸ x A P) in _ , w-lam ≤p u , cong (SS.lam _ ≤p) r

  wt-pair-lit-check : ∀ {a b A B Ψ₁ Ψ₂ aE bE} → WC ctx a A Ψ₁ aE → WC ctx b B Ψ₂ bE
                    → WC ctx (SX.RPair a b) (A ST.* B) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.pair aE bE)
  wt-pair-lit-check wa wb = (proj₁ wa , proj₁ wb) , λ P → let open At P in
    let (_ , ua , ra) = proj₂ wa P ; (_ , ub , rb) = proj₂ wb P in _ , w-pair-lit ua ub , cong₂ SS.pair ra rb

  wt-In-app-check : ∀ {e F Ψ eE} → (wf : ST.WFFun (kinds ctx) F) → WC ctx e (ST.⟦ F ⟧F (ST.μ F)) Ψ eE
                  → WC ctx (SX.RApp (gn "In") e) (ST.μ F) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
                       (SS.morph-app (subst (λ o → IR o ⌊ ST.μ F ⌋) (sym (⌊⟧T-commute F (ST.μ F))) (IR.In (wf-⌊⌋ wf))) eE)
  wt-In-app-check {F = F} wf w = (Linked-substˡ (sym (⌊⟧T-commute F (ST.μ F))) (IR.In (wf-⌊⌋ wf)) tt , proj₁ w) , λ P → let open At P in
    let (_ , u , r) = proj₂ w P
    in _ , w-In-app wf u , cong (SS.morph-app (subst (λ o → IR o ⌊ ST.μ F ⌋) (sym (⌊⟧T-commute F (ST.μ F))) (IR.In (wf-⌊⌋ wf)))) r

  wt-apply-check : ∀ {e A B Ψ eE} → WI ctx e ((A ⇒⟨ LG.pure ⟩ B) ST.* A) Ψ eE
                 → WC ctx (SX.RApp (gn "apply") e) B (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app IR.apply eE)
  wt-apply-check w = (tt , proj₁ w) , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-apply-app′ u , cong (SS.morph-app IR.apply) r

  wt-inl-app-check : ∀ {e A B Ψ eE} → WC ctx e A Ψ eE
                   → WC ctx (SX.RApp (gn "inl") e) (A ST.+ B) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app IR.inl eE)
  wt-inl-app-check w = (tt , proj₁ w) , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-inl-app u , cong (SS.morph-app IR.inl) r

  wt-inr-app-check : ∀ {e A B Ψ eE} → WC ctx e B Ψ eE
                   → WC ctx (SX.RApp (gn "inr") e) (A ST.+ B) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app IR.inr eE)
  wt-inr-app-check w = (tt , proj₁ w) , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-inr-app u , cong (SS.morph-app IR.inr) r

  wt-initial-app-check : ∀ {e T Ψ eE} → WC ctx e ST.Void Ψ eE
                       → WC ctx (SX.RApp (gn "initial") e) T (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app IR.initial eE)
  wt-initial-app-check w = (tt , proj₁ w) , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-initial-app u , cong (SS.morph-app IR.initial) r

  -- A polymorphic telescope definition, at a kinded instance.
  wt-var-poly-instantiate : ∀ {x T sc body prefix}
                          → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
                          → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix))
                          → ¬ TP.Ground sc → KindedInstance (kinds ctx) sc T
                          → WC ctx (SX.RResolved (own x)) T Z (SS.poly x T)
  wt-var-poly-instantiate {sc = sc} _ _ lp ng ins = (_ , lp , ins) , λ P → let open At P in
    let ki = kinded-instance sc ins
        d = TView.View.entry (V P) lp
        (t , w , r) = (refC d (TView.iv-poly lp refl) (h-poly P lp) (TView.View.entryIs (V P) lp) (proj₁ ki) (proj₁ (proj₂ ki)) (h-open P lp ng))
        p = proj₂ (proj₂ ki)
    in t , retype⇐ p w
       , trans (rt⇐ p w) (trans (cong (subst (E Z) p) (trans r (ref-poly d (h-poly-inline P lp) (h-poly P lp)))) (subst-poly p))

------------------------------------------------------------------------
-- An arrow out of a given domain
------------------------------------------------------------------------

module _ {m} {ctx : NamedCtx m} where

  private
    Z = SCx.zeroUsage {size ctx}
    gn : String → SX.Expr
    gn g = SX.RResolved (gen g)

  wd-infer : ∀ {g A A′ B π π′ Ψ eE} → WI ctx g (A′ ST.⇒[ LG.mk-kind LG.Many π′ ] B) Ψ eE → (a : A <: A′) → (o : π′ LG.⊑π π)
           → WD ctx g A π B Ψ (SS.coerce (sub-arr {q = LG.Many} a (<:-refl B) o) eE)
  wd-infer {B = B} w a o = proj₁ w , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-infer u a o , cong (SS.coerce (sub-arr a (<:-refl B) o)) r

  -- A polymorphic definition whose codomain's variables occur in its domain.
  wd-poly : ∀ {x A B π π′ sc sd sco body prefix}
          → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
          → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix))
          → ¬ TP.Ground sc → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
          → KindedInstance (kinds ctx) sc (A ST.⇒[ LG.mk-kind LG.Many π′ ] B) → (g : π′ LG.⊑π π)
          → WD ctx (SX.RResolved (own x)) A π B Z
               (SS.coerce (sub-arr {q = LG.Many} (<:-refl A) (<:-refl B) g) (SS.poly x (A ST.⇒[ LG.mk-kind LG.Many π′ ] B)))
  wd-poly {A = A} {B = B} {sc = sc} _ _ lp ng arr cvd ins g = (_ , lp , ins) , λ P → let open At P in
    let (X , Y , te , incl) = h-arrow P lp arr cvd
        ki = kinded-instance sc ins
        d = TView.View.entry (V P) lp
        (t , w , r) = refD d (TView.iv-poly lp refl) (h-poly P lp) (TView.View.entryIs (V P) lp) (proj₁ ki) (proj₁ (proj₂ ki))
                            (h-open P lp ng) te incl (proj₂ (proj₂ ki)) g
    in t , w , trans r (cong (SS.coerce (sub-arr (<:-refl A) (<:-refl B) g)) (ref-poly d (h-poly-inline P lp) (h-poly P lp)))

  wd-lam : ∀ {x body A B q′ π Ψ eE} {u : LG.pure LG.⊑π π} → WI (extendNamedCtx ctx x A) body B (q′ SCx.∷ Ψ) eE
         → WD ctx (SX.RLam x body) A π B Ψ (SS.lam LG.Many (≤q-Many q′) eE)
  wd-lam {x = x} {A = A} {q′ = q′} {eE = eE} w = ext-refs {ctx = ctx} {x = x} {A = A} {e = eE} (proj₁ w) , λ P → let open At P in
    let (_ , u , r) = proj₂ w (pack▸ x A P) in _ , w-lam↦ u , cong (SS.lam LG.Many (≤q-Many q′)) r

  wd-compose : ∀ {f g A M B π Ψ₁ Ψ₂ fE gE} → WD ctx g A π M Ψ₂ gE → WD ctx f M π B Ψ₁ fE
             → WD ctx (SX.RApp (SX.RApp (gn "compose") f) g) A π B (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) (SS.comp' fE gE)
  wd-compose wg wf = (proj₁ wf , proj₁ wg) , λ P → let open At P in
    let (_ , ug , rg) = proj₂ wg P ; (_ , uf , rf) = proj₂ wf P in _ , w-compose↦ ug uf , cong₂ SS.comp' rf rg

  wd-id : ∀ {A π} {u : LG.pure LG.⊑π π} → WD ctx (gn "id") A π A Z (SS.lift-morphism IR.id)
  wd-id = tt , λ P → let open At P in _ , w-id↦ , refl
  wd-fst : ∀ {A B π} {u : LG.pure LG.⊑π π} → WD ctx (gn "fst") (A ST.* B) π A Z (SS.lift-morphism IR.fst)
  wd-fst = tt , λ P → let open At P in _ , w-fst↦ , refl
  wd-snd : ∀ {A B π} {u : LG.pure LG.⊑π π} → WD ctx (gn "snd") (A ST.* B) π B Z (SS.lift-morphism IR.snd)
  wd-snd = tt , λ P → let open At P in _ , w-snd↦ , refl
  wd-terminal : ∀ {A π} {u : LG.pure LG.⊑π π} → WD ctx (gn "terminal") A π ST.Unit Z (SS.lift-morphism IR.terminal)
  wd-terminal = tt , λ P → let open At P in _ , w-terminal↦ , refl
  wd-initial : ∀ {π} {u : LG.pure LG.⊑π π} → WD ctx (gn "initial") ST.Void π ST.Void Z (SS.lift-morphism IR.initial)
  wd-initial = tt , λ P → let open At P in _ , w-initial↦ , refl

  wd-case : ∀ {f g A B Cf Cg C π Ψ₁ Ψ₂ fE gE} → WD ctx f A π Cf Ψ₁ fE → WD ctx g B π Cg Ψ₂ gE → (j : Cf ⊔ Cg ≔ C)
          → WD ctx (SX.RApp (SX.RApp (gn "case") f) g) (A ST.+ B) π C (Ψ₁ SCx.+ᵘ Ψ₂)
               (SS.copair' (SS.coerce (sub-arr (<:-refl A) (<:ᶜ⇒<: (left j)) (⊑π-refl π)) fE)
                           (SS.coerce (sub-arr (<:-refl B) (<:ᶜ⇒<: (right j)) (⊑π-refl π)) gE))
  wd-case {A = A} {B = B} {π = π} wf wg j = (proj₁ wf , proj₁ wg) , λ P → let open At P in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P
    in _ , w-case↦ uf ug j
       , cong₂ (λ a b → SS.copair' (SS.coerce (sub-arr (<:-refl A) (<:ᶜ⇒<: (left j)) (⊑π-refl π)) a)
                                   (SS.coerce (sub-arr (<:-refl B) (<:ᶜ⇒<: (right j)) (⊑π-refl π)) b)) rf rg

  wd-pair : ∀ {f g A B C π Ψ₁ Ψ₂ fE gE} → WD ctx f A π B Ψ₁ fE → WD ctx g A π C Ψ₂ gE
          → WD ctx (SX.RApp (SX.RApp (gn "pair") f) g) A π (B ST.* C) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.fork' fE gE)
  wd-pair wf wg = (proj₁ wf , proj₁ wg) , λ P → let open At P in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P in _ , w-pair↦ uf ug , cong₂ SS.fork' rf rg

  wd-cata : ∀ {alg F A π Ψ eE} {u : LG.pure LG.⊑π π} → (wf : ST.WFFun (kinds ctx) F)
          → WI ctx alg (ST.⟦ F ⟧F A ST.⇒[ LG.mk-kind LG.Many π ] A) Ψ eE
          → WD ctx (SX.RApp (gn "cata") alg) (ST.μ F) π A (LG.Many SCx.*ᵘ Ψ) (SS.cata wf eE)
  wd-cata wf w = proj₁ w , λ P → let open At P in let (_ , u , r) = proj₂ w P in _ , w-cata↦ wf u , cong (SS.cata wf) r
