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
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe
import Data.Maybe.Properties
import Data.Empty
import Data.List.Relation.Unary.All
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import Relation.Binary.PropositionalEquality as PE
open import Relation.Nullary using (¬_)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Signature using (Signature)
import Once.Spec.Signature
import Data.List.Membership.Propositional
import Once.Spec.Grade as LG
import Once.Spec.Type as ST
import Once.Spec.Core.Syntax as SC
import Once.Spec.Context as SCx
import Once.Spec.Surface.Syntax as SX
import Once.TypeCheck.View as TView
import Once.Type.Poly as TP
open import Once.TypeCheck.Scope using (NamedCtx; lookupImport; lookupPolyPrefix; extendNamedCtx)
open NamedCtx
import Once.Spec.Surface.Typing as SUT
import Once.TypeCheck.Scoped as Sc
import Once.Name
import Once.TypeCheck.Witness as WM
import Once.TypeCheck.Use as UM
import Once.Denotation.RealizeS as RS
open import Once.Surface.Syntax as SS using () renaming (Expr to SExpr)
open import Once.Denotation.SurfaceRefs using (InScope)
open import Once.Denotation.Program using (Linked)
import Once.Spec.Surface.Generators as G
import Once.Spec.Core.Derived as Der
open import Once.TypeCheck.Table using (mapAt?; mapFrom?; mapTo?; morphIR)
import Once.TypeCheck.TableSound as TS
import Once.Metatheory.Surface.Basics

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
    -- every entry has its own name, and none is named as a declaration of
    -- the scope's signature (D249: the extractor's name guard)
    nm-inj : ∀ {d d′} → nm d ≡ nm d′ → d ≡ d′
    nm-sig : ∀ d → lookupImport (sig ctx) (Once.Name.showCanonical (nm d)) ≡ nothing
    -- the scope's locals, as the Spec names them
    L      : SUT.Locals Sg S nm m (size ctx)
    lr     : Sc.Locals.LocalsOf Sg S nm (named ctx) (debruijn ctx) L
open Pack

-- A local bound inside the scope.
pack▸ : ∀ {m} {ctx : NamedCtx m} (x : String) (A : ST.Ty m) → Pack ctx → Pack (extendNamedCtx ctx x A)
pack▸ {ctx = ctx} x A P = record
  { Sg = Sg P ; S = S P ; nm = nm P ; inline = inline P ; V = V P
  ; h-imp = h-imp P ; h-imp-call = h-imp-call P ; h-poly = h-poly P ; h-poly-inline = h-poly-inline P ; h-ground = h-ground P ; h-open = h-open P ; h-arrow = h-arrow P
  ; nm-inj = nm-inj P ; nm-sig = nm-sig P
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

-- …and the declarations: those the scope's signature declares, under a name
-- the resolver writes.
OkSOf : ∀ {m} {ctx : NamedCtx m} (P : Pack ctx) → CanonicalName → ST.Type → Set
OkSOf {ctx = ctx} P c T = (lookupImport (sig ctx) (Once.Name.showCanonical c) ≡ just T) × Once.Name.WordName c

-- What the lookups a reference records give: a definition in scope is no
-- generator, no declaration in scope, and the one its name finds (D249,
-- locally: the checker looks a name up in the signature first, then among
-- the monomorphic definitions, then the telescope).
module _ {m} {ctx : NamedCtx m} (P : Pack ctx) where
  private
    own-name : ∀ {d} → OkOf P d → Σ[ x ∈ String ] (nm P d ≡ canonical (x ∷ [])) × (lookupImport (sig ctx) x ≡ Data.Maybe.nothing)
    own-name (TView.iv-imp ns lk refl)     = _ , h-imp P lk , ns
    own-name (TView.iv-poly ns _ lp refl)  = _ , h-poly P lp , ns

    uip : ∀ {ℓ} {X : Set ℓ} {a b : X} (p q : a ≡ b) → p ≡ q
    uip refl refl = refl

    one-inj : ∀ {x y} → canonical (x ∷ []) ≡ canonical (y ∷ []) → x ≡ y
    one-inj refl = refl

    just≢nothing : ∀ {A : Set} {a : A} → Data.Maybe.just a ≡ Data.Maybe.nothing → Data.Empty.⊥
    just≢nothing ()

    imp-same : ∀ {x T T′} (lk : lookupImport (imports ctx) x ≡ just T) (lk′ : lookupImport (imports ctx) x ≡ just T′)
             → TView.ImportAt.entryOf (TView.View.imported (V P) lk) ≡ TView.ImportAt.entryOf (TView.View.imported (V P) lk′)
    imp-same lk lk′ with PE.trans (sym lk) lk′
    ... | refl with uip lk lk′
    ...   | refl = refl

    poly-same : ∀ {x r r′} (lp : lookupPolyPrefix (polys ctx) x ≡ just r) (lp′ : lookupPolyPrefix (polys ctx) x ≡ just r′)
              → TView.View.entry (V P) lp ≡ TView.View.entry (V P) lp′
    poly-same lp lp′ with PE.trans (sym lp) lp′
    ... | refl with uip lp lp′
    ...   | refl = refl

  ok-sig : ∀ {d T} → OkOf P d → OkSOf P (nm P d) T → Data.Empty.⊥
  ok-sig {T = T} ok l =
    just≢nothing (PE.trans (sym (subst (λ c → lookupImport (sig ctx) (Once.Name.showCanonical c) ≡ just T) (proj₁ (proj₂ (own-name ok))) (proj₁ l)))
                        (proj₂ (proj₂ (own-name ok))))

  ok-inj : ∀ {d d′} → OkOf P d → OkOf P d′ → nm P d ≡ nm P d′ → d ≡ d′
  ok-inj (TView.iv-imp _ lk refl) (TView.iv-imp _ lk′ refl) e with one-inj (PE.trans (sym (h-imp P lk)) (PE.trans e (h-imp P lk′)))
  ... | refl = imp-same lk lk′
  ok-inj (TView.iv-imp _ lk refl) (TView.iv-poly _ ni lp refl) e with one-inj (PE.trans (sym (h-imp P lk)) (PE.trans e (h-poly P lp)))
  ... | refl = Data.Empty.⊥-elim (just≢nothing (PE.trans (sym lk) ni))
  ok-inj (TView.iv-poly _ ni lp refl) (TView.iv-imp _ lk refl) e with one-inj (PE.trans (sym (h-poly P lp)) (PE.trans e (h-imp P lk)))
  ... | refl = Data.Empty.⊥-elim (just≢nothing (PE.trans (sym lk) ni))
  ok-inj (TView.iv-poly _ _ lp refl) (TView.iv-poly _ _ lp′ refl) e with one-inj (PE.trans (sym (h-poly P lp)) (PE.trans e (h-poly P lp′)))
  ... | refl = poly-same lp lp′

  oks-fun : ∀ {c T T′} → OkSOf P c T → OkSOf P c T′ → T ≡ T′
  oks-fun l l′ = Data.Maybe.Properties.just-injective (PE.trans (sym (proj₁ l)) (proj₁ l′))

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
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (trans; cong; cong₂; _≢_)
open import Once.Spec.Name using (own)
open import Once.Spec.Sub using (_<:_; _⊔_≔_; sub-arr)
open _⊔_≔_ using (left; right)
open import Once.Type.Sub using (<:-refl; ⊑π-refl; <:ᶜ⇒<:)
open import Once.IR as IR using (IR)
open import Once.IRTy using (IRTy; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Type.Grade using (≤q-Many)
open import Once.Name using (showCanonical; WordName)
open import Once.Type.Core using (wk₀; none)
open import Once.Type.Concrete using (IsConcrete)
open import Once.Type.Instance using (KindedInstance)
open import Once.Type.Schema using (kinded-instance)
open import Once.Context using (svar; _⊔ᵘ_)
open import Once.TypeCheck.Scope using (lookupLocal)
open import Once.Core.Decl using (⌜declS⌝)
open import Once.Type.Grade using (_≤qᵇ_)
open import Once.Type.Rigid using (ground-kinded)
open import Once.Spec.Surface.Syntax using (signedDecimal)
open import Once.Spec.Surface.Operator using (binSym; BinSym)
open BinSym using (theory; shape)
open import Once.Spec.Theory using (NumTy; ⌜_⌝ⁿ; Has; Neg; symCod; ‵neg)
open import Once.TypeCheck.NumTable using (binDom)
open import Once.Surface.Numeric using (numBin; toFloatIR)
open import Data.Unit using (tt)

-- The compiler's weakening is the Spec's `↑`.
open import Once.Type.Closed using (sub0)

wk₀≡↑ : ∀ {m} (T : ST.Type) → wk₀ {m} T ≡ T ST.⟨ (λ ()) ⟩
wk₀≡↑ T = sub0 T none (λ ())

-- The Spec's annotated rules, at a pack.
module WMP {m} {ctx : NamedCtx m} (P : Pack ctx) = WM (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx)

-- …and the compiler's View there.
module At {m} {ctx : NamedCtx m} (P : Pack ctx) where
  open WMP P
  module Locals = Sc.Locals (Sg P) (S P) (nm P) using (found)
  module RS′ = RS (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (inline P) (kinds ctx) using (realize⇒; realize⇐; realize↦; ref)
  open RS′
  module SU = SUT (Sg P) (S P) (nm P)
    using (CheckHead; Locals; PartialCombinator; _⊢_⇐_⇒[_]↦_↝_; _⊢_⇒_↝_; ch-comb₁; ch-comb₂; ch-lam
          ; ch-map; ch-poly; pc-bare; pc-one; poly; s-app; s-app-spine; s-const; s-def; s-sigop)

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

  -- A head that synthesizes is no partial combinator and never checks only
  -- (`s-app`'s premises): its derivation rules out every other form, and a
  -- polymorphic name, by the names' distinctness (`nm-inj`, `nm-sig`).
  private
    module B = Once.Metatheory.Surface.Basics (Sg P) (S P) (nm P)
      using (0<0; map-comb; module Modes)
    module BM = B.Modes (kinds ctx)
      using (noSyn-comb₁; noSyn-comb₂; noSyn-map)
    const-comb : ∀ {k n} → G.IsConstant k → G.IsCombinator n k → ⊥
    const-comb G.is-constant ()

  synth-noPC : ∀ {n} {L′ : SU.Locals m n} {f T t} → SU._⊢_⇒_↝_ (kinds ctx) L′ f T t → ¬ SU.PartialCombinator f
  synth-noPC (SU.s-const {k = k} _) (SU.pc-bare ic) = const-comb k ic
  synth-noPC (SU.s-app pc _ _ _) (SU.pc-one ic)     = pc (SU.pc-bare ic)
  synth-noPC (SU.s-app-spine (SU.ch-map im) _ _) (SU.pc-one ic) = B.map-comb im ic

  synth-noCH : ∀ {n} {L′ : SU.Locals m n} {f T t Ψ} (s : SU._⊢_⇒_↝_ (kinds ctx) L′ f T t)
             → UM.Use⇒ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) s Ψ → ¬ SU.CheckHead f
  synth-noCH () _ SU.ch-lam
  synth-noCH (SU.s-sigop mem) (UM.u-sigop {ok = ok} _ _) (SU.ch-poly (SU.poly d e lt)) =
    nothing≢just (trans (sym (nm-sig P d)) (subst (λ c → lookupImport (sig ctx) (Once.Name.showCanonical c) ≡ _) (sym e) (proj₁ ok)))
    where nothing≢just : ∀ {A : Set} {a : A} → nothing ≡ just a → ⊥
          nothing≢just ()
  synth-noCH (SU.s-def d′ e′ _ a0) _ (SU.ch-poly (SU.poly d e lt)) with nm-inj P (PE.trans e (sym e′))
  ... | refl = B.0<0 a0 lt
  synth-noCH s _ (SU.ch-map im)   = BM.noSyn-map im s
  synth-noCH s _ (SU.ch-comb₁ ic) = BM.noSyn-comb₁ ic s
  synth-noCH s _ (SU.ch-comb₂ ic) = BM.noSyn-comb₂ ic s

  -- The spine at a head that is no generator applies it as an arrow.
  spineE-app : ∀ {f X T t Ψ₁ Ψ₂} {d : SU._⊢_⇐_⇒[_]↦_↝_ (kinds ctx) (L P) f X LG.pure T t} {x : E Ψ₂ X}
             → (∀ {g} → f ≢ SX.RGen g) → (u : UM.Use↦ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) d Ψ₁)
             → RS.spineE (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (inline P) (kinds ctx) sh x u ≡ SS.app (realize↦ sh u) x
  spineE-app ng UM.u-map           = ⊥-elim (ng refl)
  spineE-app ng (UM.u-infer _)     = refl
  spineE-app ng UM.u-poly          = refl
  spineE-app ng (UM.u-lam _)       = refl
  spineE-app ng (UM.u-compose _ _) = refl
  spineE-app ng (UM.u-case _ _)    = refl
  spineE-app ng (UM.u-pair _ _)    = refl
  spineE-app ng (UM.u-cata _)      = refl

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

-- A numeric term's references: its operands' (through the transport of its
-- domain).
refs-subst : ∀ {m} {ctx : NamedCtx m} {n} {Γ : SCx.Ctx m n} {Ψ A B} (p : A ≡ B) {e : SExpr Γ Ψ A}
           → InScope ctx e → InScope ctx (subst (SExpr Γ Ψ) p e)
refs-subst refl r = r

refs-numBin : ∀ {m} {ctx : NamedCtx m} {Ψ₁ Ψ₂} op (a : NumTy) (h : Has a (theory (binSym op)))
              {x : SExpr (debruijn ctx) Ψ₁ ⌜ a ⌝ⁿ} {y : SExpr (debruijn ctx) Ψ₂ ⌜ a ⌝ⁿ}
            → InScope ctx x → InScope ctx y → InScope ctx (numBin op a h x y)
refs-numBin {ctx = ctx} op a h rx ry = refs-subst {ctx = ctx} (sym (binDom op a)) (rx , ry)

-- A local's binder adds no reference.
ext-refs : ∀ {m} {ctx : NamedCtx m} {x A} {n} {Γ : SCx.Ctx m n} {Ψ B} {e : SExpr Γ Ψ B} → InScope (extendNamedCtx ctx x A) e → InScope ctx e
ext-refs r = r

-- An embedded morphism, retyped, is as call-free.
private
  Linked-substˡ : ∀ {X Y Z : IRTy} (eq : X ≡ Y) (ir : IR X Z) → Linked [] [] ir → Linked [] [] (subst (λ o → IR o Z) eq ir)
  Linked-substˡ refl ir l = l

  Linked-substʳ : ∀ {X Y Z : IRTy} (eq : Y ≡ Z) (ir : IR X Y) → Linked [] [] ir → Linked [] [] (subst (λ o → IR X o) eq ir)
  Linked-substʳ refl ir l = l

private
  cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (f : A → B → C → D)
        {x y u v s t} → x ≡ y → u ≡ v → s ≡ t → f x u s ≡ f y v t
  cong₃ f refl refl refl = refl

fd-map′ : ∀ {k} → G.FromDomain k → G.IsMap k
fd-map′ G.fd-domain = G.is-map
fd-map′ G.fd-both   = G.is-map

-- The morphisms of the table are call-free.
morph-linked : ∀ {m} {Δ : ST.KCtx m} {s} {S : SC.Defs s} {n} {g k A π B} {t : SC.Tm S m n}
             → (mo : G.Morphism Δ g k A π B t) → Linked [] [] (morphIR mo)
morph-linked G.m-id       = tt
morph-linked G.m-fst      = tt
morph-linked G.m-snd      = tt
morph-linked G.m-terminal = tt
morph-linked G.m-inl      = tt
morph-linked G.m-inr      = tt
morph-linked G.m-initial  = tt
morph-linked (G.m-apply {ρ = LG.pure}) = tt
morph-linked (G.m-apply {ρ = LG.act})  = tt , tt
morph-linked (G.m-apply {ρ = LG.eff})  = tt , tt
morph-linked (G.m-In {F = F} w)  = Linked-substˡ (sym (⌊⟧T-commute F (ST.μ F))) (IR.In (wf-⌊⌋ w)) tt
morph-linked (G.m-Out {F = F} {f = LG.pureᶠ} w) = Linked-substʳ (sym (⌊⟧T-commute F (ST.ν F LG.pureᶠ))) (IR.Out (wf-⌊⌋ w)) tt
morph-linked (G.m-Out {F = F} {f = LG.actᶠ} w)  = Linked-substʳ (sym (⌊⟧T-commute F (ST.ν F LG.actᶠ))) (IR.Out (wf-⌊⌋ w)) tt , tt

private
  linked-≡ : ∀ {X Y : IRTy} {a b : IR X Y} → a ≡ b → Linked [] [] a → Linked [] [] b
  linked-≡ refl l = l

map-linked-at : ∀ {m} {Δ : ST.KCtx m} {g A B mI} → mapAt? Δ g A B ≡ just mI → Linked [] [] mI
map-linked-at {m} {Δ} {g} {A} {B} {mI} e =
  let ok = TS.mapAt?-sound {Δ = Δ} {S = SC.[]} {n = 0} g A LG.pure B {mI = mI} e
  in linked-≡ (TS.AtOK.ir ok) (morph-linked (proj₂ (proj₂ (TS.AtOK.row ok))))

map-linked-from : ∀ {m} {Δ : ST.KCtx m} {g A B mI} → mapFrom? Δ g A ≡ just (B , mI) → Linked [] [] mI
map-linked-from {m} {Δ} {g} {A} {B} {mI} e =
  let ok = TS.mapFrom?-sound {Δ = Δ} {S = SC.[]} {n = 0} g A LG.pure {B = B} {mI = mI} e
  in linked-≡ (TS.FromOK.ir ok) (morph-linked (proj₂ (proj₂ (TS.FromOK.row ok))))

map-linked-to : ∀ {m} {Δ : ST.KCtx m} {g A B mI} → mapTo? Δ g B ≡ just (A , mI) → Linked [] [] mI
map-linked-to {m} {Δ} {g} {A} {B} {mI} e =
  let ok = TS.mapTo?-sound {Δ = Δ} {S = SC.[]} {n = 0} g B {A = A} {mI = mI} e
  in linked-≡ (TS.ToOK.ir ok) (morph-linked (proj₂ (proj₂ (TS.ToOK.row ok))))

-- An application's references: its head's and its argument's.
refs-appT : ∀ {m} {ctx : NamedCtx m} {Ψ₁ Ψ₂ A B q} (π : LG.Purity) {f : SExpr (debruijn ctx) Ψ₁ (A ST.⇒[ LG.mk-kind q π ] B)} {x : SExpr (debruijn ctx) Ψ₂ A}
          → InScope ctx f → InScope ctx x → InScope ctx (SS.appT π f x)
refs-appT LG.pure rf rx = rf , rx
refs-appT LG.act  rf rx = rf , rx
refs-appT LG.eff  rf rx = rf , rx

module _ {m} {ctx : NamedCtx m} where

  private
    E = SExpr (debruijn ctx)

  wt-int : (n : ℤ) → WI ctx (SX.RInt n) ST.Int SCx.zeroUsage (SS.int n)
  wt-int n = tt , λ P → let open WMP P using (w-int) in _ , w-int n , refl

  wt-float : ∀ sg i f l → WI ctx (SX.RFloat sg i f l) ST.Float SCx.zeroUsage (SS.float (signedDecimal sg i f l))
  wt-float sg i f l = tt , λ P → let open WMP P using (w-float) in _ , w-float sg i f l , refl

  -- The constants of the table (`s-const`): `toFloat` (D408) and `unit`.
  wt-toFloat : WI ctx (SX.RGen G.toFloat) (ST.Int ST.⇒[ LG.mk-kind LG.Many LG.pure ] ST.Float) SCx.zeroUsage
                  (SS.lift-morphism toFloatIR)
  wt-toFloat = tt , λ P → let open WMP P using (w-const) in _ , w-const G.k-toFloat , refl

  wt-unit : WI ctx SX.RUnit ST.Unit SCx.zeroUsage SS.unit
  wt-unit = tt , λ P → let open WMP P using (w-unit) in _ , w-unit , refl

  wt-unit-gen : WI ctx (SX.RGen G.unit) ST.Unit SCx.zeroUsage SS.unit
  wt-unit-gen = tt , λ P → let open WMP P using (w-const) in _ , w-const G.k-unit , refl

  wt-var-local : ∀ {x A Ψ} {eV : Once.Context.SVar (debruijn ctx) Ψ A}
               → lookupLocal ctx x ≡ just (A , Ψ , eV) → WI ctx (SX.RVar x) A Ψ (SS.svar→expr eV)
  wt-var-local {eV = svar i} lk = tt , λ P → let open At P using (subst-K; module Locals) ; open Locals using (found) ; open WMP P using (w-var) in _ , w-var (found (lr P) i lk) , subst-K _ _

  wt-var-resolved : ∀ {cn T A} → WordName cn
                  → lookupImport (sig ctx) (showCanonical cn) ≡ just T → (k : IsConcrete T) → (eq : A ≡ wk₀ T)
                  → WI ctx (SX.RResolved cn) A SCx.zeroUsage (subst (E SCx.zeroUsage) (sym eq) (SS.sigOp cn k))
  wt-var-resolved {cn} {T} wn lk k refl = lk , λ P → res P (TView.View.declares (V P) lk)
    where
      res : (P : Pack ctx) → TView.Declared (Sg P) (S P) (showCanonical cn) T
          → Σ[ t ∈ SC.Tm (S P) _ (size ctx) ] Σ[ w ∈ WM.W⇒ (Sg P) (S P) (nm P) (OkOf P) (OkSOf P) (kinds ctx) (L P) (SX.RResolved cn) (wk₀ T) t SCx.zeroUsage ]
              rz⇒ P w ≡ SS.sigOp cn k
      res P (TView.declared h mem) =
        let open At P using (retype⇒; rt⇒; subst-twice) ; open WMP P using (w-sigop) in
        let p = ⌜declS⌝ k h
            w = w-sigop {ok = lk , wn} (mem wn refl) k h
        in _ , retype⇒ p w , trans (rt⇒ p w) (subst-twice (⌜declS⌝ k h) p _)

  wt-var-own : ∀ {x T A} → lookupImport (sig ctx) x ≡ nothing → (lk : lookupImport (imports ctx) x ≡ just T) → (eq : A ≡ wk₀ T)
             → WI ctx (SX.RResolved (own x)) A SCx.zeroUsage (subst (E SCx.zeroUsage) (sym eq) (SS.closure x))
  wt-var-own ns lk refl = (_ , lk , refl) , λ P → let open At P using (ref-call; refS) in
    let d = TView.ImportAt.entryOf (TView.View.imported (V P) lk)
        (t , w , r) = (refS d (TView.iv-imp ns lk refl) (h-imp P lk) (TView.ImportAt.mono (TView.View.imported (V P) lk)) none
                            (cong SC.Schema.arity (TView.ImportAt.mono (TView.View.imported (V P) lk))))
    in t , w , trans r (ref-call d (h-imp-call P lk) (h-imp P lk))

  wt-var-poly-instantiate-infer : ∀ {x T sc body prefix} {g : TP.Ground sc}
                                → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
                                → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix))
                                → TP.Ground sc → T ≡ TP.extractGround sc g
                                → WI ctx (SX.RResolved (own x)) T SCx.zeroUsage (SS.poly x T)
  wt-var-poly-instantiate-infer {sc = sc} {g = g} nsg nim lp _ eq = (_ , lp , subst (KindedInstance (kinds ctx) sc) (sym eq) (ground-kinded {Δ = kinds ctx} sc g)) , λ P → let open At P using (ref-poly; refS; retype⇒; rt⇒; subst-poly) in
    let ki = kinded-instance sc (ground-kinded {Δ = kinds ctx} sc g)
        d = TView.View.entry (V P) lp
        (t , w , r) = (refS d (TView.iv-poly nsg nim lp refl) (h-poly P lp) (TView.View.entryIs (V P) lp) (proj₁ ki) (h-ground P lp g))
        p = trans (proj₂ (proj₂ ki)) (sym eq)
    in t , retype⇒ p w
       , trans (rt⇒ p w) (trans (cong (subst (E SCx.zeroUsage) p) (trans r (ref-poly d (h-poly-inline P lp) (h-poly P lp)))) (subst-poly p))

  wt-annot : ∀ {e T A Ψ eE} → WC ctx e A Ψ eE → A ≡ wk₀ T → WI ctx (SX.RAnnot e T) A Ψ eE
  wt-annot {T = T} w refl = proj₁ w , λ P → let open At P using (retype⇐; retype⇒; rt⇐; rt⇒) ; open WMP P using (w-annot) in
    let a = wk₀≡↑ T
        (_ , w′ , r) = proj₂ w P
    in _ , retype⇒ (sym a) (w-annot (retype⇐ a w′))
       , trans (rt⇒ (sym a) (w-annot (retype⇐ a w′))) (trans (cong (subst (E _) (sym a)) (rt⇐ a w′)) (trans (subst-back a _) r))
    where
      subst-back : ∀ {Ψ A B} (p : A ≡ B) (x : E Ψ A) → subst (E Ψ) (sym p) (subst (E Ψ) p x) ≡ x
      subst-back refl x = refl

  wt-pair : ∀ {a b A B Ψ₁ Ψ₂ aE bE} → WI ctx a A Ψ₁ aE → WI ctx b B Ψ₂ bE
          → WI ctx (SX.RPair a b) (A ST.* B) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.pair aE bE)
  wt-pair wa wb = (proj₁ wa , proj₁ wb) , λ P → let open WMP P using (w-pair) in
    let (_ , ua , ra) = proj₂ wa P ; (_ , ub , rb) = proj₂ wb P in _ , w-pair ua ub , cong₂ SS.pair ra rb

  wt-neg : ∀ {e A Ψ eE} (h : Has A Neg) → WI ctx e ⌜ A ⌝ⁿ Ψ eE → WI ctx (SX.RNeg e) ⌜ A ⌝ⁿ Ψ (SS.num h ‵neg eE)
  wt-neg h w = proj₁ w , λ P → let open WMP P using (w-neg) in let (_ , u , r) = proj₂ w P in _ , w-neg h u , cong (SS.num h ‵neg) r

  wt-let : ∀ {x e₁ e₂ A B q Ψ₁ Ψ₂ e₁E e₂E} → WI ctx e₁ A Ψ₁ e₁E → WI (extendNamedCtx ctx x A) e₂ B (q SCx.∷ Ψ₂) e₂E
         → WI ctx (SX.RLet x e₁ e₂) B (Ψ₂ SCx.+ᵘ (q SCx.*ᵘ Ψ₁)) (SS.let' e₁E e₂E)
  wt-let {x = x} {A = A} {q = q} {e₂E = e₂E} w₁ w₂ = (proj₁ w₁ , ext-refs {ctx = ctx} {x = x} {A = A} {e = e₂E} (proj₁ w₂)) , λ P → let open WMP P using (w-let) in
    let (_ , u₁ , r₁) = proj₂ w₁ P ; (_ , u₂ , r₂) = proj₂ w₂ (pack▸ x A P) in _ , w-let q u₁ u₂ , cong₂ SS.let' r₁ r₂

  wt-case : ∀ {e xl el xr er A B Cl Cr C ql qr Ψs Ψₗ Ψᵣ sE lE rE}
          → WI ctx e (A ST.+ B) Ψs sE → WI (extendNamedCtx ctx xl A) el Cl (ql SCx.∷ Ψₗ) lE
          → WI (extendNamedCtx ctx xr B) er Cr (qr SCx.∷ Ψᵣ) rE
          → (j : Cl ⊔ Cr ≔ C)
          → WI ctx (SX.RDestruct e xl el xr er) C (Ψs SCx.+ᵘ (Ψₗ ⊔ᵘ Ψᵣ))
               (SS.case' sE (SS.coerce (<:ᶜ⇒<: (left j)) lE) (SS.coerce (<:ᶜ⇒<: (right j)) rE))
  wt-case {xl = xl} {xr = xr} {A = A} {B = B} {ql = ql} {qr = qr} {lE = lE} {rE = rE} ws wl wr j = (proj₁ ws , ext-refs {ctx = ctx} {x = xl} {A = A} {e = lE} (proj₁ wl) , ext-refs {ctx = ctx} {x = xr} {A = B} {e = rE} (proj₁ wr)) , λ P → let open WMP P using (w-case) in
    let (_ , us , rs) = proj₂ ws P ; (_ , ul , rl) = proj₂ wl (pack▸ xl A P) ; (_ , ur , rr) = proj₂ wr (pack▸ xr B P)
    in _ , w-case ql qr us ul ur j
       , cong₃ (λ a b c → SS.case' a (SS.coerce (<:ᶜ⇒<: (left j)) b) (SS.coerce (<:ᶜ⇒<: (right j)) c)) rs rl rr

  -- A binary operator at a number type with its theory: `numBin`, as the
  -- realization builds it.
  wt-binop : ∀ {op e₁ e₂ a Ψ₁ Ψ₂ e₁E e₂E} (h : Has a (theory (binSym op)))
           → WI ctx e₁ ⌜ a ⌝ⁿ Ψ₁ e₁E → WI ctx e₂ ⌜ a ⌝ⁿ Ψ₂ e₂E
           → WI ctx (SX.RBinOp op e₁ e₂) (symCod a (shape (binSym op))) (Ψ₁ SCx.+ᵘ Ψ₂) (numBin op a h e₁E e₂E)
  wt-binop {op} {a = a} h w₁ w₂ = refs-numBin {ctx = ctx} op a h (proj₁ w₁) (proj₁ w₂) , λ P → let open WMP P using (w-binop) in
    let (_ , u₁ , r₁) = proj₂ w₁ P ; (_ , u₂ , r₂) = proj₂ w₂ P
    in _ , w-binop h u₁ u₂ , cong₂ (numBin op a h) r₁ r₂

  -- Application: the head's type synthesized, the argument checked; the
  -- result is `𝕋` of the arrow's grade (`s-app`).
  wt-app : ∀ {f x A B q π Ψ₁ Ψ₂ fE xE}
         → WI ctx f (A ST.⇒[ LG.mk-kind q π ] B) Ψ₁ fE → WC ctx x A Ψ₂ xE
         → WI ctx (SX.RApp f x) (Der.𝕋 π B) (Ψ₁ SCx.+ᵘ (q SCx.*ᵘ Ψ₂)) (SS.appT π fE xE)
  wt-app {π = π} {fE = fE} {xE = xE} wf wx = (refs-appT {ctx = ctx} π {f = fE} {x = xE} (proj₁ wf) (proj₁ wx)) , λ P → let open At P using (synth-noPC; synth-noCH) ; open WMP P using (w-app) in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ux , rx) = proj₂ wx P
    in _ , w-app (synth-noPC (proj₁ uf)) (synth-noCH (proj₁ uf) (proj₂ uf)) uf ux , cong₂ (SS.appT _) rf rx

  -- …or the argument's type synthesized and the head checked from that
  -- domain (`s-app-spine`): a structure map is applied as a morphism,
  -- any other head that only checks as an arrow.
  wt-map-spine : ∀ {g x X T Ψ xE mI} → mapFrom? (kinds ctx) g X ≡ just (T , mI)
               → WI ctx x X Ψ xE
               → WI ctx (SX.RApp (SX.RGen g) x) T (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app mI xE)
  wt-map-spine {g} {X = X} {T = T} {mI = mI} e wx = (map-linked-from {Δ = kinds ctx} {g = g} {A = X} {B = T} {mI = mI} e , proj₁ wx) , λ P → let open WMP P using (w-app-spine; w-map↦) in
    let ok = TS.mapFrom?-sound {Δ = kinds ctx} {S = S P} {n = size ctx} g X LG.pure {B = T} {mI = mI} e
        (_ , _ , mo) = TS.FromOK.row ok
        (_ , ux , rx) = proj₂ wx P
    in _ , w-app-spine (SUT.ch-map (fd-map′ (TS.FromOK.from ok))) ux (w-map↦ (TS.FromOK.from ok) mo (TS.FromOK.least ok))
       , cong₂ SS.morph-app (TS.FromOK.ir ok) rx

  wt-app-spine : ∀ {f x X T Ψ₁ Ψ₂ fE xE} → (∀ {g} → f ≢ SX.RGen g) → ((P : Pack ctx) → SUT.CheckHead (Sg P) (S P) (nm P) f)
               → WI ctx x X Ψ₂ xE → WD ctx f X LG.pure T Ψ₁ fE
               → WI ctx (SX.RApp f x) T (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) (SS.app fE xE)
  wt-app-spine ng ch wx wf = (proj₁ wf , proj₁ wx) , λ P → let open WMP P using (w-app-spine) ; open At P using (spineE-app) in
    let (_ , ux , rx) = proj₂ wx P ; (_ , uf , rf) = proj₂ wf P
    in _ , w-app-spine (ch P) ux uf
       , trans (spineE-app ng (proj₂ uf)) (cong₂ SS.app rf rx)

------------------------------------------------------------------------
-- Checking
------------------------------------------------------------------------

module _ {m} {ctx : NamedCtx m} where

  private
    _⇒⟨_⟩_ : ST.Ty m → LG.Purity → ST.Ty m → ST.Ty m
    A ⇒⟨ π ⟩ B = A ST.⇒[ LG.mk-kind LG.Many π ] B
    infixr 30 _⇒⟨_⟩_
    Z = SCx.zeroUsage {size ctx}
    gn : G.Gen → SX.Expr
    gn g = SX.RGen g
    E = SExpr (debruijn ctx)

  -- `c-map`: a structure map at an instance of the table.
  wt-map-check : ∀ {g A π B mI} → mapAt? (kinds ctx) g A B ≡ just mI
               → WC ctx (gn g) (A ⇒⟨ π ⟩ B) Z (SS.lift-morphism mI)
  wt-map-check {g} {A} {π} {B} {mI} e = map-linked-at {Δ = kinds ctx} {g = g} {A = A} {B = B} {mI = mI} e , λ P → let open WMP P using (w-map) in
    let ok = TS.mapAt?-sound {Δ = kinds ctx} {S = S P} {n = size ctx} g A π B {mI = mI} e
        (_ , _ , mo) = TS.AtOK.row ok
    in _ , w-map mo , cong SS.lift-morphism (TS.AtOK.ir ok)

  -- `c-map-app`: a map its codomain fixes, applied: the argument at its domain.
  wt-map-app-check : ∀ {g x A T Ψ xE mI} → mapTo? (kinds ctx) g T ≡ just (A , mI) → WC ctx x A Ψ xE
                   → WC ctx (SX.RApp (gn g) x) T (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ)) (SS.morph-app mI xE)
  wt-map-app-check {g} {A = A} {T = T} {mI = mI} e wx = (map-linked-to {Δ = kinds ctx} {g = g} {A = A} {B = T} {mI = mI} e , proj₁ wx) , λ P → let open WMP P using (w-map-app) in
    let ok = TS.mapTo?-sound {Δ = kinds ctx} {S = S P} {n = size ctx} g T {A = A} {mI = mI} e
        (_ , _ , mo) = TS.ToOK.row ok
        (_ , ux , rx) = proj₂ wx P
    in _ , w-map-app (TS.ToOK.to ok) mo ux , cong₂ SS.morph-app (TS.ToOK.ir ok) rx

  -- `compose f g`: `g`'s codomain from its domain when `g` has a
  -- domain-given form, `f`'s type synthesized otherwise.
  wt-compose-check-g : ∀ {f g A B C π Ψ₁ Ψ₂ fE gE} → ((P : Pack ctx) → SUT.DomainForm (Sg P) (S P) (nm P) g)
                     → WD ctx g A π B Ψ₂ gE → WC ctx f (B ⇒⟨ π ⟩ C) Ψ₁ fE
                     → WC ctx (SX.RApp (SX.RApp (gn G.compose) f) g) (A ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) (SS.comp' fE gE)
  wt-compose-check-g df wg wf = (proj₁ wf , proj₁ wg) , λ P → let open WMP P using (w-compose-g) in
    let (_ , ug , rg) = proj₂ wg P ; (_ , uf , rf) = proj₂ wf P in _ , w-compose-g (df P) ug uf , cong₂ SS.comp' rf rg

  wt-compose-check-f : ∀ {f g A B C C′ π π′ Ψ₁ Ψ₂ fE gE} → ((P : Pack ctx) → ¬ SUT.DomainForm (Sg P) (S P) (nm P) g)
                     → WI ctx f (B ⇒⟨ π′ ⟩ C′) Ψ₁ fE → (p : (B ⇒⟨ π′ ⟩ C′) <: (B ⇒⟨ π ⟩ C))
                     → WC ctx g (A ⇒⟨ π ⟩ B) Ψ₂ gE
                     → WC ctx (SX.RApp (SX.RApp (gn G.compose) f) g) (A ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) (SS.comp' (SS.coerce p fE) gE)
  wt-compose-check-f ndf wf p wg = (proj₁ wf , proj₁ wg) , λ P → let open WMP P using (w-compose-f) in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P in _ , w-compose-f (ndf P) uf p ug , cong₂ (λ a b → SS.comp' (SS.coerce p a) b) rf rg

  wt-case-copair-check : ∀ {f g A B C π Ψ₁ Ψ₂ fE gE} → WC ctx f (A ⇒⟨ π ⟩ C) Ψ₁ fE → WC ctx g (B ⇒⟨ π ⟩ C) Ψ₂ gE
                       → WC ctx (SX.RApp (SX.RApp (gn G.case) f) g) ((A ST.+ B) ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.copair' fE gE)
  wt-case-copair-check wf wg = (proj₁ wf , proj₁ wg) , λ P → let open WMP P using (w-case′) in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P in _ , w-case′ uf ug , cong₂ SS.copair' rf rg

  wt-pair-morph-check : ∀ {f g A B C π Ψ₁ Ψ₂ fE gE} → WC ctx f (A ⇒⟨ π ⟩ B) Ψ₁ fE → WC ctx g (A ⇒⟨ π ⟩ C) Ψ₂ gE
                      → WC ctx (SX.RApp (SX.RApp (gn G.pair) f) g) (A ⇒⟨ π ⟩ (B ST.* C)) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.fork' fE gE)
  wt-pair-morph-check wf wg = (proj₁ wf , proj₁ wg) , λ P → let open WMP P using (w-pair′) in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P in _ , w-pair′ uf ug , cong₂ SS.fork' rf rg

  wt-curry-check : ∀ {f A B C π₀ π Ψ eE} → WC ctx f ((A ST.* B) ⇒⟨ π ⟩ C) Ψ eE
                 → WC ctx (SX.RApp (gn G.curry) f) (A ⇒⟨ π₀ ⟩ (B ⇒⟨ π ⟩ C)) Ψ (SS.curry' eE)
  wt-curry-check w = proj₁ w , λ P → let open WMP P using (w-curry) in let (_ , u , r) = proj₂ w P in _ , w-curry u , cong SS.curry' r

  wt-cata-check : ∀ {alg F A π Ψ eE} → (wf : ST.WFFun (kinds ctx) F) → WC ctx alg (ST.⟦ F ⟧F A ⇒⟨ π ⟩ A) Ψ eE
                → WC ctx (SX.RApp (gn G.cata) alg) (ST.μ F ⇒⟨ π ⟩ A) (LG.Many SCx.*ᵘ Ψ) (SS.cata wf eE)
  wt-cata-check wf w = proj₁ w , λ P → let open WMP P using (w-cata) in let (_ , u , r) = proj₂ w P in _ , w-cata wf u , cong (SS.cata wf) r

  -- `c-ana`: into a stream (`final-ν`), or `T∞ B` at `eff` (`final-T∞`).
  wt-ana-check : ∀ {c F A π₀ φ Ψ eE} (ua : π₀ LG.⊑π LG.act) → (wf : ST.WFFun (kinds ctx) F)
               → WC ctx c (A ⇒⟨ LG.fin φ ⟩ ST.⟦ F ⟧F A) Ψ eE
               → WC ctx (SX.RApp (gn G.ana) c) (A ⇒⟨ π₀ ⟩ ST.ν F φ) (LG.Many SCx.*ᵘ Ψ) (SS.ana wf eE)
  wt-ana-check ua wf w = proj₁ w , λ P → let open WMP P using (w-ana) in let (_ , u , r) = proj₂ w P in _ , w-ana (G.final-ν ua wf) u , cong (SS.ana wf) r

  wt-loop-check : ∀ {c A B Ψ eE} → WC ctx c (A ⇒⟨ LG.act ⟩ (B ST.+ A)) Ψ eE
                → WC ctx (SX.RApp (gn G.ana) c) (A ⇒⟨ LG.eff ⟩ B) (LG.Many SCx.*ᵘ Ψ) (SS.loop eE)
  wt-loop-check w = proj₁ w , λ P → let open WMP P using (w-ana) in let (_ , u , r) = proj₂ w P in _ , w-ana G.final-T∞ u , cong SS.loop r

  -- `c-sub`: a synthesized type where a supertype is expected, for a form with
  -- no checking rule of its own.
  wt-sub : ∀ {e A B Ψ eE} → ((P : Pack ctx) → ¬ SUT.OwnCheck (Sg P) (S P) (nm P) e) → WI ctx e A Ψ eE → (p : A <: B) → WC ctx e B Ψ (SS.coerce p eE)
  wt-sub noc w p = proj₁ w , λ P → let open WMP P using (w-sub) in let (_ , u , r) = proj₂ w P in _ , w-sub (noc P) u p , cong (SS.coerce p) r

  wt-lam : ∀ {x body A B q q′ π Ψ eE} → (≤p : (q′ ≤qᵇ q) ≡ true)
         → WC (extendNamedCtx ctx x A) body B (q′ SCx.∷ Ψ) eE
         → WC ctx (SX.RLam x body) (A ST.⇒[ LG.mk-kind q π ] B) Ψ (SS.lam q ≤p eE)
  wt-lam {x = x} {A = A} {eE = eE} ≤p w = ext-refs {ctx = ctx} {x = x} {A = A} {e = eE} (proj₁ w) , λ P → let open WMP P using (w-lam) in
    let (_ , u , r) = proj₂ w (pack▸ x A P) in _ , w-lam ≤p u , cong (SS.lam _ ≤p) r

  wt-pair-lit-check : ∀ {a b A B Ψ₁ Ψ₂ aE bE} → WC ctx a A Ψ₁ aE → WC ctx b B Ψ₂ bE
                    → WC ctx (SX.RPair a b) (A ST.* B) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.pair aE bE)
  wt-pair-lit-check wa wb = (proj₁ wa , proj₁ wb) , λ P → let open WMP P using (w-pair-lit) in
    let (_ , ua , ra) = proj₂ wa P ; (_ , ub , rb) = proj₂ wb P in _ , w-pair-lit ua ub , cong₂ SS.pair ra rb

  -- A polymorphic telescope definition, at a kinded instance.
  wt-var-poly-instantiate : ∀ {x T sc body prefix}
                          → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
                          → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix))
                          → ¬ TP.Ground sc → KindedInstance (kinds ctx) sc T
                          → WC ctx (SX.RResolved (own x)) T Z (SS.poly x T)
  wt-var-poly-instantiate {sc = sc} nsg nim lp ng ins = (_ , lp , ins) , λ P → let open At P using (ref-poly; refC; retype⇐; rt⇐; subst-poly) in
    let ki = kinded-instance sc ins
        d = TView.View.entry (V P) lp
        (t , w , r) = (refC d (TView.iv-poly nsg nim lp refl) (h-poly P lp) (TView.View.entryIs (V P) lp) (proj₁ ki) (proj₁ (proj₂ ki)) (h-open P lp ng))
        p = proj₂ (proj₂ ki)
    in t , retype⇐ p w
       , trans (rt⇐ p w) (trans (cong (subst (E Z) p) (trans r (ref-poly d (h-poly-inline P lp) (h-poly P lp)))) (subst-poly p))

------------------------------------------------------------------------
-- An arrow out of a given domain
------------------------------------------------------------------------

module _ {m} {ctx : NamedCtx m} where

  private
    Z = SCx.zeroUsage {size ctx}
    gn : G.Gen → SX.Expr
    gn g = SX.RGen g

  wd-infer : ∀ {g A A′ B π π′ Ψ eE} → WI ctx g (A′ ST.⇒[ LG.mk-kind LG.Many π′ ] B) Ψ eE → (a : A <: A′) → (o : π′ LG.⊑π π)
           → WD ctx g A π B Ψ (SS.coerce (sub-arr {q = LG.Many} a (<:-refl B) o) eE)
  wd-infer {B = B} w a o = proj₁ w , λ P → let open WMP P using (w-infer) in let (_ , u , r) = proj₂ w P in _ , w-infer u a o , cong (SS.coerce (sub-arr a (<:-refl B) o)) r

  -- A polymorphic definition whose codomain's variables occur in its domain.
  wd-poly : ∀ {x A B π π′ sc sd sco body prefix}
          → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
          → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix))
          → ¬ TP.Ground sc → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
          → KindedInstance (kinds ctx) sc (A ST.⇒[ LG.mk-kind LG.Many π′ ] B) → (g : π′ LG.⊑π π)
          → WD ctx (SX.RResolved (own x)) A π B Z
               (SS.coerce (sub-arr {q = LG.Many} (<:-refl A) (<:-refl B) g) (SS.poly x (A ST.⇒[ LG.mk-kind LG.Many π′ ] B)))
  wd-poly {A = A} {B = B} {sc = sc} nsg nim lp ng arr cvd ins g = (_ , lp , ins) , λ P → let open At P using (ref-poly; refD) in
    let (X , Y , te , incl) = h-arrow P lp arr cvd
        ki = kinded-instance sc ins
        d = TView.View.entry (V P) lp
        (t , w , r) = refD d (TView.iv-poly nsg nim lp refl) (h-poly P lp) (TView.View.entryIs (V P) lp) (proj₁ ki) (proj₁ (proj₂ ki))
                            (h-open P lp ng) te incl (proj₂ (proj₂ ki)) g
    in t , w , trans r (cong (SS.coerce (sub-arr (<:-refl A) (<:-refl B) g)) (ref-poly d (h-poly-inline P lp) (h-poly P lp)))

  wd-lam : ∀ {x body A B q′ π Ψ eE} → WI (extendNamedCtx ctx x A) body B (q′ SCx.∷ Ψ) eE
         → WD ctx (SX.RLam x body) A π B Ψ (SS.lam LG.Many (≤q-Many q′) eE)
  wd-lam {x = x} {A = A} {q′ = q′} {eE = eE} w = ext-refs {ctx = ctx} {x = x} {A = A} {e = eE} (proj₁ w) , λ P → let open WMP P using (w-lam↦) in
    let (_ , u , r) = proj₂ w (pack▸ x A P) in _ , w-lam↦ u , cong (SS.lam LG.Many (≤q-Many q′)) r

  wd-compose : ∀ {f g A M B π Ψ₁ Ψ₂ fE gE} → WD ctx g A π M Ψ₂ gE → WD ctx f M π B Ψ₁ fE
             → WD ctx (SX.RApp (SX.RApp (gn G.compose) f) g) A π B (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂)) (SS.comp' fE gE)
  wd-compose wg wf = (proj₁ wf , proj₁ wg) , λ P → let open WMP P using (w-compose↦) in
    let (_ , ug , rg) = proj₂ wg P ; (_ , uf , rf) = proj₂ wf P in _ , w-compose↦ ug uf , cong₂ SS.comp' rf rg

  -- `d-map`: a structure map out of a given domain, at its least codomain.
  wd-map : ∀ {g A π B mI} → mapFrom? (kinds ctx) g A ≡ just (B , mI)
         → WD ctx (gn g) A π B Z (SS.lift-morphism mI)
  wd-map {g} {A} {π} {B} {mI} e = map-linked-from {Δ = kinds ctx} {g = g} {A = A} {B = B} {mI = mI} e , λ P → let open WMP P using (w-map↦) in
    let ok = TS.mapFrom?-sound {Δ = kinds ctx} {S = S P} {n = size ctx} g A π {B = B} {mI = mI} e
        (_ , _ , mo) = TS.FromOK.row ok
    in _ , w-map↦ (TS.FromOK.from ok) mo (TS.FromOK.least ok) , cong SS.lift-morphism (TS.FromOK.ir ok)

  wd-case : ∀ {f g A B Cf Cg C π Ψ₁ Ψ₂ fE gE} → WD ctx f A π Cf Ψ₁ fE → WD ctx g B π Cg Ψ₂ gE → (j : Cf ⊔ Cg ≔ C)
          → WD ctx (SX.RApp (SX.RApp (gn G.case) f) g) (A ST.+ B) π C (Ψ₁ SCx.+ᵘ Ψ₂)
               (SS.copair' (SS.coerce (sub-arr (<:-refl A) (<:ᶜ⇒<: (left j)) (⊑π-refl π)) fE)
                           (SS.coerce (sub-arr (<:-refl B) (<:ᶜ⇒<: (right j)) (⊑π-refl π)) gE))
  wd-case {A = A} {B = B} {π = π} wf wg j = (proj₁ wf , proj₁ wg) , λ P → let open WMP P using (w-case↦) in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P
    in _ , w-case↦ uf ug j
       , cong₂ (λ a b → SS.copair' (SS.coerce (sub-arr (<:-refl A) (<:ᶜ⇒<: (left j)) (⊑π-refl π)) a)
                                   (SS.coerce (sub-arr (<:-refl B) (<:ᶜ⇒<: (right j)) (⊑π-refl π)) b)) rf rg

  wd-pair : ∀ {f g A B C π Ψ₁ Ψ₂ fE gE} → WD ctx f A π B Ψ₁ fE → WD ctx g A π C Ψ₂ gE
          → WD ctx (SX.RApp (SX.RApp (gn G.pair) f) g) A π (B ST.* C) (Ψ₁ SCx.+ᵘ Ψ₂) (SS.fork' fE gE)
  wd-pair wf wg = (proj₁ wf , proj₁ wg) , λ P → let open WMP P using (w-pair↦) in
    let (_ , uf , rf) = proj₂ wf P ; (_ , ug , rg) = proj₂ wg P in _ , w-pair↦ uf ug , cong₂ SS.fork' rf rg

  -- `d-cata`: the fold at the algebra's codomain; the algebra converted.
  wd-cata : ∀ {alg F A₁ A π′ π Ψ eE} → (wf : ST.WFFun (kinds ctx) F)
          → WI ctx alg (A₁ ST.⇒[ LG.mk-kind LG.Many π′ ] A) Ψ eE → (p : ST.⟦ F ⟧F A <: A₁) → (o : π′ LG.⊑π π)
          → WD ctx (SX.RApp (gn G.cata) alg) (ST.μ F) π A (LG.Many SCx.*ᵘ Ψ)
               (SS.cata wf (SS.coerce (sub-arr {q = LG.Many} p (<:-refl A) o) eE))
  wd-cata {A = A} wf w p o = proj₁ w , λ P → let open WMP P using (w-cata↦) in
    let (_ , u , r) = proj₂ w P in _ , w-cata↦ wf u p o , cong (λ x → SS.cata wf (SS.coerce (sub-arr p (<:-refl A) o) x)) r
