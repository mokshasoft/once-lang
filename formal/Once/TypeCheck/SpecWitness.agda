-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.SpecWitness — the checker's witness: the Spec's
-- derivation, in any table the scope is read through (plan 0.122 §2b-3,
-- stage d).
--
-- A checked expression's witness is, for every `Pack` of the scope — a
-- table of earlier definitions (`S`, `nm`, `inline`), a View of the
-- compiler's scope into it with what the Spec asks of the View (`Check`'s
-- hypotheses), and the scope's locals — and every scoping of the expression
-- (`RX`), the Spec's derivation of it with its usage (`TypeCheck.Witness`).
-- One constructor per rule of the checker builds it from its premises'.
------------------------------------------------------------------------

module Once.TypeCheck.SpecWitness where

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
import Once.Internal.Elaboration as E
import Once.Internal.Type.Poly as TP
open import Once.Internal.Typing.Scope using (NamedCtx; Binding; Imports; PolyCtx; lookupImport; lookupPolyPrefix; extendNamedCtx)
open NamedCtx
import Once.Spec.Surface.Typing as SUT
import Once.Adequacy.SpecFront.Locals as LocalsM
open import Once.Adequacy.SpecFront.Expr using (RX)
open import Once.Adequacy.SpecCore.Type using (tyR)
import Once.TypeCheck.Witness as WM

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
    V      : E.View Sg S (imports ctx) (sig ctx) (polys ctx)
    -- a monomorphic definition in scope: its name
    h-imp  : ∀ {x T} (lk : lookupImport (imports ctx) x ≡ just T)
           → nm (E.ImportAt.entryOf (E.View.imported V lk)) ≡ canonical (x ∷ [])
    -- a telescope definition in scope: its name; no type variables exactly when its schema is ground
    h-poly : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
           → nm (E.View.entry V lp) ≡ canonical (x ∷ [])
    h-ground : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
             → TP.Ground sc → SC.Schema.arity (S SC.!! E.View.entry V lp) ≡ 0
    h-open : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p))
           → ¬ TP.Ground sc → 0 < SC.Schema.arity (S SC.!! E.View.entry V lp)
    -- …and an arrow schema is an arrow, its codomain's variables in its domain
    h-arrow : ∀ {x sc b p} (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , b , p)) {sd sco π′}
            → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
            → Σ[ X ∈ ST.Ty (SC.Schema.arity (S SC.!! E.View.entry V lp)) ]
              Σ[ Y ∈ ST.Ty (SC.Schema.arity (S SC.!! E.View.entry V lp)) ]
                (SC.Schema.type (S SC.!! E.View.entry V lp) ≡ X ST.⇒[ LG.mk-kind LG.Many π′ ] Y)
                × (∀ i → ST.Occurs i Y → ST.Occurs i X)
    -- the scope's locals, as the Spec names them
    L      : SUT.Locals Sg S nm m (size ctx)
    lr     : LocalsM.LR Sg S nm (kinds ctx) (named ctx) (debruijn ctx) L
open Pack

-- A local bound inside the scope.
pack▸ : ∀ {m} {ctx : NamedCtx m} (x : String) (A : ST.Ty m) → Pack ctx → Pack (extendNamedCtx ctx x A)
pack▸ {ctx = ctx} x A P = record
  { Sg = Sg P ; S = S P ; nm = nm P ; inline = inline P ; V = V P
  ; h-imp = h-imp P ; h-poly = h-poly P ; h-ground = h-ground P ; h-open = h-open P ; h-arrow = h-arrow P
  ; L = SUT._▹_∶_ (L P) x A
  ; lr = LocalsM.lr-▸ (lr P) (tyR {Δ = kinds ctx} A) }

------------------------------------------------------------------------
-- The witnesses
------------------------------------------------------------------------

-- The names the locals bind.
names : ∀ {m} → List (Binding m) → List String
names = map Binding.name

WI : ∀ {m} (ctx : NamedCtx m) → SX.Expr → ST.Ty m → SCx.Usage (size ctx) → Set
WI ctx e A Ψ = (P : Pack ctx) → RX (names (named ctx)) e e
             → Σ[ t ∈ SC.Tm (S P) _ (size ctx) ] WM.W⇒ (Sg P) (S P) (nm P) (kinds ctx) (L P) e A t Ψ

WC : ∀ {m} (ctx : NamedCtx m) → SX.Expr → ST.Ty m → SCx.Usage (size ctx) → Set
WC ctx e A Ψ = (P : Pack ctx) → RX (names (named ctx)) e e
             → Σ[ t ∈ SC.Tm (S P) _ (size ctx) ] WM.W⇐ (Sg P) (S P) (nm P) (kinds ctx) (L P) e A t Ψ

WD : ∀ {m} (ctx : NamedCtx m) → SX.Expr → ST.Ty m → LG.Purity → ST.Ty m → SCx.Usage (size ctx) → Set
WD ctx e A π B Ψ = (P : Pack ctx) → RX (names (named ctx)) e e
                 → Σ[ t ∈ SC.Tm (S P) _ (size ctx) ] WM.W↦ (Sg P) (S P) (nm P) (kinds ctx) (L P) e A π B t Ψ

------------------------------------------------------------------------
-- The constructors, one per rule of the checker
------------------------------------------------------------------------

open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (nothing)
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (trans; cong)
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
open import Once.Adequacy.SpecFront.Expr
open import Once.Adequacy.SpecCore.Type using (TyR-≡)
open import Data.Unit using (⊤)

-- The Spec's rules and the compiler's View, at a pack.
module At {m} {ctx : NamedCtx m} (P : Pack ctx) where
  open WM (Sg P) (S P) (nm P) (kinds ctx) public
  open import Once.Adequacy.SpecFront.Check (Sg P) (S P) (nm P) (V P) (h-imp P) (h-poly P) (h-ground P) (h-open P) (h-arrow P) (kinds ctx)
    public using (Syn; Chk; Dom; syn; chk; dom; refS; refC; refD; syn-retype; chk-retype; not-special)
  open LocalsM (Sg P) (S P) (nm P) (kinds ctx) public using (lk-R; lk-out)
  open import Once.Adequacy.SpecFront.Types (kinds ctx) public using (annot-R)
  module SU = SUT (Sg P) (S P) (nm P)

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

  -- `Check`'s records, at the compiler's type.
  ofSyn : ∀ {e A t Ψ} → Syn (L P) e A t Ψ → Σ[ t′ ∈ SC.Tm (S P) m (size ctx) ] W⇒ (L P) e A t′ Ψ
  ofSyn (syn ra rt der) = _ , retype⇒ (sym (TyR-≡ ra)) der
  ofChk : ∀ {e A t Ψ} → Chk (L P) e A t Ψ → Σ[ t′ ∈ SC.Tm (S P) m (size ctx) ] W⇐ (L P) e A t′ Ψ
  ofChk (chk rt der) = _ , der
  retype↦ : ∀ {e A π B B′ t Ψ} → B ≡ B′ → W↦ (L P) e A π B t Ψ → W↦ (L P) e A π B′ t Ψ
  retype↦ refl w = w
  ofDom : ∀ {e A π B t Ψ} → Dom (L P) e A π B t Ψ → Σ[ t′ ∈ SC.Tm (S P) m (size ctx) ] W↦ (L P) e A π B t′ Ψ
  ofDom (dom rb rt der) = _ , retype↦ (sym (TyR-≡ rb)) der

------------------------------------------------------------------------
-- Synthesis
------------------------------------------------------------------------

module _ {m} {ctx : NamedCtx m} where

  wt-int : (n : ℤ) → WI ctx (SX.RInt n) ST.Int SCx.zeroUsage
  wt-int n P _ = _ , w-int n where open At P

  wt-float : ∀ i f l → WI ctx (SX.RFloat i f l) ST.Float SCx.zeroUsage
  wt-float i f l P _ = _ , w-float i f l where open At P

  wt-unit : WI ctx SX.RUnit ST.Unit SCx.zeroUsage
  wt-unit P _ = _ , w-unit where open At P

  wt-unit-var : WI ctx (SX.RResolved (gen "unit")) ST.Unit SCx.zeroUsage
  wt-unit-var P _ = _ , w-unit-g where open At P

  wt-var-local : ∀ {x A Ψ} {eV : Once.Internal.Context.SVar (debruijn ctx) Ψ A}
               → lookupLocal ctx x ≡ just (A , Ψ , eV) → WI ctx (SX.RVar x) A Ψ
  wt-var-local {eV = svar i} lk P _ = let (A′ , ra , mem) = lk-R (lr P) i lk in _ , retype⇒ (sym (TyR-≡ ra)) (w-var mem)
    where open At P

  wt-var-resolved : ∀ {cn T A} → Once.Spec.Name.NotGenerator cn → WordName cn
                  → lookupImport (sig ctx) (showCanonical cn) ≡ just T → IsConcrete T → A ≡ wk₀ T
                  → WI ctx (SX.RResolved cn) A SCx.zeroUsage
  wt-var-resolved {cn} {T} ng wn lk k eq P _ = res (E.View.declares (V P) lk)
    where
      open At P
      res : E.Declared (Sg P) (S P) (showCanonical cn) T → _
      res (E.declared h mem) = _ , retype⇒ (trans (⌜declS⌝ k h) (sym eq)) (w-sigop ng (mem wn refl) k (⌜declS⌝ k h))

  wt-var-own : ∀ {x T A} → lookupImport (sig ctx) x ≡ nothing → (lk : lookupImport (imports ctx) x ≡ just T) → A ≡ wk₀ T
             → WI ctx (SX.RResolved (own x)) A SCx.zeroUsage
  wt-var-own ns lk eq P _ =
    let (t , w) = ofSyn (refS {Γd = debruijn ctx} (E.ImportAt.entryOf (E.View.imported (V P) lk)) (h-imp P lk)
                               (E.ImportAt.mono (E.View.imported (V P) lk)) none (λ ())
                               (cong SC.Schema.arity (E.ImportAt.mono (E.View.imported (V P) lk))))
    in t , retype⇒ (sym eq) w
    where open At P

  -- An import is referred to by its resolved name: a bare one is a local.
  wt-var-import : ∀ {x T A} → ¬ Once.Spec.Name.GenWord x → lookupLocal ctx x ≡ nothing → lookupImport (imports ctx) x ≡ just T
                → IsConcrete T → A ≡ wk₀ T → WI ctx (SX.RVar x) A SCx.zeroUsage
  wt-var-import _ lkl _ _ _ P (x-local inb) = ⊥-elim (lk-out (lr P) inb lkl) where open At P

  wt-var-poly-instantiate-infer : ∀ {x T sc body prefix} {g : TP.Ground sc}
                                → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
                                → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix))
                                → TP.Ground sc → T ≡ TP.extractGround sc g
                                → WI ctx (SX.RResolved (own x)) T SCx.zeroUsage
  wt-var-poly-instantiate-infer {sc = sc} {g = g} _ _ lp _ eq P _ =
    let ki = kinded-instance sc (ground-kinded sc g)
        (t , w) = ofSyn (refS {Γd = debruijn ctx} (E.View.entry (V P) lp) (h-poly P lp) (E.View.entryIs (V P) lp)
                              (proj₁ ki) (proj₁ (proj₂ ki)) (h-ground P lp g))
    in t , retype⇒ (trans (proj₂ (proj₂ ki)) (sym eq)) w
    where open At P

  wt-annot : ∀ {e T A Ψ} → WC ctx e A Ψ → A ≡ wk₀ T → WI ctx (SX.RAnnot e T) A Ψ
  wt-annot {T = T} w refl P (x-annot x) =
    let a = TyR-≡ (annot-R {T} (λ ())) in _ , retype⇒ (sym a) (w-annot (retype⇐ a (proj₂ (w P x))))
    where open At P

  wt-pair : ∀ {a b A B Ψ₁ Ψ₂} → WI ctx a A Ψ₁ → WI ctx b B Ψ₂ → WI ctx (SX.RPair a b) (A ST.* B) (Ψ₁ SCx.+ᵘ Ψ₂)
  wt-pair wa wb P (x-pair xa xb) = _ , w-pair (proj₂ (wa P xa)) (proj₂ (wb P xb)) where open At P

  wt-neg : ∀ {e Ψ} → WI ctx e ST.Int Ψ → WI ctx (SX.RNeg e) ST.Int Ψ
  wt-neg w P (x-neg x) = _ , w-neg (proj₂ (w P x)) where open At P

  wt-neg-float : ∀ i f l → WI ctx (SX.RNeg (SX.RFloat i f l)) ST.Float SCx.zeroUsage
  wt-neg-float i f l P _ = _ , w-neg-float i f l where open At P

  wt-let : ∀ {x e₁ e₂ A B q Ψ₁ Ψ₂} → WI ctx e₁ A Ψ₁ → WI (extendNamedCtx ctx x A) e₂ B (q SCx.∷ Ψ₂)
         → WI ctx (SX.RLet x e₁ e₂) B (Ψ₂ SCx.+ᵘ (q SCx.*ᵘ Ψ₁))
  wt-let {x = x} {A = A} {q = q} w₁ w₂ P (x-let x₁ x₂) = _ , w-let q (proj₂ (w₁ P x₁)) (proj₂ (w₂ (pack▸ x A P) x₂)) where open At P

  wt-case : ∀ {e xl el xr er A B Cl Cr C ql qr Ψs Ψₗ Ψᵣ}
          → WI ctx e (A ST.+ B) Ψs → WI (extendNamedCtx ctx xl A) el Cl (ql SCx.∷ Ψₗ) → WI (extendNamedCtx ctx xr B) er Cr (qr SCx.∷ Ψᵣ)
          → Cl ⊔ Cr ≔ C → WI ctx (SX.RDestruct e xl el xr er) C (Ψs SCx.+ᵘ (Ψₗ ⊔ᵘ Ψᵣ))
  wt-case {xl = xl} {xr = xr} {A = A} {B = B} {ql = ql} {qr = qr} ws wl wr j P (x-destruct xs xl′ xr′) =
    _ , w-case ql qr (proj₂ (ws P xs)) (proj₂ (wl (pack▸ xl A P) xl′)) (proj₂ (wr (pack▸ xr B P) xr′)) j
    where open At P

  wt-binop-arith : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isArithmeticOp op ≡ true → WI ctx e₁ ST.Int Ψ₁ → WI ctx e₂ ST.Int Ψ₂
                 → WI ctx (SX.RBinOp op e₁ e₂) ST.Int (Ψ₁ SCx.+ᵘ Ψ₂)
  wt-binop-arith ia w₁ w₂ P (x-binop x₁ x₂) = _ , w-arith (proj₂ (arith-of ia)) (proj₂ (w₁ P x₁)) (proj₂ (w₂ P x₂)) where open At P

  wt-binop-arith-float : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isFloatArithmeticOp op ≡ true → WI ctx e₁ ST.Float Ψ₁ → WI ctx e₂ ST.Float Ψ₂
                       → WI ctx (SX.RBinOp op e₁ e₂) ST.Float (Ψ₁ SCx.+ᵘ Ψ₂)
  wt-binop-arith-float fa w₁ w₂ P (x-binop x₁ x₂) = _ , w-arith-float (proj₂ (float-of fa)) (proj₂ (w₁ P x₁)) (proj₂ (w₂ P x₂)) where open At P

  wt-binop-arith-float-il : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isFloatArithmeticOp op ≡ true → WI ctx e₁ ST.Int Ψ₁ → WI ctx e₂ ST.Float Ψ₂
                          → WI ctx (SX.RBinOp op e₁ e₂) ST.Float (Ψ₁ SCx.+ᵘ Ψ₂)
  wt-binop-arith-float-il fa w₁ w₂ P (x-binop x₁ x₂) = _ , w-arith-float-il (proj₂ (float-of fa)) (proj₂ (w₁ P x₁)) (proj₂ (w₂ P x₂)) where open At P

  wt-binop-arith-float-ir : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isFloatArithmeticOp op ≡ true → WI ctx e₁ ST.Float Ψ₁ → WI ctx e₂ ST.Int Ψ₂
                          → WI ctx (SX.RBinOp op e₁ e₂) ST.Float (Ψ₁ SCx.+ᵘ Ψ₂)
  wt-binop-arith-float-ir fa w₁ w₂ P (x-binop x₁ x₂) = _ , w-arith-float-ir (proj₂ (float-of fa)) (proj₂ (w₁ P x₁)) (proj₂ (w₂ P x₂)) where open At P

  wt-binop-cmp : ∀ {op e₁ e₂ Ψ₁ Ψ₂} → isComparisonOp op ≡ true → WI ctx e₁ ST.Int Ψ₁ → WI ctx e₂ ST.Int Ψ₂
               → WI ctx (SX.RBinOp op e₁ e₂) (ST.Unit ST.+ ST.Unit) (Ψ₁ SCx.+ᵘ Ψ₂)
  wt-binop-cmp c w₁ w₂ P (x-binop x₁ x₂) = _ , w-compare (proj₂ (cmp-of c)) (proj₂ (w₁ P x₁)) (proj₂ (w₂ P x₂)) where open At P

  -- A generator applied to a synthesizing argument.
  wt-id-app : ∀ {e T Ψ} → WI ctx e T Ψ → WI ctx (SX.RApp (SX.RResolved (gen "id")) e) T (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-id-app w P (x-app (x-res _) x) = _ , w-id-app (proj₂ (w P x)) where open At P

  wt-fst-app : ∀ {e A B Ψ} → WI ctx e (A ST.* B) Ψ → WI ctx (SX.RApp (SX.RResolved (gen "fst")) e) A (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-fst-app w P (x-app (x-res _) x) = _ , w-fst-app (proj₂ (w P x)) where open At P

  wt-snd-app : ∀ {e A B Ψ} → WI ctx e (A ST.* B) Ψ → WI ctx (SX.RApp (SX.RResolved (gen "snd")) e) B (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-snd-app w P (x-app (x-res _) x) = _ , w-snd-app (proj₂ (w P x)) where open At P

  wt-terminal-app : ∀ {e T Ψ} → WI ctx e T Ψ → WI ctx (SX.RApp (SX.RResolved (gen "terminal")) e) ST.Unit (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-terminal-app w P (x-app (x-res _) x) = _ , w-terminal-app (proj₂ (w P x)) where open At P

  wt-apply-app-infer : ∀ {e A B Ψ} → WI ctx e ((A ST.⇒[ LG.mk-kind LG.Many LG.pure ] B) ST.* A) Ψ
                     → WI ctx (SX.RApp (SX.RResolved (gen "apply")) e) B (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-apply-app-infer w P (x-app (x-res _) x) = _ , w-apply-app (proj₂ (w P x)) where open At P

  wt-apply-eff-app-infer : ∀ {e A B Ψ π} {g : LG.EffGrade π} → WI ctx e ((A ST.⇒[ LG.mk-kind LG.Many π ] B) ST.* A) Ψ
                         → WI ctx (SX.RApp (SX.RResolved (gen "apply")) e) (ST.Unit ST.⇒[ LG.mk-kind LG.Many π ] B)
                              (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-apply-eff-app-infer {g = g} w P (x-app (x-res _) x) = _ , w-apply-eff-app g (proj₂ (w P x)) where open At P

  wt-Out-app-infer : ∀ {e F C Ψ} → ST.WFFun (kinds ctx) F → ST.⟦ F ⟧F (ST.ν F LG.pureᶠ) ≡ C → WI ctx e (ST.ν F LG.pureᶠ) Ψ
                   → WI ctx (SX.RApp (SX.RResolved (gen "Out")) e) C (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-Out-app-infer wf ce w P (x-app (x-res _) x) = _ , retype⇒ ce (w-Out-app wf (proj₂ (w P x))) where open At P

  wt-Out-eff-app-infer : ∀ {e F C Ψ} → ST.WFFun (kinds ctx) F → ST.⟦ F ⟧F (ST.ν F LG.actᶠ) ≡ C → WI ctx e (ST.ν F LG.actᶠ) Ψ
                       → WI ctx (SX.RApp (SX.RResolved (gen "Out")) e) (ST.Unit ST.⇒[ LG.mk-kind LG.Many LG.act ] C)
                            (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-Out-eff-app-infer {F = F} wf ce w P (x-app (x-res _) x) =
    _ , retype⇒ (cong (ST.Unit ST.⇒[ LG.mk-kind LG.Many LG.act ]_) ce) (w-Out-act-app wf (proj₂ (w P x))) where open At P

  -- Application: the head's type synthesized, the argument checked.
  wt-app : ∀ {f x A B q Ψ₁ Ψ₂} → classifyAppHead f ≡ nothing
         → WI ctx f (A ST.⇒[ LG.mk-kind q LG.pure ] B) Ψ₁ → WC ctx x A Ψ₂
         → WI ctx (SX.RApp f x) B (Ψ₁ SCx.+ᵘ (q SCx.*ᵘ Ψ₂))
  wt-app nh wf wx P (x-app xf xx) = _ , w-app (not-special nh xf) (proj₂ (wf P xf)) (proj₂ (wx P xx)) where open At P

  wt-effApp : ∀ {f x A B Ψ₁ Ψ₂ π} {g : LG.EffGrade π} → classifyAppHead f ≡ nothing
            → WI ctx f (A ST.⇒[ LG.mk-kind LG.Many π ] B) Ψ₁ → WC ctx x A Ψ₂
            → WI ctx (SX.RApp f x) (ST.Unit ST.⇒[ LG.mk-kind LG.Many π ] B) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  wt-effApp {g = g} nh wf wx P (x-app xf xx) = _ , w-effApp (not-special nh xf) g (proj₂ (wf P xf)) (proj₂ (wx P xx)) where open At P

  -- …or the argument's type synthesized and the head checked from that domain.
  wt-app-spine : ∀ {f x X T Ψ₁ Ψ₂} → classifyAppHead f ≡ nothing
               → WI ctx x X Ψ₂ → WD ctx f X LG.pure T Ψ₁
               → WI ctx (SX.RApp f x) T (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  wt-app-spine nh wx wf P (x-app xf xx) = _ , w-app-spine (not-special nh xf) (proj₂ (wx P xx)) (proj₂ (wf P xf)) where open At P

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

  -- The generators as morphisms, at any grade.
  wt-id-check : ∀ {T π} {u : LG.pure LG.⊑π π} → WC ctx (gn "id") (T ⇒⟨ π ⟩ T) Z
  wt-id-check P _ = _ , w-id where open At P
  wt-fst-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → WC ctx (gn "fst") ((A ST.* B) ⇒⟨ π ⟩ A) Z
  wt-fst-check P _ = _ , w-fst where open At P
  wt-snd-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → WC ctx (gn "snd") ((A ST.* B) ⇒⟨ π ⟩ B) Z
  wt-snd-check P _ = _ , w-snd where open At P
  wt-terminal-morph-check : ∀ {A π} {u : LG.pure LG.⊑π π} → WC ctx (gn "terminal") (A ⇒⟨ π ⟩ ST.Unit) Z
  wt-terminal-morph-check P _ = _ , w-terminal where open At P
  wt-initial-morph-check : ∀ {A π} {u : LG.pure LG.⊑π π} → WC ctx (gn "initial") (ST.Void ⇒⟨ π ⟩ A) Z
  wt-initial-morph-check P _ = _ , w-initial where open At P
  wt-inl-morph-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → WC ctx (gn "inl") (A ⇒⟨ π ⟩ (A ST.+ B)) Z
  wt-inl-morph-check P _ = _ , w-inl where open At P
  wt-inr-morph-check : ∀ {A B π} {u : LG.pure LG.⊑π π} → WC ctx (gn "inr") (B ⇒⟨ π ⟩ (A ST.+ B)) Z
  wt-inr-morph-check P _ = _ , w-inr where open At P

  -- `compose f g`: `g`'s codomain from its domain, or `f`'s type synthesized.
  wt-compose-check-g : ∀ {f g A B C π Ψ₁ Ψ₂} → WD ctx g A π B Ψ₂ → WC ctx f (B ⇒⟨ π ⟩ C) Ψ₁
                     → WC ctx (SX.RApp (SX.RApp (gn "compose") f) g) (A ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  wt-compose-check-g wg wf P (x-app (x-app (x-res _) xf) xg) = _ , w-compose-g (proj₂ (wg P xg)) (proj₂ (wf P xf)) where open At P

  wt-compose-check-f : ∀ {f g A B C C′ π π′ Ψ₁ Ψ₂} → WI ctx f (B ⇒⟨ π′ ⟩ C′) Ψ₁ → (B ⇒⟨ π′ ⟩ C′) <: (B ⇒⟨ π ⟩ C)
                     → WC ctx g (A ⇒⟨ π ⟩ B) Ψ₂
                     → WC ctx (SX.RApp (SX.RApp (gn "compose") f) g) (A ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  wt-compose-check-f wf p wg P (x-app (x-app (x-res _) xf) xg) = _ , w-compose-f (proj₂ (wf P xf)) p (proj₂ (wg P xg)) where open At P

  wt-case-copair-check : ∀ {f g A B C π Ψ₁ Ψ₂} → WC ctx f (A ⇒⟨ π ⟩ C) Ψ₁ → WC ctx g (B ⇒⟨ π ⟩ C) Ψ₂
                       → WC ctx (SX.RApp (SX.RApp (gn "case") f) g) ((A ST.+ B) ⇒⟨ π ⟩ C) (Ψ₁ SCx.+ᵘ Ψ₂)
  wt-case-copair-check wf wg P (x-app (x-app (x-res _) xf) xg) = _ , w-case′ (proj₂ (wf P xf)) (proj₂ (wg P xg)) where open At P

  wt-pair-morph-check : ∀ {f g A B C π Ψ₁ Ψ₂} → WC ctx f (A ⇒⟨ π ⟩ B) Ψ₁ → WC ctx g (A ⇒⟨ π ⟩ C) Ψ₂
                      → WC ctx (SX.RApp (SX.RApp (gn "pair") f) g) (A ⇒⟨ π ⟩ (B ST.* C)) (Ψ₁ SCx.+ᵘ Ψ₂)
  wt-pair-morph-check wf wg P (x-app (x-app (x-res _) xf) xg) = _ , w-pair′ (proj₂ (wf P xf)) (proj₂ (wg P xg)) where open At P

  wt-curry-check : ∀ {f A B C π₀ π Ψ} {u : LG.pure LG.⊑π π₀} → WC ctx f ((A ST.* B) ⇒⟨ π ⟩ C) Ψ
                 → WC ctx (SX.RApp (gn "curry") f) (A ⇒⟨ π₀ ⟩ (B ⇒⟨ π ⟩ C)) Ψ
  wt-curry-check w P (x-app (x-res _) x) = _ , w-curry (proj₂ (w P x)) where open At P

  wt-cata-check : ∀ {alg F A π Ψ} {u : LG.pure LG.⊑π π} → ST.WFFun (kinds ctx) F → WC ctx alg (ST.⟦ F ⟧F A ⇒⟨ π ⟩ A) Ψ
                → WC ctx (SX.RApp (gn "cata") alg) (ST.μ F ⇒⟨ π ⟩ A) (LG.Many SCx.*ᵘ Ψ)
  wt-cata-check wf w P (x-app (x-res _) x) = _ , w-cata wf (proj₂ (w P x)) where open At P

  wt-ana-check : ∀ {c F A π₀ φ Ψ} {u : LG.pure LG.⊑π π₀} {ua : π₀ LG.⊑π LG.act} → ST.WFFun (kinds ctx) F
               → WC ctx c (A ⇒⟨ LG.fin φ ⟩ ST.⟦ F ⟧F A) Ψ
               → WC ctx (SX.RApp (gn "ana") c) (A ⇒⟨ π₀ ⟩ ST.ν F φ) (LG.Many SCx.*ᵘ Ψ)
  wt-ana-check {ua = ua} wf w P (x-app (x-res _) x) = _ , w-ana ua wf (proj₂ (w P x)) where open At P

  wt-loop-check : ∀ {c A B Ψ} → WC ctx c (A ⇒⟨ LG.act ⟩ (B ST.+ A)) Ψ
                → WC ctx (SX.RApp (gn "ana") c) (A ⇒⟨ LG.eff ⟩ B) (LG.Many SCx.*ᵘ Ψ)
  wt-loop-check w P (x-app (x-res _) x) = _ , w-loop (proj₂ (w P x)) where open At P

  -- A synthesized type where a supertype is expected: its conversion.
  wt-sub : ∀ {e A B Ψ} → WI ctx e A Ψ → A <: B → WC ctx e B Ψ
  wt-sub w p P x = _ , w-sub (proj₂ (w P x)) p where open At P

  wt-lam : ∀ {x body A B q q′ π Ψ} {u : LG.pure LG.⊑π π} → (q′ ≤qᵇ q) ≡ true
         → WC (extendNamedCtx ctx x A) body B (q′ SCx.∷ Ψ)
         → WC ctx (SX.RLam x body) (A ST.⇒[ LG.mk-kind q π ] B) Ψ
  wt-lam {x = x} {A = A} ≤p w P (x-lam xb) = _ , w-lam ≤p (proj₂ (w (pack▸ x A P) xb)) where open At P

  wt-pair-lit-check : ∀ {a b A B Ψ₁ Ψ₂} → WC ctx a A Ψ₁ → WC ctx b B Ψ₂ → WC ctx (SX.RPair a b) (A ST.* B) (Ψ₁ SCx.+ᵘ Ψ₂)
  wt-pair-lit-check wa wb P (x-pair xa xb) = _ , w-pair-lit (proj₂ (wa P xa)) (proj₂ (wb P xb)) where open At P

  wt-In-app-check : ∀ {e F Ψ} → ST.WFFun (kinds ctx) F → WC ctx e (ST.⟦ F ⟧F (ST.μ F)) Ψ
                  → WC ctx (SX.RApp (gn "In") e) (ST.μ F) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-In-app-check wf w P (x-app (x-res _) x) = _ , w-In-app wf (proj₂ (w P x)) where open At P

  wt-apply-check : ∀ {e A B Ψ} → WI ctx e ((A ⇒⟨ LG.pure ⟩ B) ST.* A) Ψ
                 → WC ctx (SX.RApp (gn "apply") e) B (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-apply-check w P (x-app (x-res _) x) = _ , w-apply-app′ (proj₂ (w P x)) where open At P

  wt-inl-app-check : ∀ {e A B Ψ} → WC ctx e A Ψ → WC ctx (SX.RApp (gn "inl") e) (A ST.+ B) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-inl-app-check w P (x-app (x-res _) x) = _ , w-inl-app (proj₂ (w P x)) where open At P

  wt-inr-app-check : ∀ {e A B Ψ} → WC ctx e B Ψ → WC ctx (SX.RApp (gn "inr") e) (A ST.+ B) (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-inr-app-check w P (x-app (x-res _) x) = _ , w-inr-app (proj₂ (w P x)) where open At P

  wt-initial-app-check : ∀ {e T Ψ} → WC ctx e ST.Void Ψ → WC ctx (SX.RApp (gn "initial") e) T (SCx.zeroUsage SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ))
  wt-initial-app-check w P (x-app (x-res _) x) = _ , w-initial-app (proj₂ (w P x)) where open At P

  -- A polymorphic telescope definition, at a kinded instance.
  wt-var-poly-instantiate : ∀ {x T sc body prefix}
                          → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
                          → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix))
                          → ¬ TP.Ground sc → KindedInstance (kinds ctx) sc T
                          → WC ctx (SX.RResolved (own x)) T Z
  wt-var-poly-instantiate {sc = sc} _ _ lp ng ins P _ =
    let ki = kinded-instance sc ins
        (t , w) = ofChk (refC {Γd = debruijn ctx} (E.View.entry (V P) lp) (h-poly P lp) (E.View.entryIs (V P) lp)
                              (proj₁ ki) (proj₁ (proj₂ ki)) (h-open P lp ng))
    in t , retype⇐ (proj₂ (proj₂ ki)) w
    where open At P

------------------------------------------------------------------------
-- An arrow out of a given domain
------------------------------------------------------------------------

module _ {m} {ctx : NamedCtx m} where

  private
    Z = SCx.zeroUsage {size ctx}
    gn : String → SX.Expr
    gn g = SX.RResolved (gen g)

  wd-infer : ∀ {g A A′ B π π′ Ψ} → WI ctx g (A′ ST.⇒[ LG.mk-kind LG.Many π′ ] B) Ψ → A <: A′ → π′ LG.⊑π π → WD ctx g A π B Ψ
  wd-infer w a o P x = _ , w-infer (proj₂ (w P x)) a o where open At P

  -- A polymorphic definition whose codomain's variables occur in its domain.
  wd-poly : ∀ {x A B π π′ sc sd sco body prefix}
          → lookupImport (sig ctx) x ≡ nothing → lookupImport (imports ctx) x ≡ nothing
          → (lp : lookupPolyPrefix (polys ctx) x ≡ just (sc , body , prefix))
          → ¬ TP.Ground sc → TP.ArrowSchema sc sd sco π′ → TP.CodVarsInDom sd sco
          → KindedInstance (kinds ctx) sc (A ST.⇒[ LG.mk-kind LG.Many π′ ] B) → π′ LG.⊑π π
          → WD ctx (SX.RResolved (own x)) A π B Z
  wd-poly {sc = sc} _ _ lp ng arr cvd ins g P _ =
    let (X , Y , te , incl) = h-arrow P lp arr cvd
        ki = kinded-instance sc ins
    in ofDom (refD {Γd = debruijn ctx} (E.View.entry (V P) lp) (h-poly P lp) (E.View.entryIs (V P) lp) (proj₁ ki) (proj₁ (proj₂ ki))
                   (h-open P lp ng) te incl (proj₂ (proj₂ ki)) g)
    where open At P

  wd-lam : ∀ {x body A B q′ π Ψ} {u : LG.pure LG.⊑π π} → WI (extendNamedCtx ctx x A) body B (q′ SCx.∷ Ψ)
         → WD ctx (SX.RLam x body) A π B Ψ
  wd-lam {x = x} {A = A} w P (x-lam xb) = _ , w-lam↦ (proj₂ (w (pack▸ x A P) xb)) where open At P

  wd-compose : ∀ {f g A M B π Ψ₁ Ψ₂} → WD ctx g A π M Ψ₂ → WD ctx f M π B Ψ₁
             → WD ctx (SX.RApp (SX.RApp (gn "compose") f) g) A π B (Ψ₁ SCx.+ᵘ (LG.Many SCx.*ᵘ Ψ₂))
  wd-compose wg wf P (x-app (x-app (x-res _) xf) xg) = _ , w-compose↦ (proj₂ (wg P xg)) (proj₂ (wf P xf)) where open At P

  wd-id : ∀ {A π} {u : LG.pure LG.⊑π π} → WD ctx (gn "id") A π A Z
  wd-id P _ = _ , w-id↦ where open At P
  wd-fst : ∀ {A B π} {u : LG.pure LG.⊑π π} → WD ctx (gn "fst") (A ST.* B) π A Z
  wd-fst P _ = _ , w-fst↦ where open At P
  wd-snd : ∀ {A B π} {u : LG.pure LG.⊑π π} → WD ctx (gn "snd") (A ST.* B) π B Z
  wd-snd P _ = _ , w-snd↦ where open At P
  wd-terminal : ∀ {A π} {u : LG.pure LG.⊑π π} → WD ctx (gn "terminal") A π ST.Unit Z
  wd-terminal P _ = _ , w-terminal↦ where open At P
  wd-initial : ∀ {π} {u : LG.pure LG.⊑π π} → WD ctx (gn "initial") ST.Void π ST.Void Z
  wd-initial P _ = _ , w-initial↦ where open At P

  wd-case : ∀ {f g A B Cf Cg C π Ψ₁ Ψ₂} → WD ctx f A π Cf Ψ₁ → WD ctx g B π Cg Ψ₂ → Cf ⊔ Cg ≔ C
          → WD ctx (SX.RApp (SX.RApp (gn "case") f) g) (A ST.+ B) π C (Ψ₁ SCx.+ᵘ Ψ₂)
  wd-case wf wg j P (x-app (x-app (x-res _) xf) xg) = _ , w-case↦ (proj₂ (wf P xf)) (proj₂ (wg P xg)) j where open At P

  wd-pair : ∀ {f g A B C π Ψ₁ Ψ₂} → WD ctx f A π B Ψ₁ → WD ctx g A π C Ψ₂
          → WD ctx (SX.RApp (SX.RApp (gn "pair") f) g) A π (B ST.* C) (Ψ₁ SCx.+ᵘ Ψ₂)
  wd-pair wf wg P (x-app (x-app (x-res _) xf) xg) = _ , w-pair↦ (proj₂ (wf P xf)) (proj₂ (wg P xg)) where open At P

  wd-cata : ∀ {alg F A π Ψ} {u : LG.pure LG.⊑π π} → ST.WFFun (kinds ctx) F
          → WI ctx alg (ST.⟦ F ⟧F A ST.⇒[ LG.mk-kind LG.Many π ] A) Ψ
          → WD ctx (SX.RApp (gn "cata") alg) (ST.μ F) π A (LG.Many SCx.*ᵘ Ψ)
  wd-cata wf w P (x-app (x-res _) x) = _ , w-cata↦ wf (proj₂ (w P x)) where open At P
