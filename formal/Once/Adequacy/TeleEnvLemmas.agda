-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.TeleEnvLemmas — plan 0.103 6b, leg C.4: THE WALK'S
-- ENVIRONMENTS, AS FUNCTIONS OF WHAT THEY LOOK UP.
--
-- The walk relates the compiled program's environment (`σW`: calls of the
-- function table, references spliced by the resolver) to the scope's surface
-- environment, entry by entry. Leg A reads that environment only through two
-- lookups:
--   * `callSD n U`: the call of the table entry `n`;
--   * `refs σ y U`: the resolver's splice of the telescope entry `y`.
-- So the relation moves between environments that agree on those lookups
-- (`envrel-transport`, `imprel-transport`). The lookups themselves:
--   * a reference is a function of `lookupPolyPrefix`'s answer only
--     (`refs-lookup`), so a later entry of another name does not change it
--     (`refs-skip`), and the head entry splices its own body (`refs-head`);
--   * a call skips table entries of other names (`tableEnv-later`), and
--     `refIR` reads the environment at its one name (`refIR-cong`).
------------------------------------------------------------------------

open import Once.TypeCheck.Classify using (TopCtx)
open import Once.Target.Arch using (TargetNum)

open import Once.SigOp.Info using (FFIAnswers)

-- Plan 0.105: over the interpretation's FFI half `φ`.
module Once.Adequacy.TeleEnvLemmas (fmt : TargetNum) (φ : FFIAnswers) where

open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.String using (String)
import Data.String.Properties as StrProp
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Induction.WellFounded using (Acc; acc)

open import Once.Postulates using (extensionality)
open import Once.Type using (Type; PolyType; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; mk-kind;
  Zero; One; Many; μ-type; ν-type; rigid)
open import Once.IRTy using (IRTy)
open import Once.CanonicalName using (CanonicalName; bare)
open import Once.IR.Ref using (refIR)
import Once.Surface.Syntax as Srf
import Once.Denotation.SourceDenote as SD
open import Once.Denotation.TraceMonad using (T)
open import Once.Denotation.DenotTrace using (evalᴰ; CallEnv; callsE; ⟦_⟧ᴰᴵ; cohᴰ)
open import Once.Denotation.Program using (IRFun; fname; tableEnv; tableCalls)
open import Once.Denotation.Meaning using (DefMeanings; ImpMeanings)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (PolyCtx; lookupPolyPrefix; Imports; ctxWithImportsAndPolys)
open import Once.Adequacy.TelePosition using (lookup-skip; lookup-head)
open import Once.TypeCheck.Elaborate using (success; failure; checkElabV; VerifiedCheckResult)
open import Once.Denotation.Realize using (realize)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr; resolveExprWF; resolvePolyCase; applySplice)
import Once.Adequacy.ResolveFaithful as RF
import Once.Adequacy.MeaningBridge as MB
open import Once.Adequacy.GradedRelation fmt using (RelGM)
open import Once.Type using (pure)
open import Once.Adequacy.TableCall fmt φ using (tableEnv-skip)

------------------------------------------------------------------------
-- The walk's environment
------------------------------------------------------------------------

-- Calls of a table, references spliced in `P` with declaration imports `I`.
σW : List IRFun → PolyCtx → (String → TopCtx) → Imports → SD.DefsSem
σW tbl P I uf = RF.σR fmt (tableEnv fmt φ tbl) P I uf 0

------------------------------------------------------------------------
-- A reference, as a function of the lookup's answer
------------------------------------------------------------------------

acc-irrel : ∀ {n : ℕ} (a b : Acc _<_ n) → a ≡ b
acc-irrel (acc f) (acc g) =
  cong acc (cong (λ H {y} → H y) (extensionality λ y → extensionality λ p → acc-irrel (f {y} p) (g {y} p)))

module _ (I : String → TopCtx) (uf : Imports) where

  -- D254: the spliced body is the realization of its derivation.
  spliceClosed : ∀ {A} {b : RawExpr} (pre : PolyCtx) (x : String) {Xs : TopCtx}
               → VerifiedCheckResult (ctxWithImportsAndPolys Xs pre) b A → Srf.Expr Srf.∅ Srf.zeroUsage A
  spliceClosed {A} pre x (failure _ , _)             = Srf.poly x A
  spliceClosed     pre x (success Srf.[] eE _ _ , w) = Srf.closed (resolveExpr pre I uf 0 (realize w))

  polyVal : (x : String) (A : Type) → Maybe (PolyType × RawExpr × PolyCtx) → Srf.Expr Srf.∅ Srf.zeroUsage A
  polyVal x A nothing                 = Srf.poly x A
  polyVal x A (just (_ , body , pre)) = spliceClosed pre x (checkElabV (ctxWithImportsAndPolys (I x) pre) body A)

  private
    splice-val : ∀ (L : PolyCtx) (a : Acc _<_ (length L)) (x : String) (A : Type) {s b pre}
      (eq : lookupPolyPrefix L x ≡ just (s , b , pre)) (r : VerifiedCheckResult (ctxWithImportsAndPolys (I x) pre) b A)
      → applySplice {Γ = Srf.∅} L a I uf 0 x A eq r ≡ spliceClosed pre x r
    splice-val L a x A eq (failure _ , _) = refl
    splice-val L (acc rec) x A {pre = pre} eq (success Srf.[] eE _ _ , w) =
      cong (λ z → Srf.closed (resolveExprWF pre z I uf 0 (realize w))) (acc-irrel _ _)

    case-val : ∀ (L : PolyCtx) (a : Acc _<_ (length L)) (x : String) (A : Type)
      (look : Maybe _) (eq : lookupPolyPrefix L x ≡ look)
      → resolvePolyCase {Γ = Srf.∅} L a I uf 0 x A look eq ≡ polyVal x A look
    case-val L a x A nothing eq = refl
    case-val L a x A (just (s , body , pre)) eq =
      splice-val L a x A eq (checkElabV (ctxWithImportsAndPolys (I x) pre) body A)

  refs-lookup : ∀ (ρ : CallEnv) (L : PolyCtx) (x : String) (A : Type)
    → SD.refs (RF.σR fmt ρ L I uf 0) x A ≡ SD.⟦ polyVal x A (lookupPolyPrefix L x) ⟧ˢ fmt (RF.σ₀ fmt ρ) tt
  refs-lookup ρ L x A = cong (λ e → SD.⟦ e ⟧ˢ fmt (RF.σ₀ fmt ρ) tt)
                             (case-val L (<-wellFounded (length L)) x A (lookupPolyPrefix L x) refl)

module _ (I : String → TopCtx) (uf : Imports) (ρ : CallEnv) where

  refs-skip : ∀ (n : String) {s b} (L : PolyCtx) (y : String) (A : Type) → n ≢ y
    → SD.refs (RF.σR fmt ρ ((n , s , b) ∷ L) I uf 0) y A ≡ SD.refs (RF.σR fmt ρ L I uf 0) y A
  refs-skip n {s} {b} L y A n≢y =
    trans (refs-lookup I uf ρ ((n , s , b) ∷ L) y A)
          (trans (cong (λ l → SD.⟦ polyVal I uf y A l ⟧ˢ fmt (RF.σ₀ fmt ρ) tt) (lookup-skip n L y n≢y))
                 (sym (refs-lookup I uf ρ L y A)))

  refs-head : ∀ (n : String) {s b} (L : PolyCtx) (A : Type)
    → SD.refs (RF.σR fmt ρ ((n , s , b) ∷ L) I uf 0) n A
      ≡ SD.⟦ spliceClosed I uf L n (checkElabV (ctxWithImportsAndPolys (I n) L) b A) ⟧ˢ fmt (RF.σ₀ fmt ρ) tt
  refs-head n {s} {b} L A =
    trans (refs-lookup I uf ρ ((n , s , b) ∷ L) n A)
          (cong (λ l → SD.⟦ polyVal I uf n A l ⟧ˢ fmt (RF.σ₀ fmt ρ) tt) (lookup-head n L))

------------------------------------------------------------------------
-- Moving the relation between environments that agree on the lookups
------------------------------------------------------------------------

RefsAgree : SD.DefsSem → SD.DefsSem → PolyCtx → Set
RefsAgree σ₁ σ₂ []                   = ⊤
RefsAgree σ₁ σ₂ ((n , _ , _) ∷ rest) = (∀ A → SD.refs σ₁ n A ≡ SD.refs σ₂ n A) × RefsAgree σ₁ σ₂ rest

envrel-transport : ∀ (σ₁ σ₂ : SD.DefsSem) (polys : PolyCtx) {ρ : DefMeanings polys}
  → RefsAgree σ₁ σ₂ polys → MB.EnvRel fmt σ₁ polys ρ → MB.EnvRel fmt σ₂ polys ρ
envrel-transport σ₁ σ₂ []                   _        _        = tt
envrel-transport σ₁ σ₂ ((n , s , _) ∷ rest) {e , ρ} (h , hs) (r , rs) =
  (λ U ki → subst (RelGM pure U (e U ki)) (h U) (r U ki)) , envrel-transport σ₁ σ₂ rest hs rs

CallsAgree : SD.DefsSem → SD.DefsSem → Imports → Set
CallsAgree σ₁ σ₂ []               = ⊤
CallsAgree σ₁ σ₂ ((n , U) ∷ rest) = MB.callSD fmt σ₁ n U ≡ MB.callSD fmt σ₂ n U × CallsAgree σ₁ σ₂ rest

imprel-transport : ∀ (σ₁ σ₂ : SD.DefsSem) (imps : Imports) {ι : ImpMeanings imps}
  → CallsAgree σ₁ σ₂ imps → MB.ImpRel fmt σ₁ imps ι → MB.ImpRel fmt σ₂ imps ι
imprel-transport σ₁ σ₂ []               _        _        = tt
imprel-transport σ₁ σ₂ ((n , U) ∷ rest) {e , ι} (h , hs) (r , rs) =
  subst (RelGM pure U e) h r , imprel-transport σ₁ σ₂ rest hs rs

------------------------------------------------------------------------
-- Calls
------------------------------------------------------------------------

-- A call reads the environment at its one name.
refIR-cong : ∀ (U : Type) (f : CanonicalName) (ρ₁ ρ₂ : CallEnv)
  → (∀ (A B : IRTy) (a : ⟦ A ⟧ᴰᴵ) → callsE ρ₁ f A B a ≡ callsE ρ₂ f A B a)
  → evalᴰ fmt ρ₁ (refIR U f) tt ≡ evalᴰ fmt ρ₂ (refIR U f) tt
refIR-cong (A ⇒[ mk-kind Zero π ] B) f ρ₁ ρ₂ h = cong (λ g → Once.Denotation.TraceMonad.returnT g) (extensionality λ b → h _ _ b)
refIR-cong (A ⇒[ mk-kind One  π ] B) f ρ₁ ρ₂ h = cong (λ g → Once.Denotation.TraceMonad.returnT g) (extensionality λ b → h _ _ b)
refIR-cong (A ⇒[ mk-kind Many π ] B) f ρ₁ ρ₂ h = cong (λ g → Once.Denotation.TraceMonad.returnT g) (extensionality λ b → h _ _ b)
refIR-cong Unit         f ρ₁ ρ₂ h = h _ _ tt
refIR-cong Void         f ρ₁ ρ₂ h = h _ _ tt
refIR-cong (A * B)      f ρ₁ ρ₂ h = h _ _ tt
refIR-cong (A + B)      f ρ₁ ρ₂ h = h _ _ tt
refIR-cong (μ-type F)   f ρ₁ ρ₂ h = h _ _ tt
refIR-cong (ν-type F π) f ρ₁ ρ₂ h = h _ _ tt
refIR-cong Int          f ρ₁ ρ₂ h = h _ _ tt
refIR-cong Float        f ρ₁ ρ₂ h = h _ _ tt
refIR-cong (rigid k i)  f ρ₁ ρ₂ h = h _ _ tt

-- Entries declared later, of other names, do not change a call.
tableEnv-later : ∀ (later pre : List IRFun) (f : CanonicalName) → All (λ e → fname e ≢ f) later
  → ∀ (A B : IRTy) (a : ⟦ A ⟧ᴰᴵ) → tableCalls fmt φ (later ++ pre) f A B a ≡ tableCalls fmt φ pre f A B a
tableEnv-later []          pre f []         A B a = refl
tableEnv-later (e ∷ later) pre f (ne ∷ nes) A B a =
  trans (tableEnv-skip e (later ++ pre) ne a) (tableEnv-later later pre f nes A B a)

callSD-later : ∀ (later pre : List IRFun) (P : PolyCtx) (I : String → TopCtx) (uf : Imports) (x : String) (U : Type)
  → All (λ e → fname e ≢ bare x) later
  → MB.callSD fmt (σW (later ++ pre) P I uf) x U ≡ MB.callSD fmt (σW pre P I uf) x U
callSD-later later pre P I uf x U nes =
  cong (subst T (cohᴰ U)) (refIR-cong U (bare x) _ _ (tableEnv-later later pre (bare x) nes))

-- Two walk environments over one table make the same calls.
calls-same : ∀ (tbl : List IRFun) (P P′ : PolyCtx) (I I′ : String → TopCtx) (uf uf′ : Imports) (imps : Imports)
           → CallsAgree (σW tbl P I uf) (σW tbl P′ I′ uf′) imps
calls-same tbl P P′ I I′ uf uf′ []             = tt
calls-same tbl P P′ I I′ uf uf′ ((n , U) ∷ is) = refl , calls-same tbl P P′ I I′ uf uf′ is
