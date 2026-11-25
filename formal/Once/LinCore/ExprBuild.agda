-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ExprBuild — plan 0.146 B1.7 (D460–D462): THE BRIDGE'S
-- PROGRAM, built from the definitions' sources. Over `fmt` only (as D459's
-- lowering), so the compiler builds it (`LinCore.Emit`); its meaning against
-- master's is `ExprTable`'s.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.LinCore.ExprBuild (fmt : TargetNum) where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Product using (proj₁; proj₂; Σ; _×_)
open import Data.Unit using (tt)
import Data.Unit
import Data.Bool
open import Once.Compile using (directCallIR; irFunOf; tableOf-go; tableOf; CompiledFun; EffUU; mainEntry)
open import Once.Spec.Sub using (_<:_; sub-arr; sub-unit; sub-void)
open import Once.CompileSrc using (toCF)
import Once.Spec.Grade as G
open import Once.Spec.Type using (Ty; Type; _⇒[_]_)
import Once.Spec.Type as ST
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_)
open import Once.Context using (⟦_⟧ᶜ; _↾_)
open import Once.IRTy using (⌊_⌋)
import Once.IR as M
open import Once.LinCore.Core fmt
open import Once.IR.Semantics.Trace using (T)
open import Once.LinCore.FromExpr fmt using (ty; Co; apω; k-apω; cast; k-cast; gdB)
open import Once.LinCore.FromIR fmt using (grade)
open import Relation.Binary.PropositionalEquality using (cong; subst)
open import Once.LinCore.FromIR fmt using (⟪_⟫)
open import Once.LinCore.FromExpr fmt using (Rs; Lq; Lq-blk; callM; refL)
open import Once.Spec.Name using (bare)
open import Data.String using (String)
open import Once.CompileSrc using (CompiledSrc; module CompiledSrc)
open CompiledSrc using (csName; csType; csSrc)
open import Once.IRTy using (_≟IRTy_)
open import Once.CanonicalName using (_≟ᶜ_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Once.CompileSrc using (Src; src; srcIR; module Src)
open Src using (expr; am)
open import Once.Denotation.SurfaceRefs using (Refs)
open import Once.Adequacy.ElaborateLinked using (DeclIn)
open import Once.Contract using (ISig)
open import Once.Denotation.Program using (IRFun; irFun)
open import Once.Spec.Name using (CanonicalName)
open import Once.IRTy using (IRTy)

------------------------------------------------------------------------
-- 1. ERASURE: the variables a usage leaves out, dropped (`eraseCtx`).
------------------------------------------------------------------------

module _ {L : Cx} {E : LTy} where

  eraseL : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → Tm L E ⟪ ⌊ ⟦ Γ ⟧ᶜ ⌋ ⟫ (Co Γ Ψ)
  eraseL SC.∅          []           = lid
  eraseL (Γ SC.▸ A) (G.Zero ∷ Ψ) = eraseL Γ Ψ ∘l (ρl ∘l (lid ⊗l drop))
  eraseL (Γ SC.▸ A) (G.One  ∷ Ψ) = eraseL Γ Ψ ⊗l lid
  eraseL (Γ SC.▸ A) (G.Many ∷ Ψ) = eraseL Γ Ψ ⊗l lid

  k-eraseL : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → Blk (eraseL Γ Ψ)
  k-eraseL SC.∅          []           = k-id
  k-eraseL (Γ SC.▸ A) (G.Zero ∷ Ψ) = k-∘ (k-eraseL Γ Ψ) (k-∘ k-ρ (k-⊗ k-id k-drop))
  k-eraseL (Γ SC.▸ A) (G.One  ∷ Ψ) = k-⊗ (k-eraseL Γ Ψ) k-id
  k-eraseL (Γ SC.▸ A) (G.Many ∷ Ψ) = k-⊗ (k-eraseL Γ Ψ) k-id


------------------------------------------------------------------------
-- 2. A DEFINITION'S BODY, in `Compile.directCallIR`'s shape: an arrow's
-- closure applied to the argument, any other value on `tt`.
------------------------------------------------------------------------

dcDom dcCod : Type → Type
dcDom (A ⇒[ G.mk-kind G.Zero π ] B) = ST.Unit
dcDom (A ⇒[ G.mk-kind G.One π ] B)  = A
dcDom (A ⇒[ G.mk-kind G.Many π ] B) = A
dcDom ST.Unit = ST.Unit
dcDom ST.Void = ST.Unit
dcDom (X ST.* Y) = ST.Unit
dcDom (X ST.+ Y) = ST.Unit
dcDom (ST.μ F) = ST.Unit
dcDom (ST.ν F f) = ST.Unit
dcDom ST.Int = ST.Unit
dcDom ST.Float = ST.Unit
dcDom (ST.var ())
dcCod (A ⇒[ G.mk-kind q π ] B) = B
dcCod T@ST.Unit = T
dcCod T@ST.Void = T
dcCod T@(X ST.* Y) = T
dcCod T@(X ST.+ Y) = T
dcCod T@(ST.μ F) = T
dcCod T@(ST.ν F f) = T
dcCod T@ST.Int = T
dcCod T@ST.Float = T
dcCod (ST.var ())

-- the label's grade: the arrow's, a value's a block
dcGr : Type → Gr
dcGr (A ⇒[ G.mk-kind q π ] B) = grade π
dcGr ST.Unit = act
dcGr ST.Void = act
dcGr (X ST.* Y) = act
dcGr (X ST.+ Y) = act
dcGr (ST.μ F) = act
dcGr (ST.ν F f) = act
dcGr ST.Int = act
dcGr ST.Float = act
dcGr (ST.var ())

module _ {L : Cx} where

  dc : (T : Type) → LTm L One (ty T) → LTm L (ty (dcDom T)) (ty (dcCod T))
  dc (A ⇒[ G.mk-kind G.Zero π ] B) v = apω ∘l ((v ⊗l lid) ∘l lul⁻)
  dc (A ⇒[ G.mk-kind G.One π ] B)  v = apω ∘l ((v ⊗l lid) ∘l lul⁻)
  dc (A ⇒[ G.mk-kind G.Many π ] B) v = apω ∘l ((v ⊗l lid) ∘l lul⁻)
  dc ST.Unit v = v
  dc ST.Void v = v
  dc (X ST.* Y) v = v
  dc (X ST.+ Y) v = v
  dc (ST.μ F) v = v
  dc (ST.ν F f) v = v
  dc ST.Int v = v
  dc ST.Float v = v
  dc (ST.var ()) v

  -- a body's grade, when its blockness needs the grade to be finite
  gdT : ∀ {X Y} (π : G.Purity) (t : LTm L X Y) → (∀ {φ} → π ≡ G.fin φ → Blk t) → Gd (grade π) t
  gdT (G.fin φ) t h = h refl
  gdT G.eff     t h = tt

  -- the label's body: one-shot, over `One`, at its grade
  dcGd : ∀ (T : Type) {v : LTm L One (ty T)} → Blk v → Gd (dcGr T) (dc T v ∘l lul)
  dcGd (A ⇒[ G.mk-kind G.Zero π ] B) {v} β =
    gdT π (dc (A ⇒[ G.mk-kind G.Zero π ] B) v ∘l lul) (λ { refl → k-∘ (k-∘ k-apω (k-∘ (k-⊗ β k-id) k-lul⁻)) k-lul })
  dcGd (A ⇒[ G.mk-kind G.One π ] B) {v} β =
    gdT π (dc (A ⇒[ G.mk-kind G.One π ] B) v ∘l lul) (λ { refl → k-∘ (k-∘ k-apω (k-∘ (k-⊗ β k-id) k-lul⁻)) k-lul })
  dcGd (A ⇒[ G.mk-kind G.Many π ] B) {v} β =
    gdT π (dc (A ⇒[ G.mk-kind G.Many π ] B) v ∘l lul) (λ { refl → k-∘ (k-∘ k-apω (k-∘ (k-⊗ β k-id) k-lul⁻)) k-lul })
  dcGd T@ST.Unit      β = k-∘ β k-lul
  dcGd T@ST.Void      β = k-∘ β k-lul
  dcGd T@(_ ST.* _)   β = k-∘ β k-lul
  dcGd T@(_ ST.+ _)   β = k-∘ β k-lul
  dcGd T@(ST.μ _)     β = k-∘ β k-lul
  dcGd T@(ST.ν _ _)   β = k-∘ β k-lul
  dcGd T@ST.Int       β = k-∘ β k-lul
  dcGd T@ST.Float     β = k-∘ β k-lul
  dcGd T@(ST.var ())  β

-- `directCallIR`, by the same cases, at the call types above
dcIR : (T : Type) → M.IR ⌊ ST.Unit {0} ⌋ ⌊ T ⌋ → M.IR ⌊ dcDom T ⌋ ⌊ dcCod T ⌋
dcIR (A ⇒[ G.mk-kind G.Zero π ] B) ir = M.apply M.∘ M.⟨ ir M.∘ M.terminal , M.id ⟩
dcIR (A ⇒[ G.mk-kind G.One π ] B)  ir = M.apply M.∘ M.⟨ ir M.∘ M.terminal , M.id ⟩
dcIR (A ⇒[ G.mk-kind G.Many π ] B) ir = M.apply M.∘ M.⟨ ir M.∘ M.terminal , M.id ⟩
dcIR ST.Unit ir = ir
dcIR ST.Void ir = ir
dcIR (X ST.* Y) ir = ir
dcIR (X ST.+ Y) ir = ir
dcIR (ST.μ F) ir = ir
dcIR (ST.ν F f) ir = ir
dcIR ST.Int ir = ir
dcIR ST.Float ir = ir
dcIR (ST.var ()) ir

-- ★ master's direct call is this one
dc-eq : (T : Type) (ir : M.IR ⌊ ST.Unit {0} ⌋ ⌊ T ⌋) → directCallIR T ir ≡ (dcDom T , dcCod T , dcIR T ir)
dc-eq (A ⇒[ G.mk-kind G.Zero π ] B) ir = refl
dc-eq (A ⇒[ G.mk-kind G.One π ] B)  ir = refl
dc-eq (A ⇒[ G.mk-kind G.Many π ] B) ir = refl
dc-eq ST.Unit ir = refl
dc-eq ST.Void ir = refl
dc-eq (X ST.* Y) ir = refl
dc-eq (X ST.+ Y) ir = refl
dc-eq (ST.μ F) ir = refl
dc-eq (ST.ν F f) ir = refl
dc-eq ST.Int ir = refl
dc-eq ST.Float ir = refl
dc-eq (ST.var ()) ir


------------------------------------------------------------------------
-- 3. A SOURCE'S VALUE: its bridge after erasure, at the unit context.
------------------------------------------------------------------------

val : ∀ {L T} → Rs L → Src T → LTm L One (ty T)
val rs (src {Γ = Γ} {Ψ = Ψ} δ₀ m opt e) = cast (cong ⟪_⟫ (cong ⌊_⌋ δ₀)) refl (Lq rs e ∘l eraseL Γ Ψ)


------------------------------------------------------------------------
-- 4. THE TABLE: the definitions, oldest first (the list's last), each body
-- over the labels before it; the resolver keyed with the grade (D462).
------------------------------------------------------------------------

k-val : ∀ {L T} (rs : Rs L) (s : Src T) → Blk (val rs s)
k-val rs (src {Γ = Γ} {Ψ = Ψ} δ₀ m opt e) = k-cast (cong ⟪_⟫ (cong ⌊_⌋ δ₀)) refl (k-∘ (Lq-blk rs e) (k-eraseL Γ Ψ))

-- a definition's label
sgOf : CompiledSrc → Sg
sgOf c = sg once (dcGr (csType c)) One (ty (dcDom (csType c))) (ty (dcCod (csType c)))

bodyOf : ∀ {L} (rs : Rs L) (c : CompiledSrc) → Body L (sgOf c)
bodyOf rs c = b1 (dc (csType c) (val rs (csSrc c)) ∘l lul) (dcGd (csType c) (k-val rs (csSrc c)))

_≟Gr_ : (g g′ : Gr) → Dec (g ≡ g′)
act ≟Gr act = yes refl
act ≟Gr eff = no λ ()
eff ≟Gr act = no λ ()
eff ≟Gr eff = yes refl

-- a resolution, one label further down
weakR : ∀ {L σ g A B} → Maybe (Σ ℕ λ l → L ∋[ l ] sg once g One A B) → Maybe (Σ ℕ λ l → (L ▸ σ) ∋[ l ] sg once g One A B)
weakR = Data.Maybe.map λ { (l , p) → l , there p }

-- one more definition: its label answers its name, its call types and its grade
extendR-at : ∀ {L} (rs : Rs L) (c : CompiledSrc) f A B g
           → Dec (csName c ≡ f) → Dec (⌊ dcDom (csType c) ⌋ ≡ A) → Dec (⌊ dcCod (csType c) ⌋ ≡ B) → Dec (dcGr (csType c) ≡ g)
           → Maybe (Σ ℕ λ l → (L ▸ sgOf c) ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫)
extendR-at {L} rs c f A B g (yes _) (yes p) (yes q) (yes r) =
  just (len L , subst₂ (λ X Y → (L ▸ sgOf c) ∋[ len L ] sg once g One ⟪ X ⟫ ⟪ Y ⟫) p q
                       (subst (λ g′ → (L ▸ sgOf c) ∋[ len L ] sg once g′ One (ty (dcDom (csType c))) (ty (dcCod (csType c)))) r here))
-- (the name and the types are this definition's, which master's lookup stops at: another grade misses)
extendR-at rs c f A B g (yes _) (yes _) (yes _) (no _) = nothing
extendR-at rs c f A B g (yes _) (yes _) (no _)  _      = weakR (rs f A B g)
extendR-at rs c f A B g (yes _) (no _)  _       _      = weakR (rs f A B g)
extendR-at rs c f A B g (no _)  _       _       _      = weakR (rs f A B g)

extendR : ∀ {L} (rs : Rs L) (c : CompiledSrc) → Rs (L ▸ sgOf c)
extendR rs c f A B g = extendR-at rs c f A B g (csName c ≟ᶜ f) (⌊ dcDom (csType c) ⌋ ≟IRTy A) (⌊ dcCod (csType c) ⌋ ≟IRTy B) (dcGr (csType c) ≟Gr g)

record ETProg : Set where
  constructor etProg
  field
    {L}  : Cx
    defs : Defs L
    rs   : Rs L
open ETProg

-- ★ the table, as `FromIR.trTable` builds its own: the earliest definition the list's last
exprTable : List CompiledSrc → ETProg
exprTable []       = etProg ε (λ _ _ _ _ → nothing)
exprTable (c ∷ cs) = etProg (defs (exprTable cs) ▸ bodyOf (rs (exprTable cs)) c) (extendR (rs (exprTable cs)) c)


irE : CompiledSrc → IRFun
irE c = irFun (csName c) ⌊ dcDom (csType c) ⌋ ⌊ dcCod (csType c) ⌋ (dcIR (csType c) (srcIR (csSrc c)))

tblOf : List CompiledSrc → List IRFun
tblOf = Data.List.map irE


Graded : ∀ {L} → Rs L → CanonicalName → IRTy → IRTy → Gr → Set
Graded rs f A B g = ∀ g′ {h} → rs f A B g′ ≡ just h → g′ ≡ g

-- a reference's key (`refL`'s, case for case)
GradedRef : ∀ {L} → Rs L → ∀ {m} → String → Ty m → Set
GradedRef rs x (A ⇒[ G.mk-kind G.Zero π ] B) = Graded rs (bare x) Once.IRTy.Unit ⌊ B ⌋ (grade π)
GradedRef rs x (A ⇒[ G.mk-kind G.One π ] B)  = Graded rs (bare x) ⌊ A ⌋ ⌊ B ⌋ (grade π)
GradedRef rs x (A ⇒[ G.mk-kind G.Many π ] B) = Graded rs (bare x) ⌊ A ⌋ ⌊ B ⌋ (grade π)
GradedRef rs x T@ST.Unit = Graded rs (bare x) Once.IRTy.Unit ⌊ T ⌋ act
GradedRef rs x T@ST.Void = Graded rs (bare x) Once.IRTy.Unit ⌊ T ⌋ act
GradedRef rs x T@(X ST.* Y) = Graded rs (bare x) Once.IRTy.Unit ⌊ T ⌋ act
GradedRef rs x T@(X ST.+ Y) = Graded rs (bare x) Once.IRTy.Unit ⌊ T ⌋ act
GradedRef rs x T@(ST.μ F) = Graded rs (bare x) Once.IRTy.Unit ⌊ T ⌋ act
GradedRef rs x T@(ST.ν F f) = Graded rs (bare x) Once.IRTy.Unit ⌊ T ⌋ act
GradedRef rs x T@ST.Int = Graded rs (bare x) Once.IRTy.Unit ⌊ T ⌋ act
GradedRef rs x T@ST.Float = Graded rs (bare x) Once.IRTy.Unit ⌊ T ⌋ act
GradedRef rs x T@(ST.var _) = Graded rs (bare x) Once.IRTy.Unit ⌊ T ⌋ act


GradedBodies : List CompiledSrc → Set
GradedBodies []       = Data.Unit.⊤
GradedBodies (c ∷ cs) = GradedBodies cs × (Src.opt (csSrc c) ≡ Data.Bool.false)
                      × Refs (λ _ _ → Data.Unit.⊤) (GradedRef (rs (exprTable cs))) (GradedRef (rs (exprTable cs))) (expr (csSrc c))

-- …and their FFI references declared in the signatures (master's linking premise, D257)
SrcsDecl : ISig → List CompiledSrc → Set
SrcsDecl σ []       = Data.Unit.⊤
SrcsDecl σ (c ∷ cs) = Refs (DeclIn σ) (λ _ _ → Data.Unit.⊤) (λ _ _ → Data.Unit.⊤) (expr (csSrc c)) × SrcsDecl σ cs


------------------------------------------------------------------------
-- 8. MASTER'S TABLE is the sources', in `Compile.tableOf`'s order.
------------------------------------------------------------------------

-- `tableOf`'s order: the last compiled definition first
srcOrder : List CompiledSrc → List CompiledSrc → List CompiledSrc
srcOrder []       sofar = sofar
srcOrder (c ∷ cs) sofar = srcOrder cs (c ∷ sofar)

irFunOf-irE : ∀ c → irFunOf (toCF c) ≡ irE c
irFunOf-irE c = cong (λ d → irFun (csName c) ⌊ proj₁ d ⌋ ⌊ proj₁ (proj₂ d) ⌋ (proj₂ (proj₂ d))) (dc-eq (csType c) (srcIR (csSrc c)))

tableOf-go-src : ∀ (cs sofar : List CompiledSrc)
               → tableOf-go (Data.List.map toCF cs) (tblOf sofar) ≡ tblOf (srcOrder cs sofar)
tableOf-go-src []       sofar = refl
tableOf-go-src (c ∷ cs) sofar =
  Relation.Binary.PropositionalEquality.trans
    (cong (λ e → tableOf-go (Data.List.map toCF cs) (e ∷ tblOf sofar)) (irFunOf-irE c))
    (tableOf-go-src cs (c ∷ sofar))

-- ★ master's table of a module's compiled definitions is its sources'
tableOf-src : ∀ (cs : List CompiledSrc) → tableOf (Data.List.map toCF cs) ≡ tblOf (srcOrder cs [])
tableOf-src cs = tableOf-go-src cs []


mainCore : ∀ {L} → Rs L → ∀ {ty : Type} → ty <: EffUU → LTm L One One
mainCore rs (sub-arr {π = π} a sub-unit g) = callM (rs (bare "main") Once.IRTy.Unit Once.IRTy.Unit (grade π))
mainCore rs (sub-arr {π = π} a sub-void g) = lzero ∘l callM (rs (bare "main") Once.IRTy.Unit Once.IRTy.Void (grade π))
mainCore rs sub-void                      = lzero ∘l callM (rs (bare "main") Once.IRTy.Unit Once.IRTy.Void act)

-- main's key graded (the program's obligation, as each reference's)
MainGraded : ∀ {L} → Rs L → ∀ {ty : Type} → ty <: EffUU → Set
MainGraded rs (sub-arr {π = π} a sub-unit g) = Graded rs (bare "main") Once.IRTy.Unit Once.IRTy.Unit (grade π)
MainGraded rs (sub-arr {π = π} a sub-void g) = Graded rs (bare "main") Once.IRTy.Unit Once.IRTy.Void (grade π)
MainGraded rs sub-void                      = Graded rs (bare "main") Once.IRTy.Unit Once.IRTy.Void act


------------------------------------------------------------------------
-- 10. ★ THE BRIDGE'S FACTS of a program `ir` over `tbl`: the definitions'
-- sources, their obligation (D462), master's table as theirs and its entry
-- as main's call; what the arch apex takes (`FlatTop.ExprApex`), and the
-- compile pipeline gives (`ExprLinked.bridged`).
------------------------------------------------------------------------

record Bridged (σ : ISig) (tbl : List IRFun) (ir : M.IR Once.IRTy.Unit Once.IRTy.Unit) : Set where
  field
    tl     : List CompiledSrc
    gb     : GradedBodies tl
    sd     : SrcsDecl σ tl
    mty    : Type
    mpm    : mty <: EffUU
    mg     : MainGraded (rs (exprTable tl)) mpm
    tbl-eq : tblOf tl ≡ tbl
    mir    : ir ≡ mainEntry mpm
