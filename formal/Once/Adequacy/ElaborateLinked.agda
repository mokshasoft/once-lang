-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ElaborateLinked — a surface term whose references are
-- linked elaborates to linked IR (plan 0.103 6a‴, for `ProgramLinked`).
--
-- The only calls `elaborate` emits are its references' (`refIR`, D246): every
-- other piece of the lowering — environment plumbing, the combinators'
-- closures, coercions, literals, arithmetic — is call-free.
------------------------------------------------------------------------

module Once.Adequacy.ElaborateLinked where

open import Once.Spec.Type using (Ty)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.Spec.Grade using (Zero; One; Many; mk-kind)
open import Once.Spec.Type using (Type)
open import Once.Internal.Type.Sub
open import Once.Spec.Sub using (sub-*; sub-+; sub-var)
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_; sub-*; sub-+; subᶜ-*; subᶜ-+; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν; subᶜ-void; subᶜ-var; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Type.Sub
open import Once.Internal.Laws.SubLaws
open import Once.Spec.Name using (CanonicalName; bare)
open import Once.Internal.Name using (showCanonical)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.IR using (IR)
import Once.IR as IR
open import Once.IRTy using (IRTy; ⌊_⌋; _≟IRTy_; ⌊wk₀⌋)
import Once.IRTy.WF
open import Once.IR.Ref using (refIR)
open import Once.Internal.Type.WellFormed using (IsConcrete; con-base; con-fun)
open import Once.Spec.Type using (b-*; b-+; b-Float; b-Int; b-Unit; b-Void)
open import Once.Internal.Context hiding (_,_)
open import Once.Spec.Context using ([]; _∷_; _⊑∷_; _▸_)
open import Once.Surface.Context
open import Once.Surface.Syntax
open import Once.Denotation.SurfaceRefs using (Refs)
open import Once.Surface.CoerceIR using (runCoe; runCoe-dec; voidFree?; VoidFree; coeIR; erase-eq)
open import Once.Surface.Elaborate
import Once.Surface.Properties
import Once.IRTy
open import Once.Spec.Type using (⟦_⟧F)
open import Once.Denotation.Program using (IRFun; LinkedAt; LinkedAt-at; Linked; Declared-at)
open Once.Denotation.Program.IRFun using (fcod; fdom; fname)
open import Once.Internal.Contract using (ISig; contractOf; contract-eff)
open import Once.Internal.ContractLaws using (value-∈; answer-∈)
open import Once.SigOp.Info using (SigOpInfo; SigOpSem; pureV; primV; emitsV; haltsV; ffiV; callsV)
open import Once.Arith.SigOp.Builders using (arrow-info; arrow-sem-eff)
import Once.Spec.Grade as Ty
open import Once.Spec.Type using (Void)
open import Once.Internal.Type using (isVoid?; isUnit?)
import Once.Internal.Type as SpecTy
import Once.Spec.Type as SpecTy
open import Data.List.Membership.Propositional using (_∈_)

private variable σ : ISig

------------------------------------------------------------------------
-- (A) Linkedness grows with the table: a new entry is consed on, and the
-- lookup finds the first entry at the name and objects.
------------------------------------------------------------------------

linkedAt-cons : ∀ (e : IRFun) (tbl : List IRFun) {f A B} → LinkedAt tbl f A B → LinkedAt (e ∷ tbl) f A B
linkedAt-cons e tbl {f} {A} {B} lk = go (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B)
  where
    go : ∀ d₁ d₂ d₃ → LinkedAt-at e tbl f A B d₁ d₂ d₃
    go (yes _) (yes _) (yes _) = tt
    go (yes _) (yes _) (no _)  = lk
    go (yes _) (no _)  _       = lk
    go (no _)  _       _       = lk

linkedAt-here : ∀ (e : IRFun) (es : List IRFun) → LinkedAt (e ∷ es) (fname e) (fdom e) (fcod e)
linkedAt-here e es = go (fname e ≟ᶜ fname e) (fdom e ≟IRTy fdom e) (fcod e ≟IRTy fcod e)
  where
    go : ∀ d₁ d₂ d₃ → LinkedAt-at e es (fname e) (fdom e) (fcod e) d₁ d₂ d₃
    go (yes _) (yes _) (yes _) = tt
    go (yes _) (yes _) (no ¬p) = ⊥-elim (¬p refl)
    go (yes _) (no ¬p) _       = ⊥-elim (¬p refl)
    go (no ¬p) _       _       = ⊥-elim (¬p refl)

linked-mono : ∀ {tbl tbl′ : List IRFun} → (∀ {f A B} → LinkedAt tbl f A B → LinkedAt tbl′ f A B)
            → ∀ {A B} (ir : IR A B) → Linked σ tbl ir → Linked σ tbl′ ir
linked-mono h (g IR.∘ f)       (lg , lf) = linked-mono h g lg , linked-mono h f lf
linked-mono h IR.⟨ f , g ⟩     (lf , lg) = linked-mono h f lf , linked-mono h g lg
linked-mono h (IR.case f g)    (lf , lg) = linked-mono h f lf , linked-mono h g lg
linked-mono h (IR.curry f)     lf = linked-mono h f lf
linked-mono h (IR.Cata _ alg)  la = linked-mono h alg la
linked-mono h (IR.Ana _ coalg) lc = linked-mono h coalg lc
linked-mono h (IR.Iter body) lc = linked-mono h body lc
linked-mono h (IR.Call f)      lk = h lk
linked-mono h IR.id            _ = tt
linked-mono h IR.fst           _ = tt
linked-mono h IR.snd           _ = tt
linked-mono h IR.inl           _ = tt
linked-mono h IR.inr           _ = tt
linked-mono h IR.terminal      _ = tt
linked-mono h IR.initial       _ = tt
linked-mono h IR.apply         _ = tt
linked-mono h (IR.In _)        _ = tt
linked-mono h (IR.out-μ _)     _ = tt
linked-mono h (IR.Out _)       _ = tt
linked-mono h (IR.in-ν _)      _ = tt
linked-mono h (IR.SigOp _)     d = d
linked-mono h (IR.const _ _)   _ = tt

-- Nothing is declared in the empty signatures, so an IR linked against them
-- has no FFI SigOp, and is linked against any.
private
  decl-[] : ∀ {A B} (si : SigOpInfo A B) (s : SigOpSem A B) → Declared-at [] si s → Declared-at σ si s
  decl-[] si (pureV _)  _ = tt
  decl-[] si (primV _)  _ = tt
  decl-[] si (emitsV _) _ = tt
  decl-[] si (haltsV _) _ = tt
  decl-[] si ffiV       ()
  decl-[] si callsV     ()

linked-σ : ∀ {tbl : List IRFun} {A B} (ir : IR A B) → Linked [] tbl ir → Linked σ tbl ir
linked-σ (g IR.∘ f)       (lg , lf) = linked-σ g lg , linked-σ f lf
linked-σ IR.⟨ f , g ⟩     (lf , lg) = linked-σ f lf , linked-σ g lg
linked-σ (IR.case f g)    (lf , lg) = linked-σ f lf , linked-σ g lg
linked-σ (IR.curry f)     lf = linked-σ f lf
linked-σ (IR.Cata _ alg)  la = linked-σ alg la
linked-σ (IR.Ana _ coalg) lc = linked-σ coalg lc
linked-σ (IR.Iter body) lc = linked-σ body lc
linked-σ (IR.Call f)      lk = lk
linked-σ IR.id            _ = tt
linked-σ IR.fst           _ = tt
linked-σ IR.snd           _ = tt
linked-σ IR.inl           _ = tt
linked-σ IR.inr           _ = tt
linked-σ IR.terminal      _ = tt
linked-σ IR.initial       _ = tt
linked-σ IR.apply         _ = tt
linked-σ (IR.In _)        _ = tt
linked-σ (IR.out-μ _)     _ = tt
linked-σ (IR.Out _)       _ = tt
linked-σ (IR.in-ν _)      _ = tt
linked-σ (IR.SigOp si)    d = decl-[] si (SigOpInfo.sem si) d
linked-σ (IR.const _ _)   _ = tt

linkedAt-++ : ∀ (later tbl : List IRFun) {f A B} → LinkedAt tbl f A B → LinkedAt (later ++ tbl) f A B
linkedAt-++ []          tbl lk = lk
linkedAt-++ (e ∷ later) tbl lk = linkedAt-cons e (later ++ tbl) (linkedAt-++ later tbl lk)

-- A call-free IR (linked in the empty table) is linked in every table.
linkedAt-[] : ∀ {tbl : List IRFun} {f A B} → LinkedAt [] f A B → LinkedAt tbl f A B
linkedAt-[] ()

------------------------------------------------------------------------
-- (B) The references of a surface term.
------------------------------------------------------------------------

-- (`Refs`: `Denotation.SurfaceRefs`.)

-- A reference elaborates to a call (`refIR`); it is linked when the call is.
-- An FFI reference declared in the signatures, at its declared type: the call
-- links against the declaration (`contractOf`).
DeclIn : ISig → CanonicalName → Type → Set
DeclIn σ c A = (showCanonical c , A) ∈ σ

RefLinked : ∀ {m} → ISig → List IRFun → String → Ty m → Set
RefLinked σ tbl x A = Linked σ tbl (refIR A (bare x))

Refs-map : ∀ {m} {Ps Ps′ : CanonicalName → Type → Set} {Pc Pp Pc′ Pp′ : String → Ty m → Set}
         → (∀ {A : Type} {c} → Ps c A → Ps′ c A) → (∀ {A : Ty m} {x} → Pc x A → Pc′ x A) → (∀ {A : Ty m} {x} → Pp x A → Pp′ x A)
         → ∀ {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (e : Expr Γ Ψ A) → Refs Ps Pc Pp e → Refs Ps′ Pc′ Pp′ e
Refs-map hs hc hp (var _)             r = tt
Refs-map hs hc hp (lam _ _ b)         r = Refs-map hs hc hp b r
Refs-map hs hc hp (app f x)           (a , b) = Refs-map hs hc hp f a , Refs-map hs hc hp x b
Refs-map hs hc hp (effApp f x)        (a , b) = Refs-map hs hc hp f a , Refs-map hs hc hp x b
Refs-map hs hc hp (pair x y)          (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (fst' p)            r = Refs-map hs hc hp p r
Refs-map hs hc hp (snd' p)            r = Refs-map hs hc hp p r
Refs-map hs hc hp (inl' x)            r = Refs-map hs hc hp x r
Refs-map hs hc hp (inr' x)            r = Refs-map hs hc hp x r
Refs-map hs hc hp (case' s l r′)      (a , b , c) = Refs-map hs hc hp s a , Refs-map hs hc hp l b , Refs-map hs hc hp r′ c
Refs-map hs hc hp unit                r = tt
Refs-map hs hc hp (absurd e)          r = Refs-map hs hc hp e r
Refs-map hs hc hp (let' e₁ e₂)        (a , b) = Refs-map hs hc hp e₁ a , Refs-map hs hc hp e₂ b
Refs-map hs hc hp (int _)             r = tt
Refs-map hs hc hp (float _)           r = tt
Refs-map hs hc hp (add x y)           (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (sub x y)           (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (mul x y)           (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (fadd x y)          (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (fsub x y)          (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (fmul x y)          (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (fdiv x y)          (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (i2f x)             r = Refs-map hs hc hp x r
Refs-map hs hc hp (div x y)           (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (mod' x y)          (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (neg x)             r = Refs-map hs hc hp x r
Refs-map hs hc hp (lt x y)            (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (le x y)            (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (gt x y)            (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (ge x y)            (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (eq x y)            (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (ne x y)            (a , b) = Refs-map hs hc hp x a , Refs-map hs hc hp y b
Refs-map hs hc hp (coerce _ e)        r = Refs-map hs hc hp e r
Refs-map hs hc hp (sigOp _ _)         r = hs r
Refs-map hs hc hp (closure x)         r = hc r
Refs-map hs hc hp (poly x T)          r = hp r
Refs-map hs hc hp (closed e)          r = Refs-map hs hc hp e r
Refs-map hs hc hp (lift-morphism m)   r = r
Refs-map hs hc hp (morph-app m x)     (a , b) = a , Refs-map hs hc hp x b
Refs-map hs hc hp (comp' f g)         (a , b) = Refs-map hs hc hp f a , Refs-map hs hc hp g b
Refs-map hs hc hp (copair' f g)       (a , b) = Refs-map hs hc hp f a , Refs-map hs hc hp g b
Refs-map hs hc hp (fork' f g)         (a , b) = Refs-map hs hc hp f a , Refs-map hs hc hp g b
Refs-map hs hc hp (curry' f)          r = Refs-map hs hc hp f r
Refs-map hs hc hp (cata _ alg)        r = Refs-map hs hc hp alg r
Refs-map hs hc hp (ana _ coalg)       r = Refs-map hs hc hp coalg r
Refs-map hs hc hp (loop round)        r = Refs-map hs hc hp round r


------------------------------------------------------------------------
-- (C) The lowering's own pieces are call-free.
------------------------------------------------------------------------

-- A transport of an IR's objects moves its linkedness with it.
Linked-subst : ∀ {tbl : List IRFun} {I : Set} (F G : I → IRTy) {i j} (eq : i ≡ j) (ir : IR (F i) (G i))
             → Linked σ tbl ir → Linked σ tbl (subst (λ o → IR (F o) (G o)) eq ir)
Linked-subst F G refl ir l = l

linked-[] : ∀ {tbl : List IRFun} {A B} (ir : IR A B) → Linked σ [] ir → Linked σ tbl ir

linked-[] {tbl = tbl} = linked-mono (λ {f} {A} {B} → linkedAt-[] {tbl} {f} {A} {B})

restrictEnv-cf : ∀ {mₜ} {n} {Γ : Ctx mₜ n} {Ψ Ψ′ : Usage n} (m : _) (ule : Ψ′ ⊑ᵘ Ψ) → Linked σ [] (restrictEnv {Γ = Γ} m ule)
restrictEnv-cf {Γ = ∅}         m ⊑[]          = tt
restrictEnv-cf {Γ = Γ ▸ A} m (z≤z ⊑∷ ule) = restrictEnv-cf {Γ = Γ} m ule
restrictEnv-cf {Γ = Γ ▸ A} m (z≤o ⊑∷ ule) = restrictEnv-cf {Γ = Γ} m ule , tt
restrictEnv-cf {Γ = Γ ▸ A} m (z≤m ⊑∷ ule) = restrictEnv-cf {Γ = Γ} m ule , tt
restrictEnv-cf {Γ = Γ ▸ A} m (o≤o ⊑∷ ule) = (restrictEnv-cf {Γ = Γ} m ule , tt) , tt
restrictEnv-cf {Γ = Γ ▸ A} m (o≤m ⊑∷ ule) = (restrictEnv-cf {Γ = Γ} m ule , tt) , tt
restrictEnv-cf {Γ = Γ ▸ A} m (m≤m ⊑∷ ule) = (restrictEnv-cf {Γ = Γ} m ule , tt) , tt

projUsed-cf : ∀ {m} {n} {Γ : Ctx m n} (i : Fin n) → Linked σ [] (projUsed {Γ = Γ} i)
projUsed-cf {Γ = Γ ▸ A} Fin.zero    = tt
projUsed-cf {Γ = Γ ▸ A} (Fin.suc i) = projUsed-cf {Γ = Γ} i

eraseCtx-cf : ∀ {mₜ} {n} {Γ : Ctx mₜ n} (m : _) (Ψ : Usage n) → Linked σ [] (eraseCtx {Γ = Γ} m Ψ)
eraseCtx-cf {Γ = ∅}         m []         = tt
eraseCtx-cf {Γ = Γ ▸ A} m (Zero ∷ Ψ) = eraseCtx-cf {Γ = Γ} m Ψ , tt
eraseCtx-cf {Γ = Γ ▸ A} m (One  ∷ Ψ) = (eraseCtx-cf {Γ = Γ} m Ψ , tt) , tt
eraseCtx-cf {Γ = Γ ▸ A} m (Many ∷ Ψ) = (eraseCtx-cf {Γ = Γ} m Ψ , tt) , tt

bindEnv-cf : ∀ {mₜ} {n} {Γ : Ctx mₜ n} {Ψ′ : Usage n} {A : Ty mₜ} (m : _) (q : _) → Linked σ [] (bindEnv {Γ = Γ} {Ψ' = Ψ′} {A = A} m q)
bindEnv-cf m Zero = tt
bindEnv-cf m One  = tt
bindEnv-cf m Many = tt

coeIR-cf : ∀ {m} {A B : Ty m} (p : A <: B) → Linked σ [] (coeIR p)
coeIR-cf sub-void   = tt
coeIR-cf sub-unit   = tt
coeIR-cf sub-int    = tt
coeIR-cf sub-float  = tt
coeIR-cf (sub-arr {q = Zero} a b _) = coeIR-cf b , tt
coeIR-cf (sub-arr {q = One}  a b _) = coeIR-cf b , (tt , (tt , (coeIR-cf a , tt)))
coeIR-cf (sub-arr {q = Many} a b _) = coeIR-cf b , (tt , (tt , (coeIR-cf a , tt)))
coeIR-cf (sub-* a b) = (coeIR-cf a , tt) , (coeIR-cf b , tt)
coeIR-cf (sub-+ a b)  = (tt , coeIR-cf a) , (tt , coeIR-cf b)
coeIR-cf sub-μ = tt
coeIR-cf (sub-ν _) = tt
coeIR-cf sub-var = tt

runCoe-linked : ∀ {m} {tbl : List IRFun} {A B : Ty m} {Z} (p : A <: B) (f : IR Z ⌊ A ⌋) → Linked σ tbl f → Linked σ tbl (runCoe p f)
runCoe-linked {σ = σ} {tbl = tbl} {Z = Z} p f l = go (voidFree? p)
  where
    go : (d : Dec (VoidFree p)) → Linked σ tbl (runCoe-dec p d f)
    go (yes vf) = Linked-subst (λ _ → Z) (λ o → o) (erase-eq p vf) f l
    go (no _)   = linked-[] (coeIR p) (coeIR-cf p) , l

-- Plan 0.105 (D257 amendment 2): a DECLARED FFI reference elaborates to a SigOp
-- whose contract is declared. The elaborator reads the declared type exactly
-- as the contract form does (`contractOf`): a value at an erased arrow or a
-- constant, `arrow-info` otherwise — and at an effectful arrow the same
-- `isVoid?`/`isUnit?` split as `contract-eff`.
private
  eff-decl : ∀ {Dom Cod} (si : SigOpInfo Dom Cod) {T} (dv : Dec (Cod ≡ Void)) (du : Dec (Cod ≡ SpecTy.Unit))
           → (showCanonical (SigOpInfo.name si) , T) ∈ σ
           → contractOf (showCanonical (SigOpInfo.name si)) T ≡ contract-eff (showCanonical (SigOpInfo.name si)) Dom Cod dv du
           → Declared-at σ si (arrow-sem-eff dv du)
  eff-decl si (yes refl) du        d ce = tt
  eff-decl si (no _)     (yes refl) d ce = tt
  eff-decl si (no _)     (no _)     d ce = answer-∈ d ce

-- A transport of the codomain links as the morphism does.
Linked-substᶜ : ∀ {tbl} {X Y Y′} (e : Y ≡ Y′) {f : IR X Y} → Linked σ tbl f → Linked σ tbl (subst (IR X) e f)
Linked-substᶜ refl l = l

sigOpIR-linked : ∀ {tbl} {X} {A : Type} (name : CanonicalName) (conc : IsConcrete A)
               → (showCanonical name , A) ∈ σ → Linked σ tbl (sigOpIR {X = X} A name conc)
sigOpIR-linked name (con-fun {k = mk-kind Zero Ty.pure} bDom cCod) d = value-∈ d refl , tt
-- plan 0.113 A3: an effectful erased arrow is a call with a `Unit` slot.
sigOpIR-linked name (con-fun {B = Cod} {k = mk-kind Zero Ty.eff} bDom cCod) d =
  eff-decl (arrow-info (mk-kind Zero Ty.eff) name b-Unit cCod) (isVoid? Cod) (isUnit? Cod) d refl , tt
sigOpIR-linked name (con-fun {k = mk-kind One  Ty.pure} bDom cCod) d = value-∈ d refl , tt
sigOpIR-linked name (con-fun {k = mk-kind Many Ty.pure} bDom cCod) d = value-∈ d refl , tt
sigOpIR-linked name (con-fun {A = Dom} {B = Cod} {k = mk-kind One Ty.eff} bDom cCod) d =
  eff-decl (arrow-info (mk-kind One Ty.eff) name bDom cCod) (isVoid? Cod) (isUnit? Cod) d refl , tt
sigOpIR-linked name (con-fun {A = Dom} {B = Cod} {k = mk-kind Many Ty.eff} bDom cCod) d =
  eff-decl (arrow-info (mk-kind Many Ty.eff) name bDom cCod) (isVoid? Cod) (isUnit? Cod) d refl , tt
sigOpIR-linked name (con-fun {B = Cod} {k = mk-kind Zero Ty.act} bDom cCod) d =
  eff-decl (arrow-info (mk-kind Zero Ty.act) name b-Unit cCod) (isVoid? Cod) (isUnit? Cod) d refl , tt
sigOpIR-linked name (con-fun {A = Dom} {B = Cod} {k = mk-kind One Ty.act} bDom cCod) d =
  eff-decl (arrow-info (mk-kind One Ty.act) name bDom cCod) (isVoid? Cod) (isUnit? Cod) d refl , tt
sigOpIR-linked name (con-fun {A = Dom} {B = Cod} {k = mk-kind Many Ty.act} bDom cCod) d =
  eff-decl (arrow-info (mk-kind Many Ty.act) name bDom cCod) (isVoid? Cod) (isUnit? Cod) d refl , tt
sigOpIR-linked name (con-base b-Unit) d = value-∈ d refl , tt
sigOpIR-linked name (con-base b-Void) d = value-∈ d refl , tt
sigOpIR-linked name (con-base b-Int) d = value-∈ d refl , tt
sigOpIR-linked name (con-base b-Float) d = value-∈ d refl , tt
sigOpIR-linked name (con-base (b-* a b)) d = value-∈ d refl , tt
sigOpIR-linked name (con-base (b-+ a b)) d = value-∈ d refl , tt

sigOp-linked : ∀ {mₜ} {tbl} {n} {Γ : Ctx mₜ n} {A : Type} (m : _) (name : CanonicalName) (conc : IsConcrete A)
             → (showCanonical name , A) ∈ σ → Linked σ tbl (elaborate {Γ = Γ} m (sigOp name conc))
sigOp-linked {A = A} m name conc d = Linked-substᶜ (sym (⌊wk₀⌋ A)) (sigOpIR-linked name conc d)

------------------------------------------------------------------------
-- (D) THE LEMMA
------------------------------------------------------------------------

module _ {σ : ISig} (tbl : List IRFun) where
  private
    L : ∀ {m} → String → Ty m → Set
    L = RefLinked σ tbl
    cf : ∀ {A B} (ir : IR A B) → Linked σ [] ir → Linked σ tbl ir
    cf = linked-[]

    rE : ∀ {mₜ} {n} {Γ : Ctx mₜ n} {Ψ Ψ′ : Usage n} (m : _) (ule : Ψ′ ⊑ᵘ Ψ) → Linked σ tbl (restrictEnv {Γ = Γ} m ule)
    rE {Γ = Γ} m ule = cf (restrictEnv {Γ = Γ} m ule) (restrictEnv-cf {Γ = Γ} m ule)

    bE : ∀ {mₜ} {n} {Γ : Ctx mₜ n} {Ψ′ : Usage n} {A : Ty mₜ} (m : _) (q : _) → Linked σ tbl (bindEnv {Γ = Γ} {Ψ' = Ψ′} {A = A} m q)
    bE {Γ = Γ} {Ψ′ = Ψ′} {A = A} m q = cf (bindEnv {Γ = Γ} {Ψ' = Ψ′} {A = A} m q) (bindEnv-cf {Γ = Γ} {Ψ′ = Ψ′} {A = A} m q)

  elaborate-linked′ : ∀ {mₜ} (m : _) {n} {Γ : Ctx mₜ n} {Ψ : Usage n} {A : Ty mₜ} (e : Expr Γ Ψ A) → Refs (DeclIn σ) L L e
                    → Linked σ tbl (elaborate m e)

  -- the binary operators' shared shape
  bin : ∀ {mₜ} (m : _) {n} {Γ : Ctx mₜ n} (Ψ₁ Ψ₂ : Usage n) {X Y} (a : Expr Γ Ψ₁ X) (b : Expr Γ Ψ₂ Y) → Refs (DeclIn σ) L L a → Refs (DeclIn σ) L L b
      → Linked σ tbl (IR.⟨ elaborate m a IR.∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m b IR.∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩)
  bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb =
    (elaborate-linked′ m a ra , cf (envˡ {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _))
    , (elaborate-linked′ m b rb , cf (envʳ {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _))

  elaborate-linked′ m {Γ = Γ} (var i) r = cf (projUsed {Γ = Γ} i) (projUsed-cf {Γ = Γ} i)
  elaborate-linked′ m (lam {q' = Zero} Zero _ e) r = elaborate-linked′ m e r , tt
  elaborate-linked′ m (lam {q' = Zero} One  _ e) r = elaborate-linked′ m e r , tt
  elaborate-linked′ m (lam {q' = Zero} Many _ e) r = elaborate-linked′ m e r , tt
  elaborate-linked′ m (lam {q' = One}  One  _ e) r = elaborate-linked′ m e r
  elaborate-linked′ m (lam {q' = One}  Many _ e) r = elaborate-linked′ m e r
  elaborate-linked′ m (lam {q' = Many} Many _ e) r = elaborate-linked′ m e r
  elaborate-linked′ m {Γ = Γ} (comp' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) (rf , rg) =
    _ , ((elaborate-linked′ m f rf , cf (envˡ {Γ = Γ} m Ψ₁ (Many *ᵘ Ψ₂)) (restrictEnv-cf {Γ = Γ} m _))
        , (elaborate-linked′ m g rg , cf (envʳω {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _)))
  elaborate-linked′ m {Γ = Γ} (copair' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) (rf , rg) =
    _ , ((elaborate-linked′ m f rf , cf (envˡ {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _))
        , (elaborate-linked′ m g rg , cf (envʳ {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _)))
  elaborate-linked′ m {Γ = Γ} (fork' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) (rf , rg) =
    _ , ((elaborate-linked′ m f rf , cf (envˡ {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _))
        , (elaborate-linked′ m g rg , cf (envʳ {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _)))
  elaborate-linked′ m (curry' f) r = _ , elaborate-linked′ m f r
  elaborate-linked′ m {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {B = B} {q = Zero} f x) (rf , rx) =
    Linked-subst (λ Φ → ⌊ ⟦ Γ ↾ Φ ⟧ᶜ ⌋) (λ _ → ⌊ B ⌋) (sym (Once.Surface.Properties.erase-arg-usage Ψ₁ Ψ₂))
                 (IR.apply IR.∘ IR.⟨ elaborate m f , IR.terminal ⟩) (tt , (elaborate-linked′ m f rf , tt))
  elaborate-linked′ m {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} f x) (rf , rx) =
    tt , ((elaborate-linked′ m f rf , rE {Γ = Γ} m (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)))
         , (elaborate-linked′ m x rx , rE {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂)))))
  elaborate-linked′ m {Γ = Γ} (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} f x) (rf , rx) =
    tt , ((elaborate-linked′ m f rf , rE {Γ = Γ} m (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)))
         , (elaborate-linked′ m x rx , rE {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂)))))
  elaborate-linked′ m {Γ = Γ} (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f x) (rf , rx) =
    (tt , ((elaborate-linked′ m f rf , cf (envˡ {Γ = Γ} m Ψ₁ (Many *ᵘ Ψ₂)) (restrictEnv-cf {Γ = Γ} m _))
          , (elaborate-linked′ m x rx , cf (envʳω {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _)))) , tt
  elaborate-linked′ m {Γ = Γ} (pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) =
    (elaborate-linked′ m a ra , cf (envˡ {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _))
    , (elaborate-linked′ m b rb , cf (envʳ {Γ = Γ} m Ψ₁ Ψ₂) (restrictEnv-cf {Γ = Γ} m _))
  elaborate-linked′ m (coerce p f) r = runCoe-linked p (elaborate m f) (elaborate-linked′ m f r)
  elaborate-linked′ m (fst' p) r = tt , elaborate-linked′ m p r
  elaborate-linked′ m (snd' p) r = tt , elaborate-linked′ m p r
  elaborate-linked′ m (inl' a) r = tt , elaborate-linked′ m a r
  elaborate-linked′ m (inr' b) r = tt , elaborate-linked′ m b r
  elaborate-linked′ m {Γ = Γ} (case' {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} s l r′) (rs , rl , rr) =
    (( (elaborate-linked′ m l rl , (bE {Γ = Γ} {A = A} m qℓ , ((rE {Γ = Γ} m (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) , tt) , tt)))
     , (elaborate-linked′ m r′ rr , (bE {Γ = Γ} {A = B} m qr , ((rE {Γ = Γ} m (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) , tt) , tt))))
     , (_ , ( rE {Γ = Γ} m (⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)) , (elaborate-linked′ m s rs , rE {Γ = Γ} m (⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ))))))
  elaborate-linked′ m unit r = tt
  elaborate-linked′ m (absurd v) r = tt , elaborate-linked′ m v r
  elaborate-linked′ m {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {B = B} e1 e2) (r1 , r2) =
    Linked-subst (λ Φ → ⌊ ⟦ Γ ↾ Φ ⟧ᶜ ⌋) (λ _ → ⌊ B ⌋) (sym (Once.Surface.Properties.erase-arg-usage Ψ₂ Ψ₁))
                 (elaborate m e2) (elaborate-linked′ m e2 r2)
  elaborate-linked′ m {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {A = A} e1 e2) (r1 , r2) =
    elaborate-linked′ m e2 r2 , (bE {Γ = Γ} {Ψ′ = Ψ₂} {A = A} m One
      , (rE {Γ = Γ} m (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) , (elaborate-linked′ m e1 r1 , rE {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))))))
  elaborate-linked′ m {Γ = Γ} (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} e1 e2) (r1 , r2) =
    elaborate-linked′ m e2 r2 , (bE {Γ = Γ} {Ψ′ = Ψ₂} {A = A} m Many
      , (rE {Γ = Γ} m (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) , (elaborate-linked′ m e1 r1 , rE {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))))))
  elaborate-linked′ m (int n) r   = tt , tt
  elaborate-linked′ m (float d) r = tt , tt
  elaborate-linked′ m {Γ = Γ} (add {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (sub {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (mul {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (fadd {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (fsub {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (fmul {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (fdiv {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m (i2f e) r = tt , elaborate-linked′ m e r
  elaborate-linked′ m {Γ = Γ} (div {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (mod' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m (neg e) r = tt , elaborate-linked′ m e r
  elaborate-linked′ m {Γ = Γ} (lt {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (le {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (gt {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (ge {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (eq {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (ne {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) (ra , rb) = tt , bin m {Γ = Γ} Ψ₁ Ψ₂ a b ra rb
  elaborate-linked′ m {Γ = Γ} (sigOp name conc) r = sigOp-linked {Γ = Γ} m name conc r
  elaborate-linked′ m (closure name) r = r , tt
  elaborate-linked′ m (poly name _) r = r , tt
  elaborate-linked′ m (closed e) r = elaborate-linked′ m e r , tt
  elaborate-linked′ m (lift-morphism morph) r = cf morph (linked-σ morph r) , tt
  elaborate-linked′ m {Γ = Γ} (morph-app {Ψ = Ψ} morph x) (rm , rx) =
    cf morph (linked-σ morph rm) , (elaborate-linked′ m x rx , rE {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))))
  elaborate-linked′ m {Γ = Γ} (cata {Ψ = Ψ} {F = F} {A = A} wfF alg) r =
    Linked-subst (λ o → (⌊ ⟦ F ⟧F A ⌋ Once.IRTy.⇛ ⌊ A ⌋) Once.IRTy.* o) (λ _ → ⌊ A ⌋)
                 (Once.IRTy.⌊⟧T-commute F A) (IR.apply IR.∘ IR.⟨ IR.fst , IR.snd ⟩) (tt , (tt , tt))
    , (elaborate-linked′ m alg r , rE {Γ = Γ} m (⊑ᵘ-*Many Ψ))   -- plan 0.113 B1
  -- D273: `anaM ∘ ecoalg`, `cata`'s shape.
  elaborate-linked′ m {Γ = Γ} (ana {Ψ = Ψ} {F = F} {A = A} wfF coalg) r =
    Linked-subst (λ _ → (⌊ A ⌋ Once.IRTy.⇛ ⌊ ⟦ F ⟧F A ⌋) Once.IRTy.* ⌊ A ⌋) (λ o → o)
                 (Once.IRTy.⌊⟧T-commute F A) (IR.apply IR.∘ IR.⟨ IR.fst , IR.snd ⟩) (tt , (tt , tt))
    , (elaborate-linked′ m coalg r , rE {Γ = Γ} m (⊑ᵘ-*Many Ψ))
  -- the loop: `loopM ∘ eround`, `ana`'s shape (no functor to commute).
  elaborate-linked′ m {Γ = Γ} (loop {Ψ = Ψ} round) r =
    (tt , (tt , tt)) , (elaborate-linked′ m round r , rE {Γ = Γ} m (⊑ᵘ-*Many Ψ))

  elaborate-linked : ∀ {mₜ} (m : _) {n} {Γ : Ctx mₜ n} {Ψ : Usage n} {A : Ty mₜ} (e : Expr Γ Ψ A) → Refs (DeclIn σ) L L e
                   → Linked σ tbl (elaborateFull m e)
  elaborate-linked m {Γ = Γ} {Ψ = Ψ} e r = elaborate-linked′ m e r , cf (eraseCtx {Γ = Γ} m Ψ) (eraseCtx-cf {Γ = Γ} m Ψ)
