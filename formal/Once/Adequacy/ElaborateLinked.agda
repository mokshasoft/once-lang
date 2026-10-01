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

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (String)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Once.Type using (Type; Zero; One; Many; mk-kind; _⇒[_]_)
open import Once.Type.Sub
open import Once.CanonicalName using (CanonicalName; bare; _≟ᶜ_)
open import Once.IR using (IR)
import Once.IR as IR
open import Once.IRTy using (IRTy; ⌊_⌋; _≟IRTy_)
open import Once.IR.Ref using (refIR)
open import Once.Functor.Translate using (IsConcrete; con-base; con-fun; base-Unit; base-Void; base-Int; base-Float;
  base-Str; base-Buffer; base-Prod; base-Sum; base-rigid)
open import Once.Surface.Syntax hiding (_,_; _,_^_)
open import Once.Surface.Context using (_,_^_; ⊑[]; _⊑∷_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
open import Once.Surface.CoerceIR using (runCoe; runCoe-dec; voidFree?; VoidFree; coeIR; erase-eq)
open import Once.Surface.Elaborate
import Once.Surface.Properties
import Once.IRTy
open import Once.Type using (⟦_⟧T)
open import Once.Denotation.Program using (IRFun; fname; fdom; fcod; LinkedAt; LinkedAt-at; Linked)

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
            → ∀ {A B} (ir : IR A B) → Linked tbl ir → Linked tbl′ ir
linked-mono h (g IR.∘ f)       (lg , lf) = linked-mono h g lg , linked-mono h f lf
linked-mono h IR.⟨ f , g ⟩     (lf , lg) = linked-mono h f lf , linked-mono h g lg
linked-mono h (IR.case f g)    (lf , lg) = linked-mono h f lf , linked-mono h g lg
linked-mono h (IR.curry f)     lf = linked-mono h f lf
linked-mono h (IR.Cata _ alg)  la = linked-mono h alg la
linked-mono h (IR.Ana _ coalg) lc = linked-mono h coalg lc
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
linked-mono h (IR.SigOp _)     _ = tt
linked-mono h (IR.const _ _)   _ = tt

linkedAt-++ : ∀ (later tbl : List IRFun) {f A B} → LinkedAt tbl f A B → LinkedAt (later ++ tbl) f A B
linkedAt-++ []          tbl lk = lk
linkedAt-++ (e ∷ later) tbl lk = linkedAt-cons e (later ++ tbl) (linkedAt-++ later tbl lk)

-- A call-free IR (linked in the empty table) is linked in every table.
linkedAt-[] : ∀ {tbl : List IRFun} {f A B} → LinkedAt [] f A B → LinkedAt tbl f A B
linkedAt-[] ()

------------------------------------------------------------------------
-- (B) The references of a surface term.
------------------------------------------------------------------------

-- `Refs Pc Pp e`: every `closure x : A` in `e` satisfies `Pc x A`, every
-- `poly x A` satisfies `Pp x A`, and every embedded IR morphism is call-free.
Refs : (Pc Pp : String → Type → Set) → ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} → Expr Γ Ψ A → Set
Refs Pc Pp (var _)             = ⊤
Refs Pc Pp (lam _ _ b)         = Refs Pc Pp b
Refs Pc Pp (app f x)           = Refs Pc Pp f × Refs Pc Pp x
Refs Pc Pp (effApp f x)        = Refs Pc Pp f × Refs Pc Pp x
Refs Pc Pp (pair a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fst' p)            = Refs Pc Pp p
Refs Pc Pp (snd' p)            = Refs Pc Pp p
Refs Pc Pp (inl' a)            = Refs Pc Pp a
Refs Pc Pp (inr' a)            = Refs Pc Pp a
Refs Pc Pp (case' s l r)       = Refs Pc Pp s × Refs Pc Pp l × Refs Pc Pp r
Refs Pc Pp unit                = ⊤
Refs Pc Pp (absurd e)          = Refs Pc Pp e
Refs Pc Pp (let' e₁ e₂)        = Refs Pc Pp e₁ × Refs Pc Pp e₂
Refs Pc Pp (int _)             = ⊤
Refs Pc Pp (str _)             = ⊤
Refs Pc Pp (float _)           = ⊤
Refs Pc Pp (add a b)           = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (sub a b)           = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (mul a b)           = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fadd a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fsub a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fmul a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (fdiv a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (i2f a)             = Refs Pc Pp a
Refs Pc Pp (div a b)           = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (mod' a b)          = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (neg a)             = Refs Pc Pp a
Refs Pc Pp (lt a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (le a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (gt a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (ge a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (eq a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (ne a b)            = Refs Pc Pp a × Refs Pc Pp b
Refs Pc Pp (coerce _ e)        = Refs Pc Pp e
Refs Pc Pp (sigOp _ _)         = ⊤
Refs Pc Pp {A = A} (closure x) = Pc x A
Refs Pc Pp (poly x T)          = Pp x T
Refs Pc Pp (closed e)          = Refs Pc Pp e
Refs Pc Pp (lift-morphism m)   = Linked [] m
Refs Pc Pp (morph-app m a)     = Linked [] m × Refs Pc Pp a
Refs Pc Pp (comp' f g)         = Refs Pc Pp f × Refs Pc Pp g
Refs Pc Pp (copair' f g)       = Refs Pc Pp f × Refs Pc Pp g
Refs Pc Pp (fork' f g)         = Refs Pc Pp f × Refs Pc Pp g
Refs Pc Pp (curry' f)          = Refs Pc Pp f
Refs Pc Pp (cata _ alg)        = Refs Pc Pp alg
Refs Pc Pp (ana _ coalg)       = Refs Pc Pp coalg

-- A reference elaborates to a call (`refIR`); it is linked when the call is.
RefLinked : List IRFun → String → Type → Set
RefLinked tbl x A = Linked tbl (refIR A (bare x))

Refs-map : ∀ {Pc Pp Pc′ Pp′ : String → Type → Set}
         → (∀ {x A} → Pc x A → Pc′ x A) → (∀ {x A} → Pp x A → Pp′ x A)
         → ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A) → Refs Pc Pp e → Refs Pc′ Pp′ e
Refs-map hc hp (var _)             r = tt
Refs-map hc hp (lam _ _ b)         r = Refs-map hc hp b r
Refs-map hc hp (app f x)           (a , b) = Refs-map hc hp f a , Refs-map hc hp x b
Refs-map hc hp (effApp f x)        (a , b) = Refs-map hc hp f a , Refs-map hc hp x b
Refs-map hc hp (pair x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fst' p)            r = Refs-map hc hp p r
Refs-map hc hp (snd' p)            r = Refs-map hc hp p r
Refs-map hc hp (inl' x)            r = Refs-map hc hp x r
Refs-map hc hp (inr' x)            r = Refs-map hc hp x r
Refs-map hc hp (case' s l r′)      (a , b , c) = Refs-map hc hp s a , Refs-map hc hp l b , Refs-map hc hp r′ c
Refs-map hc hp unit                r = tt
Refs-map hc hp (absurd e)          r = Refs-map hc hp e r
Refs-map hc hp (let' e₁ e₂)        (a , b) = Refs-map hc hp e₁ a , Refs-map hc hp e₂ b
Refs-map hc hp (int _)             r = tt
Refs-map hc hp (str _)             r = tt
Refs-map hc hp (float _)           r = tt
Refs-map hc hp (add x y)           (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (sub x y)           (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (mul x y)           (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fadd x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fsub x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fmul x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (fdiv x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (i2f x)             r = Refs-map hc hp x r
Refs-map hc hp (div x y)           (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (mod' x y)          (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (neg x)             r = Refs-map hc hp x r
Refs-map hc hp (lt x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (le x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (gt x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (ge x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (eq x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (ne x y)            (a , b) = Refs-map hc hp x a , Refs-map hc hp y b
Refs-map hc hp (coerce _ e)        r = Refs-map hc hp e r
Refs-map hc hp (sigOp _ _)         r = tt
Refs-map hc hp (closure x)         r = hc r
Refs-map hc hp (poly x T)          r = hp r
Refs-map hc hp (closed e)          r = Refs-map hc hp e r
Refs-map hc hp (lift-morphism m)   r = r
Refs-map hc hp (morph-app m x)     (a , b) = a , Refs-map hc hp x b
Refs-map hc hp (comp' f g)         (a , b) = Refs-map hc hp f a , Refs-map hc hp g b
Refs-map hc hp (copair' f g)       (a , b) = Refs-map hc hp f a , Refs-map hc hp g b
Refs-map hc hp (fork' f g)         (a , b) = Refs-map hc hp f a , Refs-map hc hp g b
Refs-map hc hp (curry' f)          r = Refs-map hc hp f r
Refs-map hc hp (cata _ alg)        r = Refs-map hc hp alg r
Refs-map hc hp (ana _ coalg)       r = Refs-map hc hp coalg r


------------------------------------------------------------------------
-- (C) The lowering's own pieces are call-free.
------------------------------------------------------------------------

-- A transport of an IR's objects moves its linkedness with it.
Linked-subst : ∀ {tbl : List IRFun} {I : Set} (F G : I → IRTy) {i j} (eq : i ≡ j) (ir : IR (F i) (G i))
             → Linked tbl ir → Linked tbl (subst (λ o → IR (F o) (G o)) eq ir)
Linked-subst F G refl ir l = l

linked-[] : ∀ {tbl : List IRFun} {A B} (ir : IR A B) → Linked [] ir → Linked tbl ir
linked-[] {tbl} = linked-mono (λ {f} {A} {B} → linkedAt-[] {tbl} {f} {A} {B})

restrictEnv-cf : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} (m : _) (ule : Ψ′ ⊑ᵘ Ψ) → Linked [] (restrictEnv {Γ = Γ} m ule)
restrictEnv-cf {Γ = ∅}         m ⊑[]          = tt
restrictEnv-cf {Γ = Γ , A ^ q} m (z≤z ⊑∷ ule) = restrictEnv-cf {Γ = Γ} m ule
restrictEnv-cf {Γ = Γ , A ^ q} m (z≤o ⊑∷ ule) = restrictEnv-cf {Γ = Γ} m ule , tt
restrictEnv-cf {Γ = Γ , A ^ q} m (z≤m ⊑∷ ule) = restrictEnv-cf {Γ = Γ} m ule , tt
restrictEnv-cf {Γ = Γ , A ^ q} m (o≤o ⊑∷ ule) = (restrictEnv-cf {Γ = Γ} m ule , tt) , tt
restrictEnv-cf {Γ = Γ , A ^ q} m (o≤m ⊑∷ ule) = (restrictEnv-cf {Γ = Γ} m ule , tt) , tt
restrictEnv-cf {Γ = Γ , A ^ q} m (m≤m ⊑∷ ule) = (restrictEnv-cf {Γ = Γ} m ule , tt) , tt

projUsed-cf : ∀ {n} {Γ : Ctx n} (i : Fin n) → Linked [] (projUsed {Γ = Γ} i)
projUsed-cf {Γ = Γ , A ^ q} Fin.zero    = tt
projUsed-cf {Γ = Γ , A ^ q} (Fin.suc i) = projUsed-cf {Γ = Γ} i

eraseCtx-cf : ∀ {n} {Γ : Ctx n} (m : _) (Ψ : Usage n) → Linked [] (eraseCtx {Γ = Γ} m Ψ)
eraseCtx-cf {Γ = ∅}         m []         = tt
eraseCtx-cf {Γ = Γ , A ^ q} m (Zero ∷ Ψ) = eraseCtx-cf {Γ = Γ} m Ψ , tt
eraseCtx-cf {Γ = Γ , A ^ q} m (One  ∷ Ψ) = (eraseCtx-cf {Γ = Γ} m Ψ , tt) , tt
eraseCtx-cf {Γ = Γ , A ^ q} m (Many ∷ Ψ) = (eraseCtx-cf {Γ = Γ} m Ψ , tt) , tt

bindEnv-cf : ∀ {n} {Γ : Ctx n} {Ψ′ : Usage n} {A} (m : _) (q : _) → Linked [] (bindEnv {Γ = Γ} {Ψ' = Ψ′} {A = A} m q)
bindEnv-cf m Zero = tt
bindEnv-cf m One  = tt
bindEnv-cf m Many = tt

coeIR-cf : ∀ {A B} (p : A <: B) → Linked [] (coeIR p)
coeIR-cf sub-void   = tt
coeIR-cf sub-unit   = tt
coeIR-cf sub-int    = tt
coeIR-cf sub-float  = tt
coeIR-cf sub-str    = tt
coeIR-cf sub-buffer = tt
coeIR-cf (sub-arr {q = Zero} a b _) = coeIR-cf b , tt
coeIR-cf (sub-arr {q = One}  a b _) = coeIR-cf b , (tt , (tt , (coeIR-cf a , tt)))
coeIR-cf (sub-arr {q = Many} a b _) = coeIR-cf b , (tt , (tt , (coeIR-cf a , tt)))
coeIR-cf (sub-prod a b) = (coeIR-cf a , tt) , (coeIR-cf b , tt)
coeIR-cf (sub-sum a b)  = (tt , coeIR-cf a) , (tt , coeIR-cf b)
coeIR-cf sub-μ = tt
coeIR-cf (sub-ν _) = tt
coeIR-cf sub-rigid = tt

runCoe-linked : ∀ {tbl : List IRFun} {Z A B} (p : A <: B) (f : IR Z ⌊ A ⌋) → Linked tbl f → Linked tbl (runCoe p f)
runCoe-linked {tbl} {Z} p f l = go (voidFree? p)
  where
    go : (d : Dec (VoidFree p)) → Linked tbl (runCoe-dec p d f)
    go (yes vf) = Linked-subst (λ _ → Z) (λ o → o) (erase-eq p vf) f l
    go (no _)   = linked-[] (coeIR p) (coeIR-cf p) , l

sigOp-cf : ∀ {n} {Γ : Ctx n} {A} (m : _) (name : CanonicalName) (conc : IsConcrete A)
         → Linked [] (elaborate {Γ = Γ} m (sigOp name conc))
sigOp-cf m name (con-fun {k = mk-kind Zero π} bDom cCod) = tt , tt
sigOp-cf m name (con-fun {k = mk-kind One  π} bDom cCod) = tt , tt
sigOp-cf m name (con-fun {k = mk-kind Many π} bDom cCod) = tt , tt
sigOp-cf m name (con-base base-Unit)       = tt , tt
sigOp-cf m name (con-base base-Void)       = tt , tt
sigOp-cf m name (con-base base-Int)        = tt , tt
sigOp-cf m name (con-base base-Float)      = tt , tt
sigOp-cf m name (con-base base-Str)        = tt , tt
sigOp-cf m name (con-base base-Buffer)     = tt , tt
sigOp-cf m name (con-base (base-Prod a b)) = tt , tt
sigOp-cf m name (con-base (base-Sum a b))  = tt , tt
sigOp-cf m name (con-base base-rigid)      = tt , tt

------------------------------------------------------------------------
-- (D) THE LEMMA
------------------------------------------------------------------------

module _ (tbl : List IRFun) where
  private
    L = RefLinked tbl
    cf : ∀ {A B} (ir : IR A B) → Linked [] ir → Linked tbl ir
    cf = linked-[]

    rE : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} (m : _) (ule : Ψ′ ⊑ᵘ Ψ) → Linked tbl (restrictEnv {Γ = Γ} m ule)
    rE {Γ = Γ} m ule = cf (restrictEnv {Γ = Γ} m ule) (restrictEnv-cf {Γ = Γ} m ule)

    bE : ∀ {n} {Γ : Ctx n} {Ψ′ : Usage n} {A} (m : _) (q : _) → Linked tbl (bindEnv {Γ = Γ} {Ψ' = Ψ′} {A = A} m q)
    bE {Γ = Γ} {Ψ′} {A} m q = cf (bindEnv {Γ = Γ} {Ψ' = Ψ′} {A = A} m q) (bindEnv-cf {Γ = Γ} {Ψ′ = Ψ′} {A = A} m q)

  elaborate-linked′ : ∀ (m : _) {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A) → Refs L L e
                    → Linked tbl (elaborate m e)

  -- the binary operators' shared shape
  bin : ∀ (m : _) {n} {Γ : Ctx n} (Ψ₁ Ψ₂ : Usage n) {X Y} (a : Expr Γ Ψ₁ X) (b : Expr Γ Ψ₂ Y) → Refs L L a → Refs L L b
      → Linked tbl (IR.⟨ elaborate m a IR.∘ envˡ {Γ = Γ} m Ψ₁ Ψ₂ , elaborate m b IR.∘ envʳ {Γ = Γ} m Ψ₁ Ψ₂ ⟩)
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
  elaborate-linked′ m (str s) r   = tt , tt
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
  elaborate-linked′ m {Γ = Γ} (sigOp name conc) r = cf (elaborate {Γ = Γ} m (sigOp name conc)) (sigOp-cf {Γ = Γ} m name conc)
  elaborate-linked′ m (closure name) r = r , tt
  elaborate-linked′ m (poly name _) r = r , tt
  elaborate-linked′ m (closed e) r = elaborate-linked′ m e r , tt
  elaborate-linked′ m (lift-morphism morph) r = cf morph r , tt
  elaborate-linked′ m {Γ = Γ} (morph-app {Ψ = Ψ} morph x) (rm , rx) =
    cf morph rm , (elaborate-linked′ m x rx , rE {Γ = Γ} m (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))))
  elaborate-linked′ m (cata {F = F} {A = A} wfF alg) r =
    Linked-subst (λ o → (⌊ ⟦ F ⟧T A ⌋ Once.IRTy.⇛ ⌊ A ⌋) Once.IRTy.* o) (λ _ → ⌊ A ⌋)
                 (Once.IRTy.⌊⟧T-commute F A) (IR.apply IR.∘ IR.⟨ IR.fst , IR.snd ⟩) (tt , (tt , tt))
    , (elaborate-linked′ m alg r , tt)
  elaborate-linked′ m (ana {F = F} {A = A} wfF coalg) r =
    Linked-subst (λ _ → ⌊ A ⌋) (λ o → o) (Once.IRTy.⌊⟧T-commute F A)
                 (IR.apply IR.∘ IR.⟨ elaborate m coalg IR.∘ IR.terminal , IR.id ⟩) (tt , ((elaborate-linked′ m coalg r , tt) , tt))
    , tt

  elaborate-linked : ∀ (m : _) {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A) → Refs L L e
                   → Linked tbl (elaborateFull m e)
  elaborate-linked m {Γ = Γ} {Ψ = Ψ} e r = elaborate-linked′ m e r , cf (eraseCtx {Γ = Γ} m Ψ) (eraseCtx-cf {Γ = Γ} m Ψ)
