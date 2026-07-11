-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.SourceFaithful — `faithful` (Plan 0.46 / OCP-0006, M3).
--
-- The elaborator is meaning-preserving: the denotation of the ELABORATED IR
-- agrees, pointwise in the observation depth, with THE source semantics `⟦_⟧ˢ`:
--
--     evalᴰ (elaborate Heap e) dγ k  ≡  ⟦ e ⟧ˢ dγ k
--
-- Both sides live in the SAME trace monad `T`, so this is a plain equality (no
-- `∃s`, no fuel, no `SS.eval`) — the OCP-0006 payoff. It is THE standalone
-- elaborator-load-bearing fact (D060): the surface and IR presentations of the
-- one denotational meaning agree. No longer a conjunct of the compiler theorem;
-- the closed-`Unit` projection (`cong proj₁`) is what the apex relies on.
--
-- TOP-DOWN: structural induction on `e`; each constructor is a hole the apex
-- demanded. Leaf cases (`unit`, the `semM`-routed arith/comparison, the
-- `evalᴰ`-routed `lift-morphism`) are near-definitional because `⟦_⟧ˢ` denotes
-- them through the SAME `semM`/`evalᴰ` the elaborated IR uses. `faithful` is
-- now TOTAL and postulate-free: every constructor (including `cata`/`ana` via
-- `FaithfulLemmas.cata-body`/`ana-body`) is discharged.
------------------------------------------------------------------------

module Once.Adequacy.SourceFaithful where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Once.Denotation.Trace using (SigOpEvent)

open import Once.Type using (Type; Unit; Void; Int; Str; Float; Buffer; _*_; _+_; _⇒[_]_; μ-type; ν-type)
open import Once.Functor.Translate using (con-base; con-fun)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; lookup; _,_^_; ⟦_⟧ᶜ)
open import Once.Surface.Elaborate using (elaborate; proj)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.IR using (_∘_; ⟨_,_⟩; apply)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; inject)
open import Once.CCC.Eval as Val using ()
import Once.Denotation.SourceDenote as SD
import Once.Compile as C
import Once.Adequacy.FaithfulLemmas as FL
open import Once.Postulates using (extensionality)

open Once.Surface.Syntax.Expr

------------------------------------------------------------------------
-- The elaborator-faithfulness lemma (general — over any context/env, so the
-- induction can recurse into open subterms). Pointwise in the depth `k`.
------------------------------------------------------------------------

-- `inject` is the identity on the comparison codomain `Unit + Unit` (it recurses
-- on the sum, `inject {Unit}` = id) — but NOT definitionally, so the comparison
-- cases need this one-liner. (`Int`-codomain arith has `inject {Int}` = id
-- definitionally, hence `refl` there.) Keeps `⟦_⟧ˢ` clean (no `inject` pollution).
inj-uu : (y : Val.⟦ Unit + Unit ⟧) → inject {Unit + Unit} y ≡ y
inj-uu (inj₁ _) = refl
inj-uu (inj₂ _) = refl

-- `var i` ↦ `proj i` (`proj zero = snd`, `proj (suc i) = proj i ∘ fst`), which
-- mirrors `lookupᴰ`; `∘`/`fst` reduce (returnT, []++X) so `proj (suc i)` peels to
-- the sub-env. Pure structural induction on the de-Bruijn index.
proj-lookup : ∀ {n} {Γ : Ctx n} (i : Fin n) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
            → evalᴰ (proj {Γ = Γ} i) dγ k ≡ returnT (SD.lookupᴰ Γ i dγ) k
proj-lookup {Γ = Γ , A ^ q} zero    dγ k = refl
proj-lookup {Γ = Γ , A ^ q} (suc i) dγ k = proj-lookup {Γ = Γ} i (proj₁ dγ) k

-- app/effApp trace shape: the `⟨ef,ex⟩` pair leaves `B ++ []`, and `apply`
-- re-associates `((A ++ (B ++ [])) ++ C)` vs ⟦_⟧ˢ's `A ++ (B ++ C)`.
app-trace : ∀ (A B C : List SigOpEvent) → (A ++ (B ++ [])) ++ C ≡ A ++ (B ++ C)
app-trace A B C rewrite ++-identityʳ B = ++-assoc A B C

-- The application body, shared by `app` and `effApp` (whose suspended closure has
-- the same body). Generic over the arrow kind; takes the sub-IHs as arguments so
-- the `rewrite` happens OUTSIDE any `extensionality` lambda. After rewriting both
-- IHs the closures/args align (apply runs the SAME `vf vx`, value refl) and the
-- trace re-associates (app-trace).
-- case' trace shape: `⟨id, es⟩` + `distribute` leave two empty traces before the
-- chosen branch: `((W ++ []) ++ []) ++ Z ≡ W ++ Z`.
case-trace : ∀ (W Z : List SigOpEvent) → ((W ++ []) ++ []) ++ Z ≡ W ++ Z
case-trace W Z = cong (_++ Z) (trans (++-identityʳ (W ++ [])) (++-identityʳ W))

app-body : ∀ {m} {Γ : Ctx m} {Ψ₁ Ψ₂ : Usage m} {A B} {kk}
             (f : Expr Γ Ψ₁ (A ⇒[ kk ] B)) (x : Expr Γ Ψ₂ A)
             (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (n : ℕ)
           → evalᴰ (elaborate C.Heap f) dγ n ≡ SD.⟦ f ⟧ˢ dγ n
           → evalᴰ (elaborate C.Heap x) dγ n ≡ SD.⟦ x ⟧ˢ dγ n
           → evalᴰ (apply ∘ ⟨ elaborate C.Heap f , elaborate C.Heap x ⟩ C.Heap) dγ n
             ≡ (SD.⟦ f ⟧ˢ dγ >>=T (λ vf → SD.⟦ x ⟧ˢ dγ >>=T (λ vx → vf vx))) n
app-body f x dγ n ihf ihx rewrite ihf | ihx =
  cong₂ _,_ (app-trace (proj₁ (SD.⟦ f ⟧ˢ dγ n)) (proj₁ (SD.⟦ x ⟧ˢ dγ n))
                       (proj₁ (proj₂ (SD.⟦ f ⟧ˢ dγ n) (proj₂ (SD.⟦ x ⟧ˢ dγ n)) n))) refl

faithful :
  ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
    (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → evalᴰ (elaborate C.Heap e) dγ k ≡ SD.⟦ e ⟧ˢ dγ k
-- `unit` ↦ `terminal`; both sides reduce to `returnT tt` ⇒ refl.
faithful (var {Γ = Γ} i) dγ k = proj-lookup {Γ = Γ} i dγ k
-- lam ↦ curry: both sides are `returnT <closure>`; the closures are equal by
-- extensionality over the argument (and over the depth, via the body IH).
faithful (lam q _ e) dγ k =
  cong (_,_ []) (extensionality (λ a → extensionality (λ k′ → faithful e (dγ , a) k′)))
-- app: `apply ∘ ⟨ef,ex⟩`. Rewrite both IHs; the closures/args align so `apply`
-- runs the SAME `vf vx` ⇒ value refl; trace re-associates (app-trace).
faithful (app f x) dγ n = app-body f x dγ n (faithful f dγ n) (faithful x dγ n)
-- effApp: a SUSPENDED closure whose body is the (effectful) application of f to x.
-- Both sides are `returnT <closure>` (the Unit-thunk); the closure body is exactly
-- app-body, lifted through extensionality (over the discarded Unit arg + depth).
faithful (effApp f x) dγ k =
  cong (_,_ []) (extensionality (λ _ →
    extensionality (λ n → app-body f x dγ n (faithful f dγ n) (faithful x dγ n))))
-- absurd v : v has type Void, so `proj₂ (⟦v⟧ˢ dγ n) : ⊥` — vacuous.
faithful (absurd v) dγ n = ⊥-elim (proj₂ (SD.⟦ v ⟧ˢ dγ n))
faithful unit    dγ k = refl
faithful (int n) dγ k = refl   -- intLit's semM reduces to `absℤ n`, matching ⟦int n⟧ˢ
faithful (str s) dγ k = refl   -- ⟦str s⟧ˢ now denotes via str-lit-info's semM = strLit's evalᴰ
-- Single-subterm projections/injections: `elaborate (op e) = <prim> ∘ elaborate e`
-- and `⟦ op e ⟧ˢ = ⟦e⟧ˢ >>=T (λv → returnT (<prim> v))`; `_>>=T_` sees the same
-- depth on both sides, so the trace+value at `n` is a function of the SUBTERM's
-- (trace,value) at `n` — one `cong` over the IH (`faithful e`).
faithful (fst' e) dγ n = cong (λ r → (proj₁ r ++ [] , proj₁ (proj₂ r))) (faithful e dγ n)
faithful (snd' e) dγ n = cong (λ r → (proj₁ r ++ [] , proj₂ (proj₂ r))) (faithful e dγ n)
faithful (inl' e) dγ n = cong (λ r → (proj₁ r ++ [] , inj₁ (proj₂ r))) (faithful e dγ n)
faithful (inr' e) dγ n = cong (λ r → (proj₁ r ++ [] , inj₂ (proj₂ r))) (faithful e dγ n)
-- Two-subterm arith (elaborate = `<op>IR ∘ ⟨ea,eb⟩`, ⟦_⟧ˢ via the same `semM`):
-- rewrite both IHs; the only residual is the IR `SigOp`-bind's extra empty trace
-- (`(W ++ []) ≡ W`, ++-identityʳ); the value is identical (same `semM`).
faithful (add a b)  dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) refl
faithful (sub a b)  dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) refl
faithful (mul a b)  dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) refl
faithful (div a b)  dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) refl
faithful (mod' a b) dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) refl
faithful (lt a b)   dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (le a b)   dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (gt a b)   dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (ge a b)   dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (eq a b)   dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (ne a b)   dγ n rewrite faithful a dγ n | faithful b dγ n = cong₂ _,_ (++-identityʳ _) (inj-uu _)
-- neg: single subterm; IR `negIR ∘ ee` and ⟦_⟧ˢ share the bind+cont, so refl post-IH.
faithful (neg e)    dγ n rewrite faithful e dγ n = refl
-- pair: `elaborate = ⟨ea,eb⟩`, same bind structure as ⟦_⟧ˢ (ends in returnT(va,vb),
-- no trailing SigOp bind) ⇒ refl post both IHs.
faithful (pair a b) dγ n rewrite faithful a dγ n | faithful b dγ n = refl
-- arr': `elaborate = arr ∘ ef` adds one `returnT` bind (an extra ++[]); the kind
-- change is erased by ⟦_⟧ᴰ, value unchanged ⇒ ++-identityʳ.
faithful (arr' f)   dγ n rewrite faithful f dγ n = cong₂ _,_ (++-identityʳ _) refl
-- IR embedding: ⟦_⟧ˢ denotes these AS `evalᴰ morph`; elaborate's
-- `curry (morph ∘ snd)` / `morph ∘ ex` reduce to the same (returnT/[]++X + eta).
faithful (lift-morphism morph) dγ k = refl
faithful (morph-app morph e)   dγ n rewrite faithful e dγ n = refl
-- let': `elaborate = ee2 ∘ ⟨id, ee1⟩`. Rewrite the e1 IH, then the e2 IH at the
-- extended env (dγ , v1); residual is the ⟨id,…⟩/pair empty traces:
-- `(W ++ []) ++ Z ≡ W ++ Z`. Value identical.
faithful (let' e1 e2) dγ n
  rewrite faithful e1 dγ n | faithful e2 (dγ , proj₂ (SD.⟦ e1 ⟧ˢ dγ n)) n =
  cong₂ _,_
    (cong (_++ proj₁ (SD.⟦ e2 ⟧ˢ (dγ , proj₂ (SD.⟦ e1 ⟧ˢ dγ n)) n))
          (++-identityʳ (proj₁ (SD.⟦ e1 ⟧ˢ dγ n))))
    refl
-- Effect primitives: ⟦_⟧ˢ denotes them through generic-info/emit-D/semM exactly
-- as elaborate's `SigOp(generic-info name)∘terminal` (non-arrow) / `curry(SigOp∘
-- snd)` (arrow) reduce ([]++X, returnT, eta) ⇒ refl.
faithful (sigOp {A = (Dom ⇒[ kk ] Cod)} name (con-fun bDom cCod)) dγ k = refl
faithful (closure name conc) dγ k = refl
faithful (poly name PT conc) dγ k = refl
-- NON-ARROW `sigOp`: `elaborate`/`⟦_⟧ˢ` dispatch on `A`'s shape (it stays stuck for
-- ABSTRACT `A`), so case-split the non-arrow type constructors — each is the pure
-- `SigOp(generic-info name)∘terminal` shape ⇒ refl. No SigOp purity semantics added;
-- effect lives in the (absent here) arrow kind, so non-arrow is pure by absence.
faithful (sigOp {A = Unit}     name conc) dγ k = refl
faithful (sigOp {A = Void}     name conc) dγ k = refl
faithful (sigOp {A = Int}      name conc) dγ k = refl
faithful (sigOp {A = Str}      name conc) dγ k = refl
faithful (sigOp {A = Float}    name conc) dγ k = refl
faithful (sigOp {A = Buffer}   name conc) dγ k = refl
faithful (sigOp {A = _ * _}    name conc) dγ k = refl
faithful (sigOp {A = _ + _}    name conc) dγ k = refl
faithful (sigOp {A = μ-type _} name conc) dγ k = refl
faithful (sigOp {A = ν-type _} name conc) dγ k = refl
faithful (case' s l r) dγ n rewrite faithful s dγ n with proj₂ (SD.⟦ s ⟧ˢ dγ n)
... | inj₁ a rewrite faithful l (dγ , a) n =
        cong₂ _,_ (case-trace (proj₁ (SD.⟦ s ⟧ˢ dγ n)) (proj₁ (SD.⟦ l ⟧ˢ (dγ , a) n))) refl
... | inj₂ b rewrite faithful r (dγ , b) n =
        cong₂ _,_ (case-trace (proj₁ (SD.⟦ s ⟧ˢ dγ n)) (proj₁ (SD.⟦ r ⟧ˢ (dγ , b) n))) refl
-- cata: both sides fold with per-layer-threaded algebras; reduces to the
-- closure-bridge (`cata-body`) — the algebra IH + a monad reduction, no
-- purity assumption (the build trace is threaded, not discarded).
faithful {Γ = Γ} (cata wf alg) dγ k = FL.cata-body {Γ = Γ} wf alg (λ j → faithful alg tt j) dγ k
-- ana: dual of cata; reduces to the same closure-bridge via `ana-body`
-- (+ the `ana-ev-bridge` trace lemma). Postulate-free.
faithful {Γ = Γ} (ana wf coalg) dγ k = FL.ana-body {Γ = Γ} wf coalg (λ j → faithful coalg tt j) dγ k
