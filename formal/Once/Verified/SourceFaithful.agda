-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Verified.SourceFaithful — `faithful` (Plan 0.46 / OCP-0006, M3).
--
-- The elaborator is meaning-preserving: the denotation of the ELABORATED IR
-- agrees, pointwise in the observation depth, with THE source semantics `⟦_⟧ˢ`:
--
--     evalᴰ (elaborate Heap e) dγ k  ≡  ⟦ e ⟧ˢ dγ k
--
-- Both sides live in the SAME trace monad `T`, so this is a plain equality (no
-- `∃s`, no fuel, no `SS.eval`) — the OCP-0006 payoff. It is the elaborator-
-- load-bearing obligation under the apex (`SourceTrace.elaborate-faithful` is its
-- closed-`Unit` projection via `cong proj₁`).
--
-- TOP-DOWN: structural induction on `e`; each constructor is a hole the apex
-- demanded. Leaf cases (`unit`, the `semM`-routed arith/comparison, the
-- `evalᴰ`-routed `lift-morphism`) are near-definitional because `⟦_⟧ˢ` denotes
-- them through the SAME `semM`/`evalᴰ` the elaborated IR uses. Undischarged
-- constructors route to `faithful-todo` (an explicit obligation, NOT an island).
------------------------------------------------------------------------

module Once.Verified.SourceFaithful where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Data.List.Properties using (++-identityʳ)

open import Once.Type using (Type; Unit; _+_)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; lookup; _,_^_)
open import Once.Surface.Elaborate using (elaborate; ⟦_⟧ᶜ; proj)
open import Once.Verified.TraceMonad using (T; returnT)
open import Once.Verified.DenotTrace using (⟦_⟧ᴰ; evalᴰ; inject)
open import Once.CCC.Eval as Val using ()
import Once.Verified.SourceDenote as SD
import Once.Compile as C
open import Once.Postulates using (extensionality)

open Once.Surface.Syntax.Expr

------------------------------------------------------------------------
-- The elaborator-faithfulness lemma (general — over any context/env, so the
-- induction can recurse into open subterms). Pointwise in the depth `k`.
------------------------------------------------------------------------

postulate
  -- TOP-DOWN HOLE (M3): the not-yet-discharged constructors. Each is an obligation
  -- the apex demands; discharge in place (leaf cases definitional via the shared
  -- semM/evalᴰ, composition cases via the IH + the monad-combinator reduction).
  faithful-todo :
    ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
      (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
    → evalᴰ (elaborate C.Heap e) dγ k ≡ SD.⟦ e ⟧ˢ dγ k

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
faithful unit    dγ k = refl
faithful (int n) dγ k = refl   -- intLit's semM reduces to `absℤ n`, matching ⟦int n⟧ˢ
-- str: `str-lit-semM s tt` does NOT reduce to `s` definitionally → needs the
-- literal-semantics lemma (`str-lit-semM s tt ≡ s`); deferred to faithful-todo.
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
faithful e       dγ k = faithful-todo e dγ k
