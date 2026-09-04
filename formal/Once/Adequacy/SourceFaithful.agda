-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
-- now TOTAL: every constructor (including `cata`/`ana` via
-- `FaithfulLemmas.cata-body`/`ana-body`) is discharged.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.SourceFaithful (fmt : TargetNum) where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-subst-sym; subst-sym-subst)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Once.Denotation.Trace using (SigOpEvent)

open import Once.Type using (Type; Unit; Void; Int; Str; Float; Buffer; _*_; _+_; _⇒[_]_; μ-type; ν-type; mk-kind; pure; eff; Zero; One; Many)
open import Once.Functor.Translate using (con-base; con-fun; base-Unit)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; lookup; _,_^_; ⟦_⟧ᶜ; _↾_; zeroUsage; singleUse; ∅;
                                       _⊑ᵘ_; ⊑[]; _⊑∷_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m;
                                       ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; _+ᵘ_; _*ᵘ_)
open import Once.Surface.Context using () renaming (_,_ to _,ᶜ_)
open import Once.Surface.Elaborate using (elaborate; elaborateFull; proj; projUsed; distribute; compIR; copairIR; forkIR; curryIR; distribIR;
                                          envˡ; envʳ; restrictEnv; bindEnv)
open import Once.Denotation.Phase using (lookupᴰUsed; restrictᴰ; bindᴰ; bindᴰ0)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.IR using (_∘_; ⟨_,_⟩; apply; fst; snd; curry; SigOp; terminal; case) renaming (id to idIR)
open import Once.Arith.SigOp.Builders using (arrow-info; value-info; internal-info;
                                             add-info; sub-info; mul-info; div-info; mod-info; fadd-info; fsub-info; fmul-info; fdiv-info; lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.Adequacy.CataErased fmt using (liftFn-SigOp)
open import Once.Adequacy.LiftFnReduce fmt using (liftFn-id; liftFn-fst; liftFn-snd; liftFn-∘; liftFn-pair)
open import Once.SigOp.Info using (SigOpInfo; semM)
open import Once.Denotation.DenotTrace using (emit-D)
open import Once.CanonicalName using (bare)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; inject; forget; liftFn; cohᴰ)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)
open import Once.IRTy using (IRTy; ⌊_⌋) renaming (_*_ to _*ᴵ_; _+_ to _+ᴵ_)
open import Function using (id)
open import Once.CCC.Eval as Val using ()
import Once.Denotation.SourceDenote as SD
import Once.Compile as C
import Once.Adequacy.FaithfulLemmas fmt as FL
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
-- transport push-helpers (all `refl`)
proj₁-subst : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (dγ : A' × B')
            → proj₁ (subst id (sym (cong₂ _×_ p q)) dγ) ≡ subst id (sym p) (proj₁ dγ)
proj₁-subst refl refl dγ = refl

proj₂-subst : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (dγ : A' × B')
            → proj₂ (subst id (sym (cong₂ _×_ p q)) dγ) ≡ subst id (sym q) (proj₂ dγ)
proj₂-subst refl refl dγ = refl

subst-T-returnT : ∀ {X Y : Set} (eq : X ≡ Y) (g : X)
  → subst T eq (returnT g) ≡ returnT (subst id eq g)
subst-T-returnT refl g = refl

subst-T-apply : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) (n : ℕ)
  → subst T eq h n ≡ (proj₁ (h n) , subst id eq (proj₂ (h n)))
subst-T-apply refl h n = refl

pair-subst⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A') (b : B')
  → subst id (sym (cong₂ _×_ p q)) (a , b) ≡ (subst id (sym p) a , subst id (sym q) b)
pair-subst⁻ refl refl a b = refl

push⊎₁⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A')
  → subst id (sym (cong₂ _⊎_ p q)) (inj₁ a) ≡ inj₁ (subst id (sym p) a)
push⊎₁⁻ refl refl a = refl

push⊎₂⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (b : B')
  → subst id (sym (cong₂ _⊎_ p q)) (inj₂ b) ≡ inj₂ (subst id (sym q) b)
push⊎₂⁻ refl refl b = refl

subst-arrowᴰ : ∀ {DI DT EI ET : Set} (pD : DI ≡ DT) (pE : EI ≡ ET) (g : DI → T EI)
  → subst id (cong₂ (λ x y → x → T y) pD pE) g
    ≡ (λ x → subst T pE (g (subst id (sym pD) x)))
subst-arrowᴰ refl refl g = refl

-- MISSING COMBINATOR (not a proof fight): `distribute` is a PURE re-shaping
-- (`case`/`curry`/`apply`/`swap'`, no SigOps), but its `apply∘curry∘case` body
-- doesn't β-reduce on its own. Prove once that its denotation is the obvious
-- `returnT (reshaped v)` (empty trace) — then `case'` closes cleanly.
distribute-reduce : ∀ {Γ A B : IRTy} (dγ : ⟦ Γ ⟧ᴰᴵ) (v : ⟦ A ⟧ᴰᴵ ⊎ ⟦ B ⟧ᴰᴵ)
  → evalᴰ fmt (distribute {Γ} {A} {B} C.Heap) (dγ , v)
    ≡ returnT ([ (λ a → inj₁ (dγ , a)) , (λ b → inj₂ (dγ , b)) ]′ v)
distribute-reduce dγ (inj₁ a) = refl
distribute-reduce dγ (inj₂ b) = refl

-- single-subterm projection/injection transports (all `refl`)
fst-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (h : T (AT × BT)) (n : ℕ)
  → subst T pA ((subst T (sym (cong₂ _×_ pA pB)) h) >>=T (λ v → returnT (proj₁ v))) n
    ≡ (h >>=T (λ v → returnT (proj₁ v))) n
fst-transport refl refl h n = refl

snd-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (h : T (AT × BT)) (n : ℕ)
  → subst T pB ((subst T (sym (cong₂ _×_ pA pB)) h) >>=T (λ v → returnT (proj₂ v))) n
    ≡ (h >>=T (λ v → returnT (proj₂ v))) n
snd-transport refl refl h n = refl

inl-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (h : T AT) (n : ℕ)
  → subst T (cong₂ _⊎_ pA pB) ((subst T (sym pA) h) >>=T (λ v → returnT (inj₁ v))) n
    ≡ (h >>=T (λ v → returnT (inj₁ v))) n
inl-transport refl refl h n = refl

inr-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (h : T BT) (n : ℕ)
  → subst T (cong₂ _⊎_ pA pB) ((subst T (sym pB) h) >>=T (λ v → returnT (inj₂ v))) n
    ≡ (h >>=T (λ v → returnT (inj₂ v))) n
inr-transport refl refl h n = refl

pair-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (ha : T AT) (hb : T BT) (n : ℕ)
  → subst T (cong₂ _×_ pA pB) ((subst T (sym pA) ha) >>=T (λ va → (subst T (sym pB) hb) >>=T (λ vb → returnT (va , vb)))) n
    ≡ (ha >>=T (λ va → hb >>=T (λ vb → returnT (va , vb)))) n
pair-transport refl refl ha hb n = refl

morphapp-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT)
    (g : AI → T BI) (h : T AT) (n : ℕ)
  → subst T pB ((subst T (sym pA) h) >>=T (λ v → g v)) n
    ≡ (h >>=T (λ v → subst T pB (g (subst id (sym pA) v)))) n
morphapp-transport refl refl g h n = refl

-- `evalᴰ` of the subterm, `liftFn`→`evalᴰ` converted (for the projection cases)
ihᴰ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A) (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
    → (∀ j → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (elaborate C.Heap e) dγ j ≡ SD.⟦ e ⟧ˢ fmt dγ j)
    → evalᴰ fmt (elaborate C.Heap e) (subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ) ≡ subst T (sym (cohᴰ A)) (SD.⟦ e ⟧ˢ fmt dγ)
ihᴰ {A = A} e dγ ih = trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (extensionality ih))

-- non-arrow (value-position) `SigOp info ∘ terminal`: `terminal` discards the env,
-- so `liftFn` = the emit/semM pair transported by `cohᴰ A` (subst-subst-sym).
-- `terminal` discards the environment, so this is generic in the SOURCE OBJECT
-- — no context, and in particular no usage, appears.
sigop-value : ∀ {X : Type} {A : Type} (info : SigOpInfo Unit A) (dγ : ⟦ X ⟧ᴰ) (k : ℕ)
  → liftFn fmt {X} {A} (SigOp info ∘ terminal) dγ k ≡ (emit-D info tt , inject (semM info fmt tt))
sigop-value {A = A} info dγ k =
  trans (subst-T-apply (cohᴰ A) (evalᴰ fmt (SigOp info) tt) k)
        (cong₂ _,_ refl (subst-subst-sym (cohᴰ A)))

-- D143: a variable's RUNTIME environment is a SINGLETON — `var i` has usage
-- `singleUse i One`, so `↾` has already dropped every other slot. `projUsed`
-- and `lookupᴰUsed` then walk the index in lockstep without touching the data,
-- and the `suc` case passes `dγ` straight through (the skipped slot is `Zero`,
-- so `↾` never put it there).
proj-lookup : ∀ {n} {Γ : Ctx n} (i : Fin n) (dγ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜ ⟧ᴰ) (k : ℕ)
            → liftFn fmt {⟦ Γ ↾ singleUse i One ⟧ᶜ} {lookup Γ i} (projUsed {Γ = Γ} i) dγ k
              ≡ returnT (lookupᴰUsed Γ i dγ) k
proj-lookup {Γ = Γ , A ^ q} zero    dγ k =
  cong (λ t → t k)
    (trans (cong (λ w → subst T (cohᴰ A) (returnT w))
                 (proj₂-subst (cohᴰ ⟦ Γ ↾ zeroUsage ⟧ᶜ) (cohᴰ A) dγ))
      (trans (subst-T-returnT (cohᴰ A) (subst id (sym (cohᴰ A)) (proj₂ dγ)))
             (cong returnT (subst-subst-sym (cohᴰ A)))))
proj-lookup {Γ = Γ , A ^ q} (suc i) dγ k = proj-lookup {Γ = Γ} i dγ k

------------------------------------------------------------------------
-- D143: the IR environment plumbing DENOTES the semantic one.
--
-- `elaborate` narrows environments with `restrictEnv`/`bindEnv` (IR morphisms);
-- `⟦_⟧ˢ` narrows them with `restrictᴰ`/`bindᴰ` (functions on the value domain).
-- Every compound clause of `faithful` needs the two to agree. They do, and the
-- proofs are direct inductions: both families are defined by the SAME case
-- analysis — on the `⊑ᵘ` witness, and on the bound quantity.
------------------------------------------------------------------------

mutual
  -- head variable live in Ψ but DEAD in Ψ' — `restrictEnv … ∘ fst` drops it.
  restrictEnv-drop :
    ∀ {n} {Γ : Ctx n} {A : Type} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
      (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ × ⟦ A ⟧ᴰ) (k : ℕ)
    → liftFn fmt (restrictEnv {Γ = Γ} C.Heap ule ∘ fst) dγ k
      ≡ returnT (restrictᴰ {Γ = Γ} ule (proj₁ dγ)) k
  restrictEnv-drop {Γ = Γ} {A = A} ule dγ k =
    trans (cong (λ t → t dγ k) (liftFn-∘ (restrictEnv {Γ = Γ} C.Heap ule) fst))
      (trans (cong (λ t → (t dγ >>=T liftFn fmt (restrictEnv {Γ = Γ} C.Heap ule)) k) liftFn-fst)
             (liftFn-restrictEnv {Γ = Γ} ule (proj₁ dγ) k))

  -- head variable live in BOTH — keep it, narrow the rest.
  restrictEnv-keep :
    ∀ {n} {Γ : Ctx n} {A : Type} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
      (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ × ⟦ A ⟧ᴰ) (k : ℕ)
    → liftFn fmt (⟨ restrictEnv {Γ = Γ} C.Heap ule ∘ fst , snd ⟩ C.Heap) dγ k
      ≡ returnT (restrictᴰ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ) k
  restrictEnv-keep {Γ = Γ} {A = A} ule dγ k =
    trans (cong (λ t → t dγ k) (liftFn-pair (restrictEnv {Γ = Γ} C.Heap ule ∘ fst) snd))
      (trans (cong (λ t → (t >>=T (λ b → liftFn fmt snd dγ >>=T λ c → returnT (b , c))) k)
                   (extensionality (restrictEnv-drop {Γ = Γ} {A = A} ule dγ)))
             (cong (λ t → (returnT (restrictᴰ {Γ = Γ} ule (proj₁ dγ))
                            >>=T (λ b → t >>=T λ c → returnT (b , c))) k)
                   (cong (λ u → u dγ) liftFn-snd)))

  liftFn-restrictEnv : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (le : Ψ' ⊑ᵘ Ψ)
                       (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) (k : ℕ)
    → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ} (restrictEnv {Γ = Γ} C.Heap le) dγ k
      ≡ returnT (restrictᴰ {Γ = Γ} le dγ) k
  liftFn-restrictEnv {Γ = ∅} ⊑[] dγ k = cong (λ t → t dγ k) (liftFn-id {⟦ ∅ ⟧ᶜ})
  liftFn-restrictEnv {Γ = Γ , A ^ q} (z≤z ⊑∷ ule) dγ k = liftFn-restrictEnv {Γ = Γ} ule dγ k
  liftFn-restrictEnv {Γ = Γ , A ^ q} (z≤o ⊑∷ ule) dγ k = restrictEnv-drop {Γ = Γ} {A = A} ule dγ k
  liftFn-restrictEnv {Γ = Γ , A ^ q} (z≤m ⊑∷ ule) dγ k = restrictEnv-drop {Γ = Γ} {A = A} ule dγ k
  liftFn-restrictEnv {Γ = Γ , A ^ q} (o≤o ⊑∷ ule) dγ k = restrictEnv-keep {Γ = Γ} {A = A} ule dγ k
  liftFn-restrictEnv {Γ = Γ , A ^ q} (o≤m ⊑∷ ule) dγ k = restrictEnv-keep {Γ = Γ} {A = A} ule dγ k
  liftFn-restrictEnv {Γ = Γ , A ^ q} (m≤m ⊑∷ ule) dγ k = restrictEnv-keep {Γ = Γ} {A = A} ule dγ k


-- THE WORKHORSE: `elaborate e ∘ restrictEnv le` denotes `⟦e⟧ˢ` run on the
-- NARROWED environment. Every compound clause of `faithful` is an instance —
-- the elaborator narrows with an IR morphism, the denotation with `restrictᴰ`,
-- and this is where the two meet.
-- NB `ule`, not `le`: `le` is an `Expr` constructor (the ≤ comparison) brought
-- into scope by `open Expr`, so a pattern variable of that name is read as it.
liftFn-∘-restrictEnv : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} {A} (ule : Ψ' ⊑ᵘ Ψ)
                       (h : C.IR ⌊ ⟦ Γ ↾ Ψ' ⟧ᶜ ⌋ ⌊ A ⌋) (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (h ∘ restrictEnv {Γ = Γ} C.Heap ule) dγ k
    ≡ liftFn fmt {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} h (restrictᴰ {Γ = Γ} ule dγ) k
liftFn-∘-restrictEnv {Γ = Γ} ule h dγ k =
  trans (cong (λ t → t dγ k) (liftFn-∘ h (restrictEnv {Γ = Γ} C.Heap ule)))
        (cong (λ t → (t >>=T liftFn fmt h) k)
              (extensionality (liftFn-restrictEnv {Γ = Γ} ule dγ)))


-- D143: `restrictEnv` is pure PLUMBING — it emits no events. The arithmetic
-- clauses need this explicitly: their operands are now `e ∘ restrictEnv le`,
-- and the composition's trace is `trace(restrictEnv) ++ trace(e)`, which only
-- collapses once the left factor is known to be `[]`.
restrictEnv-trace : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                    (dγ' : ⟦ ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ ⟧ᴰᴵ) (k : ℕ)
  → proj₁ (evalᴰ fmt (restrictEnv {Γ = Γ} C.Heap ule) dγ' k) ≡ []
restrictEnv-trace {Γ = ∅}         ⊑[]            dγ' k = refl
restrictEnv-trace {Γ = Γ , A ^ q} (z≤z ⊑∷ ule) dγ' k = restrictEnv-trace {Γ = Γ} ule dγ' k
restrictEnv-trace {Γ = Γ , A ^ q} (z≤o ⊑∷ ule) dγ' k = restrictEnv-trace {Γ = Γ} ule (proj₁ dγ') k
restrictEnv-trace {Γ = Γ , A ^ q} (z≤m ⊑∷ ule) dγ' k = restrictEnv-trace {Γ = Γ} ule (proj₁ dγ') k
restrictEnv-trace {Γ = Γ , A ^ q} (o≤o ⊑∷ ule) dγ' k =
  trans (++-identityʳ _) (restrictEnv-trace {Γ = Γ} ule (proj₁ dγ') k)
restrictEnv-trace {Γ = Γ , A ^ q} (o≤m ⊑∷ ule) dγ' k =
  trans (++-identityʳ _) (restrictEnv-trace {Γ = Γ} ule (proj₁ dγ') k)
restrictEnv-trace {Γ = Γ , A ^ q} (m≤m ⊑∷ ule) dγ' k =
  trans (++-identityʳ _) (restrictEnv-trace {Γ = Γ} ule (proj₁ dγ') k)

-- `ihᴰ` for an arbitrary IR morphism (not just an elaborated `Expr`).
ihᴰgen : ∀ {X A : Type} (h : C.IR ⌊ X ⌋ ⌊ A ⌋) (sh : T ⟦ A ⟧ᴰ) (dγ : ⟦ X ⟧ᴰ)
       → (∀ j → liftFn fmt {X} {A} h dγ j ≡ sh j)
       → evalᴰ fmt h (subst id (sym (cohᴰ X)) dγ) ≡ subst T (sym (cohᴰ A)) sh
ihᴰgen {A = A} h sh dγ ih =
  trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (extensionality ih))

-- At `Unit + Unit` (the comparison result) `inject` is the identity, but only
-- after casing on the value — it pattern-matches on the injection.
inject-BB : ∀ (v : Val.⟦ Unit + Unit ⟧) → inject {Unit + Unit} v ≡ v
inject-BB (inj₁ _) = refl
inject-BB (inj₂ _) = refl

-- D143: THE ARITHMETIC NODE. `<op>IR = SigOp <op>-info`, so every two-operand
-- arithmetic clause is `SigOp info ∘ ⟨ ea , eb ⟩`. Stating it as a lemma with
-- `ea`/`eb` as PARAMETERS is what makes `rewrite` work again: inside the lemma
-- the operands are opaque variables, so `evalᴰ fmt ea dγ'` is stuck and stays
-- syntactically present, whereas in the clause they are compositions that
-- unfold — leaving nothing for `rewrite` to abstract.
--
-- Three CONCRETE instances rather than one generic lemma: the operand types are
-- base types, where `cohᴰ` is `refl` and every transport vanishes. Generic in
-- `A B C` the transports survive and the proof no longer closes.
--
-- WITH-FOOTGUN: `emit-D si x with effect si`. Abstracting `info` into a
-- parameter FREEZES that `with` — with a concrete `add-info` it reduces to `[]`
-- (arith SigOps are Pure), but on a variable it is stuck. So the equation is
-- passed in as `noEmit` rather than fought. [[feedback_de_with_parameterize_equation]]

arith-body-II : ∀ {X : Type} (info : SigOpInfo (Int * Int) Int)
               (ea : C.IR ⌊ X ⌋ ⌊ Int ⌋) (eb : C.IR ⌊ X ⌋ ⌊ Int ⌋)
               (sa : T ⟦ Int ⟧ᴰ) (sb : T ⟦ Int ⟧ᴰ) (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
             → (noEmit : ∀ v → emit-D info v ≡ [])
             → (∀ j → liftFn fmt {X} {Int} ea dγ j ≡ sa j)
             → (∀ j → liftFn fmt {X} {Int} eb dγ j ≡ sb j)
             → liftFn fmt {X} {Int} (SigOp info ∘ ⟨ ea , eb ⟩ C.Heap) dγ n
               ≡ (sa >>=T (λ va → sb >>=T (λ vb → returnT (semM info fmt (va , vb))))) n
arith-body-II {X = X} info ea eb sa sb dγ n noEmit iha ihb
  rewrite ihᴰgen {X} {Int} ea sa dγ iha | ihᴰgen {X} {Int} eb sb dγ ihb
        | noEmit (proj₂ (sa n) , proj₂ (sb n)) =
  cong₂ _,_ (++-identityʳ _) refl

arith-body-FF : ∀ {X : Type} (info : SigOpInfo (Float * Float) Float)
               (ea : C.IR ⌊ X ⌋ ⌊ Float ⌋) (eb : C.IR ⌊ X ⌋ ⌊ Float ⌋)
               (sa : T ⟦ Float ⟧ᴰ) (sb : T ⟦ Float ⟧ᴰ) (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
             → (noEmit : ∀ v → emit-D info v ≡ [])
             → (∀ j → liftFn fmt {X} {Float} ea dγ j ≡ sa j)
             → (∀ j → liftFn fmt {X} {Float} eb dγ j ≡ sb j)
             → liftFn fmt {X} {Float} (SigOp info ∘ ⟨ ea , eb ⟩ C.Heap) dγ n
               ≡ (sa >>=T (λ va → sb >>=T (λ vb → returnT (semM info fmt (va , vb))))) n
arith-body-FF {X = X} info ea eb sa sb dγ n noEmit iha ihb
  rewrite ihᴰgen {X} {Float} ea sa dγ iha | ihᴰgen {X} {Float} eb sb dγ ihb
        | noEmit (proj₂ (sa n) , proj₂ (sb n)) =
  cong₂ _,_ (++-identityʳ _) refl

arith-body-IB : ∀ {X : Type} (info : SigOpInfo (Int * Int) (Unit + Unit))
               (ea : C.IR ⌊ X ⌋ ⌊ Int ⌋) (eb : C.IR ⌊ X ⌋ ⌊ Int ⌋)
               (sa : T ⟦ Int ⟧ᴰ) (sb : T ⟦ Int ⟧ᴰ) (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
             → (noEmit : ∀ v → emit-D info v ≡ [])
             → (∀ j → liftFn fmt {X} {Int} ea dγ j ≡ sa j)
             → (∀ j → liftFn fmt {X} {Int} eb dγ j ≡ sb j)
             → liftFn fmt {X} {(Unit + Unit)} (SigOp info ∘ ⟨ ea , eb ⟩ C.Heap) dγ n
               ≡ (sa >>=T (λ va → sb >>=T (λ vb → returnT (semM info fmt (va , vb))))) n
arith-body-IB {X = X} info ea eb sa sb dγ n noEmit iha ihb
  rewrite ihᴰgen {X} {Int} ea sa dγ iha | ihᴰgen {X} {Int} eb sb dγ ihb
        | noEmit (proj₂ (sa n) , proj₂ (sb n))
        | inject-BB (semM info fmt (proj₂ (sa n) , proj₂ (sb n))) =
  cong₂ _,_ (++-identityʳ _) refl

-- D143: the narrowed `ihᴰ`. A binary node's operands are elaborated as
-- `elaborate e ∘ restrictEnv le`, so their IH must be taken at the narrowed
-- environment and pushed through the composition — `liftFn-∘-restrictEnv`.
ihᴰ∘ : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} {A} (ule : Ψ' ⊑ᵘ Ψ) (e : Expr Γ Ψ' A)
       (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
     → (∀ j → liftFn fmt {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} (elaborate C.Heap e)
                       (restrictᴰ {Γ = Γ} ule dγ) j
              ≡ SD.⟦ e ⟧ˢ fmt (restrictᴰ {Γ = Γ} ule dγ) j)
     → evalᴰ fmt (elaborate C.Heap e ∘ restrictEnv {Γ = Γ} C.Heap ule)
                 (subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ)
       ≡ subst T (sym (cohᴰ A)) (SD.⟦ e ⟧ˢ fmt (restrictᴰ {Γ = Γ} ule dγ))
ihᴰ∘ {Γ = Γ} {A = A} ule e dγ ih =
  trans (sym (subst-sym-subst (cohᴰ A)))
        (cong (subst T (sym (cohᴰ A)))
              (extensionality (λ j →
                 trans (liftFn-∘-restrictEnv ule (elaborate C.Heap e) dγ j) (ih j))))

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

-- D127 `comp'` per-call trace: inside the returned closure the inner `apply`
-- leaves one trailing `[]` (the `⟨ fst∘fst , … ⟩` pairing's second component is
-- a `returnT`). Explicit arguments for the same reason `app-trace` has them —
-- the unifier will not invert `_++_` through the `returnT`s.
comp-trace : ∀ (W Z : List SigOpEvent) → (W ++ []) ++ Z ≡ W ++ Z
comp-trace W Z = cong (_++ Z) (++-identityʳ W)

-- Double transport-apply-bind: the `cohᴰ`-transported closure computation
-- applied to the `cohᴰ`-back-transported argument computation, transported,
-- equals the untransported apply-bind (all `refl`).
app-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT)
    (hf : T (AT → T BT)) (hx : T AT) (n : ℕ)
  → subst T pB ((subst T (sym (cong₂ (λ x y → x → T y) pA pB)) hf)
                  >>=T (λ vf → (subst T (sym pA) hx) >>=T (λ vx → vf vx))) n
    ≡ (hf >>=T (λ vf → hx >>=T (λ vx → vf vx))) n
app-transport refl refl hf hx n = refl

-- D127: the composition body. `compIR ∘ ⟨ ef , eg ⟩` — the arms run ONCE, at
-- build time (that is the whole point of the closed-morphism form), and
-- building the closure emits nothing, so the outer trace is just the pair's
-- with one trailing `[]`. The per-call trace lives inside the returned
-- function, where the two `apply`s run.
comp-transport : ∀ {AI AT BI BT CI CT : Set}
    (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
    (hf : T (BT → T CT)) (hg : T (AT → T BT)) (n : ℕ)
  → subst T (cong₂ (λ u v → u → T v) pA pC)
      ((subst T (sym (cong₂ (λ u v → u → T v) pB pC)) hf) >>=T (λ vf →
       (subst T (sym (cong₂ (λ u v → u → T v) pA pB)) hg) >>=T (λ vg →
       returnT (λ a → vg a >>=T vf)))) n
    ≡ (hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ a → vg a >>=T vf)))) n
comp-transport refl refl refl hf hg n = refl

-- D143: generic in the ENVIRONMENT OBJECT `X`. These body lemmas never inspect
-- the context — they relate an IR shape to a denotation shape — so tying them
-- to `⟦ Γ ⟧ᶜ` was incidental. Generalising lets each `faithful` clause
-- instantiate `X := ⟦ Γ ↾ Ψ ⟧ᶜ` and pass its sub-terms already narrowed.
comp-body : ∀ {X : Type} {A B C} {π}
              (ef : C.IR ⌊ X ⌋ ⌊ B ⇒[ mk-kind Many π ] C ⌋)
              (eg : C.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many π ] B ⌋)
              (sf : T ⟦ B ⇒[ mk-kind Many π ] C ⟧ᴰ)
              (sg : T ⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ)
              (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
            → (∀ j → liftFn fmt {X} {B ⇒[ mk-kind Many π ] C} ef dγ j ≡ sf j)
            → (∀ j → liftFn fmt {X} {A ⇒[ mk-kind Many π ] B} eg dγ j ≡ sg j)
            → liftFn fmt {X} {A ⇒[ mk-kind Many π ] C}
                     (compIR C.Heap ∘ ⟨ ef , eg ⟩ C.Heap) dγ n
              ≡ (sf >>=T (λ vf → sg >>=T (λ vg →
                 returnT (λ a → vg a >>=T vf)))) n
comp-body {X = X} {A = A} {B = B} {C = C} {π = π} ef eg sf sg dγ n ihf ihg =
  trans (cong (λ t → subst T (cohᴰ (A ⇒[ mk-kind Many π ] C)) t n)
              (trans evalᴰ-comp-reduce
                     (cong₂ (λ hf hg → hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ a → vg a >>=T vf))))
                            ihf-T ihg-T)))
        (comp-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) sf sg n)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))) sf
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C)))) (extensionality ihf))
    ihg-T : evalᴰ fmt eg dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) sg
    ihg-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (extensionality ihg))
    evalᴰ-comp-reduce : evalᴰ fmt (compIR C.Heap ∘ ⟨ ef , eg ⟩ C.Heap) dγ'
                        ≡ (evalᴰ fmt ef dγ' >>=T (λ vf → evalᴰ fmt eg dγ' >>=T (λ vg →
                           returnT (λ a → vg a >>=T vf))))
    evalᴰ-comp-reduce = extensionality (λ m → cong₂ _,_ (++-identityʳ _)
      (extensionality (λ a → extensionality (λ k →
         cong₂ _,_ (comp-trace (proj₁ (proj₂ (evalᴰ fmt eg dγ' m) a k))
                               (proj₁ (proj₂ (evalᴰ fmt ef dγ' m)
                                             (proj₂ (proj₂ (evalᴰ fmt eg dγ' m) a k)) k)))
                   refl))))
curry-transport : ∀ {AI AT BI BT CI CT : Set}
    (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
    (hf : T ((AT × BT) → T CT)) (n : ℕ)
  → subst T (cong₂ (λ u v → u → T v) pA (cong₂ (λ u v → u → T v) pB pC))
      ((subst T (sym (cong₂ (λ u v → u → T v) (cong₂ _×_ pA pB) pC)) hf) >>=T (λ vf →
       returnT (λ a → returnT (λ b → vf (a , b))))) n
    ≡ (hf >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b))))) n
curry-transport refl refl refl hf n = refl

curry-body : ∀ {X : Type} {A B C}
               (ef : C.IR ⌊ X ⌋ ⌊ (A * B) ⇒[ mk-kind Many pure ] C ⌋)
               (sf : T ⟦ (A * B) ⇒[ mk-kind Many pure ] C ⟧ᴰ)
               (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
             → (∀ j → liftFn fmt {X} {(A * B) ⇒[ mk-kind Many pure ] C} ef dγ j ≡ sf j)
             → liftFn fmt {X} {A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C)}
                      (curryIR C.Heap ∘ ef) dγ n
               ≡ (sf >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b))))) n
curry-body {X = X} {A = A} {B = B} {C = C} ef sf dγ n ihf =
  trans (cong (λ t → subst T (cohᴰ (A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C))) t n)
              (trans evalᴰ-curry-reduce
                     (cong (λ hf → hf >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b))))) ihf-T)))
        (curry-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (sf) n)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ (A * B)) (cohᴰ C))) (sf)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ (A * B)) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ (A * B)) (cohᴰ C)))) (extensionality ihf))
    evalᴰ-curry-reduce : evalᴰ fmt (curryIR C.Heap ∘ ef) dγ'
                         ≡ (evalᴰ fmt ef dγ' >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b)))))
    evalᴰ-curry-reduce = refl

fork-transport : ∀ {AI AT BI BT CI CT : Set}
    (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
    (hf : T (AT → T BT)) (hg : T (AT → T CT)) (n : ℕ)
  → subst T (cong₂ (λ u v → u → T v) pA (cong₂ _×_ pB pC))
      ((subst T (sym (cong₂ (λ u v → u → T v) pA pB)) hf) >>=T (λ vf →
       (subst T (sym (cong₂ (λ u v → u → T v) pA pC)) hg) >>=T (λ vg →
       returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c))))))) n
    ≡ (hf >>=T (λ vf → hg >>=T (λ vg →
       returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c))))))) n
fork-transport refl refl refl hf hg n = refl

fork-body : ∀ {X : Type} {A B C}
              (ef : C.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many pure ] B ⌋)
              (eg : C.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many pure ] C ⌋)
              (sf : T ⟦ A ⇒[ mk-kind Many pure ] B ⟧ᴰ)
              (sg : T ⟦ A ⇒[ mk-kind Many pure ] C ⟧ᴰ)
              (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
            → (∀ j → liftFn fmt {X} {A ⇒[ mk-kind Many pure ] B} ef dγ j ≡ sf j)
            → (∀ j → liftFn fmt {X} {A ⇒[ mk-kind Many pure ] C} eg dγ j ≡ sg j)
            → liftFn fmt {X} {A ⇒[ mk-kind Many pure ] (B * C)}
                     (forkIR C.Heap ∘ ⟨ ef , eg ⟩ C.Heap) dγ n
              ≡ (sf >>=T (λ vf → sg >>=T (λ vg →
                 returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c))))))) n
fork-body {X = X} {A = A} {B = B} {C = C} ef eg sf sg dγ n ihf ihg =
  trans (cong (λ t → subst T (cohᴰ (A ⇒[ mk-kind Many pure ] (B * C))) t n)
              (trans evalᴰ-fork-reduce
                     (cong₂ (λ hf hg → hf >>=T (λ vf → hg >>=T (λ vg →
                              returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c)))))))
                            ihf-T ihg-T)))
        (fork-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (sf) (sg) n)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) (sf)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (extensionality ihf))
    ihg-T : evalᴰ fmt eg dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))) (sg)
    ihg-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C)))) (extensionality ihg))
    evalᴰ-fork-reduce : evalᴰ fmt (forkIR C.Heap ∘ ⟨ ef , eg ⟩ C.Heap) dγ'
                        ≡ (evalᴰ fmt ef dγ' >>=T (λ vf → evalᴰ fmt eg dγ' >>=T (λ vg →
                           returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c)))))))
    evalᴰ-fork-reduce = extensionality (λ m → cong₂ _,_ (++-identityʳ _)
      (extensionality (λ a → extensionality (λ k → cong₂ _,_ refl refl))))

copair-transport : ∀ {AI AT BI BT CI CT : Set}
    (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
    (hf : T (AT → T CT)) (hg : T (BT → T CT)) (n : ℕ)
  → subst T (cong₂ (λ u v → u → T v) (cong₂ _⊎_ pA pB) pC)
      ((subst T (sym (cong₂ (λ u v → u → T v) pA pC)) hf) >>=T (λ vf →
       (subst T (sym (cong₂ (λ u v → u → T v) pB pC)) hg) >>=T (λ vg →
       returnT (λ ab → [ vf , vg ]′ ab)))) n
    ≡ (hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ ab → [ vf , vg ]′ ab)))) n
copair-transport refl refl refl hf hg n = refl

copair-body : ∀ {X : Type} {A B C} {π}
                (ef : C.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many π ] C ⌋)
                (eg : C.IR ⌊ X ⌋ ⌊ B ⇒[ mk-kind Many π ] C ⌋)
                (sf : T ⟦ A ⇒[ mk-kind Many π ] C ⟧ᴰ)
                (sg : T ⟦ B ⇒[ mk-kind Many π ] C ⟧ᴰ)
                (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
              → (∀ j → liftFn fmt {X} {A ⇒[ mk-kind Many π ] C} ef dγ j ≡ sf j)
              → (∀ j → liftFn fmt {X} {B ⇒[ mk-kind Many π ] C} eg dγ j ≡ sg j)
              → liftFn fmt {X} {(A + B) ⇒[ mk-kind Many π ] C}
                       (copairIR C.Heap ∘ ⟨ ef , eg ⟩ C.Heap) dγ n
                ≡ (sf >>=T (λ vf → sg >>=T (λ vg →
                   returnT (λ ab → [ vf , vg ]′ ab)))) n
copair-body {X = X} {A = A} {B = B} {C = C} {π = π} ef eg sf sg dγ n ihf ihg =
  trans (cong (λ t → subst T (cohᴰ ((A + B) ⇒[ mk-kind Many π ] C)) t n)
              (trans evalᴰ-copair-reduce
                     (cong₂ (λ hf hg → hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ ab → [ vf , vg ]′ ab))))
                            ihf-T ihg-T)))
        (copair-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (sf) (sg) n)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))) (sf)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C)))) (extensionality ihf))
    ihg-T : evalᴰ fmt eg dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))) (sg)
    ihg-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C)))) (extensionality ihg))
    evalᴰ-copair-reduce : evalᴰ fmt (copairIR C.Heap ∘ ⟨ ef , eg ⟩ C.Heap) dγ'
                          ≡ (evalᴰ fmt ef dγ' >>=T (λ vf → evalᴰ fmt eg dγ' >>=T (λ vg →
                             returnT (λ ab → [ vf , vg ]′ ab))))
    -- The elaborated side goes through `distribIR` and then `case`, which is
    -- STUCK on an abstract sum value — so the per-call step case-splits on the
    -- argument. That is the only structural difference from the other three.
    branch : ∀ (m : ℕ) (ab : ⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ)
           → proj₂ (evalᴰ fmt (copairIR C.Heap ∘ ⟨ ef , eg ⟩ C.Heap) dγ' m) ab
             ≡ proj₂ ((evalᴰ fmt ef dγ' >>=T (λ vf → evalᴰ fmt eg dγ' >>=T (λ vg →
                       returnT (λ x → [ vf , vg ]′ x)))) m) ab
    branch m (inj₁ x) = extensionality (λ k → cong₂ _,_ refl refl)
    branch m (inj₂ y) = extensionality (λ k → cong₂ _,_ refl refl)
    evalᴰ-copair-reduce = extensionality (λ m →
      cong₂ _,_ (++-identityʳ _) (extensionality (branch m)))

-- D143: `apply` needs `⌊A ⇒[k] B⌋ ≡ ⌊A⌋ ⇛ ⌊B⌋`, so the arrow must be NON-erased
-- — the quantity cannot stay a variable. `One` and `Many` share the proof; the
-- `Zero` case elaborates differently (`⟨ ef , terminal ⟩`) and is handled in
-- `faithful` directly. Generic in the environment object `X`.

app-body : ∀ {X : Type} {A B} {π}
             (ef : C.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many π ] B ⌋) (ex : C.IR ⌊ X ⌋ ⌊ A ⌋)
             (sf : T ⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ) (sx : T ⟦ A ⟧ᴰ)
             (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
           → (∀ j → liftFn fmt {X} {A ⇒[ mk-kind Many π ] B} ef dγ j ≡ sf j)
           → (∀ j → liftFn fmt {X} {A} ex dγ j ≡ sx j)
           → liftFn fmt {X} {B} (apply ∘ ⟨ ef , ex ⟩ C.Heap) dγ n
             ≡ (sf >>=T (λ vf → sx >>=T (λ vx → vf vx))) n
app-body {X = X} {A = A} {B = B} ef ex sf sx dγ n ihf ihx =
  trans (cong (λ t → subst T (cohᴰ B) t n)
              (trans evalᴰ-app-reduce
                     (cong₂ (λ hf hx → hf >>=T (λ vf → hx >>=T (λ vx → vf vx))) ihf-T ihx-T)))
        (app-transport (cohᴰ A) (cohᴰ B) sf sx n)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) sf
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (extensionality ihf))
    ihx-T : evalᴰ fmt ex dγ' ≡ subst T (sym (cohᴰ A)) sx
    ihx-T = trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (extensionality ihx))
    evalᴰ-app-reduce : evalᴰ fmt (apply ∘ ⟨ ef , ex ⟩ C.Heap) dγ'
                       ≡ (evalᴰ fmt ef dγ' >>=T (λ vf → evalᴰ fmt ex dγ' >>=T (λ vx → vf vx)))
    evalᴰ-app-reduce = extensionality (λ m →
      cong₂ _,_ (app-trace (proj₁ (evalᴰ fmt ef dγ' m)) (proj₁ (evalᴰ fmt ex dγ' m))
                           (proj₁ ((proj₂ (evalᴰ fmt ef dγ' m)) (proj₂ (evalᴰ fmt ex dγ' m)) m))) refl)

app-body-One : ∀ {X : Type} {A B} {π}
             (ef : C.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind One π ] B ⌋) (ex : C.IR ⌊ X ⌋ ⌊ A ⌋)
             (sf : T ⟦ A ⇒[ mk-kind One π ] B ⟧ᴰ) (sx : T ⟦ A ⟧ᴰ)
             (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
           → (∀ j → liftFn fmt {X} {A ⇒[ mk-kind One π ] B} ef dγ j ≡ sf j)
           → (∀ j → liftFn fmt {X} {A} ex dγ j ≡ sx j)
           → liftFn fmt {X} {B} (apply ∘ ⟨ ef , ex ⟩ C.Heap) dγ n
             ≡ (sf >>=T (λ vf → sx >>=T (λ vx → vf vx))) n
app-body-One {X = X} {A = A} {B = B} ef ex sf sx dγ n ihf ihx =
  trans (cong (λ t → subst T (cohᴰ B) t n)
              (trans evalᴰ-app-reduce
                     (cong₂ (λ hf hx → hf >>=T (λ vf → hx >>=T (λ vx → vf vx))) ihf-T ihx-T)))
        (app-transport (cohᴰ A) (cohᴰ B) sf sx n)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) sf
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (extensionality ihf))
    ihx-T : evalᴰ fmt ex dγ' ≡ subst T (sym (cohᴰ A)) sx
    ihx-T = trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (extensionality ihx))
    evalᴰ-app-reduce : evalᴰ fmt (apply ∘ ⟨ ef , ex ⟩ C.Heap) dγ'
                       ≡ (evalᴰ fmt ef dγ' >>=T (λ vf → evalᴰ fmt ex dγ' >>=T (λ vx → vf vx)))
    evalᴰ-app-reduce = extensionality (λ m →
      cong₂ _,_ (app-trace (proj₁ (evalᴰ fmt ef dγ' m)) (proj₁ (evalᴰ fmt ex dγ' m))
                           (proj₁ ((proj₂ (evalᴰ fmt ef dγ' m)) (proj₂ (evalᴰ fmt ex dγ' m)) m))) refl)


-- D143: the ERASED arrow's `cohᴰ` is a ONE-equation `cong` (both sides forget
-- the argument), so the two-equation `subst-arrowᴰ` does not apply.
subst-arrow₀ᴰ : ∀ {U B B' : Set} (q : B ≡ B') (g : U → T B)
  → subst id (cong (λ y → U → T y) q) g ≡ (λ u → subst T q (g u))
subst-arrow₀ᴰ refl g = refl

-- D143: over the RUNTIME environment `Γ ↾ Ψ`. `elaborate` and `⟦_⟧ˢ` are both
-- phase-indexed, so faithfulness is a statement about the variables the term
-- actually uses — the full environment never appears.
faithful :
  ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
    (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (elaborate C.Heap e) dγ k ≡ SD.⟦ e ⟧ˢ fmt dγ k
-- `unit` ↦ `terminal`; both sides reduce to `returnT tt` ⇒ refl.
faithful (var {Γ = Γ} i) dγ k = proj-lookup {Γ = Γ} i dγ k
faithful (arr' f) dγ k = faithful f dγ k
-- lam ↦ curry. D143: SIX clauses — the arrow's quantity `q` decides whether the
-- meaning takes an argument, the binder's body-usage `q'` whether it enters the
-- body's environment. At `q' = Zero` the elaborated body is `ee ∘ fst` (the
-- bound value is dropped) and the denotation runs on `bindᴰ0 dγ`, so the two
-- agree only after `liftFn-∘`/`liftFn-fst` discard it — that is `drop` below.
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} Zero _ e) dγ k =
  trans (cong (λ t → t k) red)
        (cong (_,_ []) (extensionality (λ u → extensionality (λ k′ →
          trans (drop u k′) (faithful e (bindᴰ0 {Γ = Γ} {A = A} dγ) k′)))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate C.Heap e
    drop : ∀ u j → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * Unit} {B} (ee ∘ fst) (dγ , u) j
                 ≡ liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee dγ j
    drop u j = trans (cong (λ t → t (dγ , u) j) (liftFn-∘ ee fst))
                     (cong (λ t → (t (dγ , u) >>=T liftFn fmt ee) j) liftFn-fst)
    red : liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Zero pure ] B} (curry (ee ∘ fst) C.Heap) dγ
          ≡ returnT (λ u → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * Unit} {B} (ee ∘ fst) (dγ , u))
    red = trans (subst-T-returnT (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ B))
                                 (λ u → evalᴰ fmt (ee ∘ fst) (dγ' , u)))
            (cong returnT
              (trans (subst-arrow₀ᴰ (cohᴰ B) (λ u → evalᴰ fmt (ee ∘ fst) (dγ' , u)))
                     (extensionality (λ u →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt (ee ∘ fst) w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ Unit) dγ u))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} One _ e) dγ k =
  trans (cong (λ t → t k) red)
        (cong (_,_ []) (extensionality (λ a → extensionality (λ k′ →
          trans (drop a k′) (faithful e (bindᴰ0 {Γ = Γ} {A = A} dγ) k′)))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate C.Heap e
    drop : ∀ a j → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} (ee ∘ fst) (dγ , a) j
                 ≡ liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee dγ j
    drop a j = trans (cong (λ t → t (dγ , a) j) (liftFn-∘ ee fst))
                     (cong (λ t → (t (dγ , a) >>=T liftFn fmt ee) j) liftFn-fst)
    red : liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind One pure ] B} (curry (ee ∘ fst) C.Heap) dγ
          ≡ returnT (λ a → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} (ee ∘ fst) (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt (ee ∘ fst) (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt (ee ∘ fst) (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt (ee ∘ fst) w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} Many _ e) dγ k =
  trans (cong (λ t → t k) red)
        (cong (_,_ []) (extensionality (λ a → extensionality (λ k′ →
          trans (drop a k′) (faithful e (bindᴰ0 {Γ = Γ} {A = A} dγ) k′)))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate C.Heap e
    drop : ∀ a j → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} (ee ∘ fst) (dγ , a) j
                 ≡ liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee dγ j
    drop a j = trans (cong (λ t → t (dγ , a) j) (liftFn-∘ ee fst))
                     (cong (λ t → (t (dγ , a) >>=T liftFn fmt ee) j) liftFn-fst)
    red : liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] B} (curry (ee ∘ fst) C.Heap) dγ
          ≡ returnT (λ a → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} (ee ∘ fst) (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt (ee ∘ fst) (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt (ee ∘ fst) (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt (ee ∘ fst) w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = One} {A = A} {B = B} One _ e) dγ k =
  trans (cong (λ t → t k) red)
        (cong (_,_ []) (extensionality (λ a → extensionality (λ k′ →
          faithful e (bindᴰ {Γ = Γ} {A = A} One dγ a) k′))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate C.Heap e
    red : liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind One pure ] B} (curry ee C.Heap) dγ
          ≡ returnT (λ a → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} ee (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt ee (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ee (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ee w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = One} {A = A} {B = B} Many _ e) dγ k =
  trans (cong (λ t → t k) red)
        (cong (_,_ []) (extensionality (λ a → extensionality (λ k′ →
          faithful e (bindᴰ {Γ = Γ} {A = A} One dγ a) k′))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate C.Heap e
    red : liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] B} (curry ee C.Heap) dγ
          ≡ returnT (λ a → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} ee (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt ee (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ee (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ee w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Many} {A = A} {B = B} Many _ e) dγ k =
  trans (cong (λ t → t k) red)
        (cong (_,_ []) (extensionality (λ a → extensionality (λ k′ →
          faithful e (bindᴰ {Γ = Γ} {A = A} Many dγ a) k′))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate C.Heap e
    red : liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] B} (curry ee C.Heap) dγ
          ≡ returnT (λ a → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} ee (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt ee (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ee (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ee w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))

-- app: `apply ∘ ⟨ef,ex⟩`. Rewrite both IHs; the closures/args align so `apply`
-- runs the SAME `vf vx` ⇒ value refl; trace re-associates (app-trace).
-- D143: `app` splits on the arrow's quantity. At `One`/`Many` both operands
-- narrow and `app-body` closes it; the `Zero` case is separate below — the
-- argument is ERASED, so the elaborator emits `⟨ ef , terminal ⟩` and never
-- evaluates `x`.
faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} f x) dγ n =
  app-body-One (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
           (elaborate C.Heap x ∘ restrictEnv {Γ = Γ} C.Heap leX)
           (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
           (SD.⟦ x ⟧ˢ fmt (restrictᴰ {Γ = Γ} leX dγ))
           dγ n
           (λ j → trans (liftFn-∘-restrictEnv leF (elaborate C.Heap f) dγ j)
                        (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
           (λ j → trans (liftFn-∘-restrictEnv leX (elaborate C.Heap x) dγ j)
                        (faithful x (restrictᴰ {Γ = Γ} leX dγ) j))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)
    leX = ⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))
faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} f x) dγ n =
  app-body (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
           (elaborate C.Heap x ∘ restrictEnv {Γ = Γ} C.Heap leX)
           (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
           (SD.⟦ x ⟧ˢ fmt (restrictᴰ {Γ = Γ} leX dγ))
           dγ n
           (λ j → trans (liftFn-∘-restrictEnv leF (elaborate C.Heap f) dγ j)
                        (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
           (λ j → trans (liftFn-∘-restrictEnv leX (elaborate C.Heap x) dγ j)
                        (faithful x (restrictᴰ {Γ = Γ} leX dγ) j))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)
    leX = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))
-- effApp: a SUSPENDED closure whose body is the (effectful) application of f to x.
-- Both sides are `returnT <closure>` (the Unit-thunk); the closure body is exactly
-- app-body, lifted through extensionality (over the discarded Unit arg + depth).
faithful (effApp {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} f x) dγ k =
  trans (cong (λ t → t k) liftFn-curry-reduce-effApp)
        (cong (_,_ []) (extensionality (λ _ → extensionality (λ n →
          app-body (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
                   (elaborate C.Heap x ∘ restrictEnv {Γ = Γ} C.Heap leX)
                   (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
                   (SD.⟦ x ⟧ˢ fmt (restrictᴰ {Γ = Γ} leX dγ))
                   dγ n
                   (λ j → trans (liftFn-∘-restrictEnv leF (elaborate C.Heap f) dγ j)
                                (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
                   (λ j → trans (liftFn-∘-restrictEnv leX (elaborate C.Heap x) dγ j)
                                (faithful x (restrictᴰ {Γ = Γ} leX dγ) j))))))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leX = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ)) dγ
    inner = apply ∘ ⟨ elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF
                    , elaborate C.Heap x ∘ restrictEnv {Γ = Γ} C.Heap leX ⟩ C.Heap
    body = inner ∘ fst
    liftFn-curry-reduce-effApp :
      liftFn fmt {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {Unit ⇒[ mk-kind Many eff ] B} (curry body C.Heap) dγ
      ≡ returnT (λ _ → liftFn fmt {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {B} inner dγ)
    liftFn-curry-reduce-effApp =
      trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ Unit) (cohᴰ B))
                             (λ u → evalᴰ fmt body (dγ' , u)))
            (cong returnT (subst-arrowᴰ (cohᴰ Unit) (cohᴰ B) (λ u → evalᴰ fmt body (dγ' , u))))
-- absurd v : v has type Void, so `proj₂ (⟦v⟧ˢ dγ n) : ⊥` — vacuous.
faithful (absurd v) dγ n = ⊥-elim (proj₂ ((SD.⟦ v ⟧ˢ fmt) dγ n))
faithful unit    dγ k = refl
faithful (int n) dγ k = refl   -- both sides are `fromℤ (int-bits fmt) n` (the `absℤ` this
                               -- comment used to describe is gone; D054/D115)
faithful (float d) dγ k = refl   -- both sides are `round (float-format fmt) d` (K1)
faithful (str s) dγ k = refl   -- ⟦str s⟧ˢ fmt now denotes via str-lit-info's semM = strLit's evalᴰ fmt
-- Single-subterm projections/injections: `elaborate (op e) = <prim> ∘ elaborate e`
-- and `⟦ op e ⟧ˢ = ⟦e⟧ˢ >>=T (λv → returnT (<prim> v))`; `_>>=T_` sees the same
-- depth on both sides, so the trace+value at `n` is a function of the SUBTERM's
-- (trace,value) at `n` — one `cong` over the IH (`faithful e`).
-- D127: `comp'` delegates to `comp-body`, the same way `app` delegates to
-- `app-body`.
faithful (comp' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) dγ n =
  comp-body (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
            (elaborate C.Heap g ∘ restrictEnv {Γ = Γ} C.Heap leG)
            (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
            (SD.⟦ g ⟧ˢ fmt (restrictᴰ {Γ = Γ} leG dγ))
            dγ n
            (λ j → trans (liftFn-∘-restrictEnv leF (elaborate C.Heap f) dγ j)
                         (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
            (λ j → trans (liftFn-∘-restrictEnv leG (elaborate C.Heap g) dγ j)
                         (faithful g (restrictᴰ {Γ = Γ} leG dγ) j))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leG = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (curry' f) dγ n =
  curry-body (elaborate C.Heap f) (SD.⟦ f ⟧ˢ fmt dγ) dγ n (λ j → faithful f dγ j)
faithful (fork' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) dγ n =
  fork-body (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
            (elaborate C.Heap g ∘ restrictEnv {Γ = Γ} C.Heap leG)
            (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
            (SD.⟦ g ⟧ˢ fmt (restrictᴰ {Γ = Γ} leG dγ))
            dγ n
            (λ j → trans (liftFn-∘-restrictEnv leF (elaborate C.Heap f) dγ j)
                         (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
            (λ j → trans (liftFn-∘-restrictEnv leG (elaborate C.Heap g) dγ j)
                         (faithful g (restrictᴰ {Γ = Γ} leG dγ) j))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leG = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (copair' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) dγ n =
  copair-body (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
            (elaborate C.Heap g ∘ restrictEnv {Γ = Γ} C.Heap leG)
            (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
            (SD.⟦ g ⟧ˢ fmt (restrictᴰ {Γ = Γ} leG dγ))
            dγ n
            (λ j → trans (liftFn-∘-restrictEnv leF (elaborate C.Heap f) dγ j)
                         (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
            (λ j → trans (liftFn-∘-restrictEnv leG (elaborate C.Heap g) dγ j)
                         (faithful g (restrictᴰ {Γ = Γ} leG dγ) j))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leG = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fst' {A = A} {B = B} e) dγ n =
  trans (cong (λ t → subst T (cohᴰ A) t n) (cong (λ h → h >>=T (λ v → returnT (proj₁ v))) (ihᴰ e dγ (λ j → faithful e dγ j))))
        (fst-transport (cohᴰ A) (cohᴰ B) (SD.⟦ e ⟧ˢ fmt dγ) n)
faithful (snd' {A = A} {B = B} e) dγ n =
  trans (cong (λ t → subst T (cohᴰ B) t n) (cong (λ h → h >>=T (λ v → returnT (proj₂ v))) (ihᴰ e dγ (λ j → faithful e dγ j))))
        (snd-transport (cohᴰ A) (cohᴰ B) (SD.⟦ e ⟧ˢ fmt dγ) n)
faithful (inl' {A = A} {B = B} e) dγ n =
  trans (cong (λ t → subst T (cohᴰ (A + B)) t n) (cong (λ h → h >>=T (λ v → returnT (inj₁ v))) (ihᴰ e dγ (λ j → faithful e dγ j))))
        (inl-transport (cohᴰ A) (cohᴰ B) (SD.⟦ e ⟧ˢ fmt dγ) n)
faithful (inr' {A = A} {B = B} e) dγ n =
  trans (cong (λ t → subst T (cohᴰ (A + B)) t n) (cong (λ h → h >>=T (λ v → returnT (inj₂ v))) (ihᴰ e dγ (λ j → faithful e dγ j))))
        (inr-transport (cohᴰ A) (cohᴰ B) (SD.⟦ e ⟧ˢ fmt dγ) n)
-- Two-subterm arith (elaborate = `<op>IR ∘ ⟨ea,eb⟩`, ⟦_⟧ˢ via the same `semM`):
-- rewrite both IHs; the only residual is the IR `SigOp`-bind's extra empty trace
-- (`(W ++ []) ≡ W`, ++-identityʳ); the value is identical (same `semM`).
faithful (add {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-II add-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (sub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-II sub-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (mul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-II mul-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
faithful (fadd {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-FF fadd-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fsub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-FF fsub-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fmul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-FF fmul-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fdiv {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-FF fdiv-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (i2f a)    dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) = refl   -- unary: no `++` to neutralise, cf. `neg`
faithful (div {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-II div-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (mod' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-II mod-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (lt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB lt-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (le {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB le-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (gt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB gt-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (ge {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB ge-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (eq {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB eq-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (ne {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB ne-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
-- neg: single subterm; IR `negIR ∘ ee` and ⟦_⟧ˢ share the bind+cont, so refl post-IH.
faithful (neg e)    dγ n rewrite ihᴰ e dγ (λ j → faithful e dγ j) = refl
-- pair: `elaborate = ⟨ea,eb⟩`, same bind structure as ⟦_⟧ˢ (ends in returnT(va,vb),
-- no trailing SigOp bind) ⇒ refl post both IHs.
faithful (pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} a b) dγ n =
  trans (cong (λ t → subst T (cohᴰ (A * B)) t n)
              (cong₂ (λ ha hb → ha >>=T (λ va → hb >>=T (λ vb → returnT (va , vb))))
                     (ihᴰ∘ leA a dγ (λ j → faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
                     (ihᴰ∘ leB b dγ (λ j → faithful b (restrictᴰ {Γ = Γ} leB dγ) j))))
        (pair-transport (cohᴰ A) (cohᴰ B)
                        (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
                        (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ)) n)
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
-- arr': `elaborate = arr ∘ ef` adds one `returnT` bind (an extra ++[]); the kind
-- change is erased by ⟦_⟧ᴰ, value unchanged ⇒ ++-identityʳ.
-- IR embedding: ⟦_⟧ˢ denotes these AS `evalᴰ morph`; elaborate's
-- `curry (morph ∘ snd)` / `morph ∘ ex` reduce to the same (returnT/[]++X + eta).
faithful (lift-morphism {A = A} {B = B} morph) dγ k =
  cong (λ t → t k)
    (trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)) (λ a → evalᴰ fmt morph a))
           (cong returnT (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt morph a))))
faithful (morph-app {A = A} {B = B} morph e) dγ n =
  trans (cong (λ t → subst T (cohᴰ B) t n)
              (cong (λ h → h >>=T (λ v → evalᴰ fmt morph v)) (ihᴰ e dγ (λ j → faithful e dγ j))))
        (morphapp-transport (cohᴰ A) (cohᴰ B) (λ v → evalᴰ fmt morph v) (SD.⟦ e ⟧ˢ fmt dγ) n)
-- let': `elaborate = ee2 ∘ ⟨id, ee1⟩`. Rewrite the e1 IH, then the e2 IH at the
-- extended env (dγ , v1); residual is the ⟨id,…⟩/pair empty traces:
-- `(W ++ []) ++ Z ≡ W ++ Z`. Value identical.
faithful (let' {Γ = Γ} {A = A} {B = B} e1 e2) dγ n =
  trans (cong (λ t → subst T (cohᴰ B) t n)
              (trans let-reduce
                     (cong (λ h → h >>=T (λ v1 → evalᴰ fmt ee2 (dγ' , v1))) (ihᴰ e1 dγ (λ j → faithful e1 dγ j)))))
        (trans (morphapp-transport (cohᴰ A) (cohᴰ B) (λ v1 → evalᴰ fmt ee2 (dγ' , v1)) (SD.⟦ e1 ⟧ˢ fmt dγ) n)
               (cong (λ cont → (SD.⟦ e1 ⟧ˢ fmt dγ >>=T cont) n) (extensionality e2-eq)))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ _ ⟧ᶜ)) dγ
    ee1 = elaborate C.Heap e1
    ee2 = elaborate C.Heap e2
    let-reduce : evalᴰ fmt (ee2 ∘ ⟨ idIR , ee1 ⟩ C.Heap) dγ'
                 ≡ (evalᴰ fmt ee1 dγ' >>=T (λ v1 → evalᴰ fmt ee2 (dγ' , v1)))
    let-reduce = extensionality (λ m →
      cong₂ _,_ (app-trace [] (proj₁ (evalᴰ fmt ee1 dγ' m))
                          (proj₁ (evalᴰ fmt ee2 (dγ' , proj₂ (evalᴰ fmt ee1 dγ' m)) m))) refl)
    e2-eq : ∀ (v1 : ⟦ A ⟧ᴰ) → subst T (cohᴰ B) (evalᴰ fmt ee2 (dγ' , subst id (sym (cohᴰ A)) v1)) ≡ SD.⟦ e2 ⟧ˢ fmt (dγ , v1)
    e2-eq v1 = trans (cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ee2 w)) (sym (pair-subst⁻ (cohᴰ ⟦ Γ ⟧ᶜ) (cohᴰ A) dγ v1)))
                     (extensionality (λ j → faithful e2 (dγ , v1) j))
-- Effect primitives: ⟦_⟧ˢ denotes them through generic-info/emit-D/semM exactly
-- as elaborate's `SigOp(generic-info name)∘terminal` (non-arrow) / `curry(SigOp∘
-- snd)` (arrow) reduce ([]++X, returnT, eta) ⇒ refl.
faithful (sigOp {A = (Dom ⇒[ kk ] Cod)} name (con-fun bDom cCod)) dγ k =
  cong (λ t → t k)
    (trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ Dom) (cohᴰ Cod))
                            (λ a → evalᴰ fmt (SigOp (arrow-info kk name bDom cCod)) a))
           (cong returnT
             (trans (subst-arrowᴰ (cohᴰ Dom) (cohᴰ Cod) (λ a → evalᴰ fmt (SigOp (arrow-info kk name bDom cCod)) a))
                    (liftFn-SigOp (arrow-info kk name bDom cCod) bDom))))
faithful {Γ = Γ} {A = A} (closure name) dγ k = sigop-value {Γ = Γ} {A = A} (internal-info (bare name)) dγ k
faithful {Γ = Γ} (poly name PT) dγ k = sigop-value {Γ = Γ} {A = PT} (internal-info (bare name)) dγ k
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
faithful {Γ = Γ} (sigOp {A = _ * _}    name conc) dγ k = sigop-value {Γ = Γ} (value-info name base-Unit conc) dγ k
faithful {Γ = Γ} (sigOp {A = _ + _}    name conc) dγ k = sigop-value {Γ = Γ} (value-info name base-Unit conc) dγ k
faithful {Γ = Γ} (sigOp {A = μ-type _} name conc) dγ k = sigop-value {Γ = Γ} (value-info name base-Unit conc) dγ k
faithful {Γ = Γ} (sigOp {A = ν-type _} name conc) dγ k = sigop-value {Γ = Γ} (value-info name base-Unit conc) dγ k
faithful (case' {Γ = Γ} {A = A} {B = B} {C = C} s l r) dγ n =
  trans (cong (λ t → subst T (cohᴰ C) t n)
              (trans case-reduce (cong (λ h → h >>=T branchᴰ) (ihᴰ s dγ (λ j → faithful s dγ j)))))
        (trans (morphapp-transport (cohᴰ (A + B)) (cohᴰ C) branchᴰ (SD.⟦ s ⟧ˢ fmt dγ) n)
               (cong (λ cont → (SD.⟦ s ⟧ˢ fmt dγ >>=T cont) n) (extensionality branch-eq)))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ _ ⟧ᶜ)) dγ
    es = elaborate C.Heap s
    ll = elaborate C.Heap l
    rr = elaborate C.Heap r
    reshape : ⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ
            → ⟦ (⌊ ⟦ Γ ⟧ᶜ ⌋ *ᴵ ⌊ A ⌋) +ᴵ (⌊ ⟦ Γ ⟧ᶜ ⌋ *ᴵ ⌊ B ⌋) ⟧ᴰᴵ
    reshape v = [ (λ a → inj₁ (dγ' , a)) , (λ b → inj₂ (dγ' , b)) ]′ v
    branchᴰ = λ v → [ (λ a → evalᴰ fmt ll (dγ' , a)) , (λ b → evalᴰ fmt rr (dγ' , b)) ]′ v
    -- `distribute` is pure (`distribute-reduce`), so `distribute ∘ ⟨id,es⟩` is just
    -- `es` followed by a pure re-shape of the sum (empty distribute trace).
    dd-reduce : evalᴰ fmt (distribute {⌊ ⟦ Γ ⟧ᶜ ⌋} {⌊ A ⌋} {⌊ B ⌋} C.Heap ∘ ⟨ idIR , es ⟩ C.Heap) dγ'
              ≡ (evalᴰ fmt es dγ' >>=T λ v → returnT (reshape v))
    dd-reduce = extensionality (λ m →
      cong₂ _,_
        (trans (cong (λ z → (proj₁ (evalᴰ fmt es dγ' m) ++ []) ++ proj₁ (z m))
                     (distribute-reduce {⌊ ⟦ Γ ⟧ᶜ ⌋} {⌊ A ⌋} {⌊ B ⌋} dγ' (proj₂ (evalᴰ fmt es dγ' m))))
               (++-identityʳ (proj₁ (evalᴰ fmt es dγ' m) ++ [])))
        (cong (λ z → proj₂ (z m)) (distribute-reduce {⌊ ⟦ Γ ⟧ᶜ ⌋} {⌊ A ⌋} {⌊ B ⌋} dγ' (proj₂ (evalᴰ fmt es dγ' m)))))
    -- reshape-then-`case` fuses to the eliminator, per branch (both refl).
    case-fuse : ∀ (v : ⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ)
              → evalᴰ fmt (case ll rr) (reshape v) ≡ branchᴰ v
    case-fuse (inj₁ a) = refl
    case-fuse (inj₂ b) = refl
    -- bind-assoc + case-fuse folded pointwise (no `>>=T-assoc` in the library).
    assoc-fuse : ∀ (mm : T (⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ))
               → ((mm >>=T λ v → returnT (reshape v)) >>=T evalᴰ fmt (case ll rr))
                 ≡ (mm >>=T branchᴰ)
    assoc-fuse mm = extensionality (λ m →
      cong₂ _,_
        (trans (cong (λ z → (proj₁ (mm m) ++ []) ++ proj₁ (z m)) (case-fuse (proj₂ (mm m))))
               (cong (_++ proj₁ (branchᴰ (proj₂ (mm m)) m)) (++-identityʳ (proj₁ (mm m)))))
        (cong (λ z → proj₂ (z m)) (case-fuse (proj₂ (mm m)))))
    case-reduce : evalᴰ fmt (elaborate C.Heap (case' s l r)) dγ' ≡ (evalᴰ fmt es dγ' >>=T branchᴰ)
    case-reduce = trans (cong (_>>=T evalᴰ fmt (case ll rr)) dd-reduce)
                        (assoc-fuse (evalᴰ fmt es dγ'))
    branch-eq : ∀ (v : ⟦ A + B ⟧ᴰ)
              → subst T (cohᴰ C) (branchᴰ (subst id (sym (cohᴰ (A + B))) v))
                ≡ [ (λ a → SD.⟦ l ⟧ˢ fmt (dγ , a)) , (λ b → SD.⟦ r ⟧ˢ fmt (dγ , b)) ]′ v
    branch-eq (inj₁ a) =
      trans (cong (λ w → subst T (cohᴰ C) (branchᴰ w)) (push⊎₁⁻ (cohᴰ A) (cohᴰ B) a))
            (trans (cong (λ w → subst T (cohᴰ C) (evalᴰ fmt ll w)) (sym (pair-subst⁻ (cohᴰ ⟦ Γ ⟧ᶜ) (cohᴰ A) dγ a)))
                   (extensionality (λ j → faithful l (dγ , a) j)))
    branch-eq (inj₂ b) =
      trans (cong (λ w → subst T (cohᴰ C) (branchᴰ w)) (push⊎₂⁻ (cohᴰ A) (cohᴰ B) b))
            (trans (cong (λ w → subst T (cohᴰ C) (evalᴰ fmt rr w)) (sym (pair-subst⁻ (cohᴰ ⟦ Γ ⟧ᶜ) (cohᴰ B) dγ b)))
                   (extensionality (λ j → faithful r (dγ , b) j)))
-- cata: both sides fold with per-layer-threaded algebras; reduces to the
-- closure-bridge (`cata-body`) — the algebra IH + a monad reduction, no
-- purity assumption (the build trace is threaded, not discarded).
faithful {Γ = Γ} (cata wf alg) dγ k = FL.cata-body {Γ = Γ} wf alg (λ j → faithful alg tt j) dγ k
-- ana: dual of cata; reduces to the same closure-bridge via `ana-body`
-- (+ the `ana-ev-bridge` trace lemma).
faithful {Γ = Γ} (ana wf coalg) dγ k = FL.ana-body {Γ = Γ} wf coalg (λ j → faithful coalg tt j) dγ k
