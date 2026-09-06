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

open import Once.Type using (Type; Unit; Void; Int; Str; Float; Buffer; _*_; _+_; _⇒[_]_; μ-type; ν-type; mk-kind; pure; eff; Quantity; Zero; One; Many)
open import Once.Functor.Translate using (con-base; con-fun; base-Unit)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; lookup; _,_^_; ⟦_⟧ᶜ; _↾_; zeroUsage; singleUse; ∅;
                                       _⊑ᵘ_; ⊑[]; _⊑∷_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m;
                                       ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; _+ᵘ_; _*ᵘ_;
                                       _⊔ᵘ_; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; _∷_)
open import Once.Surface.Context using () renaming (_,_ to _,ᶜ_)
import Once.Surface.Syntax as SrfS
open import Once.Surface.Properties using (erase-arg-usage)
open import Once.Surface.Elaborate using (elaborate; elaborateFull; proj; projUsed; distribute; compIR; copairIR; forkIR; curryIR; distribIR;
                                          envˡ; envʳ; restrictEnv; bindEnv)
open import Once.Denotation.Phase using (lookupᴰUsed; restrictᴰ; bindᴰ; bindᴰ0; env0)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.IR using (_∘_; ⟨_,_⟩; apply; fst; snd; curry; SigOp; terminal; case) renaming (id to idIR)
open import Once.Arith.SigOp.Builders using (arrow-info; value-info; internal-info;
                                             add-info; sub-info; mul-info; div-info; mod-info; fadd-info; fsub-info; fmul-info; fdiv-info; lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.Adequacy.CataErased fmt using (liftFn-SigOp)
open import Once.Adequacy.LiftFnReduce fmt using (liftFn-id; liftFn-fst; liftFn-snd; liftFn-∘; liftFn-pair;
                                                  liftFn-terminal)
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
    → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ}
             (restrictEnv {Γ = Γ} C.Heap ule ∘ fst) dγ k
      ≡ returnT (restrictᴰ {Γ = Γ} ule (proj₁ dγ)) k
  restrictEnv-drop {Γ = Γ} {A = A} {Ψ = Ψ} {Ψ' = Ψ'} ule dγ k =
    trans (cong (λ t → t dγ k)
                (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = ⟦ Γ ↾ Ψ' ⟧ᶜ} {A = ⟦ Γ ↾ Ψ ⟧ᶜ * A}
                          (restrictEnv {Γ = Γ} C.Heap ule) fst))
      (trans (cong (λ t → (t dγ >>=T liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ}
                                            (restrictEnv {Γ = Γ} C.Heap ule)) k)
                   (liftFn-fst {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))
             (liftFn-restrictEnv {Γ = Γ} ule (proj₁ dγ) k))

  -- head variable live in BOTH — keep it, narrow the rest.
  restrictEnv-keep :
    ∀ {n} {Γ : Ctx n} {A : Type} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
      (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ × ⟦ A ⟧ᴰ) (k : ℕ)
    → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ * A}
             (⟨ restrictEnv {Γ = Γ} C.Heap ule ∘ fst , snd ⟩) dγ k
      ≡ returnT (restrictᴰ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ) k
  restrictEnv-keep {Γ = Γ} {A = A} {Ψ = Ψ} {Ψ' = Ψ'} ule dγ k =
    trans (cong (λ t → t dγ k)
                (liftFn-pair {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A}
                             (restrictEnv {Γ = Γ} C.Heap ule ∘ fst) snd))
      (trans (cong (λ t → (t >>=T (λ b → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {A} snd dγ
                                            >>=T λ c → returnT (b , c))) k)
                   (extensionality (restrictEnv-drop {Γ = Γ} {A = A} ule dγ)))
             (cong (λ t → (returnT (restrictᴰ {Γ = Γ} ule (proj₁ dγ))
                            >>=T (λ b → t >>=T λ c → returnT (b , c))) k)
                   (cong (λ u → u dγ) (liftFn-snd {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))))

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
liftFn-∘-restrictEnv {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule h dγ k =
  trans (cong (λ t → t dγ k)
              (liftFn-∘ {B = ⟦ Γ ↾ Ψ' ⟧ᶜ} {C = A} {A = ⟦ Γ ↾ Ψ ⟧ᶜ}
                        h (restrictEnv {Γ = Γ} C.Heap ule)))
        (cong (λ t → (t >>=T liftFn fmt {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} h) k)
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
             → liftFn fmt {X} {Int} (SigOp info ∘ ⟨ ea , eb ⟩) dγ n
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
             → liftFn fmt {X} {Float} (SigOp info ∘ ⟨ ea , eb ⟩) dγ n
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
             → liftFn fmt {X} {(Unit + Unit)} (SigOp info ∘ ⟨ ea , eb ⟩) dγ n
               ≡ (sa >>=T (λ va → sb >>=T (λ vb → returnT (semM info fmt (va , vb))))) n
arith-body-IB {X = X} info ea eb sa sb dγ n noEmit iha ihb
  rewrite ihᴰgen {X} {Int} ea sa dγ iha | ihᴰgen {X} {Int} eb sb dγ ihb
        | noEmit (proj₂ (sa n) , proj₂ (sb n))
        | inject-BB (semM info fmt (proj₂ (sa n) , proj₂ (sb n))) =
  cong₂ _,_ (++-identityʳ _) refl

-- Narrowing along a witness whose two usages are the SAME is the identity. The
-- off-diagonal constructors (`z≤o`, `z≤m`, `o≤m`) cannot occur: they demand
-- different head quantities on the two sides of one vector.
restrictᴰ-id : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} (ule : Ψ ⊑ᵘ Ψ)
               (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) → restrictᴰ {Γ = Γ} ule dγ ≡ dγ
restrictᴰ-id {Γ = ∅}         ⊑[]            dγ = refl
restrictᴰ-id {Γ = Γ , A ^ q} (z≤z ⊑∷ ule) dγ = restrictᴰ-id {Γ = Γ} ule dγ
restrictᴰ-id {Γ = Γ , A ^ q} (o≤o ⊑∷ ule) dγ =
  cong (_, proj₂ dγ) (restrictᴰ-id {Γ = Γ} ule (proj₁ dγ))
restrictᴰ-id {Γ = Γ , A ^ q} (m≤m ⊑∷ ule) dγ =
  cong (_, proj₂ dγ) (restrictᴰ-id {Γ = Γ} ule (proj₁ dγ))

-- ...hence narrowing along a PROPOSITIONALLY equal usage IS the transport.
restrictᴰ-subst : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ) (eq : Ψ ≡ Ψ')
                  (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
  → restrictᴰ {Γ = Γ} ule dγ ≡ subst (λ Φ → ⟦ ⟦ Γ ↾ Φ ⟧ᶜ ⟧ᴰ) eq dγ
restrictᴰ-subst {Γ = Γ} ule refl dγ = restrictᴰ-id {Γ = Γ} ule dγ

-- Peeling `elaborate`'s usage transport (the `q = Zero` `let'`).
liftFn-substΦ : ∀ {n} {Γ : Ctx n} {Φ Φ' : Usage n} {B} (eq : Φ ≡ Φ')
                (h : C.IR ⌊ ⟦ Γ ↾ Φ' ⟧ᶜ ⌋ ⌊ B ⌋) (dγ : ⟦ ⟦ Γ ↾ Φ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → liftFn fmt {⟦ Γ ↾ Φ ⟧ᶜ} {B}
           (subst (λ Φ'' → C.IR ⌊ ⟦ Γ ↾ Φ'' ⟧ᶜ ⌋ ⌊ B ⌋) (sym eq) h) dγ k
    ≡ liftFn fmt {⟦ Γ ↾ Φ' ⟧ᶜ} {B} h
           (subst (λ Φ'' → ⟦ ⟦ Γ ↾ Φ'' ⟧ᶜ ⟧ᴰ) eq dγ) k
liftFn-substΦ refl h dγ k = refl

-- D143: THE BRANCH ENVIRONMENT, in three steps. `case'` builds a branch's
-- environment as `bindEnv q ∘ ⟨ restrictEnv ule ∘ fst , snd ⟩` (IR) against
-- `bindᴰ q (restrictᴰ ule dγ) a` (semantics). Absorbing the quantity split into
-- `bindEnv-denote` is what keeps `case'` a SINGLE clause rather than nine:
-- `bindEnv qℓ` may stay opaque there, because its denotation is supplied here.

bindEnv-denote : ∀ {n} {Γ : Ctx n} {Ψ' : Usage n} {A} (q : Quantity)
                 (d : ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ) (k : ℕ)
  → liftFn fmt {⟦ Γ ↾ Ψ' ⟧ᶜ * A} {⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ}
           (bindEnv {Γ = Γ} {A = A} C.Heap q) (d , a) k
    ≡ returnT (bindᴰ {Γ = Γ} {A = A} q d a) k
bindEnv-denote {Γ = Γ} {A = A} Zero d a k =
  cong (λ t → t (d , a) k) (liftFn-fst {⟦ Γ ↾ _ ⟧ᶜ} {A})
bindEnv-denote {Γ = Γ} {A = A} One  d a k =
  cong (λ t → t (d , a) k) (liftFn-id {⟦ Γ ↾ _ ⟧ᶜ * A})
bindEnv-denote {Γ = Γ} {A = A} Many d a k =
  cong (λ t → t (d , a) k) (liftFn-id {⟦ Γ ↾ _ ⟧ᶜ * A})

branch-pair : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} {A} (ule : Ψ' ⊑ᵘ Ψ)
              (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ) (k : ℕ)
  → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ * A}
           (⟨ restrictEnv {Γ = Γ} C.Heap ule ∘ fst , snd ⟩) (dγ , a) k
    ≡ returnT (restrictᴰ {Γ = Γ} ule dγ , a) k
branch-pair {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule dγ a k =
  trans (cong (λ t → t (dγ , a) k)
              (liftFn-pair {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A}
                           (restrictEnv {Γ = Γ} C.Heap ule ∘ fst) snd))
    (trans (cong (λ t → (t >>=T (λ x → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {A} snd (dγ , a)
                                          >>=T λ y → returnT (x , y))) k)
                 (extensionality (restrictEnv-drop {Γ = Γ} {A = A} ule (dγ , a))))
           (cong (λ t → (returnT (restrictᴰ {Γ = Γ} ule dγ)
                          >>=T (λ x → t >>=T λ y → returnT (x , y))) k)
                 (cong (λ u → u (dγ , a)) (liftFn-snd {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))))

branchEnv-denote : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} {A} (ule : Ψ' ⊑ᵘ Ψ) (q : Quantity)
                   (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ) (k : ℕ)
  → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ}
           (bindEnv {Γ = Γ} {A = A} C.Heap q
             ∘ ⟨ restrictEnv {Γ = Γ} C.Heap ule ∘ fst , snd ⟩) (dγ , a) k
    ≡ returnT (bindᴰ {Γ = Γ} {A = A} q (restrictᴰ {Γ = Γ} ule dγ) a) k
branchEnv-denote {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule q dγ a k =
  trans (cong (λ t → t (dγ , a) k)
              (liftFn-∘ {B = ⟦ Γ ↾ Ψ' ⟧ᶜ * A} {C = ⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ}
                        {A = ⟦ Γ ↾ Ψ ⟧ᶜ * A}
                        (bindEnv {Γ = Γ} {A = A} C.Heap q)
                        (⟨ restrictEnv {Γ = Γ} C.Heap ule ∘ fst , snd ⟩)))
    (trans (cong (λ t → (t >>=T liftFn fmt {⟦ Γ ↾ Ψ' ⟧ᶜ * A} {⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ}
                                    (bindEnv {Γ = Γ} {A = A} C.Heap q)) k)
                 (extensionality (branch-pair {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule dγ a)))
           (bindEnv-denote {Γ = Γ} {Ψ' = Ψ'} {A = A} q (restrictᴰ {Γ = Γ} ule dγ) a k))

-- `liftFn-restrictEnv` in `evalᴰ` form — the shape the `let'`/`case'` clauses
-- need, since they reason under `evalᴰ` rather than `liftFn`.
evalᴰ-restrictEnv : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                    (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
  → evalᴰ fmt (restrictEnv {Γ = Γ} C.Heap ule) (subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ)
    ≡ returnT (subst id (sym (cohᴰ ⟦ Γ ↾ Ψ' ⟧ᶜ)) (restrictᴰ {Γ = Γ} ule dγ))
evalᴰ-restrictEnv {Γ = Γ} {Ψ' = Ψ'} ule dγ =
  trans (ihᴰgen {⟦ Γ ↾ _ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ}
                (restrictEnv {Γ = Γ} C.Heap ule)
                (returnT (restrictᴰ {Γ = Γ} ule dγ)) dγ
                (liftFn-restrictEnv {Γ = Γ} ule dγ))
        (subst-T-returnT (sym (cohᴰ ⟦ Γ ↾ Ψ' ⟧ᶜ)) (restrictᴰ {Γ = Γ} ule dγ))

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
ihᴰ∘ {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule e dγ ih =
  trans (sym (subst-sym-subst (cohᴰ A)))
        (cong (subst T (sym (cohᴰ A)))
              (extensionality (λ j →
                 trans (liftFn-∘-restrictEnv {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A}
                                             ule (elaborate C.Heap e) dγ j) (ih j))))

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

-- D143: the ERASED-arrow analogue. `cohᴰ (A ⇒[Zero] B)` is a ONE-equation
-- `cong` (both sides forget the argument), so `app-transport`'s two-equation
-- form does not apply.
app-transport₀ : ∀ {U BI BT : Set} (pB : BI ≡ BT)
    (hf : T (U → T BT)) (hx : T U) (n : ℕ)
  → subst T pB ((subst T (sym (cong (λ y → U → T y) pB)) hf)
                  >>=T (λ vf → hx >>=T (λ vx → vf vx))) n
    ≡ (hf >>=T (λ vf → hx >>=T (λ vx → vf vx))) n
app-transport₀ refl hf hx n = refl

app-body-Zero : ∀ {X : Type} {A B} {π}
             (ef : C.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Zero π ] B ⌋) (ex : C.IR ⌊ X ⌋ ⌊ Unit ⌋)
             (sf : T ⟦ A ⇒[ mk-kind Zero π ] B ⟧ᴰ) (sx : T ⟦ Unit ⟧ᴰ)
             (dγ : ⟦ X ⟧ᴰ) (n : ℕ)
           → (∀ j → liftFn fmt {X} {A ⇒[ mk-kind Zero π ] B} ef dγ j ≡ sf j)
           → (∀ j → liftFn fmt {X} {Unit} ex dγ j ≡ sx j)
           → liftFn fmt {X} {B} (apply ∘ ⟨ ef , ex ⟩) dγ n
             ≡ (sf >>=T (λ vf → sx >>=T (λ vx → vf vx))) n
app-body-Zero {X = X} {A = A} {B = B} ef ex sf sx dγ n ihf ihx =
  trans (cong (λ t → subst T (cohᴰ B) t n)
              (trans evalᴰ-app-reduce
                     (cong₂ (λ hf hx → hf >>=T (λ vf → hx >>=T (λ vx → vf vx))) ihf-T ihx-T)))
        (app-transport₀ (cohᴰ B) sf sx n)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ B))) sf
    ihf-T = trans (sym (subst-sym-subst (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ B))))
                  (cong (subst T (sym (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ B))))
                        (extensionality ihf))
    -- `cohᴰ Unit` is `refl`, so the transport is the identity and the IH lands
    -- directly (the general `subst-sym-subst` route leaves its motive a meta).
    ihx-T : evalᴰ fmt ex dγ' ≡ subst T (sym (cohᴰ Unit)) sx
    ihx-T = extensionality ihx
    evalᴰ-app-reduce : evalᴰ fmt (apply ∘ ⟨ ef , ex ⟩) dγ'
                       ≡ (evalᴰ fmt ef dγ' >>=T (λ vf → evalᴰ fmt ex dγ' >>=T (λ vx → vf vx)))
    evalᴰ-app-reduce = extensionality (λ m →
      cong₂ _,_ (app-trace (proj₁ (evalᴰ fmt ef dγ' m)) (proj₁ (evalᴰ fmt ex dγ' m))
                           (proj₁ ((proj₂ (evalᴰ fmt ef dγ' m)) (proj₂ (evalᴰ fmt ex dγ' m)) m))) refl)

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
                     (compIR C.Heap ∘ ⟨ ef , eg ⟩) dγ n
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
    evalᴰ-comp-reduce : evalᴰ fmt (compIR C.Heap ∘ ⟨ ef , eg ⟩) dγ'
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
                     (forkIR C.Heap ∘ ⟨ ef , eg ⟩) dγ n
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
    evalᴰ-fork-reduce : evalᴰ fmt (forkIR C.Heap ∘ ⟨ ef , eg ⟩) dγ'
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
                       (copairIR C.Heap ∘ ⟨ ef , eg ⟩) dγ n
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
    evalᴰ-copair-reduce : evalᴰ fmt (copairIR C.Heap ∘ ⟨ ef , eg ⟩) dγ'
                          ≡ (evalᴰ fmt ef dγ' >>=T (λ vf → evalᴰ fmt eg dγ' >>=T (λ vg →
                             returnT (λ ab → [ vf , vg ]′ ab))))
    -- The elaborated side goes through `distribIR` and then `case`, which is
    -- STUCK on an abstract sum value — so the per-call step case-splits on the
    -- argument. That is the only structural difference from the other three.
    branch : ∀ (m : ℕ) (ab : ⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ)
           → proj₂ (evalᴰ fmt (copairIR C.Heap ∘ ⟨ ef , eg ⟩) dγ' m) ab
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
           → liftFn fmt {X} {B} (apply ∘ ⟨ ef , ex ⟩) dγ n
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
    evalᴰ-app-reduce : evalᴰ fmt (apply ∘ ⟨ ef , ex ⟩) dγ'
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
           → liftFn fmt {X} {B} (apply ∘ ⟨ ef , ex ⟩) dγ n
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
    evalᴰ-app-reduce : evalᴰ fmt (apply ∘ ⟨ ef , ex ⟩) dγ'
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
    eeF : C.IR (⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ *ᴵ ⌊ Unit ⌋) ⌊ B ⌋
    eeF = ee ∘ fst
    drop : ∀ u j → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * Unit} {B} eeF (dγ , u) j
                 ≡ liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee dγ j
    drop u j = trans (cong (λ t → t (dγ , u) j)
                           (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = B} {A = ⟦ Γ ↾ Ψ ⟧ᶜ * Unit} ee fst))
                     (cong (λ t → (t (dγ , u) >>=T liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee) j)
                           (liftFn-fst {⟦ Γ ↾ Ψ ⟧ᶜ} {Unit}))
    red : liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Zero pure ] B} (curry eeF C.Heap) dγ
          ≡ returnT (λ u → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * Unit} {B} eeF (dγ , u))
    red = trans (subst-T-returnT (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ B))
                                 (λ u → evalᴰ fmt eeF (dγ' , u)))
            (cong returnT
              (trans (subst-arrow₀ᴰ (cohᴰ B) (λ u → evalᴰ fmt eeF (dγ' , u)))
                     (extensionality (λ u →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt eeF w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ Unit) dγ u))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} One _ e) dγ k =
  trans (cong (λ t → t k) red)
        (cong (_,_ []) (extensionality (λ a → extensionality (λ k′ →
          trans (drop a k′) (faithful e (bindᴰ0 {Γ = Γ} {A = A} dγ) k′)))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate C.Heap e
    eeF : C.IR (⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ *ᴵ ⌊ A ⌋) ⌊ B ⌋
    eeF = ee ∘ fst
    drop : ∀ a j → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} eeF (dγ , a) j
                 ≡ liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee dγ j
    drop a j = trans (cong (λ t → t (dγ , a) j)
                           (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = B} {A = ⟦ Γ ↾ Ψ ⟧ᶜ * A} ee fst))
                     (cong (λ t → (t (dγ , a) >>=T liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee) j)
                           (liftFn-fst {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))
    red : liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind One pure ] B} (curry eeF C.Heap) dγ
          ≡ returnT (λ a → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} eeF (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt eeF (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt eeF (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt eeF w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} Many _ e) dγ k =
  trans (cong (λ t → t k) red)
        (cong (_,_ []) (extensionality (λ a → extensionality (λ k′ →
          trans (drop a k′) (faithful e (bindᴰ0 {Γ = Γ} {A = A} dγ) k′)))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate C.Heap e
    eeF : C.IR (⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ *ᴵ ⌊ A ⌋) ⌊ B ⌋
    eeF = ee ∘ fst
    drop : ∀ a j → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} eeF (dγ , a) j
                 ≡ liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee dγ j
    drop a j = trans (cong (λ t → t (dγ , a) j)
                           (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = B} {A = ⟦ Γ ↾ Ψ ⟧ᶜ * A} ee fst))
                     (cong (λ t → (t (dγ , a) >>=T liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee) j)
                           (liftFn-fst {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))
    red : liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] B} (curry eeF C.Heap) dγ
          ≡ returnT (λ a → liftFn fmt {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} eeF (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt eeF (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt eeF (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt eeF w))
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
-- D143: at an ERASED arrow the argument is NOT evaluated — the elaborator emits
-- `⟨ ef , terminal ⟩` under an `erase-arg-usage` transport. Reuses
-- `app-body-Zero` carries the one-equation `cohᴰ` the erased arrow needs.
faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = Zero} f x) dγ n =
  trans (liftFn-substΦ {Γ = Γ} {Φ = Ψ₁ +ᵘ (Zero *ᵘ Ψ₂)} {Φ' = Ψ₁} {B = B}
                       (erase-arg-usage Ψ₁ Ψ₂)
                       (apply ∘ ⟨ elaborate C.Heap f , terminal ⟩) dγ n)
        (trans (cong (λ d → liftFn fmt {⟦ Γ ↾ Ψ₁ ⟧ᶜ} {B}
                              (apply ∘ ⟨ elaborate C.Heap f , terminal ⟩) d n)
                     (sym (restrictᴰ-subst {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂))
                                           (erase-arg-usage Ψ₁ Ψ₂) dγ)))
               (app-body-Zero {⟦ Γ ↾ Ψ₁ ⟧ᶜ} {A} {B} {pure}
                  (elaborate C.Heap f) terminal
                  (SD.⟦ f ⟧ˢ fmt Ez) (returnT tt) Ez n
                  (λ j → faithful f Ez j)
                  (λ j → cong (λ t → t Ez j) (liftFn-terminal {⟦ Γ ↾ Ψ₁ ⟧ᶜ}))))
  where
    Ez = restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) dγ
faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = One} f x) dγ n =
  app-body-One {⟦ Γ ↾ (Ψ₁ +ᵘ (One *ᵘ Ψ₂)) ⟧ᶜ} {A} {B} {pure}
           (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
           (elaborate C.Heap x ∘ restrictEnv {Γ = Γ} C.Heap leX)
           (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
           (SD.⟦ x ⟧ˢ fmt (restrictᴰ {Γ = Γ} leX dγ))
           dγ n
           (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind One pure ] B}
                                              leF (elaborate C.Heap f) dγ j)
                        (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
           (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A} leX (elaborate C.Heap x) dγ j)
                        (faithful x (restrictᴰ {Γ = Γ} leX dγ) j))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)
    leX = ⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))
faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = Many} f x) dγ n =
  app-body {⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ} {A} {B} {pure}
           (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
           (elaborate C.Heap x ∘ restrictEnv {Γ = Γ} C.Heap leX)
           (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
           (SD.⟦ x ⟧ˢ fmt (restrictᴰ {Γ = Γ} leX dγ))
           dγ n
           (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many pure ] B}
                                              leF (elaborate C.Heap f) dγ j)
                        (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
           (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A} leX (elaborate C.Heap x) dγ j)
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
          app-body {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {A} {B} {eff}
                   (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
                   (elaborate C.Heap x ∘ restrictEnv {Γ = Γ} C.Heap leX)
                   (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
                   (SD.⟦ x ⟧ˢ fmt (restrictᴰ {Γ = Γ} leX dγ))
                   dγ n
                   (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many eff ] B}
                                                     leF (elaborate C.Heap f) dγ j)
                                (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
                   (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A} leX (elaborate C.Heap x) dγ j)
                                (faithful x (restrictᴰ {Γ = Γ} leX dγ) j))))))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leX = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ)) dγ
    inner = apply ∘ ⟨ elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF
                    , elaborate C.Heap x ∘ restrictEnv {Γ = Γ} C.Heap leX ⟩
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
faithful (comp' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} f g) dγ n =
  comp-body {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {A} {B} {C} {π}
            (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
            (elaborate C.Heap g ∘ restrictEnv {Γ = Γ} C.Heap leG)
            (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
            (SD.⟦ g ⟧ˢ fmt (restrictᴰ {Γ = Γ} leG dγ))
            dγ n
            (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = B ⇒[ mk-kind Many π ] C} leF (elaborate C.Heap f) dγ j)
                         (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
            (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many π ] B} leG (elaborate C.Heap g) dγ j)
                         (faithful g (restrictᴰ {Γ = Γ} leG dγ) j))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leG = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (curry' {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} {C = C} f) dγ n =
  curry-body {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {B} {C}
             (elaborate C.Heap f) (SD.⟦ f ⟧ˢ fmt dγ) dγ n (λ j → faithful f dγ j)
faithful (fork' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} f g) dγ n =
  fork-body {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {A} {B} {C}
            (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
            (elaborate C.Heap g ∘ restrictEnv {Γ = Γ} C.Heap leG)
            (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
            (SD.⟦ g ⟧ˢ fmt (restrictᴰ {Γ = Γ} leG dγ))
            dγ n
            (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many pure ] B} leF (elaborate C.Heap f) dγ j)
                         (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
            (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many pure ] C} leG (elaborate C.Heap g) dγ j)
                         (faithful g (restrictᴰ {Γ = Γ} leG dγ) j))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leG = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (copair' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} f g) dγ n =
  copair-body {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {A} {B} {C} {π}
            (elaborate C.Heap f ∘ restrictEnv {Γ = Γ} C.Heap leF)
            (elaborate C.Heap g ∘ restrictEnv {Γ = Γ} C.Heap leG)
            (SD.⟦ f ⟧ˢ fmt (restrictᴰ {Γ = Γ} leF dγ))
            (SD.⟦ g ⟧ˢ fmt (restrictᴰ {Γ = Γ} leG dγ))
            dγ n
            (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many π ] C} leF (elaborate C.Heap f) dγ j)
                         (faithful f (restrictᴰ {Γ = Γ} leF dγ) j))
            (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = B ⇒[ mk-kind Many π ] C} leG (elaborate C.Heap g) dγ j)
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
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} add-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (sub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} sub-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (mul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} mul-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
faithful (fadd {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-FF {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} fadd-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fsub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-FF {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} fsub-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fmul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-FF {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} fmul-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fdiv {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-FF {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} fdiv-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (i2f a)    dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) = refl   -- unary: no `++` to neutralise, cf. `neg`
faithful (div {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} div-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (mod' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} mod-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (lt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} lt-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (le {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} le-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (gt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} gt-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (ge {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} ge-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (eq {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} eq-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ) j))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (ne {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ n =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} ne-info
    (elaborate C.Heap a ∘ restrictEnv {Γ = Γ} C.Heap leA)
    (elaborate C.Heap b ∘ restrictEnv {Γ = Γ} C.Heap leB)
    (SD.⟦ a ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt (restrictᴰ {Γ = Γ} leB dγ))
    dγ n (λ v → refl)
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate C.Heap a) dγ j)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ) j))
    (λ j → trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate C.Heap b) dγ j)
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
faithful (morph-app {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} morph e) dγ n =
  trans (cong (λ t → subst T (cohᴰ B) t n)
              (cong (λ h → h >>=T (λ v → evalᴰ fmt morph v))
                    (ihᴰ∘ leM e dγ (λ j → faithful e (restrictᴰ {Γ = Γ} leM dγ) j))))
        (morphapp-transport (cohᴰ A) (cohᴰ B) (λ v → evalᴰ fmt morph v)
                            (SD.⟦ e ⟧ˢ fmt (restrictᴰ {Γ = Γ} leM dγ)) n)
  where
    -- `leM`, not `le`: `le` is an `Expr` constructor in scope via `open Expr`.
    leM = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (Many *ᵘ Ψ))
-- let': `elaborate = ee2 ∘ ⟨id, ee1⟩`. Rewrite the e1 IH, then the e2 IH at the
-- extended env (dγ , v1); residual is the ⟨id,…⟩/pair empty traces:
-- `(W ++ []) ++ Z ≡ W ++ Z`. Value identical.
-- D143: at `q = Zero` the bound term is NOT ELABORATED at all — `elaborate`
-- returns the body transported by `erase-arg-usage`. So the clause peels that
-- transport (`liftFn-substΦ`) and identifies the transported environment with
-- the narrowed one (`restrictᴰ-subst`); `e1` never appears.
faithful (let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} {B = B} e1 e2) dγ n =
  trans (liftFn-substΦ {Γ = Γ} {Φ = Ψ₂ +ᵘ (Zero *ᵘ Ψ₁)} {Φ' = Ψ₂} {B = B}
                       (erase-arg-usage Ψ₂ Ψ₁) (elaborate C.Heap e2) dγ n)
        (trans (cong (λ d → liftFn fmt {⟦ Γ ↾ Ψ₂ ⟧ᶜ} {B} (elaborate C.Heap e2) d n)
                     (sym (restrictᴰ-subst {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁))
                                           (erase-arg-usage Ψ₂ Ψ₁) dγ)))
               (faithful e2 (bindᴰ0 {Γ = Γ} {A = A}
                              (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) dγ)) n))
faithful (let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {A = A} {B = B} e1 e2) dγ n =
  trans (cong (λ t → subst T (cohᴰ B) t n)
              (trans let-reduce
                     (cong (λ h → h >>=T (λ v1 → evalᴰ fmt ee2 (E2' , v1)))
                           (ihᴰ∘ leA e1 dγ (λ j → faithful e1 (restrictᴰ {Γ = Γ} leA dγ) j)))))
        (trans (morphapp-transport (cohᴰ A) (cohᴰ B) (λ v1 → evalᴰ fmt ee2 (E2' , v1))
                                   (SD.⟦ e1 ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ)) n)
               (cong (λ cont → (SD.⟦ e1 ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ) >>=T cont) n)
                     (extensionality e2-eq)))
  where
    leA = ⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))
    leB = ⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ (Ψ₂ +ᵘ (One *ᵘ Ψ₁)) ⟧ᶜ)) dγ
    E2' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ₂ ⟧ᶜ)) (restrictᴰ {Γ = Γ} leB dγ)
    ee1 = elaborate C.Heap e1 ∘ restrictEnv {Γ = Γ} C.Heap leA
    ee2 = elaborate C.Heap e2
    let-reduce : evalᴰ fmt (ee2 ∘ bindEnv {Γ = Γ} {A = A} C.Heap One
                            ∘ ⟨ restrictEnv {Γ = Γ} C.Heap leB , ee1 ⟩) dγ'
                 ≡ (evalᴰ fmt ee1 dγ' >>=T (λ v1 → evalᴰ fmt ee2 (E2' , v1)))
    -- `restrictEnv leB` is stuck on the bound `leB`, so unlike the clause-level
    -- goals this one IS a legitimate `rewrite` target.
    let-reduce rewrite evalᴰ-restrictEnv {Γ = Γ} leB dγ =
      extensionality (λ m →
        cong₂ _,_ (case-trace (proj₁ (evalᴰ fmt ee1 dγ' m))
                    (proj₁ (evalᴰ fmt ee2 (E2' , proj₂ (evalᴰ fmt ee1 dγ' m)) m))) refl)
    e2-eq : ∀ (v1 : ⟦ A ⟧ᴰ)
          → subst T (cohᴰ B) (evalᴰ fmt ee2 (E2' , subst id (sym (cohᴰ A)) v1))
            ≡ SD.⟦ e2 ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} One (restrictᴰ {Γ = Γ} leB dγ) v1)
    e2-eq v1 =
      trans (cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ee2 w))
                  (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ₂ ⟧ᶜ) (cohᴰ A)
                                    (restrictᴰ {Γ = Γ} leB dγ) v1)))
            (extensionality (λ j →
               faithful e2 (bindᴰ {Γ = Γ} {A = A} One (restrictᴰ {Γ = Γ} leB dγ) v1) j))
faithful (let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} {B = B} e1 e2) dγ n =
  trans (cong (λ t → subst T (cohᴰ B) t n)
              (trans let-reduce
                     (cong (λ h → h >>=T (λ v1 → evalᴰ fmt ee2 (E2' , v1)))
                           (ihᴰ∘ leA e1 dγ (λ j → faithful e1 (restrictᴰ {Γ = Γ} leA dγ) j)))))
        (trans (morphapp-transport (cohᴰ A) (cohᴰ B) (λ v1 → evalᴰ fmt ee2 (E2' , v1))
                                   (SD.⟦ e1 ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ)) n)
               (cong (λ cont → (SD.⟦ e1 ⟧ˢ fmt (restrictᴰ {Γ = Γ} leA dγ) >>=T cont) n)
                     (extensionality e2-eq)))
  where
    leA = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))
    leB = ⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ (Ψ₂ +ᵘ (Many *ᵘ Ψ₁)) ⟧ᶜ)) dγ
    E2' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ₂ ⟧ᶜ)) (restrictᴰ {Γ = Γ} leB dγ)
    ee1 = elaborate C.Heap e1 ∘ restrictEnv {Γ = Γ} C.Heap leA
    ee2 = elaborate C.Heap e2
    let-reduce : evalᴰ fmt (ee2 ∘ bindEnv {Γ = Γ} {A = A} C.Heap Many
                            ∘ ⟨ restrictEnv {Γ = Γ} C.Heap leB , ee1 ⟩) dγ'
                 ≡ (evalᴰ fmt ee1 dγ' >>=T (λ v1 → evalᴰ fmt ee2 (E2' , v1)))
    -- `restrictEnv leB` is stuck on the bound `leB`, so unlike the clause-level
    -- goals this one IS a legitimate `rewrite` target.
    let-reduce rewrite evalᴰ-restrictEnv {Γ = Γ} leB dγ =
      extensionality (λ m →
        cong₂ _,_ (case-trace (proj₁ (evalᴰ fmt ee1 dγ' m))
                    (proj₁ (evalᴰ fmt ee2 (E2' , proj₂ (evalᴰ fmt ee1 dγ' m)) m))) refl)
    e2-eq : ∀ (v1 : ⟦ A ⟧ᴰ)
          → subst T (cohᴰ B) (evalᴰ fmt ee2 (E2' , subst id (sym (cohᴰ A)) v1))
            ≡ SD.⟦ e2 ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} Many (restrictᴰ {Γ = Γ} leB dγ) v1)
    e2-eq v1 =
      trans (cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ee2 w))
                  (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ₂ ⟧ᶜ) (cohᴰ A)
                                    (restrictᴰ {Γ = Γ} leB dγ) v1)))
            (extensionality (λ j →
               faithful e2 (bindᴰ {Γ = Γ} {A = A} Many (restrictᴰ {Γ = Γ} leB dγ) v1) j))

-- Effect primitives: ⟦_⟧ˢ denotes them through generic-info/emit-D/semM exactly
-- as elaborate's `SigOp(generic-info name)∘terminal` (non-arrow) / `curry(SigOp∘
-- snd)` (arrow) reduce ([]++X, returnT, eta) ⇒ refl.
-- D143: at an ERASED arrow the SigOp is a VALUE-position reference — the
-- elaborator emits `value-info` (domain `Unit`), not `arrow-info`, and the
-- arrow's `cohᴰ` is the one-equation form.
faithful (sigOp {A = (Dom ⇒[ mk-kind Zero π ] Cod)} name (con-fun bDom cCod)) dγ k =
  cong (λ t → t k)
    (trans (subst-T-returnT (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ Cod))
                            (λ u → evalᴰ fmt (SigOp (value-info name base-Unit cCod)) u))
           (cong returnT
             (trans (subst-arrow₀ᴰ (cohᴰ Cod)
                       (λ u → evalᴰ fmt (SigOp (value-info name base-Unit cCod)) u))
                    (liftFn-SigOp (value-info name base-Unit cCod) base-Unit))))
faithful (sigOp {A = (Dom ⇒[ mk-kind One π ] Cod)} name (con-fun bDom cCod)) dγ k =
  cong (λ t → t k)
    (trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ Dom) (cohᴰ Cod))
                            (λ a → evalᴰ fmt (SigOp (arrow-info (mk-kind One π) name bDom cCod)) a))
           (cong returnT
             (trans (subst-arrowᴰ (cohᴰ Dom) (cohᴰ Cod)
                       (λ a → evalᴰ fmt (SigOp (arrow-info (mk-kind One π) name bDom cCod)) a))
                    (liftFn-SigOp (arrow-info (mk-kind One π) name bDom cCod) bDom))))
faithful (sigOp {A = (Dom ⇒[ mk-kind Many π ] Cod)} name (con-fun bDom cCod)) dγ k =
  cong (λ t → t k)
    (trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ Dom) (cohᴰ Cod))
                            (λ a → evalᴰ fmt (SigOp (arrow-info (mk-kind Many π) name bDom cCod)) a))
           (cong returnT
             (trans (subst-arrowᴰ (cohᴰ Dom) (cohᴰ Cod)
                       (λ a → evalᴰ fmt (SigOp (arrow-info (mk-kind Many π) name bDom cCod)) a))
                    (liftFn-SigOp (arrow-info (mk-kind Many π) name bDom cCod) bDom))))
faithful {Γ = Γ} {A = A} (closure name) dγ k = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} {A} (internal-info (bare name)) dγ k
faithful {Γ = Γ} (poly name PT) dγ k = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} {PT} (internal-info (bare name)) dγ k
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
faithful {Γ = Γ} (sigOp {A = _ * _}    name conc) dγ k = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit conc) dγ k
faithful {Γ = Γ} (sigOp {A = _ + _}    name conc) dγ k = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit conc) dγ k
faithful {Γ = Γ} (sigOp {A = μ-type _} name conc) dγ k = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit conc) dγ k
faithful {Γ = Γ} (sigOp {A = ν-type _} name conc) dγ k = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit conc) dγ k
faithful (case' {Γ = Γ} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr}
                {A = A} {B = B} {C = C} s l r) dγ n =
  trans (cong (λ t → subst T (cohᴰ C) t n)
              (trans case-reduce
                     (cong (λ h → h >>=T branchᴰ)
                           (ihᴰ∘ leS s dγ (λ j → faithful s (restrictᴰ {Γ = Γ} leS dγ) j)))))
        (trans (morphapp-transport (cohᴰ (A + B)) (cohᴰ C) branchᴰ
                                   (SD.⟦ s ⟧ˢ fmt (restrictᴰ {Γ = Γ} leS dγ)) n)
               (cong (λ cont → (SD.⟦ s ⟧ˢ fmt (restrictᴰ {Γ = Γ} leS dγ) >>=T cont) n)
                     (extensionality branch-eq)))
  where
    leAll = ⊑ᵘ-+ʳ Ψs (Ψₗ ⊔ᵘ Ψᵣ)
    leS   = ⊑ᵘ-+ˡ Ψs (Ψₗ ⊔ᵘ Ψᵣ)
    leL   = ⊑ᵘ-⊔ˡ Ψₗ Ψᵣ
    leR   = ⊑ᵘ-⊔ʳ Ψₗ Ψᵣ
    Eall  = restrictᴰ {Γ = Γ} leAll dγ
    Eₗ    = restrictᴰ {Γ = Γ} leL Eall
    Eᵣ    = restrictᴰ {Γ = Γ} leR Eall
    dγ'   = subst id (sym (cohᴰ ⟦ Γ ↾ (Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ)) ⟧ᶜ)) dγ
    Eall' = subst id (sym (cohᴰ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ)) Eall
    es = elaborate C.Heap s ∘ restrictEnv {Γ = Γ} C.Heap leS
    LL = elaborate C.Heap l ∘ bindEnv {Γ = Γ} {A = A} C.Heap qℓ
                            ∘ ⟨ restrictEnv {Γ = Γ} C.Heap leL ∘ fst , snd ⟩
    RR = elaborate C.Heap r ∘ bindEnv {Γ = Γ} {A = B} C.Heap qr
                            ∘ ⟨ restrictEnv {Γ = Γ} C.Heap leR ∘ fst , snd ⟩
    reshape : ⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ
            → ⟦ (⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋ *ᴵ ⌊ A ⌋) +ᴵ (⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋ *ᴵ ⌊ B ⌋) ⟧ᴰᴵ
    reshape v = [ (λ a → inj₁ (Eall' , a)) , (λ b → inj₂ (Eall' , b)) ]′ v
    branchᴰ = λ v → [ (λ a → evalᴰ fmt LL (Eall' , a)) , (λ b → evalᴰ fmt RR (Eall' , b)) ]′ v
    dd-reduce : evalᴰ fmt (distribute {⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋} {⌊ A ⌋} {⌊ B ⌋} C.Heap
                            ∘ ⟨ restrictEnv {Γ = Γ} C.Heap leAll , es ⟩) dγ'
              ≡ (evalᴰ fmt es dγ' >>=T λ v → returnT (reshape v))
    dd-reduce rewrite evalᴰ-restrictEnv {Γ = Γ} leAll dγ = extensionality (λ m →
      cong₂ _,_
        (trans (cong (λ z → (proj₁ (evalᴰ fmt es dγ' m) ++ []) ++ proj₁ (z m))
                     (distribute-reduce {⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋} {⌊ A ⌋} {⌊ B ⌋}
                                        Eall' (proj₂ (evalᴰ fmt es dγ' m))))
               (++-identityʳ (proj₁ (evalᴰ fmt es dγ' m) ++ [])))
        (cong (λ z → proj₂ (z m))
              (distribute-reduce {⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋} {⌊ A ⌋} {⌊ B ⌋}
                                 Eall' (proj₂ (evalᴰ fmt es dγ' m)))))
    case-fuse : ∀ (v : ⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ)
              → evalᴰ fmt (case LL RR) (reshape v) ≡ branchᴰ v
    case-fuse (inj₁ a) = refl
    case-fuse (inj₂ b) = refl
    assoc-fuse : ∀ (mm : T (⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ))
               → ((mm >>=T λ v → returnT (reshape v)) >>=T evalᴰ fmt (case LL RR))
                 ≡ (mm >>=T branchᴰ)
    assoc-fuse mm = extensionality (λ m →
      cong₂ _,_
        (trans (cong (λ z → (proj₁ (mm m) ++ []) ++ proj₁ (z m)) (case-fuse (proj₂ (mm m))))
               (cong (_++ proj₁ (branchᴰ (proj₂ (mm m)) m)) (++-identityʳ (proj₁ (mm m)))))
        (cong (λ z → proj₂ (z m)) (case-fuse (proj₂ (mm m)))))
    case-reduce : evalᴰ fmt (elaborate C.Heap (case' s l r)) dγ'
                ≡ (evalᴰ fmt es dγ' >>=T branchᴰ)
    case-reduce = trans (cong (_>>=T evalᴰ fmt (case LL RR)) dd-reduce)
                        (assoc-fuse (evalᴰ fmt es dγ'))
    LL-lift : ∀ (a : ⟦ A ⟧ᴰ) (j : ℕ)
            → liftFn fmt {⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ * A} {C} LL (Eall , a) j
              ≡ SD.⟦ l ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a) j
    LL-lift a j =
      trans (cong (λ t → t (Eall , a) j)
                  (liftFn-∘ {B = ⟦ (Γ ,ᶜ A) ↾ (qℓ ∷ Ψₗ) ⟧ᶜ} {C = C}
                            {A = ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ * A}
                            (elaborate C.Heap l)
                            (bindEnv {Γ = Γ} {A = A} C.Heap qℓ
                              ∘ ⟨ restrictEnv {Γ = Γ} C.Heap leL ∘ fst , snd ⟩)))
        (trans (cong (λ t → (t >>=T liftFn fmt {⟦ (Γ ,ᶜ A) ↾ (qℓ ∷ Ψₗ) ⟧ᶜ} {C}
                                        (elaborate C.Heap l)) j)
                     (extensionality (branchEnv-denote {Γ = Γ} {Ψ = Ψₗ ⊔ᵘ Ψᵣ} {Ψ' = Ψₗ}
                                                       {A = A} leL qℓ Eall a)))
               (faithful l (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a) j))
    RR-lift : ∀ (b : ⟦ B ⟧ᴰ) (j : ℕ)
            → liftFn fmt {⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ * B} {C} RR (Eall , b) j
              ≡ SD.⟦ r ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b) j
    RR-lift b j =
      trans (cong (λ t → t (Eall , b) j)
                  (liftFn-∘ {B = ⟦ (Γ ,ᶜ B) ↾ (qr ∷ Ψᵣ) ⟧ᶜ} {C = C}
                            {A = ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ * B}
                            (elaborate C.Heap r)
                            (bindEnv {Γ = Γ} {A = B} C.Heap qr
                              ∘ ⟨ restrictEnv {Γ = Γ} C.Heap leR ∘ fst , snd ⟩)))
        (trans (cong (λ t → (t >>=T liftFn fmt {⟦ (Γ ,ᶜ B) ↾ (qr ∷ Ψᵣ) ⟧ᶜ} {C}
                                        (elaborate C.Heap r)) j)
                     (extensionality (branchEnv-denote {Γ = Γ} {Ψ = Ψₗ ⊔ᵘ Ψᵣ} {Ψ' = Ψᵣ}
                                                       {A = B} leR qr Eall b)))
               (faithful r (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b) j))
    branch-eq : ∀ (v : ⟦ A + B ⟧ᴰ)
              → subst T (cohᴰ C) (branchᴰ (subst id (sym (cohᴰ (A + B))) v))
                ≡ [ (λ a → SD.⟦ l ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a))
                  , (λ b → SD.⟦ r ⟧ˢ fmt (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)) ]′ v
    branch-eq (inj₁ a) =
      trans (cong (λ w → subst T (cohᴰ C) (branchᴰ w)) (push⊎₁⁻ (cohᴰ A) (cohᴰ B) a))
            (trans (cong (λ w → subst T (cohᴰ C) (evalᴰ fmt LL w))
                         (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ) (cohᴰ A) Eall a)))
                   (extensionality (LL-lift a)))
    branch-eq (inj₂ b) =
      trans (cong (λ w → subst T (cohᴰ C) (branchᴰ w)) (push⊎₂⁻ (cohᴰ A) (cohᴰ B) b))
            (trans (cong (λ w → subst T (cohᴰ C) (evalᴰ fmt RR w))
                         (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ) (cohᴰ B) Eall b)))
                   (extensionality (RR-lift b)))
faithful {Γ = Γ} (cata wf alg) dγ k = FL.cata-body {Γ = Γ} wf alg (λ j → faithful alg tt j) dγ k
-- ana: dual of cata; reduces to the same closure-bridge via `ana-body`
-- (+ the `ana-ev-bridge` trace lemma).
faithful {Γ = Γ} (ana wf coalg) dγ k = FL.ana-body {Γ = Γ} wf coalg (λ j → faithful coalg tt j) dγ k

------------------------------------------------------------------------
-- D143: faithfulness at the EMPTY context, stated for `elaborateFull`.
--
-- `elaborateFull = elaborate ∘ eraseCtx`, and at `Γ = ∅` the erasure adapter
-- is the identity — but only once `Ψ` is MATCHED (`Usage` is a `data`, so
-- `eraseCtx {∅} m Ψ` is stuck on a variable). Matching it here, inside a
-- lemma, keeps the main reduction path free of the constraint: callers may
-- leave their `Usage 0` abstract.
------------------------------------------------------------------------
faithful∅ : ∀ {Ψ : Usage 0} {A} (e : Expr ∅ Ψ A) (k : ℕ)
          → liftFn fmt {⟦ ∅ ⟧ᶜ} {A} (elaborateFull C.Heap e) tt k
            ≡ SD.⟦ e ⟧ˢ fmt (env0 {Ψ} tt) k
faithful∅ {SrfS.[]} e k = faithful e tt k
