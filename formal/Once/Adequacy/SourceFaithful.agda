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

open import Once.Target.Arch using (TargetNum)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.SourceFaithful (fmt : TargetNum) (ρ : CallEnv) where

open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.Adequacy.CoerceFaithful fmt ρ using (coerce-lift)

open import Data.Unit using (tt)
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-subst-sym; subst-sym-subst)

open import Once.Type using (Type; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type; ⟦_⟧T; mk-kind; pure; eff; Quantity; Zero; One; Many)
open import Once.Functor.Translate using (con-base; con-fun; base-Unit)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; lookup; _,_^_; ⟦_⟧ᶜ; _↾_; zeroUsage; singleUse; ∅;
                                       _⊑ᵘ_; ⊑[]; _⊑∷_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m;
                                       ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; _+ᵘ_; _*ᵘ_;
                                       _⊔ᵘ_; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; _∷_)
open import Once.Surface.Context using () renaming (_,_ to _,ᶜ_)
import Once.Surface.Syntax as SrfS
open import Once.Surface.Properties using (erase-arg-usage)
open import Once.Surface.Elaborate using (elaborate; elaborateFull; projUsed; distribute; compIR; copairIR; forkIR; curryIR; restrictEnv; bindEnv)
open import Once.Denotation.Phase using (lookupᴰUsed; restrictᴰ; bindᴰ; bindᴰ0; env0)
open import Once.Denotation.TraceMonad using (T; ret; call; halt; returnT; _>>=T_; fmapT)
open import Once.Denotation.TraceMonadLaws using (>>=T-assoc; >>=T-identityʳ)
open import Once.IR using (_∘_; ⟨_,_⟩; apply; fst; snd; curry; SigOp; terminal; case; initial) renaming ()
open import Once.Arith.SigOp.Builders using (arrow-info; value-info;
                                             add-info; sub-info; mul-info; div-info; mod-info; fadd-info; fsub-info; fmul-info; fdiv-info; lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.Adequacy.CataErased fmt ρ using (liftFn-SigOp)
open import Once.Adequacy.LiftFnReduce fmt ρ using (liftFn-id; liftFn-fst; liftFn-snd; liftFn-∘; liftFn-pair;
                                                  liftFn-terminal)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; cohᴰ)
open import Once.IRTy using (IRTy; ⌊_⌋) renaming (_*_ to _*ᴵ_; _+_ to _+ᴵ_)
open import Function using (id)
import Once.Semantics.Machine as Val
import Once.Denotation.SourceDenote as SD

-- Plan 0.103 phase 1c: the elaborated IR lowers an unresolved definition
-- reference to an internal call, so the surface meaning it agrees with is the
-- one in the COMPILED program's definitions environment.
σ₀ : SD.DefsSem
σ₀ = SD.internalDefs fmt ρ
import Once.Compile as C
import Once.IR as IR
import Once.Adequacy.FaithfulLemmas fmt ρ as FL
open import Once.Postulates using (extensionality)

open Once.Surface.Syntax.Expr

------------------------------------------------------------------------
-- The elaborator-faithfulness lemma (general — over any context/env, so the
-- induction can recurse into open subterms). Pointwise in the depth `k`.
------------------------------------------------------------------------


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

-- A value-position SigOp (`SigOp info ∘ terminal`): `terminal` discards the
-- environment, so the meaning is the contract's computation at `tt` — the
-- source's `sigOpˢ` (plan 0.105).
sigop-value : ∀ {X : Type} {A : Type} (info : SigOpInfo Unit A) (dγ : ⟦ X ⟧ᴰ)
  → liftFn fmt ρ {X} {A} (SigOp info ∘ terminal) dγ ≡ SD.sigOpˢ fmt σ₀ info tt
sigop-value info dγ = cong (λ h → h tt) (liftFn-SigOp info)

-- THE `Void`-CONTINUATION BIND. A computation into `Void` has no `ret` leaf,
-- so binding it to anything is the same tree whatever the continuation.
void-bind′ : ∀ {Y Z : Set} (m : T ⟦ Void ⟧ᴰ) (f : ⟦ Void ⟧ᴰ → T Y) (g : ⟦ Void ⟧ᴰ → T Z) (p : Y ≡ Z)
           → subst T p (m >>=T f) ≡ (m >>=T g)
void-bind′ (ret ())     f g p
void-bind′ (call o a k) f g refl = cong (call o a) (extensionality λ b → void-bind′ (k b) f g refl)
void-bind′ (halt o a)   f g refl = refl

void-bind : ∀ {A : Type} (p : ⟦ ⌊ A ⌋ ⟧ᴰᴵ ≡ ⟦ A ⟧ᴰ) (m : T ⟦ Void ⟧ᴰ)
              (f : ⟦ Void ⟧ᴰ → T ⟦ ⌊ A ⌋ ⟧ᴰᴵ) (g : ⟦ Void ⟧ᴰ → T ⟦ A ⟧ᴰ)
          → subst T p (m >>=T f) ≡ (m >>=T g)
void-bind p m f g = void-bind′ m f g p

-- plan 0.97: THE BUDGET VIEW. Every statement in this file was written when
-- `T X` WAS `ℕ → List SigOpEvent × X`, so a computation was applied to its
-- budget. `T` is a record now and `atT` is that view of it — `h` reads
-- exactly as `h k` did, and carries the stop flag as its middle component.
-- Nothing is weakened: agreeing at every budget IS equality (`T-ext-at`).
-- Infix, because these statements apply a computation to its budget at the
-- END of a multi-line expression — which is exactly where the old
-- juxtaposition sat. Binds tighter than `≡`, looser than application.



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
  → evalᴰ fmt ρ (distribute {Γ} {A} {B} IR.Heap) (dγ , v)
    ≡ returnT ([ (λ a → inj₁ (dγ , a)) , (λ b → inj₂ (dγ , b)) ]′ v)
distribute-reduce dγ (inj₁ a) = refl
distribute-reduce dγ (inj₂ b) = refl

-- single-subterm projection/injection transports (all `refl`)
fst-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (h : T (AT × BT))
  → subst T pA ((subst T (sym (cong₂ _×_ pA pB)) h) >>=T (λ v → returnT (proj₁ v)))
    ≡ (h >>=T (λ v → returnT (proj₁ v)))
fst-transport refl refl h = refl

snd-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (h : T (AT × BT))
  → subst T pB ((subst T (sym (cong₂ _×_ pA pB)) h) >>=T (λ v → returnT (proj₂ v)))
    ≡ (h >>=T (λ v → returnT (proj₂ v)))
snd-transport refl refl h = refl

inl-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (h : T AT)
  → subst T (cong₂ _⊎_ pA pB) ((subst T (sym pA) h) >>=T (λ v → returnT (inj₁ v)))
    ≡ (h >>=T (λ v → returnT (inj₁ v)))
inl-transport refl refl h = refl

inr-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (h : T BT)
  → subst T (cong₂ _⊎_ pA pB) ((subst T (sym pB) h) >>=T (λ v → returnT (inj₂ v)))
    ≡ (h >>=T (λ v → returnT (inj₂ v)))
inr-transport refl refl h = refl

pair-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT) (ha : T AT) (hb : T BT)
  → subst T (cong₂ _×_ pA pB) ((subst T (sym pA) ha) >>=T (λ va → (subst T (sym pB) hb) >>=T (λ vb → returnT (va , vb))))
    ≡ (ha >>=T (λ va → hb >>=T (λ vb → returnT (va , vb))))
pair-transport refl refl ha hb = refl

morphapp-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT)
    (g : AI → T BI) (h : T AT)
  → subst T pB ((subst T (sym pA) h) >>=T (λ v → g v))
    ≡ (h >>=T (λ v → subst T pB (g (subst id (sym pA) v))))
morphapp-transport refl refl g h = refl

-- `evalᴰ` of the subterm, `liftFn`→`evalᴰ` converted (for the projection cases)
ihᴰ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A) (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
    → (liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (elaborate IR.Heap e) dγ ≡ SD.⟦ e ⟧ˢ fmt σ₀ dγ)
    → evalᴰ fmt ρ (elaborate IR.Heap e) (subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ) ≡ subst T (sym (cohᴰ A)) (SD.⟦ e ⟧ˢ fmt σ₀ dγ)
ihᴰ {A = A} e dγ ih = trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (ih))


-- D143: a variable's RUNTIME environment is a SINGLETON — `var i` has usage
-- `singleUse i One`, so `↾` has already dropped every other slot. `projUsed`
-- and `lookupᴰUsed` then walk the index in lockstep without touching the data,
-- and the `suc` case passes `dγ` straight through (the skipped slot is `Zero`,
-- so `↾` never put it there).
proj-lookup : ∀ {n} {Γ : Ctx n} (i : Fin n) (dγ : ⟦ ⟦ Γ ↾ singleUse i One ⟧ᶜ ⟧ᴰ)
            → liftFn fmt ρ {⟦ Γ ↾ singleUse i One ⟧ᶜ} {lookup Γ i} (projUsed {Γ = Γ} i) dγ
              ≡ returnT (lookupᴰUsed Γ i dγ)
proj-lookup {Γ = Γ , A ^ q} zero    dγ =
    (trans (cong (λ w → subst T (cohᴰ A) (returnT w))
                 (proj₂-subst (cohᴰ ⟦ Γ ↾ zeroUsage ⟧ᶜ) (cohᴰ A) dγ))
      (trans (subst-T-returnT (cohᴰ A) (subst id (sym (cohᴰ A)) (proj₂ dγ)))
             (cong returnT (subst-subst-sym (cohᴰ A)))))
proj-lookup {Γ = Γ , A ^ q} (suc i) dγ = proj-lookup {Γ = Γ} i dγ

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
      (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ × ⟦ A ⟧ᴰ)
    → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ}
             (restrictEnv {Γ = Γ} IR.Heap ule ∘ fst) dγ
      ≡ returnT (restrictᴰ {Γ = Γ} ule (proj₁ dγ))
  restrictEnv-drop {Γ = Γ} {A = A} {Ψ = Ψ} {Ψ' = Ψ'} ule dγ =
    trans (cong (λ t → t dγ)
                (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = ⟦ Γ ↾ Ψ' ⟧ᶜ} {A = ⟦ Γ ↾ Ψ ⟧ᶜ * A}
                          (restrictEnv {Γ = Γ} IR.Heap ule) fst))
      (trans (cong (λ t → (t dγ >>=T liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ}
                                            (restrictEnv {Γ = Γ} IR.Heap ule)))
                   (liftFn-fst {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))
             (liftFn-restrictEnv {Γ = Γ} ule (proj₁ dγ)))

  -- head variable live in BOTH — keep it, narrow the rest.
  restrictEnv-keep :
    ∀ {n} {Γ : Ctx n} {A : Type} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
      (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ × ⟦ A ⟧ᴰ)
    → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ * A}
             (⟨ restrictEnv {Γ = Γ} IR.Heap ule ∘ fst , snd ⟩) dγ
      ≡ returnT (restrictᴰ {Γ = Γ} ule (proj₁ dγ) , proj₂ dγ)
  restrictEnv-keep {Γ = Γ} {A = A} {Ψ = Ψ} {Ψ' = Ψ'} ule dγ =
    trans (cong (λ t → t dγ)
                (liftFn-pair {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A}
                             (restrictEnv {Γ = Γ} IR.Heap ule ∘ fst) snd))
      (trans (cong (λ t → (t >>=T (λ b → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {A} snd dγ
                                            >>=T λ c → returnT (b , c))))
                   ((restrictEnv-drop {Γ = Γ} {A = A} ule dγ)))
             (cong (λ t → (returnT (restrictᴰ {Γ = Γ} ule (proj₁ dγ))
                            >>=T (λ b → t >>=T λ c → returnT (b , c))))
                   (cong (λ u → u dγ) (liftFn-snd {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))))

  liftFn-restrictEnv : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (le : Ψ' ⊑ᵘ Ψ)
                       (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
    → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ} (restrictEnv {Γ = Γ} IR.Heap le) dγ
      ≡ returnT (restrictᴰ {Γ = Γ} le dγ)
  liftFn-restrictEnv {Γ = ∅} ⊑[] dγ = cong (λ t → t dγ) (liftFn-id {⟦ ∅ ⟧ᶜ})
  liftFn-restrictEnv {Γ = Γ , A ^ q} (z≤z ⊑∷ ule) dγ = liftFn-restrictEnv {Γ = Γ} ule dγ
  liftFn-restrictEnv {Γ = Γ , A ^ q} (z≤o ⊑∷ ule) dγ = restrictEnv-drop {Γ = Γ} {A = A} ule dγ
  liftFn-restrictEnv {Γ = Γ , A ^ q} (z≤m ⊑∷ ule) dγ = restrictEnv-drop {Γ = Γ} {A = A} ule dγ
  liftFn-restrictEnv {Γ = Γ , A ^ q} (o≤o ⊑∷ ule) dγ = restrictEnv-keep {Γ = Γ} {A = A} ule dγ
  liftFn-restrictEnv {Γ = Γ , A ^ q} (o≤m ⊑∷ ule) dγ = restrictEnv-keep {Γ = Γ} {A = A} ule dγ
  liftFn-restrictEnv {Γ = Γ , A ^ q} (m≤m ⊑∷ ule) dγ = restrictEnv-keep {Γ = Γ} {A = A} ule dγ


-- THE WORKHORSE: `elaborate e ∘ restrictEnv le` denotes `⟦e⟧ˢ` run on the
-- NARROWED environment. Every compound clause of `faithful` is an instance —
-- the elaborator narrows with an IR morphism, the denotation with `restrictᴰ`,
-- and this is where the two meet.
-- NB `ule`, not `le`: `le` is an `Expr` constructor (the ≤ comparison) brought
-- into scope by `open Expr`, so a pattern variable of that name is read as it.
liftFn-∘-restrictEnv : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} {A} (ule : Ψ' ⊑ᵘ Ψ)
                       (h : IR.IR ⌊ ⟦ Γ ↾ Ψ' ⟧ᶜ ⌋ ⌊ A ⌋) (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
  → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (h ∘ restrictEnv {Γ = Γ} IR.Heap ule) dγ
    ≡ liftFn fmt ρ {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} h (restrictᴰ {Γ = Γ} ule dγ)
liftFn-∘-restrictEnv {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule h dγ =
  trans (cong (λ t → t dγ)
              (liftFn-∘ {B = ⟦ Γ ↾ Ψ' ⟧ᶜ} {C = A} {A = ⟦ Γ ↾ Ψ ⟧ᶜ}
                        h (restrictEnv {Γ = Γ} IR.Heap ule)))
        (cong (λ t → (t >>=T liftFn fmt ρ {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} h))
              ((liftFn-restrictEnv {Γ = Γ} ule dγ)))



-- `ihᴰ` for an arbitrary IR morphism (not just an elaborated `Expr`).
ihᴰgen : ∀ {X A : Type} (h : IR.IR ⌊ X ⌋ ⌊ A ⌋) (sh : T ⟦ A ⟧ᴰ) (dγ : ⟦ X ⟧ᴰ)
       → (liftFn fmt ρ {X} {A} h dγ ≡ sh)
       → evalᴰ fmt ρ h (subst id (sym (cohᴰ X)) dγ) ≡ subst T (sym (cohᴰ A)) sh
ihᴰgen {A = A} h sh dγ ih =
  trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (ih))


-- D143: THE ARITHMETIC NODE. `<op>IR = SigOp <op>-info`, so every two-operand
-- arithmetic clause is `SigOp info ∘ ⟨ ea , eb ⟩`. Stating it as a lemma with
-- `ea`/`eb` as PARAMETERS is what makes `rewrite` work again: inside the lemma
-- the operands are opaque variables, so `evalᴰ fmt ρ ea dγ'` is stuck and stays
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
               (ea : IR.IR ⌊ X ⌋ ⌊ Int ⌋) (eb : IR.IR ⌊ X ⌋ ⌊ Int ⌋)
               (sa : T ⟦ Int ⟧ᴰ) (sb : T ⟦ Int ⟧ᴰ) (dγ : ⟦ X ⟧ᴰ)
             → (liftFn fmt ρ {X} {Int} ea dγ ≡ sa)
             → (liftFn fmt ρ {X} {Int} eb dγ ≡ sb)
             → liftFn fmt ρ {X} {Int} (SigOp info ∘ ⟨ ea , eb ⟩) dγ
               ≡ (sa >>=T (λ va → sb >>=T (λ vb → SD.sigOpˢ fmt σ₀ info (va , vb))))
arith-body-II {X = X} info ea eb sa sb dγ iha ihb
  rewrite ihᴰgen {X} {Int} ea sa dγ iha | ihᴰgen {X} {Int} eb sb dγ ihb =
  trans (reassoc)
        (cong (λ h → (sa >>=T h))
              (extensionality (λ va → (
                 cong (λ g → (sb >>=T g))
                      (extensionality (λ vb → step va vb))))))
  where
    -- The SigOp is applied to the PAIR the two binds build, so moving it
    -- inside them is exactly associativity, twice; the `returnT (va , vb)`
    -- that sat between then collapses by left identity (definitional).
    reassoc :
              ((sa >>=T (λ b → sb >>=T (λ c → returnT (b , c))))
                 >>=T evalᴰ fmt ρ (SigOp info))
              ≡ (sa >>=T (λ va → sb >>=T (λ vb →
                   evalᴰ fmt ρ (SigOp info) (va , vb))))
    reassoc =
      trans (>>=T-assoc sa (λ b → sb >>=T (λ c → returnT (b , c)))
                        (evalᴰ fmt ρ (SigOp info)))
            (cong (λ h → (sa >>=T h))
                  (extensionality (λ va → (
                     >>=T-assoc sb (λ c → returnT (va , c))
                                (evalᴰ fmt ρ (SigOp info))))))
    -- ...and once inside, the SigOp step IS the source's: the operand types are
    -- base types, where `cohᴰ` is `refl`, so the two are one term.
    step : ∀ (va vb : ⟦ Int ⟧ᴰ)
         → evalᴰ fmt ρ (SigOp info) (va , vb) ≡ SD.sigOpˢ fmt σ₀ info (va , vb)
    step va vb = refl

arith-body-FF : ∀ {X : Type} (info : SigOpInfo (Float * Float) Float)
               (ea : IR.IR ⌊ X ⌋ ⌊ Float ⌋) (eb : IR.IR ⌊ X ⌋ ⌊ Float ⌋)
               (sa : T ⟦ Float ⟧ᴰ) (sb : T ⟦ Float ⟧ᴰ) (dγ : ⟦ X ⟧ᴰ)
             → (liftFn fmt ρ {X} {Float} ea dγ ≡ sa)
             → (liftFn fmt ρ {X} {Float} eb dγ ≡ sb)
             → liftFn fmt ρ {X} {Float} (SigOp info ∘ ⟨ ea , eb ⟩) dγ
               ≡ (sa >>=T (λ va → sb >>=T (λ vb → SD.sigOpˢ fmt σ₀ info (va , vb))))
arith-body-FF {X = X} info ea eb sa sb dγ iha ihb
  rewrite ihᴰgen {X} {Float} ea sa dγ iha | ihᴰgen {X} {Float} eb sb dγ ihb =
  trans (reassoc)
        (cong (λ h → (sa >>=T h))
              (extensionality (λ va → (
                 cong (λ g → (sb >>=T g))
                      (extensionality (λ vb → step va vb))))))
  where
    -- The SigOp is applied to the PAIR the two binds build, so moving it
    -- inside them is exactly associativity, twice; the `returnT (va , vb)`
    -- that sat between then collapses by left identity (definitional).
    reassoc :
              ((sa >>=T (λ b → sb >>=T (λ c → returnT (b , c))))
                 >>=T evalᴰ fmt ρ (SigOp info))
              ≡ (sa >>=T (λ va → sb >>=T (λ vb →
                   evalᴰ fmt ρ (SigOp info) (va , vb))))
    reassoc =
      trans (>>=T-assoc sa (λ b → sb >>=T (λ c → returnT (b , c)))
                        (evalᴰ fmt ρ (SigOp info)))
            (cong (λ h → (sa >>=T h))
                  (extensionality (λ va → (
                     >>=T-assoc sb (λ c → returnT (va , c))
                                (evalᴰ fmt ρ (SigOp info))))))
    -- ...and once inside, the SigOp step IS the source's: the operand types are
    -- base types, where `cohᴰ` is `refl`, so the two are one term.
    step : ∀ (va vb : ⟦ Float ⟧ᴰ)
         → evalᴰ fmt ρ (SigOp info) (va , vb) ≡ SD.sigOpˢ fmt σ₀ info (va , vb)
    step va vb = refl

arith-body-IB : ∀ {X : Type} (info : SigOpInfo (Int * Int) (Unit + Unit))
               (ea : IR.IR ⌊ X ⌋ ⌊ Int ⌋) (eb : IR.IR ⌊ X ⌋ ⌊ Int ⌋)
               (sa : T ⟦ Int ⟧ᴰ) (sb : T ⟦ Int ⟧ᴰ) (dγ : ⟦ X ⟧ᴰ)
             → (liftFn fmt ρ {X} {Int} ea dγ ≡ sa)
             → (liftFn fmt ρ {X} {Int} eb dγ ≡ sb)
             → liftFn fmt ρ {X} {(Unit + Unit)} (SigOp info ∘ ⟨ ea , eb ⟩) dγ
               ≡ (sa >>=T (λ va → sb >>=T (λ vb → SD.sigOpˢ fmt σ₀ info (va , vb))))
arith-body-IB {X = X} info ea eb sa sb dγ iha ihb
  rewrite ihᴰgen {X} {Int} ea sa dγ iha | ihᴰgen {X} {Int} eb sb dγ ihb =
  trans (reassoc)
        (cong (λ h → (sa >>=T h))
              (extensionality (λ va → (
                 cong (λ g → (sb >>=T g))
                      (extensionality (λ vb → step va vb))))))
  where
    -- The SigOp is applied to the PAIR the two binds build, so moving it
    -- inside them is exactly associativity, twice; the `returnT (va , vb)`
    -- that sat between then collapses by left identity (definitional).
    reassoc :
              ((sa >>=T (λ b → sb >>=T (λ c → returnT (b , c))))
                 >>=T evalᴰ fmt ρ (SigOp info))
              ≡ (sa >>=T (λ va → sb >>=T (λ vb →
                   evalᴰ fmt ρ (SigOp info) (va , vb))))
    reassoc =
      trans (>>=T-assoc sa (λ b → sb >>=T (λ c → returnT (b , c)))
                        (evalᴰ fmt ρ (SigOp info)))
            (cong (λ h → (sa >>=T h))
                  (extensionality (λ va → (
                     >>=T-assoc sb (λ c → returnT (va , c))
                                (evalᴰ fmt ρ (SigOp info))))))
    -- ...and once inside, the SigOp step IS the source's: the operand types are
    -- base types, where `cohᴰ` is `refl`, so the two are one term.
    step : ∀ (va vb : ⟦ Int ⟧ᴰ)
         → evalᴰ fmt ρ (SigOp info) (va , vb) ≡ SD.sigOpˢ fmt σ₀ info (va , vb)
    step va vb = refl

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
                (h : IR.IR ⌊ ⟦ Γ ↾ Φ' ⟧ᶜ ⌋ ⌊ B ⌋) (dγ : ⟦ ⟦ Γ ↾ Φ ⟧ᶜ ⟧ᴰ)
  → liftFn fmt ρ {⟦ Γ ↾ Φ ⟧ᶜ} {B}
           (subst (λ Φ'' → IR.IR ⌊ ⟦ Γ ↾ Φ'' ⟧ᶜ ⌋ ⌊ B ⌋) (sym eq) h) dγ
    ≡ liftFn fmt ρ {⟦ Γ ↾ Φ' ⟧ᶜ} {B} h
           (subst (λ Φ'' → ⟦ ⟦ Γ ↾ Φ'' ⟧ᶜ ⟧ᴰ) eq dγ)
liftFn-substΦ refl h dγ = refl

-- D143: THE BRANCH ENVIRONMENT, in three steps. `case'` builds a branch's
-- environment as `bindEnv q ∘ ⟨ restrictEnv ule ∘ fst , snd ⟩` (IR) against
-- `bindᴰ q (restrictᴰ ule dγ) a` (semantics). Absorbing the quantity split into
-- `bindEnv-denote` is what keeps `case'` a SINGLE clause rather than nine:
-- `bindEnv qℓ` may stay opaque there, because its denotation is supplied here.

bindEnv-denote : ∀ {n} {Γ : Ctx n} {Ψ' : Usage n} {A} (q : Quantity)
                 (d : ⟦ ⟦ Γ ↾ Ψ' ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ)
  → liftFn fmt ρ {⟦ Γ ↾ Ψ' ⟧ᶜ * A} {⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ}
           (bindEnv {Γ = Γ} {A = A} IR.Heap q) (d , a)
    ≡ returnT (bindᴰ {Γ = Γ} {A = A} q d a)
bindEnv-denote {Γ = Γ} {A = A} Zero d a =
  cong (λ t → t (d , a)) (liftFn-fst {⟦ Γ ↾ _ ⟧ᶜ} {A})
bindEnv-denote {Γ = Γ} {A = A} One  d a =
  cong (λ t → t (d , a)) (liftFn-id {⟦ Γ ↾ _ ⟧ᶜ * A})
bindEnv-denote {Γ = Γ} {A = A} Many d a =
  cong (λ t → t (d , a)) (liftFn-id {⟦ Γ ↾ _ ⟧ᶜ * A})

branch-pair : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} {A} (ule : Ψ' ⊑ᵘ Ψ)
              (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ)
  → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ * A}
           (⟨ restrictEnv {Γ = Γ} IR.Heap ule ∘ fst , snd ⟩) (dγ , a)
    ≡ returnT (restrictᴰ {Γ = Γ} ule dγ , a)
branch-pair {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule dγ a =
  trans (cong (λ t → t (dγ , a))
              (liftFn-pair {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ Γ ↾ Ψ' ⟧ᶜ} {A}
                           (restrictEnv {Γ = Γ} IR.Heap ule ∘ fst) snd))
    (trans (cong (λ t → (t >>=T (λ x → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {A} snd (dγ , a)
                                          >>=T λ y → returnT (x , y))))
                 ((restrictEnv-drop {Γ = Γ} {A = A} ule (dγ , a))))
           (cong (λ t → (returnT (restrictᴰ {Γ = Γ} ule dγ)
                          >>=T (λ x → t >>=T λ y → returnT (x , y))))
                 (cong (λ u → u (dγ , a)) (liftFn-snd {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))))

branchEnv-denote : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} {A} (ule : Ψ' ⊑ᵘ Ψ) (q : Quantity)
                   (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ)
  → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ}
           (bindEnv {Γ = Γ} {A = A} IR.Heap q
             ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap ule ∘ fst , snd ⟩) (dγ , a)
    ≡ returnT (bindᴰ {Γ = Γ} {A = A} q (restrictᴰ {Γ = Γ} ule dγ) a)
branchEnv-denote {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule q dγ a =
  trans (cong (λ t → t (dγ , a))
              (liftFn-∘ {B = ⟦ Γ ↾ Ψ' ⟧ᶜ * A} {C = ⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ}
                        {A = ⟦ Γ ↾ Ψ ⟧ᶜ * A}
                        (bindEnv {Γ = Γ} {A = A} IR.Heap q)
                        (⟨ restrictEnv {Γ = Γ} IR.Heap ule ∘ fst , snd ⟩)))
    (trans (cong (λ t → (t >>=T liftFn fmt ρ {⟦ Γ ↾ Ψ' ⟧ᶜ * A} {⟦ (Γ ,ᶜ A) ↾ (q ∷ Ψ') ⟧ᶜ}
                                    (bindEnv {Γ = Γ} {A = A} IR.Heap q)))
                 ((branch-pair {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule dγ a)))
           (bindEnv-denote {Γ = Γ} {Ψ' = Ψ'} {A = A} q (restrictᴰ {Γ = Γ} ule dγ) a))

-- `liftFn-restrictEnv` in `evalᴰ` form — the shape the `let'`/`case'` clauses
-- need, since they reason under `evalᴰ` rather than `liftFn`.
evalᴰ-restrictEnv : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} (ule : Ψ' ⊑ᵘ Ψ)
                    (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
  → evalᴰ fmt ρ (restrictEnv {Γ = Γ} IR.Heap ule) (subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ)
    ≡ returnT (subst id (sym (cohᴰ ⟦ Γ ↾ Ψ' ⟧ᶜ)) (restrictᴰ {Γ = Γ} ule dγ))
evalᴰ-restrictEnv {Γ = Γ} {Ψ' = Ψ'} ule dγ =
  trans (ihᴰgen {⟦ Γ ↾ _ ⟧ᶜ} {⟦ Γ ↾ Ψ' ⟧ᶜ}
                (restrictEnv {Γ = Γ} IR.Heap ule)
                (returnT (restrictᴰ {Γ = Γ} ule dγ)) dγ
                (liftFn-restrictEnv {Γ = Γ} ule dγ))
        (subst-T-returnT (sym (cohᴰ ⟦ Γ ↾ Ψ' ⟧ᶜ)) (restrictᴰ {Γ = Γ} ule dγ))

-- D143: the narrowed `ihᴰ`. A binary node's operands are elaborated as
-- `elaborate e ∘ restrictEnv le`, so their IH must be taken at the narrowed
-- environment and pushed through the composition — `liftFn-∘-restrictEnv`.
ihᴰ∘ : ∀ {n} {Γ : Ctx n} {Ψ Ψ' : Usage n} {A} (ule : Ψ' ⊑ᵘ Ψ) (e : Expr Γ Ψ' A)
       (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
     → (liftFn fmt ρ {⟦ Γ ↾ Ψ' ⟧ᶜ} {A} (elaborate IR.Heap e)
                       (restrictᴰ {Γ = Γ} ule dγ)
              ≡ SD.⟦ e ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} ule dγ))
     → evalᴰ fmt ρ (elaborate IR.Heap e ∘ restrictEnv {Γ = Γ} IR.Heap ule)
                 (subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ)
       ≡ subst T (sym (cohᴰ A)) (SD.⟦ e ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} ule dγ))
ihᴰ∘ {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A} ule e dγ ih =
  trans (sym (subst-sym-subst (cohᴰ A)))
        (cong (subst T (sym (cohᴰ A)))
              ((
                 trans (liftFn-∘-restrictEnv {Γ = Γ} {Ψ = Ψ} {Ψ' = Ψ'} {A = A}
                                             ule (elaborate IR.Heap e) dγ) (ih))))




-- D179: the `++ []` residuals the three `*-trace` helpers above paper over are
-- intermediate `returnT`s. Under a threaded budget it is no longer enough to
-- fix the TRACE — the residual also sits inside the continuation's budget — so
-- the whole computation is rewritten instead. This is right identity, lifted
-- to a function equality (the `*-trace` helpers are trace-only and cannot).
drop-pure : ∀ {X : Set} (m : T X) → (m >>=T returnT) ≡ m
drop-pure m = >>=T-identityʳ m

-- Double transport-apply-bind: the `cohᴰ`-transported closure computation
-- applied to the `cohᴰ`-back-transported argument computation, transported,
-- equals the untransported apply-bind (all `refl`).
app-transport : ∀ {AI AT BI BT : Set} (pA : AI ≡ AT) (pB : BI ≡ BT)
    (hf : T (AT → T BT)) (hx : T AT)
  → subst T pB ((subst T (sym (cong₂ (λ x y → x → T y) pA pB)) hf)
                  >>=T (λ vf → (subst T (sym pA) hx) >>=T (λ vx → vf vx)))
    ≡ (hf >>=T (λ vf → hx >>=T (λ vx → vf vx)))
app-transport refl refl hf hx = refl

-- D143: the ERASED-arrow analogue. `cohᴰ (A ⇒[Zero] B)` is a ONE-equation
-- `cong` (both sides forget the argument), so `app-transport`'s two-equation
-- form does not apply.
app-transport₀ : ∀ {U BI BT : Set} (pB : BI ≡ BT)
    (hf : T (U → T BT)) (hx : T U)
  → subst T pB ((subst T (sym (cong (λ y → U → T y) pB)) hf)
                  >>=T (λ vf → hx >>=T (λ vx → vf vx)))
    ≡ (hf >>=T (λ vf → hx >>=T (λ vx → vf vx)))
app-transport₀ refl hf hx = refl

app-body-Zero : ∀ {X : Type} {A B} {π}
             (ef : IR.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Zero π ] B ⌋) (ex : IR.IR ⌊ X ⌋ ⌊ Unit ⌋)
             (sf : T ⟦ A ⇒[ mk-kind Zero π ] B ⟧ᴰ) (sx : T ⟦ Unit ⟧ᴰ)
             (dγ : ⟦ X ⟧ᴰ)
           → (liftFn fmt ρ {X} {A ⇒[ mk-kind Zero π ] B} ef dγ ≡ sf)
           → (liftFn fmt ρ {X} {Unit} ex dγ ≡ sx)
           → liftFn fmt ρ {X} {B} (apply ∘ ⟨ ef , ex ⟩) dγ
             ≡ (sf >>=T (λ vf → sx >>=T (λ vx → vf vx)))
app-body-Zero {X = X} {A = A} {B = B} ef ex sf sx dγ ihf ihx =
  trans (cong (λ t → subst T (cohᴰ B) t)
              (trans evalᴰ-app-reduce
                     (cong₂ (λ hf hx → hf >>=T (λ vf → hx >>=T (λ vx → vf vx))) ihf-T ihx-T)))
        (app-transport₀ (cohᴰ B) sf sx)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ρ ef dγ' ≡ subst T (sym (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ B))) sf
    ihf-T = trans (sym (subst-sym-subst (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ B))))
                  (cong (subst T (sym (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ B))))
                        (ihf))
    -- `cohᴰ Unit` is `refl`, so the transport is the identity and the IH lands
    -- directly (the general `subst-sym-subst` route leaves its motive a meta).
    ihx-T : evalᴰ fmt ρ ex dγ' ≡ subst T (sym (cohᴰ Unit)) sx
    ihx-T = ihx
    evalᴰ-app-reduce : evalᴰ fmt ρ (apply ∘ ⟨ ef , ex ⟩) dγ'
                       ≡ (evalᴰ fmt ρ ef dγ' >>=T (λ vf → evalᴰ fmt ρ ex dγ' >>=T (λ vx → vf vx)))
    -- D179: two associativity steps. `_>>=T_` threads the budget, so the
    -- left-nested `(⟨ef,ex⟩ >>=T apply)` and the right-nested form charge the
    -- continuation differently; `>>=T-assoc` is where that is reconciled.
    -- `returnT (b , c) >>=T apply` then collapses definitionally.
    evalᴰ-app-reduce = (
      trans (>>=T-assoc (evalᴰ fmt ρ ef dγ')
                        (λ b → evalᴰ fmt ρ ex dγ' >>=T λ c → returnT (b , c))
                        (evalᴰ fmt ρ (apply {⌊ Unit ⌋} {⌊ B ⌋})))
            (cong (λ h → (evalᴰ fmt ρ ef dγ' >>=T h))
                  (extensionality (λ b → (
                     >>=T-assoc (evalᴰ fmt ρ ex dγ') (λ c → returnT (b , c))
                                (evalᴰ fmt ρ (apply {⌊ Unit ⌋} {⌊ B ⌋})))))))

-- D127: the composition body. `compIR ∘ ⟨ ef , eg ⟩` — the arms run ONCE, at
-- build time (that is the whole point of the closed-morphism form), and
-- building the closure emits nothing, so the outer trace is just the pair's
-- with one trailing `[]`. The per-call trace lives inside the returned
-- function, where the two `apply`s run.
comp-transport : ∀ {AI AT BI BT CI CT : Set}
    (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
    (hf : T (BT → T CT)) (hg : T (AT → T BT))
  → subst T (cong₂ (λ u v → u → T v) pA pC)
      ((subst T (sym (cong₂ (λ u v → u → T v) pB pC)) hf) >>=T (λ vf →
       (subst T (sym (cong₂ (λ u v → u → T v) pA pB)) hg) >>=T (λ vg →
       returnT (λ a → vg a >>=T vf))))
    ≡ (hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ a → vg a >>=T vf))))
comp-transport refl refl refl hf hg = refl

-- D143: generic in the ENVIRONMENT OBJECT `X`. These body lemmas never inspect
-- the context — they relate an IR shape to a denotation shape — so tying them
-- to `⟦ Γ ⟧ᶜ` was incidental. Generalising lets each `faithful` clause
-- instantiate `X := ⟦ Γ ↾ Ψ ⟧ᶜ` and pass its sub-terms already narrowed.
comp-body : ∀ {X : Type} {A B C} {π}
              (ef : IR.IR ⌊ X ⌋ ⌊ B ⇒[ mk-kind Many π ] C ⌋)
              (eg : IR.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many π ] B ⌋)
              (sf : T ⟦ B ⇒[ mk-kind Many π ] C ⟧ᴰ)
              (sg : T ⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ)
              (dγ : ⟦ X ⟧ᴰ)
            → (liftFn fmt ρ {X} {B ⇒[ mk-kind Many π ] C} ef dγ ≡ sf)
            → (liftFn fmt ρ {X} {A ⇒[ mk-kind Many π ] B} eg dγ ≡ sg)
            → liftFn fmt ρ {X} {A ⇒[ mk-kind Many π ] C}
                     (compIR IR.Heap ∘ ⟨ ef , eg ⟩) dγ
              ≡ (sf >>=T (λ vf → sg >>=T (λ vg →
                 returnT (λ a → vg a >>=T vf))))
comp-body {X = X} {A = A} {B = B} {C = C} {π = π} ef eg sf sg dγ ihf ihg =
  trans (cong (λ t → subst T (cohᴰ (A ⇒[ mk-kind Many π ] C)) t)
              (trans evalᴰ-comp-reduce
                     (cong₂ (λ hf hg → hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ a → vg a >>=T vf))))
                            ihf-T ihg-T)))
        (comp-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) sf sg)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ρ ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))) sf
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C)))) (ihf))
    ihg-T : evalᴰ fmt ρ eg dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) sg
    ihg-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (ihg))
    evalᴰ-comp-reduce : evalᴰ fmt ρ (compIR IR.Heap ∘ ⟨ ef , eg ⟩) dγ'
                        ≡ (evalᴰ fmt ρ ef dγ' >>=T (λ vf → evalᴰ fmt ρ eg dγ' >>=T (λ vg →
                           returnT (λ a → vg a >>=T vf))))
    -- D179: the `W ++ []` is an intermediate `returnT`, i.e. RIGHT IDENTITY.
    -- Under threading it is not enough to fix the trace (`comp-trace`): the
    -- residual `++ []` also sits inside the continuation's BUDGET, so the
    -- whole inner computation has to be rewritten, not just its trace.
    -- plan 0.98: TWO ASSOCIATIVITY STEPS, not a patch on the trace. 0.97 could
    -- read each arm's value as a projection and repair the `++ []` residual on
    -- the trace and the flag separately. With `Res` the result is ONE
    -- component that a stopped arm owns outright, so the `returnT (vf , vg)`
    -- sitting between the pair and `compIR` has to be moved by the LAW.
    evalᴰ-comp-reduce = (
      trans (>>=T-assoc (evalᴰ fmt ρ ef dγ')
                        (λ b → evalᴰ fmt ρ eg dγ' >>=T λ c → returnT (b , c))
                        (evalᴰ fmt ρ (compIR {⌊ A ⌋} {⌊ B ⌋} {⌊ C ⌋} IR.Heap)))
            (cong (λ h → (evalᴰ fmt ρ ef dγ' >>=T h))
                  (extensionality (λ vf → (
                     trans (>>=T-assoc (evalᴰ fmt ρ eg dγ') (λ c → returnT (vf , c))
                                       (evalᴰ fmt ρ (compIR {⌊ A ⌋} {⌊ B ⌋} {⌊ C ⌋} IR.Heap)))
                           (cong (λ g → (evalᴰ fmt ρ eg dγ' >>=T g))
                                 (extensionality (λ vg →
                                    -- `compIR` is a `curry`: it BUILDS the
                                    -- composite and emits nothing, and the
                                    -- per-call `apply` is one more assoc step.
                                    cong returnT (extensionality (λ a → (
                                      >>=T-assoc (vg a) (λ c → returnT (vf , c))
                                                 (evalᴰ fmt ρ (apply {⌊ B ⌋} {⌊ C ⌋})))))))))))))

curry-transport : ∀ {AI AT BI BT CI CT : Set}
    (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
    (hf : T ((AT × BT) → T CT))
  → subst T (cong₂ (λ u v → u → T v) pA (cong₂ (λ u v → u → T v) pB pC))
      ((subst T (sym (cong₂ (λ u v → u → T v) (cong₂ _×_ pA pB) pC)) hf) >>=T (λ vf →
       returnT (λ a → returnT (λ b → vf (a , b)))))
    ≡ (hf >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b)))))
curry-transport refl refl refl hf = refl

curry-body : ∀ {X : Type} {A B C}
               (ef : IR.IR ⌊ X ⌋ ⌊ (A * B) ⇒[ mk-kind Many pure ] C ⌋)
               (sf : T ⟦ (A * B) ⇒[ mk-kind Many pure ] C ⟧ᴰ)
               (dγ : ⟦ X ⟧ᴰ)
             → (liftFn fmt ρ {X} {(A * B) ⇒[ mk-kind Many pure ] C} ef dγ ≡ sf)
             → liftFn fmt ρ {X} {A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C)}
                      (curryIR IR.Heap ∘ ef) dγ
               ≡ (sf >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b)))))
curry-body {X = X} {A = A} {B = B} {C = C} ef sf dγ ihf =
  trans (cong (λ t → subst T (cohᴰ (A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C))) t)
              (trans evalᴰ-curry-reduce
                     (cong (λ hf → hf >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b))))) ihf-T)))
        (curry-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (sf))
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ρ ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ (A * B)) (cohᴰ C))) (sf)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ (A * B)) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ (A * B)) (cohᴰ C)))) (ihf))
    evalᴰ-curry-reduce : evalᴰ fmt ρ (curryIR IR.Heap ∘ ef) dγ'
                         ≡ (evalᴰ fmt ρ ef dγ' >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b)))))
    evalᴰ-curry-reduce = refl

fork-transport : ∀ {AI AT BI BT CI CT : Set}
    (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
    (hf : T (AT → T BT)) (hg : T (AT → T CT))
  → subst T (cong₂ (λ u v → u → T v) pA (cong₂ _×_ pB pC))
      ((subst T (sym (cong₂ (λ u v → u → T v) pA pB)) hf) >>=T (λ vf →
       (subst T (sym (cong₂ (λ u v → u → T v) pA pC)) hg) >>=T (λ vg →
       returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c)))))))
    ≡ (hf >>=T (λ vf → hg >>=T (λ vg →
       returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c)))))))
fork-transport refl refl refl hf hg = refl

fork-body : ∀ {X : Type} {A B C}
              (ef : IR.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many pure ] B ⌋)
              (eg : IR.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many pure ] C ⌋)
              (sf : T ⟦ A ⇒[ mk-kind Many pure ] B ⟧ᴰ)
              (sg : T ⟦ A ⇒[ mk-kind Many pure ] C ⟧ᴰ)
              (dγ : ⟦ X ⟧ᴰ)
            → (liftFn fmt ρ {X} {A ⇒[ mk-kind Many pure ] B} ef dγ ≡ sf)
            → (liftFn fmt ρ {X} {A ⇒[ mk-kind Many pure ] C} eg dγ ≡ sg)
            → liftFn fmt ρ {X} {A ⇒[ mk-kind Many pure ] (B * C)}
                     (forkIR IR.Heap ∘ ⟨ ef , eg ⟩) dγ
              ≡ (sf >>=T (λ vf → sg >>=T (λ vg →
                 returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c)))))))
fork-body {X = X} {A = A} {B = B} {C = C} ef eg sf sg dγ ihf ihg =
  trans (cong (λ t → subst T (cohᴰ (A ⇒[ mk-kind Many pure ] (B * C))) t)
              (trans evalᴰ-fork-reduce
                     (cong₂ (λ hf hg → hf >>=T (λ vf → hg >>=T (λ vg →
                              returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c)))))))
                            ihf-T ihg-T)))
        (fork-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (sf) (sg))
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ρ ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) (sf)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (ihf))
    ihg-T : evalᴰ fmt ρ eg dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))) (sg)
    ihg-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C)))) (ihg))
    evalᴰ-fork-reduce : evalᴰ fmt ρ (forkIR IR.Heap ∘ ⟨ ef , eg ⟩) dγ'
                        ≡ (evalᴰ fmt ρ ef dγ' >>=T (λ vf → evalᴰ fmt ρ eg dγ' >>=T (λ vg →
                           returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c)))))))
    -- plan 0.98: the two associativity steps and nothing else — once the
    -- `returnT (vf , vg)` is moved inside both binds, `forkIR`'s `curry` body
    -- IS the denotation's closure, so there is no residual left to repair.
    evalᴰ-fork-reduce = (
      trans (>>=T-assoc (evalᴰ fmt ρ ef dγ')
                        (λ b → evalᴰ fmt ρ eg dγ' >>=T λ c → returnT (b , c))
                        (evalᴰ fmt ρ (forkIR {⌊ A ⌋} {⌊ B ⌋} {⌊ C ⌋} IR.Heap)))
            (cong (λ h → (evalᴰ fmt ρ ef dγ' >>=T h))
                  (extensionality (λ vf → (
                     >>=T-assoc (evalᴰ fmt ρ eg dγ') (λ c → returnT (vf , c))
                                (evalᴰ fmt ρ (forkIR {⌊ A ⌋} {⌊ B ⌋} {⌊ C ⌋} IR.Heap)))))))


copair-transport : ∀ {AI AT BI BT CI CT : Set}
    (pA : AI ≡ AT) (pB : BI ≡ BT) (pC : CI ≡ CT)
    (hf : T (AT → T CT)) (hg : T (BT → T CT))
  → subst T (cong₂ (λ u v → u → T v) (cong₂ _⊎_ pA pB) pC)
      ((subst T (sym (cong₂ (λ u v → u → T v) pA pC)) hf) >>=T (λ vf →
       (subst T (sym (cong₂ (λ u v → u → T v) pB pC)) hg) >>=T (λ vg →
       returnT (λ ab → [ vf , vg ]′ ab))))
    ≡ (hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ ab → [ vf , vg ]′ ab))))
copair-transport refl refl refl hf hg = refl

copair-body : ∀ {X : Type} {A B C} {π}
                (ef : IR.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many π ] C ⌋)
                (eg : IR.IR ⌊ X ⌋ ⌊ B ⇒[ mk-kind Many π ] C ⌋)
                (sf : T ⟦ A ⇒[ mk-kind Many π ] C ⟧ᴰ)
                (sg : T ⟦ B ⇒[ mk-kind Many π ] C ⟧ᴰ)
                (dγ : ⟦ X ⟧ᴰ)
              → (liftFn fmt ρ {X} {A ⇒[ mk-kind Many π ] C} ef dγ ≡ sf)
              → (liftFn fmt ρ {X} {B ⇒[ mk-kind Many π ] C} eg dγ ≡ sg)
              → liftFn fmt ρ {X} {(A + B) ⇒[ mk-kind Many π ] C}
                       (copairIR IR.Heap ∘ ⟨ ef , eg ⟩) dγ
                ≡ (sf >>=T (λ vf → sg >>=T (λ vg →
                   returnT (λ ab → [ vf , vg ]′ ab))))
copair-body {X = X} {A = A} {B = B} {C = C} {π = π} ef eg sf sg dγ ihf ihg =
  trans (cong (λ t → subst T (cohᴰ ((A + B) ⇒[ mk-kind Many π ] C)) t)
              (trans evalᴰ-copair-reduce
                     (cong₂ (λ hf hg → hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ ab → [ vf , vg ]′ ab))))
                            ihf-T ihg-T)))
        (copair-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (sf) (sg))
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ρ ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))) (sf)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C)))) (ihf))
    ihg-T : evalᴰ fmt ρ eg dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))) (sg)
    ihg-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C)))) (ihg))
    evalᴰ-copair-reduce : evalᴰ fmt ρ (copairIR IR.Heap ∘ ⟨ ef , eg ⟩) dγ'
                          ≡ (evalᴰ fmt ρ ef dγ' >>=T (λ vf → evalᴰ fmt ρ eg dγ' >>=T (λ vg →
                             returnT (λ ab → [ vf , vg ]′ ab))))
    -- The elaborated side goes through `distribIR` and then `case`, which is
    -- STUCK on an abstract sum value — so the per-call step case-splits on the
    -- argument. That is the only structural difference from the other three.
    -- plan 0.98: the two associativity steps, then the branch split. 0.97
    -- could state the split on the VALUE alone (`valueT … m ab`) because the
    -- value was a projection that always existed; with `Res` there is no such
    -- projection, so the split happens where the arms are BOUND — under the
    -- `returnT` `copairIR`'s `curry` builds.
    evalᴰ-copair-reduce = (
      trans (>>=T-assoc (evalᴰ fmt ρ ef dγ')
                        (λ b → evalᴰ fmt ρ eg dγ' >>=T λ c → returnT (b , c))
                        (evalᴰ fmt ρ (copairIR {⌊ A ⌋} {⌊ B ⌋} {⌊ C ⌋} IR.Heap)))
            (cong (λ h → (evalᴰ fmt ρ ef dγ' >>=T h))
                  (extensionality (λ vf → (
                     trans (>>=T-assoc (evalᴰ fmt ρ eg dγ') (λ c → returnT (vf , c))
                                       (evalᴰ fmt ρ (copairIR {⌊ A ⌋} {⌊ B ⌋} {⌊ C ⌋} IR.Heap)))
                           (cong (λ g → (evalᴰ fmt ρ eg dγ' >>=T g))
                                 (extensionality (λ vg →
                                    -- The branch split, written as a
                                    -- pattern-matching lambda so the IR
                                    -- objects stay solved by the goal rather
                                    -- than restated (and left as metas) in a
                                    -- `where`-signature.
                                    cong returnT (extensionality
                                      (λ { (inj₁ x) → refl
                                         ; (inj₂ y) → refl }))))))))))


-- D143: `apply` needs `⌊A ⇒[k] B⌋ ≡ ⌊A⌋ ⇛ ⌊B⌋`, so the arrow must be NON-erased
-- — the quantity cannot stay a variable. `One` and `Many` share the proof; the
-- `Zero` case elaborates differently (`⟨ ef , terminal ⟩`) and is handled in
-- `faithful` directly. Generic in the environment object `X`.

app-body : ∀ {X : Type} {A B} {π}
             (ef : IR.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind Many π ] B ⌋) (ex : IR.IR ⌊ X ⌋ ⌊ A ⌋)
             (sf : T ⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ) (sx : T ⟦ A ⟧ᴰ)
             (dγ : ⟦ X ⟧ᴰ)
           → (liftFn fmt ρ {X} {A ⇒[ mk-kind Many π ] B} ef dγ ≡ sf)
           → (liftFn fmt ρ {X} {A} ex dγ ≡ sx)
           → liftFn fmt ρ {X} {B} (apply ∘ ⟨ ef , ex ⟩) dγ
             ≡ (sf >>=T (λ vf → sx >>=T (λ vx → vf vx)))
app-body {X = X} {A = A} {B = B} ef ex sf sx dγ ihf ihx =
  trans (cong (λ t → subst T (cohᴰ B) t)
              (trans evalᴰ-app-reduce
                     (cong₂ (λ hf hx → hf >>=T (λ vf → hx >>=T (λ vx → vf vx))) ihf-T ihx-T)))
        (app-transport (cohᴰ A) (cohᴰ B) sf sx)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ρ ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) sf
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (ihf))
    ihx-T : evalᴰ fmt ρ ex dγ' ≡ subst T (sym (cohᴰ A)) sx
    ihx-T = trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (ihx))
    evalᴰ-app-reduce : evalᴰ fmt ρ (apply ∘ ⟨ ef , ex ⟩) dγ'
                       ≡ (evalᴰ fmt ρ ef dγ' >>=T (λ vf → evalᴰ fmt ρ ex dγ' >>=T (λ vx → vf vx)))
    -- D179: two associativity steps. `_>>=T_` threads the budget, so the
    -- left-nested `(⟨ef,ex⟩ >>=T apply)` and the right-nested form charge the
    -- continuation differently; `>>=T-assoc` is where that is reconciled.
    -- `returnT (b , c) >>=T apply` then collapses definitionally.
    evalᴰ-app-reduce = (
      trans (>>=T-assoc (evalᴰ fmt ρ ef dγ')
                        (λ b → evalᴰ fmt ρ ex dγ' >>=T λ c → returnT (b , c))
                        (evalᴰ fmt ρ (apply {⌊ A ⌋} {⌊ B ⌋})))
            (cong (λ h → (evalᴰ fmt ρ ef dγ' >>=T h))
                  (extensionality (λ b → (
                     >>=T-assoc (evalᴰ fmt ρ ex dγ') (λ c → returnT (b , c))
                                (evalᴰ fmt ρ (apply {⌊ A ⌋} {⌊ B ⌋})))))))

app-body-One : ∀ {X : Type} {A B} {π}
             (ef : IR.IR ⌊ X ⌋ ⌊ A ⇒[ mk-kind One π ] B ⌋) (ex : IR.IR ⌊ X ⌋ ⌊ A ⌋)
             (sf : T ⟦ A ⇒[ mk-kind One π ] B ⟧ᴰ) (sx : T ⟦ A ⟧ᴰ)
             (dγ : ⟦ X ⟧ᴰ)
           → (liftFn fmt ρ {X} {A ⇒[ mk-kind One π ] B} ef dγ ≡ sf)
           → (liftFn fmt ρ {X} {A} ex dγ ≡ sx)
           → liftFn fmt ρ {X} {B} (apply ∘ ⟨ ef , ex ⟩) dγ
             ≡ (sf >>=T (λ vf → sx >>=T (λ vx → vf vx)))
app-body-One {X = X} {A = A} {B = B} ef ex sf sx dγ ihf ihx =
  trans (cong (λ t → subst T (cohᴰ B) t)
              (trans evalᴰ-app-reduce
                     (cong₂ (λ hf hx → hf >>=T (λ vf → hx >>=T (λ vx → vf vx))) ihf-T ihx-T)))
        (app-transport (cohᴰ A) (cohᴰ B) sf sx)
  where
    dγ' = subst id (sym (cohᴰ X)) dγ
    ihf-T : evalᴰ fmt ρ ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) sf
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (ihf))
    ihx-T : evalᴰ fmt ρ ex dγ' ≡ subst T (sym (cohᴰ A)) sx
    ihx-T = trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (ihx))
    evalᴰ-app-reduce : evalᴰ fmt ρ (apply ∘ ⟨ ef , ex ⟩) dγ'
                       ≡ (evalᴰ fmt ρ ef dγ' >>=T (λ vf → evalᴰ fmt ρ ex dγ' >>=T (λ vx → vf vx)))
    -- D179: two associativity steps. `_>>=T_` threads the budget, so the
    -- left-nested `(⟨ef,ex⟩ >>=T apply)` and the right-nested form charge the
    -- continuation differently; `>>=T-assoc` is where that is reconciled.
    -- `returnT (b , c) >>=T apply` then collapses definitionally.
    evalᴰ-app-reduce = (
      trans (>>=T-assoc (evalᴰ fmt ρ ef dγ')
                        (λ b → evalᴰ fmt ρ ex dγ' >>=T λ c → returnT (b , c))
                        (evalᴰ fmt ρ (apply {⌊ A ⌋} {⌊ B ⌋})))
            (cong (λ h → (evalᴰ fmt ρ ef dγ' >>=T h))
                  (extensionality (λ b → (
                     >>=T-assoc (evalᴰ fmt ρ ex dγ') (λ c → returnT (b , c))
                                (evalᴰ fmt ρ (apply {⌊ A ⌋} {⌊ B ⌋})))))))


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
    (dγ : ⟦ ⟦ Γ ↾ Ψ ⟧ᶜ ⟧ᴰ)
  → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A} (elaborate IR.Heap e) dγ ≡ SD.⟦ e ⟧ˢ fmt σ₀ dγ
-- `unit` ↦ `terminal`; both sides reduce to `returnT tt` ⇒ refl.
faithful (var {Γ = Γ} i) dγ = proj-lookup {Γ = Γ} i dγ
-- D226: the compiled conversion means `⟦ p ⟧<:` mapped over the result
-- (`coerce-lift`), and `fmapT` leaves the trace alone, so at every budget this
-- is the operand's agreement with the result half mapped.
faithful (coerce {Γ = Γ} {Ψ = Ψ} p e) dγ =
  trans (coerce-lift {⟦ Γ ↾ Ψ ⟧ᶜ} p (elaborate IR.Heap e) dγ)
        (cong (fmapT ⟦ p ⟧<:) (faithful e dγ))
-- lam ↦ curry. D143: SIX clauses — the arrow's quantity `q` decides whether the
-- meaning takes an argument, the binder's body-usage `q'` whether it enters the
-- body's environment. At `q' = Zero` the elaborated body is `ee ∘ fst` (the
-- bound value is dropped) and the denotation runs on `bindᴰ0 dγ`, so the two
-- agree only after `liftFn-∘`/`liftFn-fst` discard it — that is `drop` below.
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} Zero _ e) dγ =
  trans red
        (cong returnT (extensionality (λ u → (
          trans (drop u) (faithful e (bindᴰ0 {Γ = Γ} {A = A} dγ))))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate IR.Heap e
    eeF : IR.IR (⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ *ᴵ ⌊ Unit ⌋) ⌊ B ⌋
    eeF = ee ∘ fst
    drop : ∀ u → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * Unit} {B} eeF (dγ , u)
                 ≡ liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee dγ
    drop u = trans (cong (λ t → t (dγ , u))
                           (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = B} {A = ⟦ Γ ↾ Ψ ⟧ᶜ * Unit} ee fst))
                     (cong (λ t → (t (dγ , u) >>=T liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee))
                           (liftFn-fst {⟦ Γ ↾ Ψ ⟧ᶜ} {Unit}))
    red : liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Zero pure ] B} (curry eeF) dγ
          ≡ returnT (λ u → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * Unit} {B} eeF (dγ , u))
    red = trans (subst-T-returnT (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ B))
                                 (λ u → evalᴰ fmt ρ eeF (dγ' , u)))
            (cong returnT
              (trans (subst-arrow₀ᴰ (cohᴰ B) (λ u → evalᴰ fmt ρ eeF (dγ' , u)))
                     (extensionality (λ u →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ρ eeF w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ Unit) dγ u))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} One _ e) dγ =
  trans red
        (cong returnT (extensionality (λ a → (
          trans (drop a) (faithful e (bindᴰ0 {Γ = Γ} {A = A} dγ))))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate IR.Heap e
    eeF : IR.IR (⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ *ᴵ ⌊ A ⌋) ⌊ B ⌋
    eeF = ee ∘ fst
    drop : ∀ a → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} eeF (dγ , a)
                 ≡ liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee dγ
    drop a = trans (cong (λ t → t (dγ , a))
                           (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = B} {A = ⟦ Γ ↾ Ψ ⟧ᶜ * A} ee fst))
                     (cong (λ t → (t (dγ , a) >>=T liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee))
                           (liftFn-fst {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))
    red : liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind One pure ] B} (curry eeF) dγ
          ≡ returnT (λ a → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} eeF (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt ρ eeF (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ρ eeF (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ρ eeF w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Zero} {A = A} {B = B} Many _ e) dγ =
  trans red
        (cong returnT (extensionality (λ a → (
          trans (drop a) (faithful e (bindᴰ0 {Γ = Γ} {A = A} dγ))))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate IR.Heap e
    eeF : IR.IR (⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ *ᴵ ⌊ A ⌋) ⌊ B ⌋
    eeF = ee ∘ fst
    drop : ∀ a → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} eeF (dγ , a)
                 ≡ liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee dγ
    drop a = trans (cong (λ t → t (dγ , a))
                           (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = B} {A = ⟦ Γ ↾ Ψ ⟧ᶜ * A} ee fst))
                     (cong (λ t → (t (dγ , a) >>=T liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {B} ee))
                           (liftFn-fst {⟦ Γ ↾ Ψ ⟧ᶜ} {A}))
    red : liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] B} (curry eeF) dγ
          ≡ returnT (λ a → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} eeF (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt ρ eeF (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ρ eeF (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ρ eeF w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = One} {A = A} {B = B} One _ e) dγ =
  trans red
        (cong returnT (extensionality (λ a → (
          faithful e (bindᴰ {Γ = Γ} {A = A} One dγ a)))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate IR.Heap e
    red : liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind One pure ] B} (curry ee) dγ
          ≡ returnT (λ a → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} ee (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt ρ ee (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ρ ee (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ρ ee w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = One} {A = A} {B = B} Many _ e) dγ =
  trans red
        (cong returnT (extensionality (λ a → (
          faithful e (bindᴰ {Γ = Γ} {A = A} One dγ a)))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate IR.Heap e
    red : liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] B} (curry ee) dγ
          ≡ returnT (λ a → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} ee (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt ρ ee (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ρ ee (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ρ ee w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ) (cohᴰ A) dγ a))))))
faithful (lam {Γ = Γ} {Ψ = Ψ} {q' = Many} {A = A} {B = B} Many _ e) dγ =
  trans red
        (cong returnT (extensionality (λ a → (
          faithful e (bindᴰ {Γ = Γ} {A = A} Many dγ a)))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ ⟧ᶜ)) dγ
    ee = elaborate IR.Heap e
    red : liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] B} (curry ee) dγ
          ≡ returnT (λ a → liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ * A} {B} ee (dγ , a))
    red = trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B))
                                 (λ a → evalᴰ fmt ρ ee (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ρ ee (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ρ ee w))
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
faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = Zero} f x) dγ =
  trans (liftFn-substΦ {Γ = Γ} {Φ = Ψ₁ +ᵘ (Zero *ᵘ Ψ₂)} {Φ' = Ψ₁} {B = B}
                       (erase-arg-usage Ψ₁ Ψ₂)
                       (apply ∘ ⟨ elaborate IR.Heap f , terminal ⟩) dγ)
        (trans (cong (λ d → liftFn fmt ρ {⟦ Γ ↾ Ψ₁ ⟧ᶜ} {B}
                              (apply ∘ ⟨ elaborate IR.Heap f , terminal ⟩) d)
                     (sym (restrictᴰ-subst {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂))
                                           (erase-arg-usage Ψ₁ Ψ₂) dγ)))
               (app-body-Zero {⟦ Γ ↾ Ψ₁ ⟧ᶜ} {A} {B} {pure}
                  (elaborate IR.Heap f) terminal
                  (SD.⟦ f ⟧ˢ fmt σ₀ Ez) (returnT tt) Ez
                  (faithful f Ez)
                  (cong (λ t → t Ez) (liftFn-terminal {⟦ Γ ↾ Ψ₁ ⟧ᶜ}))))
  where
    Ez = restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) dγ
faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = One} f x) dγ =
  app-body-One {⟦ Γ ↾ (Ψ₁ +ᵘ (One *ᵘ Ψ₂)) ⟧ᶜ} {A} {B} {pure}
           (elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF)
           (elaborate IR.Heap x ∘ restrictEnv {Γ = Γ} IR.Heap leX)
           (SD.⟦ f ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leF dγ))
           (SD.⟦ x ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leX dγ))
           dγ
           (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind One pure ] B}
                                              leF (elaborate IR.Heap f) dγ)
                        (faithful f (restrictᴰ {Γ = Γ} leF dγ)))
           (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A} leX (elaborate IR.Heap x) dγ)
                        (faithful x (restrictᴰ {Γ = Γ} leX dγ)))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)
    leX = ⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))
faithful (app {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {q = Many} f x) dγ =
  app-body {⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ} {A} {B} {pure}
           (elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF)
           (elaborate IR.Heap x ∘ restrictEnv {Γ = Γ} IR.Heap leX)
           (SD.⟦ f ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leF dγ))
           (SD.⟦ x ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leX dγ))
           dγ
           (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many pure ] B}
                                              leF (elaborate IR.Heap f) dγ)
                        (faithful f (restrictᴰ {Γ = Γ} leF dγ)))
           (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A} leX (elaborate IR.Heap x) dγ)
                        (faithful x (restrictᴰ {Γ = Γ} leX dγ)))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)
    leX = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))
-- effApp: a SUSPENDED closure whose body is the (effectful) application of f to x.
-- Both sides are `returnT <closure>` (the Unit-thunk); the closure body is exactly
-- app-body, lifted through extensionality (over the discarded Unit arg + depth).
faithful (effApp {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} f x) dγ =
  trans liftFn-curry-reduce-effApp
        (cong returnT (extensionality (λ _ → (
          app-body {⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ} {A} {B} {eff}
                   (elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF)
                   (elaborate IR.Heap x ∘ restrictEnv {Γ = Γ} IR.Heap leX)
                   (SD.⟦ f ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leF dγ))
                   (SD.⟦ x ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leX dγ))
                   dγ
                   (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many eff ] B}
                                                     leF (elaborate IR.Heap f) dγ)
                                (faithful f (restrictᴰ {Γ = Γ} leF dγ)))
                   (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A} leX (elaborate IR.Heap x) dγ)
                                (faithful x (restrictᴰ {Γ = Γ} leX dγ)))))))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)
    leX = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ)) dγ
    inner = apply ∘ ⟨ elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF
                    , elaborate IR.Heap x ∘ restrictEnv {Γ = Γ} IR.Heap leX ⟩
    body = inner ∘ fst
    liftFn-curry-reduce-effApp :
      liftFn fmt ρ {⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ} {Unit ⇒[ mk-kind Many eff ] B} (curry body) dγ
      ≡ returnT (λ _ → liftFn fmt ρ {⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ} {B} inner dγ)
    liftFn-curry-reduce-effApp =
      trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ Unit) (cohᴰ B))
                             (λ u → evalᴰ fmt ρ body (dγ' , u)))
            (cong returnT (subst-arrowᴰ (cohᴰ Unit) (cohᴰ B) (λ u → evalᴰ fmt ρ body (dγ' , u))))
-- `absurd v` — the subterm has type `Void`, so its tree has no `ret` leaf:
-- both sides are that tree, bound to a continuation that never runs
-- (`void-bind`, plan 0.105).
faithful (absurd {Γ = Γ} {Ψ = Ψ} {A = A} v) dγ =
  trans (cong (λ m → subst T (cohᴰ A) (m >>=T evalᴰ fmt ρ (initial {⌊ A ⌋})))
              (ihᴰ v dγ (faithful v dγ)))
        (void-bind {A} (cohᴰ A) (SD.⟦ v ⟧ˢ fmt σ₀ dγ) (evalᴰ fmt ρ (initial {⌊ A ⌋})) (λ x → ⊥-elim x))
faithful unit    dγ = refl
faithful (int n) dγ = refl   -- both sides are `fromℤ (int-bits fmt) n` (the `absℤ` this
                               -- comment used to describe is gone; D054/D115)
faithful (float d) dγ = refl   -- both sides are `round (float-format fmt) d` (K1)
-- Single-subterm projections/injections: `elaborate (op e) = <prim> ∘ elaborate e`
-- and `⟦ op e ⟧ˢ = ⟦e⟧ˢ >>=T (λv → returnT (<prim> v))`; `_>>=T_` sees the same
-- depth on both sides, so the trace+value at `n` is a function of the SUBTERM's
-- (trace,value) at `n` — one `cong` over the IH (`faithful e`).
-- D127: `comp'` delegates to `comp-body`, the same way `app` delegates to
-- `app-body`.
faithful (comp' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} f g) dγ =
  comp-body {⟦ Γ ↾ (Ψ₁ +ᵘ (Many *ᵘ Ψ₂)) ⟧ᶜ} {A} {B} {C} {π}
            (elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF)
            (elaborate IR.Heap g ∘ restrictEnv {Γ = Γ} IR.Heap leG)
            (SD.⟦ f ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leF dγ))
            (SD.⟦ g ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leG dγ))
            dγ
            (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = B ⇒[ mk-kind Many π ] C} leF (elaborate IR.Heap f) dγ)
                         (faithful f (restrictᴰ {Γ = Γ} leF dγ)))
            (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many π ] B} leG (elaborate IR.Heap g) dγ)
                         (faithful g (restrictᴰ {Γ = Γ} leG dγ)))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)
    leG = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))
faithful (curry' {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} {C = C} f) dγ =
  curry-body {⟦ Γ ↾ Ψ ⟧ᶜ} {A} {B} {C}
             (elaborate IR.Heap f) (SD.⟦ f ⟧ˢ fmt σ₀ dγ) dγ (faithful f dγ)
faithful (fork' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} f g) dγ =
  fork-body {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {A} {B} {C}
            (elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF)
            (elaborate IR.Heap g ∘ restrictEnv {Γ = Γ} IR.Heap leG)
            (SD.⟦ f ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leF dγ))
            (SD.⟦ g ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leG dγ))
            dγ
            (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many pure ] B} leF (elaborate IR.Heap f) dγ)
                         (faithful f (restrictᴰ {Γ = Γ} leF dγ)))
            (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many pure ] C} leG (elaborate IR.Heap g) dγ)
                         (faithful g (restrictᴰ {Γ = Γ} leG dγ)))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leG = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (copair' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} {C = C} {π = π} f g) dγ =
  copair-body {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} {A} {B} {C} {π}
            (elaborate IR.Heap f ∘ restrictEnv {Γ = Γ} IR.Heap leF)
            (elaborate IR.Heap g ∘ restrictEnv {Γ = Γ} IR.Heap leG)
            (SD.⟦ f ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leF dγ))
            (SD.⟦ g ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leG dγ))
            dγ
            (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = A ⇒[ mk-kind Many π ] C} leF (elaborate IR.Heap f) dγ)
                         (faithful f (restrictᴰ {Γ = Γ} leF dγ)))
            (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = B ⇒[ mk-kind Many π ] C} leG (elaborate IR.Heap g) dγ)
                         (faithful g (restrictᴰ {Γ = Γ} leG dγ)))
  where
    leF = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leG = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fst' {A = A} {B = B} e) dγ =
  trans (cong (λ t → subst T (cohᴰ A) t) (cong (λ h → h >>=T (λ v → returnT (proj₁ v))) (ihᴰ e dγ (faithful e dγ))))
        (fst-transport (cohᴰ A) (cohᴰ B) (SD.⟦ e ⟧ˢ fmt σ₀ dγ))
faithful (snd' {A = A} {B = B} e) dγ =
  trans (cong (λ t → subst T (cohᴰ B) t) (cong (λ h → h >>=T (λ v → returnT (proj₂ v))) (ihᴰ e dγ (faithful e dγ))))
        (snd-transport (cohᴰ A) (cohᴰ B) (SD.⟦ e ⟧ˢ fmt σ₀ dγ))
faithful (inl' {A = A} {B = B} e) dγ =
  trans (cong (λ t → subst T (cohᴰ (A + B)) t) (cong (λ h → h >>=T (λ v → returnT (inj₁ v))) (ihᴰ e dγ (faithful e dγ))))
        (inl-transport (cohᴰ A) (cohᴰ B) (SD.⟦ e ⟧ˢ fmt σ₀ dγ))
faithful (inr' {A = A} {B = B} e) dγ =
  trans (cong (λ t → subst T (cohᴰ (A + B)) t) (cong (λ h → h >>=T (λ v → returnT (inj₂ v))) (ihᴰ e dγ (faithful e dγ))))
        (inr-transport (cohᴰ A) (cohᴰ B) (SD.⟦ e ⟧ˢ fmt σ₀ dγ))
-- Two-subterm arith (elaborate = `<op>IR ∘ ⟨ea,eb⟩`, ⟦_⟧ˢ via the same `semM`):
-- rewrite both IHs; the only residual is the IR `SigOp`-bind's extra empty trace
-- (`(W ++ []) ≡ W`, ++-identityʳ); the value is identical (same `semM`).
faithful (add {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} add-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (sub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} sub-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (mul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} mul-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
faithful (fadd {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-FF {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} fadd-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fsub {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-FF {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} fsub-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fmul {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-FF {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} fmul-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (fdiv {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-FF {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} fdiv-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Float} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (i2f a)    dγ rewrite ihᴰ a dγ (faithful a dγ) = refl   -- unary: no `++` to neutralise, cf. `neg`
faithful (div {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} div-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (mod' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-II {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} mod-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (lt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} lt-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (le {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} le-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (gt {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} gt-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (ge {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} ge-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (eq {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} eq-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
faithful (ne {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) dγ =
  arith-body-IB {⟦ Γ ↾ (Ψ₁ +ᵘ Ψ₂) ⟧ᶜ} ne-info
    (elaborate IR.Heap a ∘ restrictEnv {Γ = Γ} IR.Heap leA)
    (elaborate IR.Heap b ∘ restrictEnv {Γ = Γ} IR.Heap leB)
    (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
    (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ))
    dγ
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leA (elaborate IR.Heap a) dγ)
                 (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
    (trans (liftFn-∘-restrictEnv {Γ = Γ} {A = Int} leB (elaborate IR.Heap b) dγ)
                 (faithful b (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
-- neg: single subterm; IR `negIR ∘ ee` and ⟦_⟧ˢ share the bind+cont, so refl post-IH.
faithful (neg e)    dγ rewrite ihᴰ e dγ (faithful e dγ) = refl
-- pair: `elaborate = ⟨ea,eb⟩`, same bind structure as ⟦_⟧ˢ (ends in returnT(va,vb),
-- no trailing SigOp bind) ⇒ refl post both IHs.
faithful (pair {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {A = A} {B = B} a b) dγ =
  trans (cong (λ t → subst T (cohᴰ (A * B)) t)
              (cong₂ (λ ha hb → ha >>=T (λ va → hb >>=T (λ vb → returnT (va , vb))))
                     (ihᴰ∘ leA a dγ (faithful a (restrictᴰ {Γ = Γ} leA dγ)))
                     (ihᴰ∘ leB b dγ (faithful b (restrictᴰ {Γ = Γ} leB dγ)))))
        (pair-transport (cohᴰ A) (cohᴰ B)
                        (SD.⟦ a ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ))
                        (SD.⟦ b ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leB dγ)))
  where
    leA = ⊑ᵘ-+ˡ Ψ₁ Ψ₂
    leB = ⊑ᵘ-+ʳ Ψ₁ Ψ₂
-- arr': `elaborate = arr ∘ ef` adds one `returnT` bind (an extra ++[]); the kind
-- change is erased by ⟦_⟧ᴰ, value unchanged ⇒ ++-identityʳ.
-- IR embedding: ⟦_⟧ˢ denotes these AS `evalᴰ morph`; elaborate's
-- `curry (morph ∘ snd)` / `morph ∘ ex` reduce to the same (returnT/[]++X + eta).
faithful (lift-morphism {A = A} {B = B} morph) dγ =
    (trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)) (λ a → evalᴰ fmt ρ morph a))
           (cong returnT (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ρ morph a))))
faithful (morph-app {Γ = Γ} {Ψ = Ψ} {A = A} {B = B} morph e) dγ =
  trans (cong (λ t → subst T (cohᴰ B) t)
              (cong (λ h → h >>=T (λ v → evalᴰ fmt ρ morph v))
                    (ihᴰ∘ leM e dγ (faithful e (restrictᴰ {Γ = Γ} leM dγ)))))
        (morphapp-transport (cohᴰ A) (cohᴰ B) (λ v → evalᴰ fmt ρ morph v)
                            (SD.⟦ e ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leM dγ)))
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
faithful (let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} {B = B} e1 e2) dγ =
  trans (liftFn-substΦ {Γ = Γ} {Φ = Ψ₂ +ᵘ (Zero *ᵘ Ψ₁)} {Φ' = Ψ₂} {B = B}
                       (erase-arg-usage Ψ₂ Ψ₁) (elaborate IR.Heap e2) dγ)
        (trans (cong (λ d → liftFn fmt ρ {⟦ Γ ↾ Ψ₂ ⟧ᶜ} {B} (elaborate IR.Heap e2) d)
                     (sym (restrictᴰ-subst {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁))
                                           (erase-arg-usage Ψ₂ Ψ₁) dγ)))
               (faithful e2 (bindᴰ0 {Γ = Γ} {A = A}
                              (restrictᴰ {Γ = Γ} (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) dγ))))
faithful (let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {A = A} {B = B} e1 e2) dγ =
  trans (cong (λ t → subst T (cohᴰ B) t)
              (trans let-reduce
                     (cong (λ h → h >>=T (λ v1 → evalᴰ fmt ρ ee2 (E2' , v1)))
                           (ihᴰ∘ leA e1 dγ (faithful e1 (restrictᴰ {Γ = Γ} leA dγ))))))
        (trans (morphapp-transport (cohᴰ A) (cohᴰ B) (λ v1 → evalᴰ fmt ρ ee2 (E2' , v1))
                                   (SD.⟦ e1 ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ)))
               (cong (λ cont → (SD.⟦ e1 ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ) >>=T cont))
                     (extensionality e2-eq)))
  where
    leA = ⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))
    leB = ⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ (Ψ₂ +ᵘ (One *ᵘ Ψ₁)) ⟧ᶜ)) dγ
    E2' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ₂ ⟧ᶜ)) (restrictᴰ {Γ = Γ} leB dγ)
    ee1 = elaborate IR.Heap e1 ∘ restrictEnv {Γ = Γ} IR.Heap leA
    ee2 = elaborate IR.Heap e2
    let-reduce : evalᴰ fmt ρ (ee2 ∘ bindEnv {Γ = Γ} {A = A} IR.Heap One
                            ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leB , ee1 ⟩) dγ'
                 ≡ (evalᴰ fmt ρ ee1 dγ' >>=T (λ v1 → evalᴰ fmt ρ ee2 (E2' , v1)))
    -- `restrictEnv leB` is stuck on the bound `leB`, so unlike the clause-level
    -- goals this one IS a legitimate `rewrite` target.
    -- D179: by the monad laws, not by patching the trace shape. Threading
    -- moved the `++ []` residuals into the BUDGETS, so `case-trace` (a
    -- trace-only rewrite) can no longer state what is true here.
    --   `bindEnv … One` is `id`, so the middle step is `P >>=T returnT`
    --   — RIGHT IDENTITY; then ASSOCIATIVITY, and the `returnT (E2' , c)`
    --   collapses by left identity, which is definitional.
    let-reduce rewrite evalᴰ-restrictEnv {Γ = Γ} leB dγ =
      (
        trans (cong (λ Q → (Q >>=T evalᴰ fmt ρ ee2))
                    ((>>=T-identityʳ
                       (evalᴰ fmt ρ ee1 dγ' >>=T λ c → returnT (E2' , c)))))
              (>>=T-assoc (evalᴰ fmt ρ ee1 dγ') (λ c → returnT (E2' , c))
                          (evalᴰ fmt ρ ee2)))
    e2-eq : ∀ (v1 : ⟦ A ⟧ᴰ)
          → subst T (cohᴰ B) (evalᴰ fmt ρ ee2 (E2' , subst id (sym (cohᴰ A)) v1))
            ≡ SD.⟦ e2 ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} One (restrictᴰ {Γ = Γ} leB dγ) v1)
    e2-eq v1 =
      trans (cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ρ ee2 w))
                  (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ₂ ⟧ᶜ) (cohᴰ A)
                                    (restrictᴰ {Γ = Γ} leB dγ) v1)))
            ((
               faithful e2 (bindᴰ {Γ = Γ} {A = A} One (restrictᴰ {Γ = Γ} leB dγ) v1)))
faithful (let' {Γ = Γ} {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {A = A} {B = B} e1 e2) dγ =
  trans (cong (λ t → subst T (cohᴰ B) t)
              (trans let-reduce
                     (cong (λ h → h >>=T (λ v1 → evalᴰ fmt ρ ee2 (E2' , v1)))
                           (ihᴰ∘ leA e1 dγ (faithful e1 (restrictᴰ {Γ = Γ} leA dγ))))))
        (trans (morphapp-transport (cohᴰ A) (cohᴰ B) (λ v1 → evalᴰ fmt ρ ee2 (E2' , v1))
                                   (SD.⟦ e1 ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ)))
               (cong (λ cont → (SD.⟦ e1 ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leA dγ) >>=T cont))
                     (extensionality e2-eq)))
  where
    leA = ⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))
    leB = ⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)
    dγ' = subst id (sym (cohᴰ ⟦ Γ ↾ (Ψ₂ +ᵘ (Many *ᵘ Ψ₁)) ⟧ᶜ)) dγ
    E2' = subst id (sym (cohᴰ ⟦ Γ ↾ Ψ₂ ⟧ᶜ)) (restrictᴰ {Γ = Γ} leB dγ)
    ee1 = elaborate IR.Heap e1 ∘ restrictEnv {Γ = Γ} IR.Heap leA
    ee2 = elaborate IR.Heap e2
    let-reduce : evalᴰ fmt ρ (ee2 ∘ bindEnv {Γ = Γ} {A = A} IR.Heap Many
                            ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leB , ee1 ⟩) dγ'
                 ≡ (evalᴰ fmt ρ ee1 dγ' >>=T (λ v1 → evalᴰ fmt ρ ee2 (E2' , v1)))
    -- `restrictEnv leB` is stuck on the bound `leB`, so unlike the clause-level
    -- goals this one IS a legitimate `rewrite` target.
    -- D179: by the monad laws, not by patching the trace shape. Threading
    -- moved the `++ []` residuals into the BUDGETS, so `case-trace` (a
    -- trace-only rewrite) can no longer state what is true here.
    --   `bindEnv … One` is `id`, so the middle step is `P >>=T returnT`
    --   — RIGHT IDENTITY; then ASSOCIATIVITY, and the `returnT (E2' , c)`
    --   collapses by left identity, which is definitional.
    let-reduce rewrite evalᴰ-restrictEnv {Γ = Γ} leB dγ =
      (
        trans (cong (λ Q → (Q >>=T evalᴰ fmt ρ ee2))
                    ((>>=T-identityʳ
                       (evalᴰ fmt ρ ee1 dγ' >>=T λ c → returnT (E2' , c)))))
              (>>=T-assoc (evalᴰ fmt ρ ee1 dγ') (λ c → returnT (E2' , c))
                          (evalᴰ fmt ρ ee2)))
    e2-eq : ∀ (v1 : ⟦ A ⟧ᴰ)
          → subst T (cohᴰ B) (evalᴰ fmt ρ ee2 (E2' , subst id (sym (cohᴰ A)) v1))
            ≡ SD.⟦ e2 ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} Many (restrictᴰ {Γ = Γ} leB dγ) v1)
    e2-eq v1 =
      trans (cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ρ ee2 w))
                  (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ Ψ₂ ⟧ᶜ) (cohᴰ A)
                                    (restrictᴰ {Γ = Γ} leB dγ) v1)))
            ((
               faithful e2 (bindᴰ {Γ = Γ} {A = A} Many (restrictᴰ {Γ = Γ} leB dγ) v1)))

-- Effect primitives: ⟦_⟧ˢ denotes them through generic-info/emit-D/semM exactly
-- as elaborate's `SigOp(generic-info name)∘terminal` (non-arrow) / `curry(SigOp∘
-- snd)` (arrow) reduce ([]++X, returnT, eta) ⇒ refl.
-- D143: at an ERASED arrow the SigOp is a VALUE-position reference — the
-- elaborator emits `value-info` (domain `Unit`), not `arrow-info`, and the
-- arrow's `cohᴰ` is the one-equation form.
faithful (sigOp {A = (Dom ⇒[ mk-kind Zero pure ] Cod)} name (con-fun bDom cCod)) dγ =
    (trans (subst-T-returnT (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ Cod))
                            (λ u → evalᴰ fmt ρ (SigOp (value-info name base-Unit cCod)) u))
           (cong returnT
             (trans (subst-arrow₀ᴰ (cohᴰ Cod)
                       (λ u → evalᴰ fmt ρ (SigOp (value-info name base-Unit cCod)) u))
                    (liftFn-SigOp (value-info name base-Unit cCod)))))
-- plan 0.113 A3: the effectful erased arrow is `arrow-info` at the `Unit` slot.
faithful (sigOp {A = (Dom ⇒[ mk-kind Zero eff ] Cod)} name (con-fun bDom cCod)) dγ =
    (trans (subst-T-returnT (cong (λ y → ⟦ Unit ⟧ᴰ → T y) (cohᴰ Cod))
                            (λ u → evalᴰ fmt ρ (SigOp (arrow-info (mk-kind Zero eff) name base-Unit cCod)) u))
           (cong returnT
             (trans (subst-arrow₀ᴰ (cohᴰ Cod)
                       (λ u → evalᴰ fmt ρ (SigOp (arrow-info (mk-kind Zero eff) name base-Unit cCod)) u))
                    (liftFn-SigOp (arrow-info (mk-kind Zero eff) name base-Unit cCod)))))
faithful (sigOp {A = (Dom ⇒[ mk-kind One π ] Cod)} name (con-fun bDom cCod)) dγ =
    (trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ Dom) (cohᴰ Cod))
                            (λ a → evalᴰ fmt ρ (SigOp (arrow-info (mk-kind One π) name bDom cCod)) a))
           (cong returnT
             (trans (subst-arrowᴰ (cohᴰ Dom) (cohᴰ Cod)
                       (λ a → evalᴰ fmt ρ (SigOp (arrow-info (mk-kind One π) name bDom cCod)) a))
                    (liftFn-SigOp (arrow-info (mk-kind One π) name bDom cCod)))))
faithful (sigOp {A = (Dom ⇒[ mk-kind Many π ] Cod)} name (con-fun bDom cCod)) dγ =
    (trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ Dom) (cohᴰ Cod))
                            (λ a → evalᴰ fmt ρ (SigOp (arrow-info (mk-kind Many π) name bDom cCod)) a))
           (cong returnT
             (trans (subst-arrowᴰ (cohᴰ Dom) (cohᴰ Cod)
                       (λ a → evalᴰ fmt ρ (SigOp (arrow-info (mk-kind Many π) name bDom cCod)) a))
                    (liftFn-SigOp (arrow-info (mk-kind Many π) name bDom cCod)))))
-- D245: a reference is a CALL of the entry (`refIR`), and SD's `refs` read the
-- same call environment at the same entry — the two sides are one term.
faithful (closure name) dγ = refl
faithful (poly name PT) dγ = refl
-- Plan 0.103 phase 1c: a closed term runs on the terminal environment.
faithful (closed e) dγ = faithful e tt
-- NON-ARROW `sigOp`: `elaborate`/`⟦_⟧ˢ` dispatch on `A`'s shape (it stays stuck for
-- ABSTRACT `A`), so case-split the non-arrow type constructors — each is the pure
-- `SigOp(generic-info name)∘terminal` shape ⇒ refl. No SigOp purity semantics added;
-- effect lives in the (absent here) arrow kind, so non-arrow is pure by absence.
faithful {Γ = Γ} (sigOp {A = Unit}     name (con-base ib)) dγ = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit ib) dγ
faithful {Γ = Γ} (sigOp {A = Void}     name (con-base ib)) dγ = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit ib) dγ
faithful {Γ = Γ} (sigOp {A = Int}      name (con-base ib)) dγ = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit ib) dγ
faithful {Γ = Γ} (sigOp {A = Float}    name (con-base ib)) dγ = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit ib) dγ
faithful {Γ = Γ} (sigOp {A = Once.Type.rigid _ _} name (con-base ib)) dγ = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit ib) dγ
faithful {Γ = Γ} (sigOp {A = _ * _}    name (con-base ib)) dγ = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit ib) dγ
faithful {Γ = Γ} (sigOp {A = _ + _}    name (con-base ib)) dγ = sigop-value {⟦ Γ ↾ zeroUsage ⟧ᶜ} (value-info name base-Unit ib) dγ
faithful (sigOp {A = μ-type _} name (con-base ()))
faithful (sigOp {A = ν-type _ _} name (con-base ()))
faithful (sigOp {A = _ ⇒[ _ ] _} name (con-base ()))
faithful (case' {Γ = Γ} {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr}
                {A = A} {B = B} {C = C} s l r) dγ =
  trans (cong (λ t → subst T (cohᴰ C) t)
              (trans case-reduce
                     (cong (λ h → h >>=T branchᴰ)
                           (ihᴰ∘ leS s dγ (faithful s (restrictᴰ {Γ = Γ} leS dγ))))))
        (trans (morphapp-transport (cohᴰ (A + B)) (cohᴰ C) branchᴰ
                                   (SD.⟦ s ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leS dγ)))
               (cong (λ cont → (SD.⟦ s ⟧ˢ fmt σ₀ (restrictᴰ {Γ = Γ} leS dγ) >>=T cont))
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
    es = elaborate IR.Heap s ∘ restrictEnv {Γ = Γ} IR.Heap leS
    LL = elaborate IR.Heap l ∘ bindEnv {Γ = Γ} {A = A} IR.Heap qℓ
                            ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leL ∘ fst , snd ⟩
    RR = elaborate IR.Heap r ∘ bindEnv {Γ = Γ} {A = B} IR.Heap qr
                            ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leR ∘ fst , snd ⟩
    reshape : ⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ
            → ⟦ (⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋ *ᴵ ⌊ A ⌋) +ᴵ (⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋ *ᴵ ⌊ B ⌋) ⟧ᴰᴵ
    reshape v = [ (λ a → inj₁ (Eall' , a)) , (λ b → inj₂ (Eall' , b)) ]′ v
    branchᴰ = λ v → [ (λ a → evalᴰ fmt ρ LL (Eall' , a)) , (λ b → evalᴰ fmt ρ RR (Eall' , b)) ]′ v
    dd-reduce : evalᴰ fmt ρ (distribute {⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋} {⌊ A ⌋} {⌊ B ⌋} IR.Heap
                            ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leAll , es ⟩) dγ'
              ≡ (evalᴰ fmt ρ es dγ' >>=T λ v → returnT (reshape v))
    -- D179: assoc, then the pure `distribute` step. Threading put the `++ []`
    -- residuals inside the budgets, so the trace-shape rewrite this used to do
    -- no longer states a true equation.
    dd-reduce rewrite evalᴰ-restrictEnv {Γ = Γ} leAll dγ = (
      trans (>>=T-assoc (evalᴰ fmt ρ es dγ') (λ c → returnT (Eall' , c))
                        (evalᴰ fmt ρ (distribute {⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋} {⌊ A ⌋} {⌊ B ⌋} IR.Heap)))
            (cong (λ h → (evalᴰ fmt ρ es dγ' >>=T h))
                  (extensionality (λ v →
                     distribute-reduce {⌊ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ ⌋} {⌊ A ⌋} {⌊ B ⌋} Eall' v))))
    case-fuse : ∀ (v : ⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ)
              → evalᴰ fmt ρ (case LL RR) (reshape v) ≡ branchᴰ v
    case-fuse (inj₁ a) = refl
    case-fuse (inj₂ b) = refl
    assoc-fuse : ∀ (mm : T (⟦ ⌊ A ⌋ ⟧ᴰᴵ ⊎ ⟦ ⌊ B ⌋ ⟧ᴰᴵ))
               → ((mm >>=T λ v → returnT (reshape v)) >>=T evalᴰ fmt ρ (case LL RR))
                 ≡ (mm >>=T branchᴰ)
    -- D179: associativity, then `case-fuse`. The `returnT (reshape v)` step
    -- collapses by left identity (definitional); what the old proof did by
    -- hand on the trace is now the law, and the budgets follow.
    assoc-fuse mm = (
      trans (>>=T-assoc mm (λ v → returnT (reshape v)) (evalᴰ fmt ρ (case LL RR)))
            (cong (λ h → (mm >>=T h)) (extensionality case-fuse)))
    case-reduce : evalᴰ fmt ρ (elaborate IR.Heap (case' s l r)) dγ'
                ≡ (evalᴰ fmt ρ es dγ' >>=T branchᴰ)
    case-reduce = trans (cong (_>>=T evalᴰ fmt ρ (case LL RR)) dd-reduce)
                        (assoc-fuse (evalᴰ fmt ρ es dγ'))
    LL-lift : ∀ (a : ⟦ A ⟧ᴰ)
            → liftFn fmt ρ {⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ * A} {C} LL (Eall , a)
              ≡ SD.⟦ l ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a)
    LL-lift a =
      trans (cong (λ t → t (Eall , a))
                  (liftFn-∘ {B = ⟦ (Γ ,ᶜ A) ↾ (qℓ ∷ Ψₗ) ⟧ᶜ} {C = C}
                            {A = ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ * A}
                            (elaborate IR.Heap l)
                            (bindEnv {Γ = Γ} {A = A} IR.Heap qℓ
                              ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leL ∘ fst , snd ⟩)))
        (trans (cong (λ t → (t >>=T liftFn fmt ρ {⟦ (Γ ,ᶜ A) ↾ (qℓ ∷ Ψₗ) ⟧ᶜ} {C}
                                        (elaborate IR.Heap l)))
                     ((branchEnv-denote {Γ = Γ} {Ψ = Ψₗ ⊔ᵘ Ψᵣ} {Ψ' = Ψₗ}
                                                       {A = A} leL qℓ Eall a)))
               (faithful l (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a)))
    RR-lift : ∀ (b : ⟦ B ⟧ᴰ)
            → liftFn fmt ρ {⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ * B} {C} RR (Eall , b)
              ≡ SD.⟦ r ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)
    RR-lift b =
      trans (cong (λ t → t (Eall , b))
                  (liftFn-∘ {B = ⟦ (Γ ,ᶜ B) ↾ (qr ∷ Ψᵣ) ⟧ᶜ} {C = C}
                            {A = ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ * B}
                            (elaborate IR.Heap r)
                            (bindEnv {Γ = Γ} {A = B} IR.Heap qr
                              ∘ ⟨ restrictEnv {Γ = Γ} IR.Heap leR ∘ fst , snd ⟩)))
        (trans (cong (λ t → (t >>=T liftFn fmt ρ {⟦ (Γ ,ᶜ B) ↾ (qr ∷ Ψᵣ) ⟧ᶜ} {C}
                                        (elaborate IR.Heap r)))
                     ((branchEnv-denote {Γ = Γ} {Ψ = Ψₗ ⊔ᵘ Ψᵣ} {Ψ' = Ψᵣ}
                                                       {A = B} leR qr Eall b)))
               (faithful r (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)))
    branch-eq : ∀ (v : ⟦ A + B ⟧ᴰ)
              → subst T (cohᴰ C) (branchᴰ (subst id (sym (cohᴰ (A + B))) v))
                ≡ [ (λ a → SD.⟦ l ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = A} qℓ Eₗ a))
                  , (λ b → SD.⟦ r ⟧ˢ fmt σ₀ (bindᴰ {Γ = Γ} {A = B} qr Eᵣ b)) ]′ v
    branch-eq (inj₁ a) =
      trans (cong (λ w → subst T (cohᴰ C) (branchᴰ w)) (push⊎₁⁻ (cohᴰ A) (cohᴰ B) a))
            (trans (cong (λ w → subst T (cohᴰ C) (evalᴰ fmt ρ LL w))
                         (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ) (cohᴰ A) Eall a)))
                   ((LL-lift a)))
    branch-eq (inj₂ b) =
      trans (cong (λ w → subst T (cohᴰ C) (branchᴰ w)) (push⊎₂⁻ (cohᴰ A) (cohᴰ B) b))
            (trans (cong (λ w → subst T (cohᴰ C) (evalᴰ fmt ρ RR w))
                         (sym (pair-subst⁻ (cohᴰ ⟦ Γ ↾ (Ψₗ ⊔ᵘ Ψᵣ) ⟧ᶜ) (cohᴰ B) Eall b)))
                   ((RR-lift b)))
-- Plan 0.113 B1: the algebra reads the environment through `⊑ᵘ-*Many`; its
-- composite with `restrictEnv` is faithful by `liftFn-restrictEnv` + its own IH.
faithful {Γ = Γ} (cata {Ψ = Ψ} {F = F} {A = A} {π = π} wf alg) dγ =
  FL.cata-body {Γ = Γ} wf alg dγ
    (trans (cong (λ t → t dγ)
                 (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = ⟦ F ⟧T A ⇒[ mk-kind Many π ] A} {A = ⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ}
                           (elaborate IR.Heap alg) (restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-*Many Ψ))))
       (trans (cong (_>>=T liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {⟦ F ⟧T A ⇒[ mk-kind Many π ] A} (elaborate IR.Heap alg))
                    (liftFn-restrictEnv {Γ = Γ} (⊑ᵘ-*Many Ψ) dγ))
              (faithful alg (restrictᴰ {Γ = Γ} (⊑ᵘ-*Many Ψ) dγ))))
-- ana: dual of cata; reduces to the same closure-bridge via `ana-body`
-- (+ the `ana-ev-bridge` trace lemma).
faithful {Γ = Γ} (ana {Ψ = Ψ} {F = F} {A = A} {π₀ = π₀} {π = π} wf coalg) dγ =
  FL.ana-body {Γ = Γ} {π₀ = π₀} {π = π} wf coalg dγ
    (trans (cong (λ t → t dγ)
                 (liftFn-∘ {B = ⟦ Γ ↾ Ψ ⟧ᶜ} {C = A ⇒[ mk-kind Many π ] ⟦ F ⟧T A} {A = ⟦ Γ ↾ (Many *ᵘ Ψ) ⟧ᶜ}
                           (elaborate IR.Heap coalg) (restrictEnv {Γ = Γ} IR.Heap (⊑ᵘ-*Many Ψ))))
       (trans (cong (_>>=T liftFn fmt ρ {⟦ Γ ↾ Ψ ⟧ᶜ} {A ⇒[ mk-kind Many π ] ⟦ F ⟧T A} (elaborate IR.Heap coalg))
                    (liftFn-restrictEnv {Γ = Γ} (⊑ᵘ-*Many Ψ) dγ))
              (faithful coalg (restrictᴰ {Γ = Γ} (⊑ᵘ-*Many Ψ) dγ))))

------------------------------------------------------------------------
-- D143: faithfulness at the EMPTY context, stated for `elaborateFull`.
--
-- `elaborateFull = elaborate ∘ eraseCtx`, and at `Γ = ∅` the erasure adapter
-- is the identity — but only once `Ψ` is MATCHED (`Usage` is a `data`, so
-- `eraseCtx {∅} m Ψ` is stuck on a variable). Matching it here, inside a
-- lemma, keeps the main reduction path free of the constraint: callers may
-- leave their `Usage 0` abstract.
------------------------------------------------------------------------
faithful∅ : ∀ {Ψ : Usage 0} {A} (e : Expr ∅ Ψ A)
          → liftFn fmt ρ {⟦ ∅ ⟧ᶜ} {A} (elaborateFull IR.Heap e) tt
            ≡ SD.⟦ e ⟧ˢ fmt σ₀ (env0 {Ψ} tt)
faithful∅ {SrfS.[]} e = faithful e tt
