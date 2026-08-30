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

open import Once.Type using (Type; Unit; Void; Int; Str; Float; Buffer; _*_; _+_; _⇒[_]_; μ-type; ν-type; mk-kind; pure; eff; Many)
open import Once.Functor.Translate using (con-base; con-fun; base-Unit)
open import Once.Surface.Syntax using (Expr; Ctx; Usage; lookup; _,_^_; ⟦_⟧ᶜ)
open import Once.Surface.Context using () renaming (_,_ to _,ᶜ_)
open import Once.Surface.Elaborate using (elaborate; proj; distribute; compIR; copairIR; forkIR; curryIR; distribIR)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.IR using (_∘_; ⟨_,_⟩; apply; fst; snd; curry; SigOp; terminal; case) renaming (id to idIR)
open import Once.Arith.SigOp.Builders using (arrow-info; value-info; internal-info)
open import Once.Adequacy.CataErased fmt using (liftFn-SigOp)
open import Once.SigOp.Info using (SigOpInfo; semM)
open import Once.Denotation.DenotTrace using (emit-D)
open import Once.CanonicalName using (bare)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; evalᴰ; inject; liftFn; cohᴰ)
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
ihᴰ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ)
    → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {A} (elaborate C.Heap e) dγ j ≡ SD.⟦ e ⟧ˢ fmt dγ j)
    → evalᴰ fmt (elaborate C.Heap e) (subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ) ≡ subst T (sym (cohᴰ A)) (SD.⟦ e ⟧ˢ fmt dγ)
ihᴰ {A = A} e dγ ih = trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (extensionality ih))

-- non-arrow (value-position) `SigOp info ∘ terminal`: `terminal` discards the env,
-- so `liftFn` = the emit/semM pair transported by `cohᴰ A` (subst-subst-sym).
sigop-value : ∀ {n} {Γ : Ctx n} {A : Type} (info : SigOpInfo Unit A) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → liftFn fmt {⟦ Γ ⟧ᶜ} {A} (SigOp info ∘ terminal) dγ k ≡ (emit-D info tt , inject (semM info fmt tt))
sigop-value {A = A} info dγ k =
  trans (subst-T-apply (cohᴰ A) (evalᴰ fmt (SigOp info) tt) k)
        (cong₂ _,_ refl (subst-subst-sym (cohᴰ A)))

proj-lookup : ∀ {n} {Γ : Ctx n} (i : Fin n) (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
            → liftFn fmt {⟦ Γ ⟧ᶜ} {lookup Γ i} (proj {Γ = Γ} i) dγ k ≡ returnT (SD.lookupᴰ Γ i dγ) k
proj-lookup {Γ = Γ , A ^ q} zero    dγ k =
  cong (λ t → t k)
    (trans (cong (λ w → subst T (cohᴰ A) (returnT w)) (proj₂-subst (cohᴰ ⟦ Γ ⟧ᶜ) (cohᴰ A) dγ))
      (trans (subst-T-returnT (cohᴰ A) (subst id (sym (cohᴰ A)) (proj₂ dγ)))
             (cong returnT (subst-subst-sym (cohᴰ A)))))
proj-lookup {Γ = Γ , A ^ q} (suc i) dγ k =
  trans (cong (λ arg → subst T (cohᴰ (lookup Γ i)) (evalᴰ fmt (proj {Γ = Γ} i) arg) k)
              (proj₁-subst (cohᴰ ⟦ Γ ⟧ᶜ) (cohᴰ A) dγ))
        (proj-lookup {Γ = Γ} i (proj₁ dγ) k)

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

comp-body : ∀ {m} {Γ : Ctx m} {Ψ₁ Ψ₂ : Usage m} {A B C} {π}
              (f : Expr Γ Ψ₁ (B ⇒[ mk-kind Many π ] C))
              (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many π ] B))
              (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (n : ℕ)
            → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {B ⇒[ mk-kind Many π ] C} (elaborate C.Heap f) dγ j ≡ SD.⟦ f ⟧ˢ fmt dγ j)
            → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {A ⇒[ mk-kind Many π ] B} (elaborate C.Heap g) dγ j ≡ SD.⟦ g ⟧ˢ fmt dγ j)
            → liftFn fmt {⟦ Γ ⟧ᶜ} {A ⇒[ mk-kind Many π ] C}
                     (compIR C.Heap ∘ ⟨ elaborate C.Heap f , elaborate C.Heap g ⟩ C.Heap) dγ n
              ≡ (SD.⟦ f ⟧ˢ fmt dγ >>=T (λ vf → SD.⟦ g ⟧ˢ fmt dγ >>=T (λ vg →
                 returnT (λ a → vg a >>=T vf)))) n
comp-body {Γ = Γ} {A = A} {B = B} {C = C} {π = π} f g dγ n ihf ihg =
  trans (cong (λ t → subst T (cohᴰ (A ⇒[ mk-kind Many π ] C)) t n)
              (trans evalᴰ-comp-reduce
                     (cong₂ (λ hf hg → hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ a → vg a >>=T vf))))
                            ihf-T ihg-T)))
        (comp-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (SD.⟦ f ⟧ˢ fmt dγ) (SD.⟦ g ⟧ˢ fmt dγ) n)
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ
    ef = elaborate C.Heap f
    eg = elaborate C.Heap g
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))) (SD.⟦ f ⟧ˢ fmt dγ)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C)))) (extensionality ihf))
    ihg-T : evalᴰ fmt eg dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) (SD.⟦ g ⟧ˢ fmt dγ)
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

curry-body : ∀ {m} {Γ : Ctx m} {Ψ : Usage m} {A B C}
               (f : Expr Γ Ψ ((A * B) ⇒[ mk-kind Many pure ] C))
               (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (n : ℕ)
             → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {(A * B) ⇒[ mk-kind Many pure ] C} (elaborate C.Heap f) dγ j ≡ SD.⟦ f ⟧ˢ fmt dγ j)
             → liftFn fmt {⟦ Γ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C)}
                      (curryIR C.Heap ∘ elaborate C.Heap f) dγ n
               ≡ (SD.⟦ f ⟧ˢ fmt dγ >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b))))) n
curry-body {Γ = Γ} {A = A} {B = B} {C = C} f dγ n ihf =
  trans (cong (λ t → subst T (cohᴰ (A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C))) t n)
              (trans evalᴰ-curry-reduce
                     (cong (λ hf → hf >>=T (λ vf → returnT (λ a → returnT (λ b → vf (a , b))))) ihf-T)))
        (curry-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (SD.⟦ f ⟧ˢ fmt dγ) n)
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ
    ef = elaborate C.Heap f
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ (A * B)) (cohᴰ C))) (SD.⟦ f ⟧ˢ fmt dγ)
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

fork-body : ∀ {m} {Γ : Ctx m} {Ψ₁ Ψ₂ : Usage m} {A B C}
              (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many pure ] B))
              (g : Expr Γ Ψ₂ (A ⇒[ mk-kind Many pure ] C))
              (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (n : ℕ)
            → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] B} (elaborate C.Heap f) dγ j ≡ SD.⟦ f ⟧ˢ fmt dγ j)
            → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] C} (elaborate C.Heap g) dγ j ≡ SD.⟦ g ⟧ˢ fmt dγ j)
            → liftFn fmt {⟦ Γ ⟧ᶜ} {A ⇒[ mk-kind Many pure ] (B * C)}
                     (forkIR C.Heap ∘ ⟨ elaborate C.Heap f , elaborate C.Heap g ⟩ C.Heap) dγ n
              ≡ (SD.⟦ f ⟧ˢ fmt dγ >>=T (λ vf → SD.⟦ g ⟧ˢ fmt dγ >>=T (λ vg →
                 returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c))))))) n
fork-body {Γ = Γ} {A = A} {B = B} {C = C} f g dγ n ihf ihg =
  trans (cong (λ t → subst T (cohᴰ (A ⇒[ mk-kind Many pure ] (B * C))) t n)
              (trans evalᴰ-fork-reduce
                     (cong₂ (λ hf hg → hf >>=T (λ vf → hg >>=T (λ vg →
                              returnT (λ a → vf a >>=T (λ b → vg a >>=T (λ c → returnT (b , c)))))))
                            ihf-T ihg-T)))
        (fork-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (SD.⟦ f ⟧ˢ fmt dγ) (SD.⟦ g ⟧ˢ fmt dγ) n)
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ
    ef = elaborate C.Heap f
    eg = elaborate C.Heap g
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) (SD.⟦ f ⟧ˢ fmt dγ)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (extensionality ihf))
    ihg-T : evalᴰ fmt eg dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))) (SD.⟦ g ⟧ˢ fmt dγ)
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

copair-body : ∀ {m} {Γ : Ctx m} {Ψ₁ Ψ₂ : Usage m} {A B C} {π}
                (f : Expr Γ Ψ₁ (A ⇒[ mk-kind Many π ] C))
                (g : Expr Γ Ψ₂ (B ⇒[ mk-kind Many π ] C))
                (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (n : ℕ)
              → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {A ⇒[ mk-kind Many π ] C} (elaborate C.Heap f) dγ j ≡ SD.⟦ f ⟧ˢ fmt dγ j)
              → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {B ⇒[ mk-kind Many π ] C} (elaborate C.Heap g) dγ j ≡ SD.⟦ g ⟧ˢ fmt dγ j)
              → liftFn fmt {⟦ Γ ⟧ᶜ} {(A + B) ⇒[ mk-kind Many π ] C}
                       (copairIR C.Heap ∘ ⟨ elaborate C.Heap f , elaborate C.Heap g ⟩ C.Heap) dγ n
                ≡ (SD.⟦ f ⟧ˢ fmt dγ >>=T (λ vf → SD.⟦ g ⟧ˢ fmt dγ >>=T (λ vg →
                   returnT (λ ab → [ vf , vg ]′ ab)))) n
copair-body {Γ = Γ} {A = A} {B = B} {C = C} {π = π} f g dγ n ihf ihg =
  trans (cong (λ t → subst T (cohᴰ ((A + B) ⇒[ mk-kind Many π ] C)) t n)
              (trans evalᴰ-copair-reduce
                     (cong₂ (λ hf hg → hf >>=T (λ vf → hg >>=T (λ vg → returnT (λ ab → [ vf , vg ]′ ab))))
                            ihf-T ihg-T)))
        (copair-transport (cohᴰ A) (cohᴰ B) (cohᴰ C) (SD.⟦ f ⟧ˢ fmt dγ) (SD.⟦ g ⟧ˢ fmt dγ) n)
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ
    ef = elaborate C.Heap f
    eg = elaborate C.Heap g
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))) (SD.⟦ f ⟧ˢ fmt dγ)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ C)))) (extensionality ihf))
    ihg-T : evalᴰ fmt eg dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ B) (cohᴰ C))) (SD.⟦ g ⟧ˢ fmt dγ)
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

app-body : ∀ {m} {Γ : Ctx m} {Ψ₁ Ψ₂ : Usage m} {A B} {kk}
             (f : Expr Γ Ψ₁ (A ⇒[ kk ] B)) (x : Expr Γ Ψ₂ A)
             (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (n : ℕ)
           → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {A ⇒[ kk ] B} (elaborate C.Heap f) dγ j ≡ SD.⟦ f ⟧ˢ fmt dγ j)
           → (∀ j → liftFn fmt {⟦ Γ ⟧ᶜ} {A} (elaborate C.Heap x) dγ j ≡ SD.⟦ x ⟧ˢ fmt dγ j)
           → liftFn fmt {⟦ Γ ⟧ᶜ} {B} (apply ∘ ⟨ elaborate C.Heap f , elaborate C.Heap x ⟩ C.Heap) dγ n
             ≡ (SD.⟦ f ⟧ˢ fmt dγ >>=T (λ vf → SD.⟦ x ⟧ˢ fmt dγ >>=T (λ vx → vf vx))) n
app-body {Γ = Γ} {A = A} {B = B} {kk = kk} f x dγ n ihf ihx =
  trans (cong (λ t → subst T (cohᴰ B) t n)
              (trans evalᴰ-app-reduce
                     (cong₂ (λ hf hx → hf >>=T (λ vf → hx >>=T (λ vx → vf vx))) ihf-T ihx-T)))
        (app-transport (cohᴰ A) (cohᴰ B) (SD.⟦ f ⟧ˢ fmt dγ) (SD.⟦ x ⟧ˢ fmt dγ) n)
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ
    ef = elaborate C.Heap f
    ex = elaborate C.Heap x
    ihf-T : evalᴰ fmt ef dγ' ≡ subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))) (SD.⟦ f ⟧ˢ fmt dγ)
    ihf-T = trans (sym (subst-sym-subst (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B))))
                  (cong (subst T (sym (cong₂ (λ u v → u → T v) (cohᴰ A) (cohᴰ B)))) (extensionality ihf))
    ihx-T : evalᴰ fmt ex dγ' ≡ subst T (sym (cohᴰ A)) (SD.⟦ x ⟧ˢ fmt dγ)
    ihx-T = trans (sym (subst-sym-subst (cohᴰ A))) (cong (subst T (sym (cohᴰ A))) (extensionality ihx))
    evalᴰ-app-reduce : evalᴰ fmt (apply ∘ ⟨ ef , ex ⟩ C.Heap) dγ'
                       ≡ (evalᴰ fmt ef dγ' >>=T (λ vf → evalᴰ fmt ex dγ' >>=T (λ vx → vf vx)))
    evalᴰ-app-reduce = extensionality (λ m →
      cong₂ _,_ (app-trace (proj₁ (evalᴰ fmt ef dγ' m)) (proj₁ (evalᴰ fmt ex dγ' m))
                           (proj₁ ((proj₂ (evalᴰ fmt ef dγ' m)) (proj₂ (evalᴰ fmt ex dγ' m)) m))) refl)

faithful :
  ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A} (e : Expr Γ Ψ A)
    (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → liftFn fmt (elaborate C.Heap e) dγ k ≡ SD.⟦ e ⟧ˢ fmt dγ k
-- `unit` ↦ `terminal`; both sides reduce to `returnT tt` ⇒ refl.
faithful (var {Γ = Γ} i) dγ k = proj-lookup {Γ = Γ} i dγ k
faithful (arr' f) dγ k = faithful f dγ k
-- lam ↦ curry: both sides are `returnT <closure>`; the closures are equal by
-- extensionality over the argument (and over the depth, via the body IH).
faithful (lam {Γ = Γ} {A = A} {B = B} q _ e) dγ k =
  trans (cong (λ t → t k) liftFn-curry-reduce)
        (cong (_,_ []) (extensionality (λ a → extensionality (λ k′ → faithful e (dγ , a) k′))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ
    ee = elaborate C.Heap e
    liftFn-curry-reduce : liftFn fmt {⟦ Γ ⟧ᶜ} {A ⇒[ mk-kind q pure ] B} (curry ee C.Heap) dγ
                          ≡ returnT (λ a → liftFn fmt {⟦ Γ ,ᶜ A ⟧ᶜ} {B} ee (dγ , a))
    liftFn-curry-reduce =
      trans (subst-T-returnT (cong₂ (λ x y → x → T y) (cohᴰ A) (cohᴰ B)) (λ a → evalᴰ fmt ee (dγ' , a)))
            (cong returnT
              (trans (subst-arrowᴰ (cohᴰ A) (cohᴰ B) (λ a → evalᴰ fmt ee (dγ' , a)))
                     (extensionality (λ a →
                       cong (λ w → subst T (cohᴰ B) (evalᴰ fmt ee w))
                            (sym (pair-subst⁻ (cohᴰ ⟦ Γ ⟧ᶜ) (cohᴰ A) dγ a))))))
-- app: `apply ∘ ⟨ef,ex⟩`. Rewrite both IHs; the closures/args align so `apply`
-- runs the SAME `vf vx` ⇒ value refl; trace re-associates (app-trace).
faithful (app f x) dγ n = app-body f x dγ n (λ j → faithful f dγ j) (λ j → faithful x dγ j)
-- effApp: a SUSPENDED closure whose body is the (effectful) application of f to x.
-- Both sides are `returnT <closure>` (the Unit-thunk); the closure body is exactly
-- app-body, lifted through extensionality (over the discarded Unit arg + depth).
faithful (effApp {Γ = Γ} {A = A} {B = B} f x) dγ k =
  trans (cong (λ t → t k) liftFn-curry-reduce-effApp)
        (cong (_,_ []) (extensionality (λ _ →
          extensionality (λ n → app-body f x dγ n (λ j → faithful f dγ j) (λ j → faithful x dγ j)))))
  where
    dγ' = subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ
    body = (apply ∘ ⟨ elaborate C.Heap f , elaborate C.Heap x ⟩ C.Heap) ∘ fst
    liftFn-curry-reduce-effApp :
      liftFn fmt {⟦ Γ ⟧ᶜ} {Unit ⇒[ mk-kind Many eff ] B} (curry body C.Heap) dγ
      ≡ returnT (λ _ → liftFn fmt {⟦ Γ ⟧ᶜ} {B} (apply ∘ ⟨ elaborate C.Heap f , elaborate C.Heap x ⟩ C.Heap) dγ)
    liftFn-curry-reduce-effApp =
      trans (subst-T-returnT (cong₂ (λ u v → u → T v) (cohᴰ Unit) (cohᴰ B)) (λ u → evalᴰ fmt body (dγ' , u)))
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
faithful (comp' f g) dγ n = comp-body f g dγ n (λ j → faithful f dγ j) (λ j → faithful g dγ j)
faithful (curry' f) dγ n = curry-body f dγ n (λ j → faithful f dγ j)
faithful (fork' f g) dγ n = fork-body f g dγ n (λ j → faithful f dγ j) (λ j → faithful g dγ j)
faithful (copair' f g) dγ n = copair-body f g dγ n (λ j → faithful f dγ j) (λ j → faithful g dγ j)
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
faithful (add a b)  dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) refl
faithful (sub a b)  dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) refl
faithful (mul a b)  dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) refl
-- PLAN 0.75 F4: the float family, structurally identical to the integer one.
faithful (fadd a b)  dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) refl
faithful (fsub a b)  dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) refl
faithful (fmul a b)  dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) refl
faithful (fdiv a b)  dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) refl
faithful (i2f a)    dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) = refl   -- unary: no `++` to neutralise, cf. `neg`
faithful (div a b)  dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) refl
faithful (mod' a b) dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) refl
faithful (lt a b)   dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (le a b)   dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (gt a b)   dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (ge a b)   dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (eq a b)   dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) (inj-uu _)
faithful (ne a b)   dγ n rewrite ihᴰ a dγ (λ j → faithful a dγ j) | ihᴰ b dγ (λ j → faithful b dγ j) = cong₂ _,_ (++-identityʳ _) (inj-uu _)
-- neg: single subterm; IR `negIR ∘ ee` and ⟦_⟧ˢ share the bind+cont, so refl post-IH.
faithful (neg e)    dγ n rewrite ihᴰ e dγ (λ j → faithful e dγ j) = refl
-- pair: `elaborate = ⟨ea,eb⟩`, same bind structure as ⟦_⟧ˢ (ends in returnT(va,vb),
-- no trailing SigOp bind) ⇒ refl post both IHs.
faithful (pair {A = A} {B = B} a b) dγ n =
  trans (cong (λ t → subst T (cohᴰ (A * B)) t n)
              (cong₂ (λ ha hb → ha >>=T (λ va → hb >>=T (λ vb → returnT (va , vb))))
                     (ihᴰ a dγ (λ j → faithful a dγ j)) (ihᴰ b dγ (λ j → faithful b dγ j))))
        (pair-transport (cohᴰ A) (cohᴰ B) (SD.⟦ a ⟧ˢ fmt dγ) (SD.⟦ b ⟧ˢ fmt dγ) n)
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
    dγ' = subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ
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
    dγ' = subst id (sym (cohᴰ ⟦ Γ ⟧ᶜ)) dγ
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
