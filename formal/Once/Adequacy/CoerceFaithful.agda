-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoerceFaithful — a compiled conversion means `⟦ p ⟧<:`
-- (plan 0.99, D226).
--
-- `coerce-lift`: the IR `runCoe p` emits, run through the IR semantics and
-- transported to the source value domain, is the source conversion `⟦ p ⟧<:`
-- mapped over the operand's result. Two cases, split on the SAME decision
-- `runCoe` makes:
--
--   * a void-free derivation emits no code (`subst … f`). Its meaning is a
--     transport along some `⟦ A ⟧ᴰ ≡ ⟦ B ⟧ᴰ` (`vf-sem`), and the two transports
--     that meet at the end are equal because identity proofs are unique (K).
--   * otherwise `coeIR p ∘ f`, and `coeIR-lift` shows the structural IR is pure
--     and computes `⟦ p ⟧<:`, former by former, from `LiftFnReduce`'s lemmas.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.CoerceFaithful (fmt : TargetNum) where

open import Function using (id)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Type as Ty using (Type; Zero; One; Many; mk-kind; _⇒[_]_; _*_; _+_; Unit)
open import Once.Type.Sub
open import Once.IR as IR using (IR; IRTy; _∘_; ⟨_,_⟩; fst; snd; case; curry; apply; inl; inr; initial; ⌊_⌋)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; cohᴰ)
open import Once.Denotation.TraceMonad using (T; mkT; returnT; _>>=T_; fmapT; >>=T-map)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
open import Once.Denotation.Sub using (⟦_⟧<:; fmapT-id; fmapT-cong)
open import Once.Surface.CoerceIR
open import Once.Adequacy.LiftFnReduce fmt
  using (liftFn-id; liftFn-fst; liftFn-snd; liftFn-inl; liftFn-inr; liftFn-∘; liftFn-pair;
         liftFn-apply; liftFn-curry; liftFn-case-inj₁; liftFn-case-inj₂; curry-red; apply-red)
open import Once.Adequacy.FaithfulLemmas fmt using (T-ext-at)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- Small facts.
------------------------------------------------------------------------

-- Binding a pure continuation is a map (the budget-indexed `>>=T-map`, closed).
bind-ret : ∀ {X Y : Set} (m : T X) (g : X → Y) → (m >>=T (λ x → returnT (g x))) ≡ fmapT g m
bind-ret m g = T-ext-at (>>=T-map m g)

fmapT-subst : ∀ {X Y : Set} (E : X ≡ Y) (m : T X) → fmapT (subst id E) m ≡ subst T E m
fmapT-subst refl m = fmapT-id m

subst-T-∘ : ∀ {X Y Z : Set} (P : X ≡ Y) (Q : Y ≡ Z) (m : T X)
          → subst T Q (subst T P m) ≡ subst T (trans P Q) m
subst-T-∘ refl refl m = refl

subst-⟦⟧ : ∀ {X Y : IRTy} (E : X ≡ Y) (m : T ⟦ X ⟧ᴰᴵ)
         → subst (λ W → T ⟦ W ⟧ᴰᴵ) E m ≡ subst T (cong ⟦_⟧ᴰᴵ E) m
subst-⟦⟧ refl m = refl

eval-subst : ∀ {Z X Y : IRTy} (E : X ≡ Y) (f : IR Z X) (v : ⟦ Z ⟧ᴰᴵ)
           → evalᴰ fmt (subst (IR Z) E f) v ≡ subst (λ W → T ⟦ W ⟧ᴰᴵ) E (evalᴰ fmt f v)
eval-subst refl f v = refl

uip : ∀ {X Y : Set} (p q : X ≡ Y) → p ≡ q
uip refl refl = refl

sym-sym : ∀ {X Y : Set} (E : X ≡ Y) → sym (sym E) ≡ E
sym-sym refl = refl

subst-arr : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (f : X → T Y)
          → subst id (cong₂ (λ U V → U → T V) P Q) f ≡ (λ x′ → subst T Q (f (subst id (sym P) x′)))
subst-arr refl refl f = refl

subst-arr₀ : ∀ {Y Y′ : Set} (Q : Y ≡ Y′) (f : ⊤ → T Y)
           → subst id (cong (λ V → ⊤ → T V) Q) f ≡ (λ u → subst T Q (f u))
subst-arr₀ refl f = refl

subst-pair : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (x : X) (y : Y)
           → subst id (cong₂ _×_ P Q) (x , y) ≡ (subst id P x , subst id Q y)
subst-pair refl refl x y = refl

subst-inj₁ : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (x : X)
           → subst id (cong₂ _⊎_ P Q) (inj₁ x) ≡ inj₁ (subst id P x)
subst-inj₁ refl refl x = refl

subst-inj₂ : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (y : Y)
           → subst id (cong₂ _⊎_ P Q) (inj₂ y) ≡ inj₂ (subst id Q y)
subst-inj₂ refl refl y = refl

------------------------------------------------------------------------
-- `apply` / `curry` at `One` and `Zero` arrows (LiftFnReduce states `Many`).
------------------------------------------------------------------------

liftFn-apply₁ : ∀ {A B : Type} {π}
  → liftFn fmt {(A ⇒[ mk-kind One π ] B) * A} {B} apply ≡ (λ v → proj₁ v (proj₂ v))
liftFn-apply₁ {A} {B} = extensionality λ v → apply-red (cohᴰ A) (cohᴰ B) v

liftFn-curry₁ : ∀ {A B C : Type} {π} (g : IR ⌊ A * B ⌋ ⌊ C ⌋)
  → liftFn fmt {A} {B ⇒[ mk-kind One π ] C} (curry g)
    ≡ (λ a → returnT (λ b → liftFn fmt {A * B} {C} g (a , b)))
liftFn-curry₁ {A} {B} {C} g = extensionality λ a → curry-red (cohᴰ A) (cohᴰ B) (cohᴰ C) (evalᴰ fmt g) a

private
  apply-red₀ : ∀ {BI BT : Set} (pB : BI ≡ BT) (v : (⊤ → T BT) × ⊤)
    → subst T pB (proj₁ (subst id (sym (cong₂ _×_ (cong (λ y → ⊤ → T y) pB) refl)) v)
                         (proj₂ (subst id (sym (cong₂ _×_ (cong (λ y → ⊤ → T y) pB) refl)) v)))
      ≡ proj₁ v (proj₂ v)
  apply-red₀ refl v = refl

  curry-red₀ : ∀ {AI AT CI CT : Set} (pA : AI ≡ AT) (pC : CI ≡ CT)
                 (gg : AI × ⊤ → T CI) (a : AT)
    → subst T (cong (λ y → ⊤ → T y) pC) (returnT (λ u → gg (subst id (sym pA) a , u)))
      ≡ returnT (λ u → subst T pC (gg (subst id (sym (cong₂ _×_ pA refl)) (a , u))))
  curry-red₀ refl refl gg a = refl

liftFn-apply₀ : ∀ {A B : Type} {π}
  → liftFn fmt {(A ⇒[ mk-kind Zero π ] B) * Unit} {B} apply ≡ (λ v → proj₁ v (proj₂ v))
liftFn-apply₀ {A} {B} = extensionality λ v → apply-red₀ (cohᴰ B) v

liftFn-curry₀ : ∀ {A B C : Type} {π} (g : IR ⌊ A * Unit ⌋ ⌊ C ⌋)
  → liftFn fmt {A} {B ⇒[ mk-kind Zero π ] C} (curry g)
    ≡ (λ a → returnT (λ u → liftFn fmt {A * Unit} {C} g (a , u)))
liftFn-curry₀ {A} {B} {C} g = extensionality λ a → curry-red₀ (cohᴰ A) (cohᴰ C) (evalᴰ fmt g) a

------------------------------------------------------------------------
-- The structural IR computes `⟦ p ⟧<:`, purely.
------------------------------------------------------------------------

mutual
  coeIR-lift : ∀ {A B} (p : A <: B) (v : ⟦ A ⟧ᴰ) → liftFn fmt {A} {B} (coeIR p) v ≡ returnT (⟦ p ⟧<: v)
  coeIR-lift sub-void ()
  coeIR-lift sub-unit   v = cong (λ h → h v) (liftFn-id {A = Unit})
  coeIR-lift sub-int    v = cong (λ h → h v) (liftFn-id {A = Ty.Int})
  coeIR-lift sub-float  v = cong (λ h → h v) (liftFn-id {A = Ty.Float})
  coeIR-lift sub-str    v = cong (λ h → h v) (liftFn-id {A = Ty.Str})
  coeIR-lift sub-buffer v = cong (λ h → h v) (liftFn-id {A = Ty.Buffer})
  coeIR-lift (sub-μ {F}) v = cong (λ h → h v) (liftFn-id {A = Ty.μ-type F})
  coeIR-lift (sub-ν {F}) v = cong (λ h → h v) (liftFn-id {A = Ty.ν-type F})
  coeIR-lift (sub-arr {A} {A′} {B} {B′} {Zero} {π} {π′} a b _) f =
    trans (cong (λ h → h f) (liftFn-curry₀ {A = A ⇒[ mk-kind Zero π ] B} {B = A′} {C = B′} {π = π′}
                                           (coeIR b ∘ apply)))
          (cong returnT (extensionality λ u → arr₀ {A} {A′} {B} {B′} {π} a b f u))
  coeIR-lift (sub-arr {A} {A′} {B} {B′} {One} {π} {π′} a b _) f =
    trans (cong (λ h → h f) (liftFn-curry₁ {A = A ⇒[ mk-kind One π ] B} {B = A′} {C = B′} {π = π′}
                                           (coeIR b ∘ (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩))))
          (cong returnT (extensionality λ x′ → arr₁ {A} {A′} {B} {B′} {π} a b f x′))
  coeIR-lift (sub-arr {A} {A′} {B} {B′} {Many} {π} {π′} a b _) f =
    trans (cong (λ h → h f) (liftFn-curry {A = A ⇒[ mk-kind Many π ] B} {B = A′} {C = B′} {π = π′}
                                          (coeIR b ∘ (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩))))
          (cong returnT (extensionality λ x′ → arrω {A} {A′} {B} {B′} {π} a b f x′))
  coeIR-lift (sub-prod {A} {A′} {B} {B′} a b) (x , y) =
    trans (cong (λ h → h (x , y)) (liftFn-pair {A = A * B} {B = A′} {C = B′} (coeIR a ∘ fst) (coeIR b ∘ snd)))
          (cong₂ (λ m₁ m₂ → m₁ >>=T (λ u → m₂ >>=T (λ w → returnT (u , w)))) l r)
    where
      l : liftFn fmt {A * B} {A′} (coeIR a ∘ fst) (x , y) ≡ returnT (⟦ a ⟧<: x)
      l = trans (cong (λ h → h (x , y)) (liftFn-∘ {B = A} {C = A′} {A = A * B} (coeIR a) fst))
                (trans (cong (_>>=T liftFn fmt {A} {A′} (coeIR a)) (cong (λ h → h (x , y)) (liftFn-fst {A = A} {B = B})))
                       (coeIR-lift a x))
      r : liftFn fmt {A * B} {B′} (coeIR b ∘ snd) (x , y) ≡ returnT (⟦ b ⟧<: y)
      r = trans (cong (λ h → h (x , y)) (liftFn-∘ {B = B} {C = B′} {A = A * B} (coeIR b) snd))
                (trans (cong (_>>=T liftFn fmt {B} {B′} (coeIR b)) (cong (λ h → h (x , y)) (liftFn-snd {A = A} {B = B})))
                       (coeIR-lift b y))
  coeIR-lift (sub-sum {A} {A′} {B} {B′} a b) (inj₁ x) =
    trans (liftFn-case-inj₁ {A = A} {B = B} {C = A′ + B′} (inl ∘ coeIR a) (inr ∘ coeIR b) x)
      (trans (cong (λ h → h x) (liftFn-∘ {B = A′} {C = A′ + B′} {A = A} inl (coeIR a)))
        (trans (cong (_>>=T liftFn fmt {A′} {A′ + B′} inl) (coeIR-lift a x))
               (cong (λ h → h (⟦ a ⟧<: x)) (liftFn-inl {A = A′} {B = B′}))))
  coeIR-lift (sub-sum {A} {A′} {B} {B′} a b) (inj₂ y) =
    trans (liftFn-case-inj₂ {A = A} {B = B} {C = A′ + B′} (inl ∘ coeIR a) (inr ∘ coeIR b) y)
      (trans (cong (λ h → h y) (liftFn-∘ {B = B′} {C = A′ + B′} {A = B} inr (coeIR b)))
        (trans (cong (_>>=T liftFn fmt {B′} {A′ + B′} inr) (coeIR-lift b y))
               (cong (λ h → h (⟦ b ⟧<: y)) (liftFn-inr {B = B′} {A = A′}))))

  -- The closure body at each quantity: `apply` the old closure to the argument
  -- converted backwards, then convert the result forwards.
  arr₀ : ∀ {A A′ B B′ π} (a : A′ <: A) (b : B <: B′) (f : ⟦ A ⇒[ mk-kind Zero π ] B ⟧ᴰ) (u : ⊤)
       → liftFn fmt {(A ⇒[ mk-kind Zero π ] B) * Unit} {B′} (coeIR b ∘ apply) (f , u)
         ≡ fmapT ⟦ b ⟧<: (f u)
  arr₀ {A} {A′} {B} {B′} {π} a b f u =
    trans (cong (λ h → h (f , u)) (liftFn-∘ {B = B} {C = B′} {A = (A ⇒[ mk-kind Zero π ] B) * Unit} (coeIR b) apply))
      (trans (cong (_>>=T liftFn fmt {B} {B′} (coeIR b)) (cong (λ h → h (f , u)) (liftFn-apply₀ {A = A} {B = B} {π = π})))
        (trans (cong (f u >>=T_) (extensionality (coeIR-lift b))) (bind-ret (f u) ⟦ b ⟧<:)))

  arr₁ : ∀ {A A′ B B′ π} (a : A′ <: A) (b : B <: B′) (f : ⟦ A ⇒[ mk-kind One π ] B ⟧ᴰ) (x′ : ⟦ A′ ⟧ᴰ)
       → liftFn fmt {(A ⇒[ mk-kind One π ] B) * A′} {B′}
                (coeIR b ∘ (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩)) (f , x′)
         ≡ fmapT ⟦ b ⟧<: (f (⟦ a ⟧<: x′))
  arr₁ {A} {A′} {B} {B′} {π} a b f x′ =
    trans (cong (λ h → h (f , x′))
                (liftFn-∘ {B = B} {C = B′} {A = (A ⇒[ mk-kind One π ] B) * A′} (coeIR b) (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩)))
      (trans (cong (_>>=T liftFn fmt {B} {B′} (coeIR b)) body)
        (trans (cong (f (⟦ a ⟧<: x′) >>=T_) (extensionality (coeIR-lift b)))
               (bind-ret (f (⟦ a ⟧<: x′)) ⟦ b ⟧<:)))
    where
      AB = A ⇒[ mk-kind One π ] B
      arg : liftFn fmt {AB * A′} {A} (coeIR a ∘ snd) (f , x′) ≡ returnT (⟦ a ⟧<: x′)
      arg = trans (cong (λ h → h (f , x′)) (liftFn-∘ {B = A′} {C = A} {A = AB * A′} (coeIR a) snd))
                  (trans (cong (_>>=T liftFn fmt {A′} {A} (coeIR a)) (cong (λ h → h (f , x′)) (liftFn-snd {A = AB} {B = A′})))
                         (coeIR-lift a x′))
      pr : liftFn fmt {AB * A′} {AB * A} ⟨ fst , coeIR a ∘ snd ⟩ (f , x′) ≡ returnT (f , ⟦ a ⟧<: x′)
      pr = trans (cong (λ h → h (f , x′)) (liftFn-pair {A = AB * A′} {B = AB} {C = A} fst (coeIR a ∘ snd)))
                 (cong₂ (λ m₁ m₂ → m₁ >>=T (λ u → m₂ >>=T (λ w → returnT (u , w))))
                        (cong (λ h → h (f , x′)) (liftFn-fst {A = AB} {B = A′})) arg)
      body : liftFn fmt {AB * A′} {B} (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩) (f , x′) ≡ f (⟦ a ⟧<: x′)
      body = trans (cong (λ h → h (f , x′)) (liftFn-∘ {B = AB * A} {C = B} {A = AB * A′} apply ⟨ fst , coeIR a ∘ snd ⟩))
                   (trans (cong (_>>=T liftFn fmt {AB * A} {B} apply) pr)
                          (cong (λ h → h (f , ⟦ a ⟧<: x′)) (liftFn-apply₁ {A = A} {B = B} {π = π})))

  arrω : ∀ {A A′ B B′ π} (a : A′ <: A) (b : B <: B′) (f : ⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ) (x′ : ⟦ A′ ⟧ᴰ)
       → liftFn fmt {(A ⇒[ mk-kind Many π ] B) * A′} {B′}
                (coeIR b ∘ (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩)) (f , x′)
         ≡ fmapT ⟦ b ⟧<: (f (⟦ a ⟧<: x′))
  arrω {A} {A′} {B} {B′} {π} a b f x′ =
    trans (cong (λ h → h (f , x′))
                (liftFn-∘ {B = B} {C = B′} {A = (A ⇒[ mk-kind Many π ] B) * A′} (coeIR b) (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩)))
      (trans (cong (_>>=T liftFn fmt {B} {B′} (coeIR b)) body)
        (trans (cong (f (⟦ a ⟧<: x′) >>=T_) (extensionality (coeIR-lift b)))
               (bind-ret (f (⟦ a ⟧<: x′)) ⟦ b ⟧<:)))
    where
      AB = A ⇒[ mk-kind Many π ] B
      arg : liftFn fmt {AB * A′} {A} (coeIR a ∘ snd) (f , x′) ≡ returnT (⟦ a ⟧<: x′)
      arg = trans (cong (λ h → h (f , x′)) (liftFn-∘ {B = A′} {C = A} {A = AB * A′} (coeIR a) snd))
                  (trans (cong (_>>=T liftFn fmt {A′} {A} (coeIR a)) (cong (λ h → h (f , x′)) (liftFn-snd {A = AB} {B = A′})))
                         (coeIR-lift a x′))
      pr : liftFn fmt {AB * A′} {AB * A} ⟨ fst , coeIR a ∘ snd ⟩ (f , x′) ≡ returnT (f , ⟦ a ⟧<: x′)
      pr = trans (cong (λ h → h (f , x′)) (liftFn-pair {A = AB * A′} {B = AB} {C = A} fst (coeIR a ∘ snd)))
                 (cong₂ (λ m₁ m₂ → m₁ >>=T (λ u → m₂ >>=T (λ w → returnT (u , w))))
                        (cong (λ h → h (f , x′)) (liftFn-fst {A = AB} {B = A′})) arg)
      body : liftFn fmt {AB * A′} {B} (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩) (f , x′) ≡ f (⟦ a ⟧<: x′)
      body = trans (cong (λ h → h (f , x′)) (liftFn-∘ {B = AB * A} {C = B} {A = AB * A′} apply ⟨ fst , coeIR a ∘ snd ⟩))
                   (trans (cong (_>>=T liftFn fmt {AB * A} {B} apply) pr)
                          (cong (λ h → h (f , ⟦ a ⟧<: x′)) (liftFn-apply {A = A} {B = B} {π = π})))

------------------------------------------------------------------------
-- A void-free conversion is a transport.
------------------------------------------------------------------------

record VfSem {A B : Type} (p : A <: B) : Set₁ where
  field
    D  : ⟦ A ⟧ᴰ ≡ ⟦ B ⟧ᴰ
    pt : ∀ v → ⟦ p ⟧<: v ≡ subst id D v
open VfSem

vf-sem : ∀ {A B} (p : A <: B) → VoidFree p → VfSem p
vf-sem _ vf-void   = record { D = refl ; pt = λ () }
vf-sem _ vf-unit   = record { D = refl ; pt = λ _ → refl }
vf-sem _ vf-int    = record { D = refl ; pt = λ _ → refl }
vf-sem _ vf-float  = record { D = refl ; pt = λ _ → refl }
vf-sem _ vf-str    = record { D = refl ; pt = λ _ → refl }
vf-sem _ vf-buffer = record { D = refl ; pt = λ _ → refl }
vf-sem _ vf-μ      = record { D = refl ; pt = λ _ → refl }
vf-sem _ vf-ν      = record { D = refl ; pt = λ _ → refl }
vf-sem (sub-arr {q = Zero} a b _) (vf-arr va vb) =
  let sb = vf-sem b vb in
  record { D  = cong (λ V → ⊤ → T V) (D sb)
         ; pt = λ f → trans (extensionality λ u →
                               trans (fmapT-cong (pt sb) (f u)) (fmapT-subst (D sb) (f u)))
                            (sym (subst-arr₀ (D sb) f)) }
vf-sem (sub-arr {q = One} a b _) (vf-arr va vb) =
  let sa = vf-sem a va ; sb = vf-sem b vb in
  record { D  = cong₂ (λ U V → U → T V) (sym (D sa)) (D sb)
         ; pt = λ f → trans (extensionality λ x′ →
                               trans (fmapT-cong (pt sb) (f (⟦ a ⟧<: x′)))
                                 (trans (fmapT-subst (D sb) (f (⟦ a ⟧<: x′)))
                                        (cong (λ z → subst T (D sb) (f z))
                                              (trans (pt sa x′)
                                                     (cong (λ E → subst id E x′) (sym (sym-sym (D sa))))))))
                            (sym (subst-arr (sym (D sa)) (D sb) f)) }
vf-sem (sub-arr {q = Many} a b _) (vf-arr va vb) =
  let sa = vf-sem a va ; sb = vf-sem b vb in
  record { D  = cong₂ (λ U V → U → T V) (sym (D sa)) (D sb)
         ; pt = λ f → trans (extensionality λ x′ →
                               trans (fmapT-cong (pt sb) (f (⟦ a ⟧<: x′)))
                                 (trans (fmapT-subst (D sb) (f (⟦ a ⟧<: x′)))
                                        (cong (λ z → subst T (D sb) (f z))
                                              (trans (pt sa x′)
                                                     (cong (λ E → subst id E x′) (sym (sym-sym (D sa))))))))
                            (sym (subst-arr (sym (D sa)) (D sb) f)) }
vf-sem (sub-prod a b) (vf-prod va vb) =
  let sa = vf-sem a va ; sb = vf-sem b vb in
  record { D  = cong₂ _×_ (D sa) (D sb)
         ; pt = λ { (x , y) → trans (cong₂ _,_ (pt sa x) (pt sb y)) (sym (subst-pair (D sa) (D sb) x y)) } }
vf-sem (sub-sum a b) (vf-sum va vb) =
  let sa = vf-sem a va ; sb = vf-sem b vb in
  record { D  = cong₂ _⊎_ (D sa) (D sb)
         ; pt = λ { (inj₁ x) → trans (cong inj₁ (pt sa x)) (sym (subst-inj₁ (D sa) (D sb) x))
                  ; (inj₂ y) → trans (cong inj₂ (pt sb y)) (sym (subst-inj₂ (D sa) (D sb) y)) } }

coerce-lift-yes : ∀ {Δ A B} (p : A <: B) (vf : VoidFree p) (f : IR ⌊ Δ ⌋ ⌊ A ⌋) (x : ⟦ Δ ⟧ᴰ)
  → liftFn fmt {Δ} {B} (subst (IR ⌊ Δ ⌋) (erase-eq p vf) f) x ≡ fmapT ⟦ p ⟧<: (liftFn fmt {Δ} {A} f x)
coerce-lift-yes {Δ} {A} {B} p vf f x =
  trans (cong (subst T (cohᴰ B)) (eval-subst E f x₀))
    (trans (cong (subst T (cohᴰ B)) (subst-⟦⟧ E m))
      (trans (subst-T-∘ (cong ⟦_⟧ᴰᴵ E) (cohᴰ B) m)
        (trans (cong (λ Q → subst T Q m) (uip (trans (cong ⟦_⟧ᴰᴵ E) (cohᴰ B)) (trans (cohᴰ A) (D s))))
          (sym (trans (fmapT-cong (pt s) (subst T (cohᴰ A) m))
                 (trans (fmapT-subst (D s) (subst T (cohᴰ A) m))
                        (subst-T-∘ (cohᴰ A) (D s) m)))))))
  where
    E  = erase-eq p vf
    s  = vf-sem p vf
    x₀ = subst id (sym (cohᴰ Δ)) x
    m  = evalᴰ fmt f x₀

------------------------------------------------------------------------
-- The theorem.
------------------------------------------------------------------------

coerce-lift-dec : ∀ {Δ A B} (p : A <: B) (dv : Dec (VoidFree p)) (f : IR ⌊ Δ ⌋ ⌊ A ⌋) (x : ⟦ Δ ⟧ᴰ)
  → liftFn fmt {Δ} {B} (runCoe-dec p dv f) x ≡ fmapT ⟦ p ⟧<: (liftFn fmt {Δ} {A} f x)
coerce-lift-dec {Δ} p (yes vf) f x = coerce-lift-yes {Δ} p vf f x
coerce-lift-dec {Δ} {A} {B} p (no _) f x =
  trans (cong (λ h → h x) (liftFn-∘ {B = A} {C = B} {A = Δ} (coeIR p) f))
    (trans (cong (liftFn fmt {Δ} {A} f x >>=T_) (extensionality (coeIR-lift p)))
           (bind-ret (liftFn fmt {Δ} {A} f x) ⟦ p ⟧<:))

coerce-lift : ∀ {Δ A B} (p : A <: B) (f : IR ⌊ Δ ⌋ ⌊ A ⌋) (x : ⟦ Δ ⟧ᴰ)
  → liftFn fmt {Δ} {B} (runCoe p f) x ≡ fmapT ⟦ p ⟧<: (liftFn fmt {Δ} {A} f x)
coerce-lift {Δ} p f x = coerce-lift-dec {Δ} p (voidFree? p) f x
