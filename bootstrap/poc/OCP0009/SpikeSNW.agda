------------------------------------------------------------------------
-- OCP-0009 · W1b — CONVERSION TRANSFER for the SN⁺ logical relation,
--                  on the REAL kernel syntax.
--
-- `SpikeSNU` (W1a) established that the induction-recursion goes through, and
-- relocated the difficulty: `⊢conv` needs the FORWARD transfer
-- `A ⟶ᵀ B → ⊩ A → ⊩ B`, and inducting on `⊩` localised the obstruction to the
-- single `⊩red` constructor, where two reductions out of one type must be
-- JOINED.  It named type-level confluence as the precise missing input.
--
-- ★ FINDING: that input already exists.  `NbEPDirDBInj` (dHoTT-26) proves
-- `confluentᵀ`/`church-rosserᵀ` for `_⟶ᵀ_` on the real kernel syntax, together
-- with `Π-reduct` (Π-shape preservation) — built to derive Π-injectivity, never
-- used for reducibility.  So W1b is not a new confluence proof; it is the
-- REDESIGN that consumes the confluence already in hand.  This module is that.
--
-- TWO CHANGES FROM `SpikeSNU`, both forced:
--
--   1. THE REAL SYNTAX.  Everything here is over `NbEPDirDBPi`'s `RTy`/`RTm`
--      and `NbEPDirDBType`'s `_⟶_`/`_⟶ᵀ_`, so the confluence results apply
--      directly and nothing has to be re-proven.  The spike's standalone
--      syntax has done its job.
--
--   2. ★ THE WHNF-CARRYING SHAPE.  `SpikeSNU` closed `⊩` under type reduction
--      with a constructor `⊩red : A ⟶ᵀ B → ⊩ B → ⊩ A`.  That is the naive
--      design and it is exactly what makes forward transfer non-structural.
--      Here each constructor instead CARRIES ITS OWN REDUCTION TO WEAK HEAD
--      NORMAL FORM (`A ⟶ᵀ* base`, `A ⟶ᵀ* Π F G`, …).  Then transfer is a
--      confluence argument at the constructor and the recursion stays
--      structural.  Same information, different place — and the place is what
--      decides whether the proof closes.
--
-- DELIVERED, `--safe`, zero postulates, zero holes:
--   `⊩_`/`_⊩∋_`   the whnf-carrying logical relation over the real syntax
--   ★ `irrel`     IRRELEVANCE UP TO CONVERSION — `A ≅ᵀ B` ⇒ the two relations
--                 have the same members, in BOTH directions.  Stated as a
--                 bi-implication precisely so the `Π/Π` case's domain step can
--                 recurse on structurally smaller derivations on BOTH sides.
--   ★ `fwd*`      THE FORWARD TRANSFER, `A ⟶ᵀ* B → ⊩ A → ⊩ B` — W1b's target.
--   ★ `conv-⊩`    and hence transfer along full CONVERSION, `A ≅ᵀ B → ⊩ A → ⊩ B`,
--                 which is the shape `⊢conv` actually needs.
--   `CR1`/`CR2`/`CR3` re-proven over the new shape.
--
-- STILL OPEN (unchanged from `SpikeSNU` §8, minus (b)): the Kripke action
-- (`⊩`/`⊩∋` stable under renaming — needed for `fund`'s λ-case), `fund` itself,
-- and the Σ' cases (mechanical, per dHoTT-36).  `Σ'` is deliberately absent
-- from `⊩` here: it adds a fourth whnf shape and six more cross cases to
-- `irrel` without testing anything new.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeSNW where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; Σ; _,_; _×_; ⊥; ⊥-elim )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El
        ; RTm; var; lam; app; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; Sub; subTy; subTm; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( single
        ; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ )
open import poc.OCP0009.NbEPDirDBSR using ( ⟶ᵀ-sub; ≅ᵀ-sub )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans
        ; confluentᵀ; church-rosserᵀ
        ; ΠRed; mkΠRed; Π-reduct; Πinj≡; red→≅ᵀ )

private
  variable
    Γ Δ : Cx

-- `Σ`'s fields are named `fst`/`snd`, which are also `RTm` constructors here,
-- so the record is never opened; these are the projections used instead.
projl : {P Q : Set} → P × Q → P
projl (p , _) = p

projr : {P Q : Set} → P × Q → Q
projr (_ , q) = q

------------------------------------------------------------------------
-- 1. Strong normalization and neutrals, over the kernel's `RTm`.
------------------------------------------------------------------------

data SN {Γ} (t : RTm Γ) : Set where
  sn : (∀ {u} → t ⟶ u → SN u) → SN t

sn-red : {t u : RTm Γ} → SN t → t ⟶ u → SN u
sn-red (sn h) r = h r

sn-var : (x : Var Γ) → SN (var x)
sn-var x = sn (λ ())

data Ne {Γ} : RTm Γ → Set where
  ne-var : (x : Var Γ) → Ne (var x)
  ne-app : {t u : RTm Γ} → Ne t → Ne (app t u)
  ne-fst : {p : RTm Γ} → Ne p → Ne (fst p)
  ne-snd : {p : RTm Γ} → Ne p → Ne (snd p)

ne-red : {t t' : RTm Γ} → Ne t → t ⟶ t' → Ne t'
ne-red (ne-var x) ()
ne-red (ne-app n) (ξ-appˡ r) = ne-app (ne-red n r)
ne-red (ne-app n) (ξ-appʳ r) = ne-app n
ne-red (ne-fst n) (ξ-fst r)  = ne-fst (ne-red n r)
ne-red (ne-snd n) (ξ-snd r)  = ne-snd (ne-red n r)

-- A neutral applied to an SN argument stays SN. Lexicographic on the two `SN`s;
-- the `β` case is absent by COVERAGE — `Ne t` refines `t` away from `lam _`.
sn-app-ne      : {t u : RTm Γ} → Ne t → SN t → SN u → SN (app t u)
sn-app-ne-step : {t u w : RTm Γ} → Ne t → SN t → SN u → app t u ⟶ w → SN w

sn-app-ne nt st su = sn (sn-app-ne-step nt st su)

sn-app-ne-step (ne-var x) st      su      (ξ-appˡ ())
sn-app-ne-step (ne-var x) st      (sn hu) (ξ-appʳ r) = sn-app-ne (ne-var x) st (hu r)
sn-app-ne-step (ne-app n) (sn ht) su      (ξ-appˡ r) = sn-app-ne (ne-red (ne-app n) r) (ht r) su
sn-app-ne-step (ne-app n) st      (sn hu) (ξ-appʳ r) = sn-app-ne (ne-app n) st (hu r)
sn-app-ne-step (ne-fst n) (sn ht) su      (ξ-appˡ r) = sn-app-ne (ne-red (ne-fst n) r) (ht r) su
sn-app-ne-step (ne-fst n) st      (sn hu) (ξ-appʳ r) = sn-app-ne (ne-fst n) st (hu r)
sn-app-ne-step (ne-snd n) (sn ht) su      (ξ-appˡ r) = sn-app-ne (ne-red (ne-snd n) r) (ht r) su
sn-app-ne-step (ne-snd n) st      (sn hu) (ξ-appʳ r) = sn-app-ne (ne-snd n) st (hu r)

------------------------------------------------------------------------
-- 2. Weak-head-normal shapes are preserved by type reduction.
--
-- These are what turn a confluence witness into shape information, and they
-- are the reason the whnf-carrying design works: knowing `A ⟶ᵀ* base`, any
-- other reduct of `A` still reaches `base`.
------------------------------------------------------------------------

base-nf : {A : RTy Γ} → base {Γ} ⟶ᵀ* A → A ≡ base
base-nf doneᵀ        = refl
base-nf (stepᵀ () _)

U-nf : {A : RTy Γ} → U {Γ} ⟶ᵀ* A → A ≡ U
U-nf doneᵀ        = refl
U-nf (stepᵀ () _)

-- A reduct of a NEUTRAL `El`-type is again a neutral `El`-type: `El-⌜base⌝`
-- and `El-⌜Π⌝`/`El-⌜Σ⌝` all require the code to BE a constructor, and a
-- neutral is not one — so only `ξ-El` applies, and `ne-red` carries the
-- neutrality along.
record ElNe {Γ} (A : RTy Γ) : Set where
  constructor mkElNe
  field
    nf  : RTm Γ
    nfe : Ne nf
    nfq : A ≡ El nf

El-ne-reduct : {n : RTm Γ} {A : RTy Γ} → Ne n → El n ⟶ᵀ* A → ElNe A
El-ne-reduct {n = n} ne doneᵀ            = mkElNe n ne refl
El-ne-reduct         ne (stepᵀ (ξ-El r) p) = El-ne-reduct (ne-red ne r) p

-- Multi-step substitution stability, from `NbEPDirDBSR.⟶ᵀ-sub`.
⟶ᵀ*-sub : (σ : Sub Γ Δ) {A B : RTy Γ} → A ⟶ᵀ* B → subTy σ A ⟶ᵀ* subTy σ B
⟶ᵀ*-sub σ doneᵀ        = doneᵀ
⟶ᵀ*-sub σ (stepᵀ r p)  = stepᵀ (⟶ᵀ-sub σ r) (⟶ᵀ*-sub σ p)

-- ★ The workhorse: two convertible types' whnf witnesses MEET.  Three uses of
-- confluence — one to resolve the conversion, one per side to reconcile it
-- with that side's own reduction.
joinW : {A B W₁ W₂ : RTy Γ} → A ≅ᵀ B → A ⟶ᵀ* W₁ → B ⟶ᵀ* W₂ →
        Σ (RTy Γ) (λ E → (W₁ ⟶ᵀ* E) × (W₂ ⟶ᵀ* E))
joinW c p q with church-rosserᵀ c
... | C , (aC , bC) with confluentᵀ p aC | confluentᵀ q bC
...   | D₁ , (w₁D₁ , CD₁) | D₂ , (w₂D₂ , CD₂) with confluentᵀ CD₁ CD₂
...     | E , (D₁E , D₂E) =
          E , (⟶ᵀ*-trans w₁D₁ D₁E , ⟶ᵀ*-trans w₂D₂ D₂E)

------------------------------------------------------------------------
-- ★ 3. THE LOGICAL RELATION — whnf-carrying.
--
-- Compare `SpikeSNU`: there, `⊩red : A ⟶ᵀ B → ⊩ B → ⊩ A` closed the family
-- under reduction as a separate constructor.  Here every constructor carries
-- its own `A ⟶ᵀ* «whnf»` instead.  The information is the same; the difference
-- is that forward transfer now inspects ONE constructor and applies confluence
-- to its stored reduction, rather than having to join a reduction against an
-- unbounded stack of `⊩red`s.
------------------------------------------------------------------------

infix 4 _⊩∋_

data ⊩_ {Γ} : RTy Γ → Set
_⊩∋_ : {Γ : Cx} {A : RTy Γ} → ⊩ A → RTm Γ → Set

data ⊩_ {Γ} where
  ⊩base : {A : RTy Γ} → A ⟶ᵀ* base → ⊩ A
  ⊩U    : {A : RTy Γ} → A ⟶ᵀ* U → ⊩ A
  ⊩ne   : {A : RTy Γ} {n : RTm Γ} → A ⟶ᵀ* El n → Ne n → ⊩ A
  ⊩Π    : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
        → A ⟶ᵀ* Π F G
        → (⊩F : ⊩ F)
        → ((u : RTm Γ) → ⊩F ⊩∋ u → ⊩ (subTy (single u) G))
        → ⊩ A

⊩base _     ⊩∋ t = SN t
⊩U _        ⊩∋ t = SN t
⊩ne _ _     ⊩∋ t = SN t
⊩Π _ ⊩F ⊩G  ⊩∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩∋ u) → (⊩G u r) ⊩∋ app t u)

------------------------------------------------------------------------
-- ★ 4. IRRELEVANCE UP TO CONVERSION.
--
-- Stated as a BI-IMPLICATION on purpose.  The `Π/Π` case must convert a member
-- of the RIGHT domain into a member of the LEFT one before it can apply the
-- left family; a one-directional statement would need the recursive call with
-- its arguments swapped, and then neither argument position decreases.  With
-- both directions available, the domain step is `π₂` of a call whose arguments
-- are the two domains — each a strict subterm of its own side.
------------------------------------------------------------------------

irrel : {A B : RTy Γ} → A ≅ᵀ B → (R : ⊩ A) (S : ⊩ B) →
        ((t : RTm Γ) → R ⊩∋ t → S ⊩∋ t) × ((t : RTm Γ) → S ⊩∋ t → R ⊩∋ t)

-- Nine cases where both sides are non-`Π`: membership is `SN t` on both, so
-- the transfer is the identity and no shape reasoning is needed at all.
irrel c (⊩base _)  (⊩base _)  = (λ _ h → h) , (λ _ h → h)
irrel c (⊩base _)  (⊩U _)     = (λ _ h → h) , (λ _ h → h)
irrel c (⊩base _)  (⊩ne _ _)  = (λ _ h → h) , (λ _ h → h)
irrel c (⊩U _)     (⊩base _)  = (λ _ h → h) , (λ _ h → h)
irrel c (⊩U _)     (⊩U _)     = (λ _ h → h) , (λ _ h → h)
irrel c (⊩U _)     (⊩ne _ _)  = (λ _ h → h) , (λ _ h → h)
irrel c (⊩ne _ _)  (⊩base _)  = (λ _ h → h) , (λ _ h → h)
irrel c (⊩ne _ _)  (⊩U _)     = (λ _ h → h) , (λ _ h → h)
irrel c (⊩ne _ _)  (⊩ne _ _)  = (λ _ h → h) , (λ _ h → h)

-- Six cross cases: one side is `Π`, the other is not.  These are genuinely
-- impossible, and `joinW` + the shape lemmas say so — a `Π` and a `base`/`U`/
-- neutral-`El` cannot both be reached from a common reduct.
irrel c (⊩base p) (⊩Π q _ _) with joinW c p q
... | E , (bE , πE) with base-nf bE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel c (⊩U p) (⊩Π q _ _) with joinW c p q
... | E , (uE , πE) with U-nf uE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel c (⊩ne p ne) (⊩Π q _ _) with joinW c p q
... | E , (eE , πE) with El-ne-reduct ne eE
...   | mkElNe _ _ refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel c (⊩Π p _ _) (⊩base q) with joinW c p q
... | E , (πE , bE) with base-nf bE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel c (⊩Π p _ _) (⊩U q) with joinW c p q
... | E , (πE , uE) with U-nf uE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel c (⊩Π p _ _) (⊩ne q ne) with joinW c p q
... | E , (πE , eE) with El-ne-reduct ne eE
...   | mkElNe _ _ refl with Π-reduct πE
...     | mkΠRed _ _ () _ _

-- ★ The real case.  Both sides reduce to a `Π`; confluence forces the two
-- `Π`s to have convertible domain AND codomain, and then the two families are
-- interchangeable by recursion.
irrel c (⊩Π p ⊩F ⊩G) (⊩Π q ⊩F' ⊩G') with joinW c p q
... | E , (πE₁ , πE₂) with Π-reduct πE₁ | Π-reduct πE₂
...   | mkΠRed F₁ G₁ eq₁ rF₁ rG₁ | mkΠRed F₂ G₂ eq₂ rF₂ rG₂
        with Πinj≡ (trans (sym eq₁) eq₂)
...       | (refl , refl) =
            (λ t h → (projl h , λ u r' →
               projl (irrel (≅ᵀ-sub (single u)
                              (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                            (⊩G u (projr (irrel (ctrnᵀ (red→≅ᵀ rF₁)
                                                       (csymᵀ (red→≅ᵀ rF₂)))
                                                ⊩F ⊩F') u r'))
                            (⊩G' u r'))
                     (app t u)
                     (projr h u (projr (irrel (ctrnᵀ (red→≅ᵀ rF₁)
                                                     (csymᵀ (red→≅ᵀ rF₂)))
                                              ⊩F ⊩F') u r'))))
          , (λ t h → (projl h , λ u r →
               projr (irrel (≅ᵀ-sub (single u)
                              (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                            (⊩G u r)
                            (⊩G' u (projl (irrel (ctrnᵀ (red→≅ᵀ rF₁)
                                                        (csymᵀ (red→≅ᵀ rF₂)))
                                                 ⊩F ⊩F') u r)))
                     (app t u)
                     (projr h u (projl (irrel (ctrnᵀ (red→≅ᵀ rF₁)
                                                     (csymᵀ (red→≅ᵀ rF₂)))
                                              ⊩F ⊩F') u r))))

------------------------------------------------------------------------
-- ★ 5. THE FORWARD TRANSFER — W1b's target.
--
-- Each case is one appeal to confluence against the constructor's stored whnf
-- reduction, then a shape lemma.  Nothing is joined against an unbounded
-- structure, which is exactly what the redesign bought.
------------------------------------------------------------------------

fwd* : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩ A → ⊩ B

fwd* p (⊩base q) with confluentᵀ p q
... | E , (bE , baseE) with base-nf baseE
...   | refl = ⊩base bE

fwd* p (⊩U q) with confluentᵀ p q
... | E , (uE , UE) with U-nf UE
...   | refl = ⊩U uE

fwd* p (⊩ne q ne) with confluentᵀ p q
... | E , (bE , elE) with El-ne-reduct ne elE
...   | mkElNe n' ne' refl = ⊩ne bE ne'

fwd* p (⊩Π q ⊩F ⊩G) with confluentᵀ p q
... | E , (bE , πE) with Π-reduct πE
...   | mkΠRed F₁ G₁ refl rF rG =
        ⊩Π bE (fwd* rF ⊩F)
             (λ u r → fwd* (⟶ᵀ*-sub (single u) rG)
                           (⊩G u (projr (irrel (red→≅ᵀ rF) ⊩F (fwd* rF ⊩F)) u r)))

-- The BACKWARD transfer is free under the whnf-carrying design: prepending a
-- reduction to the stored one is all it takes.  (Under `SpikeSNU`'s `⊩red` it
-- was equally free — that direction was never the problem.)
bwd* : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩ B → ⊩ A
bwd* p (⊩base q)      = ⊩base (⟶ᵀ*-trans p q)
bwd* p (⊩U q)         = ⊩U    (⟶ᵀ*-trans p q)
bwd* p (⊩ne q ne)     = ⊩ne   (⟶ᵀ*-trans p q) ne
bwd* p (⊩Π q ⊩F ⊩G)   = ⊩Π    (⟶ᵀ*-trans p q) ⊩F ⊩G

-- ★ …and hence transfer along full CONVERSION, which is the shape `⊢conv`
-- needs: resolve `A ≅ᵀ B` to a common reduct by Church–Rosser, push forward
-- from `A`, pull back to `B`.
conv-⊩ : {A B : RTy Γ} → A ≅ᵀ B → ⊩ A → ⊩ B
conv-⊩ c R with church-rosserᵀ c
... | C , (aC , bC) = bwd* bC (fwd* aC R)

------------------------------------------------------------------------
-- 6. The candidate conditions, re-proven over the whnf-carrying shape.
------------------------------------------------------------------------

CR1 : {A : RTy Γ} (R : ⊩ A) {t : RTm Γ} → R ⊩∋ t → SN t
CR1 (⊩base _)  h = h
CR1 (⊩U _)     h = h
CR1 (⊩ne _ _)  h = h
CR1 (⊩Π _ _ _) h = projl h

CR2 : {A : RTy Γ} (R : ⊩ A) {t u : RTm Γ} → R ⊩∋ t → t ⟶ u → R ⊩∋ u
CR2 (⊩base _)      h r = sn-red h r
CR2 (⊩U _)         h r = sn-red h r
CR2 (⊩ne _ _)      h r = sn-red h r
CR2 (⊩Π _ ⊩F ⊩G)   h r =
  (sn-red (projl h) r , λ u ru → CR2 (⊩G u ru) (projr h u ru) (ξ-appˡ r))

CR3 : {A : RTy Γ} (R : ⊩ A) {t : RTm Γ} → Ne t → SN t → R ⊩∋ t
CR3 (⊩base _)     nt st = st
CR3 (⊩U _)        nt st = st
CR3 (⊩ne _ _)     nt st = st
CR3 (⊩Π _ ⊩F ⊩G)  nt st =
  (st , λ u ru → CR3 (⊩G u ru) (ne-app nt) (sn-app-ne nt st (CR1 ⊩F ru)))

-- Every semantic type is inhabited at every variable.
⊩var : {A : RTy Γ} (R : ⊩ A) (x : Var Γ) → R ⊩∋ var x
⊩var R x = CR3 R (ne-var x) (sn-var x)

------------------------------------------------------------------------
-- ★ 7. NON-VACUITY, and the transfer FIRING on the case that motivated it.
--
-- `⊩` is a predicate, so everything above would hold trivially if nothing
-- inhabited it.  These witnesses rule that out, and the last two show `fwd*`
-- and `conv-⊩` doing the thing `SpikeSNU`'s `⊩red` design could not: crossing
-- an `El`-DECODE step, where the semantic shape genuinely changes.
------------------------------------------------------------------------

-- a `Set₁` equality, for the "membership computes to THIS" witness below
infix 4 _≡ₛ_
data _≡ₛ_ (P : Set) : Set → Set where
  reflₛ : P ≡ₛ P

⊩El-base : ⊩ (El (⌜base⌝ {Γ}))
⊩El-base = ⊩base (stepᵀ El-⌜base⌝ doneᵀ)

-- The code that DECODES TO A FUNCTION TYPE — the configuration erasure cannot
-- see (`El (⌜Π⌝ ⌜base⌝ ⌜base⌝)` erases to `base`, its reduct to an arrow).
⊩El-Π : ⊩ (El (⌜Π⌝ (⌜base⌝ {Γ}) ⌜base⌝))
⊩El-Π = ⊩Π (stepᵀ (El-⌜Π⌝ ⌜base⌝ ⌜base⌝) doneᵀ) ⊩El-base (λ u r → ⊩El-base)

-- …and membership there computes to the FUNCTION-SPACE clause, by `refl`.
El-Π-computes : {t : RTm Γ} →
                (⊩El-Π ⊩∋ t) ≡ₛ (SN t × ((u : RTm Γ) → SN u → SN (app t u)))
El-Π-computes = reflₛ

-- ★ `fwd*` ACROSS THE DECODE STEP — the transfer W1b was blocked on.
fwd-decode : ⊩ (Π (El (⌜base⌝ {Γ})) (El ⌜base⌝))
fwd-decode = fwd* (stepᵀ (El-⌜Π⌝ ⌜base⌝ ⌜base⌝) doneᵀ) ⊩El-Π

-- ★ …and back again along CONVERSION, the direction `⊢conv` uses.
conv-decode : ⊩ (El (⌜Π⌝ (⌜base⌝ {Γ}) ⌜base⌝))
conv-decode = conv-⊩ (csymᵀ (credᵀ (El-⌜Π⌝ ⌜base⌝ ⌜base⌝))) fwd-decode
