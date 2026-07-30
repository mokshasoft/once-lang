------------------------------------------------------------------------
-- OCP-0009 · SPIKE for W1 (SN⁺) — the INDUCTION-RECURSION SHAPE, in isolation.
--
-- PLAN §6's mitigation for W1's top risk ("the IR does not go through Agda's
-- positivity checker") is: spike the shape BEFORE touching the kernel, the way
-- the SpikeCIR line did.  This is that spike.  It is deliberately NOT the
-- kernel: no Σ, no pairs, no typing judgment yet — only the pieces that decide
-- whether the construction is expressible AND usable:
--
--   (1) `Ty`/`Tm` MUTUAL, with `El : Tm Γ → Ty Γ` — types contain terms;
--   (2) `_⟶ᵀ_` with `ξ-El` — type reduction descends INTO the code term.  This
--       is the actual coupling (`NbEPDirDBType:79`) and the reason the erasure
--       shortcut is refuted (dHoTT-37's ceiling): `El` of a redex and of its
--       reduct erase to DIFFERENT simple types;
--   (3) `⊩_` — semantic types, an INDUCTIVE family over `Ty Γ`, closed under
--       type reduction (`⊩red`);
--   (4) `_⊩∋_` — membership, a function by RECURSION ON (3), used NEGATIVELY
--       inside (3)'s `⊩Π`, with the codomain index COMPUTED by substitution.
--
-- ★ RESULT — the shape goes through, and the candidate conditions with it.
--   `--safe`, ZERO postulates, ZERO holes.  Delivered here:
--     `⊩_`/`_⊩∋_`      the IR knot, ACCEPTED by positivity + termination
--     `El-Π-computes`  decoding really changes the semantic shape (`refl`)
--     `CR1`/`CR2`/`CR3` the three candidate conditions, all three proven
--   So W1's headline risk ("the IR does not go through") is RETIRED.
--
-- ⚠ WHAT THIS SPIKE DOES **NOT** SETTLE — stated precisely, because the risk
--   register should now name the real obstruction rather than the retired one.
--   See §8 at the bottom: the two open items are the KRIPKE action (needed for
--   `fund`'s λ-case) and CONVERSION TRANSFER (needed for `⊢conv`), and the
--   second is where the remaining difficulty actually lives.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeSNU where

------------------------------------------------------------------------
-- 0. Prelude — standalone, so the spike has nothing to re-check.
------------------------------------------------------------------------

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- A `Set₁`-level equality, for the "membership computes to THIS" witnesses in
-- §6: those equate two `Set`s, which do not fit the `Set`-level `_≡_`.
infix 4 _≡ₛ_
data _≡ₛ_ (P : Set) : Set → Set where
  reflₛ : P ≡ₛ P

infixr 4 _,_
infixr 2 _×_
record _×_ (P Q : Set) : Set where
  constructor _,_
  field π₁ : P
        π₂ : Q
open _×_

------------------------------------------------------------------------
-- 1. Syntax — de Bruijn, and MUTUAL: a type may contain a term (`El`).
------------------------------------------------------------------------

data Cx : Set where
  ε  : Cx
  _∙ : Cx → Cx

data Var : Cx → Set where
  vz : ∀ {Γ} → Var (Γ ∙)
  vs : ∀ {Γ} → Var Γ → Var (Γ ∙)

data Ty : Cx → Set
data Tm : Cx → Set

data Ty where
  base : ∀ {Γ} → Ty Γ
  U    : ∀ {Γ} → Ty Γ
  Π    : ∀ {Γ} → Ty Γ → Ty (Γ ∙) → Ty Γ
  El   : ∀ {Γ} → Tm Γ → Ty Γ          -- ★ types contain terms

data Tm where
  var    : ∀ {Γ} → Var Γ → Tm Γ
  lam    : ∀ {Γ} → Tm (Γ ∙) → Tm Γ
  app    : ∀ {Γ} → Tm Γ → Tm Γ → Tm Γ
  ⌜base⌝ : ∀ {Γ} → Tm Γ               -- codes are INERT: no eliminator
  ⌜Π⌝    : ∀ {Γ} → Tm Γ → Tm (Γ ∙) → Tm Γ

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- 2. Renaming and substitution (mirrors NbEPDirDBPi exactly, minus Σ).
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

renTy : Ren Γ Δ → Ty Γ → Ty Δ
renTm : Ren Γ Δ → Tm Γ → Tm Δ
renTy ρ base    = base
renTy ρ U       = U
renTy ρ (Π A B) = Π (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (El t)  = El (renTm ρ t)
renTm ρ (var x)   = var (ρ x)
renTm ρ (lam t)   = lam (renTm (extR ρ) t)
renTm ρ (app t u) = app (renTm ρ t) (renTm ρ u)
renTm ρ ⌜base⌝    = ⌜base⌝
renTm ρ (⌜Π⌝ c d) = ⌜Π⌝ (renTm ρ c) (renTm (extR ρ) d)

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → Tm Δ

extS : Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = renTm vs (σ x)

subTy : Sub Γ Δ → Ty Γ → Ty Δ
subTm : Sub Γ Δ → Tm Γ → Tm Δ
subTy σ base    = base
subTy σ U       = U
subTy σ (Π A B) = Π (subTy σ A) (subTy (extS σ) B)
subTy σ (El t)  = El (subTm σ t)
subTm σ (var x)   = σ x
subTm σ (lam t)   = lam (subTm (extS σ) t)
subTm σ (app t u) = app (subTm σ t) (subTm σ u)
subTm σ ⌜base⌝    = ⌜base⌝
subTm σ (⌜Π⌝ c d) = ⌜Π⌝ (subTm σ c) (subTm (extS σ) d)

single : Tm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x

------------------------------------------------------------------------
-- 3. Reduction — terms, then types.  `ξ-El` is THE coupling.
------------------------------------------------------------------------

infix 3 _⟶_
data _⟶_ {Γ} : Tm Γ → Tm Γ → Set where
  β      : (t : Tm (Γ ∙)) (u : Tm Γ) → app (lam t) u ⟶ subTm (single u) t
  ξ-lam  : {t t' : Tm (Γ ∙)} → t ⟶ t' → lam t ⟶ lam t'
  ξ-appˡ : {t t' u : Tm Γ} → t ⟶ t' → app t u ⟶ app t' u
  ξ-appʳ : {t u u' : Tm Γ} → u ⟶ u' → app t u ⟶ app t u'
  ξ-⌜Π⌝ˡ : {c c' : Tm Γ} {d : Tm (Γ ∙)} → c ⟶ c' → ⌜Π⌝ c d ⟶ ⌜Π⌝ c' d
  ξ-⌜Π⌝ʳ : {c : Tm Γ} {d d' : Tm (Γ ∙)} → d ⟶ d' → ⌜Π⌝ c d ⟶ ⌜Π⌝ c d'

infix 3 _⟶ᵀ_
data _⟶ᵀ_ {Γ} : Ty Γ → Ty Γ → Set where
  El-⌜base⌝ : El (⌜base⌝ {Γ}) ⟶ᵀ base
  El-⌜Π⌝    : (c : Tm Γ) (d : Tm (Γ ∙)) → El (⌜Π⌝ c d) ⟶ᵀ Π (El c) (El d)
  ξ-El      : {t t' : Tm Γ} → t ⟶ t' → El t ⟶ᵀ El t'   -- ★ THE COUPLING
  ξ-Πˡ      : {A A' : Ty Γ} {B : Ty (Γ ∙)} → A ⟶ᵀ A' → Π A B ⟶ᵀ Π A' B
  ξ-Πʳ      : {A : Ty Γ} {B B' : Ty (Γ ∙)} → B ⟶ᵀ B' → Π A B ⟶ᵀ Π A B'

------------------------------------------------------------------------
-- 4. Strong normalization + neutrals.
------------------------------------------------------------------------

data SN {Γ} (t : Tm Γ) : Set where
  sn : (∀ {u} → t ⟶ u → SN u) → SN t

sn-red : {t u : Tm Γ} → SN t → t ⟶ u → SN u
sn-red (sn h) r = h r

sn-var : (x : Var Γ) → SN (var x)
sn-var x = sn (λ ())

-- Neutral: head is a variable, so no top-level redex can ever appear.
data Ne {Γ} : Tm Γ → Set where
  ne-var : (x : Var Γ) → Ne (var x)
  ne-app : {t u : Tm Γ} → Ne t → Ne (app t u)

ne-red : {t t' : Tm Γ} → Ne t → t ⟶ t' → Ne t'
ne-red (ne-var x) ()
ne-red (ne-app n) (ξ-appˡ r) = ne-app (ne-red n r)
ne-red (ne-app n) (ξ-appʳ r) = ne-app n

-- A neutral applied to an SN argument stays SN. Lexicographic on (SN t, SN u);
-- the `β` case is absent by COVERAGE — `Ne t` refines `t` away from `lam _`.
sn-app-ne      : {t u : Tm Γ} → Ne t → SN t → SN u → SN (app t u)
sn-app-ne-step : {t u w : Tm Γ} → Ne t → SN t → SN u → app t u ⟶ w → SN w

sn-app-ne nt st su = sn (sn-app-ne-step nt st su)

sn-app-ne-step (ne-var x) st      su      (ξ-appˡ ())
sn-app-ne-step (ne-var x) st      (sn hu) (ξ-appʳ r) = sn-app-ne (ne-var x) st (hu r)
sn-app-ne-step (ne-app n) (sn ht) su      (ξ-appˡ r) = sn-app-ne (ne-red (ne-app n) r) (ht r) su
sn-app-ne-step (ne-app n) st      (sn hu) (ξ-appʳ r) = sn-app-ne (ne-app n) st (hu r)

------------------------------------------------------------------------
-- ★ 5. THE PROBE — the inductive-recursive logical relation.
--
--   `⊩ A`    — "A is a semantic type", an inductive family over `Ty Γ`;
--   `R ⊩∋ t` — membership, BY RECURSION ON the `⊩`-derivation `R`.
--
-- Three things tested at once:
--   * `⊩Π`'s second field mentions `⊩∋` NEGATIVELY (left of an arrow) while
--     `⊩∋` recurses on `⊩` — Dybjer's IR knot;
--   * its codomain index is `subTy (single u) B`, a COMPUTED index depending on
--     the very `u` bound by the field — no textbook precedent for this here;
--   * `⊩red` closes `⊩` under type reduction, which is how `El (⌜Π⌝ c d)`
--     becomes reducible: it steps to `Π (El c) (El d)`.  Because `⊩red` is a
--     DATA constructor, an inhabitant of `⊩ A` already carries a FINITE
--     decoding derivation — the termination of `El`-decoding is encoded in the
--     evidence, not assumed as a side theorem.
--
-- Design note: the `Π` clause carries `SN t` as an explicit conjunct.  That is
-- what lets CR1 hold at `Π` WITHOUT applying `t` to a fresh variable — the
-- move that would otherwise force the Kripke machinery up front.  It costs one
-- extra obligation in `red-lam` (not in this spike) and buys a self-contained
-- candidate-condition layer.
------------------------------------------------------------------------

infix 4 _⊩∋_

data ⊩_ {Γ} : Ty Γ → Set
_⊩∋_ : {Γ : Cx} {A : Ty Γ} → ⊩ A → Tm Γ → Set

data ⊩_ {Γ} where
  ⊩base : ⊩ (base {Γ})
  ⊩U    : ⊩ (U {Γ})
  -- a NEUTRAL code gives an inert type: nothing to decode, behaves like `base`
  ⊩ne   : {n : Tm Γ} → Ne n → ⊩ (El n)
  -- ★ the knot
  ⊩Π    : {A : Ty Γ} {B : Ty (Γ ∙)}
        → (⊩A : ⊩ A)
        → ((u : Tm Γ) → ⊩A ⊩∋ u → ⊩ (subTy (single u) B))
        → ⊩ (Π A B)
  -- ★ closure under type reduction — how `El`-decoding is absorbed
  ⊩red  : {A B : Ty Γ} → A ⟶ᵀ B → ⊩ B → ⊩ A

⊩base     ⊩∋ t = SN t
⊩U        ⊩∋ t = SN t
⊩ne _     ⊩∋ t = SN t
⊩Π ⊩A ⊩B  ⊩∋ t = SN t × ((u : Tm _) (r : ⊩A ⊩∋ u) → (⊩B u r) ⊩∋ app t u)
⊩red _ ⊩B ⊩∋ t = ⊩B ⊩∋ t

------------------------------------------------------------------------
-- 6. The probe FIRES: the shape is not merely accepted, it COMPUTES.
------------------------------------------------------------------------

-- `El ⌜base⌝` is a semantic type, via one decoding step.
⊩El-base : ⊩ (El (⌜base⌝ {Γ}))
⊩El-base = ⊩red El-⌜base⌝ ⊩base

-- ...and membership there reduces, on the nose, to the one at `base`.
El-base-computes : {t : Tm Γ} → (⊩El-base ⊩∋ t) ≡ₛ SN t
El-base-computes = reflₛ

-- ★ A code that DECODES TO A FUNCTION TYPE.  This is exactly the configuration
-- the erasure shortcut cannot see: `El (⌜Π⌝ ⌜base⌝ ⌜base⌝)` erases to `base`,
-- while its reduct `Π (El ⌜base⌝) (El ⌜base⌝)` erases to an arrow.
⊩El-Π : ⊩ (El (⌜Π⌝ (⌜base⌝ {Γ}) ⌜base⌝))
⊩El-Π = ⊩red (El-⌜Π⌝ ⌜base⌝ ⌜base⌝) (⊩Π ⊩El-base (λ u r → ⊩El-base))

-- ★ and membership AT that type computes to the function-space clause — the
-- decoding genuinely changed the semantic shape, by `refl`.
El-Π-computes : {t : Tm Γ} →
                (⊩El-Π ⊩∋ t) ≡ₛ (SN t × ((u : Tm Γ) → SN u → SN (app t u)))
El-Π-computes = reflₛ

-- The neutral-code case: a variable of type `U` gives an inert semantic type.
⊩El-ne : ⊩ (El (var (vz {Γ})))
⊩El-ne = ⊩ne (ne-var vz)

------------------------------------------------------------------------
-- ★ 7. THE CANDIDATE CONDITIONS — CR1/CR2/CR3, all three, by recursion on `⊩`.
--
-- This is where the IR is CONSUMED, so it tests that the recursion is usable
-- and not merely well-formed.  Note `⊩B u r` recursing under a CONSTRUCTOR'S
-- FUNCTION FIELD (the W-type pattern `f x < sup f`) — the second thing that had
-- to hold for the shape to be workable.
------------------------------------------------------------------------

-- CR1 — members are strongly normalizing.
CR1 : {A : Ty Γ} (R : ⊩ A) {t : Tm Γ} → R ⊩∋ t → SN t
CR1 ⊩base      h = h
CR1 ⊩U         h = h
CR1 (⊩ne _)    h = h
CR1 (⊩Π _ _)   h = π₁ h
CR1 (⊩red _ R) h = CR1 R h

-- CR2 — membership is closed under reduction.
CR2 : {A : Ty Γ} (R : ⊩ A) {t u : Tm Γ} → R ⊩∋ t → t ⟶ u → R ⊩∋ u
CR2 ⊩base      h r = sn-red h r
CR2 ⊩U         h r = sn-red h r
CR2 (⊩ne _)    h r = sn-red h r
CR2 (⊩red _ R) h r = CR2 R h r
CR2 (⊩Π ⊩A ⊩B) h r =
  (sn-red (π₁ h) r , λ u ru → CR2 (⊩B u ru) (π₂ h u ru) (ξ-appˡ r))

-- CR3 — neutral SN terms are members (the "inhabited candidate" condition).
CR3 : {A : Ty Γ} (R : ⊩ A) {t : Tm Γ} → Ne t → SN t → R ⊩∋ t
CR3 ⊩base      nt st = st
CR3 ⊩U         nt st = st
CR3 (⊩ne _)    nt st = st
CR3 (⊩red _ R) nt st = CR3 R nt st
CR3 (⊩Π ⊩A ⊩B) {t} nt st =
  (st , λ u ru → CR3 (⊩B u ru) (ne-app nt) (sn-app-ne nt st (CR1 ⊩A ru)))

-- Every semantic type is INHABITED at every variable — the corollary that makes
-- CR3 usable in `fund`'s λ-case, and the reason CR1 at `Π` did not need it.
⊩var : {A : Ty Γ} (R : ⊩ A) (x : Var Γ) → R ⊩∋ var x
⊩var R x = CR3 R (ne-var x) (sn-var x)

------------------------------------------------------------------------
-- 7b. LOCALISING THE REMAINING OBSTRUCTION — machine-checked, not asserted.
--
-- `⊢conv` needs the FORWARD transfer `A ⟶ᵀ B → ⊩ A → ⊩ B` (`⊩red` is only the
-- backward direction).  Rather than claim in prose which cases work, here are
-- the ones that do, as Agda; §8 then names the single one that does not.
------------------------------------------------------------------------

-- `base` and `U` are irreducible — vacuous.
fwd-base : {B : Ty Γ} → base {Γ} ⟶ᵀ B → ⊩ B
fwd-base ()

fwd-U : {B : Ty Γ} → U {Γ} ⟶ᵀ B → ⊩ B
fwd-U ()

-- ★ the `⊩ne` case: a reduction out of a NEUTRAL El-type can only be `ξ-El`,
-- because `El-⌜base⌝`/`El-⌜Π⌝` require the code to BE a constructor and a
-- neutral is not.  So the semantic type is rebuilt directly, no joining needed.
fwd-ne : {n : Tm Γ} {B : Ty Γ} → Ne n → El n ⟶ᵀ B → ⊩ B
fwd-ne (ne-var x) (ξ-El ())
fwd-ne (ne-app m) (ξ-El r) = ⊩ne (ne-red (ne-app m) r)

-- ★ THE CRITICAL PAIR — the non-determinism that makes the `⊩red` case need
-- confluence, together with a witness that it JOINS.  `El (⌜Π⌝ c d)` steps two
-- genuinely different ways, and both meet at `Π (El c') (El d)`:
--
--         El (⌜Π⌝ c d)
--        decode ↙      ↘ ξ-El (reduce in the code)
--   Π (El c) (El d)     El (⌜Π⌝ c' d)
--        ξ-Πˡ ↘        ↙ decode
--         Π (El c') (El d)
--
-- This is the evidence that lifting `NbEPDirDBConf.church-rosser` from `_⟶_` to
-- `_⟶ᵀ_` is a tractable job rather than a new research problem.
critical-pair-joins :
  {c c' : Tm Γ} {d : Tm (Γ ∙)} → c ⟶ c' →
    (El (⌜Π⌝ c d) ⟶ᵀ Π (El c) (El d))        -- left:  decode
  × (El (⌜Π⌝ c d) ⟶ᵀ El (⌜Π⌝ c' d))          -- right: reduce inside the code
  × (Π (El c) (El d) ⟶ᵀ Π (El c') (El d))    -- left joins...
  × (El (⌜Π⌝ c' d) ⟶ᵀ Π (El c') (El d))      -- ...and right joins, same target
critical-pair-joins {c = c} {c'} {d} r =
  (El-⌜Π⌝ c d , ξ-El (ξ-⌜Π⌝ˡ r) , ξ-Πˡ (ξ-El r) , El-⌜Π⌝ c' d)

------------------------------------------------------------------------
-- 8. WHAT REMAINS — the honest ceiling, so the risk register can be updated.
--
-- RETIRED by this spike: "the induction-recursion does not go through Agda's
-- positivity checker" (PLAN §6, W1's top risk, rated HIGH).  It goes through,
-- indexed over dependent syntax, with a substitution-computed index, and the
-- three candidate conditions are provable over it with no postulates.
--
-- STILL OPEN, in the order they will bite:
--
--   (a) THE KRIPKE ACTION.  `fund`'s λ-case needs `⊩` and `⊩∋` stable under
--       renaming: `⊩ A → ⊩ (renTy ρ A)` together with `R ⊩∋ t → renᵈ ρ R ⊩∋
--       renTm ρ t`.  Both must be defined MUTUALLY with each other and land
--       inside the same recursion — mechanical but bulky, and it is what forces
--       `⊩Π`'s function field to quantify over future contexts rather than just
--       `Tm Γ`.  Medium risk: the shape is standard, the bulk is real.
--
--   (b) ★ CONVERSION TRANSFER — the real remaining difficulty, and it is NOT
--       what the plan currently names.  `⊢conv` needs the FORWARD transfer
--             fwd : A ⟶ᵀ B → ⊩ A → ⊩ B
--       (`⊩red` is only the backward direction).  Working the induction on `⊩`
--       localises the obstruction EXACTLY.  Marking what is MACHINE-CHECKED
--       here (§7b) versus what is analysis:
--
--         ⊩base / ⊩U   ✓ CHECKED (`fwd-base`/`fwd-U`) — vacuous, no reduct.
--         ⊩ne n        ✓ CHECKED (`fwd-ne`) — `El n ⟶ᵀ B` with `Ne n` forces
--                        `ξ-El`, because `El-⌜base⌝`/`El-⌜Π⌝` need the code to
--                        BE a constructor and a neutral is not.
--         ⊩Π           ~ ANALYSIS ONLY, not written here: it needs two further
--                        lemmas first — `ξ-Πˡ` wants membership INVARIANT under
--                        `fwd` at the domain (⊩-irrelevance, a mutual
--                        companion), `ξ-Πʳ` wants `_⟶ᵀ_` substitution-stable.
--                        Both look routine; neither is claimed until written.
--         ⊩red r' R    ✗ ★ THE ONE CASE THAT CANNOT CLOSE STRUCTURALLY.  Two
--                        reductions leave the same type — `r' : A ⟶ᵀ C` carried
--                        by the evidence, and the given `r : A ⟶ᵀ B` — and they
--                        must be JOINED.  No induction on `⊩` does that.
--
--       And the pair is genuinely non-deterministic, so it cannot be dodged by
--       orienting the relation: `El (⌜Π⌝ c d)` steps BOTH by `El-⌜Π⌝` (decode)
--       and by `ξ-El` (reduce inside the code).
--
--       ⇒ **Type-level confluence is the precise missing input, and it is the
--       ONLY missing input for transfer.**  Concretely: lift
--       `NbEPDirDBConf.church-rosser` from `_⟶_` to `_⟶ᵀ_`.  The critical pairs
--       are few and they do join — `El (⌜Π⌝ c d)` decoding vs. reducing inside
--       the code closes as `Π (El c) (El d) ⟶ᵀ Π (El c') (El d)` against
--       `El (⌜Π⌝ c' d) ⟶ᵀ Π (El c') (El d)` — and every remaining overlap
--       bottoms out in TERM confluence, which is already proven.
--
--       Note what this changes about the shape of W1: it is CONFLUENCE work,
--       not reducibility work — a different technique from everything in
--       dHoTT-35/36/37, but the same technique as dHoTT-25, which is already
--       done for terms.  That is a much better position than "research-scale
--       induction-recursion".
--
--   (c) The fundamental theorem itself (`fund`), then Σ/pairs (mechanical, per
--       dHoTT-36's template), then the port onto `NbEPDirDBPi`'s real syntax.
--
-- Method note (the raw-M3c lesson): (b) is the item to build BEFORE (a) or (c).
-- If type-level confluence does not lift cleanly the shape of the whole proof
-- changes, and discovering that after building the Kripke layer would waste it.
------------------------------------------------------------------------
