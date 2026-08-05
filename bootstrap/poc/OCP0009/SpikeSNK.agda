------------------------------------------------------------------------
-- OCP-0009 · W1e — `fund` is NOT assembly.  Two findings, both machine-checked:
--   the relation is not total over `RTy`, and it MUST BE STRATIFIED BY LEVEL.
--
-- W1d closed the last lemma (`exp`, via Joachimski–Matthes) and the plan booked
-- W1e as assembly — every case having its lemma.  Trying to write `fund`
-- exposes two design facts that were never checked.  Both are about the
-- universe, and the second is the reason `logrel-mltt`-style developments index
-- their logical relation by a universe level rather than doing what W1a–W1d did.
--
-- ★ FINDING 1 — `⊩` IS NOT TOTAL OVER `RTy` (§1, `¬⊩elLam`).
--   `El (lam (var vz))` is a NORMAL type — `El-⌜base⌝`/`El-⌜Π⌝`/`El-⌜Σ⌝` need the
--   code to BE a constructor and `ξ-El` needs it to step, but `lam (var vz)` is
--   normal — whose code is not neutral either.  No constructor of `⊩` applies.
--
--   Why that breaks `fund`: `⊢lam : (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Π A B` puts NO
--   condition on `A`, and the kernel has no `Γ ⊢ A type` judgment at all
--   (verified: `NbEPDirDBType` has none).  So `fund` can neither produce
--   `⊩ (subTy σ A)` nor take it as input — `⊢app` would need one for `Π A B`
--   before it has it.  `fund` needs a type-formation judgment, mutual with
--   itself.  ⚠ That is a statement about the KERNEL, not just the proof: see §6.
--
-- ★ FINDING 2 — THE OBVIOUS FIX IS REJECTED, AND STRATIFICATION IS FORCED.
--   Finding 1's type-formation judgment has `ty-El : Γ ⊢ c ∷ U → Γ ⊢ty El c`,
--   whose semantic obligation is `⊩ (El c[σ])` from the semantics of `U`.  Under
--   W1d's LR that semantics is just `SN c[σ]`, which cannot give it (§1 is the
--   counterexample: `SN (lam (var vz))` holds, `⊩ (El (lam (var vz)))` is false).
--   So the `U` clause has to carry it — `⊩U _ ⊩∋ t = SN t × ⊩ (El t)`.
--
--   ⚠ **That is REJECTED, and I checked it rather than assuming:**
--
--       NotStrictlyPositive
--       ⊩_ is not strictly positive, because it occurs
--         in the second argument of _×_ in the second clause
--         in the definition of _⊩∋_, which occurs
--         to the left of an arrow in the type of the constructor ⊩Π
--
--   `⊩Π`'s function field puts `⊩∋` NEGATIVELY, and a `⊩` in `⊩∋`'s result then
--   makes `⊩` occur negatively in its own definition.  The two knots — W1a's
--   (`⊩∋` inside `⊩Π`) and this one (`⊩` inside `⊩∋`) — are individually fine
--   and together are not.
--
--   ⇒ **The relation must be STRATIFIED BY UNIVERSE LEVEL** (§3), which is
--   exactly what `logrel-mltt` does and what W1a–W1d had no reason to discover.
--   It works here because the kernel's universe is PREDICATIVE — the codes are
--   `⌜base⌝`/`⌜Π⌝`/`⌜Σ⌝` with **no code for `U` itself** — so two levels suffice
--   and no cycle appears.  This is dHoTT-37's `snEl` observation ("`El (⌜Π⌝ c d)`
--   decodes over strictly SMALLER codes") cashed out as a stratification of the
--   logical relation rather than of a termination measure.
--
-- DELIVERED, `--safe`, zero postulates, zero holes:
--   ★ `¬⊩elLam`            finding 1, machine-checked
--   ★ `⊩₀_`/`⊩₁_`          the STRATIFIED relation — small types (no `U`) and
--                          large types, with `⊩₁U`'s membership carrying `⊩₀`
--   `CR1₁`/`CR3₁`/`exp₁`   the candidate layer at the large level
--   ★ `sem-El`             the `ty-El` obligation: ONE PROJECTION, level 1 → 0
--   `sem-⌜base⌝`           the matching introduction
--   `sem-lam`/`sem-app`    unchanged in substance from `SpikeSNJ`
--
-- ⚠ CONSOLIDATION IS NOW DUE.  This is the fourth declaration of the relation
--   (SNW over accessibility-SN, SNJ over inductive-SN, and the two levels here).
--   Keeping the spikes separate was right while the shape was still moving; it
--   has now stopped.  W1f should merge them and port `SpikeSNW`'s
--   `irrel`/`fwd*`/`conv-⊩` in ONCE, at both levels.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeSNK where

open import normalizer.Syntax.Types
  using ( _≡_; refl; ¬_; ⊥; ⊥-elim; Σ; _,_; _×_ )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El
        ; RTm; var; lam; app; pair; fst; snd; absurd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; Sub; subTy; subTm; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( single
        ; _⟶_; β; ξ-lam; ξ-appˡ; ξ-appʳ
        ; _⟶*_; done; step
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; ξ-El; ξ-Πˡ; ξ-Πʳ )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El )
open import poc.OCP0009.SpikeSNW using ( projl; projr )
open import poc.OCP0009.SpikeSNJ
  using ( SNe; sne-var; sne-app; sne-fst; sne-snd
        ; SN; sn-ne; sn-lam; sn-pair; sn-cb; sn-cΠ; sn-cΣ; sn-exp
        ; SNRed; snr-β; snr-app; snr-fst; snr-snd
        ; snr→⟶ )
open import poc.OCP0009.SpikeSNJ as J using ( )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- ★ 1. FINDING 1 — the relation is not total over `RTy`.
--
-- The witness is a type whose code is a NORMAL NON-NEUTRAL term: stuck forever
-- (it will never decode, its code not being a constructor) and not neutral
-- (its code not being variable-headed).  The kernel's syntax permits it because
-- `RTy`'s `El` takes an arbitrary `RTm`.
------------------------------------------------------------------------

elLam : RTy (ε ∙)
elLam = El (lam (var vz))

elLam-nf : {X : RTy (ε ∙)} → elLam ⟶ᵀ* X → X ≡ elLam
elLam-nf doneᵀ                      = refl
elLam-nf (stepᵀ (ξ-El (ξ-lam ())) _)

-- Stated against `SpikeSNJ`'s relation — the one W1d actually built.
¬⊩elLam : ¬ (J.⊩ elLam)
¬⊩elLam (J.⊩base p)  with elLam-nf p
... | ()
¬⊩elLam (J.⊩U p)     with elLam-nf p
... | ()
¬⊩elLam (J.⊩Π p _ _) with elLam-nf p
... | ()
¬⊩elLam (J.⊩ne p n)  with elLam-nf p
¬⊩elLam (J.⊩ne p ()) | refl

------------------------------------------------------------------------
-- ★ 2. LEVEL 0 — SMALL types: the decodings of codes.  NO `U`.
--
-- This is the layer `⊩₁U`'s membership will point at.  Because the kernel's
-- codes are `⌜base⌝`/`⌜Π⌝`/`⌜Σ⌝` and there is **no code for `U`**, nothing at
-- this level ever needs to mention the universe — which is precisely why the
-- stratification terminates at two levels and no cycle reappears.
------------------------------------------------------------------------

infix 4 _⊩₀∋_

data ⊩₀_ {Γ} : RTy Γ → Set
_⊩₀∋_ : {Γ : Cx} {A : RTy Γ} → ⊩₀ A → RTm Γ → Set

data ⊩₀_ {Γ} where
  ⊩₀base : {A : RTy Γ} → A ⟶ᵀ* base → ⊩₀ A
  ⊩₀ne   : {A : RTy Γ} {n : RTm Γ} → A ⟶ᵀ* El n → SNe n → ⊩₀ A
  ⊩₀Π    : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
         → A ⟶ᵀ* Π F G
         → (⊩F : ⊩₀ F)
         → ((u : RTm Γ) → ⊩F ⊩₀∋ u → ⊩₀ (subTy (single u) G))
         → ⊩₀ A

⊩₀base _     ⊩₀∋ t = SN t
⊩₀ne _ _     ⊩₀∋ t = SN t
⊩₀Π _ ⊩F ⊩G  ⊩₀∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ app t u)

bwd₀ : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩₀ B → ⊩₀ A
bwd₀ p (⊩₀base q)    = ⊩₀base (⟶ᵀ*-trans p q)
bwd₀ p (⊩₀ne q n)    = ⊩₀ne   (⟶ᵀ*-trans p q) n
bwd₀ p (⊩₀Π q ⊩F ⊩G) = ⊩₀Π    (⟶ᵀ*-trans p q) ⊩F ⊩G

------------------------------------------------------------------------
-- ★ 3. LEVEL 1 — LARGE types, and the `U` clause that CARRIES REDUCIBILITY.
--
--     ⊩₁U _ ⊩₁∋ t = SN t × (⊩₀ (El t))
--
-- `⊩₀` is fully defined above, so it is a CLOSED type here, not a recursive
-- occurrence — the positivity failure of §Finding-2 does not arise.  This is
-- the whole content of the stratification.
------------------------------------------------------------------------

infix 4 _⊩₁∋_

data ⊩₁_ {Γ} : RTy Γ → Set
_⊩₁∋_ : {Γ : Cx} {A : RTy Γ} → ⊩₁ A → RTm Γ → Set

data ⊩₁_ {Γ} where
  ⊩₁base : {A : RTy Γ} → A ⟶ᵀ* base → ⊩₁ A
  ⊩₁U    : {A : RTy Γ} → A ⟶ᵀ* U → ⊩₁ A
  ⊩₁ne   : {A : RTy Γ} {n : RTm Γ} → A ⟶ᵀ* El n → SNe n → ⊩₁ A
  ⊩₁Π    : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
         → A ⟶ᵀ* Π F G
         → (⊩F : ⊩₁ F)
         → ((u : RTm Γ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) G))
         → ⊩₁ A

⊩₁base _     ⊩₁∋ t = SN t
⊩₁U _        ⊩₁∋ t = SN t × (⊩₀ (El t))     -- ★ the point of the stratification
⊩₁ne _ _     ⊩₁∋ t = SN t
⊩₁Π _ ⊩F ⊩G  ⊩₁∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩₁∋ u) → (⊩G u r) ⊩₁∋ app t u)

------------------------------------------------------------------------
-- 4. The candidate layer at level 1.  Each `U` case's SECOND component is
--    discharged by exactly one level-0 construction.
------------------------------------------------------------------------

CR1₁ : {A : RTy Γ} (R : ⊩₁ A) {t : RTm Γ} → R ⊩₁∋ t → SN t
CR1₁ (⊩₁base _)  h = h
CR1₁ (⊩₁U _)     h = projl h
CR1₁ (⊩₁ne _ _)  h = h
CR1₁ (⊩₁Π _ _ _) h = projl h

CR3₁ : {A : RTy Γ} (R : ⊩₁ A) {t : RTm Γ} → SNe t → R ⊩₁∋ t
CR3₁ (⊩₁base _)     nt = sn-ne nt
CR3₁ (⊩₁U _)        nt = (sn-ne nt , ⊩₀ne doneᵀ nt)   -- a neutral code ⇒ neutral type
CR3₁ (⊩₁ne _ _)     nt = sn-ne nt
CR3₁ (⊩₁Π _ ⊩F ⊩G)  nt =
  (sn-ne nt , λ u ru → CR3₁ (⊩G u ru) (sne-app nt (CR1₁ ⊩F ru)))

⊩var₁ : {A : RTy Γ} (R : ⊩₁ A) (x : Var Γ) → R ⊩₁∋ var x
⊩var₁ R x = CR3₁ R (sne-var x)

exp₁ : {A : RTy Γ} (R : ⊩₁ A) {t t' : RTm Γ} → SNRed t t' → R ⊩₁∋ t' → R ⊩₁∋ t
exp₁ (⊩₁base _)    r h = sn-exp r h
exp₁ (⊩₁ne _ _)    r h = sn-exp r h
exp₁ (⊩₁U _)       r h =
  -- the decoded type travels BACKWARD along the code's step
  (sn-exp r (projl h) , bwd₀ (⟶ᵀ*-El (step (snr→⟶ r) done)) (projr h))
exp₁ (⊩₁Π _ ⊩F ⊩G) r h =
  (sn-exp r (projl h) , λ v rv → exp₁ (⊩G v rv) (snr-app r) (projr h v rv))

------------------------------------------------------------------------
-- ★ 5. THE PAYOFF — `ty-El` is one projection, ACROSS THE LEVELS.
------------------------------------------------------------------------

-- The `ty-El` obligation: a code inhabiting `U` at level 1 yields its decoded
-- type as a level-0 semantic type.
sem-El : {A : RTy Γ} (p : A ⟶ᵀ* U) {c : RTm Γ} → (⊩₁U p) ⊩₁∋ c → ⊩₀ (El c)
sem-El p h = projr h

-- …and the matching introduction: `⌜base⌝` inhabits `U`, decoding in one step.
sem-⌜base⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) → (⊩₁U p) ⊩₁∋ ⌜base⌝
sem-⌜base⌝ p = (sn-cb , ⊩₀base (stepᵀ El-⌜base⌝ doneᵀ))

-- ★ and the PREDICATIVITY payoff, `⌜Π⌝`: the decoding of a compound code is a
-- level-0 `Π` built from the decodings of its STRICTLY SMALLER components.
-- This is dHoTT-37's `snEl` observation, now doing structural work.
sem-⌜Π⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) {c : RTm Γ} {d : RTm (Γ ∙)}
        → SN c → SN d
        → (⊩c : ⊩₀ (El c))
        → ((u : RTm Γ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) d)))
        → (⊩₁U p) ⊩₁∋ ⌜Π⌝ c d
sem-⌜Π⌝ p snc snD ⊩c f =
  (sn-cΠ snc snD , ⊩₀Π (stepᵀ (El-⌜Π⌝ _ _) doneᵀ) ⊩c f)

-- Π intro/elim at level 1, unchanged in substance from `SpikeSNJ`.
sem-lam : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
          (p : A ⟶ᵀ* Π F G) (⊩F : ⊩₁ F)
          (⊩G : (u : RTm Γ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) G))
          {s : RTm (Γ ∙)} → SN s →
          ((u : RTm Γ) (r : ⊩F ⊩₁∋ u) → (⊩G u r) ⊩₁∋ subTm (single u) s) →
          (⊩₁Π p ⊩F ⊩G) ⊩₁∋ lam s
sem-lam p ⊩F ⊩G sns f =
  (sn-lam sns , λ u r → exp₁ (⊩G u r) (snr-β (CR1₁ ⊩F r)) (f u r))

sem-app : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
          (p : A ⟶ᵀ* Π F G) (⊩F : ⊩₁ F)
          (⊩G : (u : RTm Γ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) G))
          {t u : RTm Γ} →
          (⊩₁Π p ⊩F ⊩G) ⊩₁∋ t → (r : ⊩F ⊩₁∋ u) → (⊩G u r) ⊩₁∋ app t u
sem-app p ⊩F ⊩G h r = projr h _ r

------------------------------------------------------------------------
-- 6. WHAT `fund` STILL NEEDS — scoped against the stratified relation.
--
--   (a) ⚠ A TYPE-FORMATION JUDGMENT, and this is a KERNEL DECISION, not a proof
--       detail.  A normalization theorem for `_⊢_∷_` AS IT STANDS is not
--       provable: `⊢lam`'s domain is unconstrained and §1 shows the relation is
--       not total.  Either the kernel gains `Γ ⊢ty A` premises on
--       `⊢lam`/`⊢app`/`⊢pair` — which cascades through `NbEPDirDBSubj` and
--       `NbEPDirDBDec` exactly as PLAN §2's warning describes — or the theorem
--       is stated only for derivations whose types are independently
--       well-formed.  Take it deliberately before building on either.
--
--   (b) `fund-ty : Γ ⊢ty A → ⊩ˢ Γ σ → ⊩₁ (subTy σ A)`, MUTUAL with `fund`; its
--       `ty-El` case is `sem-El` plus the level-0→1 embedding (`⊩₀ A → ⊩₁ A`,
--       a four-line structural map, not written here).
--
--   (c) Reducible substitutions `⊩ˢ Γ σ` and `fund` itself.  Every term rule
--       has its lemma: `⊢var`→`⊩var₁`, `⊢app`→`sem-app`, `⊢lam`→`sem-lam`,
--       `⊢⌜base⌝`→`sem-⌜base⌝`, `⊢⌜Π⌝`→`sem-⌜Π⌝`, `⊢conv`→`SpikeSNW`'s
--       `conv-⊩`+`irrel` ported to both levels.
--
--   (d) `Σ'` at both levels, plus `sem-⌜Σ⌝`; `SpikeSNJ.SNRed` already carries
--       `snr-βfst`/`snr-βsnd`/`snr-fst`/`snr-snd`.
--
--   (e) `wnorm : Γ ⊢ t ∷ A → WN t` via `SpikeSNJ.wn`, hence `dec-conv`
--       unconditional.
------------------------------------------------------------------------
