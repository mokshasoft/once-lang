------------------------------------------------------------------------
-- OCP-0009 · W1f — THE LOGICAL RELATION, CONSOLIDATED.
--
-- One module for what the W1a–W1e spikes established across five.  Promoted out
-- of the `Spike` line because the shape has stopped moving; the spikes stay in
-- the tree as the negative-result record (see `HANDOFF-2026-07-30.md` §5).
--
-- WHAT IS MERGED, and from where:
--   * the JOACHIMSKI–MATTHES presentation `SNe`/`SN`/`SNRed` (W1d, `SpikeSNJ`) —
--     head expansion is a CONSTRUCTOR, which is what makes `exp` structural;
--   * the WHNF-CARRYING relation (W1b, `SpikeSNW`) — each constructor stores its
--     own reduction to weak head normal form, which is what keeps the forward
--     transfer structural;
--   * the STRATIFICATION `⊩₀`/`⊩₁` (W1e, `SpikeSNK`) — forced, because an
--     unstratified `U` clause carrying reducibility is not strictly positive;
--   * the transfer layer `irrel`/`fwd*`/`bwd*`/`conv-⊩` (W1b) — ported here to
--     BOTH LEVELS.  ⚠ This was the actual work item: the handoff recorded that
--     these "port verbatim" on the grounds that none inspects `SN` or
--     membership.  That reading is confirmed — the proofs below are `SpikeSNW`'s
--     with the constructor names changed — but it is now EXECUTED, not asserted.
--
-- Everything is over the REAL kernel syntax (`NbEPDirDBPi`/`NbEPDirDBType`) and
-- consumes the real confluence results (`NbEPDirDBInj`).  `--safe`, zero
-- postulates, zero holes, no dependency on any `Spike*` module.
--
-- `Σ'` IS IN THE RELATION at both levels (added 2026-07-30, W1g): `⊩₀Σ`/`⊩₁Σ`
-- with the DEPENDENT-pair membership
--     ⊩Σ _ ⊩F ⊩G ⊩∋ t = SN t × Σ (⊩F ⊩∋ fst t) (λ r → (⊩G (fst t) r) ⊩∋ snd t)
-- and every proof extended: 8 cross cases + the real `Σ'/Σ'` case in `irrel` at
-- each level, plus `fwd`/`CR1`/`CR3`/`exp`/`bwd`/`emb`.
--
-- ⚠ ONE THING THE `Π` CASES DID NOT PREPARE FOR.  `Σ'` is the first former whose
-- second component's TYPE moves when the term does: expanding `t` to `t'` changes
-- `fst t`, hence `G[fst t]` vs `G[fst t']`.  So `exp` at `Σ'` needs a genuine
-- CONVERSION (via `subTy-monoˢ` + `irrel`), where `exp` at `Π` needed only a
-- congruence (`snr-app`).  Same in `sem-pair`, because `fst (pair a b) ⟶ a`.
-- That is why `Σ'` was not the pure copy-paste the plan projected.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLR where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; ¬_; ⊥; ⊥-elim; Σ; _,_; _×_ )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; ⌜Hom⌝; hrefl; tr
        ; Sub; subTy; subTm; extS; renTm
        ; subTm-renTm; subTm-id; Hom-cong₃ )
open import poc.OCP0009.NbEPDirDBType
  using ( single
        ; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ
        ; _⟶*_; done; step
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ )
open import poc.OCP0009.NbEPDirDBSR using ( ⟶ᵀ-sub; ≅ᵀ-sub )
open import poc.OCP0009.NbEPDirDBSubj using ( subTy-monoˢ )
open import poc.OCP0009.NbEPDirDBConf using ( single-mono )
open import poc.OCP0009.NbEPDirDBConf
  using ( ⟶*-trans; ⟶*-lam; ⟶*-appˡ; ⟶*-appʳ
        ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd
        ; ⟶*-⌜Π⌝ˡ; ⟶*-⌜Π⌝ʳ; ⟶*-⌜Σ⌝ˡ; ⟶*-⌜Σ⌝ʳ
        ; ⟶*-⌜Hom⌝ᶜ; ⟶*-⌜Hom⌝ˡ; ⟶*-⌜Hom⌝ʳ; ⟶*-hreflᶜ; ⟶*-hreflᵃ )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; ⟶ᵀ*-Homᵀ
        ; confluentᵀ; church-rosserᵀ
        ; ΠRed; mkΠRed; Π-reduct; Πinj≡
        ; ΣRed; mkΣRed; Σ-reduct; Σinj≡; red→≅ᵀ )

private
  variable
    Γ Δ : Cx

-- `Σ`'s fields are named `fst`/`snd`, which are also `RTm` constructors, so the
-- record is never opened; these are the projections used instead.
projl : {P Q : Set} → P × Q → P
projl (p , _) = p

projr : {P Q : Set} → P × Q → Q
projr (_ , q) = q

-- dependent projections, for the `Σ'` membership clauses
dfst : {S : Set} {P : S → Set} → Σ S P → S
dfst (a , _) = a

dsnd : {S : Set} {P : S → Set} → (p : Σ S P) → P (dfst p)
dsnd (_ , b) = b

------------------------------------------------------------------------
-- 1. THE JOACHIMSKI–MATTHES PRESENTATION (W1d).
--
-- `sn-exp : SNRed t t' → SN t' → SN t` makes head expansion a CONSTRUCTOR, so
-- it is never a lemma; `snr-app : SNRed t t' → SNRed (app t u) (app t' u)`
-- makes head reduction closed under application STRUCTURALLY, which is what the
-- refuted spine route could not express (handoff §5a).
--
-- The `SN` premises on `snr-β`/`snr-βfst`/`snr-βsnd` carry the DISCARDED
-- material.  Without them the presentation is unsound: `β` can throw its
-- argument away, and `(λx. y) Ω ⟶ y` must not make `(λx. y) Ω` normal.
------------------------------------------------------------------------

data SNe {Γ} : RTm Γ → Set
data SN  {Γ} : RTm Γ → Set
data SNRed {Γ} : RTm Γ → RTm Γ → Set

data SNe {Γ} where
  sne-var : (x : Var Γ) → SNe (var x)
  sne-app : {t u : RTm Γ} → SNe t → SN u → SNe (app t u)
  sne-fst : {p : RTm Γ} → SNe p → SNe (fst p)
  sne-snd : {p : RTm Γ} → SNe p → SNe (snd p)
  -- W2 stage 1: `hrefl` is OPERATIONALLY INERT (its unfold family is
  -- deferred with the canonicity package, NbEPDirDBType), so it never
  -- becomes a `lam` and behaves as a neutral for this SN-flavored LR —
  -- exactly as long as it has no computation.
  sne-hrefl : {c t : RTm Γ} → SN c → SN t → SNe (hrefl c t)

data SN {Γ} where
  sn-ne   : {t : RTm Γ} → SNe t → SN t
  sn-lam  : {t : RTm (Γ ∙)} → SN t → SN (lam t)
  sn-pair : {a b : RTm Γ} → SN a → SN b → SN (pair a b)
  sn-cb   : SN (⌜base⌝ {Γ})
  sn-cΠ   : {c : RTm Γ} {d : RTm (Γ ∙)} → SN c → SN d → SN (⌜Π⌝ c d)
  sn-cΣ   : {c : RTm Γ} {d : RTm (Γ ∙)} → SN c → SN d → SN (⌜Σ⌝ c d)
  sn-cH   : {c a b : RTm Γ} → SN c → SN a → SN b → SN (⌜Hom⌝ c a b)
  sn-exp  : {t t' : RTm Γ} → SNRed t t' → SN t' → SN t

data SNRed {Γ} where
  snr-β    : {s : RTm (Γ ∙)} {u : RTm Γ} → SN u →
             SNRed (app (lam s) u) (subTm (single u) s)
  snr-βfst : {a b : RTm Γ} → SN b → SNRed (fst (pair a b)) a
  snr-βsnd : {a b : RTm Γ} → SN a → SNRed (snd (pair a b)) b
  snr-app  : {t t' u : RTm Γ} → SNRed t t' → SNRed (app t u) (app t' u)
  snr-fst  : {p p' : RTm Γ} → SNRed p p' → SNRed (fst p) (fst p')
  snr-snd  : {p p' : RTm Γ} → SNRed p p' → SNRed (snd p) (snd p')

snr→⟶ : {t t' : RTm Γ} → SNRed t t' → t ⟶ t'
snr→⟶ (snr-β {s} {u} _)    = β s u
snr→⟶ (snr-βfst {a} {b} _) = βfst a b
snr→⟶ (snr-βsnd {a} {b} _) = βsnd a b
snr→⟶ (snr-app r)          = ξ-appˡ (snr→⟶ r)
snr→⟶ (snr-fst r)          = ξ-fst (snr→⟶ r)
snr→⟶ (snr-snd r)          = ξ-snd (snr→⟶ r)

------------------------------------------------------------------------
-- 2. WHNF SHAPE LEMMAS, and the workhorse `joinW`.
--
-- These turn a confluence witness into shape information; they are what makes
-- the whnf-carrying design work.  `joinW` uses confluence three times — once to
-- resolve the conversion, once per side to reconcile it with that side's own
-- stored reduction.
------------------------------------------------------------------------

base-nf : {A : RTy Γ} → base {Γ} ⟶ᵀ* A → A ≡ base
base-nf doneᵀ        = refl
base-nf (stepᵀ () _)

U-nf : {A : RTy Γ} → U {Γ} ⟶ᵀ* A → A ≡ U
U-nf doneᵀ        = refl
U-nf (stepᵀ () _)

-- ⚠ The TYPE-level neutrality payload is a PLAIN syntactic `Ne`, not `SNe`.
-- `El-ne-reduct` needs neutrality preserved under reduction, and for `SNe` that
-- would need `SN` closed under reduction — a real lemma in the JM presentation
-- (its `sne-app` carries `SN` of the argument).  Nothing here uses the `SN`
-- payload at type level: it is only ever consumed by `joinW`-driven shape
-- refutation.  So carry the cheap predicate, with a forgetful map from `SNe`.
data Ne {Γ} : RTm Γ → Set where
  ne-var : (x : Var Γ) → Ne (var x)
  ne-app : {t u : RTm Γ} → Ne t → Ne (app t u)
  ne-fst : {p : RTm Γ} → Ne p → Ne (fst p)
  ne-snd : {p : RTm Γ} → Ne p → Ne (snd p)
  ne-hrefl : {c t : RTm Γ} → Ne (hrefl c t)

ne-red : {t t' : RTm Γ} → Ne t → t ⟶ t' → Ne t'
ne-red (ne-var x) ()
ne-red (ne-app n) (ξ-appˡ r) = ne-app (ne-red n r)
ne-red (ne-app n) (ξ-appʳ r) = ne-app n
ne-red (ne-fst n) (ξ-fst r)  = ne-fst (ne-red n r)
ne-red (ne-snd n) (ξ-snd r)  = ne-snd (ne-red n r)
ne-red ne-hrefl (ξ-hreflᶜ r) = ne-hrefl
ne-red ne-hrefl (ξ-hreflᵃ r) = ne-hrefl

sne→ne : {t : RTm Γ} → SNe t → Ne t
sne→ne (sne-var x)   = ne-var x
sne→ne (sne-app n _) = ne-app (sne→ne n)
sne→ne (sne-fst n)   = ne-fst (sne→ne n)
sne→ne (sne-snd n)   = ne-snd (sne→ne n)
sne→ne (sne-hrefl _ _) = ne-hrefl

record ElNe {Γ} (A : RTy Γ) : Set where
  constructor mkElNe
  field
    nf  : RTm Γ
    nfe : Ne nf
    nfq : A ≡ El nf

El-ne-reduct : {n : RTm Γ} {A : RTy Γ} → Ne n → El n ⟶ᵀ* A → ElNe A
El-ne-reduct {n = n} ne doneᵀ              = mkElNe n ne refl
El-ne-reduct         ne (stepᵀ (ξ-El r) p) = El-ne-reduct (ne-red ne r) p

------------------------------------------------------------------------
-- 2b. W2 — the STUCK HEADS of `Hom`, closed under reduction.
--
-- A `Hom H a b` is stuck exactly when `H`'s head carries no unfolding rule:
-- `base` (discrete by generation, item 4), a NEUTRAL `El`, `Σ'` (unfolding
-- deferred to transport), or a stuck `Hom` (higher paths).  `U` and `Π` are
-- deliberately ABSENT — those unfold — and that absence is what makes
-- `stkhd-red` total: the unfolding rules hit `StkHd` as absurd patterns.
-- Note `sh-Hom` REQUIRES the inner head stuck: `Hom (Hom U c d) x y` is NOT
-- stuck — the inner `Hom` unfolds to a `Π` and then the outer fires.
------------------------------------------------------------------------

data StkHd {Γ} : RTy Γ → Set where
  sh-base : StkHd base
  sh-ne   : {n : RTm Γ} → Ne n → StkHd (El n)
  sh-Σ    : {A : RTy Γ} {B : RTy (Γ ∙)} → StkHd (Σ' A B)
  sh-Hom  : {H : RTy Γ} {a b : RTm Γ} → StkHd H → StkHd (Hom H a b)

stkhd-red : {H H' : RTy Γ} → StkHd H → H ⟶ᵀ H' → StkHd H'
stkhd-red (sh-ne ()) El-⌜base⌝
stkhd-red (sh-ne ()) (El-⌜Π⌝ _ _)
stkhd-red (sh-ne ()) (El-⌜Σ⌝ _ _)
stkhd-red (sh-ne n)  (ξ-El r)    = sh-ne (ne-red n r)
stkhd-red sh-Σ       (ξ-Σˡ r)    = sh-Σ
stkhd-red sh-Σ       (ξ-Σʳ r)    = sh-Σ
stkhd-red (sh-Hom ()) (Hom-U _ _)
stkhd-red (sh-Hom ()) (Hom-Π _ _ _ _)
stkhd-red (sh-Hom s) (ξ-Homᵀ r) = sh-Hom (stkhd-red s r)
stkhd-red (sh-Hom s) (ξ-Homˡ r) = sh-Hom s
stkhd-red (sh-Hom s) (ξ-Homʳ r) = sh-Hom s

record HomStk {Γ} (C : RTy Γ) : Set where
  constructor mkHomStk
  field
    hH    : RTy Γ
    ha hb : RTm Γ
    hstk  : StkHd hH
    heq   : C ≡ Hom hH ha hb

-- reducts of a stuck `Hom` are stuck `Hom`s — the shape lemma the transfer
-- layer consumes, exactly `El-ne-reduct`'s pattern.
Hom-stk-reduct : {H : RTy Γ} {a b : RTm Γ} {C : RTy Γ} →
                 StkHd H → Hom H a b ⟶ᵀ* C → HomStk C
Hom-stk-reduct s doneᵀ                    = mkHomStk _ _ _ s refl
Hom-stk-reduct () (stepᵀ (Hom-U _ _) p)
Hom-stk-reduct () (stepᵀ (Hom-Π _ _ _ _) p)
Hom-stk-reduct s (stepᵀ (ξ-Homᵀ r) p) = Hom-stk-reduct (stkhd-red s r) p
Hom-stk-reduct s (stepᵀ (ξ-Homˡ r) p) = Hom-stk-reduct s p
Hom-stk-reduct s (stepᵀ (ξ-Homʳ r) p) = Hom-stk-reduct s p

⟶ᵀ*-sub : (σ : Sub Γ Δ) {A B : RTy Γ} → A ⟶ᵀ* B → subTy σ A ⟶ᵀ* subTy σ B
⟶ᵀ*-sub σ doneᵀ       = doneᵀ
⟶ᵀ*-sub σ (stepᵀ r p) = stepᵀ (⟶ᵀ-sub σ r) (⟶ᵀ*-sub σ p)

joinW : {A B W₁ W₂ : RTy Γ} → A ≅ᵀ B → A ⟶ᵀ* W₁ → B ⟶ᵀ* W₂ →
        Σ (RTy Γ) (λ E → (W₁ ⟶ᵀ* E) × (W₂ ⟶ᵀ* E))
joinW c p q with church-rosserᵀ c
... | C , (aC , bC) with confluentᵀ p aC | confluentᵀ q bC
...   | D₁ , (w₁D₁ , CD₁) | D₂ , (w₂D₂ , CD₂) with confluentᵀ CD₁ CD₂
...     | E , (D₁E , D₂E) =
          E , (⟶ᵀ*-trans w₁D₁ D₁E , ⟶ᵀ*-trans w₂D₂ D₂E)

------------------------------------------------------------------------
-- 3. LEVEL 0 — SMALL types: the decodings of codes.  NO `U`.
------------------------------------------------------------------------

infix 4 _⊩₀∋_

data ⊩₀_ {Γ} : RTy Γ → Set
_⊩₀∋_ : {Γ : Cx} {A : RTy Γ} → ⊩₀ A → RTm Γ → Set

data ⊩₀_ {Γ} where
  ⊩₀base : {A : RTy Γ} → A ⟶ᵀ* base → ⊩₀ A
  ⊩₀ne   : {A : RTy Γ} {n : RTm Γ} → A ⟶ᵀ* El n → Ne n → ⊩₀ A
  ⊩₀Π    : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
         → A ⟶ᵀ* Π F G
         → (⊩F : ⊩₀ F)
         → ((u : RTm Γ) → ⊩F ⊩₀∋ u → ⊩₀ (subTy (single u) G))
         → ⊩₀ A
  ⊩₀Σ    : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
         → A ⟶ᵀ* Σ' F G
         → (⊩F : ⊩₀ F)
         → ((u : RTm Γ) → ⊩F ⊩₀∋ u → ⊩₀ (subTy (single u) G))
         → ⊩₀ A
  -- ★ W2 stage 1: the LEVEL-0 `Hom` clause RETURNS, exactly as
  -- SpikeHomRefl priced — with a `⌜Hom⌝` code, small types CAN reduce to
  -- stuck `Hom`s (`El (⌜Hom⌝ c a b) ⟶ᵀ Hom (El c) a b`).  Membership is
  -- `SN`, like `base`.
  ⊩₀Hom  : {A H : RTy Γ} {a b : RTm Γ}
         → A ⟶ᵀ* Hom H a b → StkHd H → ⊩₀ A

⊩₀base _     ⊩₀∋ t = SN t
⊩₀ne _ _     ⊩₀∋ t = SN t
⊩₀Π _ ⊩F ⊩G  ⊩₀∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ app t u)
-- the DEPENDENT pair: the second component's type depends on the first.
⊩₀Σ _ ⊩F ⊩G  ⊩₀∋ t =
  SN t × Σ (⊩F ⊩₀∋ fst t) (λ r → (⊩G (fst t) r) ⊩₀∋ snd t)
⊩₀Hom _ _    ⊩₀∋ t = SN t

bwd₀ : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩₀ B → ⊩₀ A
bwd₀ p (⊩₀base q)    = ⊩₀base (⟶ᵀ*-trans p q)
bwd₀ p (⊩₀ne q n)    = ⊩₀ne   (⟶ᵀ*-trans p q) n
bwd₀ p (⊩₀Π q ⊩F ⊩G) = ⊩₀Π    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₀ p (⊩₀Σ q ⊩F ⊩G) = ⊩₀Σ    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₀ p (⊩₀Hom q s)   = ⊩₀Hom  (⟶ᵀ*-trans p q) s

------------------------------------------------------------------------
-- 3a. IRRELEVANCE UP TO CONVERSION, at level 0.
--
-- A BI-IMPLICATION on purpose: the `Π/Π` case must convert a member of the
-- RIGHT domain into one of the LEFT before applying the left family, and
-- one-directionally that needs the recursive call with arguments swapped — at
-- which point neither argument position decreases.  Returning both directions
-- makes the domain step a call whose two arguments are the two domains, each a
-- strict subterm of its own side.
------------------------------------------------------------------------

irrel₀ : {A B : RTy Γ} → A ≅ᵀ B → (R : ⊩₀ A) (S : ⊩₀ B) →
         ((t : RTm Γ) → R ⊩₀∋ t → S ⊩₀∋ t) × ((t : RTm Γ) → S ⊩₀∋ t → R ⊩₀∋ t)

-- both sides non-`Π`: membership is `SN t` on both, so transfer is identity.
irrel₀ c (⊩₀base _) (⊩₀base _) = (λ _ h → h) , (λ _ h → h)
irrel₀ c (⊩₀base _) (⊩₀ne _ _) = (λ _ h → h) , (λ _ h → h)
irrel₀ c (⊩₀ne _ _) (⊩₀base _) = (λ _ h → h) , (λ _ h → h)
irrel₀ c (⊩₀ne _ _) (⊩₀ne _ _) = (λ _ h → h) , (λ _ h → h)

-- one side `Π`, the other not: impossible, and `joinW` + the shape lemmas say so.
irrel₀ c (⊩₀base p) (⊩₀Π q _ _) with joinW c p q
... | E , (bE , πE) with base-nf bE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel₀ c (⊩₀ne p n) (⊩₀Π q _ _) with joinW c p q
... | E , (eE , πE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel₀ c (⊩₀Π p _ _) (⊩₀base q) with joinW c p q
... | E , (πE , bE) with base-nf bE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel₀ c (⊩₀Π p _ _) (⊩₀ne q n) with joinW c p q
... | E , (πE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Π-reduct πE
...     | mkΠRed _ _ () _ _

-- `Σ'` against `base`/`ne`/`Π`, both ways: impossible.
irrel₀ c (⊩₀base p) (⊩₀Σ q _ _) with joinW c p q
... | E , (bE , σE) with base-nf bE
...   | refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₀ c (⊩₀ne p n) (⊩₀Σ q _ _) with joinW c p q
... | E , (eE , σE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₀ c (⊩₀Σ p _ _) (⊩₀base q) with joinW c p q
... | E , (σE , bE) with base-nf bE
...   | refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₀ c (⊩₀Σ p _ _) (⊩₀ne q n) with joinW c p q
... | E , (σE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₀ c (⊩₀Π p _ _) (⊩₀Σ q _ _) with joinW c p q
... | E , (πE , σE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₀ c (⊩₀Σ p _ _) (⊩₀Π q _ _) with joinW c p q
... | E , (σE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Σ-reduct σE
...     | mkΣRed _ _ () _ _

-- W2 stage 1: stuck-`Hom` identity, and its refutations against the
-- other heads (`Hom-stk-reduct` pins the head, the other side's shape
-- lemma pins a different one).
irrel₀ c (⊩₀Hom _ _) (⊩₀Hom _ _) = (λ _ h → h) , (λ _ h → h)
irrel₀ c (⊩₀base p) (⊩₀Hom q s) with joinW c p q
... | E , (bE , hE) with base-nf bE
...   | refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₀ c (⊩₀Hom p s) (⊩₀base q) with joinW c p q
... | E , (hE , bE) with base-nf bE
...   | refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₀ c (⊩₀ne p n) (⊩₀Hom q s) with joinW c p q
... | E , (eE , hE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₀ c (⊩₀Hom p s) (⊩₀ne q n) with joinW c p q
... | E , (hE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₀ c (⊩₀Π p _ _) (⊩₀Hom q s) with joinW c p q
... | E , (πE , hE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₀ c (⊩₀Hom p s) (⊩₀Π q _ _) with joinW c p q
... | E , (hE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₀ c (⊩₀Σ p _ _) (⊩₀Hom q s) with joinW c p q
... | E , (σE , hE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₀ c (⊩₀Hom p s) (⊩₀Σ q _ _) with joinW c p q
... | E , (hE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()

-- the real case: confluence forces convertible domain AND codomain.
irrel₀ c (⊩₀Π p ⊩F ⊩G) (⊩₀Π q ⊩F' ⊩G') with joinW c p q
... | E , (πE₁ , πE₂) with Π-reduct πE₁ | Π-reduct πE₂
...   | mkΠRed F₁ G₁ eq₁ rF₁ rG₁ | mkΠRed F₂ G₂ eq₂ rF₂ rG₂
        with Πinj≡ (trans (sym eq₁) eq₂)
...       | (refl , refl) =
            (λ t h → (projl h , λ u r' →
               projl (irrel₀ (≅ᵀ-sub (single u)
                               (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                             (⊩G u (projr (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁)
                                                         (csymᵀ (red→≅ᵀ rF₂)))
                                                  ⊩F ⊩F') u r'))
                             (⊩G' u r'))
                     (app t u)
                     (projr h u (projr (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁)
                                                      (csymᵀ (red→≅ᵀ rF₂)))
                                               ⊩F ⊩F') u r'))))
          , (λ t h → (projl h , λ u r →
               projr (irrel₀ (≅ᵀ-sub (single u)
                               (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                             (⊩G u r)
                             (⊩G' u (projl (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁)
                                                          (csymᵀ (red→≅ᵀ rF₂)))
                                                   ⊩F ⊩F') u r)))
                     (app t u)
                     (projr h u (projl (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁)
                                                      (csymᵀ (red→≅ᵀ rF₂)))
                                               ⊩F ⊩F') u r))))

-- the `Σ'/Σ'` case: same shape as `Π/Π`, but the second component's type
-- depends on the FIRST, so the domain transfer has to happen before the
-- codomain one can even be stated.
irrel₀ c (⊩₀Σ p ⊩F ⊩G) (⊩₀Σ q ⊩F' ⊩G') with joinW c p q
... | E , (σE₁ , σE₂) with Σ-reduct σE₁ | Σ-reduct σE₂
...   | mkΣRed F₁ G₁ eq₁ rF₁ rG₁ | mkΣRed F₂ G₂ eq₂ rF₂ rG₂
        with Σinj≡ (trans (sym eq₁) eq₂)
...       | (refl , refl) =
            (λ t h →
               (projl h
               , ( projl (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁) (csymᵀ (red→≅ᵀ rF₂))) ⊩F ⊩F')
                         (fst t) (dfst (projr h))
                 , projl (irrel₀ (≅ᵀ-sub (single (fst t))
                                   (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                                 (⊩G (fst t) (dfst (projr h)))
                                 (⊩G' (fst t)
                                   (projl (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁)
                                                         (csymᵀ (red→≅ᵀ rF₂)))
                                                  ⊩F ⊩F') (fst t) (dfst (projr h)))))
                         (snd t) (dsnd (projr h)) )))
          , (λ t h →
               (projl h
               , ( projr (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁) (csymᵀ (red→≅ᵀ rF₂))) ⊩F ⊩F')
                         (fst t) (dfst (projr h))
                 , projr (irrel₀ (≅ᵀ-sub (single (fst t))
                                   (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                                 (⊩G (fst t)
                                   (projr (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁)
                                                         (csymᵀ (red→≅ᵀ rF₂)))
                                                  ⊩F ⊩F') (fst t) (dfst (projr h))))
                                 (⊩G' (fst t) (dfst (projr h))))
                         (snd t) (dsnd (projr h)) )))

------------------------------------------------------------------------
-- 3b. FORWARD TRANSFER at level 0, and hence transfer along CONVERSION.
------------------------------------------------------------------------

fwd₀ : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩₀ A → ⊩₀ B

fwd₀ p (⊩₀base q) with confluentᵀ p q
... | E , (bE , baseE) with base-nf baseE
...   | refl = ⊩₀base bE

fwd₀ p (⊩₀ne q n) with confluentᵀ p q
... | E , (bE , elE) with El-ne-reduct n elE
...   | mkElNe n' n'e refl = ⊩₀ne bE n'e

fwd₀ p (⊩₀Π q ⊩F ⊩G) with confluentᵀ p q
... | E , (bE , πE) with Π-reduct πE
...   | mkΠRed F₁ G₁ refl rF rG =
        ⊩₀Π bE (fwd₀ rF ⊩F)
              (λ u r → fwd₀ (⟶ᵀ*-sub (single u) rG)
                            (⊩G u (projr (irrel₀ (red→≅ᵀ rF) ⊩F (fwd₀ rF ⊩F)) u r)))

fwd₀ p (⊩₀Σ q ⊩F ⊩G) with confluentᵀ p q
... | E , (bE , σE) with Σ-reduct σE
...   | mkΣRed F₁ G₁ refl rF rG =
        ⊩₀Σ bE (fwd₀ rF ⊩F)
              (λ u r → fwd₀ (⟶ᵀ*-sub (single u) rG)
                            (⊩G u (projr (irrel₀ (red→≅ᵀ rF) ⊩F (fwd₀ rF ⊩F)) u r)))

fwd₀ p (⊩₀Hom q s) with confluentᵀ p q
... | E , (bE , hE) with Hom-stk-reduct s hE
...   | mkHomStk _ _ _ s' refl = ⊩₀Hom bE s'

conv₀ : {A B : RTy Γ} → A ≅ᵀ B → ⊩₀ A → ⊩₀ B
conv₀ c R with church-rosserᵀ c
... | C , (aC , bC) = bwd₀ bC (fwd₀ aC R)

------------------------------------------------------------------------
-- 3c. Candidate conditions and head expansion, at level 0.
------------------------------------------------------------------------

CR1₀ : {A : RTy Γ} (R : ⊩₀ A) {t : RTm Γ} → R ⊩₀∋ t → SN t
CR1₀ (⊩₀base _)  h = h
CR1₀ (⊩₀ne _ _)  h = h
CR1₀ (⊩₀Π _ _ _) h = projl h
CR1₀ (⊩₀Σ _ _ _) h = projl h
CR1₀ (⊩₀Hom _ _) h = h

CR3₀ : {A : RTy Γ} (R : ⊩₀ A) {t : RTm Γ} → SNe t → R ⊩₀∋ t
CR3₀ (⊩₀base _)    nt = sn-ne nt
CR3₀ (⊩₀Hom _ _)   nt = sn-ne nt
CR3₀ (⊩₀ne _ _)    nt = sn-ne nt
CR3₀ (⊩₀Π _ ⊩F ⊩G) nt =
  (sn-ne nt , λ u ru → CR3₀ (⊩G u ru) (sne-app nt (CR1₀ ⊩F ru)))
CR3₀ (⊩₀Σ _ ⊩F ⊩G) {t} nt =
  (sn-ne nt , ( CR3₀ ⊩F (sne-fst nt)
              , CR3₀ (⊩G (fst t) (CR3₀ ⊩F (sne-fst nt))) (sne-snd nt) ))

exp₀ : {A : RTy Γ} (R : ⊩₀ A) {t t' : RTm Γ} → SNRed t t' → R ⊩₀∋ t' → R ⊩₀∋ t
exp₀ (⊩₀base _)    r h = sn-exp r h
exp₀ (⊩₀Hom _ _)   r h = sn-exp r h
exp₀ (⊩₀ne _ _)    r h = sn-exp r h
exp₀ (⊩₀Π _ ⊩F ⊩G) r h =
  (sn-exp r (projl h) , λ v rv → exp₀ (⊩G v rv) (snr-app r) (projr h v rv))
-- ★ the `Σ'` case needs a CONVERSION, not just a congruence: expanding `t` to
-- `t'` changes `fst t`, so the second component's TYPE changes with it —
-- `G[fst t]` vs `G[fst t']` — and `subTy-monoˢ` + `irrel₀` bridge the two.
exp₀ (⊩₀Σ {G = G} _ ⊩F ⊩G) {t} {t'} r h =
  ( sn-exp r (projl h)
  , ( exp₀ ⊩F (snr-fst r) (dfst (projr h))
    , projl (irrel₀ (csymᵀ (red→≅ᵀ (subTy-monoˢ
                              (single-mono (step (ξ-fst (snr→⟶ r)) done)) G)))
                    (⊩G (fst t') (dfst (projr h)))
                    (⊩G (fst t) (exp₀ ⊩F (snr-fst r) (dfst (projr h)))))
            (snd t)
            (exp₀ (⊩G (fst t') (dfst (projr h))) (snr-snd r) (dsnd (projr h))) ))

⊩var₀ : {A : RTy Γ} (R : ⊩₀ A) (x : Var Γ) → R ⊩₀∋ var x
⊩var₀ R x = CR3₀ R (sne-var x)

------------------------------------------------------------------------
-- 4. LEVEL 1 — LARGE types, with the `U` clause CARRYING REDUCIBILITY.
--
--     ⊩₁U _ ⊩₁∋ t = SN t × (⊩₀ (El t))
--
-- `⊩₀` is fully defined above, so it is a CLOSED type here, not a recursive
-- occurrence — which is exactly why this typechecks and the unstratified
-- version does not (handoff §5b).  Two levels suffice because the kernel's
-- universe is PREDICATIVE: the codes are `⌜base⌝`/`⌜Π⌝`/`⌜Σ⌝`, with no code
-- for `U` itself.
------------------------------------------------------------------------

infix 4 _⊩₁∋_

data ⊩₁_ {Γ} : RTy Γ → Set
_⊩₁∋_ : {Γ : Cx} {A : RTy Γ} → ⊩₁ A → RTm Γ → Set

data ⊩₁_ {Γ} where
  ⊩₁base : {A : RTy Γ} → A ⟶ᵀ* base → ⊩₁ A
  ⊩₁U    : {A : RTy Γ} → A ⟶ᵀ* U → ⊩₁ A
  ⊩₁ne   : {A : RTy Γ} {n : RTm Γ} → A ⟶ᵀ* El n → Ne n → ⊩₁ A
  ⊩₁Π    : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
         → A ⟶ᵀ* Π F G
         → (⊩F : ⊩₁ F)
         → ((u : RTm Γ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) G))
         → ⊩₁ A
  ⊩₁Σ    : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
         → A ⟶ᵀ* Σ' F G
         → (⊩F : ⊩₁ F)
         → ((u : RTm Γ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) G))
         → ⊩₁ A
  -- W2: a STUCK `Hom` is a semantic type whose members are the SN terms —
  -- nothing constructs it (no `refl`/`J` yet), so it behaves like `base`.
  -- ★ LEVEL 0 NEEDS NO `Hom` CLAUSE AT ALL: level 0 covers only decodings
  -- of codes, and there is no `⌜Hom⌝` code, so no level-0 type ever reduces
  -- to a `Hom`.  The predicative cut does structural work again.
  ⊩₁Hom  : {A H : RTy Γ} {a b : RTm Γ}
         → A ⟶ᵀ* Hom H a b → StkHd H → ⊩₁ A

⊩₁base _     ⊩₁∋ t = SN t
⊩₁U _        ⊩₁∋ t = SN t × (⊩₀ (El t))
⊩₁ne _ _     ⊩₁∋ t = SN t
⊩₁Π _ ⊩F ⊩G  ⊩₁∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩₁∋ u) → (⊩G u r) ⊩₁∋ app t u)
⊩₁Σ _ ⊩F ⊩G  ⊩₁∋ t =
  SN t × Σ (⊩F ⊩₁∋ fst t) (λ r → (⊩G (fst t) r) ⊩₁∋ snd t)
⊩₁Hom _ _    ⊩₁∋ t = SN t

bwd₁ : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩₁ B → ⊩₁ A
bwd₁ p (⊩₁base q)    = ⊩₁base (⟶ᵀ*-trans p q)
bwd₁ p (⊩₁U q)       = ⊩₁U    (⟶ᵀ*-trans p q)
bwd₁ p (⊩₁ne q n)    = ⊩₁ne   (⟶ᵀ*-trans p q) n
bwd₁ p (⊩₁Π q ⊩F ⊩G) = ⊩₁Π    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₁ p (⊩₁Σ q ⊩F ⊩G) = ⊩₁Σ    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₁ p (⊩₁Hom q s)   = ⊩₁Hom  (⟶ᵀ*-trans p q) s

------------------------------------------------------------------------
-- 4a. IRRELEVANCE at level 1.
--
-- Note `U` is NOT an identity case against `base`/`ne` any more — its
-- membership carries a second component — so those six pairings must be
-- refuted rather than passed through.  `U`/`U` IS an identity, because the
-- carried `⊩₀ (El t)` does not mention the `⊩₁` derivation.
------------------------------------------------------------------------

irrel₁ : {A B : RTy Γ} → A ≅ᵀ B → (R : ⊩₁ A) (S : ⊩₁ B) →
         ((t : RTm Γ) → R ⊩₁∋ t → S ⊩₁∋ t) × ((t : RTm Γ) → S ⊩₁∋ t → R ⊩₁∋ t)

-- identities: both sides `SN`-valued, or both `U`.
irrel₁ c (⊩₁base _) (⊩₁base _) = (λ _ h → h) , (λ _ h → h)
irrel₁ c (⊩₁base _) (⊩₁ne _ _) = (λ _ h → h) , (λ _ h → h)
irrel₁ c (⊩₁ne _ _) (⊩₁base _) = (λ _ h → h) , (λ _ h → h)
irrel₁ c (⊩₁ne _ _) (⊩₁ne _ _) = (λ _ h → h) , (λ _ h → h)
irrel₁ c (⊩₁U _)    (⊩₁U _)    = (λ _ h → h) , (λ _ h → h)
irrel₁ c (⊩₁Hom _ _) (⊩₁Hom _ _) = (λ _ h → h) , (λ _ h → h)

-- W2 `Hom` (stuck) against everything else, both ways: impossible — reducts
-- of a stuck `Hom` stay `Hom`-headed (`Hom-stk-reduct`), and the other side's
-- shape lemma pins a different head.
irrel₁ c (⊩₁base p) (⊩₁Hom q s) with joinW c p q
... | E , (bE , hE) with base-nf bE
...   | refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁Hom p s) (⊩₁base q) with joinW c p q
... | E , (hE , bE) with base-nf bE
...   | refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁U p) (⊩₁Hom q s) with joinW c p q
... | E , (uE , hE) with U-nf uE
...   | refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁Hom p s) (⊩₁U q) with joinW c p q
... | E , (hE , uE) with U-nf uE
...   | refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁ne p n) (⊩₁Hom q s) with joinW c p q
... | E , (eE , hE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁Hom p s) (⊩₁ne q n) with joinW c p q
... | E , (hE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁Π p _ _) (⊩₁Hom q s) with joinW c p q
... | E , (πE , hE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁Hom p s) (⊩₁Π q _ _) with joinW c p q
... | E , (hE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁Σ p _ _) (⊩₁Hom q s) with joinW c p q
... | E , (σE , hE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁Hom p s) (⊩₁Σ q _ _) with joinW c p q
... | E , (hE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Hom-stk-reduct s hE
...     | mkHomStk _ _ _ _ ()

-- `U` against a non-`U`: refuted.
irrel₁ c (⊩₁U p) (⊩₁base q) with joinW c p q
... | E , (uE , bE) with U-nf uE
...   | refl with base-nf bE
...     | ()
irrel₁ c (⊩₁U p) (⊩₁ne q n) with joinW c p q
... | E , (uE , eE) with U-nf uE
...   | refl with El-ne-reduct n eE
...     | mkElNe _ _ ()
irrel₁ c (⊩₁U p) (⊩₁Π q _ _) with joinW c p q
... | E , (uE , πE) with U-nf uE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel₁ c (⊩₁base p) (⊩₁U q) with joinW c p q
... | E , (bE , uE) with base-nf bE
...   | refl with U-nf uE
...     | ()
irrel₁ c (⊩₁ne p n) (⊩₁U q) with joinW c p q
... | E , (eE , uE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with U-nf uE
...     | ()
irrel₁ c (⊩₁Π p _ _) (⊩₁U q) with joinW c p q
... | E , (πE , uE) with U-nf uE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _

-- `Π` against `base`/`ne`: refuted.
irrel₁ c (⊩₁base p) (⊩₁Π q _ _) with joinW c p q
... | E , (bE , πE) with base-nf bE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel₁ c (⊩₁ne p n) (⊩₁Π q _ _) with joinW c p q
... | E , (eE , πE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel₁ c (⊩₁Π p _ _) (⊩₁base q) with joinW c p q
... | E , (πE , bE) with base-nf bE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
irrel₁ c (⊩₁Π p _ _) (⊩₁ne q n) with joinW c p q
... | E , (πE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Π-reduct πE
...     | mkΠRed _ _ () _ _

-- `Σ'` against everything else, both ways: impossible.
irrel₁ c (⊩₁base p) (⊩₁Σ q _ _) with joinW c p q
... | E , (bE , σE) with base-nf bE
...   | refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₁ c (⊩₁ne p n) (⊩₁Σ q _ _) with joinW c p q
... | E , (eE , σE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₁ c (⊩₁U p) (⊩₁Σ q _ _) with joinW c p q
... | E , (uE , σE) with U-nf uE
...   | refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₁ c (⊩₁Σ p _ _) (⊩₁base q) with joinW c p q
... | E , (σE , bE) with base-nf bE
...   | refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₁ c (⊩₁Σ p _ _) (⊩₁ne q n) with joinW c p q
... | E , (σE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₁ c (⊩₁Σ p _ _) (⊩₁U q) with joinW c p q
... | E , (σE , uE) with U-nf uE
...   | refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₁ c (⊩₁Π p _ _) (⊩₁Σ q _ _) with joinW c p q
... | E , (πE , σE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Σ-reduct σE
...     | mkΣRed _ _ () _ _
irrel₁ c (⊩₁Σ p _ _) (⊩₁Π q _ _) with joinW c p q
... | E , (σE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Σ-reduct σE
...     | mkΣRed _ _ () _ _

irrel₁ c (⊩₁Σ p ⊩F ⊩G) (⊩₁Σ q ⊩F' ⊩G') with joinW c p q
... | E , (σE₁ , σE₂) with Σ-reduct σE₁ | Σ-reduct σE₂
...   | mkΣRed F₁ G₁ eq₁ rF₁ rG₁ | mkΣRed F₂ G₂ eq₂ rF₂ rG₂
        with Σinj≡ (trans (sym eq₁) eq₂)
...       | (refl , refl) =
            (λ t h →
               (projl h
               , ( projl (irrel₁ (ctrnᵀ (red→≅ᵀ rF₁) (csymᵀ (red→≅ᵀ rF₂))) ⊩F ⊩F')
                         (fst t) (dfst (projr h))
                 , projl (irrel₁ (≅ᵀ-sub (single (fst t))
                                   (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                                 (⊩G (fst t) (dfst (projr h)))
                                 (⊩G' (fst t)
                                   (projl (irrel₁ (ctrnᵀ (red→≅ᵀ rF₁)
                                                         (csymᵀ (red→≅ᵀ rF₂)))
                                                  ⊩F ⊩F') (fst t) (dfst (projr h)))))
                         (snd t) (dsnd (projr h)) )))
          , (λ t h →
               (projl h
               , ( projr (irrel₁ (ctrnᵀ (red→≅ᵀ rF₁) (csymᵀ (red→≅ᵀ rF₂))) ⊩F ⊩F')
                         (fst t) (dfst (projr h))
                 , projr (irrel₁ (≅ᵀ-sub (single (fst t))
                                   (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                                 (⊩G (fst t)
                                   (projr (irrel₁ (ctrnᵀ (red→≅ᵀ rF₁)
                                                         (csymᵀ (red→≅ᵀ rF₂)))
                                                  ⊩F ⊩F') (fst t) (dfst (projr h))))
                                 (⊩G' (fst t) (dfst (projr h))))
                         (snd t) (dsnd (projr h)) )))

-- the real `Π` case.
irrel₁ c (⊩₁Π p ⊩F ⊩G) (⊩₁Π q ⊩F' ⊩G') with joinW c p q
... | E , (πE₁ , πE₂) with Π-reduct πE₁ | Π-reduct πE₂
...   | mkΠRed F₁ G₁ eq₁ rF₁ rG₁ | mkΠRed F₂ G₂ eq₂ rF₂ rG₂
        with Πinj≡ (trans (sym eq₁) eq₂)
...       | (refl , refl) =
            (λ t h → (projl h , λ u r' →
               projl (irrel₁ (≅ᵀ-sub (single u)
                               (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                             (⊩G u (projr (irrel₁ (ctrnᵀ (red→≅ᵀ rF₁)
                                                         (csymᵀ (red→≅ᵀ rF₂)))
                                                  ⊩F ⊩F') u r'))
                             (⊩G' u r'))
                     (app t u)
                     (projr h u (projr (irrel₁ (ctrnᵀ (red→≅ᵀ rF₁)
                                                      (csymᵀ (red→≅ᵀ rF₂)))
                                               ⊩F ⊩F') u r'))))
          , (λ t h → (projl h , λ u r →
               projr (irrel₁ (≅ᵀ-sub (single u)
                               (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                             (⊩G u r)
                             (⊩G' u (projl (irrel₁ (ctrnᵀ (red→≅ᵀ rF₁)
                                                          (csymᵀ (red→≅ᵀ rF₂)))
                                                   ⊩F ⊩F') u r)))
                     (app t u)
                     (projr h u (projl (irrel₁ (ctrnᵀ (red→≅ᵀ rF₁)
                                                      (csymᵀ (red→≅ᵀ rF₂)))
                                               ⊩F ⊩F') u r))))

------------------------------------------------------------------------
-- 4b. FORWARD TRANSFER and CONVERSION at level 1.
------------------------------------------------------------------------

fwd₁ : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩₁ A → ⊩₁ B

fwd₁ p (⊩₁base q) with confluentᵀ p q
... | E , (bE , baseE) with base-nf baseE
...   | refl = ⊩₁base bE

fwd₁ p (⊩₁U q) with confluentᵀ p q
... | E , (uE , UE) with U-nf UE
...   | refl = ⊩₁U uE

fwd₁ p (⊩₁ne q n) with confluentᵀ p q
... | E , (bE , elE) with El-ne-reduct n elE
...   | mkElNe n' n'e refl = ⊩₁ne bE n'e

fwd₁ p (⊩₁Π q ⊩F ⊩G) with confluentᵀ p q
... | E , (bE , πE) with Π-reduct πE
...   | mkΠRed F₁ G₁ refl rF rG =
        ⊩₁Π bE (fwd₁ rF ⊩F)
              (λ u r → fwd₁ (⟶ᵀ*-sub (single u) rG)
                            (⊩G u (projr (irrel₁ (red→≅ᵀ rF) ⊩F (fwd₁ rF ⊩F)) u r)))

fwd₁ p (⊩₁Σ q ⊩F ⊩G) with confluentᵀ p q
... | E , (bE , σE) with Σ-reduct σE
...   | mkΣRed F₁ G₁ refl rF rG =
        ⊩₁Σ bE (fwd₁ rF ⊩F)
              (λ u r → fwd₁ (⟶ᵀ*-sub (single u) rG)
                            (⊩G u (projr (irrel₁ (red→≅ᵀ rF) ⊩F (fwd₁ rF ⊩F)) u r)))

fwd₁ p (⊩₁Hom q s) with confluentᵀ p q
... | E , (bE , hE) with Hom-stk-reduct s hE
...   | mkHomStk _ _ _ s' refl = ⊩₁Hom bE s'

-- ★ the shape `⊢conv` needs.
conv₁ : {A B : RTy Γ} → A ≅ᵀ B → ⊩₁ A → ⊩₁ B
conv₁ c R with church-rosserᵀ c
... | C , (aC , bC) = bwd₁ bC (fwd₁ aC R)

------------------------------------------------------------------------
-- 4c. Candidate conditions and head expansion, at level 1.
--
-- Each `U` case's SECOND component is discharged by exactly one level-0
-- construction: `CR3₁` by `⊩₀ne` (a neutral code IS a neutral type), `exp₁` by
-- `bwd₀` (the decoded type travels backward along the code's step).
------------------------------------------------------------------------

CR1₁ : {A : RTy Γ} (R : ⊩₁ A) {t : RTm Γ} → R ⊩₁∋ t → SN t
CR1₁ (⊩₁base _)  h = h
CR1₁ (⊩₁U _)     h = projl h
CR1₁ (⊩₁ne _ _)  h = h
CR1₁ (⊩₁Π _ _ _) h = projl h
CR1₁ (⊩₁Σ _ _ _) h = projl h
CR1₁ (⊩₁Hom _ _) h = h

CR3₁ : {A : RTy Γ} (R : ⊩₁ A) {t : RTm Γ} → SNe t → R ⊩₁∋ t
CR3₁ (⊩₁base _)    nt = sn-ne nt
CR3₁ (⊩₁U _)       nt = (sn-ne nt , ⊩₀ne doneᵀ (sne→ne nt))
CR3₁ (⊩₁ne _ _)    nt = sn-ne nt
CR3₁ (⊩₁Hom _ _)   nt = sn-ne nt
CR3₁ (⊩₁Π _ ⊩F ⊩G) nt =
  (sn-ne nt , λ u ru → CR3₁ (⊩G u ru) (sne-app nt (CR1₁ ⊩F ru)))
CR3₁ (⊩₁Σ _ ⊩F ⊩G) {t} nt =
  (sn-ne nt , ( CR3₁ ⊩F (sne-fst nt)
              , CR3₁ (⊩G (fst t) (CR3₁ ⊩F (sne-fst nt))) (sne-snd nt) ))

exp₁ : {A : RTy Γ} (R : ⊩₁ A) {t t' : RTm Γ} → SNRed t t' → R ⊩₁∋ t' → R ⊩₁∋ t
exp₁ (⊩₁base _)    r h = sn-exp r h
exp₁ (⊩₁ne _ _)    r h = sn-exp r h
exp₁ (⊩₁Hom _ _)   r h = sn-exp r h
exp₁ (⊩₁U _)       r h =
  (sn-exp r (projl h) , bwd₀ (⟶ᵀ*-El (step (snr→⟶ r) done)) (projr h))
exp₁ (⊩₁Π _ ⊩F ⊩G) r h =
  (sn-exp r (projl h) , λ v rv → exp₁ (⊩G v rv) (snr-app r) (projr h v rv))
exp₁ (⊩₁Σ {G = G} _ ⊩F ⊩G) {t} {t'} r h =
  ( sn-exp r (projl h)
  , ( exp₁ ⊩F (snr-fst r) (dfst (projr h))
    , projl (irrel₁ (csymᵀ (red→≅ᵀ (subTy-monoˢ
                              (single-mono (step (ξ-fst (snr→⟶ r)) done)) G)))
                    (⊩G (fst t') (dfst (projr h)))
                    (⊩G (fst t) (exp₁ ⊩F (snr-fst r) (dfst (projr h)))))
            (snd t)
            (exp₁ (⊩G (fst t') (dfst (projr h))) (snr-snd r) (dsnd (projr h))) ))

⊩var₁ : {A : RTy Γ} (R : ⊩₁ A) (x : Var Γ) → R ⊩₁∋ var x
⊩var₁ R x = CR3₁ R (sne-var x)

------------------------------------------------------------------------
-- ★ 5. THE LEVEL-0 → LEVEL-1 EMBEDDING.
--
-- Needed by `fund-ty`'s `ty-El` case, which lands at level 0.  Mutual with a
-- membership-coherence bi-implication, for the same reason `irrel` is a
-- bi-implication: the `Π` case must move a member of the level-1 domain down to
-- the level-0 domain before it can apply the level-0 family.
------------------------------------------------------------------------

emb : {A : RTy Γ} → ⊩₀ A → ⊩₁ A
emb-coh : {A : RTy Γ} (R : ⊩₀ A) →
          ((t : RTm Γ) → R ⊩₀∋ t → (emb R) ⊩₁∋ t)
        × ((t : RTm Γ) → (emb R) ⊩₁∋ t → R ⊩₀∋ t)

emb (⊩₀base p)    = ⊩₁base p
emb (⊩₀Hom p s)   = ⊩₁Hom p s
emb (⊩₀ne p n)    = ⊩₁ne p n
emb (⊩₀Π p ⊩F ⊩G) =
  ⊩₁Π p (emb ⊩F) (λ u r → emb (⊩G u (projr (emb-coh ⊩F) u r)))
emb (⊩₀Σ p ⊩F ⊩G) =
  ⊩₁Σ p (emb ⊩F) (λ u r → emb (⊩G u (projr (emb-coh ⊩F) u r)))

emb-coh (⊩₀base _) = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀Hom _ _) = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀ne _ _) = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀Σ _ ⊩F ⊩G) =
    (λ t h → (projl h
             , ( projl (emb-coh ⊩F) (fst t) (dfst (projr h))
               , projl (emb-coh (⊩G (fst t)
                          (projr (emb-coh ⊩F) (fst t)
                            (projl (emb-coh ⊩F) (fst t) (dfst (projr h))))))
                       (snd t)
                       (projl (irrel₀ crflᵀ
                                (⊩G (fst t) (dfst (projr h)))
                                (⊩G (fst t)
                                  (projr (emb-coh ⊩F) (fst t)
                                    (projl (emb-coh ⊩F) (fst t) (dfst (projr h))))))
                              (snd t) (dsnd (projr h))) )))
  , (λ t h → (projl h
             , ( projr (emb-coh ⊩F) (fst t) (dfst (projr h))
               , projl (irrel₀ crflᵀ
                          (⊩G (fst t)
                            (projr (emb-coh ⊩F) (fst t)
                              (projl (emb-coh ⊩F) (fst t)
                                (projr (emb-coh ⊩F) (fst t) (dfst (projr h))))))
                          (⊩G (fst t) (projr (emb-coh ⊩F) (fst t) (dfst (projr h)))))
                       (snd t)
                       (projr (emb-coh (⊩G (fst t)
                                 (projr (emb-coh ⊩F) (fst t)
                                   (projl (emb-coh ⊩F) (fst t)
                                     (projr (emb-coh ⊩F) (fst t) (dfst (projr h)))))))
                              (snd t)
                              (projl (irrel₁ crflᵀ
                                       (emb (⊩G (fst t)
                                         (projr (emb-coh ⊩F) (fst t) (dfst (projr h)))))
                                       (emb (⊩G (fst t)
                                         (projr (emb-coh ⊩F) (fst t)
                                           (projl (emb-coh ⊩F) (fst t)
                                             (projr (emb-coh ⊩F) (fst t) (dfst (projr h))))))))
                                     (snd t) (dsnd (projr h)))) )))
emb-coh (⊩₀Π _ ⊩F ⊩G) =
    (λ t h → (projl h , λ u r₁ →
       projl (emb-coh (⊩G u (projr (emb-coh ⊩F) u r₁)))
             (app t u)
             (projr h u (projr (emb-coh ⊩F) u r₁))))
  , (λ t h → (projl h , λ u r₀ →
       -- ⚠ the round trip `⊩F →₁ →₀` is not definitionally the identity, so the
       -- family lands at `⊩G u r₀'` for a DIFFERENT proof `r₀'` of the same
       -- membership.  Both are `⊩₀` derivations of the SAME type, so `irrel₀`
       -- at `crflᵀ` bridges them — proof-irrelevance in the membership argument,
       -- for free from the transfer layer.
       projl (irrel₀ crflᵀ
                (⊩G u (projr (emb-coh ⊩F) u (projl (emb-coh ⊩F) u r₀)))
                (⊩G u r₀))
             (app t u)
             (projr (emb-coh (⊩G u (projr (emb-coh ⊩F) u (projl (emb-coh ⊩F) u r₀))))
                    (app t u)
                    (projr h u (projl (emb-coh ⊩F) u r₀)))))

------------------------------------------------------------------------
-- 6. THE SEMANTIC TYPING RULES.
------------------------------------------------------------------------

sem-var : {A : RTy Γ} (R : ⊩₁ A) (x : Var Γ) → R ⊩₁∋ var x
sem-var = ⊩var₁

sem-conv : {A B : RTy Γ} (c : A ≅ᵀ B) (R : ⊩₁ A) (S : ⊩₁ B) {t : RTm Γ} →
           R ⊩₁∋ t → S ⊩₁∋ t
sem-conv c R S {t} h = projl (irrel₁ c R S) t h

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

-- Σ' introduction and elimination.  `sem-fst`/`sem-snd` are the two projections
-- of the membership clause; `sem-pair` is the one with content, because
-- `fst (pair a b) ⟶ a` moves the SECOND component's TYPE (`G[fst (pair a b)]`
-- vs `G[a]`), so it needs `exp₁` at both components and `irrel₁` to bridge.
sem-fst : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
          (p : A ⟶ᵀ* Σ' F G) (⊩F : ⊩₁ F)
          (⊩G : (u : RTm Γ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) G))
          {t : RTm Γ} → (⊩₁Σ p ⊩F ⊩G) ⊩₁∋ t → ⊩F ⊩₁∋ fst t
sem-fst p ⊩F ⊩G h = dfst (projr h)

sem-snd : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
          (p : A ⟶ᵀ* Σ' F G) (⊩F : ⊩₁ F)
          (⊩G : (u : RTm Γ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) G))
          {t : RTm Γ} (h : (⊩₁Σ p ⊩F ⊩G) ⊩₁∋ t) →
          (⊩G (fst t) (dfst (projr h))) ⊩₁∋ snd t
sem-snd p ⊩F ⊩G h = dsnd (projr h)

sem-pair : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
           (p : A ⟶ᵀ* Σ' F G) (⊩F : ⊩₁ F)
           (⊩G : (u : RTm Γ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) G))
           {a b : RTm Γ} → SN a → SN b →
           (ra : ⊩F ⊩₁∋ a) → (⊩G a ra) ⊩₁∋ b →
           (⊩₁Σ p ⊩F ⊩G) ⊩₁∋ pair a b
sem-pair {G = G} p ⊩F ⊩G {a} {b} sna snb ra rb =
  ( sn-pair sna snb
  , ( exp₁ ⊩F (snr-βfst snb) ra
    , projl (irrel₁ (csymᵀ (red→≅ᵀ (subTy-monoˢ
                              (single-mono (step (βfst a b) done)) G)))
                    (⊩G a ra)
                    (⊩G (fst (pair a b)) (exp₁ ⊩F (snr-βfst snb) ra)))
            (snd (pair a b))
            (exp₁ (⊩G a ra) (snr-βsnd sna) rb) ))

-- ★ the `ty-El` obligation: one projection, level 1 → 0.
sem-El : {A : RTy Γ} (p : A ⟶ᵀ* U) {c : RTm Γ} → (⊩₁U p) ⊩₁∋ c → ⊩₀ (El c)
sem-El p h = projr h

sem-⌜base⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) → (⊩₁U p) ⊩₁∋ ⌜base⌝
sem-⌜base⌝ p = (sn-cb , ⊩₀base (stepᵀ El-⌜base⌝ doneᵀ))

-- ★ where PREDICATIVITY does structural work: the decoding of a compound code
-- is a level-0 `Π` built from the decodings of its STRICTLY SMALLER components.
sem-⌜Π⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) {c : RTm Γ} {d : RTm (Γ ∙)}
        → SN c → SN d
        → (⊩c : ⊩₀ (El c))
        → ((u : RTm Γ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) d)))
        → (⊩₁U p) ⊩₁∋ ⌜Π⌝ c d
sem-⌜Π⌝ p snc snD ⊩c f =
  (sn-cΠ snc snD , ⊩₀Π (stepᵀ (El-⌜Π⌝ _ _) doneᵀ) ⊩c f)

sem-⌜Σ⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) {c : RTm Γ} {d : RTm (Γ ∙)}
        → SN c → SN d
        → (⊩c : ⊩₀ (El c))
        → ((u : RTm Γ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) d)))
        → (⊩₁U p) ⊩₁∋ ⌜Σ⌝ c d
sem-⌜Σ⌝ p snc snD ⊩c f =
  (sn-cΣ snc snD , ⊩₀Σ (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ) ⊩c f)

------------------------------------------------------------------------
-- 6b. ★ W2 — `sem-Hom` (`homSem₁`): the SEMANTIC ACTION OF `Hom`.
--
-- Given a semantic type and two members, the `Hom` between them is a
-- semantic type.  BY STRUCTURAL RECURSION ON THE `⊩₁` DERIVATION — the
-- recursive calls go through the stored `Π`-family, which is the SAME,
-- ALREADY-HANDLED scope pattern (`⊩G u r` is a structural component).  This
-- is the measured answer to the `SpikeHomLR` gate W2 carried: the `Hom`
-- clause needs NO member of `⊩` at a larger scope.
--
--   * stuck heads (`base`/`ne`/`Σ'`/stuck-`Hom`): one `⊩₁Hom` each;
--   * `Π`: unfold pointwise, recurse through the family — `wk-single`
--     rewrites `(wk a)[v] · v` back to `a · v`;
--   * `U`: DIRECTED UNIVALENCE does the work — the members of `⊩₁U` carry
--     `⊩₀ (El _)` (the stratification's payload), which after `emb` is
--     exactly the domain and codomain the unfolded `Π` needs.
------------------------------------------------------------------------

wk-single : {v : RTm Γ} (t : RTm Γ) → subTm (single v) (renTm vs t) ≡ t
wk-single t = trans (subTm-renTm t) (subTm-id t)

homSem₁ : {A : RTy Γ} (R : ⊩₁ A) {a b : RTm Γ} →
          R ⊩₁∋ a → R ⊩₁∋ b → ⊩₁ (Hom A a b)
homSem₁ (⊩₁base p)    ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) sh-base
homSem₁ (⊩₁ne p n)    ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-ne n)
homSem₁ (⊩₁Σ p ⊩F ⊩G) ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) sh-Σ
homSem₁ (⊩₁Hom p s)   ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom s)
homSem₁ (⊩₁U p) {c} {d} hc hd =
  ⊩₁Π (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ p) (stepᵀ (Hom-U c d) doneᵀ))
      (emb (projr hc))
      (λ v r → subst ⊩₁_ (sym (cong El (wk-single d))) (emb (projr hd)))
homSem₁ (⊩₁Π {F = F} {G = G} p ⊩F ⊩G) {a} {b} ha hb =
  ⊩₁Π (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ p) (stepᵀ (Hom-Π F G a b) doneᵀ))
      ⊩F
      (λ v r →
        subst ⊩₁_
              (sym (Hom-cong₃ refl
                     (cong₂ app (wk-single a) refl)
                     (cong₂ app (wk-single b) refl)))
              (homSem₁ (⊩G v r) (projr ha v r) (projr hb v r)))

-- ★ W2 stage 1: `homSem₀` — the level-0 mirror, owed since `⌜Hom⌝` made
-- small types reach `Hom`s (`SpikeHomRefl`'s repeal of "level 0 needs no
-- `Hom` clause").  STRICTLY SIMPLER than `homSem₁`: level 0 has no `U`
-- clause, so directed univalence never fires here — four stuck heads and
-- the pointwise `Π` recursion.
homSem₀ : {A : RTy Γ} (R : ⊩₀ A) {a b : RTm Γ} →
          R ⊩₀∋ a → R ⊩₀∋ b → ⊩₀ (Hom A a b)
homSem₀ (⊩₀base p)    ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) sh-base
homSem₀ (⊩₀ne p n)    ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-ne n)
homSem₀ (⊩₀Σ p ⊩F ⊩G) ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) sh-Σ
homSem₀ (⊩₀Hom p s)   ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-Hom s)
homSem₀ (⊩₀Π {F = F} {G = G} p ⊩F ⊩G) {a} {b} ha hb =
  ⊩₀Π (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ p) (stepᵀ (Hom-Π F G a b) doneᵀ))
      ⊩F
      (λ v r →
        subst ⊩₀_
              (sym (Hom-cong₃ refl
                     (cong₂ app (wk-single a) refl)
                     (cong₂ app (wk-single b) refl)))
              (homSem₀ (⊩G v r) (projr ha v r) (projr hb v r)))

-- ★ `sem-⌜Hom⌝`: the `⌜Hom⌝` code is a semantic CODE — its decoding is a
-- small semantic type, via `homSem₀` and one decode step.
sem-⌜Hom⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) {c a b : RTm Γ}
          → SN c → SN a → SN b
          → (⊩c : ⊩₀ (El c))
          → ⊩c ⊩₀∋ a → ⊩c ⊩₀∋ b
          → (⊩₁U p) ⊩₁∋ ⌜Hom⌝ c a b
sem-⌜Hom⌝ p snc sna snb ⊩c ha hb =
  ( sn-cH snc sna snb
  , bwd₀ (stepᵀ (El-⌜Hom⌝ _ _ _) doneᵀ) (homSem₀ ⊩c ha hb) )

-- ★ `sem-hrefl`: while `hrefl` is operationally inert (stage 1), it is a
-- neutral, and neutrals inhabit every semantic type — in particular the
-- `Hom` at its own endpoints.
sem-hrefl : {F : RTy Γ} (R : ⊩₁ F) {c t : RTm Γ} → SN c → SN t →
            (ht : R ⊩₁∋ t) → (homSem₁ R ht ht) ⊩₁∋ hrefl c t
sem-hrefl R snc snt ht = CR3₁ (homSem₁ R ht ht) (sne-hrefl snc snt)

------------------------------------------------------------------------
-- 7. WEAK NORMALIZATION — exactly `NbEPDirDBDec.dec-conv`'s input.
------------------------------------------------------------------------

IsNormal : RTm Γ → Set
IsNormal t = ∀ {u} → ¬ (t ⟶ u)

record WN {Γ} (t : RTm Γ) : Set where
  constructor mkWN
  field
    nfm : RTm Γ
    rd  : t ⟶* nfm
    nrm : IsNormal nfm
    snf : SN nfm

record WNe {Γ} (t : RTm Γ) : Set where
  constructor mkWNe
  field
    nfm : RTm Γ
    rd  : t ⟶* nfm
    nrm : IsNormal nfm
    neu : SNe nfm

wn  : {t : RTm Γ} → SN t → WN t
wne : {t : RTm Γ} → SNe t → WNe t

wne (sne-var x) = mkWNe (var x) done (λ ()) (sne-var x)
wne (sne-app n u) with wne n | wn u
... | mkWNe n₁ r₁ nm₁ ne₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWNe (app n₁ n₂) (⟶*-trans (⟶*-appˡ r₁) (⟶*-appʳ r₂)) nrm'
            (sne-app ne₁ sn₂)
  where
    nrm' : IsNormal (app n₁ n₂)
    nrm' (ξ-appˡ q) = nm₁ q
    nrm' (ξ-appʳ q) = nm₂ q
wne (sne-fst n) with wne n
... | mkWNe n₁ r₁ nm₁ ne₁ = mkWNe (fst n₁) (⟶*-fst r₁) nrm' (sne-fst ne₁)
  where
    nrm' : IsNormal (fst n₁)
    nrm' (ξ-fst q) = nm₁ q
wne (sne-snd n) with wne n
... | mkWNe n₁ r₁ nm₁ ne₁ = mkWNe (snd n₁) (⟶*-snd r₁) nrm' (sne-snd ne₁)
  where
    nrm' : IsNormal (snd n₁)
    nrm' (ξ-snd q) = nm₁ q
wne (sne-hrefl c t) with wn c | wn t
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWNe (hrefl n₁ n₂) (⟶*-trans (⟶*-hreflᶜ r₁) (⟶*-hreflᵃ r₂)) nrm'
            (sne-hrefl sn₁ sn₂)
  where
    nrm' : IsNormal (hrefl n₁ n₂)
    nrm' (ξ-hreflᶜ q) = nm₁ q
    nrm' (ξ-hreflᵃ q) = nm₂ q

wn (sn-ne n) with wne n
... | mkWNe n₁ r₁ nm₁ ne₁ = mkWN n₁ r₁ nm₁ (sn-ne ne₁)
wn (sn-lam s) with wn s
... | mkWN n₁ r₁ nm₁ sn₁ = mkWN (lam n₁) (⟶*-lam r₁) nrm' (sn-lam sn₁)
  where
    nrm' : IsNormal (lam n₁)
    nrm' (ξ-lam q) = nm₁ q
wn (sn-pair a b) with wn a | wn b
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWN (pair n₁ n₂) (⟶*-trans (⟶*-pairˡ r₁) (⟶*-pairʳ r₂)) nrm'
           (sn-pair sn₁ sn₂)
  where
    nrm' : IsNormal (pair n₁ n₂)
    nrm' (ξ-pairˡ q) = nm₁ q
    nrm' (ξ-pairʳ q) = nm₂ q
wn sn-cb = mkWN ⌜base⌝ done (λ ()) sn-cb
wn (sn-cΠ c d) with wn c | wn d
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWN (⌜Π⌝ n₁ n₂) (⟶*-trans (⟶*-⌜Π⌝ˡ r₁) (⟶*-⌜Π⌝ʳ r₂)) nrm' (sn-cΠ sn₁ sn₂)
  where
    nrm' : IsNormal (⌜Π⌝ n₁ n₂)
    nrm' (ξ-⌜Π⌝ˡ q) = nm₁ q
    nrm' (ξ-⌜Π⌝ʳ q) = nm₂ q
wn (sn-cΣ c d) with wn c | wn d
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWN (⌜Σ⌝ n₁ n₂) (⟶*-trans (⟶*-⌜Σ⌝ˡ r₁) (⟶*-⌜Σ⌝ʳ r₂)) nrm' (sn-cΣ sn₁ sn₂)
  where
    nrm' : IsNormal (⌜Σ⌝ n₁ n₂)
    nrm' (ξ-⌜Σ⌝ˡ q) = nm₁ q
    nrm' (ξ-⌜Σ⌝ʳ q) = nm₂ q
wn (sn-cH c a b) with wn c | wn a | wn b
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ | mkWN n₃ r₃ nm₃ sn₃ =
      mkWN (⌜Hom⌝ n₁ n₂ n₃)
           (⟶*-trans (⟶*-⌜Hom⌝ᶜ r₁) (⟶*-trans (⟶*-⌜Hom⌝ˡ r₂) (⟶*-⌜Hom⌝ʳ r₃)))
           nrm' (sn-cH sn₁ sn₂ sn₃)
  where
    nrm' : IsNormal (⌜Hom⌝ n₁ n₂ n₃)
    nrm' (ξ-⌜Hom⌝ᶜ q) = nm₁ q
    nrm' (ξ-⌜Hom⌝ˡ q) = nm₂ q
    nrm' (ξ-⌜Hom⌝ʳ q) = nm₃ q
wn (sn-exp r h) with wn h
... | mkWN n₁ r₁ nm₁ sn₁ = mkWN n₁ (step (snr→⟶ r) r₁) nm₁ sn₁

-- ★ every member of every semantic type weakly normalizes, at both levels.
⊩wn₀ : {A : RTy Γ} (R : ⊩₀ A) {t : RTm Γ} → R ⊩₀∋ t → WN t
⊩wn₀ R h = wn (CR1₀ R h)

⊩wn₁ : {A : RTy Γ} (R : ⊩₁ A) {t : RTm Γ} → R ⊩₁∋ t → WN t
⊩wn₁ R h = wn (CR1₁ R h)

------------------------------------------------------------------------
-- 8. NON-VACUITY.
------------------------------------------------------------------------

-- `El ⌜base⌝` is a small semantic type, via one decoding step.
⊩₀El-base : ⊩₀ (El (⌜base⌝ {Γ}))
⊩₀El-base = ⊩₀base (stepᵀ El-⌜base⌝ doneᵀ)

-- the configuration erasure cannot see: a code decoding to a FUNCTION type.
⊩₀El-Π : ⊩₀ (El (⌜Π⌝ (⌜base⌝ {Γ}) ⌜base⌝))
⊩₀El-Π = ⊩₀Π (stepᵀ (El-⌜Π⌝ ⌜base⌝ ⌜base⌝) doneᵀ) ⊩₀El-base (λ u r → ⊩₀El-base)

-- transfer ACROSS the decode step, and back along conversion.
fwd-decode : ⊩₀ (Π (El (⌜base⌝ {Γ})) (El ⌜base⌝))
fwd-decode = fwd₀ (stepᵀ (El-⌜Π⌝ ⌜base⌝ ⌜base⌝) doneᵀ) ⊩₀El-Π

conv-decode : ⊩₀ (El (⌜Π⌝ (⌜base⌝ {Γ}) ⌜base⌝))
conv-decode = conv₀ (csymᵀ (credᵀ (El-⌜Π⌝ ⌜base⌝ ⌜base⌝))) fwd-decode

-- the embedding lands it at level 1.
⊩₁El-Π : ⊩₁ (El (⌜Π⌝ (⌜base⌝ {Γ}) ⌜base⌝))
⊩₁El-Π = emb ⊩₀El-Π

-- a real β-redex is `SN`, and `wn` computes its normal form on the nose.
redexTm : RTm (ε ∙)
redexTm = app (lam (var vz)) (var vz)

redexSN : SN redexTm
redexSN = sn-exp (snr-β (sn-ne (sne-var vz))) (sn-ne (sne-var vz))

redex-nf : WN.nfm (wn redexSN) ≡ var vz
redex-nf = refl
