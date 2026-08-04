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
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; ¬_; ⊥; ⊥-elim; Σ; _,_; _×_; ⊤ )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; ⌜Hom⌝; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub
        ; Ren; extR; Sub; subTy; subTm; extS; renTm
        ; subTm-renTm; subTm-id; Hom-cong₃; ⌜Hom⌝-cong₃ )
open import poc.OCP0009.NbEPDirDBType
  using ( single
        ; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ
        ; tr-J-base; tr-J-Σ; tr-taut; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ
        ; tr-J-Id; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ; ξ-idreflᵃ
        ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; El-⌜Id⌝; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ; ⊢⌜Id⌝; ⊢idrefl; ⊢jsub; ⊢ap
        ; hrefl-pw; tr-J-Hom; tr-pw
        ; _⟶*_; done; step
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ )
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; false
        ; pw?; stkC?; pwDom; pwBody; pwShift
        ; pw?-ren; stkC?-ren; pwBody-ren; pwDom-ren
        ; stk⊥pw; pw⊥stk )
open import poc.OCP0009.NbEPDirDBSR using ( ⟶ᵀ-sub; ≅ᵀ-sub )
open import poc.OCP0009.NbEPDirDBSubj using ( subTy-monoˢ )
open import poc.OCP0009.NbEPDirDBConf using ( single-mono; confluent )
open import poc.OCP0009.NbEPDirDBConf
  using ( ⟶*-trans; ⟶*-lam; ⟶*-appˡ; ⟶*-appʳ
        ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd
        ; ⟶*-⌜Π⌝ˡ; ⟶*-⌜Π⌝ʳ; ⟶*-⌜Σ⌝ˡ; ⟶*-⌜Σ⌝ʳ
        ; ⟶*-⌜Hom⌝ᶜ; ⟶*-⌜Hom⌝ˡ; ⟶*-⌜Hom⌝ʳ; ⟶*-hreflᶜ; ⟶*-hreflᵃ
        ; ⟶*-trᵈ; ⟶*-trᵖ; ⟶*-trᵉ; ⟶*-apᶜ; ⟶*-apᵇ; ⟶*-apᵖ )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; ⟶ᵀ*-Homᵀ
        ; confluentᵀ; church-rosserᵀ; Id-reduct
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

-- W2 stage 2: SHAPE CLASSIFIERS for the `tr` head strategy, as BOOLEAN
-- functions — shape-only, so renaming preserves them ON THE NOSE (the
-- anti-renaming bill is one equality per classifier) and every
-- refutation is definitional.
--   `spine?`    — safe app/fst/snd spine heads: never become `lam` or
--                 `pair` at the root;
--   `stablecd?` — codes that never become `⌜base⌝`/`⌜Σ⌝`-headed (the
--                 J-able heads) — what keeps an `hrefl` path inert;
--   `pathstk?`  — paths on which no `tr` root rule can EVER fire;
--   `trstk?`    — the permanently stuck `tr d p e` configurations: an
--                 inert path, or a lambda path at a `⌜Hom⌝`-headed
--                 motive (taut needs the LITERAL `var vz` motive, and
--                 pointwise composition is deferred with the canonicity
--                 package).
homheaded? : RTm Γ → 𝔹
homheaded? (⌜Hom⌝ _ _ _) = true
homheaded? _             = false

spine? stablecd? pathstk? nopw? deadmot? apstk? idstk? : RTm Γ → 𝔹
trstk? : RTm (Γ ∙) → RTm Γ → 𝔹
trlam? : RTm (Γ ∙) → 𝔹

spine? (var x)        = true
spine? (app t u)      = spine? t
spine? (fst t)        = spine? t
spine? (snd t)        = spine? t
spine? (⌜Π⌝ c d)      = true
spine? (⌜Hom⌝ c a b)  = true
-- W2b: an hrefl HEAD stays inert only if its code can never become
-- pw-able (else hrefl-pw turns it into a lam and the spine β-fires).
spine? (hrefl c t)    = nopw? c
spine? (tr d p e)     = trstk? d p
spine? (ap c b p)     = apstk? p
spine? (⌜Id⌝ c a b)   = true
spine? (idrefl c t)   = true
spine? (jsub d p e)   = idstk? p
spine? _              = false

-- W2b: `stablecd?` is now DEAD-CODE-ness — the code can never fire a
-- J rule (⌜base⌝/⌜Σ⌝/stk-⌜Hom⌝ excluded, as before) NOR the pointwise
-- unfold (⌜Π⌝ and pw-⌜Hom⌝ excluded, NEW).
stablecd? (var x)       = true
stablecd? (lam t)       = true
stablecd? (app t u)     = spine? t
stablecd? (pair a b)    = true
stablecd? (fst t)       = spine? t
stablecd? (snd t)       = spine? t
stablecd? (⌜Hom⌝ c a b) = stablecd? c
stablecd? (hrefl c t)   = true
stablecd? (ap c b p)    = apstk? p
stablecd? (idrefl c t)  = true
stablecd? (jsub d p e)  = idstk? p
stablecd? (tr d p e)    = trstk? d p
stablecd? _             = false

pathstk? (var x)        = true
pathstk? (lam t)        = false
pathstk? (app t u)      = spine? t
pathstk? (pair a b)     = true
pathstk? (fst t)        = spine? t
pathstk? (snd t)        = spine? t
pathstk? ⌜base⌝         = true
pathstk? (⌜Π⌝ c d)      = true
pathstk? (⌜Σ⌝ c d)      = true
pathstk? (⌜Hom⌝ c a b)  = true
pathstk? (hrefl c t)    = stablecd? c
pathstk? (tr d p e)     = trstk? d p
pathstk? (ap c b p)     = apstk? p
pathstk? (⌜Id⌝ c a b)   = true
pathstk? (idrefl c t)   = true
pathstk? (jsub d p e)   = idstk? p

-- ★ the two-former kernel: `jsub` is stuck forever iff its PATH never
-- becomes an `idrefl`: everything except idrefl itself is junk-stuck
-- (idrefl is inert, hrefl-paths only ever unfold to lams — still
-- stuck), and the eliminators recurse.
idstk? (var x)        = true
idstk? (lam t)        = true
idstk? (app t u)      = spine? t
idstk? (pair a b)     = true
idstk? (fst t)        = spine? t
idstk? (snd t)        = spine? t
idstk? ⌜base⌝         = true
idstk? (⌜Π⌝ c d)      = true
idstk? (⌜Σ⌝ c d)      = true
idstk? (⌜Hom⌝ c a b)  = true
idstk? (⌜Id⌝ c a b)   = true
idstk? (hrefl c t)    = true
idstk? (idrefl c t)   = false
idstk? (tr d p e)     = trstk? d p
idstk? (ap c b p)     = apstk? p
idstk? (jsub d p e)   = idstk? p

-- ★ directed `ap` (SpikeAp): `ap` is stuck forever iff its PATH never
-- becomes a canonical hrefl the J rule fires on: lam paths have NO ap
-- rule (permanently stuck), hrefl paths are stuck iff their code is
-- DEAD (`stablecd?` — never `stkC?`-true, never pw-able).
apstk? (var x)        = true
apstk? (lam t)        = true
apstk? (app t u)      = spine? t
apstk? (pair a b)     = true
apstk? (fst t)        = spine? t
apstk? (snd t)        = spine? t
apstk? ⌜base⌝         = true
apstk? (⌜Π⌝ c d)      = true
apstk? (⌜Σ⌝ c d)      = true
apstk? (⌜Hom⌝ c a b)  = true
apstk? (hrefl c t)    = stablecd? c
apstk? (tr d p e)     = trstk? d p
apstk? (ap c b p)     = apstk? p
apstk? (⌜Id⌝ c a b)   = true
apstk? (idrefl c t)   = true
apstk? (jsub d p e)   = idstk? p

-- W2b: a lam path fires tr-pw at a pw-able-⌜Hom⌝ motive with the
-- LITERAL `var vz` endpoint — stuck only when the code can never
-- become pw (`nopw?`); a non-vz VAR endpoint never matches the rule.
-- (Other motive/endpoint shapes are conservatively not-stuck.)
trstk? d (lam f)                        = trlam? d
-- J is ⌜Hom⌝-MOTIVE-KEYED (stage 3): at a `var` motive an `hrefl` path
-- is stuck unless its CODE can become pw (then hrefl-pw → lam → taut).
trstk? (var x) (hrefl c s) = nopw? c
trstk? d p                 = pathstk? p

-- W2b: codes that can NEVER become pw-able (closed under reduction —
-- constructor heads are stable, spines stay spines, and the hrefl-pw
-- unfold turns an hrefl-head into a lam-head, both dead).
-- the lam-path motive dispatch (path-major so `trstk? d (lam f)`
-- reduces at abstract motives).
trlam? (⌜Hom⌝ c a (var vz))     = deadmot? c
trlam? (⌜Hom⌝ c a (var (vs x))) = true
trlam? _                        = false

-- W2b final frontier: motive codes that are SPINE-DEAD (no CSR step
-- ever — `snr-tr-mot` normalizes the others) AND pw-immune.  The
-- hrefl clause RECURSES: an hrefl-code is dead iff its own code is
-- (a live inner code feeds snr-hreflᶜ/hrefl-pw through csr-here).
deadmot? (var x)        = true
deadmot? (lam t)        = true
deadmot? (app t u)      = spine? t
deadmot? (pair a b)     = true
deadmot? (fst t)        = spine? t
deadmot? (snd t)        = spine? t
deadmot? ⌜base⌝         = true
deadmot? (⌜Π⌝ c d)      = false
deadmot? (⌜Σ⌝ c d)      = true
deadmot? (⌜Hom⌝ c a b)  = deadmot? c
deadmot? (hrefl c t)    = deadmot? c
deadmot? (tr d p e)     = trstk? d p
deadmot? (ap c b p)     = apstk? p
deadmot? (⌜Id⌝ c a b)   = true
deadmot? (idrefl c t)   = true
deadmot? (jsub d p e)   = idstk? p

nopw? (var x)        = true
nopw? (lam t)        = true
nopw? (app t u)      = spine? t
nopw? (pair a b)     = true
nopw? (fst t)        = spine? t
nopw? (snd t)        = spine? t
nopw? ⌜base⌝         = true
nopw? (⌜Π⌝ c d)      = false
nopw? (⌜Σ⌝ c d)      = true
nopw? (⌜Hom⌝ c a b)  = nopw? c
nopw? (hrefl c t)    = true
nopw? (tr d p e)     = trstk? d p
nopw? (ap c b p)     = true
nopw? (⌜Id⌝ c a b)   = true
nopw? (idrefl c t)   = true
nopw? (jsub d p e)   = idstk? p

f≢t : false ≡ true → ⊥
f≢t ()

-- each classifier is closed under reduction (`true` is preserved; the
-- root rules that would break a shape are refuted definitionally or
-- through the W2b key-disjointness lemmas below).

-- key disjointness (W2b): a pw-able code is never dead, never
-- pw-immune; a stable (J-able) code is never dead; and a head-redex is
-- never a pw code — the facts the keyed dispatches turn on.
pw⊥dead : (C : RTm Γ) → pw? C ≡ true → stablecd? C ≡ false
pw⊥dead (var x) ()
pw⊥dead (lam t) ()
pw⊥dead (app t u) ()
pw⊥dead (pair a b) ()
pw⊥dead (fst t) ()
pw⊥dead (snd t) ()
pw⊥dead ⌜base⌝ ()
pw⊥dead (⌜Π⌝ c d) h = refl
pw⊥dead (⌜Σ⌝ c d) ()
pw⊥dead (⌜Hom⌝ C a b) h = pw⊥dead C h
pw⊥dead (hrefl c t) ()
pw⊥dead (tr d p e) ()

nopw⊥pw : (C : RTm Γ) → nopw? C ≡ true → pw? C ≡ false
nopw⊥pw (var x) h = refl
nopw⊥pw (lam t) h = refl
nopw⊥pw (app t u) h = refl
nopw⊥pw (pair a b) h = refl
nopw⊥pw (fst t) h = refl
nopw⊥pw (snd t) h = refl
nopw⊥pw ⌜base⌝ h = refl
nopw⊥pw (⌜Π⌝ c d) ()
nopw⊥pw (⌜Σ⌝ c d) h = refl
nopw⊥pw (⌜Hom⌝ C a b) h = nopw⊥pw C h
nopw⊥pw (hrefl c t) h = refl
nopw⊥pw (tr d p e) h = refl
nopw⊥pw (ap c b p) h = refl
nopw⊥pw (⌜Id⌝ c a b) h = refl
nopw⊥pw (idrefl c t) h = refl
nopw⊥pw (jsub d p e) h = refl

deadmot→nopw : (C : RTm Γ) → deadmot? C ≡ true → nopw? C ≡ true
deadmot→nopw (var x) h = refl
deadmot→nopw (lam t) h = refl
deadmot→nopw (app t u) h = h
deadmot→nopw (pair a b) h = refl
deadmot→nopw (fst t) h = h
deadmot→nopw (snd t) h = h
deadmot→nopw ⌜base⌝ h = refl
deadmot→nopw (⌜Π⌝ c d) ()
deadmot→nopw (⌜Σ⌝ c d) h = refl
deadmot→nopw (⌜Hom⌝ C a b) h = deadmot→nopw C h
deadmot→nopw (hrefl c t) h = refl
deadmot→nopw (tr d p e) h = h
deadmot→nopw (ap c b p) h = refl
deadmot→nopw (⌜Id⌝ c a b) h = refl
deadmot→nopw (idrefl c t) h = refl
deadmot→nopw (jsub d p e) h = h

stk→deadmot : (C : RTm Γ) → stkC? C ≡ true → deadmot? C ≡ true
stk→deadmot (var x) ()
stk→deadmot (lam t) ()
stk→deadmot (app t u) ()
stk→deadmot (pair a b) ()
stk→deadmot (fst t) ()
stk→deadmot (snd t) ()
stk→deadmot ⌜base⌝ h = refl
stk→deadmot (⌜Π⌝ c d) ()
stk→deadmot (⌜Σ⌝ c d) h = refl
stk→deadmot (⌜Id⌝ c a b) h = refl
stk→deadmot (⌜Hom⌝ C a b) h = stk→deadmot C h
stk→deadmot (hrefl c t) ()
stk→deadmot (tr d p e) ()

stk⊥dead : (C : RTm Γ) → stkC? C ≡ true → stablecd? C ≡ false
stk⊥dead (var x) ()
stk⊥dead (lam t) ()
stk⊥dead (app t u) ()
stk⊥dead (pair a b) ()
stk⊥dead (fst t) ()
stk⊥dead (snd t) ()
stk⊥dead ⌜base⌝ h = refl
stk⊥dead (⌜Π⌝ c d) ()
stk⊥dead (⌜Σ⌝ c d) h = refl
stk⊥dead (⌜Id⌝ c a b) h = refl
stk⊥dead (⌜Hom⌝ C a b) h = stk⊥dead C h
stk⊥dead (hrefl c t) ()
stk⊥dead (tr d p e) ()

-- a head-reducible term is never a pw code (SNRed's subjects are
-- app/fst/snd/hrefl/tr-headed, never ⌜Π⌝/⌜Hom⌝-constructor-headed) —
-- proven after SNRed below (snr-nonpw).

homheaded?-red : {t t' : RTm Γ} → t ⟶ t' →
                 homheaded? t ≡ true → homheaded? t' ≡ true
spine?-red    : {t t' : RTm Γ} → t ⟶ t' → spine? t ≡ true → spine? t' ≡ true
stablecd?-red : {t t' : RTm Γ} → t ⟶ t' →
                stablecd? t ≡ true → stablecd? t' ≡ true
pathstk?-red  : {t t' : RTm Γ} → t ⟶ t' →
                pathstk? t ≡ true → pathstk? t' ≡ true
nopw?-red     : {t t' : RTm Γ} → t ⟶ t' → nopw? t ≡ true → nopw? t' ≡ true
apstk?-red    : {t t' : RTm Γ} → t ⟶ t' → apstk? t ≡ true → apstk? t' ≡ true
idstk?-red    : {t t' : RTm Γ} → t ⟶ t' → idstk? t ≡ true → idstk? t' ≡ true
deadmot?-red  : {t t' : RTm Γ} → t ⟶ t' →
                deadmot? t ≡ true → deadmot? t' ≡ true
trstk?-red-d  : {d d' : RTm (Γ ∙)} {p : RTm Γ} → d ⟶ d' →
                trstk? d p ≡ true → trstk? d' p ≡ true
trstk?-red-p  : {d : RTm (Γ ∙)} {p p' : RTm Γ} → p ⟶ p' →
                trstk? d p ≡ true → trstk? d p' ≡ true

homheaded?-red (β _ _) ()
homheaded?-red (βfst _ _) ()
homheaded?-red (βsnd _ _) ()
homheaded?-red (ξ-lam _) ()
homheaded?-red (ξ-appˡ _) ()
homheaded?-red (ξ-appʳ _) ()
homheaded?-red (ξ-pairˡ _) ()
homheaded?-red (ξ-pairʳ _) ()
homheaded?-red (ξ-fst _) ()
homheaded?-red (ξ-snd _) ()
homheaded?-red (ξ-⌜Π⌝ˡ _) ()
homheaded?-red (ξ-⌜Π⌝ʳ _) ()
homheaded?-red (ξ-⌜Σ⌝ˡ _) ()
homheaded?-red (ξ-⌜Σ⌝ʳ _) ()
homheaded?-red (ξ-⌜Hom⌝ᶜ r) h = h
homheaded?-red (ξ-⌜Hom⌝ˡ r) h = h
homheaded?-red (ξ-⌜Hom⌝ʳ r) h = h
homheaded?-red (ξ-hreflᶜ _) ()
homheaded?-red (ξ-hreflᵃ _) ()
homheaded?-red (hrefl-pw _ _ _) ()
homheaded?-red (tr-J-base _ _ _ _ _) ()
homheaded?-red (tr-J-Σ _ _ _ _ _ _ _) ()
homheaded?-red (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
homheaded?-red (tr-taut _ _) ()
homheaded?-red (tr-pw _ _ _ _ _) ()
homheaded?-red (ξ-trᵈ _) ()
homheaded?-red (ξ-trᵖ _) ()
homheaded?-red (ξ-trᵉ _) ()

spine?-red (β _ _) ()
spine?-red (βfst _ _) ()
spine?-red (βsnd _ _) ()
spine?-red (ξ-lam _) ()
spine?-red (ξ-appˡ r) h = spine?-red r h
spine?-red (ξ-appʳ r) h = h
spine?-red (ξ-pairˡ _) ()
spine?-red (ξ-pairʳ _) ()
spine?-red (ξ-fst r) h = spine?-red r h
spine?-red (ξ-snd r) h = spine?-red r h
spine?-red (ξ-⌜Π⌝ˡ r) h = h
spine?-red (ξ-⌜Π⌝ʳ r) h = h
spine?-red (ξ-⌜Σ⌝ˡ _) ()
spine?-red (ξ-⌜Σ⌝ʳ _) ()
spine?-red (ξ-⌜Hom⌝ᶜ r) h = h
spine?-red (ξ-⌜Hom⌝ˡ r) h = h
spine?-red (ξ-⌜Hom⌝ʳ r) h = h
spine?-red (ξ-hreflᶜ r) h = nopw?-red r h
spine?-red (ξ-hreflᵃ r) h = h
spine?-red (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (nopw⊥pw C₀ h)) kp))
spine?-red (tr-J-base _ _ _ _ _) ()
spine?-red (tr-J-Σ _ _ _ _ _ _ _) ()
spine?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) h))
spine?-red (tr-taut _ _) ()
spine?-red (tr-pw c₁ _ _ _ kp) h = ⊥-elim (f≢t (trans (sym (nopw⊥pw c₁ (deadmot→nopw c₁ h))) kp))
spine?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
spine?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
spine?-red (ξ-trᵉ r) h = h
spine?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
spine?-red (ξ-apᶜ r) h = h
spine?-red (ξ-apᵇ r) h = h
spine?-red (ξ-apᵖ r) h = apstk?-red r h
spine?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
spine?-red (jsub-refl _ _ _ _) ()
spine?-red (ξ-⌜Id⌝ᶜ r) h = h
spine?-red (ξ-⌜Id⌝ˡ r) h = h
spine?-red (ξ-⌜Id⌝ʳ r) h = h
spine?-red (ξ-idreflᶜ r) h = h
spine?-red (ξ-idreflᵃ r) h = h
spine?-red (ξ-jsubᵈ r) h = h
spine?-red (ξ-jsubᵖ r) h = idstk?-red r h
spine?-red (ξ-jsubᵉ r) h = h

stablecd?-red (β _ _) ()
stablecd?-red (βfst _ _) ()
stablecd?-red (βsnd _ _) ()
stablecd?-red (ξ-lam r) h = h
stablecd?-red (ξ-appˡ r) h = spine?-red r h
stablecd?-red (ξ-appʳ r) h = h
stablecd?-red (ξ-pairˡ r) h = h
stablecd?-red (ξ-pairʳ r) h = h
stablecd?-red (ξ-fst r) h = spine?-red r h
stablecd?-red (ξ-snd r) h = spine?-red r h
stablecd?-red (ξ-⌜Π⌝ˡ _) ()
stablecd?-red (ξ-⌜Π⌝ʳ _) ()
stablecd?-red (ξ-⌜Σ⌝ˡ _) ()
stablecd?-red (ξ-⌜Σ⌝ʳ _) ()
stablecd?-red (ξ-⌜Hom⌝ᶜ r) h = stablecd?-red r h
stablecd?-red (ξ-⌜Hom⌝ˡ r) h = h
stablecd?-red (ξ-⌜Hom⌝ʳ r) h = h
stablecd?-red (ξ-hreflᶜ r) h = h
stablecd?-red (ξ-hreflᵃ r) h = h
stablecd?-red (hrefl-pw C₀ s₀ kp) h = refl
stablecd?-red (tr-J-base _ _ _ _ _) ()
stablecd?-red (tr-J-Σ _ _ _ _ _ _ _) ()
stablecd?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) h))
stablecd?-red (tr-taut _ _) ()
stablecd?-red (tr-pw c₁ _ _ _ kp) h = ⊥-elim (f≢t (trans (sym (nopw⊥pw c₁ (deadmot→nopw c₁ h))) kp))
stablecd?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
stablecd?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
stablecd?-red (ξ-trᵉ r) h = h
stablecd?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
stablecd?-red (ξ-apᶜ r) h = h
stablecd?-red (ξ-apᵇ r) h = h
stablecd?-red (ξ-apᵖ r) h = apstk?-red r h
stablecd?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
stablecd?-red (jsub-refl _ _ _ _) ()
stablecd?-red (ξ-⌜Id⌝ᶜ r) ()
stablecd?-red (ξ-⌜Id⌝ˡ r) ()
stablecd?-red (ξ-⌜Id⌝ʳ r) ()
stablecd?-red (ξ-idreflᶜ r) h = h
stablecd?-red (ξ-idreflᵃ r) h = h
stablecd?-red (ξ-jsubᵈ r) h = h
stablecd?-red (ξ-jsubᵖ r) h = idstk?-red r h
stablecd?-red (ξ-jsubᵉ r) h = h

pathstk?-red (β _ _) ()
pathstk?-red (βfst _ _) ()
pathstk?-red (βsnd _ _) ()
pathstk?-red (ξ-lam _) ()
pathstk?-red (ξ-appˡ r) h = spine?-red r h
pathstk?-red (ξ-appʳ r) h = h
pathstk?-red (ξ-pairˡ r) h = h
pathstk?-red (ξ-pairʳ r) h = h
pathstk?-red (ξ-fst r) h = spine?-red r h
pathstk?-red (ξ-snd r) h = spine?-red r h
pathstk?-red (ξ-⌜Π⌝ˡ r) h = h
pathstk?-red (ξ-⌜Π⌝ʳ r) h = h
pathstk?-red (ξ-⌜Σ⌝ˡ r) h = h
pathstk?-red (ξ-⌜Σ⌝ʳ r) h = h
pathstk?-red (ξ-⌜Hom⌝ᶜ r) h = h
pathstk?-red (ξ-⌜Hom⌝ˡ r) h = h
pathstk?-red (ξ-⌜Hom⌝ʳ r) h = h
pathstk?-red (ξ-hreflᶜ r) h = stablecd?-red r h
pathstk?-red (ξ-hreflᵃ r) h = h
pathstk?-red (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
pathstk?-red (tr-J-base _ _ _ _ _) ()
pathstk?-red (tr-J-Σ _ _ _ _ _ _ _) ()
pathstk?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) h))
pathstk?-red (tr-taut _ _) ()
pathstk?-red (tr-pw c₁ _ _ _ kp) h = ⊥-elim (f≢t (trans (sym (nopw⊥pw c₁ (deadmot→nopw c₁ h))) kp))
pathstk?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
pathstk?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
pathstk?-red (ξ-trᵉ r) h = h
pathstk?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
pathstk?-red (ξ-apᶜ r) h = h
pathstk?-red (ξ-apᵇ r) h = h
pathstk?-red (ξ-apᵖ r) h = apstk?-red r h
pathstk?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
pathstk?-red (jsub-refl _ _ _ _) ()
pathstk?-red (ξ-⌜Id⌝ᶜ r) h = h
pathstk?-red (ξ-⌜Id⌝ˡ r) h = h
pathstk?-red (ξ-⌜Id⌝ʳ r) h = h
pathstk?-red (ξ-idreflᶜ r) h = h
pathstk?-red (ξ-idreflᵃ r) h = h
pathstk?-red (ξ-jsubᵈ r) h = h
pathstk?-red (ξ-jsubᵖ r) h = idstk?-red r h
pathstk?-red (ξ-jsubᵉ r) h = h

-- ★ `ap`-stuckness is closed under reduction: the J key clashes with
-- the dead-code key; the pw/taut unfoldings land on LAM paths, which
-- are permanently ap-stuck (unlike `pathstk?`, where lams are live).
apstk?-red (β _ _) ()
apstk?-red (βfst _ _) ()
apstk?-red (βsnd _ _) ()
apstk?-red (ξ-lam r) h = h
apstk?-red (ξ-appˡ r) h = spine?-red r h
apstk?-red (ξ-appʳ r) h = h
apstk?-red (ξ-pairˡ r) h = h
apstk?-red (ξ-pairʳ r) h = h
apstk?-red (ξ-fst r) h = spine?-red r h
apstk?-red (ξ-snd r) h = spine?-red r h
apstk?-red (ξ-⌜Π⌝ˡ r) h = h
apstk?-red (ξ-⌜Π⌝ʳ r) h = h
apstk?-red (ξ-⌜Σ⌝ˡ r) h = h
apstk?-red (ξ-⌜Σ⌝ʳ r) h = h
apstk?-red (ξ-⌜Hom⌝ᶜ r) h = h
apstk?-red (ξ-⌜Hom⌝ˡ r) h = h
apstk?-red (ξ-⌜Hom⌝ʳ r) h = h
apstk?-red (ξ-hreflᶜ r) h = stablecd?-red r h
apstk?-red (ξ-hreflᵃ r) h = h
apstk?-red (hrefl-pw C₀ s₀ kp) h = refl
apstk?-red (tr-J-base _ _ _ _ _) ()
apstk?-red (tr-J-Σ _ _ _ _ _ _ _) ()
apstk?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) h))
apstk?-red (tr-taut _ _) ()
apstk?-red (tr-pw _ _ _ _ _) h = refl
apstk?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
apstk?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
apstk?-red (ξ-trᵉ r) h = h
apstk?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
apstk?-red (ξ-apᶜ r) h = h
apstk?-red (ξ-apᵇ r) h = h
apstk?-red (ξ-apᵖ r) h = apstk?-red r h
apstk?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
apstk?-red (jsub-refl _ _ _ _) ()
apstk?-red (ξ-⌜Id⌝ᶜ r) h = h
apstk?-red (ξ-⌜Id⌝ˡ r) h = h
apstk?-red (ξ-⌜Id⌝ʳ r) h = h
apstk?-red (ξ-idreflᶜ r) h = h
apstk?-red (ξ-idreflᵃ r) h = h
apstk?-red (ξ-jsubᵈ r) h = h
apstk?-red (ξ-jsubᵖ r) h = idstk?-red r h
apstk?-red (ξ-jsubᵉ r) h = h

-- ★ jsub-stuckness is closed under reduction (the idstk? mirror).
idstk?-red (β _ _) ()
idstk?-red (βfst _ _) ()
idstk?-red (βsnd _ _) ()
idstk?-red (ξ-lam r) h = h
idstk?-red (ξ-appˡ r) h = spine?-red r h
idstk?-red (ξ-appʳ r) h = h
idstk?-red (ξ-pairˡ r) h = h
idstk?-red (ξ-pairʳ r) h = h
idstk?-red (ξ-fst r) h = spine?-red r h
idstk?-red (ξ-snd r) h = spine?-red r h
idstk?-red (ξ-⌜Π⌝ˡ r) h = h
idstk?-red (ξ-⌜Π⌝ʳ r) h = h
idstk?-red (ξ-⌜Σ⌝ˡ r) h = h
idstk?-red (ξ-⌜Σ⌝ʳ r) h = h
idstk?-red (ξ-⌜Hom⌝ᶜ r) h = h
idstk?-red (ξ-⌜Hom⌝ˡ r) h = h
idstk?-red (ξ-⌜Hom⌝ʳ r) h = h
idstk?-red (ξ-hreflᶜ r) h = h
idstk?-red (ξ-hreflᵃ r) h = h
idstk?-red (hrefl-pw C₀ s₀ kp) h = refl
idstk?-red (tr-J-base _ _ _ _ _) ()
idstk?-red (tr-J-Σ _ _ _ _ _ _ _) ()
idstk?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) h))
idstk?-red (tr-taut _ _) ()
idstk?-red (tr-pw _ _ _ _ _) h = refl
idstk?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
idstk?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
idstk?-red (ξ-trᵉ r) h = h
idstk?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
idstk?-red (ξ-apᶜ r) h = h
idstk?-red (ξ-apᵇ r) h = h
idstk?-red (ξ-apᵖ r) h = apstk?-red r h
idstk?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
idstk?-red (jsub-refl _ _ _ _) ()
idstk?-red (ξ-⌜Id⌝ᶜ r) h = h
idstk?-red (ξ-⌜Id⌝ˡ r) h = h
idstk?-red (ξ-⌜Id⌝ʳ r) h = h
idstk?-red (ξ-idreflᶜ r) h = h
idstk?-red (ξ-idreflᵃ r) h = h
idstk?-red (ξ-jsubᵈ r) h = h
idstk?-red (ξ-jsubᵖ r) h = idstk?-red r h
idstk?-red (ξ-jsubᵉ r) h = h

nopw?-red (β _ _) ()
nopw?-red (βfst _ _) ()
nopw?-red (βsnd _ _) ()
nopw?-red (ξ-lam r) h = h
nopw?-red (ξ-appˡ r) h = spine?-red r h
nopw?-red (ξ-appʳ r) h = h
nopw?-red (ξ-pairˡ r) h = h
nopw?-red (ξ-pairʳ r) h = h
nopw?-red (ξ-fst r) h = spine?-red r h
nopw?-red (ξ-snd r) h = spine?-red r h
nopw?-red (ξ-⌜Π⌝ˡ _) ()
nopw?-red (ξ-⌜Π⌝ʳ _) ()
nopw?-red (ξ-⌜Σ⌝ˡ r) h = h
nopw?-red (ξ-⌜Σ⌝ʳ r) h = h
nopw?-red (ξ-⌜Hom⌝ᶜ r) h = nopw?-red r h
nopw?-red (ξ-⌜Hom⌝ˡ r) h = h
nopw?-red (ξ-⌜Hom⌝ʳ r) h = h
nopw?-red (ξ-hreflᶜ r) h = h
nopw?-red (ξ-hreflᵃ r) h = h
nopw?-red (hrefl-pw C₀ s₀ kp) h = refl
nopw?-red (tr-J-base _ _ _ _ _) ()
nopw?-red (tr-J-Σ _ _ _ _ _ _ _) ()
nopw?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) h))
nopw?-red (tr-taut _ _) ()
nopw?-red (tr-pw c₁ _ _ _ kp) h = ⊥-elim (f≢t (trans (sym (nopw⊥pw c₁ (deadmot→nopw c₁ h))) kp))
nopw?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
nopw?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
nopw?-red (ξ-trᵉ r) h = h
nopw?-red (ap-J _ _ _ _ _) h = refl
nopw?-red (ξ-apᶜ r) h = h
nopw?-red (ξ-apᵇ r) h = h
nopw?-red (ξ-apᵖ r) h = h
nopw?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
nopw?-red (jsub-refl _ _ _ _) ()
nopw?-red (ξ-⌜Id⌝ᶜ r) h = h
nopw?-red (ξ-⌜Id⌝ˡ r) h = h
nopw?-red (ξ-⌜Id⌝ʳ r) h = h
nopw?-red (ξ-idreflᶜ r) h = h
nopw?-red (ξ-idreflᵃ r) h = h
nopw?-red (ξ-jsubᵈ r) h = h
nopw?-red (ξ-jsubᵖ r) h = idstk?-red r h
nopw?-red (ξ-jsubᵉ r) h = h

deadmot?-red (β _ _) ()
deadmot?-red (βfst _ _) ()
deadmot?-red (βsnd _ _) ()
deadmot?-red (ξ-lam r) h = h
deadmot?-red (ξ-appˡ r) h = spine?-red r h
deadmot?-red (ξ-appʳ r) h = h
deadmot?-red (ξ-pairˡ r) h = h
deadmot?-red (ξ-pairʳ r) h = h
deadmot?-red (ξ-fst r) h = spine?-red r h
deadmot?-red (ξ-snd r) h = spine?-red r h
deadmot?-red (ξ-⌜Π⌝ˡ _) ()
deadmot?-red (ξ-⌜Π⌝ʳ _) ()
deadmot?-red (ξ-⌜Σ⌝ˡ r) h = refl
deadmot?-red (ξ-⌜Σ⌝ʳ r) h = refl
deadmot?-red (ξ-⌜Hom⌝ᶜ r) h = deadmot?-red r h
deadmot?-red (ξ-⌜Hom⌝ˡ r) h = h
deadmot?-red (ξ-⌜Hom⌝ʳ r) h = h
deadmot?-red (ξ-hreflᶜ r) h = deadmot?-red r h
deadmot?-red (ξ-hreflᵃ r) h = h
deadmot?-red (hrefl-pw C₀ s₀ kp) h =
  ⊥-elim (f≢t (trans (sym (nopw⊥pw C₀ (deadmot→nopw C₀ h))) kp))
deadmot?-red (tr-J-base _ _ _ _ _) ()
deadmot?-red (tr-J-Σ _ _ _ _ _ _ _) ()
deadmot?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) h))
deadmot?-red (tr-taut _ _) ()
deadmot?-red (tr-pw c₁ _ _ _ kp) h =
  ⊥-elim (f≢t (trans (sym (nopw⊥pw c₁ (deadmot→nopw c₁ h))) kp))
deadmot?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
deadmot?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
deadmot?-red (ξ-trᵉ r) h = h
deadmot?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
deadmot?-red (ξ-apᶜ r) h = h
deadmot?-red (ξ-apᵇ r) h = h
deadmot?-red (ξ-apᵖ r) h = apstk?-red r h
deadmot?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
deadmot?-red (jsub-refl _ _ _ _) ()
deadmot?-red (ξ-⌜Id⌝ᶜ r) h = h
deadmot?-red (ξ-⌜Id⌝ˡ r) h = h
deadmot?-red (ξ-⌜Id⌝ʳ r) h = h
deadmot?-red (ξ-idreflᶜ r) h = h
deadmot?-red (ξ-idreflᵃ r) h = h
deadmot?-red (ξ-jsubᵈ r) h = h
deadmot?-red (ξ-jsubᵖ r) h = idstk?-red r h
deadmot?-red (ξ-jsubᵉ r) h = h

-- dead codes are pw-immune (deadness subsumes the weaker key).
dead→nopw : (C : RTm Γ) → stablecd? C ≡ true → nopw? C ≡ true
dead→nopw (var x) h = refl
dead→nopw (lam t) h = refl
dead→nopw (app t u) h = h
dead→nopw (pair a b) h = refl
dead→nopw (fst t) h = h
dead→nopw (snd t) h = h
dead→nopw ⌜base⌝ ()
dead→nopw (⌜Π⌝ c d) ()
dead→nopw (⌜Σ⌝ c d) ()
dead→nopw (⌜Hom⌝ C a b) h = dead→nopw C h
dead→nopw (hrefl c t) h = refl
dead→nopw (tr d p e) h = h
dead→nopw (ap c b p) h = refl
dead→nopw (idrefl c t) h = refl
dead→nopw (jsub d p e) h = h


-- an hrefl path at a DEAD code is tr-stuck under EVERY motive shape.
trstk-hrefl-any : (d : RTm (Γ ∙)) {c s : RTm Γ} →
                  stablecd? c ≡ true → trstk? d (hrefl c s) ≡ true
trstk-hrefl-any (var x) {c = c} h = dead→nopw c h
trstk-hrefl-any (lam t) h = h
trstk-hrefl-any (app t u) h = h
trstk-hrefl-any (pair a b) h = h
trstk-hrefl-any (fst t) h = h
trstk-hrefl-any (snd t) h = h
trstk-hrefl-any ⌜base⌝ h = h
trstk-hrefl-any (⌜Π⌝ c₂ d₂) h = h
trstk-hrefl-any (⌜Σ⌝ c₂ d₂) h = h
trstk-hrefl-any (⌜Hom⌝ c₂ a₂ b₂) h = h
trstk-hrefl-any (hrefl c₂ t₂) h = h
trstk-hrefl-any (tr d₂ p₂ e₂) h = h
trstk-hrefl-any (ap c b p) h = h
trstk-hrefl-any (⌜Id⌝ c a b) h = h
trstk-hrefl-any (idrefl c t) h = h
trstk-hrefl-any (jsub d p e) h = h

-- motive steps.  Only lam- and hrefl-paths inspect the motive; the
-- rest are motive-independent (the catchall clause on both sides).
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = var vz} rc) h = deadmot?-red rc h
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = var (vs x)} rc) h = h
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (lam w)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (app w₁ w₂)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (pair w₁ w₂)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (fst w)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (snd w)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = ⌜base⌝} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (⌜Π⌝ w₁ w₂)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (⌜Σ⌝ w₁ w₂)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (⌜Hom⌝ w₁ w₂ w₃)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (hrefl w₁ w₂)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ᶜ {b = (tr w₁ w₂ w₃)} rc) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = var vz} ra) h = h
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = var (vs x)} ra) h = h
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (lam w)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (app w₁ w₂)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (pair w₁ w₂)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (fst w)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (snd w)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = ⌜base⌝} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (⌜Π⌝ w₁ w₂)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (⌜Σ⌝ w₁ w₂)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (⌜Hom⌝ w₁ w₂ w₃)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (hrefl w₁ w₂)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ˡ {b = (tr w₁ w₂ w₃)} ra) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = var vz} ()) h
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = var (vs x)} ()) h
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (lam w)} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (app w₁ w₂)} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (pair w₁ w₂)} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (fst w)} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (snd w)} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = ⌜base⌝} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (⌜Π⌝ w₁ w₂)} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (⌜Σ⌝ w₁ w₂)} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (⌜Hom⌝ w₁ w₂ w₃)} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (hrefl w₁ w₂)} rb) ()
trstk?-red-d {p = lam f} (ξ-⌜Hom⌝ʳ {b = (tr w₁ w₂ w₃)} rb) ()
trstk?-red-d {p = lam f} (β _ _) ()
trstk?-red-d {p = lam f} (βfst _ _) ()
trstk?-red-d {p = lam f} (βsnd _ _) ()
trstk?-red-d {p = lam f} (ξ-lam _) ()
trstk?-red-d {p = lam f} (ξ-appˡ _) ()
trstk?-red-d {p = lam f} (ξ-appʳ _) ()
trstk?-red-d {p = lam f} (ξ-pairˡ _) ()
trstk?-red-d {p = lam f} (ξ-pairʳ _) ()
trstk?-red-d {p = lam f} (ξ-fst _) ()
trstk?-red-d {p = lam f} (ξ-snd _) ()
trstk?-red-d {p = lam f} (ξ-⌜Π⌝ˡ _) ()
trstk?-red-d {p = lam f} (ξ-⌜Π⌝ʳ _) ()
trstk?-red-d {p = lam f} (ξ-⌜Σ⌝ˡ _) ()
trstk?-red-d {p = lam f} (ξ-⌜Σ⌝ʳ _) ()
trstk?-red-d {p = lam f} (ξ-hreflᶜ _) ()
trstk?-red-d {p = lam f} (ξ-hreflᵃ _) ()
trstk?-red-d {p = lam f} (hrefl-pw _ _ _) ()
trstk?-red-d {p = lam f} (tr-J-base _ _ _ _ _) ()
trstk?-red-d {p = lam f} (tr-J-Σ _ _ _ _ _ _ _) ()
trstk?-red-d {p = lam f} (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
trstk?-red-d {p = lam f} (tr-taut _ _) ()
trstk?-red-d {p = lam f} (tr-pw _ _ _ _ _) ()
trstk?-red-d {p = lam f} (ξ-trᵈ _) ()
trstk?-red-d {p = lam f} (ξ-trᵖ _) ()
trstk?-red-d {p = lam f} (ξ-trᵉ _) ()
trstk?-red-d {d = var x} {p = hrefl c s} () h
trstk?-red-d {d = (lam t)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (app t u)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (pair a b)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (fst t)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (snd t)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = ⌜base⌝} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (⌜Π⌝ c₂ d₂)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (⌜Σ⌝ c₂ d₂)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (⌜Hom⌝ c₂ a₂ b₂)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (hrefl c₂ t₂)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (tr d₂ p₂ e₂)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (ap dz₁ dz₂ dz₃)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (⌜Id⌝ dz₁ dz₂ dz₃)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (idrefl dz₁ dz₂)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (jsub dz₁ dz₂ dz₃)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {p = (var y)} r h = h
trstk?-red-d {p = (app t₁ u₁)} r h = h
trstk?-red-d {p = (pair a₁ b₁)} r h = h
trstk?-red-d {p = (fst q)} r h = h
trstk?-red-d {p = (snd q)} r h = h
trstk?-red-d {p = ⌜base⌝} r h = h
trstk?-red-d {p = (⌜Π⌝ c₁ d₁)} r h = h
trstk?-red-d {p = (⌜Σ⌝ c₁ d₁)} r h = h
trstk?-red-d {p = (⌜Hom⌝ c₁ a₁ b₁)} r h = h
trstk?-red-d {p = (tr d₁ p₁ e₁)} r h = h
trstk?-red-d {p = ap _ _ _} r h = h
trstk?-red-d {p = ⌜Id⌝ _ _ _} r h = h
trstk?-red-d {p = idrefl _ _} r h = h
trstk?-red-d {p = jsub _ _ _} r h = h
trstk?-red-p {d = (var x)} (ξ-hreflᶜ rc) h = nopw?-red rc h
trstk?-red-p {d = (lam t)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (app t u)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (pair a b)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (fst t)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (snd t)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = ⌜base⌝} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜Π⌝ c₂ d₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜Σ⌝ c₂ d₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜Hom⌝ c₂ a₂ b₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (hrefl c₂ t₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (tr d₂ p₂ e₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (ap dz₁ dz₂ dz₃)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜Id⌝ dz₁ dz₂ dz₃)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (idrefl dz₁ dz₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (jsub dz₁ dz₂ dz₃)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (var x)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (lam t)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (app t u)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (pair a b)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (fst t)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (snd t)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = ⌜base⌝} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜Π⌝ c₂ d₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜Σ⌝ c₂ d₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜Hom⌝ c₂ a₂ b₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (hrefl c₂ t₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (tr d₂ p₂ e₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (ap dz₁ dz₂ dz₃)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜Id⌝ dz₁ dz₂ dz₃)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (idrefl dz₁ dz₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (jsub dz₁ dz₂ dz₃)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = var x} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (nopw⊥pw C₀ h)) kp))
trstk?-red-p {d = (lam t)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (app t u)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (pair a b)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (fst t)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (snd t)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = ⌜base⌝} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜Π⌝ c₂ d₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜Σ⌝ c₂ d₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜Hom⌝ c₂ a₂ b₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (hrefl c₂ t₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (tr d₂ p₂ e₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (ap dz₁ dz₂ dz₃)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜Id⌝ dz₁ dz₂ dz₃)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (idrefl dz₁ dz₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (jsub dz₁ dz₂ dz₃)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p (β _ _) ()
trstk?-red-p (βfst _ _) ()
trstk?-red-p (βsnd _ _) ()
trstk?-red-p (ξ-lam r) h = h
trstk?-red-p (ξ-appˡ r) h = spine?-red r h
trstk?-red-p (ξ-appʳ r) h = h
trstk?-red-p (ξ-pairˡ r) h = h
trstk?-red-p (ξ-pairʳ r) h = h
trstk?-red-p (ξ-fst r) h = spine?-red r h
trstk?-red-p (ξ-snd r) h = spine?-red r h
trstk?-red-p (ξ-⌜Π⌝ˡ r) h = h
trstk?-red-p (ξ-⌜Π⌝ʳ r) h = h
trstk?-red-p (ξ-⌜Σ⌝ˡ r) h = h
trstk?-red-p (ξ-⌜Σ⌝ʳ r) h = h
trstk?-red-p (ξ-⌜Hom⌝ᶜ r) h = h
trstk?-red-p (ξ-⌜Hom⌝ˡ r) h = h
trstk?-red-p (ξ-⌜Hom⌝ʳ r) h = h
trstk?-red-p (tr-J-base _ _ _ _ _) ()
trstk?-red-p (tr-J-Σ _ _ _ _ _ _ _) ()
trstk?-red-p (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) h))
trstk?-red-p (tr-taut _ _) ()
trstk?-red-p (tr-pw c₁ _ _ _ kp) h = ⊥-elim (f≢t (trans (sym (nopw⊥pw c₁ (deadmot→nopw c₁ h))) kp))
trstk?-red-p (ξ-trᵈ {p = p₁} r) h = trstk?-red-d {p = p₁} r h
trstk?-red-p (ξ-trᵖ {d = d₁} r) h = trstk?-red-p {d = d₁} r h
trstk?-red-p (ξ-trᵉ r) h = h
trstk?-red-p (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
trstk?-red-p (ξ-apᶜ r) h = h
trstk?-red-p (ξ-apᵇ r) h = h
trstk?-red-p (ξ-apᵖ r) h = apstk?-red r h
trstk?-red-p (tr-J-Id _ _ _ _ _ _ _ _) ()
trstk?-red-p (jsub-refl _ _ _ _) ()
trstk?-red-p (ξ-⌜Id⌝ᶜ r) h = h
trstk?-red-p (ξ-⌜Id⌝ˡ r) h = h
trstk?-red-p (ξ-⌜Id⌝ʳ r) h = h
trstk?-red-p (ξ-idreflᶜ r) h = h
trstk?-red-p (ξ-idreflᵃ r) h = h
trstk?-red-p (ξ-jsubᵈ r) h = h
trstk?-red-p (ξ-jsubᵖ r) h = idstk?-red r h
trstk?-red-p (ξ-jsubᵉ r) h = h

apstk?-red* : {t t' : RTm Γ} → t ⟶* t' → apstk? t ≡ true → apstk? t' ≡ true
apstk?-red* done h       = h
apstk?-red* (step r q) h = apstk?-red* q (apstk?-red r h)

trstk?-red-d* : {d d' : RTm (Γ ∙)} {p : RTm Γ} → d ⟶* d' →
                trstk? d p ≡ true → trstk? d' p ≡ true
trstk?-red-d* {p = p} done       h = h
trstk?-red-d* {p = p} (step r q) h =
  trstk?-red-d* {p = p} q (trstk?-red-d {p = p} r h)

trstk?-red-p* : {d : RTm (Γ ∙)} {p p' : RTm Γ} → p ⟶* p' →
                trstk? d p ≡ true → trstk? d p' ≡ true
trstk?-red-p* done       h = h
trstk?-red-p* (step r q) h = trstk?-red-p* q (trstk?-red-p r h)

nopw?-red* : {t t' : RTm Γ} → t ⟶* t' → nopw? t ≡ true → nopw? t' ≡ true
nopw?-red* done       h = h
nopw?-red* (step r q) h = nopw?-red* q (nopw?-red r h)

data SNe {Γ} : RTm Γ → Set
data SN  {Γ} : RTm Γ → Set
data SNRed {Γ} : RTm Γ → RTm Γ → Set
-- W2b (G1f discovery 1): the head strategy descends ⌜Hom⌝ SPINES —
-- an hrefl's code normalizes at its spine BOTTOM (where a transient
-- redex can hide from the Boolean keys).
data CSR {Γ} : RTm Γ → RTm Γ → Set

data SNe {Γ} where
  sne-var : (x : Var Γ) → SNe (var x)
  sne-app : {t u : RTm Γ} → SNe t → SN u → SNe (app t u)
  sne-fst : {p : RTm Γ} → SNe p → SNe (fst p)
  sne-snd : {p : RTm Γ} → SNe p → SNe (snd p)
  -- W2: `hrefl` is OPERATIONALLY INERT while its unfold family is
  -- deferred with the canonicity package (NbEPDirDBType), so it never
  -- becomes a `lam` and behaves as a neutral for this SN-flavored LR —
  -- exactly as long as it has no computation.
  sne-hrefl : {c t : RTm Γ} → SN c → SN t → nopw? c ≡ true →
              SNe (hrefl c t)
  -- W2 stage 2: a PERMANENTLY STUCK `tr` (`trstk?` — an inert path, or
  -- a lambda path at a `⌜Hom⌝`-headed motive) is neutral.
  sne-tr : {d : RTm (Γ ∙)} {p e : RTm Γ} →
           SN d → SN p → SN e → trstk? d p ≡ true → SNe (tr d p e)
  -- ★ directed `ap` (SpikeAp): a PERMANENTLY STUCK `ap` (`apstk?` — a
  -- lam path, or an hrefl at a DEAD code) is neutral.
  sne-ap : {cB : RTm Γ} {b : RTm (Γ ∙)} {p : RTm Γ} →
           SN cB → SN b → SN p → apstk? p ≡ true → SNe (ap cB b p)

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
  -- W2 stage 2: `hrefl` and `tr` are ELIMINATORS (of the code, of the
  -- path) — their scrutinee positions join the head strategy.  The J
  -- rules carry the DISCARDED material's `SN`, exactly like `snr-β`.
  snr-hreflᶜ : {c c' t : RTm Γ} → CSR c c' →
               SNRed (hrefl c t) (hrefl c' t)
  -- W2b: the pointwise unfold is a head rule (key-disjoint from
  -- snr-hreflᶜ — a head-reducible code is never pw, `snr-nonpw`).
  snr-hrefl-pw : {C t : RTm Γ} → pw? C ≡ true →
                 SNRed (hrefl C t)
                       (lam (hrefl (pwBody C)
                                   (app (renTm vs t) (var vz))))
  snr-J-base : {c a m : RTm (Γ ∙)} {s e : RTm Γ} →
               SN (⌜Hom⌝ c a m) → SN s →
               SNRed (tr (⌜Hom⌝ c a m) (hrefl ⌜base⌝ s) e) e
  snr-J-Σ    : {c a m : RTm (Γ ∙)} {c₁ : RTm Γ} {c₂ : RTm (Γ ∙)} {s e : RTm Γ} →
               SN (⌜Hom⌝ c a m) → SN c₁ → SN c₂ → SN s →
               SNRed (tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e) e
  snr-taut   : {f : RTm (Γ ∙)} {e : RTm Γ} →
               SNRed (tr (var vz) (lam f) e) (app (lam f) e)
  snr-trᵖ    : {d : RTm (Γ ∙)} {p p' e : RTm Γ} → SNRed p p' →
               SNRed (tr d p e) (tr d p' e)
  -- ★ directed `ap`: the path is the scrutinee; J discards the path's
  -- code (carried as SN, the snr-β pattern).
  snr-ap-J   : {cB : RTm Γ} {b : RTm (Γ ∙)} {c₁ s : RTm Γ} →
               SN c₁ → stkC? c₁ ≡ true →
               SNRed (ap cB b (hrefl c₁ s)) (hrefl cB (subTm (single s) b))
  snr-apᵖ    : {cB : RTm Γ} {b : RTm (Γ ∙)} {p p' : RTm Γ} → SNRed p p' →
               SNRed (ap cB b p) (ap cB b p')
  -- W2b: J at stable ⌜Hom⌝ codes and pointwise transport (discarded
  -- material carried as SN, the snr-β pattern; tr-pw's SN c covers the
  -- ⌜Π⌝-domain that pwBody drops).
  snr-J-Hom  : {c a m : RTm (Γ ∙)} {c₁ a₁ b₁ s e : RTm Γ} →
               SN (⌜Hom⌝ c a m) → SN c₁ → SN a₁ → SN b₁ → SN s →
               stkC? c₁ ≡ true →
               SNRed (tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e) e
  -- W2b final frontier: the motive-side spine normalization — a lam
  -- path exposes the motive's code as the next scrutinee.
  snr-tr-mot : {c c' a f : RTm (Γ ∙)} {e : RTm Γ} → CSR c c' →
               SNRed (tr (⌜Hom⌝ c a (var vz)) (lam f) e)
                     (tr (⌜Hom⌝ c' a (var vz)) (lam f) e)
  snr-tr-pw  : {c a f : RTm (Γ ∙)} {e : RTm Γ} →
               SN c → SN a → pw? c ≡ true →
               SNRed (tr (⌜Hom⌝ c a (var vz)) (lam f) e)
                     (lam (tr (⌜Hom⌝ (renTm pwShift (pwBody c))
                                     (app (renTm vs a) (var (vs vz)))
                                     (var vz))
                              f
                              (app (renTm vs e) (var vz))))

data CSR {Γ} where
  csr-here : {c c' : RTm Γ} → SNRed c c' → CSR c c'
  csr-hom  : {c c' a b : RTm Γ} → CSR c c' →
             CSR (⌜Hom⌝ c a b) (⌜Hom⌝ c' a b)

infix 3 _⟶snr*_
data _⟶snr*_ {Γ} : RTm Γ → RTm Γ → Set where
  snr-done : {t : RTm Γ} → t ⟶snr* t
  snr-step : {t u v : RTm Γ} → SNRed t u → u ⟶snr* v → t ⟶snr* v

csr→⟶ : {t t' : RTm Γ} → CSR t t' → t ⟶ t'
snr→⟶ : {t t' : RTm Γ} → SNRed t t' → t ⟶ t'
csr→⟶ (csr-here r) = snr→⟶ r
csr→⟶ (csr-hom σ)  = ξ-⌜Hom⌝ᶜ (csr→⟶ σ)
snr→⟶ (snr-β {s} {u} _)    = β s u
snr→⟶ (snr-βfst {a} {b} _) = βfst a b
snr→⟶ (snr-βsnd {a} {b} _) = βsnd a b
snr→⟶ (snr-app r)          = ξ-appˡ (snr→⟶ r)
snr→⟶ (snr-fst r)          = ξ-fst (snr→⟶ r)
snr→⟶ (snr-snd r)          = ξ-snd (snr→⟶ r)
snr→⟶ (snr-hreflᶜ σ)       = ξ-hreflᶜ (csr→⟶ σ)
snr→⟶ (snr-J-base _ _)     = tr-J-base _ _ _ _ _
snr→⟶ (snr-J-Σ _ _ _ _)    = tr-J-Σ _ _ _ _ _ _ _
snr→⟶ snr-taut             = tr-taut _ _
snr→⟶ (snr-trᵖ r)          = ξ-trᵖ (snr→⟶ r)
snr→⟶ (snr-hrefl-pw key)   = hrefl-pw _ _ key
snr→⟶ (snr-J-Hom _ _ _ _ _ key) = tr-J-Hom _ _ _ _ _ _ _ _ key
snr→⟶ (snr-tr-pw _ _ key)  = tr-pw _ _ _ _ key
snr→⟶ (snr-tr-mot σ)       = ξ-trᵈ (ξ-⌜Hom⌝ᶜ (csr→⟶ σ))
snr→⟶ (snr-ap-J _ key)     = ap-J _ _ _ _ key
snr→⟶ (snr-apᵖ r)          = ξ-apᵖ (snr→⟶ r)

-- a head-reducible term is never a pw-able code (all SNRed subjects
-- are app/fst/snd/hrefl/tr-headed).
snr-nonpw : {t t' : RTm Γ} → SNRed t t' → pw? t ≡ false
snr-nonpw (snr-β _)      = refl
snr-nonpw (snr-βfst _)   = refl
snr-nonpw (snr-βsnd _)   = refl
snr-nonpw (snr-app _)    = refl
snr-nonpw (snr-fst _)    = refl
snr-nonpw (snr-snd _)    = refl
snr-nonpw (snr-hreflᶜ _) = refl
snr-nonpw (snr-hrefl-pw _) = refl
snr-nonpw (snr-J-base _ _)  = refl
snr-nonpw (snr-J-Σ _ _ _ _) = refl
snr-nonpw (snr-J-Hom _ _ _ _ _ _) = refl
snr-nonpw snr-taut       = refl
snr-nonpw (snr-trᵖ _)    = refl
snr-nonpw (snr-tr-pw _ _ _) = refl
snr-nonpw (snr-tr-mot _)    = refl
snr-nonpw (snr-ap-J _ _)    = refl
snr-nonpw (snr-apᵖ _)       = refl

csr-nonpw : {t t' : RTm Γ} → CSR t t' → pw? t ≡ false
csr-nonpw (csr-here r) = snr-nonpw r
csr-nonpw (csr-hom σ)  = csr-nonpw σ

-- a permanently-stable code has no spine step.
csr-stk⊥ : {t t' : RTm Γ} → stkC? t ≡ true → CSR t t' → ⊥
csr-stk⊥ {t = ⌜base⌝} k (csr-here ())
csr-stk⊥ {t = ⌜Σ⌝ c d} k (csr-here ())
csr-stk⊥ {t = ⌜Hom⌝ c a b} k (csr-here ())
csr-stk⊥ {t = ⌜Hom⌝ c a b} k (csr-hom σ) = csr-stk⊥ k σ
csr-stk⊥ {t = var x} () _
csr-stk⊥ {t = lam _} () _
csr-stk⊥ {t = app _ _} () _
csr-stk⊥ {t = pair _ _} () _
csr-stk⊥ {t = fst _} () _
csr-stk⊥ {t = snd _} () _
csr-stk⊥ {t = ⌜Π⌝ _ _} () _
csr-stk⊥ {t = hrefl _ _} () _
csr-stk⊥ {t = tr _ _ _} () _


------------------------------------------------------------------------
-- W2 stage 2: the head strategy is DETERMINISTIC, so `SN` and every
-- MEMBERSHIP move FORWARD along it (`sn-whred`/`mem-whred₁` below) —
-- the transfer `fund`'s `tr` case runs its path analysis on.
------------------------------------------------------------------------

snr-det : {t u u' : RTm Γ} → SNRed t u → SNRed t u' → u ≡ u'
csr-det : {t u u' : RTm Γ} → CSR t u → CSR t u' → u ≡ u'
snr-det (snr-β _)    (snr-β _)     = refl
snr-det (snr-β _)    (snr-app ())
snr-det (snr-app ()) (snr-β _)
snr-det (snr-app {u = u} r) (snr-app r') =
  cong (λ z → app z u) (snr-det r r')
snr-det (snr-βfst _) (snr-βfst _)  = refl
snr-det (snr-βfst _) (snr-fst ())
snr-det (snr-fst ()) (snr-βfst _)
snr-det (snr-fst r)  (snr-fst r')  = cong fst (snr-det r r')
snr-det (snr-βsnd _) (snr-βsnd _)  = refl
snr-det (snr-βsnd _) (snr-snd ())
snr-det (snr-snd ()) (snr-βsnd _)
snr-det (snr-snd r)  (snr-snd r')  = cong snd (snr-det r r')
snr-det (snr-hreflᶜ {t = t} σ) (snr-hreflᶜ σ') =
  cong (λ z → hrefl z t) (csr-det σ σ')
snr-det (snr-J-base _ _) (snr-J-base _ _) = refl
snr-det (snr-J-base _ _) (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-det (snr-trᵖ (snr-hreflᶜ (csr-here ()))) (snr-J-base _ _)
snr-det (snr-J-Σ _ _ _ _) (snr-J-Σ _ _ _ _) = refl
snr-det (snr-J-Σ _ _ _ _) (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-det (snr-trᵖ (snr-hreflᶜ (csr-here ()))) (snr-J-Σ _ _ _ _)
snr-det snr-taut snr-taut = refl
snr-det snr-taut (snr-trᵖ ())
snr-det (snr-trᵖ {d = d} {e = e} r) (snr-trᵖ r') =
  cong (λ z → tr d z e) (snr-det r r')
-- W2b: the new heads.  hreflᶜ vs hrefl-pw is impossible (a
-- head-reducible code is never pw); J-Hom vs trᵖ-inside likewise
-- (⌜Hom⌝-headed codes have no head steps; pw vs stk is disjoint).
snr-det (snr-hrefl-pw _) (snr-hrefl-pw _) = refl
snr-det (snr-hrefl-pw kp) (snr-hreflᶜ σ)
  with trans (sym (csr-nonpw σ)) kp
... | ()
snr-det (snr-hreflᶜ σ) (snr-hrefl-pw kp)
  with trans (sym (csr-nonpw σ)) kp
... | ()
snr-det (snr-J-Hom _ _ _ _ _ _) (snr-J-Hom _ _ _ _ _ _) = refl
snr-det (snr-J-Hom {c₁ = c₁} _ _ _ _ _ ks) (snr-trᵖ (snr-hreflᶜ σ)) =
  ⊥-elim (csr-stk⊥ ks σ)
snr-det (snr-trᵖ (snr-hreflᶜ σ)) (snr-J-Hom {c₁ = c₁} _ _ _ _ _ ks) =
  ⊥-elim (csr-stk⊥ ks σ)
snr-det (snr-J-Hom {c₁ = c₁} _ _ _ _ _ ks) (snr-trᵖ (snr-hrefl-pw kp))
  with trans (sym (stk⊥pw c₁ ks)) kp
... | ()
snr-det (snr-trᵖ (snr-hrefl-pw kp)) (snr-J-Hom {c₁ = c₁} _ _ _ _ _ ks)
  with trans (sym (stk⊥pw c₁ ks)) kp
... | ()
snr-det (snr-J-base _ _) (snr-trᵖ (snr-hrefl-pw ()))
snr-det (snr-trᵖ (snr-hrefl-pw ())) (snr-J-base _ _)
snr-det (snr-J-Σ _ _ _ _) (snr-trᵖ (snr-hrefl-pw ()))
snr-det (snr-trᵖ (snr-hrefl-pw ())) (snr-J-Σ _ _ _ _)
snr-det (snr-tr-pw _ _ _) (snr-tr-pw _ _ _) = refl
snr-det (snr-tr-mot {a = a} {f = f} {e = e} σ) (snr-tr-mot σ') =
  cong (λ z → tr (⌜Hom⌝ z a (var vz)) (lam f) e) (csr-det σ σ')
snr-det (snr-tr-mot σ) (snr-tr-pw _ _ kp)
  with trans (sym (csr-nonpw σ)) kp
... | ()
snr-det (snr-tr-pw _ _ kp) (snr-tr-mot σ)
  with trans (sym (csr-nonpw σ)) kp
... | ()
snr-det (snr-tr-mot σ) (snr-trᵖ ())
snr-det (snr-tr-pw _ _ _) (snr-trᵖ ())
snr-det (snr-ap-J _ _) (snr-ap-J _ _) = refl
snr-det (snr-ap-J {c₁ = c₁} _ ks) (snr-apᵖ (snr-hreflᶜ σ)) =
  ⊥-elim (csr-stk⊥ ks σ)
snr-det (snr-apᵖ (snr-hreflᶜ σ)) (snr-ap-J {c₁ = c₁} _ ks) =
  ⊥-elim (csr-stk⊥ ks σ)
snr-det (snr-ap-J {c₁ = c₁} _ ks) (snr-apᵖ (snr-hrefl-pw kp))
  with trans (sym (stk⊥pw c₁ ks)) kp
... | ()
snr-det (snr-apᵖ (snr-hrefl-pw kp)) (snr-ap-J {c₁ = c₁} _ ks)
  with trans (sym (stk⊥pw c₁ ks)) kp
... | ()
snr-det (snr-apᵖ r) (snr-apᵖ r') with snr-det r r'
... | refl = refl

csr-det (csr-here r) (csr-here r') = snr-det r r'
csr-det (csr-here ()) (csr-hom σ')
csr-det (csr-hom σ) (csr-here ())
csr-det (csr-hom {a = a} {b = b} σ) (csr-hom σ') =
  cong (λ z → ⌜Hom⌝ z a b) (csr-det σ σ')

-- `idrefl` has no head step, so a head step factors PAST any chain
-- reaching one — by determinism.
noSnrIdrefl : {Γ : Cx} {c s u : RTm Γ} → SNRed (idrefl c s) u → ⊥
noSnrIdrefl ()

idpay-peel : {Γ : Cx} {t t' : RTm Γ} {c s : RTm Γ} →
             SNRed t t' → t ⟶snr* idrefl c s → t' ⟶snr* idrefl c s
idpay-peel r snr-done        = ⊥-elim (noSnrIdrefl r)
idpay-peel r (snr-step r₀ q) with snr-det r₀ r
... | refl = q

sne-whred : {t t' : RTm Γ} → SNe t → SNRed t t' → SNe t'
sn-whred  : {t t' : RTm Γ} → SN t → SNRed t t' → SN t'
-- SN moves along a spine step (⌜Hom⌝-headed SN is `sn-cH` only).
sn-csr    : {t t' : RTm Γ} → SN t → CSR t t' → SN t'

sne-whred (sne-app n s) (snr-app r) = sne-app (sne-whred n r) s
sne-whred (sne-fst n)   (snr-fst r) = sne-fst (sne-whred n r)
sne-whred (sne-snd n)   (snr-snd r) = sne-snd (sne-whred n r)
sne-whred (sne-hrefl snc snt kn) (snr-hreflᶜ σ) =
  sne-hrefl (sn-csr snc σ) snt (nopw?-red (csr→⟶ σ) kn)
sne-whred (sne-hrefl {c = c} snc snt kn) (snr-hrefl-pw kp)
  with trans (sym (nopw⊥pw c kn)) kp
... | ()
sne-whred (sne-tr snd₀ snp sne₀ ()) (snr-J-base _ _)
sne-whred (sne-tr snd₀ snp sne₀ ()) (snr-J-Σ _ _ _ _)
sne-whred (sne-tr snd₀ snp sne₀ ()) snr-taut
sne-whred (sne-tr snd₀ snp sne₀ key) (snr-J-Hom {c₁ = c₁} _ _ _ _ _ ks)
  with trans (sym (stk⊥dead c₁ ks)) key
... | ()
sne-whred (sne-tr {d = ⌜Hom⌝ c _ (var vz)} snd₀ snp sne₀ key)
          (snr-tr-pw _ _ kp)
  with trans (sym (nopw⊥pw c (deadmot→nopw c key))) kp
... | ()
sne-whred (sne-tr {d = ⌜Hom⌝ c _ (var vz)} snd₀ snp sne₀ key)
          (snr-tr-mot σ) =
  sne-tr (sn-csr snd₀ (csr-hom σ)) snp sne₀
         (deadmot?-red (csr→⟶ σ) key)
sne-whred (sne-tr snd₀ snp sne₀ key) (snr-trᵖ r) =
  sne-tr snd₀ (sn-whred snp r) sne₀ (trstk?-red-p (snr→⟶ r) key)
sne-whred (sne-ap snc snb snp key) (snr-ap-J {c₁ = c₁} _ ks)
  with trans (sym (stk⊥dead c₁ ks)) key
... | ()
sne-whred (sne-ap snc snb snp key) (snr-apᵖ r) =
  sne-ap snc snb (sn-whred snp r) (apstk?-red (snr→⟶ r) key)

-- ★ the two-former kernel: neutrals never reach a reflexivity (the
-- head strategy preserves strict neutrality; `idrefl` is not SNe), so
-- CR3's Id-payload is vacuous — and the exp/whred transports prefix or
-- peel the head step by determinism.
sneIdrefl⊥ : {Γ : Cx} {c s : RTm Γ} → SNe (idrefl c s) → ⊥
sneIdrefl⊥ ()

sne-nopay : {Γ : Cx} {p : RTm Γ} {c s : RTm Γ} →
            SNe p → p ⟶snr* idrefl c s → ⊥
sne-nopay n snr-done      = sneIdrefl⊥ n
sne-nopay n (snr-step r q) = sne-nopay (sne-whred n r) q

sn-whred (sn-ne n)      r = sn-ne (sne-whred n r)
sn-whred (sn-exp r₀ h) r with snr-det r₀ r
... | refl = h

sn-csr h (csr-here r) = sn-whred h r
sn-csr (sn-ne ()) (csr-hom σ)
sn-csr (sn-cH hc ha hb) (csr-hom σ) = sn-cH (sn-csr hc σ) ha hb

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
  ne-hrefl : {c t : RTm Γ} → nopw? c ≡ true → Ne (hrefl c t)
  ne-tr : {d : RTm (Γ ∙)} {p e : RTm Γ} →
          trstk? d p ≡ true → Ne (tr d p e)
  ne-ap : {cB : RTm Γ} {b : RTm (Γ ∙)} {p : RTm Γ} →
          apstk? p ≡ true → Ne (ap cB b p)

ne-red : {t t' : RTm Γ} → Ne t → t ⟶ t' → Ne t'
ne-red (ne-var x) ()
ne-red (ne-app n) (ξ-appˡ r) = ne-app (ne-red n r)
ne-red (ne-app n) (ξ-appʳ r) = ne-app n
ne-red (ne-fst n) (ξ-fst r)  = ne-fst (ne-red n r)
ne-red (ne-snd n) (ξ-snd r)  = ne-snd (ne-red n r)
ne-red (ne-hrefl kn) (ξ-hreflᶜ r) = ne-hrefl (nopw?-red r kn)
ne-red (ne-hrefl kn) (ξ-hreflᵃ r) = ne-hrefl kn
ne-red (ne-hrefl kn) (hrefl-pw C _ kp) =
  ⊥-elim (f≢t (trans (sym (nopw⊥pw C kn)) kp))
ne-red (ne-tr ()) (tr-J-base _ _ _ _ _)
ne-red (ne-tr ()) (tr-J-Σ _ _ _ _ _ _ _)
ne-red (ne-tr ()) (tr-taut _ _)
ne-red (ne-tr key) (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) key))
ne-red (ne-tr key) (tr-pw c₁ _ _ _ kp) =
  ⊥-elim (f≢t (trans (sym (nopw⊥pw c₁ (deadmot→nopw c₁ key))) kp))
ne-red (ne-tr key) (ξ-trᵈ {p = p} r) = ne-tr (trstk?-red-d {p = p} r key)
ne-red (ne-tr key) (ξ-trᵖ {d = d} r) = ne-tr (trstk?-red-p {d = d} r key)
ne-red (ne-tr key) (ξ-trᵉ r) = ne-tr key
ne-red (ne-ap key) (ap-J _ _ c₁ _ kh) =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ kh)) key))
ne-red (ne-ap key) (ξ-apᶜ r) = ne-ap key
ne-red (ne-ap key) (ξ-apᵇ r) = ne-ap key
ne-red (ne-ap key) (ξ-apᵖ r) = ne-ap (apstk?-red r key)

sne→ne : {t : RTm Γ} → SNe t → Ne t
sne→ne (sne-var x)   = ne-var x
sne→ne (sne-app n _) = ne-app (sne→ne n)
sne→ne (sne-fst n)   = ne-fst (sne→ne n)
sne→ne (sne-snd n)   = ne-snd (sne→ne n)
sne→ne (sne-hrefl _ _ kn) = ne-hrefl kn
sne→ne (sne-tr _ _ _ key) = ne-tr key
sne→ne (sne-ap _ _ _ key) = ne-ap key

-- extractors for `fund`'s path analysis: strict neutrals are safe spine
-- heads and stable codes.
sne→spine : {t : RTm Γ} → SNe t → spine? t ≡ true
sne→spine (sne-var x)        = refl
sne→spine (sne-app n _)      = sne→spine n
sne→spine (sne-fst n)        = sne→spine n
sne→spine (sne-snd n)        = sne→spine n
sne→spine (sne-hrefl _ _ kn) = kn
sne→spine (sne-tr _ _ _ key) = key
sne→spine (sne-ap _ _ _ key) = key

sne→stablecd : {t : RTm Γ} → SNe t → stablecd? t ≡ true
sne→stablecd (sne-var x)        = refl
sne→stablecd (sne-app n _)      = sne→spine n
sne→stablecd (sne-fst n)        = sne→spine n
sne→stablecd (sne-snd n)        = sne→spine n
sne→stablecd (sne-hrefl _ _ _)    = refl
sne→stablecd (sne-tr _ _ _ key) = key
sne→stablecd (sne-ap _ _ _ key) = key

-- renaming preserves every classifier ON THE NOSE — the entire
-- anti-renaming bill for the shape layer.
homheaded?-ren : (ρ : Ren Γ Δ) (t : RTm Γ) →
                 homheaded? (renTm ρ t) ≡ homheaded? t
homheaded?-ren ρ (var x)       = refl
homheaded?-ren ρ (lam t)       = refl
homheaded?-ren ρ (app t u)     = refl
homheaded?-ren ρ (pair a b)    = refl
homheaded?-ren ρ (fst t)       = refl
homheaded?-ren ρ (snd t)       = refl
homheaded?-ren ρ ⌜base⌝        = refl
homheaded?-ren ρ (⌜Π⌝ c d)     = refl
homheaded?-ren ρ (⌜Σ⌝ c d)     = refl
homheaded?-ren ρ (⌜Hom⌝ c a b) = refl
homheaded?-ren ρ (hrefl c t)   = refl
homheaded?-ren ρ (tr d p e)    = refl
homheaded?-ren ρ (ap c b p)  = refl
homheaded?-ren ρ (⌜Id⌝ c a b) = refl
homheaded?-ren ρ (idrefl c t) = refl
homheaded?-ren ρ (jsub d p e) = refl

spine?-ren    : (ρ : Ren Γ Δ) (t : RTm Γ) → spine? (renTm ρ t) ≡ spine? t
stablecd?-ren : (ρ : Ren Γ Δ) (t : RTm Γ) →
                stablecd? (renTm ρ t) ≡ stablecd? t
apstk?-ren    : (ρ : Ren Γ Δ) (t : RTm Γ) →
                apstk? (renTm ρ t) ≡ apstk? t
idstk?-ren    : (ρ : Ren Γ Δ) (t : RTm Γ) →
                idstk? (renTm ρ t) ≡ idstk? t
pathstk?-ren  : (ρ : Ren Γ Δ) (t : RTm Γ) →
                pathstk? (renTm ρ t) ≡ pathstk? t
trstk?-ren    : (ρ : Ren Γ Δ) (d : RTm (Γ ∙)) (p : RTm Γ) →
                trstk? (renTm (extR ρ) d) (renTm ρ p) ≡ trstk? d p
nopw?-ren     : (ρ : Ren Γ Δ) (t : RTm Γ) → nopw? (renTm ρ t) ≡ nopw? t
deadmot?-ren  : (ρ : Ren Γ Δ) (t : RTm Γ) →
                deadmot? (renTm ρ t) ≡ deadmot? t
trlam?-ren    : (ρ : Ren Γ Δ) (d : RTm (Γ ∙)) →
                trlam? (renTm (extR ρ) d) ≡ trlam? d

spine?-ren ρ (var x)       = refl
spine?-ren ρ (lam t)       = refl
spine?-ren ρ (app t u)     = spine?-ren ρ t
spine?-ren ρ (pair a b)    = refl
spine?-ren ρ (fst t)       = spine?-ren ρ t
spine?-ren ρ (snd t)       = spine?-ren ρ t
spine?-ren ρ ⌜base⌝        = refl
spine?-ren ρ (⌜Π⌝ c d)     = refl
spine?-ren ρ (⌜Σ⌝ c d)     = refl
spine?-ren ρ (⌜Hom⌝ c a b) = refl
spine?-ren ρ (hrefl c t)   = nopw?-ren ρ c
spine?-ren ρ (tr d p e)    = trstk?-ren ρ d p
spine?-ren ρ (ap c b p)    = apstk?-ren ρ p
spine?-ren ρ (⌜Id⌝ c a b)  = refl
spine?-ren ρ (idrefl c t)  = refl
spine?-ren ρ (jsub d p e)  = idstk?-ren ρ p

stablecd?-ren ρ (var x)       = refl
stablecd?-ren ρ (lam t)       = refl
stablecd?-ren ρ (app t u)     = spine?-ren ρ t
stablecd?-ren ρ (pair a b)    = refl
stablecd?-ren ρ (fst t)       = spine?-ren ρ t
stablecd?-ren ρ (snd t)       = spine?-ren ρ t
stablecd?-ren ρ ⌜base⌝        = refl
stablecd?-ren ρ (⌜Π⌝ c d)     = refl
stablecd?-ren ρ (⌜Σ⌝ c d)     = refl
stablecd?-ren ρ (⌜Hom⌝ c a b) = stablecd?-ren ρ c
stablecd?-ren ρ (hrefl c t)   = refl
stablecd?-ren ρ (tr d p e)    = trstk?-ren ρ d p
stablecd?-ren ρ (ap c b p)    = apstk?-ren ρ p
stablecd?-ren ρ (⌜Id⌝ c a b)  = refl
stablecd?-ren ρ (idrefl c t)  = refl
stablecd?-ren ρ (jsub d p e)  = idstk?-ren ρ p

pathstk?-ren ρ (var x)       = refl
pathstk?-ren ρ (lam t)       = refl
pathstk?-ren ρ (app t u)     = spine?-ren ρ t
pathstk?-ren ρ (pair a b)    = refl
pathstk?-ren ρ (fst t)       = spine?-ren ρ t
pathstk?-ren ρ (snd t)       = spine?-ren ρ t
pathstk?-ren ρ ⌜base⌝        = refl
pathstk?-ren ρ (⌜Π⌝ c d)     = refl
pathstk?-ren ρ (⌜Σ⌝ c d)     = refl
pathstk?-ren ρ (⌜Hom⌝ c a b) = refl
pathstk?-ren ρ (hrefl c t)   = stablecd?-ren ρ c
pathstk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
pathstk?-ren ρ (ap c b p)    = apstk?-ren ρ p
pathstk?-ren ρ (⌜Id⌝ c a b)  = refl
pathstk?-ren ρ (idrefl c t)  = refl
pathstk?-ren ρ (jsub d p e)  = idstk?-ren ρ p

apstk?-ren ρ (var x)       = refl
apstk?-ren ρ (lam t)       = refl
apstk?-ren ρ (app t u)     = spine?-ren ρ t
apstk?-ren ρ (pair a b)    = refl
apstk?-ren ρ (fst t)       = spine?-ren ρ t
apstk?-ren ρ (snd t)       = spine?-ren ρ t
apstk?-ren ρ ⌜base⌝        = refl
apstk?-ren ρ (⌜Π⌝ c d)     = refl
apstk?-ren ρ (⌜Σ⌝ c d)     = refl
apstk?-ren ρ (⌜Hom⌝ c a b) = refl
apstk?-ren ρ (hrefl c t)   = stablecd?-ren ρ c
apstk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
apstk?-ren ρ (ap c b p)    = apstk?-ren ρ p
apstk?-ren ρ (⌜Id⌝ c a b)  = refl
apstk?-ren ρ (idrefl c t)  = refl
apstk?-ren ρ (jsub d p e)  = idstk?-ren ρ p

idstk?-ren ρ (var x)       = refl
idstk?-ren ρ (lam t)       = refl
idstk?-ren ρ (app t u)     = spine?-ren ρ t
idstk?-ren ρ (pair a b)    = refl
idstk?-ren ρ (fst t)       = spine?-ren ρ t
idstk?-ren ρ (snd t)       = spine?-ren ρ t
idstk?-ren ρ ⌜base⌝        = refl
idstk?-ren ρ (⌜Π⌝ c d)     = refl
idstk?-ren ρ (⌜Σ⌝ c d)     = refl
idstk?-ren ρ (⌜Hom⌝ c a b) = refl
idstk?-ren ρ (⌜Id⌝ c a b)  = refl
idstk?-ren ρ (hrefl c t)   = refl
idstk?-ren ρ (idrefl c t)  = refl
idstk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
idstk?-ren ρ (ap c b p)    = apstk?-ren ρ p
idstk?-ren ρ (jsub d p e)  = idstk?-ren ρ p

trstk?-ren ρ d (var x)       = refl
trstk?-ren ρ d (lam f)       = trlam?-ren ρ d
trstk?-ren ρ d (app t u)     = spine?-ren ρ t
trstk?-ren ρ d (pair a b)    = refl
trstk?-ren ρ d (fst t)       = spine?-ren ρ t
trstk?-ren ρ d (snd t)       = spine?-ren ρ t
trstk?-ren ρ d ⌜base⌝        = refl
trstk?-ren ρ d (⌜Π⌝ c e)     = refl
trstk?-ren ρ d (⌜Σ⌝ c e)     = refl
trstk?-ren ρ d (⌜Hom⌝ c a b) = refl
trstk?-ren ρ (var x) (hrefl c t)          = nopw?-ren ρ c
trstk?-ren ρ (lam b) (hrefl c t)          = stablecd?-ren ρ c
trstk?-ren ρ (app f u) (hrefl c t)        = stablecd?-ren ρ c
trstk?-ren ρ (pair a b) (hrefl c t)       = stablecd?-ren ρ c
trstk?-ren ρ (fst q) (hrefl c t)          = stablecd?-ren ρ c
trstk?-ren ρ (snd q) (hrefl c t)          = stablecd?-ren ρ c
trstk?-ren ρ ⌜base⌝ (hrefl c t)           = stablecd?-ren ρ c
trstk?-ren ρ (⌜Π⌝ c₁ d₁) (hrefl c t)      = stablecd?-ren ρ c
trstk?-ren ρ (⌜Σ⌝ c₁ d₁) (hrefl c t)      = stablecd?-ren ρ c
trstk?-ren ρ (⌜Hom⌝ c₁ a₁ b₁) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (hrefl c₁ t₁) (hrefl c t)    = stablecd?-ren ρ c
trstk?-ren ρ (tr d₁ p₁ e₁) (hrefl c t)    = stablecd?-ren ρ c
trstk?-ren ρ (ap c₁ b₁ p₁) (hrefl c t)    = stablecd?-ren ρ c
trstk?-ren ρ (⌜Id⌝ c₁ a₁ b₁) (hrefl c t)  = stablecd?-ren ρ c
trstk?-ren ρ (idrefl c₁ t₁) (hrefl c t)   = stablecd?-ren ρ c
trstk?-ren ρ (jsub d₁ p₁ e₁) (hrefl c t)  = stablecd?-ren ρ c
trstk?-ren ρ d (tr e q w)    = trstk?-ren ρ e q
trstk?-ren ρ d (ap c b p)    = apstk?-ren ρ p
trstk?-ren ρ d (⌜Id⌝ c a b)  = refl
trstk?-ren ρ d (idrefl c t)  = refl
trstk?-ren ρ d (jsub d₁ p e) = idstk?-ren ρ p

nopw?-ren ρ (var x)       = refl
nopw?-ren ρ (lam t)       = refl
nopw?-ren ρ (app t u)     = spine?-ren ρ t
nopw?-ren ρ (pair a b)    = refl
nopw?-ren ρ (fst t)       = spine?-ren ρ t
nopw?-ren ρ (snd t)       = spine?-ren ρ t
nopw?-ren ρ ⌜base⌝        = refl
nopw?-ren ρ (⌜Π⌝ c d)     = refl
nopw?-ren ρ (⌜Σ⌝ c d)     = refl
nopw?-ren ρ (⌜Hom⌝ c a b) = nopw?-ren ρ c
nopw?-ren ρ (hrefl c t)   = refl
nopw?-ren ρ (tr d p e)    = trstk?-ren ρ d p
nopw?-ren ρ (ap c b p)    = refl
nopw?-ren ρ (⌜Id⌝ c a b)  = refl
nopw?-ren ρ (idrefl c t)  = refl
nopw?-ren ρ (jsub d p e)  = idstk?-ren ρ p

deadmot?-ren ρ (var x)       = refl
deadmot?-ren ρ (lam t)       = refl
deadmot?-ren ρ (app t u)     = spine?-ren ρ t
deadmot?-ren ρ (pair a b)    = refl
deadmot?-ren ρ (fst t)       = spine?-ren ρ t
deadmot?-ren ρ (snd t)       = spine?-ren ρ t
deadmot?-ren ρ ⌜base⌝        = refl
deadmot?-ren ρ (⌜Π⌝ c d)     = refl
deadmot?-ren ρ (⌜Σ⌝ c d)     = refl
deadmot?-ren ρ (⌜Hom⌝ c a b) = deadmot?-ren ρ c
deadmot?-ren ρ (hrefl c t)   = deadmot?-ren ρ c
deadmot?-ren ρ (tr d p e)    = trstk?-ren ρ d p
deadmot?-ren ρ (ap c b p)    = apstk?-ren ρ p
deadmot?-ren ρ (⌜Id⌝ c a b)  = refl
deadmot?-ren ρ (idrefl c t)  = refl
deadmot?-ren ρ (jsub d p e)  = idstk?-ren ρ p

trlam?-ren ρ (var vz)     = refl
trlam?-ren ρ (var (vs x)) = refl
trlam?-ren ρ (lam t)      = refl
trlam?-ren ρ (app t u)    = refl
trlam?-ren ρ (pair a b)   = refl
trlam?-ren ρ (fst t)      = refl
trlam?-ren ρ (snd t)      = refl
trlam?-ren ρ ⌜base⌝       = refl
trlam?-ren ρ (⌜Π⌝ c d)    = refl
trlam?-ren ρ (⌜Σ⌝ c d)    = refl
trlam?-ren ρ (⌜Hom⌝ c a (var vz))     = deadmot?-ren (extR ρ) c
trlam?-ren ρ (⌜Hom⌝ c a (var (vs x))) = refl
trlam?-ren ρ (⌜Hom⌝ c a (lam m))      = refl
trlam?-ren ρ (⌜Hom⌝ c a (app m₁ m₂))  = refl
trlam?-ren ρ (⌜Hom⌝ c a (pair m₁ m₂)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (fst m))      = refl
trlam?-ren ρ (⌜Hom⌝ c a (snd m))      = refl
trlam?-ren ρ (⌜Hom⌝ c a ⌜base⌝)       = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜Π⌝ m₁ m₂))  = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜Σ⌝ m₁ m₂))  = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜Hom⌝ m₁ m₂ m₃)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (hrefl m₁ m₂))    = refl
trlam?-ren ρ (⌜Hom⌝ c a (tr m₁ m₂ m₃))    = refl
trlam?-ren ρ (⌜Hom⌝ c a (ap m₁ m₂ m₃))    = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜Id⌝ m₁ m₂ m₃))  = refl
trlam?-ren ρ (⌜Hom⌝ c a (idrefl m₁ m₂))   = refl
trlam?-ren ρ (⌜Hom⌝ c a (jsub m₁ m₂ m₃))  = refl
trlam?-ren ρ (hrefl c t)  = refl
trlam?-ren ρ (tr d p e)   = refl
trlam?-ren ρ (ap c b p)   = refl
trlam?-ren ρ (⌜Id⌝ c a b) = refl
trlam?-ren ρ (idrefl c t) = refl
trlam?-ren ρ (jsub d p e) = refl


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
  sh-Id   : {A : RTy Γ} {t u : RTm Γ} → StkHd (Id A t u)

stkhd-red : {H H' : RTy Γ} → StkHd H → H ⟶ᵀ H' → StkHd H'
stkhd-red (sh-ne ()) El-⌜base⌝
stkhd-red (sh-ne ()) (El-⌜Π⌝ _ _)
stkhd-red (sh-ne ()) (El-⌜Σ⌝ _ _)
stkhd-red (sh-ne n)  (ξ-El r)    = sh-ne (ne-red n r)
stkhd-red sh-Id (ξ-Idᵀ r) = sh-Id
stkhd-red sh-Id (ξ-Idˡ r) = sh-Id
stkhd-red sh-Id (ξ-Idʳ r) = sh-Id
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

-- the endpoint-join payload: reaching an `idrefl` yields a confluence
-- join of the Id-type's endpoints.
IdPay : (a b p : RTm Γ) → Set
IdPay {Γ} a b p =
  {c s : RTm Γ} → p ⟶snr* idrefl c s →
  Σ (RTm Γ) (λ w → (a ⟶* w) × (b ⟶* w))

-- re-base a payload across component joins (TERM confluence zig-zag) —
-- what irrel's Id-Id transfer rides.
idpay-transfer :
  {a b a' b' : RTm Γ} →
  Σ (RTm Γ) (λ v → (a ⟶* v) × (a' ⟶* v)) →
  Σ (RTm Γ) (λ v → (b ⟶* v) × (b' ⟶* v)) →
  {p : RTm Γ} → IdPay a b p → IdPay a' b' p
idpay-transfer (v , (av , a'v)) (v₂ , (bv₂ , b'v₂)) pay ch with pay ch
... | w , (aw , bw) with confluent aw av
...   | z , (wz , vzc) with confluent (⟶*-trans bw wz) bv₂
...     | z₃ , (zz₃ , v₂z₃) =
        z₃ , ( ⟶*-trans a'v (⟶*-trans vzc zz₃)
             , ⟶*-trans b'v₂ v₂z₃ )

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
  -- ★ the two-former kernel: `Id` at level 0 (`⌜Id⌝` decodes).  The
  -- MEMBERSHIP carries the ENDPOINT-JOIN PAYLOAD (SPIKE-TWOFORMER §4):
  -- reaching a reflexivity witnesses the endpoints' confluence join —
  -- what makes fund's `jsub` transfer conversion-based at ARBITRARY
  -- motives.
  ⊩₀Id   : {A H : RTy Γ} {a b : RTm Γ}
         → A ⟶ᵀ* Id H a b → ⊩₀ A

⊩₀base _     ⊩₀∋ t = SN t
⊩₀ne _ _     ⊩₀∋ t = SN t
⊩₀Π _ ⊩F ⊩G  ⊩₀∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ app t u)
-- the DEPENDENT pair: the second component's type depends on the first.
⊩₀Σ _ ⊩F ⊩G  ⊩₀∋ t =
  SN t × Σ (⊩F ⊩₀∋ fst t) (λ r → (⊩G (fst t) r) ⊩₀∋ snd t)
⊩₀Hom _ _    ⊩₀∋ t = SN t
⊩₀Id {a = a} {b = b} _ ⊩₀∋ t = SN t × IdPay a b t

bwd₀ : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩₀ B → ⊩₀ A
bwd₀ p (⊩₀base q)    = ⊩₀base (⟶ᵀ*-trans p q)
bwd₀ p (⊩₀ne q n)    = ⊩₀ne   (⟶ᵀ*-trans p q) n
bwd₀ p (⊩₀Π q ⊩F ⊩G) = ⊩₀Π    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₀ p (⊩₀Σ q ⊩F ⊩G) = ⊩₀Σ    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₀ p (⊩₀Hom q s)   = ⊩₀Hom  (⟶ᵀ*-trans p q) s
bwd₀ p (⊩₀Id q)      = ⊩₀Id   (⟶ᵀ*-trans p q)

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
-- ★ `Id` against everything: the clashes ride `Id-reduct` (Id is
-- inert); Id-Id is the REAL transfer — component joins re-base the
-- endpoint payload (`idpay-transfer`).
irrel₀ c (⊩₀Id p) (⊩₀base q) with joinW c p q
... | E , (iE , bE) with base-nf bE
...   | refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀base p) (⊩₀Id q) with joinW c p q
... | E , (bE , iE) with base-nf bE
...   | refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀Id p) (⊩₀ne q n) with joinW c p q
... | E , (iE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀ne p n) (⊩₀Id q) with joinW c p q
... | E , (eE , iE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀Id p) (⊩₀Π q _ _) with joinW c p q
... | E , (iE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀Π p _ _) (⊩₀Id q) with joinW c p q
... | E , (πE , iE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀Id p) (⊩₀Σ q _ _) with joinW c p q
... | E , (iE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀Σ p _ _) (⊩₀Id q) with joinW c p q
... | E , (σE , iE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀Id p) (⊩₀Hom q sh) with joinW c p q
... | E , (iE , hE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀Hom p sh) (⊩₀Id q) with joinW c p q
... | E , (hE , iE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₀ c (⊩₀Id {a = a} {b = b} p) (⊩₀Id {a = a'} {b = b'} q)
  with joinW c p q
... | E , (iE , iE') with Id-reduct iE | Id-reduct iE'
...   | H₁ , (a₁ , (b₁ , (eq₁ , (rH₁ , (ra₁ , rb₁)))))
      | H₂ , (a₂ , (b₂ , (eq₂ , (rH₂ , (ra₂ , rb₂)))))
      with trans (sym eq₁) eq₂
...     | refl =
        ( (λ t h → ( projl h
                   , idpay-transfer (a₁ , (ra₁ , ra₂)) (b₁ , (rb₁ , rb₂))
                                    (projr h) ))
        , (λ t h → ( projl h
                   , idpay-transfer (a₁ , (ra₂ , ra₁)) (b₁ , (rb₂ , rb₁))
                                    (projr h) )) )
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
fwd₀ p (⊩₀Id q) with confluentᵀ p q
... | E , (bE , iE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) = ⊩₀Id bE

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
CR1₀ (⊩₀Id _)    h = projl h

CR3₀ : {A : RTy Γ} (R : ⊩₀ A) {t : RTm Γ} → SNe t → R ⊩₀∋ t
CR3₀ (⊩₀base _)    nt = sn-ne nt
CR3₀ (⊩₀Hom _ _)   nt = sn-ne nt
CR3₀ (⊩₀Id _)      nt = (sn-ne nt , λ ch → ⊥-elim (sne-nopay nt ch))
CR3₀ (⊩₀ne _ _)    nt = sn-ne nt
CR3₀ (⊩₀Π _ ⊩F ⊩G) nt =
  (sn-ne nt , λ u ru → CR3₀ (⊩G u ru) (sne-app nt (CR1₀ ⊩F ru)))
CR3₀ (⊩₀Σ _ ⊩F ⊩G) {t} nt =
  (sn-ne nt , ( CR3₀ ⊩F (sne-fst nt)
              , CR3₀ (⊩G (fst t) (CR3₀ ⊩F (sne-fst nt))) (sne-snd nt) ))

exp₀ : {A : RTy Γ} (R : ⊩₀ A) {t t' : RTm Γ} → SNRed t t' → R ⊩₀∋ t' → R ⊩₀∋ t
exp₀ (⊩₀base _)    r h = sn-exp r h
exp₀ (⊩₀Hom _ _)   r h = sn-exp r h
exp₀ (⊩₀Id _) r h =
  ( sn-exp r (projl h)
  , λ ch → projr h (idpay-peel r ch) )
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

------------------------------------------------------------------------
-- ★★ W2b (G1f) — THE U-MEMBERSHIP PAYLOAD (SpikeUPay, landed).
-- `PayT R c` is the UNFOLDING TREE of `hrefl c ·`: one node per
-- semantic Π-layer, carrying the code's spine-normalization (CSRs to a
-- pw-whnf), the pw-key there, SN of the instantiated body code, and
-- the recursive payload at the body interp.  Chains are DERIVED
-- (`payChain`), so the tree is pure data and transports structurally.
------------------------------------------------------------------------

wk-single : {v : RTm Γ} (t : RTm Γ) → subTm (single v) (renTm vs t) ≡ t
wk-single t = trans (subTm-renTm t) (subTm-id t)

infix 3 _⟶csr*_
data _⟶csr*_ {Γ} : RTm Γ → RTm Γ → Set where
  csr-done : {t : RTm Γ} → t ⟶csr* t
  csr-step : {t u v : RTm Γ} → CSR t u → u ⟶csr* v → t ⟶csr* v

PayT : {A : RTy Γ} (R : ⊩₀ A) (c : RTm Γ) → Set
PayT (⊩₀base _)  c = ⊤
PayT (⊩₀ne _ _)  c = ⊤
PayT (⊩₀Σ _ _ _) c = ⊤
PayT (⊩₀Hom _ _) c = ⊤
PayT (⊩₀Id _)    c = ⊤
PayT {Γ = Γ} (⊩₀Π _ ⊩F ⊩G) c =
  (v : RTm Γ) (r : ⊩F ⊩₀∋ v) →
  Σ (RTm Γ) (λ c* →
    (c ⟶csr* c*)
    × ((pw? c* ≡ true)
    × ((SN (subTm (single v) (pwBody c*)))
    × PayT (⊩G v r) (subTm (single v) (pwBody c*)))))



-- the derived wire: spine-normalize, unfold pointwise, β.
payChain : {c c* : RTm Γ} → c ⟶csr* c* → pw? c* ≡ true →
           (v : RTm Γ) → SN v → (s : RTm Γ) →
           app (hrefl c s) v ⟶snr*
           hrefl (subTm (single v) (pwBody c*)) (app s v)
payChain csr-done key v snv s =
  snr-step (snr-app (snr-hrefl-pw key))
    (snr-step (snr-β snv)
      (subst (λ z → hrefl _ (app z v) ⟶snr* hrefl _ (app s v))
             (sym (wk-single s)) snr-done))
payChain (csr-step σ rest) key v snv s =
  snr-step (snr-app (snr-hreflᶜ σ)) (payChain rest key v snv s)

-- the payload rides backward along head steps of the code (the
-- `exp₁`-side transport): prefix the spine-normalization.
payT-exp : {c c' : RTm Γ} (r : SNRed c c')
           {B B' : RTy Γ} (q : B ⟶ᵀ* B') (R : ⊩₀ B') →
           PayT R c' → PayT (bwd₀ q R) c
payT-exp r q (⊩₀base _)  pay = _
payT-exp r q (⊩₀ne _ _)  pay = _
payT-exp r q (⊩₀Σ _ _ _) pay = _
payT-exp r q (⊩₀Hom _ _) pay = _
payT-exp r q (⊩₀Id _) pay = _
payT-exp r q (⊩₀Π _ ⊩F ⊩G) pay v rv with pay v rv
... | c* , (csr , rest) = c* , (csr-step (csr-here r) csr , rest)

-- ...and forward (the `mem-whred₁`-side): peel the (deterministic)
-- first spine step.
payT-whred-node :
  {c c' : RTm Γ} (r : SNRed c c') {c* : RTm Γ} →
  c ⟶csr* c* → pw? c* ≡ true → c' ⟶csr* c*
payT-whred-node r csr-done key with trans (sym (snr-nonpw r)) key
... | ()
payT-whred-node r (csr-step σ rest) key with csr-det σ (csr-here r)
... | refl = rest

payT-whred : {c c' : RTm Γ} (r : SNRed c c')
             {B : RTy Γ} (R : ⊩₀ B) → PayT R c → PayT R c'
payT-whred r (⊩₀base _)  pay = _
payT-whred r (⊩₀ne _ _)  pay = _
payT-whred r (⊩₀Σ _ _ _) pay = _
payT-whred r (⊩₀Hom _ _) pay = _
payT-whred r (⊩₀Id _) pay = _
payT-whred r (⊩₀Π _ ⊩F ⊩G) pay v rv with pay v rv
... | c* , (csr , (key , rest)) =
      c* , (payT-whred-node r csr key , (key , rest))

-- payload transfer across interps of CONVERTIBLE types — the
-- `irrel₀`-mirror (what `fwd₀`-moved and `≅ᵀ`-aligned interps need).
payT-irrel : {A B : RTy Γ} (cv : A ≅ᵀ B) (R : ⊩₀ A) (S : ⊩₀ B)
             {c : RTm Γ} → PayT R c → PayT S c
payT-irrel cv R (⊩₀base _)  pay = _
payT-irrel cv R (⊩₀ne _ _)  pay = _
payT-irrel cv R (⊩₀Σ _ _ _) pay = _
payT-irrel cv R (⊩₀Hom _ _) pay = _
payT-irrel cv R (⊩₀Id _) pay = _
payT-irrel cv (⊩₀base p) (⊩₀Π q _ _) pay with joinW cv p q
... | E , (bE , πE) with base-nf bE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
payT-irrel cv (⊩₀ne p n) (⊩₀Π q _ _) pay with joinW cv p q
... | E , (bE , πE) with El-ne-reduct n bE
...   | mkElNe _ _ refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
payT-irrel cv (⊩₀Σ p _ _) (⊩₀Π q _ _) pay with joinW cv p q
... | E , (σE , πE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Π-reduct πE
...     | mkΠRed _ _ () _ _
payT-irrel cv (⊩₀Hom p s) (⊩₀Π q _ _) pay with joinW cv p q
... | E , (hE , πE) with Hom-stk-reduct s hE
...   | mkHomStk _ _ _ _ refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
payT-irrel cv (⊩₀Id p) (⊩₀Π q _ _) pay v r' with joinW cv p q
... | E , (iE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
payT-irrel cv (⊩₀Π p ⊩F ⊩G) (⊩₀Π q ⊩F' ⊩G') pay v r'
  with joinW cv p q
... | E , (πE₁ , πE₂) with Π-reduct πE₁ | Π-reduct πE₂
...   | mkΠRed F₁ G₁ eq₁ rF₁ rG₁ | mkΠRed F₂ G₂ eq₂ rF₂ rG₂
        with Πinj≡ (trans (sym eq₁) eq₂)
...       | (refl , refl)
          with pay v (projr (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁)
                                           (csymᵀ (red→≅ᵀ rF₂)))
                                    ⊩F ⊩F') v r')
...         | c* , (csr , (key , (snb , pb))) =
            c* , (csr , (key , (snb ,
              payT-irrel (≅ᵀ-sub (single v)
                           (ctrnᵀ (red→≅ᵀ rG₁) (csymᵀ (red→≅ᵀ rG₂))))
                         (⊩G v (projr (irrel₀ (ctrnᵀ (red→≅ᵀ rF₁)
                                                     (csymᵀ (red→≅ᵀ rF₂)))
                                              ⊩F ⊩F') v r'))
                         (⊩G' v r') pb)))

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
  ⊩₁Id   : {A H : RTy Γ} {a b : RTm Γ}
         → A ⟶ᵀ* Id H a b → ⊩₁ A

⊩₁base _     ⊩₁∋ t = SN t
⊩₁U _        ⊩₁∋ t = SN t × Σ (⊩₀ (El t)) (λ R → PayT R t)
⊩₁ne _ _     ⊩₁∋ t = SN t
⊩₁Π _ ⊩F ⊩G  ⊩₁∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩₁∋ u) → (⊩G u r) ⊩₁∋ app t u)
⊩₁Σ _ ⊩F ⊩G  ⊩₁∋ t =
  SN t × Σ (⊩F ⊩₁∋ fst t) (λ r → (⊩G (fst t) r) ⊩₁∋ snd t)
⊩₁Hom _ _    ⊩₁∋ t = SN t
⊩₁Id {a = a} {b = b} _ ⊩₁∋ t = SN t × IdPay a b t

bwd₁ : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩₁ B → ⊩₁ A
bwd₁ p (⊩₁base q)    = ⊩₁base (⟶ᵀ*-trans p q)
bwd₁ p (⊩₁U q)       = ⊩₁U    (⟶ᵀ*-trans p q)
bwd₁ p (⊩₁ne q n)    = ⊩₁ne   (⟶ᵀ*-trans p q) n
bwd₁ p (⊩₁Π q ⊩F ⊩G) = ⊩₁Π    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₁ p (⊩₁Σ q ⊩F ⊩G) = ⊩₁Σ    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₁ p (⊩₁Hom q s)   = ⊩₁Hom  (⟶ᵀ*-trans p q) s
bwd₁ p (⊩₁Id q)      = ⊩₁Id   (⟶ᵀ*-trans p q)

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
irrel₁ c (⊩₁Id p) (⊩₁base q) with joinW c p q
... | E , (iE , bE) with base-nf bE
...   | refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁base p) (⊩₁Id q) with joinW c p q
... | E , (bE , iE) with base-nf bE
...   | refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Id p) (⊩₁U q) with joinW c p q
... | E , (iE , uE) with U-nf uE
...   | refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁U p) (⊩₁Id q) with joinW c p q
... | E , (uE , iE) with U-nf uE
...   | refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Id p) (⊩₁ne q n) with joinW c p q
... | E , (iE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁ne p n) (⊩₁Id q) with joinW c p q
... | E , (eE , iE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Id p) (⊩₁Π q _ _) with joinW c p q
... | E , (iE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Π p _ _) (⊩₁Id q) with joinW c p q
... | E , (πE , iE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Id p) (⊩₁Σ q _ _) with joinW c p q
... | E , (iE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Σ p _ _) (⊩₁Id q) with joinW c p q
... | E , (σE , iE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Id p) (⊩₁Hom q sh) with joinW c p q
... | E , (iE , hE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Hom p sh) (⊩₁Id q) with joinW c p q
... | E , (hE , iE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Id-reduct iE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Id {a = a} {b = b} p) (⊩₁Id {a = a'} {b = b'} q)
  with joinW c p q
... | E , (iE , iE') with Id-reduct iE | Id-reduct iE'
...   | H₁ , (a₁ , (b₁ , (eq₁ , (rH₁ , (ra₁ , rb₁)))))
      | H₂ , (a₂ , (b₂ , (eq₂ , (rH₂ , (ra₂ , rb₂)))))
      with trans (sym eq₁) eq₂
...     | refl =
        ( (λ t h → ( projl h
                   , idpay-transfer (a₁ , (ra₁ , ra₂)) (b₁ , (rb₁ , rb₂))
                                    (projr h) ))
        , (λ t h → ( projl h
                   , idpay-transfer (a₁ , (ra₂ , ra₁)) (b₁ , (rb₂ , rb₁))
                                    (projr h) )) )
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
fwd₁ p (⊩₁Id q) with confluentᵀ p q
... | E , (bE , iE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) = ⊩₁Id bE

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
CR1₁ (⊩₁Id _)    h = projl h

CR3₁ : {A : RTy Γ} (R : ⊩₁ A) {t : RTm Γ} → SNe t → R ⊩₁∋ t
CR3₁ (⊩₁base _)    nt = sn-ne nt
CR3₁ (⊩₁U _)       nt = (sn-ne nt , (⊩₀ne doneᵀ (sne→ne nt) , _))
CR3₁ (⊩₁ne _ _)    nt = sn-ne nt
CR3₁ (⊩₁Hom _ _)   nt = sn-ne nt
CR3₁ (⊩₁Id _)      nt = (sn-ne nt , λ ch → ⊥-elim (sne-nopay nt ch))
CR3₁ (⊩₁Π _ ⊩F ⊩G) nt =
  (sn-ne nt , λ u ru → CR3₁ (⊩G u ru) (sne-app nt (CR1₁ ⊩F ru)))
CR3₁ (⊩₁Σ _ ⊩F ⊩G) {t} nt =
  (sn-ne nt , ( CR3₁ ⊩F (sne-fst nt)
              , CR3₁ (⊩G (fst t) (CR3₁ ⊩F (sne-fst nt))) (sne-snd nt) ))

exp₁ : {A : RTy Γ} (R : ⊩₁ A) {t t' : RTm Γ} → SNRed t t' → R ⊩₁∋ t' → R ⊩₁∋ t
exp₁ (⊩₁base _)    r h = sn-exp r h
exp₁ (⊩₁ne _ _)    r h = sn-exp r h
exp₁ (⊩₁Hom _ _)   r h = sn-exp r h
exp₁ (⊩₁Id _) r h =
  ( sn-exp r (projl h) , λ ch → projr h (idpay-peel r ch) )
exp₁ (⊩₁U _)       r h =
  ( sn-exp r (projl h)
  , ( bwd₀ (⟶ᵀ*-El (step (snr→⟶ r) done)) (Σ.fst (projr h))
    , payT-exp r (⟶ᵀ*-El (step (snr→⟶ r) done)) (Σ.fst (projr h))
               (Σ.snd (projr h)) ) )
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

-- W2 stage 2: memberships move FORWARD along the (deterministic) head
-- strategy — `exp₁`'s converse.  The `Σ'` case bridges the moving type
-- of the second component exactly as `exp₁`'s does, direction flipped;
-- the `U` case pushes the decoded type forward along the step.
mem-whred₁ : {A : RTy Γ} (R : ⊩₁ A) {t t' : RTm Γ} →
             SNRed t t' → R ⊩₁∋ t → R ⊩₁∋ t'
mem-whred₁ (⊩₁base _)  r h = sn-whred h r
mem-whred₁ (⊩₁ne _ _)  r h = sn-whred h r
mem-whred₁ (⊩₁Hom _ _) r h = sn-whred h r
mem-whred₁ (⊩₁Id _) r h =
  ( sn-whred (projl h) r , λ ch → projr h (snr-step r ch) )
mem-whred₁ (⊩₁U _)     r h =
  ( sn-whred (projl h) r
  , ( fwd₀ (⟶ᵀ*-El (step (snr→⟶ r) done)) (Σ.fst (projr h))
    , payT-irrel (red→≅ᵀ (⟶ᵀ*-El (step (snr→⟶ r) done)))
                 (Σ.fst (projr h))
                 (fwd₀ (⟶ᵀ*-El (step (snr→⟶ r) done)) (Σ.fst (projr h)))
                 (payT-whred r (Σ.fst (projr h)) (Σ.snd (projr h))) ) )
mem-whred₁ (⊩₁Π _ ⊩F ⊩G) r h =
  ( sn-whred (projl h) r
  , λ u ru → mem-whred₁ (⊩G u ru) (snr-app r) (projr h u ru) )
mem-whred₁ (⊩₁Σ {G = G} _ ⊩F ⊩G) {t} {t'} r h =
  ( sn-whred (projl h) r
  , ( mem-whred₁ ⊩F (snr-fst r) (dfst (projr h))
    , projl (irrel₁ (red→≅ᵀ (subTy-monoˢ
                       (single-mono (step (ξ-fst (snr→⟶ r)) done)) G))
                    (⊩G (fst t) (dfst (projr h)))
                    (⊩G (fst t') (mem-whred₁ ⊩F (snr-fst r) (dfst (projr h)))))
            (snd t')
            (mem-whred₁ (⊩G (fst t) (dfst (projr h))) (snr-snd r)
                        (dsnd (projr h))) ))

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
emb (⊩₀Id p)      = ⊩₁Id p
emb (⊩₀ne p n)    = ⊩₁ne p n
emb (⊩₀Π p ⊩F ⊩G) =
  ⊩₁Π p (emb ⊩F) (λ u r → emb (⊩G u (projr (emb-coh ⊩F) u r)))
emb (⊩₀Σ p ⊩F ⊩G) =
  ⊩₁Σ p (emb ⊩F) (λ u r → emb (⊩G u (projr (emb-coh ⊩F) u r)))

emb-coh (⊩₀base _) = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀Hom _ _) = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀Id _)    = (λ _ h → h) , (λ _ h → h)
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
sem-El p h = Σ.fst (projr h)

sem-⌜base⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) → (⊩₁U p) ⊩₁∋ ⌜base⌝
sem-⌜base⌝ p = (sn-cb , (⊩₀base (stepᵀ El-⌜base⌝ doneᵀ) , _))

-- ★ where PREDICATIVITY does structural work: the decoding of a compound code
-- is a level-0 `Π` built from the decodings of its STRICTLY SMALLER components.
-- W2b: a ⌜Π⌝-code's U-membership now carries its payload node — the
-- body code's SN and payload at every argument (`fund dδ` at extended
-- environments supplies both; SpikeUPay's `pay-⌜Π⌝`, landed).
sem-⌜Π⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) {c : RTm Γ} {d : RTm (Γ ∙)}
        → SN c → SN d
        → (⊩c : ⊩₀ (El c))
        → (f : (u : RTm Γ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) d)))
        → ((u : RTm Γ) (r : ⊩c ⊩₀∋ u) →
             SN (subTm (single u) d) × PayT (f u r) (subTm (single u) d))
        → (⊩₁U p) ⊩₁∋ ⌜Π⌝ c d
sem-⌜Π⌝ p snc snD ⊩c f pays =
  ( sn-cΠ snc snD
  , ( ⊩₀Π (stepᵀ (El-⌜Π⌝ _ _) doneᵀ) ⊩c f
    , (λ v r → ⌜Π⌝ _ _
             , (csr-done
             , (refl
             , (projl (pays v r) , projr (pays v r))))) ) )

sem-⌜Σ⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) {c : RTm Γ} {d : RTm (Γ ∙)}
        → SN c → SN d
        → (⊩c : ⊩₀ (El c))
        → ((u : RTm Γ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) d)))
        → (⊩₁U p) ⊩₁∋ ⌜Σ⌝ c d
sem-⌜Σ⌝ p snc snD ⊩c f =
  (sn-cΣ snc snD , (⊩₀Σ (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ) ⊩c f , _))

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

-- (`wk-single` moved up, before the PayT block)

homSem₁ : {A : RTy Γ} (R : ⊩₁ A) {a b : RTm Γ} →
          R ⊩₁∋ a → R ⊩₁∋ b → ⊩₁ (Hom A a b)
homSem₁ (⊩₁base p)    ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) sh-base
homSem₁ (⊩₁ne p n)    ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-ne n)
homSem₁ (⊩₁Σ p ⊩F ⊩G) ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) sh-Σ
homSem₁ (⊩₁Hom p s)   ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom s)
homSem₁ (⊩₁Id p)      ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) sh-Id
homSem₁ (⊩₁U p) {c} {d} hc hd =
  ⊩₁Π (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ p) (stepᵀ (Hom-U c d) doneᵀ))
      (emb (Σ.fst (projr hc)))
      (λ v r → subst ⊩₁_ (sym (cong El (wk-single d)))
                     (emb (Σ.fst (projr hd))))
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
homSem₀ (⊩₀Id p)      ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) sh-Id
homSem₀ (⊩₀Π {F = F} {G = G} p ⊩F ⊩G) {a} {b} ha hb =
  ⊩₀Π (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ p) (stepᵀ (Hom-Π F G a b) doneᵀ))
      ⊩F
      (λ v r →
        subst ⊩₀_
              (sym (Hom-cong₃ refl
                     (cong₂ app (wk-single a) refl)
                     (cong₂ app (wk-single b) refl)))
              (homSem₀ (⊩G v r) (projr ha v r) (projr hb v r)))

-- membership transport through `subst`-casts of a level-0 interp
mem₀-cast : {A B : RTy Γ} (eq : A ≡ B) (R : ⊩₀ A) {t : RTm Γ} →
            R ⊩₀∋ t → (subst ⊩₀_ eq R) ⊩₀∋ t
mem₀-cast refl R h = h

mem₀-cast⁻ : {A B : RTy Γ} (eq : A ≡ B) (R : ⊩₀ A) {t : RTm Γ} →
             (subst ⊩₀_ eq R) ⊩₀∋ t → R ⊩₀∋ t
mem₀-cast⁻ refl R h = h

-- ★ memberships at a `homSem₀`-interp do not depend on the ENDPOINTS
-- (SpikeTrLR, promoted): `SN` at every stuck leaf, pointwise through the
-- `Π` skeleton.  This hands `fund`'s J-branches their payload across the
-- endpoint switch — the `PosC`-pinned motive is endpoint-blind in every
-- other component.
homSem₀-mem-endpoints :
  {A : RTy Γ} (R : ⊩₀ A) {a b a' b' : RTm Γ}
  (ha : R ⊩₀∋ a) (hb : R ⊩₀∋ b) (ha' : R ⊩₀∋ a') (hb' : R ⊩₀∋ b')
  {t : RTm Γ} →
  (homSem₀ R ha hb) ⊩₀∋ t → (homSem₀ R ha' hb') ⊩₀∋ t
homSem₀-mem-endpoints (⊩₀base p)    ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀ne p n)    ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀Σ p ⊩F ⊩G) ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀Hom p s)   ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀Id p) ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀Π {F = F} {G = G} p ⊩F ⊩G)
                      {a} {b} {a'} {b'} ha hb ha' hb' {t} h =
  ( projl h
  , λ v r →
      mem₀-cast
        (sym (Hom-cong₃ refl
               (cong₂ app (wk-single a') refl)
               (cong₂ app (wk-single b') refl)))
        (homSem₀ (⊩G v r) (projr ha' v r) (projr hb' v r))
        (homSem₀-mem-endpoints (⊩G v r)
          (projr ha v r) (projr hb v r) (projr ha' v r) (projr hb' v r)
          (mem₀-cast⁻
            (sym (Hom-cong₃ refl
                   (cong₂ app (wk-single a) refl)
                   (cong₂ app (wk-single b) refl)))
            (homSem₀ (⊩G v r) (projr ha v r) (projr hb v r))
            (projr h v r))) )

-- ★ `sem-⌜Hom⌝`: the `⌜Hom⌝` code is a semantic CODE — its decoding is a
-- small semantic type, via `homSem₀` and one decode step.
-- W2b payload plumbing: tiny casts, the spine-map, and ★ `payHomT` —
-- a ⌜Hom⌝-code's payload from its inner code's payload, mirroring
-- `homSem₀`'s recursion (the spine-normalization maps through
-- `csr-hom`; the pw-key is definitionally the inner one; the body
-- code's instantiation computes by `wk-single`).
payT-cast : {A B : RTy Γ} (eq : A ≡ B) (R : ⊩₀ A) {c : RTm Γ} →
            PayT R c → PayT (subst ⊩₀_ eq R) c
payT-cast refl R pay = pay

payT-code : {A : RTy Γ} (R : ⊩₀ A) {c c' : RTm Γ} → c ≡ c' →
            PayT R c → PayT R c'
payT-code R refl pay = pay

csrs-hom : {c c' a b : RTm Γ} → c ⟶csr* c' →
           ⌜Hom⌝ c a b ⟶csr* ⌜Hom⌝ c' a b
csrs-hom csr-done       = csr-done
csrs-hom (csr-step σ q) = csr-step (csr-hom σ) (csrs-hom q)

payHomT : {X : RTy Γ} (⊩c : ⊩₀ X) {C a b : RTm Γ}
          (payC : PayT ⊩c C)
          (ha : ⊩c ⊩₀∋ a) (hb : ⊩c ⊩₀∋ b) →
          PayT (homSem₀ ⊩c ha hb) (⌜Hom⌝ C a b)
payHomT (⊩₀base _)  payC ha hb = _
payHomT (⊩₀ne _ _)  payC ha hb = _
payHomT (⊩₀Σ _ _ _) payC ha hb = _
payHomT (⊩₀Hom _ _) payC ha hb = _
payHomT (⊩₀Id p) payC ha hb = _
payHomT (⊩₀Π {F = F} {G = G} q ⊩F ⊩G) {C} {a} {b} payC ha hb v r
  with payC v r
... | C* , (csr , (key , (snb' , pb))) =
  ( ⌜Hom⌝ C* a b
  , ( csrs-hom csr
    , ( key
      , ( snBody
        , payT-cast
            (sym (Hom-cong₃ refl
                   (cong₂ app (wk-single a) refl)
                   (cong₂ app (wk-single b) refl)))
            (homSem₀ (⊩G v r) (projr ha v r) (projr hb v r))
            (payT-code (homSem₀ (⊩G v r) (projr ha v r) (projr hb v r))
              (⌜Hom⌝-cong₃ refl
                (cong (λ z → app z v) (sym (wk-single a)))
                (cong (λ z → app z v) (sym (wk-single b))))
              (payHomT (⊩G v r) pb (projr ha v r) (projr hb v r))) ) ) ) )
  where
  snBody : SN (subTm (single v) (pwBody (⌜Hom⌝ C* a b)))
  snBody = sn-cH snb'
             (subst (λ z → SN (app z v)) (sym (wk-single a))
                    (CR1₀ (⊩G v r) (projr ha v r)))
             (subst (λ z → SN (app z v)) (sym (wk-single b))
                    (CR1₀ (⊩G v r) (projr hb v r)))

sem-⌜Hom⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) {c a b : RTm Γ}
          → SN c → SN a → SN b
          → (⊩c : ⊩₀ (El c))
          → PayT ⊩c c
          → ⊩c ⊩₀∋ a → ⊩c ⊩₀∋ b
          → (⊩₁U p) ⊩₁∋ ⌜Hom⌝ c a b
sem-⌜Hom⌝ p snc sna snb ⊩c payc ha hb =
  ( sn-cH snc sna snb
  , ( bwd₀ (stepᵀ (El-⌜Hom⌝ _ _ _) doneᵀ) (homSem₀ ⊩c ha hb)
    , payT-bwd₀ (stepᵀ (El-⌜Hom⌝ _ _ _) doneᵀ) (homSem₀ ⊩c ha hb)
                (payHomT ⊩c payc ha hb) ) )
  where
  payT-bwd₀ : {A B : RTy _} (q : A ⟶ᵀ* B) (R : ⊩₀ B) {c₀ : RTm _} →
              PayT R c₀ → PayT (bwd₀ q R) c₀
  payT-bwd₀ q (⊩₀base _)  pay = _
  payT-bwd₀ q (⊩₀ne _ _)  pay = _
  payT-bwd₀ q (⊩₀Σ _ _ _) pay = _
  payT-bwd₀ q (⊩₀Hom _ _) pay = _
  payT-bwd₀ q (⊩₀Id _) pay = _
  payT-bwd₀ q (⊩₀Π _ _ _) pay = pay

-- ★ `sem-hrefl`: at a pw-IMMUNE code, `hrefl` is a neutral, and
-- neutrals inhabit every semantic type — in particular the `Hom` at
-- its own endpoints.  (W2b: pw-able codes UNFOLD, and their membership
-- is built pointwise in `fund`'s ⊢hrefl case — the semantic mirror of
-- `hrefl-pw`.)
sem-hrefl : {F : RTy Γ} (R : ⊩₁ F) {c t : RTm Γ} → SN c → SN t →
            nopw? c ≡ true →
            (ht : R ⊩₁∋ t) → (homSem₁ R ht ht) ⊩₁∋ hrefl c t
sem-hrefl R snc snt kn ht =
  CR3₁ (homSem₁ R ht ht) (sne-hrefl snc snt kn)

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
wne (sne-hrefl c t kn) with wn c | wn t
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWNe (hrefl n₁ n₂) (⟶*-trans (⟶*-hreflᶜ r₁) (⟶*-hreflᵃ r₂)) nrm'
            (sne-hrefl sn₁ sn₂ kn')
  where
    kn' : nopw? n₁ ≡ true
    kn' = nopw?-red* r₁ kn

    nrm' : IsNormal (hrefl n₁ n₂)
    nrm' (ξ-hreflᶜ q) = nm₁ q
    nrm' (ξ-hreflᵃ q) = nm₂ q
    nrm' (hrefl-pw C₀ _ kp) = f≢t (trans (sym (nopw⊥pw C₀ kn')) kp)
wne (sne-tr {d = d} {p = p} d₀ p₀ e₀ key) with wn d₀ | wn p₀ | wn e₀
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ | mkWN n₃ r₃ nm₃ sn₃ =
      mkWNe (tr n₁ n₂ n₃)
            (⟶*-trans (⟶*-trᵈ r₁) (⟶*-trans (⟶*-trᵖ r₂) (⟶*-trᵉ r₃)))
            nrm' (sne-tr sn₁ sn₂ sn₃ key')
  where
    key' : trstk? n₁ n₂ ≡ true
    key' = trstk?-red-p* {d = n₁} r₂ (trstk?-red-d* {p = p} r₁ key)

    nrm' : IsNormal (tr n₁ n₂ n₃)
    nrm' (tr-J-base _ _ _ _ _)  = ⊥-elim (f≢t key')
    nrm' (tr-J-Σ _ _ _ _ _ _ _) = ⊥-elim (f≢t key')
    nrm' (tr-J-Id _ _ _ _ _ _ _ _) = ⊥-elim (f≢t key')
    nrm' (tr-taut _ _)      = ⊥-elim (f≢t key')
    nrm' (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) =
      f≢t (trans (sym (stk⊥dead c₁ kh)) key')
    nrm' (tr-pw c₁ _ _ _ kp) =
      f≢t (trans (sym (nopw⊥pw c₁ (deadmot→nopw c₁ key'))) kp)
    nrm' (ξ-trᵈ q) = nm₁ q
    nrm' (ξ-trᵖ q) = nm₂ q
    nrm' (ξ-trᵉ q) = nm₃ q
wne (sne-ap {b = b} c₀ b₀ p₀ key) with wn c₀ | wn b₀ | wn p₀
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ | mkWN n₃ r₃ nm₃ sn₃ =
      mkWNe (ap n₁ n₂ n₃)
            (⟶*-trans (⟶*-apᶜ r₁) (⟶*-trans (⟶*-apᵇ r₂) (⟶*-apᵖ r₃)))
            nrm' (sne-ap sn₁ sn₂ sn₃ key')
  where
    key' : apstk? n₃ ≡ true
    key' = apstk?-red* r₃ key

    nrm' : IsNormal (ap n₁ n₂ n₃)
    nrm' (ap-J _ _ c₁ _ kh) = f≢t (trans (sym (stk⊥dead c₁ kh)) key')
    nrm' (ξ-apᶜ q) = nm₁ q
    nrm' (ξ-apᵇ q) = nm₂ q
    nrm' (ξ-apᵖ q) = nm₃ q
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
