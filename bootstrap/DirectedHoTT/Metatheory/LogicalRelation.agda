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
module DirectedHoTT.Metatheory.LogicalRelation where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; ¬_; ⊥; ⊥-elim; Σ; _,_; _×_; ⊤ )

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Typing using ( wk-single ) public
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam
        ; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl
        ; tr; ap; Id; ⌜Id⌝; idrefl; jsub; Unit; Nat; unit; nzero; nsuc; natrec
        ; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝; Ren; extR; Sub; subTy; subTm; extS
        ; renTm; subTm-renTm; subTm-id; Hom-cong₃; ⌜Hom⌝-cong₃; Desc; con; dι
        ; dρ; εwkTy; IMu; ielim; ⌜IMu⌝; εwkTm
        ; DIh; Fin; ⌜Fin⌝; dσ; dpay; dih; fzero; fsuc; fcase; fcase0; psplit; cong₄; cong₃ )
open import DirectedHoTT.Spec.Typing
  using ( single; nrs; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ
        ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ordtr-z; ordtr-szz; ordtr-ssz
        ; ordtr-szs; ordtr-sss; ξ-ordtrᵃ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ
        ; ξ-ordtrq; ξ-fst; ξ-snd; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; ξ-⌜Hom⌝ᶜ
        ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; tr-J-base; tr-J-Σ; tr-J-Unit
        ; tr-taut; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ; tr-J-Id
        ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ; ξ-idreflᵃ; ξ-jsubᵈ
        ; ξ-jsubᵖ; ξ-jsubᵉ; natrec-zero; natrec-suc; ξ-nsuc; ξ-natrecᶻ
        ; ξ-natrecˢ; ξ-natrecⁿ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss; El-⌜Id⌝
        ; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ; ⊢⌜Id⌝; ⊢idrefl; ⊢jsub; ⊢ap; hrefl-pw; tr-J-Hom
        ; tr-pw; _⟶*_; done; step; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝
        ; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜IMu⌝
        ; tr-J-IMu; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; _≅ᵀ_; credᵀ; crflᵀ
        ; csymᵀ; ctrnᵀ; ξ-con; ξ-ielimⁱ; ξ-ielimᵗ
        ; El-⌜Fin⌝; DIh-ι; DIh-σ; DIh-ρ; ξ-IMuᴵ; ξ-IMuᴰ; ξ-IMuⁱ; ξ-Desc; ξ-DIhᴰ; ξ-DIhᴹ; ξ-DIhᶜ; ξ-DIhᵖ; ι; dpay-ι; dpay-σ; dpay-ρ; dih-ι; dih-σ; dih-ρ; fcase-z; fcase-s; psplit-β; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ; ξ-⌜IMu⌝ⁱ; ξ-ielimᴰ; ξ-ielimᵉ; ξ-dι; ξ-dσˢ; ξ-dσᶠ; ξ-dρʲ; ξ-dρᶜ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dpayⁱ; ξ-dihᴰ; ξ-dihᵉ; ξ-dihᶜ; ξ-dihᵖ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0; ξ-psplitᵇ; ξ-psplitᵍ; tr-J-Fin; ⊢⌜IMu⌝; ⊢⌜Fin⌝; ⊢dι; ⊢dσ; ⊢dρ; ⊢dpay; ⊢con; ⊢dih; ⊢ielim; ⊢fzero; ⊢fsuc; ⊢fcase; ⊢fcase0; ⊢psplit; ty-IMu; ty-Desc; ty-DIh; ty-Fin; MethTy; motCtx; methS; wk2M; iinst; single2; pairS; fsucS; hom→≅; _≅_; cred; crfl; csym; ctrn )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; pw?; stkC?; stkA?; pwDom; pwBody; pwShift; pw?-ren
        ; stkC?-ren; stkA?-ren; pwBody-ren; pwDom-ren; stkC?→stkA?; stkA?⊥pw
        ; stk⊥pw; pw⊥stk )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( ⟶ᵀ-sub; ≅ᵀ-sub )
open import DirectedHoTT.Metatheory.TySub using ( subTy-monoˢ )
open import DirectedHoTT.Metatheory.Confluence using ( single-mono; confluent; ⟶*-absurdᶜ; ⟶*-absurdᵉ
        ; church-rosser; ⟶*-⌜IMu⌝ᴵ; ⟶*-⌜IMu⌝ᴰ; ⟶*-⌜IMu⌝ⁱ; ⟶*-ielimᴰ; ⟶*-ielimᵉ; ⟶*-dι; ⟶*-dσˢ; ⟶*-dσᶠ; ⟶*-dρʲ; ⟶*-dρᶜ; ⟶*-dpayᴵ; ⟶*-dpayᴰ; ⟶*-dpayᶜ; ⟶*-dpayⁱ; ⟶*-dihᴰ; ⟶*-dihᵉ; ⟶*-dihᶜ; ⟶*-dihᵖ; ⟶*-fsuc; ⟶*-fcaseᵗ; ⟶*-fcaseᵃ; ⟶*-fcaseᵇ; ⟶*-fcase0; ⟶*-psplitᵇ; ⟶*-psplitᵍ )
open import DirectedHoTT.Metatheory.Confluence
  using ( ⟶*-trans; ⟶*-lam; ⟶*-appˡ; ⟶*-appʳ
        ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd
        ; ⟶*-⌜Π⌝ˡ; ⟶*-⌜Π⌝ʳ; ⟶*-⌜Σ⌝ˡ; ⟶*-⌜Σ⌝ʳ
        ; ⟶*-⌜Hom⌝ᶜ; ⟶*-⌜Hom⌝ˡ; ⟶*-⌜Hom⌝ʳ; ⟶*-hreflᶜ; ⟶*-hreflᵃ
        ; ⟶*-trᵈ; ⟶*-trᵖ; ⟶*-trᵉ; ⟶*-apᶜ; ⟶*-apᵇ; ⟶*-apᵖ
        ; ⟶*-jsubᵈ; ⟶*-jsubᵖ; ⟶*-jsubᵉ; ⟶*-⌜Id⌝ᶜ; ⟶*-⌜Id⌝ˡ; ⟶*-⌜Id⌝ʳ
        ; ⟶*-idreflᶜ; ⟶*-idreflᵃ
        ; ⟶*-nsuc; ⟶*-natrecᶻ; ⟶*-natrecˢ; ⟶*-natrecⁿ ; ⟶*-absurdᶜ; ⟶*-absurdᵉ
        ; ⟶*-ordtrᵃ; ⟶*-ordtrᵗ; ⟶*-ordtrᵘ; ⟶*-ordtrᵖ; ⟶*-ordtrq
        ; ⟶*-con; subTm-monoˢ
        ; ⟶*-ielimⁱ; ⟶*-ielimᵗ )
open import DirectedHoTT.Metatheory.Injectivity
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; ⟶ᵀ*-Homᵀ
        ; confluentᵀ; church-rosserᵀ; Id-reduct
        ; ΠRed; mkΠRed; Π-reduct; Πinj≡
        ; ΣRed; mkΣRed; Σ-reduct; Σinj≡; red→≅ᵀ; IMu-reduct; IMuRed; mkIMuRed; IMuinj≡
        ; Desc-reduct )

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

spine? stablecd? stableA? pathstk? nopw? deadmot? apstk? idstk? natstk? : RTm Γ → 𝔹
-- ★★ LEVITATION: the telescope key (`dpay`/`dih` fire on a `dι`/`dσ`/`dρ`
--   telescope and nothing else) and the tag key (`fcase` fires on
--   `fzero`/`fsuc`).  Both are `natstk?`'s shape, constructors moved.
dstk? finstk? : RTm Γ → 𝔹
-- ★ INDUCTIVE TYPES: `Mu`'s stuckness key, the exact analogue of
--   `natstk?`.  `elim` fires only on a `con` scrutinee, so it is stuck
--   forever exactly when the scrutinee can never become one.
mustk? : RTm Γ → 𝔹
ordstk? : RTm Γ → RTm Γ → RTm Γ → 𝔹
ordS? : 𝔹 → RTm Γ → 𝔹
trstk? : RTm (Γ ∙) → RTm Γ → 𝔹
trlam? : RTm (Γ ∙) → 𝔹

spine? (var x)        = true
spine? (app t u)      = spine? t
spine? (absurd c e)        = true
spine? (ordtr a t u p q)        = ordstk? a t u
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
-- ★ WF stage A: `natrec` is an eliminator — a spine head exactly when
-- its SCRUTINEE can never become a numeral.
spine? (natrec z s n) = natstk? n
-- ★ INDUCTIVE TYPES: `con` is CANONICAL, so it is not a spine head (it
--   falls where `nzero`/`nsuc` fall); a stuck `elim` IS one, exactly as
--   a stuck `natrec` is.  ⚠ Leaving these to the catch-all would answer
--   `false` for `elim` and silently misclassify `app (elim …) u`.
-- ⚠⚠ EXPLICIT, NOT INHERITED.  The catch-all below answers `false`, which
--   is RIGHT for `icon` (matching `con`) and WRONG for `ielim`: an `ielim`
--   with a stuck scrutinee IS a spine, exactly as `elim` is.  check-formers
--   check 3 lists this default; its warning — "CONFIRM each default rather
--   than inherit it" — is the whole reason this was caught.
spine? (ielim D i e t)  = mustk? t
spine? (dpay I D C i)   = dstk? C
spine? (dih D e C p)    = dstk? C
spine? (fcase t a b)    = finstk? t
spine? (fcase0 t)       = true
spine? (psplit b q)     = spine? q
spine? _              = false

-- W2b: `stablecd?` is now DEAD-CODE-ness — the code can never fire a
-- J rule (⌜base⌝/⌜Σ⌝/stk-⌜Hom⌝ excluded, as before) NOR the pointwise
-- unfold (⌜Π⌝ and pw-⌜Hom⌝ excluded, NEW).
-- ★★ SpikeNatJ: the ⌜Hom⌝-WRAPPED deadness.  `stablecd? (⌜Hom⌝ c a b)`
-- asks whether the WRAPPER fires, and the wrapper's J key is `stkA? c`
-- (see `tr-J-Hom`) — so ⌜Nat⌝ under a ⌜Hom⌝ is ALIVE even though a bare
-- ⌜Nat⌝ is dead.  Everything else delegates.
stableA? ⌜Nat⌝          = false
stableA? (⌜Hom⌝ c a b)  = stableA? c
stableA? t              = stablecd? t

stablecd? (var x)       = true
stablecd? (lam t)       = true
stablecd? (app t u)     = spine? t
stablecd? (pair a b)    = true
stablecd? (absurd c e)       = true
stablecd? (ordtr a t u p q)       = ordstk? a t u
stablecd? (fst t)       = spine? t
stablecd? (snd t)       = spine? t
stablecd? (⌜Hom⌝ c a b) = stableA? c
stablecd? (hrefl c t)   = true
stablecd? (ap c b p)    = apstk? p
stablecd? (idrefl c t)  = true
stablecd? (jsub d p e)  = idstk? p
stablecd? (tr d p e)    = trstk? d p
stablecd? unit           = true
stablecd? nzero          = true
stablecd? (nsuc n)       = true
stablecd? (natrec z s n) = natstk? n
-- ★ INDUCTIVE TYPES: ⚠ these two are NOT the catch-all.  `sne→stablecd`
--   obliges every NEUTRAL to be a stable code, and a stuck `elim` is a
--   neutral — so it must answer `mustk?`, exactly as a stuck `natrec`
--   answers `natstk?`.  Inheriting `false` here makes that lemma
--   UNPROVABLE (and `stableA?` inherits this row through its own
--   catch-all `stableA? t = stablecd? t`).
-- ⚠⚠ BOTH EXPLICIT.  The catch-all answers `false`, which contradicts
--   `con`'s `true` AND `elim`'s `mustk? t`.  Two silently wrong defaults.
-- ★★ WF stage C: ⌜Nat⌝ is DEAD.  Since the retraction of `tr-J-Nat`
-- (`stkC? ⌜Nat⌝ = false`) NO rule fires on a `hrefl ⌜Nat⌝ s` path —
-- not J, not `ap-J`, not `tr-pw`/`tr-taut` (those need a lam path) —
-- so the eliminators over it are stuck forever.  ⌜Unit⌝ is NOT dead:
-- it is `stkC?`, so J and `ap-J` do fire (`stk⊥dead ⌜Unit⌝` needs
-- exactly `false` there, which the catch-all supplies).
-- This row is what lets `codeNorm` stay TWO-way: ⌜Nat⌝ — neither `pw?`
-- nor `stkC?`, the third code kind — is a DEAD code, so it lands in
-- `cf-dead` rather than needing a third `CodeFate` arm.
stablecd? ⌜Nat⌝         = true
stablecd? (con p)          = true
stablecd? (ielim D i e t)  = mustk? t
stablecd? (dι j)           = true
stablecd? (dσ S f)         = true
stablecd? (dρ j C)         = true
stablecd? (dpay I D C i)   = dstk? C
stablecd? (dih D e C p)    = dstk? C
stablecd? fzero            = true
stablecd? (fsuc t)         = true
stablecd? (fcase t a b)    = finstk? t
stablecd? (fcase0 t)       = true
stablecd? (psplit b q)     = spine? q
stablecd? _             = false

-- ★ INDUCTIVE TYPES: `elim` fires on a `con` scrutinee and nothing
--   else, so every OTHER head is junk-dead and the eliminators recurse
--   into their own keys — `natstk?`'s shape, one constructor moved.
mustk? (var x)        = true
mustk? (lam t)        = true
mustk? (app t u)      = spine? t
mustk? (pair a b)     = true
mustk? (absurd c e)   = true
mustk? (ordtr a t u p q) = ordstk? a t u
mustk? (fst t)        = spine? t
mustk? (snd t)        = spine? t
mustk? ⌜base⌝         = true
mustk? ⌜Nat⌝          = true
mustk? ⌜Unit⌝         = true
mustk? (⌜Π⌝ c d)      = true
mustk? (⌜Σ⌝ c d)      = true
mustk? (⌜Hom⌝ c a b)  = true
mustk? (⌜Id⌝ c a b)   = true
mustk? (hrefl c t)    = true
mustk? (idrefl c t)   = true
mustk? (tr d p e)     = trstk? d p
mustk? (ap c b p)     = apstk? p
mustk? (jsub d p e)   = idstk? p
mustk? unit           = true
mustk? nzero          = true
mustk? (nsuc n)       = true
mustk? (natrec z s n) = natstk? n
mustk? (⌜IMu⌝ I D i)    = true
mustk? (⌜Fin⌝ n)        = true
mustk? (con p)          = false
mustk? (ielim D i e t)  = mustk? t
mustk? (dι j)           = true
mustk? (dσ S f)         = true
mustk? (dρ j C)         = true
mustk? (dpay I D C i)   = dstk? C
mustk? (dih D e C p)    = dstk? C
mustk? fzero            = true
mustk? (fsuc t)         = true
mustk? (fcase t a b)    = finstk? t
mustk? (fcase0 t)       = true
mustk? (psplit b q)     = spine? q

pathstk? (var x)        = true
pathstk? (lam t)        = false
pathstk? (app t u)      = spine? t
pathstk? (pair a b)     = true
pathstk? (absurd c e)        = true
pathstk? (ordtr a t u p q)        = ordstk? a t u
pathstk? (fst t)        = spine? t
pathstk? (snd t)        = spine? t
pathstk? ⌜base⌝         = true
pathstk? ⌜Nat⌝ = true
pathstk? ⌜Unit⌝ = true
pathstk? (⌜Π⌝ c d)      = true
pathstk? (⌜Σ⌝ c d)      = true
pathstk? (⌜Hom⌝ c a b)  = true
pathstk? (hrefl c t)    = stablecd? c
pathstk? (tr d p e)     = trstk? d p
pathstk? (ap c b p)     = apstk? p
pathstk? (⌜Id⌝ c a b)   = true
pathstk? (idrefl c t)   = true
pathstk? (jsub d p e)   = idstk? p
pathstk? unit           = true
pathstk? nzero          = true
pathstk? (nsuc n)       = true
pathstk? (natrec z s n) = natstk? n
pathstk? (⌜IMu⌝ I D i)    = true
pathstk? (⌜Fin⌝ n)        = true
pathstk? (con p)          = true
pathstk? (ielim D i e t)  = mustk? t
pathstk? (dι j)           = true
pathstk? (dσ S f)         = true
pathstk? (dρ j C)         = true
pathstk? (dpay I D C i)   = dstk? C
pathstk? (dih D e C p)    = dstk? C
pathstk? fzero            = true
pathstk? (fsuc t)         = true
pathstk? (fcase t a b)    = finstk? t
pathstk? (fcase0 t)       = true
pathstk? (psplit b q)     = spine? q

-- ★ the two-former kernel: `jsub` is stuck forever iff its PATH never
-- becomes an `idrefl`: everything except idrefl itself is junk-stuck
-- (idrefl is inert, hrefl-paths only ever unfold to lams — still
-- stuck), and the eliminators recurse.
idstk? (var x)        = true
idstk? (lam t)        = true
idstk? (app t u)      = spine? t
idstk? (pair a b)     = true
idstk? (absurd c e)        = true
idstk? (ordtr a t u p q)        = ordstk? a t u
idstk? (fst t)        = spine? t
idstk? (snd t)        = spine? t
idstk? ⌜base⌝         = true
idstk? ⌜Nat⌝ = true
idstk? ⌜Unit⌝ = true
idstk? (⌜Π⌝ c d)      = true
idstk? (⌜Σ⌝ c d)      = true
idstk? (⌜Hom⌝ c a b)  = true
idstk? (⌜Id⌝ c a b)   = true
idstk? (hrefl c t)    = true
idstk? (idrefl c t)   = false
idstk? (tr d p e)     = trstk? d p
idstk? (ap c b p)     = apstk? p
idstk? (jsub d p e)   = idstk? p
idstk? unit           = true
idstk? nzero          = true
idstk? (nsuc n)       = true
idstk? (natrec z s n) = natstk? n
idstk? (⌜IMu⌝ I D i)    = true
idstk? (⌜Fin⌝ n)        = true
idstk? (con p)          = true
idstk? (ielim D i e t)  = mustk? t
idstk? (dι j)           = true
idstk? (dσ S f)         = true
idstk? (dρ j C)         = true
idstk? (dpay I D C i)   = dstk? C
idstk? (dih D e C p)    = dstk? C
idstk? fzero            = true
idstk? (fsuc t)         = true
idstk? (fcase t a b)    = finstk? t
idstk? (fcase0 t)       = true
idstk? (psplit b q)     = spine? q

-- ★ directed `ap` (SpikeAp): `ap` is stuck forever iff its PATH never
-- becomes a canonical hrefl the J rule fires on: lam paths have NO ap
-- rule (permanently stuck), hrefl paths are stuck iff their code is
-- DEAD (`stablecd?` — never `stkC?`-true, never pw-able).
apstk? (var x)        = true
apstk? (lam t)        = true
apstk? (app t u)      = spine? t
apstk? (pair a b)     = true
apstk? (absurd c e)        = true
apstk? (ordtr a t u p q)        = ordstk? a t u
apstk? (fst t)        = spine? t
apstk? (snd t)        = spine? t
apstk? ⌜base⌝         = true
apstk? ⌜Nat⌝ = true
apstk? ⌜Unit⌝ = true
apstk? (⌜Π⌝ c d)      = true
apstk? (⌜Σ⌝ c d)      = true
apstk? (⌜Hom⌝ c a b)  = true
apstk? (hrefl c t)    = stablecd? c
apstk? (tr d p e)     = trstk? d p
apstk? (ap c b p)     = apstk? p
apstk? (⌜Id⌝ c a b)   = true
apstk? (idrefl c t)   = true
apstk? (jsub d p e)   = idstk? p
apstk? unit           = true
apstk? nzero          = true
apstk? (nsuc n)       = true
apstk? (natrec z s n) = natstk? n
apstk? (⌜IMu⌝ I D i)    = true
apstk? (⌜Fin⌝ n)        = true
apstk? (con p)          = true
apstk? (ielim D i e t)  = mustk? t
apstk? (dι j)           = true
apstk? (dσ S f)         = true
apstk? (dρ j C)         = true
apstk? (dpay I D C i)   = dstk? C
apstk? (dih D e C p)    = dstk? C
apstk? fzero            = true
apstk? (fsuc t)         = true
apstk? (fcase t a b)    = finstk? t
apstk? (fcase0 t)       = true
apstk? (psplit b q)     = spine? q

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
deadmot? (absurd c e)        = true
deadmot? (ordtr a t u p q)        = ordstk? a t u
deadmot? (fst t)        = spine? t
deadmot? (snd t)        = spine? t
deadmot? ⌜base⌝         = true
deadmot? ⌜Nat⌝ = true
deadmot? ⌜Unit⌝ = true
deadmot? (⌜Π⌝ c d)      = false
deadmot? (⌜Σ⌝ c d)      = true
deadmot? (⌜Hom⌝ c a b)  = deadmot? c
deadmot? (hrefl c t)    = deadmot? c
deadmot? (tr d p e)     = trstk? d p
deadmot? (ap c b p)     = apstk? p
deadmot? (⌜Id⌝ c a b)   = true
deadmot? (idrefl c t)   = true
deadmot? (jsub d p e)   = idstk? p
deadmot? unit           = true
deadmot? nzero          = true
deadmot? (nsuc n)       = true
deadmot? (natrec z s n) = natstk? n
deadmot? (⌜IMu⌝ I D i)    = true
deadmot? (⌜Fin⌝ n)        = true
deadmot? (con p)          = true
deadmot? (ielim D i e t)  = mustk? t
deadmot? (dι j)           = true
deadmot? (dσ S f)         = true
deadmot? (dρ j C)         = true
deadmot? (dpay I D C i)   = dstk? C
deadmot? (dih D e C p)    = dstk? C
deadmot? fzero            = true
deadmot? (fsuc t)         = true
deadmot? (fcase t a b)    = finstk? t
deadmot? (fcase0 t)       = true
deadmot? (psplit b q)     = spine? q

nopw? (var x)        = true
nopw? (lam t)        = true
nopw? (app t u)      = spine? t
nopw? (pair a b)     = true
nopw? (absurd c e)        = true
nopw? (ordtr a t u p q)        = ordstk? a t u
nopw? (fst t)        = spine? t
nopw? (snd t)        = spine? t
nopw? ⌜base⌝         = true
nopw? ⌜Nat⌝ = true
nopw? ⌜Unit⌝ = true
nopw? (⌜Π⌝ c d)      = false
nopw? (⌜Σ⌝ c d)      = true
nopw? (⌜Hom⌝ c a b)  = nopw? c
nopw? (hrefl c t)    = true
nopw? (tr d p e)     = trstk? d p
nopw? (ap c b p)     = true
nopw? (⌜Id⌝ c a b)   = true
nopw? (idrefl c t)   = true
nopw? (jsub d p e)   = idstk? p
nopw? unit           = true
nopw? nzero          = true
nopw? (nsuc n)       = true
nopw? (natrec z s n) = natstk? n
nopw? (⌜IMu⌝ I D i)    = true
nopw? (⌜Fin⌝ n)        = true
nopw? (con p)          = true
nopw? (ielim D i e t)  = mustk? t
nopw? (dι j)           = true
nopw? (dσ S f)         = true
nopw? (dρ j C)         = true
nopw? (dpay I D C i)   = dstk? C
nopw? (dih D e C p)    = dstk? C
nopw? fzero            = true
nopw? (fsuc t)         = true
nopw? (fcase t a b)    = finstk? t
nopw? (fcase0 t)       = true
nopw? (psplit b q)     = spine? q

-- ★ WF stage A: `natrec` fires only on a NUMERAL scrutinee, so it is
-- stuck forever exactly when the scrutinee can never become one —
-- every constructor head but `nzero`/`nsuc` is junk-dead, and the
-- eliminators recurse into their own stuckness keys.
natstk? (var x)        = true
natstk? (lam t)        = true
natstk? (app t u)      = spine? t
natstk? (pair a b)     = true
natstk? (absurd c e)        = true
natstk? (ordtr a t u p q)        = ordstk? a t u
natstk? (fst t)        = spine? t
natstk? (snd t)        = spine? t
natstk? ⌜base⌝         = true
natstk? ⌜Nat⌝ = true
natstk? ⌜Unit⌝ = true
natstk? (⌜Π⌝ c d)      = true
natstk? (⌜Σ⌝ c d)      = true
natstk? (⌜Hom⌝ c a b)  = true
natstk? (⌜Id⌝ c a b)   = true
natstk? (hrefl c t)    = true
natstk? (idrefl c t)   = true
natstk? (tr d p e)     = trstk? d p
natstk? (ap c b p)     = apstk? p
natstk? (jsub d p e)   = idstk? p
natstk? unit           = true
natstk? nzero          = false
natstk? (nsuc n)       = false
natstk? (natrec z s n) = natstk? n
natstk? (⌜IMu⌝ I D i)    = true
natstk? (⌜Fin⌝ n)        = true
natstk? (con p)          = true
natstk? (ielim D i e t)  = mustk? t
natstk? (dι j)           = true
natstk? (dσ S f)         = true
natstk? (dρ j C)         = true
natstk? (dpay I D C i)   = dstk? C
natstk? (dih D e C p)    = dstk? C
natstk? fzero            = true
natstk? (fsuc t)         = true
natstk? (fcase t a b)    = finstk? t
natstk? (fcase0 t)       = true
natstk? (psplit b q)     = spine? q

dstk? (var x)          = true
dstk? (lam t)          = true
dstk? (app t u)        = spine? t
dstk? (pair a b)       = true
dstk? (absurd c e)     = true
dstk? (ordtr a t u p q) = ordstk? a t u
dstk? (fst t)          = spine? t
dstk? (snd t)          = spine? t
dstk? ⌜base⌝           = true
dstk? ⌜Nat⌝            = true
dstk? ⌜Unit⌝           = true
dstk? (⌜Π⌝ c d)        = true
dstk? (⌜Σ⌝ c d)        = true
dstk? (⌜Hom⌝ c a b)    = true
dstk? (⌜Id⌝ c a b)     = true
dstk? (hrefl c t)      = true
dstk? (idrefl c t)     = true
dstk? (tr d p e)       = trstk? d p
dstk? (ap c b p)       = apstk? p
dstk? (jsub d p e)     = idstk? p
dstk? unit             = true
dstk? nzero            = true
dstk? (nsuc n)         = true
dstk? (natrec z s n)   = natstk? n
dstk? (⌜IMu⌝ I D i)    = true
dstk? (⌜Fin⌝ n)        = true
dstk? (con p)          = true
dstk? (ielim D i e t)  = mustk? t
dstk? (dι j)           = false
dstk? (dσ S f)         = false
dstk? (dρ j C)         = false
dstk? (dpay I D C i)   = dstk? C
dstk? (dih D e C p)    = dstk? C
dstk? fzero            = true
dstk? (fsuc t)         = true
dstk? (fcase t a b)    = finstk? t
dstk? (fcase0 t)       = true
dstk? (psplit b q)     = spine? q

finstk? (var x)          = true
finstk? (lam t)          = true
finstk? (app t u)        = spine? t
finstk? (pair a b)       = true
finstk? (absurd c e)     = true
finstk? (ordtr a t u p q) = ordstk? a t u
finstk? (fst t)          = spine? t
finstk? (snd t)          = spine? t
finstk? ⌜base⌝           = true
finstk? ⌜Nat⌝            = true
finstk? ⌜Unit⌝           = true
finstk? (⌜Π⌝ c d)        = true
finstk? (⌜Σ⌝ c d)        = true
finstk? (⌜Hom⌝ c a b)    = true
finstk? (⌜Id⌝ c a b)     = true
finstk? (hrefl c t)      = true
finstk? (idrefl c t)     = true
finstk? (tr d p e)       = trstk? d p
finstk? (ap c b p)       = apstk? p
finstk? (jsub d p e)     = idstk? p
finstk? unit             = true
finstk? nzero            = true
finstk? (nsuc n)         = true
finstk? (natrec z s n)   = natstk? n
finstk? (⌜IMu⌝ I D i)    = true
finstk? (⌜Fin⌝ n)        = true
finstk? (con p)          = true
finstk? (ielim D i e t)  = mustk? t
finstk? (dι j)           = true
finstk? (dσ S f)         = true
finstk? (dρ j C)         = true
finstk? (dpay I D C i)   = dstk? C
finstk? (dih D e C p)    = dstk? C
finstk? fzero            = false
finstk? (fsuc t)         = false
finstk? (fcase t a b)    = finstk? t
finstk? (fcase0 t)       = true
finstk? (psplit b q)     = spine? q

-- ★ THE ORDER'S STUCKNESS, and it must mirror `_⁺`'s dispatch EXACTLY:
-- `a`, then `u`, then `t`.  `ordtr` is NOT like `absurd` — `absurd` has
-- no root rule and is unconditionally neutral, whereas `ordtr` fires as
-- soon as its bounds are numerals, so a blanket `true` here would make
-- `spine?-red (ordtr-z …)` demand `false ≡ true`.
--
-- Every one of the five root rules is then refuted DEFINITIONALLY: each
-- fires only on numeral bounds, and `natstk?` of a numeral is `false`.
ordstk? nzero t u    = false
ordstk? (nsuc a) t u = ordS? (natstk? t) u
ordstk? a t u        = natstk? a

-- ★ under a `nsuc` bound the order fires exactly when BOTH remaining
-- bounds are literal, i.e. when neither is `natstk?` — so this is just a
-- disjunction, keyed on `natstk? t` to keep it inside the mutual block
-- without pulling `_∨_` into scope.
--
-- ⚠ keeping the dispatch OUT of `ordstk?`'s `nsuc` clause is what makes
-- `ordstk?-redᵃ`'s `ξ-nsuc` row just `h`: `ordstk? (nsuc a) t u` and
-- `ordstk? (nsuc a') t u` are then SYNTACTICALLY the same term.
ordS? true  u = true
ordS? false u = natstk? u

f≢t : false ≡ true → ⊥
f≢t ()

-- ★ `ordS?` is monotone in both slots, and BOTH proofs are pure Boolean
-- algebra — no term induction.  This is the whole reason the order's
-- `-red` lemmas stay short: the only genuine term recursion left is
-- `natstk?-red`, which already exists.
ordS?-monoᵇ : (b b' : 𝔹) → (b ≡ true → b' ≡ true) → (u : RTm Γ) →
              ordS? b u ≡ true → ordS? b' u ≡ true
ordS?-monoᵇ true  true  f u h = refl
ordS?-monoᵇ true  false f u h with f refl
... | ()
ordS?-monoᵇ false true  f u h = refl
ordS?-monoᵇ false false f u h = h

ordS?-monoᵘ : (b : 𝔹) {u u' : RTm Γ} → (natstk? u ≡ true → natstk? u' ≡ true) →
              ordS? b u ≡ true → ordS? b u' ≡ true
ordS?-monoᵘ true  f h = refl
ordS?-monoᵘ false f h = f h

-- each classifier is closed under reduction (`true` is preserved; the
-- root rules that would break a shape are refuted definitionally or
-- through the W2b key-disjointness lemmas below).

-- key disjointness (W2b): a pw-able code is never dead, never
-- pw-immune; a stable (J-able) code is never dead; and a head-redex is
-- never a pw code — the facts the keyed dispatches turn on.
-- ★ the `stableA?` peer, for the ⌜Hom⌝-wrapped verdict.
pw⊥deadA : (C : RTm Γ) → pw? C ≡ true → stableA? C ≡ false
pw⊥deadA (var x) ()
pw⊥deadA (lam t) ()
pw⊥deadA (app t u) ()
pw⊥deadA (pair a b) ()
pw⊥deadA (fst t) ()
pw⊥deadA (snd t) ()
pw⊥deadA ⌜base⌝ ()
pw⊥deadA (⌜Π⌝ c d) h = refl
pw⊥deadA (⌜Σ⌝ c d) ()
pw⊥deadA (⌜Hom⌝ C a b) h = pw⊥deadA C h
pw⊥deadA (hrefl c t) ()
pw⊥deadA (tr d p e) ()

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
pw⊥dead (⌜Hom⌝ C a b) h = pw⊥deadA C h
pw⊥dead (hrefl c t) ()
pw⊥dead (tr d p e) ()

nopw⊥pw : (C : RTm Γ) → nopw? C ≡ true → pw? C ≡ false
nopw⊥pw (var x) h = refl
nopw⊥pw (lam t) h = refl
nopw⊥pw (app t u) h = refl
nopw⊥pw (pair a b) h = refl
nopw⊥pw (absurd c e) h = refl
nopw⊥pw (ordtr a t u p q) h = refl
nopw⊥pw (fst t) h = refl
nopw⊥pw (snd t) h = refl
nopw⊥pw ⌜base⌝ h = refl
nopw⊥pw ⌜Nat⌝ h = refl
nopw⊥pw ⌜Unit⌝ h = refl
nopw⊥pw (⌜Π⌝ c d) ()
nopw⊥pw (⌜Σ⌝ c d) h = refl
nopw⊥pw (⌜Hom⌝ C a b) h = nopw⊥pw C h
nopw⊥pw (hrefl c t) h = refl
nopw⊥pw (tr d p e) h = refl
nopw⊥pw (ap c b p) h = refl
nopw⊥pw (⌜Id⌝ c a b) h = refl
nopw⊥pw (idrefl c t) h = refl
nopw⊥pw (jsub d p e) h = refl
nopw⊥pw unit h = refl
nopw⊥pw nzero h = refl
nopw⊥pw (nsuc n) h = refl
nopw⊥pw (natrec z s n) h = refl
nopw⊥pw (⌜IMu⌝ I D i) h = refl
nopw⊥pw (⌜Fin⌝ n) h = refl
nopw⊥pw (con p) h = refl
nopw⊥pw (ielim D i e t) h = refl
nopw⊥pw (dι j) h = refl
nopw⊥pw (dσ S f) h = refl
nopw⊥pw (dρ j C) h = refl
nopw⊥pw (dpay I D C i) h = refl
nopw⊥pw (dih D e C p) h = refl
nopw⊥pw fzero h = refl
nopw⊥pw (fsuc t) h = refl
nopw⊥pw (fcase t a b) h = refl
nopw⊥pw (fcase0 t) h = refl
nopw⊥pw (psplit b q) h = refl

deadmot→nopw : (C : RTm Γ) → deadmot? C ≡ true → nopw? C ≡ true
deadmot→nopw (var x) h = refl
deadmot→nopw (lam t) h = refl
deadmot→nopw (app t u) h = h
deadmot→nopw (pair a b) h = refl
deadmot→nopw (absurd c e) h = refl
deadmot→nopw (ordtr a t u p q) h = h
deadmot→nopw (fst t) h = h
deadmot→nopw (snd t) h = h
deadmot→nopw ⌜base⌝ h = refl
deadmot→nopw ⌜Nat⌝ h = refl
deadmot→nopw ⌜Unit⌝ h = refl
deadmot→nopw (⌜Π⌝ c d) ()
deadmot→nopw (⌜Σ⌝ c d) h = refl
deadmot→nopw (⌜Hom⌝ C a b) h = deadmot→nopw C h
deadmot→nopw (hrefl c t) h = refl
deadmot→nopw (tr d p e) h = h
deadmot→nopw (ap c b p) h = refl
deadmot→nopw (⌜Id⌝ c a b) h = refl
deadmot→nopw (idrefl c t) h = refl
deadmot→nopw (jsub d p e) h = h
deadmot→nopw unit h = refl
deadmot→nopw nzero h = refl
deadmot→nopw (nsuc n) h = refl
deadmot→nopw (natrec z s n) h = h
deadmot→nopw (⌜IMu⌝ I D i) h = refl
deadmot→nopw (⌜Fin⌝ n) h = refl
deadmot→nopw (con p) h = refl
deadmot→nopw (ielim D i e t) h = h
deadmot→nopw (dι j) h = refl
deadmot→nopw (dσ S f) h = refl
deadmot→nopw (dρ j C) h = refl
deadmot→nopw (dpay I D C i) h = h
deadmot→nopw (dih D e C p) h = h
deadmot→nopw fzero h = refl
deadmot→nopw (fsuc t) h = refl
deadmot→nopw (fcase t a b) h = h
deadmot→nopw (fcase0 t) h = refl
deadmot→nopw (psplit b q) h = h

-- ★ the `stkA?` peer.  ⌜Nat⌝ IS a dead motive (nothing fires on
-- `tr ⌜Nat⌝ p e`) even though it is a live PATH code, so this goes
-- through where `stkA?→hd` cannot.
stkA?→deadmot : (C : RTm Γ) → stkA? C ≡ true → deadmot? C ≡ true
stkA?→deadmot (var x) ()
stkA?→deadmot (lam t) ()
stkA?→deadmot (app t u) ()
stkA?→deadmot (pair a b) ()
stkA?→deadmot (fst t) ()
stkA?→deadmot (snd t) ()
stkA?→deadmot ⌜base⌝ h = refl
stkA?→deadmot ⌜Nat⌝ h = refl
stkA?→deadmot ⌜Unit⌝ h = refl
stkA?→deadmot (⌜Π⌝ c d) ()
stkA?→deadmot (⌜Σ⌝ c d) h = refl
stkA?→deadmot (⌜Id⌝ c a b) h = refl
stkA?→deadmot (⌜Hom⌝ C a b) h = stkA?→deadmot C h
stkA?→deadmot (hrefl c t) ()
stkA?→deadmot (tr d p e) ()
stkA?→deadmot (⌜IMu⌝ I D i) h = refl
stkA?→deadmot (⌜Fin⌝ n) h = refl

stk→deadmot : (C : RTm Γ) → stkC? C ≡ true → deadmot? C ≡ true
stk→deadmot (var x) ()
stk→deadmot (lam t) ()
stk→deadmot (app t u) ()
stk→deadmot (pair a b) ()
stk→deadmot (fst t) ()
stk→deadmot (snd t) ()
stk→deadmot ⌜base⌝ h = refl
stk→deadmot ⌜Unit⌝ h = refl
stk→deadmot (⌜Π⌝ c d) ()
stk→deadmot (⌜Σ⌝ c d) h = refl
stk→deadmot (⌜Id⌝ c a b) h = refl
stk→deadmot (⌜Hom⌝ C a b) h = stkA?→deadmot C h
stk→deadmot (hrefl c t) ()
stk→deadmot (tr d p e) ()
stk→deadmot (⌜IMu⌝ I D i) h = refl
stk→deadmot (⌜Fin⌝ n) h = refl

-- ★ the `stkA?` peer: a stable-ambient code is never a dead WRAPPER
-- code.  ⌜Nat⌝ is the interesting row — `stableA? ⌜Nat⌝ = false` is
-- exactly the fact that `⌜Hom⌝ ⌜Nat⌝ a b` fires J.
stkA?⊥dead : (C : RTm Γ) → stkA? C ≡ true → stableA? C ≡ false
stkA?⊥dead (var x) ()
stkA?⊥dead (lam t) ()
stkA?⊥dead (app t u) ()
stkA?⊥dead (pair a b) ()
stkA?⊥dead (fst t) ()
stkA?⊥dead (snd t) ()
stkA?⊥dead ⌜base⌝ h = refl
stkA?⊥dead ⌜Nat⌝ h = refl
stkA?⊥dead ⌜Unit⌝ h = refl
stkA?⊥dead (⌜Π⌝ c d) ()
stkA?⊥dead (⌜Σ⌝ c d) h = refl
stkA?⊥dead (⌜Id⌝ c a b) h = refl
stkA?⊥dead (⌜Hom⌝ C a b) h = stkA?⊥dead C h
stkA?⊥dead (hrefl c t) ()
stkA?⊥dead (tr d p e) ()
stkA?⊥dead (⌜IMu⌝ I D i) h = refl
stkA?⊥dead (⌜Fin⌝ n) h = refl

stk⊥dead : (C : RTm Γ) → stkC? C ≡ true → stablecd? C ≡ false
stk⊥dead (var x) ()
stk⊥dead (lam t) ()
stk⊥dead (app t u) ()
stk⊥dead (pair a b) ()
stk⊥dead (fst t) ()
stk⊥dead (snd t) ()
stk⊥dead ⌜base⌝ h = refl
stk⊥dead ⌜Unit⌝ h = refl
stk⊥dead (⌜Π⌝ c d) ()
stk⊥dead (⌜Σ⌝ c d) h = refl
stk⊥dead (⌜Id⌝ c a b) h = refl
stk⊥dead (⌜Hom⌝ C a b) h = stkA?⊥dead C h
stk⊥dead (hrefl c t) ()
stk⊥dead (tr d p e) ()
stk⊥dead (⌜IMu⌝ I D i) h = refl
stk⊥dead (⌜Fin⌝ n) h = refl

-- a head-reducible term is never a pw code (SNRed's subjects are
-- app/fst/snd/hrefl/tr-headed, never ⌜Π⌝/⌜Hom⌝-constructor-headed) —
-- proven after SNRed below (snr-nonpw).

homheaded?-red : {t t' : RTm Γ} → t ⟶ t' →
                 homheaded? t ≡ true → homheaded? t' ≡ true
spine?-red    : {t t' : RTm Γ} → t ⟶ t' → spine? t ≡ true → spine? t' ≡ true
-- the order's three, one per bound it can get stuck on.  `ᵖ`/`q` need
-- none: `ordstk?` does not mention the proofs.
ordstk?-redᵃ  : {a a' t u : RTm Γ} → a ⟶ a' →
                ordstk? a t u ≡ true → ordstk? a' t u ≡ true
ordstk?-redᵗ  : {a t t' u : RTm Γ} → t ⟶ t' →
                ordstk? a t u ≡ true → ordstk? a t' u ≡ true
ordstk?-redᵘ  : {a t u u' : RTm Γ} → u ⟶ u' →
                ordstk? a t u ≡ true → ordstk? a t u' ≡ true
stableA?-red  : {t t' : RTm Γ} → t ⟶ t' →
                stableA? t ≡ true → stableA? t' ≡ true
stablecd?-red : {t t' : RTm Γ} → t ⟶ t' →
                stablecd? t ≡ true → stablecd? t' ≡ true
pathstk?-red  : {t t' : RTm Γ} → t ⟶ t' →
                pathstk? t ≡ true → pathstk? t' ≡ true
nopw?-red     : {t t' : RTm Γ} → t ⟶ t' → nopw? t ≡ true → nopw? t' ≡ true
apstk?-red    : {t t' : RTm Γ} → t ⟶ t' → apstk? t ≡ true → apstk? t' ≡ true
idstk?-red    : {t t' : RTm Γ} → t ⟶ t' → idstk? t ≡ true → idstk? t' ≡ true
natstk?-red   : {t t' : RTm Γ} → t ⟶ t' → natstk? t ≡ true → natstk? t' ≡ true
mustk?-red    : {t t' : RTm Γ} → t ⟶ t' → mustk? t ≡ true → mustk? t' ≡ true
dstk?-red     : {t t' : RTm Γ} → t ⟶ t' → dstk? t ≡ true → dstk? t' ≡ true
finstk?-red   : {t t' : RTm Γ} → t ⟶ t' → finstk? t ≡ true → finstk? t' ≡ true
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
spine?-red (ξ-absurdᶜ _) h = refl
spine?-red (ξ-absurdᵉ _) h = refl
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
spine?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
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
spine?-red (natrec-zero _ _) ()
spine?-red (natrec-suc _ _ _) ()
spine?-red (ξ-nsuc r) ()
spine?-red (ξ-natrecᶻ r) h = h
spine?-red (ξ-natrecˢ r) h = h
spine?-red (ξ-natrecⁿ r) h = natstk?-red r h
-- ★ INDUCTIVE TYPES: a stuck `elim` is a spine head, so this mirrors
--   `natrec`'s rows exactly — and ι UNSTICKS it, hence the absurdity.
spine?-red (ξ-ielimᵗ r) h = mustk?-red r h
spine?-red (ξ-ielimⁱ r) h = h
spine?-red (ordtr-z _ _ _ _) ()
spine?-red (ordtr-szz _ _ _) ()
spine?-red (ordtr-ssz _ _ _ _) ()
spine?-red (ordtr-szs _ _ _ _) ()
spine?-red (ordtr-sss _ _ _ _ _) ()
spine?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
spine?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
spine?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
spine?-red (ξ-ordtrᵖ r) h = h
spine?-red (ξ-ordtrq r) h = h
spine?-red (ι _ _ _ _) ()
spine?-red (dpay-ι _ _ _ _) ()
spine?-red (dpay-σ _ _ _ _ _) ()
spine?-red (dpay-ρ _ _ _ _ _) ()
spine?-red (dih-ι _ _ _ _) ()
spine?-red (dih-σ _ _ _ _ _) ()
spine?-red (dih-ρ _ _ _ _ _) ()
spine?-red (fcase-z _ _) ()
spine?-red (fcase-s _ _ _) ()
spine?-red (psplit-β _ _ _) ()
spine?-red (ξ-⌜IMu⌝ᴵ _) ()
spine?-red (ξ-⌜IMu⌝ᴰ _) ()
spine?-red (ξ-⌜IMu⌝ⁱ _) ()
spine?-red (ξ-con _) ()
spine?-red (ξ-ielimᴰ r) h = h
spine?-red (ξ-ielimᵉ r) h = h
spine?-red (ξ-dι _) ()
spine?-red (ξ-dσˢ _) ()
spine?-red (ξ-dσᶠ _) ()
spine?-red (ξ-dρʲ _) ()
spine?-red (ξ-dρᶜ _) ()
spine?-red (ξ-dpayᴵ r) h = h
spine?-red (ξ-dpayᴰ r) h = h
spine?-red (ξ-dpayᶜ r) h = dstk?-red r h
spine?-red (ξ-dpayⁱ r) h = h
spine?-red (ξ-dihᴰ r) h = h
spine?-red (ξ-dihᵉ r) h = h
spine?-red (ξ-dihᶜ r) h = dstk?-red r h
spine?-red (ξ-dihᵖ r) h = h
spine?-red (ξ-fsuc _) ()
spine?-red (ξ-fcaseᵗ r) h = finstk?-red r h
spine?-red (ξ-fcaseᵃ r) h = h
spine?-red (ξ-fcaseᵇ r) h = h
spine?-red (ξ-fcase0 r) h = h
spine?-red (ξ-psplitᵇ r) h = h
spine?-red (ξ-psplitᵍ r) h = spine?-red r h

-- ★ the `stableA?` peer of `stablecd?-red`: identical except that the
-- ⌜Hom⌝-code congruence recurses into ITSELF, so ⌜Nat⌝ under a ⌜Hom⌝
-- keeps its `false` verdict.  Every other row delegates definitionally.
stableA?-red (β _ _) ()
stableA?-red (βfst _ _) ()
stableA?-red (βsnd _ _) ()
stableA?-red (ξ-lam r) h = h
stableA?-red (ξ-appˡ r) h = spine?-red r h
stableA?-red (ξ-appʳ r) h = h
stableA?-red (ξ-pairˡ r) h = h
stableA?-red (ξ-pairʳ r) h = h
stableA?-red (ξ-absurdᶜ _) h = refl
stableA?-red (ξ-absurdᵉ _) h = refl
stableA?-red (ξ-fst r) h = spine?-red r h
stableA?-red (ξ-snd r) h = spine?-red r h
stableA?-red (ξ-⌜Π⌝ˡ _) ()
stableA?-red (ξ-⌜Π⌝ʳ _) ()
stableA?-red (ξ-⌜Σ⌝ˡ _) ()
stableA?-red (ξ-⌜Σ⌝ʳ _) ()
stableA?-red (ξ-⌜Hom⌝ᶜ r) h = stableA?-red r h
stableA?-red (ξ-⌜Hom⌝ˡ r) h = h
stableA?-red (ξ-⌜Hom⌝ʳ r) h = h
stableA?-red (ξ-hreflᶜ r) h = h
stableA?-red (ξ-hreflᵃ r) h = h
stableA?-red (hrefl-pw C₀ s₀ kp) h = refl
stableA?-red (tr-J-base _ _ _ _ _) ()
stableA?-red (tr-J-Σ _ _ _ _ _ _ _) ()
stableA?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
stableA?-red (tr-taut _ _) ()
stableA?-red (tr-pw c₁ _ _ _ kp) h = ⊥-elim (f≢t (trans (sym (nopw⊥pw c₁ (deadmot→nopw c₁ h))) kp))
stableA?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
stableA?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
stableA?-red (ξ-trᵉ r) h = h
stableA?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
stableA?-red (ξ-apᶜ r) h = h
stableA?-red (ξ-apᵇ r) h = h
stableA?-red (ξ-apᵖ r) h = apstk?-red r h
stableA?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
stableA?-red (jsub-refl _ _ _ _) ()
stableA?-red (ξ-⌜Id⌝ᶜ r) ()
stableA?-red (ξ-⌜Id⌝ˡ r) ()
stableA?-red (ξ-⌜Id⌝ʳ r) ()
stableA?-red (ξ-idreflᶜ r) h = h
stableA?-red (ξ-idreflᵃ r) h = h
stableA?-red (ξ-jsubᵈ r) h = h
stableA?-red (ξ-jsubᵖ r) h = idstk?-red r h
stableA?-red (ξ-jsubᵉ r) h = h
stableA?-red (natrec-zero _ _) ()
stableA?-red (natrec-suc _ _ _) ()
stableA?-red (ξ-nsuc r) h = refl
stableA?-red (ξ-natrecᶻ r) h = h
stableA?-red (ξ-natrecˢ r) h = h
stableA?-red (ξ-natrecⁿ r) h = natstk?-red r h
stableA?-red (ξ-con r) h = refl
stableA?-red (ξ-ielimᵗ r) h = mustk?-red r h
stableA?-red (ξ-ielimⁱ r) h = h
stableA?-red (ordtr-z _ _ _ _) ()
stableA?-red (ordtr-szz _ _ _) ()
stableA?-red (ordtr-ssz _ _ _ _) ()
stableA?-red (ordtr-szs _ _ _ _) ()
stableA?-red (ordtr-sss _ _ _ _ _) ()
stableA?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
stableA?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
stableA?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
stableA?-red (ξ-ordtrᵖ r) h = h
stableA?-red (ξ-ordtrq r) h = h
stableA?-red (ι _ _ _ _) ()
stableA?-red (dpay-ι _ _ _ _) ()
stableA?-red (dpay-σ _ _ _ _ _) ()
stableA?-red (dpay-ρ _ _ _ _ _) ()
stableA?-red (dih-ι _ _ _ _) ()
stableA?-red (dih-σ _ _ _ _ _) ()
stableA?-red (dih-ρ _ _ _ _ _) ()
stableA?-red (fcase-z _ _) ()
stableA?-red (fcase-s _ _ _) ()
stableA?-red (psplit-β _ _ _) ()
stableA?-red (ξ-⌜IMu⌝ᴵ _) ()
stableA?-red (ξ-⌜IMu⌝ᴰ _) ()
stableA?-red (ξ-⌜IMu⌝ⁱ _) ()
stableA?-red (ξ-ielimᴰ r) h = h
stableA?-red (ξ-ielimᵉ r) h = h
stableA?-red (ξ-dι r) h = h
stableA?-red (ξ-dσˢ r) h = h
stableA?-red (ξ-dσᶠ r) h = h
stableA?-red (ξ-dρʲ r) h = h
stableA?-red (ξ-dρᶜ r) h = h
stableA?-red (ξ-dpayᴵ r) h = h
stableA?-red (ξ-dpayᴰ r) h = h
stableA?-red (ξ-dpayᶜ r) h = dstk?-red r h
stableA?-red (ξ-dpayⁱ r) h = h
stableA?-red (ξ-dihᴰ r) h = h
stableA?-red (ξ-dihᵉ r) h = h
stableA?-red (ξ-dihᶜ r) h = dstk?-red r h
stableA?-red (ξ-dihᵖ r) h = h
stableA?-red (ξ-fsuc r) h = h
stableA?-red (ξ-fcaseᵗ r) h = finstk?-red r h
stableA?-red (ξ-fcaseᵃ r) h = h
stableA?-red (ξ-fcaseᵇ r) h = h
stableA?-red (ξ-fcase0 r) h = h
stableA?-red (ξ-psplitᵇ r) h = h
stableA?-red (ξ-psplitᵍ r) h = spine?-red r h

stablecd?-red (β _ _) ()
stablecd?-red (βfst _ _) ()
stablecd?-red (βsnd _ _) ()
stablecd?-red (ξ-lam r) h = h
stablecd?-red (ξ-appˡ r) h = spine?-red r h
stablecd?-red (ξ-appʳ r) h = h
stablecd?-red (ξ-pairˡ r) h = h
stablecd?-red (ξ-pairʳ r) h = h
stablecd?-red (ξ-absurdᶜ _) h = refl
stablecd?-red (ξ-absurdᵉ _) h = refl
stablecd?-red (ξ-fst r) h = spine?-red r h
stablecd?-red (ξ-snd r) h = spine?-red r h
stablecd?-red (ξ-⌜Π⌝ˡ _) ()
stablecd?-red (ξ-⌜Π⌝ʳ _) ()
stablecd?-red (ξ-⌜Σ⌝ˡ _) ()
stablecd?-red (ξ-⌜Σ⌝ʳ _) ()
stablecd?-red (ξ-⌜Hom⌝ᶜ r) h = stableA?-red r h
stablecd?-red (ξ-⌜Hom⌝ˡ r) h = h
stablecd?-red (ξ-⌜Hom⌝ʳ r) h = h
stablecd?-red (ξ-hreflᶜ r) h = h
stablecd?-red (ξ-hreflᵃ r) h = h
stablecd?-red (hrefl-pw C₀ s₀ kp) h = refl
stablecd?-red (tr-J-base _ _ _ _ _) ()
stablecd?-red (tr-J-Σ _ _ _ _ _ _ _) ()
stablecd?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
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
stablecd?-red (natrec-zero _ _) ()
stablecd?-red (natrec-suc _ _ _) ()
stablecd?-red (ξ-nsuc r) h = refl
stablecd?-red (ξ-natrecᶻ r) h = h
stablecd?-red (ξ-natrecˢ r) h = h
stablecd?-red (ξ-natrecⁿ r) h = natstk?-red r h
stablecd?-red (ξ-con r) h = refl
stablecd?-red (ξ-ielimᵗ r) h = mustk?-red r h
stablecd?-red (ξ-ielimⁱ r) h = h
stablecd?-red (ordtr-z _ _ _ _) ()
stablecd?-red (ordtr-szz _ _ _) ()
stablecd?-red (ordtr-ssz _ _ _ _) ()
stablecd?-red (ordtr-szs _ _ _ _) ()
stablecd?-red (ordtr-sss _ _ _ _ _) ()
stablecd?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
stablecd?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
stablecd?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
stablecd?-red (ξ-ordtrᵖ r) h = h
stablecd?-red (ξ-ordtrq r) h = h
stablecd?-red (ι _ _ _ _) ()
stablecd?-red (dpay-ι _ _ _ _) ()
stablecd?-red (dpay-σ _ _ _ _ _) ()
stablecd?-red (dpay-ρ _ _ _ _ _) ()
stablecd?-red (dih-ι _ _ _ _) ()
stablecd?-red (dih-σ _ _ _ _ _) ()
stablecd?-red (dih-ρ _ _ _ _ _) ()
stablecd?-red (fcase-z _ _) ()
stablecd?-red (fcase-s _ _ _) ()
stablecd?-red (psplit-β _ _ _) ()
stablecd?-red (ξ-⌜IMu⌝ᴵ _) ()
stablecd?-red (ξ-⌜IMu⌝ᴰ _) ()
stablecd?-red (ξ-⌜IMu⌝ⁱ _) ()
stablecd?-red (ξ-ielimᴰ r) h = h
stablecd?-red (ξ-ielimᵉ r) h = h
stablecd?-red (ξ-dι r) h = h
stablecd?-red (ξ-dσˢ r) h = h
stablecd?-red (ξ-dσᶠ r) h = h
stablecd?-red (ξ-dρʲ r) h = h
stablecd?-red (ξ-dρᶜ r) h = h
stablecd?-red (ξ-dpayᴵ r) h = h
stablecd?-red (ξ-dpayᴰ r) h = h
stablecd?-red (ξ-dpayᶜ r) h = dstk?-red r h
stablecd?-red (ξ-dpayⁱ r) h = h
stablecd?-red (ξ-dihᴰ r) h = h
stablecd?-red (ξ-dihᵉ r) h = h
stablecd?-red (ξ-dihᶜ r) h = dstk?-red r h
stablecd?-red (ξ-dihᵖ r) h = h
stablecd?-red (ξ-fsuc r) h = h
stablecd?-red (ξ-fcaseᵗ r) h = finstk?-red r h
stablecd?-red (ξ-fcaseᵃ r) h = h
stablecd?-red (ξ-fcaseᵇ r) h = h
stablecd?-red (ξ-fcase0 r) h = h
stablecd?-red (ξ-psplitᵇ r) h = h
stablecd?-red (ξ-psplitᵍ r) h = spine?-red r h

pathstk?-red (β _ _) ()
pathstk?-red (βfst _ _) ()
pathstk?-red (βsnd _ _) ()
pathstk?-red (ξ-lam _) ()
pathstk?-red (ξ-appˡ r) h = spine?-red r h
pathstk?-red (ξ-appʳ r) h = h
pathstk?-red (ξ-pairˡ r) h = h
pathstk?-red (ξ-pairʳ r) h = h
pathstk?-red (ξ-absurdᶜ _) h = refl
pathstk?-red (ξ-absurdᵉ _) h = refl
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
pathstk?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
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
pathstk?-red (natrec-zero _ _) ()
pathstk?-red (natrec-suc _ _ _) ()
pathstk?-red (ξ-nsuc r) h = refl
pathstk?-red (ξ-natrecᶻ r) h = h
pathstk?-red (ξ-natrecˢ r) h = h
pathstk?-red (ξ-natrecⁿ r) h = natstk?-red r h
pathstk?-red (ordtr-z _ _ _ _) ()
pathstk?-red (ordtr-szz _ _ _) ()
pathstk?-red (ordtr-ssz _ _ _ _) ()
pathstk?-red (ordtr-szs _ _ _ _) ()
pathstk?-red (ordtr-sss _ _ _ _ _) ()
pathstk?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
pathstk?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
pathstk?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
pathstk?-red (ξ-ordtrᵖ r) h = h
pathstk?-red (ξ-ordtrq r) h = h
pathstk?-red (ξ-con r) h = refl
pathstk?-red (ξ-ielimᵗ r) h = mustk?-red r h
pathstk?-red (ξ-ielimⁱ r) h = h
pathstk?-red (ι _ _ _ _) ()
pathstk?-red (dpay-ι _ _ _ _) ()
pathstk?-red (dpay-σ _ _ _ _ _) ()
pathstk?-red (dpay-ρ _ _ _ _ _) ()
pathstk?-red (dih-ι _ _ _ _) ()
pathstk?-red (dih-σ _ _ _ _ _) ()
pathstk?-red (dih-ρ _ _ _ _ _) ()
pathstk?-red (fcase-z _ _) ()
pathstk?-red (fcase-s _ _ _) ()
pathstk?-red (psplit-β _ _ _) ()
pathstk?-red (ξ-⌜IMu⌝ᴵ r) h = h
pathstk?-red (ξ-⌜IMu⌝ᴰ r) h = h
pathstk?-red (ξ-⌜IMu⌝ⁱ r) h = h
pathstk?-red (ξ-ielimᴰ r) h = h
pathstk?-red (ξ-ielimᵉ r) h = h
pathstk?-red (ξ-dι r) h = h
pathstk?-red (ξ-dσˢ r) h = h
pathstk?-red (ξ-dσᶠ r) h = h
pathstk?-red (ξ-dρʲ r) h = h
pathstk?-red (ξ-dρᶜ r) h = h
pathstk?-red (ξ-dpayᴵ r) h = h
pathstk?-red (ξ-dpayᴰ r) h = h
pathstk?-red (ξ-dpayᶜ r) h = dstk?-red r h
pathstk?-red (ξ-dpayⁱ r) h = h
pathstk?-red (ξ-dihᴰ r) h = h
pathstk?-red (ξ-dihᵉ r) h = h
pathstk?-red (ξ-dihᶜ r) h = dstk?-red r h
pathstk?-red (ξ-dihᵖ r) h = h
pathstk?-red (ξ-fsuc r) h = h
pathstk?-red (ξ-fcaseᵗ r) h = finstk?-red r h
pathstk?-red (ξ-fcaseᵃ r) h = h
pathstk?-red (ξ-fcaseᵇ r) h = h
pathstk?-red (ξ-fcase0 r) h = h
pathstk?-red (ξ-psplitᵇ r) h = h
pathstk?-red (ξ-psplitᵍ r) h = spine?-red r h

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
apstk?-red (ξ-absurdᶜ _) h = refl
apstk?-red (ξ-absurdᵉ _) h = refl
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
  ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
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
apstk?-red (natrec-zero _ _) ()
apstk?-red (natrec-suc _ _ _) ()
apstk?-red (ξ-nsuc r) h = refl
apstk?-red (ξ-natrecᶻ r) h = h
apstk?-red (ξ-natrecˢ r) h = h
apstk?-red (ξ-natrecⁿ r) h = natstk?-red r h
apstk?-red (ordtr-z _ _ _ _) ()
apstk?-red (ordtr-szz _ _ _) ()
apstk?-red (ordtr-ssz _ _ _ _) ()
apstk?-red (ordtr-szs _ _ _ _) ()
apstk?-red (ordtr-sss _ _ _ _ _) ()
apstk?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
apstk?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
apstk?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
apstk?-red (ξ-ordtrᵖ r) h = h
apstk?-red (ξ-ordtrq r) h = h
apstk?-red (ξ-con r) h = refl
apstk?-red (ξ-ielimᵗ r) h = mustk?-red r h
apstk?-red (ξ-ielimⁱ r) h = h
apstk?-red (ι _ _ _ _) ()
apstk?-red (dpay-ι _ _ _ _) ()
apstk?-red (dpay-σ _ _ _ _ _) ()
apstk?-red (dpay-ρ _ _ _ _ _) ()
apstk?-red (dih-ι _ _ _ _) ()
apstk?-red (dih-σ _ _ _ _ _) ()
apstk?-red (dih-ρ _ _ _ _ _) ()
apstk?-red (fcase-z _ _) ()
apstk?-red (fcase-s _ _ _) ()
apstk?-red (psplit-β _ _ _) ()
apstk?-red (ξ-⌜IMu⌝ᴵ r) h = h
apstk?-red (ξ-⌜IMu⌝ᴰ r) h = h
apstk?-red (ξ-⌜IMu⌝ⁱ r) h = h
apstk?-red (ξ-ielimᴰ r) h = h
apstk?-red (ξ-ielimᵉ r) h = h
apstk?-red (ξ-dι r) h = h
apstk?-red (ξ-dσˢ r) h = h
apstk?-red (ξ-dσᶠ r) h = h
apstk?-red (ξ-dρʲ r) h = h
apstk?-red (ξ-dρᶜ r) h = h
apstk?-red (ξ-dpayᴵ r) h = h
apstk?-red (ξ-dpayᴰ r) h = h
apstk?-red (ξ-dpayᶜ r) h = dstk?-red r h
apstk?-red (ξ-dpayⁱ r) h = h
apstk?-red (ξ-dihᴰ r) h = h
apstk?-red (ξ-dihᵉ r) h = h
apstk?-red (ξ-dihᶜ r) h = dstk?-red r h
apstk?-red (ξ-dihᵖ r) h = h
apstk?-red (ξ-fsuc r) h = h
apstk?-red (ξ-fcaseᵗ r) h = finstk?-red r h
apstk?-red (ξ-fcaseᵃ r) h = h
apstk?-red (ξ-fcaseᵇ r) h = h
apstk?-red (ξ-fcase0 r) h = h
apstk?-red (ξ-psplitᵇ r) h = h
apstk?-red (ξ-psplitᵍ r) h = spine?-red r h

-- ★ jsub-stuckness is closed under reduction (the idstk? mirror).
idstk?-red (β _ _) ()
idstk?-red (βfst _ _) ()
idstk?-red (βsnd _ _) ()
idstk?-red (ξ-lam r) h = h
idstk?-red (ξ-appˡ r) h = spine?-red r h
idstk?-red (ξ-appʳ r) h = h
idstk?-red (ξ-pairˡ r) h = h
idstk?-red (ξ-pairʳ r) h = h
idstk?-red (ξ-absurdᶜ _) h = refl
idstk?-red (ξ-absurdᵉ _) h = refl
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
  ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
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
idstk?-red (natrec-zero _ _) ()
idstk?-red (natrec-suc _ _ _) ()
idstk?-red (ξ-nsuc r) h = refl
idstk?-red (ξ-natrecᶻ r) h = h
idstk?-red (ξ-natrecˢ r) h = h
idstk?-red (ξ-natrecⁿ r) h = natstk?-red r h
idstk?-red (ordtr-z _ _ _ _) ()
idstk?-red (ordtr-szz _ _ _) ()
idstk?-red (ordtr-ssz _ _ _ _) ()
idstk?-red (ordtr-szs _ _ _ _) ()
idstk?-red (ordtr-sss _ _ _ _ _) ()
idstk?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
idstk?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
idstk?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
idstk?-red (ξ-ordtrᵖ r) h = h
idstk?-red (ξ-ordtrq r) h = h
idstk?-red (ξ-con r) h = refl
idstk?-red (ξ-ielimᵗ r) h = mustk?-red r h
idstk?-red (ξ-ielimⁱ r) h = h
idstk?-red (ι _ _ _ _) ()
idstk?-red (dpay-ι _ _ _ _) ()
idstk?-red (dpay-σ _ _ _ _ _) ()
idstk?-red (dpay-ρ _ _ _ _ _) ()
idstk?-red (dih-ι _ _ _ _) ()
idstk?-red (dih-σ _ _ _ _ _) ()
idstk?-red (dih-ρ _ _ _ _ _) ()
idstk?-red (fcase-z _ _) ()
idstk?-red (fcase-s _ _ _) ()
idstk?-red (psplit-β _ _ _) ()
idstk?-red (ξ-⌜IMu⌝ᴵ r) h = h
idstk?-red (ξ-⌜IMu⌝ᴰ r) h = h
idstk?-red (ξ-⌜IMu⌝ⁱ r) h = h
idstk?-red (ξ-ielimᴰ r) h = h
idstk?-red (ξ-ielimᵉ r) h = h
idstk?-red (ξ-dι r) h = h
idstk?-red (ξ-dσˢ r) h = h
idstk?-red (ξ-dσᶠ r) h = h
idstk?-red (ξ-dρʲ r) h = h
idstk?-red (ξ-dρᶜ r) h = h
idstk?-red (ξ-dpayᴵ r) h = h
idstk?-red (ξ-dpayᴰ r) h = h
idstk?-red (ξ-dpayᶜ r) h = dstk?-red r h
idstk?-red (ξ-dpayⁱ r) h = h
idstk?-red (ξ-dihᴰ r) h = h
idstk?-red (ξ-dihᵉ r) h = h
idstk?-red (ξ-dihᶜ r) h = dstk?-red r h
idstk?-red (ξ-dihᵖ r) h = h
idstk?-red (ξ-fsuc r) h = h
idstk?-red (ξ-fcaseᵗ r) h = finstk?-red r h
idstk?-red (ξ-fcaseᵃ r) h = h
idstk?-red (ξ-fcaseᵇ r) h = h
idstk?-red (ξ-fcase0 r) h = h
idstk?-red (ξ-psplitᵇ r) h = h
idstk?-red (ξ-psplitᵍ r) h = spine?-red r h

natstk?-red (β _ _) ()
natstk?-red (βfst _ _) ()
natstk?-red (βsnd _ _) ()
natstk?-red (ξ-lam r) h = h
natstk?-red (ξ-appˡ r) h = spine?-red r h
natstk?-red (ξ-appʳ r) h = h
natstk?-red (ξ-pairˡ r) h = h
natstk?-red (ξ-pairʳ r) h = h
natstk?-red (ξ-absurdᶜ _) h = refl
natstk?-red (ξ-absurdᵉ _) h = refl
natstk?-red (ξ-fst r) h = spine?-red r h
natstk?-red (ξ-snd r) h = spine?-red r h
natstk?-red (ξ-⌜Π⌝ˡ r) h = h
natstk?-red (ξ-⌜Π⌝ʳ r) h = h
natstk?-red (ξ-⌜Σ⌝ˡ r) h = h
natstk?-red (ξ-⌜Σ⌝ʳ r) h = h
natstk?-red (ξ-⌜Hom⌝ᶜ r) h = h
natstk?-red (ξ-⌜Hom⌝ˡ r) h = h
natstk?-red (ξ-⌜Hom⌝ʳ r) h = h
natstk?-red (ξ-hreflᶜ r) h = h
natstk?-red (ξ-hreflᵃ r) h = h
natstk?-red (hrefl-pw C₀ s₀ kp) h = refl
natstk?-red (tr-J-base _ _ _ _ _) ()
natstk?-red (tr-J-Σ _ _ _ _ _ _ _) ()
natstk?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h =
  ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
natstk?-red (tr-taut _ _) ()
natstk?-red (tr-pw _ _ _ _ _) h = refl
natstk?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
natstk?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
natstk?-red (ξ-trᵉ r) h = h
natstk?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
natstk?-red (ξ-apᶜ r) h = h
natstk?-red (ξ-apᵇ r) h = h
natstk?-red (ξ-apᵖ r) h = apstk?-red r h
natstk?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
natstk?-red (jsub-refl _ _ _ _) ()
natstk?-red (ξ-⌜Id⌝ᶜ r) h = h
natstk?-red (ξ-⌜Id⌝ˡ r) h = h
natstk?-red (ξ-⌜Id⌝ʳ r) h = h
natstk?-red (ξ-idreflᶜ r) h = refl
natstk?-red (ξ-idreflᵃ r) h = refl
natstk?-red (ξ-jsubᵈ r) h = h
natstk?-red (ξ-jsubᵖ r) h = idstk?-red r h
natstk?-red (ξ-jsubᵉ r) h = h
natstk?-red (natrec-zero _ _) ()
natstk?-red (natrec-suc _ _ _) ()
natstk?-red (ξ-nsuc r) ()
natstk?-red (ξ-natrecᶻ r) h = h
natstk?-red (ξ-natrecˢ r) h = h
natstk?-red (ξ-natrecⁿ r) h = natstk?-red r h
natstk?-red (ordtr-z _ _ _ _) ()
natstk?-red (ordtr-szz _ _ _) ()
natstk?-red (ordtr-ssz _ _ _ _) ()
natstk?-red (ordtr-szs _ _ _ _) ()
natstk?-red (ordtr-sss _ _ _ _ _) ()
natstk?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
natstk?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
natstk?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
natstk?-red (ξ-ordtrᵖ r) h = h
natstk?-red (ξ-ordtrq r) h = h
natstk?-red (ξ-con r) h = refl
natstk?-red (ξ-ielimᵗ r) h = mustk?-red r h
natstk?-red (ξ-ielimⁱ r) h = h
natstk?-red (ι _ _ _ _) ()
natstk?-red (dpay-ι _ _ _ _) ()
natstk?-red (dpay-σ _ _ _ _ _) ()
natstk?-red (dpay-ρ _ _ _ _ _) ()
natstk?-red (dih-ι _ _ _ _) ()
natstk?-red (dih-σ _ _ _ _ _) ()
natstk?-red (dih-ρ _ _ _ _ _) ()
natstk?-red (fcase-z _ _) ()
natstk?-red (fcase-s _ _ _) ()
natstk?-red (psplit-β _ _ _) ()
natstk?-red (ξ-⌜IMu⌝ᴵ r) h = h
natstk?-red (ξ-⌜IMu⌝ᴰ r) h = h
natstk?-red (ξ-⌜IMu⌝ⁱ r) h = h
natstk?-red (ξ-ielimᴰ r) h = h
natstk?-red (ξ-ielimᵉ r) h = h
natstk?-red (ξ-dι r) h = h
natstk?-red (ξ-dσˢ r) h = h
natstk?-red (ξ-dσᶠ r) h = h
natstk?-red (ξ-dρʲ r) h = h
natstk?-red (ξ-dρᶜ r) h = h
natstk?-red (ξ-dpayᴵ r) h = h
natstk?-red (ξ-dpayᴰ r) h = h
natstk?-red (ξ-dpayᶜ r) h = dstk?-red r h
natstk?-red (ξ-dpayⁱ r) h = h
natstk?-red (ξ-dihᴰ r) h = h
natstk?-red (ξ-dihᵉ r) h = h
natstk?-red (ξ-dihᶜ r) h = dstk?-red r h
natstk?-red (ξ-dihᵖ r) h = h
natstk?-red (ξ-fsuc r) h = h
natstk?-red (ξ-fcaseᵗ r) h = finstk?-red r h
natstk?-red (ξ-fcaseᵃ r) h = h
natstk?-red (ξ-fcaseᵇ r) h = h
natstk?-red (ξ-fcase0 r) h = h
natstk?-red (ξ-psplitᵇ r) h = h
natstk?-red (ξ-psplitᵍ r) h = spine?-red r h

mustk?-red (β _ _) ()
mustk?-red (βfst _ _) ()
mustk?-red (βsnd _ _) ()
mustk?-red (ξ-lam r) h = h
mustk?-red (ξ-appˡ r) h = spine?-red r h
mustk?-red (ξ-appʳ r) h = h
mustk?-red (ξ-pairˡ r) h = h
mustk?-red (ξ-pairʳ r) h = h
mustk?-red (ξ-absurdᶜ _) h = refl
mustk?-red (ξ-absurdᵉ _) h = refl
mustk?-red (ξ-fst r) h = spine?-red r h
mustk?-red (ξ-snd r) h = spine?-red r h
mustk?-red (ξ-⌜Π⌝ˡ r) h = h
mustk?-red (ξ-⌜Π⌝ʳ r) h = h
mustk?-red (ξ-⌜Σ⌝ˡ r) h = h
mustk?-red (ξ-⌜Σ⌝ʳ r) h = h
mustk?-red (ξ-⌜Hom⌝ᶜ r) h = h
mustk?-red (ξ-⌜Hom⌝ˡ r) h = h
mustk?-red (ξ-⌜Hom⌝ʳ r) h = h
mustk?-red (ξ-hreflᶜ r) h = h
mustk?-red (ξ-hreflᵃ r) h = h
mustk?-red (hrefl-pw C₀ s₀ kp) h = refl
mustk?-red (tr-J-base _ _ _ _ _) ()
mustk?-red (tr-J-Σ _ _ _ _ _ _ _) ()
mustk?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h =
  ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
mustk?-red (tr-taut _ _) ()
mustk?-red (tr-pw _ _ _ _ _) h = refl
mustk?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
mustk?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
mustk?-red (ξ-trᵉ r) h = h
mustk?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
mustk?-red (ξ-apᶜ r) h = h
mustk?-red (ξ-apᵇ r) h = h
mustk?-red (ξ-apᵖ r) h = apstk?-red r h
mustk?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
mustk?-red (jsub-refl _ _ _ _) ()
mustk?-red (ξ-⌜Id⌝ᶜ r) h = h
mustk?-red (ξ-⌜Id⌝ˡ r) h = h
mustk?-red (ξ-⌜Id⌝ʳ r) h = h
mustk?-red (ξ-idreflᶜ r) h = refl
mustk?-red (ξ-idreflᵃ r) h = refl
mustk?-red (ξ-jsubᵈ r) h = h
mustk?-red (ξ-jsubᵖ r) h = idstk?-red r h
mustk?-red (ξ-jsubᵉ r) h = h
mustk?-red (natrec-zero _ _) ()
mustk?-red (natrec-suc _ _ _) ()
mustk?-red (ξ-nsuc r) h = refl
mustk?-red (ξ-natrecᶻ r) h = h
mustk?-red (ξ-natrecˢ r) h = h
mustk?-red (ξ-natrecⁿ r) h = natstk?-red r h
mustk?-red (ordtr-z _ _ _ _) ()
mustk?-red (ordtr-szz _ _ _) ()
mustk?-red (ordtr-ssz _ _ _ _) ()
mustk?-red (ordtr-szs _ _ _ _) ()
mustk?-red (ordtr-sss _ _ _ _ _) ()
mustk?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
mustk?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
mustk?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
mustk?-red (ξ-ordtrᵖ r) h = h
mustk?-red (ξ-ordtrq r) h = h
-- ★ the four rows that are not `natstk?-red`'s: `con` is the head that
--   UNSTICKS an `elim`, so it is the one place these two keys differ.
mustk?-red (ξ-con r) ()
mustk?-red (ξ-ielimᵗ r) h = mustk?-red r h
mustk?-red (ξ-ielimⁱ r) h = h
mustk?-red (ι _ _ _ _) ()
mustk?-red (dpay-ι _ _ _ _) ()
mustk?-red (dpay-σ _ _ _ _ _) ()
mustk?-red (dpay-ρ _ _ _ _ _) ()
mustk?-red (dih-ι _ _ _ _) ()
mustk?-red (dih-σ _ _ _ _ _) ()
mustk?-red (dih-ρ _ _ _ _ _) ()
mustk?-red (fcase-z _ _) ()
mustk?-red (fcase-s _ _ _) ()
mustk?-red (psplit-β _ _ _) ()
mustk?-red (ξ-⌜IMu⌝ᴵ r) h = h
mustk?-red (ξ-⌜IMu⌝ᴰ r) h = h
mustk?-red (ξ-⌜IMu⌝ⁱ r) h = h
mustk?-red (ξ-ielimᴰ r) h = h
mustk?-red (ξ-ielimᵉ r) h = h
mustk?-red (ξ-dι r) h = h
mustk?-red (ξ-dσˢ r) h = h
mustk?-red (ξ-dσᶠ r) h = h
mustk?-red (ξ-dρʲ r) h = h
mustk?-red (ξ-dρᶜ r) h = h
mustk?-red (ξ-dpayᴵ r) h = h
mustk?-red (ξ-dpayᴰ r) h = h
mustk?-red (ξ-dpayᶜ r) h = dstk?-red r h
mustk?-red (ξ-dpayⁱ r) h = h
mustk?-red (ξ-dihᴰ r) h = h
mustk?-red (ξ-dihᵉ r) h = h
mustk?-red (ξ-dihᶜ r) h = dstk?-red r h
mustk?-red (ξ-dihᵖ r) h = h
mustk?-red (ξ-fsuc r) h = h
mustk?-red (ξ-fcaseᵗ r) h = finstk?-red r h
mustk?-red (ξ-fcaseᵃ r) h = h
mustk?-red (ξ-fcaseᵇ r) h = h
mustk?-red (ξ-fcase0 r) h = h
mustk?-red (ξ-psplitᵇ r) h = h
mustk?-red (ξ-psplitᵍ r) h = spine?-red r h

dstk?-red (β _ _) ()
dstk?-red (βfst _ _) ()
dstk?-red (βsnd _ _) ()
dstk?-red (ξ-lam r) h = h
dstk?-red (ξ-appˡ r) h = spine?-red r h
dstk?-red (ξ-appʳ r) h = h
dstk?-red (ξ-pairˡ r) h = h
dstk?-red (ξ-pairʳ r) h = h
dstk?-red (ξ-absurdᶜ _) h = refl
dstk?-red (ξ-absurdᵉ _) h = refl
dstk?-red (ξ-fst r) h = spine?-red r h
dstk?-red (ξ-snd r) h = spine?-red r h
dstk?-red (ξ-⌜Π⌝ˡ r) h = h
dstk?-red (ξ-⌜Π⌝ʳ r) h = h
dstk?-red (ξ-⌜Σ⌝ˡ r) h = h
dstk?-red (ξ-⌜Σ⌝ʳ r) h = h
dstk?-red (ξ-⌜Hom⌝ᶜ r) h = h
dstk?-red (ξ-⌜Hom⌝ˡ r) h = h
dstk?-red (ξ-⌜Hom⌝ʳ r) h = h
dstk?-red (ξ-hreflᶜ r) h = h
dstk?-red (ξ-hreflᵃ r) h = h
dstk?-red (hrefl-pw C₀ s₀ kp) h = refl
dstk?-red (tr-J-base _ _ _ _ _) ()
dstk?-red (tr-J-Σ _ _ _ _ _ _ _) ()
dstk?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h =
  ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
dstk?-red (tr-taut _ _) ()
dstk?-red (tr-pw _ _ _ _ _) h = refl
dstk?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
dstk?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
dstk?-red (ξ-trᵉ r) h = h
dstk?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
dstk?-red (ξ-apᶜ r) h = h
dstk?-red (ξ-apᵇ r) h = h
dstk?-red (ξ-apᵖ r) h = apstk?-red r h
dstk?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
dstk?-red (jsub-refl _ _ _ _) ()
dstk?-red (ξ-⌜Id⌝ᶜ r) h = h
dstk?-red (ξ-⌜Id⌝ˡ r) h = h
dstk?-red (ξ-⌜Id⌝ʳ r) h = h
dstk?-red (ξ-idreflᶜ r) h = refl
dstk?-red (ξ-idreflᵃ r) h = refl
dstk?-red (ξ-jsubᵈ r) h = h
dstk?-red (ξ-jsubᵖ r) h = idstk?-red r h
dstk?-red (ξ-jsubᵉ r) h = h
dstk?-red (natrec-zero _ _) ()
dstk?-red (natrec-suc _ _ _) ()
dstk?-red (ξ-nsuc r) h = refl
dstk?-red (ξ-natrecᶻ r) h = h
dstk?-red (ξ-natrecˢ r) h = h
dstk?-red (ξ-natrecⁿ r) h = natstk?-red r h
dstk?-red (ordtr-z _ _ _ _) ()
dstk?-red (ordtr-szz _ _ _) ()
dstk?-red (ordtr-ssz _ _ _ _) ()
dstk?-red (ordtr-szs _ _ _ _) ()
dstk?-red (ordtr-sss _ _ _ _ _) ()
dstk?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
dstk?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
dstk?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
dstk?-red (ξ-ordtrᵖ r) h = h
dstk?-red (ξ-ordtrq r) h = h
-- ★ the four rows that are not `natstk?-red`'s: `con` is the head that
--   UNSTICKS an `elim`, so it is the one place these two keys differ.
dstk?-red (ι _ _ _ _) ()
dstk?-red (dpay-ι _ _ _ _) ()
dstk?-red (dpay-σ _ _ _ _ _) ()
dstk?-red (dpay-ρ _ _ _ _ _) ()
dstk?-red (dih-ι _ _ _ _) ()
dstk?-red (dih-σ _ _ _ _ _) ()
dstk?-red (dih-ρ _ _ _ _ _) ()
dstk?-red (fcase-z _ _) ()
dstk?-red (fcase-s _ _ _) ()
dstk?-red (psplit-β _ _ _) ()
dstk?-red (ξ-⌜IMu⌝ᴵ r) h = h
dstk?-red (ξ-⌜IMu⌝ᴰ r) h = h
dstk?-red (ξ-⌜IMu⌝ⁱ r) h = h
dstk?-red (ξ-con r) h = h
dstk?-red (ξ-ielimᴰ r) h = h
dstk?-red (ξ-ielimⁱ r) h = h
dstk?-red (ξ-ielimᵉ r) h = h
dstk?-red (ξ-ielimᵗ r) h = mustk?-red r h
dstk?-red (ξ-dι _) ()
dstk?-red (ξ-dσˢ _) ()
dstk?-red (ξ-dσᶠ _) ()
dstk?-red (ξ-dρʲ _) ()
dstk?-red (ξ-dρᶜ _) ()
dstk?-red (ξ-dpayᴵ r) h = h
dstk?-red (ξ-dpayᴰ r) h = h
dstk?-red (ξ-dpayᶜ r) h = dstk?-red r h
dstk?-red (ξ-dpayⁱ r) h = h
dstk?-red (ξ-dihᴰ r) h = h
dstk?-red (ξ-dihᵉ r) h = h
dstk?-red (ξ-dihᶜ r) h = dstk?-red r h
dstk?-red (ξ-dihᵖ r) h = h
dstk?-red (ξ-fsuc r) h = h
dstk?-red (ξ-fcaseᵗ r) h = finstk?-red r h
dstk?-red (ξ-fcaseᵃ r) h = h
dstk?-red (ξ-fcaseᵇ r) h = h
dstk?-red (ξ-fcase0 r) h = h
dstk?-red (ξ-psplitᵇ r) h = h
dstk?-red (ξ-psplitᵍ r) h = spine?-red r h

finstk?-red (β _ _) ()
finstk?-red (βfst _ _) ()
finstk?-red (βsnd _ _) ()
finstk?-red (ξ-lam r) h = h
finstk?-red (ξ-appˡ r) h = spine?-red r h
finstk?-red (ξ-appʳ r) h = h
finstk?-red (ξ-pairˡ r) h = h
finstk?-red (ξ-pairʳ r) h = h
finstk?-red (ξ-absurdᶜ _) h = refl
finstk?-red (ξ-absurdᵉ _) h = refl
finstk?-red (ξ-fst r) h = spine?-red r h
finstk?-red (ξ-snd r) h = spine?-red r h
finstk?-red (ξ-⌜Π⌝ˡ r) h = h
finstk?-red (ξ-⌜Π⌝ʳ r) h = h
finstk?-red (ξ-⌜Σ⌝ˡ r) h = h
finstk?-red (ξ-⌜Σ⌝ʳ r) h = h
finstk?-red (ξ-⌜Hom⌝ᶜ r) h = h
finstk?-red (ξ-⌜Hom⌝ˡ r) h = h
finstk?-red (ξ-⌜Hom⌝ʳ r) h = h
finstk?-red (ξ-hreflᶜ r) h = h
finstk?-red (ξ-hreflᵃ r) h = h
finstk?-red (hrefl-pw C₀ s₀ kp) h = refl
finstk?-red (tr-J-base _ _ _ _ _) ()
finstk?-red (tr-J-Σ _ _ _ _ _ _ _) ()
finstk?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h =
  ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
finstk?-red (tr-taut _ _) ()
finstk?-red (tr-pw _ _ _ _ _) h = refl
finstk?-red (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
finstk?-red (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
finstk?-red (ξ-trᵉ r) h = h
finstk?-red (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
finstk?-red (ξ-apᶜ r) h = h
finstk?-red (ξ-apᵇ r) h = h
finstk?-red (ξ-apᵖ r) h = apstk?-red r h
finstk?-red (tr-J-Id _ _ _ _ _ _ _ _) ()
finstk?-red (jsub-refl _ _ _ _) ()
finstk?-red (ξ-⌜Id⌝ᶜ r) h = h
finstk?-red (ξ-⌜Id⌝ˡ r) h = h
finstk?-red (ξ-⌜Id⌝ʳ r) h = h
finstk?-red (ξ-idreflᶜ r) h = refl
finstk?-red (ξ-idreflᵃ r) h = refl
finstk?-red (ξ-jsubᵈ r) h = h
finstk?-red (ξ-jsubᵖ r) h = idstk?-red r h
finstk?-red (ξ-jsubᵉ r) h = h
finstk?-red (natrec-zero _ _) ()
finstk?-red (natrec-suc _ _ _) ()
finstk?-red (ξ-nsuc r) h = refl
finstk?-red (ξ-natrecᶻ r) h = h
finstk?-red (ξ-natrecˢ r) h = h
finstk?-red (ξ-natrecⁿ r) h = natstk?-red r h
finstk?-red (ordtr-z _ _ _ _) ()
finstk?-red (ordtr-szz _ _ _) ()
finstk?-red (ordtr-ssz _ _ _ _) ()
finstk?-red (ordtr-szs _ _ _ _) ()
finstk?-red (ordtr-sss _ _ _ _ _) ()
finstk?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
finstk?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
finstk?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
finstk?-red (ξ-ordtrᵖ r) h = h
finstk?-red (ξ-ordtrq r) h = h
-- ★ the four rows that are not `natstk?-red`'s: `con` is the head that
--   UNSTICKS an `elim`, so it is the one place these two keys differ.
finstk?-red (ι _ _ _ _) ()
finstk?-red (dpay-ι _ _ _ _) ()
finstk?-red (dpay-σ _ _ _ _ _) ()
finstk?-red (dpay-ρ _ _ _ _ _) ()
finstk?-red (dih-ι _ _ _ _) ()
finstk?-red (dih-σ _ _ _ _ _) ()
finstk?-red (dih-ρ _ _ _ _ _) ()
finstk?-red (fcase-z _ _) ()
finstk?-red (fcase-s _ _ _) ()
finstk?-red (psplit-β _ _ _) ()
finstk?-red (ξ-⌜IMu⌝ᴵ r) h = h
finstk?-red (ξ-⌜IMu⌝ᴰ r) h = h
finstk?-red (ξ-⌜IMu⌝ⁱ r) h = h
finstk?-red (ξ-con r) h = h
finstk?-red (ξ-ielimᴰ r) h = h
finstk?-red (ξ-ielimⁱ r) h = h
finstk?-red (ξ-ielimᵉ r) h = h
finstk?-red (ξ-ielimᵗ r) h = mustk?-red r h
finstk?-red (ξ-dι r) h = h
finstk?-red (ξ-dσˢ r) h = h
finstk?-red (ξ-dσᶠ r) h = h
finstk?-red (ξ-dρʲ r) h = h
finstk?-red (ξ-dρᶜ r) h = h
finstk?-red (ξ-dpayᴵ r) h = h
finstk?-red (ξ-dpayᴰ r) h = h
finstk?-red (ξ-dpayᶜ r) h = dstk?-red r h
finstk?-red (ξ-dpayⁱ r) h = h
finstk?-red (ξ-dihᴰ r) h = h
finstk?-red (ξ-dihᵉ r) h = h
finstk?-red (ξ-dihᶜ r) h = dstk?-red r h
finstk?-red (ξ-dihᵖ r) h = h
finstk?-red (ξ-fsuc _) ()
finstk?-red (ξ-fcaseᵗ r) h = finstk?-red r h
finstk?-red (ξ-fcaseᵃ r) h = h
finstk?-red (ξ-fcaseᵇ r) h = h
finstk?-red (ξ-fcase0 r) h = h
finstk?-red (ξ-psplitᵇ r) h = h
finstk?-red (ξ-psplitᵍ r) h = spine?-red r h

ordstk?-redᵃ (β _ _) ()
ordstk?-redᵃ (βfst _ _) ()
ordstk?-redᵃ (βsnd _ _) ()
ordstk?-redᵃ (ξ-lam r) h = h
ordstk?-redᵃ (ξ-appˡ r) h = spine?-red r h
ordstk?-redᵃ (ξ-appʳ r) h = h
ordstk?-redᵃ (ξ-pairˡ r) h = h
ordstk?-redᵃ (ξ-pairʳ r) h = h
ordstk?-redᵃ (ξ-absurdᶜ _) h = refl
ordstk?-redᵃ (ξ-absurdᵉ _) h = refl
ordstk?-redᵃ (ξ-fst r) h = spine?-red r h
ordstk?-redᵃ (ξ-snd r) h = spine?-red r h
ordstk?-redᵃ (ξ-⌜Π⌝ˡ r) h = h
ordstk?-redᵃ (ξ-⌜Π⌝ʳ r) h = h
ordstk?-redᵃ (ξ-⌜Σ⌝ˡ r) h = h
ordstk?-redᵃ (ξ-⌜Σ⌝ʳ r) h = h
ordstk?-redᵃ (ξ-⌜Hom⌝ᶜ r) h = h
ordstk?-redᵃ (ξ-⌜Hom⌝ˡ r) h = h
ordstk?-redᵃ (ξ-⌜Hom⌝ʳ r) h = h
ordstk?-redᵃ (ξ-hreflᶜ r) h = h
ordstk?-redᵃ (ξ-hreflᵃ r) h = h
ordstk?-redᵃ (hrefl-pw C₀ s₀ kp) h = refl
ordstk?-redᵃ (tr-J-base _ _ _ _ _) ()
ordstk?-redᵃ (tr-J-Σ _ _ _ _ _ _ _) ()
ordstk?-redᵃ (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h =
  ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
ordstk?-redᵃ (tr-taut _ _) ()
ordstk?-redᵃ (tr-pw _ _ _ _ _) h = refl
ordstk?-redᵃ (ξ-trᵈ {p = p₀} r) h = trstk?-red-d {p = p₀} r h
ordstk?-redᵃ (ξ-trᵖ {d = d₀} r) h = trstk?-red-p {d = d₀} r h
ordstk?-redᵃ (ξ-trᵉ r) h = h
ordstk?-redᵃ (ap-J _ _ c₁ _ key) h =
  ⊥-elim (f≢t (trans (sym (stk⊥dead c₁ key)) h))
ordstk?-redᵃ (ξ-apᶜ r) h = h
ordstk?-redᵃ (ξ-apᵇ r) h = h
ordstk?-redᵃ (ξ-apᵖ r) h = apstk?-red r h
ordstk?-redᵃ (tr-J-Id _ _ _ _ _ _ _ _) ()
ordstk?-redᵃ (jsub-refl _ _ _ _) ()
ordstk?-redᵃ (ξ-⌜Id⌝ᶜ r) h = h
ordstk?-redᵃ (ξ-⌜Id⌝ˡ r) h = h
ordstk?-redᵃ (ξ-⌜Id⌝ʳ r) h = h
ordstk?-redᵃ (ξ-idreflᶜ r) h = refl
ordstk?-redᵃ (ξ-idreflᵃ r) h = refl
ordstk?-redᵃ (ξ-jsubᵈ r) h = h
ordstk?-redᵃ (ξ-jsubᵖ r) h = idstk?-red r h
ordstk?-redᵃ (ξ-jsubᵉ r) h = h
ordstk?-redᵃ (natrec-zero _ _) ()
ordstk?-redᵃ (natrec-suc _ _ _) ()
-- ★ THE ONE ROW THAT DIFFERS FROM `natstk?-red`.  There this is `()`
-- because `natstk? (nsuc n)` is `false`; here `ordstk? (nsuc n) t u`
-- is `ordS? (natstk? t) u`, which does not mention the bound at all —
-- so both sides are the SAME TERM and the row is just `h`.
ordstk?-redᵃ (ξ-nsuc r) h = h
ordstk?-redᵃ (ξ-natrecᶻ r) h = h
ordstk?-redᵃ (ξ-natrecˢ r) h = h
ordstk?-redᵃ (ξ-natrecⁿ r) h = natstk?-red r h
ordstk?-redᵃ (ξ-con r) h = refl
ordstk?-redᵃ (ξ-ielimᵗ r) h = mustk?-red r h
ordstk?-redᵃ (ξ-ielimⁱ r) h = h
ordstk?-redᵃ (ordtr-z _ _ _ _) ()
ordstk?-redᵃ (ordtr-szz _ _ _) ()
ordstk?-redᵃ (ordtr-ssz _ _ _ _) ()
ordstk?-redᵃ (ordtr-szs _ _ _ _) ()
ordstk?-redᵃ (ordtr-sss _ _ _ _ _) ()
ordstk?-redᵃ (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
ordstk?-redᵃ (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
ordstk?-redᵃ (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
ordstk?-redᵃ (ξ-ordtrᵖ r) h = h
ordstk?-redᵃ (ξ-ordtrq r) h = h
ordstk?-redᵃ (ι _ _ _ _) ()
ordstk?-redᵃ (dpay-ι _ _ _ _) ()
ordstk?-redᵃ (dpay-σ _ _ _ _ _) ()
ordstk?-redᵃ (dpay-ρ _ _ _ _ _) ()
ordstk?-redᵃ (dih-ι _ _ _ _) ()
ordstk?-redᵃ (dih-σ _ _ _ _ _) ()
ordstk?-redᵃ (dih-ρ _ _ _ _ _) ()
ordstk?-redᵃ (fcase-z _ _) ()
ordstk?-redᵃ (fcase-s _ _ _) ()
ordstk?-redᵃ (psplit-β _ _ _) ()
ordstk?-redᵃ (ξ-⌜IMu⌝ᴵ r) h = h
ordstk?-redᵃ (ξ-⌜IMu⌝ᴰ r) h = h
ordstk?-redᵃ (ξ-⌜IMu⌝ⁱ r) h = h
ordstk?-redᵃ (ξ-ielimᴰ r) h = h
ordstk?-redᵃ (ξ-ielimᵉ r) h = h
ordstk?-redᵃ (ξ-dι r) h = h
ordstk?-redᵃ (ξ-dσˢ r) h = h
ordstk?-redᵃ (ξ-dσᶠ r) h = h
ordstk?-redᵃ (ξ-dρʲ r) h = h
ordstk?-redᵃ (ξ-dρᶜ r) h = h
ordstk?-redᵃ (ξ-dpayᴵ r) h = h
ordstk?-redᵃ (ξ-dpayᴰ r) h = h
ordstk?-redᵃ (ξ-dpayᶜ r) h = dstk?-red r h
ordstk?-redᵃ (ξ-dpayⁱ r) h = h
ordstk?-redᵃ (ξ-dihᴰ r) h = h
ordstk?-redᵃ (ξ-dihᵉ r) h = h
ordstk?-redᵃ (ξ-dihᶜ r) h = dstk?-red r h
ordstk?-redᵃ (ξ-dihᵖ r) h = h
ordstk?-redᵃ (ξ-fsuc r) h = h
ordstk?-redᵃ (ξ-fcaseᵗ r) h = finstk?-red r h
ordstk?-redᵃ (ξ-fcaseᵃ r) h = h
ordstk?-redᵃ (ξ-fcaseᵇ r) h = h
ordstk?-redᵃ (ξ-fcase0 r) h = h
ordstk?-redᵃ (ξ-psplitᵇ r) h = h
ordstk?-redᵃ (ξ-psplitᵍ r) h = spine?-red r h

-- `t` and `u` are inert under a reduction of the other, so these two
-- must case on `a` — its head is what selects `ordstk?`'s clause, and a
-- reduction of `t`/`u` cannot reveal it.  Every non-numeral head lands
-- in `ordstk?`'s catch-all, where the value is `natstk? a` and the row
-- is `h`; only `nzero` (refuted) and `nsuc` (the Boolean lemmas) differ.
ordstk?-redᵗ {a = nzero} r ()
ordstk?-redᵗ {a = nsuc a₀} {t = t} {t' = t'} r h =
  ordS?-monoᵇ (natstk? t) (natstk? t') (natstk?-red r) _ h
ordstk?-redᵗ {a = var x₂} r h = h
ordstk?-redᵗ {a = lam a} r h = h
ordstk?-redᵗ {a = app a a₁} r h = h
ordstk?-redᵗ {a = pair a a₁} r h = h
ordstk?-redᵗ {a = absurd a a₁} r h = h
ordstk?-redᵗ {a = ordtr a a₁ a₂ a₃ a₄} r h = h
ordstk?-redᵗ {a = fst a} r h = h
ordstk?-redᵗ {a = snd a} r h = h
ordstk?-redᵗ {a = ⌜base⌝} r h = h
ordstk?-redᵗ {a = ⌜Π⌝ a a₁} r h = h
ordstk?-redᵗ {a = ⌜Σ⌝ a a₁} r h = h
ordstk?-redᵗ {a = ⌜Hom⌝ a a₁ a₂} r h = h
ordstk?-redᵗ {a = hrefl a a₁} r h = h
ordstk?-redᵗ {a = tr a a₁ a₂} r h = h
ordstk?-redᵗ {a = ap a a₁ a₂} r h = h
ordstk?-redᵗ {a = ⌜Id⌝ a a₁ a₂} r h = h
ordstk?-redᵗ {a = idrefl a a₁} r h = h
ordstk?-redᵗ {a = jsub a a₁ a₂} r h = h
ordstk?-redᵗ {a = unit} r h = h
ordstk?-redᵗ {a = natrec a a₁ a₂} r h = h
ordstk?-redᵗ {a = ⌜Nat⌝} r h = h
ordstk?-redᵗ {a = ⌜Unit⌝} r h = h
ordstk?-redᵗ {a = ⌜IMu⌝ a a₁ a₂} r h = h
ordstk?-redᵗ {a = ⌜Fin⌝ n₀} r h = h
ordstk?-redᵗ {a = con a} r h = h
ordstk?-redᵗ {a = ielim a a₁ a₂ a₃} r h = h
ordstk?-redᵗ {a = dι a} r h = h
ordstk?-redᵗ {a = dσ a a₁} r h = h
ordstk?-redᵗ {a = dρ a a₁} r h = h
ordstk?-redᵗ {a = dpay a a₁ a₂ a₃} r h = h
ordstk?-redᵗ {a = dih a a₁ a₂ a₃} r h = h
ordstk?-redᵗ {a = fzero} r h = h
ordstk?-redᵗ {a = fsuc a} r h = h
ordstk?-redᵗ {a = fcase a a₁ a₂} r h = h
ordstk?-redᵗ {a = fcase0 a} r h = h
ordstk?-redᵗ {a = psplit a a₁} r h = h
ordstk?-redᵘ {a = nzero} r ()
ordstk?-redᵘ {a = nsuc a₀} {t = t} r h =
  ordS?-monoᵘ (natstk? t) (natstk?-red r) h
ordstk?-redᵘ {a = var x₂} r h = h
ordstk?-redᵘ {a = lam a} r h = h
ordstk?-redᵘ {a = app a a₁} r h = h
ordstk?-redᵘ {a = pair a a₁} r h = h
ordstk?-redᵘ {a = absurd a a₁} r h = h
ordstk?-redᵘ {a = ordtr a a₁ a₂ a₃ a₄} r h = h
ordstk?-redᵘ {a = fst a} r h = h
ordstk?-redᵘ {a = snd a} r h = h
ordstk?-redᵘ {a = ⌜base⌝} r h = h
ordstk?-redᵘ {a = ⌜Π⌝ a a₁} r h = h
ordstk?-redᵘ {a = ⌜Σ⌝ a a₁} r h = h
ordstk?-redᵘ {a = ⌜Hom⌝ a a₁ a₂} r h = h
ordstk?-redᵘ {a = hrefl a a₁} r h = h
ordstk?-redᵘ {a = tr a a₁ a₂} r h = h
ordstk?-redᵘ {a = ap a a₁ a₂} r h = h
ordstk?-redᵘ {a = ⌜Id⌝ a a₁ a₂} r h = h
ordstk?-redᵘ {a = idrefl a a₁} r h = h
ordstk?-redᵘ {a = jsub a a₁ a₂} r h = h
ordstk?-redᵘ {a = unit} r h = h
ordstk?-redᵘ {a = natrec a a₁ a₂} r h = h
ordstk?-redᵘ {a = ⌜Nat⌝} r h = h
ordstk?-redᵘ {a = ⌜Unit⌝} r h = h
ordstk?-redᵘ {a = ⌜IMu⌝ a a₁ a₂} r h = h
ordstk?-redᵘ {a = ⌜Fin⌝ n₀} r h = h
ordstk?-redᵘ {a = con a} r h = h
ordstk?-redᵘ {a = ielim a a₁ a₂ a₃} r h = h
ordstk?-redᵘ {a = dι a} r h = h
ordstk?-redᵘ {a = dσ a a₁} r h = h
ordstk?-redᵘ {a = dρ a a₁} r h = h
ordstk?-redᵘ {a = dpay a a₁ a₂ a₃} r h = h
ordstk?-redᵘ {a = dih a a₁ a₂ a₃} r h = h
ordstk?-redᵘ {a = fzero} r h = h
ordstk?-redᵘ {a = fsuc a} r h = h
ordstk?-redᵘ {a = fcase a a₁ a₂} r h = h
ordstk?-redᵘ {a = fcase0 a} r h = h
ordstk?-redᵘ {a = psplit a a₁} r h = h

nopw?-red (β _ _) ()
nopw?-red (βfst _ _) ()
nopw?-red (βsnd _ _) ()
nopw?-red (ξ-lam r) h = h
nopw?-red (ξ-appˡ r) h = spine?-red r h
nopw?-red (ξ-appʳ r) h = h
nopw?-red (ξ-pairˡ r) h = h
nopw?-red (ξ-pairʳ r) h = h
nopw?-red (ξ-absurdᶜ _) h = refl
nopw?-red (ξ-absurdᵉ _) h = refl
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
nopw?-red (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
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
nopw?-red (natrec-zero _ _) ()
nopw?-red (natrec-suc _ _ _) ()
nopw?-red (ξ-nsuc r) h = refl
nopw?-red (ξ-natrecᶻ r) h = h
nopw?-red (ξ-natrecˢ r) h = h
nopw?-red (ξ-natrecⁿ r) h = natstk?-red r h
nopw?-red (ordtr-z _ _ _ _) ()
nopw?-red (ordtr-szz _ _ _) ()
nopw?-red (ordtr-ssz _ _ _ _) ()
nopw?-red (ordtr-szs _ _ _ _) ()
nopw?-red (ordtr-sss _ _ _ _ _) ()
nopw?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
nopw?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
nopw?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
nopw?-red (ξ-ordtrᵖ r) h = h
nopw?-red (ξ-ordtrq r) h = h
nopw?-red (ξ-con r) h = refl
nopw?-red (ξ-ielimᵗ r) h = mustk?-red r h
nopw?-red (ξ-ielimⁱ r) h = h
nopw?-red (ι _ _ _ _) ()
nopw?-red (dpay-ι _ _ _ _) ()
nopw?-red (dpay-σ _ _ _ _ _) ()
nopw?-red (dpay-ρ _ _ _ _ _) ()
nopw?-red (dih-ι _ _ _ _) ()
nopw?-red (dih-σ _ _ _ _ _) ()
nopw?-red (dih-ρ _ _ _ _ _) ()
nopw?-red (fcase-z _ _) ()
nopw?-red (fcase-s _ _ _) ()
nopw?-red (psplit-β _ _ _) ()
nopw?-red (ξ-⌜IMu⌝ᴵ r) h = h
nopw?-red (ξ-⌜IMu⌝ᴰ r) h = h
nopw?-red (ξ-⌜IMu⌝ⁱ r) h = h
nopw?-red (ξ-ielimᴰ r) h = h
nopw?-red (ξ-ielimᵉ r) h = h
nopw?-red (ξ-dι r) h = h
nopw?-red (ξ-dσˢ r) h = h
nopw?-red (ξ-dσᶠ r) h = h
nopw?-red (ξ-dρʲ r) h = h
nopw?-red (ξ-dρᶜ r) h = h
nopw?-red (ξ-dpayᴵ r) h = h
nopw?-red (ξ-dpayᴰ r) h = h
nopw?-red (ξ-dpayᶜ r) h = dstk?-red r h
nopw?-red (ξ-dpayⁱ r) h = h
nopw?-red (ξ-dihᴰ r) h = h
nopw?-red (ξ-dihᵉ r) h = h
nopw?-red (ξ-dihᶜ r) h = dstk?-red r h
nopw?-red (ξ-dihᵖ r) h = h
nopw?-red (ξ-fsuc r) h = h
nopw?-red (ξ-fcaseᵗ r) h = finstk?-red r h
nopw?-red (ξ-fcaseᵃ r) h = h
nopw?-red (ξ-fcaseᵇ r) h = h
nopw?-red (ξ-fcase0 r) h = h
nopw?-red (ξ-psplitᵇ r) h = h
nopw?-red (ξ-psplitᵍ r) h = spine?-red r h

deadmot?-red (β _ _) ()
deadmot?-red (βfst _ _) ()
deadmot?-red (βsnd _ _) ()
deadmot?-red (ξ-lam r) h = h
deadmot?-red (ξ-appˡ r) h = spine?-red r h
deadmot?-red (ξ-appʳ r) h = h
deadmot?-red (ξ-pairˡ r) h = h
deadmot?-red (ξ-pairʳ r) h = h
deadmot?-red (ξ-absurdᶜ _) h = refl
deadmot?-red (ξ-absurdᵉ _) h = refl
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
  ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
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
deadmot?-red (natrec-zero _ _) ()
deadmot?-red (natrec-suc _ _ _) ()
deadmot?-red (ξ-nsuc r) h = refl
deadmot?-red (ξ-natrecᶻ r) h = h
deadmot?-red (ξ-natrecˢ r) h = h
deadmot?-red (ξ-natrecⁿ r) h = natstk?-red r h
deadmot?-red (ordtr-z _ _ _ _) ()
deadmot?-red (ordtr-szz _ _ _) ()
deadmot?-red (ordtr-ssz _ _ _ _) ()
deadmot?-red (ordtr-szs _ _ _ _) ()
deadmot?-red (ordtr-sss _ _ _ _ _) ()
deadmot?-red (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
deadmot?-red (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
deadmot?-red (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
deadmot?-red (ξ-ordtrᵖ r) h = h
deadmot?-red (ξ-ordtrq r) h = h
deadmot?-red (ξ-con r) h = refl
deadmot?-red (ξ-ielimᵗ r) h = mustk?-red r h
deadmot?-red (ξ-ielimⁱ r) h = h
deadmot?-red (ι _ _ _ _) ()
deadmot?-red (dpay-ι _ _ _ _) ()
deadmot?-red (dpay-σ _ _ _ _ _) ()
deadmot?-red (dpay-ρ _ _ _ _ _) ()
deadmot?-red (dih-ι _ _ _ _) ()
deadmot?-red (dih-σ _ _ _ _ _) ()
deadmot?-red (dih-ρ _ _ _ _ _) ()
deadmot?-red (fcase-z _ _) ()
deadmot?-red (fcase-s _ _ _) ()
deadmot?-red (psplit-β _ _ _) ()
deadmot?-red (ξ-⌜IMu⌝ᴵ r) h = h
deadmot?-red (ξ-⌜IMu⌝ᴰ r) h = h
deadmot?-red (ξ-⌜IMu⌝ⁱ r) h = h
deadmot?-red (ξ-ielimᴰ r) h = h
deadmot?-red (ξ-ielimᵉ r) h = h
deadmot?-red (ξ-dι r) h = h
deadmot?-red (ξ-dσˢ r) h = h
deadmot?-red (ξ-dσᶠ r) h = h
deadmot?-red (ξ-dρʲ r) h = h
deadmot?-red (ξ-dρᶜ r) h = h
deadmot?-red (ξ-dpayᴵ r) h = h
deadmot?-red (ξ-dpayᴰ r) h = h
deadmot?-red (ξ-dpayᶜ r) h = dstk?-red r h
deadmot?-red (ξ-dpayⁱ r) h = h
deadmot?-red (ξ-dihᴰ r) h = h
deadmot?-red (ξ-dihᵉ r) h = h
deadmot?-red (ξ-dihᶜ r) h = dstk?-red r h
deadmot?-red (ξ-dihᵖ r) h = h
deadmot?-red (ξ-fsuc r) h = h
deadmot?-red (ξ-fcaseᵗ r) h = finstk?-red r h
deadmot?-red (ξ-fcaseᵃ r) h = h
deadmot?-red (ξ-fcaseᵇ r) h = h
deadmot?-red (ξ-fcase0 r) h = h
deadmot?-red (ξ-psplitᵇ r) h = h
deadmot?-red (ξ-psplitᵍ r) h = spine?-red r h

-- dead codes are pw-immune (deadness subsumes the weaker key).
-- ★ the `stableA?` peer.  ⌜Nat⌝ is ABSURD here — `stableA? ⌜Nat⌝`
-- is `false`, which is exactly the split.
deadA→nopw : (C : RTm Γ) → stableA? C ≡ true → nopw? C ≡ true
deadA→nopw (var x) h = refl
deadA→nopw (lam t) h = refl
deadA→nopw (app t u) h = h
deadA→nopw (pair a b) h = refl
deadA→nopw (absurd c e) h = h
deadA→nopw (ordtr a t u p q) h = h
deadA→nopw (fst t) h = h
deadA→nopw (snd t) h = h
deadA→nopw ⌜base⌝ ()
deadA→nopw ⌜Nat⌝ ()
deadA→nopw (⌜Π⌝ c d) ()
deadA→nopw (⌜Σ⌝ c d) ()
deadA→nopw (⌜Hom⌝ C a b) h = deadA→nopw C h
deadA→nopw (hrefl c t) h = refl
deadA→nopw (tr d p e) h = h
deadA→nopw (ap c b p) h = refl
deadA→nopw (idrefl c t) h = refl
deadA→nopw (jsub d p e) h = h
deadA→nopw unit h = refl
deadA→nopw nzero h = refl
deadA→nopw (nsuc n) h = refl
deadA→nopw (natrec z s n) h = h
deadA→nopw (⌜IMu⌝ I D i) ()
deadA→nopw (⌜Fin⌝ n) ()
deadA→nopw (con p) h = refl
deadA→nopw (ielim D i e t) h = h
deadA→nopw (dι j) h = refl
deadA→nopw (dσ S f) h = refl
deadA→nopw (dρ j C) h = refl
deadA→nopw (dpay I D C i) h = h
deadA→nopw (dih D e C p) h = h
deadA→nopw fzero h = refl
deadA→nopw (fsuc t) h = refl
deadA→nopw (fcase t a b) h = h
deadA→nopw (fcase0 t) h = refl
deadA→nopw (psplit b q) h = h

dead→nopw : (C : RTm Γ) → stablecd? C ≡ true → nopw? C ≡ true
dead→nopw (var x) h = refl
dead→nopw (lam t) h = refl
dead→nopw (app t u) h = h
dead→nopw (pair a b) h = refl
dead→nopw (absurd c e) h = h
dead→nopw (ordtr a t u p q) h = h
dead→nopw (fst t) h = h
dead→nopw (snd t) h = h
dead→nopw ⌜base⌝ ()
dead→nopw ⌜Nat⌝ h = refl
dead→nopw (⌜Π⌝ c d) ()
dead→nopw (⌜Σ⌝ c d) ()
dead→nopw (⌜Hom⌝ C a b) h = deadA→nopw C h
dead→nopw (hrefl c t) h = refl
dead→nopw (tr d p e) h = h
dead→nopw (ap c b p) h = refl
dead→nopw (idrefl c t) h = refl
dead→nopw (jsub d p e) h = h
dead→nopw unit h = refl
dead→nopw nzero h = refl
dead→nopw (nsuc n) h = refl
dead→nopw (natrec z s n) h = h
dead→nopw (⌜IMu⌝ I D i) ()
dead→nopw (⌜Fin⌝ n) ()
dead→nopw (con p) h = refl
dead→nopw (ielim D i e t) h = h
dead→nopw (dι j) h = refl
dead→nopw (dσ S f) h = refl
dead→nopw (dρ j C) h = refl
dead→nopw (dpay I D C i) h = h
dead→nopw (dih D e C p) h = h
dead→nopw fzero h = refl
dead→nopw (fsuc t) h = refl
dead→nopw (fcase t a b) h = h
dead→nopw (fcase0 t) h = refl
dead→nopw (psplit b q) h = h


-- an hrefl path at a DEAD code is tr-stuck under EVERY motive shape.
trstk-hrefl-any : (d : RTm (Γ ∙)) {c s : RTm Γ} →
                  stablecd? c ≡ true → trstk? d (hrefl c s) ≡ true
trstk-hrefl-any (var x) {c = c} h = dead→nopw c h
trstk-hrefl-any (lam t) h = h
trstk-hrefl-any (app t u) h = h
trstk-hrefl-any (pair a b) h = h
trstk-hrefl-any (absurd c e) h = h
trstk-hrefl-any (ordtr a t u p q) h = h
trstk-hrefl-any (fst t) h = h
trstk-hrefl-any (snd t) h = h
trstk-hrefl-any ⌜base⌝ h = h
trstk-hrefl-any ⌜Nat⌝ h = h
trstk-hrefl-any ⌜Unit⌝ h = h
trstk-hrefl-any (⌜Π⌝ c₂ d₂) h = h
trstk-hrefl-any (⌜Σ⌝ c₂ d₂) h = h
trstk-hrefl-any (⌜Hom⌝ c₂ a₂ b₂) h = h
trstk-hrefl-any (hrefl c₂ t₂) h = h
trstk-hrefl-any (tr d₂ p₂ e₂) h = h
trstk-hrefl-any (ap c b p) h = h
trstk-hrefl-any (⌜Id⌝ c a b) h = h
trstk-hrefl-any (idrefl c t) h = h
trstk-hrefl-any (jsub d p e) h = h
trstk-hrefl-any unit h = h
trstk-hrefl-any nzero h = h
trstk-hrefl-any (nsuc n) h = h
trstk-hrefl-any (natrec z s n) h = h
trstk-hrefl-any (⌜IMu⌝ I D i) h = h
trstk-hrefl-any (⌜Fin⌝ n) h = h
trstk-hrefl-any (con p) h = h
trstk-hrefl-any (ielim D i e t) h = h
trstk-hrefl-any (dι j) h = h
trstk-hrefl-any (dσ S f) h = h
trstk-hrefl-any (dρ j C) h = h
trstk-hrefl-any (dpay I D C i) h = h
trstk-hrefl-any (dih D e C p) h = h
trstk-hrefl-any fzero h = h
trstk-hrefl-any (fsuc t) h = h
trstk-hrefl-any (fcase t a b) h = h
trstk-hrefl-any (fcase0 t) h = h
trstk-hrefl-any (psplit b q) h = h

-- motive steps.  Only lam- and hrefl-paths inspect the motive; the
-- rest are motive-independent (the catchall clause on both sides).
-- ★ stage D: an `absurd` PATH is neither `lam` nor `hrefl`, so the
-- verdict is `pathstk? (absurd _ _) = true` no matter what the motive
-- does.
-- ★ INDUCTIVE TYPES: a `con`/`elim` MOTIVE is not a `var`, so `trstk?`
-- falls to `pathstk?` on both sides — `trstk-hrefl-any` at the reduct.
trstk?-red-d {d = ielim dD di dm dt} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = ⌜IMu⌝ dD dI di} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {p = absurd p₂ e₂} r h = refl
-- an `ordtr` PATH is neither `lam` nor `hrefl`, so `trstk?` falls to
-- `pathstk?` and a reduction of the MOTIVE cannot touch it.
trstk?-red-d {p = ordtr a₂ t₂ u₂ p₂ q₂} r h = h
-- …and an `ordtr` MOTIVE is not a `var`, so the same catch-all applies
-- however the motive steps.
trstk?-red-d {p = hrefl c₂ s₂} (ordtr-z t₂ u₂ p₂ q₂) h = h
-- ⚠ these two reduce the MOTIVE to an arbitrary subterm, which may
-- well be a `var` — so the catch-all no longer applies and the row
-- needs `trstk-hrefl-any`, which covers every motive at once.
trstk?-red-d {p = hrefl c₂ s₂} (ordtr-szz a₂ p₂ q₂) h = trstk-hrefl-any p₂ h
trstk?-red-d {p = hrefl c₂ s₂} (ordtr-ssz a₂ t₂ p₂ q₂) h = trstk-hrefl-any q₂ h
trstk?-red-d {p = hrefl c₂ s₂} (ordtr-szs a₂ u₂ p₂ q₂) h = h
trstk?-red-d {p = hrefl c₂ s₂} (ordtr-sss a₂ t₂ u₂ p₂ q₂) h = h
trstk?-red-d {p = hrefl c₂ s₂} (ξ-ordtrᵃ r) h = h
trstk?-red-d {p = hrefl c₂ s₂} (ξ-ordtrᵗ r) h = h
trstk?-red-d {p = hrefl c₂ s₂} (ξ-ordtrᵘ r) h = h
trstk?-red-d {p = hrefl c₂ s₂} (ξ-ordtrᵖ r) h = h
trstk?-red-d {p = hrefl c₂ s₂} (ξ-ordtrq r) h = h
trstk?-red-d {d = absurd d₂ f₂} {p = hrefl p₂ s₂} (ξ-absurdᶜ _) h = h
trstk?-red-d {d = absurd d₂ f₂} {p = hrefl p₂ s₂} (ξ-absurdᵉ _) h = h
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
trstk?-red-d {d = unit} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = nzero} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (nsuc dz)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (natrec dz₁ dz₂ dz₃)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {p = (var y)} r h = h
trstk?-red-d {p = (app t₁ u₁)} r h = h
trstk?-red-d {p = (pair a₁ b₁)} r h = h
trstk?-red-d {p = (fst q)} r h = h
trstk?-red-d {p = (snd q)} r h = h
trstk?-red-d {p = ⌜base⌝} r h = h
trstk?-red-d {p = ⌜Nat⌝} r h = h
trstk?-red-d {p = ⌜Unit⌝} r h = h
trstk?-red-d {p = (⌜Π⌝ c₁ d₁)} r h = h
trstk?-red-d {p = (⌜Σ⌝ c₁ d₁)} r h = h
trstk?-red-d {p = (⌜Hom⌝ c₁ a₁ b₁)} r h = h
trstk?-red-d {p = (tr d₁ p₁ e₁)} r h = h
trstk?-red-d {p = ap _ _ _} r h = h
trstk?-red-d {p = ⌜Id⌝ _ _ _} r h = h
trstk?-red-d {p = idrefl _ _} r h = h
trstk?-red-d {p = jsub _ _ _} r h = h
trstk?-red-d {p = unit} r h = h
trstk?-red-d {p = nzero} r h = h
trstk?-red-d {p = nsuc _} r h = h
trstk?-red-d {p = natrec _ _ _} r h = h
-- a `con`/`elim` PATH is neither `lam` nor `hrefl`, so `trstk?` falls to
-- `pathstk?` and a reduction of the MOTIVE cannot touch it.
-- ⚠ THREE ROWS CLOSE 72 MISSING CASES.  Agda enumerated the `d` × `p`
--   cross-product, but these rows are UNIFORM in `d` — `trstk?` does not
--   look at `d` once `p` is a constructor/eliminator/code — so one row per
--   new `p`-shape suffices.  Reading the missing-case list as a worklist
--   would have produced 72 clauses for the same content.
trstk?-red-d {p = ielim _ _ _ _} r h = h
trstk?-red-d {p = ⌜IMu⌝ _ _ _} r h = h
trstk?-red-d {d = (con _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (ielim _ _ _ _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (⌜IMu⌝ _ _ _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (⌜Fin⌝ _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (dι _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (dσ _ _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (dρ _ _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (dpay _ _ _ _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (dih _ _ _ _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = fzero} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (fsuc _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (fcase _ _ _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (fcase0 _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {d = (psplit _ _)} {d' = d'} {p = hrefl c s} r h = trstk-hrefl-any d' h
trstk?-red-d {p = con _} r h = h
trstk?-red-d {p = ielim _ _ _ _} r h = h
trstk?-red-d {p = ⌜IMu⌝ _ _ _} r h = h
trstk?-red-d {p = ⌜Fin⌝ _} r h = h
trstk?-red-d {p = dι _} r h = h
trstk?-red-d {p = dσ _ _} r h = h
trstk?-red-d {p = dρ _ _} r h = h
trstk?-red-d {p = dpay _ _ _ _} r h = h
trstk?-red-d {p = dih _ _ _ _} r h = h
trstk?-red-d {p = fzero} r h = h
trstk?-red-d {p = fsuc _} r h = h
trstk?-red-d {p = fcase _ _ _} r h = h
trstk?-red-d {p = fcase0 _} r h = h
trstk?-red-d {p = psplit _ _} r h = h
trstk?-red-p {d = (var x)} (ξ-hreflᶜ rc) h = nopw?-red rc h
trstk?-red-p {d = (lam t)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (app t u)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (pair a b)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (fst t)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (snd t)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
-- ★ stage D: an `absurd` MOTIVE is not `var vz`, so `trstk?` falls to
-- `pathstk?` on the path — the same as every other non-var motive.
trstk?-red-p {d = (absurd d₂ e₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
-- an `hrefl` path can only become a `lam` by `hrefl-pw`, which needs a
-- pw-able code — and `pathstk?` already said the code is DEAD.  The two
-- keys are disjoint, so the case is absurd.
trstk?-red-p {d = (absurd d₂ e₂)} {hrefl _ _} {lam _} (hrefl-pw C₀ s₀ kp) h =
  ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (absurd d₂ e₂)} {hrefl _ _} {hrefl _ _} (ξ-hreflᵃ _) h = h
-- an `ordtr` MOTIVE behaves exactly like an `absurd` one: it is not
-- `var vz`, so `trstk?` falls through to `pathstk?` on the path.
trstk?-red-p {d = (ordtr dz₁ dz₂ dz₃ dz₄ dz₅)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (ordtr dz₁ dz₂ dz₃ dz₄ dz₅)} {hrefl _ _} {hrefl _ _} (ξ-hreflᵃ _) h = h
trstk?-red-p {d = ⌜base⌝} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = ⌜Nat⌝} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = ⌜Unit⌝} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜IMu⌝ Dˣ Iˣ iˣ)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜Π⌝ c₂ d₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜Σ⌝ c₂ d₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜Hom⌝ c₂ a₂ b₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (hrefl c₂ t₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (tr d₂ p₂ e₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (ap dz₁ dz₂ dz₃)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜Id⌝ dz₁ dz₂ dz₃)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (idrefl dz₁ dz₂)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (jsub dz₁ dz₂ dz₃)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = unit} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = nzero} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (nsuc dz)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (ielim dD iˣ dm dt)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (natrec dz₁ dz₂ dz₃)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (var x)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (lam t)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (app t u)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (pair a b)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (fst t)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (snd t)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = ⌜base⌝} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = ⌜Nat⌝} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = ⌜Unit⌝} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜IMu⌝ Dˣ Iˣ iˣ)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜Π⌝ c₂ d₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜Σ⌝ c₂ d₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜Hom⌝ c₂ a₂ b₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (hrefl c₂ t₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (tr d₂ p₂ e₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (ap dz₁ dz₂ dz₃)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜Id⌝ dz₁ dz₂ dz₃)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (idrefl dz₁ dz₂)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (jsub dz₁ dz₂ dz₃)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = unit} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = nzero} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (nsuc dz)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (ielim dD iˣ dm dt)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (natrec dz₁ dz₂ dz₃)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = var x} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (nopw⊥pw C₀ h)) kp))
trstk?-red-p {d = (lam t)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (app t u)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (pair a b)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (fst t)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (snd t)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = ⌜base⌝} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = ⌜Nat⌝} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = ⌜Unit⌝} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜IMu⌝ Dˣ Iˣ iˣ)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜Π⌝ c₂ d₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜Σ⌝ c₂ d₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜Hom⌝ c₂ a₂ b₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (hrefl c₂ t₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (tr d₂ p₂ e₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (ap dz₁ dz₂ dz₃)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜Id⌝ dz₁ dz₂ dz₃)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (idrefl dz₁ dz₂)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (jsub dz₁ dz₂ dz₃)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = unit} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = nzero} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (nsuc dz)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (ielim dD iˣ dm dt)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (natrec dz₁ dz₂ dz₃)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (ordtr dz₁ dz₂ dz₃ dz₄ dz₅)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p (β _ _) ()
trstk?-red-p (βfst _ _) ()
trstk?-red-p (βsnd _ _) ()
trstk?-red-p (ξ-lam r) h = h
trstk?-red-p (ξ-appˡ r) h = spine?-red r h
trstk?-red-p (ξ-appʳ r) h = h
trstk?-red-p (ξ-pairˡ r) h = h
trstk?-red-p (ξ-pairʳ r) h = h
trstk?-red-p (ξ-absurdᶜ _) h = refl
-- the path is an `ordtr`, so `trstk?` is `pathstk?` — i.e. `ordstk?` —
-- and the order's own `-red` lemmas discharge every congruence.
trstk?-red-p (ordtr-z _ _ _ _) ()
trstk?-red-p (ordtr-szz _ _ _) ()
trstk?-red-p (ordtr-ssz _ _ _ _) ()
trstk?-red-p (ordtr-szs _ _ _ _) ()
trstk?-red-p (ordtr-sss _ _ _ _ _) ()
trstk?-red-p (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) h = ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r h
trstk?-red-p (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) h = ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r h
trstk?-red-p (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) h = ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r h
trstk?-red-p (ξ-ordtrᵖ r) h = h
trstk?-red-p (ξ-ordtrq r) h = h
trstk?-red-p (ξ-absurdᵉ _) h = refl
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
trstk?-red-p (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) h = ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) h))
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
trstk?-red-p (natrec-zero _ _) ()
trstk?-red-p (natrec-suc _ _ _) ()
trstk?-red-p (ξ-nsuc r) h = refl
trstk?-red-p (ξ-natrecᶻ r) h = h
trstk?-red-p (ξ-natrecˢ r) h = h
trstk?-red-p (ξ-natrecⁿ r) h = natstk?-red r h
-- ★ INDUCTIVE TYPES: a `con`/`elim` path is motive-independent (neither
-- `lam` nor `hrefl`), so this is `pathstk?`'s ι row verbatim.
trstk?-red-p (ξ-con r) h = refl
trstk?-red-p (ξ-ielimᵗ r) h = mustk?-red r h
trstk?-red-p (ξ-ielimⁱ r) h = h
trstk?-red-p (ι _ _ _ _) ()
trstk?-red-p (dpay-ι _ _ _ _) ()
trstk?-red-p (dpay-σ _ _ _ _ _) ()
trstk?-red-p (dpay-ρ _ _ _ _ _) ()
trstk?-red-p (dih-ι _ _ _ _) ()
trstk?-red-p (dih-σ _ _ _ _ _) ()
trstk?-red-p (dih-ρ _ _ _ _ _) ()
trstk?-red-p (fcase-z _ _) ()
trstk?-red-p (fcase-s _ _ _) ()
trstk?-red-p (psplit-β _ _ _) ()
trstk?-red-p (ξ-⌜IMu⌝ᴵ r) h = h
trstk?-red-p (ξ-⌜IMu⌝ᴰ r) h = h
trstk?-red-p (ξ-⌜IMu⌝ⁱ r) h = h
trstk?-red-p (ξ-ielimᴰ r) h = h
trstk?-red-p (ξ-ielimᵉ r) h = h
trstk?-red-p (ξ-dι r) h = h
trstk?-red-p (ξ-dσˢ r) h = h
trstk?-red-p (ξ-dσᶠ r) h = h
trstk?-red-p (ξ-dρʲ r) h = h
trstk?-red-p (ξ-dρᶜ r) h = h
trstk?-red-p (ξ-dpayᴵ r) h = h
trstk?-red-p (ξ-dpayᴰ r) h = h
trstk?-red-p (ξ-dpayᶜ r) h = dstk?-red r h
trstk?-red-p (ξ-dpayⁱ r) h = h
trstk?-red-p (ξ-dihᴰ r) h = h
trstk?-red-p (ξ-dihᵉ r) h = h
trstk?-red-p (ξ-dihᶜ r) h = dstk?-red r h
trstk?-red-p (ξ-dihᵖ r) h = h
trstk?-red-p (ξ-fsuc r) h = h
trstk?-red-p (ξ-fcaseᵗ r) h = finstk?-red r h
trstk?-red-p (ξ-fcaseᵃ r) h = h
trstk?-red-p (ξ-fcaseᵇ r) h = h
trstk?-red-p (ξ-fcase0 r) h = h
trstk?-red-p (ξ-psplitᵇ r) h = h
trstk?-red-p (ξ-psplitᵍ r) h = spine?-red r h
trstk?-red-p {d = (con _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (con _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (con _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (⌜Fin⌝ _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (⌜Fin⌝ _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (⌜Fin⌝ _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (dι _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (dι _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (dι _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (dσ _ _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (dσ _ _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (dσ _ _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (dρ _ _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (dρ _ _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (dρ _ _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (dpay _ _ _ _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (dpay _ _ _ _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (dpay _ _ _ _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (dih _ _ _ _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (dih _ _ _ _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (dih _ _ _ _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = fzero} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = fzero} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = fzero} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (fsuc _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (fsuc _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (fsuc _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (fcase _ _ _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (fcase _ _ _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (fcase _ _ _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (fcase0 _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (fcase0 _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (fcase0 _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))
trstk?-red-p {d = (psplit _ _)} (ξ-hreflᶜ rc) h = stablecd?-red rc h
trstk?-red-p {d = (psplit _ _)} (ξ-hreflᵃ ra) h = h
trstk?-red-p {d = (psplit _ _)} (hrefl-pw C₀ s₀ kp) h = ⊥-elim (f≢t (trans (sym (pw⊥dead C₀ kp)) h))

apstk?-red* : {t t' : RTm Γ} → t ⟶* t' → apstk? t ≡ true → apstk? t' ≡ true
apstk?-red* done h       = h
apstk?-red* (step r q) h = apstk?-red* q (apstk?-red r h)

natstk?-red* : {t t' : RTm Γ} → t ⟶* t' → natstk? t ≡ true → natstk? t' ≡ true
natstk?-red* done h       = h
natstk?-red* (step r q) h = natstk?-red* q (natstk?-red r h)

mustk?-red* : {t t' : RTm Γ} → t ⟶* t' → mustk? t ≡ true → mustk? t' ≡ true
mustk?-red* done h       = h
mustk?-red* (step r q) h = mustk?-red* q (mustk?-red r h)

dstk?-red* : {t t' : RTm Γ} → t ⟶* t' → dstk? t ≡ true → dstk? t' ≡ true
dstk?-red* done h       = h
dstk?-red* (step r q) h = dstk?-red* q (dstk?-red r h)

finstk?-red* : {t t' : RTm Γ} → t ⟶* t' → finstk? t ≡ true → finstk? t' ≡ true
finstk?-red* done h       = h
finstk?-red* (step r q) h = finstk?-red* q (finstk?-red r h)

-- ★★ WF stage E: the multi-step closures, one per BOUND.  `wne` needs
-- all three, composed in `ordstk?`'s own dispatch order.
-- ⚠ every implicit is bound at the recursive call, per the standing
-- meta-leak rule for the `ordstk?` family.
ordstk?-red*ᵃ : {a a' t u : RTm Γ} → a ⟶* a' →
                ordstk? a t u ≡ true → ordstk? a' t u ≡ true
ordstk?-red*ᵃ {t = t} {u = u} done       h = h
ordstk?-red*ᵃ {a = a} {t = t} {u = u} (step {u = b} r w) h =
  ordstk?-red*ᵃ {a = b} {t = t} {u = u} w
    (ordstk?-redᵃ {a = a} {a' = b} {t = t} {u = u} r h)

ordstk?-red*ᵗ : {a t t' u : RTm Γ} → t ⟶* t' →
                ordstk? a t u ≡ true → ordstk? a t' u ≡ true
ordstk?-red*ᵗ {a = a} {u = u} done       h = h
ordstk?-red*ᵗ {a = a} {t = t} {u = u} (step {u = b} r w) h =
  ordstk?-red*ᵗ {a = a} {t = b} {u = u} w
    (ordstk?-redᵗ {a = a} {t = t} {t' = b} {u = u} r h)

ordstk?-red*ᵘ : {a t u u' : RTm Γ} → u ⟶* u' →
                ordstk? a t u ≡ true → ordstk? a t u' ≡ true
ordstk?-red*ᵘ {a = a} {t = t} done       h = h
ordstk?-red*ᵘ {a = a} {t = t} {u = u} (step {u = b} r w) h =
  ordstk?-red*ᵘ {a = a} {t = t} {u = b} w
    (ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = b} r h)

------------------------------------------------------------------------
-- ★★ WF stage B: the ORDER-HOM stuckness key.  `Hom Nat a b` fires a
-- root rule exactly when its endpoints expose numeral heads, so it is
-- PERMANENTLY stuck exactly when they never will — and stage A's
-- `natstk?` already says that.  The key is therefore three lines: a
-- `nzero` left endpoint always fires, a `nsuc` left endpoint defers to
-- the right one, and any other left endpoint decides it alone.
------------------------------------------------------------------------

homnat? : RTm Γ → RTm Γ → 𝔹
homnat? nzero    u = false
homnat? (nsuc m) u = natstk? u
homnat? t        u = natstk? t

-- a term that never becomes a numeral is never a numeral, so it makes
-- the order-hom stuck on its own.
natstk→homnat : (t u : RTm Γ) → natstk? t ≡ true → homnat? t u ≡ true
natstk→homnat (var x) u h        = h
natstk→homnat (lam t) u h        = h
natstk→homnat (app t₁ t₂) u h    = h
natstk→homnat (pair a b) u h     = h
natstk→homnat (absurd c t) u h        = h
natstk→homnat (ordtr a₀ t₀ u₀ p₀ q₀) u h = h
natstk→homnat (fst t) u h        = h
natstk→homnat (snd t) u h        = h
natstk→homnat ⌜base⌝ u h         = h
natstk→homnat ⌜Nat⌝ u h = h
natstk→homnat ⌜Unit⌝ u h = h
natstk→homnat (⌜Π⌝ c d) u h      = h
natstk→homnat (⌜Σ⌝ c d) u h      = h
natstk→homnat (⌜Hom⌝ c a b) u h  = h
natstk→homnat (⌜Id⌝ c a b) u h   = h
natstk→homnat (hrefl c t) u h    = h
natstk→homnat (idrefl c t) u h   = h
natstk→homnat (tr d p e) u h     = h
natstk→homnat (ap c b p) u h     = h
natstk→homnat (jsub d p e) u h   = h
natstk→homnat unit u h           = h
natstk→homnat nzero u ()
natstk→homnat (nsuc n) u ()
natstk→homnat (natrec z w n) u h = h
natstk→homnat (⌜IMu⌝ Dˣ Iˣ iˣ) u h = h
natstk→homnat (ielim D iˣ ms t) u h = h
natstk→homnat (con _) u h           = h
natstk→homnat (⌜Fin⌝ _) u h           = h
natstk→homnat (dι _) u h           = h
natstk→homnat (dσ _ _) u h           = h
natstk→homnat (dρ _ _) u h           = h
natstk→homnat (dpay _ _ _ _) u h           = h
natstk→homnat (dih _ _ _ _) u h           = h
natstk→homnat fzero u h           = h
natstk→homnat (fsuc _) u h           = h
natstk→homnat (fcase _ _ _) u h           = h
natstk→homnat (fcase0 _) u h           = h
natstk→homnat (psplit _ _) u h           = h

-- ★★ WF stage E: the `natstk→homnat` peer.  A bound that never becomes a
-- numeral makes the ORDER stuck on its own — and this is the lemma that
-- lets `sn-ordtr` build `sne-ordtr`'s key from a NEUTRAL bound, where
-- `ordstk?` is stuck and cannot be handed `natstk?`'s answer directly.
natstk→ordstk : (a t u : RTm Γ) → natstk? a ≡ true → ordstk? a t u ≡ true
natstk→ordstk (var x) t u h = h
natstk→ordstk (lam t₀) t u h = h
natstk→ordstk (app t₀ t₁) t u h = h
natstk→ordstk (pair a₀ b₀) t u h = h
natstk→ordstk (absurd c e) t u h = h
natstk→ordstk (ordtr a₀ t₀ u₀ p₀ q₀) t u h = h
natstk→ordstk (fst t₀) t u h = h
natstk→ordstk (snd t₀) t u h = h
natstk→ordstk ⌜base⌝ t u h = h
natstk→ordstk ⌜Nat⌝ t u h = h
natstk→ordstk ⌜Unit⌝ t u h = h
natstk→ordstk (⌜Π⌝ c d) t u h = h
natstk→ordstk (⌜Σ⌝ c d) t u h = h
natstk→ordstk (⌜Hom⌝ c a₀ b₀) t u h = h
natstk→ordstk (⌜Id⌝ c a₀ b₀) t u h = h
natstk→ordstk (hrefl c t₀) t u h = h
natstk→ordstk (idrefl c t₀) t u h = h
natstk→ordstk (tr d p₀ e) t u h = h
natstk→ordstk (ap c b₀ p₀) t u h = h
natstk→ordstk (jsub d p₀ e) t u h = h
natstk→ordstk unit t u h = h
natstk→ordstk (natrec z w n) t u h = h
natstk→ordstk (⌜IMu⌝ Dˣ Iˣ iˣ) t u h = h
natstk→ordstk (ielim D iˣ ms t₀) t u h = h
natstk→ordstk nzero t u ()
natstk→ordstk (nsuc n) t u ()
natstk→ordstk (con _) t u h = h
natstk→ordstk (⌜Fin⌝ _) t u h = h
natstk→ordstk (dι _) t u h = h
natstk→ordstk (dσ _ _) t u h = h
natstk→ordstk (dρ _ _) t u h = h
natstk→ordstk (dpay _ _ _ _) t u h = h
natstk→ordstk (dih _ _ _ _) t u h = h
natstk→ordstk fzero t u h = h
natstk→ordstk (fsuc _) t u h = h
natstk→ordstk (fcase _ _ _) t u h = h
natstk→ordstk (fcase0 _) t u h = h
natstk→ordstk (psplit _ _) t u h = h

homnat?-redˡ : {t t' u : RTm Γ} → t ⟶ t' →
               homnat? t u ≡ true → homnat? t' u ≡ true
homnat?-redˡ {t = nzero} r ()
homnat?-redˡ {t = nsuc m} (ξ-nsuc r) h = h
homnat?-redˡ {t = var x} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = lam t} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = app t₁ t₂} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = pair a b} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = absurd c t} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = ordtr a₀ t₀ u₀ p₀ q₀} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = fst t} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = snd t} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = ⌜base⌝} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = ⌜Π⌝ c d} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = ⌜Σ⌝ c d} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = ⌜Hom⌝ c a b} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = ⌜Id⌝ c a b} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = hrefl c t} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = idrefl c t} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = tr d p e} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = ap c b p} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = jsub d p e} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = unit} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = natrec z w n} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = ielim D iˣ ms t₀} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = ⌜IMu⌝ Dˣ Iˣ iˣ} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (con _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (ielim _ _ _ _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (⌜IMu⌝ _ _ _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (⌜Fin⌝ _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (dι _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (dσ _ _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (dρ _ _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (dpay _ _ _ _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (dih _ _ _ _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = fzero} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (fsuc _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (fcase _ _ _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (fcase0 _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)
homnat?-redˡ {t = (psplit _ _)} {t' = t'} {u = u} r h = natstk→homnat t' u (natstk?-red r h)

homnat?-redʳ : {t u u' : RTm Γ} → u ⟶ u' →
               homnat? t u ≡ true → homnat? t u' ≡ true
homnat?-redʳ {t = nzero} r ()
homnat?-redʳ {t = nsuc m} r h       = natstk?-red r h
homnat?-redʳ {t = var x} r h        = h
homnat?-redʳ {t = lam t} r h        = h
homnat?-redʳ {t = app t₁ t₂} r h    = h
homnat?-redʳ {t = pair a b} r h     = h
homnat?-redʳ {t = absurd c t} r h        = h
homnat?-redʳ {t = ordtr a₀ t₀ u₀ p₀ q₀} r h = h
homnat?-redʳ {t = fst t} r h        = h
homnat?-redʳ {t = snd t} r h        = h
homnat?-redʳ {t = ⌜base⌝} r h       = h
homnat?-redʳ {t = ⌜Nat⌝} r h        = h
homnat?-redʳ {t = ⌜Unit⌝} r h       = h
homnat?-redʳ {t = ⌜Π⌝ c d} r h      = h
homnat?-redʳ {t = ⌜Σ⌝ c d} r h      = h
homnat?-redʳ {t = ⌜Hom⌝ c a b} r h  = h
homnat?-redʳ {t = ⌜Id⌝ c a b} r h   = h
homnat?-redʳ {t = hrefl c t} r h    = h
homnat?-redʳ {t = idrefl c t} r h   = h
homnat?-redʳ {t = tr d p e} r h     = h
homnat?-redʳ {t = ap c b p} r h     = h
homnat?-redʳ {t = jsub d p e} r h   = h
homnat?-redʳ {t = unit} r h         = h
homnat?-redʳ {t = natrec z w n} r h = h
homnat?-redʳ {t = ielim D iˣ ms t₀} r h = h
homnat?-redʳ {t = ⌜IMu⌝ Dˣ Iˣ iˣ} r h = h
homnat?-redʳ {t = (con _)} r h         = h
homnat?-redʳ {t = (ielim _ _ _ _)} r h         = h
homnat?-redʳ {t = (⌜IMu⌝ _ _ _)} r h         = h
homnat?-redʳ {t = (⌜Fin⌝ _)} r h         = h
homnat?-redʳ {t = (dι _)} r h         = h
homnat?-redʳ {t = (dσ _ _)} r h         = h
homnat?-redʳ {t = (dρ _ _)} r h         = h
homnat?-redʳ {t = (dpay _ _ _ _)} r h         = h
homnat?-redʳ {t = (dih _ _ _ _)} r h         = h
homnat?-redʳ {t = fzero} r h         = h
homnat?-redʳ {t = (fsuc _)} r h         = h
homnat?-redʳ {t = (fcase _ _ _)} r h         = h
homnat?-redʳ {t = (fcase0 _)} r h         = h
homnat?-redʳ {t = (psplit _ _)} r h         = h

idstk?-red* : {t t' : RTm Γ} → t ⟶* t' → idstk? t ≡ true → idstk? t' ≡ true
idstk?-red* done h       = h
idstk?-red* (step r q) h = idstk?-red* q (idstk?-red r h)

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
  -- ★★ WF-axis stage D: EX FALSO IS A NEUTRAL, and permanently so —
  -- its scrutinee lives at `base`, which has no canonical forms, so no
  -- rule can ever fire.  This is what puts `absurd c e` in EVERY type's
  -- interpretation via CR3, which is exactly the semantics ex falso
  -- should have.
  sne-absurd : {c e : RTm Γ} → SN c → SN e → SNe (absurd c e)
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
  -- ★ the two-former kernel: a PERMANENTLY STUCK `jsub` is neutral.
  sne-jsub : {d : RTm (Γ ∙)} {p e : RTm Γ} →
             SN d → SN p → SN e → idstk? p ≡ true → SNe (jsub d p e)
  -- ★ WF stage A: a `natrec` whose SCRUTINEE never becomes a numeral
  -- is neutral — the same shape as the other eliminators' keys.
  sne-natrec : {z : RTm Γ} {w : RTm ((Γ ∙) ∙)} {n : RTm Γ} →
               SN z → SN w → SN n → natstk? n ≡ true →
               SNe (natrec z w n)
  -- ★★ WF stage E: `ordtr` eliminates its three BOUNDS, so it is neutral
  -- exactly when `ordstk?` says they can never all become numerals.
  -- ⚠ it is NOT `sne-absurd`: ex falso has no root rule and so needs no
  -- key, whereas `ordtr` FIRES, and a keyless constructor would let a
  -- redex claim to be neutral.  The proofs are the payload, not the
  -- scrutinee, so they only ride along as `SN`.
  sne-ordtr : {a t u p q : RTm Γ} →
              SN a → SN t → SN u → SN p → SN q → ordstk? a t u ≡ true →
              SNe (ordtr a t u p q)
  -- ★★ LEVITATED FAMILIES: an eliminator whose SCRUTINEE can never become
  --   its constructor is neutral — `sne-natrec`'s shape, one key per
  --   eliminator (`mustk?` for `con`, `dstk?` for a telescope head,
  --   `finstk?` for a tag).  Everything else rides along as `SN`.
  sne-ielim : {D i e t : RTm Γ} →
              SN D → SN i → SN e → SN t → mustk? t ≡ true → SNe (ielim D i e t)
  sne-dpay  : {I D C i : RTm Γ} →
              SN I → SN D → SN C → SN i → dstk? C ≡ true → SNe (dpay I D C i)
  sne-dih   : {D e C p : RTm Γ} →
              SN D → SN e → SN C → SN p → dstk? C ≡ true → SNe (dih D e C p)
  sne-fcase : {t a : RTm Γ} {b : RTm (Γ ∙)} →
              SN t → SN a → SN b → finstk? t ≡ true → SNe (fcase t a b)
  -- the EMPTY tag's eliminator has no rule at all: `sne-absurd`'s shape.
  sne-fcase0 : {t : RTm Γ} → SN t → SNe (fcase0 t)
  -- Σ-induction is `fst`/`snd`'s peer: stuck on a neutral pair.
  sne-psplit : {b : RTm ((Γ ∙) ∙)} {q : RTm Γ} → SN b → SNe q → SNe (psplit b q)

data SN {Γ} where
  sn-ne   : {t : RTm Γ} → SNe t → SN t
  sn-lam  : {t : RTm (Γ ∙)} → SN t → SN (lam t)
  sn-pair : {a b : RTm Γ} → SN a → SN b → SN (pair a b)
  sn-cb   : SN (⌜base⌝ {Γ})
  sn-cΠ   : {c : RTm Γ} {d : RTm (Γ ∙)} → SN c → SN d → SN (⌜Π⌝ c d)
  sn-cΣ   : {c : RTm Γ} {d : RTm (Γ ∙)} → SN c → SN d → SN (⌜Σ⌝ c d)
  sn-cH   : {c a b : RTm Γ} → SN c → SN a → SN b → SN (⌜Hom⌝ c a b)
  sn-cId  : {c a b : RTm Γ} → SN c → SN a → SN b → SN (⌜Id⌝ c a b)
  sn-idrefl : {c t : RTm Γ} → SN c → SN t → SN (idrefl c t)
  -- ★ WF stage A: the datatype constructors are SN-inert.
  -- ★ WF stage C: so are the datatype CODES — inert canonical codes,
  -- exactly like `⌜base⌝`.
  sn-cNat   : SN (⌜Nat⌝ {Γ})
  sn-cUnit  : SN (⌜Unit⌝ {Γ})
  -- ⚠ `⌜IMu⌝` carries three TERMS, so it is SN only when they are.
  sn-cIMu   : {I D i : RTm Γ} → SN I → SN D → SN i → SN (⌜IMu⌝ I D i)
  sn-cFin   : {n : ℕ} → SN (⌜Fin⌝ {Γ} n)
  sn-unit   : SN (unit {Γ})
  sn-nzero  : SN (nzero {Γ})
  sn-nsuc   : {n : RTm Γ} → SN n → SN (nsuc n)
  -- ★ LEVITATED FAMILIES: the constructor, the telescope formers and the
  --   tags are SN-inert, like `nsuc`.
  sn-con    : {p : RTm Γ} → SN p → SN (con p)
  sn-dι     : {j : RTm Γ} → SN j → SN (dι j)
  sn-dσ     : {S f : RTm Γ} → SN S → SN f → SN (dσ S f)
  sn-dρ     : {j C : RTm Γ} → SN j → SN C → SN (dρ j C)
  sn-fzero  : SN (fzero {Γ})
  sn-fsuc   : {t : RTm Γ} → SN t → SN (fsuc t)
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
  -- ★ WF stage C: J at ⌜Unit⌝, the `snr-J-base` shape verbatim.  ⚠ there
  -- is deliberately no ⌜Nat⌝ peer — J is off there, so a `hrefl ⌜Nat⌝`
  -- path is NEUTRAL, not a redex (`stablecd? ⌜Nat⌝ = true`).
  snr-J-Unit : {c a m : RTm (Γ ∙)} {s e : RTm Γ} →
               SN (⌜Hom⌝ c a m) → SN s →
               SNRed (tr (⌜Hom⌝ c a m) (hrefl ⌜Unit⌝ s) e) e
  -- ★ §10.4's SN-layer obligation: `⌜IMu⌝` and `⌜Fin⌝` are `stkC?`, so J
  --   fires — `snr-J-Unit`'s shape.
  snr-J-IMu  : {Iⁱ Dⁱ iˣ : RTm Γ} {c a m : RTm (Γ ∙)} {s e : RTm Γ} →
               SN (⌜Hom⌝ c a m) → SN s →
               SNRed (tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ Iⁱ Dⁱ iˣ) s) e) e
  snr-J-Fin  : {n : ℕ} {c a m : RTm (Γ ∙)} {s e : RTm Γ} →
               SN (⌜Hom⌝ c a m) → SN s →
               SNRed (tr (⌜Hom⌝ c a m) (hrefl (⌜Fin⌝ n) s) e) e
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
  -- ★ the two-former kernel: `jsub` eliminates the path; the unkeyed J
  -- discards the motive and the reflexivity's pieces (carried as SN).
  snr-jsub-refl : {d : RTm (Γ ∙)} {c s e : RTm Γ} →
                  SN d → SN c → SN s →
                  SNRed (jsub d (idrefl c s) e) e
  snr-jsubᵖ  : {d : RTm (Γ ∙)} {p p' e : RTm Γ} → SNRed p p' →
               SNRed (jsub d p e) (jsub d p' e)
  -- ★ WF stage A: the recursor eliminates its SCRUTINEE; the numeral
  -- rules discard the unused branch (carried as SN, the snr-β pattern).
  snr-natrec-zero : {z : RTm Γ} {w : RTm ((Γ ∙) ∙)} →
                    SN w → SNRed (natrec z w nzero) z
  snr-natrec-suc  : {z : RTm Γ} {w : RTm ((Γ ∙) ∙)} {n : RTm Γ} →
                    SN z → SN w → SN n →
                    SNRed (natrec z w (nsuc n))
                          (subTm (single (natrec z w n))
                                 (subTm (extS (single n)) w))
  snr-natrecⁿ : {z : RTm Γ} {w : RTm ((Γ ∙) ∙)} {n n' : RTm Γ} →
                SNRed n n' → SNRed (natrec z w n) (natrec z w n')
  -- ★★ LEVITATED FAMILIES: each root rule, plus ONE ξ for its scrutinee
  --   (weak head — the other slots are CARRIED, and their normalisation is
  --   the neutral's `SN` premises).  One ξ per eliminator keeps `snr-det`
  --   true (the old index-ξ made it false).  The root rules carry the SN
  --   of what they DISCARD (the `snr-β` pattern); ι discards nothing but
  --   carries its parts, as the old `snr-ιi` did.
  snr-ι      : {D i e p : RTm Γ} → SN D → SN i → SN e → SN p →
               SNRed (ielim D i e (con p)) (app (app (app e i) p) (dih D e D p))
  snr-ielimᵗ : {D i e t t' : RTm Γ} →
               SNRed t t' → SNRed (ielim D i e t) (ielim D i e t')
  snr-dpay-ι : {I D j i : RTm Γ} → SN D →
               SNRed (dpay I D (dι j) i) (⌜Id⌝ I j i)
  snr-dpay-σ : {I D S f i : RTm Γ} →
               SNRed (dpay I D (dσ S f) i)
                     (⌜Σ⌝ S (dpay (renTm vs I) (renTm vs D) (app (renTm vs f) (var vz)) (renTm vs i)))
  snr-dpay-ρ : {I D j C i : RTm Γ} →
               SNRed (dpay I D (dρ j C) i)
                     (⌜Σ⌝ (⌜IMu⌝ I D j) (dpay (renTm vs I) (renTm vs D) (renTm vs C) (renTm vs i)))
  snr-dpayᶜ  : {I D C C' i : RTm Γ} → SNRed C C' → SNRed (dpay I D C i) (dpay I D C' i)
  snr-dih-ι  : {D e j p : RTm Γ} → SN D → SN e → SN j → SN p →
               SNRed (dih D e (dι j) p) unit
  snr-dih-σ  : {D e S f p : RTm Γ} → SN S →
               SNRed (dih D e (dσ S f) p) (dih D e (app f (fst p)) (snd p))
  snr-dih-ρ  : {D e j C p : RTm Γ} →
               SNRed (dih D e (dρ j C) p) (pair (ielim D j e (fst p)) (dih D e C (snd p)))
  snr-dihᶜ   : {D e C C' p : RTm Γ} → SNRed C C' → SNRed (dih D e C p) (dih D e C' p)
  snr-fcase-z : {a : RTm Γ} {b : RTm (Γ ∙)} → SN b → SNRed (fcase fzero a b) a
  snr-fcase-s : {t a : RTm Γ} {b : RTm (Γ ∙)} → SN t → SN a →
                SNRed (fcase (fsuc t) a b) (subTm (single t) b)
  snr-fcaseᵗ : {t t' a : RTm Γ} {b : RTm (Γ ∙)} → SNRed t t' →
               SNRed (fcase t a b) (fcase t' a b)
  snr-psplit-β : {b : RTm ((Γ ∙) ∙)} {x y : RTm Γ} → SN x → SN y →
                 SNRed (psplit b (pair x y)) (subTm (single2 x y) b)
  snr-psplitᵍ : {b : RTm ((Γ ∙) ∙)} {q q' : RTm Γ} → SNRed q q' →
                SNRed (psplit b q) (psplit b q')
  -- ★★ WF stage E: the order's five root rules, each discarding the
  -- material it drops as `SN` (the `snr-β` pattern), plus one ξ per
  -- BOUND.  Three scrutinees, so three ξ's — `p`/`q` are payload and
  -- never step here, exactly as `snr-app` leaves its argument alone.
  snr-ordtr-z   : {t u p q : RTm Γ} → SN t → SN u → SN p → SN q →
                  SNRed (ordtr nzero t u p q) unit
  snr-ordtr-szz : {a p q : RTm Γ} → SN a → SN q →
                  SNRed (ordtr (nsuc a) nzero nzero p q) p
  snr-ordtr-ssz : {a t p q : RTm Γ} → SN a → SN t → SN p →
                  SNRed (ordtr (nsuc a) (nsuc t) nzero p q) q
  -- ★ stage D's first real customer: `nzero ≤ nsuc u` under a `nsuc`
  -- bound is impossible, and `absurd` at the ⌜Hom⌝ code discharges it.
  snr-ordtr-szs : {a u p q : RTm Γ} → SN q →
                  SNRed (ordtr (nsuc a) nzero (nsuc u) p q)
                        (absurd (⌜Hom⌝ ⌜Nat⌝ a u) p)
  snr-ordtr-sss : {a t u p q : RTm Γ} →
                  SNRed (ordtr (nsuc a) (nsuc t) (nsuc u) p q)
                        (ordtr a t u p q)
  -- ⚠⚠ the ξ's must be SERIALIZED, or `snr-det` is FALSE: with three
  -- scrutinees, `ordtr (app (lam s) v) (app (lam s') v') u p q` would
  -- head-step two ways.  So each ξ demands that the bounds BEFORE it
  -- already expose a numeral head — and `nzero`/`nsuc` have no `SNRed`
  -- step, which is exactly what makes the cases pairwise absurd.
  -- The order is `ordstk?`'s own dispatch order: `a`, then `t`, then `u`.
  snr-ordtrᵃ : {a a' t u p q : RTm Γ} → SNRed a a' →
               SNRed (ordtr a t u p q) (ordtr a' t u p q)
  snr-ordtrᵗ : {a t t' u p q : RTm Γ} → SNRed t t' →
               SNRed (ordtr (nsuc a) t u p q) (ordtr (nsuc a) t' u p q)
  snr-ordtrᵘᶻ : {a u u' p q : RTm Γ} → SNRed u u' →
                SNRed (ordtr (nsuc a) nzero u p q)
                      (ordtr (nsuc a) nzero u' p q)
  snr-ordtrᵘˢ : {a t u u' p q : RTm Γ} → SNRed u u' →
                SNRed (ordtr (nsuc a) (nsuc t) u p q)
                      (ordtr (nsuc a) (nsuc t) u' p q)
  -- J at `⌜Id⌝`-coded hrefl paths (the stable-shape completion).
  snr-J-Id   : {c a m : RTm (Γ ∙)} {c₁ a₁ b₁ s e : RTm Γ} →
               SN (⌜Hom⌝ c a m) → SN c₁ → SN a₁ → SN b₁ → SN s →
               SNRed (tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e) e
  -- W2b: J at stable ⌜Hom⌝ codes and pointwise transport (discarded
  -- material carried as SN, the snr-β pattern; tr-pw's SN c covers the
  -- ⌜Π⌝-domain that pwBody drops).
  snr-J-Hom  : {c a m : RTm (Γ ∙)} {c₁ a₁ b₁ s e : RTm Γ} →
               SN (⌜Hom⌝ c a m) → SN c₁ → SN a₁ → SN b₁ → SN s →
               stkA? c₁ ≡ true →
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
snr→⟶ (snr-J-Unit _ _)     = tr-J-Unit _ _ _ _ _
snr→⟶ (snr-J-IMu _ _)      = tr-J-IMu _ _ _ _ _
snr→⟶ (snr-J-Fin _ _)      = tr-J-Fin _ _ _ _ _
snr→⟶ (snr-J-Σ _ _ _ _)    = tr-J-Σ _ _ _ _ _ _ _
snr→⟶ snr-taut             = tr-taut _ _
snr→⟶ (snr-trᵖ r)          = ξ-trᵖ (snr→⟶ r)
snr→⟶ (snr-hrefl-pw key)   = hrefl-pw _ _ key
snr→⟶ (snr-J-Hom _ _ _ _ _ key) = tr-J-Hom _ _ _ _ _ _ _ _ key
snr→⟶ (snr-tr-pw _ _ key)  = tr-pw _ _ _ _ key
snr→⟶ (snr-tr-mot σ)       = ξ-trᵈ (ξ-⌜Hom⌝ᶜ (csr→⟶ σ))
snr→⟶ (snr-ap-J _ key)     = ap-J _ _ _ _ key
snr→⟶ (snr-apᵖ r)          = ξ-apᵖ (snr→⟶ r)
snr→⟶ (snr-jsub-refl _ _ _) = jsub-refl _ _ _ _
snr→⟶ (snr-jsubᵖ r)        = ξ-jsubᵖ (snr→⟶ r)
snr→⟶ (snr-J-Id _ _ _ _ _) = tr-J-Id _ _ _ _ _ _ _ _
snr→⟶ (snr-natrec-zero _)      = natrec-zero _ _
snr→⟶ (snr-natrec-suc _ _ _)   = natrec-suc _ _ _
snr→⟶ (snr-natrecⁿ r)          = ξ-natrecⁿ (snr→⟶ r)
snr→⟶ (snr-ι _ _ _ _) = ι _ _ _ _
snr→⟶ (snr-ielimᵗ r) = ξ-ielimᵗ (snr→⟶ r)
snr→⟶ (snr-dpay-ι _) = dpay-ι _ _ _ _
snr→⟶ snr-dpay-σ = dpay-σ _ _ _ _ _
snr→⟶ snr-dpay-ρ = dpay-ρ _ _ _ _ _
snr→⟶ (snr-dpayᶜ r) = ξ-dpayᶜ (snr→⟶ r)
snr→⟶ (snr-dih-ι _ _ _ _) = dih-ι _ _ _ _
snr→⟶ (snr-dih-σ _) = dih-σ _ _ _ _ _
snr→⟶ snr-dih-ρ = dih-ρ _ _ _ _ _
snr→⟶ (snr-dihᶜ r) = ξ-dihᶜ (snr→⟶ r)
snr→⟶ (snr-fcase-z _) = fcase-z _ _
snr→⟶ (snr-fcase-s _ _) = fcase-s _ _ _
snr→⟶ (snr-fcaseᵗ r) = ξ-fcaseᵗ (snr→⟶ r)
snr→⟶ (snr-psplit-β _ _) = psplit-β _ _ _
snr→⟶ (snr-psplitᵍ r) = ξ-psplitᵍ (snr→⟶ r)
snr→⟶ (snr-ordtr-z _ _ _ _)    = ordtr-z _ _ _ _
snr→⟶ (snr-ordtr-szz _ _)      = ordtr-szz _ _ _
snr→⟶ (snr-ordtr-ssz _ _ _)    = ordtr-ssz _ _ _ _
snr→⟶ (snr-ordtr-szs _)        = ordtr-szs _ _ _ _
snr→⟶ snr-ordtr-sss            = ordtr-sss _ _ _ _ _
snr→⟶ (snr-ordtrᵃ r)           = ξ-ordtrᵃ (snr→⟶ r)
snr→⟶ (snr-ordtrᵗ r)           = ξ-ordtrᵗ (snr→⟶ r)
snr→⟶ (snr-ordtrᵘᶻ r)          = ξ-ordtrᵘ (snr→⟶ r)
snr→⟶ (snr-ordtrᵘˢ r)          = ξ-ordtrᵘ (snr→⟶ r)

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
snr-nonpw (snr-J-Unit _ _)  = refl
snr-nonpw (snr-J-IMu _ _)   = refl
snr-nonpw (snr-J-Fin _ _)   = refl
snr-nonpw (snr-J-Σ _ _ _ _) = refl
snr-nonpw (snr-J-Hom _ _ _ _ _ _) = refl
snr-nonpw snr-taut       = refl
snr-nonpw (snr-trᵖ _)    = refl
snr-nonpw (snr-tr-pw _ _ _) = refl
snr-nonpw (snr-tr-mot _)    = refl
snr-nonpw (snr-ap-J _ _)    = refl
snr-nonpw (snr-apᵖ _)       = refl
snr-nonpw (snr-jsub-refl _ _ _) = refl
snr-nonpw (snr-jsubᵖ _)     = refl
snr-nonpw (snr-J-Id _ _ _ _ _) = refl
snr-nonpw (snr-natrec-zero _)     = refl
snr-nonpw (snr-natrec-suc _ _ _)  = refl
snr-nonpw (snr-natrecⁿ _)         = refl
snr-nonpw (snr-ι _ _ _ _) = refl
snr-nonpw (snr-ielimᵗ _) = refl
snr-nonpw (snr-dpay-ι _) = refl
snr-nonpw snr-dpay-σ = refl
snr-nonpw snr-dpay-ρ = refl
snr-nonpw (snr-dpayᶜ _) = refl
snr-nonpw (snr-dih-ι _ _ _ _) = refl
snr-nonpw (snr-dih-σ _) = refl
snr-nonpw snr-dih-ρ = refl
snr-nonpw (snr-dihᶜ _) = refl
snr-nonpw (snr-fcase-z _) = refl
snr-nonpw (snr-fcase-s _ _) = refl
snr-nonpw (snr-fcaseᵗ _) = refl
snr-nonpw (snr-psplit-β _ _) = refl
snr-nonpw (snr-psplitᵍ _) = refl
snr-nonpw (snr-ordtr-z _ _ _ _)   = refl
snr-nonpw (snr-ordtr-szz _ _)     = refl
snr-nonpw (snr-ordtr-ssz _ _ _)   = refl
snr-nonpw (snr-ordtr-szs _)       = refl
snr-nonpw snr-ordtr-sss           = refl
snr-nonpw (snr-ordtrᵃ _)          = refl
snr-nonpw (snr-ordtrᵗ _)          = refl
snr-nonpw (snr-ordtrᵘᶻ _)         = refl
snr-nonpw (snr-ordtrᵘˢ _)         = refl

csr-nonpw : {t t' : RTm Γ} → CSR t t' → pw? t ≡ false
csr-nonpw (csr-here r) = snr-nonpw r
csr-nonpw (csr-hom σ)  = csr-nonpw σ

-- a permanently-stable code has no spine step.
csr-stkA⊥ : {t t' : RTm Γ} → stkA? t ≡ true → CSR t t' → ⊥
csr-stkA⊥ {t = ⌜base⌝} k (csr-here ())
csr-stkA⊥ {t = ⌜Nat⌝} k (csr-here ())
csr-stkA⊥ {t = ⌜Unit⌝} k (csr-here ())
csr-stkA⊥ {t = ⌜IMu⌝ I D i} k (csr-here ())
csr-stkA⊥ {t = ⌜Fin⌝ n} k (csr-here ())
csr-stkA⊥ {t = ⌜Σ⌝ c d} k (csr-here ())
csr-stkA⊥ {t = ⌜Id⌝ c a b} k (csr-here ())
csr-stkA⊥ {t = ⌜Hom⌝ c a b} k (csr-here ())
csr-stkA⊥ {t = ⌜Hom⌝ c a b} k (csr-hom σ) = csr-stkA⊥ k σ
csr-stkA⊥ {t = var x} () _
csr-stkA⊥ {t = lam _} () _
csr-stkA⊥ {t = app _ _} () _
csr-stkA⊥ {t = pair _ _} () _
csr-stkA⊥ {t = fst _} () _
csr-stkA⊥ {t = snd _} () _
csr-stkA⊥ {t = ⌜Π⌝ _ _} () _
csr-stkA⊥ {t = hrefl _ _} () _

csr-stk⊥ : {t t' : RTm Γ} → stkC? t ≡ true → CSR t t' → ⊥
csr-stk⊥ {t = ⌜base⌝} k (csr-here ())
csr-stk⊥ {t = ⌜Σ⌝ c d} k (csr-here ())
csr-stk⊥ {t = ⌜Hom⌝ c a b} k (csr-here ())
csr-stk⊥ {t = ⌜Hom⌝ c a b} k (csr-hom σ) = csr-stkA⊥ k σ
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

-- `idrefl` has no head step, so a head step factors PAST any chain
-- reaching one — by determinism.
noSnrIdrefl : {Γ : Cx} {c s u : RTm Γ} → SNRed (idrefl c s) u → ⊥
noSnrIdrefl ()

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
snr-det (snr-J-Unit _ _) (snr-J-Unit _ _) = refl
snr-det (snr-J-Fin _ _) (snr-J-Fin _ _) = refl
snr-det (snr-J-IMu _ _) (snr-J-IMu _ _) = refl
snr-det (snr-J-Unit _ _) (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-det (snr-J-IMu _ _) (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-det (snr-J-Fin _ _) (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-det (snr-trᵖ (snr-hreflᶜ (csr-here ()))) (snr-J-Unit _ _)
snr-det (snr-trᵖ (snr-hreflᶜ (csr-here ()))) (snr-J-IMu _ _)
snr-det (snr-trᵖ (snr-hreflᶜ (csr-here ()))) (snr-J-Fin _ _)
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
  ⊥-elim (csr-stkA⊥ ks σ)
snr-det (snr-trᵖ (snr-hreflᶜ σ)) (snr-J-Hom {c₁ = c₁} _ _ _ _ _ ks) =
  ⊥-elim (csr-stkA⊥ ks σ)
snr-det (snr-J-Hom {c₁ = c₁} _ _ _ _ _ ks) (snr-trᵖ (snr-hrefl-pw kp))
  with trans (sym (stkA?⊥pw c₁ ks)) kp
... | ()
snr-det (snr-trᵖ (snr-hrefl-pw kp)) (snr-J-Hom {c₁ = c₁} _ _ _ _ _ ks)
  with trans (sym (stkA?⊥pw c₁ ks)) kp
... | ()
snr-det (snr-J-base _ _) (snr-trᵖ (snr-hrefl-pw ()))
snr-det (snr-trᵖ (snr-hrefl-pw ())) (snr-J-base _ _)
snr-det (snr-J-Unit _ _) (snr-trᵖ (snr-hrefl-pw ()))
snr-det (snr-J-IMu _ _) (snr-trᵖ (snr-hrefl-pw ()))
snr-det (snr-J-Fin _ _) (snr-trᵖ (snr-hrefl-pw ()))
snr-det (snr-trᵖ (snr-hrefl-pw ())) (snr-J-Unit _ _)
snr-det (snr-trᵖ (snr-hrefl-pw ())) (snr-J-IMu _ _)
snr-det (snr-trᵖ (snr-hrefl-pw ())) (snr-J-Fin _ _)
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
snr-det (snr-jsub-refl _ _ _) (snr-jsub-refl _ _ _) = refl
snr-det (snr-jsub-refl _ _ _) (snr-jsubᵖ r) = ⊥-elim (noSnrIdrefl r)
snr-det (snr-jsubᵖ r) (snr-jsub-refl _ _ _) = ⊥-elim (noSnrIdrefl r)
snr-det (snr-jsubᵖ r) (snr-jsubᵖ r') with snr-det r r'
... | refl = refl
snr-det (snr-J-Id _ _ _ _ _) (snr-J-Id _ _ _ _ _) = refl
snr-det (snr-J-Id _ _ _ _ _) (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-det (snr-trᵖ (snr-hreflᶜ (csr-here ()))) (snr-J-Id _ _ _ _ _)
snr-det (snr-J-Id _ _ _ _ _) (snr-trᵖ (snr-hrefl-pw ()))
snr-det (snr-trᵖ (snr-hrefl-pw ())) (snr-J-Id _ _ _ _ _)
-- ★ WF stage A: the recursor's rules are keyed on the numeral head, so
-- a firing rule and a scrutinee step can never overlap (`nzero`/`nsuc`
-- have no head step).
snr-det (snr-natrec-zero _) (snr-natrec-zero _)      = refl
snr-det (snr-natrec-zero _) (snr-natrecⁿ ())
snr-det (snr-natrecⁿ ()) (snr-natrec-zero _)
snr-det (snr-natrec-suc _ _ _) (snr-natrec-suc _ _ _) = refl
snr-det (snr-natrec-suc _ _ _) (snr-natrecⁿ ())
snr-det (snr-natrecⁿ ()) (snr-natrec-suc _ _ _)
-- ★★ LEVITATED FAMILIES: each eliminator has ONE root rule family and ONE
--   scrutinee ξ; they overlap only where the scrutinee is a constructor
--   (`con`, `dι`/`dσ`/`dρ`, `fzero`/`fsuc`, `pair`), and NO SNRed rule
--   steps a constructor — so every cross case is refuted definitionally.
snr-det (snr-ι _ _ _ _) (snr-ι _ _ _ _) = refl
snr-det (snr-ι _ _ _ _) (snr-ielimᵗ ())
snr-det (snr-ielimᵗ ()) (snr-ι _ _ _ _)
snr-det (snr-ielimᵗ {D = D} {i = i} {e = e} r) (snr-ielimᵗ r') =
  cong (λ q → ielim D i e q) (snr-det r r')
snr-det (snr-dpay-ι _) (snr-dpay-ι _) = refl
snr-det snr-dpay-σ snr-dpay-σ = refl
snr-det snr-dpay-ρ snr-dpay-ρ = refl
snr-det (snr-dpay-ι _) (snr-dpayᶜ ())
snr-det snr-dpay-σ (snr-dpayᶜ ())
snr-det snr-dpay-ρ (snr-dpayᶜ ())
snr-det (snr-dpayᶜ ()) (snr-dpay-ι _)
snr-det (snr-dpayᶜ ()) snr-dpay-σ
snr-det (snr-dpayᶜ ()) snr-dpay-ρ
snr-det (snr-dpayᶜ {I = I} {D = D} {i = i} r) (snr-dpayᶜ r') =
  cong (λ q → dpay I D q i) (snr-det r r')
snr-det (snr-dih-ι _ _ _ _) (snr-dih-ι _ _ _ _) = refl
snr-det (snr-dih-σ _) (snr-dih-σ _) = refl
snr-det snr-dih-ρ snr-dih-ρ = refl
snr-det (snr-dih-ι _ _ _ _) (snr-dihᶜ ())
snr-det (snr-dih-σ _) (snr-dihᶜ ())
snr-det snr-dih-ρ (snr-dihᶜ ())
snr-det (snr-dihᶜ ()) (snr-dih-ι _ _ _ _)
snr-det (snr-dihᶜ ()) (snr-dih-σ _)
snr-det (snr-dihᶜ ()) snr-dih-ρ
snr-det (snr-dihᶜ {D = D} {e = e} {p = p} r) (snr-dihᶜ r') =
  cong (λ q → dih D e q p) (snr-det r r')
snr-det (snr-fcase-z _) (snr-fcase-z _) = refl
snr-det (snr-fcase-s _ _) (snr-fcase-s _ _) = refl
snr-det (snr-fcase-z _) (snr-fcaseᵗ ())
snr-det (snr-fcase-s _ _) (snr-fcaseᵗ ())
snr-det (snr-fcaseᵗ ()) (snr-fcase-z _)
snr-det (snr-fcaseᵗ ()) (snr-fcase-s _ _)
snr-det (snr-fcaseᵗ {a = a} {b = b} r) (snr-fcaseᵗ r') =
  cong (λ q → fcase q a b) (snr-det r r')
snr-det (snr-psplit-β _ _) (snr-psplit-β _ _) = refl
snr-det (snr-psplit-β _ _) (snr-psplitᵍ ())
snr-det (snr-psplitᵍ ()) (snr-psplit-β _ _)
snr-det (snr-psplitᵍ {b = b} r) (snr-psplitᵍ r') =
  cong (psplit b) (snr-det r r')
snr-det (snr-natrecⁿ {z = z} {w = w} r) (snr-natrecⁿ r') =
  cong (λ q → natrec z w q) (snr-det r r')
-- ★★ WF stage E: `natrec`'s argument three times over.  Every cross
-- pair is refuted by an ABSURD `SNRed` out of a numeral — that is the
-- whole payoff of serializing the ξ's on the bound order, and the pairs
-- Agda does not even ask about are the ones `nzero`/`nsuc` separate.
snr-det (snr-ordtr-z _ _ _ _) (snr-ordtr-z _ _ _ _) = refl
snr-det (snr-ordtr-z _ _ _ _) (snr-ordtrᵃ ())
snr-det (snr-ordtrᵃ ()) (snr-ordtr-z _ _ _ _)
snr-det (snr-ordtr-szz _ _) (snr-ordtr-szz _ _) = refl
snr-det (snr-ordtr-szz _ _) (snr-ordtrᵃ ())
snr-det (snr-ordtr-szz _ _) (snr-ordtrᵗ ())
snr-det (snr-ordtr-szz _ _) (snr-ordtrᵘᶻ ())
snr-det (snr-ordtrᵃ ()) (snr-ordtr-szz _ _)
snr-det (snr-ordtrᵗ ()) (snr-ordtr-szz _ _)
snr-det (snr-ordtrᵘᶻ ()) (snr-ordtr-szz _ _)
snr-det (snr-ordtr-ssz _ _ _) (snr-ordtr-ssz _ _ _) = refl
snr-det (snr-ordtr-ssz _ _ _) (snr-ordtrᵃ ())
snr-det (snr-ordtr-ssz _ _ _) (snr-ordtrᵗ ())
snr-det (snr-ordtr-ssz _ _ _) (snr-ordtrᵘˢ ())
snr-det (snr-ordtrᵃ ()) (snr-ordtr-ssz _ _ _)
snr-det (snr-ordtrᵗ ()) (snr-ordtr-ssz _ _ _)
snr-det (snr-ordtrᵘˢ ()) (snr-ordtr-ssz _ _ _)
snr-det (snr-ordtr-szs _) (snr-ordtr-szs _) = refl
snr-det (snr-ordtr-szs _) (snr-ordtrᵃ ())
snr-det (snr-ordtr-szs _) (snr-ordtrᵗ ())
snr-det (snr-ordtr-szs _) (snr-ordtrᵘᶻ ())
snr-det (snr-ordtrᵃ ()) (snr-ordtr-szs _)
snr-det (snr-ordtrᵗ ()) (snr-ordtr-szs _)
snr-det (snr-ordtrᵘᶻ ()) (snr-ordtr-szs _)
snr-det snr-ordtr-sss snr-ordtr-sss = refl
snr-det snr-ordtr-sss (snr-ordtrᵃ ())
snr-det snr-ordtr-sss (snr-ordtrᵗ ())
snr-det snr-ordtr-sss (snr-ordtrᵘˢ ())
snr-det (snr-ordtrᵃ ()) snr-ordtr-sss
snr-det (snr-ordtrᵗ ()) snr-ordtr-sss
snr-det (snr-ordtrᵘˢ ()) snr-ordtr-sss
snr-det (snr-ordtrᵃ {t = t} {u = u} {p = p} {q = q} r) (snr-ordtrᵃ r') =
  cong (λ z → ordtr z t u p q) (snr-det r r')
snr-det (snr-ordtrᵃ ()) (snr-ordtrᵗ _)
snr-det (snr-ordtrᵗ _) (snr-ordtrᵃ ())
snr-det (snr-ordtrᵃ ()) (snr-ordtrᵘᶻ _)
snr-det (snr-ordtrᵘᶻ _) (snr-ordtrᵃ ())
snr-det (snr-ordtrᵃ ()) (snr-ordtrᵘˢ _)
snr-det (snr-ordtrᵘˢ _) (snr-ordtrᵃ ())
snr-det (snr-ordtrᵗ {a = a} {u = u} {p = p} {q = q} r) (snr-ordtrᵗ r') =
  cong (λ z → ordtr (nsuc a) z u p q) (snr-det r r')
snr-det (snr-ordtrᵗ ()) (snr-ordtrᵘᶻ _)
snr-det (snr-ordtrᵘᶻ _) (snr-ordtrᵗ ())
snr-det (snr-ordtrᵗ ()) (snr-ordtrᵘˢ _)
snr-det (snr-ordtrᵘˢ _) (snr-ordtrᵗ ())
snr-det (snr-ordtrᵘᶻ {a = a} {p = p} {q = q} r) (snr-ordtrᵘᶻ r') =
  cong (λ z → ordtr (nsuc a) nzero z p q) (snr-det r r')
snr-det (snr-ordtrᵘˢ {a = a} {t = t} {p = p} {q = q} r) (snr-ordtrᵘˢ r') =
  cong (λ z → ordtr (nsuc a) (nsuc t) z p q) (snr-det r r')

csr-det (csr-here r) (csr-here r') = snr-det r r'
csr-det (csr-here ()) (csr-hom σ')
csr-det (csr-hom σ) (csr-here ())
csr-det (csr-hom {a = a} {b = b} σ) (csr-hom σ') =
  cong (λ z → ⌜Hom⌝ z a b) (csr-det σ σ')

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
sne-whred (sne-tr snd₀ snp sne₀ ()) (snr-J-Unit _ _)
sne-whred (sne-tr snd₀ snp sne₀ ()) (snr-J-Σ _ _ _ _)
sne-whred (sne-tr snd₀ snp sne₀ ()) snr-taut
sne-whred (sne-tr snd₀ snp sne₀ key) (snr-J-Hom {c₁ = c₁} _ _ _ _ _ ks)
  with trans (sym (stkA?⊥dead c₁ ks)) key
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
sne-whred (sne-tr snd₀ snp sne₀ ()) (snr-J-Id _ _ _ _ _)
sne-whred (sne-jsub snd₀ snp sne₀ ()) (snr-jsub-refl _ _ _)
sne-whred (sne-jsub snd₀ snp sne₀ key) (snr-jsubᵖ r) =
  sne-jsub snd₀ (sn-whred snp r) sne₀ (idstk?-red (snr→⟶ r) key)
sne-whred (sne-natrec snz snw snn ()) (snr-natrec-zero _)
sne-whred (sne-natrec snz snw snn ()) (snr-natrec-suc _ _ _)
sne-whred (sne-natrec snz snw snn key) (snr-natrecⁿ r) =
  sne-natrec snz snw (sn-whred snn r) (natstk?-red (snr→⟶ r) key)
-- ★★ LEVITATED FAMILIES: every root rule is refuted DEFINITIONALLY — it
-- fires only on a constructor scrutinee, and the neutral's own key answers
-- `false` there.  The scrutinee ξ moves the key along (`X?-red`).
sne-whred (sne-ielim snD sni sne snt ()) (snr-ι _ _ _ _)
sne-whred (sne-ielim snD sni sne snt key) (snr-ielimᵗ r) =
  sne-ielim snD sni sne (sn-whred snt r) (mustk?-red (snr→⟶ r) key)
sne-whred (sne-dpay _ _ _ _ ()) (snr-dpay-ι _)
sne-whred (sne-dpay _ _ _ _ ()) snr-dpay-σ
sne-whred (sne-dpay _ _ _ _ ()) snr-dpay-ρ
sne-whred (sne-dpay snI snD snC sni key) (snr-dpayᶜ r) =
  sne-dpay snI snD (sn-whred snC r) sni (dstk?-red (snr→⟶ r) key)
sne-whred (sne-dih _ _ _ _ ()) (snr-dih-ι _ _ _ _)
sne-whred (sne-dih _ _ _ _ ()) (snr-dih-σ _)
sne-whred (sne-dih _ _ _ _ ()) snr-dih-ρ
sne-whred (sne-dih snD sne snC snp key) (snr-dihᶜ r) =
  sne-dih snD sne (sn-whred snC r) snp (dstk?-red (snr→⟶ r) key)
sne-whred (sne-fcase _ _ _ ()) (snr-fcase-z _)
sne-whred (sne-fcase _ _ _ ()) (snr-fcase-s _ _)
sne-whred (sne-fcase snt sna snb key) (snr-fcaseᵗ r) =
  sne-fcase (sn-whred snt r) sna snb (finstk?-red (snr→⟶ r) key)
sne-whred (sne-psplit snb ()) (snr-psplit-β _ _)
sne-whred (sne-psplit snb n) (snr-psplitᵍ r) = sne-psplit snb (sne-whred n r)
-- ★★ WF stage E: every root rule is refuted DEFINITIONALLY — each one
-- fires only on numeral bounds, and `natstk?` of a numeral is `false`,
-- so `ordstk?` computes to `false` and the key is `()`.
sne-whred (sne-ordtr _ _ _ _ _ ()) (snr-ordtr-z _ _ _ _)
sne-whred (sne-ordtr _ _ _ _ _ ()) (snr-ordtr-szz _ _)
sne-whred (sne-ordtr _ _ _ _ _ ()) (snr-ordtr-ssz _ _ _)
sne-whred (sne-ordtr _ _ _ _ _ ()) (snr-ordtr-szs _)
sne-whred (sne-ordtr _ _ _ _ _ ()) snr-ordtr-sss
-- ⚠ bind the implicits: bare `ordstk?-red*` leaks metas out of the row.
sne-whred (sne-ordtr {a = a} {t = t} {u = u} sna snt snu snp snq key)
          (snr-ordtrᵃ {a' = a'} r) =
  sne-ordtr (sn-whred sna r) snt snu snp snq
            (ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} (snr→⟶ r) key)
sne-whred (sne-ordtr {a = a} {t = t} {u = u} sna snt snu snp snq key)
          (snr-ordtrᵗ {t' = t'} r) =
  sne-ordtr sna (sn-whred snt r) snu snp snq
            (ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} (snr→⟶ r) key)
sne-whred (sne-ordtr {a = a} {t = t} {u = u} sna snt snu snp snq key)
          (snr-ordtrᵘᶻ {u' = u'} r) =
  sne-ordtr sna snt (sn-whred snu r) snp snq
            (ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} (snr→⟶ r) key)
sne-whred (sne-ordtr {a = a} {t = t} {u = u} sna snt snu snp snq key)
          (snr-ordtrᵘˢ {u' = u'} r) =
  sne-ordtr sna snt (sn-whred snu r) snp snq
            (ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} (snr→⟶ r) key)

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

-- ★ WF stage A: `Unit`/`Nat` are INERT type formers — no ⟶ᵀ rule has
-- them as a source, so their reduct is themselves.
Unit-nf : {A : RTy Γ} → Unit {Γ} ⟶ᵀ* A → A ≡ Unit
Unit-nf doneᵀ        = refl
Unit-nf (stepᵀ () _)

Nat-nf : {A : RTy Γ} → Nat {Γ} ⟶ᵀ* A → A ≡ Nat
Nat-nf doneᵀ        = refl
Nat-nf (stepᵀ () _)

-- ★ INDUCTIVE TYPES: `Mu D` is INERT at the type level — no `_⟶ᵀ_` rule
--   has it as subject — so it is its own only reduct, exactly like `Nat`
--   and `Unit`.  This is what makes every `Mu`-versus-X clash two lines.
Fin-nf : {n : ℕ} {A : RTy Γ} → Fin {Γ} n ⟶ᵀ* A → A ≡ Fin n
Fin-nf doneᵀ        = refl
Fin-nf (stepᵀ () _)

-- ⚠ The TYPE-level neutrality payload is a PLAIN syntactic `Ne`, not `SNe`.
-- `El-ne-reduct` needs neutrality preserved under reduction, and for `SNe` that
-- would need `SN` closed under reduction — a real lemma in the JM presentation
-- (its `sne-app` carries `SN` of the argument).  Nothing here uses the `SN`
-- payload at type level: it is only ever consumed by `joinW`-driven shape
-- refutation.  So carry the cheap predicate, with a forgetful map from `SNe`.
data Ne {Γ} : RTm Γ → Set where
  ne-var : (x : Var Γ) → Ne (var x)
  ne-app : {t u : RTm Γ} → Ne t → Ne (app t u)
  ne-absurd : {c e : RTm Γ} → Ne (absurd c e)
  ne-fst : {p : RTm Γ} → Ne p → Ne (fst p)
  ne-snd : {p : RTm Γ} → Ne p → Ne (snd p)
  ne-hrefl : {c t : RTm Γ} → nopw? c ≡ true → Ne (hrefl c t)
  ne-tr : {d : RTm (Γ ∙)} {p e : RTm Γ} →
          trstk? d p ≡ true → Ne (tr d p e)
  ne-ap : {cB : RTm Γ} {b : RTm (Γ ∙)} {p : RTm Γ} →
          apstk? p ≡ true → Ne (ap cB b p)
  ne-natrec : {z : RTm Γ} {w : RTm ((Γ ∙) ∙)} {n : RTm Γ} →
              natstk? n ≡ true → Ne (natrec z w n)
  ne-jsub : {d : RTm (Γ ∙)} {p e : RTm Γ} →
            idstk? p ≡ true → Ne (jsub d p e)
  -- ★★ WF stage E: the `Ne` peer of `sne-ordtr` — same key, and like
  -- every other eliminator it carries only the stuckness, not the SN.
  ne-ordtr : {a t u p q : RTm Γ} →
             ordstk? a t u ≡ true → Ne (ordtr a t u p q)
  -- ★★ LEVITATED FAMILIES: the `Ne` peers of the new `sne-*` — same keys,
  -- carrying only the stuckness.
  ne-ielim : {D i e t : RTm Γ} → mustk? t ≡ true → Ne (ielim D i e t)
  ne-dpay  : {I D C i : RTm Γ} → dstk? C ≡ true → Ne (dpay I D C i)
  ne-dih   : {D e C p : RTm Γ} → dstk? C ≡ true → Ne (dih D e C p)
  ne-fcase : {t a : RTm Γ} {b : RTm (Γ ∙)} → finstk? t ≡ true → Ne (fcase t a b)
  ne-fcase0 : {t : RTm Γ} → Ne (fcase0 t)
  ne-psplit : {b : RTm ((Γ ∙) ∙)} {q : RTm Γ} → Ne q → Ne (psplit b q)

ne-red : {t t' : RTm Γ} → Ne t → t ⟶ t' → Ne t'
ne-red (ne-var x) ()
ne-red (ne-app n) (ξ-appˡ r) = ne-app (ne-red n r)
ne-red (ne-app n) (ξ-appʳ r) = ne-app n
ne-red ne-absurd (ξ-absurdᶜ r) = ne-absurd
ne-red ne-absurd (ξ-absurdᵉ r) = ne-absurd
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
  ⊥-elim (f≢t (trans (sym (stkA?⊥dead c₁ kh)) key))
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
ne-red (ne-jsub key) (jsub-refl _ c₁ _ _) =
  ⊥-elim (f≢t key)
ne-red (ne-jsub key) (ξ-jsubᵈ r) = ne-jsub key
ne-red (ne-jsub key) (ξ-jsubᵖ r) = ne-jsub (idstk?-red r key)
ne-red (ne-jsub key) (ξ-jsubᵉ r) = ne-jsub key
ne-red (ne-natrec ()) (natrec-zero _ _)
ne-red (ne-natrec ()) (natrec-suc _ _ _)
ne-red (ne-natrec key) (ξ-natrecᶻ r) = ne-natrec key
ne-red (ne-natrec key) (ξ-natrecˢ r) = ne-natrec key
ne-red (ne-natrec key) (ξ-natrecⁿ r) = ne-natrec (natstk?-red r key)
-- ★★ LEVITATED FAMILIES: each root rule refuted by the key, the scrutinee
-- ξ moves the key, every other ξ leaves it alone.
ne-red (ne-ielim ()) (ι _ _ _ _)
ne-red (ne-ielim key) (ξ-ielimᴰ r) = ne-ielim key
ne-red (ne-ielim key) (ξ-ielimⁱ r) = ne-ielim key
ne-red (ne-ielim key) (ξ-ielimᵉ r) = ne-ielim key
ne-red (ne-ielim key) (ξ-ielimᵗ r) = ne-ielim (mustk?-red r key)
ne-red (ne-dpay ()) (dpay-ι _ _ _ _)
ne-red (ne-dpay ()) (dpay-σ _ _ _ _ _)
ne-red (ne-dpay ()) (dpay-ρ _ _ _ _ _)
ne-red (ne-dpay key) (ξ-dpayᴵ r) = ne-dpay key
ne-red (ne-dpay key) (ξ-dpayᴰ r) = ne-dpay key
ne-red (ne-dpay key) (ξ-dpayᶜ r) = ne-dpay (dstk?-red r key)
ne-red (ne-dpay key) (ξ-dpayⁱ r) = ne-dpay key
ne-red (ne-dih ()) (dih-ι _ _ _ _)
ne-red (ne-dih ()) (dih-σ _ _ _ _ _)
ne-red (ne-dih ()) (dih-ρ _ _ _ _ _)
ne-red (ne-dih key) (ξ-dihᴰ r) = ne-dih key
ne-red (ne-dih key) (ξ-dihᵉ r) = ne-dih key
ne-red (ne-dih key) (ξ-dihᶜ r) = ne-dih (dstk?-red r key)
ne-red (ne-dih key) (ξ-dihᵖ r) = ne-dih key
ne-red (ne-fcase ()) (fcase-z _ _)
ne-red (ne-fcase ()) (fcase-s _ _ _)
ne-red (ne-fcase key) (ξ-fcaseᵗ r) = ne-fcase (finstk?-red r key)
ne-red (ne-fcase key) (ξ-fcaseᵃ r) = ne-fcase key
ne-red (ne-fcase key) (ξ-fcaseᵇ r) = ne-fcase key
ne-red ne-fcase0 (ξ-fcase0 r) = ne-fcase0
ne-red (ne-psplit ()) (psplit-β _ _ _)
ne-red (ne-psplit n) (ξ-psplitᵇ r) = ne-psplit n
ne-red (ne-psplit n) (ξ-psplitᵍ r) = ne-psplit (ne-red n r)
-- ★★ WF stage E: the five root rules are refuted by the key, the three
-- bound congruences move it, and the two PROOF congruences leave it
-- alone — `ordstk?` does not mention `p`/`q`.
ne-red (ne-ordtr ()) (ordtr-z _ _ _ _)
ne-red (ne-ordtr ()) (ordtr-szz _ _ _)
ne-red (ne-ordtr ()) (ordtr-ssz _ _ _ _)
ne-red (ne-ordtr ()) (ordtr-szs _ _ _ _)
ne-red (ne-ordtr ()) (ordtr-sss _ _ _ _ _)
ne-red (ne-ordtr key) (ξ-ordtrᵃ {a = a} {a' = a'} {t = t} {u = u} r) =
  ne-ordtr (ordstk?-redᵃ {a = a} {a' = a'} {t = t} {u = u} r key)
ne-red (ne-ordtr key) (ξ-ordtrᵗ {a = a} {t = t} {t' = t'} {u = u} r) =
  ne-ordtr (ordstk?-redᵗ {a = a} {t = t} {t' = t'} {u = u} r key)
ne-red (ne-ordtr key) (ξ-ordtrᵘ {a = a} {t = t} {u = u} {u' = u'} r) =
  ne-ordtr (ordstk?-redᵘ {a = a} {t = t} {u = u} {u' = u'} r key)
ne-red (ne-ordtr key) (ξ-ordtrᵖ r) = ne-ordtr key
ne-red (ne-ordtr key) (ξ-ordtrq r) = ne-ordtr key

sne→ne : {t : RTm Γ} → SNe t → Ne t
sne→ne (sne-var x)   = ne-var x
sne→ne (sne-app n _) = ne-app (sne→ne n)
sne→ne (sne-absurd _ _) = ne-absurd
sne→ne (sne-fst n)   = ne-fst (sne→ne n)
sne→ne (sne-snd n)   = ne-snd (sne→ne n)
sne→ne (sne-hrefl _ _ kn) = ne-hrefl kn
sne→ne (sne-tr _ _ _ key) = ne-tr key
sne→ne (sne-ap _ _ _ key) = ne-ap key
sne→ne (sne-jsub _ _ _ key) = ne-jsub key
sne→ne (sne-natrec _ _ _ key) = ne-natrec key
sne→ne (sne-ielim _ _ _ _ key) = ne-ielim key
sne→ne (sne-dpay _ _ _ _ key) = ne-dpay key
sne→ne (sne-dih _ _ _ _ key) = ne-dih key
sne→ne (sne-fcase _ _ _ key) = ne-fcase key
sne→ne (sne-fcase0 _) = ne-fcase0
sne→ne (sne-psplit _ n) = ne-psplit (sne→ne n)
sne→ne (sne-ordtr _ _ _ _ _ key) = ne-ordtr key

ne-red* : {t t' : RTm Γ} → Ne t → t ⟶* t' → Ne t'
ne-red* n done       = n
ne-red* n (step r p) = ne-red* (ne-red n r) p

-- ★★ LEVITATED FAMILIES: the telescope formers are inert-SHAPED — every
--   reduct keeps the head and reduces componentwise.  The transfer layer's
--   joins and shape clashes ride on these (`IMu-reduct`'s term-level peers).
dι-reduct : {j C : RTm Γ} → dι j ⟶* C → Σ (RTm Γ) (λ j' → (C ≡ dι j') × (j ⟶* j'))
dι-reduct done = _ , (refl , done)
dι-reduct (step (ξ-dι r) p) with dι-reduct p
... | j' , (eq , q) = j' , (eq , step r q)

dσ-reduct : {S f C : RTm Γ} → dσ S f ⟶* C →
            Σ (RTm Γ) (λ S' → Σ (RTm Γ) (λ f' → (C ≡ dσ S' f') × ((S ⟶* S') × (f ⟶* f'))))
dσ-reduct done = _ , (_ , (refl , (done , done)))
dσ-reduct (step (ξ-dσˢ r) p) with dσ-reduct p
... | S' , (f' , (eq , (rS , rf))) = S' , (f' , (eq , (step r rS , rf)))
dσ-reduct (step (ξ-dσᶠ r) p) with dσ-reduct p
... | S' , (f' , (eq , (rS , rf))) = S' , (f' , (eq , (rS , step r rf)))

dρ-reduct : {j C E : RTm Γ} → dρ j C ⟶* E →
            Σ (RTm Γ) (λ j' → Σ (RTm Γ) (λ C' → (E ≡ dρ j' C') × ((j ⟶* j') × (C ⟶* C'))))
dρ-reduct done = _ , (_ , (refl , (done , done)))
dρ-reduct (step (ξ-dρʲ r) p) with dρ-reduct p
... | j' , (C' , (eq , (rj , rC))) = j' , (C' , (eq , (step r rj , rC)))
dρ-reduct (step (ξ-dρᶜ r) p) with dρ-reduct p
... | j' , (C' , (eq , (rj , rC))) = j' , (C' , (eq , (rj , step r rC)))

-- the shape clashes: a neutral is never a telescope former, and the three
-- formers are distinct.
ne≢dι : {C j : RTm Γ} → C ≡ dι j → Ne C → ⊥
ne≢dι refl ()
ne≢dσ : {C S f : RTm Γ} → C ≡ dσ S f → Ne C → ⊥
ne≢dσ refl ()
ne≢dρ : {C j E : RTm Γ} → C ≡ dρ j E → Ne C → ⊥
ne≢dρ refl ()
dι≢dσ : {j S f : RTm Γ} → dι j ≡ dσ S f → ⊥
dι≢dσ ()
dι≢dρ : {j j' C : RTm Γ} → dι j ≡ dρ j' C → ⊥
dι≢dρ ()
dσ≢dρ : {S f j C : RTm Γ} → dσ S f ≡ dρ j C → ⊥
dσ≢dρ ()

-- extractors for `fund`'s path analysis: strict neutrals are safe spine
-- heads and stable codes.
sne→spine : {t : RTm Γ} → SNe t → spine? t ≡ true
sne→spine (sne-var x)        = refl
sne→spine (sne-app n _)      = sne→spine n
sne→spine (sne-absurd _ _)     = refl
sne→spine (sne-fst n)        = sne→spine n
sne→spine (sne-snd n)        = sne→spine n
sne→spine (sne-hrefl _ _ kn) = kn
sne→spine (sne-tr _ _ _ key) = key
sne→spine (sne-ap _ _ _ key) = key
sne→spine (sne-jsub _ _ _ key) = key
sne→spine (sne-natrec _ _ _ key) = key
sne→spine (sne-ielim _ _ _ _ key) = key
sne→spine (sne-dpay _ _ _ _ key) = key
sne→spine (sne-dih _ _ _ _ key) = key
sne→spine (sne-fcase _ _ _ key) = key
sne→spine (sne-fcase0 _) = refl
sne→spine (sne-psplit _ n) = sne→spine n
sne→spine (sne-ordtr _ _ _ _ _ key) = key

-- ★ the `stableA?` peer.  A strict neutral is never ⌜Nat⌝- or
-- ⌜Hom⌝-headed, so `stableA?` and `stablecd?` agree once the head is
-- exposed — every row is the same term.
-- ★ INDUCTIVE TYPES: the `mustk?` peer, which `⊢elim`'s neutral case
-- needs to feed `sne-elim`.  `mustk?` and `spine?` agree on every neutral
-- former except `hrefl`, where `mustk?` is unconditionally `true` — so
-- every row is either `refl`, the sub-derivation's `spine?`, or the
-- carried key, exactly as in `sne→stableA` below.
sne→mustk : {t : RTm Γ} → SNe t → mustk? t ≡ true
sne→mustk (sne-var x)             = refl
sne→mustk (sne-app n _)           = sne→spine n
sne→mustk (sne-absurd _ _)        = refl
sne→mustk (sne-fst n)             = sne→spine n
sne→mustk (sne-snd n)             = sne→spine n
sne→mustk (sne-hrefl _ _ _)       = refl
sne→mustk (sne-tr _ _ _ key)      = key
sne→mustk (sne-ap _ _ _ key)      = key
sne→mustk (sne-jsub _ _ _ key)    = key
sne→mustk (sne-natrec _ _ _ key)  = key
sne→mustk (sne-ielim _ _ _ _ key) = key
sne→mustk (sne-dpay _ _ _ _ key) = key
sne→mustk (sne-dih _ _ _ _ key) = key
sne→mustk (sne-fcase _ _ _ key) = key
sne→mustk (sne-fcase0 _) = refl
sne→mustk (sne-psplit _ n) = sne→spine n
sne→mustk (sne-ordtr _ _ _ _ _ key) = key

sne→stableA : {t : RTm Γ} → SNe t → stableA? t ≡ true
sne→stableA (sne-var x)        = refl
sne→stableA (sne-app n _)      = sne→spine n
sne→stableA (sne-absurd _ _)     = refl
sne→stableA (sne-fst n)        = sne→spine n
sne→stableA (sne-snd n)        = sne→spine n
sne→stableA (sne-hrefl _ _ _)    = refl
sne→stableA (sne-tr _ _ _ key) = key
sne→stableA (sne-ap _ _ _ key) = key
sne→stableA (sne-jsub _ _ _ key) = key
sne→stableA (sne-natrec _ _ _ key) = key
sne→stableA (sne-ielim _ _ _ _ key) = key
sne→stableA (sne-dpay _ _ _ _ key) = key
sne→stableA (sne-dih _ _ _ _ key) = key
sne→stableA (sne-fcase _ _ _ key) = key
sne→stableA (sne-fcase0 _) = refl
sne→stableA (sne-psplit _ n) = sne→spine n
sne→stableA (sne-ordtr _ _ _ _ _ key) = key

sne→stablecd : {t : RTm Γ} → SNe t → stablecd? t ≡ true
sne→stablecd (sne-var x)        = refl
sne→stablecd (sne-app n _)      = sne→spine n
sne→stablecd (sne-absurd _ _)     = refl
sne→stablecd (sne-fst n)        = sne→spine n
sne→stablecd (sne-snd n)        = sne→spine n
sne→stablecd (sne-hrefl _ _ _)    = refl
sne→stablecd (sne-tr _ _ _ key) = key
sne→stablecd (sne-ap _ _ _ key) = key
sne→stablecd (sne-jsub _ _ _ key) = key
sne→stablecd (sne-natrec _ _ _ key) = key
sne→stablecd (sne-ielim _ _ _ _ key) = key
sne→stablecd (sne-dpay _ _ _ _ key) = key
sne→stablecd (sne-dih _ _ _ _ key) = key
sne→stablecd (sne-fcase _ _ _ key) = key
sne→stablecd (sne-fcase0 _) = refl
sne→stablecd (sne-psplit _ n) = sne→spine n
sne→stablecd (sne-ordtr _ _ _ _ _ key) = key

-- ★ WF stage A: a strict neutral is never a numeral — the extractor
-- `fund`'s `⊢natrec` neutral branch needs.
sne→natstk : {t : RTm Γ} → SNe t → natstk? t ≡ true
sne→natstk (sne-var x)          = refl
sne→natstk (sne-app n _)        = sne→spine n
sne→natstk (sne-absurd _ _)       = refl
sne→natstk (sne-fst n)          = sne→spine n
sne→natstk (sne-snd n)          = sne→spine n
sne→natstk (sne-hrefl _ _ _)    = refl
sne→natstk (sne-tr _ _ _ key)   = key
sne→natstk (sne-ap _ _ _ key)   = key
sne→natstk (sne-jsub _ _ _ key) = key
sne→natstk (sne-natrec _ _ _ key) = key
sne→natstk (sne-ielim _ _ _ _ key) = key
sne→natstk (sne-dpay _ _ _ _ key) = key
sne→natstk (sne-dih _ _ _ _ key) = key
sne→natstk (sne-fcase _ _ _ key) = key
sne→natstk (sne-fcase0 _) = refl
sne→natstk (sne-psplit _ n) = sne→spine n
sne→natstk (sne-ordtr _ _ _ _ _ key) = key

-- ★★ LEVITATED FAMILIES: the telescope and tag peers, for `fund`'s neutral
--   `dpay`/`dih`/`fcase` cases.  Every row is `sne→natstk`'s.
sne→dstk : {t : RTm Γ} → SNe t → dstk? t ≡ true
sne→dstk (sne-var x)          = refl
sne→dstk (sne-app n _)        = sne→spine n
sne→dstk (sne-absurd _ _)       = refl
sne→dstk (sne-fst n)          = sne→spine n
sne→dstk (sne-snd n)          = sne→spine n
sne→dstk (sne-hrefl _ _ _)    = refl
sne→dstk (sne-tr _ _ _ key)   = key
sne→dstk (sne-ap _ _ _ key)   = key
sne→dstk (sne-jsub _ _ _ key) = key
sne→dstk (sne-natrec _ _ _ key) = key
sne→dstk (sne-ielim _ _ _ _ key) = key
sne→dstk (sne-dpay _ _ _ _ key) = key
sne→dstk (sne-dih _ _ _ _ key) = key
sne→dstk (sne-fcase _ _ _ key) = key
sne→dstk (sne-fcase0 _) = refl
sne→dstk (sne-psplit _ n) = sne→spine n
sne→dstk (sne-ordtr _ _ _ _ _ key) = key

sne→finstk : {t : RTm Γ} → SNe t → finstk? t ≡ true
sne→finstk (sne-var x)          = refl
sne→finstk (sne-app n _)        = sne→spine n
sne→finstk (sne-absurd _ _)       = refl
sne→finstk (sne-fst n)          = sne→spine n
sne→finstk (sne-snd n)          = sne→spine n
sne→finstk (sne-hrefl _ _ _)    = refl
sne→finstk (sne-tr _ _ _ key)   = key
sne→finstk (sne-ap _ _ _ key)   = key
sne→finstk (sne-jsub _ _ _ key) = key
sne→finstk (sne-natrec _ _ _ key) = key
sne→finstk (sne-ielim _ _ _ _ key) = key
sne→finstk (sne-dpay _ _ _ _ key) = key
sne→finstk (sne-dih _ _ _ _ key) = key
sne→finstk (sne-fcase _ _ _ key) = key
sne→finstk (sne-fcase0 _) = refl
sne→finstk (sne-psplit _ n) = sne→spine n
sne→finstk (sne-ordtr _ _ _ _ _ key) = key

-- renaming preserves every classifier ON THE NOSE — the entire
-- anti-renaming bill for the shape layer.
homheaded?-ren : (ρ : Ren Γ Δ) (t : RTm Γ) →
                 homheaded? (renTm ρ t) ≡ homheaded? t
homheaded?-ren ρ (var x)       = refl
homheaded?-ren ρ (lam t)       = refl
homheaded?-ren ρ (app t u)     = refl
homheaded?-ren ρ (pair a b)    = refl
homheaded?-ren ρ (absurd c e)       = refl
homheaded?-ren ρ (ordtr a t u p q) = refl
homheaded?-ren ρ (fst t)       = refl
homheaded?-ren ρ (snd t)       = refl
homheaded?-ren ρ ⌜base⌝        = refl
homheaded?-ren ρ ⌜Nat⌝ = refl
homheaded?-ren ρ ⌜Unit⌝ = refl
homheaded?-ren ρ (⌜Π⌝ c d)     = refl
homheaded?-ren ρ (⌜Σ⌝ c d)     = refl
homheaded?-ren ρ (⌜Hom⌝ c a b) = refl
homheaded?-ren ρ (hrefl c t)   = refl
homheaded?-ren ρ (tr d p e)    = refl
homheaded?-ren ρ (ap c b p)  = refl
homheaded?-ren ρ (⌜Id⌝ c a b) = refl
homheaded?-ren ρ (idrefl c t) = refl
homheaded?-ren ρ (jsub d p e) = refl
homheaded?-ren ρ unit          = refl
homheaded?-ren ρ nzero         = refl
homheaded?-ren ρ (nsuc n)      = refl
homheaded?-ren ρ (natrec z s n) = refl
homheaded?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
homheaded?-ren ρ (ielim D iˣ ms t) = refl
homheaded?-ren ρ (⌜Fin⌝ n) = refl
homheaded?-ren ρ (con p) = refl
homheaded?-ren ρ (dι j) = refl
homheaded?-ren ρ (dσ S f) = refl
homheaded?-ren ρ (dρ j C) = refl
homheaded?-ren ρ (dpay I D C i) = refl
homheaded?-ren ρ (dih D e C p) = refl
homheaded?-ren ρ fzero = refl
homheaded?-ren ρ (fsuc t) = refl
homheaded?-ren ρ (fcase t a b) = refl
homheaded?-ren ρ (fcase0 t) = refl
homheaded?-ren ρ (psplit b q) = refl

spine?-ren    : (ρ : Ren Γ Δ) (t : RTm Γ) → spine? (renTm ρ t) ≡ spine? t
-- the order's renaming stability, shared by all nine classifiers.
ordstk?-ren   : (ρ : Ren Γ Δ) (a t u : RTm Γ) →
                ordstk? (renTm ρ a) (renTm ρ t) (renTm ρ u) ≡ ordstk? a t u
ordS?-ren     : (b : 𝔹) (ρ : Ren Γ Δ) (u : RTm Γ) →
                ordS? b (renTm ρ u) ≡ ordS? b u
stableA?-ren  : (ρ : Ren Γ Δ) (t : RTm Γ) →
                stableA? (renTm ρ t) ≡ stableA? t
stablecd?-ren : (ρ : Ren Γ Δ) (t : RTm Γ) →
                stablecd? (renTm ρ t) ≡ stablecd? t
apstk?-ren    : (ρ : Ren Γ Δ) (t : RTm Γ) →
                apstk? (renTm ρ t) ≡ apstk? t
natstk?-ren   : (ρ : Ren Γ Δ) (t : RTm Γ) → natstk? (renTm ρ t) ≡ natstk? t
dstk?-ren     : (ρ : Ren Γ Δ) (t : RTm Γ) → dstk? (renTm ρ t) ≡ dstk? t
finstk?-ren   : (ρ : Ren Γ Δ) (t : RTm Γ) → finstk? (renTm ρ t) ≡ finstk? t
mustk?-ren    : (ρ : Ren Γ Δ) (t : RTm Γ) → mustk? (renTm ρ t) ≡ mustk? t
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
spine?-ren ρ (absurd c e)       = refl
spine?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
spine?-ren ρ (fst t)       = spine?-ren ρ t
spine?-ren ρ (snd t)       = spine?-ren ρ t
spine?-ren ρ ⌜base⌝        = refl
spine?-ren ρ ⌜Nat⌝ = refl
spine?-ren ρ ⌜Unit⌝ = refl
spine?-ren ρ (⌜Π⌝ c d)     = refl
spine?-ren ρ (⌜Σ⌝ c d)     = refl
spine?-ren ρ (⌜Hom⌝ c a b) = refl
spine?-ren ρ (hrefl c t)   = nopw?-ren ρ c
spine?-ren ρ (tr d p e)    = trstk?-ren ρ d p
spine?-ren ρ (ap c b p)    = apstk?-ren ρ p
spine?-ren ρ (⌜Id⌝ c a b)  = refl
spine?-ren ρ (idrefl c t)  = refl
spine?-ren ρ (jsub d p e)  = idstk?-ren ρ p
spine?-ren ρ unit          = refl
spine?-ren ρ nzero         = refl
spine?-ren ρ (nsuc n)      = refl
spine?-ren ρ (natrec z s n) = natstk?-ren ρ n
spine?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
spine?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
spine?-ren ρ (⌜Fin⌝ n) = refl
spine?-ren ρ (con p) = refl
spine?-ren ρ (dι j) = refl
spine?-ren ρ (dσ S f) = refl
spine?-ren ρ (dρ j C) = refl
spine?-ren ρ (dpay I D C i) = dstk?-ren ρ C
spine?-ren ρ (dih D e C p) = dstk?-ren ρ C
spine?-ren ρ fzero = refl
spine?-ren ρ (fsuc t) = refl
spine?-ren ρ (fcase t a b) = finstk?-ren ρ t
spine?-ren ρ (fcase0 t) = refl
spine?-ren ρ (psplit b q) = spine?-ren ρ q

ordS?-ren true  ρ u = refl
ordS?-ren false ρ u = natstk?-ren ρ u

ordstk?-ren ρ nzero t u = refl
ordstk?-ren ρ (nsuc a₀) t u =
  trans (cong (λ b → ordS? b (renTm ρ u)) (natstk?-ren ρ t))
        (ordS?-ren (natstk? t) ρ u)
-- every other head of the bound falls to `ordstk?`'s catch-all
-- `natstk? a`, so each row is `natstk?-ren ρ a` — the enumeration is
-- irreducible (nothing pins `a`'s head) but every row is mechanical.
-- ★ the `ordtr` row recurses into `ordstk?-ren` DIRECTLY rather than
-- bouncing through `natstk?-ren` — same term, but structurally
-- decreasing, which keeps the mutual block's termination graph trivial.
ordstk?-ren ρ (var x) t u          = refl
ordstk?-ren ρ (lam a₀) t u         = refl
ordstk?-ren ρ (app a₀ a₁) t u      = spine?-ren ρ a₀
ordstk?-ren ρ (pair a₀ a₁) t u     = refl
ordstk?-ren ρ (absurd a₀ a₁) t u   = refl
ordstk?-ren ρ (ordtr a₀ t₀ u₀ p₀ q₀) t u = ordstk?-ren ρ a₀ t₀ u₀
ordstk?-ren ρ (fst a₀) t u         = spine?-ren ρ a₀
ordstk?-ren ρ (snd a₀) t u         = spine?-ren ρ a₀
ordstk?-ren ρ ⌜base⌝ t u           = refl
ordstk?-ren ρ ⌜Nat⌝ t u            = refl
ordstk?-ren ρ ⌜Unit⌝ t u           = refl
ordstk?-ren ρ (⌜Π⌝ a₀ a₁) t u      = refl
ordstk?-ren ρ (⌜Σ⌝ a₀ a₁) t u      = refl
ordstk?-ren ρ (⌜Hom⌝ a₀ a₁ a₂) t u = refl
ordstk?-ren ρ (hrefl a₀ a₁) t u    = refl
ordstk?-ren ρ (tr a₀ a₁ a₂) t u    = trstk?-ren ρ a₀ a₁
ordstk?-ren ρ (ap a₀ a₁ a₂) t u    = apstk?-ren ρ a₂
ordstk?-ren ρ (⌜Id⌝ a₀ a₁ a₂) t u  = refl
ordstk?-ren ρ (idrefl a₀ a₁) t u   = refl
ordstk?-ren ρ (jsub a₀ a₁ a₂) t u  = idstk?-ren ρ a₁
ordstk?-ren ρ unit t u             = refl
ordstk?-ren ρ (natrec a₀ a₁ a₂) t u = natstk?-ren ρ a₂
ordstk?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) t u           = refl
ordstk?-ren ρ (ielim D iˣ ms a₀) t u = mustk?-ren ρ a₀
ordstk?-ren ρ (⌜Fin⌝ n) t u = refl
ordstk?-ren ρ (con p) t u = refl
ordstk?-ren ρ (dι j) t u = refl
ordstk?-ren ρ (dσ S f) t u = refl
ordstk?-ren ρ (dρ j C) t u = refl
ordstk?-ren ρ (dpay I D C i) t u = dstk?-ren ρ C
ordstk?-ren ρ (dih D e C p) t u = dstk?-ren ρ C
ordstk?-ren ρ fzero t u = refl
ordstk?-ren ρ (fsuc t₀) t u = refl
ordstk?-ren ρ (fcase t₀ a b) t u = finstk?-ren ρ t₀
ordstk?-ren ρ (fcase0 t₀) t u = refl
ordstk?-ren ρ (psplit b q) t u = spine?-ren ρ q

-- ★ the `stableA?` peer of `stablecd?-ren`.
stableA?-ren ρ (var x)       = refl
stableA?-ren ρ (lam t)       = refl
stableA?-ren ρ (app t u)     = spine?-ren ρ t
stableA?-ren ρ (pair a b)    = refl
stableA?-ren ρ (absurd c e)       = refl
stableA?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
stableA?-ren ρ (fst t)       = spine?-ren ρ t
stableA?-ren ρ (snd t)       = spine?-ren ρ t
stableA?-ren ρ ⌜base⌝        = refl
stableA?-ren ρ ⌜Nat⌝ = refl
stableA?-ren ρ ⌜Unit⌝ = refl
stableA?-ren ρ (⌜Π⌝ c d)     = refl
stableA?-ren ρ (⌜Σ⌝ c d)     = refl
stableA?-ren ρ (⌜Hom⌝ c a b) = stableA?-ren ρ c
stableA?-ren ρ (hrefl c t)   = refl
stableA?-ren ρ (tr d p e)    = trstk?-ren ρ d p
stableA?-ren ρ (ap c b p)    = apstk?-ren ρ p
stableA?-ren ρ (⌜Id⌝ c a b)  = refl
stableA?-ren ρ (idrefl c t)  = refl
stableA?-ren ρ (jsub d p e)  = idstk?-ren ρ p
stableA?-ren ρ unit          = refl
stableA?-ren ρ nzero         = refl
stableA?-ren ρ (nsuc n)      = refl
stableA?-ren ρ (natrec z s n) = natstk?-ren ρ n
stableA?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
stableA?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
stableA?-ren ρ (⌜Fin⌝ n) = refl
stableA?-ren ρ (con p) = refl
stableA?-ren ρ (dι j) = refl
stableA?-ren ρ (dσ S f) = refl
stableA?-ren ρ (dρ j C) = refl
stableA?-ren ρ (dpay I D C i) = dstk?-ren ρ C
stableA?-ren ρ (dih D e C p) = dstk?-ren ρ C
stableA?-ren ρ fzero = refl
stableA?-ren ρ (fsuc t) = refl
stableA?-ren ρ (fcase t a b) = finstk?-ren ρ t
stableA?-ren ρ (fcase0 t) = refl
stableA?-ren ρ (psplit b q) = spine?-ren ρ q

stablecd?-ren ρ (var x)       = refl
stablecd?-ren ρ (lam t)       = refl
stablecd?-ren ρ (app t u)     = spine?-ren ρ t
stablecd?-ren ρ (pair a b)    = refl
stablecd?-ren ρ (absurd c e)       = refl
stablecd?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
stablecd?-ren ρ (fst t)       = spine?-ren ρ t
stablecd?-ren ρ (snd t)       = spine?-ren ρ t
stablecd?-ren ρ ⌜base⌝        = refl
stablecd?-ren ρ ⌜Nat⌝ = refl
stablecd?-ren ρ ⌜Unit⌝ = refl
stablecd?-ren ρ (⌜Π⌝ c d)     = refl
stablecd?-ren ρ (⌜Σ⌝ c d)     = refl
stablecd?-ren ρ (⌜Hom⌝ c a b) = stableA?-ren ρ c
stablecd?-ren ρ (hrefl c t)   = refl
stablecd?-ren ρ (tr d p e)    = trstk?-ren ρ d p
stablecd?-ren ρ (ap c b p)    = apstk?-ren ρ p
stablecd?-ren ρ (⌜Id⌝ c a b)  = refl
stablecd?-ren ρ (idrefl c t)  = refl
stablecd?-ren ρ (jsub d p e)  = idstk?-ren ρ p
stablecd?-ren ρ unit          = refl
stablecd?-ren ρ nzero         = refl
stablecd?-ren ρ (nsuc n)      = refl
stablecd?-ren ρ (natrec z s n) = natstk?-ren ρ n
stablecd?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
stablecd?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
stablecd?-ren ρ (⌜Fin⌝ n) = refl
stablecd?-ren ρ (con p) = refl
stablecd?-ren ρ (dι j) = refl
stablecd?-ren ρ (dσ S f) = refl
stablecd?-ren ρ (dρ j C) = refl
stablecd?-ren ρ (dpay I D C i) = dstk?-ren ρ C
stablecd?-ren ρ (dih D e C p) = dstk?-ren ρ C
stablecd?-ren ρ fzero = refl
stablecd?-ren ρ (fsuc t) = refl
stablecd?-ren ρ (fcase t a b) = finstk?-ren ρ t
stablecd?-ren ρ (fcase0 t) = refl
stablecd?-ren ρ (psplit b q) = spine?-ren ρ q

pathstk?-ren ρ (var x)       = refl
pathstk?-ren ρ (lam t)       = refl
pathstk?-ren ρ (app t u)     = spine?-ren ρ t
pathstk?-ren ρ (pair a b)    = refl
pathstk?-ren ρ (absurd c e)       = refl
pathstk?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
pathstk?-ren ρ (fst t)       = spine?-ren ρ t
pathstk?-ren ρ (snd t)       = spine?-ren ρ t
pathstk?-ren ρ ⌜base⌝        = refl
pathstk?-ren ρ ⌜Nat⌝ = refl
pathstk?-ren ρ ⌜Unit⌝ = refl
pathstk?-ren ρ (⌜Π⌝ c d)     = refl
pathstk?-ren ρ (⌜Σ⌝ c d)     = refl
pathstk?-ren ρ (⌜Hom⌝ c a b) = refl
pathstk?-ren ρ (hrefl c t)   = stablecd?-ren ρ c
pathstk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
pathstk?-ren ρ (ap c b p)    = apstk?-ren ρ p
pathstk?-ren ρ (⌜Id⌝ c a b)  = refl
pathstk?-ren ρ (idrefl c t)  = refl
pathstk?-ren ρ (jsub d p e)  = idstk?-ren ρ p
pathstk?-ren ρ unit          = refl
pathstk?-ren ρ nzero         = refl
pathstk?-ren ρ (nsuc n)      = refl
pathstk?-ren ρ (natrec z s n) = natstk?-ren ρ n
pathstk?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
pathstk?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
pathstk?-ren ρ (⌜Fin⌝ n) = refl
pathstk?-ren ρ (con p) = refl
pathstk?-ren ρ (dι j) = refl
pathstk?-ren ρ (dσ S f) = refl
pathstk?-ren ρ (dρ j C) = refl
pathstk?-ren ρ (dpay I D C i) = dstk?-ren ρ C
pathstk?-ren ρ (dih D e C p) = dstk?-ren ρ C
pathstk?-ren ρ fzero = refl
pathstk?-ren ρ (fsuc t) = refl
pathstk?-ren ρ (fcase t a b) = finstk?-ren ρ t
pathstk?-ren ρ (fcase0 t) = refl
pathstk?-ren ρ (psplit b q) = spine?-ren ρ q

apstk?-ren ρ (var x)       = refl
apstk?-ren ρ (lam t)       = refl
apstk?-ren ρ (app t u)     = spine?-ren ρ t
apstk?-ren ρ (pair a b)    = refl
apstk?-ren ρ (absurd c e)       = refl
apstk?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
apstk?-ren ρ (fst t)       = spine?-ren ρ t
apstk?-ren ρ (snd t)       = spine?-ren ρ t
apstk?-ren ρ ⌜base⌝        = refl
apstk?-ren ρ ⌜Nat⌝ = refl
apstk?-ren ρ ⌜Unit⌝ = refl
apstk?-ren ρ (⌜Π⌝ c d)     = refl
apstk?-ren ρ (⌜Σ⌝ c d)     = refl
apstk?-ren ρ (⌜Hom⌝ c a b) = refl
apstk?-ren ρ (hrefl c t)   = stablecd?-ren ρ c
apstk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
apstk?-ren ρ (ap c b p)    = apstk?-ren ρ p
apstk?-ren ρ (⌜Id⌝ c a b)  = refl
apstk?-ren ρ (idrefl c t)  = refl
apstk?-ren ρ (jsub d p e)  = idstk?-ren ρ p
apstk?-ren ρ unit          = refl
apstk?-ren ρ nzero         = refl
apstk?-ren ρ (nsuc n)      = refl
apstk?-ren ρ (natrec z s n) = natstk?-ren ρ n
apstk?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
apstk?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
apstk?-ren ρ (⌜Fin⌝ n) = refl
apstk?-ren ρ (con p) = refl
apstk?-ren ρ (dι j) = refl
apstk?-ren ρ (dσ S f) = refl
apstk?-ren ρ (dρ j C) = refl
apstk?-ren ρ (dpay I D C i) = dstk?-ren ρ C
apstk?-ren ρ (dih D e C p) = dstk?-ren ρ C
apstk?-ren ρ fzero = refl
apstk?-ren ρ (fsuc t) = refl
apstk?-ren ρ (fcase t a b) = finstk?-ren ρ t
apstk?-ren ρ (fcase0 t) = refl
apstk?-ren ρ (psplit b q) = spine?-ren ρ q

idstk?-ren ρ (var x)       = refl
idstk?-ren ρ (lam t)       = refl
idstk?-ren ρ (app t u)     = spine?-ren ρ t
idstk?-ren ρ (pair a b)    = refl
idstk?-ren ρ (absurd c e)       = refl
idstk?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
idstk?-ren ρ (fst t)       = spine?-ren ρ t
idstk?-ren ρ (snd t)       = spine?-ren ρ t
idstk?-ren ρ ⌜base⌝        = refl
idstk?-ren ρ ⌜Nat⌝ = refl
idstk?-ren ρ ⌜Unit⌝ = refl
idstk?-ren ρ (⌜Π⌝ c d)     = refl
idstk?-ren ρ (⌜Σ⌝ c d)     = refl
idstk?-ren ρ (⌜Hom⌝ c a b) = refl
idstk?-ren ρ (⌜Id⌝ c a b)  = refl
idstk?-ren ρ (hrefl c t)   = refl
idstk?-ren ρ (idrefl c t)  = refl
idstk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
idstk?-ren ρ (ap c b p)    = apstk?-ren ρ p
idstk?-ren ρ (jsub d p e)  = idstk?-ren ρ p
idstk?-ren ρ unit          = refl
idstk?-ren ρ nzero         = refl
idstk?-ren ρ (nsuc n)      = refl
idstk?-ren ρ (natrec z s n) = natstk?-ren ρ n
idstk?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
idstk?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
idstk?-ren ρ (⌜Fin⌝ n) = refl
idstk?-ren ρ (con p) = refl
idstk?-ren ρ (dι j) = refl
idstk?-ren ρ (dσ S f) = refl
idstk?-ren ρ (dρ j C) = refl
idstk?-ren ρ (dpay I D C i) = dstk?-ren ρ C
idstk?-ren ρ (dih D e C p) = dstk?-ren ρ C
idstk?-ren ρ fzero = refl
idstk?-ren ρ (fsuc t) = refl
idstk?-ren ρ (fcase t a b) = finstk?-ren ρ t
idstk?-ren ρ (fcase0 t) = refl
idstk?-ren ρ (psplit b q) = spine?-ren ρ q

natstk?-ren ρ (var x)       = refl
natstk?-ren ρ (lam t)       = refl
natstk?-ren ρ (app t u)     = spine?-ren ρ t
natstk?-ren ρ (pair a b)    = refl
natstk?-ren ρ (absurd c e)       = refl
natstk?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
natstk?-ren ρ (fst t)       = spine?-ren ρ t
natstk?-ren ρ (snd t)       = spine?-ren ρ t
natstk?-ren ρ ⌜base⌝        = refl
natstk?-ren ρ ⌜Nat⌝ = refl
natstk?-ren ρ ⌜Unit⌝ = refl
natstk?-ren ρ (⌜Π⌝ c d)     = refl
natstk?-ren ρ (⌜Σ⌝ c d)     = refl
natstk?-ren ρ (⌜Hom⌝ c a b) = refl
natstk?-ren ρ (⌜Id⌝ c a b)  = refl
natstk?-ren ρ (hrefl c t)   = refl
natstk?-ren ρ (idrefl c t)  = refl
natstk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
natstk?-ren ρ (ap c b p)    = apstk?-ren ρ p
natstk?-ren ρ (jsub d p e)  = idstk?-ren ρ p
natstk?-ren ρ unit          = refl
natstk?-ren ρ nzero         = refl
natstk?-ren ρ (nsuc n)      = refl
natstk?-ren ρ (natrec z s n) = natstk?-ren ρ n
natstk?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
natstk?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
natstk?-ren ρ (⌜Fin⌝ n) = refl
natstk?-ren ρ (con p) = refl
natstk?-ren ρ (dι j) = refl
natstk?-ren ρ (dσ S f) = refl
natstk?-ren ρ (dρ j C) = refl
natstk?-ren ρ (dpay I D C i) = dstk?-ren ρ C
natstk?-ren ρ (dih D e C p) = dstk?-ren ρ C
natstk?-ren ρ fzero = refl
natstk?-ren ρ (fsuc t) = refl
natstk?-ren ρ (fcase t a b) = finstk?-ren ρ t
natstk?-ren ρ (fcase0 t) = refl
natstk?-ren ρ (psplit b q) = spine?-ren ρ q

dstk?-ren ρ (var x)       = refl
dstk?-ren ρ (lam t)       = refl
dstk?-ren ρ (app t u)     = spine?-ren ρ t
dstk?-ren ρ (pair a b)    = refl
dstk?-ren ρ (absurd c e)       = refl
dstk?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
dstk?-ren ρ (fst t)       = spine?-ren ρ t
dstk?-ren ρ (snd t)       = spine?-ren ρ t
dstk?-ren ρ ⌜base⌝        = refl
dstk?-ren ρ ⌜Nat⌝ = refl
dstk?-ren ρ ⌜Unit⌝ = refl
dstk?-ren ρ (⌜Π⌝ c d)     = refl
dstk?-ren ρ (⌜Σ⌝ c d)     = refl
dstk?-ren ρ (⌜Hom⌝ c a b) = refl
dstk?-ren ρ (⌜Id⌝ c a b)  = refl
dstk?-ren ρ (hrefl c t)   = refl
dstk?-ren ρ (idrefl c t)  = refl
dstk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
dstk?-ren ρ (ap c b p)    = apstk?-ren ρ p
dstk?-ren ρ (jsub d p e)  = idstk?-ren ρ p
dstk?-ren ρ unit          = refl
dstk?-ren ρ nzero         = refl
dstk?-ren ρ (nsuc n)      = refl
dstk?-ren ρ (natrec z s n) = natstk?-ren ρ n
dstk?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
dstk?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
dstk?-ren ρ (⌜Fin⌝ n) = refl
dstk?-ren ρ (con p) = refl
dstk?-ren ρ (dι j) = refl
dstk?-ren ρ (dσ S f) = refl
dstk?-ren ρ (dρ j C) = refl
dstk?-ren ρ (dpay I D C i) = dstk?-ren ρ C
dstk?-ren ρ (dih D e C p) = dstk?-ren ρ C
dstk?-ren ρ fzero = refl
dstk?-ren ρ (fsuc t) = refl
dstk?-ren ρ (fcase t a b) = finstk?-ren ρ t
dstk?-ren ρ (fcase0 t) = refl
dstk?-ren ρ (psplit b q) = spine?-ren ρ q

finstk?-ren ρ (var x)       = refl
finstk?-ren ρ (lam t)       = refl
finstk?-ren ρ (app t u)     = spine?-ren ρ t
finstk?-ren ρ (pair a b)    = refl
finstk?-ren ρ (absurd c e)       = refl
finstk?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
finstk?-ren ρ (fst t)       = spine?-ren ρ t
finstk?-ren ρ (snd t)       = spine?-ren ρ t
finstk?-ren ρ ⌜base⌝        = refl
finstk?-ren ρ ⌜Nat⌝ = refl
finstk?-ren ρ ⌜Unit⌝ = refl
finstk?-ren ρ (⌜Π⌝ c d)     = refl
finstk?-ren ρ (⌜Σ⌝ c d)     = refl
finstk?-ren ρ (⌜Hom⌝ c a b) = refl
finstk?-ren ρ (⌜Id⌝ c a b)  = refl
finstk?-ren ρ (hrefl c t)   = refl
finstk?-ren ρ (idrefl c t)  = refl
finstk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
finstk?-ren ρ (ap c b p)    = apstk?-ren ρ p
finstk?-ren ρ (jsub d p e)  = idstk?-ren ρ p
finstk?-ren ρ unit          = refl
finstk?-ren ρ nzero         = refl
finstk?-ren ρ (nsuc n)      = refl
finstk?-ren ρ (natrec z s n) = natstk?-ren ρ n
finstk?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
finstk?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
finstk?-ren ρ (⌜Fin⌝ n) = refl
finstk?-ren ρ (con p) = refl
finstk?-ren ρ (dι j) = refl
finstk?-ren ρ (dσ S f) = refl
finstk?-ren ρ (dρ j C) = refl
finstk?-ren ρ (dpay I D C i) = dstk?-ren ρ C
finstk?-ren ρ (dih D e C p) = dstk?-ren ρ C
finstk?-ren ρ fzero = refl
finstk?-ren ρ (fsuc t) = refl
finstk?-ren ρ (fcase t a b) = finstk?-ren ρ t
finstk?-ren ρ (fcase0 t) = refl
finstk?-ren ρ (psplit b q) = spine?-ren ρ q

-- ★ INDUCTIVE TYPES: `mustk?`'s naturality — `natstk?-ren`'s clone, since
--   the two keys agree on every head that renaming can see.
mustk?-ren ρ (var x)       = refl
mustk?-ren ρ (lam t)       = refl
mustk?-ren ρ (app t u)     = spine?-ren ρ t
mustk?-ren ρ (pair a b)    = refl
mustk?-ren ρ (absurd c e)       = refl
mustk?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
mustk?-ren ρ (fst t)       = spine?-ren ρ t
mustk?-ren ρ (snd t)       = spine?-ren ρ t
mustk?-ren ρ ⌜base⌝        = refl
mustk?-ren ρ ⌜Nat⌝ = refl
mustk?-ren ρ ⌜Unit⌝ = refl
mustk?-ren ρ (⌜Π⌝ c d)     = refl
mustk?-ren ρ (⌜Σ⌝ c d)     = refl
mustk?-ren ρ (⌜Hom⌝ c a b) = refl
mustk?-ren ρ (⌜Id⌝ c a b)  = refl
mustk?-ren ρ (hrefl c t)   = refl
mustk?-ren ρ (idrefl c t)  = refl
mustk?-ren ρ (tr d p e)    = trstk?-ren ρ d p
mustk?-ren ρ (ap c b p)    = apstk?-ren ρ p
mustk?-ren ρ (jsub d p e)  = idstk?-ren ρ p
mustk?-ren ρ unit          = refl
mustk?-ren ρ nzero         = refl
mustk?-ren ρ (nsuc n)      = refl
mustk?-ren ρ (natrec z s n) = natstk?-ren ρ n
mustk?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
mustk?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
mustk?-ren ρ (⌜Fin⌝ n) = refl
mustk?-ren ρ (con p) = refl
mustk?-ren ρ (dι j) = refl
mustk?-ren ρ (dσ S f) = refl
mustk?-ren ρ (dρ j C) = refl
mustk?-ren ρ (dpay I D C i) = dstk?-ren ρ C
mustk?-ren ρ (dih D e C p) = dstk?-ren ρ C
mustk?-ren ρ fzero = refl
mustk?-ren ρ (fsuc t) = refl
mustk?-ren ρ (fcase t a b) = finstk?-ren ρ t
mustk?-ren ρ (fcase0 t) = refl
mustk?-ren ρ (psplit b q) = spine?-ren ρ q

trstk?-ren ρ d (var x)       = refl
trstk?-ren ρ d (lam f)       = trlam?-ren ρ d
trstk?-ren ρ d (app t u)     = spine?-ren ρ t
trstk?-ren ρ d (pair a b)    = refl
trstk?-ren ρ d (absurd c e)       = refl
trstk?-ren ρ d (ordtr a t u p q)  = ordstk?-ren ρ a t u
trstk?-ren ρ d (fst t)       = spine?-ren ρ t
trstk?-ren ρ d (snd t)       = spine?-ren ρ t
trstk?-ren ρ d ⌜base⌝        = refl
trstk?-ren ρ d ⌜Nat⌝ = refl
trstk?-ren ρ d ⌜Unit⌝ = refl
trstk?-ren ρ d (⌜Π⌝ c e)     = refl
trstk?-ren ρ d (⌜Σ⌝ c e)     = refl
trstk?-ren ρ d (⌜Hom⌝ c a b) = refl
trstk?-ren ρ (absurd d₂ e₂) (hrefl c t)   = stablecd?-ren ρ c
trstk?-ren ρ (ordtr d₁ d₂ d₃ d₄ d₅) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (var x) (hrefl c t)          = nopw?-ren ρ c
trstk?-ren ρ (lam b) (hrefl c t)          = stablecd?-ren ρ c
trstk?-ren ρ (app f u) (hrefl c t)        = stablecd?-ren ρ c
trstk?-ren ρ (pair a b) (hrefl c t)       = stablecd?-ren ρ c
trstk?-ren ρ (fst q) (hrefl c t)          = stablecd?-ren ρ c
trstk?-ren ρ (snd q) (hrefl c t)          = stablecd?-ren ρ c
trstk?-ren ρ ⌜base⌝ (hrefl c t)           = stablecd?-ren ρ c
trstk?-ren ρ ⌜Nat⌝ (hrefl c t)            = stablecd?-ren ρ c
trstk?-ren ρ ⌜Unit⌝ (hrefl c t)           = stablecd?-ren ρ c
trstk?-ren ρ (⌜Π⌝ c₁ d₁) (hrefl c t)      = stablecd?-ren ρ c
trstk?-ren ρ (⌜Σ⌝ c₁ d₁) (hrefl c t)      = stablecd?-ren ρ c
trstk?-ren ρ (⌜Hom⌝ c₁ a₁ b₁) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (hrefl c₁ t₁) (hrefl c t)    = stablecd?-ren ρ c
trstk?-ren ρ (tr d₁ p₁ e₁) (hrefl c t)    = stablecd?-ren ρ c
trstk?-ren ρ (ap c₁ b₁ p₁) (hrefl c t)    = stablecd?-ren ρ c
trstk?-ren ρ (⌜Id⌝ c₁ a₁ b₁) (hrefl c t)  = stablecd?-ren ρ c
trstk?-ren ρ (idrefl c₁ t₁) (hrefl c t)   = stablecd?-ren ρ c
trstk?-ren ρ (jsub d₁ p₁ e₁) (hrefl c t)  = stablecd?-ren ρ c
trstk?-ren ρ unit (hrefl c t)             = stablecd?-ren ρ c
trstk?-ren ρ nzero (hrefl c t)            = stablecd?-ren ρ c
trstk?-ren ρ (nsuc d₁) (hrefl c t)        = stablecd?-ren ρ c
trstk?-ren ρ (natrec d₁ d₂ d₃) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ d (tr e q w)    = trstk?-ren ρ e q
trstk?-ren ρ d (ap c b p)    = apstk?-ren ρ p
trstk?-ren ρ d (⌜Id⌝ c a b)  = refl
trstk?-ren ρ d (idrefl c t)  = refl
trstk?-ren ρ d (jsub d₁ p e) = idstk?-ren ρ p
trstk?-ren ρ d unit          = refl
trstk?-ren ρ d nzero         = refl
trstk?-ren ρ d (nsuc n)      = refl
trstk?-ren ρ d (natrec z w n) = natstk?-ren ρ n
trstk?-ren ρ d (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
trstk?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) (hrefl c t)           = stablecd?-ren ρ c
trstk?-ren ρ (ielim dD iˣ dm dt) (hrefl c t)   = stablecd?-ren ρ c
trstk?-ren ρ d (ielim D iˣ ms t) = mustk?-ren ρ t
trstk?-ren ρ d (⌜Fin⌝ n) = refl
trstk?-ren ρ d (con p) = refl
trstk?-ren ρ d (dι j) = refl
trstk?-ren ρ d (dσ S f) = refl
trstk?-ren ρ d (dρ j C) = refl
trstk?-ren ρ d (dpay I D C i) = dstk?-ren ρ C
trstk?-ren ρ d (dih D e C p) = dstk?-ren ρ C
trstk?-ren ρ d fzero = refl
trstk?-ren ρ d (fsuc t) = refl
trstk?-ren ρ d (fcase t a b) = finstk?-ren ρ t
trstk?-ren ρ d (fcase0 t) = refl
trstk?-ren ρ d (psplit b q) = spine?-ren ρ q
trstk?-ren ρ (⌜Fin⌝ n) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (con p) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (dι j) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (dσ S f) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (dρ j C) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (dpay I D C i) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (dih D e C p) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ fzero (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (fsuc t₀) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (fcase t₀ a b) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (fcase0 t₀) (hrefl c t) = stablecd?-ren ρ c
trstk?-ren ρ (psplit b q) (hrefl c t) = stablecd?-ren ρ c

nopw?-ren ρ (var x)       = refl
nopw?-ren ρ (lam t)       = refl
nopw?-ren ρ (app t u)     = spine?-ren ρ t
nopw?-ren ρ (pair a b)    = refl
nopw?-ren ρ (absurd c e)       = refl
nopw?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
nopw?-ren ρ (fst t)       = spine?-ren ρ t
nopw?-ren ρ (snd t)       = spine?-ren ρ t
nopw?-ren ρ ⌜base⌝        = refl
nopw?-ren ρ ⌜Nat⌝ = refl
nopw?-ren ρ ⌜Unit⌝ = refl
nopw?-ren ρ (⌜Π⌝ c d)     = refl
nopw?-ren ρ (⌜Σ⌝ c d)     = refl
nopw?-ren ρ (⌜Hom⌝ c a b) = nopw?-ren ρ c
nopw?-ren ρ (hrefl c t)   = refl
nopw?-ren ρ (tr d p e)    = trstk?-ren ρ d p
nopw?-ren ρ (ap c b p)    = refl
nopw?-ren ρ (⌜Id⌝ c a b)  = refl
nopw?-ren ρ (idrefl c t)  = refl
nopw?-ren ρ (jsub d p e)  = idstk?-ren ρ p
nopw?-ren ρ unit          = refl
nopw?-ren ρ nzero         = refl
nopw?-ren ρ (nsuc n)      = refl
nopw?-ren ρ (natrec z s n) = natstk?-ren ρ n
nopw?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
nopw?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
nopw?-ren ρ (⌜Fin⌝ n) = refl
nopw?-ren ρ (con p) = refl
nopw?-ren ρ (dι j) = refl
nopw?-ren ρ (dσ S f) = refl
nopw?-ren ρ (dρ j C) = refl
nopw?-ren ρ (dpay I D C i) = dstk?-ren ρ C
nopw?-ren ρ (dih D e C p) = dstk?-ren ρ C
nopw?-ren ρ fzero = refl
nopw?-ren ρ (fsuc t) = refl
nopw?-ren ρ (fcase t a b) = finstk?-ren ρ t
nopw?-ren ρ (fcase0 t) = refl
nopw?-ren ρ (psplit b q) = spine?-ren ρ q

deadmot?-ren ρ (var x)       = refl
deadmot?-ren ρ (lam t)       = refl
deadmot?-ren ρ (app t u)     = spine?-ren ρ t
deadmot?-ren ρ (pair a b)    = refl
deadmot?-ren ρ (absurd c e)       = refl
deadmot?-ren ρ (ordtr a t u p q) = ordstk?-ren ρ a t u
deadmot?-ren ρ (fst t)       = spine?-ren ρ t
deadmot?-ren ρ (snd t)       = spine?-ren ρ t
deadmot?-ren ρ ⌜base⌝        = refl
deadmot?-ren ρ ⌜Nat⌝ = refl
deadmot?-ren ρ ⌜Unit⌝ = refl
deadmot?-ren ρ (⌜Π⌝ c d)     = refl
deadmot?-ren ρ (⌜Σ⌝ c d)     = refl
deadmot?-ren ρ (⌜Hom⌝ c a b) = deadmot?-ren ρ c
deadmot?-ren ρ (hrefl c t)   = deadmot?-ren ρ c
deadmot?-ren ρ (tr d p e)    = trstk?-ren ρ d p
deadmot?-ren ρ (ap c b p)    = apstk?-ren ρ p
deadmot?-ren ρ (⌜Id⌝ c a b)  = refl
deadmot?-ren ρ (idrefl c t)  = refl
deadmot?-ren ρ (jsub d p e)  = idstk?-ren ρ p
deadmot?-ren ρ unit          = refl
deadmot?-ren ρ nzero         = refl
deadmot?-ren ρ (nsuc n)      = refl
deadmot?-ren ρ (natrec z s n) = natstk?-ren ρ n
deadmot?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ) = refl
deadmot?-ren ρ (ielim D iˣ ms t) = mustk?-ren ρ t
deadmot?-ren ρ (⌜Fin⌝ n) = refl
deadmot?-ren ρ (con p) = refl
deadmot?-ren ρ (dι j) = refl
deadmot?-ren ρ (dσ S f) = refl
deadmot?-ren ρ (dρ j C) = refl
deadmot?-ren ρ (dpay I D C i) = dstk?-ren ρ C
deadmot?-ren ρ (dih D e C p) = dstk?-ren ρ C
deadmot?-ren ρ fzero = refl
deadmot?-ren ρ (fsuc t) = refl
deadmot?-ren ρ (fcase t a b) = finstk?-ren ρ t
deadmot?-ren ρ (fcase0 t) = refl
deadmot?-ren ρ (psplit b q) = spine?-ren ρ q

trlam?-ren ρ (var vz)     = refl
trlam?-ren ρ (var (vs x)) = refl
trlam?-ren ρ (lam t)      = refl
trlam?-ren ρ (app t u)    = refl
trlam?-ren ρ (pair a b)   = refl
trlam?-ren ρ (absurd c e)      = refl
-- ⚠ NOT a delegation to `ordstk?-ren`: `trlam?` has no `ordtr` row at
-- all — it is `false` by catch-all — and the argument lives in `Γ ∙`,
-- so the delegation would not even typecheck.  Same as `absurd`.
trlam?-ren ρ (ordtr a t u p q) = refl
trlam?-ren ρ (fst t)      = refl
trlam?-ren ρ (snd t)      = refl
trlam?-ren ρ ⌜base⌝       = refl
trlam?-ren ρ ⌜Nat⌝        = refl
trlam?-ren ρ ⌜Unit⌝       = refl
trlam?-ren ρ (⌜Π⌝ c d)    = refl
trlam?-ren ρ (⌜Σ⌝ c d)    = refl
trlam?-ren ρ (⌜Hom⌝ c a (var vz))     = deadmot?-ren (extR ρ) c
trlam?-ren ρ (⌜Hom⌝ c a (var (vs x))) = refl
trlam?-ren ρ (⌜Hom⌝ c a (lam m))      = refl
trlam?-ren ρ (⌜Hom⌝ c a (app m₁ m₂))  = refl
trlam?-ren ρ (⌜Hom⌝ c a (pair m₁ m₂)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (absurd m₁ m₂)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (ordtr m₁ m₂ m₃ m₄ m₅)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (fst m))      = refl
trlam?-ren ρ (⌜Hom⌝ c a (snd m))      = refl
trlam?-ren ρ (⌜Hom⌝ c a ⌜base⌝)       = refl
trlam?-ren ρ (⌜Hom⌝ c a ⌜Nat⌝)        = refl
trlam?-ren ρ (⌜Hom⌝ c a ⌜Unit⌝)       = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜Π⌝ m₁ m₂))  = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜Σ⌝ m₁ m₂))  = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜Hom⌝ m₁ m₂ m₃)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (hrefl m₁ m₂))    = refl
trlam?-ren ρ (⌜Hom⌝ c a (tr m₁ m₂ m₃))    = refl
trlam?-ren ρ (⌜Hom⌝ c a (ap m₁ m₂ m₃))    = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜Id⌝ m₁ m₂ m₃))  = refl
trlam?-ren ρ (⌜Hom⌝ c a (idrefl m₁ m₂))   = refl
trlam?-ren ρ (⌜Hom⌝ c a (jsub m₁ m₂ m₃))  = refl
trlam?-ren ρ (⌜Hom⌝ c a unit)             = refl
trlam?-ren ρ (⌜Hom⌝ c a nzero)            = refl
trlam?-ren ρ (⌜Hom⌝ c a (nsuc m))         = refl
trlam?-ren ρ (⌜Hom⌝ c a (con m₁)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (dι m₁)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (dσ m₁ m₂)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (dρ m₁ m₂)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (dpay m₁ m₂ m₃ m₄)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (dih m₁ m₂ m₃ m₄)) = refl
trlam?-ren ρ (⌜Hom⌝ c a fzero) = refl
trlam?-ren ρ (⌜Hom⌝ c a (fsuc m₁)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (fcase m₁ m₂ m₃)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (fcase0 m₁)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (psplit m₁ m₂)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜Fin⌝ n₀)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (natrec m₁ m₂ m₃)) = refl
trlam?-ren ρ (hrefl c t)  = refl
trlam?-ren ρ (tr d p e)   = refl
trlam?-ren ρ (ap c b p)   = refl
trlam?-ren ρ (⌜Id⌝ c a b) = refl
trlam?-ren ρ (idrefl c t) = refl
trlam?-ren ρ (jsub d p e) = refl
trlam?-ren ρ unit         = refl
trlam?-ren ρ nzero        = refl
trlam?-ren ρ (nsuc n)     = refl
trlam?-ren ρ (natrec z w n) = refl
trlam?-ren ρ (⌜IMu⌝ Dˣ Iˣ iˣ)       = refl
trlam?-ren ρ (⌜Hom⌝ c a (ielim mD iˣ mm mt)) = refl
trlam?-ren ρ (⌜Hom⌝ c a (⌜IMu⌝ Dˣ Iˣ iˣ)) = refl
trlam?-ren ρ (ielim D iˣ ms t) = refl
trlam?-ren ρ (⌜Fin⌝ n) = refl
trlam?-ren ρ (con p) = refl
trlam?-ren ρ (dι j) = refl
trlam?-ren ρ (dσ S f) = refl
trlam?-ren ρ (dρ j C) = refl
trlam?-ren ρ (dpay I D C i) = refl
trlam?-ren ρ (dih D e C p) = refl
trlam?-ren ρ fzero = refl
trlam?-ren ρ (fsuc t) = refl
trlam?-ren ρ (fcase t a b) = refl
trlam?-ren ρ (fcase0 t) = refl
trlam?-ren ρ (psplit b q) = refl


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
  sh-Unit : StkHd (Unit {Γ})
  -- ★★ WF stage B: `sh-Nat : StkHd Nat` is GONE — the order rules make
  -- `Hom Nat a b` compute, so a `Nat` ambient is NOT a stuck head.
  -- What survives is the ENDPOINT-keyed stuck order-hom: `Hom Nat a b`
  -- is inert exactly when its endpoints never expose numeral heads.
  -- Note this arm produces `StkHd` of the whole `Hom`, which is why
  -- `⊩₀Hom`/`⊩₁Hom` now take `StkHd (Hom H a b)` rather than `StkHd H`.
  sh-NatH : {a b : RTm Γ} → homnat? a b ≡ true → StkHd (Hom Nat a b)
  -- ★★ LEVITATED FAMILIES: no rule computes `Hom` over a family, a tag
  -- type, a description type, or the hypotheses' type at a STUCK
  -- telescope — they are stuck heads, `base`-style.  (A canonical
  -- telescope's `DIh` computes to `Unit`/`Σ'`, both stuck already.)
  sh-IMu  : {I D i : RTm Γ} → StkHd (IMu I D i)
  sh-Fin  : {n : ℕ} → StkHd (Fin {Γ} n)
  sh-Desc : {I : RTm Γ} → StkHd (Desc I)
  sh-DIhNe : {D C p : RTm Γ} {M : RTy ((Γ ∙) ∙)} → Ne C → StkHd (DIh D M C p)

stkhd-red : {H H' : RTy Γ} → StkHd H → H ⟶ᵀ H' → StkHd H'
stkhd-red (sh-ne ()) El-⌜base⌝
stkhd-red (sh-ne ()) (El-⌜Π⌝ _ _)
stkhd-red (sh-ne ()) (El-⌜Σ⌝ _ _)
stkhd-red (sh-ne n)  (ξ-El r)    = sh-ne (ne-red n r)
stkhd-red sh-Id (ξ-Idᵀ r) = sh-Id
stkhd-red sh-Id (ξ-Idˡ r) = sh-Id
stkhd-red sh-Id (ξ-Idʳ r) = sh-Id
stkhd-red sh-IMu (ξ-IMuᴵ r) = sh-IMu
stkhd-red sh-IMu (ξ-IMuᴰ r) = sh-IMu
stkhd-red sh-IMu (ξ-IMuⁱ r) = sh-IMu
stkhd-red sh-Fin ()
stkhd-red sh-Desc (ξ-Desc r) = sh-Desc
stkhd-red (sh-DIhNe ()) (DIh-ι _ _ _ _)
stkhd-red (sh-DIhNe ()) (DIh-σ _ _ _ _ _)
stkhd-red (sh-DIhNe ()) (DIh-ρ _ _ _ _ _)
stkhd-red (sh-DIhNe n) (ξ-DIhᴰ r) = sh-DIhNe n
stkhd-red (sh-DIhNe n) (ξ-DIhᴹ r) = sh-DIhNe n
stkhd-red (sh-DIhNe n) (ξ-DIhᶜ r) = sh-DIhNe (ne-red n r)
stkhd-red (sh-DIhNe n) (ξ-DIhᵖ r) = sh-DIhNe n
stkhd-red sh-Unit ()
stkhd-red sh-Σ       (ξ-Σˡ r)    = sh-Σ
stkhd-red sh-Σ       (ξ-Σʳ r)    = sh-Σ
stkhd-red (sh-Hom ()) (Hom-U _ _)
stkhd-red (sh-Hom ()) (Hom-Π _ _ _ _)
stkhd-red (sh-Hom s) (ξ-Homᵀ r) = sh-Hom (stkhd-red s r)
stkhd-red (sh-Hom s) (ξ-Homˡ r) = sh-Hom s
stkhd-red (sh-Hom s) (ξ-Homʳ r) = sh-Hom s
stkhd-red (sh-Hom ()) (Hom-Nat-z _)
stkhd-red (sh-Hom ()) (Hom-Nat-sz _)
stkhd-red (sh-Hom ()) (Hom-Nat-ss _ _)
stkhd-red (sh-NatH ()) (Hom-Nat-z _)
stkhd-red (sh-NatH ()) (Hom-Nat-sz _)
stkhd-red (sh-NatH ()) (Hom-Nat-ss _ _)
stkhd-red (sh-NatH k) (ξ-Homᵀ ())
stkhd-red (sh-NatH {a = a} {b = b} k) (ξ-Homˡ r) =
  sh-NatH (homnat?-redˡ {u = b} r k)
stkhd-red (sh-NatH {a = a} {b = b} k) (ξ-Homʳ r) =
  sh-NatH (homnat?-redʳ {t = a} r k)

record HomStk {Γ} (C : RTy Γ) : Set where
  constructor mkHomStk
  field
    hH    : RTy Γ
    ha hb : RTm Γ
    hstk  : StkHd (Hom hH ha hb)
    heq   : C ≡ Hom hH ha hb

-- reducts of a stuck `Hom` are stuck `Hom`s — the shape lemma the transfer
-- layer consumes, exactly `El-ne-reduct`'s pattern.
Hom-stk-reduct : {H : RTy Γ} {a b : RTm Γ} {C : RTy Γ} →
                 StkHd (Hom H a b) → Hom H a b ⟶ᵀ* C → HomStk C
-- ★ WF stage B: with the witness on the WHOLE `Hom`, a stuck order-hom
-- provably stays `Hom`-headed — the three order rules are refuted by
-- the endpoint key (`sh-NatH`) or by `StkHd Nat` being uninhabited
-- (`sh-Hom`), so the recursion never leaves the shape.
Hom-stk-reduct s doneᵀ = mkHomStk _ _ _ s refl
Hom-stk-reduct (sh-Hom ()) (stepᵀ (Hom-U _ _) p)
Hom-stk-reduct (sh-Hom ()) (stepᵀ (Hom-Π _ _ _ _) p)
Hom-stk-reduct (sh-Hom ()) (stepᵀ (Hom-Nat-z _) p)
Hom-stk-reduct (sh-Hom ()) (stepᵀ (Hom-Nat-sz _) p)
Hom-stk-reduct (sh-Hom ()) (stepᵀ (Hom-Nat-ss _ _) p)
Hom-stk-reduct (sh-Hom s) (stepᵀ (ξ-Homᵀ r) p) =
  Hom-stk-reduct (sh-Hom (stkhd-red s r)) p
Hom-stk-reduct (sh-Hom s) (stepᵀ (ξ-Homˡ r) p) = Hom-stk-reduct (sh-Hom s) p
Hom-stk-reduct (sh-Hom s) (stepᵀ (ξ-Homʳ r) p) = Hom-stk-reduct (sh-Hom s) p
Hom-stk-reduct (sh-NatH ()) (stepᵀ (Hom-Nat-z _) p)
Hom-stk-reduct (sh-NatH ()) (stepᵀ (Hom-Nat-sz _) p)
Hom-stk-reduct (sh-NatH ()) (stepᵀ (Hom-Nat-ss _ _) p)
Hom-stk-reduct (sh-NatH k) (stepᵀ (ξ-Homᵀ ()) p)
Hom-stk-reduct (sh-NatH {a = a} {b = b} k) (stepᵀ (ξ-Homˡ r) p) =
  Hom-stk-reduct (sh-NatH (homnat?-redˡ {u = b} r k)) p
Hom-stk-reduct (sh-NatH {a = a} {b = b} k) (stepᵀ (ξ-Homʳ r) p) =
  Hom-stk-reduct (sh-NatH (homnat?-redʳ {t = a} r k)) p

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

-- ★★ WF stage A — the THIRD payload flavor.  A semantic natural
-- number is one that REACHES a numeral (or is stuck neutral): exactly
-- the induction principle `fund`'s `⊢natrec` recurses on, and the
-- reason `natrec` computes on every closed member.  The shape mirrors
-- `SN` (neutral / constructor / head-expansion), so every transport is
-- the SN transport.
data NatMem {Γ} : RTm Γ → Set where
  nm-ne   : {t : RTm Γ} → SNe t → NatMem t
  nm-zero : NatMem (nzero {Γ})
  nm-suc  : {n : RTm Γ} → NatMem n → NatMem (nsuc n)
  nm-exp  : {t t' : RTm Γ} → SNRed t t' → NatMem t' → NatMem t

-- forward closure along the head strategy — `sn-whred`'s proof, by
-- determinism of `SNRed`.
natmem-whred : {t t' : RTm Γ} → NatMem t → SNRed t t' → NatMem t'
natmem-whred (nm-ne n)   r = nm-ne (sne-whred n r)
natmem-whred (nm-exp r₀ h) r with snr-det r₀ r
... | refl = h

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

------------------------------------------------------------------------
-- ★★★ LEVITATED FAMILIES — the membership payload (SPIKE-LEVITATION S0).
--
-- ⚠⚠ WHY THIS LIVES HERE, BEFORE `⊩₀`, AND MENTIONS NOTHING OF IT.
--   `_⊩₀∋_` is negative at `Π`, and a datatype mutual with it inherits
--   that (gates 6/6b; S0's control).  So the payload takes PREDICATES:
--   `IKPred` is a telescope's shape with a predicate at each `dσ` field,
--   and `ikpredsOf` (inside the block) builds it from the WITNESSES the
--   interpretation `IKInterp` stores.
--
-- ★ A telescope is a TERM now, so its shape is reached by HEAD REDUCTION:
--   neutral / canonical former / head expansion — `NatMem`'s shape, so
--   every transport is the SN transport.
------------------------------------------------------------------------

data IKPred (Γ : Cx) : RTm Γ → Set₁ where
  ikp-ne  : {C : RTm Γ} → IKPred Γ C
  ikp-ι   : {j : RTm Γ} → IKPred Γ (dι j)
  ikp-σ   : {S f : RTm Γ} → (Q : RTm Γ → Set) →
            ((v : RTm Γ) → Q v → IKPred Γ (app f v)) → IKPred Γ (dσ S f)
  ikp-ρ   : {j C : RTm Γ} → IKPred Γ C → IKPred Γ (dρ j C)
  ikp-exp : {C C' : RTm Γ} → SNRed C C' → IKPred Γ C' → IKPred Γ C

-- the payload predicate at index `i`, walked in lockstep with `dpay`: the
-- `dι j` leaf is the index EQUATION (`⌜Id⌝ I j i`, i.e. `⊩₀Id`'s
-- membership — Fording is IN the payload now), a `dσ` field is a member of
-- its code and the tail at its VALUE, a `dρ` field is a recursive member AT
-- ITS OWN INDEX `j`.  PROJECTION-BASED and SN at every node, for the
-- reasons the list form's `Lift` recorded (the `⊢ielim` direction runs it
-- backward into a `⊩₀Σ` member).
ILift : {C : RTm Γ} → IKPred Γ C → (RTm Γ → RTm Γ → Set) → RTm Γ → RTm Γ → Set
ILift ikp-ne              P i t = SN t
ILift (ikp-ι {j = j})     P i t = SN t × IdPay j i t
ILift (ikp-σ Q k)         P i t = SN t × Σ (Q (fst t)) (λ q → ILift (k (fst t) q) P i (snd t))
ILift (ikp-ρ {j = j} k)   P i t = SN t × ((SN (fst t) × P j (fst t)) × ILift k P i (snd t))
ILift (ikp-exp r k)       P i t = ILift k P i t

-- ★ a member of the family at index `i`: neutral / constructor / head
--   expansion.  `imm-con` does NOT constrain `i` — the payload's `dι` leaf
--   carries the index equation, so the Fording argument is now a TYPE.
data IMuMem {Γ} {D : RTm Γ} (kp : IKPred Γ D) : RTm Γ → RTm Γ → Set where
  imm-ne  : {i t : RTm Γ} → SNe t → IMuMem kp i t
  imm-con : {i p : RTm Γ} → ILift kp (IMuMem kp) i p → IMuMem kp i (con p)
  imm-exp : {i t t' : RTm Γ} → SNRed t t' → IMuMem kp i t' → IMuMem kp i t

imumem-whred : {D : RTm Γ} {kp : IKPred Γ D} {i t t' : RTm Γ} →
               IMuMem kp i t → SNRed t t' → IMuMem kp i t'
imumem-whred (imm-ne n)     r = imm-ne (sne-whred n r)
imumem-whred (imm-exp r₀ h) r with snr-det r₀ r
... | refl = h

-- ★ the TAGS: `NatMem`'s shape, indexed by the bound so `Fin 0` is EMPTY
--   on canonical forms (what `fcase0`'s canonicity rests on).
data FinMem {Γ} : ℕ → RTm Γ → Set where
  fm-ne   : {n : ℕ} {t : RTm Γ} → SNe t → FinMem n t
  fm-zero : {n : ℕ} → FinMem (suc n) (fzero {Γ})
  fm-suc  : {n : ℕ} {t : RTm Γ} → FinMem n t → FinMem (suc n) (fsuc t)
  fm-exp  : {n : ℕ} {t t' : RTm Γ} → SNRed t t' → FinMem n t' → FinMem n t

finmem-whred : {n : ℕ} {t t' : RTm Γ} → FinMem n t → SNRed t t' → FinMem n t'
finmem-whred (fm-ne n)     r = fm-ne (sne-whred n r)
finmem-whred (fm-exp r₀ h) r with snr-det r₀ r
... | refl = h

------------------------------------------------------------------------
-- ★★★ WF-axis stage E: `ordtr` IS STRONGLY NORMALIZING.
--
-- This is `ordtr`'s whole semantic content, and it is the exact mirror
-- of `homNatSem`'s own recursion: both walk the SAME three `NatMem`
-- payloads in the SAME order (`a`, then `t`, then `u`), because that
-- order is `ordstk?`'s dispatch order, which is the serialization the
-- `SNRed` xi's were built around.
--
-- ★ WHY THIS IS ALL `fund` NEEDS.  Membership at level 1 IGNORES the
-- reduction chain — every leaf `homNatSem` lands on (`⊩₁Hom`, `⊩₁Unit`,
-- `⊩₁base`) has `_ ⊩₁∋ t = SN t` — so `homNatSem a u … ⊩₁∋ x` is
-- DEFINITIONALLY `SN x`.  The `⊢ordtr` case of `fund` carries no
-- conversion plumbing at all; it is this lemma and nothing else.
--
-- The recursion is lexicographic on the three `NatMem`s: the `a`-steps
-- shrink the first, the `t`-steps the second with the first fixed, the
-- `u`-steps the third — and `ordtr-sss` shrinks all three at once.
-- ★ NO fuel, NO `Acc`, NO measure: the numeral payloads ARE the
-- induction, exactly as in stage A's `natrec` worker.
------------------------------------------------------------------------
sn-ordtr : {Γ : Cx} (a t u p q : RTm Γ) →
           SN a → NatMem a → SN t → NatMem t → SN u → NatMem u →
           SN p → SN q → SN (ordtr a t u p q)

private
  snsuc-inv⁰ : {Γ : Cx} {k : RTm Γ} → SN (nsuc k) → SN k
  snsuc-inv⁰ (sn-nsuc h) = h

-- a bound that never reaches a numeral makes the whole order neutral.
sn-ordtr a t u p q sa (nm-ne nt) st mt su mu sp sq =
  sn-ne (sne-ordtr sa st su sp sq (natstk→ordstk a t u (sne→natstk nt)))
sn-ordtr a t u p q sa (nm-exp {t' = a'} r ma) st mt su mu sp sq =
  sn-exp (snr-ordtrᵃ r)
         (sn-ordtr a' t u p q (sn-whred sa r) ma st mt su mu sp sq)
-- rule 1: a zero LOWER bound discharges the order outright.
sn-ordtr .nzero t u p q sa nm-zero st mt su mu sp sq =
  sn-exp (snr-ordtr-z st su sp sq) sn-unit
-- under a `nsuc` bound the order fires exactly when BOTH remaining
-- bounds are literal, so `t` is scrutinized next — and `ordstk?`'s
-- `nsuc` clause is `ordS? (natstk? t) u`, which `ordS? true u = true`
-- closes on the nose.
sn-ordtr .(nsuc _) t u p q sa (nm-suc {n = a₀} ma) st (nm-ne nt) su mu sp sq =
  sn-ne (sne-ordtr sa st su sp sq
                   (cong (λ b → ordS? b u) (sne→natstk nt)))
sn-ordtr .(nsuc _) t u p q sa (nm-suc {n = a₀} ma) st (nm-exp {t' = t'} r mt) su mu sp sq =
  sn-exp (snr-ordtrᵗ r)
         (sn-ordtr (nsuc a₀) t' u p q sa (nm-suc ma) (sn-whred st r) mt su mu sp sq)
-- `t = nzero`: now `ordstk?` is `natstk? u`, so `u` decides alone.
sn-ordtr .(nsuc _) .nzero u p q sa (nm-suc {n = a₀} ma) st nm-zero su (nm-ne nu) sp sq =
  sn-ne (sne-ordtr sa st su sp sq (sne→natstk nu))
sn-ordtr .(nsuc _) .nzero u p q sa (nm-suc {n = a₀} ma) st nm-zero su (nm-exp {t' = u'} r mu) sp sq =
  sn-exp (snr-ordtrᵘᶻ r)
         (sn-ordtr (nsuc a₀) nzero u' p q sa (nm-suc ma) st nm-zero (sn-whred su r) mu sp sq)
-- rule 2: `0 ≤ 0` under a successor bound — the proof `p` survives.
sn-ordtr .(nsuc _) .nzero .nzero p q sa (nm-suc {n = a₀} ma) st nm-zero su nm-zero sp sq =
  sn-exp (snr-ordtr-szz (snsuc-inv⁰ sa) sq) sp
-- ★ rule 4 — STAGE D'S FIRST REAL CUSTOMER.  `nzero ≤ nsuc u₀` is
-- impossible under a `nsuc` bound, and `absurd` at the ⌜Hom⌝ code is
-- what discharges it.  The code is SN because both endpoints are.
sn-ordtr .(nsuc _) .nzero .(nsuc _) p q sa (nm-suc {n = a₀} ma) st nm-zero su (nm-suc {n = u₀} mu) sp sq =
  sn-exp (snr-ordtr-szs sq)
         (sn-ne (sne-absurd (sn-cH sn-cNat (snsuc-inv⁰ sa) (snsuc-inv⁰ su)) sp))
-- `t = nsuc t₀`: `natstk? (nsuc t₀)` is `false`, so again `u` decides.
sn-ordtr .(nsuc _) .(nsuc _) u p q sa (nm-suc {n = a₀} ma) st (nm-suc {n = t₀} mt) su (nm-ne nu) sp sq =
  sn-ne (sne-ordtr sa st su sp sq (sne→natstk nu))
sn-ordtr .(nsuc _) .(nsuc _) u p q sa (nm-suc {n = a₀} ma) st (nm-suc {n = t₀} mt) su (nm-exp {t' = u'} r mu) sp sq =
  sn-exp (snr-ordtrᵘˢ r)
         (sn-ordtr (nsuc a₀) (nsuc t₀) u' p q sa (nm-suc ma) st (nm-suc mt)
                   (sn-whred su r) mu sp sq)
-- rule 3: `t ≤ 0` forces the chain to collapse onto `q`.
sn-ordtr .(nsuc _) .(nsuc _) .nzero p q sa (nm-suc {n = a₀} ma) st (nm-suc {n = t₀} mt) su nm-zero sp sq =
  sn-exp (snr-ordtr-ssz (snsuc-inv⁰ sa) (snsuc-inv⁰ st) sp) sq
-- ★ rule 5 — THE ONLY GENUINELY RECURSIVE ROW: peel one successor off
-- all three bounds at once.  This is transitivity's actual content, and
-- the three payloads shrink together.
sn-ordtr .(nsuc _) .(nsuc _) .(nsuc _) p q sa (nm-suc {n = a₀} ma) st (nm-suc {n = t₀} mt) su (nm-suc {n = u₀} mu) sp sq =
  sn-exp snr-ordtr-sss
         (sn-ordtr a₀ t₀ u₀ p q (snsuc-inv⁰ sa) ma (snsuc-inv⁰ st) mt
                   (snsuc-inv⁰ su) mu sp sq)

data ⊩₀_ {Γ} : RTy Γ → Set
_⊩₀∋_ : {Γ : Cx} {A : RTy Γ} → ⊩₀ A → RTm Γ → Set

-- ★★ WHERE THE FIELD PREDICATES COME FROM.  `⊩₀IMu` carries WITNESSES —
--   an interpretation `IKInterp` of the telescope, built from ordinary
--   `⊩₀`s, so `⊩₀` STAYS IN `Set` — and `ikpredsOf` turns it into the
--   `IKPred` that `IMuMem` wants.  The split is the whole trick (S0):
--     · `IMuMem` takes PREDICATES, so it is not mutual with `_⊩₀∋_` and
--       stays strictly positive;
--     · `⊩₀IMu` carries WITNESSES, so `irrel₀` has something to recurse on.
--   `IKInterp` is ALSO the membership of `Desc I` at level 1 (`⊩₁Desc`):
--   a description's meaning IS its interpretation (S0's `toIK` is the
--   identity).  ⚠ it stores the index type's interpretation's MEMBERS at
--   `dρ` fields — `⊢ielim`'s induction hypothesis needs the recursive
--   field's index to be valid.
data IKInterp {Γ} {I : RTm Γ} (⊩I : ⊩₀ (El I)) : RTm Γ → Set
ikpredsOf : {I C : RTm Γ} {⊩I : ⊩₀ (El I)} → IKInterp ⊩I C → IKPred Γ C

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
         → A ⟶ᵀ* Hom H a b → StkHd (Hom H a b) → ⊩₀ A
  -- ★ the two-former kernel: `Id` at level 0 (`⌜Id⌝` decodes).  The
  -- MEMBERSHIP carries the ENDPOINT-JOIN PAYLOAD (SPIKE-TWOFORMER §4):
  -- reaching a reflexivity witnesses the endpoints' confluence join —
  -- what makes fund's `jsub` transfer conversion-based at ARBITRARY
  -- motives.
  ⊩₀Id   : {A H : RTy Γ} {a b : RTm Γ}
         → A ⟶ᵀ* Id H a b → ⊩₀ A
  -- ★★ WF stage C: the datatypes reach LEVEL 0 for the first time.
  -- Stage A could skip them — no code decoded to `Unit`/`Nat`, so the
  -- SMALL types never saw them.  ⌜Nat⌝ ∈ U changes that twice over:
  -- `El ⌜Nat⌝ ⟶ᵀ Nat` directly, and `El (⌜Hom⌝ ⌜Nat⌝ a b) ⟶ᵀ*` the
  -- ORDER type, which computes to `Unit` (or `base`).  Membership
  -- mirrors level 1 exactly, `NatMem` payload included.
  ⊩₀Unit : {A : RTy Γ} → A ⟶ᵀ* Unit → ⊩₀ A
  ⊩₀Nat  : {A : RTy Γ} → A ⟶ᵀ* Nat → ⊩₀ A
  -- ★★★ the levitated family: the index type's interpretation and the
  --   telescope's.  ⚠ the reduct's slots are TERMS and step, so two reducts
  --   of one type can differ in all three (`IMu-reduct` relates them).
  --   ⚠ the interpretation is of a CONVERTIBLE REPRESENTATIVE `I₀`/`D₀`,
  --   not of the reduct's own slots: forwarding along a type reduction
  --   then only extends a conversion, and never has to transport an
  --   interpretation along an arbitrary reduction of a TERM (which head
  --   expansion cannot do).  `irrel₀` joins two representatives by
  --   Church–Rosser.
  ⊩₀IMu  : {A : RTy Γ} {I D i I₀ D₀ : RTm Γ} → A ⟶ᵀ* IMu I D i →
           I ≅ I₀ → D ≅ D₀ → (⊩I : ⊩₀ (El I₀)) → IKInterp ⊩I D₀ → ⊩₀ A
  -- ★ the tags (`El-⌜Fin⌝`): inert, `⊩₀Nat`'s shape.
  ⊩₀Fin  : {A : RTy Γ} {n : ℕ} → A ⟶ᵀ* Fin n → ⊩₀ A

data IKInterp {Γ} {I} ⊩I where
  iki-ne  : {C : RTm Γ} → SNe C → IKInterp ⊩I C
  iki-ι   : {j : RTm Γ} → SN j → IKInterp ⊩I (dι j)
  iki-σ   : {S f : RTm Γ} → SN S → SN f → (w : ⊩₀ (El S)) →
            ((v : RTm Γ) → w ⊩₀∋ v → IKInterp ⊩I (app f v)) →
            IKInterp ⊩I (dσ S f)
  iki-ρ   : {j C : RTm Γ} → SN j → ⊩I ⊩₀∋ j → IKInterp ⊩I C →
            IKInterp ⊩I (dρ j C)
  iki-exp : {C C' : RTm Γ} → SNRed C C' → IKInterp ⊩I C' → IKInterp ⊩I C

ikpredsOf (iki-ne n)       = ikp-ne
ikpredsOf (iki-ι _)        = ikp-ι
ikpredsOf (iki-σ _ _ w k)  = ikp-σ (w ⊩₀∋_) (λ v q → ikpredsOf (k v q))
ikpredsOf (iki-ρ _ _ k)    = ikp-ρ (ikpredsOf k)
ikpredsOf (iki-exp r k)    = ikp-exp r (ikpredsOf k)

⊩₀base _     ⊩₀∋ t = SN t
⊩₀ne _ _     ⊩₀∋ t = SN t
⊩₀Π _ ⊩F ⊩G  ⊩₀∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩₀∋ u) → (⊩G u r) ⊩₀∋ app t u)
-- the DEPENDENT pair: the second component's type depends on the first.
⊩₀Σ _ ⊩F ⊩G  ⊩₀∋ t =
  SN t × Σ (⊩F ⊩₀∋ fst t) (λ r → (⊩G (fst t) r) ⊩₀∋ snd t)
⊩₀Hom _ _    ⊩₀∋ t = SN t
⊩₀Id {a = a} {b = b} _ ⊩₀∋ t = SN t × IdPay a b t
⊩₀Unit _     ⊩₀∋ t = SN t
⊩₀Nat _      ⊩₀∋ t = SN t × NatMem t
⊩₀IMu {i = i} _ _ _ ⊩I K ⊩₀∋ t = SN t × IMuMem (ikpredsOf K) i t
⊩₀Fin {n = n} _ ⊩₀∋ t = SN t × FinMem n t

bwd₀ : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩₀ B → ⊩₀ A
bwd₀ p (⊩₀base q)    = ⊩₀base (⟶ᵀ*-trans p q)
bwd₀ p (⊩₀ne q n)    = ⊩₀ne   (⟶ᵀ*-trans p q) n
bwd₀ p (⊩₀Π q ⊩F ⊩G) = ⊩₀Π    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₀ p (⊩₀Σ q ⊩F ⊩G) = ⊩₀Σ    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₀ p (⊩₀Hom q s)   = ⊩₀Hom  (⟶ᵀ*-trans p q) s
bwd₀ p (⊩₀Id q)      = ⊩₀Id   (⟶ᵀ*-trans p q)
bwd₀ p (⊩₀Unit q)    = ⊩₀Unit (⟶ᵀ*-trans p q)
bwd₀ p (⊩₀Nat q)     = ⊩₀Nat  (⟶ᵀ*-trans p q)
bwd₀ p (⊩₀IMu q cI cD ⊩I K) = ⊩₀IMu (⟶ᵀ*-trans p q) cI cD ⊩I K
bwd₀ p (⊩₀Fin q)     = ⊩₀Fin (⟶ᵀ*-trans p q)

-- `bwd₀` only rewrites the REDUCTION WITNESS, never the membership — so
-- both directions are the identity once the interp's head is exposed.
-- (Needed wherever an interp is built by a recursion that wraps each
-- step in `bwd₀`, as `homNatSem₀` does.)
bwd₀-mem : {A B : RTy Γ} (q : A ⟶ᵀ* B) (R : ⊩₀ B) {t : RTm Γ} →
           (bwd₀ q R) ⊩₀∋ t → R ⊩₀∋ t
bwd₀-mem q (⊩₀base _)  h = h
bwd₀-mem q (⊩₀ne _ _)  h = h
bwd₀-mem q (⊩₀Π _ _ _) h = h
bwd₀-mem q (⊩₀Σ _ _ _) h = h
bwd₀-mem q (⊩₀Hom _ _) h = h
bwd₀-mem q (⊩₀Id _)    h = h
bwd₀-mem q (⊩₀Unit _)  h = h
bwd₀-mem q (⊩₀Nat _)   h = h
bwd₀-mem q (⊩₀IMu _ _ _ _ _) h = h
bwd₀-mem q (⊩₀Fin _)   h = h

bwd₀-mem⁻ : {A B : RTy Γ} (q : A ⟶ᵀ* B) (R : ⊩₀ B) {t : RTm Γ} →
            R ⊩₀∋ t → (bwd₀ q R) ⊩₀∋ t
bwd₀-mem⁻ q (⊩₀base _)  h = h
bwd₀-mem⁻ q (⊩₀ne _ _)  h = h
bwd₀-mem⁻ q (⊩₀Π _ _ _) h = h
bwd₀-mem⁻ q (⊩₀Σ _ _ _) h = h
bwd₀-mem⁻ q (⊩₀Hom _ _) h = h
bwd₀-mem⁻ q (⊩₀Id _)    h = h
bwd₀-mem⁻ q (⊩₀Unit _)  h = h
bwd₀-mem⁻ q (⊩₀Nat _)   h = h
bwd₀-mem⁻ q (⊩₀IMu _ _ _ _ _) h = h
bwd₀-mem⁻ q (⊩₀Fin _)   h = h

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

-- ★★★ THE FAMILY HALF OF IRRELEVANCE, mutual with `irrel₀` itself.
--
--   Two interpretations of ONE family type interpret telescopes that are
--   only JOINABLE (they are terms, and the type's reducts may differ in
--   every slot).  `iliftK` walks both in lockstep ALONG A COMMON REDUCT:
--   a head expansion on either side is re-joined by confluence, matching
--   formers recurse (the `dσ` field's membership by `irrel₀` at the joined
--   field codes, the `dρ` field's by `irrelIMu` at the joined index), the
--   `dι` leaf's index equation by `idpay-transfer`, and every mismatch is a
--   shape clash on the common reduct.
--   ⚠ TERMINATION: `irrelIMu` on the membership, `iliftK` on the
--   interpretation it walks (the WHOLE ones, `K₁`/`K₂`, ride along for the
--   recursive field), `irrel₀` on a field witness inside it.
irrelIMu : {I₁ I₂ D₁ D₂ D* : RTm Γ} {⊩I₁ : ⊩₀ (El I₁)} {⊩I₂ : ⊩₀ (El I₂)}
           (K₁ : IKInterp ⊩I₁ D₁) (K₂ : IKInterp ⊩I₂ D₂) → D₁ ⟶* D* → D₂ ⟶* D* →
           {i₁ i₂ i* t : RTm Γ} → i₁ ⟶* i* → i₂ ⟶* i* →
           IMuMem (ikpredsOf K₁) i₁ t → IMuMem (ikpredsOf K₂) i₂ t
iliftK : {I₁ I₂ D₁ D₂ D* : RTm Γ} {⊩I₁ : ⊩₀ (El I₁)} {⊩I₂ : ⊩₀ (El I₂)}
         (K₁ : IKInterp ⊩I₁ D₁) (K₂ : IKInterp ⊩I₂ D₂) → D₁ ⟶* D* → D₂ ⟶* D* →
         {C₁ C₂ C* : RTm Γ} (Kc₁ : IKInterp ⊩I₁ C₁) (Kc₂ : IKInterp ⊩I₂ C₂) →
         C₁ ⟶* C* → C₂ ⟶* C* →
         {i₁ i₂ i* : RTm Γ} → i₁ ⟶* i* → i₂ ⟶* i* → (t : RTm Γ) →
         ILift (ikpredsOf Kc₁) (IMuMem (ikpredsOf K₁)) i₁ t →
         ILift (ikpredsOf Kc₂) (IMuMem (ikpredsOf K₂)) i₂ t

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
-- ★ `Mu` vs `IMu` — DIFFERENT FORMERS, so no common reduct.  `Mu-nf`
--   pins one side syntactically; `IMu-reduct` gives the other's shape.
irrel₀ c (⊩₀Fin p) (⊩₀IMu q _ _ _ _) with joinW c p q
... | E , (mE , iE) with Fin-nf mE
...   | refl with IMu-reduct iE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀IMu p _ _ _ _) (⊩₀Fin q) with joinW c p q
... | E , (iE , mE) with Fin-nf mE
...   | refl with IMu-reduct iE
...     | mkIMuRed _ _ _ () _ _ _
-- ★★★ THE DIAGONAL — the one case with real content, and the reason the
--   `irrelIMu`/`iliftK` transfer layer exists.  ⚠ `⊩₀Mu`'s two reducts are
--   SYNTACTICALLY EQUAL (`Mu-nf` twice, then `refl`).  `⊩₀IMu`'s are not:
--   both are `IMu D I _` but their INDICES can differ, because `IMu`
--   carries a reducible term.  `IMuinj≡` identifies the descriptions and
--   yields the index equation; the two `ridx` witnesses then feed
--   `irrelIMu`, which moves membership along them.  This is exactly the
--   shape `⊩₀Id`'s diagonal uses for its endpoints — the index is not a
--   new phenomenon, it is `Id`'s carried terms again.
-- ★★★ THE DIAGONAL.  The join identifies the two reducts' slots; the two
--   REPRESENTATIVES are then convertible through them, and Church–Rosser
--   gives the common reduct `irrelIMu` walks along.  The index is `Id`'s
--   carried terms again: its two reductions feed `idpay-transfer` at the
--   `dι` leaves.
irrel₀ c (⊩₀IMu p cI₁ cD₁ ⊩I₁ K₁) (⊩₀IMu q cI₂ cD₂ ⊩I₂ K₂) with joinW c p q
... | E , (i₁ , i₂) with IMu-reduct i₁ | IMu-reduct i₂
...   | mkIMuRed I₁' D₁' j₁ eq₁ rI₁ rD₁ r₁ | mkIMuRed I₂' D₂' j₂ eq₂ rI₂ rD₂ r₂
      with IMuinj≡ (trans (sym eq₁) eq₂)
...     | (refl , (refl , refl))
          with church-rosser (ctrn (csym cD₁) (ctrn (hom→≅ rD₁) (ctrn (csym (hom→≅ rD₂)) cD₂)))
...       | D* , (d₁ , d₂) =
          ( (λ _ h → (projl h , irrelIMu K₁ K₂ d₁ d₂ r₁ r₂ (projr h)))
          , (λ _ h → (projl h , irrelIMu K₂ K₁ d₂ d₁ r₂ r₁ (projr h))) )
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


-- ★ WF stage C: the datatype rows of the level-0 clash matrix (the
-- ~28 the level-1 matrix already carries, minus the `U` column that
-- level 0 does not have).
irrel₀ c (⊩₀Unit p) (⊩₀base q) with joinW c p q
... | E , (mE , bE) with base-nf bE
...   | refl with Unit-nf mE
...     | ()
irrel₀ c (⊩₀base p) (⊩₀Unit q) with joinW c p q
... | E , (bE , mE) with base-nf bE
...   | refl with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Unit p) (⊩₀ne q n) with joinW c p q
... | E , (mE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Unit-nf mE
...     | ()
irrel₀ c (⊩₀ne p n) (⊩₀Unit q) with joinW c p q
... | E , (eE , mE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Unit p) (⊩₀Π q _ _) with joinW c p q
... | E , (mE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Π p _ _) (⊩₀Unit q) with joinW c p q
... | E , (πE , mE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Unit p) (⊩₀Σ q _ _) with joinW c p q
... | E , (mE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Σ p _ _) (⊩₀Unit q) with joinW c p q
... | E , (σE , mE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Unit p) (⊩₀Hom q sh) with joinW c p q
... | E , (mE , hE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Hom p sh) (⊩₀Unit q) with joinW c p q
... | E , (hE , mE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Unit p) (⊩₀Id q) with joinW c p q
... | E , (mE , iE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Id p) (⊩₀Unit q) with joinW c p q
... | E , (iE , mE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Unit-nf mE
...     | ()
irrel₀ c (⊩₀Nat p) (⊩₀base q) with joinW c p q
... | E , (mE , bE) with base-nf bE
...   | refl with Nat-nf mE
...     | ()
irrel₀ c (⊩₀base p) (⊩₀Nat q) with joinW c p q
... | E , (bE , mE) with base-nf bE
...   | refl with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Nat p) (⊩₀ne q n) with joinW c p q
... | E , (mE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Nat-nf mE
...     | ()
irrel₀ c (⊩₀ne p n) (⊩₀Nat q) with joinW c p q
... | E , (eE , mE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Nat p) (⊩₀Π q _ _) with joinW c p q
... | E , (mE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Π p _ _) (⊩₀Nat q) with joinW c p q
... | E , (πE , mE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Nat p) (⊩₀Σ q _ _) with joinW c p q
... | E , (mE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Σ p _ _) (⊩₀Nat q) with joinW c p q
... | E , (σE , mE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Nat p) (⊩₀Hom q sh) with joinW c p q
... | E , (mE , hE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Hom p sh) (⊩₀Nat q) with joinW c p q
... | E , (hE , mE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Nat p) (⊩₀Id q) with joinW c p q
... | E , (mE , iE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Id p) (⊩₀Nat q) with joinW c p q
... | E , (iE , mE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Nat-nf mE
...     | ()
irrel₀ c (⊩₀Unit p) (⊩₀Nat q) with joinW c p q
... | E , (uE , nE) with Nat-nf nE
...   | refl with Unit-nf uE
...     | ()
irrel₀ c (⊩₀Nat p) (⊩₀Unit q) with joinW c p q
... | E , (nE , uE) with Nat-nf nE
...   | refl with Unit-nf uE
...     | ()
irrel₀ c (⊩₀Unit _) (⊩₀Unit _) = (λ _ h → h) , (λ _ h → h)
irrel₀ c (⊩₀Nat _)  (⊩₀Nat _)  = (λ _ h → h) , (λ _ h → h)

-- ★ `Mu` versus every other former: `Mu D` is a NORMAL FORM (`Mu-nf`), so
--   any join with a differently-headed type is absurd.
irrel₀ c (⊩₀Fin p) (⊩₀base q) with joinW c p q
... | E , (mE , bE) with base-nf bE
...   | refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀IMu p _ _ _ _) (⊩₀base q) with joinW c p q
... | E , (mE , bE) with base-nf bE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀base p) (⊩₀Fin q) with joinW c p q
... | E , (bE , mE) with base-nf bE
...   | refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀base p) (⊩₀IMu q _ _ _ _) with joinW c p q
... | E , (bE , mE) with base-nf bE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Fin p) (⊩₀ne q n) with joinW c p q
... | E , (mE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀IMu p _ _ _ _) (⊩₀ne q n) with joinW c p q
... | E , (mE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀ne p n) (⊩₀Fin q) with joinW c p q
... | E , (eE , mE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀ne p n) (⊩₀IMu q _ _ _ _) with joinW c p q
... | E , (eE , mE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Fin p) (⊩₀Π q _ _) with joinW c p q
... | E , (mE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Fin-nf mE
...     | ()
irrel₀ c (⊩₀IMu p _ _ _ _) (⊩₀Π q _ _) with joinW c p q
... | E , (mE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Π p _ _) (⊩₀Fin q) with joinW c p q
... | E , (πE , mE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Fin-nf mE
...     | ()
irrel₀ c (⊩₀Π p _ _) (⊩₀IMu q _ _ _ _) with joinW c p q
... | E , (πE , mE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Fin p) (⊩₀Σ q _ _) with joinW c p q
... | E , (mE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Fin-nf mE
...     | ()
irrel₀ c (⊩₀IMu p _ _ _ _) (⊩₀Σ q _ _) with joinW c p q
... | E , (mE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Σ p _ _) (⊩₀Fin q) with joinW c p q
... | E , (σE , mE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Fin-nf mE
...     | ()
irrel₀ c (⊩₀Σ p _ _) (⊩₀IMu q _ _ _ _) with joinW c p q
... | E , (σE , mE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Fin p) (⊩₀Hom q sh) with joinW c p q
... | E , (mE , hE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀IMu p _ _ _ _) (⊩₀Hom q sh) with joinW c p q
... | E , (mE , hE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Hom p sh) (⊩₀Fin q) with joinW c p q
... | E , (hE , mE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀Hom p sh) (⊩₀IMu q _ _ _ _) with joinW c p q
... | E , (hE , mE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Fin p) (⊩₀Id q) with joinW c p q
... | E , (mE , iE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Fin-nf mE
...     | ()
irrel₀ c (⊩₀IMu p _ _ _ _) (⊩₀Id q) with joinW c p q
... | E , (mE , iE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Id p) (⊩₀Fin q) with joinW c p q
... | E , (iE , mE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Fin-nf mE
...     | ()
irrel₀ c (⊩₀Id p) (⊩₀IMu q _ _ _ _) with joinW c p q
... | E , (iE , mE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Fin p) (⊩₀Unit q) with joinW c p q
... | E , (mE , uE) with Unit-nf uE
...   | refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀IMu p _ _ _ _) (⊩₀Unit q) with joinW c p q
... | E , (mE , uE) with Unit-nf uE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Unit p) (⊩₀Fin q) with joinW c p q
... | E , (uE , mE) with Unit-nf uE
...   | refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀Unit p) (⊩₀IMu q _ _ _ _) with joinW c p q
... | E , (uE , mE) with Unit-nf uE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Fin p) (⊩₀Nat q) with joinW c p q
... | E , (mE , nE) with Nat-nf nE
...   | refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀IMu p _ _ _ _) (⊩₀Nat q) with joinW c p q
... | E , (mE , nE) with Nat-nf nE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₀ c (⊩₀Nat p) (⊩₀Fin q) with joinW c p q
... | E , (nE , mE) with Nat-nf nE
...   | refl with Fin-nf mE
...     | ()
irrel₀ c (⊩₀Nat p) (⊩₀IMu q _ _ _ _) with joinW c p q
... | E , (nE , mE) with Nat-nf nE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
-- ★★ `Mu`/`Mu`: the join forces the two DESCRIPTIONS equal (matching the
--   second `refl` inverts `Mu`'s injectivity), but NOT the two `DPred`s —
--   that residual difference is precisely what `irrelMu` collapses.
irrel₀ c (⊩₀Fin p) (⊩₀Fin q) with joinW c p q
... | E , (m₁ , m₂) with Fin-nf m₁
...   | refl with Fin-nf m₂
...     | refl = (λ _ h → h) , (λ _ h → h)

irrelIMu K₁ K₂ d₁ d₂ r₁ r₂ (imm-ne n)    = imm-ne n
irrelIMu K₁ K₂ d₁ d₂ r₁ r₂ (imm-exp r m) = imm-exp r (irrelIMu K₁ K₂ d₁ d₂ r₁ r₂ m)
irrelIMu K₁ K₂ d₁ d₂ r₁ r₂ (imm-con {p = p} l) =
  imm-con (iliftK K₁ K₂ d₁ d₂ K₁ K₂ d₁ d₂ r₁ r₂ p l)

-- a head expansion on either side: re-join by confluence.
iliftK K₁ K₂ d₁ d₂ (iki-exp r k) Kc₂ c₁ c₂ r₁ r₂ t l with confluent (step (snr→⟶ r) done) c₁
... | w , (cw , *w) = iliftK K₁ K₂ d₁ d₂ k Kc₂ cw (⟶*-trans c₂ *w) r₁ r₂ t l
iliftK K₁ K₂ d₁ d₂ Kc₁ (iki-exp r k) c₁ c₂ r₁ r₂ t l with confluent (step (snr→⟶ r) done) c₂
... | w , (cw , *w) = iliftK K₁ K₂ d₁ d₂ Kc₁ k (⟶*-trans c₁ *w) cw r₁ r₂ t l
-- matching formers.
iliftK K₁ K₂ d₁ d₂ (iki-ne n₁) (iki-ne n₂) c₁ c₂ r₁ r₂ t l = l
iliftK K₁ K₂ d₁ d₂ (iki-ι _) (iki-ι _) c₁ c₂ r₁ r₂ t l with dι-reduct c₁ | dι-reduct c₂
... | j₁ , (eq₁ , rj₁) | j₂ , (eq₂ , rj₂) with trans (sym eq₁) eq₂
...   | refl = ( projl l
              , idpay-transfer (j₁ , (rj₁ , rj₂)) (_ , (r₁ , r₂)) (projr l) )
iliftK K₁ K₂ d₁ d₂ (iki-σ _ _ w₁ k₁) (iki-σ _ _ w₂ k₂) c₁ c₂ r₁ r₂ t (sn , (q , rest))
  with dσ-reduct c₁ | dσ-reduct c₂
... | S₁ , (f₁ , (eq₁ , (rS₁ , rf₁))) | S₂ , (f₂ , (eq₂ , (rS₂ , rf₂)))
      with trans (sym eq₁) eq₂
...   | refl =
        ( sn
        , ( q'
          , iliftK K₁ K₂ d₁ d₂ (k₁ (fst t) q) (k₂ (fst t) q') (⟶*-appˡ rf₁) (⟶*-appˡ rf₂)
                   r₁ r₂ (snd t) rest ) )
  where
  q' = projl (irrel₀ (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-El rS₁)) (csymᵀ (red→≅ᵀ (⟶ᵀ*-El rS₂)))) w₁ w₂)
             (fst t) q
iliftK K₁ K₂ d₁ d₂ (iki-ρ _ _ k₁) (iki-ρ _ _ k₂) c₁ c₂ r₁ r₂ t (sn , ((snf , m) , rest))
  with dρ-reduct c₁ | dρ-reduct c₂
... | j₁ , (C₁ , (eq₁ , (rj₁ , rC₁))) | j₂ , (C₂ , (eq₂ , (rj₂ , rC₂)))
      with trans (sym eq₁) eq₂
...   | refl =
        ( sn
        , ( (snf , irrelIMu K₁ K₂ d₁ d₂ rj₁ rj₂ m)
          , iliftK K₁ K₂ d₁ d₂ k₁ k₂ rC₁ rC₂ r₁ r₂ (snd t) rest ) )
-- every mismatch is a shape clash on the common reduct.
iliftK K₁ K₂ d₁ d₂ (iki-ne n₁) (iki-ι _) c₁ c₂ r₁ r₂ t l with dι-reduct c₂
... | _ , (eq , _) = ⊥-elim (ne≢dι eq (ne-red* (sne→ne n₁) c₁))
iliftK K₁ K₂ d₁ d₂ (iki-ne n₁) (iki-σ _ _ _ _) c₁ c₂ r₁ r₂ t l with dσ-reduct c₂
... | _ , (_ , (eq , _)) = ⊥-elim (ne≢dσ eq (ne-red* (sne→ne n₁) c₁))
iliftK K₁ K₂ d₁ d₂ (iki-ne n₁) (iki-ρ _ _ _) c₁ c₂ r₁ r₂ t l with dρ-reduct c₂
... | _ , (_ , (eq , _)) = ⊥-elim (ne≢dρ eq (ne-red* (sne→ne n₁) c₁))
iliftK K₁ K₂ d₁ d₂ (iki-ι _) (iki-ne n₂) c₁ c₂ r₁ r₂ t l with dι-reduct c₁
... | _ , (eq , _) = ⊥-elim (ne≢dι eq (ne-red* (sne→ne n₂) c₂))
iliftK K₁ K₂ d₁ d₂ (iki-ι _) (iki-σ _ _ _ _) c₁ c₂ r₁ r₂ t l with dι-reduct c₁ | dσ-reduct c₂
... | _ , (e₁ , _) | _ , (_ , (e₂ , _)) = ⊥-elim (dι≢dσ (trans (sym e₁) e₂))
iliftK K₁ K₂ d₁ d₂ (iki-ι _) (iki-ρ _ _ _) c₁ c₂ r₁ r₂ t l with dι-reduct c₁ | dρ-reduct c₂
... | _ , (e₁ , _) | _ , (_ , (e₂ , _)) = ⊥-elim (dι≢dρ (trans (sym e₁) e₂))
iliftK K₁ K₂ d₁ d₂ (iki-σ _ _ _ _) (iki-ne n₂) c₁ c₂ r₁ r₂ t l with dσ-reduct c₁
... | _ , (_ , (eq , _)) = ⊥-elim (ne≢dσ eq (ne-red* (sne→ne n₂) c₂))
iliftK K₁ K₂ d₁ d₂ (iki-σ _ _ _ _) (iki-ι _) c₁ c₂ r₁ r₂ t l with dσ-reduct c₁ | dι-reduct c₂
... | _ , (_ , (e₁ , _)) | _ , (e₂ , _) = ⊥-elim (dι≢dσ (trans (sym e₂) e₁))
iliftK K₁ K₂ d₁ d₂ (iki-σ _ _ _ _) (iki-ρ _ _ _) c₁ c₂ r₁ r₂ t l with dσ-reduct c₁ | dρ-reduct c₂
... | _ , (_ , (e₁ , _)) | _ , (_ , (e₂ , _)) = ⊥-elim (dσ≢dρ (trans (sym e₁) e₂))
iliftK K₁ K₂ d₁ d₂ (iki-ρ _ _ _) (iki-ne n₂) c₁ c₂ r₁ r₂ t l with dρ-reduct c₁
... | _ , (_ , (eq , _)) = ⊥-elim (ne≢dρ eq (ne-red* (sne→ne n₂) c₂))
iliftK K₁ K₂ d₁ d₂ (iki-ρ _ _ _) (iki-ι _) c₁ c₂ r₁ r₂ t l with dρ-reduct c₁ | dι-reduct c₂
... | _ , (_ , (e₁ , _)) | _ , (e₂ , _) = ⊥-elim (dι≢dρ (trans (sym e₂) e₁))
iliftK K₁ K₂ d₁ d₂ (iki-ρ _ _ _) (iki-σ _ _ _ _) c₁ c₂ r₁ r₂ t l with dρ-reduct c₁ | dσ-reduct c₂
... | _ , (_ , (e₁ , _)) | _ , (_ , (e₂ , _)) = ⊥-elim (dσ≢dρ (trans (sym e₂) e₁))

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

fwd₀ p (⊩₀Unit q) with confluentᵀ p q
... | E , (bE , uE) with Unit-nf uE
...   | refl = ⊩₀Unit bE

fwd₀ p (⊩₀Nat q) with confluentᵀ p q
... | E , (bE , nE) with Nat-nf nE
...   | refl = ⊩₀Nat bE

-- ★ the family's interpretation is of a REPRESENTATIVE, so forwarding
--   only extends the two conversions — nothing is transported.
fwd₀ p (⊩₀IMu q cI cD ⊩I K) with confluentᵀ p q
... | E , (bE , mE) with IMu-reduct mE
...   | mkIMuRed _ _ _ refl rI rD _ =
        ⊩₀IMu bE (ctrn (csym (hom→≅ rI)) cI) (ctrn (csym (hom→≅ rD)) cD) ⊩I K
fwd₀ p (⊩₀Fin q) with confluentᵀ p q
... | E , (bE , mE) with Fin-nf mE
...   | refl = ⊩₀Fin bE

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
CR1₀ (⊩₀Unit _)  h = h
CR1₀ (⊩₀Nat _)   h = projl h
CR1₀ (⊩₀IMu _ _ _ _ _) h = projl h
CR1₀ (⊩₀Fin _)  h = projl h

CR3₀ : {A : RTy Γ} (R : ⊩₀ A) {t : RTm Γ} → SNe t → R ⊩₀∋ t
CR3₀ (⊩₀base _)    nt = sn-ne nt
CR3₀ (⊩₀Hom _ _)   nt = sn-ne nt
CR3₀ (⊩₀Id _)      nt = (sn-ne nt , λ ch → ⊥-elim (sne-nopay nt ch))
CR3₀ (⊩₀ne _ _)    nt = sn-ne nt
CR3₀ (⊩₀Unit _)    nt = sn-ne nt
CR3₀ (⊩₀Nat _)     nt = (sn-ne nt , nm-ne nt)
CR3₀ (⊩₀IMu _ _ _ _ _) nt = (sn-ne nt , imm-ne nt)
CR3₀ (⊩₀Fin _)    nt = (sn-ne nt , fm-ne nt)
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
exp₀ (⊩₀Unit _)    r h = sn-exp r h
exp₀ (⊩₀Nat _)     r h = (sn-exp r (projl h) , nm-exp r (projr h))
exp₀ (⊩₀IMu _ _ _ _ _) r h = (sn-exp r (projl h) , imm-exp r (projr h))
exp₀ (⊩₀Fin _)    r h = (sn-exp r (projl h) , fm-exp r (projr h))
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

-- (`wk-single` moved to `…Pi`, beside its two ingredients — it is kernel
--  syntax, not metatheory.  Re-exported below so its ~50 importers are
--  unaffected.)

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
PayT (⊩₀Unit _)  c = ⊤
PayT (⊩₀Nat _)   c = ⊤
PayT (⊩₀IMu _ _ _ _ _) c = ⊤
PayT (⊩₀Fin _) c = ⊤
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
payT-exp r q (⊩₀Unit _) pay = _
payT-exp r q (⊩₀Nat _) pay = _
payT-exp r q (⊩₀IMu _ _ _ _ _) pay = _
payT-exp r q (⊩₀Fin _) pay = _
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
payT-whred r (⊩₀Unit _) pay = _
payT-whred r (⊩₀Nat _) pay = _
payT-whred r (⊩₀IMu _ _ _ _ _) pay = _
payT-whred r (⊩₀Fin _) pay = _
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
payT-irrel cv R (⊩₀Unit _) pay = _
payT-irrel cv R (⊩₀Nat _) pay = _
payT-irrel cv R (⊩₀IMu _ _ _ _ _) pay = _
payT-irrel cv R (⊩₀Fin _) pay = _
-- ★ `Mu` versus `Π`: `Mu D` is a normal form and `Π` cannot be reached
--   from it, so the join is absurd.
payT-irrel cv (⊩₀Fin p) (⊩₀Π q _ _) pay with joinW cv p q
... | E , (mE , πE) with Fin-nf mE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _
payT-irrel cv (⊩₀IMu p _ _ _ _) (⊩₀Π q _ _) pay with joinW cv p q
... | E , (mE , πE) with IMu-reduct mE
...   | mkIMuRed _ _ _ refl _ _ _ with Π-reduct πE
...     | mkΠRed _ _ () _ _
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
payT-irrel cv (⊩₀Unit p) (⊩₀Π q _ _) pay with joinW cv p q
... | E , (mE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Unit-nf mE
...     | ()
payT-irrel cv (⊩₀Nat p) (⊩₀Π q _ _) pay with joinW cv p q
... | E , (mE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Nat-nf mE
...     | ()
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
         → A ⟶ᵀ* Hom H a b → StkHd (Hom H a b) → ⊩₁ A
  -- ★ WF stage A: the datatype core's two type formers.  `Unit` is
  -- SN-only (like `base`); `Nat` carries the reaches-numeral payload.
  ⊩₁Unit : {A : RTy Γ} → A ⟶ᵀ* Unit → ⊩₁ A
  ⊩₁Nat  : {A : RTy Γ} → A ⟶ᵀ* Nat → ⊩₁ A
  ⊩₁Id   : {A H : RTy Γ} {a b : RTm Γ}
         → A ⟶ᵀ* Id H a b → ⊩₁ A
  -- ★ the levitated family at level 1 carries the SAME data as level 0,
  --   exactly as `⊩₁Nat`'s payload is `⊩₀Nat`'s — which is what makes
  --   `emb`/`emb-coh` at `IMu` the identity.
  ⊩₁IMu  : {A : RTy Γ} {I D i I₀ D₀ : RTm Γ} → A ⟶ᵀ* IMu I D i →
           I ≅ I₀ → D ≅ D₀ → (⊩I : ⊩₀ (El I₀)) → IKInterp ⊩I D₀ → ⊩₁ A
  ⊩₁Fin  : {A : RTy Γ} {n : ℕ} → A ⟶ᵀ* Fin n → ⊩₁ A
  -- ★★ LARGE: the type of descriptions.  Its members are the telescopes
  --   that HAVE an interpretation — S0's `⊩₁IDesc`, and `toIK` is the
  --   identity: the membership IS the level-0 `IKInterp`.
  ⊩₁Desc : {A : RTy Γ} {I I₀ : RTm Γ} → A ⟶ᵀ* Desc I → I ≅ I₀ → ⊩₀ (El I₀) → ⊩₁ A
  -- the hypotheses' type at a STUCK telescope (a canonical one COMPUTES to
  --   `Unit`/`Σ'`); members are the SN terms, like `⊩₁ne`.
  ⊩₁DIhNe : {A : RTy Γ} {D C p : RTm Γ} {M : RTy ((Γ ∙) ∙)} →
            A ⟶ᵀ* DIh D M C p → Ne C → ⊩₁ A

⊩₁base _     ⊩₁∋ t = SN t
⊩₁U _        ⊩₁∋ t = SN t × Σ (⊩₀ (El t)) (λ R → PayT R t)
⊩₁ne _ _     ⊩₁∋ t = SN t
⊩₁Π _ ⊩F ⊩G  ⊩₁∋ t = SN t × ((u : RTm _) (r : ⊩F ⊩₁∋ u) → (⊩G u r) ⊩₁∋ app t u)
⊩₁Σ _ ⊩F ⊩G  ⊩₁∋ t =
  SN t × Σ (⊩F ⊩₁∋ fst t) (λ r → (⊩G (fst t) r) ⊩₁∋ snd t)
⊩₁Hom _ _    ⊩₁∋ t = SN t
⊩₁Unit _     ⊩₁∋ t = SN t
⊩₁Nat _      ⊩₁∋ t = SN t × NatMem t
⊩₁IMu {i = i} _ _ _ ⊩I K ⊩₁∋ t = SN t × IMuMem (ikpredsOf K) i t
⊩₁Fin {n = n} _ ⊩₁∋ t = SN t × FinMem n t
⊩₁Desc _ _ ⊩I ⊩₁∋ t = IKInterp ⊩I t
⊩₁DIhNe _ _ ⊩₁∋ t = SN t
⊩₁Id {a = a} {b = b} _ ⊩₁∋ t = SN t × IdPay a b t

bwd₁ : {A B : RTy Γ} → A ⟶ᵀ* B → ⊩₁ B → ⊩₁ A
bwd₁ p (⊩₁base q)    = ⊩₁base (⟶ᵀ*-trans p q)
bwd₁ p (⊩₁U q)       = ⊩₁U    (⟶ᵀ*-trans p q)
bwd₁ p (⊩₁ne q n)    = ⊩₁ne   (⟶ᵀ*-trans p q) n
bwd₁ p (⊩₁Π q ⊩F ⊩G) = ⊩₁Π    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₁ p (⊩₁Σ q ⊩F ⊩G) = ⊩₁Σ    (⟶ᵀ*-trans p q) ⊩F ⊩G
bwd₁ p (⊩₁Hom q s)   = ⊩₁Hom  (⟶ᵀ*-trans p q) s
bwd₁ p (⊩₁Unit q)    = ⊩₁Unit (⟶ᵀ*-trans p q)
bwd₁ p (⊩₁Nat q)     = ⊩₁Nat  (⟶ᵀ*-trans p q)
bwd₁ p (⊩₁IMu q cI cD ⊩I K) = ⊩₁IMu (⟶ᵀ*-trans p q) cI cD ⊩I K
bwd₁ p (⊩₁Fin q)     = ⊩₁Fin  (⟶ᵀ*-trans p q)
bwd₁ p (⊩₁Desc q cI ⊩I) = ⊩₁Desc (⟶ᵀ*-trans p q) cI ⊩I
bwd₁ p (⊩₁DIhNe q n) = ⊩₁DIhNe (⟶ᵀ*-trans p q) n
bwd₁ p (⊩₁Id q)      = ⊩₁Id   (⟶ᵀ*-trans p q)

-- ★ the level-1 peer of `bwd₀-mem⁻`, never needed until stage E.
-- Membership IGNORES the reduction chain, so every row is `h` — but the
-- lemma is still load-bearing: when `R` is not in constructor form
-- (`homNatSem` applied to an opaque `NatMem`), `bwd₁ q R ⊩₁∋ t` is
-- STUCK and the identification is not available definitionally.
bwd₁-mem⁻ : {A B : RTy Γ} (q : A ⟶ᵀ* B) (R : ⊩₁ B) {t : RTm Γ} →
            R ⊩₁∋ t → (bwd₁ q R) ⊩₁∋ t
bwd₁-mem⁻ q (⊩₁base _)  h = h
bwd₁-mem⁻ q (⊩₁U _)     h = h
bwd₁-mem⁻ q (⊩₁ne _ _)  h = h
bwd₁-mem⁻ q (⊩₁Π _ _ _) h = h
bwd₁-mem⁻ q (⊩₁Σ _ _ _) h = h
bwd₁-mem⁻ q (⊩₁Hom _ _) h = h
bwd₁-mem⁻ q (⊩₁Unit _)  h = h
bwd₁-mem⁻ q (⊩₁Nat _)   h = h
bwd₁-mem⁻ q (⊩₁IMu _ _ _ _ _) h = h
bwd₁-mem⁻ q (⊩₁Fin _)   h = h
bwd₁-mem⁻ q (⊩₁Desc _ _ _) h = h
bwd₁-mem⁻ q (⊩₁DIhNe _ _) h = h
bwd₁-mem⁻ q (⊩₁Id _)    h = h

------------------------------------------------------------------------
-- ★★ LEVITATED FAMILIES — the level-1 helpers.
------------------------------------------------------------------------

-- a term conversion lifts to its decoding (Church–Rosser, then `ξ-El`).
El≅ : {a b : RTm Γ} → a ≅ b → El a ≅ᵀ El b
El≅ c with church-rosser c
... | w , (r₁ , r₂) = ctrnᵀ (red→≅ᵀ (⟶ᵀ*-El r₁)) (csymᵀ (red→≅ᵀ (⟶ᵀ*-El r₂)))

-- a telescope with an interpretation is strongly normalising (SN is
-- carried at every canonical node; head expansion is `sn-exp`).
ikinterp-sn : {I C : RTm Γ} {⊩I : ⊩₀ (El I)} → IKInterp ⊩I C → SN C
ikinterp-sn (iki-ne n)         = sn-ne n
ikinterp-sn (iki-ι sj)         = sn-dι sj
ikinterp-sn (iki-σ sS sf _ _)  = sn-dσ sS sf
ikinterp-sn (iki-ρ sj _ k)     = sn-dρ sj (ikinterp-sn k)
ikinterp-sn (iki-exp r k)      = sn-exp r (ikinterp-sn k)

-- …and closed under the head strategy (the formers have no head step).
ikinterp-whred : {I C C' : RTm Γ} {⊩I : ⊩₀ (El I)} →
                 IKInterp ⊩I C → SNRed C C' → IKInterp ⊩I C'
ikinterp-whred (iki-ne n)     r = iki-ne (sne-whred n r)
ikinterp-whred (iki-exp r₀ k) r with snr-det r₀ r
... | refl = k

-- re-base an interpretation on another witness of a CONVERTIBLE index
-- type: only the `dρ` fields' index-validity members move (`irrel₀`).
ikinterp-irrel : {I I' C : RTm Γ} → El I ≅ᵀ El I' →
                 (⊩I : ⊩₀ (El I)) (⊩I' : ⊩₀ (El I')) →
                 IKInterp ⊩I C → IKInterp ⊩I' C
ikinterp-irrel c ⊩I ⊩I' (iki-ne n)          = iki-ne n
ikinterp-irrel c ⊩I ⊩I' (iki-ι sj)          = iki-ι sj
ikinterp-irrel c ⊩I ⊩I' (iki-σ sS sf w k)   =
  iki-σ sS sf w (λ v q → ikinterp-irrel c ⊩I ⊩I' (k v q))
ikinterp-irrel c ⊩I ⊩I' (iki-ρ {j = j} sj vj k) =
  iki-ρ sj (projl (irrel₀ c ⊩I ⊩I') j vj) (ikinterp-irrel c ⊩I ⊩I' k)
ikinterp-irrel c ⊩I ⊩I' (iki-exp r k)       = iki-exp r (ikinterp-irrel c ⊩I ⊩I' k)

-- the hypotheses' type at a stuck telescope stays so under reduction.
record DIhNeRed {Γ} (A : RTy Γ) : Set where
  constructor mkDIhNe
  field
    dD  : RTm Γ
    dM  : RTy ((Γ ∙) ∙)
    dC  : RTm Γ
    dp  : RTm Γ
    dne : Ne dC
    deq : A ≡ DIh dD dM dC dp

DIhNe-reduct : {D C p : RTm Γ} {M : RTy ((Γ ∙) ∙)} {A : RTy Γ} →
               Ne C → DIh D M C p ⟶ᵀ* A → DIhNeRed A
DIhNe-reduct n doneᵀ = mkDIhNe _ _ _ _ n refl
DIhNe-reduct () (stepᵀ (DIh-ι _ _ _ _) _)
DIhNe-reduct () (stepᵀ (DIh-σ _ _ _ _ _) _)
DIhNe-reduct () (stepᵀ (DIh-ρ _ _ _ _ _) _)
DIhNe-reduct n (stepᵀ (ξ-DIhᴰ r) p) = DIhNe-reduct n p
DIhNe-reduct n (stepᵀ (ξ-DIhᴹ r) p) = DIhNe-reduct n p
DIhNe-reduct n (stepᵀ (ξ-DIhᶜ r) p) = DIhNe-reduct (ne-red n r) p
DIhNe-reduct n (stepᵀ (ξ-DIhᵖ r) p) = DIhNe-reduct n p

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
irrel₁ c (⊩₁Unit p) (⊩₁base q) with joinW c p q
... | E , (mE , bE) with base-nf bE
...   | refl with Unit-nf mE
...     | ()
irrel₁ c (⊩₁base p) (⊩₁Unit q) with joinW c p q
... | E , (bE , mE) with base-nf bE
...   | refl with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Unit p) (⊩₁U q) with joinW c p q
... | E , (mE , uE2) with U-nf uE2
...   | refl with Unit-nf mE
...     | ()
irrel₁ c (⊩₁U p) (⊩₁Unit q) with joinW c p q
... | E , (uE2 , mE) with U-nf uE2
...   | refl with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Unit p) (⊩₁ne q n) with joinW c p q
... | E , (mE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Unit-nf mE
...     | ()
irrel₁ c (⊩₁ne p n) (⊩₁Unit q) with joinW c p q
... | E , (eE , mE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Unit p) (⊩₁Π q _ _) with joinW c p q
... | E , (mE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Π p _ _) (⊩₁Unit q) with joinW c p q
... | E , (πE , mE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Unit p) (⊩₁Σ q _ _) with joinW c p q
... | E , (mE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Σ p _ _) (⊩₁Unit q) with joinW c p q
... | E , (σE , mE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Unit p) (⊩₁Hom q sh) with joinW c p q
... | E , (mE , hE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Hom p sh) (⊩₁Unit q) with joinW c p q
... | E , (hE , mE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Unit p) (⊩₁Id q) with joinW c p q
... | E , (mE , iE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Id p) (⊩₁Unit q) with joinW c p q
... | E , (iE , mE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Unit-nf mE
...     | ()
irrel₁ c (⊩₁Nat p) (⊩₁base q) with joinW c p q
... | E , (mE , bE) with base-nf bE
...   | refl with Nat-nf mE
...     | ()
irrel₁ c (⊩₁base p) (⊩₁Nat q) with joinW c p q
... | E , (bE , mE) with base-nf bE
...   | refl with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Nat p) (⊩₁U q) with joinW c p q
... | E , (mE , uE2) with U-nf uE2
...   | refl with Nat-nf mE
...     | ()
irrel₁ c (⊩₁U p) (⊩₁Nat q) with joinW c p q
... | E , (uE2 , mE) with U-nf uE2
...   | refl with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Nat p) (⊩₁ne q n) with joinW c p q
... | E , (mE , eE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Nat-nf mE
...     | ()
irrel₁ c (⊩₁ne p n) (⊩₁Nat q) with joinW c p q
... | E , (eE , mE) with El-ne-reduct n eE
...   | mkElNe _ _ refl with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Nat p) (⊩₁Π q _ _) with joinW c p q
... | E , (mE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Π p _ _) (⊩₁Nat q) with joinW c p q
... | E , (πE , mE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Nat p) (⊩₁Σ q _ _) with joinW c p q
... | E , (mE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Σ p _ _) (⊩₁Nat q) with joinW c p q
... | E , (σE , mE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Nat p) (⊩₁Hom q sh) with joinW c p q
... | E , (mE , hE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Hom p sh) (⊩₁Nat q) with joinW c p q
... | E , (hE , mE) with Hom-stk-reduct sh hE
...   | mkHomStk _ _ _ _ refl with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Nat p) (⊩₁Id q) with joinW c p q
... | E , (mE , iE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Id p) (⊩₁Nat q) with joinW c p q
... | E , (iE , mE) with Id-reduct iE
...   | _ , (_ , (_ , (refl , _))) with Nat-nf mE
...     | ()
irrel₁ c (⊩₁Unit p) (⊩₁Nat q) with joinW c p q
... | E , (uE , nE) with Nat-nf nE
...   | refl with Unit-nf uE
...     | ()
irrel₁ c (⊩₁Nat p) (⊩₁Unit q) with joinW c p q
... | E , (nE , uE) with Nat-nf nE
...   | refl with Unit-nf uE
...     | ()
irrel₁ c (⊩₁Unit _) (⊩₁Unit _) = (λ _ h → h) , (λ _ h → h)

-- ★ `Mu` versus every other level-1 former: `Mu D` is a normal form.
irrel₁ c (⊩₁Fin p) (⊩₁base q) with joinW c p q
... | E , (mE , oE) with base-nf oE
...   | refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁base q) with joinW c p q
... | E , (mE , oE) with base-nf oE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁base p) (⊩₁Fin q) with joinW c p q
... | E , (oE , mE) with base-nf oE
...   | refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁base p) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (oE , mE) with base-nf oE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Fin p) (⊩₁U q) with joinW c p q
... | E , (mE , oE) with U-nf oE
...   | refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁U q) with joinW c p q
... | E , (mE , oE) with U-nf oE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁U p) (⊩₁Fin q) with joinW c p q
... | E , (oE , mE) with U-nf oE
...   | refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁U p) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (oE , mE) with U-nf oE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Fin p) (⊩₁ne q n) with joinW c p q
... | E , (mE , oE) with El-ne-reduct n oE
...   | mkElNe _ _ refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁ne q n) with joinW c p q
... | E , (mE , oE) with El-ne-reduct n oE
...   | mkElNe _ _ refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁ne p n) (⊩₁Fin q) with joinW c p q
... | E , (oE , mE) with El-ne-reduct n oE
...   | mkElNe _ _ refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁ne p n) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (oE , mE) with El-ne-reduct n oE
...   | mkElNe _ _ refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Fin p) (⊩₁Π q _ _) with joinW c p q
... | E , (mE , oE) with Π-reduct oE
...   | mkΠRed _ _ refl _ _ with Fin-nf mE
...     | ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁Π q _ _) with joinW c p q
... | E , (mE , oE) with Π-reduct oE
...   | mkΠRed _ _ refl _ _ with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Π p _ _) (⊩₁Fin q) with joinW c p q
... | E , (oE , mE) with Π-reduct oE
...   | mkΠRed _ _ refl _ _ with Fin-nf mE
...     | ()
irrel₁ c (⊩₁Π p _ _) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (oE , mE) with Π-reduct oE
...   | mkΠRed _ _ refl _ _ with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Fin p) (⊩₁Σ q _ _) with joinW c p q
... | E , (mE , oE) with Σ-reduct oE
...   | mkΣRed _ _ refl _ _ with Fin-nf mE
...     | ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁Σ q _ _) with joinW c p q
... | E , (mE , oE) with Σ-reduct oE
...   | mkΣRed _ _ refl _ _ with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Σ p _ _) (⊩₁Fin q) with joinW c p q
... | E , (oE , mE) with Σ-reduct oE
...   | mkΣRed _ _ refl _ _ with Fin-nf mE
...     | ()
irrel₁ c (⊩₁Σ p _ _) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (oE , mE) with Σ-reduct oE
...   | mkΣRed _ _ refl _ _ with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Fin p) (⊩₁Hom q sh) with joinW c p q
... | E , (mE , oE) with Hom-stk-reduct sh oE
...   | mkHomStk _ _ _ _ refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁Hom q sh) with joinW c p q
... | E , (mE , oE) with Hom-stk-reduct sh oE
...   | mkHomStk _ _ _ _ refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Hom p sh) (⊩₁Fin q) with joinW c p q
... | E , (oE , mE) with Hom-stk-reduct sh oE
...   | mkHomStk _ _ _ _ refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁Hom p sh) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (oE , mE) with Hom-stk-reduct sh oE
...   | mkHomStk _ _ _ _ refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Fin p) (⊩₁Unit q) with joinW c p q
... | E , (mE , oE) with Unit-nf oE
...   | refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁Unit q) with joinW c p q
... | E , (mE , oE) with Unit-nf oE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Unit p) (⊩₁Fin q) with joinW c p q
... | E , (oE , mE) with Unit-nf oE
...   | refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁Unit p) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (oE , mE) with Unit-nf oE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Fin p) (⊩₁Nat q) with joinW c p q
... | E , (mE , oE) with Nat-nf oE
...   | refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁Nat q) with joinW c p q
... | E , (mE , oE) with Nat-nf oE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Nat p) (⊩₁Fin q) with joinW c p q
... | E , (oE , mE) with Nat-nf oE
...   | refl with Fin-nf mE
...     | ()
irrel₁ c (⊩₁Nat p) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (oE , mE) with Nat-nf oE
...   | refl with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Fin p) (⊩₁Id q) with joinW c p q
... | E , (mE , oE) with Id-reduct oE
...   | _ , (_ , (_ , (refl , _))) with Fin-nf mE
...     | ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁Id q) with joinW c p q
... | E , (mE , oE) with Id-reduct oE
...   | _ , (_ , (_ , (refl , _))) with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Id p) (⊩₁Fin q) with joinW c p q
... | E , (oE , mE) with Id-reduct oE
...   | _ , (_ , (_ , (refl , _))) with Fin-nf mE
...     | ()
irrel₁ c (⊩₁Id p) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (oE , mE) with Id-reduct oE
...   | _ , (_ , (_ , (refl , _))) with IMu-reduct mE
...     | mkIMuRed _ _ _ () _ _ _
-- ★★ `Mu`/`Mu` at level 1 — the same residual-`DInterp` difference as at
--   level 0, collapsed by the very same `irrelMu`.
irrel₁ c (⊩₁Fin p) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (mE , iE) with Fin-nf mE
...   | refl with IMu-reduct iE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁Fin q) with joinW c p q
... | E , (iE , mE) with Fin-nf mE
...   | refl with IMu-reduct iE
...     | mkIMuRed _ _ _ () _ _ _
-- ★★ LEVITATED FAMILIES at level 1: the description type and the stuck
--   hypotheses' type against every other head — one side's shape fixes the
--   common reduct, the other's clashes with it.
irrel₁ c (⊩₁Desc p _ _) (⊩₁base q) with joinW c p q
... | E , (aE , bE) with base-nf bE
...   | refl with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁base p) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with base-nf aE
...     | ()
irrel₁ c (⊩₁Desc p _ _) (⊩₁U q) with joinW c p q
... | E , (aE , bE) with U-nf bE
...   | refl with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁U p) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with U-nf aE
...     | ()
irrel₁ c (⊩₁Desc p _ _) (⊩₁ne q n₂) with joinW c p q
... | E , (aE , bE) with El-ne-reduct n₂ bE
...   | mkElNe _ _ refl with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁ne p n₁) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with El-ne-reduct n₁ aE
...     | mkElNe _ _ ()
irrel₁ c (⊩₁Desc p _ _) (⊩₁Π q _ _) with joinW c p q
... | E , (aE , bE) with Π-reduct bE
...   | mkΠRed _ _ refl _ _ with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁Π p _ _) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with Π-reduct aE
...     | mkΠRed _ _ () _ _
irrel₁ c (⊩₁Desc p _ _) (⊩₁Σ q _ _) with joinW c p q
... | E , (aE , bE) with Σ-reduct bE
...   | mkΣRed _ _ refl _ _ with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁Σ p _ _) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with Σ-reduct aE
...     | mkΣRed _ _ () _ _
irrel₁ c (⊩₁Desc p _ _) (⊩₁Hom q sh₂) with joinW c p q
... | E , (aE , bE) with Hom-stk-reduct sh₂ bE
...   | mkHomStk _ _ _ _ refl with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁Hom p sh₁) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with Hom-stk-reduct sh₁ aE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁Desc p _ _) (⊩₁Unit q) with joinW c p q
... | E , (aE , bE) with Unit-nf bE
...   | refl with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁Unit p) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with Unit-nf aE
...     | ()
irrel₁ c (⊩₁Desc p _ _) (⊩₁Nat q) with joinW c p q
... | E , (aE , bE) with Nat-nf bE
...   | refl with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁Nat p) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with Nat-nf aE
...     | ()
irrel₁ c (⊩₁Desc p _ _) (⊩₁Id q) with joinW c p q
... | E , (aE , bE) with Id-reduct bE
...   | _ , (_ , (_ , (refl , _))) with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁Id p) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with Id-reduct aE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁Desc p _ _) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (aE , bE) with IMu-reduct bE
...   | mkIMuRed _ _ _ refl _ _ _ with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with IMu-reduct aE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁Desc p _ _) (⊩₁Fin q) with joinW c p q
... | E , (aE , bE) with Fin-nf bE
...   | refl with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁Fin p) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with Fin-nf aE
...     | ()
irrel₁ c (⊩₁Desc p _ _) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with Desc-reduct aE
...     | _ , ((), _)
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁base q) with joinW c p q
... | E , (aE , bE) with base-nf bE
...   | refl with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁base p) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with base-nf aE
...     | ()
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁U q) with joinW c p q
... | E , (aE , bE) with U-nf bE
...   | refl with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁U p) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with U-nf aE
...     | ()
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁ne q n₂) with joinW c p q
... | E , (aE , bE) with El-ne-reduct n₂ bE
...   | mkElNe _ _ refl with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁ne p n₁) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with El-ne-reduct n₁ aE
...     | mkElNe _ _ ()
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁Π q _ _) with joinW c p q
... | E , (aE , bE) with Π-reduct bE
...   | mkΠRed _ _ refl _ _ with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁Π p _ _) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with Π-reduct aE
...     | mkΠRed _ _ () _ _
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁Σ q _ _) with joinW c p q
... | E , (aE , bE) with Σ-reduct bE
...   | mkΣRed _ _ refl _ _ with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁Σ p _ _) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with Σ-reduct aE
...     | mkΣRed _ _ () _ _
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁Hom q sh₂) with joinW c p q
... | E , (aE , bE) with Hom-stk-reduct sh₂ bE
...   | mkHomStk _ _ _ _ refl with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁Hom p sh₁) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with Hom-stk-reduct sh₁ aE
...     | mkHomStk _ _ _ _ ()
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁Unit q) with joinW c p q
... | E , (aE , bE) with Unit-nf bE
...   | refl with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁Unit p) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with Unit-nf aE
...     | ()
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁Nat q) with joinW c p q
... | E , (aE , bE) with Nat-nf bE
...   | refl with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁Nat p) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with Nat-nf aE
...     | ()
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁Id q) with joinW c p q
... | E , (aE , bE) with Id-reduct bE
...   | _ , (_ , (_ , (refl , _))) with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁Id p) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with Id-reduct aE
...     | _ , (_ , (_ , ((), _)))
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁IMu q _ _ _ _) with joinW c p q
... | E , (aE , bE) with IMu-reduct bE
...   | mkIMuRed _ _ _ refl _ _ _ with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁IMu p _ _ _ _) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with IMu-reduct aE
...     | mkIMuRed _ _ _ () _ _ _
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁Fin q) with joinW c p q
... | E , (aE , bE) with Fin-nf bE
...   | refl with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁Fin p) (⊩₁DIhNe q n₂) with joinW c p q
... | E , (aE , bE) with DIhNe-reduct n₂ bE
...   | mkDIhNe _ _ _ _ _ refl with Fin-nf aE
...     | ()
irrel₁ c (⊩₁DIhNe p n₁) (⊩₁Desc q _ _) with joinW c p q
... | E , (aE , bE) with Desc-reduct bE
...   | _ , (refl , _) with DIhNe-reduct n₁ aE
...     | mkDIhNe _ _ _ _ _ ()
irrel₁ c (⊩₁DIhNe _ _) (⊩₁DIhNe _ _) = (λ _ h → h) , (λ _ h → h)
-- ★ `Desc`/`Desc`: the two index witnesses are convertible, and the
--   membership is the interpretation itself — re-based on the other
--   witness (`ikinterp-irrel`).
irrel₁ c (⊩₁Desc {I₀ = I₁} p cI₁ ⊩I₁) (⊩₁Desc {I₀ = I₂} q cI₂ ⊩I₂) with joinW c p q
... | E , (d₁ , d₂) with Desc-reduct d₁ | Desc-reduct d₂
...   | J₁ , (eq₁ , r₁) | J₂ , (eq₂ , r₂) with trans (sym eq₁) eq₂
...     | refl =
          ( (λ t h → ikinterp-irrel cEl ⊩I₁ ⊩I₂ h)
          , (λ t h → ikinterp-irrel (csymᵀ cEl) ⊩I₂ ⊩I₁ h) )
  where
  cI : I₁ ≅ I₂
  cI = ctrn (csym cI₁) (ctrn (hom→≅ r₁) (ctrn (csym (hom→≅ r₂)) cI₂))
  cEl : El I₁ ≅ᵀ El I₂
  cEl = El≅ cI
irrel₁ c (⊩₁IMu p cI₁ cD₁ ⊩I₁ K₁) (⊩₁IMu q cI₂ cD₂ ⊩I₂ K₂) with joinW c p q
... | E , (i₁ , i₂) with IMu-reduct i₁ | IMu-reduct i₂
...   | mkIMuRed I₁' D₁' j₁ eq₁ rI₁ rD₁ r₁ | mkIMuRed I₂' D₂' j₂ eq₂ rI₂ rD₂ r₂
      with IMuinj≡ (trans (sym eq₁) eq₂)
...     | (refl , (refl , refl))
          with church-rosser (ctrn (csym cD₁) (ctrn (hom→≅ rD₁) (ctrn (csym (hom→≅ rD₂)) cD₂)))
...       | D* , (d₁ , d₂) =
          ( (λ _ h → (projl h , irrelIMu K₁ K₂ d₁ d₂ r₁ r₂ (projr h)))
          , (λ _ h → (projl h , irrelIMu K₂ K₁ d₂ d₁ r₂ r₁ (projr h))) )
irrel₁ c (⊩₁Fin p) (⊩₁Fin q) with joinW c p q
... | E , (m₁ , m₂) with Fin-nf m₁
...   | refl with Fin-nf m₂
...     | refl = (λ _ h → h) , (λ _ h → h)

irrel₁ c (⊩₁Nat _)  (⊩₁Nat _)  = (λ _ h → h) , (λ _ h → h)
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
fwd₁ p (⊩₁Unit q) with confluentᵀ p q
... | E , (bE , uE) with Unit-nf uE
...   | refl = ⊩₁Unit bE
fwd₁ p (⊩₁Nat q) with confluentᵀ p q
... | E , (bE , nE) with Nat-nf nE
...   | refl = ⊩₁Nat bE
fwd₁ p (⊩₁IMu q cI cD ⊩I K) with confluentᵀ p q
... | E , (bE , mE) with IMu-reduct mE
...   | mkIMuRed _ _ _ refl rI rD _ =
        ⊩₁IMu bE (ctrn (csym (hom→≅ rI)) cI) (ctrn (csym (hom→≅ rD)) cD) ⊩I K
fwd₁ p (⊩₁Fin q) with confluentᵀ p q
... | E , (bE , mE) with Fin-nf mE
...   | refl = ⊩₁Fin bE
fwd₁ p (⊩₁Desc q cI ⊩I) with confluentᵀ p q
... | E , (bE , dE) with Desc-reduct dE
...   | J , (refl , rI) = ⊩₁Desc bE (ctrn (csym (hom→≅ rI)) cI) ⊩I
fwd₁ p (⊩₁DIhNe q n) with confluentᵀ p q
... | E , (bE , dE) with DIhNe-reduct n dE
...   | mkDIhNe _ _ _ _ n' refl = ⊩₁DIhNe bE n'
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
CR1₁ (⊩₁Unit _) h = h
CR1₁ (⊩₁Nat _)  h = projl h
CR1₁ (⊩₁IMu _ _ _ _ _) h = projl h
CR1₁ (⊩₁Fin _) h = projl h
CR1₁ (⊩₁Desc _ _ _) h = ikinterp-sn h
CR1₁ (⊩₁DIhNe _ _) h = h
CR1₁ (⊩₁Id _)    h = projl h

CR3₁ : {A : RTy Γ} (R : ⊩₁ A) {t : RTm Γ} → SNe t → R ⊩₁∋ t
CR3₁ (⊩₁base _)    nt = sn-ne nt
CR3₁ (⊩₁U _)       nt = (sn-ne nt , (⊩₀ne doneᵀ (sne→ne nt) , _))
CR3₁ (⊩₁ne _ _)    nt = sn-ne nt
CR3₁ (⊩₁Hom _ _)   nt = sn-ne nt
CR3₁ (⊩₁Unit _)    nt = sn-ne nt
CR3₁ (⊩₁Nat _)     nt = (sn-ne nt , nm-ne nt)
CR3₁ (⊩₁IMu _ _ _ _ _) nt = (sn-ne nt , imm-ne nt)
CR3₁ (⊩₁Fin _)    nt = (sn-ne nt , fm-ne nt)
CR3₁ (⊩₁Desc _ _ _) nt = iki-ne nt
CR3₁ (⊩₁DIhNe _ _) nt = sn-ne nt
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
exp₁ (⊩₁Unit _)    r h = sn-exp r h
exp₁ (⊩₁Nat _)     r h = (sn-exp r (projl h) , nm-exp r (projr h))
exp₁ (⊩₁IMu _ _ _ _ _) r h = (sn-exp r (projl h) , imm-exp r (projr h))
exp₁ (⊩₁Fin _)    r h = (sn-exp r (projl h) , fm-exp r (projr h))
exp₁ (⊩₁Desc _ _ _) r h = iki-exp r h
exp₁ (⊩₁DIhNe _ _) r h = sn-exp r h
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
mem-whred₁ (⊩₁Unit _) r h = sn-whred h r
mem-whred₁ (⊩₁Nat _)  r h = (sn-whred (projl h) r , natmem-whred (projr h) r)
mem-whred₁ (⊩₁IMu _ _ _ _ _) r h = (sn-whred (projl h) r , imumem-whred (projr h) r)
mem-whred₁ (⊩₁Fin _) r h = (sn-whred (projl h) r , finmem-whred (projr h) r)
mem-whred₁ (⊩₁Desc _ _ _) r h = ikinterp-whred h r
mem-whred₁ (⊩₁DIhNe _ _) r h = sn-whred h r
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
emb (⊩₀Unit p)    = ⊩₁Unit p
emb (⊩₀Nat p)     = ⊩₁Nat p
emb (⊩₀IMu p cI cD ⊩I K) = ⊩₁IMu p cI cD ⊩I K
emb (⊩₀Fin p)   = ⊩₁Fin p
emb (⊩₀ne p n)    = ⊩₁ne p n
emb (⊩₀Π p ⊩F ⊩G) =
  ⊩₁Π p (emb ⊩F) (λ u r → emb (⊩G u (projr (emb-coh ⊩F) u r)))
emb (⊩₀Σ p ⊩F ⊩G) =
  ⊩₁Σ p (emb ⊩F) (λ u r → emb (⊩G u (projr (emb-coh ⊩F) u r)))

emb-coh (⊩₀base _) = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀Hom _ _) = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀Id _)    = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀Unit _)  = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀Nat _)   = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀IMu _ _ _ _ _) = (λ _ h → h) , (λ _ h → h)
emb-coh (⊩₀Fin _)  = (λ _ h → h) , (λ _ h → h)
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

-- ★ WF stage C: the datatype codes are U-members, decoding to the
-- level-0 datatype interps that just arrived above.
sem-⌜Nat⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) → (⊩₁U p) ⊩₁∋ ⌜Nat⌝
sem-⌜Nat⌝ p = (sn-cNat , (⊩₀Nat (stepᵀ El-⌜Nat⌝ doneᵀ) , _))

sem-⌜Unit⌝ : {A : RTy Γ} (p : A ⟶ᵀ* U) → (⊩₁U p) ⊩₁∋ ⌜Unit⌝
sem-⌜Unit⌝ p = (sn-cUnit , (⊩₀Unit (stepᵀ El-⌜Unit⌝ doneᵀ) , _))


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

-- ★★ WF stage B — THE ORDER, SEMANTICALLY.  `Hom Nat a b` is the one
-- hom whose interp must FOLLOW its endpoints, and it can: both
-- endpoints' memberships at `Nat` carry `NatMem`, so the interp is a
-- DOUBLE meta-induction on the reaches-numeral payloads.  Zero on the
-- left gives `Unit` (the inequality HOLDS, trivially); successor over
-- zero gives `base` (it FAILS, and `base` has no closed inhabitants);
-- successor over successor peels and recurses; a stuck endpoint gives
-- the endpoint-keyed stuck order-hom.  This is the exact mirror of
-- stage A's `fund`-worker, which is why `NatMem` was built to mirror
-- `SN` in the first place.
homNatSem : {Γ : Cx} (a b : RTm Γ) →
            SN a → NatMem a → SN b → NatMem b → ⊩₁ (Hom (Nat {Γ}) a b)
homNatSem a b sa (nm-ne nt) sb mb =
  ⊩₁Hom doneᵀ (sh-NatH (natstk→homnat a b (sne→natstk nt)))
homNatSem a b sa (nm-exp {t' = a'} r ma) sb mb =
  bwd₁ (stepᵀ (ξ-Homˡ (snr→⟶ r)) doneᵀ)
       (homNatSem a' b (sn-whred sa r) ma sb mb)
homNatSem .nzero b sa nm-zero sb mb =
  bwd₁ (stepᵀ (Hom-Nat-z b) doneᵀ) (⊩₁Unit doneᵀ)
homNatSem .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-ne nt) =
  ⊩₁Hom doneᵀ (sh-NatH (sne→natstk nt))
homNatSem .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-exp {t' = b'} r mb) =
  bwd₁ (stepᵀ (ξ-Homʳ (snr→⟶ r)) doneᵀ)
       (homNatSem (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb)
homNatSem .(nsuc _) .nzero sa (nm-suc {n = m} ma) sb nm-zero =
  bwd₁ (stepᵀ (Hom-Nat-sz m) doneᵀ) (⊩₁base doneᵀ)
homNatSem .(nsuc _) .(nsuc _) sa (nm-suc {n = m} ma) sb (nm-suc {n = n} mb) =
  bwd₁ (stepᵀ (Hom-Nat-ss m n) doneᵀ)
       (homNatSem m n (snsuc-inv sa) ma (snsuc-inv sb) mb)
  where
  snsuc-inv : {k : RTm _} → SN (nsuc k) → SN k
  snsuc-inv (sn-nsuc h) = h

-- ★★ WF stage E: SN IS MEMBERSHIP, but only once `homNatSem` has been
-- UNSTUCK.  Every leaf it lands on (`⊩₁Hom`, `⊩₁Unit`, `⊩₁base`) has
-- `_ ⊩₁∋ x = SN x`, and `bwd₁` does not touch membership — but
-- `homNatSem` matches on the two `NatMem`s, so with those opaque the
-- reduction is BLOCKED and the identification is not definitional.
-- ⚠ this lemma is what `fund`'s `⊢ordtr` case actually needs; assuming
-- the conversion holds on the nose does not typecheck.
homNatSem-mem : {Γ : Cx} (a b : RTm Γ)
                (sa : SN a) (ma : NatMem a) (sb : SN b) (mb : NatMem b)
                {x : RTm Γ} → SN x → (homNatSem a b sa ma sb mb) ⊩₁∋ x
homNatSem-mem a b sa (nm-ne nt) sb mb sx = sx
homNatSem-mem a b sa (nm-exp {t' = a'} r ma) sb mb sx =
  bwd₁-mem⁻ (stepᵀ (ξ-Homˡ (snr→⟶ r)) doneᵀ) (homNatSem a' b (sn-whred sa r) ma sb mb)
            (homNatSem-mem a' b (sn-whred sa r) ma sb mb sx)
homNatSem-mem .nzero b sa nm-zero sb mb sx = sx
homNatSem-mem .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-ne nt) sx = sx
homNatSem-mem .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-exp {t' = b'} r mb) sx =
  bwd₁-mem⁻ (stepᵀ (ξ-Homʳ (snr→⟶ r)) doneᵀ)
            (homNatSem (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb)
            (homNatSem-mem (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb sx)
homNatSem-mem .(nsuc _) .nzero sa (nm-suc {n = m} ma) sb nm-zero sx = sx
homNatSem-mem .(nsuc _) .(nsuc _) sa (nm-suc {n = m} ma) sb (nm-suc {n = n} mb) sx =
  bwd₁-mem⁻ (stepᵀ (Hom-Nat-ss m n) doneᵀ)
            (homNatSem m n (snsuc-inv¹ sa) ma (snsuc-inv¹ sb) mb)
            (homNatSem-mem m n (snsuc-inv¹ sa) ma (snsuc-inv¹ sb) mb sx)
  where
  snsuc-inv¹ : {k : RTm _} → SN (nsuc k) → SN k
  snsuc-inv¹ (sn-nsuc h) = h

homSem₁ : {A : RTy Γ} (R : ⊩₁ A) {a b : RTm Γ} →
          R ⊩₁∋ a → R ⊩₁∋ b → ⊩₁ (Hom A a b)
homSem₁ (⊩₁base p)    ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-base)
homSem₁ (⊩₁ne p n)    ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom (sh-ne n))
homSem₁ (⊩₁Σ p ⊩F ⊩G) ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-Σ)
homSem₁ (⊩₁Hom p s)   ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom s)
homSem₁ (⊩₁Unit p)    ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-Unit)
homSem₁ (⊩₁Nat p) {a} {b} ha hb =
  bwd₁ (⟶ᵀ*-Homᵀ p)
       (homNatSem a b (projl ha) (projr ha) (projl hb) (projr hb))
homSem₁ (⊩₁Id p)      ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-Id)
homSem₁ (⊩₁IMu p _ _ _ _) ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-IMu)
homSem₁ (⊩₁Fin p)    ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-Fin)
homSem₁ (⊩₁Desc p _ _) ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-Desc)
homSem₁ (⊩₁DIhNe p n) ha hb = ⊩₁Hom (⟶ᵀ*-Homᵀ p) (sh-Hom (sh-DIhNe n))
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
-- ★★ WF stage C: the LEVEL-0 mirror of stage B's keystone.  `⌜Nat⌝ ∈ U`
-- means small types now reach the ORDER type, so level 0 needs its own
-- double meta-induction on both endpoints' `NatMem`.  It is `homNatSem`
-- clause for clause — every leaf it lands on (`⊩₁Unit`/`⊩₁base`/the
-- endpoint-keyed stuck `⊩₁Hom`) has a level-0 counterpart, and level 0
-- never had the `U` clause that was the only thing missing.
homNatSem₀ : {Γ : Cx} (a b : RTm Γ) →
             SN a → NatMem a → SN b → NatMem b → ⊩₀ (Hom (Nat {Γ}) a b)
homNatSem₀ a b sa (nm-ne nt) sb mb =
  ⊩₀Hom doneᵀ (sh-NatH (natstk→homnat a b (sne→natstk nt)))
homNatSem₀ a b sa (nm-exp {t' = a'} r ma) sb mb =
  bwd₀ (stepᵀ (ξ-Homˡ (snr→⟶ r)) doneᵀ)
       (homNatSem₀ a' b (sn-whred sa r) ma sb mb)
homNatSem₀ .nzero b sa nm-zero sb mb =
  bwd₀ (stepᵀ (Hom-Nat-z b) doneᵀ) (⊩₀Unit doneᵀ)
homNatSem₀ .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-ne nt) =
  ⊩₀Hom doneᵀ (sh-NatH (sne→natstk nt))
homNatSem₀ .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-exp {t' = b'} r mb) =
  bwd₀ (stepᵀ (ξ-Homʳ (snr→⟶ r)) doneᵀ)
       (homNatSem₀ (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb)
homNatSem₀ .(nsuc _) .nzero sa (nm-suc {n = m} ma) sb nm-zero =
  bwd₀ (stepᵀ (Hom-Nat-sz m) doneᵀ) (⊩₀base doneᵀ)
homNatSem₀ .(nsuc _) .(nsuc _) sa (nm-suc {n = m} ma) sb (nm-suc {n = n} mb) =
  bwd₀ (stepᵀ (Hom-Nat-ss m n) doneᵀ)
       (homNatSem₀ m n (snsuc-inv₀ sa) ma (snsuc-inv₀ sb) mb)
  where
  snsuc-inv₀ : {k : RTm _} → SN (nsuc k) → SN k
  snsuc-inv₀ (sn-nsuc h) = h

-- ★ every leaf of `homNatSem₀` has membership `SN t` — `⊩₀Unit`,
-- `⊩₀base` and the stuck `⊩₀Hom` all do, and `bwd₀` never changes a
-- membership.  So order-hom membership is ENDPOINT-BLIND, which is what
-- `homSem₀-mem-endpoints` needs at the `⊩₀Nat` arm.  Both directions by
-- the same induction as `homNatSem₀` itself.
hns₀-out : {Γ : Cx} (a b : RTm Γ) (sa : SN a) (ma : NatMem a)
           (sb : SN b) (mb : NatMem b) {t : RTm Γ} →
           (homNatSem₀ a b sa ma sb mb) ⊩₀∋ t → SN t
hns₀-out a b sa (nm-ne nt) sb mb h = h
hns₀-out a b sa (nm-exp {t' = a'} r ma) sb mb h =
  hns₀-out a' b (sn-whred sa r) ma sb mb
    (bwd₀-mem _ (homNatSem₀ a' b (sn-whred sa r) ma sb mb) h)
hns₀-out .nzero b sa nm-zero sb mb h = h
hns₀-out .(nsuc _) b sa (nm-suc ma) sb (nm-ne nt) h = h
hns₀-out .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-exp {t' = b'} r mb) h =
  hns₀-out (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb
    (bwd₀-mem _ (homNatSem₀ (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb) h)
hns₀-out .(nsuc _) .nzero sa (nm-suc ma) sb nm-zero h = h
hns₀-out .(nsuc _) .(nsuc _) sa (nm-suc {n = m} ma) sb (nm-suc {n = n} mb) h =
  hns₀-out m n (snsuc-inv₀ sa) ma (snsuc-inv₀ sb) mb
    (bwd₀-mem _ (homNatSem₀ m n (snsuc-inv₀ sa) ma (snsuc-inv₀ sb) mb) h)
  where
  snsuc-inv₀ : {k : RTm _} → SN (nsuc k) → SN k
  snsuc-inv₀ (sn-nsuc w) = w

hns₀-in : {Γ : Cx} (a b : RTm Γ) (sa : SN a) (ma : NatMem a)
          (sb : SN b) (mb : NatMem b) {t : RTm Γ} →
          SN t → (homNatSem₀ a b sa ma sb mb) ⊩₀∋ t
hns₀-in a b sa (nm-ne nt) sb mb h = h
hns₀-in a b sa (nm-exp {t' = a'} r ma) sb mb h =
  bwd₀-mem⁻ _ (homNatSem₀ a' b (sn-whred sa r) ma sb mb)
    (hns₀-in a' b (sn-whred sa r) ma sb mb h)
hns₀-in .nzero b sa nm-zero sb mb h = h
hns₀-in .(nsuc _) b sa (nm-suc ma) sb (nm-ne nt) h = h
hns₀-in .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-exp {t' = b'} r mb) h =
  bwd₀-mem⁻ _ (homNatSem₀ (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb)
    (hns₀-in (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb h)
hns₀-in .(nsuc _) .nzero sa (nm-suc ma) sb nm-zero h = h
hns₀-in .(nsuc _) .(nsuc _) sa (nm-suc {n = m} ma) sb (nm-suc {n = n} mb) h =
  bwd₀-mem⁻ _ (homNatSem₀ m n (snsuc-inv₀ sa) ma (snsuc-inv₀ sb) mb)
    (hns₀-in m n (snsuc-inv₀ sa) ma (snsuc-inv₀ sb) mb h)
  where
  snsuc-inv₀ : {k : RTm _} → SN (nsuc k) → SN k
  snsuc-inv₀ (sn-nsuc w) = w

-- the `PayT` mirror of `bwd₀-mem⁻`: only the ⌜Π⌝ arm carries a payload,
-- and `bwd₀` leaves it untouched.
payT-bwd₀' : {A B : RTy Γ} (q : A ⟶ᵀ* B) (R : ⊩₀ B) {c : RTm Γ} →
             PayT R c → PayT (bwd₀ q R) c
payT-bwd₀' q (⊩₀base _)  pay = _
payT-bwd₀' q (⊩₀ne _ _)  pay = _
payT-bwd₀' q (⊩₀Σ _ _ _) pay = _
payT-bwd₀' q (⊩₀Hom _ _) pay = _
payT-bwd₀' q (⊩₀Id _)    pay = _
payT-bwd₀' q (⊩₀Unit _)  pay = _
payT-bwd₀' q (⊩₀Nat _)   pay = _
payT-bwd₀' q (⊩₀IMu _ _ _ _ _) pay = _
payT-bwd₀' q (⊩₀Fin _)  pay = _
payT-bwd₀' q (⊩₀Π _ _ _) pay = pay

-- ★ and the payload is trivial at every leaf too — none of `⊩₀Unit`,
-- `⊩₀base` or the stuck `⊩₀Hom` is the ⌜Π⌝ arm, the only one that
-- carries a `PayT`.  Same induction once more.
hns₀-pay : {Γ : Cx} (a b : RTm Γ) (sa : SN a) (ma : NatMem a)
           (sb : SN b) (mb : NatMem b) {c : RTm Γ} →
           PayT (homNatSem₀ a b sa ma sb mb) c
hns₀-pay a b sa (nm-ne nt) sb mb = _
hns₀-pay a b sa (nm-exp {t' = a'} r ma) sb mb =
  payT-bwd₀' _ (homNatSem₀ a' b (sn-whred sa r) ma sb mb)
    (hns₀-pay a' b (sn-whred sa r) ma sb mb)
hns₀-pay .nzero b sa nm-zero sb mb = _
hns₀-pay .(nsuc _) b sa (nm-suc ma) sb (nm-ne nt) = _
hns₀-pay .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-exp {t' = b'} r mb) =
  payT-bwd₀' _ (homNatSem₀ (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb)
    (hns₀-pay (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb)
hns₀-pay .(nsuc _) .nzero sa (nm-suc ma) sb nm-zero = _
hns₀-pay .(nsuc _) .(nsuc _) sa (nm-suc {n = m} ma) sb (nm-suc {n = n} mb) =
  payT-bwd₀' _ (homNatSem₀ m n (snsuc-inv₀ sa) ma (snsuc-inv₀ sb) mb)
    (hns₀-pay m n (snsuc-inv₀ sa) ma (snsuc-inv₀ sb) mb)
  where
  snsuc-inv₀ : {k : RTm _} → SN (nsuc k) → SN k
  snsuc-inv₀ (sn-nsuc w) = w

homSem₀ : {A : RTy Γ} (R : ⊩₀ A) {a b : RTm Γ} →
          R ⊩₀∋ a → R ⊩₀∋ b → ⊩₀ (Hom A a b)
homSem₀ (⊩₀base p)    ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-base)
homSem₀ (⊩₀ne p n)    ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-Hom (sh-ne n))
homSem₀ (⊩₀Σ p ⊩F ⊩G) ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-Σ)
homSem₀ (⊩₀Hom p s)   ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-Hom s)
homSem₀ (⊩₀Unit p)    ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-Unit)
homSem₀ (⊩₀IMu p _ _ _ _) ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-IMu)
homSem₀ (⊩₀Fin p)    ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-Fin)
homSem₀ (⊩₀Nat p) {a} {b} ha hb =
  bwd₀ (⟶ᵀ*-Homᵀ p)
       (homNatSem₀ a b (projl ha) (projr ha) (projl hb) (projr hb))
homSem₀ (⊩₀Id p)      ha hb = ⊩₀Hom (⟶ᵀ*-Homᵀ p) (sh-Hom sh-Id)
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
homSem₀-mem-endpoints (⊩₀IMu p _ _ _ _) ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀Fin p)    ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀ne p n)    ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀Σ p ⊩F ⊩G) ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀Hom p s)   ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀Id p) ha hb ha' hb' h = h
homSem₀-mem-endpoints (⊩₀Unit p) ha hb ha' hb' h = h
-- ★ the ORDER hom: membership is `SN` at every leaf, so the endpoint
-- switch is `out` then `in` through the two transparency lemmas.
homSem₀-mem-endpoints (⊩₀Nat p) {a} {b} {a'} {b'} ha hb ha' hb' h =
  bwd₀-mem⁻ (⟶ᵀ*-Homᵀ p)
    (homNatSem₀ a' b' (projl ha') (projr ha') (projl hb') (projr hb'))
    (hns₀-in a' b' (projl ha') (projr ha') (projl hb') (projr hb')
      (hns₀-out a b (projl ha) (projr ha) (projl hb) (projr hb)
        (bwd₀-mem (⟶ᵀ*-Homᵀ p)
          (homNatSem₀ a b (projl ha) (projr ha) (projl hb) (projr hb))
          h)))
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
payHomT (⊩₀IMu _ _ _ _ _) payC ha hb = _
payHomT (⊩₀Fin _)  payC ha hb = _
payHomT (⊩₀ne _ _)  payC ha hb = _
payHomT (⊩₀Σ _ _ _) payC ha hb = _
payHomT (⊩₀Hom _ _) payC ha hb = _
payHomT (⊩₀Id p) payC ha hb = _
payHomT (⊩₀Unit p) payC ha hb = _
payHomT (⊩₀Nat p) {C} {a} {b} payC ha hb =
  payT-bwd₀' (⟶ᵀ*-Homᵀ p)
    (homNatSem₀ a b (projl ha) (projr ha) (projl hb) (projr hb))
    (hns₀-pay a b (projl ha) (projr ha) (projl hb) (projr hb))
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
  payT-bwd₀ q (⊩₀IMu _ _ _ _ _) pay = _
  payT-bwd₀ q (⊩₀Fin _)  pay = _
  payT-bwd₀ q (⊩₀ne _ _)  pay = _
  payT-bwd₀ q (⊩₀Σ _ _ _) pay = _
  payT-bwd₀ q (⊩₀Hom _ _) pay = _
  payT-bwd₀ q (⊩₀Id _) pay = _
  payT-bwd₀ q (⊩₀Unit _) pay = _
  payT-bwd₀ q (⊩₀Nat _) pay = _
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

-- a neutral is never a pair (what refutes `psplit-β` on a normal neutral).
sne-nopair : {a b : RTm Γ} → SNe (pair a b) → ⊥
sne-nopair ()

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
wne (sne-absurd snc sne₀) with wn snc | wn sne₀
... | mkWN c₁ rc nmc snc₁ | mkWN n₁ r₁ nm₁ sn₁ =
      mkWNe (absurd c₁ n₁)
            (⟶*-trans (⟶*-absurdᶜ rc) (⟶*-absurdᵉ r₁))
            nrm' (sne-absurd snc₁ sn₁)
  where
    nrm' : IsNormal (absurd c₁ n₁)
    nrm' (ξ-absurdᶜ q) = nmc q
    nrm' (ξ-absurdᵉ q) = nm₁ q
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
    nrm' (tr-J-Unit _ _ _ _ _) = ⊥-elim (f≢t key')
    nrm' (tr-J-Fin _ _ _ _ _) = ⊥-elim (f≢t key')
    nrm' (tr-J-IMu _ _ _ _ _) = ⊥-elim (f≢t key')
    nrm' (tr-taut _ _)      = ⊥-elim (f≢t key')
    nrm' (tr-J-Hom _ _ _ c₁ _ _ _ _ kh) =
      f≢t (trans (sym (stkA?⊥dead c₁ kh)) key')
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
wne (sne-jsub {d = d} {p = p} d₀ p₀ e₀ key) with wn d₀ | wn p₀ | wn e₀
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ | mkWN n₃ r₃ nm₃ sn₃ =
      mkWNe (jsub n₁ n₂ n₃)
            (⟶*-trans (⟶*-jsubᵈ r₁)
                      (⟶*-trans (⟶*-jsubᵖ r₂) (⟶*-jsubᵉ r₃)))
            nrm' (sne-jsub sn₁ sn₂ sn₃ key')
  where
    key' : idstk? n₂ ≡ true
    key' = idstk?-red* r₂ key

    nrm' : IsNormal (jsub n₁ n₂ n₃)
    nrm' (jsub-refl _ _ _ _) = f≢t key'
    nrm' (ξ-jsubᵈ q) = nm₁ q
    nrm' (ξ-jsubᵖ q) = nm₂ q
    nrm' (ξ-jsubᵉ q) = nm₃ q
wne (sne-natrec {z = z} {w = w} {n = n} z₀ w₀ n₀ key)
  with wn z₀ | wn w₀ | wn n₀
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ | mkWN n₃ r₃ nm₃ sn₃ =
      mkWNe (natrec n₁ n₂ n₃)
            (⟶*-trans (⟶*-natrecᶻ r₁)
                      (⟶*-trans (⟶*-natrecˢ r₂) (⟶*-natrecⁿ r₃)))
            nrm' (sne-natrec sn₁ sn₂ sn₃ key')
  where
    key' : natstk? n₃ ≡ true
    key' = natstk?-red* r₃ key

    nrm' : IsNormal (natrec n₁ n₂ n₃)
    nrm' (natrec-zero _ _)    = f≢t key'
    nrm' (natrec-suc _ _ _)   = f≢t key'
    nrm' (ξ-natrecᶻ q) = nm₁ q
    nrm' (ξ-natrecˢ q) = nm₂ q
    nrm' (ξ-natrecⁿ q) = nm₃ q
-- ★★ WF stage E: five subterms to normalize, but only the three BOUNDS
-- carry the key — and once they are normal, all five root rules are
-- refuted by `key'` computing to `false ≡ true`, exactly as `natrec`'s
-- two are.
-- ★★ LEVITATED FAMILIES: every carried subterm is normalised, and once the
--   scrutinee is normal each root rule is refuted by its key (`psplit`'s
--   neutral pair is never a `pair`).
wne (sne-ielim a0₀ a1₀ a2₀ a3₀ key)
  with wn a0₀ | wn a1₀ | wn a2₀ | wn a3₀
... | mkWN n0 r0 nm0 sn0 | mkWN n1 r1 nm1 sn1 | mkWN n2 r2 nm2 sn2 | mkWN n3 r3 nm3 sn3 =
      mkWNe (ielim n0 n1 n2 n3) (⟶*-trans (⟶*-ielimᴰ r0) (⟶*-trans (⟶*-ielimⁱ r1) (⟶*-trans (⟶*-ielimᵉ r2) (⟶*-ielimᵗ r3))))
            nrm' (sne-ielim sn0 sn1 sn2 sn3 key')
  where
    key' : mustk? n3 ≡ true
    key' = mustk?-red* r3 key

    nrm' : IsNormal (ielim n0 n1 n2 n3)
    nrm' (ι _ _ _ _) = f≢t key'
    nrm' (ξ-ielimᴰ q) = nm0 q
    nrm' (ξ-ielimⁱ q) = nm1 q
    nrm' (ξ-ielimᵉ q) = nm2 q
    nrm' (ξ-ielimᵗ q) = nm3 q
wne (sne-dpay a0₀ a1₀ a2₀ a3₀ key)
  with wn a0₀ | wn a1₀ | wn a2₀ | wn a3₀
... | mkWN n0 r0 nm0 sn0 | mkWN n1 r1 nm1 sn1 | mkWN n2 r2 nm2 sn2 | mkWN n3 r3 nm3 sn3 =
      mkWNe (dpay n0 n1 n2 n3) (⟶*-trans (⟶*-dpayᴵ r0) (⟶*-trans (⟶*-dpayᴰ r1) (⟶*-trans (⟶*-dpayᶜ r2) (⟶*-dpayⁱ r3))))
            nrm' (sne-dpay sn0 sn1 sn2 sn3 key')
  where
    key' : dstk? n2 ≡ true
    key' = dstk?-red* r2 key

    nrm' : IsNormal (dpay n0 n1 n2 n3)
    nrm' (dpay-ι _ _ _ _) = f≢t key'
    nrm' (dpay-σ _ _ _ _ _) = f≢t key'
    nrm' (dpay-ρ _ _ _ _ _) = f≢t key'
    nrm' (ξ-dpayᴵ q) = nm0 q
    nrm' (ξ-dpayᴰ q) = nm1 q
    nrm' (ξ-dpayᶜ q) = nm2 q
    nrm' (ξ-dpayⁱ q) = nm3 q
wne (sne-dih a0₀ a1₀ a2₀ a3₀ key)
  with wn a0₀ | wn a1₀ | wn a2₀ | wn a3₀
... | mkWN n0 r0 nm0 sn0 | mkWN n1 r1 nm1 sn1 | mkWN n2 r2 nm2 sn2 | mkWN n3 r3 nm3 sn3 =
      mkWNe (dih n0 n1 n2 n3) (⟶*-trans (⟶*-dihᴰ r0) (⟶*-trans (⟶*-dihᵉ r1) (⟶*-trans (⟶*-dihᶜ r2) (⟶*-dihᵖ r3))))
            nrm' (sne-dih sn0 sn1 sn2 sn3 key')
  where
    key' : dstk? n2 ≡ true
    key' = dstk?-red* r2 key

    nrm' : IsNormal (dih n0 n1 n2 n3)
    nrm' (dih-ι _ _ _ _) = f≢t key'
    nrm' (dih-σ _ _ _ _ _) = f≢t key'
    nrm' (dih-ρ _ _ _ _ _) = f≢t key'
    nrm' (ξ-dihᴰ q) = nm0 q
    nrm' (ξ-dihᵉ q) = nm1 q
    nrm' (ξ-dihᶜ q) = nm2 q
    nrm' (ξ-dihᵖ q) = nm3 q
wne (sne-fcase a0₀ a1₀ a2₀ key)
  with wn a0₀ | wn a1₀ | wn a2₀
... | mkWN n0 r0 nm0 sn0 | mkWN n1 r1 nm1 sn1 | mkWN n2 r2 nm2 sn2 =
      mkWNe (fcase n0 n1 n2) (⟶*-trans (⟶*-fcaseᵗ r0) (⟶*-trans (⟶*-fcaseᵃ r1) (⟶*-fcaseᵇ r2)))
            nrm' (sne-fcase sn0 sn1 sn2 key')
  where
    key' : finstk? n0 ≡ true
    key' = finstk?-red* r0 key

    nrm' : IsNormal (fcase n0 n1 n2)
    nrm' (fcase-z _ _) = f≢t key'
    nrm' (fcase-s _ _ _) = f≢t key'
    nrm' (ξ-fcaseᵗ q) = nm0 q
    nrm' (ξ-fcaseᵃ q) = nm1 q
    nrm' (ξ-fcaseᵇ q) = nm2 q
wne (sne-fcase0 a0₀)
  with wn a0₀
... | mkWN n0 r0 nm0 sn0 =
      mkWNe (fcase0 n0) (⟶*-fcase0 r0)
            nrm' (sne-fcase0 sn0)
  where
    nrm' : IsNormal (fcase0 n0)
    nrm' (ξ-fcase0 q) = nm0 q
wne (sne-psplit a0₀ a1₀)
  with wn a0₀ | wne a1₀
... | mkWN n0 r0 nm0 sn0 | mkWNe n1 r1 nm1 ne1 =
      mkWNe (psplit n0 n1) (⟶*-trans (⟶*-psplitᵇ r0) (⟶*-psplitᵍ r1))
            nrm' (sne-psplit sn0 ne1)
  where
    nrm' : IsNormal (psplit n0 n1)
    nrm' (psplit-β _ _ _) = sne-nopair ne1
    nrm' (ξ-psplitᵇ q) = nm0 q
    nrm' (ξ-psplitᵍ q) = nm1 q
wne (sne-ordtr {a = a} {t = t} {u = u} a₀ t₀ u₀ p₀ q₀ key)
  with wn a₀ | wn t₀ | wn u₀ | wn p₀ | wn q₀
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ | mkWN n₃ r₃ nm₃ sn₃
    | mkWN n₄ r₄ nm₄ sn₄ | mkWN n₅ r₅ nm₅ sn₅ =
      mkWNe (ordtr n₁ n₂ n₃ n₄ n₅)
            (⟶*-trans (⟶*-ordtrᵃ r₁)
             (⟶*-trans (⟶*-ordtrᵗ r₂)
              (⟶*-trans (⟶*-ordtrᵘ r₃)
               (⟶*-trans (⟶*-ordtrᵖ r₄) (⟶*-ordtrq r₅)))))
            nrm' (sne-ordtr sn₁ sn₂ sn₃ sn₄ sn₅ key')
  where
    key' : ordstk? n₁ n₂ n₃ ≡ true
    key' = ordstk?-red*ᵘ {a = n₁} {t = n₂} {u = u} r₃
             (ordstk?-red*ᵗ {a = n₁} {t = t} {u = u} r₂
               (ordstk?-red*ᵃ {a = a} {t = t} {u = u} r₁ key))

    nrm' : IsNormal (ordtr n₁ n₂ n₃ n₄ n₅)
    nrm' (ordtr-z _ _ _ _)     = f≢t key'
    nrm' (ordtr-szz _ _ _)     = f≢t key'
    nrm' (ordtr-ssz _ _ _ _)   = f≢t key'
    nrm' (ordtr-szs _ _ _ _)   = f≢t key'
    nrm' (ordtr-sss _ _ _ _ _) = f≢t key'
    nrm' (ξ-ordtrᵃ q) = nm₁ q
    nrm' (ξ-ordtrᵗ q) = nm₂ q
    nrm' (ξ-ordtrᵘ q) = nm₃ q
    nrm' (ξ-ordtrᵖ q) = nm₄ q
    nrm' (ξ-ordtrq q) = nm₅ q

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
wn sn-cNat = mkWN ⌜Nat⌝ done (λ ()) sn-cNat
wn sn-cUnit = mkWN ⌜Unit⌝ done (λ ()) sn-cUnit
wn (sn-cIMu a0₀ a1₀ a2₀) with wn a0₀ | wn a1₀ | wn a2₀
... | mkWN n0 r0 nm0 sn0 | mkWN n1 r1 nm1 sn1 | mkWN n2 r2 nm2 sn2 =
      mkWN (⌜IMu⌝ n0 n1 n2) (⟶*-trans (⟶*-⌜IMu⌝ᴵ r0) (⟶*-trans (⟶*-⌜IMu⌝ᴰ r1) (⟶*-⌜IMu⌝ⁱ r2))) nrm' (sn-cIMu sn0 sn1 sn2)
  where
    nrm' : IsNormal (⌜IMu⌝ n0 n1 n2)
    nrm' (ξ-⌜IMu⌝ᴵ q) = nm0 q
    nrm' (ξ-⌜IMu⌝ᴰ q) = nm1 q
    nrm' (ξ-⌜IMu⌝ⁱ q) = nm2 q
wn (sn-cFin {n = n}) = mkWN (⌜Fin⌝ n) done (λ ()) sn-cFin
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
wn (sn-cId c a b) with wn c | wn a | wn b
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ | mkWN n₃ r₃ nm₃ sn₃ =
      mkWN (⌜Id⌝ n₁ n₂ n₃)
           (⟶*-trans (⟶*-⌜Id⌝ᶜ r₁) (⟶*-trans (⟶*-⌜Id⌝ˡ r₂) (⟶*-⌜Id⌝ʳ r₃)))
           nrm' (sn-cId sn₁ sn₂ sn₃)
  where
    nrm' : IsNormal (⌜Id⌝ n₁ n₂ n₃)
    nrm' (ξ-⌜Id⌝ᶜ q) = nm₁ q
    nrm' (ξ-⌜Id⌝ˡ q) = nm₂ q
    nrm' (ξ-⌜Id⌝ʳ q) = nm₃ q
wn (sn-idrefl c t) with wn c | wn t
... | mkWN n₁ r₁ nm₁ sn₁ | mkWN n₂ r₂ nm₂ sn₂ =
      mkWN (idrefl n₁ n₂)
           (⟶*-trans (⟶*-idreflᶜ r₁) (⟶*-idreflᵃ r₂))
           nrm' (sn-idrefl sn₁ sn₂)
  where
    nrm' : IsNormal (idrefl n₁ n₂)
    nrm' (ξ-idreflᶜ q) = nm₁ q
    nrm' (ξ-idreflᵃ q) = nm₂ q
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
wn sn-unit  = mkWN unit done (λ ()) sn-unit
wn sn-nzero = mkWN nzero done (λ ()) sn-nzero
wn (sn-nsuc h) with wn h
... | mkWN n₁ r₁ nm₁ sn₁ = mkWN (nsuc n₁) (⟶*-nsuc r₁) nrm' (sn-nsuc sn₁)
  where
    nrm' : IsNormal (nsuc n₁)
    nrm' (ξ-nsuc q) = nm₁ q
wn (sn-con a0₀) with wn a0₀
... | mkWN n0 r0 nm0 sn0 =
      mkWN (con n0) (⟶*-con r0) nrm' (sn-con sn0)
  where
    nrm' : IsNormal (con n0)
    nrm' (ξ-con q) = nm0 q
wn (sn-dι a0₀) with wn a0₀
... | mkWN n0 r0 nm0 sn0 =
      mkWN (dι n0) (⟶*-dι r0) nrm' (sn-dι sn0)
  where
    nrm' : IsNormal (dι n0)
    nrm' (ξ-dι q) = nm0 q
wn (sn-dσ a0₀ a1₀) with wn a0₀ | wn a1₀
... | mkWN n0 r0 nm0 sn0 | mkWN n1 r1 nm1 sn1 =
      mkWN (dσ n0 n1) (⟶*-trans (⟶*-dσˢ r0) (⟶*-dσᶠ r1)) nrm' (sn-dσ sn0 sn1)
  where
    nrm' : IsNormal (dσ n0 n1)
    nrm' (ξ-dσˢ q) = nm0 q
    nrm' (ξ-dσᶠ q) = nm1 q
wn (sn-dρ a0₀ a1₀) with wn a0₀ | wn a1₀
... | mkWN n0 r0 nm0 sn0 | mkWN n1 r1 nm1 sn1 =
      mkWN (dρ n0 n1) (⟶*-trans (⟶*-dρʲ r0) (⟶*-dρᶜ r1)) nrm' (sn-dρ sn0 sn1)
  where
    nrm' : IsNormal (dρ n0 n1)
    nrm' (ξ-dρʲ q) = nm0 q
    nrm' (ξ-dρᶜ q) = nm1 q
wn sn-fzero = mkWN fzero done (λ ()) sn-fzero
wn (sn-fsuc a0₀) with wn a0₀
... | mkWN n0 r0 nm0 sn0 =
      mkWN (fsuc n0) (⟶*-fsuc r0) nrm' (sn-fsuc sn0)
  where
    nrm' : IsNormal (fsuc n0)
    nrm' (ξ-fsuc q) = nm0 q
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
