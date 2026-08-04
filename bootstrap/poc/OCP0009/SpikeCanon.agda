------------------------------------------------------------------------
-- OCP-0009 · W2b, spike — `SpikeCanon`: THE CANONICITY PACKAGE'S RULE
--                        FORMAT, SETTLED.
--
-- The deferred W2b unit was: `hrefl`'s spine-recursive unfold family
-- (incl. hrefl-Π), J-Hom, tr-pw, and the spine judgments `Pw`/`StkC`.
-- The fear on record: spine-recursive, PREMISE-CARRYING reduction rules
-- would cascade through the premise-free Takahashi confluence
-- development.  This spike settles the design.  Three findings:
--
-- ★★ FINDING 1 (the headline): THE FEAR WAS UNFOUNDED — THE STAGE-3
-- BOOLEAN-CLASSIFIER ARCHITECTURE ALREADY IS THE ANSWER.  The spine
-- judgments `Pw`/`StkC` become total Boolean classifiers `pw?`/`stkC?`
-- (mechanized below, on the REAL syntax), the "spine-recursive unfold
-- family" becomes ONE rule whose right-hand side calls a total FUNCTION
-- `pwBody` (the pointwise-body code), and every rule carries only a
-- Boolean-equality key — exactly the `sne-tr`/`trstk?` pattern the
-- tower already pays for.  `_⁺` stays a total syntax-directed function
-- (the keys are decidable); the keys are closed under reduction,
-- renaming (as equalities) and substitution (mechanized below), which
-- is all that `⟶-sub`/`⟶-ren`/Takahashi/anti-renaming need.
--
-- ★ THE RULE SET (the package, in full — Boolean keys inlined):
--
--   hrefl-pw : pw? C ≡ true →
--              hrefl C s ⟶ lam (hrefl (pwBody C)
--                                      (app (renTm vs s) (var vz)))
--     -- `hrefl-Π` is the C = ⌜Π⌝ γ δ instance (pwBody = δ); the whole
--     -- ⌜Hom⌝ⁿ(⌜Π⌝…) spine family collapses into this ONE rule,
--     -- because `pwBody` does the spine recursion at firing time.
--
--   tr-J-Hom : stkC? c₁ ≡ true →
--              tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e ⟶ e
--     -- J at Hom-codes over PERMANENTLY-STABLE spines only: `stkC?`
--     -- excludes ⌜Π⌝-able codes (those paths unfold to lambdas by
--     -- hrefl-pw — an unjoinable overlap if J also fired) and
--     -- neutral codes (a substitution could turn them ⌜Π⌝-able; the
--     -- key must be substitution-stable, and `stkC?` is — §2).
--
--   tr-pw    : pw? c ≡ true →
--              tr (⌜Hom⌝ c a (var vz)) (lam f) e ⟶
--              lam (tr (⌜Hom⌝ (renTm pwShift (pwBody c))
--                             (app (renTm vs a) (var (vs vz)))
--                             (var vz))
--                      f
--                      (app (renTm vs e) (var vz)))
--     -- POINTWISE TRANSPORT: the transported function's value at x is
--     -- the inner transport of `e x` along the path's body `f` (the
--     -- rule fires on a literal `lam`, so `f` is available without a
--     -- β-redex), at the pointwise motive `pwBody c` — again the
--     -- Boolean key + total function; keyed on the LITERAL `var vz`
--     -- endpoint like `tr-taut`, which every typed instance has.
--     -- (`pwShift`/`renTm vs` re-index into the new binder telescope
--     -- (Γ, x, end′); the original endpoint var is mapped to junk —
--     -- typed-unreachable since the motive's components are vz-free
--     -- by `⊢tr`'s premises, and harmless to confluence since any
--     -- fixed renaming commutes with steps.)
--
-- ★★ FINDING 2 (the rejection): NO CODE-LEVEL `⌜Hom⌝-Π`.  The tempting
-- alternative — make codes compute, `⌜Hom⌝ (⌜Π⌝ γ δ) a b ⟶ ⌜Π⌝ γ
-- (⌜Hom⌝ δ (app a↑ vz) (app b↑ vz))`, so spines normalize at the code
-- level and only a literal-⌜Π⌝ `hrefl-Π` is ever needed — is FATAL to
-- the stage-2/3 architecture: the pinned motive `⌜Hom⌝ c a (var vz)`
-- becomes a ROOT REDEX whenever `c` is ⌜Π⌝-headed, so `ξ-trᵈ` rewrites
-- the motive to a ⌜Π⌝-headed term that NO typing rule matches (`gen-tr`
-- and subject reduction break immediately), and the critical pair with
-- `tr-pw` cannot join (one side is the pointwise lambda, the other a
-- `tr` at a motive shape with no rules).  The spine collapse must live
-- in a FUNCTION (`pwBody`), not in the reduction relation.
--
-- ★ FINDING 3 (the critical pairs, all discharged by the keys):
--   * hrefl-pw vs ξ-hreflᶜ — joins: `pw?-red` transports the key,
--     `pwBody-red` maps the code's step to steps of the unfolded body
--     (BOTH MECHANIZED, §2 — `pwBody-red`'s induction is also the
--     template for its parallel-reduction analogue in Conf);
--   * hrefl-pw vs the three J rules (as `tr`'s path) — DISJOINT keys:
--     `pw? ⌜base⌝ = pw? (⌜Σ⌝ …) = false` definitionally, and
--     `stk⊥pw` (§1) refutes the J-Hom overlap;
--   * tr-pw vs tr-taut — motive shapes `⌜Hom⌝ …` vs `var vz` disjoint;
--   * tr-pw vs ξ-trᵈ — joins via `pw?-red`/`pwBody-red` (and `pwDom` is
--     not even mentioned by the RHS — lam is unannotated);
--   * tr-J-Hom vs code steps in c₁ — `stkC?-red`;
--   * substitution/renaming — `pw?-sub`/`stkC?-sub` (preservation) and
--     `pw?-ren`/`stkC?-ren`/`pwBody-ren`/`pwBody-sub` (equalities), all
--     mechanized in §2: `⟶-sub`, `⟶-ren`, and Fund's anti-renaming
--     keep their current one-line-per-key shape.
--
-- ★ §3 MECHANIZES THE COHERENCE CENTERPIECE, `pw-Hom-decode`: for a
-- pw-able code C, `Hom (El C) x y` reduces to
-- `Π (El (pwDom C)) Body` where `Hom (El (pwBody C)) (x·) (y·)` also
-- reduces to `Body` (a JOIN, because deeper spines unfold one `El` step
-- further on the left).  This is the single lemma behind ALL the new
-- rules' subject-reduction cases: hrefl-pw's LHS/RHS types convert
-- through it, and tr-pw's payload/result types likewise.
--
-- THE REMAINING BILL (measured, for the landing sessions):
--   * Type: the three rules + `pw?`/`pwBody`/`pwShift`/`stkC?` (these
--     live in Var or Type; the classifiers are import-ready from here);
--   * Conf: `_⁺` rows keyed on the Booleans (`hrefl C s ⁺` fires
--     hrefl-pw when `pw? C`; `tr` rows likewise) + parallel versions of
--     the three rules + `pwBody`'s parallel-step compatibility;
--   * Subj: sr for the three rules — hrefl-pw/tr-pw from
--     `pw-Hom-decode` + generation; tr-J-Hom needs a `StkAmb` reduct
--     analysis of `El c₁` under `stkC?` (the `BaseAmb`/`ΣAmb` pattern,
--     powered by `stkC?-red`);
--   * LR: the classifier flips — `hrefl` is no longer unconditionally
--     neutral (`sne-hrefl` gains the key `pw? c ≡ false`-side;
--     `pathstk? (hrefl c t)` narrows from `stablecd? c` to neutral
--     spines, since stk-⌜Hom⌝ codes are now J-able and pw codes
--     unfold); `trstk? d (lam f)` narrows from `homheaded? d` to
--     `homheaded? d ∧ not (pw? (code of d))`; head strategy gains
--     `snr-hrefl-pw`/`snr-J-Hom`/`snr-tr-pw`;
--   * Fund: `⊢hrefl`'s case splits on `pw?` (pw codes build the
--     Π-membership pointwise); `⊢tr`'s `go`/`goh` gain the three
--     branches (J-Hom discharges like J-base; tr-pw recurses into the
--     pointwise instance — the payload membership comes from the
--     `⊩₁Π`-membership's app-closure, as in `⊢trU`'s taut branch).
--   * The W2b done-when (next analysis session): closed normal codes
--     of type `U` split as `pw? ∨ stkC?` (code canonicity), hence
--     closed paths at decoded types are `hrefl`s or lambdas, and
--     closed `tr`s always step.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeCanon where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; pair; fst; snd
        ; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap; ⌜Id⌝; idrefl; jsub
        ; ⌜Hom⌝-cong₃
        ; Ren; extR; renTm; Sub; extS; subTm; renTm-renTm )
open import poc.OCP0009.NbEPDirDBVar using ( 𝔹; true; false )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶_; _⟶*_; done; step
        ; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ; ξ-pairʳ
        ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ
        ; ξ-hreflᶜ; ξ-hreflᵃ; tr-J-base; tr-J-Σ; tr-taut
        ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; _⟶ᵀ_; El-⌜Π⌝; El-⌜Hom⌝; Hom-Π; ξ-Homᵀ )
open import poc.OCP0009.NbEPDirDBSR using ( wk-sub )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶-ren; ⟶*-⌜Hom⌝ᶜ )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-Homᵀ )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- 1. THE CLASSIFIERS — `Pw`/`StkC` as total Boolean functions on the
--    real syntax, plus the pointwise-body/domain FUNCTIONS.
------------------------------------------------------------------------

-- pw-able codes: decode to Π-unfoldable types (⌜Hom⌝-spines over ⌜Π⌝).
pw? : RTm Γ → 𝔹
pw? (⌜Π⌝ γ δ)     = true
pw? (⌜Hom⌝ C a b) = pw? C
pw? _             = false

-- permanently stable codes: J-able, and NEVER ⌜Π⌝-able — not even
-- under substitution (constructor-headed spines only; neutrals are
-- deliberately OUT, since σ could send their head variable to a ⌜Π⌝).
stkC? : RTm Γ → 𝔹
stkC? ⌜base⌝        = true
stkC? (⌜Σ⌝ c d)     = true
stkC? (⌜Hom⌝ C a b) = stkC? C
stkC? _             = false

-- the pointwise DOMAIN code (typing only — no rule RHS mentions it).
pwDom : RTm Γ → RTm Γ
pwDom (⌜Π⌝ γ δ)     = γ
pwDom (⌜Hom⌝ C a b) = pwDom C
pwDom t             = t

-- ★ the pointwise BODY code — the spine recursion, as a function.
pwBody : RTm Γ → RTm (Γ ∙)
pwBody (⌜Π⌝ γ δ)     = δ
pwBody (⌜Hom⌝ C a b) = ⌜Hom⌝ (pwBody C)
                             (app (renTm vs a) (var vz))
                             (app (renTm vs b) (var vz))
pwBody t             = renTm vs t

-- the two keys are DISJOINT — what makes hrefl-pw and tr-J-Hom
-- overlap-free on the same path.
stk⊥pw : (C : RTm Γ) → stkC? C ≡ true → pw? C ≡ false
stk⊥pw (var x) ()
stk⊥pw (lam t) ()
stk⊥pw (app t u) ()
stk⊥pw (pair a b) ()
stk⊥pw (fst t) ()
stk⊥pw (snd t) ()
stk⊥pw ⌜base⌝ h = refl
stk⊥pw (⌜Π⌝ γ δ) ()
stk⊥pw (⌜Σ⌝ c d) h = refl
stk⊥pw (⌜Hom⌝ C a b) h = stk⊥pw C h
stk⊥pw (hrefl c t) ()
stk⊥pw (tr d p e) ()

-- a depth-2 spine, concretely: the classifier and the body compute.
demo-pw-spine : (a b : RTm Γ) →
                pw? (⌜Hom⌝ (⌜Π⌝ ⌜base⌝ ⌜base⌝) a b) ≡ true
demo-pw-spine a b = refl

demo-pwBody-spine : (a b : RTm Γ) →
                    pwBody (⌜Hom⌝ (⌜Π⌝ ⌜base⌝ ⌜base⌝) a b)
                    ≡ ⌜Hom⌝ ⌜base⌝ (app (renTm vs a) (var vz))
                                   (app (renTm vs b) (var vz))
demo-pwBody-spine a b = refl

------------------------------------------------------------------------
-- 2. STABILITY — the full bill a Boolean-keyed rule owes the
--    metatheory, paid here on the real syntax:
--      * closure under reduction (⟶-preservation of the key, and the
--        BODY function mapping steps to steps: the ξ-critical pairs);
--      * renaming EQUALITIES (Takahashi's ⟶-ren; Fund's anti-renaming);
--      * substitution preservation (⟶-sub).
------------------------------------------------------------------------

pw?-red : {C C' : RTm Γ} → C ⟶ C' → pw? C ≡ true → pw? C' ≡ true
pw?-red (β _ _) ()
pw?-red (βfst _ _) ()
pw?-red (βsnd _ _) ()
pw?-red (ξ-lam _) ()
pw?-red (ξ-appˡ _) ()
pw?-red (ξ-appʳ _) ()
pw?-red (ξ-pairˡ _) ()
pw?-red (ξ-pairʳ _) ()
pw?-red (ξ-fst _) ()
pw?-red (ξ-snd _) ()
pw?-red (ξ-⌜Π⌝ˡ r) h = refl
pw?-red (ξ-⌜Π⌝ʳ r) h = refl
pw?-red (ξ-⌜Σ⌝ˡ _) ()
pw?-red (ξ-⌜Σ⌝ʳ _) ()
pw?-red (ξ-⌜Hom⌝ᶜ r) h = pw?-red r h
pw?-red (ξ-⌜Hom⌝ˡ r) h = h
pw?-red (ξ-⌜Hom⌝ʳ r) h = h
pw?-red (ξ-hreflᶜ _) ()
pw?-red (ξ-hreflᵃ _) ()
pw?-red (tr-J-base _ _ _ _ _) ()
pw?-red (tr-J-Σ _ _ _ _ _ _ _) ()
pw?-red (tr-taut _ _) ()
pw?-red (ξ-trᵈ _) ()
pw?-red (ξ-trᵖ _) ()
pw?-red (ξ-trᵉ _) ()

stkC?-red : {C C' : RTm Γ} → C ⟶ C' → stkC? C ≡ true → stkC? C' ≡ true
stkC?-red (β _ _) ()
stkC?-red (βfst _ _) ()
stkC?-red (βsnd _ _) ()
stkC?-red (ξ-lam _) ()
stkC?-red (ξ-appˡ _) ()
stkC?-red (ξ-appʳ _) ()
stkC?-red (ξ-pairˡ _) ()
stkC?-red (ξ-pairʳ _) ()
stkC?-red (ξ-fst _) ()
stkC?-red (ξ-snd _) ()
stkC?-red (ξ-⌜Π⌝ˡ _) ()
stkC?-red (ξ-⌜Π⌝ʳ _) ()
stkC?-red (ξ-⌜Σ⌝ˡ r) h = refl
stkC?-red (ξ-⌜Σ⌝ʳ r) h = refl
stkC?-red (ξ-⌜Hom⌝ᶜ r) h = stkC?-red r h
stkC?-red (ξ-⌜Hom⌝ˡ r) h = h
stkC?-red (ξ-⌜Hom⌝ʳ r) h = h
stkC?-red (ξ-hreflᶜ _) ()
stkC?-red (ξ-hreflᵃ _) ()
stkC?-red (tr-J-base _ _ _ _ _) ()
stkC?-red (tr-J-Σ _ _ _ _ _ _ _) ()
stkC?-red (tr-taut _ _) ()
stkC?-red (ξ-trᵈ _) ()
stkC?-red (ξ-trᵖ _) ()
stkC?-red (ξ-trᵉ _) ()

-- ★ the body function maps a step of the code to steps of the body —
-- the content of the hrefl-pw/ξ-hreflᶜ and tr-pw/ξ-trᵈ joins.  (Steps
-- inside a dropped component — ⌜Π⌝'s domain — join at `done`; steps
-- inside kept endpoints go through their renamed images, `⟶-ren`.)
pwBody-red : {C C' : RTm Γ} → C ⟶ C' → pw? C ≡ true →
             pwBody C ⟶* pwBody C'
pwBody-red (β _ _) ()
pwBody-red (βfst _ _) ()
pwBody-red (βsnd _ _) ()
pwBody-red (ξ-lam _) ()
pwBody-red (ξ-appˡ _) ()
pwBody-red (ξ-appʳ _) ()
pwBody-red (ξ-pairˡ _) ()
pwBody-red (ξ-pairʳ _) ()
pwBody-red (ξ-fst _) ()
pwBody-red (ξ-snd _) ()
pwBody-red (ξ-⌜Π⌝ˡ r) h = done
pwBody-red (ξ-⌜Π⌝ʳ r) h = step r done
pwBody-red (ξ-⌜Σ⌝ˡ _) ()
pwBody-red (ξ-⌜Σ⌝ʳ _) ()
pwBody-red (ξ-⌜Hom⌝ᶜ r) h = ⟶*-⌜Hom⌝ᶜ (pwBody-red r h)
pwBody-red (ξ-⌜Hom⌝ˡ r) h = step (ξ-⌜Hom⌝ˡ (ξ-appˡ (⟶-ren vs r))) done
pwBody-red (ξ-⌜Hom⌝ʳ r) h = step (ξ-⌜Hom⌝ʳ (ξ-appˡ (⟶-ren vs r))) done
pwBody-red (ξ-hreflᶜ _) ()
pwBody-red (ξ-hreflᵃ _) ()
pwBody-red (tr-J-base _ _ _ _ _) ()
pwBody-red (tr-J-Σ _ _ _ _ _ _ _) ()
pwBody-red (tr-taut _ _) ()
pwBody-red (ξ-trᵈ _) ()
pwBody-red (ξ-trᵖ _) ()
pwBody-red (ξ-trᵉ _) ()

pwDom-red : {C C' : RTm Γ} → C ⟶ C' → pw? C ≡ true →
            pwDom C ⟶* pwDom C'
pwDom-red (β _ _) ()
pwDom-red (βfst _ _) ()
pwDom-red (βsnd _ _) ()
pwDom-red (ξ-lam _) ()
pwDom-red (ξ-appˡ _) ()
pwDom-red (ξ-appʳ _) ()
pwDom-red (ξ-pairˡ _) ()
pwDom-red (ξ-pairʳ _) ()
pwDom-red (ξ-fst _) ()
pwDom-red (ξ-snd _) ()
pwDom-red (ξ-⌜Π⌝ˡ r) h = step r done
pwDom-red (ξ-⌜Π⌝ʳ r) h = done
pwDom-red (ξ-⌜Σ⌝ˡ _) ()
pwDom-red (ξ-⌜Σ⌝ʳ _) ()
pwDom-red (ξ-⌜Hom⌝ᶜ r) h = pwDom-red r h
pwDom-red (ξ-⌜Hom⌝ˡ r) h = done
pwDom-red (ξ-⌜Hom⌝ʳ r) h = done
pwDom-red (ξ-hreflᶜ _) ()
pwDom-red (ξ-hreflᵃ _) ()
pwDom-red (tr-J-base _ _ _ _ _) ()
pwDom-red (tr-J-Σ _ _ _ _ _ _ _) ()
pwDom-red (tr-taut _ _) ()
pwDom-red (ξ-trᵈ _) ()
pwDom-red (ξ-trᵖ _) ()
pwDom-red (ξ-trᵉ _) ()

-- renaming EQUALITIES (the anti-renaming currency).
pw?-ren : (ρ : Ren Γ Δ) (C : RTm Γ) → pw? (renTm ρ C) ≡ pw? C
pw?-ren ρ (var x)       = refl
pw?-ren ρ (lam t)       = refl
pw?-ren ρ (app t u)     = refl
pw?-ren ρ (pair a b)    = refl
pw?-ren ρ (fst t)       = refl
pw?-ren ρ (snd t)       = refl
pw?-ren ρ ⌜base⌝        = refl
pw?-ren ρ (⌜Π⌝ γ δ)     = refl
pw?-ren ρ (⌜Σ⌝ c d)     = refl
pw?-ren ρ (⌜Hom⌝ C a b) = pw?-ren ρ C
pw?-ren ρ (hrefl c t)   = refl
pw?-ren ρ (tr d p e)    = refl
pw?-ren ρ (ap c b p)    = refl
pw?-ren ρ (⌜Id⌝ c a b)  = refl
pw?-ren ρ (idrefl c t)  = refl
pw?-ren ρ (jsub d p e)  = refl

stkC?-ren : (ρ : Ren Γ Δ) (C : RTm Γ) → stkC? (renTm ρ C) ≡ stkC? C
stkC?-ren ρ (var x)       = refl
stkC?-ren ρ (lam t)       = refl
stkC?-ren ρ (app t u)     = refl
stkC?-ren ρ (pair a b)    = refl
stkC?-ren ρ (fst t)       = refl
stkC?-ren ρ (snd t)       = refl
stkC?-ren ρ ⌜base⌝        = refl
stkC?-ren ρ (⌜Π⌝ γ δ)     = refl
stkC?-ren ρ (⌜Σ⌝ c d)     = refl
stkC?-ren ρ (⌜Hom⌝ C a b) = stkC?-ren ρ C
stkC?-ren ρ (hrefl c t)   = refl
stkC?-ren ρ (tr d p e)    = refl
stkC?-ren ρ (ap c b p)    = refl
stkC?-ren ρ (⌜Id⌝ c a b)  = refl
stkC?-ren ρ (idrefl c t)  = refl
stkC?-ren ρ (jsub d p e)  = refl

-- weakening commutes with a renaming (local copy of Subj's `wk-ren` —
-- both composites are definitionally `x ↦ vs (ρ x)`).
wkren : (ρ : Ren Γ Δ) (t : RTm Γ) →
        renTm (extR ρ) (renTm vs t) ≡ renTm vs (renTm ρ t)
wkren ρ t = trans (renTm-renTm t) (sym (renTm-renTm t))

pwBody-ren : (ρ : Ren Γ Δ) (C : RTm Γ) → pw? C ≡ true →
             pwBody (renTm ρ C) ≡ renTm (extR ρ) (pwBody C)
pwBody-ren ρ (var x) ()
pwBody-ren ρ (lam t) ()
pwBody-ren ρ (app t u) ()
pwBody-ren ρ (pair a b) ()
pwBody-ren ρ (fst t) ()
pwBody-ren ρ (snd t) ()
pwBody-ren ρ ⌜base⌝ ()
pwBody-ren ρ (⌜Π⌝ γ δ) h = refl
pwBody-ren ρ (⌜Σ⌝ c d) ()
pwBody-ren ρ (⌜Hom⌝ C a b) h =
  ⌜Hom⌝-cong₃ (pwBody-ren ρ C h)
              (cong (λ z → app z (var vz)) (sym (wkren ρ a)))
              (cong (λ z → app z (var vz)) (sym (wkren ρ b)))
pwBody-ren ρ (hrefl c t) ()
pwBody-ren ρ (tr d p e) ()

-- substitution PRESERVES the keys (only this direction exists — a
-- substitution can CREATE pw-ability at a variable head, which is
-- exactly why `stkC?` excludes neutrals) and commutes with the body.
pw?-sub : (σ : Sub Γ Δ) (C : RTm Γ) → pw? C ≡ true →
          pw? (subTm σ C) ≡ true
pw?-sub σ (var x) ()
pw?-sub σ (lam t) ()
pw?-sub σ (app t u) ()
pw?-sub σ (pair a b) ()
pw?-sub σ (fst t) ()
pw?-sub σ (snd t) ()
pw?-sub σ ⌜base⌝ ()
pw?-sub σ (⌜Π⌝ γ δ) h = refl
pw?-sub σ (⌜Σ⌝ c d) ()
pw?-sub σ (⌜Hom⌝ C a b) h = pw?-sub σ C h
pw?-sub σ (hrefl c t) ()
pw?-sub σ (tr d p e) ()

stkC?-sub : (σ : Sub Γ Δ) (C : RTm Γ) → stkC? C ≡ true →
            stkC? (subTm σ C) ≡ true
stkC?-sub σ (var x) ()
stkC?-sub σ (lam t) ()
stkC?-sub σ (app t u) ()
stkC?-sub σ (pair a b) ()
stkC?-sub σ (fst t) ()
stkC?-sub σ (snd t) ()
stkC?-sub σ ⌜base⌝ h = refl
stkC?-sub σ (⌜Π⌝ γ δ) ()
stkC?-sub σ (⌜Σ⌝ c d) h = refl
stkC?-sub σ (⌜Hom⌝ C a b) h = stkC?-sub σ C h
stkC?-sub σ (hrefl c t) ()
stkC?-sub σ (tr d p e) ()

pwBody-sub : (σ : Sub Γ Δ) (C : RTm Γ) → pw? C ≡ true →
             pwBody (subTm σ C) ≡ subTm (extS σ) (pwBody C)
pwBody-sub σ (var x) ()
pwBody-sub σ (lam t) ()
pwBody-sub σ (app t u) ()
pwBody-sub σ (pair a b) ()
pwBody-sub σ (fst t) ()
pwBody-sub σ (snd t) ()
pwBody-sub σ ⌜base⌝ ()
pwBody-sub σ (⌜Π⌝ γ δ) h = refl
pwBody-sub σ (⌜Σ⌝ c d) ()
pwBody-sub σ (⌜Hom⌝ C a b) h =
  ⌜Hom⌝-cong₃ (pwBody-sub σ C h)
              (cong (λ z → app z (var vz)) (sym (wk-sub σ a)))
              (cong (λ z → app z (var vz)) (sym (wk-sub σ b)))
pwBody-sub σ (hrefl c t) ()
pwBody-sub σ (tr d p e) ()

------------------------------------------------------------------------
-- 3. ★★ THE COHERENCE CENTERPIECE — `pw-Hom-decode`: a Hom over a
--    pw-able code's decoding reduces to a Π whose body is ALSO reached
--    from the pointwise-body code's decoding.  (A join, not a straight
--    line: on deeper spines the left side unfolds one `El-⌜Hom⌝` step
--    further than the literal `El (pwBody C)`.)  Every new rule's
--    subject-reduction case converts through this lemma.
------------------------------------------------------------------------

pw-Hom-decode :
  (C : RTm Γ) → pw? C ≡ true → (x y : RTm Γ) →
  Σ (RTy (Γ ∙)) (λ Body →
    (Hom (El C) x y ⟶ᵀ* Π (El (pwDom C)) Body)
    × (Hom (El (pwBody C)) (app (renTm vs x) (var vz))
                           (app (renTm vs y) (var vz)) ⟶ᵀ* Body))
pw-Hom-decode (var v) () x y
pw-Hom-decode (lam t) () x y
pw-Hom-decode (app t u) () x y
pw-Hom-decode (pair a b) () x y
pw-Hom-decode (fst t) () x y
pw-Hom-decode (snd t) () x y
pw-Hom-decode ⌜base⌝ () x y
pw-Hom-decode (⌜Π⌝ γ δ) h x y =
  ( Hom (El δ) (app (renTm vs x) (var vz)) (app (renTm vs y) (var vz))
  , ( stepᵀ (ξ-Homᵀ (El-⌜Π⌝ γ δ))
      (stepᵀ (Hom-Π (El γ) (El δ) x y) doneᵀ)
    , doneᵀ ) )
pw-Hom-decode (⌜Σ⌝ c d) () x y
pw-Hom-decode (⌜Hom⌝ C a b) h x y with pw-Hom-decode C h a b
... | Body' , (c₁ , c₂) =
  ( Hom Body' (app (renTm vs x) (var vz)) (app (renTm vs y) (var vz))
  , ( stepᵀ (ξ-Homᵀ (El-⌜Hom⌝ C a b))
      (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ c₁)
        (stepᵀ (Hom-Π (El (pwDom C)) Body' x y) doneᵀ))
    , stepᵀ (ξ-Homᵀ (El-⌜Hom⌝ (pwBody C)
                              (app (renTm vs a) (var vz))
                              (app (renTm vs b) (var vz))))
            (⟶ᵀ*-Homᵀ c₂) ) )
pw-Hom-decode (hrefl c t) () x y
pw-Hom-decode (tr d p e) () x y

------------------------------------------------------------------------
-- 4. THE RULE RIGHT-HAND SIDES, import-ready — so the landing session
--    adds constructors whose RHSs are these definitions verbatim.
------------------------------------------------------------------------

-- (Γ, end, Πb) → (Γ, x, end′): the Π-binder becomes x, the old
-- endpoint goes to junk (typed-dead: the motive's components are
-- vz-free by `⊢tr`'s premises).
pwShift : Ren ((Γ ∙) ∙) ((Γ ∙) ∙)
pwShift vz     = vs vz
pwShift (vs y) = vs y

hreflPwRHS : (C s : RTm Γ) → RTm Γ
hreflPwRHS C s = lam (hrefl (pwBody C) (app (renTm vs s) (var vz)))

trPwRHS : (c a : RTm (Γ ∙)) (f : RTm (Γ ∙)) (e : RTm Γ) → RTm Γ
trPwRHS c a f e =
  lam (tr (⌜Hom⌝ (renTm pwShift (pwBody c))
                 (app (renTm vs a) (var (vs vz)))
                 (var vz))
          f
          (app (renTm vs e) (var vz)))

-- hrefl-Π is literally the ⌜Π⌝ instance of the one pw rule:
demo-hreflΠ : (γ : RTm Γ) (δ : RTm (Γ ∙)) (f : RTm Γ) →
              hreflPwRHS (⌜Π⌝ γ δ) f
              ≡ lam (hrefl δ (app (renTm vs f) (var vz)))
demo-hreflΠ γ δ f = refl
