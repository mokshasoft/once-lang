------------------------------------------------------------------------
-- OCP-0009 · W1c — toward `fund`: the semantic typing rules that do NOT need
--                  head expansion, and a scheduling result about the Kripke
--                  action.
--
-- Continues `SpikeSNW` (W1b: `irrel`/`fwd*`/`conv-⊩`).  Two things here.
--
-- ★ 1. THE KRIPKE ACTION IS NOT NEEDED.  The plan (and `SpikeSNU` §8a) had it
--   as W1c's first item, "mechanical but bulky", on the grounds that `fund`'s
--   λ-case needs `⊩`/`⊩∋` stable under renaming.  It does not, and the reason
--   is worth recording because it also says WHY:
--
--     `fund` is stated over a SUBSTITUTION `σ : Sub Γ Δ`, not over a context
--     extension.  Its λ-case, at `Γ ⊢ lam s ∷ Π A B` from `(Γ ▹ A) ⊢ s ∷ B`,
--     extends σ to `σ , u : Sub (Γ ∙) Δ` for the argument `u : RTm Δ`.  The
--     TARGET context Δ is unchanged, so nothing is ever weakened.
--
--   The one place a Kripke action IS classically forced is CR1 at `Π`, which
--   otherwise has to apply `t` to a FRESH variable — and `SpikeSNU` already
--   removed that by carrying `SN t` as a conjunct in the `Π` clause.  So the
--   design decision taken there for a local reason turns out to buy the whole
--   Kripke layer.  Recorded so W1c's item 1 can be struck rather than built.
--
--   (Renaming would come back if the LR were ever needed at η, or if `⊩Π`'s
--   domain quantified over future contexts for some other reason.  It is not
--   needed for the SN⁺ theorem as scoped.)
--
-- ★ 2. WHAT IS ACTUALLY LEFT: HEAD EXPANSION, and it is the classic hard
--   lemma, not a bookkeeping one.  Delivered below, machine-checked:
--
--     `sn-exp`   — SN closed under head expansion AT THE TOP REDEX:
--                  `SN u → SN s[u] → SN (app (lam s) u)`.  The classic `abs`
--                  lemma (dHoTT-35's shape), by lexicographic induction.
--     `sem-app`  — the semantic ⊢app rule, via the `Π` clause + `irrel`.
--     `sem-var`/`sem-conv` — recorded as immediate from `SpikeSNW`.
--
--   The gap, stated exactly: the LR-level expansion `exp` needs, at its `Π`
--   case, `SN (app t v)` where the redex sits UNDER an application — i.e.
--   `sn-exp` generalized to a SPINE, `SN u → SN (s[u] · sp) → SN (app (lam s) u · sp)`.
--   `sn-exp` above is exactly the `sp = ε` case.  See §5 for why the spine
--   case is not a routine generalization and which two routes close it.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeSNX where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; Σ; _,_; _×_ )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El
        ; RTm; var; lam; app; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; Sub; subTy; subTm; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( single
        ; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ
        ; ξ-pairˡ; ξ-pairʳ; ξ-fst; ξ-snd
        ; _⟶*_; done; step
        ; _⟶ᵀ_; ξ-El; ξ-Πˡ; ξ-Πʳ
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ )
open import poc.OCP0009.NbEPDirDBSR using ( ⟶-sub )
open import poc.OCP0009.NbEPDirDBConf using ( subTm-monoˢ; single-mono )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; red→≅ᵀ )
open import poc.OCP0009.SpikeSNW
  using ( SN; sn; sn-red; sn-var; Ne; ne-var; ne-app; ne-red
        ; ⊩_; ⊩base; ⊩U; ⊩ne; ⊩Π; _⊩∋_
        ; irrel; fwd*; bwd*; conv-⊩
        ; CR1; CR2; CR3; ⊩var
        ; projl; projr )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- 1. SN is closed under multi-step reduction.
------------------------------------------------------------------------

sn-red* : {t u : RTm Γ} → SN t → t ⟶* u → SN u
sn-red* s done       = s
sn-red* s (step r p) = sn-red* (sn-red s r) p

------------------------------------------------------------------------
-- ★ 2. HEAD EXPANSION AT THE TOP REDEX — the classic `abs` lemma.
--
-- `SN u → SN s[u] → SN (app (lam s) u)`.  Note the hypothesis `SN u` is not
-- decoration: without it the statement is FALSE (`(λx. y) Ω ⟶ y` with `y` SN
-- and `(λx. y) Ω` not).  The argument must be SN because β can DISCARD it.
--
-- Lexicographic on `(SN u, SN s[u])`:
--   * `β`      — the hypothesis, verbatim;
--   * body step `s ⟶ s'` — `s[u] ⟶ s'[u]` by `⟶-sub`, so the SECOND measure
--     drops structurally while the first is untouched;
--   * arg step `u ⟶ u'` — the FIRST drops structurally, and `s[u] ⟶* s[u']`
--     comes from `subTm-monoˢ`/`single-mono` (multi-step, possibly zero — the
--     variable may not occur, which is exactly why this component cannot be
--     the one that decreases).
------------------------------------------------------------------------

sn-exp      : {s : RTm (Γ ∙)} {u : RTm Γ} →
              SN u → SN (subTm (single u) s) → SN (app (lam s) u)
sn-exp-step : {s : RTm (Γ ∙)} {u w : RTm Γ} →
              SN u → SN (subTm (single u) s) → app (lam s) u ⟶ w → SN w

sn-exp snu snsu = sn (sn-exp-step snu snsu)

sn-exp-step snu      snsu     (β s u)              = snsu
sn-exp-step snu      (sn hs)  (ξ-appˡ (ξ-lam r))   = sn-exp snu (hs (⟶-sub (single _) r))
sn-exp-step {s = s} (sn hu) snsu (ξ-appʳ r)        =
  sn-exp (hu r) (sn-red* snsu (subTm-monoˢ (single-mono (step r done)) s))

------------------------------------------------------------------------
-- 3. The semantic typing rules that need no expansion.
--
-- `fund`'s cases split cleanly: `⊢var`, `⊢app` and `⊢conv` are discharged by
-- what `SpikeSNW` already proved plus §2; only `⊢lam` needs the spine-general
-- expansion of §5.  Stating them separately isolates that.
------------------------------------------------------------------------

-- ⊢var — immediate from CR3 (`SpikeSNW.⊩var`), recorded here for completeness.
sem-var : {A : RTy Γ} (R : ⊩ A) (x : Var Γ) → R ⊩∋ var x
sem-var = ⊩var

-- ⊢conv — immediate from `SpikeSNW`: transport the semantic type along the
-- conversion, then move the member across by irrelevance.
sem-conv : {A B : RTy Γ} (c : A ≅ᵀ B) (R : ⊩ A) (S : ⊩ B) {t : RTm Γ} →
           R ⊩∋ t → S ⊩∋ t
sem-conv c R S {t} h = projl (irrel c R S) t h

-- ★ ⊢app — eliminate a `Π`.  The stored codomain family lands at
-- `subTy (single u) G` for the `G` the semantic type reduces to, while the
-- derivation wants an arbitrary `S` at that type; `irrel` at `crflᵀ` bridges
-- the two derivations of the SAME type.
sem-app : {A : RTy Γ} {F : RTy Γ} {G : RTy (Γ ∙)}
          (p : A ⟶ᵀ* Π F G)
          (⊩F : ⊩ F)
          (⊩G : (u : RTm Γ) → ⊩F ⊩∋ u → ⊩ (subTy (single u) G))
          {t u : RTm Γ} →
          (⊩Π p ⊩F ⊩G) ⊩∋ t → (r : ⊩F ⊩∋ u) →
          (S : ⊩ (subTy (single u) G)) → S ⊩∋ app t u
sem-app p ⊩F ⊩G {t} {u} h r S =
  projl (irrel crflᵀ (⊩G u r) S) (app t u) (projr h u r)

------------------------------------------------------------------------
-- 4. Head expansion at the LR level, for the NON-`Π` semantic types.
--
-- At `base`/`U`/`El n` membership IS `SN`, so §2 discharges expansion outright.
-- These are the cases `fund`'s λ-rule needs when the codomain is not itself a
-- function type — i.e. the whole of the first-order fragment.
------------------------------------------------------------------------

exp-base : {A : RTy Γ} (p : A ⟶ᵀ* base) {s : RTm (Γ ∙)} {u : RTm Γ} →
           SN u → (⊩base p) ⊩∋ subTm (single u) s → (⊩base p) ⊩∋ app (lam s) u
exp-base p snu h = sn-exp snu h

exp-U : {A : RTy Γ} (p : A ⟶ᵀ* U) {s : RTm (Γ ∙)} {u : RTm Γ} →
        SN u → (⊩U p) ⊩∋ subTm (single u) s → (⊩U p) ⊩∋ app (lam s) u
exp-U p snu h = sn-exp snu h

exp-ne : {A : RTy Γ} {n : RTm Γ} (p : A ⟶ᵀ* El n) (nn : Ne n)
         {s : RTm (Γ ∙)} {u : RTm Γ} →
         SN u → (⊩ne p nn) ⊩∋ subTm (single u) s → (⊩ne p nn) ⊩∋ app (lam s) u
exp-ne p nn snu h = sn-exp snu h

------------------------------------------------------------------------
-- ★ 5. THE REMAINING GAP, stated exactly.
--
-- The LR-level expansion at a `Π` semantic type is
--
--     exp : (R : ⊩ A) → SN u → R ⊩∋ s[u] → R ⊩∋ app (lam s) u
--
-- and its `Π` case must produce, for every argument `v`,
--
--     ⊩G v r ⊩∋ app (app (lam s) u) v     from     ⊩G v r ⊩∋ app (s[u]) v.
--
-- The redex has moved UNDER an application.  Recursing on `⊩G v r` is fine —
-- it is structurally smaller — but the recursive call needs `SN (app t v)`
-- with `t = app (lam s) u`, and §2 only gives SN at the TOP redex.  So what is
-- required is `sn-exp` generalized to a spine:
--
--     sn-exp· : SN u → SN (s[u] · sp) → SN (app (lam s) u · sp)
--
-- of which §2's `sn-exp` is precisely the `sp = ε` case.
--
-- ⚠ WHY THE SPINE CASE IS NOT ROUTINE.  Both obvious routes fail for the same
-- reason, and it is worth writing down so neither is re-attempted:
--
--   (i) INDUCT ON THE SPINE.  To case-split a reduction of `app (lam s) u · sp`
--       Agda needs `sp` concrete, but `_·_` is a function, so with `sp` a
--       variable the term is stuck and the `β` case can be neither taken nor
--       refuted.  Making `_·_` cons-shaped (`t · (v ∷ sp) = app t v · sp`)
--       relocates the problem, it does not remove it.
--
--   (ii) PEEL THE APPLICATIONS INTO AN INDUCTIVE HEAD REDUCTION `_⟶ₕ_`
--       (`hβ`/`happ`).  This DOES refute the bad `β` case — `lam _ ⟶ₕ _` has no
--       constructor — but the `happ` case then needs `SN (app t₁ u₁)` from
--       `SN (app t₁' u₁)`, and its `ξ-appˡ` sub-case leaves `t₁ ⟶ t₂` with `t₂`
--       unrelated to the head reduction.  Peeling back into a spine to fix that
--       makes the spine GROW while the `⟶ₕ` derivation shrinks, and the reverse
--       on the other case — no lexicographic order covers both.
--
-- ⇒ The two candidate routes:
--
--   (a) SPINES WITH AN EXPLICIT INVERSION LEMMA — a datatype enumerating the
--       four ways `app (lam s) u · sp` can step (head β / in `s` / in `u` / in a
--       spine element), proven by induction on `sp`.  Then `sn-exp·` would be
--       lexicographic on `(SN u, SN (s[u] · sp))` exactly as §2 is.
--
--       ✗ **TRIED, AND IT DOES NOT WORK.**  The inversion cannot be written at
--       all — not "is bulky", cannot be written.  Writing it out and asking
--       Agda for the `sp ▸ v` case gives:
--
--           SplitError.UnificationStuck
--           I'm not sure if there should be a case for the constructor β …
--             app (lam t) u ≟ app (lam s) u₁ · (sp ▸ x)
--
--       and this is not incidental.  `_·_` is a FUNCTION, so `app (lam s) u · sp`
--       with `sp` a variable is a stuck term; a stuck term can never be unified
--       against a constructor pattern, so the `β` case can be neither taken nor
--       refuted.  Restructuring the inversion datatype does not help, because
--       its own proof needs the same split; nor does flipping `_·_` to cons form
--       (`t · (v ∷ sp) = app t v · sp`), which relocates the stuck application
--       without removing it.  The head redex has to stop being a stuck term.
--
--   (b) JOACHIMSKI–MATTHES INDUCTIVE SN — replace accessibility-`SN` with the
--       mutual inductive characterisation (`SN`/`SNe`/`SNRed`) in which head
--       expansion is a CONSTRUCTOR.  No inversion is ever needed, because
--       head-redex-hood is a datatype rather than a stuck function application —
--       which is precisely what (a) lacks.  The work moves to proving the
--       inductive presentation sound for accessibility-`SN`; that is the
--       direction actually needed, and the harder one.
--
-- ⇒ **RECOMMENDATION: (b).**  Revised from (a) on the evidence above.  (a) looked
-- cheaper because §2 already validates its lexicographic argument, and it is
-- worth being explicit that this was checked and refuted rather than merely
-- reconsidered: the induction is fine, it is the CASE ANALYSIS that is
-- impossible to state.  Secondary reason to prefer (b) anyway: the inductive
-- presentation also handles η-expansion, so it would survive a later η change
-- (not in scope — PLAN §1.2, and dHoTT-23 discharges η without reducibility).
------------------------------------------------------------------------
