------------------------------------------------------------------------
-- ⚠⚠ FROZEN AT STAGE B — THIS MODULE IS NOT EXPECTED TO COMPILE. ⚠⚠
--
-- This is a DESIGN RECORD, not a test.  Its conclusion is already
-- absorbed into the main tower; what it preserves is WHY that path was
-- taken.  It carries its own COPY of `homSem₀-mem-endpoints` and pattern-matches
-- exhaustively on `RTm`/`⊩₀`, so stage C's `⊩₀Unit`/`⊩₀Nat` broke it — in the WF-axis work,
-- not in anything since.
--
-- Do NOT "fix" it as part of a tower sweep: chasing every new
-- constructor through a dead copy costs maintenance and yields no
-- signal.  Re-derive it against the live modules if the design
-- question ever reopens.
--
-- ★ The counterexample: SpikeAp is the spike that DOES stay green,
--   because it imports Canon's real `codeCanon`/`pathCanon` instead of
--   copying them — which is exactly why it caught a genuine weakening
--   when `stkA?`/`stkC?` split.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- OCP-0009 · W2 eliminator, spike 4 — `SpikeTrLR`: HOW DOES `fund`
--                                     DISCHARGE `tr`?
--
-- The stage-1 consolidation reopened the `SpikeHomLR` gate at the
-- eliminator: an eliminator's semantic case needs its computation
-- reachable from the memberships in scope.  The handoff's guess was a
-- TRANSPORT CLOSURE inside the `Hom`-membership clause.  This spike
-- answers with a DIFFERENT — and mostly cheaper — design, mechanizes
-- its two load-bearing pieces, and isolates one genuine obstruction.
--
-- ★★ THE ANSWER: NOT a membership-clause change.  The Joachimski–
-- Matthes presentation extends PER-ELIMINATOR instead:
--
--   (1) the HEAD STRATEGY gains the eliminator's scrutinee positions —
--       `snr-hreflᶜ` (hrefl is an eliminator of its code), the two J
--       rules and taut as head redexes (discarded material carried as
--       `SN`, the `snr-β` pattern), and `snr-trᵖ` (the path is `tr`'s
--       scrutinee);
--   (2) the PERMANENTLY-STUCK `tr` configurations are NEUTRAL, keyed by
--       a reduction-closed shape family (`NeV`/`StableCd`/`PathStk`):
--       a path on which no root rule can EVER fire (var-rooted spines,
--       `hrefl` at reduction-stable non-J-able codes), and a lambda
--       path at a `⌜Hom⌝`-headed motive (taut needs the LITERAL
--       `var vz`; pointwise composition is deferred with the canonicity
--       package) — `sne-tr-stk`/`sne-tr-lam`;
--   (3) the strategy is DETERMINISTIC (`snr-det`), so `SN` and every
--       MEMBERSHIP move forward along it (`sn-whred`, `mem-whred₁`).
--
-- All of (1)–(3) are LANDED AND CHECKED in `NbEPDirDBLR` (with the
-- anti-renaming bill paid in `NbEPDirDBFund`) as of this spike.  With
-- them, `fund`'s `tr` case runs a path analysis by induction on the
-- path's `SN` derivation: head steps expand (`exp₁` ∘ `mem-whred₁`),
-- stuck shapes are `CR3`, and the J/taut redexes reduce to terms whose
-- memberships the premises supply.
--
-- ★ THE COMPOSITION MOTIVE (posc-Hom) CLOSES on this design.  Route,
-- fully mapped (next session's implementation, no design risk left):
--   * `⊢tr` gains ENDPOINT premises `Γ ⊢ t ∷ A`, `Γ ⊢ u ∷ A` (the
--     `⊢lam` option-A pattern — sr already never needed them, fund
--     does);
--   * the possible interps of the path's `Hom`-type are `⊩₁Hom`/`⊩₁Π`
--     only (`hom-shape` below: reducts of a `Hom` are `Hom`- or
--     `Π`-headed — refuting base/U/ne/Σ');
--   * the target interp `⊩₀ (El (⌜Hom⌝ c′[u] a′[u] u))` is built from
--     `⊢tr`'s premises: invert `dd` (`gen-⌜Hom⌝`), run the sub-codes'
--     IHs in the env extended at each endpoint (`⊩ˢ-ext` with `dt`/
--     `du`'s memberships), and assemble with `homSem₀`;
--   * the J-branches hand the payload's membership across the endpoint
--     switch with `homSem₀-mem-endpoints` (★ MECHANIZED BELOW): the
--     `PosC`-pinned motive is endpoint-blind in every component
--     (`subTm-occ`), so the source- and target-types differ ONLY in the
--     transported endpoint, and memberships at `homSem₀`-interps do not
--     depend on it — SN at the stuck leaves, pointwise through `Π`.
--
-- ⚠ THE OBSTRUCTION — the TAUTOLOGICAL motive (posc-var): `fund`'s
-- J-branches there need `t ≅ u` (the payload's type `El t` must convert
-- to the target `El u` when the path turns out to be an identity path),
-- and that conversion is TYPING-VISIBLE ONLY: the substituted instance
-- lives in a RAW target scope, `gen-hrefl` is unavailable, and no
-- membership in scope relates the two endpoints (measured against every
-- premise: `rA`/`rt`/`ru`/`rEt`/`rEu` and the Π-membership say nothing
-- about `t₁ ~ u₁`).  The configuration is TYPED-vacuous (a path at
-- `Hom U t u` cannot normalize to `hrefl` — `El c ≇ U`), but `fund`'s
-- induction is raw.  Candidate resolutions, for the next session to
-- pick: (i) a typed-environment (Kripke-style) `fund` — heavy; (ii) a
-- semantic U-coherence payload in the `⊩₁Π`-interp of unfolded
-- `Hom U`s — a clause change after all, but scoped to `Hom-U`;
-- (iii) keep taut STAGED (it is one `srᵗ`-checked rule with a computing
-- demo) until canonicity-package work makes the vacuity syntactic.
--
-- ★ RESOLVED (2026-08-02, stage 3) — by a FOURTH route none of the
-- candidates named: RE-KEY J ON THE MOTIVE.  J fires only at
-- `⌜Hom⌝`-headed motives; at a `var` motive a path can never be a typed
-- `hrefl` (`Hom U t u` unfolds toward `Π`, `Hom (El c) s s` toward a
-- stuck `Hom` — the shapes clash under confluence), so the un-keyed
-- rule was never typed-exercised, and keying it makes the taut
-- J-configurations PERMANENTLY STUCK (`trstk?`'s var-motive clause) —
-- the J-branches that needed `t ≅ u` simply ceased to exist.  Taut is
-- merged as `⊢trU` (ambient pinned `U`) with `sr` and `fund` in the
-- base judgment; the staged judgment is retired.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeTrLR where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; cong₂; subst; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; ⌜base⌝; ⌜Hom⌝; hrefl; tr; Hom-cong₃ 
        ; Unit; Nat; nzero; nsuc )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶ᵀ_; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; Hom-U; Hom-Π
        ; ξ-Πˡ; ξ-Πʳ 
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ )
open import poc.OCP0009.NbEPDirDBLR
  using ( ⊩₀_; ⊩₀base; ⊩₀ne; ⊩₀Π; ⊩₀Σ; ⊩₀Hom; ⊩₀Id; _⊩₀∋_
        ; homSem₀; wk-single; projl; projr )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- 1. ★ `hom-shape` — reducts of a `Hom` type are `Hom`- or `Π`-headed.
--    (What refutes the base/U/ne/Σ' interps of a path's type in
--    `fund`'s `tr` case.)
------------------------------------------------------------------------

data HomΠShape {Γ} : RTy Γ → Set where
  hsΠ : {F : RTy Γ} {G : RTy (Γ ∙)} → HomΠShape (Π F G)
  hsH : {H : RTy Γ} {a b : RTm Γ} → HomΠShape (Hom H a b)
  -- ★ WF stage B: the order rules add two reduct shapes (this spike
  -- keeps its own copy of the shape family; see NbEPDirDBSubj).
  hsUnit : HomΠShape (Unit {Γ})
  hsBase : HomΠShape (base {Γ})

Π-shape : {F : RTy Γ} {G : RTy (Γ ∙)} {C : RTy Γ} →
          Π F G ⟶ᵀ* C → HomΠShape C
Π-shape doneᵀ                = hsΠ
Π-shape (stepᵀ (ξ-Πˡ r) rest) = Π-shape rest
Π-shape (stepᵀ (ξ-Πʳ r) rest) = Π-shape rest

hom-shape : {A : RTy Γ} {t u : RTm Γ} {C : RTy Γ} →
            Hom A t u ⟶ᵀ* C → HomΠShape C
hom-shape doneᵀ                    = hsH
hom-shape (stepᵀ (ξ-Homᵀ r) rest) = hom-shape rest
hom-shape (stepᵀ (ξ-Homˡ r) rest) = hom-shape rest
hom-shape (stepᵀ (ξ-Homʳ r) rest) = hom-shape rest
hom-shape (stepᵀ (Hom-U c d) rest)    = Π-shape rest
hom-shape (stepᵀ (Hom-Π A B f g) rest) = Π-shape rest
hom-shape (stepᵀ (Hom-Nat-z n) doneᵀ)        = hsUnit
hom-shape (stepᵀ (Hom-Nat-z n) (stepᵀ () _))
hom-shape (stepᵀ (Hom-Nat-sz m) doneᵀ)       = hsBase
hom-shape (stepᵀ (Hom-Nat-sz m) (stepᵀ () _))
hom-shape (stepᵀ (Hom-Nat-ss m n) rest)      = hom-shape rest

------------------------------------------------------------------------
-- 2. ★★ `homSem₀-mem-endpoints` — memberships at a `homSem₀`-interp do
--    not depend on the ENDPOINTS (or their membership proofs): `SN` at
--    every stuck leaf, pointwise through the `Π` skeleton.  This is the
--    lemma that carries the payload across the J-branches' endpoint
--    switch at composition motives, where the `PosC`-pinned motive is
--    endpoint-blind in every other component.
------------------------------------------------------------------------

mem₀-cast : {A B : RTy Γ} (eq : A ≡ B) (R : ⊩₀ A) {t : RTm Γ} →
            R ⊩₀∋ t → (subst ⊩₀_ eq R) ⊩₀∋ t
mem₀-cast refl R h = h

mem₀-cast⁻ : {A B : RTy Γ} (eq : A ≡ B) (R : ⊩₀ A) {t : RTm Γ} →
             (subst ⊩₀_ eq R) ⊩₀∋ t → R ⊩₀∋ t
mem₀-cast⁻ refl R h = h

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
