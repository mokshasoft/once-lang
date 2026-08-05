------------------------------------------------------------------------
-- ⚠⚠ FROZEN AT STAGE B — THIS MODULE IS NOT EXPECTED TO COMPILE. ⚠⚠
--
-- This is a DESIGN RECORD, not a test.  Its conclusion is already
-- absorbed into the main tower; what it preserves is WHY that path was
-- taken.  It carries its own COPY of `PayT` and pattern-matches
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
-- OCP-0009 · W2b (G1f), spike — `SpikeUPay`: THE U-MEMBERSHIP PAYLOAD.
--
-- THE WALL (G1 landing, 2026-08-03, recorded in the handoff): the
-- membership of `hrefl c t` at a Π-interp needs, at each Π-layer, the
-- membership of `hrefl (pwBody c)[v] (app t v)` at the body interp —
-- in particular SN OF THE SUBSTITUTED BODY CODE.  Codes reached
-- through the environment (⊢var) or through β-transient forms have no
-- derivation to recurse on, and `⊩₁U`'s membership clause
-- (`SN c × ⊩₀ (El c)`) is information-theoretically too weak to
-- supply the data.  This is SpikeTrLR candidate (ii), forced.
--
-- ★★ THE DESIGN, settled and mechanized here:
--
--   PayT : (R : ⊩₀ A) (c : RTm Γ) → Set     (§1, THE spike risk)
--     * non-Π interps: ⊤ — the membership there is SN-only, and
--       SN (hrefl c t) is constructible from SN c + the interp's own
--       non-Π chains (the CSR/snHrefl machinery, billed separately);
--     * ⊩₀Π interps: for every argument (v, r), an EXISTENTIAL next
--       code c′ with (i) SN c′, (ii) an s-PARAMETRIC head-strategy
--       chain  app (hrefl c s) v  ⟶snr*  hrefl c′ (app s v)   — the
--       wire `exp`-transport rides — and (iii) PayT at the body
--       interp with c′: the payload IS the unfolding tree, one node
--       per semantic Π-layer, WELL-FOUNDED by the interp structure.
--
--   The enriched clause (the landing changes exactly this):
--     ⊩₁U p ⊩₁∋ c  =  SN c × Σ (⊩₀ (El c)) (λ R → PayT R c)
--
-- ★ FINDING 1 (mechanized, §1): `PayT` is definable by plain recursion
--   over the REAL `⊩₀` — no positivity issue (the stratification means
--   `⊩₀`/`_⊩₀∋_` are closed before the U-clause consumes them), no
--   sized types, no induction-recursion beyond what `_⊩₀∋_` already is.
--
-- ★ FINDING 2 (mechanized, §2): the ⌜Π⌝-FORMER CONSTRUCTION COMPOSES.
--   `pay-⌜Π⌝` builds the payload node for a literal ⌜Π⌝-code from
--   exactly the data `fund`'s ⊢⌜Π⌝ case possesses (the body code's SN,
--   interp, and payload at every (v,r) — i.e. `fund dδ` at extended
--   environments): the head chain is snr-app(snr-hrefl-pw) then snr-β,
--   and the endpoint computations are `wk-single` on the nose.
--
-- ★ FINDING 3 (structural, no proof needed): the payload rides INSIDE
--   the membership tuple, and the U-clause's membership mentions only
--   the MEMBER (never the ambient interp's indices) — so `irrel₁`'s
--   U-U transfer stays the IDENTITY, exactly as today.  The clause
--   change does NOT reopen the irrel machinery.  (`exp₁`'s U-clause
--   transports the payload by prepending the head step to every chain
--   — `payT-exp`'s shape, §3 — and `bwd₀` preserves the interp's
--   clause, so the payload's Π-nodes carry over unchanged.)
--
-- THE LANDING BILL (measured):
--   * LR: the U-clause + PayT (+ CSR from the handoff's discovery 1,
--     which the SN-side `snHrefl` construction consumes); exp₁'s
--     U-case gains the chain-prefix transport; CR3₁'s U-case: neutral
--     codes decode to ⊩₀ne — non-Π — payload ⊤, FREE.
--   * Fund: sem-⌜base⌝/⌜Σ⌝ payloads ⊤ (their decodes are non-Π);
--     sem-⌜Π⌝ via pay-⌜Π⌝ (+ a PayT-transport across ≅ᵀ-equal interps,
--     irrel₀-powered, for aligning `fund dδ`'s interp with ⊩G);
--     sem-⌜Hom⌝ via a homSem₀-mirroring recursion (payHomT — descends
--     the code spine with CSR, refutes neutral whnfs against the
--     Π-chains); ⊢var/⊢conv/closures: automatic (payload is cargo).
--   * fund's ⊢hrefl: READS the payload — the wall falls.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeUPay where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_; _×_; ⊤ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr
        ; Ren; renTm; Sub; subTm; subTy )
open import poc.OCP0009.NbEPDirDBVar using ( pw? )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶_; hrefl-pw; single )
open import poc.OCP0009.NbEPDirDBInj using ( _⟶ᵀ*_ )
open import poc.OCP0009.NbEPDirDBLR
  using ( SN; SNRed; snr-β; snr-app; snr-hrefl-pw
        ; ⊩₀_; ⊩₀base; ⊩₀ne; ⊩₀Π; ⊩₀Σ; ⊩₀Hom; ⊩₀Id; _⊩₀∋_
        ; wk-single; projl; projr )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- 0. the head-strategy star (local; the landing reuses LR's).
------------------------------------------------------------------------

infix 3 _⟶snr*_
data _⟶snr*_ {Γ} : RTm Γ → RTm Γ → Set where
  snr-done : {t : RTm Γ} → t ⟶snr* t
  snr-step : {t u v : RTm Γ} → SNRed t u → u ⟶snr* v → t ⟶snr* v

------------------------------------------------------------------------
-- 1. ★★ THE PAYLOAD — recursion over the interp; the unfolding tree.
------------------------------------------------------------------------

PayT : {A : RTy Γ} (R : ⊩₀ A) (c : RTm Γ) → Set
PayT (⊩₀base _)  c = ⊤
PayT (⊩₀ne _ _)  c = ⊤
PayT (⊩₀Σ _ _ _) c = ⊤
PayT (⊩₀Hom _ _) c = ⊤
PayT (⊩₀Id _)    c = ⊤
PayT {Γ = Γ} (⊩₀Π _ ⊩F ⊩G) c =
  (v : RTm Γ) (r : ⊩F ⊩₀∋ v) →
  Σ (RTm Γ) (λ c′ →
    SN c′
    × ( ((s : RTm Γ) →
          app (hrefl c s) v ⟶snr* hrefl c′ (app s v))
      × PayT (⊩G v r) c′ ))

------------------------------------------------------------------------
-- 2. ★ THE ⌜Π⌝-FORMER NODE — from exactly `fund dδ`-shaped data.
--    The chain: hrefl-pw at the literal ⌜Π⌝ (key definitional), then
--    β; both endpoint computations are `wk-single` on the nose.
------------------------------------------------------------------------

-- `hrefl (⌜Π⌝ γ δ) s` applied at `v` head-reduces to
-- `hrefl (δ[v]) (app s v)` — the s-parametric wire.
payΠ-chain : (γ : RTm Γ) (δ : RTm (Γ ∙)) (v : RTm Γ) → SN v →
             (s : RTm Γ) →
             app (hrefl (⌜Π⌝ γ δ) s) v ⟶snr*
             hrefl (subTm (single v) δ) (app s v)
payΠ-chain γ δ v snv s =
  snr-step (snr-app (snr-hrefl-pw refl))
    (snr-step (snr-β snv)
      (subst (λ z → hrefl (subTm (single v) δ) (app z v) ⟶snr*
                    hrefl (subTm (single v) δ) (app s v))
             (sym (wk-single s))
             snr-done))

pay-⌜Π⌝ :
  {γ : RTm Γ} {δ : RTm (Γ ∙)} {A F : RTy Γ} {G : RTy (Γ ∙)}
  (q : A ⟶ᵀ* Π F G) (⊩F : ⊩₀ F)
  (⊩G : (u : RTm Γ) → ⊩F ⊩₀∋ u → ⊩₀ (subTy (single u) G)) →
  -- what `fund dδ` at the (σ ,ₛ v)-extended environment delivers,
  -- already aligned with ⊩G (the PayT-transport is the landing's
  -- irrel₀-powered glue):
  ((v : RTm Γ) (r : ⊩F ⊩₀∋ v) →
     SN (subTm (single v) δ) × PayT (⊩G v r) (subTm (single v) δ)) →
  -- SN of the arguments comes with their memberships in the landing
  -- (CR1₀); here it is a hypothesis to keep the spike import-light:
  ((v : RTm Γ) (r : ⊩F ⊩₀∋ v) → SN v) →
  PayT (⊩₀Π q ⊩F ⊩G) (⌜Π⌝ γ δ)
pay-⌜Π⌝ {γ = γ} {δ = δ} q ⊩F ⊩G body sneach v r =
  ( subTm (single v) δ
  , ( projl (body v r)
    , ( payΠ-chain γ δ v (sneach v r)
      , projr (body v r) ) ) )
