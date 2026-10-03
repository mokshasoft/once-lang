-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.Coherence — THE BIDIRECTIONAL JUDGMENT IS COHERENT
-- (plan 0.103; A4 of plan 0.55, formerly the postulate `realize-invariant`).
--
-- Any two derivations of one judgment realize to terms with the same
-- meaning. The judgment overlaps — `t-sub` against the direct check rules,
-- `t-app` against the spine, `d-infer` against the domain-given rules, the
-- two compose-check routes — so this is a theorem, not a tautology.
--
-- Three layers, each its own module:
--   * `TypeCheck.RouteBuild`: every two derivations of one term have a route
--     (`TypeCheck.Route`), the case split over pairs (`ModeAgreement`'s);
--   * `CoherenceHet`: one lemma per route shape, from its premises' meaning
--     equalities to its own;
--   * here: the induction on the route, one clause per constructor.
-- The routes' two-way choices agree because a conversion commutes with the
-- formers and is unique (`CoherenceLaws`); that the types they relate are
-- related at all is `ModeSub`.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.Coherence (fmt : TargetNum) where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong-app)

open import Once.Type as T using (Type; _⇒[_]_)
open import Once.Type.Sub using (_<:_; sub-arr; sub-prod; sub-void; <:-refl; _⊑π_; ⊑-pure; ⊑π-refl)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Judgment
import Once.TypeCheck.ModeSub as MS
open import Once.TypeCheck.Route
open import Once.TypeCheck.RouteBuild using (route-cc)
import Once.Surface.Context as Surface
open import Once.Surface.Syntax using (coerce)
open import Once.Denotation.Realize using (realize; realize-infer; realize-d)
import Once.Denotation.SourceDenote as SD
open SD using (⟦_⟧ˢ)
open import Once.Adequacy.CoherenceLaws fmt
open import Once.Adequacy.CoherenceLawsWrap fmt
open import Once.Adequacy.CoherenceHet fmt

private
  RI = realize-infer
  RC = realize
  RD = realize-d

mutual
  coh-ii : ∀ {ctx e A A′ Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ A ⨾ Ψ} {d′ : ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′} → Rii d d′ → RI d ≅ RI d′
  coh-ii ii-int = ≅-refl
  coh-ii ii-float = ≅-refl
  coh-ii ii-unit = ≅-refl
  coh-ii ii-unit-var = ≅-refl
  coh-ii {ctx = ctx} (ii-resolved {n = n} {n′ = n′} {l = l} {l′ = l′} {c = c} {c′ = c′}) = resolved-h {ctx = ctx} n l c n′ l′ c′
  coh-ii {ctx = ctx} (ii-qualified {nm = nm} {al = al} {l = l} {l′ = l′} {c = c} {c′ = c′}) = qualified-h {ctx = ctx} {nm = nm} {al = al} l c l′ c′
  coh-ii {ctx = ctx} (ii-local {l = l} {l′ = l′}) = local-h {ctx = ctx} l l′
  coh-ii {ctx = ctx} (ii-import {g = g} {g′ = g′} {ln = ln} {ln′ = ln′} {i = i} {i′ = i′} {c = c} {c′ = c′}) = import-h {ctx = ctx} {g = g} {g′ = g′} {ln = ln} {ln′ = ln′} {c = c} {c′ = c′} i i′
  coh-ii {ctx = ctx} (ii-poly-infer {g = g} {g′ = g′} {ln = ln} {ln′ = ln′} {li = li} {li′ = li′} {p = p} {p′ = p′} {gr = gr} {gr′ = gr′} {eq = eq} {eq′ = eq′}) =
    polyinf-h {ctx = ctx} {g = g} {g′ = g′} {ln = ln} {ln′ = ln′} {li = li} {li′ = li′} {gr = gr} {gr′ = gr′} p eq p′ eq′
  coh-ii (ii-annot r) = coh-cc r
  coh-ii (ii-pair r₁ r₂) = pair-h (coh-ii r₁) (coh-ii r₂)
  coh-ii (ii-neg r) = neg-h (coh-ii r)
  coh-ii ii-neg-float = ≅-refl
  coh-ii (ii-let r₁ r₂) = let-h (coh-ii r₁) (coh-ii r₂)
  coh-ii (ii-case r₁ r₂ r₃) = case-h (coh-ii r₁) (coh-ii r₂) (coh-ii r₃)
  coh-ii (ii-arith {a = a} {a′ = a′} {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} r₁ r₂) = arith-h a a′ {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} (coh-ii r₁) (coh-ii r₂)
  coh-ii (ii-farith {a = a} {a′ = a′} {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} r₁ r₂) = farith-h a a′ {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} (coh-ii r₁) (coh-ii r₂)
  coh-ii (ii-il {a = a} {a′ = a′} {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} r₁ r₂) = il-h a a′ {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} (coh-ii r₁) (coh-ii r₂)
  coh-ii (ii-ir {a = a} {a′ = a′} {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} r₁ r₂) = ir-h a a′ {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} (coh-ii r₁) (coh-ii r₂)
  coh-ii (ii-cmp {a = a} {a′ = a′} {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} r₁ r₂) = cmp-h a a′ {d₁ = d₁} {d₁′ = d₁′} {d₂ = d₂} {d₂′ = d₂′} (coh-ii r₁) (coh-ii r₂)
  coh-ii (ii-id-app {d = d} {d′ = d′} r) = idapp-h {d = d} {d′ = d′} (coh-ii r)
  coh-ii (ii-fst-app {d = d} {d′ = d′} r) = fstapp-h {d = d} {d′ = d′} (coh-ii r)
  coh-ii (ii-snd-app {d = d} {d′ = d′} r) = sndapp-h {d = d} {d′ = d′} (coh-ii r)
  coh-ii (ii-terminal-app {d = d} {d′ = d′} r) = termapp-h {d = d} {d′ = d′} (coh-ii r)
  coh-ii (ii-apply {d = d} {d′ = d′} r) = apply-h {d = d} {d′ = d′} (coh-ii r)
  coh-ii (ii-apply-eff {d = d} {d′ = d′} r) = applyeff-h {d = d} {d′ = d′} (coh-ii r)
  coh-ii (ii-Out {w = w} {w′ = w′} {d = d} {d′ = d′} r) = out-h w w′ {d = d} {d′ = d′} (coh-ii r)
  coh-ii (ii-Out-eff {w = w} {w′ = w′} {d = d} {d′ = d′} r) = outeff-h w w′ {d = d} {d′ = d′} (coh-ii r)
  coh-ii (ii-app r₁ r₂) = app-h (coh-ii r₁) (coh-cc r₂)
  coh-ii (ii-effApp r₁ r₂) = effApp-h (coh-ii r₁) (coh-cc r₂)
  coh-ii (ii-app-spine {dX = dX} {dX′ = dX′} rx rd) =
    spine-h (MS.ic-sub dX′ dX) (coh-ic rx (MS.ic-sub dX′ dX)) (coh-di rd (MS.ic-sub dX′ dX) ⊑-pure)
  coh-ii (ii-spine-app {dX = dX} {dX′ = dX′} rx rd) =
    ≅-sym (spine-h (MS.ic-sub dX′ dX) (coh-ic rx (MS.ic-sub dX′ dX)) (coh-di rd (MS.ic-sub dX′ dX) ⊑-pure))
  coh-ii (ii-spine r₁ r₂) = app-h (coh-dd r₂) (coh-ii r₁)

  coh-cc : ∀ {ctx e A Ψ Ψ′} {c : ctx ⊢ᶜ e ∶ A ⨾ Ψ} {c′ : ctx ⊢ᶜ e ∶ A ⨾ Ψ′} → Rcc c c′ → RC c ≅ RC c′
  coh-cc (cc-sub-l {p = p} r) = coh-ic r p
  coh-cc (cc-sub-r {p = p} r) = ≅-sym (coh-ic r p)
  coh-cc cc-id = ≅-refl
  coh-cc cc-fst = ≅-refl
  coh-cc cc-snd = ≅-refl
  coh-cc cc-terminal = ≅-refl
  coh-cc cc-initial = ≅-refl
  coh-cc cc-inl = ≅-refl
  coh-cc cc-inr = ≅-refl
  coh-cc (cc-gg r₁ r₂) = comp-h (coh-cc r₂) (coh-dd r₁)
  coh-cc (cc-gf {s = s} {dg = dg} {df = df} {wf = wf} {dg′ = dg′} rdc ric) =
    gf-h (MS.dc-sub dg dg′) s (MS.ic-sub wf df) (coh-ic ric (MS.ic-sub wf df)) (coh-dc rdc (MS.dc-sub dg dg′))
  coh-cc (cc-fg {s = s} {dg = dg} {df = df} {wf = wf} {dg′ = dg′} rdc ric) =
    ≅-sym (gf-h (MS.dc-sub dg dg′) s (MS.ic-sub wf df) (coh-ic ric (MS.ic-sub wf df)) (coh-dc rdc (MS.dc-sub dg dg′)))
  coh-cc (cc-ff {s = s} {s′ = s′} r₁ r₂) = comp-h (coerce-h s s′ (coh-ii r₁)) (coh-cc r₂)
  coh-cc (cc-copair r₁ r₂) = copair-h (coh-cc r₁) (coh-cc r₂)
  coh-cc (cc-fork r₁ r₂) = fork-h (coh-cc r₁) (coh-cc r₂)
  coh-cc (cc-curry r) = curry-h (coh-cc r)
  coh-cc (cc-cata {w = w} {w′ = w′} r) = cata-h w w′ (coh-cc r)
  coh-cc (cc-ana {w = w} {w′ = w′} r) = ana-h w w′ (coh-cc r)
  coh-cc (cc-lam {≤p = ≤p} {≤p′ = ≤p′} r) = lam-h ≤p ≤p′ (coh-cc r)
  coh-cc (cc-pair-lit r₁ r₂) = pair-h (coh-cc r₁) (coh-cc r₂)
  coh-cc (cc-In {w = w} {w′ = w′} {d = d} {d′ = d′} r) = In-h w w′ {d = d} {d′ = d′} (coh-cc r)
  coh-cc (cc-apply {d = d} {d′ = d′} r) = applychk-h {d = d} {d′ = d′} (coh-ii r)
  coh-cc (cc-inl-app {d = d} {d′ = d′} r) = inlapp-h {d = d} {d′ = d′} (coh-cc r)
  coh-cc (cc-inr-app {d = d} {d′ = d′} r) = inrapp-h {d = d} {d′ = d′} (coh-cc r)
  coh-cc (cc-initial-app {d = d} {d′ = d′} r) = initapp-h {d = d} {d′ = d′} (coh-cc r)
  coh-cc cc-poly = ≅-refl

  -- A checked term means its inferred meaning, converted.
  coh-ic : ∀ {ctx e A B Ψ Ψ′} {d : ctx ⊢ᵢ e ∶ A ⨾ Ψ} {c : ctx ⊢ᶜ e ∶ B ⨾ Ψ′} → Ric d c → (p : A <: B)
         → coerce p (RI d) ≅ RC c
  coh-ic (ic-sub {p = p′} r) p = coerce-h p p′ (coh-ii r)
  coh-ic (ic-pair r₁ r₂) (sub-prod pa pb) = pairc-h pa pb (coh-ic r₁ pa) (coh-ic r₂ pb)
  coh-ic (ic-apply {d = d} {d′ = d′} r) p = applyic-h {d = d} {d′ = d′} p refl (coh-ii r)

  -- A term checked at an arrow from its given domain means its domain-given
  -- meaning, its codomain converted.
  coh-dc : ∀ {ctx e A B B′ π Ψ Ψ′} {dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ} {c : ctx ⊢ᶜ e ∶ (A ⇒[ T.mk-kind T.Many π ] B′) ⨾ Ψ′}
         → Rdc dd c → (p : B <: B′) → coerce (sub-arr (<:-refl A) p (⊑π-refl π)) (RD dd) ≅ RC c
  coh-dc (dc-infer {a = a} {g = g} {w = w} {c = c} r) p =
    twice-h (sub-arr a (<:-refl _) g) (sub-arr (<:-refl _) p (⊑π-refl _)) (MS.ic-sub w c) (coh-ic r (MS.ic-sub w c))
  coh-dc (dc-sub {p = sub-arr a₀ b₀ g₀} r) p = dcsub-h p a₀ b₀ g₀ (coh-di r a₀ g₀)
  coh-dc (dc-lam {≤p = ≤p} {≤p′ = ≤p′} r) p = lamc-h ≤p ≤p′ p (coh-ic r p)
  coh-dc (dc-cg r₁ r₂) p = cg-h p (coh-dc r₂ p) (coh-dd r₁)
  coh-dc (dc-cf {s = s@(sub-arr _ _ g′)} {dg = dg} {dg′ = dg′} rdi rdc) p =
    cf-h (MS.dc-sub dg dg′) p g′ s (coh-di rdi (MS.dc-sub dg dg′) g′) (coh-dc rdc (MS.dc-sub dg dg′))
  coh-dc dc-id p = ≅-of (≈-trans (coerce-uniq _ (<:-refl _) _) (coerce-refl _))
  coh-dc dc-fst p = ≅-of (≈-trans (coerce-uniq _ (<:-refl _) _) (coerce-refl _))
  coh-dc dc-snd p = ≅-of (≈-trans (coerce-uniq _ (<:-refl _) _) (coerce-refl _))
  coh-dc dc-terminal p = ≅-of (≈-trans (coerce-uniq _ (<:-refl _) _) (coerce-refl _))
  coh-dc dc-initial p = ≅-of (≈-trans (coerce-uniq _ (sub-arr sub-void sub-void (⊑π-refl _)) _) (initial-coerce _))
  coh-dc (dc-case r₁ r₂) p = casec-h p (coh-dc r₁ p) (coh-dc r₂ p)
  coh-dc (dc-pair r₁ r₂) (sub-prod pb pc) = forkc-h pb pc (coh-dc r₁ pb) (coh-dc r₂ pc)
  coh-dc (dc-cata {w = w} {w′ = w′} {a = a} {a′ = a′} r) p = catac-h w w′ p (MS.ic-sub a a′) (coh-ic r (MS.ic-sub a a′))
  coh-dc {ctx = ctx} (dc-poly {x = x} {p = q₀} {p′ = q₀′} {as = as} {ki = θ , e , _} {ki′ = θ′ , e′ , _} {gr = gr} {inc = inc}) p =
    polydc-h {ctx = ctx} {x = x} (trans (sym q₀) q₀′) as inc θ e θ′ e′ gr p

  -- A domain-given term that synthesizes means its synthesized arrow, converted.
  coh-di : ∀ {ctx e A A′ B B′ π q π′ Ψ Ψ′} {dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ} {d : ctx ⊢ᵢ e ∶ (A′ ⇒[ T.mk-kind q π′ ] B′) ⨾ Ψ′}
         → Rdi dd d → (a : A <: A′) (g : π′ ⊑π π) → RD dd ≅ coerce (sub-arr {q = q} a (<:-refl B′) g) (RI d)
  coh-di (di-infer {a = a₀} {g = g₀} r) a g = di-h a₀ g₀ a g (coh-ii r)

  coh-dd : ∀ {ctx e A B B′ π Ψ Ψ′} {dd : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ} {dd′ : ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B′ ⨾ Ψ′}
         → Rdd dd dd′ → RD dd ≅ RD dd′
  coh-dd (dd-infer-l {a = a} {g = g} r) = ≅-sym (coh-di r a g)
  coh-dd (dd-infer-r {a = a} {g = g} r) = coh-di r a g
  coh-dd (dd-lam {≤p = ≤p} {≤p′ = ≤p′} r) = lamd-h ≤p ≤p′ (coh-ii r)
  coh-dd (dd-compose r₁ r₂) = comp-h (coh-dd r₂) (coh-dd r₁)
  coh-dd dd-id = ≅-refl
  coh-dd dd-fst = ≅-refl
  coh-dd dd-snd = ≅-refl
  coh-dd dd-terminal = ≅-refl
  coh-dd dd-initial = ≅-refl
  coh-dd (dd-case r₁ r₂) = copair-h (coh-dd r₁) (coh-dd r₂)
  coh-dd (dd-pair r₁ r₂) = fork-h (coh-dd r₁) (coh-dd r₂)
  coh-dd (dd-cata {w = w} {w′ = w′} r) = catad-h w w′ (coh-ii r)
  coh-dd {ctx = ctx} (dd-poly {x = x} {p = q₀} {p′ = q₀′} {as = as} {as′ = as′} {ki = θ , e , _} {ki′ = θ′ , e′ , _} {gr = gr} {gr′ = gr′} {inc = inc}) =
    polydd-h {ctx = ctx} {x = x} (trans (sym q₀) q₀′) as as′ inc θ e θ′ e′ gr gr′

------------------------------------------------------------------------
-- A4: two derivations of one judgment mean the same.
------------------------------------------------------------------------

realize-invariant :
  ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type} {Ψ : Surface.Usage (NamedCtx.size ctx)}
    (d₁ d₂ : ctx ⊢ᶜ e ∶ A ⨾ Ψ) (σ : SD.DefsSem) (dγ : _)
  → ⟦ RC d₁ ⟧ˢ fmt σ dγ ≡ ⟦ RC d₂ ⟧ˢ fmt σ dγ
realize-invariant d₁ d₂ σ dγ = cong-app (cong-app (≈-out (≅-≈ (coh-cc (route-cc d₁ d₂)))) σ) dγ
