-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — REDUCTION and CONVERSION, over a SIGNATURE.
--
-- Split out of `Spec/Typing` by PLAN-REF (D082).  The only rule that reads
-- the signature is δ: a reference is a PROJECTION from the definition
-- context, and unfolds to the signature's body.  Everything else is the
-- kernel's computation as before (see `Spec/Typing`'s header).
--
-- ★ `δref`'s side condition (`d <ˢ size`) makes reduction MONOTONE under
--   signature extension: a name beyond the signature is stuck, so every step
--   under 𝒮 is a step under any extension of 𝒮 (PLAN-REF §1.4).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
module DirectedHoTT.Spec.Reduction (𝒮 : Defs) where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam; app
        ; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap
        ; Id; ⌜Id⌝; idrefl; jsub
        ; Unit; Nat; unit; nzero; nsuc; natrec; extS; ⌜Nat⌝; ⌜Unit⌝
        ; Ren; extR; Sub; subTy; subTm; renTy; renTm
        ; subTy-subTy; subTy-cong; renTy-subTy; subTm-renTm; subTm-id
        ; εwkTy; εwk-ren; εwk-sub; εwkTm
        ; IMu; Desc; DIh; Fin; ⌜IMu⌝; ⌜Fin⌝; con; ielim; dι; dσ; dρ; dpay; dih
        ; fzero; fsuc; fcase; fcase0; psplit; ref; Defs; _<ˢ_ )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; occTm; pw?; stkC?; stkA?; flat?; pwBody; pwShift
        ; NoNatC; nnc-base; nnc-Unit; nnc-Π; nnc-Σ; nnc-Hom; nnc-Id )
open import DirectedHoTT.Spec.Base public

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Reduction — the directed `Hom`. β on terms; congruence onto types.
------------------------------------------------------------------------

infix 3 _⟶_ _⟶ᵀ_
data _⟶_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  β       : (t : RTm (Γ ∙)) (u : RTm Γ) → app (lam t) u ⟶ subTm (single u) t
  βfst    : (a b : RTm Γ) → fst (pair a b) ⟶ a
  βsnd    : (a b : RTm Γ) → snd (pair a b) ⟶ b
  ξ-lam   : {t t' : RTm (Γ ∙)} → t ⟶ t' → lam t ⟶ lam t'
  ξ-appˡ  : {t t' u : RTm Γ} → t ⟶ t' → app t u ⟶ app t' u
  ξ-appʳ  : {t u u' : RTm Γ} → u ⟶ u' → app t u ⟶ app t u'
  ξ-pairˡ : {a a' b : RTm Γ} → a ⟶ a' → pair a b ⟶ pair a' b
  ξ-pairʳ : {a b b' : RTm Γ} → b ⟶ b' → pair a b ⟶ pair a b'
  -- ★★ WF-axis stage D: EX FALSO has NO root rule.  Its scrutinee can
  -- never become canonical (that is `consistency`), so `absurd e` is
  -- permanently NEUTRAL and only its scrutinee develops.
  -- ★★ WF-axis: ORDER TRANSPORT — ≤-transitivity at OPEN naturals.
  -- Five root rules, splitting on `a`, then `u`, then `t`.  Rule 4 is
  -- stage D's first real customer: there `p : Hom Nat (nsuc a') nzero`
  -- has ALREADY computed to `base`, so ex falso applies and the code
  -- works out exactly — `El (⌜Hom⌝ ⌜Nat⌝ a' u')` reduces to the result
  -- type `Hom Nat a' u'`.
  ordtr-z   : (t u p q : RTm Γ) → ordtr nzero t u p q ⟶ unit
  ordtr-szz : (a p q : RTm Γ) → ordtr (nsuc a) nzero nzero p q ⟶ p
  ordtr-ssz : (a t p q : RTm Γ) → ordtr (nsuc a) (nsuc t) nzero p q ⟶ q
  ordtr-szs : (a u p q : RTm Γ) →
              ordtr (nsuc a) nzero (nsuc u) p q ⟶ absurd (⌜Hom⌝ ⌜Nat⌝ a u) p
  ordtr-sss : (a t u p q : RTm Γ) →
              ordtr (nsuc a) (nsuc t) (nsuc u) p q ⟶ ordtr a t u p q
  ξ-ordtrᵃ : {a a' t u p q : RTm Γ} → a ⟶ a' → ordtr a t u p q ⟶ ordtr a' t u p q
  ξ-ordtrᵗ : {a t t' u p q : RTm Γ} → t ⟶ t' → ordtr a t u p q ⟶ ordtr a t' u p q
  ξ-ordtrᵘ : {a t u u' p q : RTm Γ} → u ⟶ u' → ordtr a t u p q ⟶ ordtr a t u' p q
  ξ-ordtrᵖ : {a t u p p' q : RTm Γ} → p ⟶ p' → ordtr a t u p q ⟶ ordtr a t u p' q
  ξ-ordtrq : {a t u p q q' : RTm Γ} → q ⟶ q' → ordtr a t u p q ⟶ ordtr a t u p q'
  ξ-absurdᶜ : {c c' e : RTm Γ} → c ⟶ c' → absurd c e ⟶ absurd c' e
  ξ-absurdᵉ : {c e e' : RTm Γ} → e ⟶ e' → absurd c e ⟶ absurd c e'
  ξ-fst   : {p p' : RTm Γ} → p ⟶ p' → fst p ⟶ fst p'
  ξ-snd   : {p p' : RTm Γ} → p ⟶ p' → snd p ⟶ snd p'
  ξ-⌜Π⌝ˡ  : {c c' : RTm Γ} {d : RTm (Γ ∙)} → c ⟶ c' → ⌜Π⌝ c d ⟶ ⌜Π⌝ c' d
  ξ-⌜Π⌝ʳ  : {c : RTm Γ} {d d' : RTm (Γ ∙)} → d ⟶ d' → ⌜Π⌝ c d ⟶ ⌜Π⌝ c d'
  ξ-⌜Σ⌝ˡ  : {c c' : RTm Γ} {d : RTm (Γ ∙)} → c ⟶ c' → ⌜Σ⌝ c d ⟶ ⌜Σ⌝ c' d
  ξ-⌜Σ⌝ʳ  : {c : RTm Γ} {d d' : RTm (Γ ∙)} → d ⟶ d' → ⌜Σ⌝ c d ⟶ ⌜Σ⌝ c d'
  -- ★ W2 eliminator (SpikeHomRefl + SpikeTr).  `tr` is an ELIMINATOR OF
  -- ITS PATH, so its rules are keyed on the path's canonical form
  -- (SpikeTr: the motive-keyed variants have unjoinable raw critical
  -- pairs).  J fires only where `hrefl` is canonical.
  --
  -- ⚠ CONSOLIDATION FINDING (2026-08-01), correcting SpikeTr/SpikeHomRefl:
  -- `⌜Hom⌝` is NOT a uniformly stuck head.  A `⌜Hom⌝` code whose ambient
  -- SPINE bottoms out in `⌜Π⌝` (`⌜Hom⌝ⁿ (⌜Π⌝ …) …` — higher paths over
  -- function-type paths) decodes to a type that unfolds pointwise to a
  -- `Π`, so `hrefl` there is not canonical — `hrefl`'s unfolding is a
  -- SPINE-RECURSIVE family, not the single `⌜Π⌝` clause SpikeHomRefl
  -- measured, and J at `⌜Hom⌝` needs spine-stuckness — an unbounded-depth
  -- key no finite pattern expresses.  HIGHER PATHS WERE ALREADY UNSCOPED
  -- in this kernel (see `Hom`'s note in NbEPDirDBPi), so the whole
  -- CANONICITY PACKAGE is deferred to that work item as one unit — the
  -- `hrefl` unfold family (incl. `hrefl-Π`), J at `⌜Hom⌝` codes, and
  -- `tr-pw` — with the clean shape being a pair of spine judgments
  -- (`Pw`/`StkC`) premising the rules.  The `swp`/`extR vs` renaming
  -- bridges in SR/Conf are kept, pre-paid.  Until then `hrefl` is
  -- OPERATIONALLY INERT (congruences only) — the LR treats it as neutral,
  -- exactly as long as it has no computation.  This tower's LR is
  -- SN-based (weak normalization + decidability, not canonicity), so
  -- nothing below needs the deferred rules.
  -- ⚠ STAGE 3 RE-KEYING (2026-08-02): J is keyed on the MOTIVE too — it
  -- fires only at `⌜Hom⌝`-headed motives.  At a `var`-motive (the
  -- tautological case, ambient ≅ `U`) a path can NEVER be a typed
  -- `hrefl` (`Hom U t u` unfolds toward `Π` while `Hom (El c) s s` is
  -- headed for a stuck `Hom` — the shapes clash under confluence), so
  -- the un-keyed rule was never typed-exercised; keying it makes the
  -- configuration PERMANENTLY STUCK, hence LR-neutral — which is what
  -- dissolves SpikeTrLR's taut obstruction and lets `⊢trU` merge below.
  tr-J-base : (c a m : RTm (Γ ∙)) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl ⌜base⌝ s) e ⟶ e
  tr-J-Σ    : (c a m : RTm (Γ ∙)) (c₁ : RTm Γ) (c₂ : RTm (Γ ∙)) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e ⟶ e
  -- ★ the two-former kernel: `⌜Id⌝` is a stable J-able shape.
  -- ★ stage C: J fires at `⌜Unit⌝` — a stable shape, so this is the
  -- `tr-J-base` pattern verbatim.  ⚠ THERE IS DELIBERATELY NO
  -- `tr-J-Nat`: `Hom Nat` COMPUTES (`Hom-Nat-z` below discards the
  -- right endpoint), so a `hrefl ⌜Nat⌝ s` does not pin its endpoints
  -- and J at ⌜Nat⌝ breaks subject reduction — see `stkC?`'s note in
  -- NbEPDirDBVar and the counterexample in SPIKE-WF.md §7.  Ordered
  -- types are not J-able; transport along an order path is the tt-path
  -- (≤-coercion) rule instead.
  tr-J-Unit : (c a m : RTm (Γ ∙)) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl ⌜Unit⌝ s) e ⟶ e
  tr-J-Id   : (c a m : RTm (Γ ∙)) (c₁ a₁ b₁ : RTm Γ) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e ⟶ e
  -- ★★★ AND ITS INDEXED TWIN (PLAN-INDEXED §10.4).  ⚠ NOT optional, and
  --   not symmetry-for-its-own-sake: WITHOUT it a closed
  --   `tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ D I i) s) e` is STUCK, and that
  --   configuration IS typeable — `⊢tr`'s `NoNatC` premise excludes
  --   ⌜Nat⌝'s stuck case but says nothing about ⌜IMu⌝ — so PROGRESS
  --   would be FALSE.  `Hom (IMu D I i) a b` computes no further (the
  --   order rules are `Nat`-only), so J at it is as sound as at `Mu D`.
  --   Found by writing `trCS`; the classifiers had it wrong three ways
  --   (`stkC?`, `stkA?`, `stablecd?`) and only the metatheorem noticed.
  tr-J-IMu  : {I D iˣ : RTm Γ} (c a m : RTm (Γ ∙))
              (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ I D iˣ) s) e ⟶ e
  -- ★ tags: `Hom (Fin n)` computes nothing either, so J fires there too.
  tr-J-Fin  : {n : RTm Γ} (c a m : RTm (Γ ∙)) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl (⌜Fin⌝ n) s) e ⟶ e
  -- directed univalence computing a third time: transport at the
  -- tautological motive along a (canonical) universe path is application
  tr-taut   : (f : RTm (Γ ∙)) (e : RTm Γ) →
              tr (var vz) (lam f) e ⟶ app (lam f) e
  -- ★ W2b (G1, SpikeCanon): the CANONICITY PACKAGE.  Three rules, each
  -- keyed by a Boolean classifier (`NbEPDirDBVar`) — the spine
  -- recursion lives in the total function `pwBody`, never in the
  -- relation (SpikeCanon finding 2: a code-level ⌜Hom⌝-Π would break
  -- the pinned-motive architecture).
  --
  -- `hrefl` at a pw-able code unfolds POINTWISE (hrefl-Π is the ⌜Π⌝
  -- instance; the whole ⌜Hom⌝ⁿ(⌜Π⌝…) family is this one rule):
  hrefl-pw : (C s : RTm Γ) → pw? C ≡ true →
             hrefl C s ⟶
             lam (hrefl (pwBody C) (app (renTm vs s) (var vz)))
  -- ★ PLAN-FAITHFUL F6 (2026-10-03): the ORDER's reflexivity computes in
  --   lockstep with its type (`Hom-Nat-z`, `Hom-Nat-ss`).  Without these,
  --   `hrefl ⌜Nat⌝ nzero` is a closed NORMAL inhabitant of `Unit` other
  --   than `unit` — `Unit` was not canonical.  Keyed on the endpoint's
  --   head, like the order rules; `⌜Nat⌝` is neither `pw?` nor `stkC?`,
  --   so nothing overlaps (`hrefl-pw`, `tr-J-*`, `ap-J`).
  hrefl-Nat-z : hrefl ⌜Nat⌝ (nzero {Γ}) ⟶ unit
  hrefl-Nat-s : (m : RTm Γ) → hrefl ⌜Nat⌝ (nsuc m) ⟶ hrefl ⌜Nat⌝ m
  -- J at Hom-codes over PERMANENTLY-STABLE spines (excludes ⌜Π⌝-able
  -- codes — those paths unfold to lambdas — and neutrals, which
  -- substitution could make ⌜Π⌝-able).
  --
  -- ★★ THE KEY IS `stkA?`, NOT `stkC?` (SpikeNatJ).  This rule
  -- DECOMPOSES the path's code as `⌜Hom⌝ c₁ a₁ b₁`, so its key is the
  -- J-ability of the WHOLE code — which is `stkC? (⌜Hom⌝ c₁ a₁ b₁)`,
  -- i.e. `stkA? c₁`.  Testing `stkC? c₁` instead propagated the ⌜Nat⌝
  -- exception outward and left `tr` STUCK on a `hrefl (⌜Hom⌝ ⌜Nat⌝ a b)`
  -- path: the decode there is `Hom Nat a b`, whose own homs have a
  -- `Hom` ambient and so can never fire an order rule.  Ordered types
  -- are not J-able; homs OVER them are.
  tr-J-Hom : (c a m : RTm (Γ ∙)) (c₁ a₁ b₁ s e : RTm Γ) →
             stkA? c₁ ≡ true →
             tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e ⟶ e
  -- POINTWISE TRANSPORT: the transported function's value at x is the
  -- inner transport of `e·x` along the path's body `f`, at the
  -- pointwise motive (keyed on the literal `var vz` endpoint, like
  -- taut — every typed instance has it):
  tr-pw    : (c a f : RTm (Γ ∙)) (e : RTm Γ) → pw? c ≡ true →
             tr (⌜Hom⌝ c a (var vz)) (lam f) e ⟶
             lam (tr (⌜Hom⌝ (renTm pwShift (pwBody c))
                            (app (renTm vs a) (var (vs vz)))
                            (var vz))
                     f
                     (app (renTm vs e) (var vz)))
  ξ-⌜Hom⌝ᶜ : {c c' a b : RTm Γ} → c ⟶ c' → ⌜Hom⌝ c a b ⟶ ⌜Hom⌝ c' a b
  ξ-⌜Hom⌝ˡ : {c a a' b : RTm Γ} → a ⟶ a' → ⌜Hom⌝ c a b ⟶ ⌜Hom⌝ c a' b
  ξ-⌜Hom⌝ʳ : {c a b b' : RTm Γ} → b ⟶ b' → ⌜Hom⌝ c a b ⟶ ⌜Hom⌝ c a b'
  ξ-hreflᶜ : {c c' t : RTm Γ} → c ⟶ c' → hrefl c t ⟶ hrefl c' t
  ξ-hreflᵃ : {c t t' : RTm Γ} → t ⟶ t' → hrefl c t ⟶ hrefl c t'
  ξ-trᵈ    : {d d' : RTm (Γ ∙)} {p e : RTm Γ} → d ⟶ d' → tr d p e ⟶ tr d' p e
  ξ-trᵖ    : {d : RTm (Γ ∙)} {p p' e : RTm Γ} → p ⟶ p' → tr d p e ⟶ tr d p' e
  ξ-trᵉ    : {d : RTm (Γ ∙)} {p e e' : RTm Γ} → e ⟶ e' → tr d p e ⟶ tr d p e'
  -- ★ directed `ap` (SpikeAp): J at stable path-codes — the SAME key as
  -- `tr-J-Hom`, so the raw overlap with `hrefl-pw` is empty (`stk⊥pw`).
  ap-J     : (cB : RTm Γ) (b : RTm (Γ ∙)) (c₁ s : RTm Γ) →
             stkC? c₁ ≡ true →
             ap cB b (hrefl c₁ s) ⟶ hrefl cB (subTm (single s) b)
  ξ-apᶜ    : {c c' : RTm Γ} {b : RTm (Γ ∙)} {p : RTm Γ} →
             c ⟶ c' → ap c b p ⟶ ap c' b p
  ξ-apᵇ    : {c : RTm Γ} {b b' : RTm (Γ ∙)} {p : RTm Γ} →
             b ⟶ b' → ap c b p ⟶ ap c b' p
  ξ-apᵖ    : {c : RTm Γ} {b : RTm (Γ ∙)} {p p' : RTm Γ} →
             p ⟶ p' → ap c b p ⟶ ap c b p'
  -- ★ the two-former kernel (SPIKE-TWOFORMER): subst-style J at an
  -- UNRESTRICTED family — UNKEYED, safe because `idrefl` is inert.
  jsub-refl : (d : RTm (Γ ∙)) (c s e : RTm Γ) →
              jsub d (idrefl c s) e ⟶ e
  ξ-⌜Id⌝ᶜ  : {c c' a b : RTm Γ} → c ⟶ c' → ⌜Id⌝ c a b ⟶ ⌜Id⌝ c' a b
  ξ-⌜Id⌝ˡ  : {c a a' b : RTm Γ} → a ⟶ a' → ⌜Id⌝ c a b ⟶ ⌜Id⌝ c a' b
  ξ-⌜Id⌝ʳ  : {c a b b' : RTm Γ} → b ⟶ b' → ⌜Id⌝ c a b ⟶ ⌜Id⌝ c a b'
  -- ★ S7b step 2: a finite set's size is a Nat TERM
  ξ-⌜Fin⌝  : {n n' : RTm Γ} → n ⟶ n' → ⌜Fin⌝ n ⟶ ⌜Fin⌝ n'
  ξ-idreflᶜ : {c c' t : RTm Γ} → c ⟶ c' → idrefl c t ⟶ idrefl c' t
  ξ-idreflᵃ : {c t t' : RTm Γ} → t ⟶ t' → idrefl c t ⟶ idrefl c t'
  ξ-jsubᵈ  : {d d' : RTm (Γ ∙)} {p e : RTm Γ} → d ⟶ d' → jsub d p e ⟶ jsub d' p e
  ξ-jsubᵖ  : {d : RTm (Γ ∙)} {p p' e : RTm Γ} → p ⟶ p' → jsub d p e ⟶ jsub d p' e
  ξ-jsubᵉ  : {d : RTm (Γ ∙)} {p e e' : RTm Γ} → e ⟶ e' → jsub d p e ⟶ jsub d p e'
  -- ★ WF-axis stage A (SPIKE-WF): Nat's recursor, keyed on the
  -- CANONICAL HEAD of the scrutinee — terminating because the
  -- recursive call is at the numeral's predecessor.
  natrec-zero : (z : RTm Γ) (s : RTm ((Γ ∙) ∙)) →
                natrec z s nzero ⟶ z
  natrec-suc  : (z : RTm Γ) (s : RTm ((Γ ∙) ∙)) (n : RTm Γ) →
                natrec z s (nsuc n) ⟶
                subTm (single (natrec z s n)) (subTm (extS (single n)) s)
  ξ-nsuc    : {n n' : RTm Γ} → n ⟶ n' → nsuc n ⟶ nsuc n'
  ξ-natrecᶻ : {z z' : RTm Γ} {s : RTm ((Γ ∙) ∙)} {n : RTm Γ} →
              z ⟶ z' → natrec z s n ⟶ natrec z' s n
  ξ-natrecˢ : {z : RTm Γ} {s s' : RTm ((Γ ∙) ∙)} {n : RTm Γ} →
              s ⟶ s' → natrec z s n ⟶ natrec z s' n
  ξ-natrecⁿ : {z : RTm Γ} {s : RTm ((Γ ∙) ∙)} {n n' : RTm Γ} →
              n ⟶ n' → natrec z s n ⟶ natrec z s n'
  -- ★★ LEVITATED INDUCTIVE FAMILIES.  THE ι-RULE: keyed on `con p` ONLY —
  --   it fires at ANY description (SPIKE-LEVITATION S1b: the method is a
  --   Π, so a neutral `D` needs no guard).  The hypotheses are `dih`,
  --   which computes on the telescope head and is stuck on a neutral one.
  ι         : (D i e p : RTm Γ) →
              ielim D i e (con p) ⟶ app (app (app e i) p) (dih D e (app D i) p)
  -- the payload CODE of a telescope: nothing at `dι` (D074: the index is
  --   the FIBRE's, not an equation), a Σ at `dσ`, a Σ over the family at
  --   `dρ`.
  dpay-ι    : (I D : RTm Γ) → dpay I D dι ⟶ ⌜Unit⌝
  dpay-σ    : (I D S f : RTm Γ) →
              dpay I D (dσ S f) ⟶
              ⌜Σ⌝ S (dpay (renTm vs I) (renTm vs D) (app (renTm vs f) (var vz)))
  dpay-ρ    : (I D j C : RTm Γ) →
              dpay I D (dρ j C) ⟶
              ⌜Σ⌝ (⌜IMu⌝ I D j) (dpay (renTm vs I) (renTm vs D) (renTm vs C))
  -- the hypotheses: one recursive call per `dρ`, AT ITS OWN INDEX `j`
  dih-ι     : (D e p : RTm Γ) → dih D e dι p ⟶ unit
  dih-σ     : (D e S f p : RTm Γ) → dih D e (dσ S f) p ⟶ dih D e (app f (fst p)) (snd p)
  dih-ρ     : (D e j C p : RTm Γ) →
              dih D e (dρ j C) p ⟶ pair (ielim D j e (fst p)) (dih D e C (snd p))
  -- tags and Σ-induction
  fcase-z   : (a : RTm Γ) (b : RTm (Γ ∙)) → fcase fzero a b ⟶ a
  fcase-s   : (t a : RTm Γ) (b : RTm (Γ ∙)) → fcase (fsuc t) a b ⟶ subTm (single t) b
  psplit-β  : (b : RTm ((Γ ∙) ∙)) (x y : RTm Γ) → psplit b (pair x y) ⟶ subTm (single2 x y) b
  -- ★ δ: a reference is a projection from the signature, and unfolds to
  --   its body (PLAN-REF, D082).  The body is closed, so the rule is
  --   context-free; a name beyond the signature is stuck.
  δref      : {Δ : Cx} (d : ℕ) → d <ˢ Defs.size 𝒮 → ref {Δ} d ⟶ εwkTm {Δ} (Defs.body 𝒮 d)
  -- congruences
  ξ-⌜IMu⌝ᴵ  : {I I' D i : RTm Γ} → I ⟶ I' → ⌜IMu⌝ I D i ⟶ ⌜IMu⌝ I' D i
  ξ-⌜IMu⌝ᴰ  : {I D D' i : RTm Γ} → D ⟶ D' → ⌜IMu⌝ I D i ⟶ ⌜IMu⌝ I D' i
  ξ-⌜IMu⌝ⁱ  : {I D i i' : RTm Γ} → i ⟶ i' → ⌜IMu⌝ I D i ⟶ ⌜IMu⌝ I D i'
  ξ-con     : {p p' : RTm Γ} → p ⟶ p' → con p ⟶ con p'
  ξ-ielimᴰ  : {D D' i e t : RTm Γ} → D ⟶ D' → ielim D i e t ⟶ ielim D' i e t
  ξ-ielimⁱ  : {D i i' e t : RTm Γ} → i ⟶ i' → ielim D i e t ⟶ ielim D i' e t
  ξ-ielimᵉ  : {D i e e' t : RTm Γ} → e ⟶ e' → ielim D i e t ⟶ ielim D i e' t
  ξ-ielimᵗ  : {D i e t t' : RTm Γ} → t ⟶ t' → ielim D i e t ⟶ ielim D i e t'
  ξ-dσˢ     : {S S' f : RTm Γ} → S ⟶ S' → dσ S f ⟶ dσ S' f
  ξ-dσᶠ     : {S f f' : RTm Γ} → f ⟶ f' → dσ S f ⟶ dσ S f'
  ξ-dρʲ     : {j j' C : RTm Γ} → j ⟶ j' → dρ j C ⟶ dρ j' C
  ξ-dρᶜ     : {j C C' : RTm Γ} → C ⟶ C' → dρ j C ⟶ dρ j C'
  ξ-dpayᴵ   : {I I' D C : RTm Γ} → I ⟶ I' → dpay I D C ⟶ dpay I' D C
  ξ-dpayᴰ   : {I D D' C : RTm Γ} → D ⟶ D' → dpay I D C ⟶ dpay I D' C
  ξ-dpayᶜ   : {I D C C' : RTm Γ} → C ⟶ C' → dpay I D C ⟶ dpay I D C'
  ξ-dihᴰ    : {D D' e C p : RTm Γ} → D ⟶ D' → dih D e C p ⟶ dih D' e C p
  ξ-dihᵉ    : {D e e' C p : RTm Γ} → e ⟶ e' → dih D e C p ⟶ dih D e' C p
  ξ-dihᶜ    : {D e C C' p : RTm Γ} → C ⟶ C' → dih D e C p ⟶ dih D e C' p
  ξ-dihᵖ    : {D e C p p' : RTm Γ} → p ⟶ p' → dih D e C p ⟶ dih D e C p'
  ξ-fsuc    : {t t' : RTm Γ} → t ⟶ t' → fsuc t ⟶ fsuc t'
  ξ-fcaseᵗ  : {t t' a : RTm Γ} {b : RTm (Γ ∙)} → t ⟶ t' → fcase t a b ⟶ fcase t' a b
  ξ-fcaseᵃ  : {t a a' : RTm Γ} {b : RTm (Γ ∙)} → a ⟶ a' → fcase t a b ⟶ fcase t a' b
  ξ-fcaseᵇ  : {t a : RTm Γ} {b b' : RTm (Γ ∙)} → b ⟶ b' → fcase t a b ⟶ fcase t a b'
  ξ-fcase0  : {t t' : RTm Γ} → t ⟶ t' → fcase0 t ⟶ fcase0 t'
  ξ-psplitᵇ : {b b' : RTm ((Γ ∙) ∙)} {q : RTm Γ} → b ⟶ b' → psplit b q ⟶ psplit b' q
  ξ-psplitᵍ : {b : RTm ((Γ ∙) ∙)} {q q' : RTm Γ} → q ⟶ q' → psplit b q ⟶ psplit b q'

data _⟶ᵀ_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  El-⌜base⌝ : El (⌜base⌝ {Γ}) ⟶ᵀ base
  El-⌜Π⌝    : (c : RTm Γ) (d : RTm (Γ ∙)) → El (⌜Π⌝ c d) ⟶ᵀ Π (El c) (El d)
  El-⌜Σ⌝    : (c : RTm Γ) (d : RTm (Γ ∙)) → El (⌜Σ⌝ c d) ⟶ᵀ Σ' (El c) (El d)
  -- W2 eliminator: the `⌜Hom⌝` code decodes to the `Hom` former
  -- (hom-sets of small types are small; still no code for `U`)
  El-⌜Hom⌝  : (c a b : RTm Γ) → El (⌜Hom⌝ c a b) ⟶ᵀ Hom (El c) a b
  El-⌜Id⌝   : (c a b : RTm Γ) → El (⌜Id⌝ c a b) ⟶ᵀ Id (El c) a b
  -- ★ stage C (N-in): the datatype codes decode.
  El-⌜Nat⌝  : El (⌜Nat⌝ {Γ}) ⟶ᵀ Nat
  El-⌜IMu⌝  : {I D i : RTm Γ} → El (⌜IMu⌝ I D i) ⟶ᵀ IMu I D i
  El-⌜Fin⌝  : {n : RTm Γ} → El (⌜Fin⌝ n) ⟶ᵀ Fin n
  -- ★★ the hypotheses' TYPE computes on the telescope head (S3).
  DIh-ι : (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (p : RTm Γ) → DIh D M dι p ⟶ᵀ Unit
  DIh-σ : (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (S f p : RTm Γ) →
          DIh D M (dσ S f) p ⟶ᵀ DIh D M (app f (fst p)) (snd p)
  DIh-ρ : (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (j C p : RTm Γ) →
          DIh D M (dρ j C) p ⟶ᵀ
          Σ' (iinst j (fst p) M)
             (DIh (renTm vs D) (renTy (extR (extR vs)) M) (renTm vs C) (snd (renTm vs p)))
  El-⌜Unit⌝ : El (⌜Unit⌝ {Γ}) ⟶ᵀ Unit
  ξ-El : {t t' : RTm Γ} → t ⟶ t' → El t ⟶ᵀ El t'
  ξ-Πˡ : {A A' : RTy Γ} {B : RTy (Γ ∙)} → A ⟶ᵀ A' → Π A B ⟶ᵀ Π A' B
  ξ-Πʳ : {A : RTy Γ} {B B' : RTy (Γ ∙)} → B ⟶ᵀ B' → Π A B ⟶ᵀ Π A B'
  ξ-Σˡ : {A A' : RTy Γ} {B : RTy (Γ ∙)} → A ⟶ᵀ A' → Σ' A B ⟶ᵀ Σ' A' B
  ξ-Σʳ : {A : RTy Γ} {B B' : RTy (Γ ∙)} → B ⟶ᵀ B' → Σ' A B ⟶ᵀ Σ' A B'
  -- ★ W2: `Hom` COMPUTES, like `El` (SpikeHomTy's clauses, promoted).
  -- `Hom-U` is DIRECTED UNIVALENCE as a computation rule: a path between
  -- codes IS a map between their decodings.  `Hom-Π` is the POINTWISE family
  -- (item 2: naturality is not carried; item 3: it must not be).  There is
  -- deliberately NO rule at `base` (discrete by generation, item 4), none at
  -- `Σ'` (its unfolding needs transport, a term former W2's eliminator will
  -- introduce — deferred, not dropped), none at a stuck `El`, none at `Hom`.
  -- ★★ WF-axis stage B (SPIKE-WF §2): THE COMPUTING ORDER.  On `Nat`
  -- the DIRECTED structure IS the order — `Hom Nat m n` does not
  -- represent `m ≤ n`, it COMPUTES to it.  The rules are keyed on the
  -- ENDPOINTS' constructor heads (not on the ambient, as `Hom-U` and
  -- `Hom-Π` are), which is what makes `Nat` an ORDERED inductive.
  --
  -- `base` is the empty type here: it has no closed inhabitants
  -- (`consistency`, NbEPDirDBCanon), so a false inequality is
  -- refuted by the kernel's own consistency theorem.
  Hom-Nat-z  : (n : RTm Γ) → Hom Nat nzero n ⟶ᵀ Unit
  Hom-Nat-sz : (m : RTm Γ) → Hom Nat (nsuc m) nzero ⟶ᵀ base
  Hom-Nat-ss : (m n : RTm Γ) → Hom Nat (nsuc m) (nsuc n) ⟶ᵀ Hom Nat m n
  Hom-U : (c d : RTm Γ) → Hom U c d ⟶ᵀ Π (El c) (El (renTm vs d))
  Hom-Π : (A : RTy Γ) (B : RTy (Γ ∙)) (f g : RTm Γ) →
          Hom (Π A B) f g ⟶ᵀ
          Π A (Hom B (app (renTm vs f) (var vz)) (app (renTm vs g) (var vz)))
  ξ-Homᵀ : {A A' : RTy Γ} {t u : RTm Γ} → A ⟶ᵀ A' → Hom A t u ⟶ᵀ Hom A' t u
  ξ-Homˡ : {A : RTy Γ} {t t' u : RTm Γ} → t ⟶ t' → Hom A t u ⟶ᵀ Hom A t' u
  ξ-Homʳ : {A : RTy Γ} {t u u' : RTm Γ} → u ⟶ u' → Hom A t u ⟶ᵀ Hom A t u'
  ξ-Idᵀ  : {A A' : RTy Γ} {t u : RTm Γ} → A ⟶ᵀ A' → Id A t u ⟶ᵀ Id A' t u
  ξ-Idˡ  : {A : RTy Γ} {t t' u : RTm Γ} → t ⟶ t' → Id A t u ⟶ᵀ Id A t' u
  ξ-Idʳ  : {A : RTy Γ} {t u u' : RTm Γ} → u ⟶ u' → Id A t u ⟶ᵀ Id A t u'
  -- ★ the formers that carry terms need congruences (a type-level `sr`
  --   preserves types on the nose; retyping after an index step needs these).
  ξ-IMuᴵ  : {I I' D i : RTm Γ} → I ⟶ I' → IMu I D i ⟶ᵀ IMu I' D i
  ξ-IMuᴰ  : {I D D' i : RTm Γ} → D ⟶ D' → IMu I D i ⟶ᵀ IMu I D' i
  ξ-IMuⁱ  : {I D i i' : RTm Γ} → i ⟶ i' → IMu I D i ⟶ᵀ IMu I D i'
  ξ-Desc  : {I I' : RTm Γ} → I ⟶ I' → Desc I ⟶ᵀ Desc I'
  ξ-Fin   : {n n' : RTm Γ} → n ⟶ n' → Fin n ⟶ᵀ Fin n'
  ξ-DIhᴰ  : {D D' C p : RTm Γ} {M : RTy ((Γ ∙) ∙)} → D ⟶ D' → DIh D M C p ⟶ᵀ DIh D' M C p
  ξ-DIhᴹ  : {D C p : RTm Γ} {M M' : RTy ((Γ ∙) ∙)} → M ⟶ᵀ M' → DIh D M C p ⟶ᵀ DIh D M' C p
  ξ-DIhᶜ  : {D C C' p : RTm Γ} {M : RTy ((Γ ∙) ∙)} → C ⟶ C' → DIh D M C p ⟶ᵀ DIh D M C' p
  ξ-DIhᵖ  : {D C p p' : RTm Γ} {M : RTy ((Γ ∙) ∙)} → p ⟶ p' → DIh D M C p ⟶ᵀ DIh D M C p'

infix 3 _⟶*_
data _⟶*_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  done : {t : RTm Γ} → t ⟶* t
  step : {t u v : RTm Γ} → t ⟶ u → u ⟶* v → t ⟶* v

-- ⚠ READING CORRECTED (W2 §4.0): `_⟶*_` is NOT the directed identity type —
-- reduction is too small to be a path type (`SpikeVar`).  The internal `Hom`
-- is now the TYPE FORMER above.  The meta-level relation keeps only its
-- operational role, renamed `Hom⟶`; `Core⟶` is its symmetric core, and it is
-- what conversion completes.
Hom⟶ : RTm Γ → RTm Γ → Set
Hom⟶ t u = t ⟶* u


Core⟶ : RTm Γ → RTm Γ → Set
Core⟶ t u = Hom⟶ t u × Hom⟶ u t

------------------------------------------------------------------------
-- Conversion = definitional equality = the R-S-T closure of reduction.
-- This is `core(Hom)`: the symmetric completion of the directed `Hom`.
------------------------------------------------------------------------

infix 3 _≅_ _≅ᵀ_
data _≅_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  cred : {t u : RTm Γ}   → t ⟶ u → t ≅ u
  crfl : {t : RTm Γ}     → t ≅ t
  csym : {t u : RTm Γ}   → t ≅ u → u ≅ t
  ctrn : {t u v : RTm Γ} → t ≅ u → u ≅ v → t ≅ v

data _≅ᵀ_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  credᵀ : {A B : RTy Γ}   → A ⟶ᵀ B → A ≅ᵀ B
  crflᵀ : {A : RTy Γ}     → A ≅ᵀ A
  csymᵀ : {A B : RTy Γ}   → A ≅ᵀ B → B ≅ᵀ A
  ctrnᵀ : {A B C : RTy Γ} → A ≅ᵀ B → B ≅ᵀ C → A ≅ᵀ C

-- Reduction (and its core) lands in the conversion the typechecker uses.
hom→≅ : {t u : RTm Γ} → Hom⟶ t u → t ≅ u
hom→≅ done       = crfl
hom→≅ (step r p) = ctrn (cred r) (hom→≅ p)

core→≅ : {t u : RTm Γ} → Core⟶ t u → t ≅ u
core→≅ c = hom→≅ (_×_.π₁ c)

