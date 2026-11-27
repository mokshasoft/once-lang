-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — REDUCTION and CONVERSION, over a SIGNATURE.
--
-- Split out of `Spec/Typing` by PLAN-REF (D501).  The only rule that reads
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
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Scope using ( Cx; ε; _∙; Var; vz; vs )
open import DirectedHoTT.Spec.Syntax
  using ( RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap; Id; ⌜Id⌝; idrefl; jsub; Unit; Nat; unit; nzero; nsuc; natrec; extS; ⌜Nat⌝; ⌜Unit⌝; Ren; extR; Sub; subTy; subTm; renTy; renTm; subTy-subTy; subTy-cong; renTy-subTy; subTm-renTm; subTm-id; εwkTy; εwk-ren; εwk-sub; εwkTm; IMu; Desc; DIh; Fin; ⌜IMu⌝; ⌜Fin⌝; con; ielim; dι; dσ; dρ; dpay; dih; fzero; fsuc; fcase; fcase0; psplit; ref; Defs; _<ˢ_ )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; occTm; pw?; stkC?; stkA?; flat?; pwBody; pwShift
        ; NoNatC; nnc-base; nnc-Unit; nnc-Π; nnc-Σ; nnc-Hom; nnc-Id )
-- ★ NOT `public`: a module application copies the whole exported scope, so
--   every instance of this module (and of Spec.Typing) would mint its own
--   `single`, `⌊_⌋`, … — two heads for one function, compared by evaluating
--   (Gcd/LeEq 4 s → 1057 s).  Import them from Spec.Base (tools/base_unshare.py).
open import DirectedHoTT.Spec.Base
import DirectedHoTT.Spec.Syntax as Sx
open import DirectedHoTT.Spec.Syntax using ( KSig )
import DirectedHoTT.Spec.Bind as G
open import DirectedHoTT.Prelude using ( _,_; inj₁; inj₂ )
open import DirectedHoTT.Spec.BindRed KSig using ( module Red )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Reduction — the directed `Hom`. β on terms; congruence onto types.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★ GENERIC REDUCTION (SPIKE-GENERIC-SYNTAX S8, branch spike-generic-syntax):
--   ONE relation over both sorts — `Spec/BindRed`'s single CONGRUENCE rule
--   (every former, every subterm position) plus the CONTRACTIONS `_⊳_`
--   below, which are the kernel's computation rules (their text unchanged,
--   arrow `⊳`). The old 88 congruence rules were exactly that uniform
--   congruence (measured: every former, every position), so nothing that
--   reduces changes. `_⟶_`/`_⟶ᵀ_` are the relation at the two sorts, and
--   every old rule name is a pattern synonym below.
------------------------------------------------------------------------

infix 3 _⊳_
data _⊳_ : ∀ {s Γ} → G.Tm KSig s Γ → G.Tm KSig s Γ → Set where
  βʳ       : (t : RTm (Γ ∙)) (u : RTm Γ) → app (lam t) u ⊳ subTm (single u) t
  βfstʳ    : (a b : RTm Γ) → fst (pair a b) ⊳ a
  βsndʳ    : (a b : RTm Γ) → snd (pair a b) ⊳ b
  ordtr-zʳ   : (t u p q : RTm Γ) → ordtr nzero t u p q ⊳ unit
  ordtr-szzʳ : (a p q : RTm Γ) → ordtr (nsuc a) nzero nzero p q ⊳ p
  ordtr-sszʳ : (a t p q : RTm Γ) → ordtr (nsuc a) (nsuc t) nzero p q ⊳ q
  ordtr-szsʳ : (a u p q : RTm Γ) →
              ordtr (nsuc a) nzero (nsuc u) p q ⊳ absurd (⌜Hom⌝ ⌜Nat⌝ a u) p
  ordtr-sssʳ : (a t u p q : RTm Γ) →
              ordtr (nsuc a) (nsuc t) (nsuc u) p q ⊳ ordtr a t u p q
  tr-J-baseʳ : (c a m : RTm (Γ ∙)) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl ⌜base⌝ s) e ⊳ e
  tr-J-Σʳ    : (c a m : RTm (Γ ∙)) (c₁ : RTm Γ) (c₂ : RTm (Γ ∙)) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e ⊳ e
  -- ★ the two-former kernel: `⌜Id⌝` is a stable J-able shape.
  -- ★ stage C: J fires at `⌜Unit⌝` — a stable shape, so this is the
  -- `tr-J-base` pattern verbatim.  ⚠ THERE IS DELIBERATELY NO
  -- `tr-J-Nat`: `Hom Nat` COMPUTES (`Hom-Nat-z` below discards the
  -- right endpoint), so a `hrefl ⌜Nat⌝ s` does not pin its endpoints
  -- and J at ⌜Nat⌝ breaks subject reduction — see `stkC?`'s note in
  -- NbEPDirDBVar and the counterexample in SPIKE-WF.md §7.  Ordered
  -- types are not J-able; transport along an order path is the tt-path
  -- (≤-coercion) rule instead.
  tr-J-Unitʳ : (c a m : RTm (Γ ∙)) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl ⌜Unit⌝ s) e ⊳ e
  tr-J-Idʳ   : (c a m : RTm (Γ ∙)) (c₁ a₁ b₁ : RTm Γ) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e ⊳ e
  -- ★★★ AND ITS INDEXED TWIN (PLAN-INDEXED §10.4).  ⚠ NOT optional, and
  --   not symmetry-for-its-own-sake: WITHOUT it a closed
  --   `tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ D I i) s) e` is STUCK, and that
  --   configuration IS typeable — `⊢tr`'s `NoNatC` premise excludes
  --   ⌜Nat⌝'s stuck case but says nothing about ⌜IMu⌝ — so PROGRESS
  --   would be FALSE.  `Hom (IMu D I i) a b` computes no further (the
  --   order rules are `Nat`-only), so J at it is as sound as at `Mu D`.
  --   Found by writing `trCS`; the classifiers had it wrong three ways
  --   (`stkC?`, `stkA?`, `stablecd?`) and only the metatheorem noticed.
  tr-J-IMuʳ  : {I D iˣ : RTm Γ} (c a m : RTm (Γ ∙))
              (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ I D iˣ) s) e ⊳ e
  -- ★ tags: `Hom (Fin n)` computes nothing either, so J fires there too.
  tr-J-Finʳ  : {n : RTm Γ} (c a m : RTm (Γ ∙)) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl (⌜Fin⌝ n) s) e ⊳ e
  -- directed univalence computing a third time: transport at the
  -- tautological motive along a (canonical) universe path is application
  tr-tautʳ   : (f : RTm (Γ ∙)) (e : RTm Γ) →
              tr (var vz) (lam f) e ⊳ app (lam f) e
  -- ★ W2b (G1, SpikeCanon): the CANONICITY PACKAGE.  Three rules, each
  -- keyed by a Boolean classifier (`NbEPDirDBVar`) — the spine
  -- recursion lives in the total function `pwBody`, never in the
  -- relation (SpikeCanon finding 2: a code-level ⌜Hom⌝-Π would break
  -- the pinned-motive architecture).
  --
  -- `hrefl` at a pw-able code unfolds POINTWISE (hrefl-Π is the ⌜Π⌝
  -- instance; the whole ⌜Hom⌝ⁿ(⌜Π⌝…) family is this one rule):
  hrefl-pwʳ : (C s : RTm Γ) → pw? C ≡ true →
             hrefl C s ⊳              lam (hrefl (pwBody C) (app (renTm vs s) (var vz)))
  -- ★ PLAN-FAITHFUL F6 (2026-10-03): the ORDER's reflexivity computes in
  --   lockstep with its type (`Hom-Nat-z`, `Hom-Nat-ss`).  Without these,
  --   `hrefl ⌜Nat⌝ nzero` is a closed NORMAL inhabitant of `Unit` other
  --   than `unit` — `Unit` was not canonical.  Keyed on the endpoint's
  --   head, like the order rules; `⌜Nat⌝` is neither `pw?` nor `stkC?`,
  --   so nothing overlaps (`hrefl-pw`, `tr-J-*`, `ap-J`).
  hrefl-Nat-zʳ : hrefl ⌜Nat⌝ (nzero {Γ}) ⊳ unit
  hrefl-Nat-sʳ : (m : RTm Γ) → hrefl ⌜Nat⌝ (nsuc m) ⊳ hrefl ⌜Nat⌝ m
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
  tr-J-Homʳ : (c a m : RTm (Γ ∙)) (c₁ a₁ b₁ s e : RTm Γ) →
             stkA? c₁ ≡ true →
             tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e ⊳ e
  -- POINTWISE TRANSPORT: the transported function's value at x is the
  -- inner transport of `e·x` along the path's body `f`, at the
  -- pointwise motive (keyed on the literal `var vz` endpoint, like
  -- taut — every typed instance has it):
  tr-pwʳ    : (c a f : RTm (Γ ∙)) (e : RTm Γ) → pw? c ≡ true →
             tr (⌜Hom⌝ c a (var vz)) (lam f) e ⊳              lam (tr (⌜Hom⌝ (renTm pwShift (pwBody c))
                            (app (renTm vs a) (var (vs vz)))
                            (var vz))
                     f
                     (app (renTm vs e) (var vz)))
  ap-Jʳ     : (cB : RTm Γ) (b : RTm (Γ ∙)) (c₁ s : RTm Γ) →
             stkC? c₁ ≡ true →
             ap cB b (hrefl c₁ s) ⊳ hrefl cB (subTm (single s) b)
  jsub-reflʳ : (d : RTm (Γ ∙)) (c s e : RTm Γ) →
              jsub d (idrefl c s) e ⊳ e
  natrec-zeroʳ : (z : RTm Γ) (s : RTm ((Γ ∙) ∙)) →
                natrec z s nzero ⊳ z
  natrec-sucʳ  : (z : RTm Γ) (s : RTm ((Γ ∙) ∙)) (n : RTm Γ) →
                natrec z s (nsuc n) ⊳                 subTm (single (natrec z s n)) (subTm (extS (single n)) s)
  ιʳ         : (D i e p : RTm Γ) →
              ielim D i e (con p) ⊳ app (app (app e i) p) (dih D e (app D i) p)
  -- the payload CODE of a telescope: nothing at `dι` (D493: the index is
  --   the FIBRE's, not an equation), a Σ at `dσ`, a Σ over the family at
  --   `dρ`.
  dpay-ιʳ    : (I D : RTm Γ) → dpay I D dι ⊳ ⌜Unit⌝
  dpay-σʳ    : (I D S f : RTm Γ) →
              dpay I D (dσ S f) ⊳               ⌜Σ⌝ S (dpay (renTm vs I) (renTm vs D) (app (renTm vs f) (var vz)))
  dpay-ρʳ    : (I D j C : RTm Γ) →
              dpay I D (dρ j C) ⊳               ⌜Σ⌝ (⌜IMu⌝ I D j) (dpay (renTm vs I) (renTm vs D) (renTm vs C))
  -- the hypotheses: one recursive call per `dρ`, AT ITS OWN INDEX `j`
  dih-ιʳ     : (D e p : RTm Γ) → dih D e dι p ⊳ unit
  dih-σʳ     : (D e S f p : RTm Γ) → dih D e (dσ S f) p ⊳ dih D e (app f (fst p)) (snd p)
  dih-ρʳ     : (D e j C p : RTm Γ) →
              dih D e (dρ j C) p ⊳ pair (ielim D j e (fst p)) (dih D e C (snd p))
  -- tags and Σ-induction
  fcase-zʳ   : (a : RTm Γ) (b : RTm (Γ ∙)) → fcase fzero a b ⊳ a
  fcase-sʳ   : (t a : RTm Γ) (b : RTm (Γ ∙)) → fcase (fsuc t) a b ⊳ subTm (single t) b
  psplit-βʳ  : (b : RTm ((Γ ∙) ∙)) (x y : RTm Γ) → psplit b (pair x y) ⊳ subTm (single2 x y) b
  -- ★ δ: a reference is a projection from the signature, and unfolds to
  --   its body (PLAN-REF, D501).  The body is closed, so the rule is
  --   context-free; a name beyond the signature is stuck.
  δrefʳ      : {Δ : Cx} (d : ℕ) → d <ˢ Defs.size 𝒮 → ref {Δ} d ⊳ εwkTm {Δ} (Defs.body 𝒮 d)
  -- congruences
  El-⌜base⌝ʳ : El (⌜base⌝ {Γ}) ⊳ base
  El-⌜Π⌝ʳ    : (c : RTm Γ) (d : RTm (Γ ∙)) → El (⌜Π⌝ c d) ⊳ Π (El c) (El d)
  El-⌜Σ⌝ʳ    : (c : RTm Γ) (d : RTm (Γ ∙)) → El (⌜Σ⌝ c d) ⊳ Σ' (El c) (El d)
  -- W2 eliminator: the `⌜Hom⌝` code decodes to the `Hom` former
  -- (hom-sets of small types are small; still no code for `U`)
  El-⌜Hom⌝ʳ  : (c a b : RTm Γ) → El (⌜Hom⌝ c a b) ⊳ Hom (El c) a b
  El-⌜Id⌝ʳ   : (c a b : RTm Γ) → El (⌜Id⌝ c a b) ⊳ Id (El c) a b
  -- ★ stage C (N-in): the datatype codes decode.
  El-⌜Nat⌝ʳ  : El (⌜Nat⌝ {Γ}) ⊳ Nat
  El-⌜IMu⌝ʳ  : {I D i : RTm Γ} → El (⌜IMu⌝ I D i) ⊳ IMu I D i
  El-⌜Fin⌝ʳ  : {n : RTm Γ} → El (⌜Fin⌝ n) ⊳ Fin n
  -- ★★ the hypotheses' TYPE computes on the telescope head (S3).
  DIh-ιʳ : (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (p : RTm Γ) → DIh D M dι p ⊳ Unit
  DIh-σʳ : (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (S f p : RTm Γ) →
          DIh D M (dσ S f) p ⊳ DIh D M (app f (fst p)) (snd p)
  DIh-ρʳ : (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (j C p : RTm Γ) →
          DIh D M (dρ j C) p ⊳           Σ' (iinst j (fst p) M)
             (DIh (renTm vs D) (renTy (extR (extR vs)) M) (renTm vs C) (snd (renTm vs p)))
  El-⌜Unit⌝ʳ : El (⌜Unit⌝ {Γ}) ⊳ Unit
  Hom-Nat-zʳ  : (n : RTm Γ) → Hom Nat nzero n ⊳ Unit
  Hom-Nat-szʳ : (m : RTm Γ) → Hom Nat (nsuc m) nzero ⊳ base
  Hom-Nat-ssʳ : (m n : RTm Γ) → Hom Nat (nsuc m) (nsuc n) ⊳ Hom Nat m n
  Hom-Uʳ : (c d : RTm Γ) → Hom U c d ⊳ Π (El c) (El (renTm vs d))
  Hom-Πʳ : (A : RTy Γ) (B : RTy (Γ ∙)) (f g : RTm Γ) →
          Hom (Π A B) f g ⊳           Π A (Hom B (app (renTm vs f) (var vz)) (app (renTm vs g) (var vz)))

-- the generic relation at the kernel's contractions (a module alias, no
-- re-export: its two rules are pattern synonyms, the relation a definition)
module R = Red _⊳_
pattern ⟶head r = R.⟶head r
pattern ⟶cong {c} st = R.⟶cong {c = c} st

infix 3 _⟶ᴳ_
_⟶ᴳ_ : ∀ {s Γ} → G.Tm KSig s Γ → G.Tm KSig s Γ → Set
t ⟶ᴳ u = R._⟶_ t u

infix 3 _⟶_ _⟶ᵀ_
_⟶_ : {Γ : Cx} → RTm Γ → RTm Γ → Set
t ⟶ u = t ⟶ᴳ u

_⟶ᵀ_ : {Γ : Cx} → RTy Γ → RTy Γ → Set
A ⟶ᵀ B = A ⟶ᴳ B

-- the old rule names: contractions, then congruence (former, position)
pattern β t u = ⟶head (βʳ t u)
pattern βfst a b = ⟶head (βfstʳ a b)
pattern βsnd a b = ⟶head (βsndʳ a b)
pattern ξ-lam {t} {t'} r = R.⟶cong {c = Sx.`lam} {xs = (t G.,ᶠ G.⟨⟩)} {ys = (t' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-appˡ {t} {t'} {u} r = R.⟶cong {c = Sx.`app} {xs = (t G.,ᶠ u G.,ᶠ G.⟨⟩)} {ys = (t' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-appʳ {t} {u} {u'} r = R.⟶cong {c = Sx.`app} {xs = (t G.,ᶠ u G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ u' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-pairˡ {a} {a'} {b} r = R.⟶cong {c = Sx.`pair} {xs = (a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (a' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-pairʳ {a} {b} {b'} r = R.⟶cong {c = Sx.`pair} {xs = (a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ b' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ordtr-z t u p q = ⟶head (ordtr-zʳ t u p q)
pattern ordtr-szz a p q = ⟶head (ordtr-szzʳ a p q)
pattern ordtr-ssz a t p q = ⟶head (ordtr-sszʳ a t p q)
pattern ordtr-szs a u p q = ⟶head (ordtr-szsʳ a u p q)
pattern ordtr-sss a t u p q = ⟶head (ordtr-sssʳ a t u p q)
pattern ξ-ordtrᵃ {a} {a'} {t} {u} {p} {q} r = R.⟶cong {c = Sx.`ordtr} {xs = (a G.,ᶠ t G.,ᶠ u G.,ᶠ p G.,ᶠ q G.,ᶠ G.⟨⟩)} {ys = (a' G.,ᶠ _ G.,ᶠ _ G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-ordtrᵗ {a} {t} {t'} {u} {p} {q} r = R.⟶cong {c = Sx.`ordtr} {xs = (a G.,ᶠ t G.,ᶠ u G.,ᶠ p G.,ᶠ q G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ t' G.,ᶠ _ G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-ordtrᵘ {a} {t} {u} {u'} {p} {q} r = R.⟶cong {c = Sx.`ordtr} {xs = (a G.,ᶠ t G.,ᶠ u G.,ᶠ p G.,ᶠ q G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ u' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-ordtrᵖ {a} {t} {u} {p} {p'} {q} r = R.⟶cong {c = Sx.`ordtr} {xs = (a G.,ᶠ t G.,ᶠ u G.,ᶠ p G.,ᶠ q G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ _ G.,ᶠ p' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ (r , refl)))))
pattern ξ-ordtrq {a} {t} {u} {p} {q} {q'} r = R.⟶cong {c = Sx.`ordtr} {xs = (a G.,ᶠ t G.,ᶠ u G.,ᶠ p G.,ᶠ q G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ _ G.,ᶠ _ G.,ᶠ q' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))))
pattern ξ-absurdᶜ {c} {c'} {e} r = R.⟶cong {c = Sx.`absurd} {xs = (c G.,ᶠ e G.,ᶠ G.⟨⟩)} {ys = (c' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-absurdᵉ {c} {e} {e'} r = R.⟶cong {c = Sx.`absurd} {xs = (c G.,ᶠ e G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ e' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-fst {p} {p'} r = R.⟶cong {c = Sx.`fst} {xs = (p G.,ᶠ G.⟨⟩)} {ys = (p' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-snd {p} {p'} r = R.⟶cong {c = Sx.`snd} {xs = (p G.,ᶠ G.⟨⟩)} {ys = (p' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-⌜Π⌝ˡ {c} {c'} {d} r = R.⟶cong {c = Sx.`⌜Π⌝} {xs = (c G.,ᶠ d G.,ᶠ G.⟨⟩)} {ys = (c' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-⌜Π⌝ʳ {c} {d} {d'} r = R.⟶cong {c = Sx.`⌜Π⌝} {xs = (c G.,ᶠ d G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ d' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-⌜Σ⌝ˡ {c} {c'} {d} r = R.⟶cong {c = Sx.`⌜Σ⌝} {xs = (c G.,ᶠ d G.,ᶠ G.⟨⟩)} {ys = (c' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-⌜Σ⌝ʳ {c} {d} {d'} r = R.⟶cong {c = Sx.`⌜Σ⌝} {xs = (c G.,ᶠ d G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ d' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern tr-J-base c a m s e = ⟶head (tr-J-baseʳ c a m s e)
pattern tr-J-Σ c a m c₁ c₂ s e = ⟶head (tr-J-Σʳ c a m c₁ c₂ s e)
pattern tr-J-Unit c a m s e = ⟶head (tr-J-Unitʳ c a m s e)
pattern tr-J-Id c a m c₁ a₁ b₁ s e = ⟶head (tr-J-Idʳ c a m c₁ a₁ b₁ s e)
pattern tr-J-IMu {I} {D} {iˣ} c a m s e = ⟶head (tr-J-IMuʳ {I = I} {D = D} {iˣ = iˣ} c a m s e)
pattern tr-J-Fin {n} c a m s e = ⟶head (tr-J-Finʳ {n = n} c a m s e)
pattern tr-taut f e = ⟶head (tr-tautʳ f e)
pattern hrefl-pw C s h1 = ⟶head (hrefl-pwʳ C s h1)
pattern hrefl-Nat-z = ⟶head (hrefl-Nat-zʳ)
pattern hrefl-Nat-s m = ⟶head (hrefl-Nat-sʳ m)
pattern tr-J-Hom c a m c₁ a₁ b₁ s e h1 = ⟶head (tr-J-Homʳ c a m c₁ a₁ b₁ s e h1)
pattern tr-pw c a f e h1 = ⟶head (tr-pwʳ c a f e h1)
pattern ξ-⌜Hom⌝ᶜ {c} {c'} {a} {b} r = R.⟶cong {c = Sx.`⌜Hom⌝} {xs = (c G.,ᶠ a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (c' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-⌜Hom⌝ˡ {c} {a} {a'} {b} r = R.⟶cong {c = Sx.`⌜Hom⌝} {xs = (c G.,ᶠ a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ a' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-⌜Hom⌝ʳ {c} {a} {b} {b'} r = R.⟶cong {c = Sx.`⌜Hom⌝} {xs = (c G.,ᶠ a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ b' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-hreflᶜ {c} {c'} {t} r = R.⟶cong {c = Sx.`hrefl} {xs = (c G.,ᶠ t G.,ᶠ G.⟨⟩)} {ys = (c' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-hreflᵃ {c} {t} {t'} r = R.⟶cong {c = Sx.`hrefl} {xs = (c G.,ᶠ t G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ t' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-trᵈ {d} {d'} {p} {e} r = R.⟶cong {c = Sx.`tr} {xs = (d G.,ᶠ p G.,ᶠ e G.,ᶠ G.⟨⟩)} {ys = (d' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-trᵖ {d} {p} {p'} {e} r = R.⟶cong {c = Sx.`tr} {xs = (d G.,ᶠ p G.,ᶠ e G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ p' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-trᵉ {d} {p} {e} {e'} r = R.⟶cong {c = Sx.`tr} {xs = (d G.,ᶠ p G.,ᶠ e G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ e' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ap-J cB b c₁ s h1 = ⟶head (ap-Jʳ cB b c₁ s h1)
pattern ξ-apᶜ {c} {c'} {b} {p} r = R.⟶cong {c = Sx.`ap} {xs = (c G.,ᶠ b G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (c' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-apᵇ {c} {b} {b'} {p} r = R.⟶cong {c = Sx.`ap} {xs = (c G.,ᶠ b G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ b' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-apᵖ {c} {b} {p} {p'} r = R.⟶cong {c = Sx.`ap} {xs = (c G.,ᶠ b G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ p' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern jsub-refl d c s e = ⟶head (jsub-reflʳ d c s e)
pattern ξ-⌜Id⌝ᶜ {c} {c'} {a} {b} r = R.⟶cong {c = Sx.`⌜Id⌝} {xs = (c G.,ᶠ a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (c' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-⌜Id⌝ˡ {c} {a} {a'} {b} r = R.⟶cong {c = Sx.`⌜Id⌝} {xs = (c G.,ᶠ a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ a' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-⌜Id⌝ʳ {c} {a} {b} {b'} r = R.⟶cong {c = Sx.`⌜Id⌝} {xs = (c G.,ᶠ a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ b' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-⌜Fin⌝ {n} {n'} r = R.⟶cong {c = Sx.`⌜Fin⌝} {xs = (n G.,ᶠ G.⟨⟩)} {ys = (n' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-idreflᶜ {c} {c'} {t} r = R.⟶cong {c = Sx.`idrefl} {xs = (c G.,ᶠ t G.,ᶠ G.⟨⟩)} {ys = (c' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-idreflᵃ {c} {t} {t'} r = R.⟶cong {c = Sx.`idrefl} {xs = (c G.,ᶠ t G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ t' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-jsubᵈ {d} {d'} {p} {e} r = R.⟶cong {c = Sx.`jsub} {xs = (d G.,ᶠ p G.,ᶠ e G.,ᶠ G.⟨⟩)} {ys = (d' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-jsubᵖ {d} {p} {p'} {e} r = R.⟶cong {c = Sx.`jsub} {xs = (d G.,ᶠ p G.,ᶠ e G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ p' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-jsubᵉ {d} {p} {e} {e'} r = R.⟶cong {c = Sx.`jsub} {xs = (d G.,ᶠ p G.,ᶠ e G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ e' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern natrec-zero z s = ⟶head (natrec-zeroʳ z s)
pattern natrec-suc z s n = ⟶head (natrec-sucʳ z s n)
pattern ξ-nsuc {n} {n'} r = R.⟶cong {c = Sx.`nsuc} {xs = (n G.,ᶠ G.⟨⟩)} {ys = (n' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-natrecᶻ {z} {z'} {s} {n} r = R.⟶cong {c = Sx.`natrec} {xs = (z G.,ᶠ s G.,ᶠ n G.,ᶠ G.⟨⟩)} {ys = (z' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-natrecˢ {z} {s} {s'} {n} r = R.⟶cong {c = Sx.`natrec} {xs = (z G.,ᶠ s G.,ᶠ n G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ s' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-natrecⁿ {z} {s} {n} {n'} r = R.⟶cong {c = Sx.`natrec} {xs = (z G.,ᶠ s G.,ᶠ n G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ n' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ι D i e p = ⟶head (ιʳ D i e p)
pattern dpay-ι I D = ⟶head (dpay-ιʳ I D)
pattern dpay-σ I D S f = ⟶head (dpay-σʳ I D S f)
pattern dpay-ρ I D j C = ⟶head (dpay-ρʳ I D j C)
pattern dih-ι D e p = ⟶head (dih-ιʳ D e p)
pattern dih-σ D e S f p = ⟶head (dih-σʳ D e S f p)
pattern dih-ρ D e j C p = ⟶head (dih-ρʳ D e j C p)
pattern fcase-z a b = ⟶head (fcase-zʳ a b)
pattern fcase-s t a b = ⟶head (fcase-sʳ t a b)
pattern psplit-β b x y = ⟶head (psplit-βʳ b x y)
pattern δref {Δ} d h1 = ⟶head (δrefʳ {Δ = Δ} d h1)
pattern ξ-⌜IMu⌝ᴵ {I} {I'} {D} {i} r = R.⟶cong {c = Sx.`⌜IMu⌝} {xs = (I G.,ᶠ D G.,ᶠ i G.,ᶠ G.⟨⟩)} {ys = (I' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-⌜IMu⌝ᴰ {I} {D} {D'} {i} r = R.⟶cong {c = Sx.`⌜IMu⌝} {xs = (I G.,ᶠ D G.,ᶠ i G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ D' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-⌜IMu⌝ⁱ {I} {D} {i} {i'} r = R.⟶cong {c = Sx.`⌜IMu⌝} {xs = (I G.,ᶠ D G.,ᶠ i G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ i' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-con {p} {p'} r = R.⟶cong {c = Sx.`con} {xs = (p G.,ᶠ G.⟨⟩)} {ys = (p' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-ielimᴰ {D} {D'} {i} {e} {t} r = R.⟶cong {c = Sx.`ielim} {xs = (D G.,ᶠ i G.,ᶠ e G.,ᶠ t G.,ᶠ G.⟨⟩)} {ys = (D' G.,ᶠ _ G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-ielimⁱ {D} {i} {i'} {e} {t} r = R.⟶cong {c = Sx.`ielim} {xs = (D G.,ᶠ i G.,ᶠ e G.,ᶠ t G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ i' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-ielimᵉ {D} {i} {e} {e'} {t} r = R.⟶cong {c = Sx.`ielim} {xs = (D G.,ᶠ i G.,ᶠ e G.,ᶠ t G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ e' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-ielimᵗ {D} {i} {e} {t} {t'} r = R.⟶cong {c = Sx.`ielim} {xs = (D G.,ᶠ i G.,ᶠ e G.,ᶠ t G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ _ G.,ᶠ t' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ (r , refl)))))
pattern ξ-dσˢ {S} {S'} {f} r = R.⟶cong {c = Sx.`dσ} {xs = (S G.,ᶠ f G.,ᶠ G.⟨⟩)} {ys = (S' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-dσᶠ {S} {f} {f'} r = R.⟶cong {c = Sx.`dσ} {xs = (S G.,ᶠ f G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ f' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-dρʲ {j} {j'} {C} r = R.⟶cong {c = Sx.`dρ} {xs = (j G.,ᶠ C G.,ᶠ G.⟨⟩)} {ys = (j' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-dρᶜ {j} {C} {C'} r = R.⟶cong {c = Sx.`dρ} {xs = (j G.,ᶠ C G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ C' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-dpayᴵ {I} {I'} {D} {C} r = R.⟶cong {c = Sx.`dpay} {xs = (I G.,ᶠ D G.,ᶠ C G.,ᶠ G.⟨⟩)} {ys = (I' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-dpayᴰ {I} {D} {D'} {C} r = R.⟶cong {c = Sx.`dpay} {xs = (I G.,ᶠ D G.,ᶠ C G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ D' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-dpayᶜ {I} {D} {C} {C'} r = R.⟶cong {c = Sx.`dpay} {xs = (I G.,ᶠ D G.,ᶠ C G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ C' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-dihᴰ {D} {D'} {e} {C} {p} r = R.⟶cong {c = Sx.`dih} {xs = (D G.,ᶠ e G.,ᶠ C G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (D' G.,ᶠ _ G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-dihᵉ {D} {e} {e'} {C} {p} r = R.⟶cong {c = Sx.`dih} {xs = (D G.,ᶠ e G.,ᶠ C G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ e' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-dihᶜ {D} {e} {C} {C'} {p} r = R.⟶cong {c = Sx.`dih} {xs = (D G.,ᶠ e G.,ᶠ C G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ C' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-dihᵖ {D} {e} {C} {p} {p'} r = R.⟶cong {c = Sx.`dih} {xs = (D G.,ᶠ e G.,ᶠ C G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ _ G.,ᶠ p' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ (r , refl)))))
pattern ξ-fsuc {t} {t'} r = R.⟶cong {c = Sx.`fsuc} {xs = (t G.,ᶠ G.⟨⟩)} {ys = (t' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-fcaseᵗ {t} {t'} {a} {b} r = R.⟶cong {c = Sx.`fcase} {xs = (t G.,ᶠ a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (t' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-fcaseᵃ {t} {a} {a'} {b} r = R.⟶cong {c = Sx.`fcase} {xs = (t G.,ᶠ a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ a' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-fcaseᵇ {t} {a} {b} {b'} r = R.⟶cong {c = Sx.`fcase} {xs = (t G.,ᶠ a G.,ᶠ b G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ b' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-fcase0 {t} {t'} r = R.⟶cong {c = Sx.`fcase0} {xs = (t G.,ᶠ G.⟨⟩)} {ys = (t' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-psplitᵇ {b} {b'} {q} r = R.⟶cong {c = Sx.`psplit} {xs = (b G.,ᶠ q G.,ᶠ G.⟨⟩)} {ys = (b' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-psplitᵍ {b} {q} {q'} r = R.⟶cong {c = Sx.`psplit} {xs = (b G.,ᶠ q G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ q' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern El-⌜base⌝ = ⟶head (El-⌜base⌝ʳ)
pattern El-⌜Π⌝ c d = ⟶head (El-⌜Π⌝ʳ c d)
pattern El-⌜Σ⌝ c d = ⟶head (El-⌜Σ⌝ʳ c d)
pattern El-⌜Hom⌝ c a b = ⟶head (El-⌜Hom⌝ʳ c a b)
pattern El-⌜Id⌝ c a b = ⟶head (El-⌜Id⌝ʳ c a b)
pattern El-⌜Nat⌝ = ⟶head (El-⌜Nat⌝ʳ)
pattern El-⌜IMu⌝ {I} {D} {i} = ⟶head (El-⌜IMu⌝ʳ {I = I} {D = D} {i = i})
pattern El-⌜Fin⌝ {n} = ⟶head (El-⌜Fin⌝ʳ {n = n})
pattern DIh-ι D M p = ⟶head (DIh-ιʳ D M p)
pattern DIh-σ D M S f p = ⟶head (DIh-σʳ D M S f p)
pattern DIh-ρ D M j C p = ⟶head (DIh-ρʳ D M j C p)
pattern El-⌜Unit⌝ = ⟶head (El-⌜Unit⌝ʳ)
pattern ξ-El {t} {t'} r = R.⟶cong {c = Sx.`El} {xs = (t G.,ᶠ G.⟨⟩)} {ys = (t' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-Πˡ {A} {A'} {B} r = R.⟶cong {c = Sx.`Π} {xs = (A G.,ᶠ B G.,ᶠ G.⟨⟩)} {ys = (A' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-Πʳ {A} {B} {B'} r = R.⟶cong {c = Sx.`Π} {xs = (A G.,ᶠ B G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ B' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-Σˡ {A} {A'} {B} r = R.⟶cong {c = Sx.`Σ'} {xs = (A G.,ᶠ B G.,ᶠ G.⟨⟩)} {ys = (A' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-Σʳ {A} {B} {B'} r = R.⟶cong {c = Sx.`Σ'} {xs = (A G.,ᶠ B G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ B' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern Hom-Nat-z n = ⟶head (Hom-Nat-zʳ n)
pattern Hom-Nat-sz m = ⟶head (Hom-Nat-szʳ m)
pattern Hom-Nat-ss m n = ⟶head (Hom-Nat-ssʳ m n)
pattern Hom-U c d = ⟶head (Hom-Uʳ c d)
pattern Hom-Π A B f g = ⟶head (Hom-Πʳ A B f g)
pattern ξ-Homᵀ {A} {A'} {t} {u} r = R.⟶cong {c = Sx.`Hom} {xs = (A G.,ᶠ t G.,ᶠ u G.,ᶠ G.⟨⟩)} {ys = (A' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-Homˡ {A} {t} {t'} {u} r = R.⟶cong {c = Sx.`Hom} {xs = (A G.,ᶠ t G.,ᶠ u G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ t' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-Homʳ {A} {t} {u} {u'} r = R.⟶cong {c = Sx.`Hom} {xs = (A G.,ᶠ t G.,ᶠ u G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ u' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-Idᵀ {A} {A'} {t} {u} r = R.⟶cong {c = Sx.`Id} {xs = (A G.,ᶠ t G.,ᶠ u G.,ᶠ G.⟨⟩)} {ys = (A' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-Idˡ {A} {t} {t'} {u} r = R.⟶cong {c = Sx.`Id} {xs = (A G.,ᶠ t G.,ᶠ u G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ t' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-Idʳ {A} {t} {u} {u'} r = R.⟶cong {c = Sx.`Id} {xs = (A G.,ᶠ t G.,ᶠ u G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ u' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-IMuᴵ {I} {I'} {D} {i} r = R.⟶cong {c = Sx.`IMu} {xs = (I G.,ᶠ D G.,ᶠ i G.,ᶠ G.⟨⟩)} {ys = (I' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-IMuᴰ {I} {D} {D'} {i} r = R.⟶cong {c = Sx.`IMu} {xs = (I G.,ᶠ D G.,ᶠ i G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ D' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-IMuⁱ {I} {D} {i} {i'} r = R.⟶cong {c = Sx.`IMu} {xs = (I G.,ᶠ D G.,ᶠ i G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ i' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-Desc {I} {I'} r = R.⟶cong {c = Sx.`Desc} {xs = (I G.,ᶠ G.⟨⟩)} {ys = (I' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-Fin {n} {n'} r = R.⟶cong {c = Sx.`Fin} {xs = (n G.,ᶠ G.⟨⟩)} {ys = (n' G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-DIhᴰ {D} {D'} {C} {p} {M} r = R.⟶cong {c = Sx.`DIh} {xs = (D G.,ᶠ M G.,ᶠ C G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (D' G.,ᶠ _ G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₁ (r , refl))
pattern ξ-DIhᴹ {D} {C} {p} {M} {M'} r = R.⟶cong {c = Sx.`DIh} {xs = (D G.,ᶠ M G.,ᶠ C G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ M' G.,ᶠ _ G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₁ (r , refl)))
pattern ξ-DIhᶜ {D} {C} {C'} {p} {M} r = R.⟶cong {c = Sx.`DIh} {xs = (D G.,ᶠ M G.,ᶠ C G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ C' G.,ᶠ _ G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₁ (r , refl))))
pattern ξ-DIhᵖ {D} {C} {p} {p'} {M} r = R.⟶cong {c = Sx.`DIh} {xs = (D G.,ᶠ M G.,ᶠ C G.,ᶠ p G.,ᶠ G.⟨⟩)} {ys = (_ G.,ᶠ _ G.,ᶠ _ G.,ᶠ p' G.,ᶠ G.⟨⟩)} (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ (r , refl)))))

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

