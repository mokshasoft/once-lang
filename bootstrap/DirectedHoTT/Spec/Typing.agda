------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 21 — INTRINSIC TYPING + CONVERSION over the dependent
--                            de Bruijn base: `Id = core(Hom)` as the conv rule
--
-- The next slice after the experiment (`NbEPDirDBPi`, dHoTT-20 — which settled
-- that dependent Π/Σ substitution is strictly stable). Here the RAW dependent
-- syntax becomes a CHECKED kernel: a typing judgment with the CONVERSION rule,
-- where the definitional equality IS the design's `core(Hom)` — the symmetric
-- completion of the directed reduction `Hom = ⟶*`.
--
--   * `_⟶_` / `_⟶ᵀ_` — β-reduction on terms and its congruence onto types
--     (through `El`/`Π`/`Σ`). `Hom = _⟶*_` is the directed identity type (as
--     in every prior rung); `Core t u = Hom t u × Hom u t` its groupoid core.
--   * `_≅_` / `_≅ᵀ_` — CONVERSION = the reflexive-symmetric-transitive closure
--     of reduction: the definitional equality a typechecker uses. `hom→≅` and
--     `core→≅` witness that it is exactly the symmetric completion of `Hom`,
--     i.e. `Id = core(Hom)` made operational (the relation NbE decides).
--   * `Ctx` / `_∋_∷_` / `_⊢_∷_` — typed contexts, variable typing, and the
--     TYPING JUDGMENT: `⊢var`, `⊢lam`, DEPENDENT `⊢app` (the codomain is
--     substituted, `app t u ∷ B[u]`), and the load-bearing `⊢conv`
--     (`Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B`) — conversion entering typing.
--   * Concrete: `⊢id` (`◇ ⊢ λx.x ∷ Π base base`), a dependent-app derivation,
--     and `conv-El` — a term re-typed across a β-computation in its type, the
--     conversion rule doing real work.
--
-- Honest ceiling: this is a DECLARATIVE kernel — the typing/conversion rules,
-- with `Id = core(Hom)` as definitional equality, on the strict-substitution
-- dependent base. The metatheory (subject reduction, and DECIDING `≅ᵀ` by the
-- NbE engine — the "decided by NbE" half of the design) is the next slice; the
-- substitution machinery it needs is already proven in `NbEPDirDBPi`.
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Typing where
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
        ; fzero; fsuc; fcase; fcase0; psplit )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; occTm; pw?; stkC?; stkA?; flat?; pwBody; pwShift
        ; NoNatC; nnc-base; nnc-Unit; nnc-Π; nnc-Σ; nnc-Hom; nnc-Id )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Single substitution (what β and dependent `app` plug in).
------------------------------------------------------------------------

single : RTm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x


-- ★ A `single` CANCELS A WEAKENING.  Two lines, used ~60 times across the
--   tree.  Lives HERE because `single` does; its other two ingredients
--   (`subTm-renTm`, `subTm-id`) are in `…Pi`.
--
-- ⚠ IT LIVED IN `…LR` — the 6269-line logical relation — until 2026-08-19,
--   because that is where it was first needed.  ⚠ THE PROBLEM IS NOT that a
--   library depended on metatheory: SN and canonicity ARE properties of the
--   kernel and a library may legitimately depend on them.  The problem is
--   that `wk-single` is not metatheory at all — it is SYNTAX, and reaching
--   into the normalisation proof to fetch it makes every user pay for a
--   6000-line development to get two lines.  `…LR` re-exports it, so its
--   ~50 importers are unaffected.
wk-single : {Γ : Cx} {v : RTm Γ} (t : RTm Γ) →
            subTm (single v) (renTm vs t) ≡ t
wk-single t = trans (subTm-renTm t) (subTm-id t)
-- ★ WF-axis stage A: the successor-instance substitution — reads the
-- motive M (over Γ, number) at `nsuc` of the number, in the recursor's
-- step context (Γ, number, IH).
nrs : Sub (Γ ∙) ((Γ ∙) ∙)
nrs vz     = nsuc (var (vs vz))
nrs (vs x) = var (vs (vs x))

-- ★ the two-binder instantiation `psplit`'s rule plugs in: the inner
--   binder gets `y`, the outer `x`.
single2 : RTm Γ → RTm Γ → Sub ((Γ ∙) ∙) Γ
single2 x y vz          = y
single2 x y (vs vz)     = x
single2 x y (vs (vs x')) = var x'

-- ★ `psplit`'s motive re-based at the two halves, and `fcase`'s at a
--   successor tag.
pairS : Sub (Γ ∙) ((Γ ∙) ∙)
pairS vz     = pair (var (vs vz)) (var vz)
pairS (vs x) = var (vs (vs x))

fsucS : Sub (Γ ∙) (Γ ∙)
fsucS vz     = fsuc (var vz)
fsucS (vs x) = var (vs x)

------------------------------------------------------------------------
-- ★★ THE ELIMINATOR'S TYPES (levitated, one-telescope form).
--
-- ⚠ THE MOTIVE IS TWO-SLOT: `M : RTy ((Γ ∙) ∙)`, a family over the INDEX
--   (outer) and the SCRUTINEE (inner).
------------------------------------------------------------------------

-- instantiate the two-slot motive at index `j` and scrutinee `t`
iinst : RTm Γ → RTm Γ → RTy ((Γ ∙) ∙) → RTy Γ
iinst j t M = subTy (single t) (subTy (extS (single j)) M)

-- the motive, after the method's three binders (i, p, h), at index `i`
--   and scrutinee `con p`
methS : Sub ((Γ ∙) ∙) (((Γ ∙) ∙) ∙)
methS vz          = con (var (vs vz))
methS (vs vz)     = var (vs (vs vz))
methS (vs (vs x)) = var (vs (vs (vs x)))

-- the base context weakened past two binders, the motive's own two kept
wk2M : RTy ((Γ ∙) ∙) → RTy ((((Γ ∙) ∙) ∙) ∙)
wk2M M = renTy (extR (extR (λ x → vs (vs x)))) M

-- ★★ THE ONE METHOD (SPIKE-LEVITATION S3/S4): at every index `i`, for the
--   payload `p` of the WHOLE telescope and its hypotheses `h`, the motive
--   at `con p`.  The payload is passed WHOLE — no η (gate 5c).
MethTy : RTm Γ → RTm Γ → RTy ((Γ ∙) ∙) → RTy Γ
MethTy I D M =
  Π (El I)
    (Π (El (dpay (renTm vs I) (renTm vs D) (renTm vs D) (var vz)))
       (Π (DIh (renTm vs (renTm vs D)) (wk2M M) (renTm vs (renTm vs D)) (var vz))
          (subTy methS M)))

-- The top-two-variable SWAP renaming — what `tr-pw` uses to move the
-- `⌜Π⌝`-codomain code under the new lambda: the Π-binder becomes the new
-- outer variable, the (necessarily absent, per `PosC`) old transported
-- variable maps onto the new one.  A RENAMING, not a substitution — the
-- commutation lemmas downstream stay in the renaming fragment.
swp : Ren ((Γ ∙) ∙) ((Γ ∙) ∙)
swp vz          = vs vz
swp (vs vz)     = vz
swp (vs (vs x)) = vs (vs x)

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
  tr-J-Fin  : {n : ℕ} (c a m : RTm (Γ ∙)) (s e : RTm Γ) →
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
              ielim D i e (con p) ⟶ app (app (app e i) p) (dih D e D p)
  -- the payload CODE of a telescope: the index EQUATION at `dι j`
  --   (Fording: a constructor exists at every index, the bad ones are
  --   uninhabitable), a Σ at `dσ`, a Σ over the family at `dρ`.
  dpay-ι    : (I D j i : RTm Γ) → dpay I D (dι j) i ⟶ ⌜Id⌝ I j i
  dpay-σ    : (I D S f i : RTm Γ) →
              dpay I D (dσ S f) i ⟶
              ⌜Σ⌝ S (dpay (renTm vs I) (renTm vs D) (app (renTm vs f) (var vz)) (renTm vs i))
  dpay-ρ    : (I D j C i : RTm Γ) →
              dpay I D (dρ j C) i ⟶
              ⌜Σ⌝ (⌜IMu⌝ I D j) (dpay (renTm vs I) (renTm vs D) (renTm vs C) (renTm vs i))
  -- the hypotheses: one recursive call per `dρ`, AT ITS OWN INDEX `j`
  dih-ι     : (D e j p : RTm Γ) → dih D e (dι j) p ⟶ unit
  dih-σ     : (D e S f p : RTm Γ) → dih D e (dσ S f) p ⟶ dih D e (app f (fst p)) (snd p)
  dih-ρ     : (D e j C p : RTm Γ) →
              dih D e (dρ j C) p ⟶ pair (ielim D j e (fst p)) (dih D e C (snd p))
  -- tags and Σ-induction
  fcase-z   : (a : RTm Γ) (b : RTm (Γ ∙)) → fcase fzero a b ⟶ a
  fcase-s   : (t a : RTm Γ) (b : RTm (Γ ∙)) → fcase (fsuc t) a b ⟶ subTm (single t) b
  psplit-β  : (b : RTm ((Γ ∙) ∙)) (x y : RTm Γ) → psplit b (pair x y) ⟶ subTm (single2 x y) b
  -- congruences
  ξ-⌜IMu⌝ᴵ  : {I I' D i : RTm Γ} → I ⟶ I' → ⌜IMu⌝ I D i ⟶ ⌜IMu⌝ I' D i
  ξ-⌜IMu⌝ᴰ  : {I D D' i : RTm Γ} → D ⟶ D' → ⌜IMu⌝ I D i ⟶ ⌜IMu⌝ I D' i
  ξ-⌜IMu⌝ⁱ  : {I D i i' : RTm Γ} → i ⟶ i' → ⌜IMu⌝ I D i ⟶ ⌜IMu⌝ I D i'
  ξ-con     : {p p' : RTm Γ} → p ⟶ p' → con p ⟶ con p'
  ξ-ielimᴰ  : {D D' i e t : RTm Γ} → D ⟶ D' → ielim D i e t ⟶ ielim D' i e t
  ξ-ielimⁱ  : {D i i' e t : RTm Γ} → i ⟶ i' → ielim D i e t ⟶ ielim D i' e t
  ξ-ielimᵉ  : {D i e e' t : RTm Γ} → e ⟶ e' → ielim D i e t ⟶ ielim D i e' t
  ξ-ielimᵗ  : {D i e t t' : RTm Γ} → t ⟶ t' → ielim D i e t ⟶ ielim D i e t'
  ξ-dι      : {j j' : RTm Γ} → j ⟶ j' → dι j ⟶ dι j'
  ξ-dσˢ     : {S S' f : RTm Γ} → S ⟶ S' → dσ S f ⟶ dσ S' f
  ξ-dσᶠ     : {S f f' : RTm Γ} → f ⟶ f' → dσ S f ⟶ dσ S f'
  ξ-dρʲ     : {j j' C : RTm Γ} → j ⟶ j' → dρ j C ⟶ dρ j' C
  ξ-dρᶜ     : {j C C' : RTm Γ} → C ⟶ C' → dρ j C ⟶ dρ j C'
  ξ-dpayᴵ   : {I I' D C i : RTm Γ} → I ⟶ I' → dpay I D C i ⟶ dpay I' D C i
  ξ-dpayᴰ   : {I D D' C i : RTm Γ} → D ⟶ D' → dpay I D C i ⟶ dpay I D' C i
  ξ-dpayᶜ   : {I D C C' i : RTm Γ} → C ⟶ C' → dpay I D C i ⟶ dpay I D C' i
  ξ-dpayⁱ   : {I D C i i' : RTm Γ} → i ⟶ i' → dpay I D C i ⟶ dpay I D C i'
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
  El-⌜Fin⌝  : {n : ℕ} → El (⌜Fin⌝ {Γ} n) ⟶ᵀ Fin n
  -- ★★ the hypotheses' TYPE computes on the telescope head (S3).
  DIh-ι : (D : RTm Γ) (M : RTy ((Γ ∙) ∙)) (j p : RTm Γ) → DIh D M (dι j) p ⟶ᵀ Unit
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

infixr 4 _,,_
record _×_ (P Q : Set) : Set where
  constructor _,,_
  field π₁ : P
        π₂ : Q

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

------------------------------------------------------------------------
-- Typed contexts (telescopes of types) and their underlying de Bruijn depth.
------------------------------------------------------------------------

data Ctx : Set
⌊_⌋ : Ctx → Cx

data Ctx where
  ◇   : Ctx
  _▹_ : (Γ : Ctx) → RTy ⌊ Γ ⌋ → Ctx

⌊ ◇ ⌋     = ε
⌊ Γ ▹ A ⌋ = ⌊ Γ ⌋ ∙

------------------------------------------------------------------------
-- Variable typing (looked-up types are weakened into the deeper context).
------------------------------------------------------------------------

infix 3 _∋_∷_
data _∋_∷_ : (Γ : Ctx) → Var ⌊ Γ ⌋ → RTy ⌊ Γ ⌋ → Set where
  here  : ∀ {Γ} {A : RTy ⌊ Γ ⌋} → (Γ ▹ A) ∋ vz ∷ renTy vs A
  there : ∀ {Γ} {A B : RTy ⌊ Γ ⌋} {x} →
          Γ ∋ x ∷ A → (Γ ▹ B) ∋ vs x ∷ renTy vs A

------------------------------------------------------------------------
-- THE TYPING JUDGMENT — dependent `app`, and the conversion rule.
------------------------------------------------------------------------

-- TYPE FORMATION, mutual with term typing (2026-07-30, "option A").
--
-- WHY IT EXISTS. Without it the judgment derives terms at MEANINGLESS types:
-- `El (lam (var vz))` is a normal type whose code is neither a constructor nor
-- neutral, so it has no semantic counterpart, yet `⊢lam` would happily type
-- `λx.t ∷ Π (El (lam y)) B`. That makes a normalization theorem for `_⊢_∷_`
-- unprovable (`NbEPDirDBLR`; the counterexample is `SpikeSNK.¬⊩elLam`). Not an
-- inconsistency — a well-formedness defect, and this closes it.
--
-- ⚠ MINIMAL BY DESIGN: only `⊢lam` and `⊢pair` gain a premise. Everywhere else
-- the type is recovered from the subderivations by syntactic validity —
-- `⊢app`'s `Π A B` comes from the IH on the function and `⊢ty` is invertible at
-- `Π`, `⊢fst`/`⊢snd` likewise at `Σ'`, and `⊢⌜Π⌝`/`⊢⌜Σ⌝` conclude at `U`, which
-- is well-formed outright. Adding premises those rules do not need would cost
-- cascade for nothing.
infix 3 _⊢_∷_
infix 3 _⊢ty_
data _⊢_∷_ : (Γ : Ctx) → RTm ⌊ Γ ⌋ → RTy ⌊ Γ ⌋ → Set
data _⊢ty_ : (Γ : Ctx) → RTy ⌊ Γ ⌋ → Set
-- ★★ LEVITATION: there is NO description well-formedness judgment.  A
--   description is a TERM of `Desc I`, and its well-formedness is ordinary
--   typing (`⊢dι`/`⊢dσ`/`⊢dρ`).  `DescWf`/`DConWf`/`IConWf`/`IDescWfFrom`/
--   `ICodeWf`/`IDescWf` are gone (PLAN-LEVITATION; A-math's content — a
--   telescope typed with no family in scope — is now the grammar).

-- the motive's context: index, then scrutinee
motCtx : (Γ : Ctx) → RTm ⌊ Γ ⌋ → RTm ⌊ Γ ⌋ → Ctx
motCtx Γ I D = (Γ ▹ El I) ▹ IMu (renTm vs I) (renTm vs D) (var vz)

data _⊢_∷_ where
  ⊢var  : ∀ {Γ x A}     → Γ ∋ x ∷ A → Γ ⊢ var x ∷ A
  ⊢lam  : ∀ {Γ A B t}   → Γ ⊢ty A → (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Π A B
  ⊢app  : ∀ {Γ A B t u} → Γ ⊢ t ∷ Π A B → Γ ⊢ u ∷ A →
                          Γ ⊢ app t u ∷ subTy (single u) B
  ⊢pair : ∀ {Γ A B a b} → (Γ ▹ A) ⊢ty B →
                          Γ ⊢ a ∷ A → Γ ⊢ b ∷ subTy (single a) B →
                          Γ ⊢ pair a b ∷ Σ' A B
  -- ★★ WF-axis stage D: `base` finally gets an ELIMINATOR.  It had
  -- formation only, so a false inequality COMPUTED to the empty type
  -- (`Hom Nat (nsuc m) nzero ⟶ᵀ base`) but the impossible branch could
  -- be discharged only meta-theoretically.  This is what strong
  -- induction needs to be written INSIDE the language.
  --
  -- The result type lives in the derivation (the `⊢lam`/`⊢natrec`
  -- motive pattern), so `absurd e` inhabits every well-formed type.
  -- Consistency is untouched: `base` still has no closed inhabitant, so
  -- no CLOSED `absurd e` exists either.
  -- The result type is carried as a CODE, exactly as `⊢hrefl`/`⊢ap` do:
  -- that makes the type DETERMINED (`El c`) and the inversion
  -- `gen-absurd` straightforward.  A `⊢ty C` premise cannot work here —
  -- it is about the RESULT type, which `⊢conv` changes, so the
  -- inversion could never rebuild it.
  ⊢absurd : ∀ {Γ c e} → Γ ⊢ c ∷ U → Γ ⊢ e ∷ base → Γ ⊢ absurd c e ∷ El c
  -- ★★ ORDER TRANSPORT: composition of order proofs, i.e. ≤-transitivity.
  ⊢ordtr : ∀ {Γ a t u p q} →
           Γ ⊢ a ∷ Nat → Γ ⊢ t ∷ Nat → Γ ⊢ u ∷ Nat →
           Γ ⊢ p ∷ Hom Nat a t → Γ ⊢ q ∷ Hom Nat t u →
           Γ ⊢ ordtr a t u p q ∷ Hom Nat a u
  ⊢fst  : ∀ {Γ A B p}   → Γ ⊢ p ∷ Σ' A B → Γ ⊢ fst p ∷ A
  ⊢snd  : ∀ {Γ A B p}   → Γ ⊢ p ∷ Σ' A B →
                          Γ ⊢ snd p ∷ subTy (single (fst p)) B
  ⊢⌜base⌝ : ∀ {Γ}       → Γ ⊢ ⌜base⌝ ∷ U
  ⊢⌜Π⌝  : ∀ {Γ c d}     → Γ ⊢ c ∷ U → (Γ ▹ El c) ⊢ d ∷ U → Γ ⊢ ⌜Π⌝ c d ∷ U
  ⊢⌜Σ⌝  : ∀ {Γ c d}     → Γ ⊢ c ∷ U → (Γ ▹ El c) ⊢ d ∷ U → Γ ⊢ ⌜Σ⌝ c d ∷ U
  -- ★ W2 eliminator (SpikeHomRefl + SpikeTr + SpikeTrLR).  `⊢⌜Hom⌝` and
  -- `⊢hrefl` join the kernel judgment, and — stage 2 — so does `⊢tr` AT
  -- THE COMPOSITION MOTIVE, its shape pinned in the rule (`posc-Hom`'s
  -- content inlined as the two vz-freeness premises) with ENDPOINT
  -- premises (the `⊢lam` option-A pattern: `sr` never needed them,
  -- `fund` does).  Stage 3 merged the TAUTOLOGICAL motive too (`⊢trU`
  -- below): re-keying J on `⌜Hom⌝`-headed motives made the taut
  -- J-configurations permanently stuck, dissolving SpikeTrLR's
  -- obstruction (its J-branches ceased to exist).
  ⊢⌜Hom⌝ : ∀ {Γ c a b}  → Γ ⊢ c ∷ U → Γ ⊢ a ∷ El c → Γ ⊢ b ∷ El c →
                          Γ ⊢ ⌜Hom⌝ c a b ∷ U
  ⊢hrefl : ∀ {Γ c t}    → Γ ⊢ c ∷ U → Γ ⊢ t ∷ El c →
                          Γ ⊢ hrefl c t ∷ Hom (El c) t t
  -- (the motive's `⊢⌜Hom⌝` premise is carried COMPONENTWISE so `fund`'s
  -- recursion stays structural)
  -- …and the TAUTOLOGICAL motive, ambient pinned to `U` (a merely
  -- convertible ambient reaches this rule through `⊢conv` on the path —
  -- conversion is a `Hom`-congruence).  Transport along a universe path
  -- is application: directed univalence, in the kernel judgment.
  ⊢trU  : ∀ {Γ p e t u} →
          Γ ⊢ t ∷ U → Γ ⊢ u ∷ U →
          Γ ⊢ p ∷ Hom U t u → Γ ⊢ e ∷ El t →
          Γ ⊢ tr (var vz) p e ∷ El u
  -- ★★ WF stage C: the motive code is RESTRICTED to non-⌜Nat⌝ heads.
  -- `tr` is hom-composition — the fibre over `x` is `Hom (El c) a x`,
  -- so transport along `p : Hom A t u` is ≤-transitivity at a `Nat`
  -- ambient.  The right answer there depends on the path's ENDPOINTS
  -- `t`/`u`, which never occur in the term `tr d p e` (only in this
  -- derivation), so no reduction rule can case on them; and every
  -- endpoint-blind rule dies to the same counterexample that killed
  -- `tr-J-Nat` (SPIKE-WF.md §7).  `tr` is J-shaped — path-keyed and
  -- endpoint-blind — so an ordered ambient is something it structurally
  -- cannot serve.  Order transport is the separate `ordtr` former; see
  -- ARCHITECTURE.md's ORDER TRANSPORT entry for its worked case tree.
  -- ★ The premise PAYS FOR ITSELF twice in `NbEPDirDBCanon`:
  -- `trProgress`'s ⌜Nat⌝ case is refuted on it, and `tr-amb-nonat` —
  -- whose old `elNat⊥` proof stage C made FALSE — gets its `{A = Nat}`
  -- case from it.
  ⊢tr   : ∀ {Γ A c a p e t u} →
          (Γ ▹ A) ⊢ c ∷ U → (Γ ▹ A) ⊢ a ∷ El c →
          (Γ ▹ A) ⊢ var vz ∷ El c →
          NoNatC c →
          occTm vz c ≡ false → occTm vz a ≡ false →
          Γ ⊢ t ∷ A → Γ ⊢ u ∷ A →
          Γ ⊢ p ∷ Hom A t u →
          Γ ⊢ e ∷ El (subTm (single t) (⌜Hom⌝ c a (var vz))) →
          Γ ⊢ tr (⌜Hom⌝ c a (var vz)) p e
            ∷ El (subTm (single u) (⌜Hom⌝ c a (var vz)))
  -- ★ directed `ap` (SpikeAp): a term's action on a hom.  The SOURCE
  -- ambient is pinned to a STABLE code (`stkC?`, substitution-stable),
  -- which makes `ap-J` complete for closed canonicity (SpikeAp's
  -- keystone); the TARGET code `cB` annotates the result reflexivity.
  -- Endpoint premises follow the `⊢lam` option-A pattern.
  ⊢ap   : ∀ {Γ cA cB b p t u} →
          Γ ⊢ cA ∷ U → flat? cA ≡ true →
          Γ ⊢ cB ∷ U →
          (Γ ▹ El cA) ⊢ b ∷ El (renTm vs cB) →
          Γ ⊢ t ∷ El cA → Γ ⊢ u ∷ El cA →
          Γ ⊢ p ∷ Hom (El cA) t u →
          Γ ⊢ ap cB b p ∷ Hom (El cB) (subTm (single t) b) (subTm (single u) b)
  ⊢⌜Id⌝ : ∀ {Γ c a b}   → Γ ⊢ c ∷ U → Γ ⊢ a ∷ El c → Γ ⊢ b ∷ El c →
                          Γ ⊢ ⌜Id⌝ c a b ∷ U
  -- ★ stage C: `Nat` and `Unit` are SMALL.
  ⊢⌜Nat⌝  : ∀ {Γ} → Γ ⊢ ⌜Nat⌝ {⌊ Γ ⌋} ∷ U
  -- ★ the family's CODE: families are small (nesting, `amrec` carriers).
  -- the code CONTAINS its index code, so it types it (as every former
  --   types each term it contains — SN of the code needs SN of `I`).
  ⊢⌜IMu⌝  : ∀ {Γ I D i} → Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → Γ ⊢ i ∷ El I → Γ ⊢ ⌜IMu⌝ I D i ∷ U
  ⊢⌜Fin⌝  : ∀ {Γ n} → Γ ⊢ ⌜Fin⌝ {⌊ Γ ⌋} n ∷ U
  ⊢⌜Unit⌝ : ∀ {Γ} → Γ ⊢ ⌜Unit⌝ {⌊ Γ ⌋} ∷ U
  ⊢idrefl : ∀ {Γ c t}   → Γ ⊢ c ∷ U → Γ ⊢ t ∷ El c →
                          Γ ⊢ idrefl c t ∷ Id (El c) t t
  ⊢jsub : ∀ {Γ A d t u p e} →
          (Γ ▹ A) ⊢ d ∷ U →
          Γ ⊢ t ∷ A → Γ ⊢ u ∷ A →
          Γ ⊢ p ∷ Id A t u →
          Γ ⊢ e ∷ El (subTm (single t) d) →
          Γ ⊢ jsub d p e ∷ El (subTm (single u) d)
  -- ★ WF-axis stage A: unit, numerals, and the TYPE-motived recursor.
  -- The motive lives in the DERIVATION only (the ⊢lam pattern) — code
  -- motives would need ⌜Nat⌝ ∈ U, which is stage C.
  ⊢unit   : ∀ {Γ}     → Γ ⊢ unit ∷ Unit
  ⊢nzero  : ∀ {Γ}     → Γ ⊢ nzero ∷ Nat
  ⊢nsuc   : ∀ {Γ n}   → Γ ⊢ n ∷ Nat → Γ ⊢ nsuc n ∷ Nat
  ⊢natrec : ∀ {Γ M z s n} →
            (Γ ▹ Nat) ⊢ty M →
            Γ ⊢ z ∷ subTy (single nzero) M →
            ((Γ ▹ Nat) ▹ M) ⊢ s ∷ subTy nrs M →
            Γ ⊢ n ∷ Nat →
            Γ ⊢ natrec z s n ∷ subTy (single n) M
  -- ★★ LEVITATED INDUCTIVE FAMILIES (SPIKE-LEVITATION S3/S4).
  --   Telescopes: well-formedness IS typing.  Every telescope former
  --   types its index code `Γ ⊢ I ∷ U`: its conclusion `Desc I` needs it,
  --   and the other premises mention `I` only under `El`/`Desc` or a
  --   binder, from which it is recoverable only up to conversion (validity
  --   sits ABOVE subject reduction).
  ⊢dι   : ∀ {Γ I j} → Γ ⊢ I ∷ U → Γ ⊢ j ∷ El I → Γ ⊢ dι j ∷ Desc I
  ⊢dσ   : ∀ {Γ I S f} → Γ ⊢ I ∷ U → Γ ⊢ S ∷ U →
          Γ ⊢ f ∷ Π (El S) (Desc (renTm vs I)) → Γ ⊢ dσ S f ∷ Desc I
  ⊢dρ   : ∀ {Γ I j C} → Γ ⊢ I ∷ U → Γ ⊢ j ∷ El I → Γ ⊢ C ∷ Desc I → Γ ⊢ dρ j C ∷ Desc I
  -- `⊢dpay` types its index code like `⊢dσ` does: its reduct at `dι j` is
  --   `⌜Id⌝ I j i`, whose formation needs `Γ ⊢ I ∷ U`, and the other
  --   premises only mention `I` under `Desc`/`El` (extracting it would
  --   need validity, which sits ABOVE subject reduction).
  ⊢dpay : ∀ {Γ I D C i} → Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → Γ ⊢ C ∷ Desc I → Γ ⊢ i ∷ El I →
          Γ ⊢ dpay I D C i ∷ U
  -- a constructor exists at EVERY index (Fording): the payload's `dι j`
  --   field is the equation `j ≡ i`, so the bad ones are uninhabitable.
  -- its TYPE mentions the index code, so it types it (validity).
  ⊢con  : ∀ {Γ I D i p} → Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → Γ ⊢ i ∷ El I →
          Γ ⊢ p ∷ El (dpay I D D i) → Γ ⊢ con p ∷ IMu I D i
  ⊢dih  : ∀ {Γ I D M e C i p} →
          Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → motCtx Γ I D ⊢ty M → Γ ⊢ e ∷ MethTy I D M →
          Γ ⊢ C ∷ Desc I → Γ ⊢ i ∷ El I → Γ ⊢ p ∷ El (dpay I D C i) →
          Γ ⊢ dih D e C p ∷ DIh D M C p
  ⊢ielim : ∀ {Γ I D M e i t} →
           Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → motCtx Γ I D ⊢ty M → Γ ⊢ e ∷ MethTy I D M →
           Γ ⊢ i ∷ El I → Γ ⊢ t ∷ IMu I D i →
           Γ ⊢ ielim D i e t ∷ iinst i t M
  -- tags: Fin (n+1) ≅ 1 + Fin n, and the empty Fin 0
  ⊢fzero  : ∀ {Γ n} → Γ ⊢ fzero ∷ Fin (suc n)
  ⊢fsuc   : ∀ {Γ n t} → Γ ⊢ t ∷ Fin n → Γ ⊢ fsuc t ∷ Fin (suc n)
  ⊢fcase  : ∀ {Γ n P t a b} →
            (Γ ▹ Fin (suc n)) ⊢ty P → Γ ⊢ t ∷ Fin (suc n) →
            Γ ⊢ a ∷ subTy (single fzero) P → (Γ ▹ Fin n) ⊢ b ∷ subTy fsucS P →
            Γ ⊢ fcase t a b ∷ subTy (single t) P
  ⊢fcase0 : ∀ {Γ P t} → (Γ ▹ Fin zero) ⊢ty P → Γ ⊢ t ∷ Fin zero →
            Γ ⊢ fcase0 t ∷ subTy (single t) P
  -- ★ Σ-INDUCTION (D071)
  ⊢psplit : ∀ {Γ A B P q b} →
            Γ ⊢ty A → (Γ ▹ A) ⊢ty B → (Γ ▹ Σ' A B) ⊢ty P → Γ ⊢ q ∷ Σ' A B →
            ((Γ ▹ A) ▹ B) ⊢ b ∷ subTy pairS P →
            Γ ⊢ psplit b q ∷ subTy (single q) P
  ⊢conv : ∀ {Γ t A B}   → Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B

data _⊢ty_ where
  ty-base : ∀ {Γ}     → Γ ⊢ty base
  ty-U    : ∀ {Γ}     → Γ ⊢ty U
  ty-Π    : ∀ {Γ A B} → Γ ⊢ty A → (Γ ▹ A) ⊢ty B → Γ ⊢ty Π A B
  ty-Σ    : ∀ {Γ A B} → Γ ⊢ty A → (Γ ▹ A) ⊢ty B → Γ ⊢ty Σ' A B
  ty-El   : ∀ {Γ c}   → Γ ⊢ c ∷ U → Γ ⊢ty El c
  ty-Id   : ∀ {Γ A t u} → Γ ⊢ty A → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ty Id A t u
  ty-Unit : ∀ {Γ}     → Γ ⊢ty Unit
  ty-Nat  : ∀ {Γ}     → Γ ⊢ty Nat
  -- the type CONTAINS its index code, so it types it (as every former
  --   types each term it contains — normalising the type normalises `I`).
  ty-IMu  : ∀ {Γ I D i} → Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → Γ ⊢ i ∷ El I → Γ ⊢ty IMu I D i
  -- ★ `Desc I` is LARGE (no code); its index must be a code
  ty-Desc : ∀ {Γ I} → Γ ⊢ I ∷ U → Γ ⊢ty Desc I
  ty-DIh  : ∀ {Γ I D M C i p} →
            Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → motCtx Γ I D ⊢ty M → Γ ⊢ C ∷ Desc I →
            Γ ⊢ i ∷ El I → Γ ⊢ p ∷ El (dpay I D C i) → Γ ⊢ty DIh D M C p
  ty-Fin  : ∀ {Γ n} → Γ ⊢ty Fin n
  -- W2: `Hom` FORMATION — both endpoints at the same (well-formed) type.
  ty-Hom  : ∀ {Γ A t u} → Γ ⊢ty A → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ty Hom A t u

-- CONTEXT well-formedness. Needed because `⊢var`'s type comes from a lookup:
-- syntactic validity at `⊢var` is exactly "a lookup in a well-formed context
-- yields a well-formed type", and `⊢lam` maintains it via its new premise.
infix 3 ⊢ctx_
data ⊢ctx_ : Ctx → Set where
  c-◇ : ⊢ctx ◇
  c-▹ : ∀ {Γ A} → ⊢ctx Γ → Γ ⊢ty A → ⊢ctx (Γ ▹ A)

------------------------------------------------------------------------
-- Concrete derivations — the kernel is non-vacuous.
------------------------------------------------------------------------

-- The identity function: `◇ ⊢ λx.x ∷ Π base base`.
⊢id : ◇ ⊢ lam (var vz) ∷ Π base base
⊢id = ⊢lam ty-base (⊢var here)

-- A dependent-`app` derivation: `(◇ ▹ base) ⊢ (λx.x) y ∷ base`.
⊢appex : (◇ ▹ base) ⊢ app (lam (var vz)) (var vz) ∷ base
⊢appex = ⊢app (⊢lam ty-base (⊢var here)) (⊢var here)

-- β-reduction is directed `Hom`, and reduction ⊆ conversion. The redex
-- `(λx.x) y` reduces to `y`, and the two are convertible.
βex : app (lam (var vz)) (var vz) ⟶ var (vz {ε})
βex = β (var vz) (var vz)

conv-βex : app (lam (var vz)) (var vz) ≅ var (vz {ε})
conv-βex = hom→≅ (step βex done)

-- THE CONVERSION RULE AT WORK: a term whose type contains a β-redex may be
-- re-typed at the reduct — definitional equality (core(Hom)) identifying types
-- that differ by a computation. This is exactly why dependent typing needs
-- `Id = core(Hom)` in the conversion rule.
conv-El : ∀ {Γ t u u'} → Γ ⊢ t ∷ El u → u ⟶ u' → Γ ⊢ t ∷ El u'
conv-El d r = ⊢conv d (credᵀ (ξ-El r))

------------------------------------------------------------------------
-- W2 non-vacuity: `Hom` COMPUTES, and has real inhabitants.
------------------------------------------------------------------------

-- The identity path at `⌜base⌝` in the universe: `Hom U ⌜base⌝ ⌜base⌝`
-- unfolds to `Π (El ⌜base⌝) (El ⌜base⌝)`, and the identity function inhabits
-- it — a directed path derived by COMPUTATION, not by a `refl` primitive.
⊢hom-id : ◇ ⊢ lam (var vz) ∷ Hom U ⌜base⌝ ⌜base⌝
⊢hom-id =
  ⊢conv (⊢lam (ty-El ⊢⌜base⌝) (⊢var here))
        (csymᵀ (credᵀ (Hom-U ⌜base⌝ ⌜base⌝)))

-- ★ A path between DEFINITIONALLY DISTINCT codes — `SpikeHom`'s fee-is-real
-- pair, internalized.  `⌜base⌝` and `⌜Π⌝ ⌜base⌝ ⌜base⌝` are not convertible,
-- yet `Hom U` between them is INHABITED: the constant-function map
-- `λx.λy.x`.  This is exactly what option (a) bought — `Hom` with
-- inhabitants where `⟶*` has none.
⊢hom-across : ◇ ⊢ lam (lam (var (vs vz)))
                ∷ Hom U ⌜base⌝ (⌜Π⌝ ⌜base⌝ ⌜base⌝)
⊢hom-across =
  ⊢conv (⊢lam (ty-El ⊢⌜base⌝)
              (⊢conv (⊢lam (ty-El ⊢⌜base⌝) (⊢var (there here)))
                     (csymᵀ (credᵀ (El-⌜Π⌝ ⌜base⌝ ⌜base⌝)))))
        (csymᵀ (credᵀ (Hom-U ⌜base⌝ (⌜Π⌝ ⌜base⌝ ⌜base⌝))))
