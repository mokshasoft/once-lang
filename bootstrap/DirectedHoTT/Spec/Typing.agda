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
open import normalizer.Syntax.Types using ( _≡_; refl; trans )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam; app
        ; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap
        ; Id; ⌜Id⌝; idrefl; jsub
        ; Unit; Nat; unit; nzero; nsuc; natrec; extS; ⌜Nat⌝; ⌜Unit⌝; ⌜Mu⌝
        ; Ren; extR; Sub; subTy; subTm; renTy; renTm
        ; Desc; Mu; con; elim; lookupD; sel; fields
        ; payTy; payTy-ren; payTy-sub; εwkTy; εwk-ren; εwk-sub; _∈D_; hereD; thereD; DCon; dι; dρ; dκ; dnil; _◃_; ihs; subTy-subTy; subTy-cong; renTy-subTy
        ; subTm-renTm; subTm-id
        ; IMu; icon; ielim; ⌜IMu⌝; ICon; IDesc; iι; iρ; iκ; inil; _◂_; ipayTy; ilookupD; _∈ID_; hereID; thereID; iihs; ifields; εwkTm )
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

------------------------------------------------------------------------
-- ★★ THE ELIMINATOR'S COMPUTED TYPES (gate 5c).  Here rather than in
--    `Pi` because they need `single`, and because `⊢con`/`⊢elim` are
--    the only consumers.
------------------------------------------------------------------------

-- ★★ the IH TUPLE's type: one entry per `dρ`, NONE per `dκ`.
--    ⚠ a non-recursive field owes no induction hypothesis — it is
--      SKIPPED, not filled with a placeholder.  Same accounting as
--      `SpikeDescSigma`'s `elimLift` in the model, which is why the term
--      layer and the model layer agree on what a description means.
ihTy : Desc → DCon → RTm Γ → RTy (Γ ∙) → RTy Γ
ihTy D dι       q M = Unit
ihTy D (dρ C)   q M = Σ' (subTy (single (fst q)) M) (renTy vs (ihTy D C (snd q) M))
ihTy D (dκ A C) q M = ihTy D C (snd q) M

-- ★★★ THE MOTIVE, RE-BASED AT THE PAYLOAD BINDER.  `atCon k M` is `M`
--     with its SCRUTINEE binder replaced by `con k ⟨-⟩`, so its own
--     binder is now the PAYLOAD.  This is the move that makes tupled
--     methods type WITHOUT η (gate 5c).
conS : ℕ → Sub (Γ ∙) (Γ ∙)
conS k vz     = con k (var vz)
conS k (vs x) = var (vs x)

atCon : ℕ → RTy (Γ ∙) → RTy (Γ ∙)
atCon k M = subTy (conS k) M

-- instantiating the re-based motive at a payload IS the motive at that
-- constructor.  ⚠ NO η — the congruence is `refl` in every case.
atCon-inst : (k : ℕ) (M : RTy (Γ ∙)) (p : RTm Γ) →
             subTy (single p) (atCon k M) ≡ subTy (single (con k p)) M
atCon-inst k M p =
  trans (subTy-subTy M) (subTy-cong (λ { vz → refl ; (vs x) → refl }) M)

-- ★★ one constructor's METHOD — TUPLED: the payload whole, then the IHs.
methTy : Desc → ℕ → DCon → RTy (Γ ∙) → RTy Γ
methTy D k C M =
  Π (payTy D C)
    (Π (ihTy D C (var vz) (renTy (extR vs) M))
       (renTy vs (atCon k M)))

-- the METHOD TUPLE, right-nested so `sel` navigates it by `fst`/`snd`.
--
-- ⚠⚠ THE TAG MUST ADVANCE.  Each method's result is `atCon k M` — the
--   motive at ITS OWN constructor — so the k-th entry carries tag `k`,
--   not `0`.  The extra `ℕ` is that offset.  With a fixed `0` every
--   method would claim to produce `M[con 0 …]` and `sel-ty` (which pulls
--   entry `k` out at `methTy D k (lookupD D k) M`) would be unprovable.
methsTyFrom : Desc → RTy (Γ ∙) → ℕ → Desc → RTy Γ
methsTyFrom D M j dnil    = Unit
methsTyFrom D M j (C ◃ E) =
  Σ' (methTy D j C M) (renTy vs (methsTyFrom D M (suc j) E))

methsTy : Desc → RTy (Γ ∙) → Desc → RTy Γ
methsTy D M E = methsTyFrom D M zero E

------------------------------------------------------------------------
-- ★★★ THE INDEXED ELIMINATOR'S APPARATUS.
--
-- ⚠⚠ THE MOTIVE IS TWO-SLOT: `M : RTy ((Γ ∙) ∙)`, a family over the INDEX
--   (outer, `var (vs vz)`) and the SCRUTINEE (inner, `var vz`).  It has to
--   be — the scrutinee's type `IMu D I i` MENTIONS the index, so a motive
--   over the scrutinee alone cannot be written down.  That is the third
--   thing about indexing that was forced rather than chosen.
------------------------------------------------------------------------

-- instantiate the two-slot motive at index `j` and scrutinee `t`
iinst : RTm Γ → RTm Γ → RTy ((Γ ∙) ∙) → RTy Γ
iinst j t M = subTy (single t) (subTy (extS (single j)) M)

-- ★ the IH tuple's TYPE.  Each recursive field contributes the motive AT
--   ITS OWN SHIFTED INDEX — that is the whole content of indexing here.
iihTy : IDesc → RTy ε → ICon → RTm Γ → RTm Γ → RTy ((Γ ∙) ∙) → RTy Γ
iihTy D I iι       i q M = Unit
iihTy D I (iρ f C) i q M =
  Σ' (iinst (app (εwkTm f) i) (fst q) M)
     (renTy vs (iihTy D I C i (snd q) M))
iihTy D I (iκ κ C) i q M = iihTy D I C i (snd q) M

-- ★ the motive RE-BASED at the payload binder, for constructor `k` at
--   index `i`: the scrutinee slot becomes `icon k ⟨-⟩` and the index slot
--   is fixed to `i`.  The indexed twin of `atCon`.
iconS : ℕ → RTm Γ → Sub ((Γ ∙) ∙) (Γ ∙)
iconS k i vz          = icon k (var vz)
iconS k i (vs vz)     = renTm vs i
iconS k i (vs (vs x)) = var (vs x)

iatCon : ℕ → RTm Γ → RTy ((Γ ∙) ∙) → RTy (Γ ∙)
iatCon k i M = subTy (iconS k i) M

imethTy : IDesc → RTy ε → ℕ → ICon → RTm Γ → RTy ((Γ ∙) ∙) → RTy Γ
imethTy D I k C i M =
  Π (ipayTy D I i C)
    (Π (iihTy D I C (renTm vs i) (var vz) (renTy (extR (extR vs)) M))
       (renTy vs (iatCon k i M)))

imethsTyFrom : IDesc → RTy ε → RTy ((Γ ∙) ∙) → RTm Γ → ℕ → IDesc → RTy Γ
imethsTyFrom D I M i j inil    = Unit
imethsTyFrom D I M i j (C ◂ E) =
  Σ' (imethTy D I j C i M)
     (renTy vs (imethsTyFrom D I M i (suc j) E))

imethsTy : IDesc → RTy ε → RTy ((Γ ∙) ∙) → RTm Γ → IDesc → RTy Γ
imethsTy D I M i E = imethsTyFrom D I M i zero E


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
  -- ★★ INDUCTIVE TYPES: `⌜Mu⌝` is J-ABLE, and belongs with ⌜base⌝/⌜Σ⌝/
  -- ⌜Id⌝/⌜Unit⌝ rather than with ⌜Nat⌝.  The dividing line is whether the
  -- decode's `Hom` COMPUTES: `Hom Nat a b` does (the order rules discard
  -- an endpoint, which is what breaks J at ⌜Nat⌝), whereas nothing
  -- computes `Hom (Mu D) a b` — that is exactly why `sh-Mu` is a STUCK
  -- HEAD in the SN layer.  So `stkC? (⌜Mu⌝ D) = true` and this rule is
  -- its obligation.
  tr-J-Mu   : {D : Desc} (c a m : RTm (Γ ∙)) (s e : RTm Γ) →
              tr (⌜Hom⌝ c a m) (hrefl (⌜Mu⌝ D) s) e ⟶ e
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
  -- ★ INDUCTIVE-TYPES AXIS: THE ι-RULE.  Keyed on the canonical head
  -- `con k p`, exactly as `natrec-suc` is keyed on `nsuc n`.
  --
  -- ⚠ NO SIDE CONDITION.  `lookupD` and `sel` are total (see Pi), so this
  -- is one rule with no `lookup D k ≡ just C` premise — determinism is a
  -- pattern match and confluence never inverts a `just`.  An out-of-range
  -- tag reduces to junk; `⊢con` is what rules it out.
  --
  -- The recursive calls are BUILT BY `fields`, one `elim D ms (fst …)` per
  -- `dρ` — at a payload projection, i.e. strictly inside `p`.  That is the
  -- same descent `natrec-suc` makes to `n`, generalised to a field list.
  ι-elim   : (D : Desc) (ms : RTm Γ) (k : ℕ) (p : RTm Γ) →
             elim D ms (con k p) ⟶ fields D ms (lookupD D k) (sel k ms) p
  ξ-con    : {k : ℕ} {p p' : RTm Γ} → p ⟶ p' → con k p ⟶ con k p'
  ξ-elimᵐ  : {D : Desc} {ms ms' t : RTm Γ} →
             ms ⟶ ms' → elim D ms t ⟶ elim D ms' t
  ξ-elimᵗ  : {D : Desc} {ms t t' : RTm Γ} →
             t ⟶ t' → elim D ms t ⟶ elim D ms t'

  -- ★★★★ THE INDEXED ι-RULE.
  --
  -- ⚠⚠ ITS SUBJECT-REDUCTION OBLIGATION, STATED HERE BECAUSE WRITING THE
  --   STATEMENT IS WHAT EXPOSES THE MISSING PREMISE (PLAN-INDUCTIVE §8 —
  --   that is how gate 5 found `k ∈D D`, three commits after the rule
  --   landed).  For this rule the obligation is:
  --
  --     GIVEN   Γ ⊢ ielim D i ms (icon k p) ∷ iinst i (icon k p) M
  --     SHOW    Γ ⊢ ifields D I i ms (ilookupD D k) (sel k ms) p
  --                 ∷ iinst i (icon k p) M
  --
  --   which needs, and this is what writing it exposes:
  --     (a) `k ∈ID D`      — from inverting ⊢icon on the scrutinee.  WITHOUT
  --         it `ilookupD D k` falls off the end of the list and returns
  --         `iι`, and the method selected is not the one that built the
  --         term.  (Exactly gate 5's `k ∈D D`.)
  --     (b) `iatCon`-instantiation: `iinst i (icon k p) M` must equal the
  --         k-th method's RESULT type at the payload — the indexed twin of
  --         `atCon-inst`, and it must hold WITH the index slot fixed to `i`.
  --     (c) the IH tuple `iihs` must inhabit `iihTy` AT THE SHIFTED INDICES
  --         — i.e. `ielim` at `app (εwkTm f) i` for each `iρ f`.
  --
  --   ⬜ (a) is discharged by the `k ∈ID D` premise on ⊢icon, already
  --      present.  (b) and (c) are the Metatheory/SubjectReduction
  --      obligations and are NOT yet proved.
  ι-ielim  : (D : IDesc) (i ms : RTm Γ) (k : ℕ) (p : RTm Γ) →
             ielim D i ms (icon k p)
               ⟶ ifields D i ms (ilookupD D k) (sel k ms) p
  ξ-icon   : {k : ℕ} {p p' : RTm Γ} → p ⟶ p' → icon k p ⟶ icon k p'
  ξ-ielimⁱ : {D : IDesc} {i i' ms t : RTm Γ} →
             i ⟶ i' → ielim D i ms t ⟶ ielim D i' ms t
  ξ-ielimᵐ : {D : IDesc} {i ms ms' t : RTm Γ} →
             ms ⟶ ms' → ielim D i ms t ⟶ ielim D i ms' t
  ξ-ielimᵗ : {D : IDesc} {i ms t t' : RTm Γ} →
             t ⟶ t' → ielim D i ms t ⟶ ielim D i ms t'
  -- ★ `⌜Mu⌝` needs no congruence — it is inert, with no subterms.
  --   `⌜IMu⌝` CARRIES THE INDEX, so it needs one.  Exposed by writing
  --   Confluence's `p⌜IMu⌝`: a parallel-reduction rule under a former
  --   implies a single-step congruence under it.
  ξ-⌜IMu⌝  : {D : IDesc} {I : RTy ε} {i i' : RTm Γ} →
             i ⟶ i' → ⌜IMu⌝ D I i ⟶ ⌜IMu⌝ D I i'

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
  -- ★★ INDUCTIVE TYPES: the code DECODES.  This is the single rule
  -- that makes `Mu D` a SMALL type, and so the single rule that
  -- unlocks nesting — `dκ (El (⌜Mu⌝ D'))` is now well-formed.
  El-⌜Mu⌝   : {D : Desc} → El (⌜Mu⌝ {Γ} D) ⟶ᵀ Mu D
  El-⌜IMu⌝  : {D : IDesc} {I : RTy ε} {i : RTm Γ} →
              El (⌜IMu⌝ D I i) ⟶ᵀ IMu D I i
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
  -- ★★★ `IMu` CARRIES A TERM, so it needs a congruence — the TYPE-LEVEL
  --   twin of the note on `ξ-⌜IMu⌝` above, and the same argument.  `Mu D`
  --   is inert and needs none; `Hom`/`Id` carry terms and have `ξ-…ˡ/ʳ`;
  --   `IMu D I i` carries the INDEX and had nothing.
  --
  -- ⚠⚠ WITHOUT THIS, SUBJECT REDUCTION IS FALSE FOR `ξ-ielimⁱ` — a rule
  --   already in the kernel.  `sr` preserves the type on the nose, so
  --   retyping `ielim D i' ms t` needs `t ∷ IMu D I i'` from
  --   `t ∷ IMu D I i`, i.e. `IMu D I i ≅ᵀ IMu D I i'`, i.e. this rule.
  --   The only alternative is deleting `ξ-ielimⁱ` so indices never
  --   reduce — which defeats `iκ` and Vec-as-sugar, both of which exist
  --   precisely so that computed indices COMPUTE.
  ξ-IMu  : {D : IDesc} {I : RTy ε} {i i' : RTm Γ} →
           i ⟶ i' → IMu D I i ⟶ᵀ IMu D I i'

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
-- ★★ PLAN §4 — DESCRIPTION WELL-FORMEDNESS.  Mutual with typing because a
--   `dκ` slot's smallness is a TYPING fact (`◇ ⊢ c ∷ U`).
data DConWf : DCon → Set
data DescWf : Desc → Set
-- ★★ their INDEXED twins.  Indexed BY the index type: a shift and a field
--   code are both functions OUT of it, so well-formedness cannot be stated
--   without knowing what it is.
data IConWf  : RTy ε → ICon → Set
data IDescWf : RTy ε → IDesc → Set

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
  -- ⚠ carries `DescWf` for the SAME reason `ty-Mu` does: the model
  -- needs a `⊩₀` witness at every `dκ` slot, and this is now a second
  -- door through which `Mu D` enters — so it must carry the same key.
  ⊢⌜Mu⌝   : ∀ {Γ D} → DescWf D → Γ ⊢ ⌜Mu⌝ {⌊ Γ ⌋} D ∷ U
  -- ★ the INDEXED code.  Required, not optional: without it an indexed type
  --   cannot live in `U`, so it could never be the carrier `A : U` that
  --   `amrec` recurses over — which is exactly what dogfooding needs.
  ⊢⌜IMu⌝  : ∀ {Γ D I i} → IDescWf I D → Γ ⊢ i ∷ εwkTy I →
            Γ ⊢ ⌜IMu⌝ D I i ∷ U
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
  -- ★★★ INDUCTIVE TYPES (gate 5c).  No new JUDGMENT: the payload's type
  -- and the method's type are COMPUTED from the description, so these
  -- reuse the existing Π/Σ rules.
  --
  -- ⚠⚠ `k ∈D D` IS LOAD-BEARING (gate 5, Q21).  `lookupD` is total, and
  -- `payTy D dι = Unit`, so without it an out-of-range tag with payload
  -- `unit` is typeable, ι reduces it to `sel k ms`, and that bottoms out
  -- in `fst unit`.  Subject reduction would be FALSE, not unprovable.
  ⊢con  : ∀ {Γ D k p} →
          DescWf D →
          k ∈D D →
          Γ ⊢ p ∷ payTy D (lookupD D k) →
          Γ ⊢ con k p ∷ Mu D
  -- ★ DEPENDENT elimination — the motive is a family over the scrutinee,
  -- exactly as `⊢natrec`'s is.  Methods are TUPLED: each receives the
  -- payload WHOLE and the IH tuple beside it, which is what lets this
  -- type without η (gate 5b vs 5c).
  ⊢elim : ∀ {Γ D M ms t} →
          DescWf D →
          (Γ ▹ Mu D) ⊢ty M →
          Γ ⊢ ms ∷ methsTy D M D →
          Γ ⊢ t ∷ Mu D →
          Γ ⊢ elim D ms t ∷ subTy (single t) M
  -- ★★★ INDEXED introduction.  The payload is typed AT THE AMBIENT INDEX;
  --   a constructor is available at EVERY index (that is what `iι` means),
  --   and a FORDING constraint field is what rules the bad ones out.
  ⊢icon : ∀ {Γ D I i k p} →
          IDescWf I D →
          k ∈ID D →
          Γ ⊢ i ∷ εwkTy I →
          Γ ⊢ p ∷ ipayTy D I i (ilookupD D k) →
          Γ ⊢ icon k p ∷ IMu D I i
  -- ★★★ INDEXED elimination.  ⚠ The result substitutes BOTH slots — the
  --   index and the scrutinee — because the motive is two-slot.
  ⊢ielim : ∀ {Γ D I M i ms t} →
           IDescWf I D →
           ((Γ ▹ εwkTy I) ▹ IMu D I (var vz)) ⊢ty M →
           Γ ⊢ i ∷ εwkTy I →
           Γ ⊢ ms ∷ imethsTy D I M i D →
           Γ ⊢ t ∷ IMu D I i →
           Γ ⊢ ielim D i ms t ∷ iinst i t M
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
  -- ★ INDUCTIVE TYPES.  ⚠ UNCONDITIONAL for now: a garbage `dκ A` yields
  -- a type nothing inhabits — permissive, not unsound.  Description
  -- WELL-FORMEDNESS becomes REQUIRED for the model, where `⊩₀ (Mu D)`
  -- needs `⊩₀ A` at every `dκ`.  See PLAN-INDUCTIVE §4.
  -- ★ now CONDITIONAL.  The model needs a `⊩₀` witness at every `dκ`
  -- slot, and there is nowhere else to get one: `ty-Mu` is the only rule
  -- that introduces `Mu D`, so it is the only place the interpretation
  -- can enter.  (It was unconditional while `Mu` had no model.)
  ty-Mu   : ∀ {Γ D}   → DescWf D → Γ ⊢ty Mu D
  -- ★★★ INDEXED formation.  ⚠ Needs the INDEX to be typed, which is why
  --   `IMu` carries the index TYPE at all — `ty-Mu` needs no such thing.
  --   Writing THIS rule is what exposed the missing field (2026-08-22).
  ty-IMu  : ∀ {Γ D I i} → IDescWf I D → Γ ⊢ i ∷ εwkTy I → Γ ⊢ty IMu D I i
  -- W2: `Hom` FORMATION — both endpoints at the same (well-formed) type.
  ty-Hom  : ∀ {Γ A t u} → Γ ⊢ty A → Γ ⊢ t ∷ A → Γ ⊢ u ∷ A → Γ ⊢ty Hom A t u

-- ★★ the descriptions the model can interpret.
--
-- ⚠ THE κ FIELD MUST BE SMALL — `El c` for a CLOSED code.  This is not an
--   ad-hoc restriction to make the proof go through: an inductive type
--   belongs to the universe exactly when its fields do, which is the rule
--   Agda and Coq use.  Concretely it is what lets `fund-ty` build the
--   `⊩₀ (εwkTy (El c))` witness that `ki-κ` demands, via `sem-El`.
--
-- ⚠ CONSEQUENCE, recorded so it is not discovered later: `dκ (Mu D')` —
--   a NESTED datatype — is NOT well-formed yet, because `Mu D'` is not
--   `El c` for any code.  There is no `⌜Mu⌝`.  Adding one (with
--   `El-⌜Mu⌝ : El (⌜Mu⌝ D) ⟶ᵀ Mu D`, on the `⌜Nat⌝`-at-stage-C template)
--   unlocks nesting and invalidates none of this — `dwf-κ` just gains
--   `⌜Mu⌝` as an admissible code.  Gate 6c's `WrapD` tested exactly that
--   case, so it is a real capability deferred, not a hypothetical.
data DConWf where
  dwf-ι : DConWf dι
  dwf-ρ : {C : DCon} → DConWf C → DConWf (dρ C)
  dwf-κ : {C : DCon} (c : RTm ε) → ◇ ⊢ c ∷ U → DConWf C → DConWf (dκ (El c) C)

data DescWf where
  dwf-nil  : DescWf dnil
  dwf-cons : {C : DCon} {E : Desc} → DConWf C → DescWf E → DescWf (C ◃ E)

-- ★★★ INDEXED well-formedness.
--
-- ⚠ `iwf-κ` asks for `◇ ⊢ κ ∷ Π I U` — a closed function from the index
--   type to CODES.  That is strictly better behaved than `dwf-κ`'s
--   `dκ (El c) C` hack: `dκ` takes an arbitrary `RTy ε` and well-formedness
--   then has to RESTRICT it to an `El` of a code ("the κ field must be
--   SMALL"). Here the code-valued function is the constructor's own field,
--   so `ipayTy` produces `El (app κ i)` and smallness is structural.
--
-- ⚠ `iwf-ρ` asks for `◇ ⊢ f ∷ Π I (εwkTy I)` — the shift is an endofunction
--   on the index type.  For a SYNTAX that is `lam (var vz)` (a field at the
--   ambient index) or `lam (nsuc (var vz))` (one under a binder).
data IConWf where
  iwf-ι : {I : RTy ε} → IConWf I iι
  iwf-ρ : {I : RTy ε} {C : ICon} (f : RTm ε) →
          ◇ ⊢ f ∷ Π I (εwkTy I) → IConWf I C → IConWf I (iρ f C)
  iwf-κ : {I : RTy ε} {C : ICon} (κ : RTm ε) →
          ◇ ⊢ κ ∷ Π I U → IConWf I C → IConWf I (iκ κ C)

data IDescWf where
  idwf-nil  : {I : RTy ε} → IDescWf I inil
  idwf-cons : {I : RTy ε} {C : ICon} {E : IDesc} →
              IConWf I C → IDescWf I E → IDescWf I (C ◂ E)

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
