------------------------------------------------------------------------
-- ⚠⚠ FROZEN AT STAGE B — THIS MODULE IS NOT EXPECTED TO COMPILE. ⚠⚠
--
-- This is a DESIGN RECORD, not a test.  Its conclusion is already
-- absorbed into the main tower; what it preserves is WHY that path was
-- taken.  It carries its own COPY of `subTm-occ` and pattern-matches
-- exhaustively on `RTm`/`⊩₀`, so stage A/C's `⌜Nat⌝`/`⌜Unit⌝` RTm constructors broke it — in the WF-axis work,
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
-- OCP-0009 · W2 eliminator, spike 3 — `tr`'s REDUCTION RULES.
--
-- The question this spike was scoped to close (HANDOFF-2026-07-31 §4.3
-- item 4a): the `⊢tr` spec in `NbEPDirDBVar`'s header carries an `RTy`
-- motive annotation — exactly the trap that rejected `refl` design (A).
-- Expected resolution: the same (B) move, CODE-annotated motives.
--
-- ★ THAT RESOLUTION IS CONFIRMED — and it is visible by construction
-- below: with the motive a CODE (`tr d p e`, `d : RTm (Γ ∙)`), every
-- reduction rule and every congruence in this file lives in ONE relation
-- on terms.  A frozen motive cannot arise: `ξ-trᵈ` is an ordinary
-- term-level congruence (`El ((λy.y) (var vz))` as a motive is the CODE
-- `app (lam …) (var vz)`, and it β-reduces inside `tr` like any subterm).
-- `_⟶_`/`_⟶ᵀ_` stay stratified; the confluence developments stay separate.
--
-- But the spike's real finding is about the RULE SET, not the annotation:
--
-- ★★ `tr` IS AN ELIMINATOR OF ITS PATH, AND ITS RULES MUST BE KEYED ON
--    THE PATH'S CANONICAL FORM — the way `app` computes on `lam` and
--    `case` computes on constructors.  The forecast rules (handoff §4.3
--    item 4a) key on the MOTIVE and leave the path arbitrary, and BOTH
--    are refuted here by unjoinable critical pairs in RAW reduction
--    (which is where this kernel proves confluence — `Conf` is raw):
--
--    (1) unkeyed `tr (var vz) p e ⟶ app p e` collides with the
--        J-equation at `p = hrefl …`: the peak reduces to `e` and to
--        `app (hrefl …) e`, two distinct normal forms (§4, measured);
--    (2) the unkeyed J-equation `tr d (hrefl c s) e ⟶ e` collides with
--        `hrefl`'s OWN `⌜Π⌝`-unfolding (`SpikeHomRefl`): at
--        `p = hrefl (⌜Π⌝ c₁ c₂) s` the peak reduces to `e` and to a
--        `tr` of a lambda, again two distinct normal forms (§5,
--        measured).  So J must fire only where `hrefl` is CANONICAL —
--        at the head-STABLE stuck codes `⌜base⌝ / ⌜Σ⌝ / ⌜Hom⌝`.  Not at
--        a neutral code: a neutral code can still become `⌜Π⌝`-headed,
--        which would reopen (2) one step later.  (`hrefl` at a neutral
--        code is stuck-but-not-J-able; it becomes J-able when its code
--        reduces to a stable head.  In the real syntax this costs
--        nothing: "hrefl at a non-canonical code" is simply not a redex.)
--
--    Both peaks are ill-typed terms — and that is the point: `Conf` is a
--    RAW theorem in this tower, so raw critical pairs must join whether
--    or not the peak is typable.  The fix is to make the peaks not exist.
--
-- ★ AND THE FORECAST RULE SET IS INCOMPLETE — a THIRD computation rule is
--   FORCED by canonicity (§6).  `NbEPDirDBVar`'s `comp-pos` licenses the
--   composition motive `⌜Hom⌝ c a (var vz)` at an ARBITRARY ambient code
--   `c`.  Take `c = ⌜Π⌝ c₁ c₂`: then both the path and the payload live
--   at pointwise-unfolded `Hom`s (function types!), their canonical
--   inhabitants are lambdas, and a `tr` sitting on a lambda with no rule
--   is a stuck non-neutral at a `Π` type — the exact canonicity break
--   `SpikeHomRefl` §0 names.  The forced rule composes POINTWISE,
--   descending into the ambient code — structurally (§7, measured, no
--   pragma: same result shape as `hunfold`).
--
-- THE FIXED RULE SET (§6, root-determinism measured):
--
--   J-base   : tr d (hrefl ⌜base⌝ s) e        ⟶ e
--   J-Σ      : tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e   ⟶ e
--   J-Hom    : tr d (hrefl (⌜Hom⌝ c a b) s) e ⟶ e
--   taut-lam : tr (var vz) (lam f) e          ⟶ app (lam f) e
--   pw-Π     : tr (⌜Hom⌝ (⌜Π⌝ c₁ c₂) a (var vz)) (lam f) e
--            ⟶ lam (tr (⌜Hom⌝ c₂ (a·x) (var vz)) ((lam f)·x) (e·x))
--
--   (`·x` = weaken and apply to the new variable, exactly `Hom-Π`'s
--   endpoint shape.  In the real syntax the rule needs only RENAMINGS —
--   `extR vs` for `a`/`p`/`e` and the top-two-variable swap for `c₂`,
--   whose action on the outer motive variable is vacuous on typed terms
--   since `posc-Hom` requires it absent — no substitutions beyond what
--   `β` already uses.  ARGUED here; `Conf`/`Inj` mechanize it at
--   consolidation.)
--
--   The motive DISCRIMINATES which rule; the path's canonical form GATES
--   firing.  `taut-lam` deliberately produces the β-redex rather than
--   contracting it — one new rule should not also do β's job (smaller
--   development cases; β is already proven).
--
-- ★ CONSTANT MOTIVES — the answer is stronger than the forecast's "no
--   rule needed": constant motives must not license `tr` AT ALL.
--   (i)  A discard rule would need an occurrence SIDE CONDITION
--        (vz-freeness is not a pattern), the shape the confluence
--        developments punish; and without one, a constant-motive `tr`
--        on a lambda-valued path is a canonicity hole by the same §6
--        argument.
--   (ii) It is never needed: substituting either endpoint into a
--        vz-free motive code yields THE SAME TERM — `El d[t]` and
--        `El d[u]` are identical on the nose, so the payload already
--        has the target type.  MEASURED over the REAL kernel syntax:
--        `const-motive-invisible` (§9).
--   Consequence: `tr`'s typing premise is NOT `NbEPDirDBVar`'s `Pos` —
--   it is the smaller `PosC` (§8): `Pos` states semantic covariance;
--   the `tr` premise is covariance WITH A COMPUTATION RULE.  `pos-const`
--   stays true (constant families are functorial) and stays out of the
--   eliminator (its action is the identity, which conversion — indeed
--   syntactic equality — already provides).
--
--   The floor `PosC = {posc-var, posc-Hom}` is exactly big enough:
--   `trans` via the composition motive, directed univalence computing at
--   the tautological motive (a third time).  What it drops is derivable
--   without `tr`: constant motives (identity, above), `Π`-shaped and
--   large motives (pointwise per instance — the `⊢hom-id` pattern), and
--   U-ambient composition (`Hom U a (var vz)` is `Pos` but has no code —
--   a composite of universe paths is literally function composition).
--   Negative control mirrors `NbEPDirDBVar`: `sym`'s motive CODE is
--   refuted by pattern alone (§8).
--
-- THE REVISED `⊢tr` SPEC this licenses (supersedes NbEPDirDBVar header):
--
--   ⊢tr : (Γ ▹ A) ⊢ d ∷ U → PosC vz d
--       → Γ ⊢ p ∷ Hom A t u
--       → Γ ⊢ e ∷ El (subTm (single t) d)
--       → Γ ⊢ tr d p e ∷ El (subTm (single u) d)
--
-- Layout: §1–2 miniature calculus (scoping elided, as in `SpikeHomRefl`);
-- §3 the FORECAST relation; §4–5 the two measured refutations; §6 the
-- fixed rule set + root determinism + the resolved peaks; §7 pointwise
-- termination; §8 `PosC` + controls; §9 REAL syntax: constant motives
-- are invisible to substitution.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeTr where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; Var; vz; vs
        ; RTm; var; lam; app; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; ⌜Hom⌝; ⌜Hom⌝-cong₃; tr-cong₃ 
        ; unit; nzero; nsuc; natrec; natrec-cong₃ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Sub; extS; subTm; renTm )
open import poc.OCP0009.NbEPDirDBPi using ( hrefl; tr; ap; ap-cong₃; ⌜Id⌝; idrefl; jsub; ⌜Id⌝-cong₃; jsub-cong₃ )
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; false; _∨_; eqv; occTm )
open import poc.OCP0009.NbEPDirDBType using ( single )

data ⊥ : Set where

------------------------------------------------------------------------
-- 1. The miniature calculus — `SpikeHomRefl`'s, plus `tr`.  Scoping
--    elided (binders do not affect the critical pairs or the measures);
--    `cv0` is the transported variable in CODE position (the motive
--    `var vz`), `v0` in term position marks it in `⌜Hom⌝` endpoints.
--    In the real syntax codes ARE terms; `Cd` here is the code fragment,
--    and `cne` stands for "a non-canonical term in code position".
------------------------------------------------------------------------

data Cd : Set
data Tm : Set

data Cd where
  cb    : Cd                  -- ⌜base⌝
  cΠ cΣ : Cd → Cd → Cd        -- ⌜Π⌝ / ⌜Σ⌝
  cH    : Cd → Tm → Tm → Cd   -- ⌜Hom⌝: ambient code + two endpoints
  cv0   : Cd                  -- ★ the transported variable, as a code
  cne   : Tm → Cd             -- a neutral (non-canonical) code

data Tm where
  v0    : Tm
  wk    : Tm → Tm
  lam   : Tm → Tm
  app   : Tm → Tm → Tm
  hrefl : Cd → Tm → Tm        -- SpikeHomRefl's annotated refl
  tr    : Cd → Tm → Tm → Tm   -- ★ tr d p e — CODE-annotated motive

private
  variable
    c c' c₁ c₂ d d' : Cd
    a a' b b' e e' f n n' p p' s t t' u u' r : Tm

------------------------------------------------------------------------
-- 2. Substitution for β — scoping-elided (`wk` blocks; binders are not
--    shifted; `cv0` under substitution becomes a term in code position).
--    Only β's existence matters to the refutations, never its output.
------------------------------------------------------------------------

instC : Cd → Tm → Cd
inst  : Tm → Tm → Tm

instC cb         u = cb
instC (cΠ c d)   u = cΠ (instC c u) (instC d u)
instC (cΣ c d)   u = cΣ (instC c u) (instC d u)
instC (cH c a b) u = cH (instC c u) (inst a u) (inst b u)
instC cv0        u = cne u
instC (cne n)    u = cne (inst n u)

inst v0          u = u
inst (wk t)      u = t
inst (lam t)     u = lam (inst t u)
inst (app t s)   u = app (inst t u) (inst s u)
inst (hrefl c t) u = hrefl (instC c u) (inst t u)
inst (tr d p e)  u = tr (instC d u) (inst p u) (inst e u)

------------------------------------------------------------------------
-- 3. THE FORECAST RELATION — the handoff's `tr` rules VERBATIM (`tr-J`
--    unkeyed, `tr-taut` unkeyed), coexisting with the standing rules
--    they must coexist with (β, `hrefl`'s `⌜Π⌝`-unfold) and the full
--    congruence closure.  Note every congruence is TERM-level — the
--    code-annotation payoff, by construction.
------------------------------------------------------------------------

infix 3 _⟶ᵁ_ _⟶ᶜ_ _⟶ᵁ*_ _⟶ᵣ_

data _⟶ᵁ_ : Tm → Tm → Set
data _⟶ᶜ_ : Cd → Cd → Set

data _⟶ᵁ_ where
  -- standing rules
  β-red    : app (lam t) u ⟶ᵁ inst t u
  hrefl-Π  : hrefl (cΠ c d) t ⟶ᵁ lam (hrefl d (app (wk t) v0))
  -- ★ the forecast `tr` rules, as stated in the handoff
  tr-J     : tr d (hrefl c s) e ⟶ᵁ e
  tr-taut  : tr cv0 p e ⟶ᵁ app p e
  -- congruences
  ξ-wk     : t ⟶ᵁ t' → wk t ⟶ᵁ wk t'
  ξ-lam    : t ⟶ᵁ t' → lam t ⟶ᵁ lam t'
  ξ-appˡ   : t ⟶ᵁ t' → app t u ⟶ᵁ app t' u
  ξ-appʳ   : u ⟶ᵁ u' → app t u ⟶ᵁ app t u'
  ξ-hreflᶜ : c ⟶ᶜ c' → hrefl c t ⟶ᵁ hrefl c' t
  ξ-hreflᵃ : t ⟶ᵁ t' → hrefl c t ⟶ᵁ hrefl c t'
  ξ-trᵈ    : d ⟶ᶜ d' → tr d p e ⟶ᵁ tr d' p e
  ξ-trᵖ    : p ⟶ᵁ p' → tr d p e ⟶ᵁ tr d p' e
  ξ-trᵉ    : e ⟶ᵁ e' → tr d p e ⟶ᵁ tr d p e'

data _⟶ᶜ_ where
  ξ-cΠˡ : c ⟶ᶜ c' → cΠ c d ⟶ᶜ cΠ c' d
  ξ-cΠʳ : d ⟶ᶜ d' → cΠ c d ⟶ᶜ cΠ c d'
  ξ-cΣˡ : c ⟶ᶜ c' → cΣ c d ⟶ᶜ cΣ c' d
  ξ-cΣʳ : d ⟶ᶜ d' → cΣ c d ⟶ᶜ cΣ c d'
  ξ-cHᶜ : c ⟶ᶜ c' → cH c a b ⟶ᶜ cH c' a b
  ξ-cHˡ : a ⟶ᵁ a' → cH c a b ⟶ᶜ cH c a' b
  ξ-cHʳ : b ⟶ᵁ b' → cH c a b ⟶ᶜ cH c a b'
  ξ-cne : n ⟶ᵁ n' → cne n ⟶ᶜ cne n'

data _⟶ᵁ*_ : Tm → Tm → Set where
  done : t ⟶ᵁ* t
  _∷*_ : t ⟶ᵁ u → u ⟶ᵁ* r → t ⟶ᵁ* r

data Joins (x y : Tm) : Set where
  join : x ⟶ᵁ* r → y ⟶ᵁ* r → Joins x y

-- a term with no step reaches only itself
nf-* : ({x : Tm} → t ⟶ᵁ x → ⊥) → t ⟶ᵁ* r → t ≡ r
nf-* h done = refl
nf-* h (st ∷* _) with h st
... | ()

------------------------------------------------------------------------
-- 4. ★ REFUTATION 1 — the unkeyed tautological rule breaks confluence.
--    Peak: `tr cv0 (hrefl cb v0) v0`.  J gives `v0`; unkeyed taut gives
--    `app (hrefl cb v0) v0`.  Both are normal forms, and they differ.
------------------------------------------------------------------------

nf-cb : cb ⟶ᶜ c → ⊥
nf-cb ()

nf-v0 : v0 ⟶ᵁ t → ⊥
nf-v0 ()

nf-hb : hrefl cb v0 ⟶ᵁ t → ⊥
nf-hb (ξ-hreflᶜ st) = nf-cb st
nf-hb (ξ-hreflᵃ st) = nf-v0 st

nf-app-hb : app (hrefl cb v0) v0 ⟶ᵁ t → ⊥
nf-app-hb (ξ-appˡ st) = nf-hb st
nf-app-hb (ξ-appʳ st) = nf-v0 st

peak₁ : Tm
peak₁ = tr cv0 (hrefl cb v0) v0

peak₁-J : peak₁ ⟶ᵁ v0
peak₁-J = tr-J

peak₁-taut : peak₁ ⟶ᵁ app (hrefl cb v0) v0
peak₁-taut = tr-taut

taut-unkeyed-breaks-confluence : Joins v0 (app (hrefl cb v0) v0) → ⊥
taut-unkeyed-breaks-confluence (join pp qq) with nf-* nf-v0 pp | nf-* nf-app-hb qq
... | refl | ()

------------------------------------------------------------------------
-- 5. ★ REFUTATION 2 — the unkeyed J-equation breaks confluence against
--    `hrefl`'s own `⌜Π⌝`-unfold.  Peak: `tr cb (hrefl (cΠ cb cb) v0) v0`
--    (motive deliberately ≠ cv0, isolating this pair from §4's).  J
--    gives `v0`; unfolding the path first strands a `tr` on a lambda.
--    Both normal, distinct.  Hence J must be keyed to `hrefl` at the
--    head-stable stuck codes — where `hrefl` is CANONICAL, not a redex.
------------------------------------------------------------------------

peak₂ : Tm
peak₂ = tr cb (hrefl (cΠ cb cb) v0) v0

r₂ : Tm
r₂ = tr cb (lam (hrefl cb (app (wk v0) v0))) v0

peak₂-J : peak₂ ⟶ᵁ v0
peak₂-J = tr-J

peak₂-unfold : peak₂ ⟶ᵁ r₂
peak₂-unfold = ξ-trᵖ hrefl-Π

nf-wkv0 : wk v0 ⟶ᵁ t → ⊥
nf-wkv0 (ξ-wk st) = nf-v0 st

nf-app-wk : app (wk v0) v0 ⟶ᵁ t → ⊥
nf-app-wk (ξ-appˡ st) = nf-wkv0 st
nf-app-wk (ξ-appʳ st) = nf-v0 st

nf-hb' : hrefl cb (app (wk v0) v0) ⟶ᵁ t → ⊥
nf-hb' (ξ-hreflᶜ st) = nf-cb st
nf-hb' (ξ-hreflᵃ st) = nf-app-wk st

nf-r₂ : r₂ ⟶ᵁ t → ⊥
nf-r₂ (ξ-trᵈ st)         = nf-cb st
nf-r₂ (ξ-trᵖ (ξ-lam st)) = nf-hb' st
nf-r₂ (ξ-trᵉ st)         = nf-v0 st

J-unkeyed-breaks-confluence : Joins v0 r₂ → ⊥
J-unkeyed-breaks-confluence (join pp qq) with nf-* nf-v0 pp | nf-* nf-r₂ qq
... | refl | ()

------------------------------------------------------------------------
-- 6. ★★ THE FIXED RULE SET — every rule keyed on the path's canonical
--    form.  Root-determinism is MEASURED (`det`): the five rules are
--    pairwise non-overlapping, so the only remaining overlaps in the
--    full relation are root-vs-congruence — the one-step-behind pattern
--    `Conf` already handles twice (`Hom-Π`, `hrefl`-unfold) — and J's
--    key is DEVELOPMENT-STABLE: internal reduction cannot change a
--    `cb`/`cΣ`/`cH` head (measured implicitly: `_⟶ᶜ_` is head-preserving
--    by construction).  ARGUED here, mechanized by `Conf` at
--    consolidation.
------------------------------------------------------------------------

data _⟶ᵣ_ : Tm → Tm → Set where
  -- the J-equation, at the three head-STABLE stuck codes only
  J-base   : tr d (hrefl cb s) e ⟶ᵣ e
  J-Σ      : tr d (hrefl (cΣ c₁ c₂) s) e ⟶ᵣ e
  J-Hom    : tr d (hrefl (cH c a b) s) e ⟶ᵣ e
  -- directed univalence, a third time: transport along a universe path
  -- at the tautological motive is application — on a CANONICAL path
  taut-lam : tr cv0 (lam f) e ⟶ᵣ app (lam f) e
  -- ★ the rule the forecast missed: pointwise composition at a
  -- `⌜Π⌝`-ambient `⌜Hom⌝` motive (forced by canonicity at `comp-pos`)
  pw-Π     : tr (cH (cΠ c₁ c₂) a v0) (lam f) e ⟶ᵣ
             lam (tr (cH c₂ (app (wk a) v0) v0)
                     (app (wk (lam f)) v0)
                     (app (wk e) v0))

det : t ⟶ᵣ u → t ⟶ᵣ r → u ≡ r
det J-base   J-base   = refl
det J-Σ      J-Σ      = refl
det J-Hom    J-Hom    = refl
det taut-lam taut-lam = refl
det pw-Π     pw-Π     = refl

-- Both §4/§5 peaks are RESOLVED, not just joined:
-- peak₁ now steps uniquely (J fires, taut cannot — the path is not a
-- lambda) …
peak₁-fixed : peak₁ ⟶ᵣ t → t ≡ v0
peak₁-fixed J-base = refl

-- … and peak₂ has NO root step at all: J is not licensed at a `⌜Π⌝`
-- code (the path is a redex there, not canonical), so only the
-- congruence path remains and the pair never forms.
peak₂-no-root : peak₂ ⟶ᵣ t → ⊥
peak₂-no-root ()

-- The J-computation the consolidation's done-when demands, as the
-- right-unit law of `trans p q := tr (⌜Hom⌝ c a vz) q p`:
trans-unit : (x q : Tm) → tr (cH cb x v0) (hrefl cb v0) q ⟶ᵣ q
trans-unit x q = J-base

univalence-computes : (g x : Tm) → tr cv0 (lam g) x ⟶ᵣ app (lam g) x
univalence-computes g x = taut-lam

------------------------------------------------------------------------
-- 7. ★ `pw-Π` TERMINATES STRUCTURALLY — the iterated pointwise unfolding
--    descends into the ambient CODE, a strict subterm; Agda accepts the
--    composite with no pragma, no measure, no sized types (the same
--    result shape as `SpikeHomTy` item 1 and `SpikeHomRefl`'s
--    `hunfold`).  Every non-`⌜Π⌝` ambient bottoms out in a real `tr`,
--    whose path is then canonical-`hrefl` territory (J) or neutral.
------------------------------------------------------------------------

pwtrans : Cd → Tm → Tm → Tm → Tm
pwtrans (cΠ c₁ c₂) x p e =
  lam (pwtrans c₂ (app (wk x) v0) (app (wk p) v0) (app (wk e) v0))
pwtrans cb         x p e = tr (cH cb x v0) p e
pwtrans (cΣ c₁ c₂) x p e = tr (cH (cΣ c₁ c₂) x v0) p e
pwtrans (cH c y z) x p e = tr (cH (cH c y z) x v0) p e
pwtrans cv0        x p e = tr (cH cv0 x v0) p e
pwtrans (cne n)    x p e = tr (cH (cne n) x v0) p e

------------------------------------------------------------------------
-- 8. `PosC` — THE `tr` LICENSE, deliberately smaller than
--    `NbEPDirDBVar`'s `Pos`: only motive shapes that come with a
--    computation rule.  Occurrence of the marker mirrors
--    `NbEPDirDBVar`'s Boolean machinery (`wk` blocks it — `avoids-wk`).
------------------------------------------------------------------------

occT : Tm → 𝔹
occC : Cd → 𝔹

occT v0          = true
occT (wk t)      = false
occT (lam t)     = occT t
occT (app t u)   = occT t ∨ occT u
occT (hrefl c t) = occC c ∨ occT t
occT (tr d p e)  = occC d ∨ (occT p ∨ occT e)

occC cb         = false
occC (cΠ c d)   = occC c ∨ occC d
occC (cΣ c d)   = occC c ∨ occC d
occC (cH c a b) = occC c ∨ (occT a ∨ occT b)
occC cv0        = true
occC (cne n)    = occT n

data PosC : Cd → Set where
  posc-var : PosC cv0
  posc-Hom : occC c ≡ false → occT a ≡ false → PosC (cH c a v0)

-- deliberately ABSENT, and each absence is content:
--   * no `posc-const` — semantically covariant, but its action is the
--     identity and it has no rule; licensing it is §0's canonicity hole,
--     and `const-motive-invisible` (§9) shows nothing is lost;
--   * no `posc-⌜Π⌝`/`posc-⌜Σ⌝` congruence rules — a covariant compound
--     motive without a computation rule is the same hole; those
--     transports are derivable pointwise per instance instead.

-- ★★ THE CONTROLS (mirroring NbEPDirDBVar §4).
-- POSITIVE: the composition motive — `trans` via `tr`…
comp-posc : PosC (cH cb (wk v0) v0)
comp-posc = posc-Hom refl refl

-- …and the tautological motive — directed univalence.
taut-posc : PosC cv0
taut-posc = posc-var

-- NEGATIVE: `sym`'s motive CODE — marker in the FIRST (contravariant)
-- endpoint — is refuted by pattern alone.
sym-code-not-posc : PosC (cH cb v0 (wk v0)) → ⊥
sym-code-not-posc ()

-- NEGATIVE: constant motives are not licensed.
const-not-posc : PosC cb → ⊥
const-not-posc ()

------------------------------------------------------------------------
-- 9. ★ REAL SYNTAX — constant motives never need `tr`, MEASURED.
--    Substituting either endpoint into a `vz`-free motive code yields
--    the SAME term: `subTm (single t) d ≡ subTm (single u) d`.  So the
--    payload `e : El d[t]` already has the target type `El d[u]` — on
--    the nose, before conversion is even invoked.  This is the measured
--    half of excluding `posc-const`; consolidation inherits the lemma
--    as-is (it is stated over the kernel's own `RTm`/`occTm`/`single`).
------------------------------------------------------------------------

private
  variable
    Γ Δ : Cx

∨-inl : {x y : 𝔹} → x ≡ true → (x ∨ y) ≡ true
∨-inl refl = refl

∨-inr : (x : 𝔹) {y : 𝔹} → y ≡ true → (x ∨ y) ≡ true
∨-inr true  h = refl
∨-inr false h = h

eqv-refl : (x : Var Γ) → eqv x x ≡ true
eqv-refl vz     = refl
eqv-refl (vs x) = eqv-refl x

-- two substitutions agreeing on every OCCURRING variable act equally
ext-agree : {σ τ : Sub Γ Δ} (f : Var (Γ ∙) → 𝔹)
          → ((y : Var Γ) → f (vs y) ≡ true → σ y ≡ τ y)
          → (x : Var (Γ ∙)) → f x ≡ true → extS σ x ≡ extS τ x
ext-agree f g vz     _ = refl
ext-agree f g (vs y) o = cong (renTm vs) (g y o)

subTm-occ : {σ τ : Sub Γ Δ} (m : RTm Γ)
          → ((x : Var Γ) → occTm x m ≡ true → σ x ≡ τ x)
          → subTm σ m ≡ subTm τ m
subTm-occ unit       h = refl
subTm-occ nzero      h = refl
subTm-occ (nsuc n)   h = cong nsuc (subTm-occ n h)
subTm-occ (natrec z w n) h =
  natrec-cong₃
    (subTm-occ z (λ x o → h x (∨-inl o)))
    (subTm-occ w (ext-agree (λ x → occTm x w)
       (ext-agree (λ x → occTm (vs x) w)
         (λ y o → h y (∨-inr (occTm y z) (∨-inl o))))))
    (subTm-occ n (λ x o → h x (∨-inr (occTm x z) (∨-inr (occTm (vs (vs x)) w) o))))
subTm-occ (var y)    h = h y (eqv-refl y)
subTm-occ (lam m)    h = cong lam (subTm-occ m (ext-agree (λ x → occTm x m) h))
subTm-occ (app m k)  h = cong₂ app
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) o)))
subTm-occ (pair m k) h = cong₂ pair
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) o)))
subTm-occ (fst m)    h = cong fst (subTm-occ m h)
subTm-occ (snd m)    h = cong snd (subTm-occ m h)
subTm-occ ⌜base⌝     h = refl
subTm-occ (⌜Π⌝ m k)  h = cong₂ ⌜Π⌝
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (ext-agree (λ x → occTm x k) (λ y o → h y (∨-inr (occTm y m) o))))
subTm-occ (⌜Σ⌝ m k)  h = cong₂ ⌜Σ⌝
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (ext-agree (λ x → occTm x k) (λ y o → h y (∨-inr (occTm y m) o))))
-- (the three W2 formers, added when the consolidation landed them in `RTm`)
subTm-occ (⌜Hom⌝ m k l) h = ⌜Hom⌝-cong₃
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) (∨-inl o))))
  (subTm-occ l (λ x o → h x (∨-inr (occTm x m) (∨-inr (occTm x k) o))))
subTm-occ (hrefl m k) h = cong₂ hrefl
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) o)))
subTm-occ (tr m k l) h = tr-cong₃
  (subTm-occ m (ext-agree (λ x → occTm x m) (λ y o → h y (∨-inl o))))
  (subTm-occ k (λ x o → h x (∨-inr (occTm (vs x) m) (∨-inl o))))
  (subTm-occ l (λ x o → h x (∨-inr (occTm (vs x) m) (∨-inr (occTm x k) o))))
subTm-occ (ap m k l) h = ap-cong₃
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (ext-agree (λ x → occTm x k)
                          (λ y o → h y (∨-inr (occTm y m) (∨-inl o)))))
  (subTm-occ l (λ x o → h x (∨-inr (occTm x m) (∨-inr (occTm (vs x) k) o))))
subTm-occ (⌜Id⌝ m k l) h = ⌜Id⌝-cong₃
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) (∨-inl o))))
  (subTm-occ l (λ x o → h x (∨-inr (occTm x m) (∨-inr (occTm x k) o))))
subTm-occ (idrefl m k) h = cong₂ idrefl
  (subTm-occ m (λ x o → h x (∨-inl o)))
  (subTm-occ k (λ x o → h x (∨-inr (occTm x m) o)))
subTm-occ (jsub m k l) h = jsub-cong₃
  (subTm-occ m (ext-agree (λ x → occTm x m) (λ y o → h y (∨-inl o))))
  (subTm-occ k (λ x o → h x (∨-inr (occTm (vs x) m) (∨-inl o))))
  (subTm-occ l (λ x o → h x (∨-inr (occTm (vs x) m) (∨-inr (occTm x k) o))))

const-motive-invisible :
  (m : RTm (Γ ∙)) → occTm vz m ≡ false → (x y : RTm Γ) →
  subTm (single x) m ≡ subTm (single y) m
const-motive-invisible m h x y = subTm-occ m agree
  where
    agree : (z : Var _) → occTm z m ≡ true → single x z ≡ single y z
    agree vz     o with trans (sym o) h
    ... | ()
    agree (vs z) o = refl

------------------------------------------------------------------------
-- 10. WHAT THIS SETTLES, and the consolidation bill (4b), repriced.
--
-- SETTLED: code-annotated motives (design (B), third confirmation);
-- the five-rule set above, path-keyed, root-deterministic; J at stable
-- stuck heads only; `pw-Π` as a new REQUIRED rule; no constant-motive
-- rule AND no constant-motive license (`PosC` ⊊ `Pos`); the revised
-- `⊢tr` spec (§0).
--
-- THE BILL (unchanged in shape from HANDOFF §4.3 item 4b, updated in
-- content):
--   * three new term formers `⌜Hom⌝`/`hrefl`/`tr` through the tower;
--     `tr`'s reduction contributes FIVE root rules, not two;
--   * `pw-Π`'s real-syntax RHS uses `extR vs` and the top-swap renaming
--     (vacuous on the outer motive variable for `PosC`-licensed terms);
--     `Inj`/`Subj` gain the matching commutation lemmas;
--   * `PosC` lands beside `Pos` in `NbEPDirDBVar`'s module family as
--     the eliminator's premise; `Pos` itself is untouched (it remains
--     the semantic statement `fund` validates — `tr`'s `fund` case now
--     validates `PosC`);
--   * done-when gains: `det`-style root-orthogonality survives in
--     `Conf`'s development; `peak₂-no-root`'s shape (no J at `⌜Π⌝`
--     codes) as a regression control.
------------------------------------------------------------------------
