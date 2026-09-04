------------------------------------------------------------------------
-- OCP-0009 · WF LIBRARY — THE WEAKENING AND SUBSTITUTION KIT.
--
-- Generic substitution metatheory.  No recursor appears in this module:
-- everything here is about how `renTm`/`subTm` interact with weakening,
-- and it is shared by every combinator the WF axis provides.
--
-- ★ TWO FLAVOURS OF WEAKENING, and the distinction is load-bearing:
--
--     w  t   inserts a slot ABOVE everything          (`renTm vs`)
--     wᶠ t   inserts a slot BELOW a FAMILY's variable  (`renTm (extR vs)`)
--
--   A "family" is a term over an extended context — a motive or a measure
--   whose free variable IS the carrier element.  Use `⊢wkᶠ` for those and
--   `⊢wk` for ordinary terms: they produce terms that look interchangeable
--   and are not.
--
-- ⚠ P1 — ETA COVERS EVERYTHING EXCEPT MOVING A FAMILY UNDER A RENAMING.
--   `extS σ ₛ∘ᵣ vs` and `vs ᵣ∘ₛ σ` are literally the same function, so
--   `sub-w`/`ren-w` are two-step `trans`es with no case analysis.  That
--   does NOT extend to families: `wᶠ-single`, `wᶠ¹/²-single`, `wᶠ-nrs` and
--   `ren-wᶠ` each need a pointwise BRIDGE, because the composites agree
--   only after casing on the variable.  Budget a bridge whenever a lemma
--   moves a family under `extR`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Wk where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR
        ; subTm-renTm; renTm-subTm; renTm-renTm; subTm-id; subTm-cong
        ; subTy-renTy; subTy-id; renTy-renTy; renTy-subTy; renTm-cong; idₛ )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs; _⊢_∷_; _∋_∷_; here; there; wk-single )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ren-lemma; Ren⊢; Ren⊢-ext; ∋-cast )
open import DirectedHoTT.Spec.Variance using ( ren-as-sub )

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )

------------------------------------------------------------------------
-- congruences
------------------------------------------------------------------------

cong₃ : {A B C D : Set} (f : A → B → C → D)
        {a a' : A} {b b' : B} {c c' : C} →
        a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

cong₄ : {A B C D E : Set} (f : A → B → C → D → E)
        {a a' : A} {b b' : B} {c c' : C} {d d' : D} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
cong₄ f refl refl refl refl = refl

cong₅ : {A B C D E F : Set} (f : A → B → C → D → E → F)
        {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' →
        f a b c d e ≡ f a' b' c' d' e'
cong₅ f refl refl refl refl refl = refl

cong₆ : {A B C D E F G : Set} (f : A → B → C → D → E → F → G)
        {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} {h h' : F} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → h ≡ h' →
        f a b c d e h ≡ f a' b' c' d' e' h'
cong₆ f refl refl refl refl refl refl = refl

------------------------------------------------------------------------
-- the two weakenings
------------------------------------------------------------------------

w : {Γ : Cx} → RTm Γ → RTm (Γ ∙)
w = renTm vs

wᶠ : {Γ : Cx} → RTm (Γ ∙) → RTm ((Γ ∙) ∙)
wᶠ = renTm (extR vs)

⊢wkᶠ : {Γ : Ctx} {A B : RTy ⌊ Γ ⌋} {t : RTm (⌊ Γ ⌋ ∙)} {T : RTy (⌊ Γ ⌋ ∙)} →
       (Γ ▹ A) ⊢ t ∷ T → ((Γ ▹ B) ▹ renTy vs A) ⊢ wᶠ t ∷ renTy (extR vs) T
⊢wkᶠ d = ren-lemma d (Ren⊢-ext there)

------------------------------------------------------------------------
-- substitution vs weakening — the ETA half (no case analysis)
------------------------------------------------------------------------

sub-w : {Γ Δ : Cx} {σ : Sub Γ Δ} (t : RTm Γ) →
        subTm (extS σ) (w t) ≡ w (subTm σ t)
sub-w t = trans (subTm-renTm t) (sym (renTm-subTm t))

sub-w² : {Γ Δ : Cx} {σ : Sub Γ Δ} (t : RTm Γ) →
         subTm (extS (extS σ)) (w (w t)) ≡ w (w (subTm σ t))
sub-w² {σ = σ} t = trans (sub-w {σ = extS σ} (w t)) (cong w (sub-w t))

sub-w³ : {Γ Δ : Cx} {σ : Sub Γ Δ} (t : RTm Γ) →
         subTm (extS (extS (extS σ))) (w (w (w t))) ≡ w (w (w (subTm σ t)))
sub-w³ {σ = σ} t = trans (sub-w {σ = extS (extS σ)} (w (w t))) (cong w (sub-w² t))

-- ⚠ a fourth rung, wanted by D7's successor case (`aSBr` carries FIVE
--   weakenings on the step).  ⭐ D5's argument applies: these are iterates
--   of one lemma and want indexing, not listing.
sub-w⁴ : {Γ Δ : Cx} {σ : Sub Γ Δ} (t : RTm Γ) →
         subTm (extS (extS (extS (extS σ)))) (w (w (w (w t))))
       ≡ w (w (w (w (subTm σ t))))
sub-w⁴ {σ = σ} t =
  trans (sub-w {σ = extS (extS (extS σ))} (w (w (w t)))) (cong w (sub-w³ t))

ren-w : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm Γ) →
        renTm (extR ρ) (w t) ≡ w (renTm ρ t)
ren-w t = trans (renTm-renTm t) (sym (renTm-renTm t))

ren-w² : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm Γ) →
         renTm (extR (extR ρ)) (w (w t)) ≡ w (w (renTm ρ t))
ren-w² {ρ = ρ} t = trans (ren-w {ρ = extR ρ} (w t)) (cong w (ren-w t))

ren-w³ : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm Γ) →
         renTm (extR (extR (extR ρ))) (w (w (w t))) ≡ w (w (w (renTm ρ t)))
ren-w³ {ρ = ρ} t = trans (ren-w {ρ = extR (extR ρ)} (w (w t))) (cong w (ren-w² t))

ren-sub : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm Γ) →
          renTm ρ t ≡ subTm (λ x → var (ρ x)) t
ren-sub {ρ = ρ} t = trans (cong (renTm ρ) (sym (subTm-id t)))
                          (renTm-subTm {σ = idₛ} t)

-- ★★★ THE ONE-BINDER PEEL — `sub-w` then `wk-single`, the composite
--   that appears whenever a term is carried past a binder and then
--   substituted back.
--
-- ⚠⚠ IT HAD **SIX** INDEPENDENT COPIES before being written here:
--   `Gcd/Dvd:414`, `Gcd/IndG:205`, `Gcd/IndG:315` (as `p₁`),
--   `Gcd/StepExt:488`, `Comparison/GcdIndStepConcrete:118` (all as
--   `peel₁`), and `Knot/Build:467` as `rtA` — the last already
--   generalised in the substituted term, which is why it served three
--   positions there.  ⇒ every one of them a `where`-bound proof, so
--   nothing could find the others.
sub-w-single : {Γ : Cx} {v : RTm Γ} (t : RTm Γ) →
               subTm (extS (single v)) (w (w t)) ≡ w t
sub-w-single {v = v} t =
  trans (sub-w {σ = single v} (w t)) (cong w (wk-single {v = v} t))

nrs-w : {Γ : Cx} (t : RTm Γ) → subTm nrs (w t) ≡ w (w t)
nrs-w t = trans (subTm-renTm t) (sym (trans (renTm-renTm t) (ren-sub t)))

------------------------------------------------------------------------
-- the TYPE-level twins
------------------------------------------------------------------------

wk-singleTy : {Γ : Cx} {v : RTm Γ} (T : RTy Γ) → subTy (single v) (renTy vs T) ≡ T
wk-singleTy T = trans (subTy-renTy T) (subTy-id T)

-- ★★★ SUBSTITUTING BY A RENAMING **IS** RENAMING — the type-level twin
--   of `ren-sub`.
--
-- ⚠⚠ THIS WAS TRAPPED IN A `where` CLAUSE inside `nrs-wTy`, and
--   `Lib/IPay`'s `iatCon-wf` spike stalled for want of exactly it —
--   its note reads "what is missing is the last hop, «substituting by a
--   renaming IS renaming» ⇒ look for that lemma before writing one."
--   ★ It was three files away, one scope too deep to find.
--
-- ⇒ a `where`-bound lemma is INVISIBLE to search.  If it is general in
--   its own right, it belongs at top level even when it has one
--   customer — the cost of hoisting is a line, the cost of not doing so
--   was a blocked generalisation.
ren-subTy : {Γ Δ : Cx} {ρ : Ren Γ Δ} (T : RTy Γ) →
            renTy ρ T ≡ subTy (λ x → var (ρ x)) T
ren-subTy {ρ = ρ} T = trans (cong (renTy ρ) (sym (subTy-id T)))
                            (renTy-subTy T)

nrs-wTy : {Γ : Cx} (T : RTy Γ) → subTy nrs (renTy vs T) ≡ renTy vs (renTy vs T)
nrs-wTy T =
  trans (subTy-renTy T)
        (sym (trans (renTy-renTy T) (ren-subTy T)))

ren-wTy : {Γ Δ : Cx} {ρ : Ren Γ Δ} (T : RTy Γ) →
          renTy (extR ρ) (renTy vs T) ≡ renTy vs (renTy ρ T)
ren-wTy T = trans (renTy-renTy T) (sym (renTy-renTy T))

------------------------------------------------------------------------
-- ⚠ the FAMILY lemmas — each needs a pointwise bridge (P1)
------------------------------------------------------------------------

wᶠ-single : {Γ : Cx} {v : RTm Γ} (t : RTm (Γ ∙)) →
            subTm (extS (single v)) (wᶠ t) ≡ t
wᶠ-single t =
  trans (subTm-renTm t) (trans (subTm-cong bridge t) (subTm-id t))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl

wᶠ¹-single : {Γ : Cx} (t : RTm (Γ ∙)) →
             subTm (single (var vz)) (wᶠ t) ≡ t
wᶠ¹-single t =
  trans (subTm-renTm t) (trans (subTm-cong bridge t) (subTm-id t))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl

wᶠ²-single : {Γ : Cx} (t : RTm (Γ ∙)) →
             subTm (single (var (vs vz))) (wᶠ (wᶠ t)) ≡ w t
wᶠ²-single t =
  trans (subTm-renTm (wᶠ t))
        (trans (subTm-renTm t)
               (trans (subTm-cong bridge t) (sym (ren-sub'' t))))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl
    -- ⚠ was a local copy of the top-level `ren-sub` above.
    ren-sub'' : (u : RTm _) → renTm vs u ≡ subTm (λ x → var (vs x)) u
    ren-sub'' u = ren-sub u

-- ⚠ THE PATTERN, and it is a ladder in waiting: `single (var (vs^(n-1) vz))`
--   collapses `n` family-weakenings to `n-1` ordinary ones.  Three rungs
--   so far — the branch depth decides which you need, and (0,S) wanted the
--   third.  Worth indexing (D5) if a fourth ever appears.
wᶠ³-single : {Γ : Cx} (t : RTm (Γ ∙)) →
             subTm (single (var (vs (vs vz)))) (wᶠ (wᶠ (wᶠ t))) ≡ w (w t)
wᶠ³-single t =
  trans (subTm-renTm (wᶠ (wᶠ t)))
        (trans (subTm-renTm (wᶠ t))
               (trans (subTm-renTm t)
                      (trans (subTm-cong bridge t) (sym (ren-sub'' t)))))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl
    ren-sub'' : (u : RTm _) → renTm vs (renTm vs u) ≡ subTm (λ x → var (vs (vs x))) u
    ren-sub'' u = trans (renTm-renTm u) (ren-sub u)

wᶠ-nrs : {Γ : Cx} (t : RTm (Γ ∙)) → subTm (extS nrs) (wᶠ t) ≡ wᶠ (wᶠ t)
wᶠ-nrs t =
  trans (subTm-renTm t)
        (trans (subTm-cong bridge t)
               (sym (trans (renTm-renTm t) (ren-sub' t))))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl
    -- ⚠ was a local copy of the top-level `ren-sub` above.
    ren-sub' : (u : RTm _) → renTm _ u ≡ subTm (λ x → var _) u
    ren-sub' u = ren-sub u

ren-wᶠ : {Γ Δ : Cx} {ρ : Ren Γ Δ} (t : RTm (Γ ∙)) →
         renTm (extR (extR ρ)) (wᶠ t) ≡ wᶠ (renTm (extR ρ) t)
ren-wᶠ t =
  trans (renTm-renTm t) (trans (renTm-cong bridge t) (sym (renTm-renTm t)))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = refl

-- the TYPE-level twin of `sub-w`, by the same eta observation (P1: this
-- one moves no family, so no bridge).  ★ Lifted here 2026-08-12; it was local to a spike.
sub-wTy : {Γ Δ : Cx} {σ : Sub Γ Δ} (T : RTy Γ) →
          subTy (extS σ) (renTy vs T) ≡ renTy vs (subTy σ T)
sub-wTy T = trans (subTy-renTy T) (sym (renTy-subTy T))

-- ★ …and the FAMILY twin, which by P1 needs a pointwise BRIDGE — it moves
--   a family under `extR`.  `wᶠ-single` and `wᶠ-nrs` are its two special
--   cases; the ASSEMBLY needs the general σ, because the outer motive is
--   instantiated at an arbitrary bound.
-- ⚠ The bridge's successor case is exactly `ren-w` at `ρ := vs`: both
--   composites weaken `σ x` twice, one through `extR vs ∘ᵣ vs` and one
--   through `vs ∘ᵣ vs`, and those are the same function only after the
--   variable is cased on.
wᶠ-sub : {Γ Δ : Cx} {σ : Sub Γ Δ} (t : RTm (Γ ∙)) →
         subTm (extS (extS σ)) (wᶠ t) ≡ wᶠ (subTm (extS σ) t)
wᶠ-sub {σ = σ} t =
  trans (subTm-renTm t)
        (trans (subTm-cong bridge t) (sym (renTm-subTm t)))
  where
    bridge : ∀ x → _
    bridge vz     = refl
    bridge (vs x) = sym (ren-w {ρ = vs} (σ x))

------------------------------------------------------------------------
-- ★★ D5 — ITERATED WEAKENING, INDEXED RATHER THAN ENUMERATED.
--
-- Every combinator so far grew its own hand-written ladder — `lStepT-w²⁻⁸`,
-- `auxBody-w²⁻⁷`, `auxMotB-w²⁻⁹`, `aAuxB-w²/⁵`, `aStepT-w⁴` — because each
-- branch depth needs one more rung.  Four combinators, all listing iterates
-- of ONE lemma.  These are that lemma, indexed by the depth.
--
-- ⚠ The `-w^` ladder for a given combinator is then THREE LINES and covers
--   every depth, instead of one definition per rung.  See `LibAmrec`.
------------------------------------------------------------------------

infixl 6 _∙^_
_∙^_ : Cx → ℕ → Cx
Γ ∙^ zero  = Γ
Γ ∙^ suc n = (Γ ∙^ n) ∙

-- ordinary weakening, n times
w^ : {Γ : Cx} (n : ℕ) → RTm Γ → RTm (Γ ∙^ n)
w^ zero    t = t
w^ (suc n) t = w (w^ n t)

wTy^ : {Γ : Cx} (n : ℕ) → RTy Γ → RTy (Γ ∙^ n)
wTy^ zero    T = T
wTy^ (suc n) T = renTy vs (wTy^ n T)

-- ★ FAMILY weakening, n times: the family's own variable stays on top and
--   n slots are inserted beneath it.
wᶠ^ : {Γ : Cx} (n : ℕ) → RTm (Γ ∙) → RTm ((Γ ∙^ n) ∙)
wᶠ^ zero    t = t
wᶠ^ (suc n) t = wᶠ (wᶠ^ n t)

------------------------------------------------------------------------
-- ★★★ AN `extS`-LIFTED SUBSTITUTION CANCELS ONE WEAKENING — and the
--     instances COMPOSE, so each depth is one line given the previous.
--
--   subTm (extSᵏ (single u)) (wᵏ⁺¹ t) ≡ wᵏ t
--
-- ⚠ GENERAL — no gcd content.  This is `wkS2`/`wkS3`/`wkS3e` generalised in
--   the LIFTING DEPTH; those three exist only at the depths gcd happened to
--   need.  Belongs in `…LibWk` beside `sub-w`; kept here while iterating.
------------------------------------------------------------------------

pw1 : {Γ' : Cx} {u : RTm Γ'} (t : RTm Γ') →
      subTm (extS (single u)) (w (w t)) ≡ w t
pw1 {u = u} t = trans (sub-w {σ = single u} (w t)) (cong w (wk-single t))

pw2 : {Γ' : Cx} {u : RTm Γ'} (t : RTm Γ') →
      subTm (extS (extS (single u))) (w (w (w t))) ≡ w (w t)
pw2 {u = u} t =
  trans (sub-w {σ = extS (single u)} (w (w t))) (cong w (pw1 {u = u} t))

pw3 : {Γ' : Cx} {u : RTm Γ'} (t : RTm Γ') →
      subTm (extS (extS (extS (single u)))) (w (w (w (w t)))) ≡ w (w (w t))
pw3 {u = u} t =
  trans (sub-w {σ = extS (extS (single u))} (w (w (w t)))) (cong w (pw2 {u = u} t))

-- ★ one deeper again — the `natrec` SUCCESSOR branch sits two slots below
--   the zero branch, so its parameter needs this depth.
pw4 : {Γ' : Cx} {u : RTm Γ'} (t : RTm Γ') →
      subTm (extS (extS (extS (extS (single u))))) (w (w (w (w (w t)))))
    ≡ w (w (w (w t)))
pw4 {u = u} t =
  trans (sub-w {σ = extS (extS (extS (single u)))} (w (w (w (w t)))))
        (cong w (pw3 {u = u} t))

-- ★ one deeper still — the successor branch's BODY, under its `lam`.  Route
--   8 builds `⊢S3s` at the final context, and the `n'` slot arrives there
--   through `extS⁵`.
pw5 : {Γ' : Cx} {u : RTm Γ'} (t : RTm Γ') →
      subTm (extS (extS (extS (extS (extS (single u)))))) (w (w (w (w (w (w t))))))
    ≡ w (w (w (w (w t))))
pw5 {u = u} t =
  trans (sub-w {σ = extS (extS (extS (extS (single u))))} (w (w (w (w (w t))))))
        (cong w (pw4 {u = u} t))

------------------------------------------------------------------------
-- ★★ TWO MORE CANCELS, both from gap A's equation 4.
------------------------------------------------------------------------

-- ★ `wk-single` with a FAMILY weakening on the inside.  Applying an IH
--   substitutes the argument into the codomain, and the measure slot comes
--   back as `subTm (single v) (wᶠ (w t))`.
-- ⚠ When the slot is a de Bruijn VARIABLE that reduces definitionally and
--   no lemma is needed; at an abstract TERM it does not.  `ren-w` fuses the
--   two renamings, `wk-single` cancels the result.
wfw-single : {Γ : Cx} {v : RTm (Γ ∙)} (t : RTm Γ) →
             subTm (single v) (wᶠ (w t)) ≡ w t
wfw-single {v = v} t =
  trans (cong (subTm (single v)) (ren-w t)) (wk-single (w t))

------------------------------------------------------------------------
-- ★★★ THE CANCELLATION LAW, GENERIC IN THE DEPTH.
--
--   Every `pwᵏ`/`wkSᵏ`/`w²-single` above is this lemma at one particular
--   lifting depth.  The caller supplies only the POINTWISE fact that the
--   composite `σ ∘ ρ` is the identity on variables — which is `refl`
--   whenever the composite computes, and a three-case bridge when it does
--   not.  Nested weakenings collapse (`renTm-renTm`) and nested
--   substitutions collapse (`subTm-subTm`) BEFORE this applies, which is
--   why one law covers depths 1 through 7.
--
-- ⚠ Promoted here from `…ExamplesGcdStep`, where it was proved for gap A's
--   equations 3 and 4.  It has no gcd content and never did.
------------------------------------------------------------------------

wkGen : {Γ Δ : Cx} {σ : Sub Δ Γ} {ρ : Ren Γ Δ} →
        ((x : Var Γ) → σ (ρ x) ≡ var x) →
        (t : RTm Γ) → subTm σ (renTm ρ t) ≡ t
wkGen h t = trans (subTm-renTm t) (trans (subTm-cong h t) (subTm-id t))

-- ★★ …and the version landing on a RENAMED target rather than on `t`.
--   ⚠ The `single`-headed composites return `t` EXACTLY; the `extS`-headed
--   ones return `t` STILL WEAKENED.  Same three moves, one different
--   endpoint — `ren-as-sub` where `wkGen` uses `subTm-id`.
wkGenR : {Γ Δ Θ : Cx} {σ : Sub Δ Θ} {ρ : Ren Γ Δ} {ρ' : Ren Γ Θ} →
         ((x : Var Γ) → σ (ρ x) ≡ var (ρ' x)) →
         (t : RTm Γ) → subTm σ (renTm ρ t) ≡ renTm ρ' t
wkGenR {ρ' = ρ'} h t =
  trans (subTm-renTm t) (trans (subTm-cong h t) (sym (ren-as-sub ρ' t)))

-- ★ `wk-single` one binder deeper — what a `natrec`'s SUCCESSOR branch
--   needs, since `natrec-suc` binds the predecessor AND the IH.
w²-single : {Γ : Cx} {x : RTm Γ} (t : RTm ((Γ ∙) ∙)) →
            subTm (extS (extS (single x))) (renTm (extR (extR vs)) t) ≡ t
w²-single {x = x} t = wkGen br t
  where
    br : ∀ v → extS (extS (single x)) (extR (extR vs) v) ≡ var v
    br vz          = refl
    br (vs vz)     = refl
    br (vs (vs u)) = refl

------------------------------------------------------------------------
-- ★★★ INSERTING ONE BINDER **BELOW THE TOP TWO** — the renaming
-- `extR (extR vs)`, as a `Ren⊢`.
--
-- ⚠⚠ `Ren⊢-ext (Ren⊢-ext there)` IS NOT THIS.  `Ren⊢-ext` renames the
--   type it extends by, so its target context reads
--   `renTy vs A` where a caller with a renaming-STABLE `A` (`εwkTy I`,
--   say) has plain `A`.  Those agree only PROPOSITIONALLY, and `Ren⊢` is
--   a FUNCTION type — no `⊢-cast` reaches it.  ⇒ it must be pointwise.
--
-- ★ AND THE MIDDLE TYPE IS A SEPARATE PARAMETER, not `renTy vs A`.  It
--   cannot be `A` itself: the source has `A : RTy ⌊ Γ ⌋` while the
--   target needs it one binder deeper.  So the caller supplies `A'` and
--   the equation relating them — which for `εwkTy I` is `εwk-ren`.
------------------------------------------------------------------------

Ren⊢-ins² : {Γ : Ctx} {X A : RTy ⌊ Γ ⌋} {A' B : RTy (⌊ Γ ⌋ ∙)} →
            renTy vs A ≡ A' →
            Ren⊢ ((Γ ▹ A) ▹ B) (((Γ ▹ X) ▹ A') ▹ renTy (extR vs) B)
                 (extR (extR vs))
-- ★ each case is `ren-wTy`, once per binder the variable sits under.
Ren⊢-ins² {B = B} eqA here =
  ∋-cast (sym (ren-wTy {ρ = extR vs} B)) here
Ren⊢-ins² {A = A} eqA (there here) =
  ∋-cast (sym (trans (ren-wTy {ρ = extR vs} (renTy vs A))
                     (trans (cong (renTy vs) (ren-wTy {ρ = vs} A))
                            (cong (λ z → renTy vs (renTy vs z)) eqA))))
         (there here)
Ren⊢-ins² eqA (there (there {A = A₀} v)) =
  ∋-cast (sym (trans (ren-wTy {ρ = extR vs} (renTy vs A₀))
                     (cong (renTy vs) (ren-wTy {ρ = vs} A₀))))
         (there (there (there v)))

------------------------------------------------------------------------
-- ★★★ THE DESCENT THROUGH AN `iinst`ed MOTIVE'S Π-TOWER.
--
-- A two-slot motive reaches its own binders as `var (vs^k vz)`, and
-- `iinst` plus each `⊢app` wraps ONE more substitution around it.  These
-- two peel the resulting tower for the two positions that actually
-- occur: a variable at de Bruijn 2 under three substitutions, and one at
-- de Bruijn 3 under four.
--
-- ⚠ THEY MENTION NO MOTIVE.  Written for `Knot/SubMot`'s `subMotK` and
--   moved here at the THIRD customer (`ipayTyMotK`, `ihTyMotK` — both of
--   which chose their passenger ORDER so as to land on these shapes).
--   ★ Ordering a motive's passengers to make the tower SHORT is the same
--     act as making it a REUSE.
--
-- ⭐ `sub-w`'s note applies: these are iterates of one lemma and want
--   INDEXING, not listing.  Two rungs is where it stops being worth it.
------------------------------------------------------------------------

-- ★ THE THREE RUNGS, and each is `sub-w` then the next one down.  The
--   innermost `subTm (extS³ (single J)) (var (vs³ vz))` computes to
--   `w³ J` on its own — variables are where substitution still reduces.
towerJ : {Γ : Cx} (sb m u J : RTm Γ) →
         subTm (single sb)
           (subTm (extS (single m))
             (subTm (extS (extS (single u)))
               (subTm (extS (extS (extS (single J)))) (var (vs (vs (vs vz)))))))
           ≡ J
towerJ sb m u J = trans (cong (λ z → subTm (single sb) (subTm (extS (single m)) z)) rA)
                   (trans (cong (subTm (single sb)) rB) rC)
  where
    rB' : subTm (extS (single u)) (w (w J)) ≡ w J
    rB' = trans (sub-w {σ = single u} (w J)) (cong w (wk-single {v = u} J))
    rA : subTm (extS (extS (single u))) (w (w (w J))) ≡ w (w J)
    rA = trans (sub-w {σ = extS (single u)} (w (w J))) (cong w rB')
    rB : subTm (extS (single m)) (w (w J)) ≡ w J
    rB = trans (sub-w {σ = single m} (w J)) (cong w (wk-single {v = m} J))
    rC : subTm (single sb) (w J) ≡ J
    rC = wk-single {v = sb} J

-- ⚠ AND THE ARGUMENT'S TOWER IS ONE RUNG SHORTER — it is read under the
--   Π, so `iinst`'s outermost substitution has not reached it.
towerA : {Γ : Cx} (m u J : RTm Γ) →
         subTm (single m)
           (subTm (extS (single u))
             (subTm (extS (extS (single J))) (var (vs (vs vz))))) ≡ J
towerA m u J =
  trans (cong (subTm (single m)) (sub-w-single J)) (wk-single {v = m} J)

-- ★★★ THE THREE-RUNG DESCENT ON A **WEAKENED TERM**, as `towerA`/`towerJ`
--   are on a VARIABLE.
--
-- ⚠ A method's payload field arrives weakened past the binders that
--   follow it and then substituted back, once per `⊢app` — so reading a
--   field out of it leaves `subTm σ₁ (subTm σ₂ (subTm σ₃ (w³ t)))` where
--   the towers leave `var (vs³ vz)`.  Same shape, different carrier, and
--   `Knot/RenSpec` is the first customer.
sub-w³-single : {Γ : Cx} {a b c : RTm Γ} (t : RTm Γ) →
                subTm (single a)
                  (subTm (extS (single b))
                    (subTm (extS (extS (single c))) (w (w (w t)))))
                  ≡ t
sub-w³-single {a = a} {b = b} {c = c} t =
  trans (cong (λ z → subTm (single a) (subTm (extS (single b)) z))
              (trans (sub-w² {σ = single c} (w t))
                     (cong (λ z → w (w z)) (wk-single {v = c} t))))
        (trans (cong (subTm (single a))
                     (trans (sub-w {σ = single b} (w t))
                            (cong w (wk-single {v = b} t))))
               (wk-single {v = a} t))

-- ★ …and the TWO-rung form.  ⚠ The count is the number of binders that
--   follow the payload in the METHOD, which is one per motive passenger
--   plus the IH tuple — so it differs per motive and both are needed.
sub-w²-single : {Γ : Cx} {a b : RTm Γ} (t : RTm Γ) →
                subTm (single a) (subTm (extS (single b)) (w (w t))) ≡ t
sub-w²-single {a = a} {b = b} t =
  trans (cong (subTm (single a))
              (trans (sub-w {σ = single b} (w t)) (cong w (wk-single {v = b} t))))
        (wk-single {v = a} t)

-- ★ `towerA`'s SIBLING AT DE BRUIJN 1 — the MIDDLE substitution's value.
--
-- ⚠ `towerA`/`towerJ` read a variable at index 2 and 3 and return the
--   INNERMOST substitution's value; a method's PAYLOAD sits at index 1
--   and returns the MIDDLE one.  Any further inert layers compute away
--   (`extS² σ (vs vz) = var (vs vz)`), so two rungs is the general form.
towerP : {Γ : Cx} (a b : RTm Γ) →
         subTm (single a) (subTm (extS (single b)) (var (vs vz))) ≡ b
towerP a b = wk-single {v = a} b
