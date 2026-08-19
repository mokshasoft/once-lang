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
module poc.OCP0009.NbEPDirDBLibWk where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; Ren
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc
        ; Π; renTy; renTm; subTy; subTm; Sub; extS; extR
        ; subTm-renTm; renTm-subTm; renTm-renTm; subTm-id; subTm-cong
        ; subTy-renTy; subTy-id; renTy-renTy; renTy-subTy; renTm-cong; idₛ )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs; _⊢_∷_; there; wk-single )
open import poc.OCP0009.NbEPDirDBSubj using ( ren-lemma; Ren⊢-ext )

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

nrs-w : {Γ : Cx} (t : RTm Γ) → subTm nrs (w t) ≡ w (w t)
nrs-w t = trans (subTm-renTm t) (sym (trans (renTm-renTm t) (ren-sub t)))

------------------------------------------------------------------------
-- the TYPE-level twins
------------------------------------------------------------------------

wk-singleTy : {Γ : Cx} {v : RTm Γ} (T : RTy Γ) → subTy (single v) (renTy vs T) ≡ T
wk-singleTy T = trans (subTy-renTy T) (subTy-id T)

nrs-wTy : {Γ : Cx} (T : RTy Γ) → subTy nrs (renTy vs T) ≡ renTy vs (renTy vs T)
nrs-wTy T =
  trans (subTy-renTy T)
        (sym (trans (renTy-renTy T) (ren-subTy T)))
  where
    ren-subTy : (T : RTy _) → renTy _ T ≡ subTy (λ x → var _) T
    ren-subTy T = trans (cong (renTy _) (sym (subTy-id T))) (renTy-subTy T)

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
    ren-sub'' : (u : RTm _) → renTm vs u ≡ subTm (λ x → var (vs x)) u
    ren-sub'' u = trans (cong (renTm vs) (sym (subTm-id u))) (renTm-subTm u)

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
    ren-sub' : (u : RTm _) → renTm _ u ≡ subTm (λ x → var _) u
    ren-sub' u = trans (cong (renTm _) (sym (subTm-id u))) (renTm-subTm u)

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
