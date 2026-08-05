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
module poc.OCP0009.NbEPDirDBType where

open import normalizer.Syntax.Types using ( _≡_; refl )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; RTm; var; lam; app
        ; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap
        ; Id; ⌜Id⌝; idrefl; jsub
        ; Unit; Nat; unit; nzero; nsuc; natrec; extS; ⌜Nat⌝; ⌜Unit⌝
        ; Ren; extR; Sub; subTy; subTm; renTy; renTm )
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; false; occTm; pw?; stkC?; flat?; pwBody; pwShift )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Single substitution (what β and dependent `app` plug in).
------------------------------------------------------------------------

single : RTm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x

-- ★ WF-axis stage A: the successor-instance substitution — reads the
-- motive M (over Γ, number) at `nsuc` of the number, in the recursor's
-- step context (Γ, number, IH).
nrs : Sub (Γ ∙) ((Γ ∙) ∙)
nrs vz     = nsuc (var (vs vz))
nrs (vs x) = var (vs (vs x))

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
  -- J at Hom-codes over PERMANENTLY-STABLE spines (`stkC?` excludes
  -- ⌜Π⌝-able codes — those paths unfold to lambdas — and neutrals,
  -- which substitution could make ⌜Π⌝-able):
  tr-J-Hom : (c a m : RTm (Γ ∙)) (c₁ a₁ b₁ s e : RTm Γ) →
             stkC? c₁ ≡ true →
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

data _⊢_∷_ where
  ⊢var  : ∀ {Γ x A}     → Γ ∋ x ∷ A → Γ ⊢ var x ∷ A
  ⊢lam  : ∀ {Γ A B t}   → Γ ⊢ty A → (Γ ▹ A) ⊢ t ∷ B → Γ ⊢ lam t ∷ Π A B
  ⊢app  : ∀ {Γ A B t u} → Γ ⊢ t ∷ Π A B → Γ ⊢ u ∷ A →
                          Γ ⊢ app t u ∷ subTy (single u) B
  ⊢pair : ∀ {Γ A B a b} → (Γ ▹ A) ⊢ty B →
                          Γ ⊢ a ∷ A → Γ ⊢ b ∷ subTy (single a) B →
                          Γ ⊢ pair a b ∷ Σ' A B
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
  ⊢tr   : ∀ {Γ A c a p e t u} →
          (Γ ▹ A) ⊢ c ∷ U → (Γ ▹ A) ⊢ a ∷ El c →
          (Γ ▹ A) ⊢ var vz ∷ El c →
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
