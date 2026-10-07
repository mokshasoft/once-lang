-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 21 — INTRINSIC TYPING over a SIGNATURE.
--
-- Parameters (PLAN-REF, D082): the signature 𝒮 (the definition context;
-- reduction, re-exported from `Spec/Reduction 𝒮`) and `n`, the number of
-- its names a derivation may USE (`⊢ref`).  An entry d is typed at n = d,
-- its prefix, under the SAME reduction as every other entry.
--
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
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( KSig )
module DirectedHoTT.Spec.Typing (𝒮 : KSig) (n : ℕ) where
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
        ; fzero; fsuc; fcase; fcase0; psplit; ref; KSig; _<ˢ_ )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; occTm; pw?; stkC?; stkA?; flat?; pwBody; pwShift
        ; NoNatC; nnc-base; nnc-Unit; nnc-Π; nnc-Σ; nnc-Hom; nnc-Id )
open import DirectedHoTT.Spec.Reduction 𝒮 public

private
  variable
    Γ : Cx

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
  ⊢⌜IMu⌝  : ∀ {Γ I D i} → Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ i ∷ El I → Γ ⊢ ⌜IMu⌝ I D i ∷ U
  ⊢⌜Fin⌝  : ∀ {Γ n} → Γ ⊢ n ∷ Nat → Γ ⊢ ⌜Fin⌝ n ∷ U
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
  ⊢dι   : ∀ {Γ I} → Γ ⊢ I ∷ U → Γ ⊢ dι ∷ Desc I
  ⊢dσ   : ∀ {Γ I S f} → Γ ⊢ I ∷ U → Γ ⊢ S ∷ U →
          Γ ⊢ f ∷ Π (El S) (Desc (renTm vs I)) → Γ ⊢ dσ S f ∷ Desc I
  ⊢dρ   : ∀ {Γ I j C} → Γ ⊢ I ∷ U → Γ ⊢ j ∷ El I → Γ ⊢ C ∷ Desc I → Γ ⊢ dρ j C ∷ Desc I
  -- `⊢dpay` types each term it contains (the index code included).
  ⊢dpay : ∀ {Γ I D C} → Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ C ∷ Desc I →
          Γ ⊢ dpay I D C ∷ U
  -- ★ D074: a constructor at index `i` is a payload of the telescope
  --   `D i` — the FIBRE over `i`.  Its type mentions the index code, so it
  --   types it (validity).
  ⊢con  : ∀ {Γ I D i p} → Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ i ∷ El I →
          Γ ⊢ p ∷ El (dpay I D (app D i)) → Γ ⊢ con p ∷ IMu I D i
  ⊢dih  : ∀ {Γ I D M e C p} →
          Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → motCtx Γ I D ⊢ty M → Γ ⊢ e ∷ MethTy I D M →
          Γ ⊢ C ∷ Desc I → Γ ⊢ p ∷ El (dpay I D C) →
          Γ ⊢ dih D e C p ∷ DIh D M C p
  ⊢ielim : ∀ {Γ I D M e i t} →
           Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → motCtx Γ I D ⊢ty M → Γ ⊢ e ∷ MethTy I D M →
           Γ ⊢ i ∷ El I → Γ ⊢ t ∷ IMu I D i →
           Γ ⊢ ielim D i e t ∷ iinst i t M
  -- tags: Fin (n+1) ≅ 1 + Fin n, and the empty Fin 0.  ★ S7b step 2: the
  --   size `n` is a Nat TERM (`fzero` types it: nothing else does).
  ⊢fzero  : ∀ {Γ n} → Γ ⊢ n ∷ Nat → Γ ⊢ fzero ∷ Fin (nsuc n)
  ⊢fsuc   : ∀ {Γ n t} → Γ ⊢ t ∷ Fin n → Γ ⊢ fsuc t ∷ Fin (nsuc n)
  ⊢fcase  : ∀ {Γ n P t a b} →
            (Γ ▹ Fin (nsuc n)) ⊢ty P → Γ ⊢ t ∷ Fin (nsuc n) →
            Γ ⊢ a ∷ subTy (single fzero) P → (Γ ▹ Fin n) ⊢ b ∷ subTy fsucS P →
            Γ ⊢ fcase t a b ∷ subTy (single t) P
  ⊢fcase0 : ∀ {Γ P t} → (Γ ▹ Fin nzero) ⊢ty P → Γ ⊢ t ∷ Fin nzero →
            Γ ⊢ fcase0 t ∷ subTy (single t) P
  -- ★ Σ-INDUCTION (D071)
  ⊢psplit : ∀ {Γ A B P q b} →
            Γ ⊢ty A → (Γ ▹ A) ⊢ty B → (Γ ▹ Σ' A B) ⊢ty P → Γ ⊢ q ∷ Σ' A B →
            ((Γ ▹ A) ▹ B) ⊢ b ∷ subTy pairS P →
            Γ ⊢ psplit b q ∷ subTy (single q) P
  -- ★ a definition is typed by its body's typing in the EMPTY context —
  --   one shared proof per definition, weakened to every use
  -- ★ a reference is typed by its DECLARATION alone (PLAN-REF, D082): a
  --   projection from the signature, among the first n names
  ⊢ref : ∀ {Γ d} → d <ˢ n → Γ ⊢ ref d ∷ εwkTy (KSig.type 𝒮 d)
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
  ty-IMu  : ∀ {Γ I D i} → Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → Γ ⊢ i ∷ El I → Γ ⊢ty IMu I D i
  -- ★ `Desc I` is LARGE (no code); its index must be a code
  ty-Desc : ∀ {Γ I} → Γ ⊢ I ∷ U → Γ ⊢ty Desc I
  ty-DIh  : ∀ {Γ I D M C p} →
            Γ ⊢ I ∷ U → Γ ⊢ D ∷ DescF I → motCtx Γ I D ⊢ty M → Γ ⊢ C ∷ Desc I →
            Γ ⊢ p ∷ El (dpay I D C) → Γ ⊢ty DIh D M C p
  ty-Fin  : ∀ {Γ n} → Γ ⊢ n ∷ Nat → Γ ⊢ty Fin n
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


------------------------------------------------------------------------
-- ★ THE SIGNATURE'S ENTRIES ARE TYPED (PLAN-REF, D082) — the hypothesis
--   δ needs: subject reduction unfolds `ref d` to its body, which must be
--   typed at the reference's declared type.  Stated at THIS judgement's
--   names; `Metatheory/Signature` derives it from the telescope's
--   context formation (each entry typed in its prefix).
------------------------------------------------------------------------

-- an entry: its declared type is well-formed (context formation, as
--   `c-▹`), and its body inhabits it
record EntryOK (d : ℕ) : Set where
  constructor entryOK
  field
    okTy   : ◇ ⊢ty KSig.type 𝒮 d
    okBody : ◇ ⊢ KSig.body 𝒮 d ∷ KSig.type 𝒮 d
open EntryOK public

SigOK : Set
SigOK = ∀ {d} → d <ˢ n → EntryOK d
