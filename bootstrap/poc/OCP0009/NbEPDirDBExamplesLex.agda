------------------------------------------------------------------------
-- OCP-0009 — EXAMPLES, WF-AXIS STAGE E: LEXICOGRAPHIC RECURSION.
--
-- Verifies the ARCHITECTURE.md claim that the remaining WF-axis induction
-- forms are DERIVABLE, not new kernel formers.  Nothing here is added to
-- `RTm`/`RTy`/`_⊢_∷_` — this is an object-language DEFINITION built from
-- `natrec`, `ordtr`, `absurd` and Π, so it cannot affect soundness.
--
--     lexrec : ((x : Nat) → ((y) → μ₁ y < μ₁ x → P y)
--                         → ((y) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y)
--                         → P x)
--            → (x : Nat) → P x
--
-- ★ TWO DESIGN POINTS THAT MAKE IT CHEAP ON THIS KERNEL:
--   * the descent is stated with `<` and `≤` — both COMPUTING `Hom Nat` —
--     so NO equality on ℕ is needed (which would drag in `Id`/`jsub`);
--   * TWO recursor arguments instead of one disjunction, so NO COPRODUCT
--     is needed — `RTy` has none.
--
-- ★ THE CARRIER IS `Nat`, deliberately.  Carrier-genericity is verified
--   SEPARATELY by `⊢amrec` (NbEPDirDBExamplesDogfood), which generalises
--   to any `A : U` with its proof UNCHANGED.  What is in doubt here is the
--   NESTING structure, and that is what this file tests.
--
-- ⚠ NO `Acc`, NO fuel, NO `TERMINATING`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLex where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst; ⊥ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; ⌜Hom⌝; ⌜Nat⌝
        ; Π; lam; app; renTy; renTm; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶ᵀ_; Hom-Nat-sz; Hom-Nat-ss
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢absurd; ⊢ordtr
        ; _⊢ty_; ty-El; ty-Nat; ty-U; ty-Π; ty-Hom )
open import poc.OCP0009.NbEPDirDBInj
  using ( red→≅ᵀ; _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBExamplesStrong
  using ( El-homNat; ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesOrd
  using ( ⊢strong-base'; ⊢strong-step )

------------------------------------------------------------------------
-- 1. THE CONTEXT.  `cP : Nat → U` (motive), `μ₁ μ₂ : Nat → Nat` (the two
--    measures), `stp` (the step).  Context variables, so every
--    substitution `natrec`/`app` generates COMPUTES.
------------------------------------------------------------------------

-- ★ SPLIT AT THE `y` BINDER.  The `…body` halves are what a branch's
--   derivation is left with after its FIRST `⊢lam`, so naming them is what
--   lets a recursor argument be split across two modules: the peeled
--   lemma's type is
--     `subTy (extS σ) (subTy (extS σ') (renTy (extR ρ)ⁿ REC_Tbody))`,
--   read off Agda by the probe technique below.  Needed only since the
--   carrier became generic — at the ℕ carrier a whole recursor argument
--   still fit in one module.

-- `μ₁ y < μ₁ x → P y`   — vz = y, vs = x, vs² = μ₂, vs³ = μ₁, vs⁴ = cP, vs⁵ = A
REC1Tbody : RTy (ε ∙ ∙ ∙ ∙ ∙ ∙)
REC1Tbody =
  Π (Hom Nat (nsuc (app (var (vs (vs (vs vz)))) (var vz)))
             (app (var (vs (vs (vs vz)))) (var (vs vz))))
    (El (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz))))

-- `(y : Nat) → μ₁ y < μ₁ x → P y`   — vz = x, vs = μ₂, vs² = μ₁, vs³ = cP,
--                                     vs⁴ = A
REC1T : RTy (ε ∙ ∙ ∙ ∙ ∙)
REC1T = Π (El (var (vs (vs (vs (vs vz))))))  REC1Tbody

-- `μ₂ y < μ₂ x → P y`   — rec₂ after TWO binders (y and the `≤`)
REC2Tbody2 : RTy (ε ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
REC2Tbody2 =
  Π (Hom Nat (nsuc (app (var (vs (vs (vs (vs vz))))) (var (vs vz))))
             (app (var (vs (vs (vs (vs vz))))) (var (vs (vs (vs vz))))))
    (El (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs vz)))))

-- `μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`
-- vz = y, vs = rec1, vs² = x, vs³ = μ₂, vs⁴ = μ₁, vs⁵ = cP, vs⁶ = A
REC2Tbody : RTy (ε ∙ ∙ ∙ ∙ ∙ ∙ ∙)
REC2Tbody =
  Π (Hom Nat (app (var (vs (vs (vs (vs vz))))) (var vz))
             (app (var (vs (vs (vs (vs vz))))) (var (vs (vs vz)))))
    REC2Tbody2

-- `(y : Nat) → μ₁ y ≤ μ₁ x → μ₂ y < μ₂ x → P y`
-- vz = rec1, vs = x, vs² = μ₂, vs³ = μ₁, vs⁴ = cP, vs⁵ = A
REC2T : RTy (ε ∙ ∙ ∙ ∙ ∙ ∙)
REC2T = Π (El (var (vs (vs (vs (vs (vs vz))))))) REC2Tbody

-- vz = μ₂, vs = μ₁, vs² = cP
LStepT : RTy (ε ∙ ∙ ∙ ∙)
LStepT =
  Π (El (var (vs (vs (vs vz))))) (Π REC1T (Π REC2T
    (El (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs (vs vz)))))))

Γ₅ : Ctx
Γ₅ = ((((◇ ▹ U) ▹ Π (El (var vz)) U) ▹ Π (El (var (vs vz))) Nat)
        ▹ Π (El (var (vs (vs vz)))) Nat) ▹ LStepT

------------------------------------------------------------------------
-- ★★ 2a. THE MOTIVE COMBINATOR — one place where the measures are named.
--
-- ⚠ WHY THIS EXISTS.  `lexAuxMot`, `M0lex` and `M1lex` are the SAME
--   invariant at three different bounds, but written as raw de Bruijn
--   they were three independent hand-counts.  The measure bug (§2) was a
--   `vs⁵` written as `vs⁶` in ONE of them — a slip no reviewer catches.
--
-- ★ THE FIX, AND ITS HONEST LIMIT.  A measure has a DIFFERENT INDEX in
--   every context, so a combinator cannot refer to μ₂ by name; it must
--   take the measures as ARGUMENTS.  That is the whole trick: the caller
--   supplies `cP μ₁ μ₂` at its own scope, and ALL the binder weakening
--   happens here, once.  Getting it wrong now means passing μ₁ where you
--   meant μ₂ — a NAME slip at the call site, which review does catch —
--   instead of a numeral slip buried in a `vs` tower, which it does not.
--   ⚠ It is still NOT a type error: μ₁ and μ₂ are both `Π Nat Nat` and
--     nothing in this kernel can separate them.  See §6.
--
--     auxBody cP μ₁ μ₂ b₁ b₂  =  (x : Nat) → μ₁ x ≤ b₁ → μ₂ x ≤ b₂ → P x
------------------------------------------------------------------------

auxBody : {Γ : Cx} (cA cP μ₁ μ₂ b₁ b₂ : RTm Γ) → RTy Γ
auxBody cA cP μ₁ μ₂ b₁ b₂ =
  Π (El cA)
    (Π (Hom Nat (app (renTm vs μ₁) (var vz)) (renTm vs b₁))
       (Π (Hom Nat (app (renTm vs (renTm vs μ₂)) (var (vs vz)))
                   (renTm vs (renTm vs b₂)))
          (El (app (renTm vs (renTm vs (renTm vs cP))) (var (vs (vs vz)))))))

------------------------------------------------------------------------
-- 2. THE DOUBLY-BOUNDED AUXILIARY.
--
--      aux : (n₁ : Nat) → (n₂ : Nat) → (x : Nat)
--          → μ₁ x ≤ n₁ → μ₂ x ≤ n₂ → P x
--
--    by `natrec` on n₁, and INSIDE the branches, `natrec` on n₂.  That
--    nesting IS the lexicographic order: a `rec₁` call decreases n₁ and
--    RESETS n₂; a `rec₂` call keeps n₁ and decreases n₂.
--
--    vz = n₁, vs = stp, vs² = μ₂, vs³ = μ₁, vs⁴ = cP
------------------------------------------------------------------------

lexAuxMot : RTy (ε ∙ ∙ ∙ ∙ ∙ ∙)
lexAuxMot =
  Π Nat (auxBody (var (vs (vs (vs (vs (vs (vs vz)))))))   -- cA
                 (var (vs (vs (vs (vs (vs vz))))))   -- cP
                 (var (vs (vs (vs (vs vz)))))        -- μ₁
                 (var (vs (vs (vs vz))))             -- μ₂
                 (var (vs vz))                       -- b₁ = n₁
                 (var vz))                           -- b₂ = n₂' (just bound)


------------------------------------------------------------------------
-- 3. THE FOUR BRANCHES, as raw terms.  Generated with a de Bruijn helper
--    rather than hand-counted — at depth 14 hand-counting is the error.
--    ★ every branch is `stp x rec₁ rec₂`; only how rec₁/rec₂ discharge
--      their descent differs, and each is ONE of the two lemmas already
--      machine-checked in ExamplesOrd (`⊢strong-base'` / `⊢strong-step`)
--      or a plain `ordtr` composition of two ≤'s.
------------------------------------------------------------------------

lexZZ : RTm (ε ∙ ∙ ∙ ∙ ∙ ∙)
lexZZ =
  lam (lam (lam (app (app (app (var (vs (vs (vs (vs vz))))) (var (vs (vs vz)))) (lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz))))))))) (lam (lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))))))))

lexZS : RTm (ε ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
lexZS =
  lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) (lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz))))))))) (lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) (ordtr (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var (vs vz)) (var (vs (vs (vs (vs vz))))))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))))))))))

lexSZ : RTm (ε ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
lexSZ =
  lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) (lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs vz)))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz)))))) (natrec unit (var vz) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs vz)))))))) (lam (lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))))))))

lexSS : RTm (ε ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
lexSS =
  lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs vz)))) (lam (lam (app (app (app (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz)))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var vz) (var (vs (vs (vs vz)))))) (natrec unit (var vz) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz)))))))) (lam (lam (lam (app (app (app (var (vs (vs (vs (vs (vs (vs vz))))))) (var (vs (vs vz)))) (ordtr (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))))) (var (vs (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) (var (vs vz)) (var (vs (vs (vs (vs vz))))))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz) (var (vs (vs (vs vz))))))))))))
lexZBr : RTm (ε ∙ ∙ ∙ ∙ ∙)
lexZBr = lam (natrec lexZZ lexZS (var vz))

lexSBr : RTm (ε ∙ ∙ ∙ ∙ ∙ ∙ ∙)
lexSBr = lam (natrec lexSZ lexSS (var vz))

lexAuxTm : RTm (ε ∙ ∙ ∙ ∙ ∙) → RTm (ε ∙ ∙ ∙ ∙ ∙)
lexAuxTm n = natrec lexZBr lexSBr n



------------------------------------------------------------------------
-- ★★ DONE — `lexrec` IS DERIVED, END TO END.
--
-- Four branches, each in its own module (RAM, see below):
--   (0,0) ⊢lexZZ  NbEPDirDBExamplesLexZZ       35.2s / 2.12 GB
--   (0,S) ⊢lexZS  NbEPDirDBExamplesLexZS      100.1s / 4.74 GB
--   (S,0) ⊢lexSZ  NbEPDirDBExamplesLexSZ       91.4s / 4.32 GB
--   (S,S) ⊢lexSS  NbEPDirDBExamplesLexSS{Data,1,2}  — needs `+RTS -c`
-- and the assembly in NbEPDirDBExamplesLexAsm:
--   ⊢lexZBr / ⊢lexSBr  the two inner `natrec`s on n₂
--   ⊢lexAux            the outer `natrec` on n₁
--   ⊢lexrec            aux at μ₁ x, μ₂ x, x and two `⊢le-refl`s, GENERIC in x
--
-- ★ SO THE ARCHITECTURE CLAIM HOLDS: the lexicographic recursor is an
--   object-language DEFINITION over `natrec`/`ordtr`/`absurd`/Π.  Nothing
--   was added to `RTm`/`RTy`/`_⊢_∷_`, so soundness is untouched — which is
--   what this file was written to test.  No `Acc`, no fuel, no
--   `TERMINATING`, no coproduct, and no equality on ℕ.
--
-- ★ WHAT THE DERIVATION BOUGHT beyond itself: it is a MEANING CHECK on the
--   statement.  Writing it found the `lexAuxMot` measure bug (μ₁ where μ₂
--   was meant — see §2), which no amount of `RTy` well-formedness would
--   have caught, and the assembly then forced `lexAuxMot`/`M0lex`/`M1lex`
--   to agree with each other via `⊢natrec`'s motive discipline.
--
-- Everything above TYPECHECKS: `REC1T`, `REC2T`, `LStepT`, `Γ₅` and
-- `lexAuxMot` are well-formed, which settles the part most likely to be
-- wrong — that the lexicographic descent is EXPRESSIBLE in this kernel
-- with no equality on ℕ and no coproduct.
--
-- ALSO VERIFIED (§3): all four branch TERMS typecheck as raw `RTm`s.
-- So the shape of the construction is right; what is unfinished is the
-- TYPING derivation for them.
--
-- ⚠ WHERE IT ACTUALLY STICKS — sharper than "it is a big build".  The
--   descent logic is NOT the problem: each branch's obligations are one
--   application of `⊢strong-base'`, `⊢strong-step` or plain `⊢ordtr`,
--   and those were written out and are believed right.  The blocker is
--   the WEAKENING ARITHMETIC of `stp`'s type: `stp` sits in the context
--   as `renTy vs^k LStepT`, so after `⊢app stp x` the expected types of
--   `rec₁`/`rec₂` are `REC1T`/`REC2T` under a `renTy (extR (extR vs))`
--   chain, and those must line up with the `⊢lam` domains written at
--   CURRENT context indices.  Getting that by hand-counting failed; it
--   wants the expected types read off Agda rather than reconstructed.
--
-- ★ THE PROBE TECHNIQUE THAT WORKS IN BATCH MODE (use this, it is the
--   poor man's agda-mode goal display).  Put a deliberately wrong term
--   where the derivation goes — `⊢nzero` does fine — and Agda's
--   `UnequalTerms` error prints the EXPECTED type in full:
--
--     probe : (Γ₅ ▹ Nat) ⊢ lexZZ ∷ subTy (single nzero) M0lex
--     probe = ⊢lam ty-Nat (⊢lam … (⊢lam … (⊢app (⊢app (⊢app stp x) ⊢nzero) …)))
--                                                                 ↑ prints it
--
--   That told us the expected `rec₁` type is
--     `subTy (single x) (renTy (extR vs)⁵ REC1T)`,
--   which confirms the AMBIENT indices (μ₂/μ₁/cP at 5/6/7) are right.
--   It also hinted the residual mismatch was INSIDE `REC1T`/`REC2T`'s own
--   indexing — `cP` one binder deeper than written.  ★ THAT HINT WAS RIGHT
--   and §5 cashed it: `REC2T`'s RESULT had `cP` at 6 where it must be 7,
--   because three binders (y, le, lt) sit above it.  Now fixed.
--
-- ⚠ AND A CORRECTION worth keeping: "the statement typechecks" is much
--   WEAKER evidence than it sounds.  `REC1T : RTy (ε ∙ ∙ ∙ ∙)` is
--   well-formed for ANY well-scoped index assignment — it says the
--   indices are in SCOPE, not that they denote μ₁/x/cP.  The types
--   themselves were a suspect, not just the derivation — and rightly so:
--   §5 discharges that suspicion with `⊢ty` derivations, and FOUND A REAL
--   BUG doing it.  The types are no longer in doubt; the derivation is.
--
-- ⚠⚠ SECOND BLOCKER, MEASURED 2026-08-06: THE INLINE STYLE DOES NOT BUILD.
--   ✔ RESOLVED for branch (0,0) — see §6/§7.  Split into Def-backed lemmas
--     it checks in 37.6s / 3.01 GB, exit 0.  ★ AND THE VERDICT IS: the
--     branch was CORRECT all along.  It had simply never fitted in memory,
--     so "unfinished" had been hiding "unknown", not "wrong".
--   ⚠ STILL OPEN for the other three branches and the three assembly
--     layers.  At 3.01 GB for ONE branch they will not share a module on a
--     7.5 GiB box — plan one module per branch, which the Def-backed split
--     now makes possible (a branch exports as a name, not a term).
--
--   A first `⊢lexZZ` written as ONE nested term ran 349s to 4.69 GB and was
--   killed WITHOUT a verdict — so it was not known to be wrong OR right.
--   Half of it (one of the two `⊢lam`-nest arguments) does check, in
--   13.6s / 1.34 GB.  Growth is SUPERLINEAR, and four branches plus three
--   assembly layers are still to come.  Getting the indices right is
--   necessary but NOT sufficient — the derivation must also fit in RAM.
--
--   ★ THE COST IS ELABORATED-TERM SIZE, NOT PROOF DIFFICULTY.  Under
--     `--profile=all`, Positivity (231→2224ms), Coverage (139→893ms),
--     Termination (74→510ms) and DeadCode (60→464ms) grow with the term —
--     in a module with NO datatypes, NO pattern matching and NO recursion,
--     where those phases have nothing to check and are pure TRAVERSALS.
--     With meta-instantiation they are ~45% of runtime and respond only to
--     size.  Every rule node stores its implicit types (`⊢app {Γ A B t u}`,
--     `there {Γ A B x}` at EVERY tower level) and `subTy (single u) B` is
--     materialized in full at each application.
--
--   ★ THE FIX: split each branch into TOP-LEVEL LEMMAS whose implicits are
--     `RTm`s and whose bodies sit behind a `Def` — the `⊢strong-base'`
--     pattern in ExamplesOrd, which is exactly why the branches calling it
--     are cheap.  Name intermediate types so the stored payload is a
--     reference, not an expanded `RTy`.  A derived
--     `⊢app' d e refl = ⊢app d e` at `subTy (single u) B ≡ C` makes the cut
--     without touching the TCB.  ⚠ Splitting per MODULE is NOT enough —
--     one branch alone exceeds RAM, so the split must go BELOW branch level.
--
--   ✗ REJECTED (tested, do not retry): replacing the `there`-tower with a
--     computed `lkp : (Γ : Ctx) → Var ⌊ Γ ⌋ → RTy ⌊ Γ ⌋` plus `lkp-sound`.
--     It typechecks and stores ONE variable instead of ~14 types, and it is
--     WORSE — 24.1s / 3.12 GB against the tower's 14.5s / 1.92 GB.  A
--     non-injective DEFINED function in an index position costs more than
--     the tower it removes: comparisons drop to reduction and lose the
--     constructor-guided shortcut.  Variable lookup is not the bottleneck.
--
-- Structure, fully worked out:
--
--   aux : (n₁ n₂ x : Nat) → μ₁ x ≤ n₁ → μ₂ x ≤ n₂ → P x
--       = natrec on n₁, and INSIDE EACH BRANCH a natrec on n₂.
--
--   ★ that nesting IS the lexicographic order: a `rec₁` call decreases
--     n₁ and RESETS n₂ to `μ₂ y`; a `rec₂` call keeps n₁ and decreases
--     n₂.  Both branches of the OUTER recursion need the inner one —
--     at n₁ = 0, `rec₁` is vacuous but `rec₂` still recurses on μ₂.
--
--   the four branches, and how each discharges its obligations:
--     (0,0)  rec₁ : μ₁ y < μ₁ x ≤ 0        → ordtr, then `absurd`
--            rec₂ : μ₂ y < μ₂ x ≤ 0        → ordtr, then `absurd`
--     (0,S)  rec₁ : as above, `absurd`
--            rec₂ : μ₂ y < μ₂ x ≤ suc n₂'  → ordtr + Hom-Nat-ss → IH₂
--     (S,0)  rec₁ : μ₁ y < μ₁ x ≤ suc n₁'  → ordtr + Hom-Nat-ss → IH₁
--            rec₂ : `absurd`
--     (S,S)  rec₁ → IH₁ (bound n₁' , μ₂ y) ; rec₂ → IH₂ (bound n₁ , n₂')
--
--   then  lexrec x = aux (μ₁ x) (μ₂ x) x (le-refl _) (le-refl _).
--
-- ★ EVERY obligation above is a move already MACHINE-CHECKED elsewhere in
--   this POC: `ordtr` composition (⊢monus-le), `Hom-Nat-ss` peeling
--   (⊢strong-step), and `absurd` at a collapsed order (⊢strong-base').
--   Nothing new is required from the kernel — which is the claim under
--   test — but "assembles as expected" is NOT yet verified, and the
--   `ordtr` checkpoint is the standing reminder that mechanical-looking
--   remainders can hide real work.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★ MEANING CHECK.  A raw `RTy` typechecks for ANY well-scoped index
--   assignment, so §1 proves almost nothing on its own.  A `⊢ty`
--   derivation DOES pin the meaning down: `ty-El (⊢app dcP dy)` forces
--   `dcP ∷ Π Nat U`, which only the real `cP` index inhabits, and
--   `ty-Hom ty-Nat da db` forces both endpoints to be at `Nat`.
------------------------------------------------------------------------

Γ₅₀ : Ctx
Γ₅₀ = (((◇ ▹ U) ▹ Π (El (var vz)) U) ▹ Π (El (var (vs vz))) Nat)
        ▹ Π (El (var (vs (vs vz)))) Nat

-- ctx: x=0, μ₂=1, μ₁=2, cP=3   (+y ⇒ +1, +lt ⇒ +2)
⊢REC1T : (Γ₅₀ ▹ El (var (vs (vs (vs vz))))) ⊢ty REC1T
⊢REC1T =
  ty-Π (ty-El (⊢var (there (there (there (there here))))))
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there here)))) (⊢var (here)))) (⊢app (⊢var (there (there (there here)))) (⊢var (there here))))
          (ty-El (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var (there here)))))

-- ctx: rec1=0, x=1, μ₂=2, μ₁=3, cP=4   (+y ⇒ +1, +le ⇒ +2, +lt ⇒ +3)
⊢REC2T : ((Γ₅₀ ▹ El (var (vs (vs (vs vz))))) ▹ REC1T) ⊢ty REC2T
⊢REC2T =
  ty-Π (ty-El (⊢var (there (there (there (there (there here)))))))
    (ty-Π (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there here))))) (⊢var (here))) (⊢app (⊢var (there (there (there (there here))))) (⊢var (there (there here)))))
      (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there here))))) (⊢var (there here)))) (⊢app (⊢var (there (there (there (there here))))) (⊢var (there (there (there here))))))
        (ty-El (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there (there here)))))))

-- ctx: μ₂=0, μ₁=1, cP=2   (+x ⇒ +1, +rec1 ⇒ +2, +rec2 ⇒ +3)
⊢LStepT : Γ₅₀ ⊢ty LStepT
⊢LStepT =
  ty-Π (ty-El (⊢var (there (there (there here))))) (ty-Π ⊢REC1T (ty-Π ⊢REC2T (ty-El (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var (there (there here)))))))

M0lex : RTy (ε ∙ ∙ ∙ ∙ ∙ ∙ ∙)
M0lex = auxBody (var (vs (vs (vs (vs (vs (vs vz)))))))   -- cA
                (var (vs (vs (vs (vs (vs vz))))))   -- cP
                (var (vs (vs (vs (vs vz)))))        -- μ₁
                (var (vs (vs (vs vz))))             -- μ₂
                nzero                               -- b₁ = 0   ← the n₁ = 0 branch
                (var vz)                            -- b₂ = m

-- ★ the motive of the INNER `natrec` in the n₁ = suc branch.  Same shape
--   as `M0lex` but the μ₁ bound is `nsuc n₁'` instead of `nzero`, which is
--   what makes `rec₁` live there and vacuous here.
--   ctx: vz=m, vs=n₂, vs²=IH₁, vs³=n₁', vs⁴=stp, vs⁵=μ₂, vs⁶=μ₁, vs⁷=cP
M1lex : RTy (ε ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙)
M1lex = auxBody (var (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))            -- cA
                (var (vs (vs (vs (vs (vs (vs (vs vz))))))))  -- cP
                (var (vs (vs (vs (vs (vs (vs vz)))))))       -- μ₁
                (var (vs (vs (vs (vs (vs vz))))))            -- μ₂
                (nsuc (var (vs (vs (vs vz)))))               -- b₁ = suc n₁' ← the n₁ = suc branch
                (var vz)                                     -- b₂ = m

------------------------------------------------------------------------
-- ★ 6. MOTIVE WELL-FORMEDNESS — needed by `⊢natrec`, which demands
--   `(Γ ▹ Nat) ⊢ty M`, and doubling as the meaning check §5 never gave
--   these three.
--
-- ⚠ READ THE LIMIT HONESTLY — and this was MEASURED, not reasoned.
--   A `⊢ty` derivation pins cP down, because `ty-El (⊢app dcP dy)`
--   forces `dcP ∷ Π Nat U` and only cP inhabits that.  That is why §5
--   caught the REC2T `cP` bug.  It does NOT pin down μ₁ vs μ₂: both are
--   `Π Nat Nat`, so both readings are well-typed.
--
--   Two experiments, 2026-08-06:
--     * motive buggy, derivation below CORRECT  ⇒ error (exit 42).
--     * motive buggy AND derivation buggy the same way ⇒ GREEN (exit 0).
--
--   So `⊢lexAuxMot` is a CROSS-CHECK between two hand-written artifacts,
--   not a meaning check.  It catches DISAGREEMENT, not MISCONCEPTION:
--   make the same misreading twice and it passes.  ★ THE GENERAL LESSON,
--   which applies to any Spec/Implementation split here: redundancy buys
--   nothing unless the two artifacts are written from DIFFERENT
--   information.  The branch derivations qualify — they are written from
--   the ALGORITHM, not transcribed from the motive — which is exactly
--   why `⊢lexSZ` caught the measure bug (its `⊢le-refl` at `μ₂ y` could
--   not match an expected `μ₁ y`) and this file could not.
--
--   The check that WOULD be independent is a negative tripwire: assert
--   that the μ₁/μ₂-swapped motive FAILS to typecheck.  Not written —
--   each branch costs minutes — but it is the only mechanical check that
--   can see a type-preserving confusion.  Cf. check-formers.sh.
--
-- ⚠ NOTE THE TRAP that made it easy: in `lexAuxMot` the μ₁ bound sits
--   ONE BINDER SHALLOWER than the μ₂ bound, so BOTH are `vs⁵` in their
--   own frames.  The correct index is the same numeral twice.
------------------------------------------------------------------------

-- ctx: vz=n₁', vs=stp, vs²=μ₂, vs³=μ₁, vs⁴=cP
⊢lexAuxMot : (Γ₅ ▹ Nat) ⊢ty lexAuxMot
⊢lexAuxMot =
  ty-Π ty-Nat (ty-Π (ty-El (⊢var (there (there (there (there (there (there here))))))))
    (ty-Π (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var here)) (⊢var (there (there here))))
       (ty-Π (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var (there here))) (⊢var (there (there here))))
          (ty-El (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there here))))))))

-- ctx: vz=m, vs=n₂, vs²=stp, vs³=μ₂, vs⁴=μ₁, vs⁵=cP
⊢M0lex : ((Γ₅ ▹ Nat) ▹ Nat) ⊢ty M0lex
⊢M0lex =
  ty-Π (ty-El (⊢var (there (there (there (there (there (there here))))))))
    (ty-Π (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var here)) ⊢nzero)
       (ty-Π (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there here)))))) (⊢var (there here))) (⊢var (there (there here))))
          (ty-El (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there here)))))))

-- ctx: vz=m, vs=n₂, vs²=IH₁, vs³=n₁', vs⁴=stp, vs⁵=μ₂, vs⁶=μ₁, vs⁷=cP
⊢M1lex : ((((Γ₅ ▹ Nat) ▹ lexAuxMot) ▹ Nat) ▹ Nat) ⊢ty M1lex
⊢M1lex =
  ty-Π (ty-El (⊢var (there (there (there (there (there (there (there (there here))))))))))
    (ty-Π (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var here)) (⊢nsuc (⊢var (there (there (there (there here)))))))
       (ty-Π (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there here))) (⊢var (there (there here))))
          (ty-El (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there (there here)))))))
