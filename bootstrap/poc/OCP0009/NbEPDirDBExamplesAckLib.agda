------------------------------------------------------------------------
-- OCP-0009 — ★★★ ACKERMANN THROUGH `⊢lexrec`.  (#9)
--
--     ack (0      , n)      = n + 1
--     ack (suc m' , 0)      = ack (m' , 1)              -- μ₁ DOWN  → rec₁
--     ack (suc m' , suc n') = ack (m' , ack (suc m' , n'))
--                                       ↑ μ₁ HELD, μ₂ DOWN → rec₂
--                             ↑ μ₁ DOWN → rec₁
--
-- ★ THE USE SITE THAT EXERCISES BOTH RECURSORS.  `NbEPDirDBExamplesLexPair` uses
--   `rec₂` alone; this one uses `rec₁` twice and `rec₂` once, and the
--   outer call CONSUMES the inner call's result, so the recursion is
--   genuinely nested and not merely two-armed.
--
-- ⛔⛔ AND ACKERMANN DOES **NOT** NEED `⊢lexrec`.  Do not cite this file as
--   the justification for the WF axis — `NbEPDirDBExamplesAckKernel` defines the same
--   function over the same kernel by NESTED `natrec` with a higher-order
--   motive (the outer recursion returns `Nat → Nat`), in 26 lines and
--   0.61 s, with no measure, no `Hom Nat` order and no combinator at all.
--   Ackermann happens to be structurally recursive at HIGHER TYPE.
--   `NbEPDirDBExamplesAckKernel`'s own header says this and warns against exactly the
--   claim; the functions that genuinely need lexicographic descent are
--   the ones it names — div, gcd, quicksort on a pair measure.
--
--   What this file IS: the first use site to exercise rec₁, rec₂ and a
--   nested call together, and the one that found the `Def` cliff below.
--   ⚠ It is ~18× slower than `NbEPDirDBExamplesAckKernel` at the same function; that gap
--   is the price of going through a general recursor, and it is worth
--   knowing before quoting this module as evidence of anything.
--
-- ⚠ THIS IS ALSO THE SPEC-ERROR TEST.  `⊢gcd-descend` once certified a
--   recursion that was not gcd; a lexicographic recursor that typechecks
--   while recursing at the wrong argument would show here and nowhere
--   else.  The three descents below pin the three recursive calls.
--
-- ★ BOTH BOUNDS ARE ABSTRACTED (D8, twice).  `natrec` needs a ℕ, so the
--   case split lands on the MEASURES: outer on `fst x`, inner on `snd x`.
--   Each split's motive must abstract the bound it moves —
--     `M₁` abstracts rec₁'s bound AND rec₂'s μ₁-bound to the outer var;
--     `M₂` abstracts rec₂'s μ₂-bound to the inner var.
--   `aIHTat`/`rec2Tat` are what can say that; nothing in the
--   codes-and-functions interface could.
--
-- ctx after the two splits and the two ⊢lams (C5, five slots):
--     vz = rec₂, vs = rec₁, vs² = M₁, vs³ = m', vs⁴ = x
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesAckLib where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U; Σ'
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Π; renTy; renTm; subTy; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢⌜Nat⌝; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Σ
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; El-⌜Nat⌝; Hom-Nat-ss
        ; ξ-nsuc; ξ-Homˡ; βfst; βsnd )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat )
-- ★ ONE import: the façade re-exports the type layer.
open import poc.OCP0009.NbEPDirDBLibLexrec using ( rec2Tat; lStepT; module LxΠ )
open import poc.OCP0009.NbEPDirDBLibPair
  using ( PairT; ⊢PairT; msr₁; msr₂; ⊢msr₁; ⊢msr₂
        ; elNat; asP; asN; dropˡ; dropʳ; holdˡ )
open import poc.OCP0009.NbEPDirDBLibPairLex using ( ⊢rec1Tat; ⊢rec2Tat )

-- ★ `asN`, `dropˡ`, `dropʳ` and `holdˡ` now come from
--   `NbEPDirDBLibPair` (D10) — this file used to define all four.

------------------------------------------------------------------------
-- THE OUTER MOTIVE — the split on `fst x`.  It abstracts BOTH of rec₁'s
-- bound and rec₂'s μ₁-bound to the natrec variable; rec₂'s μ₂-bound stays
-- concrete (`snd x`), because the outer split does not move it.
------------------------------------------------------------------------

M₁ : RTy (ε ∙ ∙)
M₁ =
  Π (aIHTat PairT ⌜Nat⌝ msr₁ (var vz))
    (Π (rec2Tat PairT ⌜Nat⌝ msr₁ msr₂ (var (vs vz)) (snd (var (vs (vs vz)))))
       (El ⌜Nat⌝))

⊢M₁ : ((◇ ▹ PairT) ▹ Nat) ⊢ty M₁
⊢M₁ =
  ty-Π (⊢rec1Tat (⊢var here))
    (ty-Π (⊢rec2Tat (⊢var (there here)) (⊢snd (⊢var (there (there here)))))
          (ty-El ⊢⌜Nat⌝))

-- fst x = 0 : `ack (0 , n) = n + 1`.  Both recursors discarded.
fZ₁ : RTm (ε ∙)
fZ₁ = lam (lam (nsuc (snd (var (vs (vs vz))))))

⊢fZ₁ : (◇ ▹ PairT) ⊢ fZ₁ ∷ subTy (single nzero) M₁
⊢fZ₁ =
  ⊢lam (⊢rec1Tat ⊢nzero)
    (⊢lam (⊢rec2Tat ⊢nzero (⊢snd (⊢var (there here))))
          (asP (⊢nsuc (⊢snd (⊢var (there (there here)))))))

------------------------------------------------------------------------
-- THE INNER MOTIVE — the split on `snd x`, inside the outer successor
-- branch.  ⚠ It lives five slots deep: rec₁ and rec₂ are already bound as
-- context VARIABLES, so the motive names only rec₂'s μ₂-bound.
------------------------------------------------------------------------

M₂ : RTy (ε ∙ ∙ ∙ ∙ ∙ ∙)
M₂ =
  Π (rec2Tat PairT ⌜Nat⌝ msr₁ msr₂
             (nsuc (var (vs (vs (vs (vs vz)))))) (var vz))
    (El ⌜Nat⌝)

-- C5 — the context the inner recursor lives in
C5 : Ctx
C5 =
  ((((◇ ▹ PairT) ▹ Nat) ▹ M₁)
     ▹ aIHTat PairT ⌜Nat⌝ msr₁ (nsuc (var (vs vz))))
     ▹ rec2Tat PairT ⌜Nat⌝ msr₁ msr₂
               (nsuc (var (vs (vs vz)))) (snd (var (vs (vs (vs vz)))))

⊢M₂ : (C5 ▹ Nat) ⊢ty M₂
⊢M₂ =
  ty-Π (⊢rec2Tat (⊢nsuc (⊢var (there (there (there (there here)))))) (⊢var here))
       (ty-El ⊢⌜Nat⌝)

-- snd x = 0 : `ack (suc m' , 0) = ack (m' , 1)` — rec₁, μ₁ strictly down.
fZ₂ : RTm (ε ∙ ∙ ∙ ∙ ∙)
fZ₂ =
  lam (app (app (var (vs (vs vz)))
                (pair (var (vs (vs (vs (vs vz))))) (nsuc nzero)))
           (reflTm (var (vs (vs (vs (vs vz)))))))

⊢fZ₂ : C5 ⊢ fZ₂ ∷ subTy (single nzero) M₂
⊢fZ₂ =
  ⊢lam (⊢rec2Tat (⊢nsuc (⊢var (there (there (there here))))) ⊢nzero)
    (⊢app (⊢app (⊢var (there (there here)))
                (⊢pair ty-Nat dm' (⊢nsuc ⊢nzero)))
          (dropˡ (var (vs (vs (vs (vs vz))))) (nsuc nzero) dm'))
  where
    dm' = ⊢var (there (there (there (there here))))

-- snd x = suc n' : `ack (suc m' , suc n') = ack (m' , ack (suc m' , n'))`.
-- ★ THE NESTED CALL.  The inner one goes through rec₂ (μ₁ held, μ₂ down);
--   its RESULT is the second component of the pair the outer one — rec₁,
--   μ₁ strictly down — recurses at.
-- ⚠⚠ THE INNER CALL IS HOISTED, and that is not cosmetic.  Written inline
--   inside `⊢fS₂` this module costs 192.5 s / 4.41 GB; behind a top-level
--   `Def` with an explicit type it costs 10.1 s / 0.84 GB.  19× time,
--   5.3× memory, both measured cold on an IDLE box.  The traversal phases
--   walk a NAME instead of the spine — the `⊢strong-base'` pattern, and
--   the one lever `agda-cost-is-elaborated-term-size` says works.
--   ⚠ 4.41 GB against the 5.5 GB cap is a 20% margin: the inline form
--   OOMs as soon as anything else is running.  That is how this was
--   found, and it is why the hoist is a robustness fix and not merely a
--   speed-up.
C8 : Ctx
C8 =
  ((C5 ▹ Nat) ▹ M₂)
    ▹ rec2Tat PairT ⌜Nat⌝ msr₁ msr₂
              (nsuc (var (vs (vs (vs (vs (vs vz))))))) (nsuc (var (vs vz)))

innerTm : RTm ⌊ C8 ⌋
innerTm =
  app (app (app (var vz)
                (pair (nsuc (var (vs (vs (vs (vs (vs (vs vz))))))))
                      (var (vs (vs vz)))))
           (reflTm (nsuc (var (vs (vs (vs (vs (vs (vs vz))))))))))
      (reflTm (var (vs (vs vz))))

-- `ack (suc m' , n')` — μ₁ HELD (reflexivity after βfst), μ₂ DOWN.
⊢innerCall : C8 ⊢ innerTm ∷ El ⌜Nat⌝
⊢innerCall =
  ⊢app (⊢app (⊢app (⊢var here) (⊢pair ty-Nat (⊢nsuc dm') dn'))
             (holdˡ (nsuc (var (vs (vs (vs (vs (vs (vs vz))))))))
                    (var (vs (vs vz))) (⊢nsuc dm')))
       (dropʳ (nsuc (var (vs (vs (vs (vs (vs (vs vz))))))))
              (var (vs (vs vz))) dn')
  where
    dm' = ⊢var (there (there (there (there (there (there here))))))
    dn' = ⊢var (there (there here))

fS₂ : RTm (ε ∙ ∙ ∙ ∙ ∙ ∙ ∙)
fS₂ =
  lam (app (app (var (vs (vs (vs (vs vz)))))
                (pair (var (vs (vs (vs (vs (vs (vs vz))))))) innerTm))
           (reflTm (var (vs (vs (vs (vs (vs (vs vz)))))))))

⊢fS₂ : ((C5 ▹ Nat) ▹ M₂) ⊢ fS₂ ∷ subTy nrs M₂
⊢fS₂ =
  ⊢lam (⊢rec2Tat (⊢nsuc dm'₇) (⊢nsuc dn'₇))
    (⊢app (⊢app drec₁ (⊢pair ty-Nat dm' (asN ⊢innerCall)))
          (dropˡ (var (vs (vs (vs (vs (vs (vs vz))))))) innerTm dm'))
  where
    -- ⚠ the ⊢lam's DOMAIN is one slot shallower than its BODY, and the
    --   two need different lookups.  Seven slots: vz = M₂, vs = n',
    --   vs² = rec₂, vs³ = rec₁, vs⁴ = M₁, vs⁵ = m', vs⁶ = x
    dm'₇   = ⊢var (there (there (there (there (there here)))))
    dn'₇   = ⊢var (there here)
    -- eight slots (inside the ⊢lam): vz = rec₂', vs = M₂, vs² = n',
    --   vs³ = rec₂, vs⁴ = rec₁, vs⁵ = M₁, vs⁶ = m', vs⁷ = x
    dm'    = ⊢var (there (there (there (there (there (there here))))))
    drec₁  = ⊢var (there (there (there (there here))))

------------------------------------------------------------------------
-- the outer successor branch: bind rec₁ and rec₂, then split on `snd x`
-- and hand the result the rec₂ that is now in scope.
------------------------------------------------------------------------

fS₁ : RTm (ε ∙ ∙ ∙)
fS₁ =
  lam (lam (app (natrec fZ₂ fS₂ (snd (var (vs (vs (vs (vs vz)))))))
                (var vz)))

⊢fS₁ : (((◇ ▹ PairT) ▹ Nat) ▹ M₁) ⊢ fS₁ ∷ subTy nrs M₁
⊢fS₁ =
  ⊢lam (⊢rec1Tat (⊢nsuc (⊢var (there here))))
    (⊢lam (⊢rec2Tat (⊢nsuc (⊢var (there (there here))))
                    (⊢snd (⊢var (there (there (there here))))))
      (⊢app (⊢natrec ⊢M₂ ⊢fZ₂ ⊢fS₂
                     (⊢snd (⊢var (there (there (there (there here)))))))
            (⊢var here)))

------------------------------------------------------------------------
-- THE STEP, and the use site.
------------------------------------------------------------------------

ackStp : RTm ε
ackStp = lam (natrec fZ₁ fS₁ msr₁)

⊢ackStp : ◇ ⊢ ackStp ∷ lStepT PairT ⌜Nat⌝ msr₁ msr₂
⊢ackStp = ⊢lam ⊢PairT (⊢natrec ⊢M₁ ⊢fZ₁ ⊢fS₁ ⊢msr₁)

open LxΠ ◇ PairT ⌜Nat⌝ msr₁ msr₂ ackStp ⊢PairT ⊢⌜Nat⌝ ⊢msr₁ ⊢msr₂ ⊢ackStp
  using ( lexrecTm; ⊢lexrecΠ; ⊢lexrecPt )

ackTm : RTm ε
ackTm = lexrecTm

-- ★★★ A CLOSED, WELL-TYPED ACKERMANN — total by construction, with no
--     `TERMINATING`, no fuel, no `Acc`, and nothing added to the kernel.
⊢ack : ◇ ⊢ ackTm ∷ Π PairT (El ⌜Nat⌝)
⊢ack = ⊢lexrecΠ

⊢ack-at : ◇ ⊢ app ackTm (pair (nsuc nzero) (nsuc nzero))
          ∷ subTy (single (pair (nsuc nzero) (nsuc nzero))) (El ⌜Nat⌝)
⊢ack-at = ⊢lexrecPt (⊢pair ty-Nat (⊢nsuc ⊢nzero) (⊢nsuc ⊢nzero))
