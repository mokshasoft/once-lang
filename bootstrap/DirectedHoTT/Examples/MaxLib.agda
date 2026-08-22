------------------------------------------------------------------------
-- DirectedHoTT · EXAMPLES — `Lib/Max`'s LAST THREE BRANCHES, EXERCISED.
--
-- ⚠⚠ WHY THIS FILE EXISTS.  An audit on 2026-08-22 found `⊢MaxT`,
--   `MaxCode-conv` and `MaxCode-convU` with no client — internally OR
--   externally.  Standing rule: every library branch is exercised by an
--   Example, because derived-and-green is not evidence of anything
--   (`lexrec` was derived, green, `--safe`, and uncallable).
--
-- ★ AND WHY THEY WERE ORPHANED, which is the interesting part.  They are
--   the maximality analogues of `QCode-conv`/`QCode-convU`/`⊢QCode`, and
--   divisibility genuinely needed those when it had a BESPOKE `IndStep`.
--   Maximality never did: `Plumb` derives `PC-conv`/`PC-convU` once,
--   generically, from the `PC-redV`/`PC-redU` fields of `Motive`.  So the
--   abstraction did not merely save maximality from writing an assembly —
--   it removed the need for three library lemmas written in anticipation
--   of one.
--
--   ⇒ They are kept rather than deleted because the CALL was
--     "client, not deletion", and because `Comparison/GcdIndStepConcrete`
--     shows why: hand-rolled-versus-generic is a measurement someone will
--     want, and a hand-rolled maximality would need exactly these.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.MaxLib where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; RTm; El; Nat; nzero; nsuc )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; ⌊_⌋; _⊢_∷_; _⊢ty_; _≅ᵀ_; _⟶*_; done; step
        ; ⊢nzero; ⊢nsuc; natrec-zero )
open import DirectedHoTT.Lib.Max
  using ( MaxT; ⊢MaxT; MaxCode; MaxCode-conv; MaxCode-convU )
open import DirectedHoTT.Lib.Nat using ( plusTm )

------------------------------------------------------------------------
-- 1 · `⊢MaxT` — the DECODED predicate is a well-formed type.
--     ⚠ `⊢MaxCode` (the CODE's typing) is exercised through `maxMotive`;
--       this is its `El`-side twin, which nothing else reaches.
------------------------------------------------------------------------

⊢MaxT-at : ◇ ⊢ty MaxT (nsuc nzero) (nsuc (nsuc nzero)) (nsuc nzero)
⊢MaxT-at = ⊢MaxT (⊢nsuc ⊢nzero) (⊢nsuc (⊢nsuc ⊢nzero)) (⊢nsuc ⊢nzero)

------------------------------------------------------------------------
-- 2 · `MaxCode-conv` — the RESULT slot converts under reduction.
--     `plusTm 0 1 ⟶* 1`, so maximality at the computed witness and at the
--     numeral are the same type.
------------------------------------------------------------------------

plus01 : plusTm {ε} nzero (nsuc nzero) ⟶* nsuc nzero
plus01 = step (natrec-zero _ _) done

conv-result : El (MaxCode (nsuc nzero) (nsuc nzero) (plusTm nzero (nsuc nzero)))
            ≅ᵀ El (MaxCode (nsuc nzero) (nsuc nzero) (nsuc nzero))
conv-result = MaxCode-conv (nsuc nzero) (nsuc nzero) plus01

------------------------------------------------------------------------
-- 3 · `MaxCode-convU` — BOTH argument slots convert, independently.
------------------------------------------------------------------------

conv-args : El (MaxCode (plusTm nzero (nsuc nzero))
                        (plusTm nzero (nsuc nzero)) (nsuc nzero))
          ≅ᵀ El (MaxCode (nsuc nzero) (nsuc nzero) (nsuc nzero))
conv-args = MaxCode-convU (nsuc nzero) plus01 plus01
