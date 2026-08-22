------------------------------------------------------------------------
-- BRANCH (S,S), rec₂ — THE INNER DESCENT.
--
-- Calls the INNER IH (`M1lex` variable, vs⁶) with n₁ HELD FIXED:
--   μ₁ y ≤ suc n₁'  by plain `⊢ordtr` — the n₁ bound is merely CARRIED;
--   μ₂ y ≤ m        by `⊢strong-step` — n₂ STRICTLY DOWN.
--
-- ★ Together with rec₁ this is the lexicographic order in full: either
--   n₁ drops and n₂ is free, or n₁ is held and n₂ drops.  No coproduct,
--   no equality on ℕ, no new kernel former.
--
-- ⚠⚠ THIS MODULE NEEDS THE COMPACTING COLLECTOR.  Check it with
--
--       ./check.sh poc/OCP0009/NbEPDirDBExamplesLexSS2.agda +RTS -c -RTS
--
--   Under the default (copying) GC it is OOM-KILLED at the 5.5 GB cap
--   after ~198s; with `-c` it passes in 196s / 4.81 GB.  Copying GC needs
--   roughly 2× the live set as headroom, and here the live set is simply
--   too big for that — this is the single most expensive definition in
--   the POC.  It is NOT slower for the time budget either: the -c run
--   costs about what the failed run did, it just fits.
--
--   If it ever stops fitting even with -c, the next lever is splitting
--   the ⊢ordtr and ⊢strong-step arguments below into their own Def-backed
--   modules, exactly as the branch itself was split.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexSS2 where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; Unit
        ; RTm; var; unit; nzero; nsuc; natrec; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢ordtr
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import DirectedHoTT.Lib.Strong using ( ⊢le-refl; reflTm )
open import DirectedHoTT.Lib.Ord
  using ( ⊢strong-base'; ⊢strong-step )
open import DirectedHoTT.Negative.Lex using ( REC2T )
open import DirectedHoTT.Negative.LexSSData
  using ( ΓSS; lexSSrec2; REC2TSS )

⊢lexSSrec2 : ΓSS ⊢ lexSSrec2 ∷ REC2TSS
⊢lexSSrec2 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var here)) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there (there (there (there here))))))) (⊢app (⊢app (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var (there (there here)))) (⊢ordtr (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (there (there here))))))))))))) (⊢var (there (there (there (there (there here))))))) (⊢nsuc (⊢var (there (there (there (there (there (there (there (there (there (there here)))))))))))) (⊢var (there here)) (⊢var (there (there (there (there here))))))) (⊢strong-step (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there (there here)))))))))))) (⊢var (there (there (there (there (there here))))))) (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var here) (⊢var (there (there (there here))))))))
