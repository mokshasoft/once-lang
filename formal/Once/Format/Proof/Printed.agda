-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Printed — the comment words of a printed module, in
-- the printer's order (plan 0.124 step 4.5).
--
-- Declaration by declaration: the notes that stand before it (the top notes
-- of its anchors, its first anchor's inner notes joined to them), then each
-- anchor's inner and end-of-line notes (`pdecls-DocC`); after the last, the
-- notes left at the end.
------------------------------------------------------------------------

module Once.Format.Proof.Printed where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Once.Spec.Surface.Syntax using (Decl; Module; mkModule)
open import Once.Format.Doc using (empty; blank; _<>_)
open import Once.Format.Print using (Note; note-comment; note-blank; Trivia; hoist; topList; runs; topDoc; hasComment;
  blankIf; blankLast; lead; ending; gap; gapEnd; together; pdecl; pdecls; pmodule)
open import Once.Format.Proof.Words using (DocC; Mn; commentRun-DW; cm-++; ifcase)
open import Once.Format.Proof.Counts using (Ind; ind-pdecl; AnchC)

-- | A note's words.
MNote : Note → List (List Char)
MNote (note-comment c) = Mn c
MNote note-blank       = []

MNotes : List Note → List (List Char)
MNotes = concatMap MNote

private
  runs-DocC : ∀ ns acc sd → DocC (runs ns acc sd) ≡ concatMap Mn acc ++ MNotes ns
  runs-DocC []                    []          _     = refl
  runs-DocC []                    acc@(_ ∷ _) _     = trans (commentRun-DW acc) (sym (++-identityʳ _))
  runs-DocC (note-blank ∷ ns)     acc         _     = runs-DocC ns acc true
  runs-DocC (note-comment c ∷ ns) []          _     =
    trans (runs-DocC ns (c ∷ []) false) (cong (_++ MNotes ns) (++-identityʳ (Mn c)))
  runs-DocC (note-comment c ∷ ns) acc@(_ ∷ _) false =
    trans (runs-DocC ns (acc ++ c ∷ []) false)
      (trans (cong (_++ MNotes ns) (trans (cm-++ Mn acc (c ∷ [])) (cong (concatMap Mn acc ++_) (++-identityʳ (Mn c)))))
        (++-assoc (concatMap Mn acc) (Mn c) (MNotes ns)))
  runs-DocC (note-comment c ∷ ns) acc@(_ ∷ _) true  =
    cong₂ _++_ (commentRun-DW acc) (trans (runs-DocC ns (c ∷ []) false) (cong (_++ MNotes ns) (++-identityʳ (Mn c))))

  topDoc-DocC : ∀ ns → DocC (topDoc ns) ≡ MNotes ns
  topDoc-DocC ns = runs-DocC ns [] false

  -- notes without a comment have no words
  none-words : ∀ ns → hasComment ns ≡ false → MNotes ns ≡ []
  none-words []                _  = refl
  none-words (note-blank ∷ ns) e  = none-words ns e
  none-words (note-comment _ ∷ _) ()

  lead-DocC : ∀ prev ns → DocC (lead prev ns) ≡ MNotes ns
  lead-DocC nothing ns =
    ifcase {P = λ z → DocC z ≡ MNotes ns} (hasComment ns)
      (λ _ → trans (cong (DocC (topDoc ns) ++_) (blankIf-DocC (blankLast ns))) (trans (++-identityʳ _) (topDoc-DocC ns)))
      (λ e → sym (none-words ns e))
    where
      blankIf-DocC : ∀ b → DocC (blankIf b) ≡ []
      blankIf-DocC true  = refl
      blankIf-DocC false = refl
  lead-DocC (just _) ns = topDoc-DocC ns

  gapEnd-DocC : ∀ prev → DocC (gapEnd prev) ≡ []
  gapEnd-DocC nothing  = refl
  gapEnd-DocC (just _) = refl

  ending-DocC : ∀ prev ns → DocC (ending prev ns) ≡ MNotes ns
  ending-DocC prev ns =
    ifcase {P = λ z → DocC z ≡ MNotes ns} (hasComment ns)
      (λ _ → trans (cong (_++ DocC (topDoc ns)) (gapEnd-DocC prev)) (topDoc-DocC ns))
      (λ e → sym (none-words ns e))

  gap-DocC : ∀ prev d → DocC (gap prev d) ≡ []
  gap-DocC nothing  d = refl
  gap-DocC (just p) d = ifcase {P = λ z → DocC z ≡ []} (together p d) (λ _ → refl) (λ _ → refl)

-- | The words of the declarations from anchor `k` on, in the printer's order.
DC : List Decl → Trivia → ℕ → List (List Char)
DC []       tv k = MNotes (topList k (suc k) (hoist k tv))
DC (d ∷ ds) tv k = MNotes (topList k (k + Ind.c (ind-pdecl d)) (hoist k tv))
                   ++ AnchC (hoist k tv) k (Ind.c (ind-pdecl d)) ++ DC ds (hoist k tv) (k + Ind.c (ind-pdecl d))

-- | A printed module's comment words: the printer's order.
pdecls-DocC : ∀ prev ds tv k → DocC (proj₁ (pdecls prev ds tv k)) ≡ DC ds tv k
pdecls-DocC prev []       tv k = ending-DocC prev (topList k (suc k) (hoist k tv))
pdecls-DocC prev (d ∷ ds) tv k =
  trans (cong (_++ (DocC (lead prev ns) ++ (DocC dd ++ DocC r))) (gap-DocC prev d))
    (cong₂ _++_
      (trans (lead-DocC prev ns) (cong (λ j → MNotes (topList k j tv′)) (Ind.cnt I tv′ k)))
      (cong₂ _++_ (Ind.cms I tv′ k)
        (trans (pdecls-DocC (just d) ds tv′ (proj₂ (pdecl d tv′ k))) (cong (DC ds tv′) (Ind.cnt I tv′ k)))))
  where
    tv′ = hoist k tv
    I = ind-pdecl d
    ns = topList k (proj₂ (pdecl d tv′ k)) tv′
    dd = proj₁ (pdecl d tv′ k)
    r = proj₁ (pdecls (just d) ds tv′ (proj₂ (pdecl d tv′ k)))

pmodule-DocC : ∀ ds tv → DocC (proj₁ (pmodule (mkModule ds) tv 0)) ≡ DC ds tv 0
pmodule-DocC ds tv = pdecls-DocC nothing ds tv 0
