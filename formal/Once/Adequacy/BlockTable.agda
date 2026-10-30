-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.BlockTable   (plan 0.129 B5)
--
-- A COMPILER-OWNED SIGOP'S SYMBOL IS IN THE FILE'S BLOCK TABLE. Two halves,
-- both arch-free:
--
--   * `image-owned`: every `instr-sigop si` of the program image satisfies
--     `Named (program-blocks p)` — the IR fact `program-owned` carried through
--     the emitter's walk (`ImageInstrs`);
--   * `table-has`: a block of `program-blocks p` keeps its symbol through
--     `dedup-blocks` (a later duplicate is dropped only for an earlier one with
--     the same symbol), whatever the arch's symbol and payload.
--
-- Each arch's `block-env` lookup then finds a payload (`block-env-hit`, beside
-- its `block-env`), which is the lookup half of `arith-sigop-contract`.
------------------------------------------------------------------------

module Once.Adequacy.BlockTable where

open import Data.Bool using (true; false)
import Data.Bool.ListAction as BLA
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (map⁺)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _==_; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; sym)
open import Relation.Nullary using (yes; no)

open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Compile using (program-blocks; rewrite-program; image-of; entry-owner; dedup-go; dedup-blocks)
open import Once.Denotation.Program using (IRProgram)
open import Once.CCC.Codegen.CallOK using (InstrOK)
import Once.CCC.Codegen.ImageInstrs as II
open import Once.Adequacy.RewriteOwned using (Named; program-owned)

------------------------------------------------------------------------
-- The image's SigOps name blocks.
------------------------------------------------------------------------

image-owned : ∀ (p : IRProgram) → All (InstrOK (λ _ _ _ → ⊤) (Named (program-blocks p))) (image-of p)
image-owned p =
  II.image-ok (λ _ _ _ _ → ⊤) tt (Named (program-blocks p)) entry-owner (rewrite-program p)
    (proj₁ (program-owned p)) (proj₂ (program-owned p))

------------------------------------------------------------------------
-- `dedup-blocks` keeps every symbol.
------------------------------------------------------------------------

private
  any-sound : ∀ (seen : List String) (s : String) → BLA.any (λ x → x == s) seen ≡ true → Any (λ x → x ≡ s) seen
  any-sound (x ∷ seen) s e with x ≟ s
  ... | yes x≡s = here x≡s
  ... | no  _   = there (any-sound seen s e)

  -- a symbol of the input is already seen, or survives
  dedup-key : ∀ (seen : List String) (xs : List (String × ArithBlock)) (s : String)
            → Any (λ x → proj₁ x ≡ s) xs → Any (λ x → x ≡ s) seen ⊎ Any (λ x → proj₁ x ≡ s) (dedup-go seen xs)
  dedup-key seen ((s′ , b) ∷ xs) s a with BLA.any (λ x → x == s′) seen in eq
  dedup-key seen ((s′ , b) ∷ xs) s (here s′≡s) | true  = inj₁ (subst (λ t → Any (λ x → x ≡ t) seen) s′≡s (any-sound seen s′ eq))
  dedup-key seen ((s′ , b) ∷ xs) s (there a)   | true  = dedup-key seen xs s a
  dedup-key seen ((s′ , b) ∷ xs) s (here s′≡s) | false = inj₂ (here s′≡s)
  dedup-key seen ((s′ , b) ∷ xs) s (there a)   | false with dedup-key (s′ ∷ seen) xs s a
  ... | inj₁ (here s′≡s) = inj₂ (here s′≡s)
  ... | inj₁ (there m)   = inj₁ m
  ... | inj₂ m           = inj₂ (there m)

dedup-keeps : ∀ (xs : List (String × ArithBlock)) (s : String)
            → Any (λ x → proj₁ x ≡ s) xs → Any (λ x → proj₁ x ≡ s) (dedup-blocks xs)
dedup-keeps xs s a with dedup-key [] xs s a
... | inj₁ ()
... | inj₂ m = m

-- A block of the program is in the file's table under its symbol, at any arch.
table-has : ∀ {P : Set} (symb : ArithBlock → String) (pay : ArithBlock → P) (bs : List ArithBlock) {b : ArithBlock}
          → b ∈ bs
          → Any (λ x → proj₁ x ≡ symb b) (map (λ sb → proj₁ sb , pay (proj₂ sb)) (dedup-blocks (map (λ b′ → symb b′ , b′) bs)))
table-has symb pay bs {b} m =
  map⁺ (dedup-keeps _ (symb b) (map⁺ (Any.map (λ e → cong symb (sym e)) m)))
