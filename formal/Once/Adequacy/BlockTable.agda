-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.BlockTable   (plan 0.129 B5)
--
-- A COMPILER-OWNED SIGOP'S SYMBOL IS IN THE FILE'S BLOCK TABLE. Arch-free:
--
--   * every `instr-sigop si` of the image names a block of its list (`SigNamed`;
--     the linear core's image: `LinCore.ImageOwned`; master's image, with its
--     `image-owned`, went with master's lowering, plan 0.146 D462);
--   * `table-has`: a block of the list keeps its symbol through
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
open import Once.Compile using (dedup-go; dedup-blocks)
open import Once.Adequacy.RewriteOwned using (Named; BlockOf)
open import Once.Arith.SigOp.DigestInjective using (block-symbol-injective)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Arith.Machine.IR using (mk-block)
open Once.Arith.Machine.IR.ArithBlock using (block-body)
open import Once.Compile using (block-symbol)
open import Once.SigOp.Info using (SigOpInfo; Internal; module SigOpInfo)
open SigOpInfo using (name; sem)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Spec.Name using (bare)
open import Data.Product using (Σ)
open import Data.List.Relation.Unary.Any.Properties using (map⁻)
open import Relation.Binary.PropositionalEquality using (refl; trans)

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

------------------------------------------------------------------------
-- plan 0.123 α′ (f1): …and every entry of the table is a block of the
-- program, under its own symbol — `dedup-blocks` only drops.
------------------------------------------------------------------------

private
  dedup-sub : ∀ {Q : String × ArithBlock → Set} (seen : List String) (xs : List (String × ArithBlock))
            → Any Q (dedup-go seen xs) → Any Q xs
  dedup-sub seen []             ()
  dedup-sub seen ((s′ , b) ∷ xs) a with BLA.any (λ x → x == s′) seen
  ... | true  = there (dedup-sub seen xs a)
  ... | false with a
  ...   | here q  = here q
  ...   | there m = there (dedup-sub (s′ ∷ seen) xs m)

table-sound : ∀ {P : Set} (symb : ArithBlock → String) (pay : ArithBlock → P) (bs : List ArithBlock)
                {Q : String → P → Set}
            → Any (λ x → Q (proj₁ x) (proj₂ x)) (map (λ sb → proj₁ sb , pay (proj₂ sb)) (dedup-blocks (map (λ b′ → symb b′ , b′) bs)))
            → Σ ArithBlock (λ b → b ∈ bs × Q (symb b) (pay b))
table-sound {P} symb pay bs {Q} a = from bs (dedup-sub [] (map (λ b′ → symb b′ , b′) bs) (map⁻ a))
  where
    R : String × ArithBlock → Set
    R sb = Q (proj₁ sb) (pay (proj₂ sb))
    from : ∀ (cs : List ArithBlock) → Any R (map (λ b′ → symb b′ , b′) cs) → Σ ArithBlock (λ b → b ∈ cs × Q (symb b) (pay b))
    from (c ∷ cs) (here q)  = c , here refl , q
    from (c ∷ cs) (there m) = let (b , i , q) = from cs m in b , there i , q

-- THE BLOCK A SYMBOL NAMES. A compiler-owned SigOp names a block of the
-- program whose body is its contract (`Named`); the table entry found under
-- its symbol is some block with that symbol; one symbol is one block
-- (`block-symbol-injective`, D395) — so the payload found is the payload of
-- the SigOp's own block.
which-block : ∀ {P : Set} (pay : ArithBlock → P) (bs : List ArithBlock) {X Y} (si : SigOpInfo X Y) {pl : P}
            → Σ ArithBlock (λ b₀ → b₀ ∈ bs × name si ≡ bare (block-name (block-body b₀)) × BlockOf si b₀)
            → Any (λ x → proj₁ x ≡ once-symbol-path (name si) × proj₂ x ≡ pl)
                  (map (λ sb → proj₁ sb , pay (proj₂ sb)) (dedup-blocks (map (λ b′ → block-symbol b′ , b′) bs)))
            → Σ ArithBlock (λ b → b ∈ bs × BlockOf si b × pl ≡ pay b)
which-block pay bs si nd a
  with nd | table-sound block-symbol pay bs {Q = λ s p → s ≡ once-symbol-path (name si) × p ≡ _} a
... | b₀ , m₀ , nm , bo | b , m , s≡ , p≡ = b₀ , m₀ , bo , trans (sym p≡) (cong pay (same b b₀ (trans s≡ (cong once-symbol-path nm))))
  where
    same : ∀ (b b₀ : ArithBlock) → block-symbol b ≡ once-symbol-path (bare (block-name (block-body b₀))) → b ≡ b₀
    same (mk-block sh n e) (mk-block sh₀ n₀ e₀) eq with block-symbol-injective e e₀ eq
    ... | refl = refl

------------------------------------------------------------------------
-- D459: THE TABLE OF A BLOCK LIST, for any image whose calls name its blocks.
--
-- The linear core's image has its own blocks (`LinCore.ImageOwned`). What the
-- arch layer reads: every `instr-sigop si` of the program names a block of
-- `bs` (`SigNamed`), and the file's table is `bs`'s, by symbol, once each
-- (`Target.Backend.file-table`).
------------------------------------------------------------------------

open import Once.CCC.Machine.SMCore using (AbstractTrace; AbstractInstr; instr-sigop)
import Data.List.Relation.Unary.All as All

-- an instruction that calls an op names a block of `bs`
SigNamed : List ArithBlock → AbstractInstr → Set
SigNamed bs i = ∀ {A B} (si : SigOpInfo A B) → i ≡ instr-sigop si → Named bs si
