-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.FlatLayout — HOW A COMPONENT GOES INTO A BLOCK (plan 0.123
-- B.4 α, D375, D378).
--
-- A value is one of two kinds, by its type alone:
--   word — a scalar (Int, Float) or a node (μ, ν, a closure): ONE word, held in
--          a register as itself;
--   flat — Unit, a product or a sum: its `size` words at an address, held in a
--          register as that address.
-- So a component goes into its container's block as its word (`store-at`), or
-- as a copy of its words (`copy-from`). One rule, used by every construct.
------------------------------------------------------------------------

module Once.CCC.Codegen.FlatLayout where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Once.IRTy using (IRTy; Unit; Void; _*_; _⇛_; μ-type; ν-type; Int; Float; ⌈_⌉) renaming (_+_ to _+ᵀ_)
open import Once.Spec.Type using (Ty; Fun; var)
import Once.Spec.Type as T
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; restore-input; load-from-slot; load-at; store-at; addr-at)

data Kind : Set where
  word flat : Kind

kind : IRTy → Kind
kind Unit       = flat
kind Void       = flat
kind (_ * _)    = flat
kind (_ +ᵀ _)   = flat
kind (_ ⇛ _)    = word
kind (μ-type _) = word
kind (ν-type _) = word
kind Int        = word
kind Float      = word

-- the k words from word i of the value whose address is in slot `src`, to the
-- block whose address is in slot `blk`, from its word `off + i`
copy-from : (src blk off i k : ℕ) → AbstractTrace
copy-from src blk off i zero    = []
copy-from src blk off i (suc k) =
  restore-input src ∷ load-at i ∷ restore-input blk ∷ store-at (off + i) ∷
  copy-from src blk off (suc i) k

-- a component, stashed in slot `stash`, into the block in slot `blk` at `off`
put-k : Kind → ℕ → (stash blk off : ℕ) → AbstractTrace
put-k word _ stash blk off = restore-input blk ∷ load-from-slot stash ∷ store-at off ∷ []
put-k flat n stash blk off = copy-from stash blk off 0 n

put : IRTy → (stash blk off : ℕ) → AbstractTrace
put X = put-k (kind X) (size X)

-- the component at word `k` of the flat value whose address is in `Input1`, into
-- `Output`: a word kind is its word, a flat kind its address. A 0-word component
-- reads nothing, so any cell of the block is its address: it takes the
-- container's own (word 0 — always in the block, so `addr-at` never points past
-- it, D379).
get-k : Kind → ℕ → ℕ → AbstractTrace
get-k word _       k = load-at k ∷ []
get-k flat zero    k = addr-at 0 ∷ []
get-k flat (suc _) k = addr-at k ∷ []

get : IRTy → ℕ → AbstractTrace
get X = get-k (kind X) (size X)

------------------------------------------------------------------------
-- WHAT THE LAYOUT CODE IS MADE OF, for the structural facts about emitted
-- code (fences, slot budgets, labels, …): `copy-from`/`put` use only the two
-- stash slots' restores and loads and the offset load/store, `get` only the
-- offset load or address. A property of those instructions is a property of
-- every such trace.
------------------------------------------------------------------------
module _ {P : AbstractInstr → Set} where
  copy-from-All : ∀ src blk off i k
                → P (restore-input src) → P (restore-input blk)
                → (∀ j → P (load-at j)) → (∀ j → P (store-at j))
                → All P (copy-from src blk off i k)
  copy-from-All src blk off i zero    rs rb pl ps = []
  copy-from-All src blk off i (suc k) rs rb pl ps =
    rs ∷ pl i ∷ rb ∷ ps (off + i) ∷ copy-from-All src blk off (suc i) k rs rb pl ps

  put-k-All : ∀ kd n stash blk off
            → P (restore-input stash) → P (restore-input blk) → P (load-from-slot stash)
            → (∀ j → P (load-at j)) → (∀ j → P (store-at j))
            → All P (put-k kd n stash blk off)
  put-k-All word n stash blk off rs rb ls pl ps = rb ∷ ls ∷ ps off ∷ []
  put-k-All flat n stash blk off rs rb ls pl ps = copy-from-All stash blk off 0 n rs rb pl ps

  put-All : ∀ X stash blk off
          → P (restore-input stash) → P (restore-input blk) → P (load-from-slot stash)
          → (∀ j → P (load-at j)) → (∀ j → P (store-at j))
          → All P (put X stash blk off)
  put-All X = put-k-All (kind X) (size X)

  get-k-All : ∀ kd n k → (∀ j → P (load-at j)) → (∀ j → P (addr-at j)) → All P (get-k kd n k)
  get-k-All word n       k pl pa = pl k ∷ []
  get-k-All flat zero    k pl pa = pa 0 ∷ []
  get-k-All flat (suc _) k pl pa = pa k ∷ []

  get-All : ∀ X k → (∀ j → P (load-at j)) → (∀ j → P (addr-at j)) → All P (get X k)
  get-All X = get-k-All (kind X) (size X)

------------------------------------------------------------------------
-- THE SAME RULE ON SPEC TYPES, for the walks indexed by a Spec functor (the
-- cata's `Fun 0`): a type's size and kind, and a LAYER's `⟦ G ⟧ X` at a
-- carrier of kind `ck` and size `cs` (a μ carrier: a word of size 1).
------------------------------------------------------------------------
ssize : ∀ {m} → Ty m → ℕ
ssize (var _)        = 1
ssize T.Unit         = 0
ssize T.Void         = 0
ssize (A T.* B)      = ssize A + ssize B
ssize (A T.+ B)      = suc (ssize A ⊔ ssize B)
ssize (_ T.⇒[ _ ] _) = 1
ssize (T.μ _)        = 1
ssize (T.ν _ _)      = 1
ssize T.Int          = 1
ssize T.Float        = 1

skind : ∀ {m} → Ty m → Kind
skind (var _)        = word
skind T.Unit         = flat
skind T.Void         = flat
skind (_ T.* _)      = flat
skind (_ T.+ _)      = flat
skind (_ T.⇒[ _ ] _) = word
skind (T.μ _)        = word
skind (T.ν _ _)      = word
skind T.Int          = word
skind T.Float        = word

lkind : Fun 0 → Kind → Kind
lkind (T.K A)   ck = skind A
lkind T.Id      ck = ck
lkind (_ T.⊕ _) ck = flat
lkind (_ T.⊗ _) ck = flat

lsz : Fun 0 → ℕ → ℕ
lsz (T.K A)   cs = ssize A
lsz T.Id      cs = cs
lsz (F T.⊕ G) cs = suc (lsz F cs ⊔ lsz G cs)
lsz (F T.⊗ G) cs = lsz F cs + lsz G cs

-- on the image of `⌈_⌉`, the two rules agree
size-ssize : ∀ (A : IRTy) → size A ≡ ssize ⌈ A ⌉
size-ssize Unit       = refl
size-ssize Void       = refl
size-ssize (A * B)    = cong₂ _+_ (size-ssize A) (size-ssize B)
size-ssize (A +ᵀ B)   = cong suc (cong₂ _⊔_ (size-ssize A) (size-ssize B))
size-ssize (A ⇛ B)    = refl
size-ssize (μ-type F) = refl
size-ssize (ν-type F) = refl
size-ssize Int        = refl
size-ssize Float      = refl

kind-skind : ∀ (A : IRTy) → kind A ≡ skind ⌈ A ⌉
kind-skind Unit       = refl
kind-skind Void       = refl
kind-skind (A * B)    = refl
kind-skind (A +ᵀ B)   = refl
kind-skind (A ⇛ B)    = refl
kind-skind (μ-type F) = refl
kind-skind (ν-type F) = refl
kind-skind Int        = refl
kind-skind Float      = refl
