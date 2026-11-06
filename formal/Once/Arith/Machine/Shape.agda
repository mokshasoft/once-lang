-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Machine.Shape
--
-- The WIDTH-AGNOSTIC core of the arith-block machine: the input-shape
-- tree, its word-leaf interpretation `⟦_⟧S`, and positional `InputPath`s.
--
-- Split out of `Once.Arith.Machine.AbsState` (clean-semantics L1 step a)
-- so the width-bearing abstract state can be parameterised by `bits`
-- (D054 `Word` width) WITHOUT dragging the width into `MArithIR` /
-- `ArithBlock` — which `Once.Compile` / `Once.Target` consume
-- width-agnostically. Nothing here mentions `Word`.
------------------------------------------------------------------------

module Once.Arith.Machine.Shape where

open import Data.Nat using (ℕ; _+_; _*_; _<_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Arith.Type using (NumType; NInt; NFloat)

------------------------------------------------------------------------
-- InputShape: tree-shape of an arith block's input
--
-- Plan 0.20 Phase G: shape-unit added so closed arith expressions
-- (`exit (3 + 5*2)`) — whose CCC type is `IR Unit Int` — can be
-- lifted into a block. With shape-int / shape-pair only, recognition
-- could never produce a SigOpInfo whose A matched Unit.
------------------------------------------------------------------------

data InputShape : Set where
  shape-unit  : InputShape
  shape-int   : InputShape
  -- PLAN 0.75 F4: a FLOAT leaf. Its spec value is the target's BIT PATTERN,
  -- not an exact number — D113 removed the exact value level from `Float`
  -- exactly as D054 removed it from `Int`. D396: so both leaves are WORDS —
  -- the `Int` leaf is the machine word `Int` denotes (D054), not a ℤ that
  -- `fromℤ` narrows; a block computes on exactly the words its SigOp does.
  shape-float : InputShape
  shape-pair  : InputShape → InputShape → InputShape

⟦_⟧S : InputShape → Set
⟦ shape-unit      ⟧S = ⊤
⟦ shape-int       ⟧S = ℕ
⟦ shape-float     ⟧S = ℕ
⟦ shape-pair l r  ⟧S = ⟦ l ⟧S × ⟦ r ⟧S

------------------------------------------------------------------------
-- InputPath
------------------------------------------------------------------------

data Side : Set where
  Fst : Side
  Snd : Side

InputPath : Set
InputPath = List Side

-- | Project an `Int` leaf. A path that lands anywhere else — including on a
-- FLOAT leaf — is `nothing`, and the caller defaults. Recognition only ever
-- builds paths that land correctly; the validity theorem restates that, so the
-- default never fires in practice.
project : ∀ (sh : InputShape) → InputPath → ⟦ sh ⟧S → Maybe ℕ
project shape-unit       _        _       = nothing
project shape-int        []       z       = just z
project shape-int        (_ ∷ _)  _       = nothing
project shape-float      _        _       = nothing
project (shape-pair _ _) []       _       = nothing
project (shape-pair l _) (Fst ∷ p) (x , _) = project l p x
project (shape-pair _ r) (Snd ∷ p) (_ , y) = project r p y

-- | …and its FLOAT twin (plan 0.75 F4). Two projections rather than one
-- returning a sum: the leaf types are different Agda types, and a caller
-- always knows which it wants — the `MArithIR` node it is evaluating is
-- indexed by the `NumType`.
projectF : ∀ (sh : InputShape) → InputPath → ⟦ sh ⟧S → Maybe ℕ
projectF shape-unit       _        _       = nothing
projectF shape-int        _        _       = nothing
projectF shape-float      []       w       = just w
projectF shape-float      (_ ∷ _)  _       = nothing
projectF (shape-pair _ _) []       _       = nothing
projectF (shape-pair l _) (Fst ∷ p) (x , _) = projectF l p x
projectF (shape-pair _ r) (Snd ∷ p) (_ , y) = projectF r p y

------------------------------------------------------------------------
-- TYPED PATHS — the leaf's type is part of the path, not a side condition
--
-- `project`'s header above says the quiet part out loud: "a path that lands
-- anywhere else — including on a FLOAT leaf — is `nothing`, and the caller
-- defaults… the default never fires in practice." That default is a value
-- INVENTED for a case that should not exist, and inventing it is what made the
-- float-argument correspondence unstatable: `R-input` had to claim the
-- concrete load equals the INTEGER reading at every path, which is false at a
-- float leaf, and no repair fixes it because the missing fact — which leaf
-- this load reads — is decided by the PROGRAM and cannot be recovered from a
-- state relation.
--
-- So the fact travels with the path. A `Path sh n` is a path that lands on an
-- `n` leaf of `sh`, BY CONSTRUCTION, and `readLeaf` is total: there is no
-- `Maybe`, hence no default, hence nothing to be false about. `shape-unit` and
-- interior nodes simply have no inhabitant, which is the correct statement —
-- nothing loads from them.
------------------------------------------------------------------------

data Path : InputShape → NumType → Set where
  here-int : Path shape-int   NInt
  here-flt : Path shape-float NFloat
  go-fst   : ∀ {l r n} → Path l n → Path (shape-pair l r) n
  go-snd   : ∀ {l r n} → Path r n → Path (shape-pair l r) n

-- | What a leaf of each kind holds: a word (D396) — the `Int`'s two's
-- complement residue, the float's bit pattern.
LeafVal : NumType → Set
LeafVal NInt   = ℕ
LeafVal NFloat = ℕ

-- | THE read. Total, because the path proves the leaf is there.
readLeaf : ∀ {sh n} → Path sh n → ⟦ sh ⟧S → LeafVal n
readLeaf here-int   z       = z
readLeaf here-flt   w       = w
readLeaf (go-fst p) (x , _) = readLeaf p x
readLeaf (go-snd p) (_ , y) = readLeaf p y

-- | D396: the input's `Int` leaves are words — each below the target's modulus
-- `m`. A value the program holds is the target's (its ops `norm`, its literals
-- are elaborated words, the world's answers are read at the target), and the
-- block's code computes on the word as it is (`lit-word` is the identity).
IntsBelow : ℕ → ∀ sh → ⟦ sh ⟧S → Set
IntsBelow m shape-unit       _       = ⊤
IntsBelow m shape-int        v       = v < m
IntsBelow m shape-float      _       = ⊤
IntsBelow m (shape-pair l r) (x , y) = IntsBelow m l x × IntsBelow m r y

readLeaf-below : ∀ {m sh} (p : Path sh NInt) (env : ⟦ sh ⟧S) → IntsBelow m sh env → readLeaf p env < m
readLeaf-below here-int   v       h       = h
readLeaf-below (go-fst p) (x , _) (h , _) = readLeaf-below p x h
readLeaf-below (go-snd p) (_ , y) (_ , h) = readLeaf-below p y h

-- | Erasure to the untyped path. The CONCRETE side wants this: an address
-- computation genuinely does not care which type lives at the end of it, so
-- the index stops at the boundary rather than being pushed through the ISA.
⌊_⌋ᴾ : ∀ {sh n} → Path sh n → InputPath
⌊ here-int  ⌋ᴾ = []
⌊ here-flt  ⌋ᴾ = []
⌊ go-fst p  ⌋ᴾ = Fst ∷ ⌊ p ⌋ᴾ
⌊ go-snd p  ⌋ᴾ = Snd ∷ ⌊ p ⌋ᴾ

-- | D390: WHERE A LEAF IS, in the flat layout (D380). A compound input is a
-- pointer to its words; a component is embedded, so a leaf is one word at the
-- sum of its left siblings' sizes along the path. A whole-input scalar (`[]`)
-- is its register, as before.
shape-size : InputShape → ℕ
shape-size shape-unit       = 0
shape-size shape-int        = 1
shape-size shape-float      = 1
shape-size (shape-pair l r) = shape-size l + shape-size r

-- the word offset of a typed path's leaf (left siblings' sizes, along the path)
flat-off : ∀ {sh n} → Path sh n → ℕ
flat-off here-int            = 0
flat-off here-flt            = 0
flat-off (go-fst p)          = flat-off p
flat-off (go-snd {l = l} p)  = shape-size l + flat-off p

-- the address a target reads a leaf from, for a word of `w` bytes: the input
-- pointer `base` itself for `[]` (as the arch models have it), else one word
-- at the leaf's offset
flat-addr : (w base : ℕ) → InputPath → ℕ → ℕ
flat-addr w base []      k = base
flat-addr w base (_ ∷ _) k = base + w * k

-- | …and the two bridges that retire the defaults: along an erased typed path
-- the old projections are `just`, so `maybe-zero` provably never fires.
project-path : ∀ {sh} (p : Path sh NInt) (inp : ⟦ sh ⟧S)
             → project sh ⌊ p ⌋ᴾ inp ≡ just (readLeaf p inp)
project-path here-int   z       = refl
project-path (go-fst p) (x , _) = project-path p x
project-path (go-snd p) (_ , y) = project-path p y

projectF-path : ∀ {sh} (p : Path sh NFloat) (inp : ⟦ sh ⟧S)
              → projectF sh ⌊ p ⌋ᴾ inp ≡ just (readLeaf p inp)
projectF-path here-flt   w       = refl
projectF-path (go-fst p) (x , _) = projectF-path p x
projectF-path (go-snd p) (_ , y) = projectF-path p y

-- | Type an untyped path against a shape. This is the FRONTIER: recognition
-- meets an `InputPath` read off a projection chain and must establish which
-- leaf it lands on before it can build an `ainput`.
--
-- `nothing` is now a REFUSAL rather than a silent zero. Before typed paths, a
-- chain landing on a float leaf in an `Int` tree was recognised happily and
-- then evaluated to `0`; now it is simply not an arith block, and stays a
-- general IR term. That is a behaviour change and it is the right one.
typePath? : ∀ (sh : InputShape) (n : NumType) → InputPath → Maybe (Path sh n)
typePath? shape-int        NInt   []        = just here-int
typePath? shape-float      NFloat []        = just here-flt
typePath? (shape-pair l _) n      (Fst ∷ p) = mapᴹ go-fst (typePath? l n p)
typePath? (shape-pair _ r) n      (Snd ∷ p) = mapᴹ go-snd (typePath? r n p)
typePath? shape-unit       _      _         = nothing
typePath? shape-int        NInt   (_ ∷ _)   = nothing
typePath? shape-int        NFloat _         = nothing
typePath? shape-float      NFloat (_ ∷ _)   = nothing
typePath? shape-float      NInt   _         = nothing
typePath? (shape-pair _ _) _      []        = nothing
