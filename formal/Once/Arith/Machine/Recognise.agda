-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.Machine.Recognise
--
-- Plan 0.20 Phase B — the recognition pass.
--
-- Given a CCC morphism `IR A B`, attempt to classify it as a pure
-- arith block: an expression tree built only from
--   - `intLit n` (== `const fits-int n |n| ∘ terminal`)
--   - input projections (`snd`, `fst`, compositions thereof)
--   - the arithmetic SigOps `arith.{add,sub,mul,neg}.int`
--
-- A subtree containing `apply`, `case`, `cata`, μ-constructors,
-- closure references, or non-arith SigOps is *not* an arith block:
-- recognition returns `nothing` and the caller leaves the subtree
-- as ordinary CCC.
--
-- The recogniser is intentionally type-AGNOSTIC: it pattern-matches
-- on IR constructors without ever forcing the codomain from outside,
-- which avoids the dependent-pattern-matching dead-ends triggered by
-- `out-μ` and friends (whose indices unify badly with a fixed
-- product/Int target). Phase C's validity theorem layers typing on
-- top: when recognition succeeds and the IR is well-typed at Int,
-- the abstract trace matches eval-arith.
------------------------------------------------------------------------

module Once.Arith.Machine.Recognise where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Integer using (ℤ; +_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Type using (Type; Unit; Int)
open import Once.IR
open import Once.SigOp.Info using (SigOpInfo; name; sem; SigOpSem; primV)
open import Once.Arith.Prim using (p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f)
open import Once.IRTy using (⌊_⌋)
import Once.IRTy as II
open import Once.CanonicalName using (bare; _≟ᶜ_)

open import Once.Arith.Machine.AbsState
  using (InputShape; shape-int; shape-float; shape-pair; InputPath;
         Side; Fst; Snd; Path; typePath?)
-- PLAN 0.75 F4: the abstract-machine compile path is pinned at `NInt`, and
-- that restriction is STATED rather than assumed. Its instruction set
-- (`add-rrr`, `div-rrr`, …) is integer-register shaped, so a float block has
-- no lowering here yet; saying so in the type means the gate sees the gap
-- instead of a float tree silently taking the integer path.
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f; acmp;
         numtype-as-type; ArithBlock;
         mk-block)

------------------------------------------------------------------------
-- Projection-path recognition
------------------------------------------------------------------------

-- | Recognise a CCC morphism that's a pure projection chain.
--
-- Returns the `InputPath` corresponding to "from the input, walk
-- this sequence of Fst/Snd to reach the result." Composition is
-- ordered "rightmost first": `snd ∘ fst` is the path `[Fst, Snd]`.
--
-- Returns `nothing` for non-projection morphisms.
-- D163: recognition must see terms UP TO THE CCC LAWS, because the elaborator
-- no longer hands it normal forms. QTT (plan 0.86) wraps every operand in a
-- usage restriction — `envˡ` / `envʳ`, i.e. `restrictEnv`, which is `fst` where
-- a variable is dropped and `⟨ … ∘ fst , snd ⟩` where it is kept. That pair is
-- not a projection, so the old `recognise-path` returned `nothing` for every
-- arith operand and NO arith block was ever built again. The bare
-- `arith.<op>.int` SigOp then reached the emitter as a call to a symbol nothing
-- defines: 19 exit tests and 119 cabal tests, all `undefined reference`.
--
-- The fix is PRODUCT BETA — `fst ∘ ⟨a,b⟩ ≡ a`, `snd ∘ ⟨a,b⟩ ≡ b` — applied
-- while walking, so an environment reshuffle collapses back to the projection
-- it denotes. `recognise-path-through` carries the path accumulated SO FAR into
-- the morphism being applied, which is what lets it choose a component: a pair
-- consumes one step and recurses into that side. Its indices are free, the
-- `recognise-binop` trick (a pinned product index is unification-stuck).
-- the two shapes of an operator's operands
binop : ∀ {X Y : Set} → (X → X → Y) → Maybe (X × X) → Maybe Y
binop k (just (a , b)) = just (k a b)
binop k nothing        = nothing

pair-of : ∀ {X : Set} → Maybe X → Maybe X → Maybe (X × X)
pair-of (just a) (just b) = just (a , b)
pair-of (just a) nothing  = nothing
pair-of nothing  _        = nothing

-- The operand view: a pair, a pair after an environment step, or neither.
data BView : ∀ {X Y} → IR X Y → Set where
  bv-pair  : ∀ {X Y Z} (a : IR X Y) (b : IR X Z) → BView ⟨ a , b ⟩
  bv-dist  : ∀ {W X Y Z} (a : IR X Y) (b : IR X Z) (h : IR W X) → BView (⟨ a , b ⟩ ∘ h)
  bv-other : ∀ {X Y} (e : IR X Y) → BView e

b-view : ∀ {X Y} (e : IR X Y) → BView e
b-view ⟨ a , b ⟩       = bv-pair a b
b-view (⟨ a , b ⟩ ∘ h) = bv-dist a b h
{-# CATCHALL #-}
b-view e               = bv-other e

unop : ∀ {X Y : Set} → (X → Y) → Maybe X → Maybe Y
unop k (just a) = just (k a)
unop k nothing  = nothing

-- ENVIRONMENT PLUMBING: projections, pairing, `terminal` and their
-- composites. Its meaning is a value and no event, so a literal may absorb it.
plumbing? : ∀ {X Y} → IR X Y → Bool
plumbing? id          = true
plumbing? fst         = true
plumbing? snd         = true
plumbing? terminal    = true
plumbing? ⟨ f , g ⟩   = plumbing? f ∧ plumbing? g
plumbing? (f ∘ g)     = plumbing? f ∧ plumbing? g
{-# CATCHALL #-}
plumbing? _           = false

-- A literal's right-hand side: `terminal`, after plumbing.
data TView : ∀ {X Y} → IR X Y → Set where
  tv-term  : ∀ {X} → TView (terminal {X})
  tv-comp  : ∀ {X Z} (g : IR X Z) → TView (terminal ∘ g)
  tv-other : ∀ {X Y} (m : IR X Y) → TView m

t-view : ∀ {X Y} (m : IR X Y) → TView m
t-view terminal       = tv-term
t-view (terminal ∘ g) = tv-comp g
{-# CATCHALL #-}
t-view m              = tv-other m

it-at : ∀ {X Y} (m : IR X Y) → TView m → Bool
it-at .terminal       tv-term      = true
it-at .(terminal ∘ g) (tv-comp g)  = plumbing? g
it-at m               (tv-other m) = false

is-terminal? : ∀ {X Y} → IR X Y → Bool
is-terminal? m = it-at m (t-view m)

-- The path view: the shapes an input path is read through, and everything else.
data PView : ∀ {A B} → IR A B → Set where
  pv-id    : ∀ {A} → PView (id {A})
  pv-fst   : ∀ {A B} → PView (fst {A} {B})
  pv-snd   : ∀ {A B} → PView (snd {A} {B})
  pv-pair  : ∀ {A B C} (a : IR A B) (b : IR A C) → PView ⟨ a , b ⟩
  pv-comp  : ∀ {A B C} (f : IR B C) (g : IR A B) → PView (f ∘ g)
  pv-other : ∀ {A B} (m : IR A B) → PView m

p-view : ∀ {A B} (m : IR A B) → PView m
p-view id          = pv-id
p-view fst         = pv-fst
p-view snd         = pv-snd
p-view ⟨ a , b ⟩   = pv-pair a b
p-view (f ∘ g)     = pv-comp f g
{-# CATCHALL #-}
p-view m           = pv-other m

recognise-path         : ∀ {A B} → IR A B → Maybe InputPath
recognise-path-through : ∀ {A B} → IR A B → InputPath → Maybe InputPath
rp-at                  : ∀ {A B} (m : IR A B) → PView m → InputPath → Maybe InputPath
rp-comp                : ∀ {A B} → IR A B → Maybe InputPath → Maybe InputPath
pair-path              : ∀ {A B} → Bool → IR A B → InputPath → Maybe InputPath

recognise-path m = recognise-path-through m []
recognise-path-through m p = rp-at m (p-view m) p

rp-at .id            pv-id         p         = just p
rp-at .fst           pv-fst        p         = just (Fst ∷ p)
rp-at .snd           pv-snd        p         = just (Snd ∷ p)
-- A pair is navigated only when the component NOT taken is plumbing: its
-- meaning is a value and no event, so reading through the pair drops nothing.
rp-at .(⟨ a , b ⟩)   (pv-pair a b) (Fst ∷ p) = pair-path (plumbing? b) a p
rp-at .(⟨ a , b ⟩)   (pv-pair a b) (Snd ∷ p) = pair-path (plumbing? a) b p
rp-at .(⟨ a , b ⟩)   (pv-pair a b) []        = nothing
rp-at .(f ∘ g)       (pv-comp f g) p         = rp-comp g (recognise-path-through f p)
rp-at m              (pv-other m)  p         = nothing

rp-comp g (just pf) = recognise-path-through g pf
rp-comp g nothing   = nothing

pair-path true  m p = recognise-path-through m p
pair-path false m p = nothing

------------------------------------------------------------------------
-- Arith body recognition (type-agnostic on IR's codomain)
------------------------------------------------------------------------

-- | Recognise a CCC morphism as an arith body over `sh`.
--
-- The IR's codomain is left fully generic so that Agda's case tree
-- only ever dispatches on the morphism's CONSTRUCTOR; we never
-- pin the codomain to `Int` or `Int * Int` from outside. SigOp
-- arithmetic ops are identified by `name` (string compare), which
-- carries enough information without forcing index unification.
-- THE SHAPE VIEW the recogniser dispatches on (explicit-aux form): the four
-- shapes it reads, and everything else — an input path, if anything.
data RBView : ∀ {A B} → IR A B → Set where
  v-reassoc : ∀ {A B C D} (f : IR C D) (g : IR B C) (h : IR A B) → RBView ((f ∘ g) ∘ h)
  v-sigop   : ∀ {A X Y} (si : SigOpInfo X Y) (e : IR A ⌊ X ⌋) → RBView (SigOp si ∘ e)
  v-cint    : ∀ {A} (v : _) (rhs : IR A II.Unit) → RBView (const fits-int v ∘ rhs)
  v-cflt    : ∀ {A} (d : _) (rhs : IR A II.Unit) → RBView (const fits-float d ∘ rhs)
  v-other   : ∀ {A B} (ir : IR A B) → RBView ir

rb-view : ∀ {A B} (ir : IR A B) → RBView ir
rb-view ((f ∘ g) ∘ h)            = v-reassoc f g h
rb-view (SigOp si ∘ e)           = v-sigop si e
rb-view (const fits-int v ∘ rhs) = v-cint v rhs
rb-view (const fits-float d ∘ rhs) = v-cflt d rhs
{-# CATCHALL #-}
rb-view ir                       = v-other ir

-- a literal, when its right-hand side is `terminal` after plumbing
lit-at : ∀ {sh} → Bool → _ → Maybe (MArithIR sh NInt)
lit-at true  v = just (alit v)
lit-at false v = nothing

flit-at : ∀ {sh} → Bool → _ → Maybe (MArithIR sh NFloat)
flit-at true  d = just (aflit d)
flit-at false d = nothing

-- an input path, when it lands on a leaf of the right kind
path-at : ∀ (sh : InputShape) (n : NumType) → Maybe InputPath → Maybe (MArithIR sh n)
path-at sh n (just p) = unop ainput (typePath? sh n p)
path-at sh n nothing  = nothing

{-# TERMINATING #-}
recognise-body : (sh : InputShape) → ∀ {A B} → IR A B → Maybe (MArithIR sh NInt)
-- `recognise-binop` recognises the two operands of a binary op. Its codomain
-- `Y` is a FREE variable, so matching `⟨_,_⟩` instantiates `Y := B * C` freely —
-- unlike matching the pair directly under `SigOp _ ∘ _`, where the middle object
-- is the SigOp's ERASED domain `⌊Dom⌋` and `⌊Dom⌋ ≟ B * C` is unification-stuck
-- (`⌊_⌋` non-invertible). Plan 0.52 M2.
recognise-binop : (sh : InputShape) → ∀ {X Y} → IR X Y → Maybe (MArithIR sh NInt × MArithIR sh NInt)
-- D255: `SigOp si ∘ e` is an arithmetic op when its semantics IS one — the
-- compiler's primitive (`primV`), whose meaning is fixed by it — not when its
-- name looks like one.
recognise-prim : (sh : InputShape) → ∀ {X Y A} → SigOpSem X Y → IR A ⌊ X ⌋ → Maybe (MArithIR sh NInt)
rb-at          : (sh : InputShape) → ∀ {A B} (ir : IR A B) → RBView ir → Maybe (MArithIR sh NInt)
binop-at       : (sh : InputShape) → ∀ {X Y Z W} → Bool → IR Z X → IR Z Y → IR W Z
               → Maybe (MArithIR sh NInt × MArithIR sh NInt)
rbin-at        : (sh : InputShape) → ∀ {X Y} (e : IR X Y) → BView e → Maybe (MArithIR sh NInt × MArithIR sh NInt)
recognise-binop sh e = rbin-at sh e (b-view e)

rbin-at sh .(⟨ a , b ⟩)     (bv-pair a b)   = pair-of (recognise-body sh a) (recognise-body sh b)
rbin-at sh .(⟨ a , b ⟩ ∘ h) (bv-dist a b h) = binop-at sh (plumbing? h) a b h
rbin-at sh e                (bv-other e)    = nothing
-- D163: `⟨a,b⟩ ∘ h ≡ ⟨ a ∘ h , b ∘ h ⟩` — composition distributes over pairing.
-- QTT hands the operand pair an environment restriction `h`, and pushing it
-- into the components is what lets each one be recognised on its own.
-- …and only when `h` is plumbing: distributing runs `h` twice, which means
-- the same only when `h`'s meaning is a value and no event.

binop-at sh true a b h  = pair-of (recognise-body sh (a ∘ h)) (recognise-body sh (b ∘ h))
binop-at sh false a b h = nothing

recognise-prim sh (primV p-add) e = binop aadd (recognise-binop sh e)
recognise-prim sh (primV p-sub) e = binop asub (recognise-binop sh e)
recognise-prim sh (primV p-mul) e = binop amul (recognise-binop sh e)
recognise-prim sh (primV p-div) e = binop adiv (recognise-binop sh e)
recognise-prim sh (primV p-mod) e = binop amod (recognise-binop sh e)
recognise-prim sh (primV p-neg) e = unop aneg (recognise-body sh e)
{-# CATCHALL #-}
recognise-prim sh _             e = nothing

-- Binary/unary-op `SigOp si ∘ e` — dispatch on `name si`; `e` stays GENERIC so
-- the pair operand is recognised by `recognise-binop` (no stuck product index).
-- D163: RE-ASSOCIATE FIRST. `∘` is a constructor, so `(f ∘ g) ∘ h` is a
-- different TERM from `f ∘ (g ∘ h)` even though the CCC law identifies them,
-- and every clause below matches on the right-nested form. QTT (plan 0.86)
-- composes a usage restriction onto each operand, and `effApp` composes
-- another on top, so operands arrive left-nested to arbitrary depth —
-- `((SigOp fdiv ∘ ⟨…⟩) ∘ envˡ) ∘ envʳ`. One clause, applied repeatedly,
-- normalises all of it; it strictly reduces left-nesting, so it terminates.
recognise-body sh ir = rb-at sh ir (rb-view ir)

rb-at sh .((f ∘ g) ∘ h)            (v-reassoc f g h) = recognise-body sh (f ∘ (g ∘ h))
rb-at sh .(SigOp si ∘ e)            (v-sigop si e)    = recognise-prim sh (sem si) e
rb-at sh .(const fits-int v ∘ rhs)  (v-cint v rhs)    = lit-at (is-terminal? rhs) v
rb-at sh .(const fits-float d ∘ rhs) (v-cflt d rhs)   = nothing
rb-at sh ir                         (v-other ir)      = path-at sh NInt (recognise-path ir)


------------------------------------------------------------------------
-- FLOAT body recognition (plan 0.75 F4, step 2)
--
-- A SEPARATE function rather than a `NumType`-indexed one, and deliberately:
-- the integer chain above is proven and heavily `with`-structured, and giving
-- it an extra index would rewrite every continuation for no gain. The two are
-- MUTUALLY recursive in one place only — `arith.i2f`, D125's widening, which
-- is the single node where a float tree contains an integer one.
--
-- The SigOp names are what separate the kinds. `arith.add.int` and
-- `arith.add.float` are different instructions on every target, so matching by
-- name is exactly the right discrimination and no type index is needed.
------------------------------------------------------------------------

{-# TERMINATING #-}
recognise-body-float : (sh : InputShape) → ∀ {A B} → IR A B → Maybe (MArithIR sh NFloat)

recognise-binop-float : (sh : InputShape) → ∀ {X Y} → IR X Y
                      → Maybe (MArithIR sh NFloat × MArithIR sh NFloat)
recognise-prim-float : (sh : InputShape) → ∀ {X Y A} → SigOpSem X Y → IR A ⌊ X ⌋ → Maybe (MArithIR sh NFloat)
rbf-at               : (sh : InputShape) → ∀ {A B} (ir : IR A B) → RBView ir → Maybe (MArithIR sh NFloat)
binop-at-float       : (sh : InputShape) → ∀ {X Y Z W} → Bool → IR Z X → IR Z Y → IR W Z
                     → Maybe (MArithIR sh NFloat × MArithIR sh NFloat)
rbinf-at             : (sh : InputShape) → ∀ {X Y} (e : IR X Y) → BView e → Maybe (MArithIR sh NFloat × MArithIR sh NFloat)
recognise-binop-float sh e = rbinf-at sh e (b-view e)

-- D163: distribution, the float twin. See the int version.
rbinf-at sh .(⟨ a , b ⟩)     (bv-pair a b)   = pair-of (recognise-body-float sh a) (recognise-body-float sh b)
rbinf-at sh .(⟨ a , b ⟩ ∘ h) (bv-dist a b h) = binop-at-float sh (plumbing? h) a b h
rbinf-at sh e                (bv-other e)    = nothing

binop-at-float sh true a b h = pair-of (recognise-body-float sh (a ∘ h)) (recognise-body-float sh (b ∘ h))
binop-at-float sh false a b h = nothing

recognise-prim-float sh (primV p-fadd) e = binop aadd (recognise-binop-float sh e)
recognise-prim-float sh (primV p-fsub) e = binop asub (recognise-binop-float sh e)
recognise-prim-float sh (primV p-fmul) e = binop amul (recognise-binop-float sh e)
recognise-prim-float sh (primV p-fdiv) e = binop adiv (recognise-binop-float sh e)
recognise-prim-float sh (primV p-i2f)  e = unop ai2f (recognise-body sh e)
{-# CATCHALL #-}
recognise-prim-float sh _              e = nothing

-- D163: re-associate first — the float twin. See the int version.
recognise-body-float sh ir = rbf-at sh ir (rb-view ir)

rbf-at sh .((f ∘ g) ∘ h)            (v-reassoc f g h) = recognise-body-float sh (f ∘ (g ∘ h))
rbf-at sh .(SigOp si ∘ e)            (v-sigop si e)    = recognise-prim-float sh (sem si) e
rbf-at sh .(const fits-int v ∘ rhs)  (v-cint v rhs)    = nothing
rbf-at sh .(const fits-float d ∘ rhs) (v-cflt d rhs)   = flit-at (is-terminal? rhs) d
rbf-at sh ir                         (v-other ir)      = path-at sh NFloat (recognise-path ir)

------------------------------------------------------------------------
-- Block-level entry
------------------------------------------------------------------------

-- | Top-level entry. The caller (a higher-level extraction pass)
-- strips enclosing `curry` layers off the source lambda and
-- supplies the resulting `InputShape` plus the body IR.
-- | Top-level entry, now taking the KIND the caller wants. `Once.Arith.Machine.
-- Rewrite` reads it off the morphism's CODOMAIN — a block returning `Int` is an
-- integer block and one returning `Float` is a float block — so recognition
-- never has to guess.
recognise : (sh : InputShape) (n : NumType) → ∀ {A B} → IR A B → Maybe ArithBlock
recognise sh NInt ir with recognise-body sh ir
... | just body = just (mk-block sh NInt body)
... | nothing   = nothing
recognise sh NFloat ir with recognise-body-float sh ir
... | just body = just (mk-block sh NFloat body)
... | nothing   = nothing
