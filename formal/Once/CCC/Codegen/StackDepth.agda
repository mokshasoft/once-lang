-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.StackDepth — D490: HOW DEEP EACH FUNCTION'S STACK GOES,
-- statically, and WHICH CALLS ARE CHECKED.
--
-- A function is an entry and the code up to the next entry (the start's segment
-- comes first): its OWNER. Its depth past its frame (`past`) is the most any of
-- its instructions pushes beyond the frame: a SigOp its block's words, an
-- UNCHECKED call one return word plus the callee's whole depth (`dep`: frame and
-- past). A CHECKED call costs nothing here: the room check before it finds its
-- `1 + dep` on the stack. A call is checked where it would close a cycle — a call
-- to its own function (a fold's recursion), or to a callee not marked bounded;
-- an indirect call unless every closure body is.
--
-- The table is a CERTIFICATE. It is computed by iteration over maps that nothing
-- proves anything about (`Codegen.StackDepthTable`); what the proof uses is
-- `consistent? T t ≡ true`, a check of every instruction against the table
-- (`Cert`, `cert-of`). On a cycle of unchecked calls the check is
-- `1 + dep ≤ past ≤ … ≤ dep`, so a table that leaves one unchecked fails it. The
-- pass then falls back to `T₀`: every call and every SigOp checked, every `past`
-- 0 — consistent by construction (`cert₀`).
------------------------------------------------------------------------

module Once.CCC.Codegen.StackDepth where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
import Data.Bool
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤ᵇ_; _≤_; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; instr-ctrl; instr-call-closure; instr-sigop
        ; c-entry; c-call-fn; c-label; c-jmp; c-branch-tag-zero; c-start; c-ret; c-leave; start-stack-words)
open import Once.CCC.Label using (EntryId; e-fn; e-thunk; _≡ᵇᴱ_; ≡ᵇᴱ-true; LabelId; _≡ᵇᴵ_)
open import Once.CCC.Codegen.AllocExpand using (skip-label)
open import Once.SigOp.Info using (SigOpSem; blockV; SigOpInfo; module SigOpInfo)
open import Once.Arith.Machine.IR using (MArithIR)
open import Once.Arith.Machine.Compile using (required-scratch; normalize)
open import Once.Arith.Type using (NInt; NFloat)

------------------------------------------------------------------------
-- D393: what a SigOp's block pushes, on the arch that pushes most: the call
-- sequence's words and its scratch
------------------------------------------------------------------------
block-scratch : ∀ {sh n} → MArithIR sh n → ℕ
block-scratch {n = NInt}   e = required-scratch (normalize e)
block-scratch {n = NFloat} e = required-scratch e

sigop-call-words : ℕ
sigop-call-words = 5

sigop-scratch : ∀ {A B} → SigOpSem A B → ℕ
sigop-scratch (blockV e _ _) = block-scratch e
{-# CATCHALL #-}
sigop-scratch _              = 0

sigop-need : ∀ {A B} → SigOpInfo A B → ℕ
sigop-need si = sigop-call-words + sigop-scratch (SigOpInfo.sem si)

------------------------------------------------------------------------
-- Who owns an instruction: the start's segment, or the entry last met
------------------------------------------------------------------------
data Owner : Set where
  o-start : Owner
  o-entry : EntryId → Owner

_≡ᵇᴼ_ : Owner → Owner → Bool
o-start   ≡ᵇᴼ o-start   = true
o-entry a ≡ᵇᴼ o-entry b = a ≡ᵇᴱ b
o-start   ≡ᵇᴼ o-entry _ = false
o-entry _ ≡ᵇᴼ o-start   = false

≡ᵇᴼ-true : ∀ (a b : Owner) → (a ≡ᵇᴼ b) ≡ true → a ≡ b
≡ᵇᴼ-true o-start     o-start     _ = refl
≡ᵇᴼ-true (o-entry a) (o-entry b) e = cong o-entry (≡ᵇᴱ-true a b e)

------------------------------------------------------------------------
-- What kind of instruction it is, as far as the stack's depth goes
------------------------------------------------------------------------
data Kind : Set where
  k-call  : EntryId → Kind          -- a direct call (its callee's entry)
  k-clo   : Kind                    -- an indirect call (some closure body)
  k-sig   : ℕ → Kind                -- a SigOp: what its block pushes
  k-entry : EntryId → ℕ → Kind      -- an entry: its frame
  k-label : LabelId → Kind
  k-jump  : LabelId → Kind          -- a jump to a label (control does not fall through)
  k-branch : LabelId → Kind         -- a branch to a label (or on)
  k-ret   : Kind                    -- a return, the leave (control does not fall through)
  k-start : ℕ → Kind               -- the start (it reserves the stack: D491 stage 4, its words)
  k-none  : Kind

kind : AbstractInstr → Kind
kind (instr-ctrl (c-call-fn g))         = k-call (e-fn g)
kind instr-call-closure                 = k-clo
kind (instr-sigop si)                   = k-sig (sigop-need si)
kind (instr-ctrl (c-entry e b))         = k-entry e b
kind (instr-ctrl (c-label ℓ))           = k-label ℓ
kind (instr-ctrl (c-jmp ℓ))             = k-jump ℓ
kind (instr-ctrl (c-branch-tag-zero ℓ)) = k-branch ℓ
kind (instr-ctrl (c-ret _))             = k-ret
kind (instr-ctrl c-leave)               = k-ret
kind (instr-ctrl (c-start _ r))           = k-start r
{-# CATCHALL #-}
kind _                                  = k-none

-- the owner of an instruction, given the owner before it (an entry owns itself)
own-k : Owner → Kind → Owner
own-k o (k-entry e _) = o-entry e
own-k o (k-call _)    = o
own-k o k-clo         = o
own-k o (k-sig _)     = o
-- (D490: the allocator outline's skip label is the start's — its routines sit
-- in the start's code, jumped over; `AllocExpand.outline`)
own-k o (k-label ℓ)   = if ℓ ≡ᵇᴵ skip-label then o-start else o
own-k o (k-jump _)    = o
own-k o (k-branch _)  = o
own-k o k-ret         = o
own-k o (k-start _)   = o
own-k o k-none        = o

own : Owner → AbstractInstr → Owner
own o i = own-k o (kind i)

-- an entry, and the frame it reserves
entry-k : Kind → Bool
entry-k (k-entry _ _) = true
entry-k (k-call _)    = false
entry-k k-clo         = false
entry-k (k-sig _)     = false
entry-k (k-label _)   = false
entry-k (k-jump _)    = false
entry-k (k-branch _)  = false
entry-k k-ret         = false
entry-k (k-start _)   = false
entry-k k-none        = false

frame-k : Kind → ℕ
frame-k (k-entry _ b) = b
frame-k (k-call _)    = 0
frame-k k-clo         = 0
frame-k (k-sig _)     = 0
frame-k (k-label _)   = 0
frame-k (k-jump _)    = 0
frame-k (k-branch _)  = 0
frame-k k-ret         = 0
frame-k (k-start _)   = 0
frame-k k-none        = 0

-- control falls through (to the next instruction) unless this is a jump or a return
falls-k : Kind → Bool
falls-k (k-jump _) = false
falls-k k-ret      = false
{-# CATCHALL #-}
falls-k _          = true

-- what reserves nothing

frame-other : ∀ (k : Kind) → entry-k k ≡ false → frame-k k ≡ 0
frame-other (k-call _)  _ = refl
frame-other k-clo       _ = refl
frame-other (k-sig _)   _ = refl
frame-other (k-label _) _ = refl
frame-other (k-jump _)  _ = refl
frame-other (k-branch _) _ = refl
frame-other k-ret       _ = refl
frame-other (k-start _) _ = refl
frame-other k-none      _ = refl

-- the owner BEFORE `pc` (what `own` turns into the instruction's)
before-from : Owner → AbstractTrace → ℕ → Owner
before-from o []      _       = o
before-from o (i ∷ t) zero    = o
before-from o (i ∷ t) (suc n) = before-from (own o i) t n

-- the owner of the instruction at `pc`, scanning from `o`
owner-from : Owner → AbstractTrace → ℕ → Owner
owner-from o []      _       = o
owner-from o (i ∷ t) zero    = own o i
owner-from o (i ∷ t) (suc n) = owner-from (own o i) t n

owner : AbstractTrace → ℕ → Owner
owner = owner-from o-start

-- (the instruction at `pc`, as the flat machine fetches it)
at : AbstractTrace → ℕ → Maybe AbstractInstr
at []      _       = nothing
at (i ∷ _) zero    = just i
at (_ ∷ t) (suc n) = at t n

-- one instruction on, the owner is the next instruction's `own` of this one's
owner-from-suc : ∀ o (t : AbstractTrace) pc (x : AbstractInstr) → at t (suc pc) ≡ just x
               → owner-from o t (suc pc) ≡ own (owner-from o t pc) x
owner-from-suc o (y ∷ r)        (suc pc) x f   = owner-from-suc (own o y) r pc x f
owner-from-suc o (y ∷ (x′ ∷ r)) zero    x refl = refl

-- (and past the end it stays)
owner-from-end : ∀ o (t : AbstractTrace) pc → at t (suc pc) ≡ nothing → owner-from o t (suc pc) ≡ owner-from o t pc
owner-from-end o []             pc       _ = refl
owner-from-end o (y ∷ r)        (suc pc) f = owner-from-end (own o y) r pc f
owner-from-end o (y ∷ [])       zero     _ = refl
owner-from-end o (y ∷ (x ∷ r))  zero     ()


------------------------------------------------------------------------
-- A TABLE
------------------------------------------------------------------------
record Depths : Set where
  constructor depths
  field
    bnd     : EntryId → Bool    -- a call to it may go unchecked (from elsewhere)
    dep     : EntryId → ℕ       -- its whole depth: frame and past (an upper bound)
    past    : EntryId → ℕ       -- its depth past its frame
    past₀   : ℕ                 -- the start segment's
    clo-chk : Owner → Bool      -- an indirect call it makes is checked
    clo-dep : ℕ                 -- every closure body's whole depth is at most this
    sig-chk : Bool              -- a SigOp is checked (its words in the stretch)
    lown    : LabelId → Owner   -- whose a label is
open Depths

pastO : Depths → Owner → ℕ
pastO T o-start     = past₀ T
pastO T (o-entry e) = past T e

-- A DIRECT CALL IS CHECKED: to its own function, or to one not bounded
chk : Depths → Owner → EntryId → Bool
chk T o g = not (bnd T g) ∨ (o ≡ᵇᴼ o-entry g)

-- WHAT AN INSTRUCTION PUSHES BEYOND ITS FUNCTION'S FRAME (at owner `o`)
cost-k : Depths → Owner → Kind → ℕ
cost-k T o (k-call g)    = if chk T o g then 0 else suc (dep T g)
cost-k T o k-clo         = if clo-chk T o then 0 else suc (clo-dep T)
cost-k T o (k-sig w)     = if sig-chk T then 0 else w
cost-k T o (k-entry _ _) = 0
cost-k T o (k-label _)   = 0
cost-k T o (k-jump _)    = 0
cost-k T o (k-branch _)  = 0
cost-k T o k-ret         = 0
cost-k T o (k-start _)   = 0
cost-k T o k-none        = 0

cost : Depths → Owner → AbstractInstr → ℕ
cost T o i = cost-k T o (kind i)

------------------------------------------------------------------------
-- THE CERTIFICATE: instruction by instruction, at its owner
------------------------------------------------------------------------
thunk-ok : Depths → EntryId → Bool
thunk-ok T (e-thunk ℓ) = dep T (e-thunk ℓ) ≤ᵇ clo-dep T
thunk-ok T (e-fn _)    = true

extra-k : Depths → Owner → Kind → Bool
extra-k T o (k-entry e b) = (b + past T e ≤ᵇ dep T e) ∧ thunk-ok T e
extra-k T o (k-label ℓ)   = lown T ℓ ≡ᵇᴼ o
extra-k T o (k-jump ℓ)    = pastO T (lown T ℓ) ≤ᵇ pastO T o
extra-k T o (k-branch ℓ)  = pastO T (lown T ℓ) ≤ᵇ pastO T o
extra-k T o k-ret         = true
extra-k T o (k-call _)    = true
extra-k T o k-clo         = true
extra-k T o (k-sig _)     = true
extra-k T o (k-start r)   = pastO T o ≤ᵇ r
extra-k T o k-none        = true

ok-at : Depths → Owner → AbstractInstr → Bool
ok-at T o i = (cost T o i ≤ᵇ pastO T o) ∧ extra-k T o (kind i)

-- (and where control falls through, the next function is no deeper: `f`, the last
-- instruction falls through; `o`, its owner)
fall-ok : Depths → Owner → Bool → Owner → Bool
fall-ok T o true  o′ = pastO T o′ ≤ᵇ pastO T o
fall-ok T o false o′ = true

consistent-from : Depths → Owner → Bool → AbstractTrace → Bool
consistent-from T o f []      = true
consistent-from T o f (i ∷ r) = ok-at T (own o i) i ∧ fall-ok T o f (own o i) ∧ consistent-from T (own o i) (falls-k (kind i)) r

consistent? : Depths → AbstractTrace → Bool
consistent? T t = consistent-from T o-start false t

------------------------------------------------------------------------
-- WHAT IT CERTIFIES
------------------------------------------------------------------------
-- (a jump or a branch at `pc`, to `ℓ`)
jumps-k : Kind → LabelId → Set
jumps-k (k-jump m)   ℓ = m ≡ ℓ
jumps-k (k-branch m) ℓ = m ≡ ℓ
{-# CATCHALL #-}
jumps-k _            ℓ = ⊥

jumps-to : Maybe AbstractInstr → LabelId → Set
jumps-to (just i) ℓ = jumps-k (kind i) ℓ
jumps-to nothing  ℓ = ⊥

-- (what jumps is no entry)
jumps-not-entry : ∀ (k : Kind) ℓ → jumps-k k ℓ → entry-k k ≡ false
jumps-not-entry (k-jump _)   ℓ _ = refl
jumps-not-entry (k-branch _) ℓ _ = refl

record Cert (T : Depths) (prog : AbstractTrace) : Set where
  field
    -- every instruction's cost is within its owner's depth
    cost-le  : ∀ pc (i : AbstractInstr) → at prog pc ≡ just i → cost T (owner prog pc) i ≤ pastO T (owner prog pc)
    -- an entry's frame and depth are within its `dep`, a closure body's within `clo-dep`
    dep-le   : ∀ pc e b → at prog pc ≡ just (instr-ctrl (c-entry e b)) → b + past T e ≤ dep T e
    clo-le   : ∀ pc ℓ b → at prog pc ≡ just (instr-ctrl (c-entry (e-thunk ℓ) b)) → dep T (e-thunk ℓ) ≤ clo-dep T
    -- a jump lands no deeper than it left
    jump-le  : ∀ pc j ℓ → jumps-to (at prog pc) ℓ → at prog j ≡ just (instr-ctrl (c-label ℓ))
             → pastO T (owner prog j) ≤ pastO T (owner prog pc)
    -- the start's reserve holds the start's function's depth
    start-le : ∀ pc b r → at prog pc ≡ just (instr-ctrl (c-start b r)) → pastO T (owner prog pc) ≤ r
    -- where control falls through, the next instruction's function is no deeper
    fall-le  : ∀ pc (i x : AbstractInstr) → at prog pc ≡ just i → at prog (suc pc) ≡ just x → falls-k (kind i) ≡ true
             → pastO T (owner prog (suc pc)) ≤ pastO T (owner prog pc)

private
  ∧-l : ∀ {a b : Bool} → (a ∧ b) ≡ true → a ≡ true
  ∧-l {true} _ = refl
  ∧-r : ∀ {a b : Bool} → (a ∧ b) ≡ true → b ≡ true
  ∧-r {true} e = e
  ≤ᵇ-sound : ∀ {m n : ℕ} → (m ≤ᵇ n) ≡ true → m ≤ n
  ≤ᵇ-sound {m} {n} e = ≤ᵇ⇒≤ m n (subst Data.Bool.T (sym e) _)

  -- (the rest of the scan, past one instruction)
  rest-of : ∀ T o f (x : AbstractInstr) (r : AbstractTrace) → consistent-from T o f (x ∷ r) ≡ true
          → consistent-from T (own o x) (falls-k (kind x)) r ≡ true
  rest-of T o f x r c = ∧-r {fall-ok T o f (own o x)} (∧-r {ok-at T (own o x) x} c)

  -- the checks at the instruction at `pc` of `r`, scanning from `o`
  ok-of : ∀ T o f (r : AbstractTrace) → consistent-from T o f r ≡ true → ∀ pc i → at r pc ≡ just i
        → ok-at T (owner-from o r pc) i ≡ true
  ok-of T o f (x ∷ r) c zero    i refl = ∧-l c
  ok-of T o f (x ∷ r) c (suc pc) i f′  = ok-of T (own o x) (falls-k (kind x)) r (rest-of T o f x r c) pc i f′

  -- where control falls through, the next is no deeper
  fall-of : ∀ T o f (r : AbstractTrace) → consistent-from T o f r ≡ true → ∀ pc (i x : AbstractInstr)
          → at r pc ≡ just i → at r (suc pc) ≡ just x → falls-k (kind i) ≡ true
          → pastO T (owner-from o r (suc pc)) ≤ pastO T (owner-from o r pc)
  fall-of T o f (y ∷ r)       c (suc pc) i x′ fi′ fx fi = fall-of T (own o y) (falls-k (kind y)) r (rest-of T o f y r c) pc i x′ fi′ fx fi
  fall-of T o f (y ∷ (x ∷ r)) c zero     i x′ refl refl fi =
    ≤ᵇ-sound (subst (λ b → fall-ok T (own o y) b (own (own o y) x) ≡ true) fi
                    (∧-l (∧-r {ok-at T (own (own o y) x) x} (rest-of T o f y (x ∷ r) c))))

  extra-of : ∀ T o (i : AbstractInstr) → ok-at T o i ≡ true → extra-k T o (kind i) ≡ true
  extra-of T o i e = ∧-r {cost T o i ≤ᵇ pastO T o} e

  -- an entry owns itself
  owner-entry : ∀ o (r : AbstractTrace) pc e b → at r pc ≡ just (instr-ctrl (c-entry e b)) → owner-from o r pc ≡ o-entry e
  owner-entry o (x ∷ r) zero    e b refl = refl
  owner-entry o (x ∷ r) (suc pc) e b f   = owner-entry (own o x) r pc e b f

  -- …and a label is its table owner's, once the label's check holds
  label-owner : ∀ T o ℓ → extra-k T o (k-label ℓ) ≡ true → lown T ℓ ≡ o
  label-owner T o ℓ e = ≡ᵇᴼ-true (lown T ℓ) o e

  jump-k : ∀ T o ℓ (k : Kind) → jumps-k k ℓ → extra-k T o k ≡ true → pastO T (lown T ℓ) ≤ pastO T o
  jump-k T o ℓ (k-jump m)   refl e = ≤ᵇ-sound e
  jump-k T o ℓ (k-branch m) refl e = ≤ᵇ-sound e

  jump-at : ∀ T o f (r : AbstractTrace) pc ℓ → consistent-from T o f r ≡ true → jumps-to (at r pc) ℓ
          → pastO T (lown T ℓ) ≤ pastO T (owner-from o r pc)
  jump-at T o f r pc ℓ c jt = go (at r pc) refl jt
    where
      go : ∀ m → at r pc ≡ m → jumps-to m ℓ → pastO T (lown T ℓ) ≤ pastO T (owner-from o r pc)
      go (just i) e ki = jump-k T (owner-from o r pc) ℓ (kind i) ki (extra-of T _ i (ok-of T o f r c pc i e))

  entry-ok : ∀ T o e b → extra-k T o (k-entry e b) ≡ true → (b + past T e ≤ᵇ dep T e) ≡ true × thunk-ok T e ≡ true
  entry-ok T o e b x = ∧-l x , ∧-r {b + past T e ≤ᵇ dep T e} x

-- A CONSISTENT TABLE IS CERTIFIED
cert-of : ∀ T prog → consistent? T prog ≡ true → Cert T prog
cert-of T prog c = record
  { cost-le  = λ pc i f → ≤ᵇ-sound (∧-l {cost T (owner prog pc) i ≤ᵇ pastO T (owner prog pc)} (ok-of T o-start false prog cs pc i f))
  ; dep-le   = λ pc e b f → ≤ᵇ-sound (proj₁ (entry-ok T (owner prog pc) e b
                 (extra-of T (owner prog pc) (instr-ctrl (c-entry e b)) (ok-of T o-start false prog cs pc (instr-ctrl (c-entry e b)) f))))
  ; clo-le   = λ pc ℓ b f → ≤ᵇ-sound (proj₂ (entry-ok T (owner prog pc) (e-thunk ℓ) b
                 (extra-of T (owner prog pc) (instr-ctrl (c-entry (e-thunk ℓ) b)) (ok-of T o-start false prog cs pc (instr-ctrl (c-entry (e-thunk ℓ) b)) f))))
  ; jump-le  = λ pc j ℓ jt fl →
      subst (λ o → pastO T o ≤ pastO T (owner prog pc))
            (label-owner T (owner prog j) ℓ
               (extra-of T (owner prog j) (instr-ctrl (c-label ℓ)) (ok-of T o-start false prog cs j (instr-ctrl (c-label ℓ)) fl)))
            (jump-at T o-start false prog pc ℓ cs jt)
  ; start-le = λ pc b r f → ≤ᵇ-sound (extra-of T (owner prog pc) (instr-ctrl (c-start b r)) (ok-of T o-start false prog cs pc (instr-ctrl (c-start b r)) f))
  ; fall-le  = λ pc i x f fx fi → fall-of T o-start false prog cs pc i x f fx fi }
  where
    cs = c

------------------------------------------------------------------------
-- THE FALLBACK: every call and SigOp checked, nothing deeper than its frame
------------------------------------------------------------------------
-- (`E`: the largest entry frame)
T₀ : ℕ → Depths
T₀ E = depths (λ _ → false) (λ _ → E) (λ _ → 0) 0 (λ _ → true) E true (λ _ → o-start)

private
  cost₀-k : ∀ E o (k : Kind) → cost-k (T₀ E) o k ≡ 0
  cost₀-k E o (k-call g)    = refl
  cost₀-k E o k-clo         = refl
  cost₀-k E o (k-sig w)     = refl
  cost₀-k E o (k-entry _ _) = refl
  cost₀-k E o (k-label _)   = refl
  cost₀-k E o (k-jump _)    = refl
  cost₀-k E o (k-branch _)  = refl
  cost₀-k E o k-ret         = refl
  cost₀-k E o (k-start _)   = refl
  cost₀-k E o k-none        = refl

  pastO₀ : ∀ E o → pastO (T₀ E) o ≡ 0
  pastO₀ E o-start     = refl
  pastO₀ E (o-entry _) = refl

-- consistent whenever every entry's frame is at most `E`
cert₀ : ∀ E prog → (∀ pc e b → at prog pc ≡ just (instr-ctrl (c-entry e b)) → b ≤ E) → Cert (T₀ E) prog
cert₀ E prog le = record
  { cost-le  = λ pc i f → subst (_≤ pastO (T₀ E) (owner prog pc)) (sym (cost₀-k E (owner prog pc) (kind i))) z≤n
  ; dep-le   = λ pc e b f → subst (_≤ E) (sym (+-identityʳ b)) (le pc e b f)
  ; clo-le   = λ pc ℓ b f → Data.Nat.Properties.≤-refl
  ; jump-le  = λ pc j ℓ jt fl → subst (_≤ pastO (T₀ E) (owner prog pc)) (sym (pastO₀ E (owner prog j))) z≤n
  ; start-le = λ pc b r f → subst (_≤ r) (sym (pastO₀ E (owner prog pc))) z≤n
  ; fall-le  = λ pc i x f fx fi → subst (_≤ pastO (T₀ E) (owner prog pc)) (sym (pastO₀ E (owner prog (suc pc)))) z≤n }
  where import Data.Nat.Properties
