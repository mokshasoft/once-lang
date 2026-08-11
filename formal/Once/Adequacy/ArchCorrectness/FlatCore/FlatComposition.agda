-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition
--
-- THE BLOCK-OFFSET MACHINERY, arch-generic (Plan 0.65 G1b, 2026-08-11).
--
-- Each abstract instruction lowers to a contiguous BLOCK of machine
-- instructions (1 for most, 2 for `alloc-heap`, …), so the machine pc is NOT
-- the flat pc — it is `blk-off prog flat-pc`, the sum of block lengths before
-- it. Everything here is about that arithmetic and about the label scan
-- stepping over blocks; none of it is about an instruction SET.
--
-- WHAT THE ARCH SUPPLIES, and why it is this and not its constructors.
-- x86-64's version of this module spent 22 clauses proving one thing: that a
-- block containing no label is skipped by `find-label-go`. It had to enumerate
-- every `Instr` constructor because `find-label-go`'s catch-all does not reduce
-- on a variable instruction. That enumeration is a fact about an ISA's
-- instruction set — it cannot be generalised away — but it does not belong in
-- the correspondence. So the core asks for the CONSEQUENCE instead:
--
--     is-label? : Instr → Bool
--     skip-law  : is-label? i ≡ false
--               → find-label-go t (i ∷ rest) xi ≡ find-label-go t rest (suc xi)
--
-- and `find-label-go-skip` becomes a three-line induction. Each arch discharges
-- `skip-law` once, next to its own instruction type, where the case split
-- belongs. (`ArithSimCore`'s rule, third application in this plan:
-- parameterise over what holds AFTER the step, never over how it is built.)
--
-- G1b-2 adds the SCAN-PRESERVATION half — the four theorems saying the flat
-- machine's label scans and the machine's own agree modulo `blk-off`. Those
-- proofs used to lean on definitional reduction of a CONCRETE `find-label-go`
-- on a literal `label _ ∷ _`. With the scan a parameter nothing reduces, so
-- each such step is an explicit law:
--
--     mk-label   : Label → Instr
--     label-hit  : (ℓ ≡ᵇᴸ t) ≡ true  → find-label-go t (mk-label ℓ ∷ rest) xi ≡ just xi
--     label-miss : (ℓ ≡ᵇᴸ t) ≡ false → find-label-go t (mk-label ℓ ∷ rest) xi
--                                     ≡ find-label-go t rest (suc xi)
--     headView   : ∀ i → HeadView i
--
-- and the transport that used to be `rewrite ca-eq | meq` is factored ONCE,
-- into the three BLOCK-GRANULARITY laws below (`skip-plain`, `skip-labelled`,
-- `hit-labelled`). That is what stops the surgery from being repeated four
-- times: every clause of every scan theorem is now one of those three laws
-- plus `cons-step`.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace)
open import Once.CCC.Label using (Label; once; thunk; LabelId; _≡ᵇᴸ_; _≡ᵇᴵ_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; length; drop)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Once.Adequacy.ArchCorrectness.FlatCore.HeadView as HV

module Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition
  (FS : FrameSemantics)
  -- the machine's instruction type and the emitter into it
  (Instr : Set)
  (compile-abstract : AbstractInstr → List Instr)
  (compile-trace : AbstractTrace → List Instr)
  (ct-nil  : compile-trace [] ≡ [])
  (ct-cons : ∀ i is → compile-trace (i ∷ is) ≡ compile-abstract i ++ compile-trace is)
  -- the machine's instruction fetch, by its three defining equations (`refl`
  -- at every arch — they all index a list)
  (mfetch      : List Instr → ℕ → Maybe Instr)
  (mfetch-nil  : ∀ n → mfetch [] n ≡ nothing)
  (mfetch-zero : ∀ x xs → mfetch (x ∷ xs) zero ≡ just x)
  (mfetch-suc  : ∀ x xs n → mfetch (x ∷ xs) (suc n) ≡ mfetch xs n)
  -- the ONE view of an instruction this development needs, and the laws that
  -- replace the constructor enumeration: the label scan on the empty program,
  -- on a non-label, and on a label it does / does not match.
  (is-label?     : Instr → Bool)
  (mk-label      : Label → Instr)
  (find-label-go : Label → List Instr → ℕ → Maybe ℕ)
  (find-label-nil : ∀ (t : Label) (xi : ℕ) → find-label-go t [] xi ≡ nothing)
  (skip-law : ∀ (t : Label) (i : Instr) (rest : List Instr) (xi : ℕ)
            → is-label? i ≡ false
            → find-label-go t (i ∷ rest) xi ≡ find-label-go t rest (suc xi))
  -- the two label equations. Everything the old proofs got from
  -- `find-label-go` reducing on a literal `label _ ∷ _` is exactly these.
  (label-hit : ∀ (ℓ t : Label) (rest : List Instr) (xi : ℕ)
             → (ℓ ≡ᵇᴸ t) ≡ true
             → find-label-go t (mk-label ℓ ∷ rest) xi ≡ just xi)
  (label-miss : ∀ (ℓ t : Label) (rest : List Instr) (xi : ℕ)
              → (ℓ ≡ᵇᴸ t) ≡ false
              → find-label-go t (mk-label ℓ ∷ rest) xi ≡ find-label-go t rest (suc xi))
  -- how THIS emitter lowers each abstract instruction, as far as the scans
  -- can see it. 39 clauses at the arch, none of them here.
  (headView : ∀ i → HV.HeadView FS Instr compile-abstract is-label? mk-label i)
  where

open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open import Relation.Binary.PropositionalEquality using (refl; cong; sym; trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Once.CCC.Machine.Flat
open FlatMachine {FS} using (fetch; fl-go; fl-label-match; ft-go; ft-match)
open HV FS Instr compile-abstract is-label? mk-label using (has-label; HeadView; hv-clabel; hv-plain; hv-otherlabel)

------------------------------------------------------------------------
-- Block lengths and the cumulative machine offset of a flat pc.
------------------------------------------------------------------------
blk-len : AbstractInstr → ℕ
blk-len i = length (compile-abstract i)

-- blk-off prog j = number of machine instructions before flat index j.
blk-off : AbstractTrace → ℕ → ℕ
blk-off _        zero    = zero
blk-off []       (suc _) = zero
blk-off (i ∷ is) (suc j) = blk-len i + blk-off is j

------------------------------------------------------------------------
-- A label-free block: the scan steps past it, advancing by its length
-- without matching. THREE LINES, where the arch-specific version was 22
-- clauses — the difference is `skip-law`.
------------------------------------------------------------------------
-- (`has-label` itself lives in `FlatCore.HeadView`, opened above — it is part
-- of the view's vocabulary, and a parameter's type may not mention this
-- module's body.)
find-label-go-skip : ∀ (target : Label) (block rest : List Instr) (xi : ℕ)
  → has-label block ≡ false
  → find-label-go target (block ++ rest) xi ≡ find-label-go target rest (xi + length block)
find-label-go-skip target []       rest xi _  =
  cong (find-label-go target rest) (sym (+-identityʳ xi))
find-label-go-skip target (b ∷ bs) rest xi nl with is-label? b in eq
... | true  = ⊥-elim (true≢false nl)
  where open import Data.Empty using (⊥-elim)
        true≢false : true ≡ false → _
        true≢false ()
... | false =
  trans (skip-law target b (bs ++ rest) xi eq)
        (trans (find-label-go-skip target bs rest (suc xi) nl)
               (cong (find-label-go target rest) (sym (+-suc xi (length bs)))))

------------------------------------------------------------------------
-- `drop` bookkeeping: dropping k flat blocks ⟺ dropping their machine
-- instructions. Pure list arithmetic, no machine anywhere.
------------------------------------------------------------------------
drop-[] : ∀ {A : Set} (n : ℕ) → drop {A = A} n [] ≡ []
drop-[] zero    = refl
drop-[] (suc n) = refl

drop-len-++ : ∀ {A : Set} (xs ys : List A) → drop (length xs) (xs ++ ys) ≡ ys
drop-len-++ []       ys = refl
drop-len-++ (x ∷ xs) ys = drop-len-++ xs ys

drop-+ : ∀ {A : Set} (m n : ℕ) (xs : List A) → drop (m + n) xs ≡ drop n (drop m xs)
drop-+ zero    n xs       = refl
drop-+ (suc m) n []       = sym (drop-[] n)
drop-+ (suc m) n (x ∷ xs) = drop-+ m n xs

drop-compile : ∀ (prog : AbstractTrace) (k : ℕ)
  → drop (blk-off prog k) (compile-trace prog) ≡ compile-trace (drop k prog)
drop-compile prog     zero    = refl
drop-compile []       (suc k) = refl
drop-compile (i ∷ is) (suc k) =
  trans (cong (drop (blk-len i + blk-off is k)) (ct-cons i is))
        (trans (drop-+ (blk-len i) (blk-off is k) (compile-abstract i ++ compile-trace is))
               (trans (cong (drop (blk-off is k)) (drop-len-++ (compile-abstract i) (compile-trace is)))
                      (drop-compile is k)))

------------------------------------------------------------------------
-- Fetching at a block offset.
------------------------------------------------------------------------
fetch-drop : ∀ (xs : List Instr) (n : ℕ) → mfetch xs n ≡ mfetch (drop n xs) zero
fetch-drop []       n       =
  trans (mfetch-nil n)
        (sym (trans (cong (λ ys → mfetch ys zero) (drop-[] n)) (mfetch-nil zero)))
fetch-drop (x ∷ xs) zero    = refl
fetch-drop (x ∷ xs) (suc n) = trans (mfetch-suc x xs n) (fetch-drop xs n)

-- The machine instruction at the block offset = the head of block k.
fetch-at-offset : ∀ (prog : AbstractTrace) (k : ℕ)
  → mfetch (compile-trace prog) (blk-off prog k) ≡ mfetch (compile-trace (drop k prog)) zero
fetch-at-offset prog k =
  trans (fetch-drop (compile-trace prog) (blk-off prog k))
        (cong (λ xs → mfetch xs zero) (drop-compile prog k))

-- pc advance: the machine offset of the NEXT flat pc = current offset + the
-- block length of the instruction at the current pc.
blk-off-suc : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → blk-off prog (suc k) ≡ blk-off prog k + blk-len i
blk-off-suc []       k       i ()
blk-off-suc (j ∷ js) zero    .j refl = +-identityʳ (blk-len j)
blk-off-suc (j ∷ js) (suc k) i  eq   =
  trans (cong (blk-len j +_) (blk-off-suc js k i eq))
        (sym (+-assoc (blk-len j) (blk-off js k) (blk-len i)))

-- drop at a fetched position exposes the instruction as the head.
drop-fetch : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i → drop k prog ≡ i ∷ drop (suc k) prog
drop-fetch []       k       i ()
drop-fetch (j ∷ js) zero    .j refl = refl
drop-fetch (j ∷ js) (suc k) i  eq   = drop-fetch js k i eq

-- The machine instruction at offset n INSIDE block k. One statement for the
-- whole `fetch-block-*` family: the machine program, viewed from a block
-- offset, is the compiled tail of the flat program.
fetch-block-nth : ∀ (prog : AbstractTrace) (k n : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → mfetch (compile-trace prog) (blk-off prog k + n)
    ≡ mfetch (drop n (compile-abstract i ++ compile-trace (drop (suc k) prog))) zero
fetch-block-nth prog k n i ft =
  trans (fetch-drop (compile-trace prog) (blk-off prog k + n))
        (cong (λ xs → mfetch xs zero)
              (trans (drop-+ (blk-off prog k) n (compile-trace prog))
                     (trans (cong (drop n) (drop-compile prog k))
                            (trans (cong (λ p → drop n (compile-trace p)) (drop-fetch prog k i ft))
                                   (cong (drop n) (ct-cons i (drop (suc k) prog)))))))

-- The named offsets the block-steps use. `head` is `nth … 0` modulo `+ 0`;
-- the rest are `nth` outright (2-instruction blocks up to `lea-indexed`'s 6).
fetch-block-head : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → mfetch (compile-trace prog) (blk-off prog k)
    ≡ mfetch (compile-abstract i ++ compile-trace (drop (suc k) prog)) zero
fetch-block-head prog k i ft =
  trans (cong (mfetch (compile-trace prog)) (sym (+-identityʳ (blk-off prog k))))
        (fetch-block-nth prog k zero i ft)

fetch-block-2nd : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → mfetch (compile-trace prog) (blk-off prog k + 1)
    ≡ mfetch (drop 1 (compile-abstract i ++ compile-trace (drop (suc k) prog))) zero
fetch-block-2nd prog k i ft = fetch-block-nth prog k 1 i ft

fetch-block-3rd : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → mfetch (compile-trace prog) (blk-off prog k + 2)
    ≡ mfetch (drop 2 (compile-abstract i ++ compile-trace (drop (suc k) prog))) zero
fetch-block-3rd prog k i ft = fetch-block-nth prog k 2 i ft

fetch-block-4th : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → mfetch (compile-trace prog) (blk-off prog k + 3)
    ≡ mfetch (drop 3 (compile-abstract i ++ compile-trace (drop (suc k) prog))) zero
fetch-block-4th prog k i ft = fetch-block-nth prog k 3 i ft

fetch-block-5th : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → mfetch (compile-trace prog) (blk-off prog k + 4)
    ≡ mfetch (drop 4 (compile-abstract i ++ compile-trace (drop (suc k) prog))) zero
fetch-block-5th prog k i ft = fetch-block-nth prog k 4 i ft

fetch-block-6th : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → mfetch (compile-trace prog) (blk-off prog k + 5)
    ≡ mfetch (drop 5 (compile-abstract i ++ compile-trace (drop (suc k) prog))) zero
fetch-block-6th prog k i ft = fetch-block-nth prog k 5 i ft

------------------------------------------------------------------------
-- THE SCAN LAWS AT BLOCK GRANULARITY (Plan 0.65 G1b-2).
--
-- The arch-specific proofs read `rewrite ca-eq | meq` and then relied on the
-- concrete scan reducing. These three lemmas are that reliance, made explicit
-- and paid for ONCE. Every clause of the four theorems below is one of them.
------------------------------------------------------------------------

-- a label-free block: the scan steps over it, at the cost of its length.
skip-plain : ∀ (t : Label) (i : AbstractInstr) (rest : AbstractTrace) (xi : ℕ)
  → has-label (compile-abstract i) ≡ false
  → find-label-go t (compile-trace (i ∷ rest)) xi
    ≡ find-label-go t (compile-trace rest) (xi + blk-len i)
skip-plain t i rest xi nl =
  trans (cong (λ xs → find-label-go t xs xi) (ct-cons i rest))
        (find-label-go-skip t (compile-abstract i) (compile-trace rest) xi nl)

-- a block that OPENS with a label the target does not match: the label costs
-- one index, the (label-free) tail costs its length. `hv-clabel` is the
-- `tail ≡ []` case of this, `hv-otherlabel` the general one.
skip-labelled : ∀ (t ℓ : Label) (tail : List Instr)
                  (i : AbstractInstr) (rest : AbstractTrace) (xi : ℕ)
  → compile-abstract i ≡ mk-label ℓ ∷ tail
  → has-label tail ≡ false
  → (ℓ ≡ᵇᴸ t) ≡ false
  → find-label-go t (compile-trace (i ∷ rest)) xi
    ≡ find-label-go t (compile-trace rest) (xi + blk-len i)
skip-labelled t ℓ tail i rest xi ca nl ne =
  trans (cong (λ xs → find-label-go t xs xi) (ct-cons i rest))
        (trans (cong (λ xs → find-label-go t (xs ++ compile-trace rest) xi) ca)
               (trans (label-miss ℓ t (tail ++ compile-trace rest) xi ne)
                      (trans (find-label-go-skip t tail (compile-trace rest) (suc xi) nl)
                             (cong (find-label-go t (compile-trace rest)) len-eq))))
  where
    len-eq : suc xi + length tail ≡ xi + blk-len i
    len-eq = trans (sym (+-suc xi (length tail)))
                   (cong (xi +_) (sym (cong length ca)))

-- …and the MATCH: the scan stops at the block's first index.
hit-labelled : ∀ (t ℓ : Label) (tail : List Instr)
                 (i : AbstractInstr) (rest : AbstractTrace) (xi : ℕ)
  → compile-abstract i ≡ mk-label ℓ ∷ tail
  → (ℓ ≡ᵇᴸ t) ≡ true
  → find-label-go t (compile-trace (i ∷ rest)) xi ≡ just xi
hit-labelled t ℓ tail i rest xi ca hit =
  trans (cong (λ xs → find-label-go t xs xi) (ct-cons i rest))
        (trans (cong (λ xs → find-label-go t (xs ++ compile-trace rest) xi) ca)
               (label-hit ℓ t (tail ++ compile-trace rest) xi hit))

-- one skipped block, then the induction hypothesis, re-associated. The shared
-- tail of every non-matching clause below.
cons-step : ∀ (t : Label) (i : AbstractInstr) (rest : AbstractTrace) (xi d : ℕ)
  → find-label-go t (compile-trace (i ∷ rest)) xi
    ≡ find-label-go t (compile-trace rest) (xi + blk-len i)
  → find-label-go t (compile-trace rest) (xi + blk-len i)
    ≡ just ((xi + blk-len i) + blk-off rest d)
  → find-label-go t (compile-trace (i ∷ rest)) xi ≡ just (xi + blk-off (i ∷ rest) (suc d))
cons-step t i rest xi d sk ih =
  trans sk (trans ih (cong just (+-assoc xi (blk-len i) (blk-off rest d))))

just-inj : ∀ {a b : ℕ} → (just a) ≡ (just b) → a ≡ b
just-inj refl = refl

------------------------------------------------------------------------
-- THE CALL SCAN (Plan 0.63). `find-thunk` is `find-label`'s mirror over the
-- OTHER provenance: a closure call resolves its body by scanning for
-- `c-thunk n`, and the emitted call resolves the `thunk n` label. The two
-- agree modulo `blk-off`, by a structural induction over `All HeadView`, with
-- the roles of the two label cases EXCHANGED: `hv-clabel` steps past (a jump
-- label is invisible to the call scan) and `hv-otherlabel` is the match.
--
-- That exchange is exactly what D082 bought. Both "steps past" premises are
-- the catch-all of `_≡ᵇᴸ_` on mismatched provenances, so they are `refl` here
-- — no label-uniqueness argument anywhere.
------------------------------------------------------------------------
find-thunk-pres : ∀ (prog : AbstractTrace) (target : LabelId) (acc xi j : ℕ)
  → All HeadView prog
  → ft-go prog target acc ≡ just j
  → Σ ℕ (λ d → (j ≡ acc + d)
        × (find-label-go (thunk target) (compile-trace prog) xi ≡ just (xi + blk-off prog d)))
find-thunk-pres [] target acc xi j _ ()
find-thunk-pres (i ∷ rest) target acc xi j (hv-plain hl _ ft-p ∷ all-rest) ft-eq =
  let ih = find-thunk-pres rest target (suc acc) (xi + blk-len i) j all-rest
             (trans (sym (ft-p rest target acc)) ft-eq)
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , cons-step (thunk target) i rest xi d'
       (skip-plain (thunk target) i rest xi hl) (proj₂ (proj₂ ih))
-- a JUMP label: the call scan misses it, and so does the compiled scan
-- (`once m ≡ᵇᴸ thunk target` is `_≡ᵇᴸ_`'s catch-all, hence `refl`).
find-thunk-pres (i ∷ rest) target acc xi j (hv-clabel m ca-eq _ ft-p ∷ all-rest) ft-eq =
  let ih = find-thunk-pres rest target (suc acc) (xi + blk-len i) j all-rest
             (trans (sym (ft-p rest target acc)) ft-eq)
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , cons-step (thunk target) i rest xi d'
       (skip-labelled (thunk target) (once m) [] i rest xi ca-eq refl refl) (proj₂ (proj₂ ih))
-- THE MATCH CASE: a `c-thunk m` block. Both scans decide on `m ≡ᵇᴵ target`.
find-thunk-pres (i ∷ rest) target acc xi j (hv-otherlabel m tl ca-eq nl _ ft-m ∷ all-rest) ft-eq
  with m ≡ᵇᴵ target in meq
... | true = 0 , comp1
           , trans (hit-labelled (thunk target) (thunk m) tl i rest xi ca-eq meq)
                   (cong just (sym (+-identityʳ xi)))
  where
    acc≡j : acc ≡ j
    acc≡j = just-inj (trans (sym (cong (λ b → ft-match b rest target acc) meq))
                            (trans (sym (ft-m rest target acc)) ft-eq))
    comp1 : j ≡ acc + 0
    comp1 = trans (sym acc≡j) (sym (+-identityʳ acc))
... | false =
  let ih = find-thunk-pres rest target (suc acc) (xi + blk-len i) j all-rest
             (trans (sym (cong (λ b → ft-match b rest target acc) meq))
                    (trans (sym (ft-m rest target acc)) ft-eq))
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , cons-step (thunk target) i rest xi d'
       (skip-labelled (thunk target) (thunk m) tl i rest xi ca-eq nl meq) (proj₂ (proj₂ ih))

------------------------------------------------------------------------
-- find-label preservation: a flat jump landing at flat index j lands at
-- machine index `blk-off prog j` in the compiled program. The flat target is
-- a `LabelId`; the machine target is `once target` (compiler provenance), so
-- SigOp labels never interfere — definitional via `_≡ᵇᴸ_`.
------------------------------------------------------------------------
find-label-pres : ∀ (prog : AbstractTrace) (target : LabelId) (acc xi j : ℕ)
  → All HeadView prog
  → fl-go prog target acc ≡ just j
  → Σ ℕ (λ d → (j ≡ acc + d)
        × (find-label-go (once target) (compile-trace prog) xi ≡ just (xi + blk-off prog d)))
find-label-pres [] target acc xi j _ ()
find-label-pres (i ∷ rest) target acc xi j (hv-plain hl fl-p _ ∷ all-rest) fl-eq =
  let ih = find-label-pres rest target (suc acc) (xi + blk-len i) j all-rest
             (trans (sym (fl-p rest target acc)) fl-eq)
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , cons-step (once target) i rest xi d'
       (skip-plain (once target) i rest xi hl) (proj₂ (proj₂ ih))
-- a BODY-ENTRY label never matches a `once` target — the catch-all again.
find-label-pres (i ∷ rest) target acc xi j (hv-otherlabel m tl ca-eq nl fl-p _ ∷ all-rest) fl-eq =
  let ih = find-label-pres rest target (suc acc) (xi + blk-len i) j all-rest
             (trans (sym (fl-p rest target acc)) fl-eq)
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , cons-step (once target) i rest xi d'
       (skip-labelled (once target) (thunk m) tl i rest xi ca-eq nl refl) (proj₂ (proj₂ ih))
find-label-pres (i ∷ rest) target acc xi j (hv-clabel m ca-eq fl-c _ ∷ all-rest) fl-eq
  with m ≡ᵇᴵ target in meq
... | true = 0 , comp1
           , trans (hit-labelled (once target) (once m) [] i rest xi ca-eq meq)
                   (cong just (sym (+-identityʳ xi)))
  where
    acc≡j : acc ≡ j
    acc≡j = just-inj (trans (sym (cong (λ b → fl-label-match b rest target acc) meq))
                            (trans (sym (fl-c rest target acc)) fl-eq))
    comp1 : j ≡ acc + 0
    comp1 = trans (sym acc≡j) (sym (+-identityʳ acc))
... | false =
  let ih = find-label-pres rest target (suc acc) (xi + blk-len i) j all-rest
             (trans (sym (cong (λ b → fl-label-match b rest target acc) meq))
                    (trans (sym (fl-c rest target acc)) fl-eq))
      d' = proj₁ ih
  in suc d'
   , trans (proj₁ (proj₂ ih)) (sym (+-suc acc d'))
   , cons-step (once target) i rest xi d'
       (skip-labelled (once target) (once m) [] i rest xi ca-eq refl meq) (proj₂ (proj₂ ih))

-- `headView` is total, so the All-HeadView side condition is always
-- dischargeable — which is what makes the three corollaries below premise-free.
all-headView : ∀ (prog : AbstractTrace) → All HeadView prog
all-headView []         = []
all-headView (i ∷ rest) = headView i ∷ all-headView rest

-- find-label preservation, side condition discharged.
find-label-corr : ∀ (prog : AbstractTrace) (target : LabelId) (xi j : ℕ)
  → fl-go prog target 0 ≡ just j
  → find-label-go (once target) (compile-trace prog) xi ≡ just (xi + blk-off prog j)
find-label-corr prog target xi j fl-eq
  with find-label-pres prog target 0 xi j (all-headView prog) fl-eq
... | (d , j≡0+d , m-eq) rewrite j≡0+d = m-eq

-- …and the CALL's, the same statement over the `thunk` provenance: the flat
-- machine's `find-thunk` and the emitted call's label resolution land on the
-- same block. This is what `instr-call-closure`'s block-step consumes.
find-thunk-corr : ∀ (prog : AbstractTrace) (target : LabelId) (xi j : ℕ)
  → ft-go prog target 0 ≡ just j
  → find-label-go (thunk target) (compile-trace prog) xi ≡ just (xi + blk-off prog j)
find-thunk-corr prog target xi j ft-eq
  with find-thunk-pres prog target 0 xi j (all-headView prog) ft-eq
... | (d , j≡0+d , m-eq) rewrite j≡0+d = m-eq

------------------------------------------------------------------------
-- find-label, NEGATIVE direction: if the flat scan finds no `c-label m`,
-- the compiled scan finds no `once m` label either.
--
-- The invariant this needs is PROVENANCE, not disjointness: the emitter emits
-- a label only for `instr-ctrl (c-label m)` / `c-thunk m`, and then exactly
-- that provenance — which is what `HeadView` enumerates. Label UNIQUENESS is
-- never needed: both scanners return their first match, so duplicates align
-- rather than conflict.
------------------------------------------------------------------------
find-label-none-go : ∀ (prog : AbstractTrace) (target : LabelId) (acc xi : ℕ)
  → All HeadView prog
  → fl-go prog target acc ≡ nothing
  → find-label-go (once target) (compile-trace prog) xi ≡ nothing
find-label-none-go [] target acc xi _ _ =
  trans (cong (λ xs → find-label-go (once target) xs xi) ct-nil)
        (find-label-nil (once target) xi)
find-label-none-go (i ∷ rest) target acc xi (hv-plain nl fl-p _ ∷ all-rest) fl-eq =
  trans (skip-plain (once target) i rest xi nl)
        (find-label-none-go rest target (suc acc) (xi + blk-len i) all-rest
                            (trans (sym (fl-p rest target acc)) fl-eq))
find-label-none-go (i ∷ rest) target acc xi (hv-otherlabel m tl ca-eq nl fl-p _ ∷ all-rest) fl-eq =
  trans (skip-labelled (once target) (thunk m) tl i rest xi ca-eq nl refl)
        (find-label-none-go rest target (suc acc) (xi + blk-len i) all-rest
                            (trans (sym (fl-p rest target acc)) fl-eq))
find-label-none-go (i ∷ rest) target acc xi (hv-clabel m ca-eq fl-c _ ∷ all-rest) fl-eq
  with m ≡ᵇᴵ target in meq
-- a MATCH contradicts the flat scan's `nothing`
... | true  = absurd (trans (sym fl-eq)
                (trans (fl-c rest target acc)
                       (cong (λ b → fl-label-match b rest target acc) meq)))
  where absurd : ∀ {A : Set} {x : A} → (nothing ≡ just x)
               → find-label-go (once target) (compile-trace (i ∷ rest)) xi ≡ nothing
        absurd ()
... | false =
  trans (skip-labelled (once target) (once m) [] i rest xi ca-eq refl meq)
        (find-label-none-go rest target (suc acc) (xi + blk-len i) all-rest
                            (trans (sym (cong (λ b → fl-label-match b rest target acc) meq))
                                   (trans (sym (fl-c rest target acc)) fl-eq)))

find-label-none-corr : ∀ (prog : AbstractTrace) (target : LabelId)
  → fl-go prog target 0 ≡ nothing
  → find-label-go (once target) (compile-trace prog) 0 ≡ nothing
find-label-none-corr prog target fl-eq =
  find-label-none-go prog target 0 0 (all-headView prog) fl-eq
