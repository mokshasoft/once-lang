-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandPc — where the expansion puts things (D468, 3c3b).
--
-- The pc half of `AllocExpand`'s simulation: `off s P n` is where the primitive
-- program's instruction `n` begins in the expanded one; each instruction's
-- expansion is fetched there (`fetch-exp`); a jump label or a call entry of the
-- primitive program is found at the mapped pc (`fl-exp`, `ft-exp`), since the
-- expansion's own labels have a non-empty path (an image label's is empty) and
-- it adds no entry.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandPc {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-assoc; +-comm; +-identityʳ)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (dec-false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Once.CCC.Label using (LabelId; mkLabelId; module LabelId; _≟ᴵ_; _≡ᵇᴵ_; EntryId; _≡ᵇᴱ_)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (fetch; fl-go; fl-at; fl-label-match; label-of?; ft-go; ft-at; ft-match; entry-of?
                            ; fetch-++-left; fetch-++-right; fl-go-++-miss; ft-go-++-miss)
open import Once.CCC.Codegen.AllocExpand

module _ (C : Classes) where

  ------------------------------------------------------------------------
  -- The pc map
  ------------------------------------------------------------------------

  off : ℕ → AbstractTrace → ℕ → ℕ
  off s []      n       = n
  off s (i ∷ P) zero    = 0
  off s (i ∷ P) (suc n) = length (expand-at C s i) + off (suc s) P n

  -- an instruction's expansion, fetched at its mapped pc
  fetch-exp : ∀ s P n i → fetch P n ≡ just i
            → ∀ k j → fetch (expand-at C (n + s) i) k ≡ just j → fetch (expand-from C s P) (off s P n + k) ≡ just j
  fetch-exp s []      n       i () k j _
  fetch-exp s (x ∷ P) zero    i refl k j e = fetch-++-left (expand-at C s x) (expand-from C (suc s) P) k j e
  fetch-exp s (x ∷ P) (suc n) i f  k j e =
    trans (cong (fetch (expand-at C s x ++ expand-from C (suc s) P)) (+-assoc (length (expand-at C s x)) (off (suc s) P n) k))
      (trans (fetch-++-right (expand-at C s x) (expand-from C (suc s) P) (off (suc s) P n + k))
             (fetch-exp (suc s) P n i f k j (trans (cong (λ z → fetch (expand-at C z i) k) (+-suc n s)) e)))

  -- the next instruction begins past this one's expansion
  off-suc : ∀ s P n i → fetch P n ≡ just i → off s P (suc n) ≡ off s P n + length (expand-at C (n + s) i)
  off-suc s []      n       i ()
  off-suc s (x ∷ P) zero    i refl = trans (cong (length (expand-at C s x) +_) (off-zero (suc s) P)) (+-identityʳ _)
    where
      off-zero : ∀ s′ P′ → off s′ P′ zero ≡ 0
      off-zero s′ []       = refl
      off-zero s′ (_ ∷ _)  = refl
  off-suc s (x ∷ P) (suc n) i f =
    trans (cong (length (expand-at C s x) +_) (off-suc (suc s) P n i f))
      (trans (sym (+-assoc (length (expand-at C s x)) (off (suc s) P n) _))
             (cong (λ z → (length (expand-at C s x) + off (suc s) P n) + length (expand-at C z i)) (+-suc n s)))

  ------------------------------------------------------------------------
  -- Which instructions the expansion rewrites (enumerated: `expand-at`'s
  -- catch-all does not reduce on a variable instruction)
  ------------------------------------------------------------------------

  data ExpView (s : ℕ) : AbstractInstr → Set where
    ev-alloc : ∀ k → ExpView s (instr-alloc-heap k)
    ev-free  : ∀ k → ExpView s (instr-free-heap k)
    ev-start : ∀ b → ExpView s (instr-ctrl (c-start b))
    ev-same  : ∀ {i} → expand-at C s i ≡ i ∷ [] → ExpView s i

  exp-view : ∀ s i → ExpView s i
  exp-view s mov-to-output              = ev-same refl
  exp-view s mov-to-input               = ev-same refl
  exp-view s load-indirect              = ev-same refl
  exp-view s load-indirect-suc          = ev-same refl
  exp-view s (load-from-slot x)         = ev-same refl
  exp-view s (store-at-slot x)          = ev-same refl
  exp-view s store-indirect             = ev-same refl
  exp-view s store-indirect-suc         = ev-same refl
  exp-view s (lea-slot x)               = ev-same refl
  exp-view s (restore-input x)          = ev-same refl
  exp-view s (instr-alloc-stack x)      = ev-same refl
  exp-view s (instr-dealloc-stack x)    = ev-same refl
  exp-view s (instr-reclaim-to x)       = ev-same refl
  exp-view s (instr-push-frame x)       = ev-same refl
  exp-view s instr-pop-frame            = ev-same refl
  exp-view s instr-call-closure         = ev-same refl
  exp-view s (worklist-init x)          = ev-same refl
  exp-view s (worklist-push x)          = ev-same refl
  exp-view s (worklist-pop x)           = ev-same refl
  exp-view s (worklist-check x)         = ev-same refl
  exp-view s (instr-sigop si)           = ev-same refl
  exp-view s (instr-load-const p v)     = ev-same refl
  exp-view s (instr-load-code-addr l)   = ev-same refl
  exp-view s instr-save-closure-reg     = ev-same refl
  exp-view s (instr-load-tag-lit n)     = ev-same refl
  exp-view s (instr-alloc-heap k)       = ev-alloc k
  exp-view s (instr-reg-op op)          = ev-same refl
  exp-view s (instr-free-heap k)        = ev-free k
  exp-view s (instr-room k)             = ev-same refl
  exp-view s (load-at k)                = ev-same refl
  exp-view s (store-at k)               = ev-same refl
  exp-view s (addr-at k)                = ev-same refl
  exp-view s (load-rec k)               = ev-same refl
  exp-view s (store-rec k)              = ev-same refl
  exp-view s (instr-ctrl (c-label l))   = ev-same refl
  exp-view s (instr-ctrl (c-jmp l))     = ev-same refl
  exp-view s (instr-ctrl (c-branch-tag-zero l)) = ev-same refl
  exp-view s (instr-ctrl (c-entry e b)) = ev-same refl
  exp-view s (instr-ctrl (c-call-fn f)) = ev-same refl
  exp-view s (instr-ctrl (c-ret b))     = ev-same refl
  exp-view s (instr-ctrl (c-start b))   = ev-start b
  exp-view s (instr-ctrl c-leave)       = ev-same refl

  ------------------------------------------------------------------------
  -- The label scan: an image label (empty path) is found at the mapped pc
  ------------------------------------------------------------------------

  private
    mm-cong : ∀ {f g : ℕ → ℕ} (m : Maybe ℕ) → (∀ p → f p ≡ g p) → mmap f m ≡ mmap g m
    mm-cong (just p) h = cong just (h p)
    mm-cong nothing  h = refl

    mm-∘ : ∀ (f g : ℕ → ℕ) (m : Maybe ℕ) → mmap f (mmap g m) ≡ mmap (λ p → f (g p)) m
    mm-∘ f g (just p) = refl
    mm-∘ f g nothing  = refl

  -- a scan from one further on finds one further on
  fl-shift  : ∀ P L d → fl-go P L (suc d) ≡ mmap suc (fl-go P L d)
  fl-shiftᵃ : ∀ mo P L d → fl-at mo P L (suc d) ≡ mmap suc (fl-at mo P L d)
  fl-shiftᵐ : ∀ b P L d → fl-label-match b P L (suc d) ≡ mmap suc (fl-label-match b P L d)
  fl-shift []      L d = refl
  fl-shift (x ∷ P) L d = fl-shiftᵃ (label-of? x) P L d
  fl-shiftᵃ (just m) P L d = fl-shiftᵐ (m ≡ᵇᴵ L) P L d
  fl-shiftᵃ nothing  P L d = fl-shift P L (suc d)
  fl-shiftᵐ true  P L d = refl
  fl-shiftᵐ false P L d = fl-shift P L (suc d)

  -- a trace none of whose labels is `L` misses it
  record NoL (L : LabelId) (x : AbstractInstr) : Set where
    constructor nol
    field nol-f : ∀ m → label-of? x ≡ just m → (m ≡ᵇᴵ L) ≡ false
  open NoL

  infixr 5 _∷ᴺ_
  data AllNoL (L : LabelId) : AbstractTrace → Set where
    []ᴺ  : AllNoL L []
    _∷ᴺ_ : ∀ {x xs} → NoL L x → AllNoL L xs → AllNoL L (x ∷ xs)

  nol-++ : ∀ {L xs ys} → AllNoL L xs → AllNoL L ys → AllNoL L (xs ++ ys)
  nol-++ []ᴺ        b = b
  nol-++ (p ∷ᴺ ps) b = p ∷ᴺ nol-++ ps b

  nol-go  : ∀ {L} xs i → AllNoL L xs → fl-go xs L i ≡ nothing
  nol-at  : ∀ {L} x xs i mo → label-of? x ≡ mo → NoL L x → AllNoL L xs → fl-at mo xs L i ≡ nothing
  nol-mt  : ∀ {L} xs i b → b ≡ false → AllNoL L xs → fl-label-match b xs L i ≡ nothing
  nol-go []       i []ᴺ        = refl
  nol-go (x ∷ xs) i (p ∷ᴺ ps) = nol-at x xs i (label-of? x) refl p ps
  nol-at x xs i (just m) e p ps = nol-mt xs i (m ≡ᵇᴵ _) (nol-f p m e) ps
  nol-at x xs i nothing  e p ps = nol-go xs (suc i) ps
  nol-mt xs i .false refl ps = nol-go xs (suc i) ps

  -- the expansion's labels are none of an image's
  lb-false : ∀ site n L → LabelId.path L ≡ [] → (mkLabelId alloc-owner (site ∷ []) n ≡ᵇᴵ L) ≡ false
  lb-false site n L pe = dec-false (mkLabelId alloc-owner (site ∷ []) n ≟ᴵ L) (λ eq → nil≢ (trans (sym pe) (sym (cong LabelId.path eq))))
    where
      nil≢ : ¬ ([] ≡ site ∷ [])
      nil≢ ()

  plain : ∀ {L x} → label-of? x ≡ nothing → NoL L x
  plain {L} e = nol (λ m e′ → absurd m (trans (sym e) e′))
    where
      absurd : ∀ m → nothing ≡ just m → (m ≡ᵇᴵ L) ≡ false
      absurd m ()

  heads-nol : ∀ {L} c → AllNoL L (heads C c)
  heads-nol zero    = []ᴺ
  heads-nol (suc c) = plain refl ∷ᴺ heads-nol c

  alloc-nol : ∀ site k L → LabelId.path L ≡ [] → AllNoL L (alloc-code C site k)
  alloc-nol site k L pe =
      plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl
    ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl
    ∷ᴺ lbl 0 ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ lbl 1 ∷ᴺ []ᴺ
    where
      lbl : ∀ n → NoL L (instr-ctrl (c-label (mkLabelId alloc-owner (site ∷ []) n)))
      lbl n = nol (λ { .(mkLabelId alloc-owner (site ∷ []) n) refl → lb-false site n L pe })

  free-nol : ∀ k L → AllNoL L (free-code C k)
  free-nol k L = plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ []ᴺ

  start-nol : ∀ L → AllNoL L (setup C)
  start-nol L = plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl
              ∷ᴺ nol-++ (heads-nol (count C))
                   (plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ plain refl ∷ᴺ []ᴺ)

  -- ★ the scan of the expanded program, by the primitive one's
  fl-exp : ∀ s P L i → LabelId.path L ≡ [] → fl-go (expand-from C s P) L i ≡ mmap (λ p → i + off s P p) (fl-go P L 0)
  fl-exp s []      L i pe = refl
  fl-exp s (x ∷ P) L i pe = fl-cons (exp-view s x)
    where
      E′ = expand-from C (suc s) P
      IH : ∀ i′ → fl-go E′ L i′ ≡ mmap (λ p → i′ + off (suc s) P p) (fl-go P L 0)
      IH i′ = fl-exp (suc s) P L i′ pe
      -- past an expansion with no label `L`, by its length
      past : ∀ xs → AllNoL L xs → length (expand-at C s x) ≡ length xs → label-of? x ≡ nothing
           → fl-go (xs ++ E′) L i ≡ mmap (λ p → i + off s (x ∷ P) p) (fl-go (x ∷ P) L 0)
      past xs nl le lx =
        trans (fl-go-++-miss xs E′ L i (nol-go xs i nl))
          (trans (IH (length xs + i))
            (trans (mm-cong (fl-go P L 0) (λ p → trans (cong (_+ off (suc s) P p) (trans (+-comm (length xs) i) (cong (i +_) (sym le))))
                                                   (+-assoc i (length (expand-at C s x)) _)))
              (trans (sym (mm-∘ (λ p → i + off s (x ∷ P) p) suc (fl-go P L 0)))
                (trans (cong (mmap (λ p → i + off s (x ∷ P) p)) (sym (fl-shift P L 0)))
                       (cong (λ mo → mmap (λ p → i + off s (x ∷ P) p) (fl-at mo P L 0)) (sym lx))))))
      -- one instruction kept
      kept-at : ∀ mo → label-of? x ≡ mo → expand-at C s x ≡ x ∷ []
              → fl-at mo E′ L i ≡ mmap (λ p → i + off s (x ∷ P) p) (fl-at mo P L 0)
      kept-mt : ∀ b → expand-at C s x ≡ x ∷ []
              → fl-label-match b E′ L i ≡ mmap (λ p → i + off s (x ∷ P) p) (fl-label-match b P L 0)
      kept-at (just m) _ ex = kept-mt (m ≡ᵇᴵ L) ex
      kept-at nothing  _ ex = after ex
        where
          after : expand-at C s x ≡ x ∷ [] → fl-go E′ L (suc i) ≡ mmap (λ p → i + off s (x ∷ P) p) (fl-go P L 1)
          after ex′ =
            trans (IH (suc i))
              (trans (mm-cong (fl-go P L 0) (λ p → trans (cong (_+ off (suc s) P p) (+-comm 1 i))
                                                     (trans (+-assoc i 1 _) (cong (λ z → i + (z + off (suc s) P p)) (sym (cong length ex′))))))
                (trans (sym (mm-∘ (λ p → i + off s (x ∷ P) p) suc (fl-go P L 0)))
                       (cong (mmap (λ p → i + off s (x ∷ P) p)) (sym (fl-shift P L 0)))))
      kept-mt true  ex = cong just (sym (+-identityʳ i))
      kept-mt false ex =
        trans (IH (suc i))
          (trans (mm-cong (fl-go P L 0) (λ p → trans (cong (_+ off (suc s) P p) (+-comm 1 i))
                                                 (trans (+-assoc i 1 _) (cong (λ z → i + (z + off (suc s) P p)) (sym (cong length ex))))))
            (trans (sym (mm-∘ (λ p → i + off s (x ∷ P) p) suc (fl-go P L 0)))
                   (cong (mmap (λ p → i + off s (x ∷ P) p)) (sym (fl-shift P L 0)))))
      fl-cons : ExpView s x → fl-go (expand-at C s x ++ E′) L i ≡ mmap (λ p → i + off s (x ∷ P) p) (fl-go (x ∷ P) L 0)
      fl-cons (ev-alloc k) = past (alloc-code C s k) (alloc-nol s k L pe) refl refl
      fl-cons (ev-free k)  = past (free-code C k) (free-nol k L) refl refl
      fl-cons (ev-start b) = past (instr-ctrl (c-start b) ∷ setup C) (plain refl ∷ᴺ start-nol L) refl refl
      fl-cons (ev-same ex) =
        trans (cong (λ xs → fl-go (xs ++ E′) L i) ex) (kept-at (label-of? x) refl ex)

  ------------------------------------------------------------------------
  -- The entry scan: the expansion adds no entry, so every entry is found at
  -- its mapped pc
  ------------------------------------------------------------------------

  ft-shift  : ∀ P E d → ft-go P E (suc d) ≡ mmap suc (ft-go P E d)
  ft-shiftᵃ : ∀ mo P E d → ft-at mo P E (suc d) ≡ mmap suc (ft-at mo P E d)
  ft-shiftᵐ : ∀ b P E d → ft-match b P E (suc d) ≡ mmap suc (ft-match b P E d)
  ft-shift []      E d = refl
  ft-shift (x ∷ P) E d = ft-shiftᵃ (entry-of? x) P E d
  ft-shiftᵃ (just m) P E d = ft-shiftᵐ (m ≡ᵇᴱ E) P E d
  ft-shiftᵃ nothing  P E d = ft-shift P E (suc d)
  ft-shiftᵐ true  P E d = refl
  ft-shiftᵐ false P E d = ft-shift P E (suc d)

  record NoE (x : AbstractInstr) : Set where
    constructor noe
    field noe-f : entry-of? x ≡ nothing
  open NoE

  infixr 5 _∷ᴱ_
  data AllNoE : AbstractTrace → Set where
    []ᴱ  : AllNoE []
    _∷ᴱ_ : ∀ {x xs} → NoE x → AllNoE xs → AllNoE (x ∷ xs)

  noe-++ : ∀ {xs ys} → AllNoE xs → AllNoE ys → AllNoE (xs ++ ys)
  noe-++ []ᴱ        b = b
  noe-++ (p ∷ᴱ ps) b = p ∷ᴱ noe-++ ps b

  noe-go : ∀ {E} xs i → AllNoE xs → ft-go xs E i ≡ nothing
  noe-at : ∀ {E} x xs i mo → entry-of? x ≡ mo → NoE x → AllNoE xs → ft-at mo xs E i ≡ nothing
  noe-go []       i []ᴱ        = refl
  noe-go (x ∷ xs) i (p ∷ᴱ ps) = noe-at x xs i (entry-of? x) refl p ps
  noe-at x xs i (just m) e p ps = absurd (trans (sym e) (noe-f p))
    where
      absurd : just m ≡ nothing → _
      absurd ()
  noe-at x xs i nothing  e p ps = noe-go xs (suc i) ps

  heads-noe : ∀ c → AllNoE (heads C c)
  heads-noe zero    = []ᴱ
  heads-noe (suc c) = noe refl ∷ᴱ heads-noe c

  alloc-noe : ∀ site k → AllNoE (alloc-code C site k)
  alloc-noe site k =
      noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl
    ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl
    ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ []ᴱ

  free-noe : ∀ k → AllNoE (free-code C k)
  free-noe k = noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ []ᴱ

  start-noe : AllNoE (setup C)
  start-noe = noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl
            ∷ᴱ noe-++ (heads-noe (count C))
                 (noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ noe refl ∷ᴱ []ᴱ)

  -- ★ the entry scan of the expanded program, by the primitive one's
  ft-exp : ∀ s P E i → ft-go (expand-from C s P) E i ≡ mmap (λ p → i + off s P p) (ft-go P E 0)
  ft-exp s []      E i = refl
  ft-exp s (x ∷ P) E i = ft-cons (exp-view s x)
    where
      E′ = expand-from C (suc s) P
      IH : ∀ i′ → ft-go E′ E i′ ≡ mmap (λ p → i′ + off (suc s) P p) (ft-go P E 0)
      IH i′ = ft-exp (suc s) P E i′
      shifted : ∀ n → length (expand-at C s x) ≡ n
              → ft-go E′ E (n + i) ≡ mmap (λ p → i + off s (x ∷ P) p) (ft-go P E 1)
      shifted n le =
        trans (IH (n + i))
          (trans (mm-cong (ft-go P E 0) (λ p → trans (cong (_+ off (suc s) P p) (trans (+-comm n i) (cong (i +_) (sym le))))
                                                 (+-assoc i (length (expand-at C s x)) _)))
            (trans (sym (mm-∘ (λ p → i + off s (x ∷ P) p) suc (ft-go P E 0)))
                   (cong (mmap (λ p → i + off s (x ∷ P) p)) (sym (ft-shift P E 0)))))
      past : ∀ xs → AllNoE xs → length (expand-at C s x) ≡ length xs → entry-of? x ≡ nothing
           → ft-go (xs ++ E′) E i ≡ mmap (λ p → i + off s (x ∷ P) p) (ft-go (x ∷ P) E 0)
      past xs ne le ex =
        trans (ft-go-++-miss xs E′ E i (noe-go xs i ne))
          (trans (shifted (length xs) le)
                 (cong (λ mo → mmap (λ p → i + off s (x ∷ P) p) (ft-at mo P E 0)) (sym ex)))
      kept-at : ∀ mo → expand-at C s x ≡ x ∷ []
              → ft-at mo E′ E i ≡ mmap (λ p → i + off s (x ∷ P) p) (ft-at mo P E 0)
      kept-mt : ∀ b → expand-at C s x ≡ x ∷ []
              → ft-match b E′ E i ≡ mmap (λ p → i + off s (x ∷ P) p) (ft-match b P E 0)
      kept-at (just m) ex = kept-mt (m ≡ᵇᴱ E) ex
      kept-at nothing  ex = shifted 1 (cong length ex)
      kept-mt true  ex = cong just (sym (+-identityʳ i))
      kept-mt false ex = shifted 1 (cong length ex)
      ft-cons : ExpView s x → ft-go (expand-at C s x ++ E′) E i ≡ mmap (λ p → i + off s (x ∷ P) p) (ft-go (x ∷ P) E 0)
      ft-cons (ev-alloc k) = past (alloc-code C s k) (alloc-noe s k) refl refl
      ft-cons (ev-free k)  = past (free-code C k) (free-noe k) refl refl
      ft-cons (ev-start b) = past (instr-ctrl (c-start b) ∷ setup C) (noe refl ∷ᴱ start-noe) refl refl
      ft-cons (ev-same ex) = trans (cong (λ xs → ft-go (xs ++ E′) E i) ex) (kept-at (entry-of? x) ex)
