-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.SigOp.DigestInjective  (plan 0.123 α′ (f1), D389)
--
-- ONE DIGEST IS ONE BLOCK. A block's symbol is its digest (`block-digest`:
-- the input shape, then the tree), and the file's table keeps one body per
-- symbol (`dedup-blocks`), so which body a SigOp's call runs is "the block
-- whose digest is this one" — a function only if equal digests mean equal
-- blocks. D389 is what made that true (the shape was missing).
--
-- The proof reads the digest as characters: every rendering is prefix-free —
-- a tree node is one letter and its children, a path ends in `Z`, a number in
-- `_` (which no digit is) — so a rendering followed by anything determines
-- both the thing rendered and the rest.
------------------------------------------------------------------------

module Once.Arith.SigOp.DigestInjective where

open import Data.Bool using (true)
open import Data.Char using (Char; isDigit)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ∷-injectiveˡ; ∷-injectiveʳ; ++-identityʳ; ++-cancelˡ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show.Properties using (charsInBase-injective)
open import Data.Nat.Show using (charsInBase)
open import Data.List using (length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Postulates using (toList-++)
open import Once.Target.Symbol using (showNat; once-symbol-own; mangle-component)
open import Once.Target.SymbolInjective
  using (toList-showNat; charsInBase-all-digits; zencL; zencL-inj; mangL; toList-mangle; HeadNotDigit; digit-prefix-unique)
open import Once.Arith.CmpOp using (CmpOp; c-lt; c-le; c-gt; c-ge; c-eq; c-ne)
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.Shape
  using (InputShape; shape-unit; shape-int; shape-float; shape-pair; InputPath; Side; Fst; Snd
        ; Path; here-int; here-flt; go-fst; go-snd; ⌊_⌋ᴾ)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f; acmp)
open import Once.Spec.Float.Decimal using (Decimal; _/10^_)
open import Once.Arith.SigOp.Block
  using (show-shape; show-path; show-zlit; show-dlit; show-arith-ir; block-digest; block-name)

------------------------------------------------------------------------
-- The renderings, as characters.
------------------------------------------------------------------------

shape-cs : InputShape → List Char
shape-cs shape-unit       = 'u' ∷ []
shape-cs shape-int        = 'i' ∷ []
shape-cs shape-float      = 'f' ∷ []
shape-cs (shape-pair a b) = 'p' ∷ (shape-cs a ++ shape-cs b)

path-cs : InputPath → List Char
path-cs []        = 'Z' ∷ []
path-cs (Fst ∷ p) = 'F' ∷ path-cs p
path-cs (Snd ∷ p) = 'S' ∷ path-cs p

-- a number and its terminator
nat-cs : ℕ → List Char
nat-cs n = toList (showNat n) ++ ('_' ∷ [])

zlit-cs : ℤ → List Char
zlit-cs (+ n)      = nat-cs n
zlit-cs (-[1+ n ]) = 'n' ∷ nat-cs (suc n)

dlit-cs : Decimal → List Char
dlit-cs (s /10^ e) = zlit-cs s ++ nat-cs e

cmp-c : CmpOp → Char
cmp-c c-lt = '0'
cmp-c c-le = '1'
cmp-c c-gt = '2'
cmp-c c-ge = '3'
cmp-c c-eq = '4'
cmp-c c-ne = '5'

tree-cs : ∀ {sh n} → MArithIR sh n → List Char
tree-cs (alit z)                 = 'L' ∷ zlit-cs z
tree-cs (aflit d)                = 'F' ∷ dlit-cs d
tree-cs {n = NInt}   (ainput p)  = 'I' ∷ path-cs ⌊ p ⌋ᴾ
tree-cs {n = NFloat} (ainput p)  = 'J' ∷ path-cs ⌊ p ⌋ᴾ
tree-cs (aadd a b)               = 'A' ∷ (tree-cs a ++ tree-cs b)
tree-cs (asub a b)               = 'B' ∷ (tree-cs a ++ tree-cs b)
tree-cs (amul a b)               = 'M' ∷ (tree-cs a ++ tree-cs b)
tree-cs (adiv a b)               = 'D' ∷ (tree-cs a ++ tree-cs b)
tree-cs (amod a b)               = 'R' ∷ (tree-cs a ++ tree-cs b)
tree-cs (aneg a)                 = 'G' ∷ tree-cs a
tree-cs (ai2f a)                 = 'C' ∷ tree-cs a
tree-cs (acmp o a b)             = 'K' ∷ cmp-c o ∷ (tree-cs a ++ tree-cs b)

------------------------------------------------------------------------
-- …are the strings' characters.
------------------------------------------------------------------------

private
  br1 : ∀ (k x : String) {xs} → toList x ≡ xs → toList (k ++ˢ x) ≡ toList k ++ xs
  br1 k x ex = trans (toList-++ k x) (cong (toList k ++_) ex)

  br2 : ∀ (k x y : String) {xs ys} → toList x ≡ xs → toList y ≡ ys
      → toList (k ++ˢ (x ++ˢ y)) ≡ toList k ++ (xs ++ ys)
  br2 k x y ex ey = br1 k (x ++ˢ y) (trans (toList-++ x y) (cong₂ _++_ ex ey))

shape-br : ∀ sh → toList (show-shape sh) ≡ shape-cs sh
shape-br shape-unit       = refl
shape-br shape-int        = refl
shape-br shape-float      = refl
shape-br (shape-pair a b) = br2 "p" (show-shape a) (show-shape b) (shape-br a) (shape-br b)

path-br : ∀ p → toList (show-path p) ≡ path-cs p
path-br []        = refl
path-br (Fst ∷ p) = br1 "F" (show-path p) (path-br p)
path-br (Snd ∷ p) = br1 "S" (show-path p) (path-br p)

nat-br : ∀ n → toList (showNat n ++ˢ "_") ≡ nat-cs n
nat-br n = toList-++ (showNat n) "_"

zlit-br : ∀ z → toList (show-zlit z) ≡ zlit-cs z
zlit-br (+ n)      = nat-br n
zlit-br (-[1+ n ]) = br1 "n" (showNat (suc n) ++ˢ "_") (nat-br (suc n))

dlit-br : ∀ d → toList (show-dlit d) ≡ dlit-cs d
dlit-br (s /10^ e) = trans (toList-++ (show-zlit s) _) (cong₂ _++_ (zlit-br s) (nat-br e))

tree-br : ∀ {sh n} (e : MArithIR sh n) → toList (show-arith-ir e) ≡ tree-cs e
tree-br (alit z)                = br1 "L" (show-zlit z) (zlit-br z)
tree-br (aflit d)               = br1 "F" (show-dlit d) (dlit-br d)
tree-br {n = NInt}   (ainput p) = br1 "I" (show-path ⌊ p ⌋ᴾ) (path-br ⌊ p ⌋ᴾ)
tree-br {n = NFloat} (ainput p) = br1 "J" (show-path ⌊ p ⌋ᴾ) (path-br ⌊ p ⌋ᴾ)
tree-br (aadd a b)              = br2 "A" (show-arith-ir a) (show-arith-ir b) (tree-br a) (tree-br b)
tree-br (asub a b)              = br2 "B" (show-arith-ir a) (show-arith-ir b) (tree-br a) (tree-br b)
tree-br (amul a b)              = br2 "M" (show-arith-ir a) (show-arith-ir b) (tree-br a) (tree-br b)
tree-br (adiv a b)              = br2 "D" (show-arith-ir a) (show-arith-ir b) (tree-br a) (tree-br b)
tree-br (amod a b)              = br2 "R" (show-arith-ir a) (show-arith-ir b) (tree-br a) (tree-br b)
tree-br (aneg a)                = br1 "G" (show-arith-ir a) (tree-br a)
tree-br (ai2f a)                = br1 "C" (show-arith-ir a) (tree-br a)
tree-br (acmp c-lt a b)         = br2 "K" "0" (show-arith-ir a ++ˢ show-arith-ir b) refl (trans (toList-++ (show-arith-ir a) _) (cong₂ _++_ (tree-br a) (tree-br b)))
tree-br (acmp c-le a b)         = br2 "K" "1" (show-arith-ir a ++ˢ show-arith-ir b) refl (trans (toList-++ (show-arith-ir a) _) (cong₂ _++_ (tree-br a) (tree-br b)))
tree-br (acmp c-gt a b)         = br2 "K" "2" (show-arith-ir a ++ˢ show-arith-ir b) refl (trans (toList-++ (show-arith-ir a) _) (cong₂ _++_ (tree-br a) (tree-br b)))
tree-br (acmp c-ge a b)         = br2 "K" "3" (show-arith-ir a ++ˢ show-arith-ir b) refl (trans (toList-++ (show-arith-ir a) _) (cong₂ _++_ (tree-br a) (tree-br b)))
tree-br (acmp c-eq a b)         = br2 "K" "4" (show-arith-ir a ++ˢ show-arith-ir b) refl (trans (toList-++ (show-arith-ir a) _) (cong₂ _++_ (tree-br a) (tree-br b)))
tree-br (acmp c-ne a b)         = br2 "K" "5" (show-arith-ir a ++ˢ show-arith-ir b) refl (trans (toList-++ (show-arith-ir a) _) (cong₂ _++_ (tree-br a) (tree-br b)))

------------------------------------------------------------------------
-- Prefix-freeness: a rendering, then anything, determines both.
------------------------------------------------------------------------

private
  digit≢_ : ∀ {c : Char} → isDigit c ≡ true → c ≢ '_'
  digit≢_ d refl = case d of λ ()
    where open import Function using (case_of_)

  digit≢n : ∀ {c : Char} → isDigit c ≡ true → c ≢ 'n'
  digit≢n d refl = case d of λ ()
    where open import Function using (case_of_)

  digits : ∀ n → All (λ c → isDigit c ≡ true) (toList (showNat n))
  digits n = subst (All (λ c → isDigit c ≡ true)) (sym (toList-showNat n)) (charsInBase-all-digits n)

  -- a `_`-free word, its `_`, then anything
  split-_ : ∀ (ds ds′ r r′ : List Char) → All (_≢ '_') ds → All (_≢ '_') ds′
          → ds ++ ('_' ∷ r) ≡ ds′ ++ ('_' ∷ r′) → ds ≡ ds′ × r ≡ r′
  split-_ []       []         r r′ _        _          eq = refl , ∷-injectiveʳ eq
  split-_ []       (d′ ∷ ds′) r r′ _        (n′ ∷ _)   eq = ⊥-elim (n′ (sym (∷-injectiveˡ eq)))
  split-_ (d ∷ ds) []         r r′ (n ∷ _)  _          eq = ⊥-elim (n (∷-injectiveˡ eq))
  split-_ (d ∷ ds) (d′ ∷ ds′) r r′ (_ ∷ nd) (_ ∷ nd′)  eq =
    let (e , t) = split-_ ds ds′ r r′ nd nd′ (∷-injectiveʳ eq)
    in cong₂ _∷_ (∷-injectiveˡ eq) e , t

  reassoc : ∀ (xs : List Char) (c : Char) (r : List Char) → (xs ++ (c ∷ [])) ++ r ≡ xs ++ (c ∷ r)
  reassoc xs c r = ++-assoc xs (c ∷ []) r

nat-inj : ∀ (n m : ℕ) (r r′ : List Char) → nat-cs n ++ r ≡ nat-cs m ++ r′ → n ≡ m × r ≡ r′
nat-inj n m r r′ eq =
  let (e , t) = split-_ (toList (showNat n)) (toList (showNat m)) r r′
                  (All-map digit≢_ (digits n)) (All-map digit≢_ (digits m))
                  (trans (sym (reassoc _ '_' r)) (trans eq (reassoc _ '_' r′)))
  in charsInBase-injective 10 n m (trans (sym (toList-showNat n)) (trans e (toList-showNat m))) , t

private
  -- a number never starts with the sign letter
  nat≢n : ∀ (n : ℕ) (r s : List Char) → nat-cs n ++ r ≡ 'n' ∷ s → ⊥
  nat≢n n r s eq = go (toList (showNat n)) (All-map digit≢n (digits n)) (trans (sym (reassoc _ '_' r)) eq)
    where
      go : ∀ (ds : List Char) → All (_≢ 'n') ds → ds ++ ('_' ∷ r) ≡ 'n' ∷ s → ⊥
      go []       _       ()
      go (d ∷ ds) (n ∷ _) eq′ = n (∷-injectiveˡ eq′)

zlit-inj : ∀ (z z′ : ℤ) (r r′ : List Char) → zlit-cs z ++ r ≡ zlit-cs z′ ++ r′ → z ≡ z′ × r ≡ r′
zlit-inj (+ n)      (+ m)      r r′ eq = let (e , t) = nat-inj n m r r′ eq in cong +_ e , t
zlit-inj (+ n)      (-[1+ m ]) r r′ eq = ⊥-elim (nat≢n n r _ eq)
zlit-inj (-[1+ n ]) (+ m)      r r′ eq = ⊥-elim (nat≢n m r′ _ (sym eq))
zlit-inj (-[1+ n ]) (-[1+ m ]) r r′ eq =
  let (e , t) = nat-inj (suc n) (suc m) r r′ (∷-injectiveʳ eq) in cong -[1+_] (suc-inj e) , t
  where suc-inj : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
        suc-inj refl = refl

dlit-inj : ∀ (d d′ : Decimal) (r r′ : List Char) → dlit-cs d ++ r ≡ dlit-cs d′ ++ r′ → d ≡ d′ × r ≡ r′
dlit-inj (s /10^ e) (s′ /10^ e′) r r′ eq
  with zlit-inj s s′ (nat-cs e ++ r) (nat-cs e′ ++ r′)
         (trans (sym (++-assoc (zlit-cs s) (nat-cs e) r)) (trans eq (++-assoc (zlit-cs s′) (nat-cs e′) r′)))
... | refl , t with nat-inj e e′ r r′ t
...   | refl , t′ = refl , t′

path-inj : ∀ (p p′ : InputPath) (r r′ : List Char) → path-cs p ++ r ≡ path-cs p′ ++ r′ → p ≡ p′ × r ≡ r′
path-inj []        []         r r′ eq = refl , ∷-injectiveʳ eq
path-inj (Fst ∷ p) (Fst ∷ p′) r r′ eq = let (e , t) = path-inj p p′ r r′ (∷-injectiveʳ eq) in cong (Fst ∷_) e , t
path-inj (Snd ∷ p) (Snd ∷ p′) r r′ eq = let (e , t) = path-inj p p′ r r′ (∷-injectiveʳ eq) in cong (Snd ∷_) e , t
path-inj []        (Fst ∷ _)  _ _ ()
path-inj []        (Snd ∷ _)  _ _ ()
path-inj (Fst ∷ _) []         _ _ ()
path-inj (Snd ∷ _) []         _ _ ()
path-inj (Fst ∷ _) (Snd ∷ _)  _ _ ()
path-inj (Snd ∷ _) (Fst ∷ _)  _ _ ()

shape-inj : ∀ (a b : InputShape) (r r′ : List Char) → shape-cs a ++ r ≡ shape-cs b ++ r′ → a ≡ b × r ≡ r′
shape-inj shape-unit  shape-unit  r r′ eq = refl , ∷-injectiveʳ eq
shape-inj shape-int   shape-int   r r′ eq = refl , ∷-injectiveʳ eq
shape-inj shape-float shape-float r r′ eq = refl , ∷-injectiveʳ eq
shape-inj (shape-pair a b) (shape-pair a′ b′) r r′ eq
  with shape-inj a a′ (shape-cs b ++ r) (shape-cs b′ ++ r′)
         (trans (sym (++-assoc (shape-cs a) (shape-cs b) r)) (trans (∷-injectiveʳ eq) (++-assoc (shape-cs a′) (shape-cs b′) r′)))
... | refl , t with shape-inj b b′ r r′ t
...   | refl , t′ = refl , t′

-- a typed path is its erasure, at a fixed shape
erase-inj : ∀ {sh n n′} (p : Path sh n) (p′ : Path sh n′) → ⌊ p ⌋ᴾ ≡ ⌊ p′ ⌋ᴾ
          → _≡_ {A = Σ NumType (Path sh)} (n , p) (n′ , p′)
erase-inj here-int   here-int    _  = refl
erase-inj here-flt   here-flt    _  = refl
erase-inj (go-fst p) (go-fst p′) eq with erase-inj p p′ (∷-injectiveʳ eq)
... | refl = refl
erase-inj (go-snd p) (go-snd p′) eq with erase-inj p p′ (∷-injectiveʳ eq)
... | refl = refl

private
  -- re-associate two renderings and a rest
  as2 : ∀ (xs ys xs′ ys′ r r′ : List Char) → (xs ++ ys) ++ r ≡ (xs′ ++ ys′) ++ r′
      → xs ++ (ys ++ r) ≡ xs′ ++ (ys′ ++ r′)
  as2 xs ys xs′ ys′ r r′ eq = trans (sym (++-assoc xs ys r)) (trans eq (++-assoc xs′ ys′ r′))

  cmp-inj : ∀ (o o′ : CmpOp) → cmp-c o ≡ cmp-c o′ → o ≡ o′
  cmp-inj c-lt c-lt _ = refl
  cmp-inj c-le c-le _ = refl
  cmp-inj c-gt c-gt _ = refl
  cmp-inj c-ge c-ge _ = refl
  cmp-inj c-eq c-eq _ = refl
  cmp-inj c-ne c-ne _ = refl

tree-inj : ∀ {sh n n′} (e : MArithIR sh n) (e′ : MArithIR sh n′) (r r′ : List Char)
         → tree-cs e ++ r ≡ tree-cs e′ ++ r′ → _≡_ {A = Σ NumType (MArithIR sh)} (n , e) (n′ , e′) × r ≡ r′
tree-inj (alit z) (alit z′) r r′ eq with zlit-inj z z′ r r′ (∷-injectiveʳ eq)
... | refl , t = refl , t
tree-inj (aflit d) (aflit d′) r r′ eq with dlit-inj d d′ r r′ (∷-injectiveʳ eq)
... | refl , t = refl , t
tree-inj {n = NInt} {n′ = NInt} (ainput p) (ainput p′) r r′ eq
  with path-inj ⌊ p ⌋ᴾ ⌊ p′ ⌋ᴾ r r′ (∷-injectiveʳ eq)
... | e , t with erase-inj p p′ e
...   | refl = refl , t
tree-inj {n = NFloat} {n′ = NFloat} (ainput p) (ainput p′) r r′ eq
  with path-inj ⌊ p ⌋ᴾ ⌊ p′ ⌋ᴾ r r′ (∷-injectiveʳ eq)
... | e , t with erase-inj p p′ e
...   | refl = refl , t
tree-inj (aadd a b) (aadd a′ b′) r r′ eq
  with tree-inj a a′ _ _ (as2 (tree-cs a) (tree-cs b) (tree-cs a′) (tree-cs b′) r r′ (∷-injectiveʳ eq))
... | refl , t with tree-inj b b′ r r′ t
...   | refl , t′ = refl , t′
tree-inj (asub a b) (asub a′ b′) r r′ eq
  with tree-inj a a′ _ _ (as2 (tree-cs a) (tree-cs b) (tree-cs a′) (tree-cs b′) r r′ (∷-injectiveʳ eq))
... | refl , t with tree-inj b b′ r r′ t
...   | refl , t′ = refl , t′
tree-inj (amul a b) (amul a′ b′) r r′ eq
  with tree-inj a a′ _ _ (as2 (tree-cs a) (tree-cs b) (tree-cs a′) (tree-cs b′) r r′ (∷-injectiveʳ eq))
... | refl , t with tree-inj b b′ r r′ t
...   | refl , t′ = refl , t′
tree-inj (adiv a b) (adiv a′ b′) r r′ eq
  with tree-inj a a′ _ _ (as2 (tree-cs a) (tree-cs b) (tree-cs a′) (tree-cs b′) r r′ (∷-injectiveʳ eq))
... | refl , t with tree-inj b b′ r r′ t
...   | refl , t′ = refl , t′
tree-inj (amod a b) (amod a′ b′) r r′ eq
  with tree-inj a a′ _ _ (as2 (tree-cs a) (tree-cs b) (tree-cs a′) (tree-cs b′) r r′ (∷-injectiveʳ eq))
... | refl , t with tree-inj b b′ r r′ t
...   | refl , t′ = refl , t′
tree-inj (aneg a) (aneg a′) r r′ eq with tree-inj a a′ r r′ (∷-injectiveʳ eq)
... | refl , t = refl , t
tree-inj (ai2f a) (ai2f a′) r r′ eq with tree-inj a a′ r r′ (∷-injectiveʳ eq)
... | refl , t = refl , t
tree-inj (acmp o a b) (acmp o′ a′ b′) r r′ eq
  with cmp-inj o o′ (∷-injectiveˡ (∷-injectiveʳ eq))
... | refl
  with tree-inj a a′ _ _ (as2 (tree-cs a) (tree-cs b) (tree-cs a′) (tree-cs b′) r r′ (∷-injectiveʳ (∷-injectiveʳ eq)))
...   | refl , t with tree-inj b b′ r r′ t
...     | refl , t′ = refl , t′

-- (an input on the right: its letter waits on its kind)
tree-inj (alit _) (ainput {NInt} _) _ _ ()
tree-inj (alit _) (ainput {NFloat} _) _ _ ()
tree-inj (aflit _) (ainput {NInt} _) _ _ ()
tree-inj (aflit _) (ainput {NFloat} _) _ _ ()
tree-inj (aadd _ _) (ainput {NInt} _) _ _ ()
tree-inj (aadd _ _) (ainput {NFloat} _) _ _ ()
tree-inj (asub _ _) (ainput {NInt} _) _ _ ()
tree-inj (asub _ _) (ainput {NFloat} _) _ _ ()
tree-inj (amul _ _) (ainput {NInt} _) _ _ ()
tree-inj (amul _ _) (ainput {NFloat} _) _ _ ()
tree-inj (adiv _ _) (ainput {NInt} _) _ _ ()
tree-inj (adiv _ _) (ainput {NFloat} _) _ _ ()
tree-inj (amod _ _) (ainput {NInt} _) _ _ ()
tree-inj (amod _ _) (ainput {NFloat} _) _ _ ()
tree-inj (aneg _) (ainput {NInt} _) _ _ ()
tree-inj (aneg _) (ainput {NFloat} _) _ _ ()
tree-inj (ai2f _) (ainput {NInt} _) _ _ ()
tree-inj (ai2f _) (ainput {NFloat} _) _ _ ()
tree-inj (acmp _ _ _) (ainput {NInt} _) _ _ ()
tree-inj (acmp _ _ _) (ainput {NFloat} _) _ _ ()

------------------------------------------------------------------------
-- THE THEOREM.
------------------------------------------------------------------------

Block : Set
Block = Σ InputShape (λ sh → Σ NumType (MArithIR sh))

digest-cs : ∀ s {m} (x : MArithIR s m) → toList (block-digest x) ≡ shape-cs s ++ tree-cs x
digest-cs s x = trans (toList-++ (show-shape s) (show-arith-ir x)) (cong₂ _++_ (shape-br s) (tree-br x))

digest-injective : ∀ {sh n sh′ n′} (e : MArithIR sh n) (e′ : MArithIR sh′ n′)
                 → block-digest e ≡ block-digest e′
                 → _≡_ {A = Block} (sh , n , e) (sh′ , n′ , e′)
-- …read off the characters
digest-cs-injective : ∀ {sh n sh′ n′} (e : MArithIR sh n) (e′ : MArithIR sh′ n′)
                    → toList (block-digest e) ≡ toList (block-digest e′)
                    → _≡_ {A = Block} (sh , n , e) (sh′ , n′ , e′)
digest-cs-injective {sh} {n} {sh′} {n′} e e′ eq
  with shape-inj sh sh′ (tree-cs e) (tree-cs e′)
         (trans (sym (digest-cs sh e)) (trans eq (digest-cs sh′ e′)))
... | refl , t with tree-inj e e′ [] [] (trans (++-identityʳ (tree-cs e)) (trans t (sym (++-identityʳ (tree-cs e′)))))
...   | refl , _ = refl

digest-injective e e′ eq = digest-cs-injective e e′ (cong toList eq)

------------------------------------------------------------------------
-- …AND ONE SYMBOL IS ONE BLOCK. The symbol is `once_`, the length of the
-- z-encoded name, then the z-encoding (`mangle-component`); the encoding
-- starts with the `a` of `arith.block.`, no digit, so the length prefix ends
-- where it does (`digit-prefix-unique`), and z-encoding is injective
-- (`zencL-inj`). No `ValidName` is needed — a block name has dots, which no
-- lexer name does.
------------------------------------------------------------------------

private
  name-cs : ∀ {sh n} (e : MArithIR sh n) → toList (block-name e) ≡ toList "arith.block." ++ toList (block-digest e)
  name-cs e = toList-++ "arith.block." (block-digest e)

  sym-cs : ∀ {sh n} (e : MArithIR sh n)
         → toList (once-symbol-own (block-name e)) ≡ toList "once_" ++ mangL (toList (block-name e))
  sym-cs e = trans (toList-++ "once_" (mangle-component (block-name e))) (cong (toList "once_" ++_) (toList-mangle (block-name e)))

  head-a : ∀ (d : List Char) → HeadNotDigit (zencL (toList "arith.block." ++ d))
  head-a d = refl

block-symbol-injective : ∀ {sh n sh′ n′} (e : MArithIR sh n) (e′ : MArithIR sh′ n′)
                       → once-symbol-own (block-name e) ≡ once-symbol-own (block-name e′)
                       → _≡_ {A = Block} (sh , n , e) (sh′ , n′ , e′)
block-symbol-injective e e′ eq =
  digest-cs-injective e e′
    (++-cancelˡ (toList "arith.block.") _ _
      (trans (sym (name-cs e)) (trans names (name-cs e′))))
  where
    mang : mangL (toList (block-name e)) ≡ mangL (toList (block-name e′))
    mang = ++-cancelˡ (toList "once_") _ _ (trans (sym (sym-cs e)) (trans (cong toList eq) (sym-cs e′)))
    hd : ∀ {sh n} (x : MArithIR sh n) → HeadNotDigit (zencL (toList (block-name x)))
    hd x = subst (λ z → HeadNotDigit (zencL z)) (sym (name-cs x)) (head-a (toList (block-digest x)))
    names : toList (block-name e) ≡ toList (block-name e′)
    z  = zencL (toList (block-name e))
    z′ = zencL (toList (block-name e′))
    names = zencL-inj _ _ (proj₂ (digit-prefix-unique
              (charsInBase 10 (length z)) (charsInBase 10 (length z′)) z z′
              (charsInBase-all-digits (length z)) (charsInBase-all-digits (length z′)) (hd e) (hd e′) mang))
