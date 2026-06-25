-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Target.SymbolInjective
--
-- Plan 0.50. INJECTIVITY of `once-symbol-path` under the `ValidIdent`
-- precondition: two resolved identities whose components are all genuine
-- lexer identifiers get DISTINCT assembly symbols. This is the clash-free
-- guarantee the mangling scheme was designed to give, proved (not assumed).
--
-- Why it holds: the symbol is `once_` + `_`-joined, per-component
-- `<decimal-length><z-encoded-component>` segments. The decimal length
-- prefix is self-delimiting because (a) the decimal digits are all digit
-- chars, while (b) a z-encoded LEXER identifier never starts with a digit
-- (its first char is the z-escape `z`, an underscore, or an alphabetic —
-- `isIdentStart`). So the boundary between `<length>` and `<component>` is
-- unambiguous, the length pins the component's char-count, and the whole
-- thing decodes uniquely.
--
-- The proof bottoms out at ONE primitive postulate, `alpha⇒¬digit` — the
-- disjointness of the opaque Unicode predicates `isAlpha`/`isDigit` — which
-- cannot be derived (both are `prim…` black boxes), exactly the kind of
-- char-primitive fact the stdlib itself discharges with `trustMe`
-- (`Data.String.Unsafe`). Everything else is proved.
------------------------------------------------------------------------

module Once.Target.SymbolInjective where

open import Data.Bool using (Bool; true; false; _∨_; T)
open import Data.Char using (Char; isAlpha; isDigit; toℕ)
open import Data.Char.Properties using (_≟_) renaming (toℕ-injective to charToℕ-injective)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; length)
open import Data.List.Properties using (∷-injective)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Nat.Show using (showInBase; charsInBase)
open import Data.Digit using (showDigit)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Data.Empty using (⊥; ⊥-elim)

open import Once.Parser.Lexer using (isIdentStart; isIdentContinue; toNat)
open import Once.Target.Symbol using (z-encode-char; z-encode-char-aux)

------------------------------------------------------------------------
-- Digit-character predicate.
------------------------------------------------------------------------

-- A char is a decimal digit exactly when the opaque `isDigit` says so.
IsDigitC : Char → Set
IsDigitC c = isDigit c ≡ true

NotDigitC : Char → Set
NotDigitC c = isDigit c ≡ false

------------------------------------------------------------------------
-- The ONE primitive postulate: `isAlpha` and `isDigit` are disjoint.
-- True of the Unicode categories, but both are opaque `prim…` functions
-- with no equational theory, so this is irreducible (cf. stdlib `trustMe`).
------------------------------------------------------------------------
postulate
  alpha⇒¬digit : ∀ {c} → isAlpha c ≡ true → isDigit c ≡ false

------------------------------------------------------------------------
-- Every char produced by `charsInBase 10` is a digit char.
------------------------------------------------------------------------

-- `showDigit` of a base-10 digit is one of '0'..'9' — a digit char.
showDigit10-isDigit : ∀ (d : Fin 10) → isDigit (showDigit {10} d) ≡ true
showDigit10-isDigit zero = refl
showDigit10-isDigit (suc zero) = refl
showDigit10-isDigit (suc (suc zero)) = refl
showDigit10-isDigit (suc (suc (suc zero))) = refl
showDigit10-isDigit (suc (suc (suc (suc zero)))) = refl
showDigit10-isDigit (suc (suc (suc (suc (suc zero))))) = refl
showDigit10-isDigit (suc (suc (suc (suc (suc (suc zero)))))) = refl
showDigit10-isDigit (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
showDigit10-isDigit (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
showDigit10-isDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl

------------------------------------------------------------------------
-- Per-character z-encoding: classification + left inverse.
--
-- `unescape` maps an escape tag back to the special char it stands for
-- (defined on explicit `_≟_` decisions, NO `with` — exact-split friendly,
-- and the user's blanket preference). `zec-class` then classifies any char:
-- either it is special — `z-encode-char c ≡ 'z' ∷ tag ∷ []` with
-- `unescape tag ≡ c` recovering it — or ordinary — `z-encode-char c ≡ c ∷ []`
-- and `c ≢ 'z'`. This is the proof-carrying VIEW the injectivity argument
-- consumes (cf. lessons-learned: classify by a datatype that carries the
-- proof, never by piercing an opaque `with`-chain).
------------------------------------------------------------------------

unescape-aux :
  (t : Char)
  → Dec (t ≡ 'z') → Dec (t ≡ 'q') → Dec (t ≡ 'p') → Dec (t ≡ 't')
  → Dec (t ≡ 'b') → Dec (t ≡ 'h') → Dec (t ≡ 'd') → Char
unescape-aux t (yes _) _ _ _ _ _ _ = 'z'
unescape-aux t (no _) (yes _) _ _ _ _ _ = '\''
unescape-aux t (no _) (no _) (yes _) _ _ _ _ = '+'
unescape-aux t (no _) (no _) (no _) (yes _) _ _ _ = '*'
unescape-aux t (no _) (no _) (no _) (no _) (yes _) _ _ = '!'
unescape-aux t (no _) (no _) (no _) (no _) (no _) (yes _) _ = '?'
unescape-aux t (no _) (no _) (no _) (no _) (no _) (no _) (yes _) = '.'
unescape-aux t (no _) (no _) (no _) (no _) (no _) (no _) (no _) = t

unescape : Char → Char
unescape t = unescape-aux t (t ≟ 'z') (t ≟ 'q') (t ≟ 'p') (t ≟ 't')
                            (t ≟ 'b') (t ≟ 'h') (t ≟ 'd')

-- Classification of one char's z-encoding, with the char recoverable.
ZClass : Char → List Char → Set
ZClass c enc =
  (Σ[ t ∈ Char ] (enc ≡ 'z' ∷ t ∷ []) × (unescape t ≡ c))
  ⊎ ((enc ≡ c ∷ []) × ¬ (c ≡ 'z'))

zec-class-aux :
  (c : Char)
  → (d1 : Dec (c ≡ 'z')) (d2 : Dec (c ≡ '\'')) (d3 : Dec (c ≡ '+'))
    (d4 : Dec (c ≡ '*')) (d5 : Dec (c ≡ '!')) (d6 : Dec (c ≡ '?'))
    (d7 : Dec (c ≡ '.'))
  → ZClass c (z-encode-char-aux c d1 d2 d3 d4 d5 d6 d7)
zec-class-aux c (yes p) _ _ _ _ _ _ = inj₁ ('z' , refl , sym p)
zec-class-aux c (no _) (yes p) _ _ _ _ _ = inj₁ ('q' , refl , sym p)
zec-class-aux c (no _) (no _) (yes p) _ _ _ _ = inj₁ ('p' , refl , sym p)
zec-class-aux c (no _) (no _) (no _) (yes p) _ _ _ = inj₁ ('t' , refl , sym p)
zec-class-aux c (no _) (no _) (no _) (no _) (yes p) _ _ = inj₁ ('b' , refl , sym p)
zec-class-aux c (no _) (no _) (no _) (no _) (no _) (yes p) _ = inj₁ ('h' , refl , sym p)
zec-class-aux c (no _) (no _) (no _) (no _) (no _) (no _) (yes p) = inj₁ ('d' , refl , sym p)
zec-class-aux c (no ¬z) (no _) (no _) (no _) (no _) (no _) (no _) = inj₂ (refl , ¬z)

zec-class : (c : Char) → ZClass c (z-encode-char c)
zec-class c = zec-class-aux c (c ≟ 'z') (c ≟ '\'') (c ≟ '+') (c ≟ '*')
                              (c ≟ '!') (c ≟ '?') (c ≟ '.')

------------------------------------------------------------------------
-- `zencL` (= `concatMap z-encode-char`, the char-list z-encoding) is
-- injective. By induction: the per-char classification fixes whether the
-- next 1 or 2 chars belong to this component, the escape tag decodes back
-- to the original char, and an ordinary char (≢ 'z') can never collide with
-- an escape (which always starts 'z').
------------------------------------------------------------------------

zencL : List Char → List Char
zencL = concatMap z-encode-char

cons≢[] : ∀ {A : Set} {x : A} {xs : List A} → ¬ (x ∷ xs ≡ [])
cons≢[] ()

zenc++-nonempty : ∀ {y} → ZClass y (z-encode-char y)
                → (rest : List Char) → ¬ (z-encode-char y ++ rest ≡ [])
zenc++-nonempty (inj₁ (t , ex , _)) rest eq rewrite ex = cons≢[] eq
zenc++-nonempty (inj₂ (ex , _))     rest eq rewrite ex = cons≢[] eq

-- One induction step: peel the leading component off both sides.
consStep : ∀ {x y} (xs ys : List Char)
  → ZClass x (z-encode-char x) → ZClass y (z-encode-char y)
  → z-encode-char x ++ zencL xs ≡ z-encode-char y ++ zencL ys
  → (x ≡ y) × (zencL xs ≡ zencL ys)
consStep xs ys (inj₁ (tx , ex , dx)) (inj₁ (ty , ey , dy)) eq rewrite ex | ey =
  let (_    , r1) = ∷-injective eq
      (txty , zz) = ∷-injective r1
  in trans (sym dx) (trans (cong unescape txty) dy) , zz
consStep xs ys (inj₁ (tx , ex , dx)) (inj₂ (ey , ¬y)) eq rewrite ex | ey =
  ⊥-elim (¬y (sym (proj₁ (∷-injective eq))))
consStep xs ys (inj₂ (ex , ¬x)) (inj₁ (ty , ey , dy)) eq rewrite ex | ey =
  ⊥-elim (¬x (proj₁ (∷-injective eq)))
consStep xs ys (inj₂ (ex , ¬x)) (inj₂ (ey , ¬y)) eq rewrite ex | ey =
  let (x≡y , zz) = ∷-injective eq in x≡y , zz

zencL-inj : ∀ (xs ys : List Char) → zencL xs ≡ zencL ys → xs ≡ ys
zencL-inj [] [] eq = refl
zencL-inj [] (y ∷ ys) eq = ⊥-elim (zenc++-nonempty (zec-class y) (zencL ys) (sym eq))
zencL-inj (x ∷ xs) [] eq = ⊥-elim (zenc++-nonempty (zec-class x) (zencL xs) eq)
zencL-inj (x ∷ xs) (y ∷ ys) eq =
  let (x≡y , zz) = consStep xs ys (zec-class x) (zec-class y) eq
  in cong₂ _∷_ x≡y (zencL-inj xs ys zz)

------------------------------------------------------------------------
-- Length-prefix self-delimiting machinery.
--
-- The decimal length-prefix `charsInBase 10 n` is made of digit chars,
-- while a z-encoded LEXER identifier starts with a NON-digit (the first
-- char is `isIdentStart` — alphabetic or `_` — or, if special, the escape
-- `z`). So in `<digits><component>…` the maximal digit run is exactly the
-- length prefix: the boundary is forced. `digit-prefix-unique` makes that
-- precise; `len-prefix-cancel` then splits at the (now known) length.
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

-- Every char in `charsInBase 10 n` is a digit char.
all-digits-mapped : ∀ (zs : List (Fin 10)) → All IsDigitC (map (showDigit {10}) zs)
all-digits-mapped [] = []
all-digits-mapped (z ∷ zs) = showDigit10-isDigit z ∷ all-digits-mapped zs

charsInBase-all-digits : ∀ (n : ℕ) → All IsDigitC (charsInBase 10 n)
charsInBase-all-digits n = all-digits-mapped _

-- A `true` disjunction splits into a `true` disjunct.
∨-true-split : ∀ (a b : Bool) → (a ∨ b) ≡ true → (a ≡ true) ⊎ (b ≡ true)
∨-true-split true  b _  = inj₁ refl
∨-true-split false true _ = inj₂ refl
∨-true-split false false ()

-- A lexer identifier-start char is never a decimal digit.
identStart⇒¬digit : ∀ {c} → isIdentStart c ≡ true → isDigit c ≡ false
identStart⇒¬digit {c} h = go (∨-true-split (isAlpha c) (toNat c ≡ᵇ toNat '_') h)
  where
    go : (isAlpha c ≡ true) ⊎ ((toNat c ≡ᵇ toNat '_') ≡ true) → isDigit c ≡ false
    go (inj₁ a) = alpha⇒¬digit {c} a
    go (inj₂ u) = cong isDigit (charToℕ-injective c '_' (≡ᵇ⇒≡ (toNat c) (toNat '_') (subst T (sym u) tt)))

-- "the list is empty, or its head is a non-digit char"
HeadNotDigit : List Char → Set
HeadNotDigit [] = ⊤
HeadNotDigit (c ∷ _) = isDigit c ≡ false

-- The decimal length-prefix is uniquely determined: matching digit prefixes
-- (each followed by a non-digit) coincide, and so do the remainders.
digit-prefix-unique : ∀ (D1 D2 r1 r2 : List Char)
  → All IsDigitC D1 → All IsDigitC D2 → HeadNotDigit r1 → HeadNotDigit r2
  → D1 ++ r1 ≡ D2 ++ r2 → (D1 ≡ D2) × (r1 ≡ r2)
digit-prefix-unique [] [] r1 r2 _ _ _ _ eq = refl , eq
digit-prefix-unique [] (d2 ∷ D2') r1 r2 _ (ad2 ∷ _) hnd1 _ eq =
  ⊥-elim (false≢true (trans (sym (subst HeadNotDigit eq hnd1)) ad2))
digit-prefix-unique (d1 ∷ D1') [] r1 r2 (ad1 ∷ _) _ _ hnd2 eq =
  ⊥-elim (false≢true (trans (sym (subst HeadNotDigit (sym eq) hnd2)) ad1))
digit-prefix-unique (d1 ∷ D1') (d2 ∷ D2') r1 r2 (_ ∷ aD1) (_ ∷ aD2) hnd1 hnd2 eq =
  let (d1≡d2 , eqrest) = ∷-injective eq
      (D1'≡D2' , r1≡r2) = digit-prefix-unique D1' D2' r1 r2 aD1 aD2 hnd1 hnd2 eqrest
  in cong₂ _∷_ d1≡d2 D1'≡D2' , r1≡r2

-- Equal-length prefixes of equal concatenations coincide (with remainders).
len-prefix-cancel : ∀ (A B s t : List Char)
  → length A ≡ length B → A ++ s ≡ B ++ t → (A ≡ B) × (s ≡ t)
len-prefix-cancel [] [] s t _ eq = refl , eq
len-prefix-cancel (a ∷ A') (b ∷ B') s t leq eq =
  let (a≡b , eqrest) = ∷-injective eq
      (A'≡B' , s≡t) = len-prefix-cancel A' B' s t (cong-pred leq) eqrest
  in cong₂ _∷_ a≡b A'≡B' , s≡t
  where
    cong-pred : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
    cong-pred refl = refl
