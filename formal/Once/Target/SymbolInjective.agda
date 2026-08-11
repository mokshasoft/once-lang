-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.List.Properties using (∷-injective; ++-assoc; ++-conicalˡ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Nat.Show using (showInBase; charsInBase)
open import Data.Digit using (showDigit)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no; Dec)
open import Data.Empty using (⊥; ⊥-elim)

open import Data.List.Properties using (map-cong; map-∘; ++-cancelˡ)
                                 renaming (map-injective to mapL-injective)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Function using (_∘_)
import Data.String as Str
open import Data.String using (String; toList; fromList)
open import Data.String.Properties using (toList-injective)
open import Data.String.Unsafe using (toList-++; toList∘fromList)

open import Once.Parser.Lexer using (isIdentStart; isIdentContinue; toNat)
open import Once.Target.Symbol
  using (z-encode-char; z-encode-char-aux; z-encode; showNat;
         mangle-component; join-us; once-prefix; once-symbol-path; once-symbol-own)
open import Once.CanonicalName using (CanonicalName; canonical; parts)

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

------------------------------------------------------------------------
-- Component lists → the joined symbol body, and its injectivity.
--
-- A `ValidIdentChars` is a non-empty char list whose head is a lexer
-- `isIdentStart` (so, by the length-prefix argument, its z-encoding starts
-- non-digit). `mangL` is the per-component mangling at the char-list level
-- (matches `toList ∘ mangle-component`); `joinUsL'`/`withSep` the `_`-join
-- (matches `toList ∘ join-us`). `joinL-inj` is the core: the list of
-- components is recovered from the joined body.
------------------------------------------------------------------------

open import Data.Nat.Show.Properties using (charsInBase-injective)

ValidIdentChars : List Char → Set
ValidIdentChars [] = ⊥
ValidIdentChars (c ∷ cs) =
  (isIdentStart c ≡ true) × All (λ d → isIdentContinue d ≡ true) cs

mangL : List Char → List Char
mangL cs = charsInBase 10 (length (zencL cs)) ++ zencL cs

-- z-encoding of a valid identifier: a cons cell with a non-digit head.
zencL-vic : ∀ {cs} → ValidIdentChars cs
  → Σ[ h ∈ Char ] Σ[ t ∈ List Char ] (zencL cs ≡ h ∷ t) × (isDigit h ≡ false)
zencL-vic {c0 ∷ cs'} (isC0 , _) = go (zec-class c0)
  where
    go : ZClass c0 (z-encode-char c0)
       → Σ[ h ∈ Char ] Σ[ t ∈ List Char ] (zencL (c0 ∷ cs') ≡ h ∷ t) × (isDigit h ≡ false)
    go (inj₁ (tag , ex , _)) = 'z' , tag ∷ zencL cs' , cong (_++ zencL cs') ex , refl
    go (inj₂ (ex , _))       = c0 , zencL cs'        , cong (_++ zencL cs') ex , identStart⇒¬digit {c0} isC0

zencL-suffix-headND : ∀ {cs} (suffix : List Char)
                    → ValidIdentChars cs → HeadNotDigit (zencL cs ++ suffix)
zencL-suffix-headND {cs} suffix vic =
  let (h , t , zceq , hnd) = zencL-vic vic
  in subst (λ z → HeadNotDigit (z ++ suffix)) (sym zceq) hnd

++-cons-≢[] : ∀ (A : List Char) {h : Char} {rest : List Char} → ¬ (A ++ (h ∷ rest) ≡ [])
++-cons-≢[] [] ()
++-cons-≢[] (a ∷ A') ()

mangL-nonempty : ∀ {d} → ValidIdentChars d → ¬ (mangL d ≡ [])
mangL-nonempty {d} vic eq =
  let (h , t , zceq , _) = zencL-vic vic
  in ++-cons-≢[] (charsInBase 10 (length (zencL d)))
       (subst (λ z → charsInBase 10 (length (zencL d)) ++ z ≡ []) zceq eq)

joinUsL' : List (List Char) → List Char
withSep  : List (List Char) → List Char
joinUsL' []       = []
joinUsL' (x ∷ xs) = x ++ withSep xs
withSep []       = []
withSep (x ∷ xs) = '_' ∷ (x ++ withSep xs)

-- Peel one mangled component (+ its arbitrary suffix) off both sides.
peel : ∀ {c d} (wc wd : List Char)
  → ValidIdentChars c → ValidIdentChars d
  → mangL c ++ wc ≡ mangL d ++ wd
  → (c ≡ d) × (wc ≡ wd)
peel {c} {d} wc wd vc vd eq =
  let A = charsInBase 10 (length (zencL c))
      B = charsInBase 10 (length (zencL d))
      eq' : A ++ (zencL c ++ wc) ≡ B ++ (zencL d ++ wd)
      eq' = trans (sym (++-assoc A (zencL c) wc)) (trans eq (++-assoc B (zencL d) wd))
      pu = digit-prefix-unique A B (zencL c ++ wc) (zencL d ++ wd)
             (charsInBase-all-digits (length (zencL c)))
             (charsInBase-all-digits (length (zencL d)))
             (zencL-suffix-headND wc vc) (zencL-suffix-headND wd vd) eq'
      lenEq = charsInBase-injective 10 (length (zencL c)) (length (zencL d)) (proj₁ pu)
      lpc = len-prefix-cancel (zencL c) (zencL d) wc wd lenEq (proj₂ pu)
  in zencL-inj c d (proj₁ lpc) , proj₂ lpc

withSep-inj : ∀ (css dss : List (List Char))
  → withSep (map mangL css) ≡ withSep (map mangL dss)
  → All ValidIdentChars css → All ValidIdentChars dss → css ≡ dss
withSep-inj [] [] eq vc vd = refl
withSep-inj [] (d ∷ dss') eq vc vd = ⊥-elim (cons≢[] (sym eq))
withSep-inj (c ∷ css') [] eq vc vd = ⊥-elim (cons≢[] eq)
withSep-inj (c ∷ css') (d ∷ dss') eq (vc0 ∷ vcs) (vd0 ∷ vds) =
  let (c≡d , wEq) = peel (withSep (map mangL css')) (withSep (map mangL dss'))
                         vc0 vd0 (proj₂ (∷-injective eq))
  in cong₂ _∷_ c≡d (withSep-inj css' dss' wEq vcs vds)

joinL-inj : ∀ (css dss : List (List Char))
  → joinUsL' (map mangL css) ≡ joinUsL' (map mangL dss)
  → All ValidIdentChars css → All ValidIdentChars dss → css ≡ dss
joinL-inj [] [] eq vc vd = refl
joinL-inj [] (d ∷ dss') eq vc (vd0 ∷ _) =
  ⊥-elim (mangL-nonempty vd0 (++-conicalˡ (mangL d) (withSep (map mangL dss')) (sym eq)))
joinL-inj (c ∷ css') [] eq (vc0 ∷ _) vd =
  ⊥-elim (mangL-nonempty vc0 (++-conicalˡ (mangL c) (withSep (map mangL css')) eq))
joinL-inj (c ∷ css') (d ∷ dss') eq (vc0 ∷ vcs) (vd0 ∷ vds) =
  let (c≡d , wEq) = peel (withSep (map mangL css')) (withSep (map mangL dss')) vc0 vd0 eq
  in cong₂ _∷_ c≡d (withSep-inj css' dss' wEq vcs vds)

------------------------------------------------------------------------
-- String ⇄ char-list bridge, and the headline injectivity theorem.
--
-- `toList` is the homomorphism from the String-level mangling
-- (`mangle-component`/`join-us`/`once-symbol-path`) to the char-list
-- mirrors above. Pushing `toList` through, cancelling the shared `once_`
-- prefix, and applying `joinL-inj` recovers the component list; `toList`
-- injectivity then recovers the component strings, and record-η the name.
------------------------------------------------------------------------

ValidIdent : String → Set
ValidIdent s = ValidIdentChars (toList s)

toList-showNat : ∀ (n : ℕ) → toList (showNat n) ≡ charsInBase 10 n
toList-showNat n = toList∘fromList (charsInBase 10 n)

toList-zencode : ∀ (s : String) → toList (z-encode s) ≡ zencL (toList s)
toList-zencode s = toList∘fromList (concatMap z-encode-char (toList s))

toList-mangle : ∀ (s : String) → toList (mangle-component s) ≡ mangL (toList s)
toList-mangle s =
  trans (toList-++ (showNat L) (z-encode s))
        (cong₂ _++_
          (trans (toList-showNat L) (cong (charsInBase 10) (cong length (toList-zencode s))))
          (toList-zencode s))
  where L = length (toList (z-encode s))

toList-joinUs : ∀ (strs : List String) → toList (join-us strs) ≡ joinUsL' (map toList strs)
toList-joinUs [] = refl
toList-joinUs (x ∷ []) = sym (++-identityʳ (toList x))
  where open import Data.List.Properties using (++-identityʳ)
toList-joinUs (x ∷ y ∷ xs) =
  trans (toList-++ x ("_" Str.++ join-us (y ∷ xs)))
        (cong (toList x ++_)
          (trans (toList-++ "_" (join-us (y ∷ xs)))
                 (cong ('_' ∷_) (toList-joinUs (y ∷ xs)))))

-- component-body relation: map toList ∘ map mangle-component ≡ map mangL ∘ map toList
body-rel : ∀ (p : List String) → map toList (map mangle-component p) ≡ map mangL (map toList p)
body-rel p = trans (sym (map-∘ p)) (trans (map-cong toList-mangle p) (map-∘ p))

once-symbol-path-injective :
  ∀ (cn₁ cn₂ : CanonicalName)
  → All ValidIdent (parts cn₁) → All ValidIdent (parts cn₂)
  → once-symbol-path cn₁ ≡ once-symbol-path cn₂ → cn₁ ≡ cn₂
once-symbol-path-injective cn₁ cn₂ v1 v2 eq =
  cong canonical
    (mapL-injective (λ {a} {b} → toList-injective a b)
      (joinL-inj (map toList (parts cn₁)) (map toList (parts cn₂))
        bodyEq (map⁺ v1) (map⁺ v2)))
  where
    M : CanonicalName → String
    M cn = join-us (map mangle-component (parts cn))
    -- cancel the shared `once_` prefix at the char-list level
    teq : toList (M cn₁) ≡ toList (M cn₂)
    teq = ++-cancelˡ (toList once-prefix) _ _
      (trans (sym (toList-++ once-prefix (M cn₁)))
             (trans (cong toList eq) (toList-++ once-prefix (M cn₂))))
    bodyEq : joinUsL' (map mangL (map toList (parts cn₁)))
           ≡ joinUsL' (map mangL (map toList (parts cn₂)))
    bodyEq =
      trans (sym (trans (toList-joinUs (map mangle-component (parts cn₁)))
                        (cong joinUsL' (body-rel (parts cn₁)))))
            (trans teq
                   (trans (toList-joinUs (map mangle-component (parts cn₂)))
                          (cong joinUsL' (body-rel (parts cn₂)))))

------------------------------------------------------------------------
-- Plan 0.50 — the BARE-name corollary. `once-symbol-own` (the symbol of a
-- single top-level definition name, = `once-symbol-path (canonical [name])`)
-- is injective on ValidIdent names; its ≢-form is what `program-no-clash`
-- uses to lift distinct DEFINITION names to distinct emitted SYMBOLS.
------------------------------------------------------------------------

once-symbol-own-injective : ∀ (x y : String)
  → ValidIdent x → ValidIdent y
  → once-symbol-own x ≡ once-symbol-own y → x ≡ y
once-symbol-own-injective x y vx vy eq =
  proj₁ (∷-injective (cong parts
    (once-symbol-path-injective (canonical (x ∷ [])) (canonical (y ∷ []))
      (vx ∷ []) (vy ∷ []) eq)))

once-symbol-own-≢ : ∀ (x y : String)
  → ValidIdent x → ValidIdent y
  → x ≢ y → once-symbol-own x ≢ once-symbol-own y
once-symbol-own-≢ x y vx vy x≢y eq = x≢y (once-symbol-own-injective x y vx vy eq)
