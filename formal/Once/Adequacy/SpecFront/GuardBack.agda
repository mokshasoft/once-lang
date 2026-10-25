-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.GuardBack — the extractor's name guard admits
-- what the Spec reads (plan 0.121 `complete`; the converse of
-- `NameClash.guard-entries`).
--
-- `guardDistinct` admits a list of entries, the FFI declarations' first,
-- whose names are distinct and whose definitions are named by identifiers
-- or operators (`guard←`). The Spec gives both: its definitions' names are
-- distinct (the walk's naming is injective, `walk-distinct`), its
-- declarations' names are (`OneName`, rendered apart: `rnames-distinct`), no
-- definition is named as a declaration (`def-not-sig`), and the rendered
-- name of a declaration starts with an identifier's first character, which
-- no operator's does (`op-not-ident`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.GuardBack where

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.Char using (Char)
import Data.Char.Properties as CharP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; tabulate; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-tabulate⁻; ∈-map⁺)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
import Data.Nat.Properties as NatP
open import Data.Nat using (_≡ᵇ_)
import Data.Char
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Injective)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (dec-true)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Postulates using (toList-++)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Signature using (Signature; Decl; _∶_; OneName)
import Once.Spec.Surface.Syntax as S
import Once.Spec.Surface.Program as SPr
open import Once.Internal.Name using (showCanonical; WordName)
import Once.Parser as Parser
open import Once.Parser using (Entry; e-fun; e-poly; mkFunInfo; FunInfo; PolyFunInfo; guardDistinct; namesDistinct; allValidNameB;
                               validNameB; validCharsB; opCharsB; allOpNameChars; emittedNames; funsOf; polysOf; entryNameOf)
open import Once.Parser.Lexer using (isIdentStart; isOpNameChar; opNameChars)
import Once.Parser.Module.Core as PC
open import Once.Spec.Surface.Syntax using (DTypeSig; DFunDef; DSignature; DTypeAlias; DImport)
open import Once.Adequacy.SpecFront.Extract using (XAlign; xa-nil; xa-pass; xa-mono; xa-poly; xa-nosig; xa-sig; IsSig; is-sig; FFIEntry)
open import Once.Adequacy.SpecFront.Render using (render-inj)
open import Once.Adequacy.SpecFront.Words using (Ident; DefName; IdentName; KeysI; KeysW; ident-word; DeclW)
open import Once.Adequacy.SpecFront.SigFacts using (rname)

private
  ∧-l : ∀ {a b} → T (a ∧ b) → T a
  ∧-l {true} _ = tt

  ∧-r : ∀ {a b} → T (a ∧ b) → T b
  ∧-r {true} t = t

  T⇒≡ : ∀ {b} → T b → b ≡ true
  T⇒≡ {true} _ = refl

  ∧-true : ∀ {a b} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
  ∧-true refl refl = refl

------------------------------------------------------------------------
-- Distinct lists
------------------------------------------------------------------------

private
  ≢-sym : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  ≢-sym n e = n (sym e)

  all-pre : ∀ {A : Set} {P : A → Set} xs {ys} → All P (xs ++ ys) → All P xs
  all-pre []       _        = []
  all-pre (x ∷ xs) (p ∷ ps) = p ∷ all-pre xs ps

  all-ins : ∀ {A : Set} {P : A → Set} (xs : List A) {ys n} → P n → All P (xs ++ ys) → All P (xs ++ n ∷ ys)
  all-ins []       p ps       = p ∷ ps
  all-ins (x ∷ xs) p (q ∷ ps) = q ∷ all-ins xs p ps

  ap-pre : ∀ {A : Set} (xs : List A) {ys} → AllPairs _≢_ (xs ++ ys) → AllPairs _≢_ xs
  ap-pre []       _       = []
  ap-pre (x ∷ xs) (a ∷ u) = all-pre xs a ∷ ap-pre xs u

  ap-ins : ∀ {A : Set} (xs : List A) {ys n} → All (n ≢_) (xs ++ ys) → AllPairs _≢_ (xs ++ ys) → AllPairs _≢_ (xs ++ n ∷ ys)
  ap-ins []       a       u       = a ∷ u
  ap-ins (x ∷ xs) (h ∷ a) (b ∷ u) = all-ins xs (≢-sym h) b ∷ ap-ins xs a u

  ap-++ : ∀ {A : Set} (xs : List A) {ys} → AllPairs _≢_ xs → AllPairs _≢_ ys → All (λ x → All (x ≢_) ys) xs
        → AllPairs _≢_ (xs ++ ys)
  ap-++ []       _       v _       = v
  ap-++ (x ∷ xs) (a ∷ u) v (d ∷ ds) = all-++ a d ∷ ap-++ xs u v ds
    where
      all-++ : ∀ {P : _ → Set} {as bs} → All P as → All P bs → All P (as ++ bs)
      all-++ []       q = q
      all-++ (p ∷ ps) q = p ∷ all-++ ps q

  -- a list, reversed onto another: its pairs are the two lists' and across
  ap-ʳ++ : ∀ {A : Set} (xs : List A) {acc} → AllPairs _≢_ (xs ʳ++ acc)
         → AllPairs _≢_ xs × AllPairs _≢_ acc × All (λ x → All (x ≢_) acc) xs
  ap-ʳ++ []       u = [] , u , []
  ap-ʳ++ (x ∷ xs) u = step (ap-ʳ++ xs u)
    where
      step : _ → _
      step (uxs , (a ∷ uacc) , d) = All.map (λ { (h ∷ _) → ≢-sym h }) d ∷ uxs , uacc , a ∷ All.map (λ { (_ ∷ t) → t }) d

  ap-map⁻ : ∀ {A B : Set} (f : A → B) (xs : List A) → AllPairs _≢_ (map f xs) → AllPairs _≢_ xs
  ap-map⁻ f []       []      = []
  ap-map⁻ f (x ∷ xs) (a ∷ u) = ne xs a ∷ ap-map⁻ f xs u
    where
      ne : ∀ ys → All (f x ≢_) (map f ys) → All (x ≢_) ys
      ne []       []      = []
      ne (y ∷ ys) (n ∷ a′) = (λ e → n (cong f e)) ∷ ne ys a′

  mem-ʳ++ : ∀ {A : Set} (xs : List A) {acc x} → x ∈ xs ⊎ x ∈ acc → x ∈ (xs ʳ++ acc)
  mem-ʳ++ []       (inj₂ m)          = m
  mem-ʳ++ (y ∷ xs) (inj₁ (here e))   = mem-ʳ++ xs (inj₂ (here e))
  mem-ʳ++ (y ∷ xs) (inj₁ (there m))  = mem-ʳ++ xs (inj₁ m)
  mem-ʳ++ (y ∷ xs) (inj₂ m)          = mem-ʳ++ xs (inj₂ (there m))

-- `namesDistinct` decides distinctness.
distinct-true : ∀ xs → AllPairs _≢_ xs → namesDistinct xs ≡ true
distinct-true xs u = dec-true (Data.List.Relation.Unary.AllPairs.allPairs? (λ x y → Relation.Nullary.¬? (x Data.String.≟ y)) xs) u
  where import Data.List.Relation.Unary.AllPairs ; import Relation.Nullary ; import Data.String

valid-true : ∀ {xs} → All DefName xs → allValidNameB xs ≡ true
valid-true []       = refl
valid-true (v ∷ vs) = ∧-true (T⇒≡ v) (valid-true vs)

------------------------------------------------------------------------
-- The guard
------------------------------------------------------------------------

-- A definition's entry: not an FFI declaration.
data DefEntry : Entry → Set where
  de-fun  : ∀ {x t b} → DefEntry (e-fun (mkFunInfo x t b false))
  de-poly : ∀ {p}     → DefEntry (e-poly p)

names : List Entry → List String
names = map entryNameOf

private
  -- (what the guard reads off a list of entries)
  E P : List Entry → List String
  E es = emittedNames (funsOf es)
  P es = map PolyFunInfo.pfunName (polysOf es)

  ffi-E : ∀ fs ds → All FFIEntry fs → E (fs ++ ds) ≡ E ds
  ffi-E []                                ds []          = refl
  ffi-E (e-fun (mkFunInfo _ _ _ .true) ∷ fs) ds (refl ∷ a) = ffi-E fs ds a
  ffi-E (e-poly _ ∷ fs)                   ds (() ∷ a)

  ffi-P : ∀ fs ds → All FFIEntry fs → P (fs ++ ds) ≡ P ds
  ffi-P []              ds []      = refl
  ffi-P (e-fun _ ∷ fs)  ds (_ ∷ a) = ffi-P fs ds a
  ffi-P (e-poly _ ∷ fs) ds (() ∷ a)

  -- the emitted and the telescope's names are the definitions'
  sub : ∀ {Q : String → Set} ds → All DefEntry ds → All Q (names ds) → All Q (E ds ++ P ds)
  sub []                        []             []      = []
  sub (e-fun _ ∷ ds)            (de-fun ∷ a)   (q ∷ qs) = q ∷ sub ds a qs
  sub (e-poly _ ∷ ds)           (de-poly ∷ a)  (q ∷ qs) = all-ins (E ds) q (sub ds a qs)

  sub-distinct : ∀ ds → All DefEntry ds → AllPairs _≢_ (names ds) → AllPairs _≢_ (E ds ++ P ds)
  sub-distinct []              []            []      = []
  sub-distinct (e-fun _ ∷ ds)  (de-fun ∷ a)  (h ∷ u) = sub ds a h ∷ sub-distinct ds a u
  sub-distinct (e-poly _ ∷ ds) (de-poly ∷ a) (h ∷ u) = ap-ins (E ds) (sub ds a h) (sub-distinct ds a u)

  dist-ok : ∀ b m r → b ≡ true → Parser.distinctOrErr b m r ≡ r
  dist-ok .true m r refl = refl

-- The guard admits FFI declarations followed by definitions, all named apart,
-- the definitions by identifiers or operators.
guard← : ∀ fs ds → All FFIEntry fs → All DefEntry ds → AllPairs _≢_ (names (fs ++ ds)) → All DefName (names ds)
       → guardDistinct (inj₂ (fs ++ ds)) ≡ inj₂ (fs ++ ds)
guard← fs ds ff de u v =
  dist-ok _ _ (inj₂ (fs ++ ds))
    (∧-true (∧-true (∧-true (distinct-true (E es) (subst (AllPairs _≢_) (sym eE) (ap-pre (E ds) ed)))
                            (valid-true (subst (All DefName) (sym eE) (all-pre (E ds) (sub ds de v)))))
                    (distinct-true (E es ++ P es) (subst (AllPairs _≢_) (sym (cong₂ _++_ eE eP)) ed)))
            (distinct-true (names es) u))
  where
    es = fs ++ ds
    eE = ffi-E fs ds ff
    eP = ffi-P fs ds ff
    ud : AllPairs _≢_ (names ds)
    ud = proj₂ (split (names fs) (subst (AllPairs _≢_) (map-++ entryNameOf fs ds) u))
      where
        split : ∀ xs {ys} → AllPairs _≢_ (xs ++ ys) → AllPairs _≢_ xs × AllPairs _≢_ ys
        split []       v′      = [] , v′
        split (x ∷ xs) (a ∷ w) = let (p , q) = split xs w in all-pre xs a ∷ p , q
    ed = sub-distinct ds de ud

------------------------------------------------------------------------
-- Names apart, by their characters
------------------------------------------------------------------------

private
  true≢false : true ≡ false → ⊥
  true≢false ()

  any-eq : ∀ h ks → T (any (λ k → Once.Parser.Lexer.toNat h ≡ᵇ Once.Parser.Lexer.toNat k) ks) → Σ[ k ∈ Char ] (k ∈ ks) × (h ≡ k)
  any-eq h []       ()
  any-eq h (k ∷ ks) t = go (Once.Parser.Lexer.toNat h ≡ᵇ Once.Parser.Lexer.toNat k) refl t
    where
      go : ∀ b → (Once.Parser.Lexer.toNat h ≡ᵇ Once.Parser.Lexer.toNat k) ≡ b
         → T (b ∨ any (λ k′ → Once.Parser.Lexer.toNat h ≡ᵇ Once.Parser.Lexer.toNat k′) ks) → Σ[ k′ ∈ Char ] (k′ ∈ k ∷ ks) × (h ≡ k′)
      go true  e _ = k , here refl , CharP.≈⇒≡ (NatP.≡ᵇ⇒≡ (Data.Char.toℕ h) (Data.Char.toℕ k) (subst T (sym e) tt))
      go false _ t′ = let (k′ , m , e′) = any-eq h ks t′ in k′ , there m , e′

  ops-not-start : All (λ k → isIdentStart k ≡ false) opNameChars
  ops-not-start = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []

-- No operator character starts an identifier.
op-not-ident : ∀ h → T (isOpNameChar h) → T (isIdentStart h) → ⊥
op-not-ident h o i =
  let (k , m , e) = any-eq h opNameChars o
  in true≢false (trans (sym (T⇒≡ (subst (λ c → T (isIdentStart c)) e i))) (All.lookup ops-not-start m))

private
  ident-head : ∀ x → Ident x → Σ[ h ∈ Char ] Σ[ t ∈ List Char ] (toList x ≡ h ∷ t) × T (isIdentStart h)
  ident-head x i = go (toList x) refl i
    where
      go : ∀ cs → toList x ≡ cs → T (validCharsB cs) → Σ[ h ∈ Char ] Σ[ t ∈ List Char ] (toList x ≡ h ∷ t) × T (isIdentStart h)
      go []       _ ()
      go (c ∷ cs) e v = c , cs , e , ∧-l v

  render-head : ∀ x xs {h t} → toList x ≡ h ∷ t → Σ[ t′ ∈ List Char ] toList (showCanonical (canonical (x ∷ xs))) ≡ h ∷ t′
  render-head x []       e = _ , e
  render-head x (y ∷ ys) e = _ , trans (toList-++ x _) (cong (_++ toList ("." Data.String.++ showCanonical (canonical (y ∷ ys)))) e)

  or-split : ∀ a b → T (a ∨ b) → T a ⊎ T b
  or-split true  b t = inj₁ tt
  or-split false b t = inj₂ t

  op-head : ∀ cs → T (opCharsB cs) → Σ[ h ∈ Char ] Σ[ t ∈ List Char ] (cs ≡ h ∷ t) × T (isOpNameChar h)
  op-head []       ()
  op-head (c ∷ cs) o = c , cs , refl , ∧-l o

-- A definition's name is no declaration's rendered name.
def-not-key : ∀ {Σ : Signature} {d y} → d ∈ Σ → IdentName (Decl.name d) → WordName (Decl.name d) → DefName y
            → (∀ {t} → ¬ ((canonical (y ∷ []) ∶ t) ∈ Σ)) → rname d ≢ y
def-not-key {Σ} {canonical [] ∶ t} m (_ , ne) _ _ _ _ = ne refl
def-not-key {Σ} {canonical (x ∷ xs) ∶ t} {y} m (ix ∷ _ , _) wc dy ns e = cases (or-split (validCharsB (toList y)) (opCharsB (toList y)) dy)
  where
    cases : Ident y ⊎ T (opCharsB (toList y)) → ⊥
    cases (inj₁ iy) = ns (subst (λ c → (c ∶ t) ∈ Σ) (render-inj (canonical (x ∷ xs)) (canonical (y ∷ [])) wc (ident-step iy) e) m)
      where
        ident-step : Ident y → WordName (canonical (y ∷ []))
        ident-step i = subst T (sym (Data.Bool.Properties.∧-identityʳ _)) (ident-word {y} i)
          where import Data.Bool.Properties
    cases (inj₂ oy) =
      let (h , tl , ex , sx) = ident-head x ix
          (t′ , er) = render-head x xs ex
          (h′ , tl′ , ey , oh) = op-head (toList y) oy
          hh = proj₁ (Data.List.Properties.∷-injective (trans (sym er) (trans (cong toList e) ey)))
      in op-not-ident h′ oh (subst (λ c → T (isIdentStart c)) hh sx)
      where import Data.List.Properties

-- Σ's declarations render apart.
rnames-distinct : ∀ {Σ : Signature} → KeysW Σ → OneName Σ → AllPairs _≢_ (map rname Σ)
rnames-distinct {[]}    []       []      = []
rnames-distinct {d ∷ Σ} (k ∷ ks) (h ∷ u) = go Σ ks h ∷ rnames-distinct ks u
  where
    go : ∀ Σ′ → KeysW Σ′ → All (Decl.name d ≢_) (map Decl.name Σ′) → All (rname d ≢_) (map rname Σ′)
    go []        []        []       = []
    go (d′ ∷ Σ′) (k′ ∷ ks′) (n ∷ a) = (λ e → n (render-inj _ _ k k′ e)) ∷ go Σ′ ks′ a

------------------------------------------------------------------------
-- The definitions' names
------------------------------------------------------------------------

-- The names a list of Spec declarations defines, in order…
defNamesS : List S.Decl → List String
defNamesS []                         = []
defNamesS (S.DFunDef x _ ∷ ds)       = x ∷ defNamesS ds
defNamesS (S.DTypeSig _ _ ∷ ds)      = defNamesS ds
defNamesS (S.DSignature _ _ ∷ ds)    = defNamesS ds
defNamesS (S.DTypeAlias _ _ _ ∷ ds)  = defNamesS ds
defNamesS (S.DImport _ ∷ ds)         = defNamesS ds

-- …and of the compiler's.
defNamesC : List S.Decl → List String
defNamesC []                        = []
defNamesC (DFunDef x _ ∷ ds)        = x ∷ defNamesC ds
defNamesC (DTypeSig _ _ ∷ ds)       = defNamesC ds
defNamesC (DSignature _ _ ∷ ds)   = defNamesC ds
defNamesC (DTypeAlias _ _ _ ∷ ds)   = defNamesC ds
defNamesC (DImport _ ∷ ds)          = defNamesC ds

private
  own : String → CanonicalName
  own x = canonical (x ∷ [])

-- The walk names its definitions, in reverse, before the names it starts from.
walk-tab : ∀ {Σ s} {S : _} {nm : Fin s → CanonicalName} {tl ds s′} {S′ : _} {nm′ : Fin s′ → CanonicalName} {tl′}
         → SPr.Walk Σ S nm tl ds S′ nm′ tl′ → tabulate nm′ ≡ map own (defNamesS ds) ʳ++ tabulate nm
walk-tab SPr.w-end                    = refl
walk-tab (SPr.w-skip SPr.nd-sig w)    = walk-tab w
walk-tab (SPr.w-skip SPr.nd-alias w)  = walk-tab w
walk-tab (SPr.w-skip SPr.nd-import w) = walk-tab w
walk-tab (SPr.w-sig _ _ _ w)          = walk-tab w
walk-tab (SPr.w-nosig _ _ _ w)        = walk-tab w

-- A program's definitions are named apart…
walk-distinct : ∀ {Σ ds s′} {S′ : _} {nm′ : Fin s′ → CanonicalName} {tl′} {S₀ : _} {nm₀ : Fin 0 → CanonicalName} {tl₀}
              → SPr.Walk Σ S₀ nm₀ tl₀ ds S′ nm′ tl′ → Injective _≡_ _≡_ nm′ → AllPairs _≢_ (defNamesS ds)
walk-distinct {ds = ds} w inj =
  ap-map⁻ own (defNamesS ds) (proj₁ (ap-ʳ++ (map own (defNamesS ds)) (subst (AllPairs _≢_) (walk-tab w) (UniqueP.tabulate⁺ inj))))

-- …and none as a declaration of Σ.
walk-named : ∀ {Σ ds s′} {S′ : _} {nm′ : Fin s′ → CanonicalName} {tl′} {S₀ : _} {nm₀ : Fin 0 → CanonicalName} {tl₀}
           → SPr.Walk Σ S₀ nm₀ tl₀ ds S′ nm′ tl′ → (∀ i {t} → ¬ ((nm′ i ∶ t) ∈ Σ))
           → All (λ y → ∀ {t} → ¬ ((own y ∶ t) ∈ Σ)) (defNamesS ds)
walk-named {Σ} {ds} w ns = All.tabulate at
  where
    at : ∀ {y} → y ∈ defNamesS ds → ∀ {t} → ¬ ((own y ∶ t) ∈ Σ)
    at {y} m {t} M =
      let m′ = subst (own y ∈_) (sym (walk-tab w)) (mem-ʳ++ (map own (defNamesS ds)) (inj₁ (∈-map⁺ own m)))
          (i , e) = ∈-tabulate⁻ m′
      in ns i (subst (λ c → (c ∶ t) ∈ Σ) e M)

-- The Spec's resolution keeps the definitions' names.
res-names : ∀ {E ds ds′} → SPr.ResolvesDecls E ds ds′ → defNamesS ds′ ≡ defNamesS ds
res-names SPr.rd-nil                  = refl
res-names (SPr.rd-def _ rd)           = cong (_ ∷_) (res-names rd)
res-names (SPr.rd-other SPr.nf-sig rd)    = res-names rd
res-names (SPr.rd-other SPr.nf-tsig rd)   = res-names rd
res-names (SPr.rd-other SPr.nf-alias rd)  = res-names rd
res-names (SPr.rd-other SPr.nf-import rd) = res-names rd

-- A module the Spec parses names its definitions by identifiers or operators.
def-names : ∀ {ds} → All DeclW ds → All DefName (defNamesS ds)
def-names {[]}                      []       = []
def-names {S.DFunDef _ _ ∷ ds}      (w ∷ ws) = w ∷ def-names ws
def-names {S.DTypeSig _ _ ∷ ds}     (_ ∷ ws) = def-names ws
def-names {S.DSignature _ _ ∷ ds}   (_ ∷ ws) = def-names ws
def-names {S.DTypeAlias _ _ _ ∷ ds} (_ ∷ ws) = def-names ws
def-names {S.DImport _ ∷ ds}        (_ ∷ ws) = def-names ws

-- The definitions' entries, by name.
xa-names : ∀ {ds es} → XAlign ds es → All (λ d → ¬ IsSig d) ds → All DefEntry es × (names es ≡ defNamesC ds)
xa-names xa-nil []                                  = [] , refl
xa-names (xa-pass Once.Adequacy.SpecFront.Extract.pa-alias xa)  (_ ∷ ns) = xa-names xa ns
xa-names (xa-pass Once.Adequacy.SpecFront.Extract.pa-import xa) (_ ∷ ns) = xa-names xa ns
xa-names (xa-mono _ xa)  (_ ∷ _ ∷ ns) = let (a , e) = xa-names xa ns in de-fun ∷ a , cong (_ ∷_) e
xa-names (xa-poly _ xa)  (_ ∷ _ ∷ ns) = let (a , e) = xa-names xa ns in de-poly ∷ a , cong (_ ∷_) e
xa-names (xa-nosig xa)   (_ ∷ ns)     = let (a , e) = xa-names xa ns in de-fun ∷ a , cong (_ ∷_) e
xa-names (xa-sig _ _)    (n ∷ _)      = ⊥-elim (n is-sig)

nonSigs-names : ∀ ds → defNamesC (Parser.nonSigs ds) ≡ defNamesC ds
nonSigs-names []                       = refl
nonSigs-names (DFunDef _ _ ∷ ds)       = cong (_ ∷_) (nonSigs-names ds)
nonSigs-names (DTypeSig _ _ ∷ ds)      = nonSigs-names ds
nonSigs-names (DSignature _ _ ∷ ds)  = nonSigs-names ds
nonSigs-names (DTypeAlias _ _ _ ∷ ds)  = nonSigs-names ds
nonSigs-names (DImport _ ∷ ds)         = nonSigs-names ds

module _ (Σ : Signature) where
  open import Once.Adequacy.SpecFront.Align Σ using (DR; dr-nil; dr-tsig; dr-def; dr-sig; dr-import; dr-alias)

  -- The compiler's resolved declarations define the Spec's names.
  dr-names : ∀ {ds dc} → DR ds dc → defNamesC dc ≡ defNamesS ds
  dr-names dr-nil            = refl
  dr-names (dr-tsig dr)      = dr-names dr
  dr-names (dr-def _ dr)     = cong (_ ∷_) (dr-names dr)
  dr-names (dr-sig dr)       = dr-names dr
  dr-names (dr-import dr)   = dr-names dr
  dr-names (dr-alias dr)     = dr-names dr
