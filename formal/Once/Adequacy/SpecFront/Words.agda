-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Words — the names a Spec program's signature
-- declares are word names, so the compiler's rendered keys find them
-- (plan 0.121 R13, D329).
--
-- The Spec's lexer makes a word token of an identifier (`lex-words`, by
-- T2), and an identifier has no `.`, so it is a word; a parse only reads
-- tokens off the front (`SpecGrammar.Suffix`), so every `signature` name and
-- import path it reads is made of identifiers, and every definition it reads
-- is named by an identifier or an operator's characters (`decls-words`); so
-- every key of the signature is made of identifiers (`signature-idents`),
-- and of words (`signature-words`). A generator the compiler finds by the
-- rendered name of a word name is then Σ's declaration of that name
-- (`r13-at`, by `render-inj`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Words where

open import Data.Bool using (Bool; true; false; T; not; _∧_)
open import Data.Char using (Char; _≈ᵇ_)
import Data.Char.Properties as CharP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.List using (reverse; _ʳ++_)
open import Data.Bool using (_∨_)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Parser using (validCharsB; allIdentContinue; validNameB; opCharsB; allOpNameChars)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Postulates using (toList∘fromList)
open import Once.Spec.Signature using (Signature; Decl; _∶_)
open import Once.Spec.Surface.Lexing
open import Once.Spec.Surface.Syntax using (DSignature; DImport; DTypeSig; DFunDef; DTypeAlias; mkImport; Module)
import Once.Spec.Surface.Syntax as SX
open import Once.Spec.Surface.Grammar as G
  using (Parses; ParsesDecls; decls-stop; decls-cons; ParsesDecl; decl-import; decl-alias; decl-signature;
         decl-typesig; decl-fundef; decl-op; ParsesImport; import-as; import-plain;
         ParsesModulePath; path-cons; path-dotstop; path-end)
open import Once.Spec.Surface.Resolution using (ModuleMap; FirstAt; fa-here; fa-there; Expands; ex-nil; ex-I; ex-other)
open import Once.Spec.Surface.Program using (SignatureOf; SignaturesOf; so-nil; so-sig; so-other; Imported; im-nil; im-import; im-other)
open import Once.Spec.Source using (ParsesModules)
open import Once.Name using (showCanonical; noDotB; wordCharsB; wordB; wordsB; WordName)
open import Once.Adequacy.SpecInterp using (declTy)
open import Once.Core.Decl using (toISig)
open import Once.Core.Decl using (declS)
open import Once.Adequacy.SpecCore.DeclType using (declS-declTy)
open import Once.Adequacy.SpecGrammar.Suffix using (All-⊒)
import Once.Adequacy.SpecGrammar.Suffix as Suf
import Once.Parser.Lexer
open import Once.Adequacy.SpecFront.Render using (render-inj)

------------------------------------------------------------------------
-- The lexer's words
------------------------------------------------------------------------

Word : String → Set
Word w = T (wordB w)

-- An identifier, as the compiler's lexer makes one.
Ident : String → Set
Ident w = T (validCharsB (toList w))

-- A definition's name: an identifier or an operator's characters.
DefName : String → Set
DefName x = T (validNameB x)

-- What a token says of its names: a word token is an identifier.
TokW : Token → Set
TokW (TWord w) = Ident w
{-# CATCHALL #-}
TokW _         = ⊤

private
  ∧-intro : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ tb = tb

  -- a character a lexer predicate accepts, where it refuses `.`, is not `.`
  not-dot : ∀ (p : Char → Bool) → p '.' ≡ false → ∀ ch → p ch ≡ true → T (not (ch ≈ᵇ '.'))
  not-dot p pd ch pc = go (ch ≈ᵇ '.') refl
    where
      go : ∀ b → (ch ≈ᵇ '.') ≡ b → T (not b)
      go false _ = tt
      go true  e =
        let ch≡ = CharP.≈⇒≡ (NatP.≡ᵇ⇒≡ (Data.Char.toℕ ch) (Data.Char.toℕ '.') (subst T (sym e) tt))
        in ⊥-elim (true≢false (trans (sym pc) (trans (cong p ch≡) pd)))
        where
          true≢false : true ≡ false → ⊥
          true≢false ()

  ∨-introˡ : ∀ {a} b → T a → T (a ∨ b)
  ∨-introˡ {true} _ t = t

  ∨-introʳ : ∀ a {b} → T b → T (a ∨ b)
  ∨-introʳ true  _ = tt
  ∨-introʳ false t = t

  ∧-l : ∀ {a b} → T (a ∧ b) → T a
  ∧-l {true} _ = tt

  ∧-r : ∀ {a b} → T (a ∧ b) → T b
  ∧-r {true} t = t

  T-≡ : ∀ {b} → b ≡ true → T b
  T-≡ refl = tt

  rest-ident : ∀ {cs i r} → IdentRest cs i r → T (allIdentContinue i)
  rest-ident id-end         = tt
  rest-ident (id-stop _)    = tt
  rest-ident (id-more c p)  = ∧-intro (T-≡ c) (rest-ident p)

  ident-tok : ∀ {c cs i r} → isIdentStart c ≡ true → IdentRest cs i r → Ident (fromList (c ∷ i))
  ident-tok {c} {i = i} s p =
    subst (λ l → T (validCharsB l)) (sym (toList∘fromList (c ∷ i))) (∧-intro (T-≡ s) (rest-ident p))

  conts-nd : ∀ cs → T (allIdentContinue cs) → T (noDotB cs)
  conts-nd []       _ = tt
  conts-nd (c ∷ cs) a = ∧-intro (not-dot isIdentContinue refl c (T⇒≡ (∧-l a))) (conts-nd cs (∧-r a))
    where
      T⇒≡ : ∀ {b} → T b → b ≡ true
      T⇒≡ {true} _ = refl

-- An identifier is a word.
ident-word : ∀ {w} → Ident w → Word w
ident-word {w} i = go (toList w) i
  where
    go : ∀ cs → T (validCharsB cs) → T (wordCharsB cs)
    go []       ()
    go (c ∷ cs) a = ∧-intro (not-dot isIdentStart refl c (T⇒≡ (∧-l a))) (conts-nd cs (∧-r a))
      where
        T⇒≡ : ∀ {b} → T b → b ≡ true
        T⇒≡ {true} _ = refl

-- Every word the Spec's lexer makes is a word.
lex-words : ∀ {cs ts} → LexesChars cs ts → All TokW ts
lex-words lex-eof                    = tt ∷ []
lex-words (lex-space l)              = lex-words l
lex-words (lex-tab l)                = lex-words l
lex-words (lex-cr l)                 = lex-words l
lex-words (lex-nl-cont _ _ l)        = lex-words l
lex-words (lex-nl _ _ l)             = tt ∷ lex-words l
lex-words (lex-caret1 l)             = tt ∷ lex-words l
lex-words (lex-caret0 l)             = tt ∷ lex-words l
lex-words (lex-caretw l)             = tt ∷ lex-words l
lex-words (lex-caret _ _ _ l)        = lex-words l
lex-words (lex-comment _ l)          = lex-words l
lex-words (lex-arrow l)              = tt ∷ lex-words l
lex-words (lex-minus _ _ l)          = tt ∷ lex-words l
lex-words (lex-block _ l)            = lex-words l
lex-words (lex-lbrace _ l)           = tt ∷ lex-words l
lex-words (lex-le l)                 = tt ∷ lex-words l
lex-words (lex-lt _ l)               = tt ∷ lex-words l
lex-words (lex-ge l)                 = tt ∷ lex-words l
lex-words (lex-gt _ l)               = tt ∷ lex-words l
lex-words (lex-eqeq l)               = tt ∷ lex-words l
lex-words (lex-equal _ l)            = tt ∷ lex-words l
lex-words (lex-neq l)                = tt ∷ lex-words l
lex-words (lex-bang _ l)             = tt ∷ lex-words l
lex-words (lex-lparen l)             = tt ∷ lex-words l
lex-words (lex-rparen l)             = tt ∷ lex-words l
lex-words (lex-rbrace l)             = tt ∷ lex-words l
lex-words (lex-colon l)              = tt ∷ lex-words l
lex-words (lex-lambda l)             = tt ∷ lex-words l
lex-words (lex-comma l)              = tt ∷ lex-words l
lex-words (lex-semi l)               = tt ∷ lex-words l
lex-words (lex-at l)                 = tt ∷ lex-words l
lex-words (lex-pipe l)               = tt ∷ lex-words l
lex-words (lex-plus l)               = tt ∷ lex-words l
lex-words (lex-star l)               = tt ∷ lex-words l
lex-words (lex-slash l)              = tt ∷ lex-words l
lex-words (lex-pct l)                = tt ∷ lex-words l
lex-words (lex-amp l)                = tt ∷ lex-words l
lex-words (lex-dot l)                = tt ∷ lex-words l
lex-words (lex-string _ l)           = tt ∷ lex-words l
lex-words (lex-string-end _)         = []
lex-words (lex-int _ _ _ l)          = tt ∷ lex-words l
lex-words (lex-float _ _ _ l)        = tt ∷ lex-words l
lex-words (lex-ident _ _ s p l)      = ident-tok s p ∷ lex-words l
lex-words (lex-skip _ _ _ l)         = lex-words l

------------------------------------------------------------------------
-- The declarations' names
------------------------------------------------------------------------

-- What a declaration says of the signature's names.
DeclW : SX.Decl → Set
DeclW (DSignature x _)          = Ident x
DeclW (DImport (mkImport p _))  = All Ident p × p ≢ []
DeclW (DTypeSig _ _)            = ⊤
DeclW (DFunDef x _)             = DefName x
DeclW (DTypeAlias _ _ _)        = ⊤

private
  path-words′ : ∀ {ts p r} → ParsesModulePath ts p r → All TokW ts → All Ident p
  path-words′ (path-cons p)    (w ∷ _ ∷ ws) = w ∷ path-words′ p ws
  path-words′ (path-dotstop _) (w ∷ _)      = w ∷ []
  path-words′ (path-end _)     (w ∷ _)      = w ∷ []

  path-words : ∀ {ts p r} → All TokW ts → ParsesModulePath ts p r → All Ident p
  path-words ws p = path-words′ p ws

  import-words : ∀ {ts d r} → All TokW ts → ParsesImport ts d r → DeclW d
  path-ne : ∀ {ts p r} → ParsesModulePath ts p r → p ≢ []
  path-ne (path-cons _)    ()
  path-ne (path-dotstop _) ()
  path-ne (path-end _)     ()

  import-words ws (import-as p)      = path-words ws p , path-ne p
  import-words ws (import-plain p _) = path-words ws p , path-ne p

  alias-words : ∀ {x ps ts d r} → G.ParsesTypeAlias x ps ts d r → DeclW d
  alias-words (G.alias-eq _)    = tt
  alias-words (G.alias-param p) = alias-words p

  fundef-words : ∀ {x ts d r} → DefName x → G.ParsesFunDef x ts d r → DeclW d
  fundef-words n (G.fundef _ _) = n

  -- an operator's characters
  oc-op : ∀ {t ch} → G.OpChar t ch → T (Once.Parser.Lexer.isOpNameChar ch)
  oc-op G.oc-dot   = tt
  oc-op G.oc-plus  = tt
  oc-op G.oc-minus = tt
  oc-op G.oc-star  = tt
  oc-op G.oc-slash = tt
  oc-op G.oc-pct   = tt
  oc-op G.oc-lt    = tt
  oc-op G.oc-gt    = tt
  oc-op G.oc-pipe  = tt
  oc-op G.oc-amp   = tt
  oc-op G.oc-at    = tt

  ops-ʳ++ : ∀ xs {acc} → T (allOpNameChars xs) → T (allOpNameChars acc) → T (allOpNameChars (xs ʳ++ acc))
  ops-ʳ++ []       _ a = a
  ops-ʳ++ (x ∷ xs) o a = ops-ʳ++ xs (∧-r o) (∧-intro (∧-l o) a)

  op-name : ∀ {ts cs x r} → G.ParsesOpChars ts cs x r → T (allOpNameChars cs) → DefName x
  op-name (G.op-close {c} {cs}) o =
    ∨-introʳ (validCharsB (toList (fromList (reverse (c ∷ cs)))))
      (subst (λ l → T (opCharsB l)) (sym (toList∘fromList (reverse (c ∷ cs))))
        (ops-ne cs (ops-ʳ++ cs (∧-r o) (∧-intro (∧-l o) tt))))
    where
      -- (`reverse (c ∷ cs)` is `cs ʳ++ (c ∷ [])`, a cons)
      ops-ne : ∀ ys {a as} → T (allOpNameChars (ys ʳ++ (a ∷ as))) → T (opCharsB (ys ʳ++ (a ∷ as)))
      ops-ne []       t = t
      ops-ne (y ∷ ys) t = ops-ne ys t
  op-name (G.op-char oc p) o = op-name p (∧-intro (oc-op oc) o)

  decl-words′ : ∀ {ts d r} → ParsesDecl ts d r → All TokW ts → DeclW d
  decl-words′ (decl-import p)            (_ ∷ ws)    = import-words ws p
  decl-words′ (decl-alias p)             _           = alias-words p
  decl-words′ (decl-signature _)         (_ ∷ w ∷ _) = w
  decl-words′ (decl-typesig _ _ _)       _           = tt
  decl-words′ (decl-fundef _ _ p)        (w ∷ _)     = fundef-words (∨-introˡ _ w) p
  decl-words′ (decl-op _ (G.op-sig _))   _           = tt
  decl-words′ (decl-op o (G.op-def _ p)) _           = fundef-words (op-name o tt) p

  decl-words : ∀ {ts d r} → All TokW ts → ParsesDecl ts d r → DeclW d
  decl-words ws d = decl-words′ d ws

  decls-words′ : ∀ {ts ds r} → All TokW ts → ParsesDecls ts ds r → All DeclW ds
  decls-words′ ws (decls-stop _ _)    = []
  decls-words′ ws (decls-cons k d ds) =
    let ws₁ = All-⊒ ws (Suf.skip k)
    in decl-words ws₁ d ∷ decls-words′ (All-⊒ ws₁ (Suf.decl d)) ds

-- A module the Spec parses declares word names.
decls-words : ∀ {txt m} → Parses txt m → All DeclW (Module.decls m)
decls-words (_ , _ , lx , pd , _) = decls-words′ (lex-words lx) pd

-- So does every module of a compilation unit.
ModsW : ModuleMap → Set
ModsW = All (λ e → All DeclW (Module.decls (proj₂ e)))

mods-words : ∀ {ms mm} → ParsesModules ms mm → ModsW mm
mods-words []                  = []
mods-words {(_ , txt) ∷ _} {(_ , m) ∷ _} ((_ , pm) ∷ pms) = decls-words {txt} {m} pm ∷ mods-words pms

------------------------------------------------------------------------
-- The signature's keys
------------------------------------------------------------------------

-- A name made of identifiers.
IdentName : CanonicalName → Set
IdentName (canonical xs) = All Ident xs × xs ≢ []

KeysI : Signature → Set
KeysI = All (λ d → IdentName (Decl.name d))

KeysW : Signature → Set
KeysW = All (λ d → WordName (Decl.name d))

private
  ++-all : ∀ {Σ₁ Σ₂ : Signature} → KeysI Σ₁ → KeysI Σ₂ → KeysI (Σ₁ ++ Σ₂)
  ++-all []       k₂ = k₂
  ++-all (k ∷ k₁) k₂ = k ∷ ++-all k₁ k₂

  idents-++ : ∀ (p : List String) {x} → All Ident p → Ident x → IdentName (canonical (p ++ x ∷ []))
  idents-++ []      []       i = i ∷ [] , λ ()
  idents-++ (y ∷ p) (j ∷ jp) i = j ∷ proj₁ (idents-++ p jp i) , λ ()

  sigs-idents : ∀ {path ds Σ} → All Ident path → All DeclW ds → SignaturesOf path ds Σ → KeysI Σ
  sigs-idents wp _        so-nil                    = []
  sigs-idents {path} wp (w ∷ ws) (so-sig {x = x} _ so) = idents-++ path wp w ∷ sigs-idents wp ws so
  sigs-idents wp (_ ∷ ws) (so-other _ so)            = sigs-idents wp ws so

  first-words : ∀ {p m mm} → ModsW mm → FirstAt p m mm → All DeclW (Module.decls m)
  first-words (w ∷ _)  fa-here        = w
  first-words (_ ∷ ws) (fa-there _ f) = first-words ws f

  expand-idents′ : ∀ {p p′} → Expands p p′ → All Ident p → All Ident p′
  expand-idents′ ex-nil       []       = []
  expand-idents′ ex-I         (_ ∷ ws) = tt ∷ ws
  expand-idents′ (ex-other _) ws       = ws

  expand-idents : ∀ {p p′} → All Ident p → Expands p p′ → All Ident p′
  expand-idents ws ex = expand-idents′ ex ws

  imp-idents : ∀ {mm ds Σ} → ModsW mm → All DeclW ds → Imported mm ds Σ → KeysI Σ
  imp-idents wm _        im-nil                  = []
  imp-idents wm ((wp , _) ∷ ws) (im-import f ex so im) =
    ++-all (sigs-idents (expand-idents wp ex) (first-words wm f) so) (imp-idents wm ws im)
  imp-idents wm (_ ∷ ws) (im-other _ im)         = imp-idents wm ws im

  idents-words : ∀ xs → All Ident xs → T (wordsB xs)
  idents-words []       []       = tt
  idents-words (x ∷ xs) (i ∷ is) = ∧-intro (ident-word {x} i) (idents-words xs is)

  keys-words : ∀ {Σ} → KeysI Σ → KeysW Σ
  keys-words []                                    = []
  keys-words {(canonical xs ∶ _) ∷ _} ((is , _) ∷ ks) = idents-words xs is ∷ keys-words ks

-- Every key of the program's signature is made of identifiers…
signature-idents : ∀ {mm ds Σ} → ModsW mm → All DeclW ds → SignatureOf mm ds Σ → KeysI Σ
signature-idents wm wd (_ , _ , so , im , refl) = ++-all (sigs-idents [] wd so) (imp-idents wm wd im)

-- …so it is a word name.
signature-words : ∀ {mm ds Σ} → ModsW mm → All DeclW ds → SignatureOf mm ds Σ → KeysW Σ
signature-words wm wd s = keys-words (signature-idents wm wd s)

------------------------------------------------------------------------
-- R13: the rendered key of a word name finds its declaration
------------------------------------------------------------------------

-- a declaration of Σ has a word name
key-word : ∀ {Σ : Signature} {d} → KeysW Σ → d ∈ Σ → WordName (Decl.name d)
key-word (k ∷ _)  (here refl) = k
key-word (_ ∷ ks) (there m)   = key-word ks m

private
  -- a compiler declaration of Σ's table is a declaration of Σ
  at-key : ∀ {Σ : Signature} {s A} → (s , A) ∈ toISig Σ
         → Σ[ d ∈ Decl ] (d ∈ Σ) × (showCanonical (Decl.name d) ≡ s) × (declTy (Decl.type d) ≡ A)
  at-key {(c ∶ t) ∷ Σ} (here refl) = (c ∶ t) , here refl , refl , refl
  at-key {_ ∷ Σ}       (there m)   =
    let (d , md , es , eA) = at-key {Σ} m in d , there md , es , eA

r13-at : ∀ {Σ : Signature} → KeysW Σ → ∀ {c A} → WordName c → (showCanonical c , A) ∈ toISig Σ → (c ∶ declS A) ∈ Σ
r13-at {Σ} ks {c} wc mem =
  let ((c′ ∶ t) , md , es , eA) = at-key {Σ} mem
      ec = render-inj c′ c (key-word ks md) wc es
  in subst (λ d → d ∈ Σ) (cong₂∶ ec (trans (sym (declS-declTy t)) (cong declS eA))) md
  where
    cong₂∶ : ∀ {c₁ c₂ t₁ t₂} → c₁ ≡ c₂ → t₁ ≡ t₂ → (c₁ ∶ t₁) ≡ (c₂ ∶ t₂)
    cong₂∶ refl refl = refl
