-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Words — the names a Spec program's signature
-- declares are word names, so the compiler's rendered keys find them
-- (plan 0.121 R13, D329).
--
-- The Spec's lexer makes a word of identifier characters, none of them `.`
-- (`lex-words`, by T2); a parse only reads tokens off the front
-- (`SpecGrammar.Suffix`), so every `signature` name and import path it
-- reads is made of words (`decls-words`), and so is every key of the
-- signature (`signature-words`). A generator the compiler finds by the
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
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.String using (String; toList; fromList)
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
open import Once.Lang.Name using (showCanonical; noDotB; wordCharsB; wordB; wordsB; WordName)
open import Once.Adequacy.SpecInterp using (toISig; declTy)
open import Once.Adequacy.SpecCore.Poly using (declS)
open import Once.Adequacy.SpecCore.DeclType using (declS-declTy)
open import Once.Adequacy.SpecGrammar.Suffix using (All-⊒)
import Once.Adequacy.SpecGrammar.Suffix as Suf
open import Once.Adequacy.SpecFront.Render using (render-inj)

------------------------------------------------------------------------
-- The lexer's words
------------------------------------------------------------------------

Word : String → Set
Word w = T (wordB w)

-- What a token says of its names: a word token is a word.
TokW : Token → Set
TokW (TWord w) = Word w
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

  rest-nd : ∀ {cs i r} → IdentRest cs i r → T (noDotB i)
  rest-nd id-end         = tt
  rest-nd (id-stop _)    = tt
  rest-nd (id-more {c = ch} c p) = ∧-intro (not-dot isIdentContinue refl ch c) (rest-nd p)

  ident-word : ∀ {c cs i r} → isIdentStart c ≡ true → IdentRest cs i r → Word (fromList (c ∷ i))
  ident-word {c} {i = i} s p =
    subst (λ l → T (wordCharsB l)) (sym (toList∘fromList (c ∷ i))) (∧-intro (not-dot isIdentStart refl c s) (rest-nd p))

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
lex-words (lex-ident _ _ s p l)      = ident-word s p ∷ lex-words l
lex-words (lex-skip _ _ _ l)         = lex-words l

------------------------------------------------------------------------
-- The declarations' names
------------------------------------------------------------------------

-- What a declaration says of the signature's names.
DeclW : SX.Decl → Set
DeclW (DSignature x _)          = Word x
DeclW (DImport (mkImport p _))  = All Word p × p ≢ []
DeclW (DTypeSig _ _)            = ⊤
DeclW (DFunDef _ _)             = ⊤
DeclW (DTypeAlias _ _ _)        = ⊤

private
  path-words′ : ∀ {ts p r} → ParsesModulePath ts p r → All TokW ts → All Word p
  path-words′ (path-cons p)    (w ∷ _ ∷ ws) = w ∷ path-words′ p ws
  path-words′ (path-dotstop _) (w ∷ _)      = w ∷ []
  path-words′ (path-end _)     (w ∷ _)      = w ∷ []

  path-words : ∀ {ts p r} → All TokW ts → ParsesModulePath ts p r → All Word p
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

  fundef-words : ∀ {x ts d r} → G.ParsesFunDef x ts d r → DeclW d
  fundef-words (G.fundef _ _) = tt

  decl-words′ : ∀ {ts d r} → ParsesDecl ts d r → All TokW ts → DeclW d
  decl-words′ (decl-import p)            (_ ∷ ws)    = import-words ws p
  decl-words′ (decl-alias p)             _           = alias-words p
  decl-words′ (decl-signature _)         (_ ∷ w ∷ _) = w
  decl-words′ (decl-typesig _ _ _)       _           = tt
  decl-words′ (decl-fundef _ _ p)        _           = fundef-words p
  decl-words′ (decl-op _ (G.op-sig _))   _           = tt
  decl-words′ (decl-op _ (G.op-def _ p)) _           = fundef-words p

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

KeysW : Signature → Set
KeysW = All (λ d → WordName (Decl.name d))

private
  words-++ : ∀ (p q : List String) → All Word p → T (wordsB q) → T (wordsB (p ++ q))
  words-++ []      q []       wq = wq
  words-++ (x ∷ p) q (w ∷ wp) wq = ∧-intro w (words-++ p q wp wq)

  ++-all : ∀ {Σ₁ Σ₂ : Signature} → KeysW Σ₁ → KeysW Σ₂ → KeysW (Σ₁ ++ Σ₂)
  ++-all []       k₂ = k₂
  ++-all (k ∷ k₁) k₂ = k ∷ ++-all k₁ k₂

  sigs-words : ∀ {path ds Σ} → All Word path → All DeclW ds → SignaturesOf path ds Σ → KeysW Σ
  sigs-words wp _        so-nil                    = []
  sigs-words {path} wp (w ∷ ws) (so-sig {x = x} _ so) = words-++ path (x ∷ []) wp (∧-intro w tt) ∷ sigs-words wp ws so
  sigs-words wp (_ ∷ ws) (so-other _ so)            = sigs-words wp ws so

  first-words : ∀ {p m mm} → ModsW mm → FirstAt p m mm → All DeclW (Module.decls m)
  first-words (w ∷ _)  fa-here        = w
  first-words (_ ∷ ws) (fa-there _ f) = first-words ws f

  expand-words′ : ∀ {p p′} → Expands p p′ → All Word p → All Word p′
  expand-words′ ex-nil       []       = []
  expand-words′ ex-I         (_ ∷ ws) = tt ∷ ws
  expand-words′ (ex-other _) ws       = ws

  expand-words : ∀ {p p′} → All Word p → Expands p p′ → All Word p′
  expand-words ws ex = expand-words′ ex ws

  imp-words : ∀ {mm ds Σ} → ModsW mm → All DeclW ds → Imported mm ds Σ → KeysW Σ
  imp-words wm _        im-nil                  = []
  imp-words wm ((wp , _) ∷ ws) (im-import f ex so im) =
    ++-all (sigs-words (expand-words wp ex) (first-words wm f) so) (imp-words wm ws im)
  imp-words wm (_ ∷ ws) (im-other _ im)         = imp-words wm ws im

-- Every key of the program's signature is a word name.
signature-words : ∀ {mm ds Σ} → ModsW mm → All DeclW ds → SignatureOf mm ds Σ → KeysW Σ
signature-words wm wd (_ , _ , so , im , refl) = ++-all (sigs-words [] wd so) (imp-words wm wd im)

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
