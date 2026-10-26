-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Format.Proof.Decl — a printed declaration reads back, and so does a
-- printed module's token stream (plan 0.124 step 4.2).
--
-- A well-formed declaration (`WFD`) printed and followed by a line end parses
-- as itself up to that line end; the stream `DS` the layout writes
-- (`Format.Proof.Module`) parses as the module's declarations, with nothing
-- but line ends and the end after them. What the layout needs of a
-- declaration (`DeclOK`) follows from its words and literals being printable
-- (`PD`).
------------------------------------------------------------------------

module Once.Format.Proof.Decl where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; reverse; reverseAcc)
open import Data.List.Properties using (++-assoc; reverse-involutive)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.String using (String; toList; _==_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Once.Spec.Surface.Lexing using (Token; TWord; TLParen; TRParen; TColon; TEquals; TDot; TNewline; TEOF)
open import Once.Spec.Surface.Syntax using (Expr; RLam; Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport;
  mkImport; Module; mkModule; RVar; RQualified; RResolved; RApp; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot;
  RBinOp; RNeg)
open import Once.Spec.Surface.Grammar
open import Once.Format.Doc using (Doc; toks; empty; tk; _<>_)
open import Once.Format.Print
open import Once.Format.Proof.Tokens using (word-toks)
open import Once.Format.Proof.ExprBase using (WF; OpName; op-isOperator; word-notOperator; stops-newline)
open import Once.Format.Proof.Expr using (wholeL; opName-parses)
open import Once.Format.Proof.TypeAlgs using (sig-id; alias-id)
import Once.Format.Proof.TypeAlgs as TA
open import Once.Format.Proof.Layout using (Lead; lead-tk; lead-l; lead-r; Silent; s-empty; toks-++; nls)
open import Once.Format.Proof.Printable using (PD; pr-body; run)
open import Once.Format.Proof.Module using (DeclOK; DS; ds-end; ds-cons)

------------------------------------------------------------------------
-- Well-formed declarations
------------------------------------------------------------------------

-- | A declaration's name: an operator, or a word that starts as an
-- identifier and is no keyword.
DeclName : String → Set
DeclName x = OpName x ⊎ (NotKeyword x × ∃[ c ] ∃[ cs ] (toList x ≡ c ∷ cs × Once.Spec.Surface.Lexing.isIdentStart c ≡ true))

WFD : Decl → Set
WFD (DImport (mkImport [] _))      = ⊥
WFD (DImport (mkImport (_ ∷ _) _)) = ⊤
WFD (DTypeAlias x ps A)            = TA.Alias.WF A
WFD (DSignature x A)               = TA.Sig.WF A
WFD (DTypeSig x A)                 = DeclName x × TA.Sig.WF A
WFD (DFunDef x e)                  = DeclName x × WF e

------------------------------------------------------------------------
-- A definition's parameters
------------------------------------------------------------------------

private
  lams-wf : ∀ e → WF e → WF (proj₂ (lams e))
  lams-wf (RLam x e) w = lams-wf e w
  lams-wf (RVar x) w = w
  lams-wf (RQualified x q) w = w
  lams-wf (RResolved n) w = w
  lams-wf (RApp f a) w = w
  lams-wf (RLet x v b) w = w
  lams-wf (RPair a b) w = w
  lams-wf (RDestruct s x el y er) w = w
  lams-wf RUnit w = w
  lams-wf (RInt z) w = w
  lams-wf (RFloat i f l) w = w
  lams-wf (RAnnot e T) w = w
  lams-wf (RBinOp op a b) w = w
  lams-wf (RNeg e) w = w

  lams-wrap : ∀ e → wrapLams (proj₁ (lams e)) (proj₂ (lams e)) ≡ e
  lams-wrap (RLam x e) = cong (RLam x) (lams-wrap e)
  lams-wrap (RVar x) = refl
  lams-wrap (RQualified x q) = refl
  lams-wrap (RResolved n) = refl
  lams-wrap (RApp f a) = refl
  lams-wrap (RLet x v b) = refl
  lams-wrap (RPair a b) = refl
  lams-wrap (RDestruct s x el y er) = refl
  lams-wrap RUnit = refl
  lams-wrap (RInt z) = refl
  lams-wrap (RFloat i f l) = refl
  lams-wrap (RAnnot e T) = refl
  lams-wrap (RBinOp op a b) = refl
  lams-wrap (RNeg e) = refl

  params : ∀ ps tv k B → ParsesParams (toks (proj₁ (spaced ps tv k)) (TEquals ∷ B)) ps (TEquals ∷ B)
  params []           tv k B = params-none (λ ())
  params (p ∷ [])     tv k B =
    subst (λ ts → ParsesParams ts (p ∷ []) (TEquals ∷ B)) (sym (word-toks p tv k _)) (params-eq starts)
  params (p ∷ q ∷ qs) tv k B =
    subst (λ ts → ParsesParams ts (p ∷ q ∷ qs) (TEquals ∷ B)) (sym (word-toks p tv k _))
      (params-cons (subst StartsWord (sym (word-toks q tv _ _)) starts-word) (params (q ∷ qs) tv _ B))

  params-no-colon : ∀ ps tv k B → ¬ Starts (toks (proj₁ (spaced ps tv k)) (TEquals ∷ B)) TColon
  params-no-colon []       tv k B ()
  params-no-colon (p ∷ ps) tv k B s with subst (λ ts → Starts ts TColon) (word-toks p tv k _) s
  ... | ()

  -- `f x … = b`, after the name.
  funDef : ∀ x e tv k r → WF e
         → ParsesFunDef x (toks (proj₁ ((spaced (proj₁ (lams e)) ⊕ᵈ ␣ ⊕ᵈ t TEquals ⊕ᵈ pure′ Once.Format.Doc.line
                                         ⊕ᵈ pex 0 true (proj₂ (lams e))) tv k)) (TNewline ∷ r))
                        (DFunDef x e) (TNewline ∷ r)
  funDef x e tv k r w =
    subst (λ e′ → ParsesFunDef x (toks (proj₁ ((spaced (proj₁ (lams e)) ⊕ᵈ ␣ ⊕ᵈ t TEquals ⊕ᵈ pure′ Once.Format.Doc.line
                                         ⊕ᵈ pex 0 true (proj₂ (lams e))) tv k)) (TNewline ∷ r)) (DFunDef x e′) (TNewline ∷ r))
      (lams-wrap e)
      (fundef (params (proj₁ (lams e)) tv k _) (wholeL (proj₂ (lams e)) tv _ (TNewline ∷ r) (lams-wf e w) stops-newline))

  -- `a.b.c`
  pathL : ∀ x xs tv k r → ¬ Starts r TDot → ParsesModulePath (toks (proj₁ (path (x ∷ xs) tv k)) r) (x ∷ xs) r
  pathL x []       tv k r nd = subst (λ ts → ParsesModulePath ts (x ∷ []) r) (sym (word-toks x tv k r)) (path-end nd)
  pathL x (y ∷ ys) tv k r nd =
    subst (λ ts → ParsesModulePath ts (x ∷ y ∷ ys) r) (sym (word-toks x tv k _)) (path-cons (pathL y ys tv _ r nd))

  -- `T p … = A`, after `type T`.
  aliasL : ∀ x ps acc tv k {A ts r} → AliasType.ParsesType ts A r
         → ParsesTypeAlias x acc (toks (proj₁ (spaced ps tv k)) (TEquals ∷ ts)) (DTypeAlias x (reverse (reverseAcc acc ps)) A) r
  aliasL x []       acc tv k p = alias-eq p
  aliasL x (q ∷ qs) acc tv k {A} {ts} {r} p =
    subst (λ us → ParsesTypeAlias x acc us (DTypeAlias x (reverse (reverseAcc (q ∷ acc) qs)) A) r) (sym (word-toks q tv k _))
      (alias-param (aliasL x qs (q ∷ acc) tv _ p))

  aliasL0 : ∀ x ps tv k {A ts r} → AliasType.ParsesType ts A r
          → ParsesTypeAlias x [] (toks (proj₁ (spaced ps tv k)) (TEquals ∷ ts)) (DTypeAlias x ps A) r
  aliasL0 x ps tv k {A} {ts} {r} p =
    subst (λ ps′ → ParsesTypeAlias x [] (toks (proj₁ (spaced ps tv k)) (TEquals ∷ ts)) (DTypeAlias x ps′ A) r)
      (reverse-involutive ps) (aliasL x ps [] tv k p)

  aliasType : ∀ A tv k r → TA.Alias.WF A → AliasType.ParsesType (toks (proj₁ (pty 0 true A tv k)) (TNewline ∷ r)) A (TNewline ∷ r)
  aliasType A tv k r w =
    subst (λ B → AliasType.ParsesType (toks (proj₁ (pty 0 true A tv k)) (TNewline ∷ r)) B (TNewline ∷ r)) (alias-id A)
      (TA.Alias.type′ A true tv k (TNewline ∷ r) w ((λ ()) , (λ ())) ((λ ()) , (λ ()) , (λ ()) , (λ ())) (λ ()) (λ ()))

  sigType : ∀ A tv k r → TA.Sig.WF A → SigType.ParsesType (toks (proj₁ (pty 0 true A tv k)) (TNewline ∷ r)) A (TNewline ∷ r)
  sigType A tv k r w =
    subst (λ B → SigType.ParsesType (toks (proj₁ (pty 0 true A tv k)) (TNewline ∷ r)) B (TNewline ∷ r)) (sig-id A)
      (TA.Sig.type′ A true tv k (TNewline ∷ r) w ((λ ()) , (λ ())) ((λ ()) , (λ ()) , (λ ()) , (λ ())) (λ ()) (λ ()))

------------------------------------------------------------------------
-- A declaration reads back
------------------------------------------------------------------------

-- | A declaration, followed by a line end.
decl-parses : ∀ d tv k r → WFD d → ParsesDecl (toks (proj₁ (pdecl d tv k)) (TNewline ∷ r)) d (TNewline ∷ r)
decl-parses (DImport (mkImport (x ∷ xs) nothing)) tv k r w =
  subst (λ ts → ParsesDecl ts _ (TNewline ∷ r)) (sym (word-toks "import" tv k _))
    (decl-import (import-plain (pathL x xs tv _ (TNewline ∷ r) (λ ())) (λ ())))
decl-parses (DImport (mkImport (x ∷ xs) (just a))) tv k r w =
  subst (λ ts → ParsesDecl ts _ (TNewline ∷ r)) (sym (word-toks "import" tv k _))
    (subst (λ ts → ParsesDecl (TWord "import" ∷ toks (proj₁ (path (x ∷ xs) tv _)) ts) _ (TNewline ∷ r))
      (sym (word-toks "as" tv _ _))
      (subst (λ ts → ParsesDecl (TWord "import" ∷ toks (proj₁ (path (x ∷ xs) tv _)) (TWord "as" ∷ ts)) _ (TNewline ∷ r))
        (sym (word-toks a tv _ _))
        (decl-import (import-as (pathL x xs tv _ _ (λ ()))))))
decl-parses (DTypeAlias x ps A) tv k r w =
  subst (λ ts → ParsesDecl ts _ (TNewline ∷ r)) (sym (word-toks "type" tv k _))
    (subst (λ ts → ParsesDecl (TWord "type" ∷ ts) _ (TNewline ∷ r)) (sym (word-toks x tv _ _))
      (decl-alias (aliasL0 x ps tv _ (aliasType A tv _ r w))))
decl-parses (DSignature x A) tv k r w =
  subst (λ ts → ParsesDecl ts _ (TNewline ∷ r)) (sym (word-toks "signature" tv k _))
    (subst (λ ts → ParsesDecl (TWord "signature" ∷ ts) _ (TNewline ∷ r)) (sym (word-toks x tv _ _))
      (decl-signature (sigType A tv _ r w)))
decl-parses (DTypeSig x A) tv k r (inj₁ op , w) rewrite op-isOperator x op =
  decl-op (opName-parses x tv k _ op) (op-sig (sigType A tv _ r w))
decl-parses (DTypeSig x A) tv k r (inj₂ (nk , c , cs , eq , st) , w) rewrite word-notOperator x c cs eq st =
  subst (λ ts → ParsesDecl ts _ (TNewline ∷ r)) (sym (word-toks x tv k _)) (decl-typesig nk (sigType A tv _ r w) (λ ()))
decl-parses (DFunDef x e) tv k r (inj₁ op , w) rewrite op-isOperator x op =
  decl-op (opName-parses x tv k _ op) (op-def (params-no-colon (proj₁ (lams e)) tv _ _) (funDef x e tv _ r w))
decl-parses (DFunDef x e) tv k r (inj₂ (nk , c , cs , eq , st) , w) rewrite word-notOperator x c cs eq st =
  subst (λ ts → ParsesDecl ts _ (TNewline ∷ r)) (sym (word-toks x tv k _))
    (decl-fundef nk (params-no-colon (proj₁ (lams e)) tv _ _) (funDef x e tv _ r w))

------------------------------------------------------------------------
-- What the layout needs
------------------------------------------------------------------------

private
  lead-word : ∀ s tv k → Notes.inner (lookupNotes k tv) ≡ [] → Lead (proj₁ (word s tv k))
  lead-word s tv k eq with s == "compose"
  ... | true  = lead-tk
  ... | false = subst (λ cs → Lead (inners cs <> (tk (TWord s) <> eols (Notes.after (lookupNotes k tv))))) (sym eq)
                  (lead-r s-empty (lead-l lead-tk))

  lead-name : ∀ x tv k → Notes.inner (lookupNotes k tv) ≡ [] → Lead (proj₁ (name x tv k))
  lead-name x tv k eq with isOperator x
  ... | true  = lead-l lead-tk
  ... | false = lead-word x tv k eq

  lead-body : ∀ d tv k → Notes.inner (lookupNotes k tv) ≡ [] → Lead (proj₁ (pbody d tv k))
  lead-body (DImport (mkImport p nothing))  tv k eq = lead-l (lead-word "import" tv k eq)
  lead-body (DImport (mkImport p (just a))) tv k eq = lead-l (lead-word "import" tv k eq)
  lead-body (DTypeAlias x ps A) tv k eq = lead-l (lead-word "type" tv k eq)
  lead-body (DSignature x A)    tv k eq = lead-l (lead-word "signature" tv k eq)
  lead-body (DTypeSig x A)      tv k eq = lead-l (lead-name x tv k eq)
  lead-body (DFunDef x e)       tv k eq = lead-l (lead-name x tv k eq)

-- | A declaration with printable words is one the layout can write.
decl-ok : ∀ d → PD d → DeclOK d
decl-ok d p tv k eq = lead-body d tv k eq , run (pr-body d p) tv k [] []

------------------------------------------------------------------------
-- The module
------------------------------------------------------------------------

private
  skip : ∀ k ts → ¬ Starts ts TNewline → SkipNewlines (nls k ++ ts) ts
  skip zero    ts nn = skip-done nn
  skip (suc k) ts nn = skip-nl (skip k ts nn)

  decl-head : ∀ {ts d r} → ParsesDecl ts d r → ¬ Starts ts TNewline
  decl-head (decl-import _)        ()
  decl-head (decl-alias _)         ()
  decl-head (decl-signature _)     ()
  decl-head (decl-typesig _ _ _)   ()
  decl-head (decl-fundef _ _ _)    ()
  decl-head (decl-op _ _)          ()

  decls-nl : ∀ {ts ds r} → ParsesDecls ts ds r → ParsesDecls (TNewline ∷ ts) ds r
  decls-nl (decls-stop s n)   = decls-stop (skip-nl s) n
  decls-nl (decls-cons s p q) = decls-cons (skip-nl s) p q

-- | The stream reads as the declarations, then only line ends and the end.
ds-parses : ∀ {ds ys} → All WFD ds → DS ds ys → ∃[ r ] (ParsesDecls (ys ++ TEOF ∷ []) ds r × Trailing r)
ds-parses [] (ds-end {k}) = TEOF ∷ [] , decls-stop (skip k (TEOF ∷ []) (λ ())) (λ ()) , trail-eof trail-end
ds-parses (w ∷ ws) (ds-cons {d} {ds} {ys} {k} {tv} {j} rest) with ds-parses ws rest
... | r , p , tr =
  r ,
  subst (λ ts → ParsesDecls ts (d ∷ ds) r)
    (sym (trans (++-assoc (nls k) (toks (proj₁ (pdecl d tv j)) (TNewline ∷ ys)) (TEOF ∷ []))
           (cong (nls k ++_) (trans (cong (_++ TEOF ∷ []) (toks-++ (proj₁ (pdecl d tv j)) (TNewline ∷ ys))) (toks-++′ ys)))))
    (decls-cons (skip k _ (decl-head pd)) pd (decls-nl p)) ,
  tr
  where
    pd = decl-parses d tv j (ys ++ TEOF ∷ []) w
    toks-++′ : ∀ ys → (toks (proj₁ (pdecl d tv j)) [] ++ TNewline ∷ ys) ++ TEOF ∷ []
                     ≡ toks (proj₁ (pdecl d tv j)) (TNewline ∷ ys ++ TEOF ∷ [])
    toks-++′ ys = trans (++-assoc (toks (proj₁ (pdecl d tv j)) []) (TNewline ∷ ys) (TEOF ∷ []))
                    (sym (toks-++ (proj₁ (pdecl d tv j)) (TNewline ∷ ys ++ TEOF ∷ [])))
