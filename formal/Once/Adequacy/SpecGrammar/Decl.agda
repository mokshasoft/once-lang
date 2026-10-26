-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.Decl — the compiler's declaration and module
-- grammar (`Once.Parser.Relation.{Decl,…}`, `Once.Parser.Relation.Parsing`) against the Spec's.
--
--   * `parses→` : a text the compiler parses is one the Spec parses, into the
--     same module;
--   * `parses←` : a text the Spec parses is one the compiler parses, into the
--     same module.
--
-- The compiler's declarations are the Spec's (plan 0.122), so the two
-- grammars relate a text to one module.
--
-- A program the Spec parses has no string literal (no Spec rule reads one,
-- and nothing but newlines may be left over), which is what the expression
-- bridge needs (`decls-ns`).
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.Decl where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; reverse)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Once.Spec.Surface.Syntax using (Expr)
import Once.Spec.Surface.Syntax as S
open import Once.Spec.Surface.Lexing using (Token; TString; TWord; TLParen; TRParen; TColon; TEquals; TDot; TNewline; TEOF; Lexes)
open import Once.Spec.Surface.Grammar as G
  using (Starts; starts; StartsWord; starts-word; NotKeyword; not-keyword; OpChar;
         oc-dot; oc-plus; oc-minus; oc-star; oc-slash; oc-pct; oc-lt; oc-gt; oc-pipe; oc-amp; oc-at;
         op-close; op-char; op-sig; op-def; fundef; params-eq; params-cons; params-stop; params-none;
         path-cons; path-dotstop; path-end; import-as; import-plain; alias-eq; alias-param;
         decl-import; decl-alias; decl-signature; decl-typesig; decl-fundef; decl-op;
         SkipNewlines; skip-nl; skip-done; decls-stop; decls-cons; Trailing; trail-end; trail-nl; trail-eof; wrapLams)
import Once.Parser.Token as P
open import Once.Parser.Core using (skipNewlines)
open import Once.Parser.Module.Core using (wordHead)
open import Once.Spec.Surface.Syntax using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport)
open import Once.Spec.Surface.Syntax using (mkImport)
open import Once.Parser.Module.DeclTail using (colonHead)
open import Once.Parser.Module.OpName using (opTokClass)
open import Once.Parser.Module.FunDef.Body using (eqHead)
import Once.Parser.Module.FunDef.Params as LPar
import Once.Parser.Relation.Decl as LD
import Once.Parser.Relation.Import as LI
import Once.Parser.Relation.TypeAlias as LT
import Once.Parser.Relation.Signature as LS
import Once.Parser.Relation.FunDef as LF
import Once.Parser.Relation.OpDecl as LO
import Once.Parser.Relation.Parsing as LP
import Once.Parser.Relation.Lexing as LL
import Once.Parser
import Once.Parser.Module.Core
import Once.Parser.Module.Import
import Once.Parser.Module.DeclTail
import Once.Parser.Module.FunDef.Body
import Once.Parser.Module.OpName
import Once.Parser.TypeRelation
import Once.Parser.ExprRelation
import Once.Parser.Generic.PolyInst
open import Once.Adequacy.SpecLexing using (toNew; toOld; forget)
open import Once.Adequacy.SpecGrammar.Tokens using (step; peel; peels; []; _∷_)
open import Once.Adequacy.SpecGrammar.DeclHeads
open import Once.Adequacy.SpecGrammar.ExprHeads using (StrHead; str-head)
open import Once.Adequacy.SpecGrammar.Expr using (expr→; expr←)
open import Once.Adequacy.SpecGrammar.Conv using (toPoly)
open import Once.Type.Poly using (polyOf)
open import Once.Adequacy.SpecGrammar.SigTypes using (sig→; sig←)
open import Once.Adequacy.SpecGrammar.GroundTypes using (alias→; alias←)

private
  F : List P.Token → List Token
  F = map forget

  N : List Token → Set
  N r = ¬ StrHead r

------------------------------------------------------------------------
-- Small facts about the views
------------------------------------------------------------------------

private
  not-as : ∀ {s ts} → s ≢ "as" → ¬ Starts (TWord s ∷ ts) (TWord "as")
  not-as ne starts = ne refl

  starts→word : ∀ {ts s} → Starts ts (TWord s) → StartsWord ts
  starts→word starts = starts-word

  word-false : ∀ {toks b} → WordView toks b → ¬ StartsWord (F toks) → b ≡ false
  word-false wv-word n = ⊥-elim (n starts-word)
  word-false (wv-not _) _ = refl

  dot-false : ∀ {toks b} → DotView toks b → ¬ Starts (F toks) TDot → b ≡ false
  dot-false dot-yes n = ⊥-elim (n starts)
  dot-false (dot-no _) _ = refl

  colon-false : ∀ {toks b} → ColonView toks b → ¬ Starts (F toks) TColon → b ≡ false
  colon-false colon-yes n = ⊥-elim (n starts)
  colon-false (colon-no _) _ = refl

  eq-false : ∀ {toks b} → EqView toks b → ¬ Starts (F toks) TEquals → b ≡ false
  eq-false eq-yes n = ⊥-elim (n starts)
  eq-false (eq-no _) _ = refl

  sep-eq : ∀ {toks k} → SepView toks k → Starts (F toks) TEquals → k ≡ LPar.skEq
  sep-eq sv-eq _ = refl
  sep-eq sv-word ()
  sep-eq (sv-stop a _) s = ⊥-elim (a s)

  sep-word : ∀ {toks k} → SepView toks k → StartsWord (F toks) → k ≡ LPar.skWord
  sep-word sv-eq ()
  sep-word sv-word _ = refl
  sep-word (sv-stop _ b) s = ⊥-elim (b s)

  sep-stop : ∀ {toks k} → SepView toks k → ¬ Starts (F toks) TEquals → ¬ StartsWord (F toks) → k ≡ LPar.skStop
  sep-stop sv-eq a _ = ⊥-elim (a starts)
  sep-stop sv-word _ b = ⊥-elim (b starts-word)
  sep-stop (sv-stop _ _) _ _ = refl

  transport : ∀ {ts ts′} (P′ : List Token → Set) → ts ≡ ts′ → P′ ts′ → P′ ts
  transport P′ e p = subst P′ (sym e) p

------------------------------------------------------------------------
-- The compiler's derivation gives the Spec's
------------------------------------------------------------------------

path→ : ∀ {toks p rest} → LI.ParsesModulePath toks p rest → G.ParsesModulePath (F toks) p (F rest)

private
  pcons : ∀ {name tail p rest} {b} → DotView tail b → b ≡ true
        → LI.ParsesModulePath (Once.Parser.Module.Import.dropDot tail) p rest
        → G.ParsesModulePath (TWord name ∷ F tail) (name ∷ p) (F rest)
  pcons dot-yes _ d = path-cons (path→ d)
  pcons (dot-no _) () d

  pstop : ∀ {name tail} {b c} → DotView tail b → b ≡ true → WordView (Once.Parser.Module.Import.dropDot tail) c → c ≡ false
        → G.ParsesModulePath (TWord name ∷ F tail) (name ∷ []) (F tail)
  pstop dot-yes _ (wv-not n) _ = path-dotstop n
  pstop dot-yes _ wv-word ()
  pstop (dot-no _) () _ _

  pend : ∀ {name tail} {b} → DotView tail b → b ≡ false → G.ParsesModulePath (TWord name ∷ F tail) (name ∷ []) (F tail)
  pend dot-yes ()
  pend (dot-no n) _ = path-end n

path→ (LI.pmp-cons {tail = tail} e d) = pcons (dot-view tail) e d
path→ (LI.pmp-dotfail {tail = tail} e w) = pstop (dot-view tail) e (word-view _) w
path→ (LI.pmp-nodot {tail = tail} e) = pend (dot-view tail) e

private
  nonword-as : ∀ {toks} {b} → WordView toks b → b ≡ false → ¬ Starts (F toks) (TWord "as")
  nonword-as wv-word () _
  nonword-as (wv-not n) _ s = n (starts→word s)

import→ : ∀ {toks d rest} → LI.ParsesImport toks d rest → G.ParsesImport (F toks) d (F rest)
import→ (LI.pi-mk dp LI.pia-alias-r) = import-as (path→ dp)
import→ (LI.pi-mk dp (LI.pia-neq-r ne)) = import-plain (path→ dp) (not-as ne)
import→ (LI.pi-mk dp (LI.pia-nonword-r {toks} w)) = import-plain (path→ dp) (nonword-as (word-view toks) w)

aliasd→ : ∀ {name ps toks d rest} → LT.ParsesTypeAlias name ps toks d rest
        → G.ParsesTypeAlias name ps (F toks) d (F rest)

private
  aeq : ∀ {name ps toks T rest} {b} → TaEqView toks b → b ≡ true
      → Once.Parser.TypeRelation.ParsesType (Once.Parser.Module.DeclTail.taDrop1 toks) T rest
      → G.ParsesTypeAlias name ps (F toks) (S.DTypeAlias name (reverse ps) (polyOf T)) (F rest)
  aeq taEq-yes _ dT = alias-eq (alias→ dT)
  aeq (taEq-no _) () dT

aliasd→ (LT.gta-eq-r {toks = toks} w e dT) = aeq (taEq-view toks) e dT
aliasd→ (LT.gta-word-r d) = alias-param (aliasd→ d)

params→ : ∀ {toks ps rest} → LF.ParsesParams toks ps rest → G.ParsesParams (F toks) ps (F rest)

private
  peq : ∀ {name tail k} → SepView tail k → k ≡ LPar.skEq → G.ParsesParams (TWord name ∷ F tail) (name ∷ []) (F tail)
  peq sv-eq _ = params-eq starts
  peq sv-word ()
  peq (sv-stop _ _) ()

  pcons′ : ∀ {name tail k ps rest} → SepView tail k → k ≡ LPar.skWord → LF.ParsesParams tail ps rest
         → G.ParsesParams (TWord name ∷ F tail) (name ∷ ps) (F rest)
  pcons′ sv-eq () d
  pcons′ sv-word _ d = params-cons starts-word (params→ d)
  pcons′ (sv-stop _ _) () d

  pstop′ : ∀ {name tail k} → SepView tail k → k ≡ LPar.skStop → G.ParsesParams (TWord name ∷ F tail) [] (TWord name ∷ F tail)
  pstop′ sv-eq ()
  pstop′ sv-word ()
  pstop′ (sv-stop a b) _ = params-stop a b

  pnone : ∀ {toks b} → WordView toks b → b ≡ false → G.ParsesParams (F toks) [] (F toks)
  pnone wv-word ()
  pnone (wv-not n) _ = params-none n

params→ (LF.pp-eq {tail = tail} e) = peq (sep-view tail) e
params→ (LF.pp-cons {tail = tail} e d) = pcons′ (sep-view tail) e d
params→ (LF.pp-stop {tail = tail} e) = pstop′ (sep-view tail) e
params→ (LF.pp-noword {toks} w) = pnone (word-view toks) w

fundef→ : ∀ {name toks d rest} → LF.ParsesFunDef name toks d rest → G.ParsesFunDef name (F toks) d (F rest)

private
  body→ : ∀ {name ps toks toks″ body rest} {b} → LF.ParsesParams toks ps toks″ → EqView toks″ b → b ≡ true
        → Once.Parser.ExprRelation.ParsesExpr (Once.Parser.Module.FunDef.Body.drop1 toks″) body rest
        → G.ParsesFunDef name (F toks) (S.DFunDef name (wrapLams ps body)) (F rest)
  body→ dp eq-yes _ de = fundef (params→ dp) (expr→ de)
  body→ dp (eq-no _) () de

fundef→ (LF.pfd-mk dp (LF.pfb-mk {toks = toks″} e de)) = body→ dp (eq-view toks″) e de

opchars→ : ∀ {toks cs s rest} → LO.ParsesOpChars toks cs s rest → G.ParsesOpChars (F toks) cs s (F rest)

private
  oclose : ∀ {tok rest c cs k} → OpTokView tok k → k ≡ Once.Parser.Module.OpName.otClose
         → G.ParsesOpChars (forget tok ∷ F rest) (c ∷ cs) (Data.String.fromList (reverse (c ∷ cs))) (F rest)
  oclose otv-close _ = op-close
  oclose (otv-char _) ()
  oclose (otv-none _ _) ()

  ochar : ∀ {tok rest cs ch s rest′ k} → OpTokView tok k → k ≡ Once.Parser.Module.OpName.otChar ch
        → LO.ParsesOpChars rest (ch ∷ cs) s rest′ → G.ParsesOpChars (forget tok ∷ F rest) cs s (F rest′)
  ochar otv-close () d
  ochar (otv-char oc) refl d = op-char oc (opchars→ d)
  ochar (otv-none _ _) () d

opchars→ (LO.poc-close {tok} e) = oclose (optok-view tok) e
opchars→ (LO.poc-char {tok} e d) = ochar (optok-view tok) e d

opafter→ : ∀ {name toks d rest} → LO.ParsesOpAfter name toks d rest → G.ParsesOpAfter name (F toks) d (F rest)

private
  osig : ∀ {name toks ty rest} {b} → ColonView toks b → b ≡ true
       → Once.Parser.Generic.PolyInst.ParsesPolyType (Once.Parser.Module.DeclTail.colDrop1 toks) ty rest
       → G.ParsesOpAfter name (F toks) (S.DTypeSig name (toPoly ty)) (F rest)
  osig colon-yes _ dT = op-sig (sig→ dT)
  osig (colon-no _) () dT

  ofun : ∀ {name toks d rest} {b} → ColonView toks b → b ≡ false → LF.ParsesFunDef name toks d rest
       → G.ParsesOpAfter name (F toks) d (F rest)
  ofun colon-yes () dF
  ofun (colon-no n) _ dF = op-def n (fundef→ dF)

opafter→ (LO.poa-sig {toks} e dT) = osig (colon-view toks) e dT
opafter→ (LO.poa-fun {toks} e dF) = ofun (colon-view toks) e dF

decl→ : ∀ {toks d rest} → LD.ParsesDecl toks d rest → G.ParsesDecl (F toks) d (F rest)

private
  dsig : ∀ {name residual ty rest} {b} → ColonView residual b → b ≡ true
       → Once.Parser.Generic.PolyInst.ParsesPolyType (Once.Parser.Module.DeclTail.colDrop1 residual) ty rest
       → G.ParsesDecl (TWord "signature" ∷ TWord name ∷ F residual) (S.DSignature name (toPoly ty)) (F rest)
  dsig colon-yes _ dT = decl-signature (sig→ dT)
  dsig (colon-no _) () dT

  dtsig : ∀ {w rest ty rest′} {b c} → NotKeyword w → ColonView rest b → b ≡ true
        → Once.Parser.Generic.PolyInst.ParsesPolyType (Once.Parser.Module.DeclTail.colDrop1 rest) ty rest′
        → EqView rest′ c → c ≡ false
        → G.ParsesDecl (TWord w ∷ F rest) (S.DTypeSig w (toPoly ty)) (F rest′)
  dtsig nk colon-yes _ dT eq-yes ()
  dtsig nk colon-yes _ dT (eq-no n) _ = decl-typesig nk (sig→ dT) n
  dtsig nk (colon-no _) () dT _ _

  dfun : ∀ {w rest d rest′} {b} → NotKeyword w → ColonView rest b → b ≡ false → LF.ParsesFunDef w rest d rest′
       → G.ParsesDecl (TWord w ∷ F rest) d (F rest′)
  dfun nk colon-yes () dF
  dfun nk (colon-no n) _ dF = decl-fundef nk n (fundef→ dF)

decl→ (LD.pd-import di) = decl-import (import→ di)
decl→ (LD.pd-typealias (LT.pta-mk da)) = decl-alias (aliasd→ da)
decl→ (LD.pd-signature (LS.psig-mk {residual = residual} e dT)) = dsig (colon-view residual) e dT
decl→ (LD.pd-typesig {rest = rest} {rest' = rest′} a b c e dT f) =
  dtsig (not-keyword a b c) (colon-view rest) e dT (eq-view rest′) f
decl→ (LD.pd-fundef {rest = rest} a b c e dF) = dfun (not-keyword a b c) (colon-view rest) e dF
decl→ (LD.pd-opdecl (LO.pod-mk dc da)) = decl-op (opchars→ dc) (opafter→ da)

-- Newlines.
skip-nl-eq : ∀ t {ns r} → skipNewlines t ≡ just (ns , r) → skipNewlines (P.TNewline ∷ t) ≡ just (P.TNewline ∷ ns , r)
skip-nl-eq t e rewrite e = refl

skip-total : ∀ toks → Σ[ ns ∈ List P.Token ] Σ[ r ∈ List P.Token ] skipNewlines toks ≡ just (ns , r)
private
  skip-total′ : ∀ {toks} → SkipView toks → Σ[ ns ∈ List P.Token ] Σ[ r ∈ List P.Token ] skipNewlines toks ≡ just (ns , r)
  skip-total′ sk-nil = [] , [] , refl
  skip-total′ (sk-nl {t}) = nl-total t (skip-total t)
    where
      nl-total : ∀ t → Σ[ ns ∈ List P.Token ] Σ[ r ∈ List P.Token ] skipNewlines t ≡ just (ns , r)
               → Σ[ ns ∈ List P.Token ] Σ[ r ∈ List P.Token ] skipNewlines (P.TNewline ∷ t) ≡ just (ns , r)
      nl-total t (ns , r , e) = P.TNewline ∷ ns , r , skip-nl-eq t e
  skip-total′ {toks} (sk-stop _ e) = [] , toks , e
skip-total []      = skip-total′ sk-nil
skip-total (h ∷ t) = skip-total′ (skip-view (h ∷ t))

private
  just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  pair-snd : ∀ {A B : Set} {a a′ : A} {b b′ : B} → (a , b) ≡ (a′ , b′) → b ≡ b′
  pair-snd refl = refl

skip→ : ∀ toks {nl toks′} → skipNewlines toks ≡ just (nl , toks′) → SkipNewlines (F toks) (F toks′)
private
  skip→′ : ∀ {toks nl toks′} → SkipView toks → skipNewlines toks ≡ just (nl , toks′) → SkipNewlines (F toks) (F toks′)
  skip→′ sk-nil refl = skip-done (λ ())
  skip→′ (sk-nl {t}) e = nl-step t (skip-total t) e
    where
      nl-step : ∀ t {nl toks′} → Σ[ ns ∈ List P.Token ] Σ[ r ∈ List P.Token ] skipNewlines t ≡ just (ns , r)
              → skipNewlines (P.TNewline ∷ t) ≡ just (nl , toks′) → SkipNewlines (TNewline ∷ F t) (F toks′)
      nl-step t (ns , r , et) e =
        subst (λ z → SkipNewlines (TNewline ∷ F t) (F z)) (pair-snd (just-inj (trans (sym (skip-nl-eq t et)) e)))
              (skip-nl (skip→ t et))
  skip→′ (sk-stop n e₀) e = subst (λ z → SkipNewlines _ (F z)) (pair-snd (just-inj (trans (sym e₀) e))) (skip-done n)
skip→ []      e = skip→′ sk-nil e
skip→ (h ∷ t) e = skip→′ (skip-view (h ∷ t)) e

skip-not-nl : ∀ {ts ts₁} → SkipNewlines ts ts₁ → ¬ Starts ts₁ TNewline
skip-not-nl (skip-nl s) = skip-not-nl s
skip-not-nl (skip-done n) = n

private
  trail-nodecl : ∀ {ts d r} → Trailing ts → ¬ Starts ts TNewline → ¬ G.ParsesDecl ts d r
  trail-nodecl trail-end _ ()
  trail-nodecl (trail-nl _) n _ = n starts
  trail-nodecl (trail-eof _) _ ()

  skip-never-nothing : ∀ toks → skipNewlines toks ≡ nothing → ⊥
  skip-never-nothing toks e = nothing≢ (trans (sym e) (proj₂ (proj₂ (skip-total toks))))
    where
      nothing≢ : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
      nothing≢ ()

decls→ : ∀ {toks ds rest} → LP.ParsesDecls toks ds rest → Once.Parser.allTrailing rest ≡ true
       → G.ParsesDecls (F toks) ds (F rest)
decls→ (LP.pds-noskip {toks} e) at = ⊥-elim (skip-never-nothing toks e)
decls→ (LP.pds-stop {toks} {toks' = toks′} e _) at =
  decls-stop (skip→ toks e) (λ d → trail-nodecl (trail→ toks′ at) (skip-not-nl (skip→ toks e)) d)
decls→ (LP.pds-cons {toks} e d ds) at = decls-cons (skip→ toks e) (decl→ d) (decls→ ds at)

------------------------------------------------------------------------
-- The Spec's derivation comes from the compiler's
------------------------------------------------------------------------

BackD : (List P.Token → Decl → List P.Token → Set) → List P.Token → Decl → List Token → Set
BackD Rel toks d r = Σ[ rest ∈ List P.Token ] (Rel toks d rest × F rest ≡ r)

path← : ∀ {ts p r} → G.ParsesModulePath ts p r → ∀ toks → F toks ≡ ts
      → Σ[ rest ∈ List P.Token ] (LI.ParsesModulePath toks p rest × F rest ≡ r)
path← (path-cons dp) toks e =
  step (λ z → Σ[ rest ∈ List P.Token ] (LI.ParsesModulePath z _ rest × F rest ≡ _)) refl e (λ e₁ →
  step (λ z → Σ[ rest ∈ List P.Token ] (LI.ParsesModulePath (P.TWord _ ∷ z) _ rest × F rest ≡ _)) refl e₁ (λ {toks′} e₂ →
  pc← (path← dp toks′ e₂)))
  where
    pc← : ∀ {x toks′ p r} → Σ[ rest ∈ List P.Token ] (LI.ParsesModulePath toks′ p rest × F rest ≡ r)
        → Σ[ rest ∈ List P.Token ] (LI.ParsesModulePath (P.TWord x ∷ P.TDot ∷ toks′) (x ∷ p) rest × F rest ≡ r)
    pc← (rest , d , er) = rest , LI.pmp-cons refl d , er
path← (path-dotstop nw) toks e =
  step (λ z → Σ[ rest ∈ List P.Token ] (LI.ParsesModulePath z _ rest × F rest ≡ _)) refl e (λ e₁ →
  step (λ z → Σ[ rest ∈ List P.Token ] (LI.ParsesModulePath (P.TWord _ ∷ z) _ rest × F rest ≡ _)) refl e₁ (λ {toks′} e₂ →
  P.TDot ∷ toks′ , LI.pmp-dotfail refl (word-false (word-view toks′) (transport (λ z → ¬ StartsWord z) e₂ nw)) , cong (TDot ∷_) e₂))
path← (path-end nd) toks e =
  step (λ z → Σ[ rest ∈ List P.Token ] (LI.ParsesModulePath z _ rest × F rest ≡ _)) refl e (λ {toks′} e′ →
  toks′ , LI.pmp-nodot (dot-false (dot-view toks′) (transport (λ z → ¬ Starts z TDot) e′ nd)) , e′)

private
  alias-plain : ∀ {path} rest {b} → WordView rest b → b ≡ wordHead rest → ¬ Starts (F rest) (TWord "as")
              → LI.ParsesImportAlias path rest (DImport (mkImport path nothing)) rest
  alias-plain _ (wv-word {s}) _ n = plain-word (s ≟ "as") n
    where
      plain-word : ∀ {path t} → Relation.Nullary.Dec (s ≡ "as") → ¬ Starts (TWord s ∷ F t) (TWord "as")
                 → LI.ParsesImportAlias path (P.TWord s ∷ t) (DImport (mkImport path nothing)) (P.TWord s ∷ t)
      plain-word (yes refl) n = ⊥-elim (n starts)
      plain-word (no ne) _ = LI.pia-neq-r ne
  alias-plain rest (wv-not _) eq _ = LI.pia-nonword-r (sym eq)

import← : ∀ {ts d′ r} → G.ParsesImport ts d′ r → ∀ toks → F toks ≡ ts → BackD LI.ParsesImport toks d′ r
import← (import-as dp) toks e = as₁ (path← dp toks e)
  where
    as₂ : ∀ {toks p rest₁ a r} → LI.ParsesModulePath toks p rest₁
        → Σ[ rest ∈ List P.Token ] (rest₁ ≡ P.TWord "as" ∷ P.TWord a ∷ rest × F rest ≡ r)
        → BackD LI.ParsesImport toks (S.DImport (S.mkImport p (just a))) r
    as₂ dp (rest , refl , er) = rest , LI.pi-mk dp LI.pia-alias-r , er
    as₁ : ∀ {toks p a r} → Σ[ rest₁ ∈ List P.Token ] (LI.ParsesModulePath toks p rest₁ × F rest₁ ≡ TWord "as" ∷ TWord a ∷ r)
        → BackD LI.ParsesImport toks (S.DImport (S.mkImport p (just a))) r
    as₁ (rest₁ , dp , e₁) = as₂ dp (peels (TWord "as" ∷ TWord _ ∷ []) (refl ∷ refl ∷ []) e₁)
import← (import-plain dp ns) toks e = pl₁ ns (path← dp toks e)
  where
    pl₁ : ∀ {toks p r} → ¬ Starts r (TWord "as") → Σ[ rest ∈ List P.Token ] (LI.ParsesModulePath toks p rest × F rest ≡ r)
        → BackD LI.ParsesImport toks (S.DImport (S.mkImport p nothing)) r
    pl₁ ns (rest , dp , er) =
      rest , LI.pi-mk dp (alias-plain rest (word-view rest) refl (transport (λ z → ¬ Starts z (TWord "as")) er ns)) , er

aliasd← : ∀ {x ps ts d′ r} → G.ParsesTypeAlias x ps ts d′ r → ∀ toks → F toks ≡ ts → BackD (LT.ParsesTypeAlias x ps) toks d′ r
aliasd← (alias-eq dT) toks e =
  step (λ z → BackD (LT.ParsesTypeAlias _ _) z _ _) refl e (λ {toks′} e′ → ae₁ (alias← dT toks′ e′))
  where
    ae₁ : ∀ {x ps toks′ A′ r} → Σ[ T ∈ _ ] Σ[ rest ∈ List P.Token ] (Once.Parser.TypeRelation.ParsesType toks′ T rest × polyOf T ≡ A′ × F rest ≡ r)
        → BackD (LT.ParsesTypeAlias x ps) (P.TEquals ∷ toks′) (S.DTypeAlias x (reverse ps) A′) r
    ae₁ (T , rest , dT , refl , er) = rest , LT.gta-eq-r refl refl dT , er
aliasd← (alias-param da) toks e =
  step (λ z → BackD (LT.ParsesTypeAlias _ _) z _ _) refl e (λ {toks′} e′ → ap₁ (aliasd← da toks′ e′))
  where
    ap₁ : ∀ {x p ps toks′ d r} → BackD (LT.ParsesTypeAlias x (p ∷ ps)) toks′ d r → BackD (LT.ParsesTypeAlias x ps) (P.TWord p ∷ toks′) d r
    ap₁ (rest , da , er) = rest , LT.gta-word-r da , er

params← : ∀ {ts ps r} → G.ParsesParams ts ps r → ∀ toks → F toks ≡ ts
        → Σ[ rest ∈ List P.Token ] (LF.ParsesParams toks ps rest × F rest ≡ r)
params← (params-eq st) toks e =
  step (λ z → Σ[ rest ∈ List P.Token ] (LF.ParsesParams z _ rest × F rest ≡ _)) refl e (λ {toks′} e′ →
  toks′ , LF.pp-eq (sep-eq (sep-view toks′) (transport (λ z → Starts z TEquals) e′ st)) , e′)
params← (params-cons sw dp) toks e =
  step (λ z → Σ[ rest ∈ List P.Token ] (LF.ParsesParams z _ rest × F rest ≡ _)) refl e (λ {toks′} e′ →
  pc₁ (sep-word (sep-view toks′) (transport StartsWord e′ sw)) (params← dp toks′ e′))
  where
    pc₁ : ∀ {x toks′ ps r} → LPar.sepClass toks′ ≡ LPar.skWord → Σ[ rest ∈ List P.Token ] (LF.ParsesParams toks′ ps rest × F rest ≡ r)
        → Σ[ rest ∈ List P.Token ] (LF.ParsesParams (P.TWord x ∷ toks′) (x ∷ ps) rest × F rest ≡ r)
    pc₁ sc (rest , dp , er) = rest , LF.pp-cons sc dp , er
params← (params-stop a b) toks e =
  step (λ z → Σ[ rest ∈ List P.Token ] (LF.ParsesParams z _ rest × F rest ≡ _)) refl e (λ {toks′} e′ →
  P.TWord _ ∷ toks′ ,
  LF.pp-stop (sep-stop (sep-view toks′) (transport (λ z → ¬ Starts z TEquals) e′ a) (transport (λ z → ¬ StartsWord z) e′ b)) ,
  cong (TWord _ ∷_) e′)
params← (params-none nw) toks e = toks , LF.pp-noword (word-false (word-view toks) (transport (λ z → ¬ StartsWord z) e nw)) , e

fundef← : ∀ {x ts d′ r} → G.ParsesFunDef x ts d′ r → ∀ toks → F toks ≡ ts → N r → BackD (LF.ParsesFunDef x) toks d′ r
fundef← (fundef dp de) toks e n = fd₁ n de (params← dp toks e)
  where
    fd₃ : ∀ {x ps toks toks₁ b′ r} → LF.ParsesParams toks ps (P.TEquals ∷ toks₁)
        → Σ[ rest ∈ List P.Token ] (Once.Parser.ExprRelation.ParsesExpr toks₁ b′ rest × F rest ≡ r)
        → BackD (LF.ParsesFunDef x) toks (S.DFunDef x (wrapLams ps b′)) r
    fd₃ dp (rest , de , er) = rest , LF.pfd-mk dp (LF.pfb-mk refl de) , er
    fd₂ : ∀ {x ps toks rest₁ ts₁ b′ r} → N r → G.ParsesExpr ts₁ b′ r → LF.ParsesParams toks ps rest₁
        → Σ[ toks₁ ∈ List P.Token ] (rest₁ ≡ P.TEquals ∷ toks₁ × F toks₁ ≡ ts₁)
        → BackD (LF.ParsesFunDef x) toks (S.DFunDef x (wrapLams ps b′)) r
    fd₂ n de dp (toks₁ , refl , e₂) = fd₃ dp (expr← de toks₁ e₂ n)
    fd₁ : ∀ {x ps toks ts₁ b′ r} → N r → G.ParsesExpr ts₁ b′ r
        → Σ[ rest₁ ∈ List P.Token ] (LF.ParsesParams toks ps rest₁ × F rest₁ ≡ TEquals ∷ ts₁)
        → BackD (LF.ParsesFunDef x) toks (S.DFunDef x (wrapLams ps b′)) r
    fd₁ n de (rest₁ , dp , e₁) = fd₂ n de dp (peel refl e₁)

opchars← : ∀ {ts cs s r} → G.ParsesOpChars ts cs s r → ∀ toks → F toks ≡ ts
         → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars toks cs s rest × F rest ≡ r)
private
  oc← : ∀ {cs ch s r toks} (tok : P.Token) → opTokClass tok ≡ Once.Parser.Module.OpName.otChar ch
      → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars toks (ch ∷ cs) s rest × F rest ≡ r)
      → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars (tok ∷ toks) cs s rest × F rest ≡ r)
  oc← tok e (rest , d , er) = rest , LO.poc-char e d , er
opchars← op-close toks e =
  step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z (_ ∷ _) _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → toks′ , LO.poc-close refl , e′)
opchars← (op-char oc-dot d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TDot refl (opchars← d toks′ e′))
opchars← (op-char oc-plus d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TPlus refl (opchars← d toks′ e′))
opchars← (op-char oc-minus d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TMinus refl (opchars← d toks′ e′))
opchars← (op-char oc-star d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TStar refl (opchars← d toks′ e′))
opchars← (op-char oc-slash d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TSlash refl (opchars← d toks′ e′))
opchars← (op-char oc-pct d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TPercent refl (opchars← d toks′ e′))
opchars← (op-char oc-lt d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TLt refl (opchars← d toks′ e′))
opchars← (op-char oc-gt d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TGt refl (opchars← d toks′ e′))
opchars← (op-char oc-pipe d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TPipe refl (opchars← d toks′ e′))
opchars← (op-char oc-amp d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TAmpersand refl (opchars← d toks′ e′))
opchars← (op-char oc-at d) toks e = step (λ z → Σ[ rest ∈ List P.Token ] (LO.ParsesOpChars z _ _ rest × F rest ≡ _)) refl e (λ {toks′} e′ → oc← P.TAt refl (opchars← d toks′ e′))

opafter← : ∀ {x ts d′ r} → G.ParsesOpAfter x ts d′ r → ∀ toks → F toks ≡ ts → N r → BackD (LO.ParsesOpAfter x) toks d′ r
opafter← (op-sig dT) toks e n =
  step (λ z → BackD (LO.ParsesOpAfter _) z _ _) refl e (λ {toks′} e′ → os₁ (sig← dT toks′ e′))
  where
    os₁ : ∀ {x toks′ A′ r} → Σ[ A ∈ _ ] Σ[ rest ∈ List P.Token ] (Once.Parser.Generic.PolyInst.ParsesPolyType toks′ A rest × toPoly A ≡ A′ × F rest ≡ r)
        → BackD (LO.ParsesOpAfter x) (P.TColon ∷ toks′) (S.DTypeSig x A′) r
    os₁ (A , rest , dA , refl , er) = rest , LO.poa-sig refl dA , er
opafter← (op-def nc dF) toks e n = of₁ (fundef← dF toks e n)
  where
    of₁ : ∀ {x d r} → BackD (LF.ParsesFunDef x) toks d r → BackD (LO.ParsesOpAfter x) toks d r
    of₁ (rest , dF , er) =
      rest , LO.poa-fun (colon-false (colon-view toks) (transport (λ z → ¬ Starts z TColon) e nc)) dF , er

decl← : ∀ {ts d′ r} → G.ParsesDecl ts d′ r → ∀ toks → F toks ≡ ts → N r → BackD LD.ParsesDecl toks d′ r
decl← (decl-import di) toks e n =
  step (λ z → BackD LD.ParsesDecl z _ _) refl e (λ {toks′} e′ → di₁ (import← di toks′ e′))
  where
    di₁ : ∀ {toks′ d r} → BackD LI.ParsesImport toks′ d r → BackD LD.ParsesDecl (P.TWord "import" ∷ toks′) d r
    di₁ (rest , di , er) = rest , LD.pd-import di , er
decl← (decl-alias da) toks e n =
  step (λ z → BackD LD.ParsesDecl z _ _) refl e (λ e₁ →
  step (λ z → BackD LD.ParsesDecl (P.TWord "type" ∷ z) _ _) refl e₁ (λ {toks′} e₂ → da₁ (aliasd← da toks′ e₂)))
  where
    da₁ : ∀ {x toks′ d r} → BackD (LT.ParsesTypeAlias x []) toks′ d r → BackD LD.ParsesDecl (P.TWord "type" ∷ P.TWord x ∷ toks′) d r
    da₁ (rest , da , er) = rest , LD.pd-typealias (LT.pta-mk da) , er
decl← (decl-signature dT) toks e n =
  step (λ z → BackD LD.ParsesDecl z _ _) refl e (λ e₁ →
  step (λ z → BackD LD.ParsesDecl (P.TWord "signature" ∷ z) _ _) refl e₁ (λ e₂ →
  step (λ z → BackD LD.ParsesDecl (P.TWord "signature" ∷ P.TWord _ ∷ z) _ _) refl e₂ (λ {toks′} e₃ →
  ds₁ (sig← dT toks′ e₃))))
  where
    ds₁ : ∀ {x toks′ A′ r} → Σ[ A ∈ _ ] Σ[ rest ∈ List P.Token ] (Once.Parser.Generic.PolyInst.ParsesPolyType toks′ A rest × toPoly A ≡ A′ × F rest ≡ r)
        → BackD LD.ParsesDecl (P.TWord "signature" ∷ P.TWord x ∷ P.TColon ∷ toks′) (S.DSignature x A′) r
    ds₁ (A , rest , dA , refl , er) = rest , LD.pd-signature (LS.psig-mk refl dA) , er
decl← (decl-typesig (not-keyword a b c) dT ne) toks e n =
  step (λ z → BackD LD.ParsesDecl z _ _) refl e (λ e₁ →
  step (λ z → BackD LD.ParsesDecl (P.TWord _ ∷ z) _ _) refl e₁ (λ {toks′} e₂ →
  dt₁ ne (sig← dT toks′ e₂)))
  where
    dt₁ : ∀ {toks′ A′ r} → ¬ Starts r TEquals
        → Σ[ A ∈ _ ] Σ[ rest ∈ List P.Token ] (Once.Parser.Generic.PolyInst.ParsesPolyType toks′ A rest × toPoly A ≡ A′ × F rest ≡ r)
        → BackD LD.ParsesDecl (P.TWord _ ∷ P.TColon ∷ toks′) (S.DTypeSig _ A′) r
    dt₁ ne (A , rest , dA , refl , er) =
      rest , LD.pd-typesig a b c refl dA (eq-false (eq-view rest) (transport (λ z → ¬ Starts z TEquals) er ne)) , er
decl← (decl-fundef (not-keyword a b c) nc dF) toks e n =
  step (λ z → BackD LD.ParsesDecl z _ _) refl e (λ {toks′} e′ →
  df₁ (colon-false (colon-view toks′) (transport (λ z → ¬ Starts z TColon) e′ nc)) (fundef← dF toks′ e′ n))
  where
    df₁ : ∀ {toks′ d r} → colonHead toks′ ≡ false → BackD (LF.ParsesFunDef _) toks′ d r
        → BackD LD.ParsesDecl (P.TWord _ ∷ toks′) d r
    df₁ cf (rest , dF , er) = rest , LD.pd-fundef a b c cf dF , er
decl← (decl-op dc da) toks e n =
  step (λ z → BackD LD.ParsesDecl z _ _) refl e (λ {toks′} e′ → do₁ n da (opchars← dc toks′ e′))
  where
    do₂ : ∀ {toks′ x rest₁ d r} → LO.ParsesOpChars toks′ [] x rest₁ → BackD (LO.ParsesOpAfter x) rest₁ d r
        → BackD LD.ParsesDecl (P.TLParen ∷ toks′) d r
    do₂ dc (rest , da , er) = rest , LD.pd-opdecl (LO.pod-mk dc da) , er
    do₁ : ∀ {toks′ x ts₁ d r} → N r → G.ParsesOpAfter x ts₁ d r
        → Σ[ rest₁ ∈ List P.Token ] (LO.ParsesOpChars toks′ [] x rest₁ × F rest₁ ≡ ts₁)
        → BackD LD.ParsesDecl (P.TLParen ∷ toks′) d r
    do₁ n da (rest₁ , dc , e₁) = do₂ dc (opafter← da rest₁ e₁ n)

-- Newlines, read back.
skip← : ∀ {ts ts₁} → SkipNewlines ts ts₁ → ∀ toks → F toks ≡ ts
      → Σ[ nl ∈ List P.Token ] Σ[ toks₁ ∈ List P.Token ] (skipNewlines toks ≡ just (nl , toks₁) × F toks₁ ≡ ts₁)
skip← (skip-nl s) toks e =
  step (λ z → Σ[ nl ∈ List P.Token ] Σ[ toks₁ ∈ List P.Token ] (skipNewlines z ≡ just (nl , toks₁) × F toks₁ ≡ _)) refl e
    (λ {toks′} e′ → sn₁ toks′ (skip← s toks′ e′))
  where
    sn₁ : ∀ toks′ {ts₁} → Σ[ nl ∈ List P.Token ] Σ[ toks₁ ∈ List P.Token ] (skipNewlines toks′ ≡ just (nl , toks₁) × F toks₁ ≡ ts₁)
        → Σ[ nl ∈ List P.Token ] Σ[ toks₁ ∈ List P.Token ] (skipNewlines (P.TNewline ∷ toks′) ≡ just (nl , toks₁) × F toks₁ ≡ ts₁)
    sn₁ toks′ (nl , toks₁ , es , e₁) = P.TNewline ∷ nl , toks₁ , skip-nl-eq toks′ es , e₁
skip← (skip-done n) toks e = sd (skip-view toks) (transport (λ z → ¬ Starts z TNewline) e n) e
  where
    sd : ∀ {toks ts} → SkipView toks → ¬ Starts (F toks) TNewline → F toks ≡ ts
       → Σ[ nl ∈ List P.Token ] Σ[ toks₁ ∈ List P.Token ] (skipNewlines toks ≡ just (nl , toks₁) × F toks₁ ≡ ts)
    sd sk-nil _ e = [] , [] , refl , e
    sd sk-nl n _ = ⊥-elim (n starts)
    sd {toks} (sk-stop _ es) _ e = [] , toks , es , e

private
  trail-str : ∀ {s ts} → Trailing (TString s ∷ ts) → ⊥
  trail-str ()

  decl-str : ∀ {s ts d r} → G.ParsesDecl (TString s ∷ ts) d r → ⊥
  decl-str ()

-- What a declaration ends at, in a whole program, is no string literal.
decls-ns : ∀ {r ds r′} → G.ParsesDecls r ds r′ → Trailing r′ → N r
decls-ns (decls-stop (skip-done _) _) tr str-head = trail-str tr
decls-ns (decls-stop (skip-nl _) _) _ ()
decls-ns (decls-cons (skip-done _) d _) _ str-head = decl-str d
decls-ns (decls-cons (skip-nl _) _ _) _ ()

decls← : ∀ {ts ds r} → G.ParsesDecls ts ds r → Trailing r → ∀ toks → F toks ≡ ts
       → Σ[ rest ∈ List P.Token ] (LP.ParsesDecls toks ds rest × F rest ≡ r)
decls← (decls-stop sk nd) tr toks e = st₁ tr (skip← sk toks e)
  where
    st₁ : ∀ {ts₁} → Trailing ts₁
        → Σ[ nl ∈ List P.Token ] Σ[ toks₁ ∈ List P.Token ] (skipNewlines toks ≡ just (nl , toks₁) × F toks₁ ≡ ts₁)
        → Σ[ rest ∈ List P.Token ] (LP.ParsesDecls toks [] rest × F rest ≡ ts₁)
    st₁ tr (nl , toks₁ , es , refl) =
      toks₁ , LP.pds-stop es (decl-trail toks₁ tr (skip-not-nl (skip→ toks es))) , refl
decls← (decls-cons sk d ds) tr toks e = dc₁ (skip← sk toks e)
  where
    dc₃ : ∀ {toks₁ dd rest₁ nl} → skipNewlines toks ≡ just (nl , toks₁) → LD.ParsesDecl toks₁ dd rest₁
        → Σ[ rest ∈ List P.Token ] (LP.ParsesDecls rest₁ _ rest × F rest ≡ _)
        → Σ[ rest ∈ List P.Token ] (LP.ParsesDecls toks (dd ∷ _) rest × F rest ≡ _)
    dc₃ es d (rest , ds , er) = rest , LP.pds-cons es d ds , er
    dc₂ : ∀ {toks₁ nl} → skipNewlines toks ≡ just (nl , toks₁) → BackD LD.ParsesDecl toks₁ _ _
        → Σ[ rest ∈ List P.Token ] (LP.ParsesDecls toks _ rest × F rest ≡ _)
    dc₂ es (rest₁ , d′ , e₂) = dc₃ es d′ (decls← ds tr rest₁ e₂)
    dc₁ : Σ[ nl ∈ List P.Token ] Σ[ toks₁ ∈ List P.Token ] (skipNewlines toks ≡ just (nl , toks₁) × F toks₁ ≡ _)
        → Σ[ rest ∈ List P.Token ] (LP.ParsesDecls toks _ rest × F rest ≡ _)
    dc₁ (nl , toks₁ , es , e₁) = dc₂ es (decl← d toks₁ e₁ (decls-ns ds tr))

------------------------------------------------------------------------
-- A text
------------------------------------------------------------------------

-- The compiler's parse of a text is the Spec's.
parses→ : ∀ {text m} → LP.ParsesText text m → G.Parses text m
parses→ (toks , rest , lx , dd , at) = F toks , F rest , toNew lx , decls→ dd at , trail→ rest at

-- A text the Spec parses is one the compiler parses, into the same module.
parses← : ∀ {text m} → G.Parses text m → LP.ParsesText text m
parses← {text} (ts , r , lx , dd , tr) = pr₁ dd tr (toOld lx 0)
  where
    pr₂ : ∀ {toks ds} → LL.LexesChars 0 (toList text) toks
        → Σ[ rest ∈ List P.Token ] (LP.ParsesDecls toks ds rest × F rest ≡ r)
        → LP.ParsesText text (S.mkModule ds)
    pr₂ {toks} lx (rest , dd , refl) = toks , rest , lx , dd , trail← rest tr
    pr₁ : ∀ {ds} → G.ParsesDecls ts ds r → Trailing r
        → Σ[ toks ∈ List P.Token ] (LL.LexesChars 0 (toList text) toks × F toks ≡ ts)
        → LP.ParsesText text (S.mkModule ds)
    pr₁ dd tr (toks , lx , e) = pr₂ lx (decls← dd tr toks e)
