-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.FrontEndBridge — the front-end (lexer + parser) correctness
-- bridge (Plan 0.52). `ParsesText` is the INDEPENDENT grammar/relational parse
-- spec the apex `_⊢R_` anchors on; `parseStrict-sound`/`-complete` force the
-- executable front-end (`parseStrict`) to agree with it.
--
-- `parseStrict-sound`/`-complete` are PROVEN here (no longer apex postulates),
-- by decomposing the front-end:  text --[lexer]--> tokens --[parser]--> Module.
-- `ParsesText text m := ∃ toks rest, Lexes text toks × ParsesModule toks m rest
--                       × allTrailing rest ≡ true`.
--
-- PROVEN here: the `parseStrict` glue (`parseStrict`/`parseModule` were
-- refactored clause-based so they reduce) and the module wrapper.
-- REMAINING decomposed obligations (`make postulates`; each strictly smaller
-- than the old opaque whole-front-end axiom):
--   * LEXER   — `Lexes` + `lexer-sound`/`-complete` (deferred sub-stage).
--   * PER-DECL — `ParsesDecl` + `sound-decl`/`complete-decl` (grammar work,
--     to build from the expr/type islands per decl form).
--   * DECLS LOOP — `sound-decls`/`complete-decls` (the `parseDeclsWF` WF bridge;
--     relation `ParsesDecls` is DEFINED here).
------------------------------------------------------------------------

module Once.Adequacy.FrontEndBridge where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (_<_; _≤_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (<-≤-trans)
open import Induction.WellFounded using (Acc; acc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Parser.Token using (Token)
open import Once.Parser.Module.Core using (Decl; Module; mkModule; ParseAtB)
open Module using (decls)
open import Once.Parser.Lexer using (tokenizeString)
open import Once.Parser.Core using (skipNewlines)
open import Once.Parser.Module
  using (parseModule; parseModule-pd; parseDecls; parseDeclsWF; parseDeclB;
         pdwf-sk; pdwf-dc; skipNewlines-≤)
open import Once.Parser
  using (allTrailing; parseStrict; parseStrict-pm; parseStrict-at)

------------------------------------------------------------------------
-- LEXER. The genuine independent char-production relation `Lexes` +
-- `lexer-sound`/`lexer-complete` now come from `Once.Adequacy.LexerBridge`
-- (relation over `LexesChars`; soundness for all 27 special heads + full
-- determinism + completeness = sound ∘ det, all GENUINELY PROVEN). The single
-- remaining `LexerBridge.lexes-tok-gen` postulate (general-head reduction; needs
-- `tokenize-WF`'s head routed through a `headK` classifier) is scoped INSIDE that
-- module — the three opaque postulates that were here are now retired.
------------------------------------------------------------------------

open import Once.Spec.Lexing public using (Lexes)
open import Once.Adequacy.LexerBridge using (lexer-sound; lexer-complete)

------------------------------------------------------------------------
-- PER-DECL parser obligation — now DISCHARGED (was postulated). The relation
-- `ParsesDecl` (a sum of the six decl forms) + `sound-decl`/`complete-decl` are
-- proven in `Once.Grammar.DeclBridge`, bottoming at the expr/type/poly islands.
------------------------------------------------------------------------

open import Once.Grammar.DeclBridge using (ParsesDecl; sound-decl; complete-decl) public

------------------------------------------------------------------------
-- DECLS LOOP — relation DEFINED (mirrors `parseDeclsWF`); bridge postulated.
-- (`skipNewlines` never returns `nothing`, so there is no no-skip case.)
------------------------------------------------------------------------

data ParsesDecls : List Token → List Decl → List Token → Set where
  -- `skipNewlines` never returns `nothing`; this aligns the relation with
  -- `pdwf-sk`'s (unreachable) `nothing` clause.
  pds-noskip : ∀ {toks} → skipNewlines toks ≡ nothing → ParsesDecls toks [] toks
  pds-stop : ∀ {toks nl toks'} →
    skipNewlines toks ≡ just (nl , toks') → parseDeclB toks' ≡ nothing →
    ParsesDecls toks [] toks'
  pds-cons : ∀ {toks nl toks' d rest ds rest'} →
    skipNewlines toks ≡ just (nl , toks') → ParsesDecl toks' d rest →
    ParsesDecls rest ds rest' →
    ParsesDecls toks (d ∷ ds) rest'

-- DECLS-LOOP soundness — PROVEN over the de-`with`'d `pdwf-sk`/`pdwf-dc` by
-- casing their result PARAMETERS (the `with`-clash is gone). Mutual, terminating
-- on the same `Acc` as `parseDeclsWF`.
SkBnd : (toks : List Token) (sk : Maybe (List Token × List Token)) → Set
SkBnd toks sk = ∀ {nl toks'} → sk ≡ just (nl , toks') → length toks' ≤ length toks

sound-declsWF  : ∀ (toks : List Token) (a : Acc _<_ (length toks)) →
  ParsesDecls toks (proj₁ (parseDeclsWF toks a)) (proj₁ (proj₂ (parseDeclsWF toks a)))
sound-pdwf-sk : ∀ (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
  (sk : Maybe (List Token × List Token)) (bnd : SkBnd toks sk) (eq : skipNewlines toks ≡ sk) →
  ParsesDecls toks (proj₁ (pdwf-sk toks rec sk bnd)) (proj₁ (proj₂ (pdwf-sk toks rec sk bnd)))
sound-pdwf-dc : ∀ (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
  (toks' : List Token) (skipBnd : length toks' ≤ length toks)
  (pd : ParseAtB {Decl} toks') (pdeq : parseDeclB toks' ≡ pd)
  (nl : List Token) (skeq : skipNewlines toks ≡ just (nl , toks')) →
  ParsesDecls toks (proj₁ (pdwf-dc toks rec toks' skipBnd pd)) (proj₁ (proj₂ (pdwf-dc toks rec toks' skipBnd pd)))

sound-declsWF toks (acc rec) = sound-pdwf-sk toks rec (skipNewlines toks) (skipNewlines-≤ toks) refl

sound-pdwf-sk toks rec nothing             bnd eq = pds-noskip eq
sound-pdwf-sk toks rec (just (nl , toks')) bnd eq =
  sound-pdwf-dc toks rec toks' (bnd refl) (parseDeclB toks') refl nl eq

sound-pdwf-dc toks rec toks' skipBnd nothing                     pdeq nl skeq = pds-stop skeq pdeq
sound-pdwf-dc toks rec toks' skipBnd (just (d , rest , declBnd)) pdeq nl skeq =
  pds-cons skeq (sound-decl pdeq) (sound-declsWF rest (rec (<-≤-trans declBnd skipBnd)))

sound-decls : ∀ {toks ds rest} → parseDecls toks ≡ just (ds , rest) → ParsesDecls toks ds rest
sound-decls {toks} {ds} {rest} eq =
  subst (λ p → ParsesDecls toks (proj₁ p) (proj₂ p))
        (just-injective eq)
        (sound-declsWF toks (<-wellFounded (length toks)))

-- COMPLETENESS — induct on the `ParsesDecls` derivation. `pdwf-sk` reduces under
-- the derivation's `skipNewlines toks ≡ …` (via `trans (sym eq) skeq` rewriting
-- the `sk` PARAMETER — no self-referential `refl`, so no with-clash).
complete-declsWF : ∀ {toks ds rest} (a : Acc _<_ (length toks)) → ParsesDecls toks ds rest →
  (proj₁ (parseDeclsWF toks a) ≡ ds) × (proj₁ (proj₂ (parseDeclsWF toks a)) ≡ rest)
complete-pdwf-sk : ∀ (toks : List Token) (rec : ∀ {y} → y < length toks → Acc _<_ y)
  (sk : Maybe (List Token × List Token)) (bnd : SkBnd toks sk) (eq : skipNewlines toks ≡ sk)
  {ds rest} → ParsesDecls toks ds rest →
  (proj₁ (pdwf-sk toks rec sk bnd) ≡ ds) × (proj₁ (proj₂ (pdwf-sk toks rec sk bnd)) ≡ rest)

complete-declsWF {toks} (acc rec) deriv =
  complete-pdwf-sk toks rec (skipNewlines toks) (skipNewlines-≤ toks) refl deriv

complete-pdwf-sk toks rec sk bnd eq (pds-noskip skeq)
  rewrite trans (sym eq) skeq = refl , refl
complete-pdwf-sk toks rec sk bnd eq (pds-stop skeq decleq)
  rewrite trans (sym eq) skeq | decleq = refl , refl
complete-pdwf-sk toks rec sk bnd eq (pds-cons skeq pdcl restderiv)
  rewrite trans (sym eq) skeq with complete-decl pdcl
... | (declBnd' , pdeq) rewrite pdeq
    with complete-declsWF (rec (<-≤-trans declBnd' (bnd refl))) restderiv
...   | (eqds , eqrest) = cong (_ ∷_) eqds , eqrest

complete-decls : ∀ {toks ds rest} → ParsesDecls toks ds rest → parseDecls toks ≡ just (ds , rest)
complete-decls {toks} {ds} {rest} deriv with complete-declsWF (<-wellFounded (length toks)) deriv
... | (eqds , eqrest) = cong₂ (λ a b → just (a , b)) eqds eqrest

------------------------------------------------------------------------
-- MODULE wrapper — PROVEN (`ParsesModule` over `ParsesDecls`, via the record
-- accessor so it reduces for an abstract `m`; record eta ties `mkModule (decls
-- m) ≡ m`).
------------------------------------------------------------------------

ParsesModule : List Token → Module → List Token → Set
ParsesModule toks m rest = ParsesDecls toks (decls m) rest

-- `parseDecls` always succeeds (it wraps the total `parseDeclsWF`).
parseDecls-total : ∀ (toks : List Token) →
  Σ[ ds ∈ List Decl ] Σ[ rest ∈ List Token ] parseDecls toks ≡ just (ds , rest)
parseDecls-total toks with parseDeclsWF toks (<-wellFounded (length toks))
... | (ds , rest , _) = ds , rest , refl

complete-module : ∀ {toks m rest} → ParsesModule toks m rest → parseModule toks ≡ just (m , rest)
complete-module {toks} {m} {rest} pm =
  cong (λ z → parseModule-pd z toks) (complete-decls pm)

sound-module : ∀ {toks m rest} → parseModule toks ≡ just (m , rest) → ParsesModule toks m rest
sound-module {toks} {m} {rest} pmEq with parseDecls-total toks
... | (ds , rest' , pdEq) =
  subst (λ p → ParsesModule toks (proj₁ p) (proj₂ p))
        (sym (just-injective (trans (sym pmEq) (cong (λ z → parseModule-pd z toks) pdEq))))
        (sound-decls pdEq)

------------------------------------------------------------------------
-- ParsesText — the apex anchor. PROVEN bridges to the executable front-end.
------------------------------------------------------------------------

ParsesText : String → Module → Set
ParsesText text m =
  Σ[ toks ∈ List Token ] Σ[ rest ∈ List Token ]
    (Lexes text toks × ParsesModule toks m rest × (allTrailing rest ≡ true))

-- Explicit `trans`/`cong` chain (NOT `rewrite`): `parseModule toks` partially
-- normalises once the `<-wellFounded` Acc reduces, so `rewrite` can't locate it
-- as a subterm; `cong` threads the equalities through `parseStrict-pm` cleanly.
parseStrict-complete :
  ∀ (text : String) (m : Module) → ParsesText text m → parseStrict text ≡ inj₂ m
parseStrict-complete text m (toks , rest , lx , pm , at) =
  trans (cong (λ t → parseStrict-pm (parseModule t)) (lexer-complete text toks lx))
  (trans (cong parseStrict-pm (complete-module {toks} {m} {rest} pm))
         (cong (parseStrict-at rest m) at))

-- `parseModule` on the lexed text always succeeds.
parseModule-total-at : ∀ (text : String) →
  Σ[ m' ∈ Module ] Σ[ r ∈ List Token ] parseModule (tokenizeString text) ≡ just (m' , r)
parseModule-total-at text with parseDecls-total (tokenizeString text)
... | (ds , r , pdEq) = mkModule ds , r , cong (λ z → parseModule-pd z (tokenizeString text)) pdEq

-- Inversion of `parseStrict`'s clause-based dispatch (`parseStrict-pm` /
-- `parseStrict-at`): a success pins `allTrailing` true and the parsed module.
parseStrict-sound :
  ∀ (text : String) (m : Module) → parseStrict text ≡ inj₂ m → ParsesText text m
parseStrict-sound text m eq with parseModule-total-at text
... | (m' , r , pmEq) = go (allTrailing r) refl
  where
    -- after rewriting parseModule by `pmEq`, the success equation lands on the
    -- `parseStrict-at` dispatch.
    eqAt : parseStrict-at r m' (allTrailing r) ≡ inj₂ m
    eqAt = subst (λ z → parseStrict-pm z ≡ inj₂ m) pmEq eq
    go : (b : Bool) → allTrailing r ≡ b → ParsesText text m
    go b atEq = goB b (subst (λ a → parseStrict-at r m' a ≡ inj₂ m) atEq eqAt) atEq
      where
        goB : (b : Bool) → parseStrict-at r m' b ≡ inj₂ m → allTrailing r ≡ b → ParsesText text m
        goB true  eqB atEq =
          tokenizeString text , r , lexer-sound text ,
          sound-module (trans pmEq (cong (λ x → just (x , r)) (inj₂-injective eqB))) , atEq
        goB false () atEq
