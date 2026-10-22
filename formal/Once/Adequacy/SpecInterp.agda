-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecInterp — an Interpretation of the Spec, read as the
-- compiler's.
--
-- The Spec's `Signature` names each declaration by its canonical name and
-- gives it a first-order `DeclType` (D318 item 5); its `Interp` is a MODEL
-- (the constants and pure functions) and a WORLD (an operation's answer, from
-- the calls it has seen, whenever one exists). The compiler's `ISig` keys a
-- declaration by its rendered name and its compiler type, and its `Impl`
-- answers by contract key (`Once.Internal.Contract`). This module translates the
-- first into the second, so a binary can be run against a Spec
-- Interpretation: each value key is read from the model, each answer key from
-- the world, with the history read as the Spec's events (`toEvent`).
--
-- A world answers only when an answer exists (`NotEmpty`); a well-formed
-- signature (`WellFormed`, which every Spec program carries) is what makes
-- every answer key's codomain inhabited.
------------------------------------------------------------------------

module Once.Adequacy.SpecInterp where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Spec.Word using (Carrier)
import Once.Internal.Value Carrier Carrier as M
import Once.Internal.Type as T
import Once.Spec.Type as T
import Once.Spec.Grade as G
open import Once.Internal.Name using (showCanonical)
open import Once.Internal.Core.Decl using (toISig)
open import Once.Spec.Name using (CanonicalName)
open import Once.Internal.Contract
  using (Key; key; kdom; kcod; ISig; Contract; answers; effect; contract-eff; contractOf;
         value-step; answer-step; valueKeys; answerKeys; Impl)
import Once.Internal.Contract as C
open import Once.Internal.Event using (SigOpEvent; toEvent)
open import Once.Internal.Trace using (Interp; interp)
import Once.Spec.Grade as SG
import Once.Spec.Signature as S
open S using (BTy; DeclType; constant; operation; _∶_; Signature; WellFormed; argAt; NotEmpty; op)
import Once.Spec.Observation as Obs

------------------------------------------------------------------------
-- Types and values
------------------------------------------------------------------------

qL : SG.Quantity → G.Quantity
qL SG.Zero = G.Zero
qL SG.One  = G.One
qL SG.Many = G.Many

-- A declaration's types are the Spec's (`⌜_⌝`, `⌜_⌝ᵈ`), at the ground index.
⌞_⌟ : BTy → T.Type
⌞_⌟ = S.⌜_⌝

declTy : DeclType → T.Type
declTy = S.⌜_⌝ᵈ

toB : ∀ b → M.⟦ ⌞ b ⌟ ⟧ → S.⟦ b ⟧ᵇ
fromB : ∀ b → S.⟦ b ⟧ᵇ → M.⟦ ⌞ b ⌟ ⟧
toB S.unit  v = v
toB S.void  v = v
toB S.int   v = v
toB S.float v = v
toB (a S.* b) (x , y) = toB a x , toB b y
toB (a S.+ b) (inj₁ x) = inj₁ (toB a x)
toB (a S.+ b) (inj₂ y) = inj₂ (toB b y)
fromB S.unit  v = v
fromB S.void  v = v
fromB S.int   v = v
fromB S.float v = v
fromB (a S.* b) (x , y) = fromB a x , fromB b y
fromB (a S.+ b) (inj₁ x) = inj₁ (fromB a x)
fromB (a S.+ b) (inj₂ y) = inj₂ (fromB b y)

------------------------------------------------------------------------
-- The contract a declaration owes
------------------------------------------------------------------------

-- What `contractOf` makes of a declaration: a constant and a pure function are
-- values (an erased argument read as `Unit`, D143); an operation answers, or
-- owes nothing when its answer type is `Unit` (it emits) or `Void` (it halts).
data DeclContract (s : String) : DeclType → Contract → Set where
  dc-const     : ∀ {b} → DeclContract s (constant b) (C.value (key s T.Unit ⌞ b ⌟))
  dc-value     : ∀ {a q b} → DeclContract s (S.value a q b) (C.value (key s ⌞ argAt q a ⌟ ⌞ b ⌟))
  dc-op-answer : ∀ {a q b} → ⌞ b ⌟ ≢ T.Void → ⌞ b ⌟ ≢ T.Unit
               → DeclContract s (operation a q b) (answers (key s ⌞ argAt q a ⌟ ⌞ b ⌟))
  dc-op-effect : ∀ {a q b} → DeclContract s (operation a q b) effect

private
  opC : ∀ {s a q b} (dv : Dec (⌞ b ⌟ ≡ T.Void)) (du : Dec (⌞ b ⌟ ≡ T.Unit))
      → DeclContract s (operation a q b) (contract-eff s ⌞ argAt q a ⌟ ⌞ b ⌟ dv du)
  opC (yes _)  _        = dc-op-effect
  opC (no _)   (yes _)  = dc-op-effect
  opC (no ¬v)  (no ¬u)  = dc-op-answer ¬v ¬u

  constC : ∀ s b → DeclContract s (constant b) (contractOf s ⌞ b ⌟)
  constC s S.unit      = dc-const
  constC s S.void      = dc-const
  constC s S.int       = dc-const
  constC s S.float     = dc-const
  constC s (a S.* b)   = dc-const
  constC s (a S.+ b)   = dc-const

declContract : ∀ s t → DeclContract s t (contractOf s (declTy t))
declContract s (constant b)              = constC s b
declContract s (S.value a SG.Zero b)     = dc-value
declContract s (S.value a SG.One  b)     = dc-value
declContract s (S.value a SG.Many b)     = dc-value
declContract s (operation a SG.Zero b)   = opC (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟)
declContract s (operation a SG.One  b)   = opC (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟)
declContract s (operation a SG.Many b)   = opC (T.isVoid? ⌞ b ⌟) (T.isUnit? ⌞ b ⌟)

-- An answering operation's answer type is inhabited in a well-formed signature.
answer-inhabited : ∀ {a q b} → S.WellFormedDecl (operation a q b)
                 → ⌞ b ⌟ ≢ T.Void → ⌞ b ⌟ ≢ T.Unit → NotEmpty b
answer-inhabited (inj₁ refl)               ¬v ¬u = ⊥-elim (¬u refl)
answer-inhabited (inj₂ (inj₁ refl))        ¬v ¬u = ⊥-elim (¬v refl)
answer-inhabited (inj₂ (inj₂ (ne , _)))    ¬v ¬u = ne

------------------------------------------------------------------------
-- The implementation
------------------------------------------------------------------------

module _ (Σ : Signature) (J : Obs.Interp Σ) where
  open Obs Σ using (Model; World; module Model; module World)
  open Obs.Interp J using (model; world)
  open Model model using (constantᵐ; valueᵐ)
  open World world using (answer)

  -- Walking a suffix `Σ′` of `Σ`, each declaration found in `Σ`.
  pureAt : ∀ (Σ′ : Signature) → (∀ {d} → d ∈ Σ′ → d ∈ Σ)
         → (k : Key) → k ∈ valueKeys (toISig Σ′) → M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧
  pureStep : ∀ {c t ct} (Σ′ : Signature) → (∀ {d} → d ∈ ((c ∶ t) ∷ Σ′) → d ∈ Σ)
           → DeclContract (showCanonical c) t ct
           → (k : Key) → k ∈ value-step ct (valueKeys (toISig Σ′)) → M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧
  pureAt []              inj k ()
  pureAt ((c ∶ t) ∷ Σ′) inj k p = pureStep Σ′ inj (declContract (showCanonical c) t) k p
  pureStep {t = constant b}    Σ′ inj dc-const     k (here refl) x = fromB b (constantᵐ (inj (here refl)))
  pureStep {t = S.value a q b} Σ′ inj dc-value     k (here refl) x = fromB b (valueᵐ (inj (here refl)) (toB (argAt q a) x))
  pureStep Σ′ inj dc-const           k (there p) x = pureAt Σ′ (λ m → inj (there m)) k p x
  pureStep Σ′ inj dc-value           k (there p) x = pureAt Σ′ (λ m → inj (there m)) k p x
  pureStep Σ′ inj (dc-op-answer _ _) k p x         = pureAt Σ′ (λ m → inj (there m)) k p x
  pureStep Σ′ inj dc-op-effect       k p x         = pureAt Σ′ (λ m → inj (there m)) k p x

  -- An operation's answer, at the inhabitant its answer type is decided to
  -- have (the one the Spec's trace asks the world at, `Observation.after`).
  answerAt-dec : ∀ (o : S.Op Σ) → Obs.History Σ → S.⟦ S.arg o ⟧ᵇ → Dec (NotEmpty (S.Op.ans o)) → NotEmpty (S.Op.ans o)
               → S.⟦ S.Op.ans o ⟧ᵇ
  answerAt-dec o h x (yes p) _  = answer o h x p
  answerAt-dec o h x (no ¬p) ne = ⊥-elim (¬p ne)

  answerAt : ∀ (Σ′ : Signature) → (∀ {d} → d ∈ Σ′ → d ∈ Σ) → WellFormed Σ′
           → List SigOpEvent → (k : Key) → k ∈ answerKeys (toISig Σ′) → M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧
  answerStep : ∀ {c t ct} (Σ′ : Signature) → (∀ {d} → d ∈ ((c ∶ t) ∷ Σ′) → d ∈ Σ)
             → S.WellFormedDecl t → WellFormed Σ′ → DeclContract (showCanonical c) t ct
             → List SigOpEvent → (k : Key) → k ∈ answer-step ct (answerKeys (toISig Σ′))
             → M.⟦ kdom k ⟧ → M.⟦ kcod k ⟧
  answerAt []              inj wf       h k ()
  answerAt ((c ∶ t) ∷ Σ′) inj (w S.∷ wf) h k p = answerStep Σ′ inj w wf (declContract (showCanonical c) t) h k p
  answerStep {t = operation a q b} Σ′ inj w wf (dc-op-answer ¬v ¬u) h k (here refl) x =
    fromB b (answerAt-dec (op (inj (here refl))) (map toEvent h) (toB (argAt q a) x) (S.notEmpty? b)
                          (answer-inhabited {a = a} {q = q} w ¬v ¬u))
  answerStep Σ′ inj w wf (dc-op-answer _ _) h k (there p) x = answerAt Σ′ (λ m → inj (there m)) wf h k p x
  answerStep Σ′ inj w wf dc-const           h k p x = answerAt Σ′ (λ m → inj (there m)) wf h k p x
  answerStep Σ′ inj w wf dc-value           h k p x = answerAt Σ′ (λ m → inj (there m)) wf h k p x
  answerStep Σ′ inj w wf dc-op-effect       h k p x = answerAt Σ′ (λ m → inj (there m)) wf h k p x

  -- The compiler's implementation of `Σ`, read from `J`.
  toImpl : WellFormed Σ → Impl (toISig Σ)
  toImpl wf = record
    { answerI = λ h k p x → answerAt Σ (λ m → m) wf h k p x
    ; pureI   = λ k p x → pureAt Σ (λ m → m) k p x
    }

-- The compiler's Interpretation of a well-formed Spec signature.
toInterp : (Σ : Signature) → WellFormed Σ → Obs.Interp Σ → Interp
toInterp Σ wf J = interp (toISig Σ) (toImpl Σ J wf)

------------------------------------------------------------------------
-- Well-formedness, decided
------------------------------------------------------------------------

private
  both? : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
  both? (yes a) (yes b) = yes (a , b)
  both? (no ¬a) _       = no λ { (a , _) → ¬a a }
  both? (yes _) (no ¬b) = no λ { (_ , b) → ¬b b }

  either? : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
  either? (yes a) _       = yes (inj₁ a)
  either? (no _)  (yes b) = yes (inj₂ b)
  either? (no ¬a) (no ¬b) = no λ { (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b }

  notSingleton? : ∀ b → Dec (S.NotSingleton b)
  notSingleton? S.unit    = no λ ()
  notSingleton? S.void    = yes tt
  notSingleton? S.int     = yes tt
  notSingleton? S.float   = yes tt
  notSingleton? (a S.* b) = either? (notSingleton? a) (notSingleton? b)
  notSingleton? (a S.+ b) = either? (both? (S.notEmpty? a) (S.notEmpty? b)) (both? (notSingleton? a) (notSingleton? b))

  -- A value's codomain: inhabited and not `unit`.
  valueCod? : ∀ b → Dec (NotEmpty b × b ≢ S.unit)
  valueCod? S.unit    = no λ { (_ , ¬u) → ¬u refl }
  valueCod? S.void    = no λ { (() , _) }
  valueCod? S.int     = yes (tt , λ ())
  valueCod? S.float   = yes (tt , λ ())
  valueCod? (a S.* b) = map-ne (S.notEmpty? (a S.* b))
    where map-ne : Dec (NotEmpty (a S.* b)) → Dec (NotEmpty (a S.* b) × a S.* b ≢ S.unit)
          map-ne (yes p) = yes (p , λ ())
          map-ne (no ¬p) = no λ { (p , _) → ¬p p }
  valueCod? (a S.+ b) = map-ne (S.notEmpty? (a S.+ b))
    where map-ne : Dec (NotEmpty (a S.+ b)) → Dec (NotEmpty (a S.+ b) × a S.+ b ≢ S.unit)
          map-ne (yes p) = yes (p , λ ())
          map-ne (no ¬p) = no λ { (p , _) → ¬p p }

  -- An operation's codomain: `unit`, `void`, or inhabited and not a singleton.
  effCod? : ∀ b → Dec (S.EffCod b)
  effCod? S.unit    = yes (inj₁ refl)
  effCod? S.void    = yes (inj₂ (inj₁ refl))
  effCod? S.int     = yes (inj₂ (inj₂ (tt , tt)))
  effCod? S.float   = yes (inj₂ (inj₂ (tt , tt)))
  effCod? (a S.* b) = data? (both? (S.notEmpty? (a S.* b)) (notSingleton? (a S.* b)))
    where data? : Dec (NotEmpty (a S.* b) × S.NotSingleton (a S.* b)) → Dec (S.EffCod (a S.* b))
          data? (yes p) = yes (inj₂ (inj₂ p))
          data? (no ¬p) = no λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ p)) → ¬p p }
  effCod? (a S.+ b) = data? (both? (S.notEmpty? (a S.+ b)) (notSingleton? (a S.+ b)))
    where data? : Dec (NotEmpty (a S.+ b) × S.NotSingleton (a S.+ b)) → Dec (S.EffCod (a S.+ b))
          data? (yes p) = yes (inj₂ (inj₂ p))
          data? (no ¬p) = no λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ p)) → ¬p p }

  wellFormedDecl? : ∀ t → Dec (S.WellFormedDecl t)
  wellFormedDecl? (constant b)      = valueCod? b
  wellFormedDecl? (S.value a q b)   = valueCod? b
  wellFormedDecl? (operation a q b) = effCod? b

wellFormed? : (Σ : Signature) → Dec (WellFormed Σ)
wellFormed? []              = yes S.[]
wellFormed? ((c ∶ t) ∷ Σ′) = cons? (wellFormedDecl? t) (wellFormed? Σ′)
  where cons? : Dec (S.WellFormedDecl t) → Dec (WellFormed Σ′) → Dec (WellFormed ((c ∶ t) ∷ Σ′))
        cons? (yes w) (yes ws) = yes (w S.∷ ws)
        cons? (no ¬w) _        = no λ { (w S.∷ _) → ¬w w }
        cons? (yes _) (no ¬ws) = no λ { (_ S.∷ ws) → ¬ws ws }
