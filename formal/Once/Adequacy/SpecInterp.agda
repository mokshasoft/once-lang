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
-- answers by contract key (`Once.Contract`). This module translates the
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
open import Once.Spec.Numerics using (TargetNum; module TargetNum)
open TargetNum using (float-format)
open import Once.Spec.Float.Value using (fitV)
open import Once.Spec.Float.Encoding using (encode; decode)
import Once.Float.Word as FW
open import Once.Float.EncodingLaws using (decode-encode)
open import Once.Metatheory.Float.Range using (fitV-inRange; fitV-idem)
open import Once.Spec.Boundary using (readAt)
open import Once.IR.Semantics.Boundary using (atTarget)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Spec.Word using (Carrier)
import Once.IR.Semantics.Value Carrier Carrier as M
import Once.Type.Core as T
import Once.Spec.Type as T
import Once.Spec.Grade as G
open import Once.Name using (showCanonical)
open import Once.Core.Decl using (toISig)
open import Once.Spec.Name using (CanonicalName)
open import Once.Contract
  using (Key; key; kdom; kcod; ISig; Contract; answers; effect; contract-eff; contractOf;
         value-step; answer-step; valueKeys; answerKeys; Impl)
import Once.Contract as C
open import Once.IR.Semantics.Event using (SigOpEvent; toEvent)
open import Once.IR.Semantics.Trace using (Interp; interp)
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

-- The base conversions, at a target: a `Float` crosses as its value
-- (`decode`) one way and as the encoding of the value read at the format
-- (`encode ∘ fitV`, plan 0.150 R2) the other; the rest is the identity.
toB : TargetNum → ∀ b → M.⟦ ⌞ b ⌟ ⟧ → S.⟦ b ⟧ᵇ
fromB : TargetNum → ∀ b → S.⟦ b ⟧ᵇ → M.⟦ ⌞ b ⌟ ⟧
toB tn S.unit  v = v
toB tn S.void  v = v
toB tn S.int   v = v
toB tn S.float v = decode (float-format tn) v
toB tn (a S.* b) (x , y) = toB tn a x , toB tn b y
toB tn (a S.+ b) (inj₁ x) = inj₁ (toB tn a x)
toB tn (a S.+ b) (inj₂ y) = inj₂ (toB tn b y)
fromB tn S.unit  v = v
fromB tn S.void  v = v
fromB tn S.int   v = v
fromB tn S.float v = encode (float-format tn) (fitV (float-format tn) v)
fromB tn (a S.* b) (x , y) = fromB tn a x , fromB tn b y
fromB tn (a S.+ b) (inj₁ x) = inj₁ (fromB tn a x)
fromB tn (a S.+ b) (inj₂ y) = inj₂ (fromB tn b y)

-- | A machine value with its floats read at the format (`Float.Word.fit`):
-- what a `Float` word means, as a word.
canonB : TargetNum → ∀ b → M.⟦ ⌞ b ⌟ ⟧ → M.⟦ ⌞ b ⌟ ⟧
canonB tn S.unit  v = v
canonB tn S.void  v = v
canonB tn S.int   v = v
canonB tn S.float v = FW.fit (float-format tn) v
canonB tn (a S.* b) (x , y) = canonB tn a x , canonB tn b y
canonB tn (a S.+ b) (inj₁ x) = inj₁ (canonB tn a x)
canonB tn (a S.+ b) (inj₂ y) = inj₂ (canonB tn b y)

-- | A machine value, read and written back, is its canonical form.
fromB-toB : ∀ tn b x → canonB tn b x ≡ fromB tn b (toB tn b x)
fromB-toB tn S.unit  x = refl
fromB-toB tn S.void  x = refl
fromB-toB tn S.int   x = refl
fromB-toB tn S.float x = refl
fromB-toB tn (a S.* b) (x , y) = cong₂ _,_ (fromB-toB tn a x) (fromB-toB tn b y)
fromB-toB tn (a S.+ b) (inj₁ x) = cong inj₁ (fromB-toB tn a x)
fromB-toB tn (a S.+ b) (inj₂ y) = cong inj₂ (fromB-toB tn b y)

private
  -- A value read at the format is one, so its encoding decodes back to it.
  fit-enc : ∀ F v → FW.fit F (encode F (fitV F v)) ≡ encode F (fitV F (fitV F v))
  fit-enc F v = cong (λ u → encode F (fitV F u)) (decode-encode F (fitV F v) (fitV-inRange F v))

-- | A written value is canonical.
canonB-fromB : ∀ tn b y → canonB tn b (fromB tn b y) ≡ fromB tn b y
canonB-fromB tn S.unit  y = refl
canonB-fromB tn S.void  y = refl
canonB-fromB tn S.int   y = refl
canonB-fromB tn S.float y = trans (fit-enc F y) (cong (encode F) (fitV-idem F y))
  where F = float-format tn
canonB-fromB tn (a S.* b) (x , y) = cong₂ _,_ (canonB-fromB tn a x) (canonB-fromB tn b y)
canonB-fromB tn (a S.+ b) (inj₁ x) = cong inj₁ (canonB-fromB tn a x)
canonB-fromB tn (a S.+ b) (inj₂ y) = cong inj₂ (canonB-fromB tn b y)

-- | Reading at the target sees through the canonical form (`fit` is
-- idempotent on words).
atTarget-canonB : ∀ tn b x → atTarget tn ⌞ b ⌟ (canonB tn b x) ≡ atTarget tn ⌞ b ⌟ x
atTarget-canonB tn S.unit  x = refl
atTarget-canonB tn S.void  x = refl
atTarget-canonB tn S.int   x = refl
atTarget-canonB tn S.float x =
  trans (cong (λ u → encode F (fitV F u)) (decode-encode F (fitV F (decode F x)) (fitV-inRange F (decode F x))))
        (cong (encode F) (fitV-idem F (decode F x)))
  where F = float-format tn
atTarget-canonB tn (a S.* b) (x , y)  = cong₂ _,_ (atTarget-canonB tn a x) (atTarget-canonB tn b y)
atTarget-canonB tn (a S.+ b) (inj₁ x) = cong inj₁ (atTarget-canonB tn a x)
atTarget-canonB tn (a S.+ b) (inj₂ y) = cong inj₂ (atTarget-canonB tn b y)

-- | The implementation's `atTarget` is the Spec's `readAt`, leaf by leaf.
fromB-at : ∀ (tn : TargetNum) b (v : S.⟦ b ⟧ᵇ) → atTarget tn ⌞ b ⌟ (fromB tn b v) ≡ fromB tn b (readAt tn b v)
fromB-at tn S.unit  v = refl
fromB-at tn S.void  v = refl
fromB-at tn S.int   v = refl
fromB-at tn S.float v = fit-enc (float-format tn) v
fromB-at tn (a S.* b) (x , y)  = cong₂ _,_ (fromB-at tn a x) (fromB-at tn b y)
fromB-at tn (a S.+ b) (inj₁ x) = cong inj₁ (fromB-at tn a x)
fromB-at tn (a S.+ b) (inj₂ y) = cong inj₂ (fromB-at tn b y)

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

module _ (tn : TargetNum) (Σ : Signature) (J : Obs.Interp Σ) where
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
  pureStep {t = constant b}    Σ′ inj dc-const     k (here refl) x = fromB tn b (constantᵐ (inj (here refl)))
  pureStep {t = S.value a q b} Σ′ inj dc-value     k (here refl) x = fromB tn b (valueᵐ (inj (here refl)) (toB tn (argAt q a) x))
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
    fromB tn b (answerAt-dec (op (inj (here refl))) (map (toEvent (float-format tn)) h) (toB tn (argAt q a) x) (S.notEmpty? b)
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
toInterp : TargetNum → (Σ : Signature) → WellFormed Σ → Obs.Interp Σ → Interp
toInterp tn Σ wf J = interp (toISig Σ) (toImpl tn Σ J wf)

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
