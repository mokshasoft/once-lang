------------------------------------------------------------------------
-- Theory.Models.StrongCCL3.NormalForm
--
-- Proof that the encoding from Theory.Models.StrongCCL3.Encoding
-- always produces βη-normal forms.
--
-- Strategy:
--   - Helper lemmas for atomic constants being NF (at non-Void source).
--   - Helper lemma for compositions In ∘ X / inl ∘ X / inr ∘ X being
--     NF given X is NF and the head pattern doesn't trigger any rule.
--   - Main theorem encode-is-nf by structural induction on g.
--
-- KEY OBSERVATION:
--   `initial-unique : ∀ {A} {f : Term Void A} → f ⟶s initial`
--   means ANY morphism with source Void reduces. Our encoded terms
--   always have source Unit (encode g : Term Unit Code), so this
--   doesn't apply at the outer level. Sub-Terms within the encoding
--   also have source Unit by construction (the encoding pre-composes
--   with terminal where needed). So source-Void cases are handled by
--   construction of the encoding.
--
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

module Theory.Models.StrongCCL3.NormalForm where

open import Relation.Nullary using (¬_)
open import Theory.Models.StrongCCL3.Encoding
import Theory.Syntax.StrongCCL.CCT3 as Syn
open Syn using
  ( Ty; Unit; _×_; _⇒_; Void; _⊎_; μ
  ; Term; id; _∘_; terminal; fst; snd; ⟨_,_⟩
  ; curry; apply; initial; inl; inr; [_,_]
  ; In; Out; cata; fmap
  ; _⟶βη_; _⟶βη*_; IsβηNormalForm
  ; β-rule; η-rule; s-rule
  ; from-CCTB-β; from-CCT1-β; from-CCT2-β; from-CCT3-β
  ; from-CCTB-s; from-CCT2-s )

open Syn.βη-Closure using (base; ∘-congˡ; ∘-congʳ;
                            ⟨,⟩-congˡ; ⟨,⟩-congʳ;
                            curry-cong; [,]-congˡ; [,]-congʳ;
                            cata-cong; fmap-cong)

------------------------------------------------------------------------
-- Atomic NF lemmas
--
-- Each atomic constructor at a non-Void source is NF. Proofs are
-- uniform: pattern-match on each base-rule category and use Agda's
-- absurd pattern () to rule out non-matching rule LHS shapes.
------------------------------------------------------------------------

terminal-nf : IsβηNormalForm (terminal {Unit})
terminal-nf (base (β-rule (from-CCTB-β ())))
terminal-nf (base (β-rule (from-CCT1-β ())))
terminal-nf (base (β-rule (from-CCT2-β ())))
terminal-nf (base (β-rule (from-CCT3-β ())))
terminal-nf (base (η-rule ()))
terminal-nf (base (s-rule (from-CCTB-s ())))
terminal-nf (base (s-rule (from-CCT2-s ())))

-- In is NF when its source TermF Code is not Void. Our specific TermF
-- has TermF X containing 10 Unit summands plus 3 X's plus 3 (X × X)'s,
-- so TermF Code ≠ Void. Specializing to In {TermF}.
In-nf : IsβηNormalForm (In {TermF})
In-nf (base (β-rule (from-CCTB-β ())))
In-nf (base (β-rule (from-CCT1-β ())))
In-nf (base (β-rule (from-CCT2-β ())))
In-nf (base (β-rule (from-CCT3-β ())))
In-nf (base (η-rule ()))
In-nf (base (s-rule (from-CCTB-s ())))
In-nf (base (s-rule (from-CCT2-s ())))

-- inl at non-Void source; specialized to source Unit (which is what
-- the encoding uses).
inl-Unit-nf : ∀ {B} → IsβηNormalForm (inl {Unit} {B})
inl-Unit-nf (base (β-rule (from-CCTB-β ())))
inl-Unit-nf (base (β-rule (from-CCT1-β ())))
inl-Unit-nf (base (β-rule (from-CCT2-β ())))
inl-Unit-nf (base (β-rule (from-CCT3-β ())))
inl-Unit-nf (base (η-rule ()))
inl-Unit-nf (base (s-rule (from-CCTB-s ())))
inl-Unit-nf (base (s-rule (from-CCT2-s ())))

inr-Unit-nf : ∀ {A} → IsβηNormalForm (inr {A} {Unit})
inr-Unit-nf (base (β-rule (from-CCTB-β ())))
inr-Unit-nf (base (β-rule (from-CCT1-β ())))
inr-Unit-nf (base (β-rule (from-CCT2-β ())))
inr-Unit-nf (base (β-rule (from-CCT3-β ())))
inr-Unit-nf (base (η-rule ()))
inr-Unit-nf (base (s-rule (from-CCTB-s ())))
inr-Unit-nf (base (s-rule (from-CCT2-s ())))

-- inr with sum source — used in iterated inr chains.
-- Source A ⊎ B is structurally distinct from Void, so initial-unique
-- doesn't apply.
inr-sum-nf :
  ∀ {A' A B} → IsβηNormalForm (inr {A'} {A ⊎ B})
inr-sum-nf (base (β-rule (from-CCTB-β ())))
inr-sum-nf (base (β-rule (from-CCT1-β ())))
inr-sum-nf (base (β-rule (from-CCT2-β ())))
inr-sum-nf (base (β-rule (from-CCT3-β ())))
inr-sum-nf (base (η-rule ()))
inr-sum-nf (base (s-rule (from-CCTB-s ())))
inr-sum-nf (base (s-rule (from-CCT2-s ())))

-- inr with product source — for binary tag encodings where the
-- inj is `inr` over a sum that has X × X components.
inr-prod-nf :
  ∀ {A' A B} → IsβηNormalForm (inr {A'} {A × B})
inr-prod-nf (base (β-rule (from-CCTB-β ())))
inr-prod-nf (base (β-rule (from-CCT1-β ())))
inr-prod-nf (base (β-rule (from-CCT2-β ())))
inr-prod-nf (base (β-rule (from-CCT3-β ())))
inr-prod-nf (base (η-rule ()))
inr-prod-nf (base (s-rule (from-CCTB-s ())))
inr-prod-nf (base (s-rule (from-CCT2-s ())))

------------------------------------------------------------------------
-- Composition NF helper.
--
-- f ∘ g is NF when:
--   - f is NF
--   - g is NF
--   - no head-βη-rule fires at f ∘ g
------------------------------------------------------------------------

comp-nf :
  ∀ {A B C} {f : Term B C} {g : Term A B} →
    IsβηNormalForm f →
    IsβηNormalForm g →
    (∀ {u} → ¬ ((f Syn.∘ g) Syn.⟶βη-rules u)) →
    IsβηNormalForm (f Syn.∘ g)
comp-nf f-nf g-nf no-head (base r)        = no-head r
comp-nf f-nf g-nf no-head (∘-congˡ step)  = f-nf step
comp-nf f-nf g-nf no-head (∘-congʳ step)  = g-nf step

------------------------------------------------------------------------
-- "no-head" proofs for our specific composition shapes.
--
-- These rule out all base βη-rules whose LHS could match the given
-- composition shape. For our encoding, no rule fires at any
-- composition head, but Agda needs explicit case analysis.
------------------------------------------------------------------------

-- inl ∘ terminal: no rule has either
--   - inl as left factor with no further constraint on right
--   - or matches our specific shape
-- Source is Unit (not Void), so initial-unique doesn't apply.
no-head-inl-terminal :
  ∀ {X} {u} →
    ¬ ((inl {Unit} {X} Syn.∘ terminal {Unit}) Syn.⟶βη-rules u)
no-head-inl-terminal (β-rule (from-CCTB-β ()))
no-head-inl-terminal (β-rule (from-CCT1-β ()))
no-head-inl-terminal (β-rule (from-CCT2-β ()))
no-head-inl-terminal (β-rule (from-CCT3-β ()))
no-head-inl-terminal (η-rule ())
no-head-inl-terminal (s-rule (from-CCTB-s ()))
no-head-inl-terminal (s-rule (from-CCT2-s ()))

-- (inl-terminal-nf moved below with the other helpers.)

-- In ∘ (inl ∘ terminal): the encoding of id.
-- No rule fires at this composition head; in-out doesn't apply because
-- the right factor isn't Out.
no-head-In-inl-terminal :
  ∀ {u} →
    ¬ ((In {TermF} Syn.∘ (inl {Unit} Syn.∘ terminal {Unit})) Syn.⟶βη-rules u)
no-head-In-inl-terminal (β-rule (from-CCTB-β ()))
no-head-In-inl-terminal (β-rule (from-CCT1-β ()))
no-head-In-inl-terminal (β-rule (from-CCT2-β ()))
no-head-In-inl-terminal (β-rule (from-CCT3-β ()))
no-head-In-inl-terminal (η-rule ())
no-head-In-inl-terminal (s-rule (from-CCTB-s ()))
no-head-In-inl-terminal (s-rule (from-CCT2-s ()))

------------------------------------------------------------------------
-- encode (id) is NF.
--
-- encode id = In ∘ (inl ∘ terminal)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- encode (id {Unit}) is NF — direct pattern matching attempt.
--
-- We specialize the type of id to {Unit} to give Agda enough to
-- reduce `encode id` to `In ∘ inl ∘ terminal`.
------------------------------------------------------------------------

-- Shorthand for the 7-line "no base βη rule applies" pattern.
-- We use this throughout the NF proofs.

encode-id-nf : ∀ {A} → IsβηNormalForm (encode (id {A}))
encode-id-nf (base (β-rule (from-CCTB-β ())))
encode-id-nf (base (β-rule (from-CCT1-β ())))
encode-id-nf (base (β-rule (from-CCT2-β ())))
encode-id-nf (base (β-rule (from-CCT3-β ())))
encode-id-nf (base (η-rule ()))
encode-id-nf (base (s-rule (from-CCTB-s ())))
encode-id-nf (base (s-rule (from-CCT2-s ())))
encode-id-nf (∘-congˡ step) = In-nf step
encode-id-nf (∘-congʳ (base (β-rule (from-CCTB-β ()))))
encode-id-nf (∘-congʳ (base (β-rule (from-CCT1-β ()))))
encode-id-nf (∘-congʳ (base (β-rule (from-CCT2-β ()))))
encode-id-nf (∘-congʳ (base (β-rule (from-CCT3-β ()))))
encode-id-nf (∘-congʳ (base (η-rule ())))
encode-id-nf (∘-congʳ (base (s-rule (from-CCTB-s ()))))
encode-id-nf (∘-congʳ (base (s-rule (from-CCT2-s ()))))
encode-id-nf (∘-congʳ (∘-congˡ step)) = inl-Unit-nf step
encode-id-nf (∘-congʳ (∘-congʳ step)) = terminal-nf step

------------------------------------------------------------------------
-- Iterated NF helpers — significantly reduce LOC for the deeper chains.
--
-- inr-then-nf : if rest is NF and rest's target is a sum (so inr's
-- source is non-Void), then `inr ∘ rest` is NF.
------------------------------------------------------------------------

inr-then-nf :
  ∀ {A A' B} {rest : Term Unit (A ⊎ B)} →
  IsβηNormalForm rest →
  IsβηNormalForm (inr {A'} {A ⊎ B} Syn.∘ rest)
inr-then-nf rest-nf (base (β-rule (from-CCTB-β ())))
inr-then-nf rest-nf (base (β-rule (from-CCT1-β ())))
inr-then-nf rest-nf (base (β-rule (from-CCT2-β ())))
inr-then-nf rest-nf (base (β-rule (from-CCT3-β ())))
inr-then-nf rest-nf (base (η-rule ()))
inr-then-nf rest-nf (base (s-rule (from-CCTB-s ())))
inr-then-nf rest-nf (base (s-rule (from-CCT2-s ())))
inr-then-nf rest-nf (∘-congˡ step) = inr-sum-nf step
inr-then-nf rest-nf (∘-congʳ step) = rest-nf step

-- inr-then-nf for product targets (used when stepping past binary tags).
inr-then-nf-prod :
  ∀ {A A' B} {rest : Term Unit (A × B)} →
  IsβηNormalForm rest →
  IsβηNormalForm (inr {A'} {A × B} Syn.∘ rest)
inr-then-nf-prod rest-nf (base (β-rule (from-CCTB-β ())))
inr-then-nf-prod rest-nf (base (β-rule (from-CCT1-β ())))
inr-then-nf-prod rest-nf (base (β-rule (from-CCT2-β ())))
inr-then-nf-prod rest-nf (base (β-rule (from-CCT3-β ())))
inr-then-nf-prod rest-nf (base (η-rule ()))
inr-then-nf-prod rest-nf (base (s-rule (from-CCTB-s ())))
inr-then-nf-prod rest-nf (base (s-rule (from-CCT2-s ())))
inr-then-nf-prod rest-nf (∘-congˡ step) = inr-prod-nf step
inr-then-nf-prod rest-nf (∘-congʳ step) = rest-nf step

-- inl ∘ terminal is NF.
inl-terminal-nf :
  ∀ {X} → IsβηNormalForm (inl {Unit} {X} Syn.∘ terminal {Unit})
inl-terminal-nf (base (β-rule (from-CCTB-β ())))
inl-terminal-nf (base (β-rule (from-CCT1-β ())))
inl-terminal-nf (base (β-rule (from-CCT2-β ())))
inl-terminal-nf (base (β-rule (from-CCT3-β ())))
inl-terminal-nf (base (η-rule ()))
inl-terminal-nf (base (s-rule (from-CCTB-s ())))
inl-terminal-nf (base (s-rule (from-CCT2-s ())))
inl-terminal-nf (∘-congˡ step) = inl-Unit-nf step
inl-terminal-nf (∘-congʳ step) = terminal-nf step

-- In ∘ rest where rest is NF and rest's target is `TermF Code`. Since
-- TermF Code is structurally a sum starting with Unit, in-out doesn't
-- apply (would require the right factor to be Out).
In-then-nf :
  ∀ {rest : Term Unit (TermF Code)} →
  IsβηNormalForm rest →
  IsβηNormalForm (In {TermF} Syn.∘ rest)
In-then-nf rest-nf (base (β-rule (from-CCTB-β ())))
In-then-nf rest-nf (base (β-rule (from-CCT1-β ())))
In-then-nf rest-nf (base (β-rule (from-CCT2-β ())))
In-then-nf rest-nf (base (β-rule (from-CCT3-β ())))
In-then-nf rest-nf (base (η-rule ()))
In-then-nf rest-nf (base (s-rule (from-CCTB-s ())))
In-then-nf rest-nf (base (s-rule (from-CCT2-s ())))
In-then-nf rest-nf (∘-congˡ step) = In-nf step
In-then-nf rest-nf (∘-congʳ step) = rest-nf step

-- inl with source Code (= μ TermF). Used for 1-arity tag selection
-- where the payload is a recursive sub-encoding.
inl-Code-nf : ∀ {B} → IsβηNormalForm (inl {Code} {B})
inl-Code-nf (base (β-rule (from-CCTB-β ())))
inl-Code-nf (base (β-rule (from-CCT1-β ())))
inl-Code-nf (base (β-rule (from-CCT2-β ())))
inl-Code-nf (base (β-rule (from-CCT3-β ())))
inl-Code-nf (base (η-rule ()))
inl-Code-nf (base (s-rule (from-CCTB-s ())))
inl-Code-nf (base (s-rule (from-CCT2-s ())))

-- inl ∘ payload-NF: the 1-arity tag's "select then embed payload" step.
inl-then-encoded-nf :
  ∀ {X} {payload : Term Unit Code} →
  IsβηNormalForm payload →
  IsβηNormalForm (inl {Code} {X} Syn.∘ payload)
inl-then-encoded-nf p-nf (base (β-rule (from-CCTB-β ())))
inl-then-encoded-nf p-nf (base (β-rule (from-CCT1-β ())))
inl-then-encoded-nf p-nf (base (β-rule (from-CCT2-β ())))
inl-then-encoded-nf p-nf (base (β-rule (from-CCT3-β ())))
inl-then-encoded-nf p-nf (base (η-rule ()))
inl-then-encoded-nf p-nf (base (s-rule (from-CCTB-s ())))
inl-then-encoded-nf p-nf (base (s-rule (from-CCT2-s ())))
inl-then-encoded-nf p-nf (∘-congˡ step) = inl-Code-nf step
inl-then-encoded-nf p-nf (∘-congʳ step) = p-nf step

------------------------------------------------------------------------
-- 2-arity helpers: pair NF, inl/inr applied to a pair.
------------------------------------------------------------------------

-- A predicate witnessing that a Term has the form In {F} ∘ rest.
-- Used to rule out eta-pair-gen, which would require components to
-- have the shape `fst ∘ h` and `snd ∘ h` — incompatible with In-headed.
data StartsWithIn : ∀ {A B} → Term A B → Set where
  starts-In :
    ∀ {F : Ty → Ty} {rest : Term Unit (F (μ F))} →
    StartsWithIn (In {F} Syn.∘ rest)

-- Every encoded morphism starts with In.
encode-starts-with-In : ∀ {A B} (g : Term A B) → StartsWithIn (encode g)
encode-starts-with-In id        = starts-In
encode-starts-with-In terminal  = starts-In
encode-starts-with-In fst       = starts-In
encode-starts-with-In snd       = starts-In
encode-starts-with-In apply     = starts-In
encode-starts-with-In initial   = starts-In
encode-starts-with-In inl       = starts-In
encode-starts-with-In inr       = starts-In
encode-starts-with-In In        = starts-In
encode-starts-with-In Out       = starts-In
encode-starts-with-In (curry _) = starts-In
encode-starts-with-In (cata _)  = starts-In
encode-starts-with-In (fmap _)  = starts-In
encode-starts-with-In (_ ∘ _)   = starts-In
encode-starts-with-In ⟨ _ , _ ⟩ = starts-In
encode-starts-with-In [ _ , _ ] = starts-In

-- Pair of In-headed NF terms is NF.
pair-nf :
  ∀ {e₁ e₂ : Term Unit Code} →
  StartsWithIn e₁ → StartsWithIn e₂ →
  IsβηNormalForm e₁ → IsβηNormalForm e₂ →
  IsβηNormalForm ⟨ e₁ , e₂ ⟩
pair-nf starts-In starts-In e₁-nf e₂-nf (base (β-rule (from-CCTB-β ())))
pair-nf starts-In starts-In e₁-nf e₂-nf (base (β-rule (from-CCT1-β ())))
pair-nf starts-In starts-In e₁-nf e₂-nf (base (β-rule (from-CCT2-β ())))
pair-nf starts-In starts-In e₁-nf e₂-nf (base (β-rule (from-CCT3-β ())))
pair-nf starts-In starts-In e₁-nf e₂-nf (base (η-rule ()))
pair-nf starts-In starts-In e₁-nf e₂-nf (base (s-rule (from-CCTB-s ())))
pair-nf starts-In starts-In e₁-nf e₂-nf (base (s-rule (from-CCT2-s ())))
pair-nf starts-In starts-In e₁-nf e₂-nf (⟨,⟩-congˡ step) = e₁-nf step
pair-nf starts-In starts-In e₁-nf e₂-nf (⟨,⟩-congʳ step) = e₂-nf step

-- inl with source `Code × Code` (used for tag13, tag14).
inl-prod-Code-nf :
  ∀ {B} → IsβηNormalForm (inl {Code × Code} {B})
inl-prod-Code-nf (base (β-rule (from-CCTB-β ())))
inl-prod-Code-nf (base (β-rule (from-CCT1-β ())))
inl-prod-Code-nf (base (β-rule (from-CCT2-β ())))
inl-prod-Code-nf (base (β-rule (from-CCT3-β ())))
inl-prod-Code-nf (base (η-rule ()))
inl-prod-Code-nf (base (s-rule (from-CCTB-s ())))
inl-prod-Code-nf (base (s-rule (from-CCT2-s ())))

-- inr with source `Code × Code` (used for the last alternative tag15).
inr-pair-Code-nf :
  ∀ {A} → IsβηNormalForm (inr {A} {Code × Code})
inr-pair-Code-nf (base (β-rule (from-CCTB-β ())))
inr-pair-Code-nf (base (β-rule (from-CCT1-β ())))
inr-pair-Code-nf (base (β-rule (from-CCT2-β ())))
inr-pair-Code-nf (base (β-rule (from-CCT3-β ())))
inr-pair-Code-nf (base (η-rule ()))
inr-pair-Code-nf (base (s-rule (from-CCTB-s ())))
inr-pair-Code-nf (base (s-rule (from-CCT2-s ())))

-- inl ∘ pair: select then embed pair. Used in tag13, tag14.
inl-then-pair-nf :
  ∀ {X} {e₁ e₂ : Term Unit Code} →
  StartsWithIn e₁ → StartsWithIn e₂ →
  IsβηNormalForm e₁ → IsβηNormalForm e₂ →
  IsβηNormalForm (inl {Code × Code} {X} Syn.∘ ⟨ e₁ , e₂ ⟩)
inl-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (β-rule (from-CCTB-β ())))
inl-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (β-rule (from-CCT1-β ())))
inl-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (β-rule (from-CCT2-β ())))
inl-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (β-rule (from-CCT3-β ())))
inl-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (η-rule ()))
inl-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (s-rule (from-CCTB-s ())))
inl-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (s-rule (from-CCT2-s ())))
inl-then-pair-nf s₁ s₂ e₁-nf e₂-nf (∘-congˡ step) = inl-prod-Code-nf step
inl-then-pair-nf s₁ s₂ e₁-nf e₂-nf (∘-congʳ step) = pair-nf s₁ s₂ e₁-nf e₂-nf step

-- inr ∘ pair: the last-alternative step (tag15). Source is Code × Code.
inr-then-pair-nf :
  ∀ {A} {e₁ e₂ : Term Unit Code} →
  StartsWithIn e₁ → StartsWithIn e₂ →
  IsβηNormalForm e₁ → IsβηNormalForm e₂ →
  IsβηNormalForm (inr {A} {Code × Code} Syn.∘ ⟨ e₁ , e₂ ⟩)
inr-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (β-rule (from-CCTB-β ())))
inr-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (β-rule (from-CCT1-β ())))
inr-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (β-rule (from-CCT2-β ())))
inr-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (β-rule (from-CCT3-β ())))
inr-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (η-rule ()))
inr-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (s-rule (from-CCTB-s ())))
inr-then-pair-nf s₁ s₂ e₁-nf e₂-nf (base (s-rule (from-CCT2-s ())))
inr-then-pair-nf s₁ s₂ e₁-nf e₂-nf (∘-congˡ step) = inr-pair-Code-nf step
inr-then-pair-nf s₁ s₂ e₁-nf e₂-nf (∘-congʳ step) = pair-nf s₁ s₂ e₁-nf e₂-nf step

------------------------------------------------------------------------
-- Test scaling: encode (terminal {Unit}) is NF.
-- Shape: In ∘ inr ∘ inl ∘ terminal — one more level than encode id.
------------------------------------------------------------------------

-- All 0-arity encoded constants are NF, via the helper chain.

encode-terminal-nf : ∀ {A} → IsβηNormalForm (encode (terminal {A}))
encode-terminal-nf = In-then-nf (inr-then-nf inl-terminal-nf)

-- For fst, snd, apply we specialize to specific source types so the
-- encoded shape's implicit type parameters are determined.

encode-fst-nf : ∀ {A B} → IsβηNormalForm (encode (fst {A} {B}))
encode-fst-nf =
  In-then-nf (inr-then-nf (inr-then-nf inl-terminal-nf))

encode-snd-nf : ∀ {A B} → IsβηNormalForm (encode (snd {A} {B}))
encode-snd-nf =
  In-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf inl-terminal-nf)))

encode-apply-nf : ∀ {A B} → IsβηNormalForm (encode (apply {A} {B}))
encode-apply-nf =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf inl-terminal-nf))))

encode-initial-nf : ∀ {A} → IsβηNormalForm (encode (initial {A}))
encode-initial-nf =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf inl-terminal-nf)))))

encode-inl-nf : ∀ {A B} → IsβηNormalForm (encode (inl {A} {B}))
encode-inl-nf =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf inl-terminal-nf))))))

encode-inr-nf : ∀ {A B} → IsβηNormalForm (encode (inr {A} {B}))
encode-inr-nf =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf inl-terminal-nf)))))))

encode-In-nf : ∀ {F : Ty → Ty} → IsβηNormalForm (encode (In {F}))
encode-In-nf =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf inl-terminal-nf))))))))

encode-Out-nf : ∀ {F : Ty → Ty} → IsβηNormalForm (encode (Out {F}))
encode-Out-nf =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf inl-terminal-nf)))))))))

------------------------------------------------------------------------
-- Recursive main theorem: encode g is NF for all g.
--
-- 1-arity and 2-arity cases recurse via encode-is-nf on subterms.
------------------------------------------------------------------------

encode-is-nf : ∀ {A B} (g : Term A B) → IsβηNormalForm (encode g)

-- 0-arity cases — inlined chains.
encode-is-nf id =
  In-then-nf inl-terminal-nf

encode-is-nf terminal =
  In-then-nf (inr-then-nf inl-terminal-nf)

encode-is-nf fst =
  In-then-nf (inr-then-nf (inr-then-nf inl-terminal-nf))

encode-is-nf snd =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf inl-terminal-nf)))

encode-is-nf apply =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf inl-terminal-nf))))

encode-is-nf initial =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf inl-terminal-nf)))))

encode-is-nf inl =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf inl-terminal-nf))))))

encode-is-nf inr =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf inl-terminal-nf)))))))

encode-is-nf In =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf inl-terminal-nf))))))))

encode-is-nf Out =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf inl-terminal-nf)))))))))

-- 1-arity: curry, cata, fmap. Tag at position 10, 11, 12.
encode-is-nf (curry f) =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf (inr-then-nf
        (inl-then-encoded-nf (encode-is-nf f))))))))))))

encode-is-nf (cata α)  =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf (inr-then-nf (inr-then-nf
        (inl-then-encoded-nf (encode-is-nf α)))))))))))))

encode-is-nf (fmap g)  =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
        (inl-then-encoded-nf (encode-is-nf g))))))))))))))

-- 2-arity: ∘, ⟨,⟩, [,] at positions 13, 14, 15.

-- tag13 (∘): 13 inr's + inl + pair.
encode-is-nf (g ∘ h) =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
        (inr-then-nf
          (inl-then-pair-nf (encode-starts-with-In g) (encode-starts-with-In h)
            (encode-is-nf g) (encode-is-nf h)))))))))))))))

-- tag14 (⟨,⟩): 14 inr's + inl + pair.
encode-is-nf ⟨ f , g ⟩ =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
        (inr-then-nf (inr-then-nf
          (inl-then-pair-nf (encode-starts-with-In f) (encode-starts-with-In g)
            (encode-is-nf f) (encode-is-nf g))))))))))))))))

-- tag15 ([,]): 15 inr's (NO inl, since this is the last alternative).
-- The innermost inr has product source; the rest have sum source.
encode-is-nf [ f , g ] =
  In-then-nf (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
    (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
      (inr-then-nf (inr-then-nf (inr-then-nf (inr-then-nf
        (inr-then-nf (inr-then-nf
          (inr-then-pair-nf (encode-starts-with-In f) (encode-starts-with-In g)
            (encode-is-nf f) (encode-is-nf g))))))))))))))))

