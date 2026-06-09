------------------------------------------------------------------------
-- normalizer.Theory.Eval.Adequacy
--
-- The TRANSPARENCY content for the real normalizer: the code-level
-- normalizer on an encoded term yields the code of its spec normal form,
--
--     adequacy : ∀ g → eval normalize (code-of g) ≡ code-of (nf g)
--               (code-of g = eval (encode g) tt : Fix TermF)
--
-- which is exactly `RanzowFixpoint.EvalFullCorrectness.Correct nf normalize`
-- once `⇓`/`encVal` are unfolded — the NON-degenerate transparency (spec=nf,
-- not the trivial spec=id of RefoldFullCorrectness).
--
-- encode→code commutation is DEFINITIONAL (refl), so the induction on the
-- Term g mirrors idem-step: leaves are refl, recursive rebuilds close by
-- cong/cong₂ over the IH, and the comp case uses `comp-adequacy` — which
-- aligns handle-comp's code-level is-id trichotomy with comp-nf's IsId?
-- decision (the encode-faithfulness of `id`-detection). All with-FREE.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/Adequacy.agda
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Theory.Eval.Adequacy where

open import normalizer.Syntax.Types
  using (_≡_; refl; sym; trans; cong; cong₂; tt; _,_; inj₁; inj₂)
open import normalizer.Syntax.CCC
  using (Term; id; _∘_; fst; snd; ⟨_,_⟩; inl; inr; [_,_];
         terminal; initial; curry; apply; In; Out; cata)
open import normalizer.Encoding.Encoding
  using (TermF; encode; ⌜_⌝Ty; ⌜_⌝Func)
open import normalizer.Testing.Evaluator using (Fix; fix; eval)
open import normalizer.TCB0.Normalizer.Handlers using (normalize; handle-comp)
open import normalizer.TCB0.Normalizer.Dispatch using (is-id)
open import normalizer.Theory.Eval.HandlerCorrectness
  using (handle-comp-spec-id-left; handle-comp-spec-id-right; handle-comp-spec-rebuild)
open import normalizer.Theory.Eval.StepTransparency using (comp-code; pair-code; case-code)
open import normalizer.Theory.Eval.NfSpec
  using (nf; comp-nf; comp-elim; isId?; yes-id; no-id)

-- The code of a term: evaluate its encoding to the Fix TermF tree.
code-of : ∀ {A B} → Term A B → Fix TermF
code-of g = eval (encode g) tt

------------------------------------------------------------------------
-- idView: for each term, either it is `id`, or it is not — and in the not
-- case we carry (a) isId? t ≡ no-id (so comp-nf reduces) and (b) the
-- encode-faithfulness fact is-id (code-of t) ≡ inj₂ (code-of t). Both are
-- refl per constructor.
------------------------------------------------------------------------

data IdView : ∀ {A B} → Term A B → Set where
  vid : ∀ {A} → IdView (id {A})
  vno : ∀ {A B} {t : Term A B} →
        isId? t ≡ no-id → eval is-id (code-of t) ≡ inj₂ (code-of t) → IdView t

idView : ∀ {A B} (t : Term A B) → IdView t

idView id = vid
idView (f ∘ g) = vno refl refl
idView fst = vno refl refl
idView snd = vno refl refl
idView ⟨ f , g ⟩ = vno refl refl
idView inl = vno refl refl
idView inr = vno refl refl
idView [ f , g ] = vno refl refl
idView terminal = vno refl refl
idView initial = vno refl refl
idView (curry f) = vno refl refl
idView apply = vno refl refl
idView In = vno refl refl
idView Out = vno refl refl
idView (cata F alg) = vno refl refl

------------------------------------------------------------------------
-- comp-adequacy: handle-comp on two codes equals the code of comp-nf of
-- the corresponding terms. The bridge from code-level trichotomy to the
-- Term-level id-elimination.
------------------------------------------------------------------------

private
  caux : ∀ {A B C} (f : Term B C) (g : Term A B) → IdView f → IdView g →
         eval handle-comp (code-of f , code-of g) ≡ code-of (comp-nf f g)
  caux f g vid _ =
    handle-comp-spec-id-left (code-of f) (code-of g) refl
  caux f g (vno nf₁ id₁) vid =
    trans (handle-comp-spec-id-right (code-of f) (code-of g) (code-of f) id₁ refl)
          (sym (cong (λ z → code-of (comp-elim f g z yes-id)) nf₁))
  caux f g (vno nf₁ id₁) (vno nf₂ id₂) =
    trans (handle-comp-spec-rebuild (code-of f) (code-of g) (code-of f) (code-of g) id₁ id₂)
          (sym (trans (cong (λ z → code-of (comp-elim f g z (isId? g))) nf₁)
                      (cong (λ z → code-of (comp-elim f g no-id z)) nf₂)))

comp-adequacy : ∀ {A B C} (f : Term B C) (g : Term A B) →
  eval handle-comp (code-of f , code-of g) ≡ code-of (comp-nf f g)
comp-adequacy f g = caux f g (idView f) (idView g)

------------------------------------------------------------------------
-- The adequacy theorem, by structural induction on the Term g.
------------------------------------------------------------------------

adequacy : ∀ {A B} (g : Term A B) → eval normalize (code-of g) ≡ code-of (nf g)
adequacy id = refl
adequacy (f ∘ g) =
  trans (cong₂ (λ a b → eval handle-comp (a , b)) (adequacy f) (adequacy g))
        (comp-adequacy (nf f) (nf g))
adequacy fst = refl
adequacy snd = refl
adequacy inl = refl
adequacy inr = refl
adequacy terminal = refl
adequacy initial = refl
adequacy In = refl
adequacy Out = refl
adequacy apply = refl
adequacy ⟨ f , g ⟩ = cong₂ pair-code (adequacy f) (adequacy g)
adequacy [ f , g ] = cong₂ case-code (adequacy f) (adequacy g)
adequacy (cata F alg) = cong (λ b → fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (eval (⌜ F ⌝Func) tt , b))))))))))))))) (adequacy alg)
adequacy (curry {A} {B} {C} f) = cong (λ b → fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ ((eval (⌜ A ⌝Ty) tt , eval (⌜ B ⌝Ty) tt) , (eval (⌜ C ⌝Ty) tt , b))))))))))))))))) (adequacy f)
