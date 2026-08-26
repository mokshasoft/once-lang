------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE KNOT'S CONSTRUCTORS AS DERIVED RULES,
-- and the one design question the adequacy map turns on.
--
-- `Knot/Terms` builds inhabitants at CONCRETE indices.  The map
-- `⌈_⌉ : RTm Γ → RTm ε` cannot: in its `app f a` clause `Γ` is a
-- VARIABLE, so the depth is an opaque term.  This file establishes what
-- that costs, on three rungs chosen to bracket the table.
--
-- ★★★ THE ANSWER, and it is the whole content of this module:
--
--     STATE THE SMART CONSTRUCTORS WITH THE DEPTH AS A CONTEXT
--     VARIABLE.  `subTm (single f) (w (var vz))` COMPUTES to `var vz`;
--     the same round trip on an opaque `d` is `wk-single` —
--     PROPOSITIONAL — and it grows a rung per field position.
--
--   ⇒ measured: rungs 1, 2 and 3 (one, two and FIVE recursive fields)
--     all go through with ZERO transports.  `ordtr`, the widest row in
--     the table, costs exactly what `lam` costs.
--
-- ⚠ THREE ROUTES WERE TRIED AND TWO ARE DEAD ENDS, recorded so they are
--   not re-tried:
--
--   (a) abstract `d` + `wk-single` per field.  Works, but each field
--       needs a chain whose length is its POSITION — the
--       `Lib/Amrec.stp-cancel-s` shape, five rungs deep at `ordtr`.
--   (b) `d = εwkTm d₀`, a closed depth weakened in.  The rewrite is
--       position-independent (two library lemmas), which looked
--       better — but `εwkTm` is a DEFINED function, so it is not
--       injective and every implicit `d₀` goes unsolved
--       (`pin-implicits-on-defined-set-types`).  Pinning `d₀` fixes
--       that and then the CONTEXT metas go unsolved instead.
--   (c) ★ the depth as a context VARIABLE — free, and the reason is
--       one line: renaming and substitution COMPUTE on variables.
--
-- ⚠ WHAT THIS DEFERS, stated so it is not mistaken for solved: a caller
--   who wants these at a concrete depth must INSTANTIATE by
--   substitution, and that step pays one `wk-single` per child — once
--   per constructor in a derived lemma, not once per use, and uniform
--   in the field's position.  That is the shape `⌈_⌉`'s typing will
--   consume; it is `abstract-the-substituted-terms` applied to a
--   53-row table.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Build where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; RTm; El; Unit; Nat; Σ'; IMu
        ; var; pair; fst; snd; unit; nzero; nsuc; ⌜Nat⌝; ⌜Id⌝; idrefl; icon
        ; Ren; Sub; renTm; subTm; extS; εwkTm; εwkTm-ren; εwkTm-sub )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; wk-single; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv
        ; ⊢pair; ⊢fst; ⊢snd; ⊢unit; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢idrefl
        ; ⊢icon
        ; ty-El; ty-Unit; ty-Nat; ty-Σ; ty-IMu
        ; _⟶_; βfst; βsnd; ξ-pairʳ; ξ-nsuc
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; credᵀ
        ; El-⌜Id⌝; ξ-El; ξ-IMu; ξ-⌜Id⌝ˡ )
open import normalizer.Syntax.Types using ( _≡_; sym; trans; cong; subst )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTm; ⊢sTm; toI; fromI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Tags
  using ( tagTm-lam; memTm-lam; tagTm-app; memTm-app; tagTm-ordtr; memTm-ordtr )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Terms
  using ( ixConv; fordFst; tyFordFst )

kLam : {Γ : Cx} → RTm Γ → RTm Γ
kLam b = icon tagTm-lam (pair b (pair (idrefl ⌜Nat⌝ sTm) unit))

-- the naive attempt: `Terms.⊢klam` with `⊢nzero` replaced by an abstract `dd`
⊢kLam : {Δ : Ctx} {d b : RTm ⌊ Δ ⌋} → Δ ⊢ d ∷ Nat →
        Δ ⊢ b ∷ K (pair sTm (nsuc d)) → Δ ⊢ kLam b ∷ K (pair sTm d)
⊢kLam {d = d} dd db =
  ⊢icon KnotWf memTm-lam (⊢ixP ⊢sTm dd)
    (⊢pair (tyFordFst ⊢sTm (⊢wk dd))
           (ixConv (ξ-pairʳ (ξ-nsuc (βsnd sTm d))) db)
           (⊢pair ty-Unit (fordFst ⊢sTm) ⊢unit))

------------------------------------------------------------------------
-- RUNG 2: TWO recursive fields, and THE DESIGN QUESTION.
--
-- The second field's index is `snd (subTm (single f) (w i))`.  `snd` of
-- the ambient is the one thing the ford never touches, so unlike rung 1
-- this does NOT unify for free — it needs `w i` to come back to `i`.
--
-- ★ THE FIX: THE DEPTH IS A CLOSED TERM, WEAKENED IN.  `εwkTm d₀` with
--   `d₀ : RTm ε` is stable under BOTH actions by two library lemmas that
--   already exist for exactly this purpose (`Spec/Syntax` proves them so
--   that `εwkTy I` survives the telescope).  Crucially the rewrite is the
--   SAME at every field position — it does not grow into a `sub-w⁴` chain
--   the way `Lib/Amrec.stp-cancel-s` does — because the two lemmas absorb
--   an arbitrary `ρ`/`σ` rather than one binder at a time.
------------------------------------------------------------------------

kApp : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
kApp f a = icon tagTm-app (pair f (pair a (pair (idrefl ⌜Nat⌝ sTm) unit)))

-- ★★★ THE DEPTH IS A CONTEXT VARIABLE, AND THAT IS THE WHOLE FIX.
--   `subTm (single f) (w (var vz))` COMPUTES to `var vz`; the same
--   round trip on an opaque `d` is `wk-single`, propositional, and it
--   grows a rung per field position.  So the smart constructors are
--   proved ONCE at `Δ ▹ Nat` with the depth bound, and a caller
--   instantiates by substitution — `abstract-the-substituted-terms`.
⊢kApp : {Δ : Ctx} {f a : RTm (⌊ Δ ⌋ ∙)} →
        (Δ ▹ Nat) ⊢ f ∷ K (pair sTm (var vz)) →
        (Δ ▹ Nat) ⊢ a ∷ K (pair sTm (var vz)) →
        (Δ ▹ Nat) ⊢ kApp f a ∷ K (pair sTm (var vz))
⊢kApp df da =
  ⊢icon KnotWf memTm-app (⊢ixP ⊢sTm (⊢var here))
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there here))))))
                 (tyFordFst ⊢sTm (⊢var (there (there here)))))
           (ixConv (ξ-pairʳ (βsnd sTm (var vz))) df)
           (⊢pair (tyFordFst ⊢sTm (⊢var (there here)))
                  (ixConv (ξ-pairʳ (βsnd sTm (var vz))) da)
                  (⊢pair ty-Unit (fordFst ⊢sTm) ⊢unit)))


------------------------------------------------------------------------
-- RUNG 3: THE WORST ROW — `ordtr`, five recursive fields.
--
-- ★ THE POINT: the transports do NOT grow with position, because there
--   are none.  What grows is the ⊢ty premise nest, TRIANGULARLY — the
--   k-th `⊢pair` states the tail from k+1 on — and every entry in it is
--   a de Bruijn lookup.  Bookkeeping, and exactly a generator's job.
------------------------------------------------------------------------

kOrdtr : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
kOrdtr a t u p q =
  icon tagTm-ordtr
    (pair a (pair t (pair u (pair p (pair q (pair (idrefl ⌜Nat⌝ sTm) unit))))))

⊢kOrdtr : {Δ : Ctx} {a t u p q : RTm (⌊ Δ ⌋ ∙)} →
          (Δ ▹ Nat) ⊢ a ∷ K (pair sTm (var vz)) →
          (Δ ▹ Nat) ⊢ t ∷ K (pair sTm (var vz)) →
          (Δ ▹ Nat) ⊢ u ∷ K (pair sTm (var vz)) →
          (Δ ▹ Nat) ⊢ p ∷ K (pair sTm (var vz)) →
          (Δ ▹ Nat) ⊢ q ∷ K (pair sTm (var vz)) →
          (Δ ▹ Nat) ⊢ kOrdtr a t u p q ∷ K (pair sTm (var vz))
⊢kOrdtr da dt du dp dq =
  ⊢icon KnotWf memTm-ordtr (⊢ixP ⊢sTm (⊢var here))
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there here)))))) (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there (there here))))))) (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there (there (there here)))))))) (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there (there (there (there here))))))))) (tyFordFst ⊢sTm (⊢var (there (there (there (there (there here)))))))))))
           (cv da)
     (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there here)))))) (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there (there here))))))) (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there (there (there here)))))))) (tyFordFst ⊢sTm (⊢var (there (there (there (there here)))))))))
            (cv dt)
      (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there here)))))) (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there (there here))))))) (tyFordFst ⊢sTm (⊢var (there (there (there here)))))))
             (cv du)
       (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢var (there here)))))) (tyFordFst ⊢sTm (⊢var (there (there here)))))
              (cv dp)
        (⊢pair (tyFordFst ⊢sTm (⊢var (there here)))
               (cv dq)
         (⊢pair ty-Unit (fordFst ⊢sTm) ⊢unit))))))
  where
    cv : {Δ' : Ctx} {x : RTm (⌊ Δ' ⌋ ∙)} →
         (Δ' ▹ Nat) ⊢ x ∷ K (pair sTm (var vz)) → _
    cv d = ixConv (ξ-pairʳ (βsnd sTm (var vz))) d
