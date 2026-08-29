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
  using ( Cx; ε; _∙; vz; vs; Var
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
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Wk using ( w; sub-w )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTm; sVar; ⊢sTm; ⊢sVar; toI; fromI; ⊢ixP
        ; num; ⊢num; num-ren; num-sub )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Tags
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Terms
  using ( ixConv; fordFst; fordSnd; tyFordFst )

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

-- ⚠ A NAMED CAST, not `subst` with an underscored motive.  Writing
--   `subst (λ A → _ ⊢ty A)` makes the CONTEXT a meta INSIDE the lambda,
--   so Agda generalises it over `A` and it never solves.  As a top-level
--   lemma the context is an ordinary implicit and the expected type
--   pins it.
tyCast : {Γ : Ctx} {A B : RTy ⌊ Γ ⌋} → A ≡ B → Γ ⊢ty A → Γ ⊢ty B
tyCast refl d = d

-- ★ THE TWO WORKHORSES the generated rows are built from.  Both exist
--   ONLY to keep the context an ordinary implicit: written inline as
--   `subst (λ z → _ ⊢ z ∷ Nat) …` the `_` sits inside a lambda, becomes
--   a FUNCTION-typed meta, and never solves.
--
-- `⊢numAt n eq` — the depth, at whatever mangled form the payload's
--   substitutions left it in.  `⊢num` is context-polymorphic, so there
--   is nothing to weaken: the equation does all the work.
⊢numAt : {Γ : Ctx} (n : ℕ) {t : RTm ⌊ Γ ⌋} → t ≡ num n → Γ ⊢ t ∷ Nat
⊢numAt n eq = subst (λ z → _ ⊢ z ∷ Nat) (sym eq) (⊢num n)

-- `kCast` — a child, whose index the payload mangled the same way.
kCast : {Γ : Ctx} {s t d e : RTm ⌊ Γ ⌋} →
        d ≡ e → Γ ⊢ t ∷ K (pair s d) → Γ ⊢ t ∷ K (pair s e)
kCast refl dt = dt

kApp : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
kApp f a = icon tagTm-app (pair f (pair a (pair (idrefl ⌜Nat⌝ sTm) unit)))

-- ★★ AT AN ABSTRACT DEPTH `num n`.  `⊢num` is CONTEXT-POLYMORPHIC, so
--   every ⊢ty premise is the same `⊢num n` transported by a chain of
--   `num-ren`/`num-sub` — one rung per action the payload applied.
⊢kApp : {Δ : Ctx} (n : ℕ) {f a : RTm ⌊ Δ ⌋} →
        Δ ⊢ f ∷ K (pair sTm (num n)) → Δ ⊢ a ∷ K (pair sTm (num n)) →
        Δ ⊢ kApp f a ∷ K (pair sTm (num n))
⊢kApp n {f = f} df da =
  ⊢icon KnotWf memTm-app (⊢ixP ⊢sTm (⊢num n))
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢snd (⊢ixP ⊢sTm (⊢numAt n r1)))))
                 (tyFordFst ⊢sTm (⊢numAt n r2)))
           (ixConv (ξ-pairʳ (βsnd sTm (num n))) df)
           (⊢pair (tyFordFst ⊢sTm (⊢numAt n s1r2))
                  (ixConv (ξ-pairʳ (βsnd sTm _)) (kCast (sym s0r1) da))
                  (⊢pair ty-Unit (fordFst ⊢sTm) ⊢unit)))
  where
    -- ★ ONE RUNG PER ACTION, outermost first.  `renTm`s come from the
    --   payload's binders, `subTm`s from the components already given.
    r1 : renTm vs (num n) ≡ num n
    r1 = num-ren vs n
    r2 : renTm vs (renTm vs (num n)) ≡ num n
    r2 = trans (cong (renTm vs) r1) (num-ren vs n)
    s0r1 : subTm (single f) (renTm vs (num n)) ≡ num n
    s0r1 = trans (cong (subTm (single f)) r1) (num-sub (single f) n)
    s1r2 : subTm (extS (single f)) (renTm vs (renTm vs (num n))) ≡ num n
    s1r2 = trans (cong (subTm (extS (single f))) r2) (num-sub (extS (single f)) n)

------------------------------------------------------------------------
-- ★★ THE TWO `Var` ROWS — hand-written, because they Ford the DEPTH.
--
-- Their ambient index is `num (suc n)`, not `num n`, and their second
-- constraint names a BOUND FIELD rather than a constant.  ⚠ But the
-- bound field is itself the numeral `num n`, so every mangled form it
-- takes comes back by the SAME two lemmas — which is why these rows are
-- longer than the generated ones without being harder.
------------------------------------------------------------------------

Var-vzK : {Γ : Cx} → RTm Γ → RTm Γ
Var-vzK m = icon tagVar-vz
  (pair m (pair (idrefl ⌜Nat⌝ sVar) (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))

⊢Var-vzK : {Δ : Ctx} (n : ℕ) →
           Δ ⊢ Var-vzK (num n) ∷ K (pair sVar (num (suc n)))
⊢Var-vzK n =
  ⊢icon KnotWf memVar-vz (⊢ixP ⊢sVar (⊢num (suc n)))
    (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                          (toI (⊢fst (⊢ixP ⊢sVar (⊢numAt (suc n) r1))))
                          (toI ⊢sVar)))
                 (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                (toI (⊢snd (⊢ixP ⊢sVar (⊢numAt (suc n) r2))))
                                (toI (⊢nsuc (fromI (⊢var (there here)))))))
                       ty-Unit))
           (toI (⊢num n))
      (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                            (toI (⊢snd (⊢ixP ⊢sVar (⊢numAt (suc n) s1r2))))
                            (toI (⊢nsuc (⊢numAt n q1)))))
                   ty-Unit)
             (fordFst ⊢sVar)
        (⊢pair ty-Unit
               -- ★ the DEPTH ford is the one component needing a cast:
               --   `fordSnd` forces the pair's second component and the
               --   right-hand side to be the SAME term, and here one is
               --   the mangled ambient and the other is `suc` of the
               --   bound field.  They agree — but only propositionally.
               (⊢-cast (cong₂ (λ z w → El (⌜Id⌝ ⌜Nat⌝ (snd (pair sVar z))
                                                      (nsuc w)))
                              (sym s2) (sym q2))
                       (fordSnd (⊢nsuc (⊢num n))))
               ⊢unit)))
  where
    r1 : renTm vs (num (suc n)) ≡ num (suc n)
    r1 = num-ren vs (suc n)
    r2 : renTm vs (renTm vs (num (suc n))) ≡ num (suc n)
    r2 = trans (cong (renTm vs) r1) (num-ren vs (suc n))
    s1r2 : subTm (extS (single (num n))) (renTm vs (renTm vs (num (suc n))))
         ≡ num (suc n)
    s1r2 = trans (cong (subTm (extS (single (num n)))) r2)
                 (num-sub (extS (single (num n))) (suc n))
    -- ⚠ ONE action, not two: the field reference is a VARIABLE, and the
    --   payload's own substitution turns it into  — it does
    --   not then get hit by the component substitution as well.
    q1 : renTm vs (num n) ≡ num n
    q1 = num-ren vs n
    q2 : subTm (single (idrefl ⌜Nat⌝ sVar)) (renTm vs (num n)) ≡ num n
    q2 = trans (cong (subTm (single (idrefl ⌜Nat⌝ sVar))) (num-ren vs n))
               (num-sub (single (idrefl ⌜Nat⌝ sVar)) n)
    s2 : subTm (single (idrefl ⌜Nat⌝ sVar))
           (subTm (extS (single (num n))) (renTm vs (renTm vs (num (suc n)))))
       ≡ num (suc n)
    s2 = trans (cong (subTm (single (idrefl ⌜Nat⌝ sVar))) s1r2)
               (num-sub (single (idrefl ⌜Nat⌝ sVar)) (suc n))

Var-vsK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
Var-vsK m x = icon tagVar-vs
  (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar) (pair (idrefl ⌜Nat⌝ (nsuc m)) unit))))

⊢Var-vsK : {Δ : Ctx} (n : ℕ) {x : RTm ⌊ Δ ⌋} →
           Δ ⊢ x ∷ K (pair sVar (num n)) →
           Δ ⊢ Var-vsK (num n) x ∷ K (pair sVar (num (suc n)))
⊢Var-vsK n {x = x} dx =
  ⊢icon KnotWf memVar-vs (⊢ixP ⊢sVar (⊢num (suc n)))
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (fromI (⊢var here))))
             (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                            (toI (⊢fst (⊢ixP ⊢sVar (⊢numAt (suc n) r2))))
                            (toI ⊢sVar)))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢snd (⊢ixP ⊢sVar (⊢numAt (suc n) r3))))
                              (toI (⊢nsuc (fromI (⊢var (there (there here))))))))
                     ty-Unit)))
           (toI (⊢num n))
      (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                            (toI (⊢fst (⊢ixP ⊢sVar (⊢numAt (suc n) a1r2))))
                            (toI ⊢sVar)))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢snd (⊢ixP ⊢sVar (⊢numAt (suc n) a2r3))))
                              (toI (⊢nsuc (⊢numAt n w2)))))
                     ty-Unit))
             dx
        (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢snd (⊢ixP ⊢sVar (⊢numAt (suc n) b2r3))))
                              (toI (⊢nsuc (⊢numAt n w2x)))))
                     ty-Unit)
               (fordFst ⊢sVar)
          (⊢pair ty-Unit
                 (⊢-cast (cong₂ (λ z w → El (⌜Id⌝ ⌜Nat⌝ (snd (pair sVar z))
                                                        (nsuc w)))
                                (sym c3) (sym c0))
                         (fordSnd (⊢nsuc (⊢num n))))
                 ⊢unit))))
  where
    -- ⚠ NO `renTm vs = renTm vs` ABBREVIATION.  A `where` binding with no type
    --   signature is monomorphised by its first use, so the same name
    --   cannot serve at two telescope depths.
    r2 : renTm vs (renTm vs (num (suc n))) ≡ num (suc n)
    r2 = trans (cong (renTm vs) (num-ren vs (suc n))) (num-ren vs (suc n))
    r3 : renTm vs (renTm vs (renTm vs (num (suc n)))) ≡ num (suc n)
    r3 = trans (cong (renTm vs) r2) (num-ren vs (suc n))
    σ0 = extS (single (num n))
    σ0² = extS (extS (single (num n)))
    a1r2 : subTm σ0 (renTm vs (renTm vs (num (suc n)))) ≡ num (suc n)
    a1r2 = trans (cong (subTm σ0) r2) (num-sub σ0 (suc n))
    a2r3 : subTm σ0² (renTm vs (renTm vs (renTm vs (num (suc n))))) ≡ num (suc n)
    a2r3 = trans (cong (subTm σ0²) r3) (num-sub σ0² (suc n))
    w2 : renTm vs (renTm vs (num n)) ≡ num n
    w2 = trans (cong (renTm vs) (num-ren vs n)) (num-ren vs n)
    w2x : subTm (extS (single x)) (renTm vs (renTm vs (num n))) ≡ num n
    w2x = trans (cong (subTm (extS (single x))) w2) (num-sub (extS (single x)) n)
    σ1 = extS (single x)
    b2r3 : subTm σ1 (subTm σ0² (renTm vs (renTm vs (renTm vs (num (suc n)))))) ≡ num (suc n)
    b2r3 = trans (cong (subTm σ1) a2r3) (num-sub σ1 (suc n))
    σ2 = single (idrefl ⌜Nat⌝ sVar)
    c3 : subTm σ2 (subTm σ1 (subTm σ0² (renTm vs (renTm vs (renTm vs (num (suc n))))))) ≡ num (suc n)
    c3 = trans (cong (subTm σ2) b2r3) (num-sub σ2 (suc n))
    c0 : subTm σ2 (subTm (extS (single x)) (renTm vs (renTm vs (num n))))
       ≡ num n
    c0 = trans (cong (subTm σ2) w2x) (num-sub σ2 n)

------------------------------------------------------------------------
-- ★★ `Var-vzK` AT A **VARIABLE** DEPTH — and why it is needed at all.
--
-- ⚠ §4's rule "the depth must be a NUMERAL" was written for the ADEQUACY
--   MAP, whose depths are `len Γ` and hence numerals.  A JUDGEMENT's
--   constructor telescope is the other case: its depth is a bound
--   `iκ ⌜Nat⌝` field, i.e. a VARIABLE.
--
-- ★ AND THAT IS THE CHEAP CASE, not a harder one — route (c) of this
--   module's header, verbatim: renaming and substitution COMPUTE on a
--   variable, so every `num-ren`/`num-sub` chain the numeral version
--   needs collapses to `refl` and the derivation is SHORTER.
--
-- ⇒ the two forms are siblings, neither subsumes the other, and which one
--   applies is decided by whether the depth is a numeral or a variable.
------------------------------------------------------------------------

⊢Var-vzKv : {Δ : Ctx} {x : Var ⌊ Δ ⌋} → Δ ⊢ var x ∷ Nat →
            Δ ⊢ Var-vzK (var x) ∷ K (pair sVar (nsuc (var x)))
⊢Var-vzKv {x = x} dx =
  ⊢icon KnotWf memVar-vz (⊢ixP ⊢sVar (⊢nsuc dx))
    (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                          (toI (⊢fst (⊢ixP ⊢sVar (⊢nsuc (⊢wk dx)))))
                          (toI ⊢sVar)))
                 (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                (toI (⊢snd (⊢ixP ⊢sVar (⊢nsuc (⊢wk (⊢wk dx))))))
                                (toI (⊢nsuc (fromI (⊢var (there here)))))))
                       ty-Unit))
           (toI dx)
      (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                            (toI (⊢snd (⊢ixP ⊢sVar (⊢nsuc (⊢wk dx)))))
                            (toI (⊢nsuc (⊢wk dx)))))
                   ty-Unit)
             (fordFst ⊢sVar)
        (⊢pair ty-Unit (fordSnd (⊢nsuc dx)) ⊢unit)))

-- …and `Var-vsK` likewise.  ⚠ Same story: the numeral form serves the
--   adequacy map, this one serves a constructor telescope.
⊢Var-vsKv : {Δ : Ctx} {y : Var ⌊ Δ ⌋} {x : RTm ⌊ Δ ⌋} →
            Δ ⊢ var y ∷ Nat → Δ ⊢ x ∷ K (pair sVar (var y)) →
            Δ ⊢ Var-vsK (var y) x ∷ K (pair sVar (nsuc (var y)))
⊢Var-vsKv {y = y} {x = x} dy dx =
  ⊢icon KnotWf memVar-vs (⊢ixP ⊢sVar (⊢nsuc dy))
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (fromI (⊢var here))))
             (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                            (toI (⊢fst (⊢ixP ⊢sVar (⊢nsuc (⊢wk (⊢wk dy))))))
                            (toI ⊢sVar)))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢snd (⊢ixP ⊢sVar (⊢nsuc (⊢wk (⊢wk (⊢wk dy)))))))
                              (toI (⊢nsuc (fromI (⊢var (there (there here))))))))
                     ty-Unit)))
           (toI dy)
      (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                            (toI (⊢fst (⊢ixP ⊢sVar (⊢nsuc (⊢wk dy)))))
                            (toI ⊢sVar)))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢snd (⊢ixP ⊢sVar (⊢nsuc (⊢wk (⊢wk dy))))))
                              (toI (⊢nsuc (⊢wk (⊢wk dy))))))
                     ty-Unit))
             dx
        (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢snd (⊢ixP ⊢sVar (⊢nsuc (⊢wk dy)))))
                              (toI (⊢nsuc (⊢wk dy)))))
                     ty-Unit)
               (fordFst ⊢sVar)
          (⊢pair ty-Unit (fordSnd (⊢nsuc dy)) ⊢unit))))

------------------------------------------------------------------------
-- ★★★ RUNG 4: `Var-vzK` AT AN **ARBITRARY** DEPTH TERM.
--
-- ⚠ ROUTE (a), AND HERE IT IS FORCED.  `Knot/SubMot`'s two `Var`
--   substitution methods rebuild a variable from `m = fst p`, a
--   PROJECTION of the method's payload — so route (c)'s "make the depth
--   a context VARIABLE" has nothing to offer: there is no variable.
--   ★ And reusing the scrutinee fails too: `σ` wants
--   `K (pair sVar (snd ⟨i⟩))` while `icon k p` sits at `K ⟨i⟩`, and
--   closing that needs a pair-η the kernel does not have.
--
-- ★★★ AND THE ROUND TRIP IS **GENERIC IN THE TERM**, which is what makes
--   this cheap after all.  A first attempt (2026-08-28) stated it
--   separately at each position and concluded "three round trips at
--   three levels".  ⚠ That was an artefact of stating them at CONCRETE
--   terms: there is ONE trip, `rt₁`, and the deeper one is `rt₁`
--   composed with `wk-single`.  Two lemmas, both `∀ X`.
------------------------------------------------------------------------

-- retyping a SUBJECT.  ⚠ `⊢-cast` moves the TYPE; a bare `subst` makes
-- Agda abstract the CONTEXT too and those metas never solve.
tmCast : {Δ : Ctx} {A : RTy ⌊ Δ ⌋} {t t' : RTm ⌊ Δ ⌋} →
         t ≡ t' → Δ ⊢ t ∷ A → Δ ⊢ t' ∷ A
tmCast refl d = d

⊢Var-vzKt : {Δ : Ctx} {d : RTm ⌊ Δ ⌋} → Δ ⊢ d ∷ Nat →
            Δ ⊢ Var-vzK d ∷ K (pair sVar (nsuc d))
⊢Var-vzKt {Δ = Δ} {d = d} dd =
  ⊢icon KnotWf memVar-vz (⊢ixP ⊢sVar (⊢nsuc dd))
    (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                          (toI (⊢fst (⊢ixP ⊢sVar (⊢nsuc (⊢wk dd)))))
                          (toI ⊢sVar)))
                 (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                (toI (⊢snd (⊢ixP ⊢sVar (⊢nsuc (⊢wk (⊢wk dd))))))
                                (toI (⊢nsuc (fromI (⊢var (there here)))))))
                       ty-Unit))
           (toI dd)
      (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                            (toI (⊢snd (⊢ixP ⊢sVar (⊢nsuc dw))))
                            (toI (⊢nsuc (⊢wk dd)))))
                   ty-Unit)
             (fordFst ⊢sVar)
        (⊢pair ty-Unit
               (⊢-cast eqFord (fordSnd {t = sVar} (⊢nsuc dd)))
               ⊢unit)))
  where
    -- ★ ONE round trip, generic in the term it is stated at.
    rt₁ : (X : RTm ⌊ Δ ⌋) → subTm (extS (single d)) (w (w X)) ≡ w X
    rt₁ X = trans (sub-w {σ = single d} (w X)) (cong w (wk-single {v = d} X))

    -- …and the deeper one is that, then one more `wk-single`.
    rt₂ : (X : RTm ⌊ Δ ⌋) →
          subTm (single (idrefl ⌜Nat⌝ sVar)) (subTm (extS (single d)) (w (w X))) ≡ X
    rt₂ X = trans (cong (subTm (single (idrefl ⌜Nat⌝ sVar))) (rt₁ X))
                  (wk-single {v = idrefl ⌜Nat⌝ sVar} X)

    -- ⚠ the CONTEXT is left to inference: `dw` is used one binder
    --   deeper, inside the payload.
    dw : _ ⊢ subTm (extS (single d)) (w (w d)) ∷ Nat
    dw = tmCast (sym (rt₁ d)) (⊢wk dd)

    -- ⚠ THE TWO ENDPOINTS NEED **DIFFERENT** TRIPS, which is the whole
    --   subtlety of this row.  The LEFT one carries the index through
    --   `w (w -)` and needs the full `rt₂`; the RIGHT one meets
    --   `extS (single d)` at a VARIABLE — which substitutes
    --   definitionally — so only the outer `wk-single` is left.
    eqFord : _
    eqFord = cong₂ (λ a b → El (⌜Id⌝ ⌜Nat⌝ (snd a) b))
                   (sym (rt₂ (pair sVar (nsuc d))))
                   (sym (cong nsuc (wk-single {v = idrefl ⌜Nat⌝ sVar} d)))
