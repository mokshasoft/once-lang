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
--   55-row table.
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
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sVar; sCtx; ⊢sTy; ⊢sTm; ⊢sVar; ⊢sCtx
        ; toI; fromI; ⊢ixP
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
-- ★★ THE TWO `Ctx` ROWS — the 8th sort, hand-written for the same
--    reason the `Var` rows are: they Ford the DEPTH.
--
-- ⚠ BUT `_▹_` IS A SHAPE THE TABLE DID NOT YET HAVE.  `Var`'s rows Ford
--   the depth with at most ONE ordinary field beside the Ford; `_▹_` has
--   TWO — a `Ctx` and an `RTy` — and BOTH sit at the BOUND field's depth
--   rather than at the ambient's.  Five slots, and the deepest telescope
--   in the table after `ordtr`'s six.
--
-- ★ AND IT COSTS ONE `kCast` AND ONE `⊢-cast`, no more.  Every mangled
--   form of the two numerals comes back by `num-ren`/`num-sub`, one rung
--   per action, exactly as the `Var` rows do — the extra field lengthens
--   the chains without adding a KIND of obligation.  ⇒ the depth-Forded
--   shape scales to fields, which is what the judgement layer will need
--   (`_∋_∷_`'s index is a three-component telescope over the same).
------------------------------------------------------------------------

Ctx-empK : {Γ : Cx} → RTm Γ
Ctx-empK = icon tagCtx-emp
  (pair (idrefl ⌜Nat⌝ sCtx) (pair (idrefl ⌜Nat⌝ nzero) unit))

-- ⚠ AT A LITERAL INDEX, SO NOT ONE TRANSPORT.  `◇` Fords the depth to
--   `0`, so its ambient is the CLOSED `pair sCtx nzero` and both actions
--   compute on it — `Knot/Terms`' situation, not `Var-vsK`'s.
⊢Ctx-empK : {Δ : Ctx} → Δ ⊢ Ctx-empK ∷ K (pair sCtx (num 0))
⊢Ctx-empK =
  ⊢icon KnotWf memCtx-emp (⊢ixP ⊢sCtx ⊢nzero)
    (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                          (toI (⊢snd (⊢ixP ⊢sCtx ⊢nzero))) (toI ⊢nzero)))
                 ty-Unit)
           (fordFst ⊢sCtx)
           (⊢pair ty-Unit (fordSnd ⊢nzero) ⊢unit))

Ctx-extK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
Ctx-extK m g a = icon tagCtx-ext
  (pair m (pair g (pair a (pair (idrefl ⌜Nat⌝ sCtx)
                                (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))

⊢Ctx-extK : {Δ : Ctx} (n : ℕ) {g a : RTm ⌊ Δ ⌋} →
            Δ ⊢ g ∷ K (pair sCtx (num n)) →
            Δ ⊢ a ∷ K (pair sTy (num n)) →
            Δ ⊢ Ctx-extK (num n) g a ∷ K (pair sCtx (num (suc n)))
⊢Ctx-extK n {g = g} {a = a} dg da =
  ⊢icon KnotWf memCtx-ext (⊢ixP ⊢sCtx (⊢num (suc n)))
    -- level 0 — the bound depth `m`.  Both recursive fields still read
    -- it as a VARIABLE here, hence the two `fromI (⊢var …)`.
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sCtx (fromI (⊢var here))))
             (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTy (fromI (⊢var (there here)))))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢fst (⊢ixP ⊢sCtx (⊢numAt (suc n) r3))))
                              (toI ⊢sCtx)))
                 (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                (toI (⊢snd (⊢ixP ⊢sCtx (⊢numAt (suc n) r4))))
                                (toI (⊢nsuc (fromI (⊢var (there (there (there here)))))))))
                       ty-Unit))))
           (toI (⊢num n))
    -- level 1 — the `Ctx` field.  Its index is `single m`-substituted and
    -- so COMPUTES to `num n`: `dg` goes in untouched.
      (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢numAt n q1)))
               (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢fst (⊢ixP ⊢sCtx (⊢numAt (suc n) s31))))
                              (toI ⊢sCtx)))
                 (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                (toI (⊢snd (⊢ixP ⊢sCtx (⊢numAt (suc n) s41))))
                                (toI (⊢nsuc (⊢numAt n w3)))))
                       ty-Unit)))
             dg
    -- level 2 — the `RTy` field.  ⚠ ONE rung further from the binder, so
    -- its depth arrives as `subTm (single g) (renTm vs (num n))`: the
    -- single `kCast` this row costs.
        (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                              (toI (⊢fst (⊢ixP ⊢sCtx (⊢numAt (suc n) s32))))
                              (toI ⊢sCtx)))
                 (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                (toI (⊢snd (⊢ixP ⊢sCtx (⊢numAt (suc n) s42))))
                                (toI (⊢nsuc (⊢numAt n f42)))))
                       ty-Unit))
               (kCast (sym q2) da)
    -- level 3 — the SORT ford, free as everywhere else
          (⊢pair (ty-Σ (ty-El (⊢⌜Id⌝ ⊢⌜Nat⌝
                                (toI (⊢snd (⊢ixP ⊢sCtx (⊢numAt (suc n) s43))))
                                (toI (⊢nsuc (⊢numAt n f43)))))
                       ty-Unit)
                 (fordFst ⊢sCtx)
    -- level 4 — the DEPTH ford.  `fordSnd` forces the pair's second
    -- component and the right-hand side to be the SAME term; here one is
    -- the four-times-mangled ambient and the other is `suc` of the
    -- three-times-mangled bound field, so BOTH need the cast.
            (⊢pair ty-Unit
                   (⊢-cast (cong₂ (λ z w → El (⌜Id⌝ ⌜Nat⌝ (snd (pair sCtx z))
                                                          (nsuc w)))
                                  (sym s44) (sym f44))
                           (fordSnd (⊢nsuc (⊢num n))))
                   ⊢unit)))))
  where
    r3 : renTm vs (renTm vs (renTm vs (num (suc n)))) ≡ num (suc n)
    r3 = trans (cong (renTm vs) (trans (cong (renTm vs) (num-ren vs (suc n))) (num-ren vs (suc n)))) (num-ren vs (suc n))
    s31 : subTm (extS (extS (single (num n)))) (renTm vs (renTm vs (renTm vs (num (suc n))))) ≡ num (suc n)
    s31 = trans (cong (subTm (extS (extS (single (num n))))) r3) (num-sub (extS (extS (single (num n)))) (suc n))
    s32 : subTm (extS (single g)) (subTm (extS (extS (single (num n)))) (renTm vs (renTm vs (renTm vs (num (suc n)))))) ≡ num (suc n)
    s32 = trans (cong (subTm (extS (single g))) s31) (num-sub (extS (single g)) (suc n))

    r4 : renTm vs (renTm vs (renTm vs (renTm vs (num (suc n))))) ≡ num (suc n)
    r4 = trans (cong (renTm vs) (trans (cong (renTm vs) (trans (cong (renTm vs) (num-ren vs (suc n))) (num-ren vs (suc n)))) (num-ren vs (suc n)))) (num-ren vs (suc n))
    s41 : subTm (extS (extS (extS (single (num n))))) (renTm vs (renTm vs (renTm vs (renTm vs (num (suc n)))))) ≡ num (suc n)
    s41 = trans (cong (subTm (extS (extS (extS (single (num n)))))) r4) (num-sub (extS (extS (extS (single (num n))))) (suc n))
    s42 : subTm (extS (extS (single g))) (subTm (extS (extS (extS (single (num n))))) (renTm vs (renTm vs (renTm vs (renTm vs (num (suc n))))))) ≡ num (suc n)
    s42 = trans (cong (subTm (extS (extS (single g)))) s41) (num-sub (extS (extS (single g))) (suc n))
    s43 : subTm (extS (single a)) (subTm (extS (extS (single g))) (subTm (extS (extS (extS (single (num n))))) (renTm vs (renTm vs (renTm vs (renTm vs (num (suc n)))))))) ≡ num (suc n)
    s43 = trans (cong (subTm (extS (single a))) s42) (num-sub (extS (single a)) (suc n))
    s44 : subTm (single (idrefl ⌜Nat⌝ sCtx)) (subTm (extS (single a)) (subTm (extS (extS (single g))) (subTm (extS (extS (extS (single (num n))))) (renTm vs (renTm vs (renTm vs (renTm vs (num (suc n))))))))) ≡ num (suc n)
    s44 = trans (cong (subTm (single (idrefl ⌜Nat⌝ sCtx))) s43) (num-sub (single (idrefl ⌜Nat⌝ sCtx)) (suc n))

    q1 : renTm vs (num n) ≡ num n
    q1 = num-ren vs n
    q2 : subTm (single g) (renTm vs (num n)) ≡ num n
    q2 = trans (cong (subTm (single g)) q1) (num-sub (single g) n)

    w3 : renTm vs (renTm vs (renTm vs (num n))) ≡ num n
    w3 = trans (cong (renTm vs) (trans (cong (renTm vs) (num-ren vs n)) (num-ren vs n))) (num-ren vs n)
    f42 : subTm (extS (extS (single g))) (renTm vs (renTm vs (renTm vs (num n)))) ≡ num n
    f42 = trans (cong (subTm (extS (extS (single g)))) w3) (num-sub (extS (extS (single g))) n)
    f43 : subTm (extS (single a)) (subTm (extS (extS (single g))) (renTm vs (renTm vs (renTm vs (num n))))) ≡ num n
    f43 = trans (cong (subTm (extS (single a))) f42) (num-sub (extS (single a)) n)
    f44 : subTm (single (idrefl ⌜Nat⌝ sCtx)) (subTm (extS (single a)) (subTm (extS (extS (single g))) (renTm vs (renTm vs (renTm vs (num n)))))) ≡ num n
    f44 = trans (cong (subTm (single (idrefl ⌜Nat⌝ sCtx))) f43) (num-sub (single (idrefl ⌜Nat⌝ sCtx)) n)
