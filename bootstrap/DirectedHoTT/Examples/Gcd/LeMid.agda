------------------------------------------------------------------------
-- OCP-0009 — EQUATION 4: gcd's STEP, WITH THE DESCENT ABSTRACTED.
--
-- ★ WHAT THIS IS FOR.  Equation 4's `⟶*` premise is unsatisfiable at
--   variables, so the descent must be rewritten PROPOSITIONALLY (see
--   `⊢monusLe`, the bridge).  Transport needs the step application as a
--   ONE-HOLE context with the descent as the hole — that is `midAt`.
--
-- ★★ HOW IT WAS FOUND, and the technique is the reusable part: NOT by
--   hand-composing gcd's substitution stack, which is where this kind of
--   work usually dies.  Instead state the chain with a deliberately WRONG
--   target (`⟶* nzero`) and read the real endpoint out of Agda's
--   mismatch message, one layer at a time.  Four probes gave `Zt`/`St`,
--   then `W`, then the shape, then the descent.
--
-- ⚠ AND THE ONE THAT COST A CYCLE: after the substitution stack the
--   descent is NOT syntactically `monus (nsuc a') (nsuc b')` — it is the
--   SUBSTITUTED form `D3'`, equal only propositionally (`wkS3`/`wkS3e`).
--   That is exactly why `gcd-le-term` carries `mhAt` to rewrite it, so the
--   propositional route pays at the same place the reductional one did.
--
-- ⇒ `subTm (single (D3' a' b')) F` is the chain's endpoint;
--   `subTm (single nzero) F` is where `natrec-zero` fires and gcd's
--   existing tail chain runs unchanged.  `congAt F` bridges them.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Gcd.LeMid where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; Nat; pair; nsuc; nzero; natrec; app
        ; subTm; subTy; extS; renTm; vs; var; vz; _∘ₛ_; subTy-subTy; subTy-cong; Var; Sub
        ; Π; El; ⌜Nat⌝ )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; _⟶_; β; βfst; βsnd; ξ-appˡ; natrec-suc; natrec-zero; single; wk-single )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ; ⟶*-natrecⁿ )
open import DirectedHoTT.Lib.Monus using ( monusTm )
open import DirectedHoTT.Lib.Nat using ( plusTm )
open import DirectedHoTT.Lib.Amrec using ( aIHTat-sub )
open import DirectedHoTT.Examples.Gcd.Step using ( gcdIH; msr; gcdG-sub )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; _⊢ty_; _▹_; ⊢natrec; ⊢pair; ⊢nsuc; ⊢var; here; there; ty-Nat )
open import DirectedHoTT.Metatheory.TySub
  using ( sub-lemma; sub-ty; Sub⊢; Sub⊢-ext; ⊢single; ⊢-cast; ⊢wk; subTy-comm )
open import DirectedHoTT.Lib.Pair using ( PairT )
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import DirectedHoTT.Lib.Wk
  using ( nrs-w; w; sub-w; pw1; pw2; pw3; pw4 )
open import DirectedHoTT.Lib.Natrec
  using ( na-z; na-s; ⊢natrec-at; ⊢natrec-var; ⊢natrec-var-push
        ; ⊢natrec-var-tr; Sub⊢-∘ )
open import DirectedHoTT.Examples.Gcd.Step
  using ( gcdStp; gcdBody; G1z; gcdInn1; G2z; gcdInn2; G3z; G3s
        ; PAIRᶻ; CERTᶻ; one; _⟫_; wkS3; wkS3e
        ; G1; ⊢G1; ⊢G1z; ⊢gcdInn1; wkS2; G2; ⊢G2; ⊢G2z; ⊢gcdInn2
        ; G3; ⊢G3; ⊢G3z; ⊢G3s; gcdG; PAIRˢ; ⊢PAIRˢ; CERTˢ; ⊢CERTˢ )
open import DirectedHoTT.Spec.Typing using ( single; nrs )

gXx : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
gXx x y = pair (nsuc x) (nsuc y)

R1' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
R1' x y = natrec (subTm (single (gXx x y)) G1z)
                 (subTm (extS (extS (single (gXx x y)))) gcdInn1) y

W' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
W' x y = subTm (single (R1' x y))
           (subTm (extS (single y)) (renTm vs (renTm vs x)))

R2' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
R2' x y = natrec (subTm (single (R1' x y))
                    (subTm (extS (single y))
                      (subTm (extS (extS (single (gXx x y)))) G2z)))
                 (subTm (extS (extS (single (R1' x y))))
                   (subTm (extS (extS (extS (single y))))
                     (subTm (extS (extS (extS (extS (single (gXx x y)))))) gcdInn2)))
                 (W' x y)

-- ★ the third natrec's branches, with the SAME substitution stack pushed onto
-- `G3z`/`G3s` separately — sound because `subTm` distributes over `natrec`
Z3' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
Z3' x y = subTm (single (R2' x y))
            (subTm (extS (single (W' x y)))
              (subTm (extS (extS (single (R1' x y))))
                (subTm (extS (extS (extS (single y))))
                  (subTm (extS (extS (extS (extS (single (gXx x y)))))) G3z))))

S3' : {Γ : Cx} → RTm Γ → RTm Γ → RTm ((Γ ∙) ∙)
S3' x y = subTm (extS (extS (single (R2' x y))))
            (subTm (extS (extS (extS (single (W' x y)))))
              (subTm (extS (extS (extS (extS (single (R1' x y))))))
                (subTm (extS (extS (extS (extS (extS (single y))))))
                  (subTm (extS (extS (extS (extS (extS (extS (single (gXx x y))))))))
                         G3s))))

-- ⚠ the descent as the substitution stack ACTUALLY leaves it — equal to
--   `monus (nsuc a') (nsuc b')` only PROPOSITIONALLY (`wkS3`/`wkS3e`),
--   which is exactly why `gcd-le-term` needs `mhAt` to rewrite it.
D3' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
D3' x y = subTm (single (R2' x y))
            (subTm (extS (single (W' x y)))
              (subTm (extS (extS (single (R1' x y))))
                (subTm (extS (extS (extS (single y))))
                  (subTm (extS (extS (extS (extS (single (gXx x y))))))
                         (monusTm (nsuc (var (vs vz)))
                                  (nsuc (var (vs (vs (vs vz))))))))))

midAt : {Γ : Cx} (a' b' ih d : RTm Γ) → RTm Γ
midAt a' b' ih d = app (natrec (Z3' a' b') (S3' a' b') d) ih

MID : {Γ : Cx} (a' b' ih : RTm Γ) → RTm Γ
MID a' b' ih = midAt a' b' ih (D3' a' b')

-- ★★★ THE mh-FREE PREFIX.  Every step here unfolds a CONSTRUCTOR-headed
--     scrutinee, so none of it needs the branch premise — which is why the
--     chain can be split here at all.
gcd-le-prefix : {Γ : Cx} (a' b' ih : RTm Γ) →
                app (app gcdStp (pair (nsuc a') (nsuc b'))) ih ⟶* MID a' b' ih
gcd-le-prefix a' b' ih =
  ( one (ξ-appˡ (β gcdBody (gXx a' b')))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βsnd _ _)))
  ⟫ ⟶*-appˡ (one (natrec-suc (subTm (single (gXx a' b')) G1z)
                             (subTm (extS (extS (single (gXx a' b')))) gcdInn1)
                             b'))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βfst _ _)))
  ⟫ ⟶*-appˡ (one (natrec-suc _ _ (W' a' b')))
  )

------------------------------------------------------------------------
-- ★★★ THE TAIL, AT A LITERAL ZERO.
--
-- ⭐ THIS IS THE WHOLE POINT OF THE PROPOSITIONAL ROUTE.  At `nzero` the
--   third `natrec` FIRES (`natrec-zero` selects `G3z`) and one β-step
--   reaches the recursive call.  Both are ordinary reductions needing no
--   premise, because the scrutinee is now a literal CONSTRUCTOR instead of
--   a stuck term.  The reduction that is impossible at a variable is
--   trivial here, and the bridge's `Id` carries the result back.
------------------------------------------------------------------------

-- the substitution stack the two `G3z` components land under
σz : {Γ : Cx} (a' b' ih : RTm Γ) → RTm ((((((Γ ∙) ∙) ∙) ∙) ∙) ∙) → RTm Γ
σz a' b' ih t =
  subTm (single ih)
    (subTm (extS (single (R2' a' b')))
      (subTm (extS (extS (single (W' a' b'))))
        (subTm (extS (extS (extS (single (R1' a' b')))))
          (subTm (extS (extS (extS (extS (single b')))))
            (subTm (extS (extS (extS (extS (extS (single (gXx a' b'))))))) t)))))

-- the recursive call `gcd (suc a', (suc b') ∸ (suc a'))`, with certificate
RHSz : {Γ : Cx} (a' b' ih : RTm Γ) → RTm Γ
RHSz a' b' ih = app (σz a' b' ih (app (var vz) PAIRᶻ)) (σz a' b' ih CERTᶻ)

gcd-le-tail : {Γ : Cx} (a' b' ih : RTm Γ) →
              midAt a' b' ih nzero ⟶* RHSz a' b' ih
gcd-le-tail a' b' ih =
  ( ⟶*-appˡ (one (natrec-zero (Z3' a' b') (S3' a' b')))
  ⟫ one (β _ ih)
  )

------------------------------------------------------------------------
-- ★★ AND THE DESCENT IS THE CLEAN ONE, up to the two weakening peels the
--    reductional proof already carries.  `gcd-le-term` spends these inside
--    `mhAt`; the propositional route spends them here, once.
------------------------------------------------------------------------

D3-clean : {Γ : Cx} (a' b' : RTm Γ) →
           D3' a' b' ≡ monusTm (nsuc a') (nsuc b')
D3-clean a' b' = cong₂ (λ x y → monusTm (nsuc x) (nsuc y))
                       (wkS3 a') (wkS3e b')

------------------------------------------------------------------------
-- ⚠⚠ THE NEXT OBSTACLE, MEASURED — TYPING THE ONE-HOLE CONTEXT.
--
-- Everything above is `⟶*`, which is UNTYPED, so none of it needed a
-- typing derivation.  `congAt` is a `⊢` statement, so the transport needs
--
--     (Γ ▹ El ⌜Nat⌝) ⊢ <one-hole context> ∷ Nat
--
-- and that is the price of going propositional; the reductional proof
-- never pays it because it never needs the term well-typed.
--
-- ⚠ AND IT CANNOT BE INHERITED.  Two routes are closed, both checked:
--   * SUBJECT REDUCTION — `…SR` records general SR as an "HONEST CEILING
--     (the real obstruction, not a gap)"; only a concrete instance exists.
--     So the typing of an intermediate state does NOT follow from
--     `⊢gcdStp` plus the chain.
--   * REUSING `⊢G1`/`⊢G2`/`⊢G3` DIRECTLY — MEASURED, does not typecheck:
--     `⊢G1` lives in `Γ ▹ PairT ▹ Nat`, while `R1'` sits in plain `Γ`
--     after `single gX`.  The generalized sibling slots (`B`, `C`, `D`)
--     make these context-POLYMORPHIC in their siblings, not in their own
--     prefix, so they do not transport across the substitution.
--   ⚠ And `subTm` does not invert (see `…GcdStep`'s note at `⊢gcdInn2`),
--     so the sub-derivations cannot be recovered from `⊢gcdStp` either.
--
-- ⇒ SO EACH LAYER NEEDS ITS OWN DERIVATION, by the substitution lemma:
--   typings for `gXx`, `R1'`, `W'`, `R2'`, then `⊢G3`/`⊢G3z`/`⊢G3s` pushed
--   through the stack, then `⊢natrec-var` (which wants the branches
--   WEAKENED — so build `F` from `w (Z3' a' b')`, not `Z3' (w a') (w b')`,
--   and the peels cancel by `wk-single`).
--
--   That is ~12 substitution-lemma applications with their `Sub⊢`
--   derivations.  Real work, well-defined, no known obstruction.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★★ THE TYPING HALF — LAYER BY LAYER, BY THE SUBSTITUTION LEMMA.
--
-- Neither shortcut is available (see the note above), so each intermediate
-- state gets its own derivation.  The recipe is uniform: `⊢single` for the
-- substitution, `Sub⊢-ext` once per binder the target sits under, then
-- `sub-ty` for motives and `sub-lemma` for terms.
------------------------------------------------------------------------

⊢gXx : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋} →
       Γ ⊢ a' ∷ Nat → Γ ⊢ b' ∷ Nat → Γ ⊢ gXx a' b' ∷ PairT
⊢gXx da db = ⊢pair ty-Nat (⊢nsuc da) (⊢nsuc db)

-- ★★★ LAYER 1, IN ONE LINE.  `⊢natrec-at`'s conclusion is
--     `natrec (subTm σ z) (subTm (extS² σ) s) n`
--   which is EXACTLY `R1'` at σ = `single gX`, z = `G1z`, s = `gcdInn1`,
--   n = `b'`, M = `G1`.  It performs the `na-z`/`na-s` casts internally.
--
-- ⚠ I hand-wrote those casts as `peelZ`/`peelS` before finding the lemma —
--   ~25 lines, now deleted.  See `…LibNatrec`'s header.
⊢R1' : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
       (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) →
       Γ ⊢ R1' a' b'
         ∷ subTy (single b') (subTy (extS (single (gXx a' b'))) G1)
⊢R1' da db = ⊢natrec-at ⊢G1 ⊢G1z ⊢gcdInn1 (⊢single (⊢gXx da db)) db

-- ★ layer 2: `W'` is `a'` IN DISGUISE.  `wkS2` is exactly its shape — two
--   weakenings cancelled by two substitutions — so no new work.
⊢W' : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋} →
      Γ ⊢ a' ∷ Nat → Γ ⊢ b' ∷ Nat → Γ ⊢ W' a' b' ∷ Nat
-- ⚠ the TERM moves here, not the type — `⊢-cast` is for types, so this
--   is a `subst` on the subject position.
⊢W' {Γ} {a' = a'} da db = subst (λ z → Γ ⊢ z ∷ Nat) (sym (wkS2 a')) da

------------------------------------------------------------------------
-- ★★★ LAYER 3 — `R2'`, ALSO VIA `⊢natrec-at`.
--
-- Same lemma, now at σ = `single R1'`.  The TWO INNER substitution levels
-- (`single gX`, then `single b'`) ride on the motive and branches via
-- `sub-ty`/`sub-lemma`; the outer one is `⊢natrec-at`'s own σ.  No
-- `Sub⊢-∘` composition is needed, and the `na-z`/`na-s` casts are inside
-- the lemma.
--
-- ⚠ `B` PINNED throughout — the generalised sibling slot is `G1` here and
--   cannot be inferred.
------------------------------------------------------------------------

-- ⚠ AND THE INNER LEVELS DO NOT NEED THEIR OWN CASTS EITHER.  `subTm`
--   DISTRIBUTES over `natrec`, so pushing the WHOLE `⊢natrec-at`
--   derivation through the outer substitutions with `sub-lemma` produces
--   the 3-level substituted `natrec` directly — no `na-z` at the inner
--   levels, which is what the hand-written version needed.
-- ⚠ `⊢natrec-at` concludes `subTy (single n) …`, and `sub-lemma` pushes the
--   outer substitutions AROUND that — leaving `single n` INSIDE, where the
--   next layer needs it OUTSIDE as `single W'`.  `subTy-comm` walks it out,
--   once per push.  (`n` here is `w (w a')`, and the two pushes turn it into
--   exactly `W'` — which is `wkS2`'s statement, seen from the other side.)
⊢R2' : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
       (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) →
       Γ ⊢ R2' a' b'
         ∷ subTy (single (W' a' b'))
             (subTy (extS (single (R1' a' b')))
               (subTy (extS (extS (single b')))
                 (subTy (extS (extS (extS (single (gXx a' b'))))) G2)))
⊢R2' {Γ} {a' = a'} {b' = b'} da db = ⊢-cast comm2 raw
  where
    raw = sub-lemma (sub-lemma (⊢natrec-at (⊢G2 {B = G1}) (⊢G2z {B = G1})
                                   (⊢gcdInn2 {B = G1})
                                   (Sub⊢-ext (Sub⊢-ext (⊢single (⊢gXx da db))))
                                   (⊢wk (⊢wk da)))
                       (Sub⊢-ext (⊢single db)))
            (⊢single (⊢R1' da db))

    inner = subTy (extS (extS (extS (single (gXx a' b'))))) G2

    -- ⚠ `B` is EXPLICIT in `subTy-comm` and must be given: it is the type
    --   `⊢natrec-at` produced under its own `single n`.
    comm2 = trans (cong (subTy (single (R1' a' b')))
                        (subTy-comm (extS (single b')) inner
                                    (renTm vs (renTm vs a'))))
                  (subTy-comm (single (R1' a' b'))
                              (subTy (extS (extS (single b'))) inner)
                              (subTm (extS (single b')) (renTm vs (renTm vs a'))))

------------------------------------------------------------------------
-- ⚠⚠ LAYER 4 — DRAFTED, BLOCKED ON SLOT TYPES.  Kept below, commented.
--
-- The five `sub-lemma`/`sub-ty` levels are in the RIGHT ORDER — read off
-- the printed endpoint: outermost `single R2'`, then `extS (single W')`,
-- then `extS² (single R1')`, `extS³ (single b')`, `extS⁴ (single gX)`
-- innermost.  What does not line up is the SLOT TYPES: `⊢W'` is typed
-- `Γ ⊢ W' ∷ Nat`, so `⊢single ⊢W'` is a `Sub⊢ (Γ ▹ Nat) Γ`, but the slot
-- it substitutes at that depth is not `Nat` — Agda reports `W'` where it
-- wants `R1'`, i.e. the two levels' contexts are exchanged.
--
-- ⇒ WHAT IS NEEDED: track what TYPE each of the five slots actually has
--   (they are `PairT`, `Nat`, `G1`, `Nat`, `G2` reading outward from `G3`)
--   and give each `⊢single` a derivation at THAT type, rather than at
--   `Nat` throughout.  `⊢W'`/`⊢R1'`/`⊢R2'` are already green — this is
--   about which one goes at which depth, not about proving them.
--
-- ⚠ Layers 1-3 ARE green and committed; this is the last typing layer.
------------------------------------------------------------------------

-- ★ TEST: the ZERO BRANCH chain alone.  `⊢G3z` sits at
--     (((((Γ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2)
--   and `single` removes the slot nearest `Γ` first, so the values are
--   gX(PairT), b'(Nat), R1'(G1), W'(Nat), R2'(G2), with DECREASING extS.
⊢Z3 : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
      (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) → _
⊢Z3 da db =
  sub-lemma (sub-lemma (sub-lemma (sub-lemma (sub-lemma (⊢G3z {B = G1} {C = G2})
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢gXx da db)))))))
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single db)))))
      (Sub⊢-ext (Sub⊢-ext (⊢single (⊢R1' da db)))))
      (Sub⊢-ext (⊢single (⊢W' da db))))
      (⊢single (⊢R2' da db))

-- ★ the MOTIVE: `⊢G3` sits ONE slot deeper than `⊢G3z` (its own `natrec`
--   variable), so every level gets one more `extS`.
-- ⚠⚠ TESTED 2026-08-19 — EXPLICIT TYPES MAKE IT WORSE, NOT BETTER.
--
--   `⊢M3` with `→ _`                    module green, ~15s
--   `⊢M3` with its type WRITTEN OUT     EXIT 143, 1m19s
--
--   …and that is `⊢M3` ALONE; the `⊢Fnr` assembly is still commented out.
--
-- ⇒ THE HYPOTHESIS IS DEAD.  The question was whether the types are BIG or
--   only big AS WRITTEN.  They are big: Agda's INFERENCE keeps them in a
--   compact form and writing them out EXPANDS them.  Stating types
--   explicitly is the standard remedy in this codebase and here it is
--   actively harmful.
--
-- ★ ONE THING THE TEST DID ESTABLISH: the context collapses.  Agda accepted
--   `(Γ ▹ Nat)` and objected only to the substitution arity, so
--   `subTy σ⁵ Nat ≡ Nat` definitionally — the layered context in the probe
--   output was DISPLAY, not substance.
--
-- ⇒ So the remaining direction is NOT "state it smaller" but "never build
--   the five-level stack at all" — i.e. change what the one-hole context is
--   expressed in terms of.  That is a redesign of `midAt`, and it would
--   invalidate `gcd-le-prefix`, which is green.  Scope before starting.
-- ⚠ OPTION B, FIRST ATTEMPT — type error at 13.3s (NOT an OOM), and it
--   revealed TWO obstacles where I expected one:
--
--     1. THE PEEL IS REQUIRED.  The five substitutions do NOT collapse
--        definitionally onto `gcdG (plusTm …)`.  The mismatch is at the `μ`
--        LEAVES — `subTm (extS σ) … (w⁵ b')` vs `w (w b')` — so the peel is
--        on `μ` alone, as scoped.  ⚠ Note `μ` appears WEAKENED once inside
--        `gcdIH`, so the depths are `w (w b')`, not `w b'`.
--
--     2. STATING THE TYPE UN-DETERMINES THE BODY.  With the signature
--        given, the σ's in the `sub-ty` chain print as METAS (`_σ_992`).
--        Inference had been fixing them from the inferred type; an explicit
--        type removes that constraint and they must be pinned too.
--
--   ⚠ AND THE 13.3s IS NOT EVIDENCE THE REDUCED MOTIVE IS CHEAP — an early
--     type error never reaches the expensive elaboration.  Do not read it
--     as a win.
--
--   ⇒ Option B is still live but is TWO fixes, not one: peel `μ` (the wkS
--     family, known tractable) AND pin the chain's σ's.
⊢M3 : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
      (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) →
      _
⊢M3 da db =
  sub-ty (sub-ty (sub-ty (sub-ty (sub-ty (⊢G3 {B = G1} {C = G2})
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢gXx da db))))))))
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single db))))))
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢R1' da db))))))
      (Sub⊢-ext (Sub⊢-ext (⊢single (⊢W' da db)))))
      (Sub⊢-ext (⊢single (⊢R2' da db)))

-- ★ the SUCCESSOR branch: THREE generalised slots here (`B`=G1, `C`=G2,
--   `D`=G3 — the third natrec's own motive), all pinned.  `⊢G3s` sits TWO deeper (`natrec` binds two in its
--   successor branch), so two more `extS` at every level.
⊢S3 : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
      (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) → _
⊢S3 da db =
  sub-lemma (sub-lemma (sub-lemma (sub-lemma (sub-lemma (⊢G3s {B = G1} {C = G2} {D = G3})
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢gXx da db)))))))))
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single db)))))))
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢R1' da db)))))))
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢W' da db))))))
      (Sub⊢-ext (Sub⊢-ext (⊢single (⊢R2' da db))))

------------------------------------------------------------------------
-- ⚠⚠⚠ THE ASSEMBLY OOMs BY EVERY ROUTE — FOUR MEASURED, ALL UNCONTENDED.
--
--   `⊢natrec-var` on the layer-4 pieces   type error (`R2' != nzero`):
--                                         `single nzero`/`nrs` are INSIDE
--                                         the stack, it wants them outside
--   push with `sub-lemma`, one term       EXIT 143, 2m04s
--   …split into five `Def`s               EXIT 143, 1m50s
--   …via `⊢natrec-var-push`/`-tr`         EXIT 143, 4m54s  ← WORSE
--
--   in a module that otherwise checks in ~15s, 0 errors throughout.
--
-- ⚠⚠ AND THE LIBRARY ROUTE WAS MY HYPOTHESIS, MEASURED WRONG.  I expected
--   `…LibNatrec`'s lemmas to fix it the way `AbsProbe`'s abstract-then-
--   instantiate fixed the other half of gap A.  It does not, and the reason
--   is the difference between the two cases:
--
--     * THERE, the type stayed the SAME SIZE and only the ELABORATION moved
--       — so checking it once generically was a pure win (9.9s → 1.7s).
--     * HERE, the TYPE ITSELF GROWS with stack depth.  Each transport is
--       typed at `subTy (extS σ) M`, and by level five `M` is a fivefold
--       substituted `G3` no matter where the proof was checked.
--
--   ⇒ LIBRARY ABSTRACTION MOVES THE PROOF, NOT THE TYPE.  That is the
--     limit of the remedy that closed equation 3, stated precisely.
--
-- ⇒ SO THE REMAINING OPTION IS THE ONE `irrT` NEEDED: SHRINK WHAT THE
--   ASSEMBLY'S TYPES MENTION.  The five-level stack over `G3` is the
--   problem; nothing that preserves it will fit.  That is a redesign of how
--   the one-hole context is expressed, not another proof tactic.
--
-- ★ EVERYTHING ELSE IS GREEN AND COMMITTED: the bridge, the reduction
--   skeleton, all four typing layers, and the library lemmas (which are
--   correct and useful — `⊢natrec-var-push`/`-tr` just do not solve THIS).
------------------------------------------------------------------------

{-
⊢Fnr0 : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
        (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) → _
⊢Fnr0 da db =
  ⊢natrec-var-push
    (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢gXx da db))))))
    (⊢G3 {B = G1} {C = G2}) (⊢G3z {B = G1} {C = G2})
    (⊢G3s {B = G1} {C = G2} {D = G3})

⊢Fnr1 : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
        (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) → _
⊢Fnr1 da db =
  ⊢natrec-var-tr (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single db)))) (⊢Fnr0 da db)

⊢Fnr2 : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
        (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) → _
⊢Fnr2 da db =
  ⊢natrec-var-tr (Sub⊢-ext (Sub⊢-ext (⊢single (⊢R1' da db)))) (⊢Fnr1 da db)

⊢Fnr3 : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
        (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) → _
⊢Fnr3 da db =
  ⊢natrec-var-tr (Sub⊢-ext (⊢single (⊢W' da db))) (⊢Fnr2 da db)

⊢Fnr : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
       (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) → _
⊢Fnr da db = ⊢natrec-var-tr (⊢single (⊢R2' da db)) (⊢Fnr3 da db)

{-
------------------------------------------------------------------------
-- ★★★ LAYER 4 — the THIRD `natrec`'s motive and branches, through the
--     FIVE-level stack.  Same recipe as layer 3, one level deeper at each
--     step; `⊢natrec-var` then assembles them at the HOLE.
--
-- ⚠ `B`/`C` PINNED — `⊢G3`/`⊢G3z`/`⊢G3s` have TWO generalised sibling
--   slots here (`G1` and `G2`), neither inferable.
------------------------------------------------------------------------

-- ★ TEST: state the type EXPLICITLY with the CONTEXT COLLAPSED to
--   `Γ ▹ Nat`.  If this checks, `subTy σ⁵ Nat ≡ Nat` definitionally and the
--   inferred layered context was only big AS WRITTEN.
⊢M3 : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
      (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) →
      (Γ ▹ Nat) ⊢ty
        subTy (extS (single (R2' a' b')))
          (subTy (extS (extS (single (W' a' b'))))
            (subTy (extS (extS (extS (single (R1' a' b')))))
              (subTy (extS (extS (extS (extS (single b')))))
                (subTy (extS (extS (extS (extS (extS (single (gXx a' b'))))))) G3))))
⊢M3 da db =
  sub-ty (sub-ty (sub-ty (sub-ty (sub-ty (⊢G3 {B = G1} {C = G2})
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢gXx da db))))))))
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single db))))))
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢R1' da db))))))
      (Sub⊢-ext (Sub⊢-ext (⊢single (⊢W' da db)))))
      (Sub⊢-ext (⊢single (⊢R2' da db)))

⊢Z3 : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
      (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) → _
⊢Z3 da db =
  sub-lemma (sub-lemma (sub-lemma (sub-lemma (sub-lemma (⊢G3z {B = G1} {C = G2})
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single (⊢gXx da db)))))))
      (Sub⊢-ext (Sub⊢-ext (Sub⊢-ext (⊢single db)))))
      (Sub⊢-ext (Sub⊢-ext (⊢single (⊢R1' da db)))))
      (Sub⊢-ext (⊢single (⊢W' da db))))
      (⊢single (⊢R2' da db))
-}

-}

------------------------------------------------------------------------
-- ★ WHAT THE MOTIVE ACTUALLY LOOKS LIKE — probed 2026-08-19.
--
-- Printing `⊢M3`'s type (wrong-target probe) shows the five substitutions
-- do NOT collapse on their own.  They sit as five nested `subTy` layers
-- around `gcdIH (plusTm …)` — and also around `El ⌜Nat⌝`, and even in the
-- CONTEXT, which prints as `Γ ▹ subTy σ⁵ Nat` rather than `Γ ▹ Nat`.
--
-- ⚠ CAVEAT, and it matters: Agda's error messages show UNNORMALISED forms,
--   so this does not prove the ELABORATED types are that large.  `subTy σ`
--   on a closed type (`Nat`, `El ⌜Nat⌝`) should compute away.  The print is
--   evidence about the SYNTACTIC form the derivations carry, not about
--   what the checker holds.
--
-- ⇒ THE CHEAP TEST NOT YET RUN: state `⊢M3`/`⊢Z3`/`⊢S3` with EXPLICIT
--   REDUCED types instead of `_`.  If `subTy σ⁵ Nat ≡ Nat` definitionally,
--   the contexts collapse and the stated types are small — and Agda checks
--   against the small form rather than inferring the layered one.  That is
--   one line per definition and would discriminate "the types are big" from
--   "the types are only big as WRITTEN".
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★★★ SCOPING THE `midAt` REDESIGN — 2026-08-19.
--
-- ★ THE FACT EVERYTHING TURNS ON, and it was not established until now:
--
--     gcdG μx = Π (gcdIH μx) (El ⌜Nat⌝)          -- SMALL, parametric in μx
--     G3      = gcdG (plusTm (nsuc (var (vs² vz))) (nsuc (var (vs⁴ vz))))
--
--   `vs² vz` is `k'` (a's predecessor), `vs⁴ vz` is `n'` (b's).  Under the
--   five-level stack those become `W'` and `b'`, and `wkS2` already proves
--   `W' ≡ a'`.  So the motive REDUCES to
--
--     gcdG (plusTm (nsuc a') (nsuc b'))
--
--   which is TINY.  G3 never mentions `var vz` (established earlier — that
--   is why the transport is sound at all), so nothing else varies.
--
-- ⚠ AND THIS IS WHY THE EXPLICIT-TYPE TEST FAILED.  It wrote the LAYERED
--   form — five nested `subTy`s — which is not the reduced form at all.
--   Stating the REDUCED motive is untested and is a different proposition.
--
-- ─── OPTIONS, cheapest first ────────────────────────────────────────────
--
-- (B) STATE THE MOTIVE REDUCED.  `⊢M3 : … ⊢ty gcdG (plusTm (nsuc a') …)`,
--     with a peel proving the five-fold substituted form equals it.  The
--     peel is on `μ` ALONE — one `plusTm` argument pair — not on the whole
--     type.  ⇒ CHEAPEST TEST BY FAR, and the one to run first.
--     Risk: the peel may need the same `wkS` family already used for `W'`
--     and the descent, which is known-tractable (both landed in one line).
--
-- (A) COMPUTE `Z3'`/`S3'` DIRECTLY.  `G3z = lam (app (app (var vz) PAIRᶻ)
--     CERTᶻ)` and `PAIRᶻ`/`CERTᶻ` are modest terms in two variables, so the
--     substituted branches ARE writable in closed form.  ⇒ removes the
--     stack from the TERMS as well as the types.  More writing than (B),
--     and `gcd-le-prefix` must be re-verified against the new forms.
--
-- (C) INTERNAL SPLIT INSTEAD OF TRANSPORT.  Prove eq 4 by internal `natrec`
--     on the descent with `eqG`/`pwT`, as `gcdStepExt` does — the motive is
--     then WRITTEN, never a substitution residue.  ⇒ no stack at all, but
--     it is a different proof, and `gcd-le-prefix`/`-tail` become unused.
--
-- (D) Id-VALUED `RecCall`.  Replace `RecCall`'s `⟶*` with a `Prv … (Id …)`
--     so eq 4 joins the amrec-level machinery that eq 3 uses, where gcd's
--     step internals never enter the types.  ⇒ most principled, biggest
--     blast radius: `RecCall`/`recRed` are used by eq 3 as well.
--
-- ⇒ RECOMMENDATION: run (B) first — it is one signature plus one peel, and
--   it either fixes the OOM outright or tells us the motive is not the
--   binding constraint.  (C) is the fallback and reuses machinery that is
--   already proved.  (D) is the right END STATE but should not be started
--   before eq 4 works at all.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ OPTION B, ATTEMPT 2 — the per-level peel, from an EXISTING lemma.
--
-- `gcdG μ = Π (gcdIH μ) (El ⌜Nat⌝)` and `gcdIH μ = aIHTat PairT ⌜Nat⌝ msr μ`.
-- `aIHTat-sub` ALREADY gives the naturality:
--
--   subTy σ (aIHTat A cM m μ) ≡ aIHTat (subTy σ A) (subTm (extS σ) cM)
--                                      (subTm (extS σ) m) (subTm σ μ)
--
-- and `PairT`/`⌜Nat⌝` are closed while `msr` mentions only `vz`, which
-- `extS σ` fixes — so all three collapse and only `μ` moves.
--
-- ⇒ ONE LEVEL of the peel is this lemma; the motive's five levels are five
--   applications.  ★ REUSABLE: `gcdG-sub` belongs beside `gcdG` in
--   `…GcdStep`; its CONTENT is `aIHTat-sub`, which is already general.
------------------------------------------------------------------------

-- (`gcdG-sub` moved to `…GcdStep`, beside `gcdG`.)

-- (`pw1`/`pw2`/`pw3` moved to `…LibWk`, beside `sub-w`.)

------------------------------------------------------------------------
-- ★★★ COLLAPSING THE MOTIVE — five `gcdG-sub`s.
--
-- Each level rewrites `subTy σ (gcdG μ)` to `gcdG (subTm σ μ)`, walking the
-- substitutions inward until only `μ` carries them.  `μ` is then a `plusTm`
-- of two variables the stack fills, and those DO compute.
--
-- ⚠ The substitutions are NAMED — writing them inline is five levels of
--   nesting and the parens do not survive hand-counting.
------------------------------------------------------------------------

module _ {Γ : Cx} (a' b' : RTm Γ) where

  t0 : Sub ((((((Γ ∙) ∙) ∙) ∙) ∙) ∙) (((((Γ ∙) ∙) ∙) ∙) ∙)
  t0 = extS (extS (extS (extS (extS (single (gXx a' b'))))))
  t1 : Sub (((((Γ ∙) ∙) ∙) ∙) ∙) ((((Γ ∙) ∙) ∙) ∙)
  t1 = extS (extS (extS (extS (single b'))))
  t2 : Sub ((((Γ ∙) ∙) ∙) ∙) (((Γ ∙) ∙) ∙)
  t2 = extS (extS (extS (single (R1' a' b'))))
  t3 : Sub (((Γ ∙) ∙) ∙) ((Γ ∙) ∙)
  t3 = extS (extS (single (W' a' b')))
  t4 : Sub ((Γ ∙) ∙) (Γ ∙)
  t4 = extS (single (R2' a' b'))

  μ0 : RTm ((((((Γ ∙) ∙) ∙) ∙) ∙) ∙)
  μ0 = plusTm (nsuc (var (vs (vs vz)))) (nsuc (var (vs (vs (vs (vs vz))))))

  M3-collapse : subTy t4 (subTy t3 (subTy t2 (subTy t1 (subTy t0 G3))))
              ≡ gcdG (subTm t4 (subTm t3 (subTm t2 (subTm t1 (subTm t0 μ0)))))
  -- ⚠ σ PINNED on every call — `gcdG-sub`'s σ occurs only in its subject.
  M3-collapse =
    trans (cong (λ T → subTy t4 (subTy t3 (subTy t2 (subTy t1 T))))
                (gcdG-sub {σ = t0} μ0))
      (trans (cong (λ T → subTy t4 (subTy t3 (subTy t2 T)))
                   (gcdG-sub {σ = t1} (subTm t0 μ0)))
        (trans (cong (λ T → subTy t4 (subTy t3 T))
                     (gcdG-sub {σ = t2} (subTm t1 (subTm t0 μ0))))
          (trans (cong (subTy t4)
                       (gcdG-sub {σ = t3} (subTm t2 (subTm t1 (subTm t0 μ0)))))
                 (gcdG-sub {σ = t4}
                           (subTm t3 (subTm t2 (subTm t1 (subTm t0 μ0))))))))

  -- ★ …and now `μ` DOES collapse: three peels per side, at the lifting
  --   depths of `t2`/`t3`/`t4` (`extS³`, `extS²`, `extS¹`).
  μ-computes : subTm t4 (subTm t3 (subTm t2 (subTm t1 (subTm t0 μ0))))
             ≡ plusTm (nsuc (w (W' a' b'))) (nsuc (w b'))
  μ-computes = cong₂ (λ x y → plusTm (nsuc x) (nsuc y)) sideA sideB
    where
      -- `W'` enters MID-stack (it fills the `k'` slot), so by the time the
      -- outer substitution reaches it only ONE weakening is left.
      sideA = pw1 (W' a' b')
      sideB = trans (cong (λ x → subTm t4 (subTm t3 x)) (pw3 b'))
                    (trans (cong (subTm t4) (pw2 b')) (pw1 b'))

  -- ★★★★★ …AND THE MOTIVE, STATED SMALL.
  --
  --   `M3-collapse` then `μ-computes` rewrite the five-level substituted
  --   motive to `gcdG (plusTm (nsuc (w W')) (nsuc (w b')))`.  The
  --   DERIVATION is unchanged; only its STATED type shrinks — which is
  --   the whole point of option (B).
  M3-small : subTy t4 (subTy t3 (subTy t2 (subTy t1 (subTy t0 G3))))
           ≡ gcdG (plusTm (nsuc (w (W' a' b'))) (nsuc (w b')))
  M3-small = trans M3-collapse (cong gcdG μ-computes)

  -- ★★ THE ZERO BRANCH's chain — same five `gcdG-sub`s, one `extS` less at
  --    every level (`⊢G3z` sits at 5 slots, `⊢G3` at 6).
  u0 : Sub (((((Γ ∙) ∙) ∙) ∙) ∙) ((((Γ ∙) ∙) ∙) ∙)
  u0 = extS (extS (extS (extS (single (gXx a' b')))))
  u1 : Sub ((((Γ ∙) ∙) ∙) ∙) (((Γ ∙) ∙) ∙)
  u1 = extS (extS (extS (single b')))
  u2 : Sub (((Γ ∙) ∙) ∙) ((Γ ∙) ∙)
  u2 = extS (extS (single (R1' a' b')))
  u3 : Sub ((Γ ∙) ∙) (Γ ∙)
  u3 = extS (single (W' a' b'))
  u4 : Sub (Γ ∙) Γ
  u4 = single (R2' a' b')

  μz : RTm (((((Γ ∙) ∙) ∙) ∙) ∙)
  μz = plusTm (nsuc (var (vs vz))) (nsuc (var (vs (vs (vs vz)))))

  Z3-collapse : subTy u4 (subTy u3 (subTy u2 (subTy u1 (subTy u0 (gcdG μz)))))
              ≡ gcdG (subTm u4 (subTm u3 (subTm u2 (subTm u1 (subTm u0 μz)))))
  Z3-collapse =
    trans (cong (λ T → subTy u4 (subTy u3 (subTy u2 (subTy u1 T))))
                (gcdG-sub {σ = u0} μz))
      (trans (cong (λ T → subTy u4 (subTy u3 (subTy u2 T)))
                   (gcdG-sub {σ = u1} (subTm u0 μz)))
        (trans (cong (λ T → subTy u4 (subTy u3 T))
                     (gcdG-sub {σ = u2} (subTm u1 (subTm u0 μz))))
          (trans (cong (subTy u4)
                       (gcdG-sub {σ = u3} (subTm u2 (subTm u1 (subTm u0 μz)))))
                 (gcdG-sub {σ = u4}
                           (subTm u3 (subTm u2 (subTm u1 (subTm u0 μz))))))))

  -- ★ `μz` collapses too.  PROBED, not guessed — tracing each slot through
  --   the stack:
  --     `var (vs vz)`  (the `k'` slot) passes `u0`–`u2` UNTOUCHED (each
  --        `extSᵏ σ` maps it to itself), `u3` yields `w W'`, `u4` cancels
  --        that by `wk-single`.                       ⇒ one `wk-single`
  --     `var (vs³ vz)` (the `n'` slot) survives `u0`, becomes `w³ b'` at
  --        `u1`, then `pw2`/`pw1`/`wk-single`.        ⇒ three peels
  --   The asymmetry is the same one the motive had, one level shallower.
  μz-computes : subTm u4 (subTm u3 (subTm u2 (subTm u1 (subTm u0 μz))))
              ≡ plusTm (nsuc (W' a' b')) (nsuc b')
  μz-computes = cong₂ (λ x y → plusTm (nsuc x) (nsuc y)) zA zB
    where
      zA = wk-single (W' a' b')
      zB = trans (cong (λ x → subTm u4 (subTm u3 x)) (pw2 b'))
                 (trans (cong (subTm u4) (pw1 b')) (wk-single b'))

  Z3-small : subTy u4 (subTy u3 (subTy u2 (subTy u1 (subTy u0 (gcdG μz)))))
           ≡ gcdG (plusTm (nsuc (W' a' b')) (nsuc b'))
  Z3-small = trans Z3-collapse (cong gcdG μz-computes)

  -- ★★ THE SUCCESSOR BRANCH — two `extS` deeper again (`⊢G3s` sits at 7
  --    slots; `natrec` binds two in its successor branch).
  v0 : Sub ((((((( Γ ∙) ∙) ∙) ∙) ∙) ∙) ∙) (((((( Γ ∙) ∙) ∙) ∙) ∙) ∙)
  v0 = extS (extS (extS (extS (extS (extS (single (gXx a' b')))))))
  v1 : Sub (((((( Γ ∙) ∙) ∙) ∙) ∙) ∙) ((((( Γ ∙) ∙) ∙) ∙) ∙)
  v1 = extS (extS (extS (extS (extS (single b')))))
  v2 : Sub ((((( Γ ∙) ∙) ∙) ∙) ∙) (((( Γ ∙) ∙) ∙) ∙)
  v2 = extS (extS (extS (extS (single (R1' a' b')))))
  v3 : Sub (((( Γ ∙) ∙) ∙) ∙) ((( Γ ∙) ∙) ∙)
  v3 = extS (extS (extS (single (W' a' b'))))
  v4 : Sub ((( Γ ∙) ∙) ∙) (( Γ ∙) ∙)
  v4 = extS (extS (single (R2' a' b')))

  μs : RTm ((((((( Γ ∙) ∙) ∙) ∙) ∙) ∙) ∙)
  μs = plusTm (nsuc (var (vs (vs (vs vz)))))
              (nsuc (var (vs (vs (vs (vs (vs vz)))))))

  S3-collapse : subTy v4 (subTy v3 (subTy v2 (subTy v1 (subTy v0 (gcdG μs)))))
              ≡ gcdG (subTm v4 (subTm v3 (subTm v2 (subTm v1 (subTm v0 μs)))))
  S3-collapse =
    trans (cong (λ T → subTy v4 (subTy v3 (subTy v2 (subTy v1 T))))
                (gcdG-sub {σ = v0} μs))
      (trans (cong (λ T → subTy v4 (subTy v3 (subTy v2 T)))
                   (gcdG-sub {σ = v1} (subTm v0 μs)))
        (trans (cong (λ T → subTy v4 (subTy v3 T))
                     (gcdG-sub {σ = v2} (subTm v1 (subTm v0 μs))))
          (trans (cong (subTy v4)
                       (gcdG-sub {σ = v3} (subTm v2 (subTm v1 (subTm v0 μs)))))
                 (gcdG-sub {σ = v4}
                           (subTm v3 (subTm v2 (subTm v1 (subTm v0 μs))))))))

  -- ★ `μs` collapses.  TRACED slot by slot (the module is 7m/iteration, so
  --   derived rather than probed — the trace is short enough to follow):
  --     `var (vs³ vz)` (k'): `v0`/`v1`/`v2` pass it through (each `extSᵏ σ`
  --        with k>3 maps it to itself), `v3 = extS³ (single W')` yields
  --        `w³ W'`, `v4 = extS² (single R2')` peels one ⇒ ONE `pw2`.
  --     `var (vs⁵ vz)` (n'): `v0` passes, `v1 = extS⁵ (single b')` yields
  --        `w⁵ b'`, then `pw4`/`pw3`/`pw2`   ⇒ THREE peels.
  μs-computes : subTm v4 (subTm v3 (subTm v2 (subTm v1 (subTm v0 μs))))
              ≡ plusTm (nsuc (w (w (W' a' b')))) (nsuc (w (w b')))
  μs-computes = cong₂ (λ x y → plusTm (nsuc x) (nsuc y)) sA sB
    where
      sA = pw2 (W' a' b')
      sB = trans (cong (λ x → subTm v4 (subTm v3 x)) (pw4 b'))
                 (trans (cong (subTm v4) (pw3 b')) (pw2 b'))

  S3-small : subTy v4 (subTy v3 (subTy v2 (subTy v1 (subTy v0 (gcdG μs)))))
           ≡ gcdG (plusTm (nsuc (w (w (W' a' b')))) (nsuc (w (w b'))))
  S3-small = trans S3-collapse (cong gcdG μs-computes)

------------------------------------------------------------------------
-- ★★★★★ THE ASSEMBLY, AT SMALL TYPES.
--
-- `⊢M3`'s chain produces exactly `M3-small`'s left-hand side (the `sub-ty`
-- levels use `Sub⊢-ext` counts 5,4,3,2,1, which are `t0`…`t4`), so one
-- `subst` restates it at the collapsed motive.
------------------------------------------------------------------------

⊢M3s : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
       (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) →
       (Γ ▹ Nat) ⊢ty gcdG (plusTm (nsuc (w (W' a' b'))) (nsuc (w b')))
⊢M3s {Γ} {a'} {b'} da db =
  subst (λ T → (Γ ▹ Nat) ⊢ty T) (M3-small a' b') (⊢M3 da db)

-- ★ THE BRANCHES, same shape.  `subTy (single nzero)` and `subTy nrs` of the
--   small motive collapse through `gcdG-sub` — only `gcdG`'s PARAMETER
--   moves — so each is one `gcdG-sub` and one `subst`.

Zs-collapse : {Γ : Cx} (a' b' : RTm Γ) →
              subTy (single nzero) (gcdG (plusTm (nsuc (w (W' a' b'))) (nsuc (w b'))))
            ≡ gcdG (subTm (single nzero)
                     (plusTm (nsuc (w (W' a' b'))) (nsuc (w b'))))
Zs-collapse a' b' =
  gcdG-sub {σ = single nzero} (plusTm (nsuc (w (W' a' b'))) (nsuc (w b')))

Ss-collapse : {Γ : Cx} (a' b' : RTm Γ) →
              subTy nrs (gcdG (plusTm (nsuc (w (W' a' b'))) (nsuc (w b'))))
            ≡ gcdG (subTm nrs (plusTm (nsuc (w (W' a' b'))) (nsuc (w b'))))
Ss-collapse a' b' =
  gcdG-sub {σ = nrs} (plusTm (nsuc (w (W' a' b'))) (nsuc (w b')))

------------------------------------------------------------------------
-- ★★★★★ THE ASSEMBLY — `⊢natrec-var` AT THE SMALL MOTIVE.
--
-- ⚠ THIS IS THE STEP THAT FAILED FOUR TIMES: once as a type error
--   (`R2' != nzero`, the branches' `single nzero`/`nrs` being INSIDE the
--   stack) and three times as an OOM (nested `sub-lemma`; split into five
--   `Def`s; via `⊢natrec-var-push`/`-tr`).  Every one of those carried
--   five-deep `subTy` types.  Now every type is in `gcdG` form.
------------------------------------------------------------------------

-- ⚠ AND EACH BRANCH NEEDS ITS OWN COLLAPSE CHAIN.  Attempted `⊢Z3s` by
--   `subst`ing `⊢Z3` along `Zs-collapse` alone — that fails, because
--   `⊢Z3`'s type is ALSO the five-level layered form (it is `G3z`'s type
--   under the same stack).  `Zs-collapse` only relates the SMALL motive to
--   its substituted parameter; it says nothing about the layered one.
--
-- ⇒ WHAT IS NEEDED, and it is the shape already proved for the motive:
--     `Z3-collapse` — five `gcdG-sub`s on `G3z`'s type, then a `μ` peel
--     `S3-collapse` — the same for `G3s`, two `extS` deeper
--   Then `⊢Z3s`/`⊢S3s` are one `subst` each, and `⊢natrec-var` assembles
--   `⊢M3s`/`⊢Z3s`/`⊢S3s` — all three in `gcdG` form.
--
-- ★ The motive chain (`M3-collapse` + `μ-computes` + `M3-small` + `⊢M3s`)
--   is the worked template; the branches differ only in depth.

------------------------------------------------------------------------
-- ★★★★★ THE BRANCH DERIVATIONS, AT THE SMALL TYPES.
--
-- `⊢Z3`/`⊢S3` produce exactly the left-hand sides of `Z3-small`/`S3-small`
-- (their `sub-lemma` levels are `u0`…`u4` and `v0`…`v4`), so each is one
-- `subst` — the same shape as `⊢M3s`.
------------------------------------------------------------------------

⊢Z3s : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
       (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) →
       Γ ⊢ Z3' a' b' ∷ gcdG (plusTm (nsuc (W' a' b')) (nsuc b'))
⊢Z3s {Γ} {a'} {b'} da db =
  subst (λ T → Γ ⊢ Z3' a' b' ∷ T) (Z3-small a' b') (⊢Z3 da db)

------------------------------------------------------------------------
-- ⚠⚠ `⊢S3s` — THE SUCCESSOR BRANCH'S RESTATEMENT IS BLOCKED.  Four attempts:
--
--   `subst` with `_` for the context        OOM, 1m52s
--   …context pinned                         type error — `⊢S3`'s context
--                                           mentions the LAYERED motive
--   two `subst`s (context then type)        needs `⊢S3`'s layered type
--                                           WRITTEN, which is the thing the
--                                           collapse avoids
--   `ctx-conv refl d = d` (type implicit)   OOM, 2m20s
--
-- ★ WHY THE LAST ONE FAILS, and it is the interesting part: matching on
--   `refl` forces Agda to evaluate `M3-small`'s whole `trans` chain to
--   `refl`.  So a lemma written to AVOID naming the big type instead forces
--   COMPUTING the proof that relates it.  Keeping the type implicit is not
--   enough if the EQUALITY has to be inspected.
--
-- ⚠ AND THE SUCCESSOR BRANCH IS THE ONLY ONE WITH THIS PROBLEM.  `natrec`
--   binds the motive in its successor branch, so `⊢S3` is the only piece
--   whose CONTEXT mentions the motive; `⊢M3s`/`⊢Z3s` needed one `subst`
--   each and both are green.  This is inherent to `natrec`, not to the
--   collapse approach.
--
-- ⇒ WHAT TO TRY: a context-conversion that does NOT inspect the equality —
--   e.g. carrying the motive as a module PARAMETER so both forms are the
--   same variable, or restating `⊢S3` at the small motive from the start
--   (its `sub-lemma` chain built at `gcdG`-form inputs) rather than
--   converting after the fact.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★★★ ROUTE (ii) — COLLAPSE AS YOU PUSH, don't shrink afterwards.
--
-- The four failed `⊢S3s` attempts all built the layered type first and then
-- tried to convert it.  `push-gcdG` instead collapses at EVERY step, so the
-- type is never anything but `gcdG` applied to a parameter:
--
--     Γ ⊢ t ∷ gcdG μ   ⇒   Δ ⊢ subTm σ t ∷ gcdG (subTm σ μ)
--
-- ⚠ AND THE EQUALITY IT INSPECTS IS ONE `gcdG-sub`, not a `trans` chain.
--   That is what killed `ctx-conv`: matching on `refl` had to evaluate
--   `M3-small`'s whole chain.  A single-step equality is cheap to match.
--
-- ★ REUSABLE for any `gcdG`-typed derivation being transported.
------------------------------------------------------------------------

push-gcdG : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {t : RTm ⌊ Γ ⌋} {μ : RTm ⌊ Γ ⌋} →
            Sub⊢ Γ Δ σ → Γ ⊢ t ∷ gcdG μ →
            Δ ⊢ subTm σ t ∷ gcdG (subTm σ μ)
push-gcdG {Δ = Δ} {σ = σ} {t = t} {μ = μ} σ⊢ d =
  subst (λ T → Δ ⊢ subTm σ t ∷ T) (gcdG-sub {σ = σ} μ) (sub-lemma d σ⊢)

------------------------------------------------------------------------
-- ⚠⚠⚠ `⊢S3s` RESISTS EVERY TRANSPORT FORMULATION — SIX ATTEMPTS, MEASURED.
--
--   `subst`, context as `_`                     OOM   1m52s
--   …context pinned                             type error (ctx is layered)
--   two `subst`s (context then type)            needs the layered type
--                                               WRITTEN — self-defeating
--   `ctx-conv refl d = d`, type implicit        OOM   2m20s
--   route (ii): five `push-gcdG`, one term      OOM   3m52s
--   …the same, split into five `Def`s           OOM   1m24s
--
-- ★ EVERY SURROUNDING PIECE IS GREEN: all three collapse chains
--   (`M3-small`/`Z3-small`/`S3-small`), `⊢M3s`, `⊢Z3s`, and `push-gcdG`
--   itself.  ONLY the successor branch's derivation fails.
--
-- ★★ AND THE COMMON FACTOR IS THAT ALL SIX **TRANSPORT** `⊢S3`.  Route (ii)
--   was supposed to differ by collapsing per step — and it does keep the
--   TYPE small — but it still carries `⊢S3`'s derivation through five
--   substitutions, and that is apparently the cost, not the type.
--
--   ⚠ NOTE THIS CONTRADICTS THE WORKING HYPOTHESIS OF THE WHOLE COLLAPSE
--     EFFORT.  `M3-small` demonstrably made things CHEAPER (1m02s against a
--     6m44s baseline), so type size is real — but it is not the ONLY cost
--     here, and for `⊢S3` it is not the binding one.
--
-- ⇒ SO THE NEXT MOVE IS NOT ANOTHER TRANSPORT.  The successor branch has to
--   be BUILT at its final context rather than moved there — i.e. an
--   `⊢G3s`-analogue stated directly at the substituted slots, the way
--   `⊢natrec-var` states its branches rather than transporting them.
--   ⚠ Do not attempt a seventh transport.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ⚠⚠⚠ ATTEMPT 7 FAILS TOO — AND IT SETTLES THE MECHANISM.
--
-- Transport only the LEAVES: `⊢G3s` is `⊢lam <ih> (⊢app (⊢app (⊢var here)
-- ⊢PAIRˢ) ⊢CERTˢ)`, and `⊢PAIRˢ`'s type is `PairT` — CLOSED.  It cannot
-- grow under any substitution.  Five pushes, one per `Def`.
--
--     OOM, 1m39s.
--
-- ★★★ SO TYPE SIZE IS NOT THE BINDING COST.  A derivation whose type is a
--   closed constant still cannot be carried through five substitutions.
--   What is expensive is the TRANSPORT ITSELF — `sub-lemma` recursing over
--   a derivation under a stack of `Sub⊢-ext`s, where every variable lookup
--   walks the whole stack.
--
-- ⚠ THIS CORRECTS THE PREMISE OF THE WHOLE COLLAPSE EFFORT.  `M3-small` is
--   still a real win (1m02s vs a 6m44s baseline), so type size MATTERS —
--   but it is not what blocks `⊢S3s`, and no amount of shrinking types will
--   unblock it.
--
-- ⇒ SEVEN attempts on `⊢S3s`, all measured.  See the session summary for
--   the full side-by-side across gap A.
------------------------------------------------------------------------
