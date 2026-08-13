------------------------------------------------------------------------
-- OCP-0009 — ★ GATE 5: THE TYPING RULES, AND SUBJECT REDUCTION FOR ι.
--
-- Gates 1–4 settled the DESCRIPTION language and the logical relation's
-- shape.  The kernel now has the formers, the ι-rule, and a green tower —
-- but `⊢con`/`⊢elim` do not exist, so nothing can be TYPED at `Mu D`, and
-- three headline results (`sr` at ι, `prog`, `usplit`) are VACUOUS rather
-- than false.  This gate is about making them real.
--
-- ★★ THE DESIGN UNDER TEST — the payload's type and the method's type are
--   COMPUTED FROM THE DESCRIPTION, so NO NEW JUDGMENT is needed:
--
--     payTy   D C     a Σ-chain over one constructor's field list
--     methTy  D B C   a Π-chain, FIELD-then-IH at each `ρ`
--     methsTy D B E   a Σ-chain over the constructors, navigated by `sel`
--
--   ⚠ `methTy`'s shape is not free: it must match what `fields` ALREADY
--     does operationally, or ι's subject reduction cannot close.  That
--     correspondence IS the gate.
--
-- ⛔ NON-DEPENDENT ON PURPOSE.  `B` is a plain type, so this is a
--   RECURSOR, not an induction principle.  The dependent version needs the
--   method's result to mention the payload built from its OWN bound
--   variables — an accumulator threaded through a growing context.  A
--   separate increment, deliberately not priced here.
--
-- ⛔ AND THE Π/Σ RULES ARE NON-DEPENDENT TOO (`Π A (wk B)`, `Σ' A (wk B)`).
--   That is sound for this gate because EVERY body in the three chains
--   above is a weakening — which is exactly what the `-ren` lemmas say.
--   The kernel's own rules are dependent; porting means replacing each
--   `wk`-shaped premise with a `subTy (single _)` one and carrying the
--   same lemmas.
--
-- THE FOUR QUESTIONS:
--   Q18  ★ do the computed types typecheck — does the de Bruijn weakening
--        line up as the chains grow?
--   Q19  ★★ does `sel k` pick a method AT `methTy D B (lookupD D k)` out
--        of `methsTy D B D`?
--   Q20  ★★★ THE GATE: does `fields` applied to a well-typed method and a
--        well-typed payload land at `B`?  That is subject reduction for ι.
--   Q21  ★★ what does the TOTALITY of `lookupD` cost?  See the finding.
--
-- Self-contained: no imports.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeIotaTy where

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B} →
        x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- a miniature kernel
------------------------------------------------------------------------

data Cx : Set where
  ε  : Cx
  _∙ : Cx → Cx

infixl 5 _∙

data Var : Cx → Set where
  vz : {Γ : Cx} → Var (Γ ∙)
  vs : {Γ : Cx} → Var Γ → Var (Γ ∙)

data Desc : Set
data DCon : Set
data RTy : Cx → Set
data RTm : Cx → Set

data RTy where
  Unit : {Γ : Cx} → RTy Γ
  Π    : {Γ : Cx} → RTy Γ → RTy (Γ ∙) → RTy Γ
  Σ'   : {Γ : Cx} → RTy Γ → RTy (Γ ∙) → RTy Γ
  Mu   : {Γ : Cx} → Desc → RTy Γ

data RTm where
  var  : {Γ : Cx} → Var Γ → RTm Γ
  lam  : {Γ : Cx} → RTm (Γ ∙) → RTm Γ
  app  : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
  unit : {Γ : Cx} → RTm Γ
  pair : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
  fst  : {Γ : Cx} → RTm Γ → RTm Γ
  snd  : {Γ : Cx} → RTm Γ → RTm Γ
  con  : {Γ : Cx} → ℕ → RTm Γ → RTm Γ
  elim : {Γ : Cx} → Desc → RTm Γ → RTm Γ → RTm Γ

-- ★ CLOSED descriptions, exactly as the kernel has them.
data DCon where
  dι : DCon
  dρ : DCon → DCon
  dκ : RTy ε → DCon → DCon

data Desc where
  dnil : Desc
  _◃_  : DCon → Desc → Desc

infixr 5 _◃_

------------------------------------------------------------------------
-- renaming, and the two laws the computed types need
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : {Γ Δ : Cx} → Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

extR-cong : {Γ Δ : Cx} {ρ σ : Ren Γ Δ} → (∀ x → ρ x ≡ σ x) →
            ∀ x → extR ρ x ≡ extR σ x
extR-cong h vz     = refl
extR-cong h (vs x) = cong vs (h x)

renTy : {Γ Δ : Cx} → Ren Γ Δ → RTy Γ → RTy Δ
renTy ρ Unit     = Unit
renTy ρ (Π A B)  = Π (renTy ρ A) (renTy (extR ρ) B)
renTy ρ (Σ' A B) = Σ' (renTy ρ A) (renTy (extR ρ) B)
-- ★ descriptions are CLOSED, so `Mu` is inert under renaming ON THE NOSE.
--   Every computed type below inherits that; it is why none of the `-ren`
--   lemmas needs a parallel `renDesc`.
renTy ρ (Mu D)   = Mu D

renTy-cong : {Γ Δ : Cx} {ρ σ : Ren Γ Δ} → (∀ x → ρ x ≡ σ x) →
             (A : RTy Γ) → renTy ρ A ≡ renTy σ A
renTy-cong h Unit     = refl
renTy-cong h (Π A B)  = cong₂ Π (renTy-cong h A) (renTy-cong (extR-cong h) B)
renTy-cong h (Σ' A B) = cong₂ Σ' (renTy-cong h A) (renTy-cong (extR-cong h) B)
renTy-cong h (Mu D)   = refl

renTy-renTy : {Γ Δ Θ : Cx} (ρ : Ren Δ Θ) (σ : Ren Γ Δ) (A : RTy Γ) →
              renTy ρ (renTy σ A) ≡ renTy (λ x → ρ (σ x)) A
renTy-renTy ρ σ Unit     = refl
renTy-renTy ρ σ (Π A B)  =
  cong₂ Π (renTy-renTy ρ σ A)
          (trans (renTy-renTy (extR ρ) (extR σ) B)
                 (renTy-cong (λ { vz → refl ; (vs x) → refl }) B))
renTy-renTy ρ σ (Σ' A B) =
  cong₂ Σ' (renTy-renTy ρ σ A)
           (trans (renTy-renTy (extR ρ) (extR σ) B)
                  (renTy-cong (λ { vz → refl ; (vs x) → refl }) B))
renTy-renTy ρ σ (Mu D)   = refl

wk : {Γ : Cx} → RTy Γ → RTy (Γ ∙)
wk = renTy vs

-- weakening is natural: `renTy (extR ρ) ∘ wk ≡ wk ∘ renTy ρ`.
wk-nat : {Γ Δ : Cx} (ρ : Ren Γ Δ) (A : RTy Γ) →
         renTy (extR ρ) (wk A) ≡ wk (renTy ρ A)
wk-nat ρ A = trans (renTy-renTy (extR ρ) vs A) (sym (renTy-renTy vs ρ A))

-- ★ the unique renaming OUT OF the empty context.  This is what lets a
--   `dκ`'s CLOSED field type be used at an arbitrary Γ.
εren : {Γ : Cx} → Ren ε Γ
εren ()

εwkTy : {Γ : Cx} → RTy ε → RTy Γ
εwkTy = renTy εren

-- and it is absorbing: renaming a closed-weakened type does nothing.
εwk-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) (A : RTy ε) →
          renTy ρ (εwkTy A) ≡ εwkTy A
εwk-ren ρ A = trans (renTy-renTy ρ εren A) (renTy-cong (λ ()) A)

------------------------------------------------------------------------
-- ★ Q18 — THE COMPUTED TYPES.
------------------------------------------------------------------------

-- one constructor's PAYLOAD: `unit` at `dι`, a pair at each field.
payTy : {Γ : Cx} → Desc → DCon → RTy Γ
payTy D dι       = Unit
payTy D (dρ C)   = Σ' (Mu D)    (payTy D C)
payTy D (dκ A C) = Σ' (εwkTy A) (payTy D C)

-- ★★ one constructor's METHOD.  The `dρ` row is FIELD THEN IH because
--    that is the order `fields` applies them in:
--
--      fields D ms (dρ C) m p =
--        fields D ms C (app (app m (fst p)) (elim D ms (fst p))) (snd p)
--                            ^^^^^^^^^^^^^^ field  ^^^^^^^^^^^^^ IH
methTy : {Γ : Cx} → Desc → RTy Γ → DCon → RTy Γ
methTy D B dι       = B
methTy D B (dρ C)   = Π (Mu D) (Π (wk B) (methTy D (wk (wk B)) C))
methTy D B (dκ A C) = Π (εwkTy A) (methTy D (wk B) C)

-- the METHOD TUPLE, right-nested so `sel` navigates it by `fst`/`snd`.
methsTy : {Γ : Cx} → Desc → RTy Γ → Desc → RTy Γ
methsTy D B dnil    = Unit
methsTy D B (C ◃ E) = Σ' (methTy D B C) (methsTy D (wk B) E)

------------------------------------------------------------------------
-- the three commute with renaming.  ⚠ THESE ARE LOAD-BEARING: they are
-- what say every Π/Σ body in the chains is a WEAKENING, which is what the
-- non-dependent rules below require.
------------------------------------------------------------------------

payTy-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) (D : Desc) (C : DCon) →
            renTy ρ (payTy D C) ≡ payTy D C
payTy-ren ρ D dι       = refl
payTy-ren ρ D (dρ C)   = cong (Σ' (Mu D)) (payTy-ren (extR ρ) D C)
payTy-ren ρ D (dκ A C) =
  cong₂ Σ' (εwk-ren ρ A) (payTy-ren (extR ρ) D C)

methTy-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) (D : Desc) (B : RTy Γ) (C : DCon) →
             renTy ρ (methTy D B C) ≡ methTy D (renTy ρ B) C
methTy-ren ρ D B dι       = refl
methTy-ren ρ D B (dρ C)   =
  cong (Π (Mu D))
    (cong₂ Π (wk-nat ρ B)
             (trans (methTy-ren (extR (extR ρ)) D (wk (wk B)) C)
                    (cong (λ z → methTy D z C)
                          (trans (wk-nat (extR ρ) (wk B))
                                 (cong wk (wk-nat ρ B))))))
methTy-ren ρ D B (dκ A C) =
  cong₂ Π (εwk-ren ρ A)
          (trans (methTy-ren (extR ρ) D (wk B) C)
                 (cong (λ z → methTy D z C) (wk-nat ρ B)))

methsTy-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) (D : Desc) (B : RTy Γ) (E : Desc) →
              renTy ρ (methsTy D B E) ≡ methsTy D (renTy ρ B) E
methsTy-ren ρ D B dnil    = refl
methsTy-ren ρ D B (C ◃ E) =
  cong₂ Σ' (methTy-ren ρ D B C)
           (trans (methsTy-ren (extR ρ) D (wk B) E)
                  (cong (λ z → methsTy D z E) (wk-nat ρ B)))

-- ★ the `dρ` method, RESHAPED so the non-dependent `⊢app` can consume it:
--   its body really is a WEAKENING, and this is the proof.
methTy-dρ : {Γ : Cx} (D : Desc) (B : RTy Γ) (C : DCon) →
            wk (Π B (methTy D (wk B) C))
              ≡ Π (wk B) (methTy D (wk (wk B)) C)
methTy-dρ D B C =
  cong (Π (wk B))
       (trans (methTy-ren (extR vs) D (wk B) C)
              (cong (λ z → methTy D z C) (wk-nat vs B)))

------------------------------------------------------------------------
-- the ι-rule's machinery, verbatim from the kernel
------------------------------------------------------------------------

lookupD : Desc → ℕ → DCon
lookupD dnil    _       = dι
lookupD (C ◃ D) zero    = C
lookupD (C ◃ D) (suc k) = lookupD D k

sel : {Γ : Cx} → ℕ → RTm Γ → RTm Γ
sel zero    ms = fst ms
sel (suc k) ms = sel k (snd ms)

fields : {Γ : Cx} → Desc → RTm Γ → DCon → RTm Γ → RTm Γ → RTm Γ
fields D ms dι       m p = m
fields D ms (dρ C)   m p =
  fields D ms C (app (app m (fst p)) (elim D ms (fst p))) (snd p)
fields D ms (dκ A C) m p = fields D ms C (app m (fst p)) (snd p)

------------------------------------------------------------------------
-- ★★ Q21 — THE FINDING, AND IT IS THE POINT OF THIS GATE.
--
-- `lookupD` is TOTAL: it answers `dι` off the end of a description, so
-- that `_⟶_` needs no `lookup D k ≡ just C` side condition.  That choice
-- is right for the reduction relation — but it does NOT come for free at
-- the typing layer, and the bill arrives here:
--
--   * `payTy D dι = Unit`, so `⊢con` with an OUT-OF-RANGE tag and payload
--     `unit` would be DERIVABLE;
--   * `elim D ms (con k unit)` then reduces (by ι) to `sel k ms`;
--   * but `sel k ms` for an out-of-range `k` bottoms out in `fst unit`,
--     which has no type.
--
--   ⇒ SUBJECT REDUCTION WOULD BE FALSE.  Not unprovable — false.
--
-- The fix is the one the ι-rule's own commit message promised: junk tags
-- reduce to junk, and `⊢con` is what rules them out.  So `⊢con` carries a
-- proof that the tag INDEXES A REAL CONSTRUCTOR.  The reduction relation
-- stays side-condition-free; the discipline lives entirely in typing.
------------------------------------------------------------------------

data _∈D_ : ℕ → Desc → Set where
  hereD  : {C : DCon} {E : Desc} → zero ∈D (C ◃ E)
  thereD : {k : ℕ} {C : DCon} {E : Desc} → k ∈D E → suc k ∈D (C ◃ E)

------------------------------------------------------------------------
-- typing.  ⚠ Π/Σ rules are the NON-DEPENDENT ones — see the header.
------------------------------------------------------------------------

data Ctx : Cx → Set where
  ◇   : Ctx ε
  _▹_ : {Γ : Cx} → Ctx Γ → RTy Γ → Ctx (Γ ∙)

data _⊢_∷_ : {Γ : Cx} → Ctx Γ → RTm Γ → RTy Γ → Set where
  ⊢unit : {Γ : Cx} {Θ : Ctx Γ} → Θ ⊢ unit ∷ Unit
  ⊢lam  : {Γ : Cx} {Θ : Ctx Γ} {A : RTy Γ} {B : RTy Γ} {t : RTm (Γ ∙)} →
          (Θ ▹ A) ⊢ t ∷ wk B → Θ ⊢ lam t ∷ Π A (wk B)
  ⊢app  : {Γ : Cx} {Θ : Ctx Γ} {A B : RTy Γ} {t u : RTm Γ} →
          Θ ⊢ t ∷ Π A (wk B) → Θ ⊢ u ∷ A → Θ ⊢ app t u ∷ B
  ⊢pair : {Γ : Cx} {Θ : Ctx Γ} {A B : RTy Γ} {a b : RTm Γ} →
          Θ ⊢ a ∷ A → Θ ⊢ b ∷ B → Θ ⊢ pair a b ∷ Σ' A (wk B)
  ⊢fst  : {Γ : Cx} {Θ : Ctx Γ} {A B : RTy Γ} {p : RTm Γ} →
          Θ ⊢ p ∷ Σ' A (wk B) → Θ ⊢ fst p ∷ A
  ⊢snd  : {Γ : Cx} {Θ : Ctx Γ} {A B : RTy Γ} {p : RTm Γ} →
          Θ ⊢ p ∷ Σ' A (wk B) → Θ ⊢ snd p ∷ B
  -- ★★ THE TWO NEW RULES.
  ⊢con  : {Γ : Cx} {Θ : Ctx Γ} {D : Desc} {k : ℕ} {p : RTm Γ} →
          k ∈D D →                              -- ⚠ Q21: the tag is real
          Θ ⊢ p ∷ payTy D (lookupD D k) →
          Θ ⊢ con k p ∷ Mu D
  ⊢elim : {Γ : Cx} {Θ : Ctx Γ} {D : Desc} {B : RTy Γ} {ms t : RTm Γ} →
          Θ ⊢ ms ∷ methsTy D B D →
          Θ ⊢ t ∷ Mu D →
          Θ ⊢ elim D ms t ∷ B

------------------------------------------------------------------------
-- ★★ Q19 — `sel` navigates the method tuple, AT the right type.
--
-- ⚠ the `k ∈D E` premise is exactly what makes the `dnil` case
-- impossible.  Without it the lemma is FALSE (see Q21).
------------------------------------------------------------------------

sel-ty : {Γ : Cx} {Θ : Ctx Γ} (D : Desc) (B : RTy Γ) (E : Desc)
         (k : ℕ) (ms : RTm Γ) → k ∈D E →
         Θ ⊢ ms ∷ methsTy D B E →
         Θ ⊢ sel k ms ∷ methTy D B (lookupD E k)
sel-ty D B (C ◃ E) zero ms hereD hms =
  ⊢fst (subst (λ z → _ ⊢ ms ∷ Σ' (methTy D B C) z)
              (sym (methsTy-ren vs D B E))
              hms)
sel-ty D B (C ◃ E) (suc k) ms (thereD i) hms =
  sel-ty D B E k (snd ms) i
    (⊢snd (subst (λ z → _ ⊢ ms ∷ Σ' (methTy D B C) z)
                 (sym (methsTy-ren vs D B E))
                 hms))

------------------------------------------------------------------------
-- ★★★ Q20 — THE GATE.  `fields` against a well-typed method and payload.
--
-- This IS subject reduction for ι: the ι-rule's right-hand side is
-- `fields D ms (lookupD D k) (sel k ms) p`, so
--
--     ⊢elim  gives  ms ∷ methsTy D B D  and  con k p ∷ Mu D
--     ⊢con   gives  k ∈D D  and  p ∷ payTy D (lookupD D k)
--     sel-ty gives  sel k ms ∷ methTy D B (lookupD D k)
--     fields-ty     ⇒  the reduct ∷ B
------------------------------------------------------------------------

fields-ty : {Γ : Cx} {Θ : Ctx Γ} (D : Desc) (B : RTy Γ) (ms : RTm Γ)
            (C : DCon) (m p : RTm Γ) →
            Θ ⊢ ms ∷ methsTy D B D →
            Θ ⊢ m ∷ methTy D B C →
            Θ ⊢ p ∷ payTy D C →
            Θ ⊢ fields D ms C m p ∷ B
fields-ty D B ms dι m p hms hm hp = hm
fields-ty D B ms (dρ C) m p hms hm hp =
  fields-ty D B ms C _ (snd p) hms
    (⊢app (⊢app hm' hfst) (⊢elim hms hfst))
    (⊢snd hp')
  where
    hp' : _ ⊢ p ∷ Σ' (Mu D) (wk (payTy D C))
    hp' = subst (λ z → _ ⊢ p ∷ Σ' (Mu D) z) (sym (payTy-ren vs D C)) hp

    hfst : _ ⊢ fst p ∷ Mu D
    hfst = ⊢fst hp'

    -- ⚠ `m`'s type must be READ as `Π (Mu D) (wk _)` before `⊢app` will
    --   take it — that is what `methTy-dρ` is for.  And the SECOND `⊢app`
    --   needs the inner body read as a weakening too (`methTy-ren`).
    hm' : _ ⊢ m ∷ Π (Mu D) (wk (Π B (wk (methTy D B C))))
    hm' = subst (λ z → _ ⊢ m ∷ Π (Mu D) z)
                (sym (trans (methTy-dρ D B C)
                            (cong (Π (wk B))
                                  (cong (λ z → methTy D z C)
                                        (sym (wk-nat vs B))))))
                (subst (λ z → _ ⊢ m ∷ Π (Mu D) (Π (wk B) z))
                       (cong (λ z → methTy D z C) (wk-nat vs B))
                       hm)
fields-ty D B ms (dκ A C) m p hms hm hp =
  fields-ty D B ms C _ (snd p) hms (⊢app hm' hfst) (⊢snd hp')
  where
    hp' : _ ⊢ p ∷ Σ' (εwkTy A) (wk (payTy D C))
    hp' = subst (λ z → _ ⊢ p ∷ Σ' (εwkTy A) z) (sym (payTy-ren vs D C)) hp

    hfst : _ ⊢ fst p ∷ εwkTy A
    hfst = ⊢fst hp'

    hm' : _ ⊢ m ∷ Π (εwkTy A) (wk (methTy D B C))
    hm' = subst (λ z → _ ⊢ m ∷ Π (εwkTy A) z)
                (sym (methTy-ren vs D B C)) hm

------------------------------------------------------------------------
-- ★★★ AND THE GATE ITSELF: subject reduction for the ι-rule.
------------------------------------------------------------------------

sr-ι : {Γ : Cx} {Θ : Ctx Γ} (D : Desc) (B : RTy Γ) (ms : RTm Γ)
       (k : ℕ) (p : RTm Γ) →
       Θ ⊢ ms ∷ methsTy D B D →
       k ∈D D →
       Θ ⊢ p ∷ payTy D (lookupD D k) →
       Θ ⊢ fields D ms (lookupD D k) (sel k ms) p ∷ B
sr-ι D B ms k p hms i hp =
  fields-ty D B ms (lookupD D k) (sel k ms) p hms
            (sel-ty D B D k ms i hms) hp

------------------------------------------------------------------------
-- ★ NON-VACUITY: ℕ as a description, and the recursor over it.
--
--   NatD = dι            zero, no fields
--        ◃ dρ dι         suc, one recursive field
--        ◃ dnil
------------------------------------------------------------------------

NatD : Desc
NatD = dι ◃ dρ dι ◃ dnil

`zero : {Γ : Cx} → RTm Γ
`zero = con zero unit

`suc : {Γ : Cx} → RTm Γ → RTm Γ
`suc n = con (suc zero) (pair n unit)

⊢`zero : {Γ : Cx} {Θ : Ctx Γ} → Θ ⊢ `zero ∷ Mu NatD
⊢`zero = ⊢con hereD ⊢unit

⊢`suc : {Γ : Cx} {Θ : Ctx Γ} {n : RTm Γ} →
        Θ ⊢ n ∷ Mu NatD → Θ ⊢ `suc n ∷ Mu NatD
⊢`suc hn = ⊢con (thereD hereD) (⊢pair hn ⊢unit)

-- a concrete numeral, typed
⊢two : ◇ ⊢ `suc (`suc `zero) ∷ Mu NatD
⊢two = ⊢`suc (⊢`suc ⊢`zero)

-- ★★ and the ELIMINATOR fires, with subject reduction closing.  The
--    method tuple at motive `Unit`:  ⟨ unit , ⟨ λx.λih. unit , unit ⟩ ⟩
NatMs : {Γ : Cx} → RTm Γ
NatMs = pair unit (pair (lam (lam unit)) unit)

⊢NatMs : {Γ : Cx} {Θ : Ctx Γ} → Θ ⊢ NatMs ∷ methsTy NatD Unit NatD
⊢NatMs = ⊢pair ⊢unit (⊢pair (⊢lam (⊢lam ⊢unit)) ⊢unit)

⊢elim-two : ◇ ⊢ elim NatD NatMs (`suc (`suc `zero)) ∷ Unit
⊢elim-two = ⊢elim ⊢NatMs ⊢two

-- ★★★ THE GATE, INSTANTIATED: the ι-reduct of that elimination is still
--     at `Unit`.  This is `sr` at ι, on a real term.
⊢elim-two-reduct :
  ◇ ⊢ fields NatD NatMs (lookupD NatD (suc zero))
             (sel (suc zero) NatMs) (pair (`suc `zero) unit) ∷ Unit
⊢elim-two-reduct =
  sr-ι NatD Unit NatMs (suc zero) (pair (`suc `zero) unit)
       ⊢NatMs (thereD hereD) (⊢pair (⊢`suc ⊢`zero) ⊢unit)
