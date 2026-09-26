------------------------------------------------------------------------
-- OCP-0009 · G2 — CODE CANONICITY, CLOSED PROGRESS, and ★ CONSISTENCY
--                 of the full W2/W2b kernel.
--
-- The W2b done-when, delivered as a PROGRESS induction over closed
-- typed terms (structural on the term, generation lemmas supplying
-- the typing data, `usplit` supplying the code-level Boolean split):
--
--   ★ `usplit`  — a closed code of type `U` is pw-able, permanently
--     stable, or steps (CODE CANONICITY: `pw? ∨ stkC?` on normal
--     forms).
--   ★ `prog`    — a closed typed term is CANONICAL (lam / pair /
--     code-former / hrefl) or steps.  There is NO canonical `tr`:
--     the tr-case of the induction always produces a step — the
--     three W2b rules were built to make exactly this true.
--   ★ `trProgress`  — closed well-typed `tr`s ALWAYS step.
--   ★ `pathCanon`   — a closed NORMAL path at a `Hom` type is an
--     `hrefl` or a lambda.
--   ★★ `consistency` — `◇ ⊢ t ∷ base → ⊥`.  `base` has no
--     introduction rule; `wnorm` (the fundamental theorem) yields a
--     closed normal inhabitant, and every canonical shape's type
--     clashes with `base` by confluence.  The full directed kernel —
--     Π, Σ, Tarski-U, Hom with computing Hom-U/Hom-Π, hrefl with the
--     pointwise unfold, tr at both motives with J/taut/pointwise —
--     is CONSISTENT.
--
-- ★★ LEVITATION: the clash toolkit is ONE lemma, not a matrix.  Every
--   canonical form but `hrefl` has an INERT-headed type (`canTy`), inert
--   heads survive reduction (`inert-conv`), so at an inert type a
--   canonical inhabitant is one of that head's own introduction forms
--   (`canAt`, indexed by the head — coverage refutes the rest).  A new
--   former costs one `Canon`/`CanOf` row, not a row per consumer.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Canonicity where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_; _×_; ⊥; ⊥-elim
        ; _⊎_; inj₁; inj₂; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom; Id; Unit; Nat; IMu; Desc; DIh; Fin
        ; RTm; var; lam; app; pair; fst; snd; absurd; ordtr
        ; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap; ⌜Id⌝; idrefl; jsub
        ; unit; nzero; nsuc; natrec; ⌜Nat⌝; ⌜Unit⌝
        ; con; ielim; ⌜IMu⌝; ⌜Fin⌝; dι; dσ; dρ; dpay; dih; fzero; fsuc; fcase; fcase0; psplit
        ; Ren; renTm; renTy; Sub; subTm; subTy
        ; renTm-subTm; subTm-id
        ; subTy-renTy; subTy-cong; subTy-id )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; pw?; stkC?; stkA?; flat→stk; pw?-ren; occTm; subTm-occ
        ; NoNatC; NoNatHd; nonatc→hd; nonatc-sub; stkC?→stkA?; stkC?→hd )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.Confluence using ( ⟶-ren; confluent; ⟶*-trans; church-rosser )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( ≅ᵀ-sub )
open import DirectedHoTT.Metatheory.Injectivity
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; church-rosserᵀ; red→≅ᵀ
        ; Π-reduct; ΠRed; mkΠRed; Id-reduct; Fin-inj )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( gen-lam; gen-app; gen-absurd; gen-pair; gen-fst; gen-snd; gen-ap
        ; gen-⌜Id⌝; gen-idrefl; gen-jsub; gen-nsuc; gen-natrec; gen-ordtr
        ; gen-var; gen-hrefl; gen-⌜Π⌝; gen-⌜Σ⌝; gen-⌜Hom⌝
        ; gen-tr; TrGen; tgC; tgU; TrInv; mkTrInv; TrInvU; mkTrInvU
        ; StkAmb; st-el; st-hom; stamb-red
        ; HomΠShape; hsΠ; hsH; hsUnit; hsBase; hom-shape; hom-shapeN
        ; NoNat; nn-base; nn-U; nn-Unit; nn-El; nn-Π; nn-Σ; nn-Hom; nn-Id
        ; homAmb→; ≅ᵀ-Homᵀ; ⊢[]; sr*; nonathd-red
        ; gen-con; gen-ielim; gen-⌜IMu⌝; gen-dι; gen-dσ; gen-dρ; gen-dpay; gen-dih
        ; gen-fsuc; gen-fcase; gen-fcase0; gen-psplit )
open import DirectedHoTT.Metatheory.LogicalRelation
  using ( base-nf; Unit-nf; Nat-nf; IsNormal; WN; mkWN )
open import DirectedHoTT.Metatheory.Fundamental using ( wnorm )
open import DirectedHoTT.Algorithm.DecideConversion using ( red→≅ )

------------------------------------------------------------------------
-- 0. INERT HEADS.  A type whose head no type-level rule rewrites keeps
--    it along every reduction, so two convertible inert types share it
--    (Church–Rosser).  This one fact replaces the old pairwise clash
--    matrix: every canonical form but `hrefl` has an inert-headed type
--    (`canTy`), and a consumer at an inert type sees only the canonical
--    forms of ITS head (`canAt`) — Agda's coverage does the rest.
------------------------------------------------------------------------

noVar : Var ε → ⊥
noVar ()

data Hd : Set where
  hbase hU hΠ hΣ hUnit hNat hId hIMu hDesc hFin : Hd

data Inert {Γ : Cx} : RTy Γ → Hd → Set where
  in-base : Inert base hbase
  in-U    : Inert U hU
  in-Π    : {F : RTy Γ} {G : RTy (Γ ∙)} → Inert (Π F G) hΠ
  in-Σ    : {F : RTy Γ} {G : RTy (Γ ∙)} → Inert (Σ' F G) hΣ
  in-Unit : Inert Unit hUnit
  in-Nat  : Inert Nat hNat
  in-Id   : {A : RTy Γ} {a b : RTm Γ} → Inert (Id A a b) hId
  in-IMu  : {I D i : RTm Γ} → Inert (IMu I D i) hIMu
  in-Desc : {I : RTm Γ} → Inert (Desc I) hDesc
  in-Fin  : {n : ℕ} → Inert (Fin n) hFin

inert-red : {Γ : Cx} {A B : RTy Γ} {h : Hd} → Inert A h → A ⟶ᵀ B → Inert B h
inert-red in-base ()
inert-red in-U    ()
inert-red in-Unit ()
inert-red in-Nat  ()
inert-red in-Fin  ()
inert-red in-Π (ξ-Πˡ _) = in-Π
inert-red in-Π (ξ-Πʳ _) = in-Π
inert-red in-Σ (ξ-Σˡ _) = in-Σ
inert-red in-Σ (ξ-Σʳ _) = in-Σ
inert-red in-Id (ξ-Idᵀ _) = in-Id
inert-red in-Id (ξ-Idˡ _) = in-Id
inert-red in-Id (ξ-Idʳ _) = in-Id
inert-red in-IMu (ξ-IMuᴵ _) = in-IMu
inert-red in-IMu (ξ-IMuᴰ _) = in-IMu
inert-red in-IMu (ξ-IMuⁱ _) = in-IMu
inert-red in-Desc (ξ-Desc _) = in-Desc

inert-red* : {Γ : Cx} {A B : RTy Γ} {h : Hd} → Inert A h → A ⟶ᵀ* B → Inert B h
inert-red* i doneᵀ       = i
inert-red* i (stepᵀ r q) = inert-red* (inert-red i r) q

inert-uniq : {Γ : Cx} {A : RTy Γ} {h h' : Hd} → Inert A h → Inert A h' → h ≡ h'
inert-uniq in-base in-base = refl
inert-uniq in-U    in-U    = refl
inert-uniq in-Π    in-Π    = refl
inert-uniq in-Σ    in-Σ    = refl
inert-uniq in-Unit in-Unit = refl
inert-uniq in-Nat  in-Nat  = refl
inert-uniq in-Id   in-Id   = refl
inert-uniq in-IMu  in-IMu  = refl
inert-uniq in-Desc in-Desc = refl
inert-uniq in-Fin  in-Fin  = refl

-- ★ THE clash lemma.
inert-conv : {Γ : Cx} {A B : RTy Γ} {h h' : Hd} → A ≅ᵀ B → Inert A h → Inert B h' → h ≡ h'
inert-conv c iA iB with church-rosserᵀ c
... | W , (aW , bW) = inert-uniq (inert-red* iA aW) (inert-red* iB bW)

-- a `Hom` computes (`Hom-U`, `Hom-Π`, the order rules), so it is not
--   inert — but the heads it can reach are exactly these three.
data HomHd : Hd → Set where
  hh-Π    : HomHd hΠ
  hh-Unit : HomHd hUnit
  hh-base : HomHd hbase

homShape-inert : {Γ : Cx} {W : RTy Γ} {h : Hd} → HomΠShape W → Inert W h → HomHd h
homShape-inert hsΠ    in-Π    = hh-Π
homShape-inert hsUnit in-Unit = hh-Unit
homShape-inert hsBase in-base = hh-base

hom-inert : {Γ : Cx} {A B : RTy Γ} {t u : RTm Γ} {h : Hd} →
            Hom A t u ≅ᵀ B → Inert B h → HomHd h
hom-inert cv iB with church-rosserᵀ cv
... | W , (hW , bW) = homShape-inert (hom-shape hW) (inert-red* iB bW)

-- `El` decodes to an inert type or a `Hom`; neither is `U`, and only
--   ⌜Nat⌝'s decode is `Nat`.
elnotNat : {Γ : Cx} {t : RTm Γ} → NoNatHd t → El t ⟶ᵀ* Nat → ⊥
elnotNat _ (stepᵀ El-⌜base⌝ rest) with inert-red* in-base rest
... | ()
elnotNat _ (stepᵀ (El-⌜Π⌝ _ _) rest) with inert-red* in-Π rest
... | ()
elnotNat _ (stepᵀ (El-⌜Σ⌝ _ _) rest) with inert-red* in-Σ rest
... | ()
elnotNat _ (stepᵀ (El-⌜Hom⌝ _ _ _) rest) with hom-shape rest
... | ()
elnotNat _ (stepᵀ (El-⌜Id⌝ _ _ _) rest) with inert-red* in-Id rest
... | ()
elnotNat _ (stepᵀ El-⌜Unit⌝ rest) with inert-red* in-Unit rest
... | ()
elnotNat _ (stepᵀ El-⌜IMu⌝ rest) with inert-red* in-IMu rest
... | ()
elnotNat _ (stepᵀ El-⌜Fin⌝ rest) with inert-red* in-Fin rest
... | ()
-- ★ THE excluded case, and the only one.
elnotNat () (stepᵀ El-⌜Nat⌝ rest)
elnotNat nc (stepᵀ (ξ-El r) rest) = elnotNat (nonathd-red nc r) rest

elNat⊥ : {Γ : Cx} {c : RTm Γ} → NoNatHd c → El c ≅ᵀ Nat → ⊥
elNat⊥ nc cv with church-rosserᵀ cv
... | E , (eE , nE) with Nat-nf nE
...   | refl = elnotNat nc eE

-- …hence a well-typed `tr`'s ambient is convertible to a Nat-FREE
-- decode.  ⚠ It is NOT `NoNat A` any more: `A` itself may be `El c` for
-- a code we know nothing about (only that it CONVERTS to the motive
-- code), and `NoNat`'s `nn-El` needs a syntactic head.  What survives —
-- and what the one consumer actually uses — is the conversion plus the
-- head fact about the STRENGTHENED motive code, which `⊢tr`'s `NoNatC`
-- premise supplies.
tr-amb-conv : {A : RTy ⌊ ◇ ⌋} {cM : RTm (⌊ ◇ ⌋ ∙)} (tI : RTm ε) →
              NoNatC cM → ((◇ ▹ A) ⊢ var vz ∷ El cM) →
              Σ (RTm ε) (λ c → (NoNatHd c) × (El c ≅ᵀ A))
tr-amb-conv {A = A} {cM = cM} tI ncM dvM =
  subTm (single tI) cM
  , ( nonatc→hd (nonatc-sub (single tI) ncM)
    , cvA )
  where
  bridge : Σ (RTy (ε ∙)) (λ A' → ((◇ ▹ A) ∋ vz ∷ A') × (El cM ≅ᵀ A')) →
           El cM ≅ᵀ renTy vs A
  bridge (_ , (here , cv)) = cv

  eqA : subTy (single tI) (renTy vs A) ≡ A
  eqA = trans (subTy-renTy A) (trans (subTy-cong (λ x → refl) A) (subTy-id A))

  cvA : El (subTm (single tI) cM) ≅ᵀ A
  cvA = subst (λ z → El (subTm (single tI) cM) ≅ᵀ z) eqA
              (≅ᵀ-sub (single tI) (bridge (gen-var dvM)))


elnotU : {Γ : Cx} {t : RTm Γ} → El t ⟶ᵀ* U → ⊥
elnotU (stepᵀ El-⌜base⌝ rest) with inert-red* in-base rest
... | ()
elnotU (stepᵀ (El-⌜Π⌝ _ _) rest) with inert-red* in-Π rest
... | ()
elnotU (stepᵀ (El-⌜Σ⌝ _ _) rest) with inert-red* in-Σ rest
... | ()
elnotU (stepᵀ (El-⌜Hom⌝ _ _ _) rest) with hom-shape rest
... | ()
elnotU (stepᵀ (El-⌜Id⌝ _ _ _) rest) with inert-red* in-Id rest
... | ()
elnotU (stepᵀ El-⌜Nat⌝ rest) with inert-red* in-Nat rest
... | ()
elnotU (stepᵀ El-⌜Unit⌝ rest) with inert-red* in-Unit rest
... | ()
elnotU (stepᵀ El-⌜IMu⌝ rest) with inert-red* in-IMu rest
... | ()
elnotU (stepᵀ El-⌜Fin⌝ rest) with inert-red* in-Fin rest
... | ()
elnotU (stepᵀ (ξ-El r) rest) = elnotU rest

------------------------------------------------------------------------
-- 1. The HOM clashes — a `Hom` is not inert, so these stay special:
--    which of its three reachable heads a given hom can reach depends on
--    its ambient (`NoNat`, a permanently stable code, the order).
------------------------------------------------------------------------

Hombase-clash : {Γ : Cx} {A : RTy Γ} {t u : RTm Γ} →
                NoNat A → Hom A t u ≅ᵀ base → ⊥
Hombase-clash nn cv with church-rosserᵀ cv
... | E , (hE , bE) with base-nf bE
...   | refl with hom-shapeN nn hE
...     | ()

HomUnit-clash : {Γ : Cx} {A : RTy Γ} {t u : RTm Γ} →
                NoNat A → Hom A t u ≅ᵀ Unit → ⊥
HomUnit-clash nn cv with church-rosserᵀ cv
... | E , (hE , uE) with Unit-nf uE
...   | refl with hom-shapeN nn hE
...     | ()

-- stable-vs-unfolding clashes.
stamb-star : {Γ : Cx} {A A' : RTy Γ} → StkAmb A → A ⟶ᵀ* A' → StkAmb A'
stamb-star sh doneᵀ        = sh
stamb-star sh (stepᵀ r q) = stamb-star (stamb-red sh r) q

-- a Hom over a PERMANENTLY-STABLE code's decode never joins a Π-form.
HomStkΠ-clash : {Γ : Cx} {c t u : RTm Γ} {F : RTy Γ} {G : RTy (Γ ∙)} →
                stkC? c ≡ true → Hom (El c) t u ≅ᵀ Π F G → ⊥
HomStkΠ-clash {c = c} k cv with church-rosserᵀ cv
... | E , (hE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _
        with stamb-star (st-hom (st-el {c = c} (stkC?→stkA? c k))) hE
...     | ()

-- ...nor a `Hom U`-form (`U` is not a stable ambient).
homU-inv : {Γ : Cx} {t u : RTm Γ} {C : RTy Γ} → Hom U t u ⟶ᵀ* C →
           (Σ (RTm Γ) (λ t' → Σ (RTm Γ) (λ u' → C ≡ Hom U t' u')))
           ⊎ (Σ (RTy Γ) (λ P → Σ (RTy (Γ ∙)) (λ Q → C ≡ Π P Q)))
homU-inv doneᵀ = inj₁ (_ , (_ , refl))
homU-inv (stepᵀ (ξ-Homᵀ ()) rest)
homU-inv (stepᵀ (ξ-Homˡ r) rest) = homU-inv rest
homU-inv (stepᵀ (ξ-Homʳ r) rest) = homU-inv rest
homU-inv (stepᵀ (Hom-U c d) rest) with Π-reduct rest
... | mkΠRed P Q eq _ _ = inj₂ (P , (Q , eq))

HomStkU-clash : {Γ : Cx} {c s₀ s₁ tU uU : RTm Γ} →
                stkC? c ≡ true →
                Hom U tU uU ≅ᵀ Hom (El c) s₀ s₁ → ⊥
HomStkU-clash {c = c} k cv with church-rosserᵀ cv
... | E , (uL , sR) with homU-inv uL
... | inj₁ (t' , (u' , refl)) with stamb-star (st-hom (st-el {c = c} (stkC?→stkA? c k))) sR
...   | st-hom ()
HomStkU-clash {c = c} k cv | E , (uL , sR) | inj₂ (P , (Q , refl))
  with stamb-star (st-hom (st-el {c = c} (stkC?→stkA? c k))) sR
... | ()


------------------------------------------------------------------------
-- ★★ SpikeNatJ: the reducts of a hom over the ORDERED type.
--
-- After the `stkA?` split the only code that is neither `pw?` nor
-- `stkC?` is the LITERAL ⌜Nat⌝ (a ⌜Hom⌝ over it is J-able), so every
-- `u-nat` consumer faces exactly `Hom (El ⌜Nat⌝) s s`.  Its ambient
-- decodes to the INERT `Nat`, whence the order rules take the whole
-- type to `Unit` or `base` (both inert) or peel it back to another
-- `Nat`-ambient hom.  The ambient is never `U` or `Π`, so `Hom-U` and
-- `Hom-Π` never fire — Π is UNREACHABLE, which is what refutes J at a
-- bare ⌜Nat⌝ everywhere.
------------------------------------------------------------------------

data NatHomShape {Γ : Cx} : RTy Γ → Set where
  nhs-el   : {a b : RTm Γ} → NatHomShape (Hom (El (⌜Nat⌝ {Γ})) a b)
  nhs-hom  : {a b : RTm Γ} → NatHomShape (Hom (Nat {Γ}) a b)
  nhs-Unit : NatHomShape (Unit {Γ})
  nhs-base : NatHomShape (base {Γ})

nathom-red : {Γ : Cx} {A A' : RTy Γ} → NatHomShape A → A ⟶ᵀ A' → NatHomShape A'
nathom-red nhs-el (ξ-Homᵀ El-⌜Nat⌝) = nhs-hom
nathom-red nhs-el (ξ-Homᵀ (ξ-El ()))
nathom-red nhs-el (ξ-Homˡ _) = nhs-el
nathom-red nhs-el (ξ-Homʳ _) = nhs-el
nathom-red nhs-hom (ξ-Homᵀ ())
nathom-red nhs-hom (ξ-Homˡ _) = nhs-hom
nathom-red nhs-hom (ξ-Homʳ _) = nhs-hom
nathom-red nhs-hom (Hom-Nat-z _)    = nhs-Unit
nathom-red nhs-hom (Hom-Nat-sz _)   = nhs-base
nathom-red nhs-hom (Hom-Nat-ss _ _) = nhs-hom
nathom-red nhs-Unit ()
nathom-red nhs-base ()

nathom-star : {Γ : Cx} {A A' : RTy Γ} → NatHomShape A → A ⟶ᵀ* A' → NatHomShape A'
nathom-star h doneᵀ       = h
nathom-star h (stepᵀ r q) = nathom-star (nathom-red h r) q

-- …so an order-hom never joins a Π-form.
HomNatΠ-clash : {Γ : Cx} {t u : RTm Γ} {F : RTy Γ} {G : RTy (Γ ∙)} →
                Hom (El (⌜Nat⌝ {Γ})) t u ≅ᵀ Π F G → ⊥
HomNatΠ-clash cv with church-rosserᵀ cv
... | E , (hE , πE) with Π-reduct πE
...   | mkΠRed _ _ refl _ _ with nathom-star nhs-el hE
...     | ()

-- …and its ambient is never a `NoNat` decode: the joins are `Unit`,
-- `base`, or a `Nat`-ambient hom, and `NoNat` refutes the last while
-- the clashes refute the first two.
HomNatNoNat-clash : {Γ : Cx} {A : RTy Γ} {s t u : RTm Γ} → NoNat A →
                    Hom (El (⌜Nat⌝ {Γ})) s s ≅ᵀ Hom A t u → ⊥
HomNatNoNat-clash nn cv with church-rosserᵀ cv
... | E , (nE , aE) with nathom-star nhs-el nE
...   | nhs-Unit = HomUnit-clash nn (red→≅ᵀ aE)
...   | nhs-base = Hombase-clash nn (red→≅ᵀ aE)
-- the join is still an `El ⌜Nat⌝`-ambient hom: `NoNat` pushed forward
-- would need `NoNatHd ⌜Nat⌝`, which is empty.
...   | nhs-el   with homAmb→ aE nn
...     | nn-El ()
HomNatNoNat-clash nn cv | E , (nE , aE) | nhs-hom with homAmb→ aE nn
... | ()


------------------------------------------------------------------------
-- ★★ A DIAGONAL HOM NEVER REACHES `base`.
--
-- `base` is produced by EXACTLY ONE rule — `Hom-Nat-sz`, at
-- `Hom Nat (nsuc m) nzero` — so reaching it forces the two endpoints to
-- be joinable with `nsuc m` and `nzero` respectively.  For a DIAGONAL
-- hom `Hom X s s` the endpoints start joinable (`s` with itself), and
-- the invariant survives every step: the congruences extend the join by
-- confluence, and `Hom-Nat-ss` peels both successors off a common
-- reduct.  At `Hom-Nat-sz` it collapses: one term cannot reduce to both
-- `nsuc m` and `nzero`.
--
-- This is what `canBase⊥`'s `can-hrefl` case needs.  `Hombase-clash`
-- cannot serve it: that wants `NoNat A`, and the hrefl's own code is
-- ARBITRARY — `El c` for a `c` we know nothing about.  The diagonality
-- is the fact that was there all along.
------------------------------------------------------------------------

nsuc-inj : {Γ : Cx} {a b : RTm Γ} → nsuc a ≡ nsuc b → a ≡ b
nsuc-inj refl = refl

nzero-nf : {Γ : Cx} {w : RTm Γ} → nzero {Γ} ⟶* w → w ≡ nzero
nzero-nf done       = refl
nzero-nf (step () _)

nsuc-red* : {Γ : Cx} {m w : RTm Γ} → nsuc m ⟶* w →
            Σ (RTm Γ) (λ m' → (w ≡ nsuc m') × (m ⟶* m'))
nsuc-red* {m = m} done = m , (refl , done)
nsuc-red* (step (ξ-nsuc r) rest) with nsuc-red* rest
... | m' , (eq , rm) = m' , (eq , step r rm)

Join : {Γ : Cx} → RTm Γ → RTm Γ → Set
Join {Γ} t u = Σ (RTm Γ) (λ w → (t ⟶* w) × (u ⟶* w))

diagbase⊥ : {Γ : Cx} {X : RTy Γ} {t u : RTm Γ} →
            Join t u → Hom X t u ⟶ᵀ* base → ⊥
diagbase⊥ j (stepᵀ (ξ-Homᵀ r) rest) = diagbase⊥ j rest
diagbase⊥ (w , (rt , ru)) (stepᵀ (ξ-Homˡ r) rest)
  with confluent (step r done) rt
... | w' , (rw , rt') = diagbase⊥ (w' , (rw , ⟶*-trans ru rt')) rest
diagbase⊥ (w , (rt , ru)) (stepᵀ (ξ-Homʳ r) rest)
  with confluent (step r done) ru
... | w' , (rw , ru') = diagbase⊥ (w' , (⟶*-trans rt ru' , rw)) rest
diagbase⊥ j (stepᵀ (Hom-U _ _) rest) with Π-reduct rest
... | mkΠRed _ _ () _ _
diagbase⊥ j (stepᵀ (Hom-Π _ _ _ _) rest) with Π-reduct rest
... | mkΠRed _ _ () _ _
diagbase⊥ j (stepᵀ (Hom-Nat-z _) rest) with Unit-nf rest
... | ()
-- ★ THE COLLAPSE: `nsuc m` and `nzero` are joinable — impossible.
diagbase⊥ (w , (rt , ru)) (stepᵀ (Hom-Nat-sz m) rest) with nzero-nf ru
... | refl with nsuc-red* rt
...   | _ , (() , _)
-- ★ the peel: a common reduct of `nsuc m` and `nsuc n` is `nsuc k`,
-- so the peeled endpoints are joinable at `k`.
diagbase⊥ (w , (rt , ru)) (stepᵀ (Hom-Nat-ss m n) rest)
  with nsuc-red* rt | nsuc-red* ru
... | k , (refl , rm) | k' , (eq , rn) with nsuc-inj eq
...   | refl = diagbase⊥ (k , (rm , rn)) rest

-- …nor a `Hom U`-form: `U` is neither `El ⌜Nat⌝` nor `Nat`, so no
-- reduct of an order-hom is one.
HomNatU-clash : {Γ : Cx} {s₀ s₁ tU uU : RTm Γ} →
                Hom U tU uU ≅ᵀ Hom (El (⌜Nat⌝ {Γ})) s₀ s₁ → ⊥
HomNatU-clash cv with church-rosserᵀ cv
... | E , (uL , sR) with homU-inv uL
... | inj₁ (t' , (u' , refl)) with nathom-star nhs-el sR
...   | ()
HomNatU-clash cv | E , (uL , sR) | inj₂ (P , (Q , refl))
  with nathom-star nhs-el sR
... | ()

------------------------------------------------------------------------
-- 2. TERM SIZE and bounded recursion — the tr-case must analyze the
--    STRENGTHENED motive-code (`subTm (single t) cM`), which is not a
--    structural subterm but has exactly `cM`'s size.  We recurse on a
--    Nat bound, structurally.
------------------------------------------------------------------------

-- ★ WF stage A: the OBJECT language now has its own `Nat`, so the
-- meta-level bound is renamed.

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-refl : {n : ℕ} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : {l m n : ℕ} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-suc : {a b : ℕ} → a ≤ b → a ≤ suc b
≤-suc z≤n     = z≤n
≤-suc (s≤s p) = s≤s (≤-suc p)

un≤ : {a b : ℕ} → suc a ≤ suc b → a ≤ b
un≤ (s≤s p) = p

-- summands EXPLICIT (the `+`-inversion trap: implicit summands leak
-- metas through `with`-abstractions).
≤+ˡ : (a b : ℕ) → a ≤ a + b
≤+ˡ zero    b = z≤n
≤+ˡ (suc a) b = s≤s (≤+ˡ a b)

≤+ʳ : (a b : ℕ) → b ≤ a + b
≤+ʳ zero    b = ≤-refl
≤+ʳ (suc a) b = ≤-suc (≤+ʳ a b)

-- `sz` is suc-headed by its single top clause, so `sz t ≤ zero` is
-- judgmentally absurd even for neutral `t`.
szb : {Γ : Cx} → RTm Γ → ℕ
sz  : {Γ : Cx} → RTm Γ → ℕ
sz t = suc (szb t)
szb (var x)        = zero
szb (lam t)        = sz t
szb (absurd c e)   = sz c + sz e
szb (app f a)      = sz f + sz a
szb (pair a b)     = sz a + sz b
szb (fst p)        = sz p
szb (snd p)        = sz p
szb ⌜base⌝         = zero
szb ⌜Nat⌝          = zero
szb ⌜Unit⌝         = zero
szb (⌜Π⌝ c d)      = sz c + sz d
szb (⌜Σ⌝ c d)      = sz c + sz d
szb (⌜Hom⌝ c a b)  = sz c + sz a + sz b
szb (hrefl c t)    = sz c + sz t
szb (tr d p e)     = sz d + sz p + sz e
szb (ap c b p)     = sz c + sz b + sz p
szb (⌜Id⌝ c a b)   = sz c + sz a + sz b
szb (idrefl c t)   = sz c + sz t
szb (jsub d p e)   = sz d + sz p + sz e
szb unit           = zero
szb nzero          = zero
szb (nsuc n)       = sz n
szb (ordtr a t u p q) = sz a + sz t + sz u + sz p + sz q
szb (natrec z w n) = sz z + sz w + sz n
szb (con p)        = sz p
szb (ielim D i e t) = sz D + sz i + sz e + sz t
szb (⌜IMu⌝ I D i)  = sz I + sz D + sz i
szb (⌜Fin⌝ n)      = zero
szb dι             = zero
szb (dσ S f)       = sz S + sz f
szb (dρ j C)       = sz j + sz C
szb (dpay I D C)   = sz I + sz D + sz C
szb (dih D e C p)  = sz D + sz e + sz C + sz p
szb fzero          = zero
szb (fsuc t)       = sz t
szb (fcase t a b)  = sz t + sz a + sz b
szb (fcase0 t)     = sz t
szb (psplit b q)   = sz b + sz q

szb-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) (t : RTm Γ) → szb (renTm ρ t) ≡ szb t
sz-ren  : {Γ Δ : Cx} (ρ : Ren Γ Δ) (t : RTm Γ) → sz (renTm ρ t) ≡ sz t
sz-ren ρ t = cong suc (szb-ren ρ t)
szb-ren ρ ⌜Nat⌝         = refl
szb-ren ρ ⌜Unit⌝        = refl
szb-ren ρ (var x)       = refl
szb-ren ρ (lam t)       = sz-ren _ t
szb-ren ρ (absurd c e)  = cong₂ _+_ (sz-ren ρ c) (sz-ren ρ e)
szb-ren ρ (app f a)     = cong₂ _+_ (sz-ren ρ f) (sz-ren ρ a)
szb-ren ρ (pair a b)    = cong₂ _+_ (sz-ren ρ a) (sz-ren ρ b)
szb-ren ρ (fst p)       = sz-ren ρ p
szb-ren ρ (snd p)       = sz-ren ρ p
szb-ren ρ ⌜base⌝        = refl
szb-ren ρ (⌜Π⌝ c d)     = cong₂ _+_ (sz-ren ρ c) (sz-ren _ d)
szb-ren ρ (⌜Σ⌝ c d)     = cong₂ _+_ (sz-ren ρ c) (sz-ren _ d)
szb-ren ρ (⌜Hom⌝ c a b) =
  cong₂ _+_ (cong₂ _+_ (sz-ren ρ c) (sz-ren ρ a)) (sz-ren ρ b)
szb-ren ρ (hrefl c t)   = cong₂ _+_ (sz-ren ρ c) (sz-ren ρ t)
szb-ren ρ (tr d p e)    =
  cong₂ _+_ (cong₂ _+_ (sz-ren _ d) (sz-ren ρ p)) (sz-ren ρ e)
szb-ren ρ (ap c b p)    =
  cong₂ _+_ (cong₂ _+_ (sz-ren ρ c) (sz-ren _ b)) (sz-ren ρ p)
szb-ren ρ (⌜Id⌝ c a b)  =
  cong₂ _+_ (cong₂ _+_ (sz-ren ρ c) (sz-ren ρ a)) (sz-ren ρ b)
szb-ren ρ (idrefl c t)  = cong₂ _+_ (sz-ren ρ c) (sz-ren ρ t)
szb-ren ρ (jsub d p e)  =
  cong₂ _+_ (cong₂ _+_ (sz-ren _ d) (sz-ren ρ p)) (sz-ren ρ e)
szb-ren ρ unit          = refl
szb-ren ρ nzero         = refl
szb-ren ρ (nsuc n)      = sz-ren ρ n
szb-ren ρ (natrec z w n) =
  cong₂ _+_ (cong₂ _+_ (sz-ren ρ z) (sz-ren _ w)) (sz-ren ρ n)
szb-ren ρ (con p)       = sz-ren ρ p
szb-ren ρ (ielim D i e t) =
  cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (sz-ren ρ D) (sz-ren ρ i)) (sz-ren ρ e)) (sz-ren ρ t)
szb-ren ρ (⌜IMu⌝ I D i) = cong₂ _+_ (cong₂ _+_ (sz-ren ρ I) (sz-ren ρ D)) (sz-ren ρ i)
szb-ren ρ (⌜Fin⌝ n)     = refl
szb-ren ρ dι            = refl
szb-ren ρ (dσ S f)      = cong₂ _+_ (sz-ren ρ S) (sz-ren ρ f)
szb-ren ρ (dρ j C)      = cong₂ _+_ (sz-ren ρ j) (sz-ren ρ C)
szb-ren ρ (dpay I D C) =
  cong₂ _+_ (cong₂ _+_ (sz-ren ρ I) (sz-ren ρ D)) (sz-ren ρ C)
szb-ren ρ (dih D e C p) =
  cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (sz-ren ρ D) (sz-ren ρ e)) (sz-ren ρ C)) (sz-ren ρ p)
szb-ren ρ fzero         = refl
szb-ren ρ (fsuc t)      = sz-ren ρ t
szb-ren ρ (fcase t a b) = cong₂ _+_ (cong₂ _+_ (sz-ren ρ t) (sz-ren ρ a)) (sz-ren _ b)
szb-ren ρ (fcase0 t)    = sz-ren ρ t
szb-ren ρ (psplit b q)  = cong₂ _+_ (sz-ren _ b) (sz-ren ρ q)
szb-ren ρ (ordtr a t u p q) =
  cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (sz-ren ρ a) (sz-ren ρ t))
                                  (sz-ren ρ u))
                       (sz-ren ρ p))
            (sz-ren ρ q)

------------------------------------------------------------------------
-- 3. CANONICAL SHAPES and the progress verdicts.  There is NO `tr`
--    (and no `var`, `app`, `fst`, `snd`, no eliminator) row in `Canon` —
--    the whole point of the induction is that those always step (or
--    clash).  `Canon` lists introduction forms and codes only.
------------------------------------------------------------------------

data Canon {Γ : Cx} : RTm Γ → Set where
  can-lam   : (s : RTm (Γ ∙))            → Canon (lam s)
  can-pair  : (a b : RTm Γ)              → Canon (pair a b)
  can-cb    :                              Canon ⌜base⌝
  can-cΠ    : (c : RTm Γ) (d : RTm (Γ ∙)) → Canon (⌜Π⌝ c d)
  can-cΣ    : (c : RTm Γ) (d : RTm (Γ ∙)) → Canon (⌜Σ⌝ c d)
  can-cH    : (c a b : RTm Γ)            → Canon (⌜Hom⌝ c a b)
  can-hrefl : (c s : RTm Γ)              → Canon (hrefl c s)
  can-cId   : (c a b : RTm Γ)            → Canon (⌜Id⌝ c a b)
  can-idrefl : (c s : RTm Γ)             → Canon (idrefl c s)
  can-cNat  :                              Canon (⌜Nat⌝ {Γ})
  can-cUnit :                              Canon (⌜Unit⌝ {Γ})
  can-unit  :                              Canon (unit {Γ})
  can-nzero :                              Canon (nzero {Γ})
  can-nsuc  : (n : RTm Γ)                → Canon (nsuc n)
  -- ★★ LEVITATION: the family's constructor, its code, the telescope
  --   formers and the tags are introduction forms / codes.
  can-con   : (p : RTm Γ)                → Canon (con p)
  can-cIMu  : (I D i : RTm Γ)            → Canon (⌜IMu⌝ I D i)
  can-cFin  : (n : ℕ)                    → Canon (⌜Fin⌝ {Γ} n)
  can-dι    :                              Canon (dι {Γ})
  can-dσ    : (S f : RTm Γ)              → Canon (dσ S f)
  can-dρ    : (j C : RTm Γ)              → Canon (dρ j C)
  can-fzero :                              Canon (fzero {Γ})
  can-fsuc  : (t : RTm Γ)                → Canon (fsuc t)

data Prog (t : RTm ε) : Set where
  prog-can  : Canon t → Prog t
  prog-step : {u : RTm ε} → t ⟶ u → Prog t

-- ★ the CODE verdict: pw-able, PERMANENTLY stable, ORDERED, or steps.
--
-- ★★ SpikeNatJ: the third arm covers exactly the LITERAL ⌜Nat⌝ — the
-- one closed normal code that is neither `pw?` nor `stkC?`.
data UProg (c : RTm ε) : Set where
  u-pw   : pw? c ≡ true   → UProg c
  u-stk  : stkC? c ≡ true → UProg c
  u-nat  : c ≡ ⌜Nat⌝      → UProg c
  u-step : {c' : RTm ε} → c ⟶ c' → UProg c

-- generation for the nullary intro forms and codes (local: nothing
--   upstream needs them).
gen-unit : {Γ : Ctx} {C : RTy ⌊ Γ ⌋} → Γ ⊢ unit ∷ C → C ≅ᵀ Unit
gen-unit ⊢unit      = crflᵀ
gen-unit (⊢conv d c) = ctrnᵀ (csymᵀ c) (gen-unit d)

gen-nzero : {Γ : Ctx} {C : RTy ⌊ Γ ⌋} → Γ ⊢ nzero ∷ C → C ≅ᵀ Nat
gen-nzero ⊢nzero      = crflᵀ
gen-nzero (⊢conv d c) = ctrnᵀ (csymᵀ c) (gen-nzero d)

gen-⌜base⌝ : {Γ : Ctx} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ⌜base⌝ ∷ C → C ≅ᵀ U
gen-⌜base⌝ ⊢⌜base⌝      = crflᵀ
gen-⌜base⌝ (⊢conv d c) = ctrnᵀ (csymᵀ c) (gen-⌜base⌝ d)

gen-⌜Nat⌝ : {Γ : Ctx} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ⌜Nat⌝ ∷ C → C ≅ᵀ U
gen-⌜Nat⌝ ⊢⌜Nat⌝       = crflᵀ
gen-⌜Nat⌝ (⊢conv d c) = ctrnᵀ (csymᵀ c) (gen-⌜Nat⌝ d)

gen-⌜Unit⌝ : {Γ : Ctx} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ⌜Unit⌝ ∷ C → C ≅ᵀ U
gen-⌜Unit⌝ ⊢⌜Unit⌝      = crflᵀ
gen-⌜Unit⌝ (⊢conv d c) = ctrnᵀ (csymᵀ c) (gen-⌜Unit⌝ d)

gen-⌜Fin⌝ : {Γ : Ctx} {n : ℕ} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ⌜Fin⌝ n ∷ C → C ≅ᵀ U
gen-⌜Fin⌝ ⊢⌜Fin⌝      = crflᵀ
gen-⌜Fin⌝ (⊢conv d c) = ctrnᵀ (csymᵀ c) (gen-⌜Fin⌝ d)

gen-fzero : {Γ : Ctx} {C : RTy ⌊ Γ ⌋} → Γ ⊢ fzero ∷ C → Σ ℕ (λ n → C ≅ᵀ Fin (suc n))
gen-fzero ⊢fzero      = _ , crflᵀ
gen-fzero (⊢conv d c) with gen-fzero d
... | n , c' = n , ctrnᵀ (csymᵀ c) c'

------------------------------------------------------------------------
-- 4. ★ THE CANONICAL VIEWS.  `canTy`: every canonical form but `hrefl`
--    has an inert-headed type.  `canAt`: at an inert type of head `h`,
--    a canonical inhabitant is one of `h`'s own introduction forms —
--    the index `h` makes every other form impossible by COVERAGE.
--    `homCan`: at a `Hom`, what the hom can reach (`hom-inert`).
------------------------------------------------------------------------

data CanOf {Γ : Cx} : Hd → RTm Γ → Set where
  co-lam    : (s : RTm (Γ ∙)) → CanOf hΠ (lam s)
  co-pair   : (a b : RTm Γ) → CanOf hΣ (pair a b)
  co-cb     : CanOf hU ⌜base⌝
  co-cΠ     : (c : RTm Γ) (d : RTm (Γ ∙)) → CanOf hU (⌜Π⌝ c d)
  co-cΣ     : (c : RTm Γ) (d : RTm (Γ ∙)) → CanOf hU (⌜Σ⌝ c d)
  co-cH     : (c a b : RTm Γ) → CanOf hU (⌜Hom⌝ c a b)
  co-cId    : (c a b : RTm Γ) → CanOf hU (⌜Id⌝ c a b)
  co-cNat   : CanOf hU ⌜Nat⌝
  co-cUnit  : CanOf hU ⌜Unit⌝
  co-cIMu   : (I D i : RTm Γ) → CanOf hU (⌜IMu⌝ I D i)
  co-cFin   : (n : ℕ) → CanOf hU (⌜Fin⌝ n)
  co-idrefl : (c s : RTm Γ) → CanOf hId (idrefl c s)
  co-unit   : CanOf hUnit unit
  co-nzero  : CanOf hNat nzero
  co-nsuc   : (n : RTm Γ) → CanOf hNat (nsuc n)
  co-con    : (p : RTm Γ) → CanOf hIMu (con p)
  co-dι     : CanOf hDesc (dι {Γ})
  co-dσ     : (S f : RTm Γ) → CanOf hDesc (dσ S f)
  co-dρ     : (j C : RTm Γ) → CanOf hDesc (dρ j C)
  co-fzero  : CanOf hFin fzero
  co-fsuc   : (t : RTm Γ) → CanOf hFin (fsuc t)

-- `base` has no introduction form.
noBase : {Γ : Cx} {t : RTm Γ} → CanOf hbase t → ⊥
noBase ()

IsHrefl : {Γ : Cx} → RTm Γ → Set
IsHrefl {Γ} t = Σ (RTm Γ) (λ c → Σ (RTm Γ) (λ s → t ≡ hrefl c s))

InertTy : {Γ : Ctx} → RTm ⌊ Γ ⌋ → RTy ⌊ Γ ⌋ → Set
InertTy {Γ} t T = Σ Hd (λ h → CanOf h t × Σ (RTy ⌊ Γ ⌋) (λ A → (T ≅ᵀ A) × Inert A h))

HreflTy : {Γ : Ctx} → RTm ⌊ Γ ⌋ → RTy ⌊ Γ ⌋ → Set
HreflTy {Γ} t T = IsHrefl t × Σ (RTy ⌊ Γ ⌋) (λ A → Σ (RTm ⌊ Γ ⌋) (λ a → Σ (RTm ⌊ Γ ⌋) (λ b →
                    T ≅ᵀ Hom A a b)))

canTy : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {T : RTy ⌊ Γ ⌋} → Γ ⊢ t ∷ T → Canon t →
        HreflTy t T ⊎ InertTy t T
canTy d (can-lam s) with gen-lam d
... | _ , (_ , (cv , _)) = inj₂ (hΠ , (co-lam s , (_ , (cv , in-Π))))
canTy d (can-pair a b) with gen-pair d
... | _ , (_ , (cv , _)) = inj₂ (hΣ , (co-pair a b , (_ , (cv , in-Σ))))
canTy d can-cb = inj₂ (hU , (co-cb , (_ , (gen-⌜base⌝ d , in-U))))
canTy d (can-cΠ x y) with gen-⌜Π⌝ d
... | _ , (_ , cv) = inj₂ (hU , (co-cΠ x y , (_ , (cv , in-U))))
canTy d (can-cΣ x y) with gen-⌜Σ⌝ d
... | _ , (_ , cv) = inj₂ (hU , (co-cΣ x y , (_ , (cv , in-U))))
canTy d (can-cH x y z) with gen-⌜Hom⌝ d
... | _ , (_ , (_ , cv)) = inj₂ (hU , (co-cH x y z , (_ , (cv , in-U))))
canTy d (can-cId x y z) with gen-⌜Id⌝ d
... | _ , (_ , (_ , cv)) = inj₂ (hU , (co-cId x y z , (_ , (cv , in-U))))
canTy d can-cNat = inj₂ (hU , (co-cNat , (_ , (gen-⌜Nat⌝ d , in-U))))
canTy d can-cUnit = inj₂ (hU , (co-cUnit , (_ , (gen-⌜Unit⌝ d , in-U))))
canTy d (can-cIMu I D i) with gen-⌜IMu⌝ d
... | _ , (_ , (_ , cv)) = inj₂ (hU , (co-cIMu I D i , (_ , (cv , in-U))))
canTy d (can-cFin n) = inj₂ (hU , (co-cFin n , (_ , (gen-⌜Fin⌝ d , in-U))))
canTy d (can-hrefl c s) with gen-hrefl d
... | _ , (_ , cv) = inj₁ ((c , (s , refl)) , (_ , (_ , (_ , cv))))
canTy d (can-idrefl c s) with gen-idrefl d
... | _ , (_ , cv) = inj₂ (hId , (co-idrefl c s , (_ , (cv , in-Id))))
canTy d can-unit = inj₂ (hUnit , (co-unit , (_ , (gen-unit d , in-Unit))))
canTy d can-nzero = inj₂ (hNat , (co-nzero , (_ , (gen-nzero d , in-Nat))))
canTy d (can-nsuc n) with gen-nsuc d
... | _ , cv = inj₂ (hNat , (co-nsuc n , (_ , (cv , in-Nat))))
canTy d (can-con p) with gen-con d
... | _ , (_ , (_ , (_ , (_ , (_ , (_ , cv)))))) = inj₂ (hIMu , (co-con p , (_ , (cv , in-IMu))))
canTy d can-dι with gen-dι d
... | _ , (_ , cv) = inj₂ (hDesc , (co-dι , (_ , (cv , in-Desc))))
canTy d (can-dσ S f) with gen-dσ d
... | _ , (_ , (_ , (_ , cv))) = inj₂ (hDesc , (co-dσ S f , (_ , (cv , in-Desc))))
canTy d (can-dρ j C) with gen-dρ d
... | _ , (_ , (_ , (_ , cv))) = inj₂ (hDesc , (co-dρ j C , (_ , (cv , in-Desc))))
canTy d can-fzero with gen-fzero d
... | _ , cv = inj₂ (hFin , (co-fzero , (_ , (cv , in-Fin))))
canTy d (can-fsuc t) with gen-fsuc d
... | _ , (_ , cv) = inj₂ (hFin , (co-fsuc t , (_ , (cv , in-Fin))))

canView : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {T A : RTy ⌊ Γ ⌋} {h : Hd} →
          Γ ⊢ t ∷ T → T ≅ᵀ A → Inert A h → Canon t → CanOf h t ⊎ (HomHd h × IsHrefl t)
canView d cv iA cn with canTy d cn
... | inj₁ (ih , (_ , (_ , (_ , cvH)))) = inj₂ (hom-inert (ctrnᵀ (csymᵀ cvH) cv) iA , ih)
... | inj₂ (h' , (co , (A' , (cv' , iA')))) with inert-conv (ctrnᵀ (csymᵀ cv') cv) iA' iA
...   | refl = inj₁ co

-- at a head no `Hom` reaches, the view is total.
canAt : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} {T A : RTy ⌊ Γ ⌋} {h : Hd} →
        Γ ⊢ t ∷ T → T ≅ᵀ A → Inert A h → (HomHd h → ⊥) → Canon t → CanOf h t
canAt d cv iA nh cn with canView d cv iA cn
... | inj₁ co       = co
... | inj₂ (hh , _) = ⊥-elim (nh hh)

-- a canonical inhabitant of a CODE-free inert type is no code.
notU : {t : RTm ε} → ◇ ⊢ t ∷ U → (cn : Canon t) → (CanOf hU t → ⊥) → ⊥
notU d cn nc = nc (canAt d crflᵀ in-U (λ ()) cn)

-- at a `Hom`: an `hrefl`, a λ at a Π-join, or `unit` at a Unit-join.
data HomCan {Γ : Ctx} (A : RTy ⌊ Γ ⌋) (a b : RTm ⌊ Γ ⌋) : RTm ⌊ Γ ⌋ → Set where
  hc-refl : (c s : RTm ⌊ Γ ⌋) → HomCan A a b (hrefl c s)
  hc-lam  : (f : RTm (⌊ Γ ⌋ ∙)) {F : RTy ⌊ Γ ⌋} {G : RTy (⌊ Γ ⌋ ∙)} →
            Hom A a b ≅ᵀ Π F G → HomCan A a b (lam f)
  hc-unit : Hom A a b ≅ᵀ Unit → HomCan A a b unit

homCan-go : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {A A' : RTy ⌊ Γ ⌋} {a b : RTm ⌊ Γ ⌋} {h : Hd} →
            CanOf h p → Inert A' h → HomHd h → Hom A a b ≅ᵀ A' → HomCan A a b p
homCan-go (co-lam f) in-Π    hh-Π    cv = hc-lam f cv
homCan-go co-unit    in-Unit hh-Unit cv = hc-unit cv
homCan-go co         iA      hh-base cv = ⊥-elim (noBase co)

homCan : {Γ : Ctx} {p : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} {a b : RTm ⌊ Γ ⌋} →
         Γ ⊢ p ∷ Hom A a b → Canon p → HomCan A a b p
homCan d cn with canTy d cn
... | inj₁ ((c , (s , refl)) , _) = hc-refl c s
... | inj₂ (h , (co , (A' , (cv , iA)))) = homCan-go co iA (hom-inert cv iA) cv

-- the canonical forms of `Nat` (`natrec` inlines this; `ordtr` needs
--   it three times).
data NatShape : RTm ε → Set where
  ns-zero : NatShape nzero
  ns-suc  : (k : RTm ε) → NatShape (nsuc k)

canNat : {n : RTm ε} → ◇ ⊢ n ∷ Nat → Canon n → NatShape n
canNat d cn with canAt d crflᵀ in-Nat (λ ()) cn
... | co-nzero  = ns-zero
... | co-nsuc k = ns-suc k

canΣ : {p : RTm ε} {A : RTy ε} {B : RTy (ε ∙)} → ◇ ⊢ p ∷ Σ' A B → Canon p →
       Σ (RTm ε) (λ a → Σ (RTm ε) (λ b → p ≡ pair a b))
canΣ dp cn with canAt dp crflᵀ in-Σ (λ ()) cn
... | co-pair a b = a , (b , refl)

-- the J-rules, dispatched by the stable code's SHAPE (the Boolean
-- refutes every other constructor).
jfire : {Γ : Cx} (cM aM : RTm (Γ ∙)) (c₁ s e : RTm Γ) →
        stkC? c₁ ≡ true →
        tr (⌜Hom⌝ cM aM (var vz)) (hrefl c₁ s) e ⟶ e
jfire cM aM (var _) s e ()
jfire cM aM (lam _) s e ()
jfire cM aM (app _ _) s e ()
jfire cM aM (pair _ _) s e ()
jfire cM aM (absurd _ _) s e ()
jfire cM aM (ordtr _ _ _ _ _) s e ()
jfire cM aM (fst _) s e ()
jfire cM aM (snd _) s e ()
jfire cM aM ⌜base⌝ s e k = tr-J-base cM aM (var vz) s e
jfire cM aM (⌜Π⌝ _ _) s e ()
jfire cM aM (⌜Σ⌝ x y) s e k = tr-J-Σ cM aM (var vz) x y s e
jfire cM aM (⌜Hom⌝ x y z) s e k = tr-J-Hom cM aM (var vz) x y z s e k
jfire cM aM (hrefl _ _) s e ()
jfire cM aM (tr _ _ _) s e ()
jfire cM aM (ap _ _ _) s e ()
jfire cM aM (⌜Id⌝ x y z) s e k = tr-J-Id cM aM (var vz) x y z s e
jfire cM aM (idrefl _ _) s e ()
jfire cM aM (jsub _ _ _) s e ()
jfire cM aM unit s e ()
jfire cM aM nzero s e ()
jfire cM aM (nsuc _) s e ()
jfire cM aM (natrec _ _ _) s e ()
jfire cM aM (con _) s e ()
jfire cM aM (ielim _ _ _ _) s e ()
jfire cM aM dι s e ()
jfire cM aM (dσ _ _) s e ()
jfire cM aM (dρ _ _) s e ()
jfire cM aM (dpay _ _ _) s e ()
jfire cM aM (dih _ _ _ _) s e ()
jfire cM aM fzero s e ()
jfire cM aM (fsuc _) s e ()
jfire cM aM (fcase _ _ _) s e ()
jfire cM aM (fcase0 _) s e ()
jfire cM aM (psplit _ _) s e ()
jfire cM aM ⌜Nat⌝ s e ()
jfire cM aM (⌜IMu⌝ _ _ _) s e k = tr-J-IMu cM aM (var vz) s e
jfire cM aM (⌜Fin⌝ _) s e k = tr-J-Fin cM aM (var vz) s e
jfire cM aM ⌜Unit⌝ s e k = tr-J-Unit cM aM (var vz) s e

------------------------------------------------------------------------
-- 5. The POINTWISE dispatch (non-recursive: takes the strengthened
--    motive-code's verdict as an argument).  The three outcomes:
--      pw?  → `tr-pw` FIRES (the key transported up the strengthening);
--      step → the motive-code steps (`ξ-trᵈ ∘ ξ-⌜Hom⌝ᶜ`, forward-renamed);
--      stk  → UNTYPEABLE: the path is a lambda, so the Hom over the
--             permanently-stable decode would have to unfold to Π.
------------------------------------------------------------------------

trPwGo : (cM aM f : RTm (ε ∙)) (e : RTm ε)
         {A : RTy ε} {tI uI : RTm ε} →
         ((◇ ▹ A) ⊢ var vz ∷ El cM) →
         ◇ ⊢ lam f ∷ Hom A tI uI →
         renTm vs (subTm (single tI) cM) ≡ cM →
         NoNatC cM →
         UProg (subTm (single tI) cM) →
         Σ (RTm ε) (λ u → tr (⌜Hom⌝ cM aM (var vz)) (lam f) e ⟶ u)
trPwGo cM aM f e {tI = tI} dvM dp sEq ncM (u-pw k) =
  _ , tr-pw cM aM f e
        (trans (cong pw? (sym sEq))
               (trans (pw?-ren vs (subTm (single tI) cM)) k))
trPwGo cM aM f e {tI = tI} dvM dp sEq ncM (u-step {c' = c'} r) =
  _ , ξ-trᵈ (ξ-⌜Hom⌝ᶜ (subst (λ z → z ⟶ renTm vs c') sEq (⟶-ren vs r)))
-- ★★ the ORDERED motive code is excluded by `⊢tr`'s own premise:
-- `NoNatC` is stable under substitution, so the strengthened code is
-- ⌜Nat⌝-free and this arm cannot arise.
trPwGo cM aM f e {A} {tI} dvM dp sEq ncM (u-nat eqN) =
  ⊥-elim (nonatc-nat⊥ (subst NoNatC eqN (nonatc-sub (single tI) ncM)))
  where
  nonatc-nat⊥ : NoNatC (⌜Nat⌝ {ε}) → ⊥
  nonatc-nat⊥ ()
trPwGo cM aM f e {A} {tI} dvM dp sEq ncM (u-stk k) with gen-lam dp
... | A₁ , (B₁ , (cvΠ , _)) =
      ⊥-elim (HomStkΠ-clash k (ctrnᵀ (≅ᵀ-Homᵀ cvA) cvΠ))
  where
  bridge : Σ (RTy (ε ∙)) (λ A' → ((◇ ▹ A) ∋ vz ∷ A') × (El cM ≅ᵀ A')) →
           El cM ≅ᵀ renTy vs A
  bridge (_ , (here , cv)) = cv

  eqA : subTy (single tI) (renTy vs A) ≡ A
  eqA = trans (subTy-renTy A) (trans (subTy-cong (λ x → refl) A) (subTy-id A))

  cvA : El (subTm (single tI) cM) ≅ᵀ A
  cvA = subst (λ z → El (subTm (single tI) cM) ≅ᵀ z) eqA
              (≅ᵀ-sub (single tI) (bridge (gen-var dvM)))

-- no canonical shape types at `base`: it has no introduction form, and
--   a DIAGONAL hom never reaches it (`diagbase⊥`).
canBase⊥ : {t : RTm ε} → ◇ ⊢ t ∷ base → Canon t → ⊥
canBase⊥ d cn with canView d crflᵀ in-base cn
... | inj₁ co = noBase co
... | inj₂ (hh-base , (c , (s , refl))) with gen-hrefl d
...   | _ , (_ , cv) with church-rosserᵀ (csymᵀ cv)
...     | E , (hE , bE) with base-nf bE
...       | refl = diagbase⊥ (s , (done , done)) hE

------------------------------------------------------------------------
-- 6. ★★ THE MUTUAL PROGRESS INDUCTION — bounded by term size,
--    structural on the bound.  `prog`: canonical or steps.  `usplit`:
--    pw, permanently stable, or steps.  Eliminator workers produce the
--    step outright (there IS no canonical eliminator form).
------------------------------------------------------------------------

-- ⚠ the five summands are EXPLICIT arguments on purpose: leaving them
-- implicit makes `+`-inversion leak metas out of every use site (the
-- trap already recorded for the other bound lemmas).
ordtr-bᵃ : (a t u p q : ℕ) {m : ℕ} → a + t + u + p + q ≤ m → a ≤ m
ordtr-bᵃ a t u p q le =
  ≤-trans (≤+ˡ a t)
    (≤-trans (≤+ˡ (a + t) u)
      (≤-trans (≤+ˡ (a + t + u) p)
        (≤-trans (≤+ˡ (a + t + u + p) q) le)))

ordtr-bᵗ : (a t u p q : ℕ) {m : ℕ} → a + t + u + p + q ≤ m → t ≤ m
ordtr-bᵗ a t u p q le =
  ≤-trans (≤+ʳ a t)
    (≤-trans (≤+ˡ (a + t) u)
      (≤-trans (≤+ˡ (a + t + u) p)
        (≤-trans (≤+ˡ (a + t + u + p) q) le)))

ordtr-bᵘ : (a t u p q : ℕ) {m : ℕ} → a + t + u + p + q ≤ m → u ≤ m
ordtr-bᵘ a t u p q le =
  ≤-trans (≤+ʳ (a + t) u)
    (≤-trans (≤+ˡ (a + t + u) p)
      (≤-trans (≤+ˡ (a + t + u + p) q) le))

mutual
  prog : (n : ℕ) {t : RTm ε} {T : RTy ε} → ◇ ⊢ t ∷ T → sz t ≤ n → Prog t
  prog zero    d ()
  prog (suc m) {t = var x}       d le = ⊥-elim (noVar x)
  prog (suc m) {t = lam s}       d le = prog-can (can-lam s)
  prog (suc m) {t = pair a b}    d le = prog-can (can-pair a b)
  prog (suc m) {t = ⌜base⌝}      d le = prog-can can-cb
  prog (suc m) {t = ⌜Nat⌝}       d le = prog-can can-cNat
  prog (suc m) {t = ⌜Unit⌝}      d le = prog-can can-cUnit
  prog (suc m) {t = ⌜IMu⌝ I D i} d le = prog-can (can-cIMu I D i)
  prog (suc m) {t = ⌜Fin⌝ n}     d le = prog-can (can-cFin n)
  prog (suc m) {t = ⌜Π⌝ c cd}    d le = prog-can (can-cΠ c cd)
  prog (suc m) {t = ⌜Σ⌝ c cd}    d le = prog-can (can-cΣ c cd)
  prog (suc m) {t = ⌜Hom⌝ c a b} d le = prog-can (can-cH c a b)
  prog (suc m) {t = hrefl c s}   d le = prog-can (can-hrefl c s)
  prog (suc m) {t = ⌜Id⌝ c a b}  d le = prog-can (can-cId c a b)
  prog (suc m) {t = idrefl c s}  d le = prog-can (can-idrefl c s)
  prog (suc m) {t = unit}        d le = prog-can can-unit
  prog (suc m) {t = nzero}       d le = prog-can can-nzero
  prog (suc m) {t = nsuc n}      d le = prog-can (can-nsuc n)
  prog (suc m) {t = con p}       d le = prog-can (can-con p)
  prog (suc m) {t = dι}        d le = prog-can can-dι
  prog (suc m) {t = dσ S f}      d le = prog-can (can-dσ S f)
  prog (suc m) {t = dρ j C}      d le = prog-can (can-dρ j C)
  prog (suc m) {t = fzero}       d le = prog-can can-fzero
  prog (suc m) {t = fsuc t}      d le = prog-can (can-fsuc t)
  prog (suc m) {t = natrec z w n} d le with natrecS m d (un≤ le)
  ... | _ , r = prog-step r
  -- ★★★ WF-axis stage E: a closed `ordtr` ALWAYS STEPS.
  prog (suc m) {t = ordtr a t u p q} d le with ordtrS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = jsub dM p e} d le with jsubS m d (un≤ le)
  ... | _ , r = prog-step r
  -- ★★★ WF-axis stage D: a closed `absurd` ALWAYS STEPS — its scrutinee
  -- steps, or is canonical at `base`, which `canBase⊥` refutes.
  prog (suc m) {t = absurd c e}  d le with gen-absurd d
  ... | dc , (de , _) with prog m de (≤-trans (≤+ʳ (sz c) (sz e)) (un≤ le))
  ...   | prog-step r = prog-step (ξ-absurdᵉ r)
  ...   | prog-can cn = ⊥-elim (canBase⊥ de cn)
  prog (suc m) {t = app f a}     d le with appS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = fst p}       d le with fstS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = snd p}       d le with sndS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = tr dM p e}   d le with trS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = ap cB b p}   d le with apS m d (un≤ le)
  ... | _ , r = prog-step r
  -- ★★ LEVITATION: every eliminator of the levitated formers ALWAYS
  --   STEPS on closed terms — its scrutinee is canonical at an inert
  --   type (`canAt`), and each canonical shape fires a head rule.
  prog (suc m) {t = ielim D i e t} d le with ielimS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = dpay I D C} d le with dpayS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = dih D e C p} d le with dihS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = fcase t a b} d le with fcaseS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = fcase0 t} d le with fcase0S m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = psplit b q} d le with psplitS m d (un≤ le)
  ... | _ , r = prog-step r

  -- ★ CODE CANONICITY, progress form.
  usplit : (n : ℕ) {c : RTm ε} → ◇ ⊢ c ∷ U → sz c ≤ n → UProg c
  usplit zero    d ()
  usplit (suc m) {c = var x}   d le = ⊥-elim (noVar x)
  usplit (suc m) {c = ⌜base⌝}  d le = u-stk refl
  usplit (suc m) {c = ⌜Nat⌝}   d le = u-nat refl
  usplit (suc m) {c = ⌜Unit⌝}  d le = u-stk refl
  -- ★ §10.4: `⌜IMu⌝` is `stkC?` (it has `tr-J-IMu`); so is `⌜Fin⌝`.
  usplit (suc m) {c = ⌜IMu⌝ I D i} d le = u-stk refl
  usplit (suc m) {c = ⌜Fin⌝ n} d le = u-stk refl
  usplit (suc m) {c = ⌜Π⌝ x y} d le = u-pw refl
  usplit (suc m) {c = ⌜Σ⌝ x y} d le = u-stk refl
  usplit (suc m) {c = ⌜Id⌝ x a b} d le = u-stk refl
  usplit (suc m) {c = ⌜Hom⌝ x a b} d le with gen-⌜Hom⌝ d
  ... | dx , _
        with usplit m dx
               (≤-trans (≤-trans (≤+ˡ (sz x) (sz a))
                                 (≤+ˡ (sz x + sz a) (sz b)))
                        (un≤ le))
  ...   | u-pw k   = u-pw k
  ...   | u-stk k  = u-stk (stkC?→stkA? x k)
  -- ★★ THE PAYOFF: a ⌜Nat⌝ INSIDE a ⌜Hom⌝ makes the wrapper J-able.
  ...   | u-nat refl = u-stk refl
  ...   | u-step r = u-step (ξ-⌜Hom⌝ᶜ r)
  -- an introduction form of any other inert type is no code.
  usplit (suc m) {c = lam s}      d le = ⊥-elim (notU d (can-lam s) λ ())
  usplit (suc m) {c = pair a b}   d le = ⊥-elim (notU d (can-pair a b) λ ())
  usplit (suc m) {c = hrefl x s}  d le = ⊥-elim (notU d (can-hrefl x s) λ ())
  usplit (suc m) {c = idrefl x s} d le = ⊥-elim (notU d (can-idrefl x s) λ ())
  usplit (suc m) {c = unit}       d le = ⊥-elim (notU d can-unit λ ())
  usplit (suc m) {c = nzero}      d le = ⊥-elim (notU d can-nzero λ ())
  usplit (suc m) {c = nsuc n}     d le = ⊥-elim (notU d (can-nsuc n) λ ())
  usplit (suc m) {c = con p}      d le = ⊥-elim (notU d (can-con p) λ ())
  usplit (suc m) {c = dι}       d le = ⊥-elim (notU d can-dι λ ())
  usplit (suc m) {c = dσ S f}     d le = ⊥-elim (notU d (can-dσ S f) λ ())
  usplit (suc m) {c = dρ j C}     d le = ⊥-elim (notU d (can-dρ j C) λ ())
  usplit (suc m) {c = fzero}      d le = ⊥-elim (notU d can-fzero λ ())
  usplit (suc m) {c = fsuc t}     d le = ⊥-elim (notU d (can-fsuc t) λ ())
  -- same argument as `prog`, at `U`: the scrutinee is at `base`.
  usplit (suc m) {c = absurd c₁ e} d le with gen-absurd d
  ... | dc , (de , _) with prog m de (≤-trans (≤+ʳ (sz c₁) (sz e)) (un≤ le))
  ...   | prog-step r = u-step (ξ-absurdᵉ r)
  ...   | prog-can cn = ⊥-elim (canBase⊥ de cn)
  -- every eliminator steps (the `prog` rows' workers).
  usplit (suc m) {c = app f a} d le with appS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = fst p} d le with fstS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = snd p} d le with sndS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = tr dM p e} d le with trS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = ap cB b p} d le with apS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = jsub dM p e} d le with jsubS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = natrec z w n} d le with natrecS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = ordtr a t u p q} d le with ordtrS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = ielim D i e t} d le with ielimS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = dpay I D C} d le with dpayS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = dih D e C p} d le with dihS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = fcase t a b} d le with fcaseS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = fcase0 t} d le with fcase0S m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = psplit b q} d le with psplitS m d (un≤ le)
  ... | _ , r = u-step r

  appS : (m : ℕ) {f a : RTm ε} {T : RTy ε} → ◇ ⊢ app f a ∷ T →
         sz f + sz a ≤ m → Σ (RTm ε) (λ u → app f a ⟶ u)
  appS m {f} {a} dv q with gen-app dv
  ... | A , (B , (df , (da , cB))) with prog m df (≤-trans (≤+ˡ (sz f) (sz a)) q)
  ...   | prog-step r = _ , ξ-appˡ r
  ...   | prog-can cn = canΠ m df cn (≤-trans (≤+ˡ (sz f) (sz a)) q) a

  -- canonical Π-inhabitants β-reduce or (hrefl at a pw-able code)
  -- unfold; the stable-code and order hrefls never join a Π.
  canΠ : (m : ℕ) {f : RTm ε} {A : RTy ε} {B : RTy (ε ∙)} →
         ◇ ⊢ f ∷ Π A B → Canon f → sz f ≤ m →
         (a : RTm ε) → Σ (RTm ε) (λ u → app f a ⟶ u)
  canΠ m df cn le a with canView df crflᵀ in-Π cn
  ... | inj₁ (co-lam s) = _ , β s a
  ... | inj₂ (hh-Π , (c₁ , (s , refl))) with gen-hrefl df
  ...   | dc₁ , (ds , cvh)
          with usplit m dc₁ (≤-trans (≤-suc (≤+ˡ (sz c₁) (sz s))) le)
  ...     | u-pw k   = _ , ξ-appˡ (hrefl-pw c₁ s k)
  ...     | u-step r = _ , ξ-appˡ (ξ-hreflᶜ r)
  ...     | u-stk k  = ⊥-elim (HomStkΠ-clash k (csymᵀ cvh))
  ...     | u-nat refl = ⊥-elim (HomNatΠ-clash (csymᵀ cvh))

  fstS : (m : ℕ) {p : RTm ε} {T : RTy ε} → ◇ ⊢ fst p ∷ T →
         sz p ≤ m → Σ (RTm ε) (λ u → fst p ⟶ u)
  fstS m dv q with gen-fst dv
  ... | A , (B , (dp , cA)) with prog m dp q
  ...   | prog-step r = _ , ξ-fst r
  ...   | prog-can cn with canΣ dp cn
  ...     | a , (b , refl) = _ , βfst a b

  sndS : (m : ℕ) {p : RTm ε} {T : RTy ε} → ◇ ⊢ snd p ∷ T →
         sz p ≤ m → Σ (RTm ε) (λ u → snd p ⟶ u)
  sndS m dv q with gen-snd dv
  ... | A , (B , (dp , cA)) with prog m dp q
  ...   | prog-step r = _ , ξ-snd r
  ...   | prog-can cn with canΣ dp cn
  ...     | a , (b , refl) = _ , βsnd a b

  -- ★ closed `ap`s ALWAYS step: the path steps, unfolds pointwise, or
  -- is a canonical hrefl (J fires — the code is stable or steps); a
  -- lam path (or `unit`) is UNTYPEABLE at the flat source ambient.
  apS : (m : ℕ) {cB : RTm ε} {b : RTm (ε ∙)} {p : RTm ε} {T : RTy ε} →
        ◇ ⊢ ap cB b p ∷ T → sz cB + sz b + sz p ≤ m →
        Σ (RTm ε) (λ w → ap cB b p ⟶ w)
  apS m {cB} {b} {p} dv q with gen-ap dv
  ... | cA , (t , (u , (dcA , (keyA , (dcB , (db , (dt , (du , (dp , cC)))))))))
        with prog m dp
               (≤-trans (≤+ʳ (sz cB + sz b) (sz p)) q)
  ...   | prog-step r = _ , ξ-apᵖ r
  ...   | prog-can cn with homCan dp cn
  ...     | hc-lam f cv = ⊥-elim (HomStkΠ-clash (flat→stk cA keyA) cv)
  ...     | hc-unit cv =
            ⊥-elim (HomUnit-clash (nn-El (stkC?→hd cA (flat→stk cA keyA))) cv)
  ...     | hc-refl c₁ s with gen-hrefl dp
  ...       | dc₁ , (ds , cvh)
              with usplit m dc₁
                     (≤-trans (≤-suc (≤+ˡ (sz c₁) (sz s)))
                              (≤-trans (≤+ʳ (sz cB + sz b) (sz (hrefl c₁ s))) q))
  ...         | u-pw k   = _ , ξ-apᵖ (hrefl-pw c₁ s k)
  ...         | u-step r = _ , ξ-apᵖ (ξ-hreflᶜ r)
  ...         | u-stk k  = _ , ap-J cB b c₁ s k
  -- ★★ untypeable: `El ⌜Nat⌝ ⟶ᵀ Nat`, but a `flat?` source ambient
  -- decodes to `base` or a `Hom` and never reaches `Nat`.
  ...         | u-nat refl =
                ⊥-elim (HomNatNoNat-clash (nn-El (stkC?→hd cA (flat→stk cA keyA)))
                                          (csymᵀ cvh))

  -- ★ CLOSED `tr`s ALWAYS STEP.  The dispatch: path steps → ξ; path
  -- canonical → per the motive.
  trS : (m : ℕ) {dM : RTm (ε ∙)} {p e : RTm ε} {T : RTy ε} →
        ◇ ⊢ tr dM p e ∷ T → sz dM + sz p + sz e ≤ m →
        Σ (RTm ε) (λ u → tr dM p e ⟶ u)
  trS m {dM} {p} {e} dv q with gen-tr dv
  ... | tgU inv =
        trUS m inv
          (≤-trans (≤-trans (≤+ʳ (sz dM) (sz p))
                            (≤+ˡ (sz dM + sz p) (sz e))) q)
  ... | tgC (mkTrInv cM aM refl A tI uI dcM daM dvM ncM hcM haM dt du dp de cC) =
        trCS m cM aM e dcM hcM ncM dt dvM dp
          (≤-trans (≤-trans (≤+ʳ (sz dM) (sz p))
                            (≤+ˡ (sz dM + sz p) (sz e))) q)
          (≤-trans (≤-suc (≤-trans (≤+ˡ (sz cM) (sz aM))
                                   (≤+ˡ (sz cM + sz aM) (suc zero))))
                   (≤-trans (≤-trans (≤+ˡ (sz dM) (sz p))
                                     (≤+ˡ (sz dM + sz p) (sz e))) q))

  -- ★ closed `jsub`s ALWAYS step: the path is a canonical `idrefl`
  -- (J fires, unkeyed) or steps.
  jsubS : (m : ℕ) {dM : RTm (ε ∙)} {p e : RTm ε} {T : RTy ε} →
          ◇ ⊢ jsub dM p e ∷ T → sz dM + sz p + sz e ≤ m →
          Σ (RTm ε) (λ w → jsub dM p e ⟶ w)
  jsubS m {dM} {p} {e} dv q with gen-jsub dv
  ... | A , (t , (u , (dd , (dt , (du , (dp , (de , cC)))))))
        with prog m dp
               (≤-trans (≤-trans (≤+ʳ (sz dM) (sz p))
                                 (≤+ˡ (sz dM + sz p) (sz e))) q)
  ...   | prog-step r = _ , ξ-jsubᵖ r
  ...   | prog-can cn with canAt dp crflᵀ in-Id (λ ()) cn
  ...     | co-idrefl c s = _ , jsub-refl dM c s e

  -- ★★ WF stage A: CLOSED `natrec`s ALWAYS STEP — a closed `Nat` is a
  -- numeral (which fires) or steps (which propagates).
  natrecS : (m : ℕ) {z : RTm ε} {w : RTm ((ε ∙) ∙)} {n : RTm ε} {T : RTy ε} →
            ◇ ⊢ natrec z w n ∷ T → sz z + sz w + sz n ≤ m →
            Σ (RTm ε) (λ v → natrec z w n ⟶ v)
  natrecS m {z} {w} {n} dv q with gen-natrec dv
  ... | M , (tyM , (dz , (dw , (dn , cC))))
        with prog m dn
               (≤-trans (≤+ʳ (sz z + sz w) (sz n)) q)
  ...   | prog-step r          = _ , ξ-natrecⁿ r
  ...   | prog-can cn with canNat dn cn
  ...     | ns-zero  = _ , natrec-zero z w
  ...     | ns-suc k = _ , natrec-suc z w k

  -- ★★★ LEVITATION: the family's ι.  A closed scrutinee at `IMu I D i`
  --   is a `con` (ι fires, at ANY description) or steps.
  ielimS : (m : ℕ) {D i e t : RTm ε} {T : RTy ε} →
           ◇ ⊢ ielim D i e t ∷ T → sz D + sz i + sz e + sz t ≤ m →
           Σ (RTm ε) (λ v → ielim D i e t ⟶ v)
  ielimS m {D} {i} {e} {t} dv q with gen-ielim dv
  ... | I , (M , (dI , (dD , (dM , (de , (di , (dt , cC)))))))
        with prog m dt (≤-trans (≤+ʳ (sz D + sz i + sz e) (sz t)) q)
  ...   | prog-step r = _ , ξ-ielimᵗ r
  ...   | prog-can cn with canAt dt crflᵀ in-IMu (λ ()) cn
  ...     | co-con p = _ , ι D i e p

  -- the payload code and the hypotheses compute on a CLOSED telescope,
  --   which is `dι`/`dσ`/`dρ` or steps.
  dpayS : (m : ℕ) {I D C : RTm ε} {T : RTy ε} →
          ◇ ⊢ dpay I D C ∷ T → sz I + sz D + sz C ≤ m →
          Σ (RTm ε) (λ v → dpay I D C ⟶ v)
  dpayS m {I} {D} {C} dv q with gen-dpay dv
  ... | dI , (dD , (dC , cU))
        with prog m dC (≤-trans (≤+ʳ (sz I + sz D) (sz C)) q)
  ...   | prog-step r = _ , ξ-dpayᶜ r
  ...   | prog-can cn with canAt dC crflᵀ in-Desc (λ ()) cn
  ...     | co-dι      = _ , dpay-ι I D
  ...     | co-dσ S f  = _ , dpay-σ I D S f
  ...     | co-dρ j C' = _ , dpay-ρ I D j C'

  dihS : (m : ℕ) {D e C p : RTm ε} {T : RTy ε} →
         ◇ ⊢ dih D e C p ∷ T → sz D + sz e + sz C + sz p ≤ m →
         Σ (RTm ε) (λ v → dih D e C p ⟶ v)
  dihS m {D} {e} {C} {p} dv q with gen-dih dv
  ... | I , (M , (dI , (dD , (dM , (de , (dC , (dp , cC)))))))
        with prog m dC (≤-trans (≤-trans (≤+ʳ (sz D + sz e) (sz C))
                                         (≤+ˡ (sz D + sz e + sz C) (sz p))) q)
  ...   | prog-step r = _ , ξ-dihᶜ r
  ...   | prog-can cn with canAt dC crflᵀ in-Desc (λ ()) cn
  ...     | co-dι      = _ , dih-ι D e p
  ...     | co-dσ S f  = _ , dih-σ D e S f p
  ...     | co-dρ j C' = _ , dih-ρ D e j C' p

  -- the tags: a closed `Fin (suc n)` is `fzero` or `fsuc`; `Fin zero`
  --   has no canonical inhabitant at all (the index clashes).
  fcaseS : (m : ℕ) {t a : RTm ε} {b : RTm (ε ∙)} {T : RTy ε} →
           ◇ ⊢ fcase t a b ∷ T → sz t + sz a + sz b ≤ m →
           Σ (RTm ε) (λ v → fcase t a b ⟶ v)
  fcaseS m {t} {a} {b} dv q with gen-fcase dv
  ... | n , (P , (dP , (dt , (da , (db , cC)))))
        with prog m dt (≤-trans (≤-trans (≤+ˡ (sz t) (sz a)) (≤+ˡ (sz t + sz a) (sz b))) q)
  ...   | prog-step r = _ , ξ-fcaseᵗ r
  ...   | prog-can cn with canAt dt crflᵀ in-Fin (λ ()) cn
  ...     | co-fzero   = _ , fcase-z a b
  ...     | co-fsuc t' = _ , fcase-s t' a b

  fcase0S : (m : ℕ) {t : RTm ε} {T : RTy ε} →
            ◇ ⊢ fcase0 t ∷ T → sz t ≤ m → Σ (RTm ε) (λ v → fcase0 t ⟶ v)
  fcase0S m {t} dv q with gen-fcase0 dv
  ... | P , (dP , (dt , cC)) with prog m dt q
  ...   | prog-step r = _ , ξ-fcase0 r
  ...   | prog-can cn with canAt dt crflᵀ in-Fin (λ ()) cn
  ...     | co-fzero with gen-fzero dt
  ...       | _ , cv with Fin-inj cv
  ...         | ()
  fcase0S m {t} dv q | P , (dP , (dt , cC)) | prog-can cn | co-fsuc t' with gen-fsuc dt
  ... | _ , (_ , cv) with Fin-inj cv
  ...   | ()

  -- Σ-induction: a closed pair fires β.
  psplitS : (m : ℕ) {b : RTm ((ε ∙) ∙)} {q : RTm ε} {T : RTy ε} →
            ◇ ⊢ psplit b q ∷ T → sz b + sz q ≤ m →
            Σ (RTm ε) (λ v → psplit b q ⟶ v)
  psplitS m {b} {q} dv le with gen-psplit dv
  ... | A , (B , (P , (dA , (dB , (dP , (dq , (db , cC)))))))
        with prog m dq (≤-trans (≤+ʳ (sz b) (sz q)) le)
  ...   | prog-step r = _ , ξ-psplitᵍ r
  ...   | prog-can cn with canΣ dq cn
  ...     | x , (y , refl) = _ , psplit-β b x y

  -- ★★★ WF-axis stage E: ORDER TRANSPORT STEPS.  The bounds are walked
  -- in `ordstk?`'s dispatch order — `a`, then `t`, then `u` — which is
  -- the same order `sn-ordtr` and `homNatSem` use, so the five root
  -- rules line up with the five numeral leaves one-to-one.
  ordtrS : (m : ℕ) {a t u p q : RTm ε} {T : RTy ε} →
           ◇ ⊢ ordtr a t u p q ∷ T →
           sz a + sz t + sz u + sz p + sz q ≤ m →
           Σ (RTm ε) (λ v → ordtr a t u p q ⟶ v)
  ordtrS m {a} {t} {u} {p} {q} dv le with gen-ordtr dv
  ... | da , (dt , (du , (dp , (dq , cC))))
        with prog m da (ordtr-bᵃ (sz a) (sz t) (sz u) (sz p) (sz q) le)
  ...     | prog-step r = _ , ξ-ordtrᵃ r
  ...     | prog-can cn with canNat da cn
  -- rule 1: a zero lower bound discharges the order outright.
  ...       | ns-zero = _ , ordtr-z t u p q
  ...       | ns-suc a'
              with prog m dt (ordtr-bᵗ (sz a) (sz t) (sz u) (sz p) (sz q) le)
  ...         | prog-step r = _ , ξ-ordtrᵗ r
  ...         | prog-can cn' with canNat dt cn'
  ...           | ns-zero
                  with prog m du (ordtr-bᵘ (sz a) (sz t) (sz u) (sz p) (sz q) le)
  ...             | prog-step r = _ , ξ-ordtrᵘ r
  ...             | prog-can cn'' with canNat du cn''
  -- rule 2, then rule 4 — stage D's customer, at the top level this time.
  ...               | ns-zero    = _ , ordtr-szz a' p q
  ...               | ns-suc u'  = _ , ordtr-szs a' u' p q
  ordtrS m {a} {t} {u} {p} {q} dv le
      | da , (dt , (du , (dp , (dq , cC))))
      | prog-can cn | ns-suc a' | prog-can cn' | ns-suc t'
        with prog m du (ordtr-bᵘ (sz a) (sz t) (sz u) (sz p) (sz q) le)
  ...   | prog-step r = _ , ξ-ordtrᵘ r
  ...   | prog-can cn'' with canNat du cn''
  -- rule 3, then rule 5 — transitivity's own recursive step.
  ...     | ns-zero   = _ , ordtr-ssz a' t' p q
  ...     | ns-suc u' = _ , ordtr-sss a' t' u' p q

  -- the TAUT motive (`var vz`, ambient `U`).
  trUS : (m : ℕ) {dM : RTm (ε ∙)} {p e : RTm ε} {T : RTy ε} →
         TrInvU ◇ dM p e T → sz p ≤ m →
         Σ (RTm ε) (λ u → tr dM p e ⟶ u)
  trUS m {p = p} {e = e} (mkTrInvU refl tI uI dt du dp de cC) lep
    with prog m dp lep
  ... | prog-step r = _ , ξ-trᵖ r
  ... | prog-can cn with homCan dp cn
  ...   | hc-lam f cv = _ , tr-taut f e
  ...   | hc-unit cv  = ⊥-elim (HomUnit-clash nn-U cv)
  ...   | hc-refl c₁ s with gen-hrefl dp
  ...     | dc₁ , (ds , cvh)
            with usplit m dc₁ (≤-trans (≤-suc (≤+ˡ (sz c₁) (sz s))) lep)
  ...       | u-pw k   = _ , ξ-trᵖ (hrefl-pw c₁ s k)
  ...       | u-step r = _ , ξ-trᵖ (ξ-hreflᶜ r)
  ...       | u-stk k  = ⊥-elim (HomStkU-clash k cvh)
  ...       | u-nat refl = ⊥-elim (HomNatU-clash cvh)

  -- the CODE motive (`⌜Hom⌝ cM aM (var vz)`).
  trCS : (m : ℕ) (cM aM : RTm (ε ∙)) (e : RTm ε)
         {A : RTy ε} {tI uI : RTm ε} {p : RTm ε} →
         ((◇ ▹ A) ⊢ cM ∷ U) → occTm vz cM ≡ false → NoNatC cM →
         (◇ ⊢ tI ∷ A) → ((◇ ▹ A) ⊢ var vz ∷ El cM) →
         (◇ ⊢ p ∷ Hom A tI uI) →
         sz p ≤ m → sz cM ≤ m →
         Σ (RTm ε) (λ u → tr (⌜Hom⌝ cM aM (var vz)) p e ⟶ u)
  trCS m cM aM e {tI = tI} dcM hcM ncM dt dvM dp lep lecM with prog m dp lep
  ... | prog-step r = _ , ξ-trᵖ r
  ... | prog-can cn with homCan dp cn
  ...   | hc-lam f cv = trPw m cM aM f e dcM hcM ncM dt dvM dp lecM
  ...   | hc-unit cv with tr-amb-conv tI ncM dvM
  ...     | c₉ , (hd₉ , cvA₉) =
            ⊥-elim (HomUnit-clash (nn-El hd₉) (ctrnᵀ (≅ᵀ-Homᵀ cvA₉) cv))
  trCS m cM aM e {tI = tI} dcM hcM ncM dt dvM dp lep lecM
    | prog-can cn | hc-refl c₁ s with gen-hrefl dp
  ... | dc₁ , (ds , cvh)
        with usplit m dc₁ (≤-trans (≤-suc (≤+ˡ (sz c₁) (sz s))) lep)
  ...   | u-pw k   = _ , ξ-trᵖ (hrefl-pw c₁ s k)
  ...   | u-step r = _ , ξ-trᵖ (ξ-hreflᶜ r)
  ...   | u-stk k  = _ , jfire cM aM c₁ s e k
  -- ★★ the ORDERED path code: the `tr` ambient is convertible to a
  -- Nat-FREE decode (`⊢tr`'s `NoNatC` premise), and an order-hom joins
  -- only `Unit`, `base`, or another `Nat`-ambient hom.
  ...   | u-nat refl with tr-amb-conv tI ncM dvM
  ...     | c₉ , (hd₉ , cvA₉) =
            ⊥-elim (HomNatNoNat-clash (nn-El hd₉)
                      (ctrnᵀ (csymᵀ cvh) (≅ᵀ-Homᵀ (csymᵀ cvA₉))))

  -- ★★ THE POINTWISE CASE: strengthen the motive-code, run the split
  -- on the CLOSED instance, dispatch.  (`sz` is renaming-invariant, so
  -- the strengthened code fits the SAME bound — the reason this whole
  -- induction is size-based.)
  trPw : (m : ℕ) (cM aM f : RTm (ε ∙)) (e : RTm ε)
         {A : RTy ε} {tI uI : RTm ε} →
         ((◇ ▹ A) ⊢ cM ∷ U) → occTm vz cM ≡ false → NoNatC cM →
         (◇ ⊢ tI ∷ A) → ((◇ ▹ A) ⊢ var vz ∷ El cM) →
         (◇ ⊢ lam f ∷ Hom A tI uI) →
         sz cM ≤ m →
         Σ (RTm ε) (λ u → tr (⌜Hom⌝ cM aM (var vz)) (lam f) e ⟶ u)
  trPw m cM aM f e {tI = tI} dcM hcM ncM dt dvM dp lecM =
    trPwGo cM aM f e dvM dp strengthEq ncM
      (usplit m (⊢[] dcM dt)
         (subst (λ z → z ≤ m)
                (trans (cong sz (sym strengthEq))
                       (sz-ren vs (subTm (single tI) cM)))
                lecM))
    where
    strengthEq : renTm vs (subTm (single tI) cM) ≡ cM
    strengthEq =
      trans (renTm-subTm cM) (trans (subTm-occ cM agree) (subTm-id cM))
      where
      agree : ∀ x → occTm x cM ≡ true → _
      agree vz oc with trans (sym oc) hcM
      ... | ()
      agree (vs i) oc = refl

------------------------------------------------------------------------
-- 7. ★ THE G2 THEOREMS.
------------------------------------------------------------------------

-- closed progress: canonical or steps.
progress : {t : RTm ε} {T : RTy ε} → ◇ ⊢ t ∷ T → Prog t
progress {t = t} d = prog (sz t) d ≤-refl

-- closed code split, progress form.
codeSplit : {c : RTm ε} → ◇ ⊢ c ∷ U → UProg c
codeSplit {c = c} d = usplit (sz c) d ≤-refl

-- ★ CODE CANONICITY (the W2b done-when, item 1): a closed NORMAL code
-- of type `U` is pointwise-able, permanently stable, or ORDERED.
--
-- ★★ SpikeNatJ: THE THREE-WAY SPLIT THE SPIKE PREDICTED, and it is
-- exactly one code wide.  ⌜Nat⌝ is neither `pw?` nor `stkC?`; after the
-- `stkA?` split every ⌜Hom⌝ OVER it is `stkC?`, so the third arm does
-- not spread up the spine.
codeCanon : {c : RTm ε} → ◇ ⊢ c ∷ U → IsNormal c →
            (pw? c ≡ true) ⊎ ((stkC? c ≡ true) ⊎ (c ≡ ⌜Nat⌝))
codeCanon d nrm with codeSplit d
... | u-pw k   = inj₁ k
... | u-stk k  = inj₂ (inj₁ k)
... | u-nat eq = inj₂ (inj₂ eq)
... | u-step r = ⊥-elim (nrm r)

-- ★ PATH CANONICITY (item 2): a closed normal path at a `Hom` type is
-- an `hrefl` or a lambda.
-- ★ WF stage B: `pathCanon` needs the ambient guard.  At a `Nat`
-- ambient a closed normal path can be `unit` — that IS the computing
-- order's payoff — so the two-shape conclusion holds exactly off
-- `Nat`.  Every consumer has an `El` ambient.
pathCanon : {p : RTm ε} {A : RTy ε} {t u : RTm ε} → NoNat A →
            ◇ ⊢ p ∷ Hom A t u → IsNormal p →
            (Σ (RTm ε) (λ c → Σ (RTm ε) (λ s → p ≡ hrefl c s)))
            ⊎ (Σ (RTm (ε ∙)) (λ f → p ≡ lam f))
pathCanon nn d nrm with progress d
... | prog-step r = ⊥-elim (nrm r)
... | prog-can cn with homCan d cn
...   | hc-refl c s = inj₁ (c , (s , refl))
...   | hc-lam f _  = inj₂ (f , refl)
...   | hc-unit cv  = ⊥-elim (HomUnit-clash nn cv)

-- ★ TR-PROGRESS (item 3): a closed well-typed `tr` ALWAYS steps —
-- transport never sticks on closed terms.
trProgress : {dM : RTm (ε ∙)} {p e : RTm ε} {T : RTy ε} →
             ◇ ⊢ tr dM p e ∷ T → Σ (RTm ε) (λ u → tr dM p e ⟶ u)
trProgress {dM} {p} {e} d = trS (sz dM + sz p + sz e) d ≤-refl


-- ★★ CONSISTENCY of the full W2/W2b kernel: `base` has no closed
-- inhabitant.  Normalize (`wnorm`, the fundamental theorem), preserve
-- the typing (`sr*`), and the normal form is canonical (impossible at
-- `base`) or steps (impossible for a normal form).
consistency : {t : RTm ε} → ◇ ⊢ t ∷ base → ⊥
consistency d with wnorm c-◇ d
... | mkWN nfm rd nrm snf with progress (sr* d rd)
...   | prog-step r = nrm r
...   | prog-can cn = canBase⊥ (sr* d rd) cn

------------------------------------------------------------------------
-- ★★★ 9. WHAT FORDING ACTUALLY BUYS — `Typing.agda`'s ⊢icon note, PROVED.
--
-- ⚠⚠ THE NOTE THIS DISCHARGES.  `⊢icon` carried a comment claiming that
--   the FORDING constraint field excludes the bad constructors.  That was
--   an invariant nothing checked, and the `⊢con` premise one rule up is
--   the cautionary tale: stated as a comment it was FALSE, and only gate
--   5 caught it.  So the mechanism is stated and proved here instead.
--
-- ★ THE MECHANISM, in one theorem: a CLOSED proof of `Id` forces its
--   endpoints CONVERTIBLE.  A Fording field has type `El (⌜Id⌝ c a b)`,
--   which decodes to `Id (El c) a b`, so a constructor at the wrong
--   index would need a closed inhabitant there — and `idEndpoints` says
--   that inhabitant makes the index and the constructor's own target
--   convertible.  Instantiated at distinct numerals (`zero≇suc`) the
--   constructor is uninhabitable.  `Examples/Vec` runs it.
--
-- ⚠ NOT a soundness patch and not a restriction: nothing here changes
--   the rules.  It is the SEMANTIC CONTENT of §3's Fording decision,
--   which until now lived only in a comment.
------------------------------------------------------------------------

-- `nzero` is a value: no rule fires on it, so it is its own only reduct.
zeroNF : {C : RTm ε} → nzero ⟶* C → C ≡ nzero
zeroNF done       = refl
zeroNF (step () _)

-- `nsuc` is INERT: only `ξ-nsuc` applies, so the head survives.
sucRed : {n : RTm ε} {C : RTm ε} → nsuc n ⟶* C →
         Σ (RTm ε) (λ n' → C ≡ nsuc n')
sucRed done               = _ , refl
sucRed (step (ξ-nsuc r) q) = sucRed q

-- ★ distinct numerals are not convertible.  The one fact the Fording
--   constraint is FOR.
zero≇suc : {n : RTm ε} → nzero ≅ nsuc n → ⊥
zero≇suc cv with church-rosser cv
... | w , (rz , rs) with zeroNF rz
...   | refl with sucRed rs
...     | _ , ()

-- ★★ a CLOSED canonical inhabitant of `Id` pins its endpoints together.
--   Every non-`idrefl` shape is refuted by the clash toolkit — the same
--   enumeration `elimS`/`pathCanon` walk, at `Id` instead of `Mu`/`Hom`.
canIdEnds : {A : RTy ε} {a b q : RTm ε} → ◇ ⊢ q ∷ Id A a b → Canon q → a ≅ b
canIdEnds d cn with canAt d crflᵀ in-Id (λ ()) cn
... | co-idrefl c s with gen-idrefl d
...   | _ , (_ , cv) with church-rosserᵀ cv
...     | E , (rL , rR) with Id-reduct rL
...       | A₁ , (a₁ , (b₁ , (refl , (_ , (ra , rb))))) with Id-reduct rR
...         | A₂ , (s₁ , (s₂ , (refl , (_ , (rs₁ , rs₂))))) =
              ctrn (red→≅ ra)
                (ctrn (csym (red→≅ rs₁))
                  (ctrn (red→≅ rs₂) (csym (red→≅ rb))))

-- ★★★ THE THEOREM.  A closed proof of `Id A a b` forces `a ≅ b`.
idEndpoints : {A : RTy ε} {a b q : RTm ε} → ◇ ⊢ q ∷ Id A a b → a ≅ b
idEndpoints d with wnorm c-◇ d
... | mkWN n r nrm _ with progress (sr* d r)
...   | prog-step s  = ⊥-elim (nrm s)
...   | prog-can cn  = canIdEnds (sr* d r) cn
