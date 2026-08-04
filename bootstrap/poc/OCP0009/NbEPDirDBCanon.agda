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
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBCanon where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_; _×_; ⊥; ⊥-elim
        ; _⊎_; inj₁; inj₂; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; pair; fst; snd
        ; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr
        ; Ren; renTm; renTy; Sub; subTm; subTy
        ; renTm-subTm; subTm-id
        ; subTy-renTy; subTy-cong; subTy-id )
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; false; pw?; stkC?; pw?-ren; occTm; subTm-occ
        ; eqv; occ-sub; occ-ren-tm; avoids-wk )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶_; _⟶*_; done; step
        ; β; βfst; βsnd; ξ-appˡ; ξ-fst; ξ-snd
        ; ξ-hreflᶜ; ξ-trᵈ; ξ-trᵖ; ξ-⌜Hom⌝ᶜ
        ; hrefl-pw; tr-J-base; tr-J-Σ; tr-J-Hom; tr-taut; tr-pw
        ; _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝; ξ-El
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ; credᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_; here
        ; _⊢_∷_; ⊢conv; ⊢⌜base⌝
        ; ⊢ctx_; c-◇ )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶-ren )
open import poc.OCP0009.NbEPDirDBSR using ( ≅ᵀ-sub )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ
        ; church-rosserᵀ; red→≅ᵀ
        ; Π-reduct; ΠRed; mkΠRed; Σ-reduct; ΣRed; mkΣRed )
open import poc.OCP0009.NbEPDirDBSubj
  using ( gen-lam; gen-app; gen-pair; gen-fst; gen-snd
        ; gen-var; gen-hrefl; gen-⌜Π⌝; gen-⌜Σ⌝; gen-⌜Hom⌝
        ; gen-tr; TrGen; tgC; tgU; TrInv; mkTrInv; TrInvU; mkTrInvU
        ; StkAmb; st-el; st-hom; stamb-red; homred-inv
        ; HomΠShape; hsΠ; hsH; hom-shape
        ; ≅ᵀ-Homᵀ; ⊢[]; sr*; ⊢wk )
open import poc.OCP0009.NbEPDirDBLR
  using ( base-nf; U-nf; IsNormal; WN; mkWN )
open import poc.OCP0009.NbEPDirDBFund using ( wnorm )

------------------------------------------------------------------------
-- 0. Small facts: no closed variables; `El` never reaches `U`.
------------------------------------------------------------------------

noVar : Var ε → ⊥
noVar ()

-- reducts of `Π`/`Σ'`/`Hom`-forms never reach `U`; `El`-chains reach
-- `U` through nothing (each decode-step lands in one of those shapes).
elnotU : {Γ : Cx} {t : RTm Γ} → El t ⟶ᵀ* U → ⊥
elnotU (stepᵀ El-⌜base⌝ rest) with base-nf rest
... | ()
elnotU (stepᵀ (El-⌜Π⌝ _ _) rest) with Π-reduct rest
... | mkΠRed _ _ () _ _
elnotU (stepᵀ (El-⌜Σ⌝ _ _) rest) with Σ-reduct rest
... | mkΣRed _ _ () _ _
elnotU (stepᵀ (El-⌜Hom⌝ _ _ _) rest) with hom-shape rest
... | ()
elnotU (stepᵀ (ξ-El r) rest) = elnotU rest

------------------------------------------------------------------------
-- 1. The CLASH toolkit — canonical-shape types against each other,
--    by confluence.
------------------------------------------------------------------------

ΠU-clash : {Γ : Cx} {F : RTy Γ} {G : RTy (Γ ∙)} → Π F G ≅ᵀ U → ⊥
ΠU-clash cv with church-rosserᵀ cv
... | E , (πE , uE) with U-nf uE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _

ΣU-clash : {Γ : Cx} {F : RTy Γ} {G : RTy (Γ ∙)} → Σ' F G ≅ᵀ U → ⊥
ΣU-clash cv with church-rosserᵀ cv
... | E , (σE , uE) with U-nf uE
...   | refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _

ΣΠ-clash : {Γ : Cx} {F : RTy Γ} {G : RTy (Γ ∙)}
           {F' : RTy Γ} {G' : RTy (Γ ∙)} → Σ' F G ≅ᵀ Π F' G' → ⊥
ΣΠ-clash cv with church-rosserᵀ cv
... | E , (σE , πE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with Π-reduct πE
...     | mkΠRed _ _ () _ _

HomU-clash : {Γ : Cx} {A : RTy Γ} {t u : RTm Γ} → Hom A t u ≅ᵀ U → ⊥
HomU-clash cv with church-rosserᵀ cv
... | E , (hE , uE) with U-nf uE
...   | refl with hom-shape hE
...     | ()

HomΣ-clash : {Γ : Cx} {A : RTy Γ} {t u : RTm Γ}
             {F : RTy Γ} {G : RTy (Γ ∙)} → Hom A t u ≅ᵀ Σ' F G → ⊥
HomΣ-clash cv with church-rosserᵀ cv
... | E , (hE , σE) with Σ-reduct σE
...   | mkΣRed _ _ refl _ _ with hom-shape hE
...     | ()

Πbase-clash : {Γ : Cx} {F : RTy Γ} {G : RTy (Γ ∙)} → Π F G ≅ᵀ base → ⊥
Πbase-clash cv with church-rosserᵀ cv
... | E , (πE , bE) with base-nf bE
...   | refl with Π-reduct πE
...     | mkΠRed _ _ () _ _

Σbase-clash : {Γ : Cx} {F : RTy Γ} {G : RTy (Γ ∙)} → Σ' F G ≅ᵀ base → ⊥
Σbase-clash cv with church-rosserᵀ cv
... | E , (σE , bE) with base-nf bE
...   | refl with Σ-reduct σE
...     | mkΣRed _ _ () _ _

Ubase-clash : {Γ : Cx} → U {Γ} ≅ᵀ base → ⊥
Ubase-clash cv with church-rosserᵀ cv
... | E , (uE , bE) with base-nf bE
...   | refl with U-nf uE
...     | ()

Hombase-clash : {Γ : Cx} {A : RTy Γ} {t u : RTm Γ} →
                Hom A t u ≅ᵀ base → ⊥
Hombase-clash cv with church-rosserᵀ cv
... | E , (hE , bE) with base-nf bE
...   | refl with hom-shape hE
...     | ()

-- StkAmb transported along a chain — the one tool behind the
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
        with stamb-star (st-hom (st-el {c = c} k)) hE
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
... | inj₁ (t' , (u' , refl)) with stamb-star (st-hom (st-el {c = c} k)) sR
...   | st-hom ()
HomStkU-clash {c = c} k cv | E , (uL , sR) | inj₂ (P , (Q , refl))
  with stamb-star (st-hom (st-el {c = c} k)) sR
... | ()

------------------------------------------------------------------------
-- 2. TERM SIZE and bounded recursion — the tr-case must analyze the
--    STRENGTHENED motive-code (`subTm (single t) cM`), which is not a
--    structural subterm but has exactly `cM`'s size.  We recurse on a
--    Nat bound, structurally.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using ( Nat; zero; suc; _+_ )

infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : {n : Nat} → zero ≤ n
  s≤s : {m n : Nat} → m ≤ n → suc m ≤ suc n

≤-refl : {n : Nat} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : {l m n : Nat} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n     _       = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-suc : {a b : Nat} → a ≤ b → a ≤ suc b
≤-suc z≤n     = z≤n
≤-suc (s≤s p) = s≤s (≤-suc p)

un≤ : {a b : Nat} → suc a ≤ suc b → a ≤ b
un≤ (s≤s p) = p

-- summands EXPLICIT (the `+`-inversion trap: implicit summands leak
-- metas through `with`-abstractions).
≤+ˡ : (a b : Nat) → a ≤ a + b
≤+ˡ zero    b = z≤n
≤+ˡ (suc a) b = s≤s (≤+ˡ a b)

≤+ʳ : (a b : Nat) → b ≤ a + b
≤+ʳ zero    b = ≤-refl
≤+ʳ (suc a) b = ≤-suc (≤+ʳ a b)

-- `sz` is suc-headed by its single top clause, so `sz t ≤ zero` is
-- judgmentally absurd even for neutral `t`.
szb : {Γ : Cx} → RTm Γ → Nat
sz  : {Γ : Cx} → RTm Γ → Nat
sz t = suc (szb t)
szb (var x)        = zero
szb (lam t)        = sz t
szb (app f a)      = sz f + sz a
szb (pair a b)     = sz a + sz b
szb (fst p)        = sz p
szb (snd p)        = sz p
szb ⌜base⌝         = zero
szb (⌜Π⌝ c d)      = sz c + sz d
szb (⌜Σ⌝ c d)      = sz c + sz d
szb (⌜Hom⌝ c a b)  = sz c + sz a + sz b
szb (hrefl c t)    = sz c + sz t
szb (tr d p e)     = sz d + sz p + sz e

szb-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) (t : RTm Γ) → szb (renTm ρ t) ≡ szb t
sz-ren  : {Γ Δ : Cx} (ρ : Ren Γ Δ) (t : RTm Γ) → sz (renTm ρ t) ≡ sz t
sz-ren ρ t = cong suc (szb-ren ρ t)
szb-ren ρ (var x)       = refl
szb-ren ρ (lam t)       = sz-ren _ t
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

------------------------------------------------------------------------
-- 3. CANONICAL SHAPES and the progress verdicts.  There is NO `tr`
--    (and no `var`, `app`, `fst`, `snd`) row in `Canon` — the whole
--    point of the induction is that those always step (or clash).
------------------------------------------------------------------------

data Canon {Γ : Cx} : RTm Γ → Set where
  can-lam   : (s : RTm (Γ ∙))            → Canon (lam s)
  can-pair  : (a b : RTm Γ)              → Canon (pair a b)
  can-cb    :                              Canon ⌜base⌝
  can-cΠ    : (c : RTm Γ) (d : RTm (Γ ∙)) → Canon (⌜Π⌝ c d)
  can-cΣ    : (c : RTm Γ) (d : RTm (Γ ∙)) → Canon (⌜Σ⌝ c d)
  can-cH    : (c a b : RTm Γ)            → Canon (⌜Hom⌝ c a b)
  can-hrefl : (c s : RTm Γ)              → Canon (hrefl c s)

data Prog (t : RTm ε) : Set where
  prog-can  : Canon t → Prog t
  prog-step : {u : RTm ε} → t ⟶ u → Prog t

-- ★ the CODE verdict: pw-able, PERMANENTLY stable, or steps.
data UProg (c : RTm ε) : Set where
  u-pw   : pw? c ≡ true   → UProg c
  u-stk  : stkC? c ≡ true → UProg c
  u-step : {c' : RTm ε} → c ⟶ c' → UProg c

-- (Subj has no `gen-⌜base⌝`; local.)
gen-⌜base⌝ : {Γ : Ctx} {C : RTy ⌊ Γ ⌋} → Γ ⊢ ⌜base⌝ ∷ C → C ≅ᵀ U
gen-⌜base⌝ ⊢⌜base⌝      = crflᵀ
gen-⌜base⌝ (⊢conv d c) = ctrnᵀ (csymᵀ c) (gen-⌜base⌝ d)

-- the J-rules, dispatched by the stable code's SHAPE (the Boolean
-- refutes every other constructor).
jfire : {Γ : Cx} (cM aM : RTm (Γ ∙)) (c₁ s e : RTm Γ) →
        stkC? c₁ ≡ true →
        tr (⌜Hom⌝ cM aM (var vz)) (hrefl c₁ s) e ⟶ e
jfire cM aM ⌜base⌝        s e k = tr-J-base cM aM (var vz) s e
jfire cM aM (⌜Σ⌝ x y)     s e k = tr-J-Σ cM aM (var vz) x y s e
jfire cM aM (⌜Hom⌝ x y z) s e k = tr-J-Hom cM aM (var vz) x y z s e k
jfire cM aM (var _)       s e ()
jfire cM aM (lam _)       s e ()
jfire cM aM (app _ _)     s e ()
jfire cM aM (pair _ _)    s e ()
jfire cM aM (fst _)       s e ()
jfire cM aM (snd _)       s e ()
jfire cM aM (⌜Π⌝ _ _)     s e ()
jfire cM aM (hrefl _ _)   s e ()
jfire cM aM (tr _ _ _)    s e ()

------------------------------------------------------------------------
-- 4. Non-recursive head analyses: canonical Σ'-inhabitants project,
--    everything else at Σ' clashes.
------------------------------------------------------------------------

canΣfst : {p : RTm ε} {A : RTy ε} {B : RTy (ε ∙)} →
          ◇ ⊢ p ∷ Σ' A B → Canon p → Σ (RTm ε) (λ u → fst p ⟶ u)
canΣfst dp (can-pair a b) = _ , βfst a b
canΣfst dp (can-lam s) with gen-lam dp
... | _ , (_ , (cv , _)) = ⊥-elim (ΣΠ-clash cv)
canΣfst dp can-cb = ⊥-elim (ΣU-clash (gen-⌜base⌝ dp))
canΣfst dp (can-cΠ x y) with gen-⌜Π⌝ dp
... | _ , (_ , cv) = ⊥-elim (ΣU-clash cv)
canΣfst dp (can-cΣ x y) with gen-⌜Σ⌝ dp
... | _ , (_ , cv) = ⊥-elim (ΣU-clash cv)
canΣfst dp (can-cH x y z) with gen-⌜Hom⌝ dp
... | _ , (_ , (_ , cv)) = ⊥-elim (ΣU-clash cv)
canΣfst dp (can-hrefl c s) with gen-hrefl dp
... | _ , (_ , cv) = ⊥-elim (HomΣ-clash (csymᵀ cv))

canΣsnd : {p : RTm ε} {A : RTy ε} {B : RTy (ε ∙)} →
          ◇ ⊢ p ∷ Σ' A B → Canon p → Σ (RTm ε) (λ u → snd p ⟶ u)
canΣsnd dp (can-pair a b) = _ , βsnd a b
canΣsnd dp (can-lam s) with gen-lam dp
... | _ , (_ , (cv , _)) = ⊥-elim (ΣΠ-clash cv)
canΣsnd dp can-cb = ⊥-elim (ΣU-clash (gen-⌜base⌝ dp))
canΣsnd dp (can-cΠ x y) with gen-⌜Π⌝ dp
... | _ , (_ , cv) = ⊥-elim (ΣU-clash cv)
canΣsnd dp (can-cΣ x y) with gen-⌜Σ⌝ dp
... | _ , (_ , cv) = ⊥-elim (ΣU-clash cv)
canΣsnd dp (can-cH x y z) with gen-⌜Hom⌝ dp
... | _ , (_ , (_ , cv)) = ⊥-elim (ΣU-clash cv)
canΣsnd dp (can-hrefl c s) with gen-hrefl dp
... | _ , (_ , cv) = ⊥-elim (HomΣ-clash (csymᵀ cv))

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
         UProg (subTm (single tI) cM) →
         Σ (RTm ε) (λ u → tr (⌜Hom⌝ cM aM (var vz)) (lam f) e ⟶ u)
trPwGo cM aM f e {tI = tI} dvM dp sEq (u-pw k) =
  _ , tr-pw cM aM f e
        (trans (cong pw? (sym sEq))
               (trans (pw?-ren vs (subTm (single tI) cM)) k))
trPwGo cM aM f e {tI = tI} dvM dp sEq (u-step {c' = c'} r) =
  _ , ξ-trᵈ (ξ-⌜Hom⌝ᶜ (subst (λ z → z ⟶ renTm vs c') sEq (⟶-ren vs r)))
trPwGo cM aM f e {A} {tI} dvM dp sEq (u-stk k) with gen-lam dp
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

------------------------------------------------------------------------
-- 6. ★★ THE MUTUAL PROGRESS INDUCTION — bounded by term size,
--    structural on the bound.  `prog`: canonical or steps.  `usplit`:
--    pw, permanently stable, or steps.  Eliminator workers produce the
--    step outright (there IS no canonical eliminator form).
------------------------------------------------------------------------

mutual
  prog : (n : Nat) {t : RTm ε} {T : RTy ε} → ◇ ⊢ t ∷ T → sz t ≤ n → Prog t
  prog zero    d ()
  prog (suc m) {t = var x}       d le = ⊥-elim (noVar x)
  prog (suc m) {t = lam s}       d le = prog-can (can-lam s)
  prog (suc m) {t = pair a b}    d le = prog-can (can-pair a b)
  prog (suc m) {t = ⌜base⌝}      d le = prog-can can-cb
  prog (suc m) {t = ⌜Π⌝ c cd}    d le = prog-can (can-cΠ c cd)
  prog (suc m) {t = ⌜Σ⌝ c cd}    d le = prog-can (can-cΣ c cd)
  prog (suc m) {t = ⌜Hom⌝ c a b} d le = prog-can (can-cH c a b)
  prog (suc m) {t = hrefl c s}   d le = prog-can (can-hrefl c s)
  prog (suc m) {t = app f a}     d le with appS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = fst p}       d le with fstS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = snd p}       d le with sndS m d (un≤ le)
  ... | _ , r = prog-step r
  prog (suc m) {t = tr dM p e}   d le with trS m d (un≤ le)
  ... | _ , r = prog-step r

  -- ★ CODE CANONICITY, progress form.
  usplit : (n : Nat) {c : RTm ε} → ◇ ⊢ c ∷ U → sz c ≤ n → UProg c
  usplit zero    d ()
  usplit (suc m) {c = var x}   d le = ⊥-elim (noVar x)
  usplit (suc m) {c = ⌜base⌝}  d le = u-stk refl
  usplit (suc m) {c = ⌜Π⌝ x y} d le = u-pw refl
  usplit (suc m) {c = ⌜Σ⌝ x y} d le = u-stk refl
  usplit (suc m) {c = ⌜Hom⌝ x a b} d le with gen-⌜Hom⌝ d
  ... | dx , _
        with usplit m dx
               (≤-trans (≤-trans (≤+ˡ (sz x) (sz a))
                                 (≤+ˡ (sz x + sz a) (sz b)))
                        (un≤ le))
  ...   | u-pw k   = u-pw k
  ...   | u-stk k  = u-stk k
  ...   | u-step r = u-step (ξ-⌜Hom⌝ᶜ r)
  usplit (suc m) {c = lam s} d le with gen-lam d
  ... | _ , (_ , (cv , _)) = ⊥-elim (ΠU-clash (csymᵀ cv))
  usplit (suc m) {c = pair a b} d le with gen-pair d
  ... | _ , (_ , (cv , _)) = ⊥-elim (ΣU-clash (csymᵀ cv))
  usplit (suc m) {c = hrefl x s} d le with gen-hrefl d
  ... | _ , (_ , cv) = ⊥-elim (HomU-clash (csymᵀ cv))
  usplit (suc m) {c = app f a} d le with appS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = fst p} d le with fstS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = snd p} d le with sndS m d (un≤ le)
  ... | _ , r = u-step r
  usplit (suc m) {c = tr dM p e} d le with trS m d (un≤ le)
  ... | _ , r = u-step r

  appS : (m : Nat) {f a : RTm ε} {T : RTy ε} → ◇ ⊢ app f a ∷ T →
         sz f + sz a ≤ m → Σ (RTm ε) (λ u → app f a ⟶ u)
  appS m {f} {a} dv q with gen-app dv
  ... | A , (B , (df , (da , cB))) with prog m df (≤-trans (≤+ˡ (sz f) (sz a)) q)
  ...   | prog-step r = _ , ξ-appˡ r
  ...   | prog-can cn = canΠ m df cn (≤-trans (≤+ˡ (sz f) (sz a)) q) a

  -- canonical Π-inhabitants β-reduce or (hrefl at a pw-able code)
  -- unfold; the stable-code hrefl and the other shapes are untypeable.
  canΠ : (m : Nat) {f : RTm ε} {A : RTy ε} {B : RTy (ε ∙)} →
         ◇ ⊢ f ∷ Π A B → Canon f → sz f ≤ m →
         (a : RTm ε) → Σ (RTm ε) (λ u → app f a ⟶ u)
  canΠ m df (can-lam s) le a = _ , β s a
  canΠ m df (can-pair x y) le a with gen-pair df
  ... | _ , (_ , (cv , _)) = ⊥-elim (ΣΠ-clash (csymᵀ cv))
  canΠ m df can-cb le a = ⊥-elim (ΠU-clash (gen-⌜base⌝ df))
  canΠ m df (can-cΠ x y) le a with gen-⌜Π⌝ df
  ... | _ , (_ , cv) = ⊥-elim (ΠU-clash cv)
  canΠ m df (can-cΣ x y) le a with gen-⌜Σ⌝ df
  ... | _ , (_ , cv) = ⊥-elim (ΠU-clash cv)
  canΠ m df (can-cH x y z) le a with gen-⌜Hom⌝ df
  ... | _ , (_ , (_ , cv)) = ⊥-elim (ΠU-clash cv)
  canΠ m df (can-hrefl c₁ s) le a with gen-hrefl df
  ... | dc₁ , (ds , cvh)
        with usplit m dc₁ (≤-trans (≤-suc (≤+ˡ (sz c₁) (sz s))) le)
  ...   | u-pw k   = _ , ξ-appˡ (hrefl-pw c₁ s k)
  ...   | u-step r = _ , ξ-appˡ (ξ-hreflᶜ r)
  ...   | u-stk k  = ⊥-elim (HomStkΠ-clash k (csymᵀ cvh))

  fstS : (m : Nat) {p : RTm ε} {T : RTy ε} → ◇ ⊢ fst p ∷ T →
         sz p ≤ m → Σ (RTm ε) (λ u → fst p ⟶ u)
  fstS m dv q with gen-fst dv
  ... | A , (B , (dp , cA)) with prog m dp q
  ...   | prog-step r = _ , ξ-fst r
  ...   | prog-can cn = canΣfst dp cn

  sndS : (m : Nat) {p : RTm ε} {T : RTy ε} → ◇ ⊢ snd p ∷ T →
         sz p ≤ m → Σ (RTm ε) (λ u → snd p ⟶ u)
  sndS m dv q with gen-snd dv
  ... | A , (B , (dp , cA)) with prog m dp q
  ...   | prog-step r = _ , ξ-snd r
  ...   | prog-can cn = canΣsnd dp cn

  -- ★ CLOSED `tr`s ALWAYS STEP.  The dispatch: path steps → ξ; path
  -- canonical → per the motive.
  trS : (m : Nat) {dM : RTm (ε ∙)} {p e : RTm ε} {T : RTy ε} →
        ◇ ⊢ tr dM p e ∷ T → sz dM + sz p + sz e ≤ m →
        Σ (RTm ε) (λ u → tr dM p e ⟶ u)
  trS m {dM} {p} {e} dv q with gen-tr dv
  ... | tgU inv =
        trUS m inv
          (≤-trans (≤-trans (≤+ʳ (sz dM) (sz p))
                            (≤+ˡ (sz dM + sz p) (sz e))) q)
  ... | tgC (mkTrInv cM aM refl A tI uI dcM daM dvM hcM haM dt du dp de cC) =
        trCS m cM aM e dcM hcM dt dvM dp
          (≤-trans (≤-trans (≤+ʳ (sz dM) (sz p))
                            (≤+ˡ (sz dM + sz p) (sz e))) q)
          (≤-trans (≤-suc (≤-trans (≤+ˡ (sz cM) (sz aM))
                                   (≤+ˡ (sz cM + sz aM) (suc zero))))
                   (≤-trans (≤-trans (≤+ˡ (sz dM) (sz p))
                                     (≤+ˡ (sz dM + sz p) (sz e))) q))

  -- the TAUT motive (`var vz`, ambient `U`).
  trUS : (m : Nat) {dM : RTm (ε ∙)} {p e : RTm ε} {T : RTy ε} →
         TrInvU ◇ dM p e T → sz p ≤ m →
         Σ (RTm ε) (λ u → tr dM p e ⟶ u)
  trUS m {p = p} {e = e} (mkTrInvU refl tI uI dt du dp de cC) lep
    with prog m dp lep
  ... | prog-step r = _ , ξ-trᵖ r
  ... | prog-can (can-lam f) = _ , tr-taut f e
  ... | prog-can (can-hrefl c₁ s) with gen-hrefl dp
  ...   | dc₁ , (ds , cvh)
          with usplit m dc₁ (≤-trans (≤-suc (≤+ˡ (sz c₁) (sz s))) lep)
  ...     | u-pw k   = _ , ξ-trᵖ (hrefl-pw c₁ s k)
  ...     | u-step r = _ , ξ-trᵖ (ξ-hreflᶜ r)
  ...     | u-stk k  = ⊥-elim (HomStkU-clash k cvh)
  trUS m {p = p} {e = e} (mkTrInvU refl tI uI dt du dp de cC) lep
    | prog-can (can-pair a b) with gen-pair dp
  ... | _ , (_ , (cv , _)) = ⊥-elim (HomΣ-clash cv)
  trUS m (mkTrInvU refl tI uI dt du dp de cC) lep
    | prog-can can-cb = ⊥-elim (HomU-clash (gen-⌜base⌝ dp))
  trUS m (mkTrInvU refl tI uI dt du dp de cC) lep
    | prog-can (can-cΠ x y) with gen-⌜Π⌝ dp
  ... | _ , (_ , cv) = ⊥-elim (HomU-clash cv)
  trUS m (mkTrInvU refl tI uI dt du dp de cC) lep
    | prog-can (can-cΣ x y) with gen-⌜Σ⌝ dp
  ... | _ , (_ , cv) = ⊥-elim (HomU-clash cv)
  trUS m (mkTrInvU refl tI uI dt du dp de cC) lep
    | prog-can (can-cH x y z) with gen-⌜Hom⌝ dp
  ... | _ , (_ , (_ , cv)) = ⊥-elim (HomU-clash cv)

  -- the CODE motive (`⌜Hom⌝ cM aM (var vz)`).
  trCS : (m : Nat) (cM aM : RTm (ε ∙)) (e : RTm ε)
         {A : RTy ε} {tI uI : RTm ε} {p : RTm ε} →
         ((◇ ▹ A) ⊢ cM ∷ U) → occTm vz cM ≡ false →
         (◇ ⊢ tI ∷ A) → ((◇ ▹ A) ⊢ var vz ∷ El cM) →
         (◇ ⊢ p ∷ Hom A tI uI) →
         sz p ≤ m → sz cM ≤ m →
         Σ (RTm ε) (λ u → tr (⌜Hom⌝ cM aM (var vz)) p e ⟶ u)
  trCS m cM aM e dcM hcM dt dvM dp lep lecM with prog m dp lep
  ... | prog-step r = _ , ξ-trᵖ r
  ... | prog-can (can-lam f) = trPw m cM aM f e dcM hcM dt dvM dp lecM
  ... | prog-can (can-hrefl c₁ s) with gen-hrefl dp
  ...   | dc₁ , (ds , cvh)
          with usplit m dc₁ (≤-trans (≤-suc (≤+ˡ (sz c₁) (sz s))) lep)
  ...     | u-pw k   = _ , ξ-trᵖ (hrefl-pw c₁ s k)
  ...     | u-step r = _ , ξ-trᵖ (ξ-hreflᶜ r)
  ...     | u-stk k  = _ , jfire cM aM c₁ s e k
  trCS m cM aM e dcM hcM dt dvM dp lep lecM
    | prog-can (can-pair a b) with gen-pair dp
  ... | _ , (_ , (cv , _)) = ⊥-elim (HomΣ-clash cv)
  trCS m cM aM e dcM hcM dt dvM dp lep lecM
    | prog-can can-cb = ⊥-elim (HomU-clash (gen-⌜base⌝ dp))
  trCS m cM aM e dcM hcM dt dvM dp lep lecM
    | prog-can (can-cΠ x y) with gen-⌜Π⌝ dp
  ... | _ , (_ , cv) = ⊥-elim (HomU-clash cv)
  trCS m cM aM e dcM hcM dt dvM dp lep lecM
    | prog-can (can-cΣ x y) with gen-⌜Σ⌝ dp
  ... | _ , (_ , cv) = ⊥-elim (HomU-clash cv)
  trCS m cM aM e dcM hcM dt dvM dp lep lecM
    | prog-can (can-cH x y z) with gen-⌜Hom⌝ dp
  ... | _ , (_ , (_ , cv)) = ⊥-elim (HomU-clash cv)

  -- ★★ THE POINTWISE CASE: strengthen the motive-code, run the split
  -- on the CLOSED instance, dispatch.  (`sz` is renaming-invariant, so
  -- the strengthened code fits the SAME bound — the reason this whole
  -- induction is size-based.)
  trPw : (m : Nat) (cM aM f : RTm (ε ∙)) (e : RTm ε)
         {A : RTy ε} {tI uI : RTm ε} →
         ((◇ ▹ A) ⊢ cM ∷ U) → occTm vz cM ≡ false →
         (◇ ⊢ tI ∷ A) → ((◇ ▹ A) ⊢ var vz ∷ El cM) →
         (◇ ⊢ lam f ∷ Hom A tI uI) →
         sz cM ≤ m →
         Σ (RTm ε) (λ u → tr (⌜Hom⌝ cM aM (var vz)) (lam f) e ⟶ u)
  trPw m cM aM f e {tI = tI} dcM hcM dt dvM dp lecM =
    trPwGo cM aM f e dvM dp strengthEq
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
-- of type `U` is pointwise-able or permanently stable.
codeCanon : {c : RTm ε} → ◇ ⊢ c ∷ U → IsNormal c →
            (pw? c ≡ true) ⊎ (stkC? c ≡ true)
codeCanon d nrm with codeSplit d
... | u-pw k   = inj₁ k
... | u-stk k  = inj₂ k
... | u-step r = ⊥-elim (nrm r)

-- ★ PATH CANONICITY (item 2): a closed normal path at a `Hom` type is
-- an `hrefl` or a lambda.
pathCanon : {p : RTm ε} {A : RTy ε} {t u : RTm ε} →
            ◇ ⊢ p ∷ Hom A t u → IsNormal p →
            (Σ (RTm ε) (λ c → Σ (RTm ε) (λ s → p ≡ hrefl c s)))
            ⊎ (Σ (RTm (ε ∙)) (λ f → p ≡ lam f))
pathCanon d nrm with progress d
... | prog-step r = ⊥-elim (nrm r)
... | prog-can (can-hrefl c s) = inj₁ (c , (s , refl))
... | prog-can (can-lam f)     = inj₂ (f , refl)
... | prog-can (can-pair a b) with gen-pair d
...   | _ , (_ , (cv , _)) = ⊥-elim (HomΣ-clash cv)
pathCanon d nrm | prog-can can-cb = ⊥-elim (HomU-clash (gen-⌜base⌝ d))
pathCanon d nrm | prog-can (can-cΠ x y) with gen-⌜Π⌝ d
... | _ , (_ , cv) = ⊥-elim (HomU-clash cv)
pathCanon d nrm | prog-can (can-cΣ x y) with gen-⌜Σ⌝ d
... | _ , (_ , cv) = ⊥-elim (HomU-clash cv)
pathCanon d nrm | prog-can (can-cH x y z) with gen-⌜Hom⌝ d
... | _ , (_ , (_ , cv)) = ⊥-elim (HomU-clash cv)

-- ★ TR-PROGRESS (item 3): a closed well-typed `tr` ALWAYS steps —
-- transport never sticks on closed terms.
trProgress : {dM : RTm (ε ∙)} {p e : RTm ε} {T : RTy ε} →
             ◇ ⊢ tr dM p e ∷ T → Σ (RTm ε) (λ u → tr dM p e ⟶ u)
trProgress {dM} {p} {e} d = trS (sz dM + sz p + sz e) d ≤-refl

-- no canonical shape types at `base`.
canBase⊥ : {t : RTm ε} → ◇ ⊢ t ∷ base → Canon t → ⊥
canBase⊥ d (can-lam s) with gen-lam d
... | _ , (_ , (cv , _)) = Πbase-clash (csymᵀ cv)
canBase⊥ d (can-pair a b) with gen-pair d
... | _ , (_ , (cv , _)) = Σbase-clash (csymᵀ cv)
canBase⊥ d can-cb = Ubase-clash (csymᵀ (gen-⌜base⌝ d))
canBase⊥ d (can-cΠ x y) with gen-⌜Π⌝ d
... | _ , (_ , cv) = Ubase-clash (csymᵀ cv)
canBase⊥ d (can-cΣ x y) with gen-⌜Σ⌝ d
... | _ , (_ , cv) = Ubase-clash (csymᵀ cv)
canBase⊥ d (can-cH x y z) with gen-⌜Hom⌝ d
... | _ , (_ , (_ , cv)) = Ubase-clash (csymᵀ cv)
canBase⊥ d (can-hrefl c s) with gen-hrefl d
... | _ , (_ , cv) = Hombase-clash (csymᵀ cv)

-- ★★ CONSISTENCY of the full W2/W2b kernel: `base` has no closed
-- inhabitant.  Normalize (`wnorm`, the fundamental theorem), preserve
-- the typing (`sr*`), and the normal form is canonical (impossible at
-- `base`) or steps (impossible for a normal form).
consistency : {t : RTm ε} → ◇ ⊢ t ∷ base → ⊥
consistency d with wnorm c-◇ d
... | mkWN nfm rd nrm snf with progress (sr* d rd)
...   | prog-step r = nrm r
...   | prog-can cn = canBase⊥ (sr* d rd) cn
