-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE ELABORATOR: surface → annotated core.
--                      (PLAN-BIDI S6)
--
-- ★ UNTRUSTED, by design (PLAN-BIDI §0, the de Bruijn criterion).  The
--   elaborator only PROPOSES an annotated term; `elaborate` re-checks it
--   with the certifying `Algorithm/CheckA` and returns CheckA's derivation.
--   So nothing here needs a proof, and an elaborator bug can only make a
--   term fail, never make a false derivation.  It may be incomplete; it
--   cannot be unsound.
--
-- ★ BIDIRECTIONAL, as ONE function: `el Γ t (just T)` checks `t` against
--   `T`, `el Γ t nothing` infers.  A hole `□`/`□ᵀ` in an ANNOTATION
--   position is filled from
--     · the expected type: `lam □ t` against `Π A B` takes `A`; `pair`,
--       `con`, `dι`/`dσ`/`dρ`, `fzero`/`fsuc` likewise;
--     · a premise's inferred type: `tr`/`jsub`/`ap` read their ambient and
--       endpoints off the path's `Hom`/`Id`; `ielim` its index code off
--       the scrutinee's `IMu`; `psplit` its `A B` off the pair's `Σ'`;
--       `fcase`/`fsuc` the bound off a `Fin`;
--     · for a MOTIVE in checking mode, the CONSTANT motive — the expected
--       type, weakened past the motive's binders.  Dependent motives are
--       written out.
--
-- ★ TYPES ARE KEPT ANNOTATED.  A hole is filled with an ANNOTATED type, so
--   the elaborator never goes through erasure: it has its own weak-head
--   evaluator on `ATm`/`ATy` (`whTm`/`whTy` — β, projections, `natrec`,
--   δ through the signature's annotated bodies, and `El` of a code), with
--   fuel.  Exhausted fuel only makes elaboration fail.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import normalizer.Syntax.Types using ( Σ; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; vz; vs )
open import DirectedHoTT.Spec.Typing using ( ⊢ctx_; _⊢ty_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature using ( Sig; SigOK )
import DirectedHoTT.Algorithm.Surface as S
open S using ( STy; STm )
open import DirectedHoTT.Algorithm.DecEq using ( Dec; yes; no )

-- `abody d` is entry d's ANNOTATED body — only a HINT for weak-head
-- evaluation (the checker re-validates everything); `fuel` bounds it
module DirectedHoTT.Algorithm.Elab (Sg : Sig) (abody : ℕ → ATm ε) (fuel : ℕ) where
open Sig Sg
open Era body
open import DirectedHoTT.Spec.AnnotatedDesc body
open import DirectedHoTT.Spec.TypingA Sg using ( ACtx; ◇ᴬ; _▹ᴬ_; ⌊_⌋ᴬ; ⌈_⌉ᶜ; _⊢ᴬ_∷_; nrsᴬ )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- 0. Maybe plumbing.
------------------------------------------------------------------------

infixl 1 _>>=_
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>= f = f a
nothing >>= f = nothing

infixl 3 _<|>_
_<|>_ : {A : Set} → Maybe A → Maybe A → Maybe A
just a  <|> _ = just a
nothing <|> m = m

------------------------------------------------------------------------
-- 1. Weak-head evaluation on ANNOTATED terms (fuel-bounded, untrusted).
------------------------------------------------------------------------

whTm : ℕ → ATm Γ → ATm Γ
whTm zero t = t
whTm (suc k) (ref d) = whTm k (εwkTmᴬ (abody d))
whTm (suc k) (app f u) with whTm k f
... | lam A t = whTm k (subTmᴬ (singleᴬ u) t)
... | f'      = app f' u
whTm (suc k) (fst p) with whTm k p
... | pair A B a b = whTm k a
... | p'           = fst p'
whTm (suc k) (snd p) with whTm k p
... | pair A B a b = whTm k b
... | p'           = snd p'
whTm (suc k) (natrec M z s n) with whTm k n
... | nzero  = whTm k z
... | nsuc m = whTm k (subTmᴬ (single2ᴬ m (natrec M z s m)) s)
... | n'     = natrec M z s n'
whTm (suc k) t = t

-- `El` of a code decodes to its type former
decode : ATm Γ → ATy Γ
decode ⌜base⌝        = base
decode (⌜Π⌝ c d)     = Π (El c) (El d)
decode (⌜Σ⌝ c d)     = Σ' (El c) (El d)
decode (⌜Hom⌝ c a b) = Hom (El c) a b
decode (⌜Id⌝ c a b)  = Id (El c) a b
decode ⌜Nat⌝         = Nat
decode ⌜Unit⌝        = Unit
decode (⌜IMu⌝ I D i) = IMu I D i
decode (⌜Fin⌝ n)     = Fin n
decode c             = El c

whTy : ATy Γ → ATy Γ
whTy (El c) = decode (whTm fuel c)
whTy A      = A

------------------------------------------------------------------------
-- 2. Views of a (weak-head) type.
------------------------------------------------------------------------

Pair : Set → Set → Set
Pair A B = Σ A (λ _ → B)

Triple : Set → Set → Set → Set
Triple A B C = Σ A (λ _ → Σ B (λ _ → C))

piV : ATy Γ → Maybe (Pair (ATy Γ) (ATy (Γ ∙)))
piV A with whTy A
... | Π X Y = just (X , Y)
... | _     = nothing

sgV : ATy Γ → Maybe (Pair (ATy Γ) (ATy (Γ ∙)))
sgV A with whTy A
... | Σ' X Y = just (X , Y)
... | _      = nothing

homV : ATy Γ → Maybe (Triple (ATy Γ) (ATm Γ) (ATm Γ))
homV A with whTy A
... | Hom X t u = just (X , (t , u))
... | _         = nothing

idV : ATy Γ → Maybe (Triple (ATy Γ) (ATm Γ) (ATm Γ))
idV A with whTy A
... | Id X t u = just (X , (t , u))
... | _        = nothing

muV : ATy Γ → Maybe (Triple (ATm Γ) (ATm Γ) (ATm Γ))
muV A with whTy A
... | IMu I D i = just (I , (D , i))
... | _         = nothing

descV : ATy Γ → Maybe (ATm Γ)
descV A with whTy A
... | Desc I = just I
... | _      = nothing

finV : ATy Γ → Maybe ℕ
finV A with whTy A
... | Fin n = just n
... | _     = nothing

finSV : ATy Γ → Maybe ℕ
finSV A with whTy A
... | Fin (suc n) = just n
... | _           = nothing

-- the code of an `El` type
elV : ATy Γ → Maybe (ATm Γ)
elV (El c) = just c
elV _      = nothing

------------------------------------------------------------------------
-- 3. The elaborator.
------------------------------------------------------------------------

-- the elaborator's context: a type for every variable
Env : Cx → Set
Env Γ = Var Γ → ATy Γ

infixl 5 _▸_
_▸_ : Env Γ → ATy Γ → Env (Γ ∙)
(e ▸ A) vz     = renTyᴬ vs A
(e ▸ A) (vs x) = renTyᴬ vs (e x)

envᴬ : (Γ : ACtx) → Env ⌊ Γ ⌋ᴬ
envᴬ ◇ᴬ ()
envᴬ (Γ ▹ᴬ A) = envᴬ Γ ▸ A

record Inf (Γ : Cx) : Set where
  constructor _∶_
  field
    tm : ATm Γ
    ty : ATy Γ
open Inf

-- a motive's context for the inductive families: index, then scrutinee
motEnv : Env Γ → ATm Γ → ATm Γ → Env ((Γ ∙) ∙)
motEnv e I D = (e ▸ El I) ▸ IMu (renTmᴬ vs I) (renTmᴬ vs D) (var vz)

-- the constant motive: the expected type, past `k` binders
wk1 : ATy Γ → ATy (Γ ∙)
wk1 = renTyᴬ vs

wk2 : ATy Γ → ATy ((Γ ∙) ∙)
wk2 = renTyᴬ (λ x → vs (vs x))

elT : Env Γ → STy Γ → Maybe (ATy Γ)
el  : Env Γ → STm Γ → Maybe (ATy Γ) → Maybe (Inf Γ)

chk : Env Γ → STm Γ → ATy Γ → Maybe (ATm Γ)
chk e t A = el e t (just A) >>= λ r → just (tm r)

inf : Env Γ → STm Γ → Maybe (Inf Γ)
inf e t = el e t nothing

-- an annotation: a hole takes the proposal, anything else is elaborated
annT : Env Γ → STy Γ → Maybe (ATy Γ) → Maybe (ATy Γ)
annT e S.□ᵀ p = p
annT e A    p = elT e A

annM : Env Γ → STm Γ → Maybe (ATm Γ) → Maybe (ATy Γ) → Maybe (ATm Γ)
annM e S.□ p T        = p
annM e t p (just T)   = chk e t T
annM e t p nothing    = inf e t >>= λ r → just (tm r)

-- a motive: written out, or (checking mode only) the constant one
annMot : {Δ : Cx} → Env Δ → STy Δ → Maybe (ATy Δ) → Maybe (ATy Δ)
annMot = annT

fstM : {A B : Set} → Maybe (Pair A B) → Maybe A
fstM m = m >>= λ { (a , _) → just a }

sndM : {A B : Set} → Maybe (Pair A B) → Maybe B
sndM m = m >>= λ { (_ , b) → just b }

p1 : {A B C : Set} → Maybe (Triple A B C) → Maybe A
p1 m = m >>= λ { (a , _) → just a }
p2 : {A B C : Set} → Maybe (Triple A B C) → Maybe B
p2 m = m >>= λ { (_ , (b , _)) → just b }
p3 : {A B C : Set} → Maybe (Triple A B C) → Maybe C
p3 m = m >>= λ { (_ , (_ , c)) → just c }

-- the expectation, viewed
_⟫_ : {A : Set} → Maybe (ATy Γ) → (ATy Γ → Maybe A) → Maybe A
mT ⟫ v = mT >>= v

-- ★ types
elT e S.base    = just base
elT e S.U       = just U
elT e S.Unit    = just Unit
elT e S.Nat     = just Nat
elT e (S.Fin n) = just (Fin n)
elT e (S.Π A B) = elT e A >>= λ A' → elT (e ▸ A') B >>= λ B' → just (Π A' B')
elT e (S.Σ' A B) = elT e A >>= λ A' → elT (e ▸ A') B >>= λ B' → just (Σ' A' B')
elT e (S.El c)  = chk e c U >>= λ c' → just (El c')
elT e (S.Hom A t u) =
  elT e A >>= λ A' → chk e t A' >>= λ t' → chk e u A' >>= λ u' → just (Hom A' t' u')
elT e (S.Id A t u) =
  elT e A >>= λ A' → chk e t A' >>= λ t' → chk e u A' >>= λ u' → just (Id A' t' u')
elT e (S.IMu I D i) =
  chk e I U >>= λ I' → chk e D (DescFᴬ I') >>= λ D' → chk e i (El I') >>= λ i' →
  just (IMu I' D' i')
elT e (S.Desc I) = chk e I U >>= λ I' → just (Desc I')
elT e (S.DIh I D M C p) =
  annM e I (inf e C >>= λ r → descV (ty r)) (just U) >>= λ I' →
  chk e D (DescFᴬ I') >>= λ D' → elT (motEnv e I' D') M >>= λ M' →
  chk e C (Desc I') >>= λ C' → chk e p (El (dpay I' D' C')) >>= λ p' →
  just (DIh I' D' M' C' p')
elT e S.□ᵀ = nothing

-- ★ terms
el e (S.var x) mT = just (var x ∶ e x)
el e (S.ref d) mT = just (ref d ∶ εwkTyᴬ (type d))
el e (S.the A t) mT = elT e A >>= λ A' → chk e t A' >>= λ t' → just (t' ∶ A')
el e S.□ mT = nothing
el e (S.lam A t) mT =
  annT e A (fstM (mT ⟫ piV)) >>= λ A' →
  el (e ▸ A') t (sndM (mT ⟫ piV)) >>= λ r →
  just (lam A' (tm r) ∶ Π A' (ty r))
el e (S.app t u) mT =
  inf e t >>= λ r → piV (ty r) >>= λ { (A , B) →
  chk e u A >>= λ u' → just (app (tm r) u' ∶ subTyᴬ (singleᴬ u') B) }
el e (S.pair A B a b) mT =
  annT e A (fstM (mT ⟫ sgV)) >>= λ A' →
  chk e a A' >>= λ a' →
  -- no family given or expected: the non-dependent one, from `b`
  (annT (e ▸ A') B (sndM (mT ⟫ sgV)) >>= λ B' →
     chk e b (subTyᴬ (singleᴬ a') B') >>= λ b' → just (pair A' B' a' b' ∶ Σ' A' B'))
  <|> (inf e b >>= λ r → just (pair A' (wk1 (ty r)) a' (tm r) ∶ Σ' A' (wk1 (ty r))))
el e (S.absurd c x) mT =
  chk e c U >>= λ c' → chk e x base >>= λ x' → just (absurd c' x' ∶ El c')
el e (S.ordtr a t u p q) mT =
  chk e a Nat >>= λ a' → chk e t Nat >>= λ t' → chk e u Nat >>= λ u' →
  chk e p (Hom Nat a' t') >>= λ p' → chk e q (Hom Nat t' u') >>= λ q' →
  just (ordtr a' t' u' p' q' ∶ Hom Nat a' u')
el e (S.fst p) mT =
  inf e p >>= λ r → sgV (ty r) >>= λ { (A , B) → just (fst (tm r) ∶ A) }
el e (S.snd p) mT =
  inf e p >>= λ r → sgV (ty r) >>= λ { (A , B) →
  just (snd (tm r) ∶ subTyᴬ (singleᴬ (fst (tm r))) B) }
el e S.⌜base⌝ mT = just (⌜base⌝ ∶ U)
el e (S.⌜Π⌝ c d) mT =
  chk e c U >>= λ c' → chk (e ▸ El c') d U >>= λ d' → just (⌜Π⌝ c' d' ∶ U)
el e (S.⌜Σ⌝ c d) mT =
  chk e c U >>= λ c' → chk (e ▸ El c') d U >>= λ d' → just (⌜Σ⌝ c' d' ∶ U)
el e (S.⌜Hom⌝ c a b) mT =
  chk e c U >>= λ c' → chk e a (El c') >>= λ a' → chk e b (El c') >>= λ b' →
  just (⌜Hom⌝ c' a' b' ∶ U)
el e (S.⌜Id⌝ c a b) mT =
  chk e c U >>= λ c' → chk e a (El c') >>= λ a' → chk e b (El c') >>= λ b' →
  just (⌜Id⌝ c' a' b' ∶ U)
el e (S.hrefl c t) mT =
  chk e c U >>= λ c' → chk e t (El c') >>= λ t' → just (hrefl c' t' ∶ Hom (El c') t' t')
el e (S.idrefl c t) mT =
  chk e c U >>= λ c' → chk e t (El c') >>= λ t' → just (idrefl c' t' ∶ Id (El c') t' t')
-- ★ the path formers read their ambient and endpoints off the path
el e (S.tr A t u d p x) mT =
  inf e p >>= λ rp →
  annT e A (p1 (homV (ty rp))) >>= λ A' →
  annM e t (p2 (homV (ty rp))) (just A') >>= λ t' →
  annM e u (p3 (homV (ty rp))) (just A') >>= λ u' →
  chk (e ▸ A') d U >>= λ d' →
  chk e x (El (subTmᴬ (singleᴬ t') d')) >>= λ x' →
  just (tr A' t' u' d' (tm rp) x' ∶ El (subTmᴬ (singleᴬ u') d'))
el e (S.ap cA t u cB b p) mT =
  inf e p >>= λ rp →
  annM e cA (p1 (homV (ty rp)) >>= elV) (just U) >>= λ cA' →
  annM e t (p2 (homV (ty rp))) (just (El cA')) >>= λ t' →
  annM e u (p3 (homV (ty rp))) (just (El cA')) >>= λ u' →
  chk e cB U >>= λ cB' →
  chk (e ▸ El cA') b (El (renTmᴬ vs cB')) >>= λ b' →
  just (ap cA' t' u' cB' b' (tm rp)
        ∶ Hom (El cB') (subTmᴬ (singleᴬ t') b') (subTmᴬ (singleᴬ u') b'))
el e (S.jsub A t u d p x) mT =
  inf e p >>= λ rp →
  annT e A (p1 (idV (ty rp))) >>= λ A' →
  annM e t (p2 (idV (ty rp))) (just A') >>= λ t' →
  annM e u (p3 (idV (ty rp))) (just A') >>= λ u' →
  chk (e ▸ A') d U >>= λ d' →
  chk e x (El (subTmᴬ (singleᴬ t') d')) >>= λ x' →
  just (jsub A' t' u' d' (tm rp) x' ∶ El (subTmᴬ (singleᴬ u') d'))
el e S.unit mT = just (unit ∶ Unit)
el e S.nzero mT = just (nzero ∶ Nat)
el e (S.nsuc n) mT = chk e n Nat >>= λ n' → just (nsuc n' ∶ Nat)
el e (S.natrec M z s n) mT =
  annMot (e ▸ Nat) M (mT >>= λ T → just (wk1 T)) >>= λ M' →
  chk e z (subTyᴬ (singleᴬ nzero) M') >>= λ z' →
  chk ((e ▸ Nat) ▸ M') s (subTyᴬ nrsᴬ M') >>= λ s' →
  chk e n Nat >>= λ n' →
  just (natrec M' z' s' n' ∶ subTyᴬ (singleᴬ n') M')
el e S.⌜Nat⌝ mT = just (⌜Nat⌝ ∶ U)
el e S.⌜Unit⌝ mT = just (⌜Unit⌝ ∶ U)
el e (S.⌜IMu⌝ I D i) mT =
  chk e I U >>= λ I' → chk e D (DescFᴬ I') >>= λ D' → chk e i (El I') >>= λ i' →
  just (⌜IMu⌝ I' D' i' ∶ U)
el e (S.⌜Fin⌝ n) mT = just (⌜Fin⌝ n ∶ U)
-- ★ the levitated formers: index code (description, index) from the
--   expected type or the scrutinee
el e (S.con I D i p) mT =
  annM e I (p1 (mT ⟫ muV)) (just U) >>= λ I' →
  annM e D (p2 (mT ⟫ muV)) (just (DescFᴬ I')) >>= λ D' →
  annM e i (p3 (mT ⟫ muV)) (just (El I')) >>= λ i' →
  chk e p (El (dpay I' D' (app D' i'))) >>= λ p' →
  just (con I' D' i' p' ∶ IMu I' D' i')
el e (S.ielim I D M i x t) mT =
  annM e I (inf e t >>= λ r → p1 (muV (ty r))) (just U) >>= λ I' →
  chk e D (DescFᴬ I') >>= λ D' →
  annMot (motEnv e I' D') M (mT >>= λ T → just (wk2 T)) >>= λ M' →
  chk e x (MethTyᴬ I' D' M') >>= λ x' →
  chk e i (El I') >>= λ i' →
  chk e t (IMu I' D' i') >>= λ t' →
  just (ielim I' D' M' i' x' t' ∶ iinstᴬ i' t' M')
el e (S.dι I) mT =
  annM e I (mT ⟫ descV) (just U) >>= λ I' → just (dι I' ∶ Desc I')
el e (S.dσ I Sx f) mT =
  annM e I (mT ⟫ descV) (just U) >>= λ I' →
  chk e Sx U >>= λ S' → chk e f (Π (El S') (Desc (renTmᴬ vs I'))) >>= λ f' →
  just (dσ I' S' f' ∶ Desc I')
el e (S.dρ I j C) mT =
  annM e I ((mT ⟫ descV) <|> (inf e C >>= λ r → descV (ty r))) (just U) >>= λ I' →
  chk e j (El I') >>= λ j' → chk e C (Desc I') >>= λ C' →
  just (dρ I' j' C' ∶ Desc I')
el e (S.dpay I D C) mT =
  chk e I U >>= λ I' → chk e D (DescFᴬ I') >>= λ D' → chk e C (Desc I') >>= λ C' →
  just (dpay I' D' C' ∶ U)
el e (S.dih I D M x C p) mT =
  annM e I (inf e C >>= λ r → descV (ty r)) (just U) >>= λ I' →
  chk e D (DescFᴬ I') >>= λ D' →
  elT (motEnv e I' D') M >>= λ M' →
  chk e x (MethTyᴬ I' D' M') >>= λ x' →
  chk e C (Desc I') >>= λ C' →
  chk e p (El (dpay I' D' C')) >>= λ p' →
  just (dih I' D' M' x' C' p' ∶ DIh I' D' M' C' p')
el e (S.fzero n) mT = just (fzero n ∶ Fin (suc n))
el e (S.fsuc n t) mT =
  ((mT ⟫ finSV) >>= λ k → chk e t (Fin k) >>= λ t' → just (fsuc k t' ∶ Fin (suc k)))
  <|> (inf e t >>= λ r → finV (ty r) >>= λ k → just (fsuc k (tm r) ∶ Fin (suc k)))
el e (S.fcase n P t a b) mT =
  inf e t >>= λ rt → finSV (ty rt) >>= λ k →
  annMot (e ▸ Fin (suc k)) P (mT >>= λ T → just (wk1 T)) >>= λ P' →
  chk e a (subTyᴬ (singleᴬ (fzero k)) P') >>= λ a' →
  chk (e ▸ Fin k) b (subTyᴬ (fsucSᴬ k) P') >>= λ b' →
  just (fcase k P' (tm rt) a' b' ∶ subTyᴬ (singleᴬ (tm rt)) P')
el e (S.fcase0 P t) mT =
  annMot (e ▸ Fin zero) P (mT >>= λ T → just (wk1 T)) >>= λ P' →
  chk e t (Fin zero) >>= λ t' →
  just (fcase0 P' t' ∶ subTyᴬ (singleᴬ t') P')
el e (S.psplit A B P b q) mT =
  inf e q >>= λ rq →
  annT e A (fstM (sgV (ty rq))) >>= λ A' →
  annT (e ▸ A') B (sndM (sgV (ty rq))) >>= λ B' →
  annMot (e ▸ Σ' A' B') P (mT >>= λ T → just (wk1 T)) >>= λ P' →
  chk ((e ▸ A') ▸ B') b (subTyᴬ (pairSᴬ A' B') P') >>= λ b' →
  just (psplit A' B' P' b' (tm rq) ∶ subTyᴬ (singleᴬ (tm rq)) P')

------------------------------------------------------------------------
-- 4. ★ Elaborate, then CHECK: the result is CheckA's derivation.
------------------------------------------------------------------------

module Checked (ok : SigOK Sg) where
  import DirectedHoTT.Algorithm.CheckA Sg ok as CA

  -- the derivation, when the elaborated term checks; `nothing` otherwise
  -- (an elaboration failure, or CheckA's certified "no")
  elaborate : (Γ : ACtx) → ⊢ctx ⌈ Γ ⌉ᶜ → STm ⌊ Γ ⌋ᴬ → (A : ATy ⌊ Γ ⌋ᴬ) →
              ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ → Maybe (Σ (ATm ⌊ Γ ⌋ᴬ) (λ t → Γ ⊢ᴬ t ∷ A))
  elaborate Γ wΓ s A dA with chk (envᴬ Γ) s A
  ... | nothing = nothing
  ... | just t with CA.checkᴬ Γ wΓ t A dA
  ...   | yes d = just (t , d)
  ...   | no _  = nothing
