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
-- ★ A FAILURE SAYS WHY: results are `R` — `ok`, or `err` with a path of
--   formers and the hole that could not be filled.
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
open import Agda.Builtin.String using ( String; primStringAppend )
open import DirectedHoTT.Algorithm.Result
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; vz; vs; extR )
open import DirectedHoTT.Spec.Typing using ( ⊢ctx_; _⊢ty_; c-◇ )
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
open import DirectedHoTT.Spec.TypingA Sg using ( ACtx; ◇ᴬ; _▹ᴬ_; ⌊_⌋ᴬ; ⌈_⌉ᶜ; _⊢ᴬ_∷_; _⊢tyᴬ_; nrsᴬ )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- 0. Plumbing: `Maybe` for proposals and views, `R` for results — a
--    failure says WHY (what an author of a surface term needs to read).
------------------------------------------------------------------------

infixl 1 _>>=ᵐ_
_>>=ᵐ_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>=ᵐ f = f a
nothing >>=ᵐ f = nothing

infixl 3 _<|>ᵐ_
_<|>ᵐ_ : {A : Set} → Maybe A → Maybe A → Maybe A
just a  <|>ᵐ _ = just a
nothing <|>ᵐ m = m

mapᵐ : {A B : Set} → (A → B) → Maybe A → Maybe B
mapᵐ f m = m >>=ᵐ λ a → just (f a)

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
-- ★ S7b step 3: a case on a tag, and the payload code of a telescope —
--   so a convoy's motive, instantiated at a constructor, is seen through
whTm (suc k) (fcase n P t a b) with whTm k t
... | fzero _    = whTm k a
... | fsuc _ t'  = whTm k (subTmᴬ (singleᴬ t') b)
... | t'         = fcase n P t' a b
whTm (suc k) (dpay I D C) with whTm k C
... | dι _       = ⌜Unit⌝
... | dσ _ S f   = ⌜Σ⌝ S (dpay (renTmᴬ vs I) (renTmᴬ vs D) (app (renTmᴬ vs f) (var vz)))
... | dρ _ j C'  = ⌜Σ⌝ (⌜IMu⌝ I D j) (dpay (renTmᴬ vs I) (renTmᴬ vs D) (renTmᴬ vs C'))
... | C'         = dpay I D C'
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

-- the hypotheses of a payload, along its telescope's head (`DIh-ι/σ/ρ`)
whTyₖ : ℕ → ATy Γ → ATy Γ
whTyₖ k (El c) = decode (whTm fuel c)
whTyₖ zero    A = A
whTyₖ (suc k) (DIh I D M C p) with whTm fuel C
... | dι _      = Unit
... | dσ _ S f  = whTyₖ k (DIh I D M (app f (fst p)) (snd p))
... | dρ _ j C' = Σ' (iinstᴬ j (fst p) M)
                      (DIh (renTmᴬ vs I) (renTmᴬ vs D) (renTyᴬ (extR (extR vs)) M) (renTmᴬ vs C') (snd (renTmᴬ vs p)))
... | C'        = DIh I D M C' p
whTyₖ (suc k) A = A

whTy : ATy Γ → ATy Γ
whTy A = whTyₖ fuel A

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

finV : ATy Γ → Maybe (ATm Γ)
finV A with whTy A
... | Fin n = just n
... | _     = nothing

-- ★ S7b step 2: the bound is a term, so its successor is read off its
--   weak-head form
sucV : ATm Γ → Maybe (ATm Γ)
sucV n with whTm fuel n
... | nsuc k = just k
... | _      = nothing

finSV : ATy Γ → Maybe (ATm Γ)
finSV A with finV A
... | just n  = sucV n
... | nothing = nothing

-- the code of an `El` type
elV : ATy Γ → Maybe (ATm Γ)
elV (El c) = just c
elV _      = nothing

-- the index code of a payload type `El (dpay I D C)`
payV : ATy Γ → Maybe (ATm Γ)
payV (El c) with whTm fuel c
... | dpay I D C = just I
... | _          = nothing
payV _ = nothing

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

elT : Env Γ → STy Γ → R (ATy Γ)
el  : Env Γ → STm Γ → Maybe (ATy Γ) → R (Inf Γ)

chk : Env Γ → STm Γ → ATy Γ → R (ATm Γ)
chk e t A = el e t (just A) >>= λ r → ok (tm r)

inf : Env Γ → STm Γ → R (Inf Γ)
inf e t = el e t nothing

-- an annotation: a hole takes the proposal, anything else is elaborated
annT : String → Env Γ → STy Γ → Maybe (ATy Γ) → R (ATy Γ)
annT w e S.□ᵀ p = need (primStringAppend "cannot fill hole: " w) p
annT w e A    p = elT e A

annM : String → Env Γ → STm Γ → Maybe (ATm Γ) → Maybe (ATy Γ) → R (ATm Γ)
annM w e S.□ p T        = need (primStringAppend "cannot fill hole: " w) p
annM w e t p (just T)   = chk e t T
annM w e t p nothing    = inf e t >>= λ r → ok (tm r)

-- a motive: written out, or (checking mode only) the constant one
annMot : {Δ : Cx} → String → Env Δ → STy Δ → Maybe (ATy Δ) → R (ATy Δ)
annMot = annT

-- a case's motive with no expected type: the CONSTANT one at the type
-- its first branch infers (the result is re-checked by CheckA anyway)
constMot : {Δ : Cx} → Env Δ → STy (Δ ∙) → STm Δ → Maybe (ATy Δ) → R (Maybe (ATy (Δ ∙)))
constMot e P     a (just T) = ok (just (wk1 T))
constMot e S.□ᵀ a nothing  = inf e a >>= λ ra → ok (just (wk1 (ty ra)))
constMot e P     a nothing  = ok nothing

fstM : {A B : Set} → Maybe (Pair A B) → Maybe A
fstM m = m >>=ᵐ λ { (a , _) → just a }

sndM : {A B : Set} → Maybe (Pair A B) → Maybe B
sndM m = m >>=ᵐ λ { (_ , b) → just b }

p1 : {A B C : Set} → Maybe (Triple A B C) → Maybe A
p1 m = m >>=ᵐ λ { (a , _) → just a }
p2 : {A B C : Set} → Maybe (Triple A B C) → Maybe B
p2 m = m >>=ᵐ λ { (_ , (b , _)) → just b }
p3 : {A B C : Set} → Maybe (Triple A B C) → Maybe C
p3 m = m >>=ᵐ λ { (_ , (_ , c)) → just c }

-- the expectation, viewed
_⟫_ : {A : Set} → Maybe (ATy Γ) → (ATy Γ → Maybe A) → Maybe A
mT ⟫ v = mT >>=ᵐ v

-- a premise's inferred type, viewed (a proposal: failure is silent)
_⟪_ : {A : Set} → R (Inf Γ) → (ATy Γ → Maybe A) → Maybe A
r ⟪ v = opt r >>=ᵐ λ i → v (Inf.ty i)

-- ★ types
elT e S.base    = ok base
elT e S.U       = ok U
elT e S.Unit    = ok Unit
elT e S.Nat     = ok Nat
elT e (S.Fin n) = at "Fin" (chk e n Nat >>= λ n' → ok (Fin n'))
elT e (S.Π A B) = elT e A >>= λ A' → elT (e ▸ A') B >>= λ B' → ok (Π A' B')
elT e (S.Σ' A B) = elT e A >>= λ A' → elT (e ▸ A') B >>= λ B' → ok (Σ' A' B')
elT e (S.El c)  = at "El" (chk e c U >>= λ c' → ok (El c'))
elT e (S.Hom A t u) = at "Hom" (
  elT e A >>= λ A' → chk e t A' >>= λ t' → chk e u A' >>= λ u' → ok (Hom A' t' u'))
elT e (S.Id A t u) = at "Id" (
  elT e A >>= λ A' → chk e t A' >>= λ t' → chk e u A' >>= λ u' → ok (Id A' t' u'))
elT e (S.IMu I D i) = at "IMu" (
  chk e I U >>= λ I' → chk e D (DescFᴬ I') >>= λ D' → chk e i (El I') >>= λ i' →
  ok (IMu I' D' i'))
elT e (S.Desc I) = at "Desc" (chk e I U >>= λ I' → ok (Desc I'))
elT e (S.DIh I D M C p) = at "DIh" (
  annM "the index code, from C : Desc I or p : El (dpay I …)" e I
       ((inf e C ⟪ descV) <|>ᵐ (inf e p ⟪ payV)) (just U) >>= λ I' →
  chk e D (DescFᴬ I') >>= λ D' → elT (motEnv e I' D') M >>= λ M' →
  chk e C (Desc I') >>= λ C' → chk e p (El (dpay I' D' C')) >>= λ p' →
  ok (DIh I' D' M' C' p'))
elT e S.□ᵀ = err "a type hole outside an annotation position"

-- ★ terms
el e (S.var x) mT = ok (var x ∶ e x)
el e (S.ref d) mT = ok (ref d ∶ εwkTyᴬ (type d))
el e (S.the A t) mT = at "the" (elT e A >>= λ A' → chk e t A' >>= λ t' → ok (t' ∶ A'))
el e S.□ mT = err "a term hole outside an annotation position"
el e (S.lam A t) mT = at "lam" (
  annT "the domain, from an expected Π" e A (fstM (mT ⟫ piV)) >>= λ A' →
  el (e ▸ A') t (sndM (mT ⟫ piV)) >>= λ r →
  ok (lam A' (tm r) ∶ Π A' (ty r)))
-- a β-redex `app (lam □ t) u`: the domain is the argument's type; when
-- checking against `T`, the body is checked against `T` past the binder
-- (the constant family — a guess the checker verifies), else inferred
el e (S.app (S.lam S.□ᵀ t) u) mT = at "app (β-redex)" (
  inf e u >>= λ ru →
  (need "no expected type" mT >>= λ T →
     chk (e ▸ ty ru) t (wk1 T) >>= λ t' → ok (app (lam (ty ru) t') (tm ru) ∶ T))
  <|> (inf (e ▸ ty ru) t >>= λ rt →
       ok (app (lam (ty ru) (tm rt)) (tm ru) ∶ subTyᴬ (singleᴬ (tm ru)) (ty rt))))
el e (S.app t u) mT = at "app" (
  inf e t >>= λ r → need "the function's type is not a Π" (piV (ty r)) >>= λ { (A , B) →
  chk e u A >>= λ u' → ok (app (tm r) u' ∶ subTyᴬ (singleᴬ u') B) })
el e (S.pair A B a b) mT = at "pair" (
  annT "the first type, from an expected Σ'" e A (fstM (mT ⟫ sgV)) >>= λ A' →
  chk e a A' >>= λ a' →
  -- no family given or expected: the non-dependent one, from `b`
  ((annT "the family, from an expected Σ'" (e ▸ A') B (sndM (mT ⟫ sgV)) >>= λ B' →
     chk e b (subTyᴬ (singleᴬ a') B') >>= λ b' → ok (pair A' B' a' b' ∶ Σ' A' B'))
   <|> (inf e b >>= λ r → ok (pair A' (wk1 (ty r)) a' (tm r) ∶ Σ' A' (wk1 (ty r))))))
el e (S.absurd c x) mT = at "absurd" (
  chk e c U >>= λ c' → chk e x base >>= λ x' → ok (absurd c' x' ∶ El c'))
el e (S.ordtr a t u p q) mT = at "ordtr" (
  chk e a Nat >>= λ a' → chk e t Nat >>= λ t' → chk e u Nat >>= λ u' →
  chk e p (Hom Nat a' t') >>= λ p' → chk e q (Hom Nat t' u') >>= λ q' →
  ok (ordtr a' t' u' p' q' ∶ Hom Nat a' u'))
el e (S.fst p) mT = at "fst" (
  inf e p >>= λ r → need "not a pair type" (sgV (ty r)) >>= λ { (A , B) → ok (fst (tm r) ∶ A) })
el e (S.snd p) mT = at "snd" (
  inf e p >>= λ r → need "not a pair type" (sgV (ty r)) >>= λ { (A , B) →
  ok (snd (tm r) ∶ subTyᴬ (singleᴬ (fst (tm r))) B) })
el e S.⌜base⌝ mT = ok (⌜base⌝ ∶ U)
el e (S.⌜Π⌝ c d) mT = at "⌜Π⌝" (
  chk e c U >>= λ c' → chk (e ▸ El c') d U >>= λ d' → ok (⌜Π⌝ c' d' ∶ U))
el e (S.⌜Σ⌝ c d) mT = at "⌜Σ⌝" (
  chk e c U >>= λ c' → chk (e ▸ El c') d U >>= λ d' → ok (⌜Σ⌝ c' d' ∶ U))
el e (S.⌜Hom⌝ c a b) mT = at "⌜Hom⌝" (
  chk e c U >>= λ c' → chk e a (El c') >>= λ a' → chk e b (El c') >>= λ b' →
  ok (⌜Hom⌝ c' a' b' ∶ U))
el e (S.⌜Id⌝ c a b) mT = at "⌜Id⌝" (
  chk e c U >>= λ c' → chk e a (El c') >>= λ a' → chk e b (El c') >>= λ b' →
  ok (⌜Id⌝ c' a' b' ∶ U))
el e (S.hrefl c t) mT = at "hrefl" (
  chk e c U >>= λ c' → chk e t (El c') >>= λ t' → ok (hrefl c' t' ∶ Hom (El c') t' t'))
el e (S.idrefl c t) mT = at "idrefl" (
  chk e c U >>= λ c' → chk e t (El c') >>= λ t' → ok (idrefl c' t' ∶ Id (El c') t' t'))
-- ★ the path formers read their ambient and endpoints off the path
el e (S.tr A t u d p x) mT = at "tr" (
  inf e p >>= λ rp →
  annT "the ambient, from the path's Hom" e A (p1 (homV (ty rp))) >>= λ A' →
  annM "the source, from the path's Hom" e t (p2 (homV (ty rp))) (just A') >>= λ t' →
  annM "the target, from the path's Hom" e u (p3 (homV (ty rp))) (just A') >>= λ u' →
  chk (e ▸ A') d U >>= λ d' →
  chk e x (El (subTmᴬ (singleᴬ t') d')) >>= λ x' →
  ok (tr A' t' u' d' (tm rp) x' ∶ El (subTmᴬ (singleᴬ u') d')))
el e (S.ap cA t u cB b p) mT = at "ap" (
  inf e p >>= λ rp →
  annM "the ambient code, from the path's Hom" e cA (p1 (homV (ty rp)) >>=ᵐ elV) (just U) >>= λ cA' →
  annM "the source, from the path's Hom" e t (p2 (homV (ty rp))) (just (El cA')) >>= λ t' →
  annM "the target, from the path's Hom" e u (p3 (homV (ty rp))) (just (El cA')) >>= λ u' →
  chk e cB U >>= λ cB' →
  chk (e ▸ El cA') b (El (renTmᴬ vs cB')) >>= λ b' →
  ok (ap cA' t' u' cB' b' (tm rp)
        ∶ Hom (El cB') (subTmᴬ (singleᴬ t') b') (subTmᴬ (singleᴬ u') b')))
el e (S.jsub A t u d p x) mT = at "jsub" (
  inf e p >>= λ rp →
  annT "the ambient, from the path's Id" e A (p1 (idV (ty rp))) >>= λ A' →
  annM "the source, from the path's Id" e t (p2 (idV (ty rp))) (just A') >>= λ t' →
  annM "the target, from the path's Id" e u (p3 (idV (ty rp))) (just A') >>= λ u' →
  chk (e ▸ A') d U >>= λ d' →
  chk e x (El (subTmᴬ (singleᴬ t') d')) >>= λ x' →
  ok (jsub A' t' u' d' (tm rp) x' ∶ El (subTmᴬ (singleᴬ u') d')))
el e S.unit mT = ok (unit ∶ Unit)
el e S.nzero mT = ok (nzero ∶ Nat)
el e (S.nsuc n) mT = chk e n Nat >>= λ n' → ok (nsuc n' ∶ Nat)
el e (S.natrec M z s n) mT = at "natrec" (
  annMot "the motive (the constant one needs an expected type)" (e ▸ Nat) M (mapᵐ wk1 mT) >>= λ M' →
  chk e z (subTyᴬ (singleᴬ nzero) M') >>= λ z' →
  chk ((e ▸ Nat) ▸ M') s (subTyᴬ nrsᴬ M') >>= λ s' →
  chk e n Nat >>= λ n' →
  ok (natrec M' z' s' n' ∶ subTyᴬ (singleᴬ n') M'))
el e S.⌜Nat⌝ mT = ok (⌜Nat⌝ ∶ U)
el e S.⌜Unit⌝ mT = ok (⌜Unit⌝ ∶ U)
el e (S.⌜IMu⌝ I D i) mT = at "⌜IMu⌝" (
  chk e I U >>= λ I' → chk e D (DescFᴬ I') >>= λ D' → chk e i (El I') >>= λ i' →
  ok (⌜IMu⌝ I' D' i' ∶ U))
el e (S.⌜Fin⌝ n) mT = at "⌜Fin⌝" (chk e n Nat >>= λ n' → ok (⌜Fin⌝ n' ∶ U))
-- ★ the levitated formers: index code (description, index) from the
--   expected type or the scrutinee
el e (S.con I D i p) mT = at "con" (
  annM "the index code, from an expected IMu" e I (p1 (mT ⟫ muV)) (just U) >>= λ I' →
  annM "the description, from an expected IMu" e D (p2 (mT ⟫ muV)) (just (DescFᴬ I')) >>= λ D' →
  annM "the index, from an expected IMu" e i (p3 (mT ⟫ muV)) (just (El I')) >>= λ i' →
  chk e p (El (dpay I' D' (app D' i'))) >>= λ p' →
  ok (con I' D' i' p' ∶ IMu I' D' i'))
el e (S.ielim I D M i x t) mT = at "ielim" (
  annM "the index code, from the scrutinee's IMu" e I (p1 (inf e t ⟪ muV)) (just U) >>= λ I' →
  chk e D (DescFᴬ I') >>= λ D' →
  annMot "the motive (the constant one needs an expected type)" (motEnv e I' D') M (mapᵐ wk2 mT) >>= λ M' →
  chk e x (MethTyᴬ I' D' M') >>= λ x' →
  chk e i (El I') >>= λ i' →
  chk e t (IMu I' D' i') >>= λ t' →
  ok (ielim I' D' M' i' x' t' ∶ iinstᴬ i' t' M'))
el e (S.dι I) mT = at "dι" (
  annM "the index code, from an expected Desc" e I (mT ⟫ descV) (just U) >>= λ I' → ok (dι I' ∶ Desc I'))
el e (S.dσ I Sx f) mT = at "dσ" (
  annM "the index code, from an expected Desc" e I (mT ⟫ descV) (just U) >>= λ I' →
  chk e Sx U >>= λ S' → chk e f (Π (El S') (Desc (renTmᴬ vs I'))) >>= λ f' →
  ok (dσ I' S' f' ∶ Desc I'))
el e (S.dρ I j C) mT = at "dρ" (
  annM "the index code, from an expected Desc or C" e I ((mT ⟫ descV) <|>ᵐ (inf e C ⟪ descV)) (just U) >>= λ I' →
  chk e j (El I') >>= λ j' → chk e C (Desc I') >>= λ C' →
  ok (dρ I' j' C' ∶ Desc I'))
el e (S.dpay I D C) mT = at "dpay" (
  chk e I U >>= λ I' → chk e D (DescFᴬ I') >>= λ D' → chk e C (Desc I') >>= λ C' →
  ok (dpay I' D' C' ∶ U))
el e (S.dih I D M x C p) mT = at "dih" (
  annM "the index code, from C : Desc I or p : El (dpay I …)" e I
       ((inf e C ⟪ descV) <|>ᵐ (inf e p ⟪ payV)) (just U) >>= λ I' →
  chk e D (DescFᴬ I') >>= λ D' →
  elT (motEnv e I' D') M >>= λ M' →
  chk e x (MethTyᴬ I' D' M') >>= λ x' →
  chk e C (Desc I') >>= λ C' →
  chk e p (El (dpay I' D' C')) >>= λ p' →
  ok (dih I' D' M' x' C' p' ∶ DIh I' D' M' C' p'))
-- a bound is a ℕ, so it has no hole: the expected type's wins
el e (S.fzero n) mT = at "fzero" (
  annM "the bound, from an expected Fin (suc n)" e n (mT ⟫ finSV) (just Nat) >>= λ k →
  ok (fzero k ∶ Fin (nsuc k)))
el e (S.fsuc n t) mT with mT ⟫ finSV
... | just k  = at "fsuc" (chk e t (Fin k) >>= λ t' → ok (fsuc k t' ∶ Fin (nsuc k)))
... | nothing = at "fsuc" (
  inf e t >>= λ r → need "the bound, from the argument's Fin" (finV (ty r)) >>= λ k →
  ok (fsuc k (tm r) ∶ Fin (nsuc k)))
el e (S.fcase n P t a b) mT = at "fcase" (
  inf e t >>= λ rt → need "the scrutinee is not a Fin (suc n)" (finSV (ty rt)) >>= λ k →
  constMot e P a mT >>= λ mP →
  annMot "the motive (the constant one needs an expected type)" (e ▸ Fin (nsuc k)) P mP >>= λ P' →
  chk e a (subTyᴬ (singleᴬ (fzero k)) P') >>= λ a' →
  chk (e ▸ Fin k) b (subTyᴬ (fsucSᴬ k) P') >>= λ b' →
  ok (fcase k P' (tm rt) a' b' ∶ subTyᴬ (singleᴬ (tm rt)) P'))
el e (S.fcase0 P t) mT = at "fcase0" (
  annMot "the motive (the constant one needs an expected type)" (e ▸ Fin nzero) P (mapᵐ wk1 mT) >>= λ P' →
  chk e t (Fin nzero) >>= λ t' →
  ok (fcase0 P' t' ∶ subTyᴬ (singleᴬ t') P'))
el e (S.psplit A B P b q) mT = at "psplit" (
  inf e q >>= λ rq →
  annT "the first type, from the pair's Σ'" e A (fstM (sgV (ty rq))) >>= λ A' →
  annT "the family, from the pair's Σ'" (e ▸ A') B (sndM (sgV (ty rq))) >>= λ B' →
  annMot "the motive (the constant one needs an expected type)" (e ▸ Σ' A' B') P (mapᵐ wk1 mT) >>= λ P' →
  chk ((e ▸ A') ▸ B') b (subTyᴬ (pairSᴬ A' B') P') >>= λ b' →
  ok (psplit A' B' P' b' (tm rq) ∶ subTyᴬ (singleᴬ (tm rq)) P'))

------------------------------------------------------------------------
-- 4. ★ Elaborate, then CHECK: the result is CheckA's derivation.
------------------------------------------------------------------------

module Checked (sok : SigOK Sg) where
  import DirectedHoTT.Algorithm.CheckA Sg sok as CA
  import DirectedHoTT.Metatheory.Erasure Sg sok as Er

  -- the derivation, when the elaborated term checks; otherwise the reason
  -- (an elaboration failure, or CheckA's certified "no")
  elaborate : (Γ : ACtx) → ⊢ctx ⌈ Γ ⌉ᶜ → STm ⌊ Γ ⌋ᴬ → (A : ATy ⌊ Γ ⌋ᴬ) →
              ⌈ Γ ⌉ᶜ ⊢ty ⌈ A ⌉ᵀ → R (Σ (ATm ⌊ Γ ⌋ᴬ) (λ t → Γ ⊢ᴬ t ∷ A))
  elaborate Γ wΓ s A dA with chk (envᴬ Γ) s A
  ... | err w = err w
  ... | ok t with CA.checkᴬ Γ wΓ t A dA
  ...   | yes d = ok (t , d)
  ...   | no _  = err "elaborated, but the checker says no"

  -- ★ a CLOSED definition: its type and its body, both elaborated and
  --   checked — what a signature entry needs
  Closed : Set
  Closed = Σ (ATy ε) (λ A → Σ (ATm ε) (λ t → Pair (◇ᴬ ⊢tyᴬ A) (◇ᴬ ⊢ᴬ t ∷ A)))

  elabClosed : STy ε → STm ε → R Closed
  elabClosed sA s with elT (envᴬ ◇ᴬ) sA
  ... | err w = err (primStringAppend "type › " w)
  ... | ok A with CA.checkTyᴬ ◇ᴬ c-◇ A
  ...   | no _ = err "type: elaborated, but the checker says no"
  ...   | yes dA with elaborate ◇ᴬ c-◇ s A (Er.erase-ty dA)
  ...     | err w        = err (primStringAppend "body › " w)
  ...     | ok (t , d)   = ok (A , (t , (dA , d)))
