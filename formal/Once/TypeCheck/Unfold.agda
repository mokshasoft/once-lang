-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Unfold
--
-- Plan 0.94 D2 (§0): δ-UNFOLDING. A use of a top-level definition may be
-- replaced by its definiens:
--
--     Γ ⟨x ≝ e : A⟩ ⊢ b ∶ B ⨾ Ψ      ⟹      Γ ⊢ b[(e : A)/x] ∶ B ⨾ Ψ
--
-- Two things the plan's first statement got wrong, both forced:
--
--   * The name unfolds to the ANNOTATED definiens `(e : A)`. A definition is
--     checked against its signature, and a use of it SYNTHESIZES `A`; a bare
--     `e` (say `inl 1`) need not synthesize, so `case x of …` would stop
--     typing. `(e : A)` synthesizes `A` exactly as the use did.
--   * Substitution follows Once's SCOPING, which is not purely lexical: a
--     binder named `x` shadows the definition — except inside a `cata`/`ana`
--     algebra, which is typed without locals and so sees the definition even
--     under `\x`. `sub` carries that as a flag, reset at an algebra position.
--
-- Capture is excluded by a premise, not by renaming: no binder of `b` and no
-- local of Γ is a name that occurs in `e` (`NC`, `Fr`) — the variable
-- convention, which every `b` meets up to renaming its binders.
--
-- The proof is two inductions over the three judgments: `W` moves `e`'s
-- derivation from the context a definition sees (no locals) to the use site,
-- and `S` is the substitution lemma itself.
------------------------------------------------------------------------
module Once.TypeCheck.Unfold where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
open import Data.String.Properties as StrProp using ()
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Once.Type as T using (Type; PolyType; Ground; extractGround; Quantity)
open import Once.TypeCheck.Raw as Raw using (RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet;
  RPair; RDestruct; RUnit; RInt; RFloat; RStringLit; RAnnot; RBinOp; RUnaryOp; RAna)
open import Once.CanonicalName using (CanonicalName; canonical; gen; generatorNS; GenWord)
open import Once.Functor.Translate using (IsConcrete)
open import Once.TypeCheck.Classify
  using (NamedCtx; mkCtx; Imports; PolyCtx; lookupLocal; lookupLocal-go; lookupImport;
         lookupPolyPrefix; ctxWithImportsAndPolys; classifyAppHead; classifyAppHeadView;
         AppHeadView; ahv-cata; ahv-ana; ahv-other; classifyAppHead-nothing⇒view-other)
open import Once.TypeCheck.Context using (Ctx)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.TypeCheck.Judgment
open import Once.TypeCheck.ModeAgreement using (extractGround-irr; agree-cc)
open import Once.TypeCheck.LetIsDef using (defineNamedCtx)
open import Once.Surface.Context as SC using (Usage; SVar; zeroUsage; _+ᵘ_; _*ᵘ_; _⊔ᵘ_)
open SC.Usage using () renaming (_∷_ to _∷ᵘ_)

------------------------------------------------------------------------
-- A property of every variable occurrence of a term, and the variable
-- convention.
------------------------------------------------------------------------

Fr : (String → Set) → RawExpr → Set
Fr Q (RVar z) = Q z
Fr Q (RQualified _ _) = ⊤
Fr Q (RResolved _) = ⊤
Fr Q (RApp f a) = Fr Q f × Fr Q a
Fr Q (RLam _ b) = Fr Q b
Fr Q (RLet _ a b) = Fr Q a × Fr Q b
Fr Q (RPair a b) = Fr Q a × Fr Q b
Fr Q (RDestruct s _ l _ r) = Fr Q s × Fr Q l × Fr Q r
Fr Q RUnit = ⊤
Fr Q (RInt _) = ⊤
Fr Q (RFloat _ _ _ _) = ⊤
Fr Q (RStringLit _) = ⊤
Fr Q (RAnnot b _) = Fr Q b
Fr Q (RBinOp _ a b) = Fr Q a × Fr Q b
Fr Q (RUnaryOp _ a) = Fr Q a
Fr Q (RAna _ a) = Fr Q a

Fr-map₂ : ∀ {Q R S : String → Set} (h : ∀ z → Q z → R z → S z) (b : RawExpr) → Fr Q b → Fr R b → Fr S b
Fr-map₂ h (RVar z) q r = h z q r
Fr-map₂ h (RQualified _ _) _ _ = tt
Fr-map₂ h (RResolved _) _ _ = tt
Fr-map₂ h (RApp f a) (q₁ , q₂) (r₁ , r₂) = Fr-map₂ h f q₁ r₁ , Fr-map₂ h a q₂ r₂
Fr-map₂ h (RLam _ b) q r = Fr-map₂ h b q r
Fr-map₂ h (RLet _ a b) (q₁ , q₂) (r₁ , r₂) = Fr-map₂ h a q₁ r₁ , Fr-map₂ h b q₂ r₂
Fr-map₂ h (RPair a b) (q₁ , q₂) (r₁ , r₂) = Fr-map₂ h a q₁ r₁ , Fr-map₂ h b q₂ r₂
Fr-map₂ h (RDestruct s _ l _ r) (q₁ , q₂ , q₃) (r₁ , r₂ , r₃) =
  Fr-map₂ h s q₁ r₁ , Fr-map₂ h l q₂ r₂ , Fr-map₂ h r q₃ r₃
Fr-map₂ h RUnit _ _ = tt
Fr-map₂ h (RInt _) _ _ = tt
Fr-map₂ h (RFloat _ _ _ _) _ _ = tt
Fr-map₂ h (RStringLit _) _ _ = tt
Fr-map₂ h (RAnnot b _) q r = Fr-map₂ h b q r
Fr-map₂ h (RBinOp _ a b) (q₁ , q₂) (r₁ , r₂) = Fr-map₂ h a q₁ r₁ , Fr-map₂ h b q₂ r₂
Fr-map₂ h (RUnaryOp _ a) q r = Fr-map₂ h a q r
Fr-map₂ h (RAna _ a) q r = Fr-map₂ h a q r

Fr-triv : ∀ {Q : String → Set} (h : ∀ z → Q z) (b : RawExpr) → Fr Q b
Fr-triv h (RVar z) = h z
Fr-triv h (RQualified _ _) = tt
Fr-triv h (RResolved _) = tt
Fr-triv h (RApp f a) = Fr-triv h f , Fr-triv h a
Fr-triv h (RLam _ b) = Fr-triv h b
Fr-triv h (RLet _ a b) = Fr-triv h a , Fr-triv h b
Fr-triv h (RPair a b) = Fr-triv h a , Fr-triv h b
Fr-triv h (RDestruct s _ l _ r) = Fr-triv h s , Fr-triv h l , Fr-triv h r
Fr-triv h RUnit = tt
Fr-triv h (RInt _) = tt
Fr-triv h (RFloat _ _ _ _) = tt
Fr-triv h (RStringLit _) = tt
Fr-triv h (RAnnot b _) = Fr-triv h b
Fr-triv h (RBinOp _ a b) = Fr-triv h a , Fr-triv h b
Fr-triv h (RUnaryOp _ a) = Fr-triv h a
Fr-triv h (RAna _ a) = Fr-triv h a

-- The binders of `b` do not occur as variables of `e`.
NC : RawExpr → RawExpr → Set
NC e (RVar _) = ⊤
NC e (RQualified _ _) = ⊤
NC e (RResolved _) = ⊤
NC e (RApp f a) = NC e f × NC e a
NC e (RLam y b) = Fr (λ z → z ≢ y) e × NC e b
NC e (RLet y a b) = Fr (λ z → z ≢ y) e × NC e a × NC e b
NC e (RPair a b) = NC e a × NC e b
NC e (RDestruct s xL l xR r) = NC e s × Fr (λ z → z ≢ xL) e × NC e l × Fr (λ z → z ≢ xR) e × NC e r
NC e RUnit = ⊤
NC e (RInt _) = ⊤
NC e (RFloat _ _ _ _) = ⊤
NC e (RStringLit _) = ⊤
NC e (RAnnot b _) = NC e b
NC e (RBinOp _ a b) = NC e a × NC e b
NC e (RUnaryOp _ a) = NC e a
NC e (RAna _ a) = NC e a

------------------------------------------------------------------------
-- Algebra positions reset the local scope.
------------------------------------------------------------------------

isAlgV : ∀ {f} → AppHeadView f → Bool
isAlgV ahv-cata = true
isAlgV ahv-ana = true
isAlgV _ = false

isAlg : RawExpr → Bool
isAlg f = isAlgV (classifyAppHeadView f)

scopeOf : Bool → Bool → Bool
scopeOf true _ = false
scopeOf false sh = sh

isAlg-other : ∀ {f} → classifyAppHead f ≡ nothing → isAlg f ≡ false
isAlg-other {f} ah rewrite classifyAppHead-nothing⇒view-other ah = refl

-- The head classification does not look at an application's argument.
app-head-irr : ∀ (h a a′ : RawExpr) → classifyAppHead (RApp h a) ≡ classifyAppHead (RApp h a′)
app-head-irr (RResolved (canonical (ns ∷ g ∷ []))) a a′ with ns StrProp.≟ generatorNS
... | no _ = refl
... | yes refl with g StrProp.≟ "pair"
...   | yes refl = refl
...   | no _ with g StrProp.≟ "compose"
...     | yes refl = refl
...     | no _ with g StrProp.≟ "case"
...       | yes refl = refl
...       | no _ = refl
app-head-irr (RResolved (canonical [])) a a′ = refl
app-head-irr (RResolved (canonical (_ ∷ []))) a a′ = refl
app-head-irr (RResolved (canonical (_ ∷ _ ∷ _ ∷ _))) a a′ = refl
app-head-irr (RVar _) a a′ = refl
app-head-irr (RQualified _ _) a a′ = refl
app-head-irr (RApp _ _) a a′ = refl
app-head-irr (RLam _ _) a a′ = refl
app-head-irr (RLet _ _ _) a a′ = refl
app-head-irr (RPair _ _) a a′ = refl
app-head-irr (RDestruct _ _ _ _ _) a a′ = refl
app-head-irr RUnit a a′ = refl
app-head-irr (RInt _) a a′ = refl
app-head-irr (RFloat _ _ _ _) a a′ = refl
app-head-irr (RStringLit _) a a′ = refl
app-head-irr (RAnnot _ _) a a′ = refl
app-head-irr (RBinOp _ _ _) a a′ = refl
app-head-irr (RUnaryOp _ _) a a′ = refl
app-head-irr (RAna _ _) a a′ = refl


private
  just≢nothing : ∀ {ℓ} {X : Set ℓ} {v : X} → just v ≡ nothing → ⊥
  just≢nothing ()

  -- Local lookup past a binder.
  miss-ext : ∀ {n} {G : Ctx} {Δ : SC.Ctx n} {y z : String} {B : Type}
           → z ≢ y → lookupLocal-go z G Δ ≡ nothing
           → lookupLocal-go z (extendCtx G y B) (Δ SC., B) ≡ nothing
  miss-ext {G = G} {Δ = Δ} {y = y} {z = z} z≢y eq with z StrProp.≟ y
  ... | yes z≡y = ⊥-elim (z≢y z≡y)
  ... | no _ with lookupLocal-go z G Δ | eq
  ...   | nothing | refl = refl

  miss-ext← : ∀ {n} {G : Ctx} {Δ : SC.Ctx n} {y z : String} {B : Type}
            → z ≢ y → lookupLocal-go z (extendCtx G y B) (Δ SC., B) ≡ nothing
            → lookupLocal-go z G Δ ≡ nothing
  miss-ext← {G = G} {Δ = Δ} {y = y} {z = z} z≢y eq with z StrProp.≟ y
  ... | yes z≡y = ⊥-elim (z≢y z≡y)
  ... | no _ with lookupLocal-go z G Δ | eq
  ...   | nothing | _ = refl
  ...   | just (_ , _ , SC.svar _) | ()

  hit-ext : ∀ {n} {G : Ctx} {Δ : SC.Ctx n} {y z : String} {B : Type}
          → z ≡ y → lookupLocal-go z (extendCtx G y B) (Δ SC., B) ≡ nothing → ⊥
  hit-ext {y = y} {z = z} z≡y eq with z StrProp.≟ y
  ... | yes _ = just≢nothing eq
  ... | no z≢y = z≢y z≡y

  -- Quantities: zero is absorbed.
  z+z : ∀ n → zeroUsage {n} +ᵘ zeroUsage ≡ zeroUsage
  z+z 0 = refl
  z+z (suc n) = cong (T.Zero ∷ᵘ_) (z+z n)

  q*z : ∀ q n → q *ᵘ zeroUsage {n} ≡ zeroUsage
  q*z q 0 = refl
  q*z T.Zero (suc n) = cong (T.Zero ∷ᵘ_) (q*z T.Zero n)
  q*z T.One  (suc n) = cong (T.Zero ∷ᵘ_) (q*z T.One n)
  q*z T.Many (suc n) = cong (T.Zero ∷ᵘ_) (q*z T.Many n)

  z⊔z : ∀ n → zeroUsage {n} ⊔ᵘ zeroUsage ≡ zeroUsage
  z⊔z 0 = refl
  z⊔z (suc n) = cong (T.Zero ∷ᵘ_) (z⊔z n)

------------------------------------------------------------------------
-- W: a term typed with no locals types under any locals it does not
-- mention — with the same type and no use of the new ones.
------------------------------------------------------------------------

module Weaken (imps : Imports) (P : PolyCtx) where

  data WK : ∀ {m n} → Ctx → SC.Ctx m → Ctx → SC.Ctx n → Set where
    wk-base  : ∀ {n} {G : Ctx} {Δ : SC.Ctx n} → WK Context.∅ SC.∅ G Δ
    wk-under : ∀ {m n} {GL : Ctx} {ΔL : SC.Ctx m} {GD : Ctx} {ΔD : SC.Ctx n}
               (y : String) (B : Type)
             → WK GL ΔL GD ΔD
             → WK (extendCtx GL y B) (ΔL SC., B) (extendCtx GD y B) (ΔD SC., B)

  -- The names the term uses must be absent from the new locals.
  baseClear : ∀ {m n GL ΔL GD ΔD} → WK {m} {n} GL ΔL GD ΔD → String → Set
  baseClear (wk-base {G = G} {Δ = Δ}) z = lookupLocal-go z G Δ ≡ nothing
  baseClear (wk-under _ _ wk) z = baseClear wk z

  up : ∀ {m n GL ΔL GD ΔD} → WK {m} {n} GL ΔL GD ΔD → Usage m → Usage n
  up wk-base _ = zeroUsage
  up (wk-under _ _ wk) (q ∷ᵘ U) = q ∷ᵘ up wk U

  up-zero : ∀ {m n GL ΔL GD ΔD} (wk : WK {m} {n} GL ΔL GD ΔD) → up wk zeroUsage ≡ zeroUsage
  up-zero wk-base = refl
  up-zero (wk-under _ _ wk) = cong (T.Zero ∷ᵘ_) (up-zero wk)

  up-+ : ∀ {m n GL ΔL GD ΔD} (wk : WK {m} {n} GL ΔL GD ΔD) (U₁ U₂ : Usage m)
       → up wk (U₁ +ᵘ U₂) ≡ up wk U₁ +ᵘ up wk U₂
  up-+ {n = n} wk-base _ _ = sym (z+z n)
  up-+ (wk-under _ _ wk) (_ ∷ᵘ U₁) (_ ∷ᵘ U₂) = cong (_ ∷ᵘ_) (up-+ wk U₁ U₂)

  up-* : ∀ {m n GL ΔL GD ΔD} (wk : WK {m} {n} GL ΔL GD ΔD) (q : Quantity) (U : Usage m)
       → up wk (q *ᵘ U) ≡ q *ᵘ up wk U
  up-* {n = n} wk-base q _ = sym (q*z q n)
  up-* (wk-under _ _ wk) q (_ ∷ᵘ U) = cong (_ ∷ᵘ_) (up-* wk q U)

  up-⊔ : ∀ {m n GL ΔL GD ΔD} (wk : WK {m} {n} GL ΔL GD ΔD) (U₁ U₂ : Usage m)
       → up wk (U₁ ⊔ᵘ U₂) ≡ up wk U₁ ⊔ᵘ up wk U₂
  up-⊔ {n = n} wk-base _ _ = sym (z⊔z n)
  up-⊔ (wk-under _ _ wk) (_ ∷ᵘ U₁) (_ ∷ᵘ U₂) = cong (_ ∷ᵘ_) (up-⊔ wk U₁ U₂)

  up-z+M : ∀ {m n GL ΔL GD ΔD} (wk : WK {m} {n} GL ΔL GD ΔD) (U : Usage m)
         → up wk (zeroUsage +ᵘ (T.Many *ᵘ U)) ≡ zeroUsage +ᵘ (T.Many *ᵘ up wk U)
  up-z+M wk U = trans (up-+ wk _ _) (cong₂ _+ᵘ_ (up-zero wk) (up-* wk T.Many U))

  up-+* : ∀ {m n GL ΔL GD ΔD} (wk : WK {m} {n} GL ΔL GD ΔD) (U₁ : Usage m) (q : Quantity) (U₂ : Usage m)
        → up wk (U₁ +ᵘ (q *ᵘ U₂)) ≡ up wk U₁ +ᵘ (q *ᵘ up wk U₂)
  up-+* wk U₁ q U₂ = trans (up-+ wk _ _) (cong (up wk U₁ +ᵘ_) (up-* wk q U₂))

  up-+⊔ : ∀ {m n GL ΔL GD ΔD} (wk : WK {m} {n} GL ΔL GD ΔD) (U₀ U₁ U₂ : Usage m)
        → up wk (U₀ +ᵘ (U₁ ⊔ᵘ U₂)) ≡ up wk U₀ +ᵘ (up wk U₁ ⊔ᵘ up wk U₂)
  up-+⊔ wk U₀ U₁ U₂ = trans (up-+ wk _ _) (cong (up wk U₀ +ᵘ_) (up-⊔ wk U₁ U₂))

  data WRel {m n GL ΔL GD ΔD} (wk : WK {m} {n} GL ΔL GD ΔD)
       : Maybe (∃[ T ] ∃[ U ] SVar ΔL U T) → Maybe (∃[ T ] ∃[ U ] SVar ΔD U T) → Set where
    wr-none : WRel wk nothing nothing
    wr-both : ∀ {T U eV T′ U′ eV′} → T′ ≡ T → U′ ≡ up wk U
            → WRel wk (just (T , U , eV)) (just (T′ , U′ , eV′))

  mk-none : ∀ {m n GL ΔL GD ΔD} {wk : WK {m} {n} GL ΔL GD ΔD} {r} → r ≡ nothing → WRel wk nothing r
  mk-none refl = wr-none

  wloc : ∀ {m n GL ΔL GD ΔD} (wk : WK {m} {n} GL ΔL GD ΔD) (z : String) → baseClear wk z
       → WRel wk (lookupLocal-go z GL ΔL) (lookupLocal-go z GD ΔD)
  wloc wk-base z bc = mk-none bc
  wloc (wk-under {GL = GL} {ΔL = ΔL} {GD = GD} {ΔD = ΔD} y B wk) z bc with z StrProp.≟ y
  ... | yes _ = wr-both refl (cong (T.One ∷ᵘ_) (sym (up-zero wk)))
  ... | no _ with lookupLocal-go z GL ΔL | lookupLocal-go z GD ΔD | wloc wk z bc
  ...   | nothing | nothing | wr-none = wr-none
  ...   | nothing | just _ | ()
  ...   | just (_ , _ , SC.svar i) | just (_ , _ , SC.svar j) | wr-both a b = wr-both a (cong (T.Zero ∷ᵘ_) b)

  wnone : ∀ {m n GL ΔL GD ΔD} {wk : WK {m} {n} GL ΔL GD ΔD} {r₁ r₂} → WRel wk r₁ r₂ → r₁ ≡ nothing → r₂ ≡ nothing
  wnone wr-none _ = refl
  wnone (wr-both _ _) ()

  Wc : ∀ {n} → Ctx → SC.Ctx n → ℕ → NamedCtx
  Wc {n} G Δ fr = mkCtx n G Δ fr imps P

  wvar : ∀ {m n GL ΔL GD ΔD frD} (wk : WK {m} {n} GL ΔL GD ΔD) (z : String) {T U eV} r₁ r₂
       → WRel wk r₁ r₂ → r₁ ≡ just (T , U , eV) → lookupLocal-go z GD ΔD ≡ r₂
       → Wc GD ΔD frD ⊢ᵢ RVar z ∶ T ⨾ up wk U
  wvar wk z _ _ wr-none () _
  wvar wk z _ _ (wr-both a b) refl q = subst₂ (λ T U → _ ⊢ᵢ RVar z ∶ T ⨾ U) a b (t-var-local q)

  cᵢ : ∀ {ctx b T U U′} → U ≡ U′ → ctx ⊢ᵢ b ∶ T ⨾ U → ctx ⊢ᵢ b ∶ T ⨾ U′
  cᵢ refl d = d
  cᶜ : ∀ {ctx b T U U′} → U ≡ U′ → ctx ⊢ᶜ b ∶ T ⨾ U → ctx ⊢ᶜ b ∶ T ⨾ U′
  cᶜ refl d = d
  cᵈ : ∀ {ctx b A′ π B U U′} → U ≡ U′ → ctx ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ U → ctx ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ U′
  cᵈ refl d = d

  mutual
    W-i : ∀ {m n GL ΔL GD ΔD frL frD} (wk : WK {m} {n} GL ΔL GD ΔD) {b T U}
        → Fr (baseClear wk) b → Wc GL ΔL frL ⊢ᵢ b ∶ T ⨾ U → Wc GD ΔD frD ⊢ᵢ b ∶ T ⨾ up wk U
    W-c : ∀ {m n GL ΔL GD ΔD frL frD} (wk : WK {m} {n} GL ΔL GD ΔD) {b T U}
        → Fr (baseClear wk) b → Wc GL ΔL frL ⊢ᶜ b ∶ T ⨾ U → Wc GD ΔD frD ⊢ᶜ b ∶ T ⨾ up wk U
    W-d : ∀ {m n GL ΔL GD ΔD frL frD} (wk : WK {m} {n} GL ΔL GD ΔD) {b A′ π B U}
        → Fr (baseClear wk) b → Wc GL ΔL frL ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ U → Wc GD ΔD frD ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ up wk U

    W-i wk _ (t-int n) = cᵢ (sym (up-zero wk)) (t-int n)
    W-i wk _ (t-float i f l p) = cᵢ (sym (up-zero wk)) (t-float i f l p)
    W-i wk _ (t-str t) = cᵢ (sym (up-zero wk)) (t-str t)
    W-i wk _ t-unit = cᵢ (sym (up-zero wk)) t-unit
    W-i wk _ t-unit-var = cᵢ (sym (up-zero wk)) t-unit-var
    W-i {GL = GL} {ΔL = ΔL} {GD = GD} {ΔD = ΔD} wk fr (t-var-local {x = z} eq) =
        wvar wk z (lookupLocal-go z GL ΔL) (lookupLocal-go z GD ΔD) (wloc wk z fr) eq refl
    W-i wk _ (t-var-qualified l c) = cᵢ (sym (up-zero wk)) (t-var-qualified l c)
    W-i wk _ (t-var-resolved ng l c) = cᵢ (sym (up-zero wk)) (t-var-resolved ng l c)
    W-i wk fr (t-var-import {x = z} ¬gw ln li c) = cᵢ (sym (up-zero wk)) (t-var-import ¬gw (wnone (wloc wk z fr) ln) li c)
    W-i wk fr (t-var-poly-instantiate-infer {x = z} ln li lp gr eT body) =
        cᵢ (sym (up-zero wk)) (t-var-poly-instantiate-infer (wnone (wloc wk z fr) ln) li lp gr eT body)
    W-i wk fr (t-annot c) = t-annot (W-c wk fr c)
    W-i wk (f₁ , f₂) (t-pair d₁ d₂) = cᵢ (sym (up-+ wk _ _)) (t-pair (W-i wk f₁ d₁) (W-i wk f₂ d₂))
    W-i wk fr (t-neg d) = t-neg (W-i wk fr d)
    W-i wk _ (t-neg-float i f l p) = cᵢ (sym (up-zero wk)) (t-neg-float i f l p)
    W-i wk (f₁ , f₂) (t-let {x = y} {A = B} d₁ d₂) =
        cᵢ (sym (up-+* wk _ _ _)) (t-let (W-i wk f₁ d₁) (W-i (wk-under y B wk) f₂ d₂))
    W-i wk (fS , fL , fR) (t-case {xL = xL} {xR = xR} {A = AL} {B = AR} dS dL dR) =
        cᵢ (sym (up-+⊔ wk _ _ _)) (t-case (W-i wk fS dS) (W-i (wk-under xL AL wk) fL dL) (W-i (wk-under xR AR wk) fR dR))
    W-i wk (f₁ , f₂) (t-binop-arith o d₁ d₂) = cᵢ (sym (up-+ wk _ _)) (t-binop-arith o (W-i wk f₁ d₁) (W-i wk f₂ d₂))
    W-i wk (f₁ , f₂) (t-binop-arith-float o d₁ d₂) = cᵢ (sym (up-+ wk _ _)) (t-binop-arith-float o (W-i wk f₁ d₁) (W-i wk f₂ d₂))
    W-i wk (f₁ , f₂) (t-binop-arith-float-il o d₁ d₂) = cᵢ (sym (up-+ wk _ _)) (t-binop-arith-float-il o (W-i wk f₁ d₁) (W-i wk f₂ d₂))
    W-i wk (f₁ , f₂) (t-binop-arith-float-ir o d₁ d₂) = cᵢ (sym (up-+ wk _ _)) (t-binop-arith-float-ir o (W-i wk f₁ d₁) (W-i wk f₂ d₂))
    W-i wk (f₁ , f₂) (t-binop-cmp o d₁ d₂) = cᵢ (sym (up-+ wk _ _)) (t-binop-cmp o (W-i wk f₁ d₁) (W-i wk f₂ d₂))
    W-i wk (_ , fr) (t-id-app d) = cᵢ (sym (up-z+M wk _)) (t-id-app (W-i wk fr d))
    W-i wk (_ , fr) (t-fst-app d) = cᵢ (sym (up-z+M wk _)) (t-fst-app (W-i wk fr d))
    W-i wk (_ , fr) (t-snd-app d) = cᵢ (sym (up-z+M wk _)) (t-snd-app (W-i wk fr d))
    W-i wk (_ , fr) (t-terminal-app d) = cᵢ (sym (up-z+M wk _)) (t-terminal-app (W-i wk fr d))
    W-i wk (_ , fr) (t-apply-app-infer d) = cᵢ (sym (up-z+M wk _)) (t-apply-app-infer (W-i wk fr d))
    W-i wk (_ , fr) (t-apply-eff-app-infer d) = cᵢ (sym (up-z+M wk _)) (t-apply-eff-app-infer (W-i wk fr d))
    W-i wk (_ , fr) (t-Out-app-infer wf eq d) = cᵢ (sym (up-z+M wk _)) (t-Out-app-infer wf eq (W-i wk fr d))
    W-i wk (f₁ , f₂) (t-app ah dF dX) = cᵢ (sym (up-+* wk _ _ _)) (t-app ah (W-i wk f₁ dF) (W-c wk f₂ dX))
    W-i wk (f₁ , f₂) (t-effApp ah dF dX) = cᵢ (sym (up-+ wk _ _)) (t-effApp ah (W-i wk f₁ dF) (W-c wk f₂ dX))
    W-i wk (f₁ , f₂) (t-app-spine ah dX dF) = cᵢ (sym (up-+* wk _ _ _)) (t-app-spine ah (W-i wk f₂ dX) (W-d wk f₁ dF))
    W-c wk _ t-id-check = cᶜ (sym (up-zero wk)) t-id-check
    W-c wk _ t-fst-check = cᶜ (sym (up-zero wk)) t-fst-check
    W-c wk _ t-snd-check = cᶜ (sym (up-zero wk)) t-snd-check
    W-c wk _ t-terminal-morph-check = cᶜ (sym (up-zero wk)) t-terminal-morph-check
    W-c wk _ t-initial-morph-check = cᶜ (sym (up-zero wk)) t-initial-morph-check
    W-c wk _ t-inl-morph-check = cᶜ (sym (up-zero wk)) t-inl-morph-check
    W-c wk _ t-inr-morph-check = cᶜ (sym (up-zero wk)) t-inr-morph-check
    W-c wk ((_ , f₁) , f₂) (t-compose-check-g dg df) = cᶜ (sym (up-+ wk _ _)) (t-compose-check-g (W-d wk f₂ dg) (W-c wk f₁ df))
    W-c wk ((_ , f₁) , f₂) (t-compose-check-f wf p dg) = cᶜ (sym (up-+ wk _ _)) (t-compose-check-f (W-i wk f₁ wf) p (W-c wk f₂ dg))
    W-c wk ((_ , f₁) , f₂) (t-case-copair-check df dg) = cᶜ (sym (up-+ wk _ _)) (t-case-copair-check (W-c wk f₁ df) (W-c wk f₂ dg))
    W-c wk ((_ , f₁) , f₂) (t-pair-morph-check df dg) = cᶜ (sym (up-+ wk _ _)) (t-pair-morph-check (W-c wk f₁ df) (W-c wk f₂ dg))
    W-c wk (_ , fr) (t-curry-check d) = t-curry-check (W-c wk fr d)
    W-c wk _ (t-cata-check wf dalg) = cᶜ (sym (up-zero wk)) (t-cata-check wf dalg)
    W-c wk _ (t-ana-check wf dco) = cᶜ (sym (up-zero wk)) (t-ana-check wf dco)
    W-c wk fr (t-sub d p) = t-sub (W-i wk fr d) p
    W-c wk fb (t-lam {x = y} {A = B} leq body) = t-lam leq (W-c (wk-under y B wk) fb body)
    W-c wk (f₁ , f₂) (t-pair-lit-check d₁ d₂) = cᶜ (sym (up-+ wk _ _)) (t-pair-lit-check (W-c wk f₁ d₁) (W-c wk f₂ d₂))
    W-c wk (_ , fr) (t-In-app-check wf d) = cᶜ (sym (up-z+M wk _)) (t-In-app-check wf (W-c wk fr d))
    W-c wk (_ , fr) (t-apply-check d) = cᶜ (sym (up-z+M wk _)) (t-apply-check (W-i wk fr d))
    W-c wk (_ , fr) (t-inl-app-check d) = cᶜ (sym (up-z+M wk _)) (t-inl-app-check (W-c wk fr d))
    W-c wk (_ , fr) (t-inr-app-check d) = cᶜ (sym (up-z+M wk _)) (t-inr-app-check (W-c wk fr d))
    W-c wk (_ , fr) (t-initial-app-check d) = cᶜ (sym (up-z+M wk _)) (t-initial-app-check (W-c wk fr d))
    W-c wk fr (t-var-poly-instantiate {x = z} ln li lp ¬g body) =
        cᶜ (sym (up-zero wk)) (t-var-poly-instantiate (wnone (wloc wk z fr) ln) li lp ¬g body)
    W-d wk fr (d-infer w sb gr) = d-infer (W-i wk fr w) sb gr
    W-d wk fb (d-lam {x = y} {A = B} leq body) = d-lam leq (W-i (wk-under y B wk) fb body)
    W-d wk ((_ , f₁) , f₂) (d-compose dg df) = cᵈ (sym (up-+ wk _ _)) (d-compose (W-d wk f₂ dg) (W-d wk f₁ df))
    W-d wk _ d-id = cᵈ (sym (up-zero wk)) d-id
    W-d wk _ d-fst = cᵈ (sym (up-zero wk)) d-fst
    W-d wk _ d-snd = cᵈ (sym (up-zero wk)) d-snd
    W-d wk _ d-terminal = cᵈ (sym (up-zero wk)) d-terminal
    W-d wk _ d-initial = cᵈ (sym (up-zero wk)) d-initial
    W-d wk ((_ , f₁) , f₂) (d-case df dg) = cᵈ (sym (up-+ wk _ _)) (d-case (W-d wk f₁ df) (W-d wk f₂ dg))
    W-d wk ((_ , f₁) , f₂) (d-pair df dg) = cᵈ (sym (up-+ wk _ _)) (d-pair (W-d wk f₁ df) (W-d wk f₂ dg))
    W-d wk _ (d-cata wf dalg) = cᵈ (sym (up-zero wk)) (d-cata wf dalg)

------------------------------------------------------------------------
-- The substitution.
------------------------------------------------------------------------

module Sub (x : String) (ê : RawExpr) where

  bindSh : ∀ {y : String} → Dec (y ≡ x) → Bool → Bool
  bindSh (yes _) _ = true
  bindSh (no _) sh = sh

  subVar : Bool → (y : String) → Dec (y ≡ x) → RawExpr
  subVar _     y (no _)  = RVar y
  subVar false y (yes _) = ê
  subVar true  y (yes _) = RVar y

  -- `sh`: is `x` shadowed by a local here? An algebra position resets it.
  sub : Bool → RawExpr → RawExpr
  sub sh (RVar y) = subVar sh y (y StrProp.≟ x)
  sub sh (RQualified n a) = RQualified n a
  sub sh (RResolved c) = RResolved c
  sub sh (RApp f a) = RApp (sub sh f) (sub (scopeOf (isAlg f) sh) a)
  sub sh (RLam y b) = RLam y (sub (bindSh (y StrProp.≟ x) sh) b)
  sub sh (RLet y a b) = RLet y (sub sh a) (sub (bindSh (y StrProp.≟ x) sh) b)
  sub sh (RPair a b) = RPair (sub sh a) (sub sh b)
  sub sh (RDestruct s xL l xR r) =
    RDestruct (sub sh s) xL (sub (bindSh (xL StrProp.≟ x) sh) l) xR (sub (bindSh (xR StrProp.≟ x) sh) r)
  sub sh RUnit = RUnit
  sub sh (RInt n) = RInt n
  sub sh (RFloat i f l p) = RFloat i f l p
  sub sh (RStringLit t) = RStringLit t
  sub sh (RAnnot b T) = RAnnot (sub sh b) T
  sub sh (RBinOp o a b) = RBinOp o (sub sh a) (sub sh b)
  sub sh (RUnaryOp o a) = RUnaryOp o (sub sh a)
  sub sh (RAna F a) = RAna F (sub sh a)

------------------------------------------------------------------------
-- The unfolding.
------------------------------------------------------------------------

module Unfolding
  (x : String) (A : Type) (e : RawExpr) (s : PolyType) (g : Ground s)
  (eqA : extractGround s g ≡ A)
  (imps : Imports) (P : PolyCtx)
  (noImp : lookupImport imps x ≡ nothing)
  (eD : ctxWithImportsAndPolys imps P ⊢ᶜ e ∶ A ⨾ zeroUsage)
  where

  open Sub x (RAnnot e A) public
  open Weaken imps P using (WK; wk-base; W-c)

  P′ : PolyCtx
  P′ = (x , s , e) ∷ P

  lpp-head : lookupPolyPrefix P′ x ≡ just (s , e , P)
  lpp-head with x StrProp.≟ x
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  lpp-skip : ∀ {y : String} {r} → y ≢ x → lookupPolyPrefix P′ y ≡ r → lookupPolyPrefix P y ≡ r
  lpp-skip {y} y≢x eq with x StrProp.≟ y
  ... | yes x≡y = ⊥-elim (y≢x (sym x≡y))
  ... | no _ = eq

  -- The replacement classifies as `other`, like the variable it replaces.
  sub-head : ∀ (sh : Bool) (f : RawExpr) → classifyAppHead (sub sh f) ≡ classifyAppHead f
  sub-head sh (RVar y) with y StrProp.≟ x | sh
  ... | no _ | _ = refl
  ... | yes _ | false = refl
  ... | yes _ | true = refl
  sub-head sh (RApp (RVar y) a) with y StrProp.≟ x | sh
  ... | no _ | _ = refl
  ... | yes _ | false = refl
  ... | yes _ | true = refl
  sub-head sh (RApp (RResolved c) a) = app-head-irr (RResolved c) _ a
  sub-head sh (RApp (RQualified _ _) a) = refl
  sub-head sh (RApp (RApp _ _) a) = refl
  sub-head sh (RApp (RLam _ _) a) = refl
  sub-head sh (RApp (RLet _ _ _) a) = refl
  sub-head sh (RApp (RPair _ _) a) = refl
  sub-head sh (RApp (RDestruct _ _ _ _ _) a) = refl
  sub-head sh (RApp RUnit a) = refl
  sub-head sh (RApp (RInt _) a) = refl
  sub-head sh (RApp (RFloat _ _ _ _) a) = refl
  sub-head sh (RApp (RStringLit _) a) = refl
  sub-head sh (RApp (RAnnot _ _) a) = refl
  sub-head sh (RApp (RBinOp _ _ _) a) = refl
  sub-head sh (RApp (RUnaryOp _ _) a) = refl
  sub-head sh (RApp (RAna _ _) a) = refl
  sub-head sh (RQualified _ _) = refl
  sub-head sh (RResolved _) = refl
  sub-head sh (RLam _ _) = refl
  sub-head sh (RLet _ _ _) = refl
  sub-head sh (RPair _ _) = refl
  sub-head sh (RDestruct _ _ _ _ _) = refl
  sub-head sh RUnit = refl
  sub-head sh (RInt _) = refl
  sub-head sh (RFloat _ _ _ _) = refl
  sub-head sh (RStringLit _) = refl
  sub-head sh (RAnnot _ _) = refl
  sub-head sh (RBinOp _ _ _) = refl
  sub-head sh (RUnaryOp _ _) = refl
  sub-head sh (RAna _ _) = refl

  -- The scope invariant: the flag says whether `x` is a local here, and the
  -- locals avoid every variable of `e`.
  record SR {n} (sh : Bool) (G : Ctx) (Δ : SC.Ctx n) : Set where
    field
      noX  : sh ≡ false → lookupLocal-go x G Δ ≡ nothing
      yesX : sh ≡ true → lookupLocal-go x G Δ ≡ nothing → ⊥
      clr  : Fr (λ z → lookupLocal-go z G Δ ≡ nothing) e

  sr-ext : ∀ {n sh} {G : Ctx} {Δ : SC.Ctx n} → SR sh G Δ → (y : String) (B : Type)
         → Fr (λ z → z ≢ y) e
         → SR (bindSh (y StrProp.≟ x) sh) (extendCtx G y B) (Δ SC., B)
  sr-ext r y B ny with y StrProp.≟ x
  ... | yes y≡x = record
        { noX = λ ()
        ; yesX = λ _ → hit-ext (sym y≡x)
        ; clr = Fr-map₂ (λ z l z≢y → miss-ext z≢y l) e (SR.clr r) ny }
  ... | no y≢x = record
        { noX = λ q → miss-ext (λ x≡y → y≢x (sym x≡y)) (SR.noX r q)
        ; yesX = λ q o → SR.yesX r q (miss-ext← (λ x≡y → y≢x (sym x≡y)) o)
        ; clr = Fr-map₂ (λ z l z≢y → miss-ext z≢y l) e (SR.clr r) ny }

  sr-alg : SR false Context.∅ SC.∅
  sr-alg = record { noX = λ _ → refl ; yesX = λ () ; clr = Fr-triv (λ _ → refl) e }

  Dc : ∀ {n} → Ctx → SC.Ctx n → ℕ → NamedCtx
  Dc {n} G Δ fr = mkCtx n G Δ fr imps P′
  Lc : ∀ {n} → Ctx → SC.Ctx n → ℕ → NamedCtx
  Lc {n} G Δ fr = mkCtx n G Δ fr imps P

  -- The variable cases, one per rule that can derive a variable.
  s-local : ∀ {n G Δ fr sh} → SR {n} sh G Δ → (y : String) (d : Dec (y ≡ x)) → ∀ {T U eV}
          → lookupLocal-go y G Δ ≡ just (T , U , eV) → Lc G Δ fr ⊢ᵢ subVar sh y d ∶ T ⨾ U
  s-local {G = G} {Δ = Δ} {sh = false} r y (yes y≡x) eq =
    ⊥-elim (just≢nothing (trans (sym eq) (subst (λ z → lookupLocal-go z G Δ ≡ nothing) (sym y≡x) (SR.noX r refl))))
  s-local {sh = true} r y (yes _) eq = t-var-local eq
  s-local r y (no _) eq = t-var-local eq

  s-import : ∀ {n G Δ fr sh} → SR {n} sh G Δ → (y : String) (d : Dec (y ≡ x)) → ∀ {T}
           → ¬ GenWord y → lookupLocal-go y G Δ ≡ nothing → lookupImport imps y ≡ just T → IsConcrete T
           → Lc G Δ fr ⊢ᵢ subVar sh y d ∶ T ⨾ zeroUsage
  s-import r y (yes y≡x) _ _ li _ =
    ⊥-elim (just≢nothing (trans (sym li) (subst (λ z → lookupImport imps z ≡ nothing) (sym y≡x) noImp)))
  s-import r y (no _) ¬gw ln li c = t-var-import ¬gw ln li c

  s-poly-infer : ∀ {n G Δ fr sh} → SR {n} sh G Δ → (y : String) (d : Dec (y ≡ x))
                 {T : Type} {schema : PolyType} {body : RawExpr} {prefix : PolyCtx} {g′ : Ground schema}
               → lookupLocal-go y G Δ ≡ nothing → lookupImport imps y ≡ nothing
               → lookupPolyPrefix P′ y ≡ just (schema , body , prefix) → Ground schema
               → T ≡ extractGround schema g′
               → ctxWithImportsAndPolys imps prefix ⊢ᶜ body ∶ T ⨾ zeroUsage
               → Lc G Δ fr ⊢ᵢ subVar sh y d ∶ T ⨾ zeroUsage
  s-poly-infer {G = G} {Δ = Δ} {sh = true} r y (yes y≡x) ln _ _ _ _ _ =
    ⊥-elim (SR.yesX r refl (subst (λ z → lookupLocal-go z G Δ ≡ nothing) y≡x ln))
  s-poly-infer {G = G} {Δ = Δ} {sh = false} r y (yes y≡x) {g′ = g′} _ _ lp _ eT _
    with trans (sym lpp-head) (subst (λ z → lookupPolyPrefix P′ z ≡ _) y≡x lp)
  ... | refl =
    subst (λ T → _ ⊢ᵢ RAnnot e A ∶ T ⨾ zeroUsage) (sym (trans eT (trans (extractGround-irr s g′ g) eqA)))
      (t-annot (W-c wk-base (SR.clr r) eD))
  s-poly-infer r y (no y≢x) ln li lp gr eT body =
    t-var-poly-instantiate-infer ln li (lpp-skip y≢x lp) gr eT body

  s-poly : ∀ {n G Δ fr sh} → SR {n} sh G Δ → (y : String) (d : Dec (y ≡ x))
           {T : Type} {schema : PolyType} {body : RawExpr} {prefix : PolyCtx}
         → lookupLocal-go y G Δ ≡ nothing → lookupImport imps y ≡ nothing
         → lookupPolyPrefix P′ y ≡ just (schema , body , prefix) → ¬ Ground schema
         → ctxWithImportsAndPolys imps prefix ⊢ᶜ body ∶ T ⨾ zeroUsage
         → Lc G Δ fr ⊢ᶜ subVar sh y d ∶ T ⨾ zeroUsage
  s-poly r y (yes y≡x) _ _ lp ¬g _
    with trans (sym lpp-head) (subst (λ z → lookupPolyPrefix P′ z ≡ _) y≡x lp)
  ... | refl = ⊥-elim (¬g g)
  s-poly r y (no y≢x) ln li lp ¬g body = t-var-poly-instantiate ln li (lpp-skip y≢x lp) ¬g body

  -- An application whose head is not a builtin keeps the scope for its argument.
  app-scope : ∀ {n G Δ fr sh} {f a : RawExpr} {T U}
            → classifyAppHead f ≡ nothing
            → Lc {n} G Δ fr ⊢ᵢ RApp (sub sh f) (sub sh a) ∶ T ⨾ U
            → Lc G Δ fr ⊢ᵢ sub sh (RApp f a) ∶ T ⨾ U
  app-scope {G = G} {Δ = Δ} {fr = fr} {sh = sh} {f = f} {a = a} {T} {U} ah d =
    subst (λ b → Lc G Δ fr ⊢ᵢ RApp (sub sh f) (sub (scopeOf b sh) a) ∶ T ⨾ U) (sym (isAlg-other ah)) d

  head-ok : ∀ {sh f} → classifyAppHead f ≡ nothing → classifyAppHead (sub sh f) ≡ nothing
  head-ok {sh} {f} ah = trans (sub-head sh f) ah

  mutual
    S-i : ∀ {n G Δ fr sh} → SR {n} sh G Δ → ∀ {b T U}
        → NC e b → Dc G Δ fr ⊢ᵢ b ∶ T ⨾ U → Lc G Δ fr ⊢ᵢ sub sh b ∶ T ⨾ U
    S-c : ∀ {n G Δ fr sh} → SR {n} sh G Δ → ∀ {b T U}
        → NC e b → Dc G Δ fr ⊢ᶜ b ∶ T ⨾ U → Lc G Δ fr ⊢ᶜ sub sh b ∶ T ⨾ U
    S-d : ∀ {n G Δ fr sh} → SR {n} sh G Δ → ∀ {b A′ π B U}
        → NC e b → Dc G Δ fr ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ U → Lc G Δ fr ⊢ᵈ sub sh b ∶ A′ ⇒[ π ]↦ B ⨾ U

    S-i r _ (t-int n) = t-int n
    S-i r _ (t-float i f l p) = t-float i f l p
    S-i r _ (t-str t) = t-str t
    S-i r _ t-unit = t-unit
    S-i r _ t-unit-var = t-unit-var
    S-i r _ (t-var-local {x = y} eq) = s-local r y (y StrProp.≟ x) eq
    S-i r _ (t-var-qualified l c) = t-var-qualified l c
    S-i r _ (t-var-resolved ng l c) = t-var-resolved ng l c
    S-i r _ (t-var-import {x = y} ¬gw ln li c) = s-import r y (y StrProp.≟ x) ¬gw ln li c
    S-i r _ (t-var-poly-instantiate-infer {x = y} ln li lp gr eT body) =
        s-poly-infer r y (y StrProp.≟ x) ln li lp gr eT body
    S-i r nc (t-annot c) = t-annot (S-c r nc c)
    S-i r (n₁ , n₂) (t-pair d₁ d₂) = t-pair (S-i r n₁ d₁) (S-i r n₂ d₂)
    S-i r nc (t-neg d) = t-neg (S-i r nc d)
    S-i r _ (t-neg-float i f l p) = t-neg-float i f l p
    S-i r (ny , n₁ , n₂) (t-let {x = y} {A = B} d₁ d₂) = t-let (S-i r n₁ d₁) (S-i (sr-ext r y B ny) n₂ d₂)
    S-i r (nS , nL , cL , nR , cR) (t-case {xL = xL} {xR = xR} {A = AL} {B = AR} dS dL dR) =
        t-case (S-i r nS dS) (S-i (sr-ext r xL AL nL) cL dL) (S-i (sr-ext r xR AR nR) cR dR)
    S-i r (n₁ , n₂) (t-binop-arith o d₁ d₂) = t-binop-arith o (S-i r n₁ d₁) (S-i r n₂ d₂)
    S-i r (n₁ , n₂) (t-binop-arith-float o d₁ d₂) = t-binop-arith-float o (S-i r n₁ d₁) (S-i r n₂ d₂)
    S-i r (n₁ , n₂) (t-binop-arith-float-il o d₁ d₂) = t-binop-arith-float-il o (S-i r n₁ d₁) (S-i r n₂ d₂)
    S-i r (n₁ , n₂) (t-binop-arith-float-ir o d₁ d₂) = t-binop-arith-float-ir o (S-i r n₁ d₁) (S-i r n₂ d₂)
    S-i r (n₁ , n₂) (t-binop-cmp o d₁ d₂) = t-binop-cmp o (S-i r n₁ d₁) (S-i r n₂ d₂)
    S-i r (_ , nc) (t-id-app d) = t-id-app (S-i r nc d)
    S-i r (_ , nc) (t-fst-app d) = t-fst-app (S-i r nc d)
    S-i r (_ , nc) (t-snd-app d) = t-snd-app (S-i r nc d)
    S-i r (_ , nc) (t-terminal-app d) = t-terminal-app (S-i r nc d)
    S-i r (_ , nc) (t-apply-app-infer d) = t-apply-app-infer (S-i r nc d)
    S-i r (_ , nc) (t-apply-eff-app-infer d) = t-apply-eff-app-infer (S-i r nc d)
    S-i r (_ , nc) (t-Out-app-infer wf eq d) = t-Out-app-infer wf eq (S-i r nc d)
    S-i r (n₁ , n₂) (t-app {x = xa} ah dF dX) = app-scope {a = xa} ah (t-app (head-ok ah) (S-i r n₁ dF) (S-c r n₂ dX))
    S-i r (n₁ , n₂) (t-effApp {x = xa} ah dF dX) = app-scope {a = xa} ah (t-effApp (head-ok ah) (S-i r n₁ dF) (S-c r n₂ dX))
    S-i r (n₁ , n₂) (t-app-spine {arg = xa} ah dX dF) = app-scope {a = xa} ah (t-app-spine (head-ok ah) (S-i r n₂ dX) (S-d r n₁ dF))
    S-c r _ t-id-check = t-id-check
    S-c r _ t-fst-check = t-fst-check
    S-c r _ t-snd-check = t-snd-check
    S-c r _ t-terminal-morph-check = t-terminal-morph-check
    S-c r _ t-initial-morph-check = t-initial-morph-check
    S-c r _ t-inl-morph-check = t-inl-morph-check
    S-c r _ t-inr-morph-check = t-inr-morph-check
    S-c r ((_ , n₁) , n₂) (t-compose-check-g dg df) = t-compose-check-g (S-d r n₂ dg) (S-c r n₁ df)
    S-c r ((_ , n₁) , n₂) (t-compose-check-f wf p dg) = t-compose-check-f (S-i r n₁ wf) p (S-c r n₂ dg)
    S-c r ((_ , n₁) , n₂) (t-case-copair-check df dg) = t-case-copair-check (S-c r n₁ df) (S-c r n₂ dg)
    S-c r ((_ , n₁) , n₂) (t-pair-morph-check df dg) = t-pair-morph-check (S-c r n₁ df) (S-c r n₂ dg)
    S-c r (_ , nc) (t-curry-check d) = t-curry-check (S-c r nc d)
    S-c r (_ , nc) (t-cata-check wf dalg) = t-cata-check wf (S-c sr-alg nc dalg)
    S-c r (_ , nc) (t-ana-check wf dco) = t-ana-check wf (S-c sr-alg nc dco)
    S-c r nc (t-sub d p) = t-sub (S-i r nc d) p
    S-c r (ny , nb) (t-lam {x = y} {A = B} leq body) = t-lam leq (S-c (sr-ext r y B ny) nb body)
    S-c r (n₁ , n₂) (t-pair-lit-check d₁ d₂) = t-pair-lit-check (S-c r n₁ d₁) (S-c r n₂ d₂)
    S-c r (_ , nc) (t-In-app-check wf d) = t-In-app-check wf (S-c r nc d)
    S-c r (_ , nc) (t-apply-check d) = t-apply-check (S-i r nc d)
    S-c r (_ , nc) (t-inl-app-check d) = t-inl-app-check (S-c r nc d)
    S-c r (_ , nc) (t-inr-app-check d) = t-inr-app-check (S-c r nc d)
    S-c r (_ , nc) (t-initial-app-check d) = t-initial-app-check (S-c r nc d)
    S-c r _ (t-var-poly-instantiate {x = y} ln li lp ¬g body) = s-poly r y (y StrProp.≟ x) ln li lp ¬g body
    S-d r nc (d-infer w sb gr) = d-infer (S-i r nc w) sb gr
    S-d r (ny , nb) (d-lam {x = y} {A = B} leq body) = d-lam leq (S-i (sr-ext r y B ny) nb body)
    S-d r ((_ , n₁) , n₂) (d-compose dg df) = d-compose (S-d r n₂ dg) (S-d r n₁ df)
    S-d r _ d-id = d-id
    S-d r _ d-fst = d-fst
    S-d r _ d-snd = d-snd
    S-d r _ d-terminal = d-terminal
    S-d r _ d-initial = d-initial
    S-d r ((_ , n₁) , n₂) (d-case df dg) = d-case (S-d r n₁ df) (S-d r n₂ dg)
    S-d r ((_ , n₁) , n₂) (d-pair df dg) = d-pair (S-d r n₁ df) (S-d r n₂ dg)
    S-d r (_ , nc) (d-cata wf dalg) = d-cata wf (S-i sr-alg nc dalg)


  ------------------------------------------------------------------------
  -- Inverting the substitution: it changes nothing but an unshadowed `x`,
  -- which becomes `(e : A)`; so a substituted term of any other shape came
  -- from a term of the same shape.
  ------------------------------------------------------------------------

  inv-RQualified : ∀ {sh b n a} → sub sh b ≡ (RQualified n a)
            → (b ≡ RQualified n a)
  inv-RQualified {b = (RQualified n a)} refl = refl
  inv-RQualified {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RQualified {b = (RAnnot _ _)} ()
  inv-RQualified {b = (RResolved _)} ()
  inv-RQualified {b = (RApp _ _)} ()
  inv-RQualified {b = (RLam _ _)} ()
  inv-RQualified {b = (RLet _ _ _)} ()
  inv-RQualified {b = (RPair _ _)} ()
  inv-RQualified {b = (RDestruct _ _ _ _ _)} ()
  inv-RQualified {b = RUnit} ()
  inv-RQualified {b = (RInt _)} ()
  inv-RQualified {b = (RFloat _ _ _ _)} ()
  inv-RQualified {b = (RStringLit _)} ()
  inv-RQualified {b = (RBinOp _ _ _)} ()
  inv-RQualified {b = (RUnaryOp _ _)} ()
  inv-RQualified {b = (RAna _ _)} ()
  inv-RResolved : ∀ {sh b c} → sub sh b ≡ (RResolved c)
            → (b ≡ RResolved c)
  inv-RResolved {b = (RResolved c)} refl = refl
  inv-RResolved {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RResolved {b = (RAnnot _ _)} ()
  inv-RResolved {b = (RQualified _ _)} ()
  inv-RResolved {b = (RApp _ _)} ()
  inv-RResolved {b = (RLam _ _)} ()
  inv-RResolved {b = (RLet _ _ _)} ()
  inv-RResolved {b = (RPair _ _)} ()
  inv-RResolved {b = (RDestruct _ _ _ _ _)} ()
  inv-RResolved {b = RUnit} ()
  inv-RResolved {b = (RInt _)} ()
  inv-RResolved {b = (RFloat _ _ _ _)} ()
  inv-RResolved {b = (RStringLit _)} ()
  inv-RResolved {b = (RBinOp _ _ _)} ()
  inv-RResolved {b = (RUnaryOp _ _)} ()
  inv-RResolved {b = (RAna _ _)} ()
  inv-RApp : ∀ {sh b f a} → sub sh b ≡ (RApp f a)
            → ∃[ f₀ ] ∃[ a₀ ] (b ≡ RApp f₀ a₀ × sub (sh) f₀ ≡ f × sub (scopeOf (isAlg f₀) sh) a₀ ≡ a)
  inv-RApp {b = (RApp f₀ a₀)} refl = f₀ , a₀ , refl , refl , refl
  inv-RApp {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RApp {b = (RAnnot _ _)} ()
  inv-RApp {b = (RQualified _ _)} ()
  inv-RApp {b = (RResolved _)} ()
  inv-RApp {b = (RLam _ _)} ()
  inv-RApp {b = (RLet _ _ _)} ()
  inv-RApp {b = (RPair _ _)} ()
  inv-RApp {b = (RDestruct _ _ _ _ _)} ()
  inv-RApp {b = RUnit} ()
  inv-RApp {b = (RInt _)} ()
  inv-RApp {b = (RFloat _ _ _ _)} ()
  inv-RApp {b = (RStringLit _)} ()
  inv-RApp {b = (RBinOp _ _ _)} ()
  inv-RApp {b = (RUnaryOp _ _)} ()
  inv-RApp {b = (RAna _ _)} ()
  inv-RLam : ∀ {sh b y u} → sub sh b ≡ (RLam y u)
            → ∃[ u₀ ] (b ≡ RLam y u₀ × sub (bindSh (y StrProp.≟ x) sh) u₀ ≡ u)
  inv-RLam {b = (RLam y u₀)} refl = u₀ , refl , refl
  inv-RLam {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RLam {b = (RAnnot _ _)} ()
  inv-RLam {b = (RQualified _ _)} ()
  inv-RLam {b = (RResolved _)} ()
  inv-RLam {b = (RApp _ _)} ()
  inv-RLam {b = (RLet _ _ _)} ()
  inv-RLam {b = (RPair _ _)} ()
  inv-RLam {b = (RDestruct _ _ _ _ _)} ()
  inv-RLam {b = RUnit} ()
  inv-RLam {b = (RInt _)} ()
  inv-RLam {b = (RFloat _ _ _ _)} ()
  inv-RLam {b = (RStringLit _)} ()
  inv-RLam {b = (RBinOp _ _ _)} ()
  inv-RLam {b = (RUnaryOp _ _)} ()
  inv-RLam {b = (RAna _ _)} ()
  inv-RLet : ∀ {sh b y a u} → sub sh b ≡ (RLet y a u)
            → ∃[ a₀ ] ∃[ u₀ ] (b ≡ RLet y a₀ u₀ × sub (sh) a₀ ≡ a × sub (bindSh (y StrProp.≟ x) sh) u₀ ≡ u)
  inv-RLet {b = (RLet y a₀ u₀)} refl = a₀ , u₀ , refl , refl , refl
  inv-RLet {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RLet {b = (RAnnot _ _)} ()
  inv-RLet {b = (RQualified _ _)} ()
  inv-RLet {b = (RResolved _)} ()
  inv-RLet {b = (RApp _ _)} ()
  inv-RLet {b = (RLam _ _)} ()
  inv-RLet {b = (RPair _ _)} ()
  inv-RLet {b = (RDestruct _ _ _ _ _)} ()
  inv-RLet {b = RUnit} ()
  inv-RLet {b = (RInt _)} ()
  inv-RLet {b = (RFloat _ _ _ _)} ()
  inv-RLet {b = (RStringLit _)} ()
  inv-RLet {b = (RBinOp _ _ _)} ()
  inv-RLet {b = (RUnaryOp _ _)} ()
  inv-RLet {b = (RAna _ _)} ()
  inv-RPair : ∀ {sh b a u} → sub sh b ≡ (RPair a u)
            → ∃[ a₀ ] ∃[ u₀ ] (b ≡ RPair a₀ u₀ × sub (sh) a₀ ≡ a × sub (sh) u₀ ≡ u)
  inv-RPair {b = (RPair a₀ u₀)} refl = a₀ , u₀ , refl , refl , refl
  inv-RPair {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RPair {b = (RAnnot _ _)} ()
  inv-RPair {b = (RQualified _ _)} ()
  inv-RPair {b = (RResolved _)} ()
  inv-RPair {b = (RApp _ _)} ()
  inv-RPair {b = (RLam _ _)} ()
  inv-RPair {b = (RLet _ _ _)} ()
  inv-RPair {b = (RDestruct _ _ _ _ _)} ()
  inv-RPair {b = RUnit} ()
  inv-RPair {b = (RInt _)} ()
  inv-RPair {b = (RFloat _ _ _ _)} ()
  inv-RPair {b = (RStringLit _)} ()
  inv-RPair {b = (RBinOp _ _ _)} ()
  inv-RPair {b = (RUnaryOp _ _)} ()
  inv-RPair {b = (RAna _ _)} ()
  inv-RDestruct : ∀ {sh b xL xR s l r} → sub sh b ≡ (RDestruct s xL l xR r)
            → ∃[ s₀ ] ∃[ l₀ ] ∃[ r₀ ] (b ≡ RDestruct s₀ xL l₀ xR r₀ × sub (sh) s₀ ≡ s × sub (bindSh (xL StrProp.≟ x) sh) l₀ ≡ l × sub (bindSh (xR StrProp.≟ x) sh) r₀ ≡ r)
  inv-RDestruct {b = (RDestruct s₀ xL l₀ xR r₀)} refl = s₀ , l₀ , r₀ , refl , refl , refl , refl
  inv-RDestruct {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RDestruct {b = (RAnnot _ _)} ()
  inv-RDestruct {b = (RQualified _ _)} ()
  inv-RDestruct {b = (RResolved _)} ()
  inv-RDestruct {b = (RApp _ _)} ()
  inv-RDestruct {b = (RLam _ _)} ()
  inv-RDestruct {b = (RLet _ _ _)} ()
  inv-RDestruct {b = (RPair _ _)} ()
  inv-RDestruct {b = RUnit} ()
  inv-RDestruct {b = (RInt _)} ()
  inv-RDestruct {b = (RFloat _ _ _ _)} ()
  inv-RDestruct {b = (RStringLit _)} ()
  inv-RDestruct {b = (RBinOp _ _ _)} ()
  inv-RDestruct {b = (RUnaryOp _ _)} ()
  inv-RDestruct {b = (RAna _ _)} ()
  inv-RUnit : ∀ {sh b} → sub sh b ≡ RUnit
            → (b ≡ RUnit)
  inv-RUnit {b = RUnit} refl = refl
  inv-RUnit {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RUnit {b = (RAnnot _ _)} ()
  inv-RUnit {b = (RQualified _ _)} ()
  inv-RUnit {b = (RResolved _)} ()
  inv-RUnit {b = (RApp _ _)} ()
  inv-RUnit {b = (RLam _ _)} ()
  inv-RUnit {b = (RLet _ _ _)} ()
  inv-RUnit {b = (RPair _ _)} ()
  inv-RUnit {b = (RDestruct _ _ _ _ _)} ()
  inv-RUnit {b = (RInt _)} ()
  inv-RUnit {b = (RFloat _ _ _ _)} ()
  inv-RUnit {b = (RStringLit _)} ()
  inv-RUnit {b = (RBinOp _ _ _)} ()
  inv-RUnit {b = (RUnaryOp _ _)} ()
  inv-RUnit {b = (RAna _ _)} ()
  inv-RInt : ∀ {sh b n} → sub sh b ≡ (RInt n)
            → (b ≡ RInt n)
  inv-RInt {b = (RInt n)} refl = refl
  inv-RInt {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RInt {b = (RAnnot _ _)} ()
  inv-RInt {b = (RQualified _ _)} ()
  inv-RInt {b = (RResolved _)} ()
  inv-RInt {b = (RApp _ _)} ()
  inv-RInt {b = (RLam _ _)} ()
  inv-RInt {b = (RLet _ _ _)} ()
  inv-RInt {b = (RPair _ _)} ()
  inv-RInt {b = (RDestruct _ _ _ _ _)} ()
  inv-RInt {b = RUnit} ()
  inv-RInt {b = (RFloat _ _ _ _)} ()
  inv-RInt {b = (RStringLit _)} ()
  inv-RInt {b = (RBinOp _ _ _)} ()
  inv-RInt {b = (RUnaryOp _ _)} ()
  inv-RInt {b = (RAna _ _)} ()
  inv-RFloat : ∀ {sh b i f l p} → sub sh b ≡ (RFloat i f l p)
            → (b ≡ RFloat i f l p)
  inv-RFloat {b = (RFloat i f l p)} refl = refl
  inv-RFloat {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RFloat {b = (RAnnot _ _)} ()
  inv-RFloat {b = (RQualified _ _)} ()
  inv-RFloat {b = (RResolved _)} ()
  inv-RFloat {b = (RApp _ _)} ()
  inv-RFloat {b = (RLam _ _)} ()
  inv-RFloat {b = (RLet _ _ _)} ()
  inv-RFloat {b = (RPair _ _)} ()
  inv-RFloat {b = (RDestruct _ _ _ _ _)} ()
  inv-RFloat {b = RUnit} ()
  inv-RFloat {b = (RInt _)} ()
  inv-RFloat {b = (RStringLit _)} ()
  inv-RFloat {b = (RBinOp _ _ _)} ()
  inv-RFloat {b = (RUnaryOp _ _)} ()
  inv-RFloat {b = (RAna _ _)} ()
  inv-RStringLit : ∀ {sh b t} → sub sh b ≡ (RStringLit t)
            → (b ≡ RStringLit t)
  inv-RStringLit {b = (RStringLit t)} refl = refl
  inv-RStringLit {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RStringLit {b = (RAnnot _ _)} ()
  inv-RStringLit {b = (RQualified _ _)} ()
  inv-RStringLit {b = (RResolved _)} ()
  inv-RStringLit {b = (RApp _ _)} ()
  inv-RStringLit {b = (RLam _ _)} ()
  inv-RStringLit {b = (RLet _ _ _)} ()
  inv-RStringLit {b = (RPair _ _)} ()
  inv-RStringLit {b = (RDestruct _ _ _ _ _)} ()
  inv-RStringLit {b = RUnit} ()
  inv-RStringLit {b = (RInt _)} ()
  inv-RStringLit {b = (RFloat _ _ _ _)} ()
  inv-RStringLit {b = (RBinOp _ _ _)} ()
  inv-RStringLit {b = (RUnaryOp _ _)} ()
  inv-RStringLit {b = (RAna _ _)} ()
  inv-RBinOp : ∀ {sh b o a u} → sub sh b ≡ (RBinOp o a u)
            → ∃[ a₀ ] ∃[ u₀ ] (b ≡ RBinOp o a₀ u₀ × sub (sh) a₀ ≡ a × sub (sh) u₀ ≡ u)
  inv-RBinOp {b = (RBinOp o a₀ u₀)} refl = a₀ , u₀ , refl , refl , refl
  inv-RBinOp {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RBinOp {b = (RAnnot _ _)} ()
  inv-RBinOp {b = (RQualified _ _)} ()
  inv-RBinOp {b = (RResolved _)} ()
  inv-RBinOp {b = (RApp _ _)} ()
  inv-RBinOp {b = (RLam _ _)} ()
  inv-RBinOp {b = (RLet _ _ _)} ()
  inv-RBinOp {b = (RPair _ _)} ()
  inv-RBinOp {b = (RDestruct _ _ _ _ _)} ()
  inv-RBinOp {b = RUnit} ()
  inv-RBinOp {b = (RInt _)} ()
  inv-RBinOp {b = (RFloat _ _ _ _)} ()
  inv-RBinOp {b = (RStringLit _)} ()
  inv-RBinOp {b = (RUnaryOp _ _)} ()
  inv-RBinOp {b = (RAna _ _)} ()
  inv-RUnaryOp : ∀ {sh b o a} → sub sh b ≡ (RUnaryOp o a)
            → ∃[ a₀ ] (b ≡ RUnaryOp o a₀ × sub (sh) a₀ ≡ a)
  inv-RUnaryOp {b = (RUnaryOp o a₀)} refl = a₀ , refl , refl
  inv-RUnaryOp {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RUnaryOp {b = (RAnnot _ _)} ()
  inv-RUnaryOp {b = (RQualified _ _)} ()
  inv-RUnaryOp {b = (RResolved _)} ()
  inv-RUnaryOp {b = (RApp _ _)} ()
  inv-RUnaryOp {b = (RLam _ _)} ()
  inv-RUnaryOp {b = (RLet _ _ _)} ()
  inv-RUnaryOp {b = (RPair _ _)} ()
  inv-RUnaryOp {b = (RDestruct _ _ _ _ _)} ()
  inv-RUnaryOp {b = RUnit} ()
  inv-RUnaryOp {b = (RInt _)} ()
  inv-RUnaryOp {b = (RFloat _ _ _ _)} ()
  inv-RUnaryOp {b = (RStringLit _)} ()
  inv-RUnaryOp {b = (RBinOp _ _ _)} ()
  inv-RUnaryOp {b = (RAna _ _)} ()
  inv-RAna : ∀ {sh b F a} → sub sh b ≡ (RAna F a)
            → ∃[ a₀ ] (b ≡ RAna F a₀ × sub (sh) a₀ ≡ a)
  inv-RAna {b = (RAna F a₀)} refl = a₀ , refl , refl
  inv-RAna {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes _ | false | ()
  ... | yes _ | true | ()
  inv-RAna {b = (RAnnot _ _)} ()
  inv-RAna {b = (RQualified _ _)} ()
  inv-RAna {b = (RResolved _)} ()
  inv-RAna {b = (RApp _ _)} ()
  inv-RAna {b = (RLam _ _)} ()
  inv-RAna {b = (RLet _ _ _)} ()
  inv-RAna {b = (RPair _ _)} ()
  inv-RAna {b = (RDestruct _ _ _ _ _)} ()
  inv-RAna {b = RUnit} ()
  inv-RAna {b = (RInt _)} ()
  inv-RAna {b = (RFloat _ _ _ _)} ()
  inv-RAna {b = (RStringLit _)} ()
  inv-RAna {b = (RBinOp _ _ _)} ()
  inv-RAna {b = (RUnaryOp _ _)} ()

  inv-RVar : ∀ {sh b z} → sub sh b ≡ RVar z → b ≡ RVar z × (z ≢ x ⊎ sh ≡ true)
  inv-RVar {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no y≢x | _ | refl = refl , inj₁ y≢x
  ... | yes _ | true | refl = refl , inj₂ refl
  ... | yes _ | false | ()
  inv-RVar {b = (RAnnot _ _)} ()
  inv-RVar {b = (RQualified _ _)} ()
  inv-RVar {b = (RResolved _)} ()
  inv-RVar {b = (RApp _ _)} ()
  inv-RVar {b = (RLam _ _)} ()
  inv-RVar {b = (RLet _ _ _)} ()
  inv-RVar {b = (RPair _ _)} ()
  inv-RVar {b = (RDestruct _ _ _ _ _)} ()
  inv-RVar {b = RUnit} ()
  inv-RVar {b = (RInt _)} ()
  inv-RVar {b = (RFloat _ _ _ _)} ()
  inv-RVar {b = (RStringLit _)} ()
  inv-RVar {b = (RBinOp _ _ _)} ()
  inv-RVar {b = (RUnaryOp _ _)} ()
  inv-RVar {b = (RAna _ _)} ()

  inv-RAnnot : ∀ {sh b e′ T} → sub sh b ≡ RAnnot e′ T
             → (∃[ b₀ ] (b ≡ RAnnot b₀ T × sub sh b₀ ≡ e′)) ⊎ (b ≡ RVar x × sh ≡ false × e′ ≡ e × T ≡ A)
  inv-RAnnot {b = RAnnot b₀ T} refl = inj₁ (b₀ , refl , refl)
  inv-RAnnot {sh} {b = RVar y} eq with y StrProp.≟ x | sh | eq
  ... | no _ | _ | ()
  ... | yes y≡x | false | refl = inj₂ (cong RVar y≡x , refl , refl , refl)
  ... | yes _ | true | ()
  inv-RAnnot {b = (RQualified _ _)} ()
  inv-RAnnot {b = (RResolved _)} ()
  inv-RAnnot {b = (RApp _ _)} ()
  inv-RAnnot {b = (RLam _ _)} ()
  inv-RAnnot {b = (RLet _ _ _)} ()
  inv-RAnnot {b = (RPair _ _)} ()
  inv-RAnnot {b = (RDestruct _ _ _ _ _)} ()
  inv-RAnnot {b = RUnit} ()
  inv-RAnnot {b = (RInt _)} ()
  inv-RAnnot {b = (RFloat _ _ _ _)} ()
  inv-RAnnot {b = (RStringLit _)} ()
  inv-RAnnot {b = (RBinOp _ _ _)} ()
  inv-RAnnot {b = (RUnaryOp _ _)} ()
  inv-RAnnot {b = (RAna _ _)} ()

  -- A `z` the substitution kept is not the unshadowed `x`: the definition's
  -- entry does not change what `z` finds.
  lpp-cons : ∀ {z : String} {res} → z ≢ x → lookupPolyPrefix P z ≡ res → lookupPolyPrefix P′ z ≡ res
  lpp-cons {z} z≢x lp with x StrProp.≟ z
  ... | yes x≡z = ⊥-elim (z≢x (sym x≡z))
  ... | no _ = lp

  lpp-add : ∀ {n G Δ sh} → SR {n} sh G Δ → (z : String) {res : _}
          → (z ≢ x ⊎ sh ≡ true) → lookupLocal-go z G Δ ≡ nothing
          → lookupPolyPrefix P z ≡ res → lookupPolyPrefix P′ z ≡ res
  lpp-add {G = G} {Δ = Δ} r z alt ln lp with z StrProp.≟ x
  ... | no z≢x = lpp-cons z≢x lp
  ... | yes z≡x with alt
  ...   | inj₁ z≢x = ⊥-elim (z≢x z≡x)
  ...   | inj₂ sh≡t = ⊥-elim (SR.yesX r sh≡t (subst (λ w → lookupLocal-go w G Δ ≡ nothing) z≡x ln))

  -- The unfolded occurrence `(e : A)`: `e` is checked at the use site with
  -- no local use (checking agrees with checking, `ModeAgreement`), which is
  -- exactly what a use of the definition costs.
  unfolded : ∀ {n G Δ fr} → SR {n} false G Δ → ∀ {U}
           → Lc G Δ fr ⊢ᶜ e ∶ A ⨾ U → Dc G Δ fr ⊢ᵢ RVar x ∶ A ⨾ U
  unfolded {G = G} {Δ = Δ} {fr = fr} r {U} c =
    subst (λ U → Dc G Δ fr ⊢ᵢ RVar x ∶ A ⨾ U) (agree-cc (W-c wk-base (SR.clr r) eD) c)
      (t-var-poly-instantiate-infer {g = g} (SR.noX r refl) noImp lpp-head g (sym eqA) eD)

  mutual
    F-i : ∀ {n G Δ fr sh} → SR {n} sh G Δ → ∀ {b b′ T U}
        → NC e b → Lc G Δ fr ⊢ᵢ b′ ∶ T ⨾ U → sub sh b ≡ b′ → Dc G Δ fr ⊢ᵢ b ∶ T ⨾ U
    F-c : ∀ {n G Δ fr sh} → SR {n} sh G Δ → ∀ {b b′ T U}
        → NC e b → Lc G Δ fr ⊢ᶜ b′ ∶ T ⨾ U → sub sh b ≡ b′ → Dc G Δ fr ⊢ᶜ b ∶ T ⨾ U
    F-d : ∀ {n G Δ fr sh} → SR {n} sh G Δ → ∀ {b b′ A′ π B U}
        → NC e b → Lc G Δ fr ⊢ᵈ b′ ∶ A′ ⇒[ π ]↦ B ⨾ U → sub sh b ≡ b′ → Dc G Δ fr ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ U

    F-i {sh = sh} r {b = b} nc (t-int n) eq with inv-RInt {sh = sh} {b = b} eq
    ... | refl = t-int n
    F-i {sh = sh} r {b = b} nc (t-float i f l p) eq with inv-RFloat {sh = sh} {b = b} eq
    ... | refl = t-float i f l p
    F-i {sh = sh} r {b = b} nc (t-str t) eq with inv-RStringLit {sh = sh} {b = b} eq
    ... | refl = t-str t
    F-i {sh = sh} r {b = b} nc t-unit eq with inv-RUnit {sh = sh} {b = b} eq
    ... | refl = t-unit
    F-i {sh = sh} r {b = b} nc t-unit-var eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = t-unit-var
    F-i {sh = sh} r {b = b} nc (t-var-qualified l c) eq with inv-RQualified {sh = sh} {b = b} eq
    ... | refl = t-var-qualified l c
    F-i {sh = sh} r {b = b} nc (t-var-resolved ng l c) eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = t-var-resolved ng l c
    F-i {sh = sh} r {b = b} nc (t-var-local q) eq with inv-RVar {sh = sh} {b = b} eq
    ... | refl , _ = t-var-local q
    F-i {sh = sh} r {b = b} nc (t-var-import ¬gw ln li c) eq with inv-RVar {sh = sh} {b = b} eq
    ... | refl , _ = t-var-import ¬gw ln li c
    F-i {sh = sh} r {b = b} nc (t-var-poly-instantiate-infer {x = z} ln li lp gr eT body) eq with inv-RVar {sh = sh} {b = b} eq
    ... | refl , alt = t-var-poly-instantiate-infer ln li (lpp-add r z alt ln lp) gr eT body
    F-i {sh = sh} r {b = b} nc (t-annot c) eq with inv-RAnnot {sh = sh} {b = b} eq
    ... | inj₁ (b₀ , refl , eb) = t-annot (F-c r nc c eb)
    ... | inj₂ (refl , refl , refl , refl) = unfolded r c
    F-i {sh = sh} r {b = b} nc (t-pair d₁ d₂) eq with inv-RPair {sh = sh} {b = b} eq
    ... | a₀ , u₀ , refl , e₁ , e₂ = t-pair (F-i r (proj₁ nc) d₁ e₁) (F-i r (proj₂ nc) d₂ e₂)
    F-i {sh = sh} r {b = b} nc (t-neg d) eq with inv-RUnaryOp {sh = sh} {b = b} eq
    ... | a₀ , refl , e₁ = t-neg (F-i r nc d e₁)
    F-i {sh = sh} r {b = b} nc (t-neg-float i f l p) eq with inv-RUnaryOp {sh = sh} {b = b} eq
    ... | a₀ , refl , e₁ with inv-RFloat {sh = sh} {b = a₀} e₁
    ...   | refl = t-neg-float i f l p
    F-i {sh = sh} r {b = b} nc (t-let {x = y} {A = B} d₁ d₂) eq with inv-RLet {sh = sh} {b = b} eq
    ... | a₀ , u₀ , refl , e₁ , e₂ =
          t-let (F-i r (proj₁ (proj₂ nc)) d₁ e₁) (F-i (sr-ext r y B (proj₁ nc)) (proj₂ (proj₂ nc)) d₂ e₂)
    F-i {sh = sh} r {b = b} nc (t-case {xL = xL} {xR = xR} {A = AL} {B = AR} dS dL dR) eq with inv-RDestruct {sh = sh} {b = b} eq
    ... | s₀ , l₀ , r₀ , refl , eS , eL , eR =
          t-case (F-i r (proj₁ nc) dS eS)
                 (F-i (sr-ext r xL AL (proj₁ (proj₂ nc))) (proj₁ (proj₂ (proj₂ nc))) dL eL)
                 (F-i (sr-ext r xR AR (proj₁ (proj₂ (proj₂ (proj₂ nc))))) (proj₂ (proj₂ (proj₂ (proj₂ nc)))) dR eR)
    F-i {sh = sh} r {b = b} nc (t-binop-arith o d₁ d₂) eq with inv-RBinOp {sh = sh} {b = b} eq
    ... | a₀ , u₀ , refl , e₁ , e₂ = t-binop-arith o (F-i r (proj₁ nc) d₁ e₁) (F-i r (proj₂ nc) d₂ e₂)
    F-i {sh = sh} r {b = b} nc (t-binop-arith-float o d₁ d₂) eq with inv-RBinOp {sh = sh} {b = b} eq
    ... | a₀ , u₀ , refl , e₁ , e₂ = t-binop-arith-float o (F-i r (proj₁ nc) d₁ e₁) (F-i r (proj₂ nc) d₂ e₂)
    F-i {sh = sh} r {b = b} nc (t-binop-arith-float-il o d₁ d₂) eq with inv-RBinOp {sh = sh} {b = b} eq
    ... | a₀ , u₀ , refl , e₁ , e₂ = t-binop-arith-float-il o (F-i r (proj₁ nc) d₁ e₁) (F-i r (proj₂ nc) d₂ e₂)
    F-i {sh = sh} r {b = b} nc (t-binop-arith-float-ir o d₁ d₂) eq with inv-RBinOp {sh = sh} {b = b} eq
    ... | a₀ , u₀ , refl , e₁ , e₂ = t-binop-arith-float-ir o (F-i r (proj₁ nc) d₁ e₁) (F-i r (proj₂ nc) d₂ e₂)
    F-i {sh = sh} r {b = b} nc (t-binop-cmp o d₁ d₂) eq with inv-RBinOp {sh = sh} {b = b} eq
    ... | a₀ , u₀ , refl , e₁ , e₂ = t-binop-cmp o (F-i r (proj₁ nc) d₁ e₁) (F-i r (proj₂ nc) d₂ e₂)
    F-i {sh = sh} r {b = b} nc (t-id-app d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-id-app (F-i r (proj₂ nc) d ea)
    F-i {sh = sh} r {b = b} nc (t-fst-app d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-fst-app (F-i r (proj₂ nc) d ea)
    F-i {sh = sh} r {b = b} nc (t-snd-app d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-snd-app (F-i r (proj₂ nc) d ea)
    F-i {sh = sh} r {b = b} nc (t-terminal-app d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-terminal-app (F-i r (proj₂ nc) d ea)
    F-i {sh = sh} r {b = b} nc (t-apply-app-infer d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-apply-app-infer (F-i r (proj₂ nc) d ea)
    F-i {sh = sh} r {b = b} nc (t-apply-eff-app-infer d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-apply-eff-app-infer (F-i r (proj₂ nc) d ea)
    F-i {sh = sh} r {b = b} nc (t-Out-app-infer wf eqC d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-Out-app-infer wf eqC (F-i r (proj₂ nc) d ea)
    F-i {sh = sh} r {b = b} nc (t-app ah dF dX) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , refl , refl =
          t-app ah₀ (F-i r (proj₁ nc) dF refl) (F-c r (proj₂ nc) dX eqX)
        where
          ah₀ = trans (sym (sub-head sh f₀)) ah
          eqX = cong (λ β → sub (scopeOf β sh) a₀) (sym (isAlg-other ah₀))
    F-i {sh = sh} r {b = b} nc (t-effApp ah dF dX) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , refl , refl =
          t-effApp ah₀ (F-i r (proj₁ nc) dF refl) (F-c r (proj₂ nc) dX eqX)
        where
          ah₀ = trans (sym (sub-head sh f₀)) ah
          eqX = cong (λ β → sub (scopeOf β sh) a₀) (sym (isAlg-other ah₀))
    F-i {sh = sh} r {b = b} nc (t-app-spine ah dX dF) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , refl , refl =
          t-app-spine ah₀ (F-i r (proj₂ nc) dX eqX) (F-d r (proj₁ nc) dF refl)
        where
          ah₀ = trans (sym (sub-head sh f₀)) ah
          eqX = cong (λ β → sub (scopeOf β sh) a₀) (sym (isAlg-other ah₀))
    F-c {sh = sh} r {b = b} nc t-id-check eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = t-id-check
    F-c {sh = sh} r {b = b} nc t-fst-check eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = t-fst-check
    F-c {sh = sh} r {b = b} nc t-snd-check eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = t-snd-check
    F-c {sh = sh} r {b = b} nc t-terminal-morph-check eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = t-terminal-morph-check
    F-c {sh = sh} r {b = b} nc t-initial-morph-check eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = t-initial-morph-check
    F-c {sh = sh} r {b = b} nc t-inl-morph-check eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = t-inl-morph-check
    F-c {sh = sh} r {b = b} nc t-inr-morph-check eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = t-inr-morph-check
    F-c {sh = sh} r {b = b} nc (t-compose-check-g dg df) eq with inv-RApp {sh = sh} {b = b} eq
    ... | h₀ , a₀ , refl , eh , ea with inv-RApp {sh = sh} {b = h₀} eh
    ...   | c₀ , f₁ , refl , ec , ef with inv-RResolved {sh = sh} {b = c₀} ec
    ...     | refl = t-compose-check-g (F-d r (proj₂ nc) dg ea) (F-c r (proj₂ (proj₁ nc)) df ef)
    F-c {sh = sh} r {b = b} nc (t-compose-check-f wf p dg) eq with inv-RApp {sh = sh} {b = b} eq
    ... | h₀ , a₀ , refl , eh , ea with inv-RApp {sh = sh} {b = h₀} eh
    ...   | c₀ , f₁ , refl , ec , ef with inv-RResolved {sh = sh} {b = c₀} ec
    ...     | refl = t-compose-check-f (F-i r (proj₂ (proj₁ nc)) wf ef) p (F-c r (proj₂ nc) dg ea)
    F-c {sh = sh} r {b = b} nc (t-case-copair-check df dg) eq with inv-RApp {sh = sh} {b = b} eq
    ... | h₀ , a₀ , refl , eh , ea with inv-RApp {sh = sh} {b = h₀} eh
    ...   | c₀ , f₁ , refl , ec , ef with inv-RResolved {sh = sh} {b = c₀} ec
    ...     | refl = t-case-copair-check (F-c r (proj₂ (proj₁ nc)) df ef) (F-c r (proj₂ nc) dg ea)
    F-c {sh = sh} r {b = b} nc (t-pair-morph-check df dg) eq with inv-RApp {sh = sh} {b = b} eq
    ... | h₀ , a₀ , refl , eh , ea with inv-RApp {sh = sh} {b = h₀} eh
    ...   | c₀ , f₁ , refl , ec , ef with inv-RResolved {sh = sh} {b = c₀} ec
    ...     | refl = t-pair-morph-check (F-c r (proj₂ (proj₁ nc)) df ef) (F-c r (proj₂ nc) dg ea)
    F-c {sh = sh} r {b = b} nc (t-curry-check d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-curry-check (F-c r (proj₂ nc) d ea)
    F-c {sh = sh} r {b = b} nc (t-cata-check wf dalg) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-cata-check wf (F-c sr-alg (proj₂ nc) dalg ea)
    F-c {sh = sh} r {b = b} nc (t-ana-check wf dco) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-ana-check wf (F-c sr-alg (proj₂ nc) dco ea)
    F-c {sh = sh} r {b = b} nc (t-sub d p) eq = t-sub (F-i r nc d eq) p
    F-c {sh = sh} r {b = b} nc (t-lam {x = y} {A = B} leq body) eq with inv-RLam {sh = sh} {b = b} eq
    ... | u₀ , refl , eu = t-lam leq (F-c (sr-ext r y B (proj₁ nc)) (proj₂ nc) body eu)
    F-c {sh = sh} r {b = b} nc (t-pair-lit-check d₁ d₂) eq with inv-RPair {sh = sh} {b = b} eq
    ... | a₀ , u₀ , refl , e₁ , e₂ = t-pair-lit-check (F-c r (proj₁ nc) d₁ e₁) (F-c r (proj₂ nc) d₂ e₂)
    F-c {sh = sh} r {b = b} nc (t-In-app-check wf d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-In-app-check wf (F-c r (proj₂ nc) d ea)
    F-c {sh = sh} r {b = b} nc (t-apply-check d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-apply-check (F-i r (proj₂ nc) d ea)
    F-c {sh = sh} r {b = b} nc (t-inl-app-check d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-inl-app-check (F-c r (proj₂ nc) d ea)
    F-c {sh = sh} r {b = b} nc (t-inr-app-check d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-inr-app-check (F-c r (proj₂ nc) d ea)
    F-c {sh = sh} r {b = b} nc (t-initial-app-check d) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = t-initial-app-check (F-c r (proj₂ nc) d ea)
    F-c {sh = sh} r {b = b} nc (t-var-poly-instantiate {x = z} ln li lp ¬g body) eq with inv-RVar {sh = sh} {b = b} eq
    ... | refl , alt = t-var-poly-instantiate ln li (lpp-add r z alt ln lp) ¬g body
    F-d {sh = sh} r {b = b} nc (d-infer w sb gr) eq = d-infer (F-i r nc w eq) sb gr
    F-d {sh = sh} r {b = b} nc (d-lam {x = y} {A = B} leq body) eq with inv-RLam {sh = sh} {b = b} eq
    ... | u₀ , refl , eu = d-lam leq (F-i (sr-ext r y B (proj₁ nc)) (proj₂ nc) body eu)
    F-d {sh = sh} r {b = b} nc (d-compose dg df) eq with inv-RApp {sh = sh} {b = b} eq
    ... | h₀ , a₀ , refl , eh , ea with inv-RApp {sh = sh} {b = h₀} eh
    ...   | c₀ , f₁ , refl , ec , ef with inv-RResolved {sh = sh} {b = c₀} ec
    ...     | refl = d-compose (F-d r (proj₂ nc) dg ea) (F-d r (proj₂ (proj₁ nc)) df ef)
    F-d {sh = sh} r {b = b} nc d-id eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = d-id
    F-d {sh = sh} r {b = b} nc d-fst eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = d-fst
    F-d {sh = sh} r {b = b} nc d-snd eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = d-snd
    F-d {sh = sh} r {b = b} nc d-terminal eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = d-terminal
    F-d {sh = sh} r {b = b} nc d-initial eq with inv-RResolved {sh = sh} {b = b} eq
    ... | refl = d-initial
    F-d {sh = sh} r {b = b} nc (d-case df dg) eq with inv-RApp {sh = sh} {b = b} eq
    ... | h₀ , a₀ , refl , eh , ea with inv-RApp {sh = sh} {b = h₀} eh
    ...   | c₀ , f₁ , refl , ec , ef with inv-RResolved {sh = sh} {b = c₀} ec
    ...     | refl = d-case (F-d r (proj₂ (proj₁ nc)) df ef) (F-d r (proj₂ nc) dg ea)
    F-d {sh = sh} r {b = b} nc (d-pair df dg) eq with inv-RApp {sh = sh} {b = b} eq
    ... | h₀ , a₀ , refl , eh , ea with inv-RApp {sh = sh} {b = h₀} eh
    ...   | c₀ , f₁ , refl , ec , ef with inv-RResolved {sh = sh} {b = c₀} ec
    ...     | refl = d-pair (F-d r (proj₂ (proj₁ nc)) df ef) (F-d r (proj₂ nc) dg ea)
    F-d {sh = sh} r {b = b} nc (d-cata wf dalg) eq with inv-RApp {sh = sh} {b = b} eq
    ... | f₀ , a₀ , refl , ef , ea with inv-RResolved {sh = sh} {b = f₀} ef
    ...   | refl = d-cata wf (F-i sr-alg (proj₂ nc) dalg ea)

------------------------------------------------------------------------
-- The theorem, in all three judgments.
------------------------------------------------------------------------

module _ {Γ : NamedCtx} {x : String} {A : Type} {e : RawExpr} {s : PolyType} {g : Ground s}
  (eqA : extractGround s g ≡ A)
  (noLocal : lookupLocal Γ x ≡ nothing)
  (clear : Fr (λ z → lookupLocal Γ z ≡ nothing) e)
  (noImp : lookupImport (NamedCtx.imports Γ) x ≡ nothing)
  (eD : ctxWithImportsAndPolys (NamedCtx.imports Γ) (NamedCtx.polys Γ) ⊢ᶜ e ∶ A ⨾ zeroUsage)
  where
  private
    module U = Unfolding x A e s g eqA (NamedCtx.imports Γ) (NamedCtx.polys Γ) noImp eD
    r₀ : U.SR false (NamedCtx.named Γ) (NamedCtx.debruijn Γ)
    r₀ = record { noX = λ _ → noLocal ; yesX = λ () ; clr = clear }

  open Sub x (RAnnot e A) using (sub)

  unfoldᵢ : ∀ {b B Ψ} → NC e b → defineNamedCtx Γ x s e ⊢ᵢ b ∶ B ⨾ Ψ → Γ ⊢ᵢ sub false b ∶ B ⨾ Ψ
  unfoldᵢ = U.S-i r₀

  unfoldᶜ : ∀ {b B Ψ} → NC e b → defineNamedCtx Γ x s e ⊢ᶜ b ∶ B ⨾ Ψ → Γ ⊢ᶜ sub false b ∶ B ⨾ Ψ
  unfoldᶜ = U.S-c r₀

  unfoldᵈ : ∀ {b A′ π B Ψ} → NC e b → defineNamedCtx Γ x s e ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ Ψ
          → Γ ⊢ᵈ sub false b ∶ A′ ⇒[ π ]↦ B ⨾ Ψ
  unfoldᵈ = U.S-d r₀

  -- Folding: the unfolded term types only if the name did. Together with
  -- `unfold`, a definition and its definiens are interchangeable (§0).
  foldᵢ : ∀ {b B Ψ} → NC e b → Γ ⊢ᵢ sub false b ∶ B ⨾ Ψ → defineNamedCtx Γ x s e ⊢ᵢ b ∶ B ⨾ Ψ
  foldᵢ nc d = U.F-i r₀ nc d refl

  foldᶜ : ∀ {b B Ψ} → NC e b → Γ ⊢ᶜ sub false b ∶ B ⨾ Ψ → defineNamedCtx Γ x s e ⊢ᶜ b ∶ B ⨾ Ψ
  foldᶜ nc d = U.F-c r₀ nc d refl

  foldᵈ : ∀ {b A′ π B Ψ} → NC e b → Γ ⊢ᵈ sub false b ∶ A′ ⇒[ π ]↦ B ⨾ Ψ
        → defineNamedCtx Γ x s e ⊢ᵈ b ∶ A′ ⇒[ π ]↦ B ⨾ Ψ
  foldᵈ nc d = U.F-d r₀ nc d refl
