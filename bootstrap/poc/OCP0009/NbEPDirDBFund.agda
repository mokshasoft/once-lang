------------------------------------------------------------------------
-- OCP-0009 · W1h — `fund`: THE FUNDAMENTAL THEOREM.
--
-- Every well-typed term is a member of the semantic type its type denotes, at
-- every reducible substitution.  With `NbEPDirDBLR` supplying the logical
-- relation and one semantic lemma per typing rule, this module is the
-- assembly: the substitution calculus `fund` needs, the two shape inversions,
-- the mutual `fund-ty`/`fund` induction, and the corollary the kernel actually
-- wanted — WEAK NORMALIZATION for `_⊢_∷_`, hence `dec-conv` with no premise.
--
-- ★ THE STATEMENT IS EXISTENTIAL, on purpose (handoff 2026-07-30 §4.0):
--
--     fund : Γ ⊢ t ∷ A → Var Δ → Γ ⊩ˢ σ → Σ (⊩₁ (subTy σ A)) (_⊩₁∋ subTm σ t)
--
-- It does NOT take a `Γ ⊢ty A`.  Syntactic validity is unprovable here — `⊢ty`
-- is not closed under conversion, because `ty-Π` does not record that its
-- components were `El`s — and demanding it would force a `Γ ⊢ty B` premise on
-- `⊢conv`, cascading into all of `sr`'s `⊢conv` reconstructions.  Existentially,
-- `⊢conv` is discharged by `conv₁` + `sem-conv`: the relation is ALREADY closed
-- under conversion, which is what W1b bought.  Nothing else is needed.
--
-- ⚠ ONE OBLIGATION THE SPIKES DEFERRED, and where it landed.  `sem-lam` takes
-- `SN s` for the lambda's BODY — a term under a binder — and `sem-⌜Π⌝`/`sem-⌜Σ⌝`
-- take `SN d` for the code's second component, likewise.  The induction hands
-- back only CLOSED-UP instances `s[σ,u]`, so those premises need SN to come
-- back OUT of a substitution.  The classical fix is a Kripke-indexed relation,
-- which W1c refuted for this development (`SpikeSNX`; and `⊩₁` genuinely does
-- not admit a renaming action — its `Π` family quantifies over ALL terms of the
-- target scope, and a renaming cannot be undone on them).  The fix used here is
-- cheaper and local:
--
--   * instantiate the family at a VARIABLE `var x₀` of the target scope — free,
--     by `CR3`, since every neutral is a member;
--   * `s[single (var x₀)]` IS a renaming of `s`;
--   * so ANTI-RENAMING for `SN` (§2) recovers `SN s`.
--
-- That is why `fund` carries a `Var Δ`: the target scope must be non-empty.
-- It always can be — `⊩ˢ-ren` (§7) makes EVERY renaming substitution reducible,
-- so `wnorm` runs the induction at `vs : Ren ⌊ Γ ⌋ (⌊ Γ ⌋ ∙)` and undoes that
-- one weakening with the same anti-renaming lemma.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBFund where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_ )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom; Hom-cong₃; ⌜Hom⌝-cong₃; tr-cong₃
        ; RTm; var; lam; app; pair; fst; snd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr
        ; Ren; extR; renTy; renTm
        ; Sub; subTy; subTm; extS
        ; _∘ᵣ_
        ; subTy-cong; subTm-cong
        ; subTy-renTy; subTm-renTm
        ; renTy-subTy; renTm-subTm
        ; subTy-subTy; subTm-subTm
        ; subTy-id; subTm-id )
open import poc.OCP0009.NbEPDirDBType
  using ( single
        ; _⟶_; _⟶*_; done; step
        ; _≅_
        ; _≅ᵀ_; crflᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋
        ; _∋_∷_; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd
        ; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢conv
        ; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom
        ; ⊢ctx_; c-◇; c-▹
        ; ⊢id; ⊢appex )
open import poc.OCP0009.NbEPDirDBSR using ( ≅ᵀ-sub )
open import poc.OCP0009.NbEPDirDBDec using ( Dec; dec-conv )
open import poc.OCP0009.NbEPDirDBInj using ( _⟶ᵀ*_; doneᵀ; red→≅ᵀ; Π-reduct; Σ-reduct; mkΠRed; mkΣRed )
open import poc.OCP0009.NbEPDirDBLR
  using ( SNe; sne-var; sne-app; sne-fst; sne-snd; sne-hrefl
        ; sne-tr-stk; sne-tr-lam
        ; SN; sn-ne; sn-lam; sn-pair; sn-cb; sn-cΠ; sn-cΣ; sn-cH; sn-exp
        ; SNRed; snr-β; snr-βfst; snr-βsnd; snr-app; snr-fst; snr-snd
        ; snr-hreflᶜ; snr-J-base; snr-J-Σ; snr-taut; snr-trᵖ
        ; NeV; nv-var; nv-app; nv-fst; nv-snd
        ; StableCd; sc-lam; sc-pair; sc-cΠ; sc-cH; sc-hrefl; sc-nev
        ; PathStk; ps-nev; ps-h
        ; ⊩₀_; ⊩₀base; ⊩₀ne; ⊩₀Π; ⊩₀Σ; _⊩₀∋_
        ; ⊩₁_; ⊩₁base; ⊩₁U; ⊩₁ne; ⊩₁Π; ⊩₁Σ; ⊩₁Hom; _⊩₁∋_
        ; bwd₁; irrel₁; conv₁; CR1₀; CR1₁; CR3₀; CR3₁
        ; emb; emb-coh
        ; sem-conv; sem-lam; sem-app; sem-fst; sem-snd; sem-pair
        ; sem-El; sem-⌜base⌝; sem-⌜Π⌝; sem-⌜Σ⌝; sem-⌜Hom⌝; sem-hrefl
        ; homSem₁
        ; ⟶ᵀ*-sub
        ; IsNormal; WN; mkWN; wn
        ; projl; projr; dfst; dsnd )

private
  variable
    Θ Ξ : Cx
    Γ Δ : Ctx

------------------------------------------------------------------------
-- 1. THE SUBSTITUTION CALCULUS `fund` NEEDS.
--
-- Four equations, all instances of the mutual laws already proven in
-- `NbEPDirDBPi`.  Nothing here is about the logical relation.
------------------------------------------------------------------------

-- `σ , u` — the extension used by `⊢lam`/`⊢pair`/`ty-Π`.  Its target scope is
-- the SAME as `σ`'s: this is why no weakening happens in the λ-case (handoff
-- §5c), and why `Δ` is fixed for the whole induction.
infixl 5 _,ₛ_
_,ₛ_ : Sub Θ Ξ → RTm Ξ → Sub (Θ ∙) Ξ
(σ ,ₛ u) vz     = u
(σ ,ₛ u) (vs x) = σ x

-- a renaming, viewed as a substitution
⟨_⟩ᵣ : Ren Θ Ξ → Sub Θ Ξ
⟨ ρ ⟩ᵣ x = var (ρ x)

exts-var : (ρ : Ren Θ Ξ) (x : Var (Θ ∙)) → extS ⟨ ρ ⟩ᵣ x ≡ ⟨ extR ρ ⟩ᵣ x
exts-var ρ vz     = refl
exts-var ρ (vs x) = refl

-- (1a) substituting a renaming IS renaming.
subTy-var : (ρ : Ren Θ Ξ) (A : RTy Θ) → subTy ⟨ ρ ⟩ᵣ A ≡ renTy ρ A
subTm-var : (ρ : Ren Θ Ξ) (t : RTm Θ) → subTm ⟨ ρ ⟩ᵣ t ≡ renTm ρ t
subTy-var ρ base     = refl
subTy-var ρ U        = refl
subTy-var ρ (Π A B)  =
  cong₂ Π (subTy-var ρ A)
          (trans (subTy-cong (exts-var ρ) B) (subTy-var (extR ρ) B))
subTy-var ρ (Σ' A B) =
  cong₂ Σ' (subTy-var ρ A)
           (trans (subTy-cong (exts-var ρ) B) (subTy-var (extR ρ) B))
subTy-var ρ (El t)   = cong El (subTm-var ρ t)
subTy-var ρ (Hom A t u) =
  Hom-cong₃ (subTy-var ρ A) (subTm-var ρ t) (subTm-var ρ u)
subTm-var ρ (var x)   = refl
subTm-var ρ (lam t)   =
  cong lam (trans (subTm-cong (exts-var ρ) t) (subTm-var (extR ρ) t))
subTm-var ρ (app t u)  = cong₂ app (subTm-var ρ t) (subTm-var ρ u)
subTm-var ρ (pair a b) = cong₂ pair (subTm-var ρ a) (subTm-var ρ b)
subTm-var ρ (fst p)    = cong fst (subTm-var ρ p)
subTm-var ρ (snd p)    = cong snd (subTm-var ρ p)
subTm-var ρ ⌜base⌝     = refl
subTm-var ρ (⌜Π⌝ c d)  =
  cong₂ ⌜Π⌝ (subTm-var ρ c)
            (trans (subTm-cong (exts-var ρ) d) (subTm-var (extR ρ) d))
subTm-var ρ (⌜Σ⌝ c d)  =
  cong₂ ⌜Σ⌝ (subTm-var ρ c)
            (trans (subTm-cong (exts-var ρ) d) (subTm-var (extR ρ) d))
subTm-var ρ (⌜Hom⌝ c a b) =
  ⌜Hom⌝-cong₃ (subTm-var ρ c) (subTm-var ρ a) (subTm-var ρ b)
subTm-var ρ (hrefl c t) = cong₂ hrefl (subTm-var ρ c) (subTm-var ρ t)
subTm-var ρ (tr d p e)  =
  tr-cong₃ (trans (subTm-cong (exts-var ρ) d) (subTm-var (extR ρ) d))
           (subTm-var ρ p) (subTm-var ρ e)

-- (1b) single substitution commutes with renaming — what `snr-β` needs when
-- reflected through a renaming (§2).
ren-single : (ρ : Ren Θ Ξ) (u : RTm Θ) (t : RTm (Θ ∙)) →
             subTm (single (renTm ρ u)) (renTm (extR ρ) t)
           ≡ renTm ρ (subTm (single u) t)
ren-single {Θ = Θ} ρ u t =
  trans (subTm-renTm t) (trans (subTm-cong pw t) (sym (renTm-subTm t)))
  where
    pw : (x : Var (Θ ∙)) →
         single (renTm ρ u) (extR ρ x) ≡ renTm ρ (single u x)
    pw vz     = refl
    pw (vs x) = refl

-- (1c) the extension absorbs the weakening it was built to cancel.
sub-ext-wk : (σ : Sub Θ Ξ) (u : RTm Ξ) (A : RTy Θ) →
             subTy (σ ,ₛ u) (renTy vs A) ≡ subTy σ A
sub-ext-wk σ u A = trans (subTy-renTy A) (subTy-cong (λ _ → refl) A)

-- (1d) instantiating the codomain = extending the substitution.
sub-single-Ty : (σ : Sub Θ Ξ) (u : RTm Ξ) (B : RTy (Θ ∙)) →
                subTy (single u) (subTy (extS σ) B) ≡ subTy (σ ,ₛ u) B
sub-single-Tm : (σ : Sub Θ Ξ) (u : RTm Ξ) (t : RTm (Θ ∙)) →
                subTm (single u) (subTm (extS σ) t) ≡ subTm (σ ,ₛ u) t

single-exts : (σ : Sub Θ Ξ) (u : RTm Ξ) (x : Var (Θ ∙)) →
              subTm (single u) (extS σ x) ≡ (σ ,ₛ u) x
single-exts σ u vz     = refl
single-exts σ u (vs x) =
  trans (subTm-renTm (σ x))
        (trans (subTm-cong (λ _ → refl) (σ x)) (subTm-id (σ x)))

sub-single-Ty σ u B = trans (subTy-subTy B) (subTy-cong (single-exts σ u) B)
sub-single-Tm σ u t = trans (subTm-subTm t) (subTm-cong (single-exts σ u) t)

-- (1e) pushing a substitution through a single one — `⊢app`/`⊢snd`'s codomain.
sub-comm-Ty : (σ : Sub Θ Ξ) (a : RTm Θ) (B : RTy (Θ ∙)) →
              subTy σ (subTy (single a) B)
            ≡ subTy (single (subTm σ a)) (subTy (extS σ) B)
comm-single : (σ : Sub Θ Ξ) (a : RTm Θ) (x : Var (Θ ∙)) →
              subTm σ (single a x) ≡ (σ ,ₛ subTm σ a) x
comm-single σ a vz     = refl
comm-single σ a (vs x) = refl

sub-comm-Ty σ a B =
  trans (trans (subTy-subTy B) (subTy-cong (comm-single σ a) B))
        (sym (sub-single-Ty σ (subTm σ a) B))

------------------------------------------------------------------------
-- 2. ★ ANTI-RENAMING FOR `SN` — the obligation the spikes deferred.
--
-- `SN (renTm ρ t) → SN t`.  Renaming creates no redexes, so the whole thing is
-- a structural case split on `t` followed by inversion of the derivation; the
-- only content is `snr-anti`, which must reflect a HEAD REDUCTION through the
-- renaming, and whose `snr-β` case is exactly `ren-single`.
--
-- This is what makes the `SN`-under-a-binder premises of `sem-lam`/`sem-⌜Π⌝`
-- reachable without a Kripke-indexed relation.
------------------------------------------------------------------------

-- the shape judgments reflect through renamings, like everything raw
nev-anti : {ρ : Ren Θ Ξ} {t : RTm Θ} → NeV (renTm ρ t) → NeV t
nev-anti {t = var x}   _          = nv-var x
nev-anti {t = app t u} (nv-app n) = nv-app (nev-anti n)
nev-anti {t = fst p}   (nv-fst n) = nv-fst (nev-anti n)
nev-anti {t = snd p}   (nv-snd n) = nv-snd (nev-anti n)

stablecd-anti : {ρ : Ren Θ Ξ} {t : RTm Θ} → StableCd (renTm ρ t) → StableCd t
stablecd-anti {t = lam s}       sc-lam     = sc-lam
stablecd-anti {t = pair a b}    sc-pair    = sc-pair
stablecd-anti {t = ⌜Π⌝ c d}     sc-cΠ      = sc-cΠ
stablecd-anti {t = ⌜Hom⌝ c a b} sc-cH      = sc-cH
stablecd-anti {t = hrefl c s}   sc-hrefl   = sc-hrefl
stablecd-anti {t = var x}       (sc-nev n) = sc-nev (nv-var x)
stablecd-anti {t = app t u}     (sc-nev n) = sc-nev (nev-anti n)
stablecd-anti {t = fst p}       (sc-nev n) = sc-nev (nev-anti n)
stablecd-anti {t = snd p}       (sc-nev n) = sc-nev (nev-anti n)
stablecd-anti {t = ⌜base⌝}      (sc-nev ())
stablecd-anti {t = ⌜Σ⌝ c d}     (sc-nev ())
stablecd-anti {t = tr d p e}    (sc-nev ())

pathstk-anti : {ρ : Ren Θ Ξ} {t : RTm Θ} → PathStk (renTm ρ t) → PathStk t
pathstk-anti {t = hrefl c s} (ps-h sc)  = ps-h (stablecd-anti sc)
pathstk-anti {t = hrefl c s} (ps-nev ())
pathstk-anti {t = var x}     (ps-nev n) = ps-nev (nv-var x)
pathstk-anti {t = app t u}   (ps-nev n) = ps-nev (nev-anti n)
pathstk-anti {t = fst p}     (ps-nev n) = ps-nev (nev-anti n)
pathstk-anti {t = snd p}     (ps-nev n) = ps-nev (nev-anti n)
pathstk-anti {t = lam s}        (ps-nev ())
pathstk-anti {t = pair a b}     (ps-nev ())
pathstk-anti {t = ⌜base⌝}       (ps-nev ())
pathstk-anti {t = ⌜Π⌝ c d}      (ps-nev ())
pathstk-anti {t = ⌜Σ⌝ c d}      (ps-nev ())
pathstk-anti {t = ⌜Hom⌝ c a b}  (ps-nev ())
pathstk-anti {t = tr d p e}     (ps-nev ())

sne-anti : {ρ : Ren Θ Ξ} {t : RTm Θ} → SNe (renTm ρ t) → SNe t
sn-anti  : {ρ : Ren Θ Ξ} {t : RTm Θ} → SN  (renTm ρ t) → SN t
snr-anti : {ρ : Ren Θ Ξ} {t : RTm Θ} {v : RTm Ξ} → SNRed (renTm ρ t) v →
           Σ (RTm Θ) (λ t' → SNRed t t' × (v ≡ renTm ρ t'))

sne-anti {t = var x}    _             = sne-var x
sne-anti {t = app t u}  (sne-app n s) = sne-app (sne-anti n) (sn-anti s)
sne-anti {t = fst p}    (sne-fst n)   = sne-fst (sne-anti n)
sne-anti {t = snd p}    (sne-snd n)   = sne-snd (sne-anti n)
sne-anti {t = hrefl c t} (sne-hrefl hc ht) =
  sne-hrefl (sn-anti hc) (sn-anti ht)
sne-anti {ρ = ρ} {t = tr d (var x) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = var x} hp)
             (pathstk-anti {ρ = ρ} {t = var x} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (app g w) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = app g w} hp)
             (pathstk-anti {ρ = ρ} {t = app g w} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (pair g w) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = pair g w} hp)
             (pathstk-anti {ρ = ρ} {t = pair g w} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (fst g) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = fst g} hp)
             (pathstk-anti {ρ = ρ} {t = fst g} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (snd g) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = snd g} hp)
             (pathstk-anti {ρ = ρ} {t = snd g} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (⌜base⌝) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = ⌜base⌝} hp)
             (pathstk-anti {ρ = ρ} {t = ⌜base⌝} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (⌜Π⌝ g w) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = ⌜Π⌝ g w} hp)
             (pathstk-anti {ρ = ρ} {t = ⌜Π⌝ g w} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (⌜Σ⌝ g w) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = ⌜Σ⌝ g w} hp)
             (pathstk-anti {ρ = ρ} {t = ⌜Σ⌝ g w} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (⌜Hom⌝ g w v) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = ⌜Hom⌝ g w v} hp)
             (pathstk-anti {ρ = ρ} {t = ⌜Hom⌝ g w v} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (hrefl g w) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = hrefl g w} hp)
             (pathstk-anti {ρ = ρ} {t = hrefl g w} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr d (tr g w v) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti hd) (sn-anti {ρ = ρ} {t = tr g w v} hp)
             (pathstk-anti {ρ = ρ} {t = tr g w v} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (var x) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = var x} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (lam g) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = lam g} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (app g w) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = app g w} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (pair g w) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = pair g w} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (fst g) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = fst g} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (snd g) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = snd g} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (⌜base⌝) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = ⌜base⌝} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (⌜Π⌝ g w) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = ⌜Π⌝ g w} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (⌜Σ⌝ g w) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = ⌜Σ⌝ g w} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (hrefl g w) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = hrefl g w} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {ρ = ρ} {t = tr (tr g w v) (lam f) e} (sne-tr-stk hd hp ps he) =
  sne-tr-stk (sn-anti {ρ = extR ρ} {t = tr g w v} hd) (sn-anti {ρ = ρ} {t = lam f} hp)
             (pathstk-anti {ρ = ρ} {t = lam f} ps) (sn-anti he)
sne-anti {t = tr (⌜Hom⌝ d₁ d₂ d₃) (lam f) e} (sne-tr-stk hd hp (ps-nev ()) he)
sne-anti {t = tr (⌜Hom⌝ d₁ d₂ d₃) (lam f) e} (sne-tr-lam h₁ h₂ h₃ h₄ h₅) =
  sne-tr-lam (sn-anti h₁) (sn-anti h₂) (sn-anti h₃) (sn-anti h₄) (sn-anti h₅)

sn-anti {t = var x}    _              = sn-ne (sne-var x)
sn-anti {t = lam s}    (sn-lam h)     = sn-lam (sn-anti h)
sn-anti {t = pair a b} (sn-pair ha hb) = sn-pair (sn-anti ha) (sn-anti hb)
sn-anti {t = ⌜base⌝}   _              = sn-cb
sn-anti {t = ⌜Π⌝ c d}  (sn-cΠ hc hd)  = sn-cΠ (sn-anti hc) (sn-anti hd)
sn-anti {t = ⌜Σ⌝ c d}  (sn-cΣ hc hd)  = sn-cΣ (sn-anti hc) (sn-anti hd)
sn-anti {t = ⌜Hom⌝ c a b} (sn-cH hc ha hb) =
  sn-cH (sn-anti hc) (sn-anti ha) (sn-anti hb)
sn-anti {t = hrefl c t} (sn-ne n)     = sn-ne (sne-anti n)
sn-anti {t = hrefl c t} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = tr d p e}  (sn-ne n)     = sn-ne (sne-anti n)
sn-anti {t = tr d p e}  (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = app t u}  (sn-ne n)      = sn-ne (sne-anti n)
sn-anti {t = fst p}    (sn-ne n)      = sn-ne (sne-anti n)
sn-anti {t = snd p}    (sn-ne n)      = sn-ne (sne-anti n)
sn-anti {t = app t u}  (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = fst p}    (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = snd p}    (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)

snr-anti {ρ = ρ} {t = app (lam s) u} (snr-β h) =
  subTm (single u) s , (snr-β (sn-anti h) , ren-single ρ u s)
snr-anti {t = app (app a b) u}  (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (fst p) u}    (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (snd p) u}    (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = fst (pair a b)}   (snr-βfst h) =
  a , (snr-βfst (sn-anti h) , refl)
snr-anti {t = fst (app a b)}    (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = fst (fst p)}      (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = fst (snd p)}      (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = snd (pair a b)}   (snr-βsnd h) =
  b , (snr-βsnd (sn-anti h) , refl)
snr-anti {t = snd (app a b)}    (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (fst p)}      (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (snd p)}      (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = hrefl c s} (snr-hreflᶜ r) with snr-anti r
... | c' , (r' , refl) = hrefl c' s , (snr-hreflᶜ r' , refl)
snr-anti {t = tr d (hrefl ⌜base⌝ s) e} (snr-J-base hd hs) =
  e , (snr-J-base (sn-anti hd) (sn-anti hs) , refl)
snr-anti {t = tr d (hrefl ⌜base⌝ s) e} (snr-trᵖ (snr-hreflᶜ ()))
snr-anti {t = tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e} (snr-J-Σ hd h₁ h₂ hs) =
  e , (snr-J-Σ (sn-anti hd) (sn-anti h₁) (sn-anti h₂) (sn-anti hs) , refl)
snr-anti {t = tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e} (snr-trᵖ (snr-hreflᶜ ()))
snr-anti {t = tr (var vz) (lam f) e} snr-taut =
  app (lam f) e , (snr-taut , refl)
snr-anti {t = tr d (hrefl (var x) s) e} (snr-trᵖ (snr-hreflᶜ ()))
snr-anti {t = tr d (hrefl (lam g) s) e} (snr-trᵖ (snr-hreflᶜ ()))
snr-anti {t = tr d (hrefl (app g w) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (pair g w) s) e} (snr-trᵖ (snr-hreflᶜ ()))
snr-anti {t = tr d (hrefl (fst g) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (snd g) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (⌜Π⌝ g w) s) e} (snr-trᵖ (snr-hreflᶜ ()))
snr-anti {t = tr d (hrefl (⌜Hom⌝ g w v) s) e} (snr-trᵖ (snr-hreflᶜ ()))
snr-anti {t = tr d (hrefl (hrefl g w) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (tr g w v) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (var x) e} (snr-trᵖ ())
snr-anti {t = tr d (lam g) e} (snr-trᵖ ())
snr-anti {t = tr d (app g w) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (pair g w) e} (snr-trᵖ ())
snr-anti {t = tr d (fst g) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (snd g) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d ⌜base⌝ e} (snr-trᵖ ())
snr-anti {t = tr d (⌜Π⌝ g w) e} (snr-trᵖ ())
snr-anti {t = tr d (⌜Σ⌝ g w) e} (snr-trᵖ ())
snr-anti {t = tr d (⌜Hom⌝ g w v) e} (snr-trᵖ ())
snr-anti {t = tr d (tr g w v) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
-- the heads that reduce to nothing: a renaming cannot turn them into redexes.
snr-anti {t = app (var x) u}    (snr-app ())
snr-anti {t = app (pair a b) u} (snr-app ())
snr-anti {t = app ⌜base⌝ u}     (snr-app ())
snr-anti {t = app (⌜Π⌝ c d) u}  (snr-app ())
snr-anti {t = app (⌜Σ⌝ c d) u}  (snr-app ())
snr-anti {t = fst (var x)}      (snr-fst ())
snr-anti {t = fst (lam s)}      (snr-fst ())
snr-anti {t = fst ⌜base⌝}       (snr-fst ())
snr-anti {t = fst (⌜Π⌝ c d)}    (snr-fst ())
snr-anti {t = fst (⌜Σ⌝ c d)}    (snr-fst ())
snr-anti {t = app (⌜Hom⌝ c a b) u} (snr-app ())
snr-anti {t = app (hrefl c s) u}   (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (tr d p e) u}    (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = fst (⌜Hom⌝ c a b)}   (snr-fst ())
snr-anti {t = fst (hrefl c s)}     (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = fst (tr d p e)}      (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = snd (⌜Hom⌝ c a b)}   (snr-snd ())
snr-anti {t = snd (hrefl c s)}     (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (tr d p e)}      (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (var x)}      (snr-snd ())
snr-anti {t = snd (lam s)}      (snr-snd ())
snr-anti {t = snd ⌜base⌝}       (snr-snd ())
snr-anti {t = snd (⌜Π⌝ c d)}    (snr-snd ())
snr-anti {t = snd (⌜Σ⌝ c d)}    (snr-snd ())

-- ★ the corollary actually used: instantiating a body at a VARIABLE is a
-- renaming, so `SN` comes back out of it.
sn-body : (x₀ : Var Ξ) {s : RTm (Ξ ∙)} → SN (subTm (single (var x₀)) s) → SN s
sn-body {Ξ = Ξ} x₀ {s} h = sn-anti (subst SN eq h)
  where
    ρ₀ : Ren (Ξ ∙) Ξ
    ρ₀ vz     = x₀
    ρ₀ (vs y) = y

    pw : (x : Var (Ξ ∙)) → single (var x₀) x ≡ ⟨ ρ₀ ⟩ᵣ x
    pw vz     = refl
    pw (vs y) = refl

    eq : subTm (single (var x₀)) s ≡ renTm ρ₀ s
    eq = trans (subTm-cong pw s) (subTm-var ρ₀ s)

------------------------------------------------------------------------
-- 3. THE EXISTENTIAL PAYLOAD, and its two casts.
--
-- `fund` returns a PAIR — some semantic type at `A`, and a membership at `t`.
-- Casting is by `≡` on both indices AT ONCE: doing it in two steps would leave
-- the membership pointing at a different (though equal) first component.
------------------------------------------------------------------------

Rel : {Θ : Cx} → RTy Θ → RTm Θ → Set
Rel A t = Σ (⊩₁ A) (λ R → R ⊩₁∋ t)

relCast : {A A' : RTy Θ} {t t' : RTm Θ} → A ≡ A' → t ≡ t' → Rel A t → Rel A' t'
relCast refl refl h = h

relTy : {A A' : RTy Θ} {t : RTm Θ} → A ≡ A' → Rel A t → Rel A' t
relTy p h = relCast p refl h

⊩₁cast : {A A' : RTy Θ} → A ≡ A' → ⊩₁ A → ⊩₁ A'
⊩₁cast refl R = R

⊩₀cast : {A A' : RTy Θ} → A ≡ A' → ⊩₀ A → ⊩₀ A'
⊩₀cast refl R = R

------------------------------------------------------------------------
-- 4. REDUCIBLE SUBSTITUTIONS.
--
-- `Γ ⊩ˢ σ` — every variable of `Γ` is sent to a member of its (substituted)
-- type.  Note `subTm σ (var x) = σ x` definitionally, so the membership is
-- stated at `σ x` directly.
------------------------------------------------------------------------

infix 3 _⊩ˢ_
_⊩ˢ_ : (Γ : Ctx) {Ξ : Cx} → Sub ⌊ Γ ⌋ Ξ → Set
Γ ⊩ˢ σ = {x : Var ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → Γ ∋ x ∷ A → Rel (subTy σ A) (σ x)

-- extension by a member — the λ-case's move.  The target scope is unchanged.
⊩ˢ-ext : {σ : Sub ⌊ Γ ⌋ Ξ} {A : RTy ⌊ Γ ⌋} →
         Γ ⊩ˢ σ → (R : ⊩₁ (subTy σ A)) (u : RTm Ξ) → R ⊩₁∋ u →
         (Γ ▹ A) ⊩ˢ (σ ,ₛ u)
⊩ˢ-ext {σ = σ} {A = A} ρ R u r here =
  relTy (sym (sub-ext-wk σ u A)) (R , r)
⊩ˢ-ext {σ = σ} {A = A} ρ R u r (there {A = B} d) =
  relTy (sym (sub-ext-wk σ u B)) (ρ d)

------------------------------------------------------------------------
-- 5. ★ SHAPE INVERSION — the one genuinely new lemma about the relation.
--
-- `⊢app` recurses on the function and gets SOME `R : ⊩₁ (Π F G)`; a priori `R`
-- could be any constructor.  The four wrong ones are refuted by `Π-reduct`
-- alone: a reduct of `Π F G` is a `Π`, and `base`/`U`/`El n`/`Σ' _ _` are not.
-- The `Π` case then needs only the transfer layer — `irrel₁` to move the
-- argument into the stored domain, `bwd₁` to move the result back along the
-- stored codomain reduction.
--
-- Stated as ELIMINATION rules (they consume the member and produce the
-- existential) rather than as inversion records: that is exactly the shape
-- `fund`'s `⊢app`/`⊢fst`/`⊢snd` cases want, and it keeps the reduct's
-- reduction witness local.
------------------------------------------------------------------------

⊩₁-app : {F : RTy Θ} {G : RTy (Θ ∙)} (R : ⊩₁ (Π F G)) (S : ⊩₁ F)
         {w v : RTm Θ} → R ⊩₁∋ w → S ⊩₁∋ v → Rel (subTy (single v) G) (app w v)
⊩₁-app (⊩₁base p) S h k with Π-reduct p
... | mkΠRed _ _ () _ _
⊩₁-app (⊩₁U p)    S h k with Π-reduct p
... | mkΠRed _ _ () _ _
⊩₁-app (⊩₁ne p n) S h k with Π-reduct p
... | mkΠRed _ _ () _ _
⊩₁-app (⊩₁Σ p _ _) S h k with Π-reduct p
... | mkΠRed _ _ () _ _
⊩₁-app (⊩₁Hom p _) S h k with Π-reduct p
... | mkΠRed _ _ () _ _
⊩₁-app (⊩₁Π p ⊩F ⊩G) S {v = v} h k with Π-reduct p
... | mkΠRed _ _ refl rF rG =
      ( bwd₁ q (⊩G v r)
      , projr (irrel₁ (red→≅ᵀ q) (bwd₁ q (⊩G v r)) (⊩G v r)) _ (projr h v r) )
  where
    r = projl (irrel₁ (red→≅ᵀ rF) S ⊩F) v k
    q = ⟶ᵀ*-sub (single v) rG

⊩₁-fstm : {F : RTy Θ} {G : RTy (Θ ∙)} (R : ⊩₁ (Σ' F G)) {w : RTm Θ} →
          R ⊩₁∋ w → Rel F (fst w)
⊩₁-fstm (⊩₁base p) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-fstm (⊩₁U p)    h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-fstm (⊩₁ne p n) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-fstm (⊩₁Π p _ _) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-fstm (⊩₁Hom p _) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-fstm (⊩₁Σ p ⊩F ⊩G) h with Σ-reduct p
... | mkΣRed _ _ refl rF rG =
      ( bwd₁ rF ⊩F
      , projr (irrel₁ (red→≅ᵀ rF) (bwd₁ rF ⊩F) ⊩F) _ (dfst (projr h)) )

⊩₁-sndm : {F : RTy Θ} {G : RTy (Θ ∙)} (R : ⊩₁ (Σ' F G)) {w : RTm Θ} →
          (h : R ⊩₁∋ w) → Rel (subTy (single (fst w)) G) (snd w)
⊩₁-sndm (⊩₁base p) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-sndm (⊩₁U p)    h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-sndm (⊩₁ne p n) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-sndm (⊩₁Π p _ _) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-sndm (⊩₁Hom p _) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-sndm (⊩₁Σ p ⊩F ⊩G) {w = w} h with Σ-reduct p
... | mkΣRed _ _ refl rF rG =
      ( bwd₁ q (⊩G (fst w) (dfst (projr h)))
      , projr (irrel₁ (red→≅ᵀ q) (bwd₁ q (⊩G (fst w) (dfst (projr h))))
                      (⊩G (fst w) (dfst (projr h))))
              _ (dsnd (projr h)) )
  where
    q = ⟶ᵀ*-sub (single (fst w)) rG

------------------------------------------------------------------------
-- 6. ★ `fund-ty` / `fund` — THE FUNDAMENTAL THEOREM.
--
-- Mutual, structural on the derivation: `⊢lam` needs its domain's `⊢ty`, and
-- `ty-El` needs its code's typing.  Every case is one semantic lemma from
-- `NbEPDirDBLR` plus one equation from §1; the only genuinely semantic step is
-- the shape inversion of §5, at `⊢app`/`⊢fst`/`⊢snd`.
--
-- `Var Ξ` is the non-emptiness of the TARGET scope — see the header.  It is
-- used in exactly three places (`⊢lam`, `⊢⌜Π⌝`, `⊢⌜Σ⌝`): the binders.
------------------------------------------------------------------------

fund-ty : {σ : Sub ⌊ Γ ⌋ Ξ} {A : RTy ⌊ Γ ⌋} →
          Γ ⊢ty A → Var Ξ → Γ ⊩ˢ σ → ⊩₁ (subTy σ A)
fund : {σ : Sub ⌊ Γ ⌋ Ξ} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
       Γ ⊢ t ∷ A → Var Ξ → Γ ⊩ˢ σ → Rel (subTy σ A) (subTm σ t)

-- TYPE FORMATION.  `base`/`U` are their own whnf; `Π`/`Σ'` build the family by
-- extending the substitution; `El` is the one that changes level — down to `⊩₀`
-- through `sem-El`, and back up through `emb`.
fund-ty ty-base x₀ ρ = ⊩₁base doneᵀ
fund-ty ty-U    x₀ ρ = ⊩₁U doneᵀ
fund-ty {Ξ = Ξ} {σ = σ} (ty-Π {B = B} tyA tyB) x₀ ρ = ⊩₁Π doneᵀ ⊩F ⊩G
  where
    ⊩F = fund-ty tyA x₀ ρ

    ⊩G : (u : RTm Ξ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) (subTy (extS σ) B))
    ⊩G u r = ⊩₁cast (sym (sub-single-Ty σ u B))
                    (fund-ty tyB x₀ (⊩ˢ-ext ρ ⊩F u r))
fund-ty {Ξ = Ξ} {σ = σ} (ty-Σ {B = B} tyA tyB) x₀ ρ = ⊩₁Σ doneᵀ ⊩F ⊩G
  where
    ⊩F = fund-ty tyA x₀ ρ

    ⊩G : (u : RTm Ξ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) (subTy (extS σ) B))
    ⊩G u r = ⊩₁cast (sym (sub-single-Ty σ u B))
                    (fund-ty tyB x₀ (⊩ˢ-ext ρ ⊩F u r))
fund-ty {σ = σ} (ty-El {c = c} dc) x₀ ρ = emb (sem-El doneᵀ hc)
  where
    -- `fund` hands back SOME derivation of `⊩₁ U`; move it onto `⊩₁U doneᵀ`
    -- first (both are derivations of the same type, so `irrel₁ crflᵀ` suffices)
    -- and the `U` clause's second component IS the decoding.
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
-- W2 `ty-Hom` — the semantic action `homSem₁` does all the work; the only
-- plumbing is moving each endpoint's membership onto the IH's derivation of
-- `⊩₁ A[σ]` (the `ty-El` idiom: `irrel₁` at `crflᵀ`).  `Hom` is
-- substitution-stable definitionally, so the goal needs no cast.
fund-ty {σ = σ} (ty-Hom {t = t} {u = u} tyA dt du) x₀ ρ = homSem₁ R ht hu
  where
    R  = fund-ty tyA x₀ ρ
    ht = projl (irrel₁ crflᵀ (dfst (fund dt x₀ ρ)) R)
               (subTm σ t) (dsnd (fund dt x₀ ρ))
    hu = projl (irrel₁ crflᵀ (dfst (fund du x₀ ρ)) R)
               (subTm σ u) (dsnd (fund du x₀ ρ))

-- TERMS.
fund (⊢var d) x₀ ρ = ρ d

fund {Ξ = Ξ} {σ = σ} (⊢lam {B = B} {t = s} tyA d) x₀ ρ =
  ( ⊩₁Π doneᵀ ⊩F ⊩G , sem-lam doneᵀ ⊩F ⊩G sns f )
  where
    ⊩F = fund-ty tyA x₀ ρ

    -- ONE call, projected twice: `⊩G u r` and `f u r` must be the first and
    -- second component of the SAME cast, or the membership would be stated at
    -- a different (though equal) semantic type.
    body : (u : RTm Ξ) (r : ⊩F ⊩₁∋ u) →
           Rel (subTy (single u) (subTy (extS σ) B))
               (subTm (single u) (subTm (extS σ) s))
    body u r = relCast (sym (sub-single-Ty σ u B)) (sym (sub-single-Tm σ u s))
                       (fund d x₀ (⊩ˢ-ext ρ ⊩F u r))

    ⊩G : (u : RTm Ξ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) (subTy (extS σ) B))
    ⊩G u r = dfst (body u r)

    f : (u : RTm Ξ) (r : ⊩F ⊩₁∋ u) →
        (⊩G u r) ⊩₁∋ subTm (single u) (subTm (extS σ) s)
    f u r = dsnd (body u r)

    -- ★ the SN premise: instantiate at a variable, then anti-rename (§2).
    r₀ = CR3₁ ⊩F (sne-var x₀)

    sns : SN (subTm (extS σ) s)
    sns = sn-body x₀ (CR1₁ (⊩G (var x₀) r₀) (f (var x₀) r₀))

fund {σ = σ} (⊢app {B = B} {u = u} d₁ d₂) x₀ ρ =
  relTy (sym (sub-comm-Ty σ u B))
        (⊩₁-app (dfst (fund d₁ x₀ ρ)) (dfst (fund d₂ x₀ ρ))
                (dsnd (fund d₁ x₀ ρ)) (dsnd (fund d₂ x₀ ρ)))

fund {Ξ = Ξ} {σ = σ} (⊢pair {B = B} {a = a} {b = b} tyB d₁ d₂) x₀ ρ =
  ( ⊩₁Σ doneᵀ ⊩F ⊩G , sem-pair doneᵀ ⊩F ⊩G sna snb ra rb )
  where
    ⊩F = dfst (fund d₁ x₀ ρ)
    ra = dsnd (fund d₁ x₀ ρ)

    ⊩G : (u : RTm Ξ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) (subTy (extS σ) B))
    ⊩G u r = ⊩₁cast (sym (sub-single-Ty σ u B))
                    (fund-ty tyB x₀ (⊩ˢ-ext ρ ⊩F u r))

    -- the second component arrives at `B[a][σ]`; push `σ` inside, then bridge
    -- to the family's instance by proof-irrelevance in the membership argument.
    Sb = relTy (sub-comm-Ty σ a B) (fund d₂ x₀ ρ)

    sna = CR1₁ ⊩F ra
    snb = CR1₁ (dfst Sb) (dsnd Sb)
    rb  = projl (irrel₁ crflᵀ (dfst Sb) (⊩G (subTm σ a) ra))
                (subTm σ b) (dsnd Sb)

fund (⊢fst d) x₀ ρ = ⊩₁-fstm (dfst (fund d x₀ ρ)) (dsnd (fund d x₀ ρ))

fund {σ = σ} (⊢snd {B = B} {p = p} d) x₀ ρ =
  relTy (sym (sub-comm-Ty σ (fst p) B))
        (⊩₁-sndm (dfst (fund d x₀ ρ)) (dsnd (fund d x₀ ρ)))

fund ⊢⌜base⌝ x₀ ρ = ( ⊩₁U doneᵀ , sem-⌜base⌝ doneᵀ )

fund {Ξ = Ξ} {σ = σ} (⊢⌜Π⌝ {c = c} {d = e} dc de) x₀ ρ =
  ( ⊩₁U doneᵀ , sem-⌜Π⌝ doneᵀ snc sne ⊩c f )
  where
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    ⊩c  = sem-El doneᵀ hc

    -- the codomain code lives in `Γ ▹ El c`, so the extension's semantic type
    -- is `emb ⊩c` and its members come from `emb-coh`.
    body : (u : RTm Ξ) → ⊩c ⊩₀∋ u → Rel U (subTm (σ ,ₛ u) e)
    body u r = fund de x₀ (⊩ˢ-ext ρ (emb ⊩c) u (projl (emb-coh ⊩c) u r))

    f : (u : RTm Ξ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) (subTm (extS σ) e)))
    f u r = ⊩₀cast (cong El (sym (sub-single-Tm σ u e)))
                   (sem-El doneᵀ
                     (projl (irrel₁ crflᵀ (dfst (body u r)) (⊩₁U doneᵀ))
                            (subTm (σ ,ₛ u) e) (dsnd (body u r))))

    r₀ = CR3₀ ⊩c (sne-var x₀)

    sne : SN (subTm (extS σ) e)
    sne = sn-body x₀ (subst SN (sym (sub-single-Tm σ (var x₀) e))
                            (CR1₁ (dfst (body (var x₀) r₀))
                                  (dsnd (body (var x₀) r₀))))

fund {Ξ = Ξ} {σ = σ} (⊢⌜Σ⌝ {c = c} {d = e} dc de) x₀ ρ =
  ( ⊩₁U doneᵀ , sem-⌜Σ⌝ doneᵀ snc sne ⊩c f )
  where
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    ⊩c  = sem-El doneᵀ hc

    body : (u : RTm Ξ) → ⊩c ⊩₀∋ u → Rel U (subTm (σ ,ₛ u) e)
    body u r = fund de x₀ (⊩ˢ-ext ρ (emb ⊩c) u (projl (emb-coh ⊩c) u r))

    f : (u : RTm Ξ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) (subTm (extS σ) e)))
    f u r = ⊩₀cast (cong El (sym (sub-single-Tm σ u e)))
                   (sem-El doneᵀ
                     (projl (irrel₁ crflᵀ (dfst (body u r)) (⊩₁U doneᵀ))
                            (subTm (σ ,ₛ u) e) (dsnd (body u r))))

    r₀ = CR3₀ ⊩c (sne-var x₀)

    sne : SN (subTm (extS σ) e)
    sne = sn-body x₀ (subst SN (sym (sub-single-Tm σ (var x₀) e))
                            (CR1₁ (dfst (body (var x₀) r₀))
                                  (dsnd (body (var x₀) r₀))))

-- W2 stage 1: the `⌜Hom⌝` code is semantic via `homSem₀` (through
-- `sem-⌜Hom⌝`); its endpoints come down to level 0 through `emb-coh`.
fund {σ = σ} (⊢⌜Hom⌝ {c = c} {a = a} {b = b} dc da db) x₀ ρ =
  ( ⊩₁U doneᵀ , sem-⌜Hom⌝ doneᵀ snc sna snb ⊩c ha hb )
  where
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    ⊩c  = sem-El doneᵀ hc

    ha = projr (emb-coh ⊩c) (subTm σ a)
               (projl (irrel₁ crflᵀ (dfst (fund da x₀ ρ)) (emb ⊩c))
                      (subTm σ a) (dsnd (fund da x₀ ρ)))
    hb = projr (emb-coh ⊩c) (subTm σ b)
               (projl (irrel₁ crflᵀ (dfst (fund db x₀ ρ)) (emb ⊩c))
                      (subTm σ b) (dsnd (fund db x₀ ρ)))

    sna = CR1₀ ⊩c ha
    snb = CR1₀ ⊩c hb

-- W2 stage 1: `hrefl` is an inert neutral (its unfold family is deferred
-- with the canonicity package), so it inhabits the `Hom` at its own
-- endpoints by `CR3` — via `sem-hrefl`.
fund {σ = σ} (⊢hrefl {c = c} {t = t} dc dt) x₀ ρ =
  ( homSem₁ (dfst Rt) (dsnd Rt) (dsnd Rt)
  , sem-hrefl (dfst Rt) snc snt (dsnd Rt) )
  where
    Rt = fund dt x₀ ρ
    snc = CR1₁ (dfst (fund dc x₀ ρ)) (dsnd (fund dc x₀ ρ))
    snt = CR1₁ (dfst Rt) (dsnd Rt)

-- ★ `⊢conv` — no validity premise, no `⊢ty` closed under conversion.  The
-- relation is already closed under conversion; this is the whole of §4.0.
fund {σ = σ} (⊢conv d c) x₀ ρ =
  ( conv₁ (≅ᵀ-sub σ c) (dfst (fund d x₀ ρ))
  , sem-conv (≅ᵀ-sub σ c) (dfst (fund d x₀ ρ))
             (conv₁ (≅ᵀ-sub σ c) (dfst (fund d x₀ ρ))) (dsnd (fund d x₀ ρ)) )

------------------------------------------------------------------------
-- 7. STARTING THE INDUCTION, and the corollaries.
--
-- ★ EVERY RENAMING SUBSTITUTION IS REDUCIBLE.  This is the "identity
-- substitution is reducible" lemma, generalised over a renaming — and the
-- generalisation is what makes it provable WITHOUT a renaming action on `⊩₁`
-- (which does not exist, see the header).  At `c-▹` the type is built by
-- `fund-ty` AT THE RENAMED SUBSTITUTION directly, so nothing ever has to be
-- transported across scopes; the members are variables, free by `CR3₁`.
--
-- Recursion is on `⊢ctx Γ`, which is why `wnorm` needs it and `fund` does not.
------------------------------------------------------------------------

⊩ˢ-ren : ⊢ctx Γ → (ρ : Ren ⌊ Γ ⌋ Ξ) → Γ ⊩ˢ ⟨ ρ ⟩ᵣ
⊩ˢ-ren c-◇ ρ ()
⊩ˢ-ren (c-▹ {A = A} wΓ tyA) ρ here = ( R , CR3₁ R (sne-var (ρ vz)) )
  where
    eq : subTy ⟨ ρ ⟩ᵣ (renTy vs A) ≡ subTy ⟨ ρ ∘ᵣ vs ⟩ᵣ A
    eq = trans (subTy-renTy A) (subTy-cong (λ _ → refl) A)

    R = ⊩₁cast (sym eq) (fund-ty tyA (ρ vz) (⊩ˢ-ren wΓ (ρ ∘ᵣ vs)))
⊩ˢ-ren (c-▹ wΓ tyA) ρ (there {A = B} d) =
  relTy (sym eq) (⊩ˢ-ren wΓ (ρ ∘ᵣ vs) d)
  where
    eq : subTy ⟨ ρ ⟩ᵣ (renTy vs B) ≡ subTy ⟨ ρ ∘ᵣ vs ⟩ᵣ B
    eq = trans (subTy-renTy B) (subTy-cong (λ _ → refl) B)

------------------------------------------------------------------------
-- ★ THE THEOREM.  Run the induction at `vs`, which makes the target scope
-- non-empty for free, and undo that one weakening with §2.
------------------------------------------------------------------------

snorm : {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → ⊢ctx Γ → Γ ⊢ t ∷ A → SN t
snorm {t = t} wΓ d = sn-anti (subst SN (subTm-var vs t) (CR1₁ R m))
  where
    R = dfst (fund d vz (⊩ˢ-ren wΓ vs))
    m = dsnd (fund d vz (⊩ˢ-ren wΓ vs))

-- ⚠ WEAK normalization is the headline (handoff §4.1): `SN` here is the
-- INDUCTIVE Joachimski–Matthes predicate, and nothing proves it equivalent to
-- accessibility-`SN`.  `dec-conv` consumes `WN`, so nothing downstream cares.
wnorm : {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → ⊢ctx Γ → Γ ⊢ t ∷ A → WN t
wnorm wΓ d = wn (snorm wΓ d)

------------------------------------------------------------------------
-- ★ PHASE 1 CLOSED: `dec-conv` with its normalization premises DISCHARGED.
-- Deciding conversion of two well-typed terms now asks for nothing but the
-- derivations (and decidable equality of raw terms, which is structural).
------------------------------------------------------------------------

dec-conv-typed : (dec-eq : {Θ : Cx} (t u : RTm Θ) → Dec (t ≡ u)) →
                 {t u : RTm ⌊ Γ ⌋} {A B : RTy ⌊ Γ ⌋} →
                 ⊢ctx Γ → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B → Dec (t ≅ u)
dec-conv-typed deq wΓ d₁ d₂ with wnorm wΓ d₁ | wnorm wΓ d₂
... | mkWN n₁ r₁ nm₁ _ | mkWN n₂ r₂ nm₂ _ = dec-conv deq r₁ nm₁ r₂ nm₂

------------------------------------------------------------------------
-- 8. NON-VACUITY — the theorem RUNS.
--
-- Type-checking these is the check that `fund` is not merely inhabited but
-- computes: each equation forces the whole induction (`⊩ˢ-ren`, the semantic
-- lemmas, `wn`) to evaluate on a closed derivation, and pins the normal form.
------------------------------------------------------------------------

-- `◇ ⊢ λx.x ∷ Π base base` — already normal, and `wnorm` says so.
id-nf : WN.nfm (wnorm c-◇ ⊢id) ≡ lam (var vz)
id-nf = refl

-- `(◇ ▹ base) ⊢ (λx.x) y ∷ base` — a real β-redex, contracted by the theorem.
appex-nf : WN.nfm (wnorm (c-▹ c-◇ ty-base) ⊢appex) ≡ var vz
appex-nf = refl
