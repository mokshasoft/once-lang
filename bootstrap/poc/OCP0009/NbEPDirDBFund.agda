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
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_; ⊥; ⊥-elim )

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
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋
        ; _∋_∷_; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd
        ; El-⌜Hom⌝; ξ-El; El-⌜Π⌝
        ; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢trU; ⊢conv
        ; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom
        ; ⊢ctx_; c-◇; c-▹
        ; ⊢id; ⊢appex )
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; false; occTm; subTm-occ
        ; pw?; stkC?; pwBody; pwDom; pwShift
        ; pw?-ren; stkC?-ren; pwBody-ren; wk-ren-tm; pw?-sub
        ; stk⊥pw; pw⊥stk )
open import poc.OCP0009.NbEPDirDBSR using ( ≅ᵀ-sub; sub-comm )
open import poc.OCP0009.NbEPDirDBConf using ( pwShift-ren )
open import poc.OCP0009.NbEPDirDBDec using ( Dec; dec-conv )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; confluentᵀ; church-rosserᵀ; Π-inj
        ; red→≅ᵀ; Π-reduct; Σ-reduct; mkΠRed; mkΣRed )
open import poc.OCP0009.NbEPDirDBSubj
  using ( HomΠShape; hsΠ; hsH; hom-shape; pw-El-decode
        ; HomRed; mkHomRed; Hom-to-Hom
        ; HomToΠ; via-U; via-Π; hom-to-Π
        ; U-reduct; wk-cancel-tm )
open import poc.OCP0009.NbEPDirDBLR
  using ( SNe; sne-var; sne-app; sne-fst; sne-snd; sne-hrefl; sne-tr
        ; SN; sn-ne; sn-lam; sn-pair; sn-cb; sn-cΠ; sn-cΣ; sn-cH; sn-exp
        ; SNRed; snr-β; snr-βfst; snr-βsnd; snr-app; snr-fst; snr-snd
        ; snr-hreflᶜ; snr-J-base; snr-J-Σ; snr-taut; snr-trᵖ
        ; trstk?-ren; nopw?-ren; trlam?-ren; nopw?; trlam?
        ; nopw⊥pw; stk⊥dead; pw⊥dead; dead→nopw; snr-nonpw
        ; snr-hrefl-pw; snr-J-Hom; snr-tr-pw; nopw?-red; nopw?-red*
        ; CSR; csr-here; csr-hom; csr→⟶; csr-nonpw; csr-stk⊥; sn-csr
        ; _⟶csr*_; csr-done; csr-step; csrs-hom
        ; PayT; payChain; payT-exp; payT-whred; payT-irrel
        ; payT-cast; payT-code; payHomT; _⟶snr*_; snr-done; snr-step
        ; ⊩₀_; ⊩₀base; ⊩₀ne; ⊩₀Π; ⊩₀Σ; ⊩₀Hom; _⊩₀∋_; bwd₀; exp₁
        ; base-nf; El-ne-reduct; mkElNe; Hom-stk-reduct; mkHomStk
        ; nopw?; stkC?; stablecd?; sne→spine; wk-single; snr→⟶
        ; mem-whred₁; homSem₀; homSem₀-mem-endpoints
        ; sne→stablecd; trstk?
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

sne-anti : {ρ : Ren Θ Ξ} {t : RTm Θ} → SNe (renTm ρ t) → SNe t
sn-anti  : {ρ : Ren Θ Ξ} {t : RTm Θ} → SN  (renTm ρ t) → SN t
snr-anti : {ρ : Ren Θ Ξ} {t : RTm Θ} {v : RTm Ξ} → SNRed (renTm ρ t) v →
           Σ (RTm Θ) (λ t' → SNRed t t' × (v ≡ renTm ρ t'))
csr-anti : {ρ : Ren Θ Ξ} {t : RTm Θ} {v : RTm Ξ} → CSR (renTm ρ t) v →
           Σ (RTm Θ) (λ t' → CSR t t' × (v ≡ renTm ρ t'))

sne-anti {t = var x}    _             = sne-var x
sne-anti {t = app t u}  (sne-app n s) = sne-app (sne-anti n) (sn-anti s)
sne-anti {t = fst p}    (sne-fst n)   = sne-fst (sne-anti n)
sne-anti {t = snd p}    (sne-snd n)   = sne-snd (sne-anti n)
sne-anti {ρ = ρ} {t = hrefl c t} (sne-hrefl hc ht kn) =
  sne-hrefl (sn-anti hc) (sn-anti ht) (trans (sym (nopw?-ren ρ c)) kn)
sne-anti {ρ = ρ} {t = tr d p e} (sne-tr hd hp he key) =
  sne-tr (sn-anti hd) (sn-anti hp) (sn-anti he)
         (trans (sym (trstk?-ren ρ d p)) key)

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
snr-anti {t = hrefl c s} (snr-hreflᶜ σ) with csr-anti σ
... | c' , (σ' , refl) = hrefl c' s , (snr-hreflᶜ σ' , refl)
snr-anti {ρ = ρ} {t = hrefl c s} (snr-hrefl-pw kp) =
  lam (hrefl (pwBody c) (app (renTm vs s) (var vz)))
  , ( snr-hrefl-pw (trans (sym (pw?-ren ρ c)) kp)
    , cong₂ (λ x y → lam (hrefl x (app y (var vz))))
            (pwBody-ren ρ c (trans (sym (pw?-ren ρ c)) kp))
            (sym (wk-ren-tm ρ s)) )
snr-anti {t = tr (⌜Hom⌝ c a m) (hrefl ⌜base⌝ s) e} (snr-J-base hd hs) =
  e , (snr-J-base (sn-anti hd) (sn-anti hs) , refl)
snr-anti {t = tr d (hrefl ⌜base⌝ s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl ⌜base⌝ s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e} (snr-J-Σ hd h₁ h₂ hs) =
  e , (snr-J-Σ (sn-anti hd) (sn-anti h₁) (sn-anti h₂) (sn-anti hs) , refl)
snr-anti {t = tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr (var vz) (lam f) e} snr-taut =
  app (lam f) e , (snr-taut , refl)
snr-anti {ρ = ρ} {t = tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e}
         (snr-J-Hom hd h₁ h₂ h₃ hs kh) =
  e , ( snr-J-Hom (sn-anti hd) (sn-anti h₁) (sn-anti h₂) (sn-anti h₃)
                  (sn-anti hs) (trans (sym (stkC?-ren ρ c₁)) kh)
      , refl )
snr-anti {ρ = ρ} {t = tr (⌜Hom⌝ c a (var vz)) (lam f) e}
         (snr-tr-pw hc ha kp) =
  lam (tr (⌜Hom⌝ (renTm pwShift (pwBody c))
                 (app (renTm vs a) (var (vs vz)))
                 (var vz))
          f (app (renTm vs e) (var vz)))
  , ( snr-tr-pw (sn-anti hc) (sn-anti ha) kp'
    , cong lam
        (tr-cong₃
          (⌜Hom⌝-cong₃
            (trans (cong (renTm pwShift) (pwBody-ren (extR ρ) c kp'))
                   (sym (pwShift-ren ρ (pwBody c))))
            (cong (λ z → app z (var (vs vz))) (sym (wk-ren-tm (extR ρ) a)))
            refl)
          refl
          (cong (λ z → app z (var vz)) (sym (wk-ren-tm ρ e)))) )
  where
  kp' = trans (sym (pw?-ren (extR _) c)) kp
snr-anti {t = tr d (hrefl (var x) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (var x) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (lam g) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (lam g) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (app g w) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (pair g w) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (pair g w) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (fst g) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (snd g) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (⌜Π⌝ g w) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (⌜Hom⌝ g w v) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
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

csr-anti {t = var x} (csr-here ())
csr-anti {t = lam _} (csr-here ())
csr-anti {t = pair _ _} (csr-here ())
csr-anti {t = ⌜base⌝} (csr-here ())
csr-anti {t = ⌜Π⌝ _ _} (csr-here ())
csr-anti {t = ⌜Σ⌝ _ _} (csr-here ())
csr-anti {t = app f u} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = fst q} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = snd q} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = hrefl _ _} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = tr _ _ _} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = ⌜Hom⌝ c a b} (csr-here ())
csr-anti {t = ⌜Hom⌝ c a b} (csr-hom σ) with csr-anti σ
... | c' , (σ' , refl) = ⌜Hom⌝ c' a b , (csr-hom σ' , refl)

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
⊩₀cast eq R = subst ⊩₀_ eq R

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
------------------------------------------------------------------------
-- ★★ W2b (G1f) — `hrefl`'s SEMANTIC VALIDATION, payload-powered.
-- At non-Π interps the membership is SN-only: `snHH` builds it by
-- descending the code's ⌜Hom⌝ SPINE (CSR), with the interp's own
-- non-Π chain refuting the ⌜Π⌝-leaf by confluence.  At Π interps the
-- payload's node supplies the unfolding: the closure head-expands
-- along `payChain` into the RECURSIVE membership one Π-layer down,
-- and the SN part instantiates the node at the fresh `x₀` (the
-- established `sn-body` pattern).
------------------------------------------------------------------------

-- neutral codes are pw-immune.
sne→nopw : {t : RTm Ξ} → SNe t → nopw? t ≡ true
sne→nopw (sne-var x)        = refl
sne→nopw (sne-app n _)      = sne→spine n
sne→nopw (sne-fst n)        = sne→spine n
sne→nopw (sne-snd n)        = sne→spine n
sne→nopw (sne-hrefl _ _ _)  = refl
sne→nopw (sne-tr _ _ _ key) = key

-- star-folds for the head strategy.
snrs-hreflᶜ : {c c* t : RTm Ξ} → c ⟶csr* c* → hrefl c t ⟶snr* hrefl c* t
snrs-hreflᶜ csr-done       = snr-done
snrs-hreflᶜ (csr-step σ q) = snr-step (snr-hreflᶜ σ) (snrs-hreflᶜ q)

snExpStar : {t t' : RTm Ξ} → t ⟶snr* t' → SN t' → SN t
snExpStar snr-done       h = h
snExpStar (snr-step r q) h = sn-exp r (snExpStar q h)

expStar₁ : {A : RTy Ξ} (R : ⊩₁ A) {t t' : RTm Ξ} →
           t ⟶snr* t' → R ⊩₁∋ t' → R ⊩₁∋ t
expStar₁ R snr-done       h = h
expStar₁ R (snr-step r q) h = exp₁ R r (expStar₁ R q h)

mem₁-cast : {A B : RTy Ξ} (eq : A ≡ B) (R : ⊩₁ A) {w : RTm Ξ} →
            R ⊩₁∋ w → (subst ⊩₁_ eq R) ⊩₁∋ w
mem₁-cast refl R h = h

-- the ⌜Hom⌝-spine context for the raw-SN construction.
data Spine (Ξ : Cx) : Set where
  sp-nil  : Spine Ξ
  sp-cons : (a b : RTm Ξ) → SN a → SN b → Spine Ξ → Spine Ξ

plug : {Ξ : Cx} → Spine Ξ → RTm Ξ → RTm Ξ
plug sp-nil x                = x
plug (sp-cons a b _ _ sp) x  = plug sp (⌜Hom⌝ x a b)

wrapCSR : (sp : Spine Ξ) {x y : RTm Ξ} → CSR x y →
          CSR (plug sp x) (plug sp y)
wrapCSR sp-nil σ                = σ
wrapCSR (sp-cons a b _ _ sp) σ  = wrapCSR sp (csr-hom σ)

nopw-plug : (sp : Spine Ξ) {x : RTm Ξ} → nopw? x ≡ true →
            nopw? (plug sp x) ≡ true
nopw-plug sp-nil h               = h
nopw-plug (sp-cons a b _ _ sp) h = nopw-plug sp h

pw-plug : (sp : Spine Ξ) {x : RTm Ξ} → pw? x ≡ true →
          pw? (plug sp x) ≡ true
pw-plug sp-nil h               = h
pw-plug (sp-cons a b _ _ sp) h = pw-plug sp h

snPlug : (sp : Spine Ξ) {x : RTm Ξ} → SN x → SN (plug sp x)
snPlug sp-nil h                    = h
snPlug (sp-cons a b sa sb sp) h    = snPlug sp (sn-cH h sa sb)

-- SN of `hrefl` at a code whose decode NEVER reaches Π: descend the
-- spine; leaves are neutral (`sne→nopw`) or canonical-non-pw; the
-- ⌜Π⌝-leaf contradicts the ambient interp through `pw-El-decode`.
snHH : (sp : Spine Ξ) {C : RTm Ξ} (snC : SN C) {t : RTm Ξ} (snt : SN t) →
       (∀ {P : RTy Ξ} {Q : RTy (Ξ ∙)} → El (plug sp C) ⟶ᵀ* Π P Q → ⊥) →
       SN (hrefl (plug sp C) t)
snHH sp (sn-exp r h) snt noPiT =
  sn-exp (snr-hreflᶜ (wrapCSR sp (csr-here r)))
         (snHH sp h snt
               (λ ch → noPiT (stepᵀ (ξ-El (csr→⟶ (wrapCSR sp (csr-here r)))) ch)))
snHH sp (sn-ne n) snt noPiT =
  sn-ne (sne-hrefl (snPlug sp (sn-ne n)) snt (nopw-plug sp (sne→nopw n)))
snHH sp (sn-lam h) snt noPiT =
  sn-ne (sne-hrefl (snPlug sp (sn-lam h)) snt (nopw-plug sp refl))
snHH sp (sn-pair ha hb) snt noPiT =
  sn-ne (sne-hrefl (snPlug sp (sn-pair ha hb)) snt (nopw-plug sp refl))
snHH sp sn-cb snt noPiT =
  sn-ne (sne-hrefl (snPlug sp sn-cb) snt (nopw-plug sp refl))
snHH sp (sn-cΣ h₁ h₂) snt noPiT =
  sn-ne (sne-hrefl (snPlug sp (sn-cΣ h₁ h₂)) snt (nopw-plug sp refl))
snHH sp (sn-cΠ {c = γ} {d = δ} h₁ h₂) snt noPiT =
  ⊥-elim (noPiT (Σ.fst (Σ.snd (pw-El-decode (plug sp (⌜Π⌝ γ δ))
                                            (pw-plug sp refl)))))
snHH sp (sn-cH {c = C'} {a = a'} {b = b'} hC ha hb) snt noPiT =
  snHH (sp-cons a' b' ha hb sp) hC snt noPiT

-- ★ the membership itself, by recursion on the interp.  The interp's
-- type and the code stay LINKED by a conversion (`lk`) — it powers the
-- ⌜Π⌝-leaf refutations at non-Π interps and the body-link one Π-layer
-- down.
csrs→⟶* : {c c* : RTm Ξ} → c ⟶csr* c* → c ⟶* c*
csrs→⟶* csr-done       = done
csrs→⟶* (csr-step σ q) = step (csr→⟶ σ) (csrs→⟶* q)

semHreflPay :
  (x₀ : Var Ξ) {A : RTy Ξ} {c t : RTm Ξ} (R₀ : ⊩₀ A)
  (lk : A ≅ᵀ El c) → SN c → PayT R₀ c →
  SN t → (ht : (emb R₀) ⊩₁∋ t) →
  (homSem₁ (emb R₀) ht ht) ⊩₁∋ hrefl c t
semHreflPay x₀ (⊩₀base p) lk snc pay snt ht =
  snHH sp-nil snc snt noPiT
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (bE , πE) with base-nf bE
  ...   | refl with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semHreflPay x₀ (⊩₀ne p n) lk snc pay snt ht =
  snHH sp-nil snc snt noPiT
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (nE , πE) with El-ne-reduct n nE
  ...   | mkElNe _ _ refl with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semHreflPay x₀ (⊩₀Σ p ⊩F ⊩G) lk snc pay snt ht =
  snHH sp-nil snc snt noPiT
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (σE , πE) with Σ-reduct σE
  ...   | mkΣRed _ _ refl _ _ with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semHreflPay x₀ (⊩₀Hom p sh) lk snc pay snt ht =
  snHH sp-nil snc snt noPiT
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (hE , πE) with Hom-stk-reduct sh hE
  ...   | mkHomStk _ _ _ _ refl with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semHreflPay x₀ {c = c} {t = t} (⊩₀Π {G = G} p ⊩F ⊩G) lk snc pay snt ht =
  ( snWhole , closure )
  where
  -- the code-side decode of any payload node, linked to the interp's
  -- own Π-chain through `lk`.
  bodyLk : (v : RTm _) (r : ⊩F ⊩₀∋ v) →
           subTy (single v) G
           ≅ᵀ El (subTm (single v)
                        (pwBody (Σ.fst (pay v r))))
  bodyLk v r =
    ctrnᵀ (≅ᵀ-sub (single v)
            (Σ.snd (Π-inj
              (ctrnᵀ (csymᵀ (red→≅ᵀ p))
                (ctrnᵀ lk
                  (red→≅ᵀ
                    (⟶ᵀ*-trans
                      (⟶ᵀ*-El (csrs→⟶* (Σ.fst (Σ.snd (pay v r)))))
                      (Σ.fst (Σ.snd (pw-El-decode (Σ.fst (pay v r))
                               (Σ.fst (Σ.snd (Σ.snd (pay v r))))))))))))))
          (csymᵀ (≅ᵀ-sub (single v)
            (red→≅ᵀ (Σ.snd (Σ.snd (pw-El-decode (Σ.fst (pay v r))
                       (Σ.fst (Σ.snd (Σ.snd (pay v r))))))))))

  rE₀ = CR3₁ (emb ⊩F) (sne-var x₀)
  r₀  = projr (emb-coh ⊩F) (var x₀) rE₀
  htv₀ = projr ht (var x₀) rE₀

  rmem₀ =
    semHreflPay x₀ (⊩G (var x₀) r₀) (bodyLk (var x₀) r₀)
      (Σ.fst (Σ.snd (Σ.snd (Σ.snd (pay (var x₀) r₀)))))
      (Σ.snd (Σ.snd (Σ.snd (Σ.snd (pay (var x₀) r₀)))))
      (CR1₁ (emb (⊩G (var x₀) r₀)) htv₀) htv₀

  body-eq : hrefl (subTm (single (var x₀)) (pwBody (Σ.fst (pay (var x₀) r₀))))
                  (app t (var x₀))
            ≡ subTm (single (var x₀))
                    (hrefl (pwBody (Σ.fst (pay (var x₀) r₀)))
                           (app (renTm vs t) (var vz)))
  body-eq = cong (λ z → hrefl (subTm (single (var x₀))
                                     (pwBody (Σ.fst (pay (var x₀) r₀))))
                              (app z (var x₀)))
                 (sym (wk-single t))

  snWhole : SN (hrefl c t)
  snWhole =
    snExpStar (snrs-hreflᶜ (Σ.fst (Σ.snd (pay (var x₀) r₀))))
      (sn-exp (snr-hrefl-pw (Σ.fst (Σ.snd (Σ.snd (pay (var x₀) r₀)))))
        (sn-lam (sn-body x₀
          (subst SN body-eq (CR1₁ _ rmem₀)))))

  closure : (v : RTm _) (r' : (emb ⊩F) ⊩₁∋ v) → _
  closure v r' =
    mem₁-cast
      (sym (Hom-cong₃ refl
             (cong₂ app (wk-single t) refl)
             (cong₂ app (wk-single t) refl)))
      (homSem₁ (emb (⊩G v (projr (emb-coh ⊩F) v r')))
               (projr ht v r') (projr ht v r'))
      (expStar₁ _
        (payChain (Σ.fst (Σ.snd (pay v (projr (emb-coh ⊩F) v r'))))
                  (Σ.fst (Σ.snd (Σ.snd (pay v (projr (emb-coh ⊩F) v r')))))
                  v (CR1₁ (emb ⊩F) r') t)
        (semHreflPay x₀ (⊩G v (projr (emb-coh ⊩F) v r'))
          (bodyLk v (projr (emb-coh ⊩F) v r'))
          (Σ.fst (Σ.snd (Σ.snd (Σ.snd (pay v (projr (emb-coh ⊩F) v r'))))))
          (Σ.snd (Σ.snd (Σ.snd (Σ.snd (pay v (projr (emb-coh ⊩F) v r'))))))
          (CR1₁ (emb (⊩G v (projr (emb-coh ⊩F) v r'))) (projr ht v r'))
          (projr ht v r')))


-- ★ W2b: the CODE-FATE analysis for `goh` — normalize an hrefl-path's
-- code down its ⌜Hom⌝ spine (CSR); the leaf is either J-able (stable)
-- or forever-dead.  Replaces per-shape rows with one recursion.
data CodeFate {Ξ : Cx} (c* : RTm Ξ) : Set where
  cf-stk  : stkC? c* ≡ true → CodeFate c*
  cf-dead : stablecd? c* ≡ true → CodeFate c*

codeNorm : {c' : RTm Ξ} → SN c' → nopw? c' ≡ true →
           Σ (RTm Ξ) (λ c* → (c' ⟶csr* c*) × CodeFate c*)
codeNorm (sn-exp r h) kn with codeNorm h (nopw?-red (snr→⟶ r) kn)
... | c* , (csr , fate) = c* , (csr-step (csr-here r) csr , fate)
codeNorm (sn-ne n) kn = _ , (csr-done , cf-dead (sne→stablecd n))
codeNorm (sn-lam h) kn = _ , (csr-done , cf-dead refl)
codeNorm (sn-pair ha hb) kn = _ , (csr-done , cf-dead refl)
codeNorm sn-cb kn = _ , (csr-done , cf-stk refl)
codeNorm (sn-cΣ h₁ h₂) kn = _ , (csr-done , cf-stk refl)
codeNorm (sn-cΠ h₁ h₂) ()
codeNorm (sn-cH {a = a₂} {b = b₂} hC ha hb) kn with codeNorm hC kn
... | C* , (csr , cf-stk k)  =
      ⌜Hom⌝ C* a₂ b₂ , (csrs-hom' csr , cf-stk k)
  where
  csrs-hom' : {x y : RTm _} → x ⟶csr* y →
              ⌜Hom⌝ x a₂ b₂ ⟶csr* ⌜Hom⌝ y a₂ b₂
  csrs-hom' csr-done       = csr-done
  csrs-hom' (csr-step σ q) = csr-step (csr-hom σ) (csrs-hom' q)
... | C* , (csr , cf-dead k) =
      ⌜Hom⌝ C* a₂ b₂ , (csrs-hom' csr , cf-dead k)
  where
  csrs-hom' : {x y : RTm _} → x ⟶csr* y →
              ⌜Hom⌝ x a₂ b₂ ⟶csr* ⌜Hom⌝ y a₂ b₂
  csrs-hom' csr-done       = csr-done
  csrs-hom' (csr-step σ q) = csr-step (csr-hom σ) (csrs-hom' q)

sn-csrs : {t t' : RTm Ξ} → SN t → t ⟶csr* t' → SN t'
sn-csrs h csr-done       = h
sn-csrs h (csr-step σ q) = sn-csrs (sn-csr h σ) q

nopw?-csrs : {t t' : RTm Ξ} → t ⟶csr* t' → nopw? t ≡ true → nopw? t' ≡ true
nopw?-csrs csr-done       h = h
nopw?-csrs (csr-step σ q) h = nopw?-csrs q (nopw?-red (csr→⟶ σ) h)

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
  ( ⊩₁U doneᵀ , sem-⌜Π⌝ doneᵀ snc sne ⊩c f pays )
  where
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    ⊩c  = sem-El doneᵀ hc

    -- the codomain code lives in `Γ ▹ El c`, so the extension's semantic type
    -- is `emb ⊩c` and its members come from `emb-coh`.
    body : (u : RTm Ξ) → ⊩c ⊩₀∋ u → Rel U (subTm (σ ,ₛ u) e)
    body u r = fund de x₀ (⊩ˢ-ext ρ (emb ⊩c) u (projl (emb-coh ⊩c) u r))

    memb : (u : RTm Ξ) (r : ⊩c ⊩₀∋ u) → (⊩₁U doneᵀ) ⊩₁∋ subTm (σ ,ₛ u) e
    memb u r = projl (irrel₁ crflᵀ (dfst (body u r)) (⊩₁U doneᵀ))
                     (subTm (σ ,ₛ u) e) (dsnd (body u r))

    f : (u : RTm Ξ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) (subTm (extS σ) e)))
    f u r = ⊩₀cast (cong El (sym (sub-single-Tm σ u e)))
                   (sem-El doneᵀ (memb u r))

    -- W2b: the body code's SN and payload at each argument — straight
    -- off `fund de`'s enriched U-membership (the environment case that
    -- WALLED before the payload existed is now cargo).
    pays : (u : RTm Ξ) (r : ⊩c ⊩₀∋ u) →
           SN (subTm (single u) (subTm (extS σ) e))
           × PayT (f u r) (subTm (single u) (subTm (extS σ) e))
    pays u r =
      ( subst SN (sym (sub-single-Tm σ u e)) (projl (memb u r))
      , payT-cast (cong El (sym (sub-single-Tm σ u e)))
                  (Σ.fst (projr (memb u r)))
                  (payT-code (Σ.fst (projr (memb u r)))
                             (sym (sub-single-Tm σ u e))
                             (Σ.snd (projr (memb u r)))) )

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
  ( ⊩₁U doneᵀ , sem-⌜Hom⌝ doneᵀ snc sna snb ⊩c payc ha hb )
  where
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    ⊩c  = sem-El doneᵀ hc
    payc = Σ.snd (projr hc)

    ha = projr (emb-coh ⊩c) (subTm σ a)
               (projl (irrel₁ crflᵀ (dfst (fund da x₀ ρ)) (emb ⊩c))
                      (subTm σ a) (dsnd (fund da x₀ ρ)))
    hb = projr (emb-coh ⊩c) (subTm σ b)
               (projl (irrel₁ crflᵀ (dfst (fund db x₀ ρ)) (emb ⊩c))
                      (subTm σ b) (dsnd (fund db x₀ ρ)))

    sna = CR1₀ ⊩c ha
    snb = CR1₀ ⊩c hb

-- ★★ W2b: `hrefl` computes now (`hrefl-pw`), so its semantic case
-- reads the U-PAYLOAD: the membership is built by `semHreflPay` at the
-- code's decoded interp and transferred to the ambient's interp by
-- proof-irrelevance (both interpret the same `El`).
fund {σ = σ} (⊢hrefl {c = c} {t = t} dc dt) x₀ ρ =
  ( homSem₁ (dfst Rt) (dsnd Rt) (dsnd Rt)
  , projl (irrel₁ crflᵀ (homSem₁ (emb R₀) htE htE)
                        (homSem₁ (dfst Rt) (dsnd Rt) (dsnd Rt)))
          (hrefl (subTm σ c) (subTm σ t))
          (semHreflPay x₀ R₀ crflᵀ (projl hcode) (Σ.snd (projr hcode))
                       snt htE) )
  where
    Rt = fund dt x₀ ρ
    snt = CR1₁ (dfst Rt) (dsnd Rt)
    hcode = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
                  (subTm σ c) (dsnd (fund dc x₀ ρ))
    R₀ = Σ.fst (projr hcode)
    htE = projl (irrel₁ crflᵀ (dfst Rt) (emb R₀))
                (subTm σ t) (dsnd Rt)

-- ★★ W2 stage 3 — `⊢trU`, the TAUTOLOGICAL motive: transport along a
-- universe path IS application (directed univalence, semantically).
-- With J ⌜Hom⌝-MOTIVE-KEYED, a `tr` at the `var vz` motive whose path
-- is an `hrefl` is PERMANENTLY STUCK (`trstk?`'s var-motive clause), so
-- SpikeTrLR's obstruction — the J-branches' need for `t ≅ u` — has no
-- cases left.  The path's type `Hom U tI uI` can only interp as `⊩₁Π`
-- (every other clause dies on `hom-shape`, and the stuck-`Hom` clause
-- on `U-reduct` against `StkHd`); its membership is the app-closure
-- that discharges the one computing branch, taut itself.
fund {Ξ = Ξ} {σ = σ}
  (⊢trU {p = p₀} {e = e₀} {t = t₀} {u = u₀} dt du dp de) x₀ ρ =
  main (dfst (fund dp x₀ ρ)) (dsnd (fund dp x₀ ρ))
  where
  tI uI pI eI : RTm Ξ
  tI = subTm σ t₀
  uI = subTm σ u₀
  pI = subTm σ p₀
  eI = subTm σ e₀

  hUu : (⊩₁U doneᵀ) ⊩₁∋ uI
  hUu = projl (irrel₁ crflᵀ (dfst (fund du x₀ ρ)) (⊩₁U doneᵀ)) uI
              (dsnd (fund du x₀ ρ))

  R_result : ⊩₁ (El uI)
  R_result = emb (Σ.fst (projr hUu))

  R_e : ⊩₁ (El tI)
  R_e = dfst (fund de x₀ ρ)
  he  : R_e ⊩₁∋ eI
  he  = dsnd (fund de x₀ ρ)
  snE = CR1₁ R_e he

  -- every permanently stuck configuration, in one place: at a `var`
  -- motive, `trstk?` needs only the path to be rule-dead.
  nkey : {p' : RTm Ξ} → SNe p' → trstk? (var (vz {Ξ})) p' ≡ true
  nkey (sne-var x)        = refl
  nkey (sne-app n s)      = sne→spine n
  nkey (sne-fst n)        = sne→spine n
  nkey (sne-snd n)        = sne→spine n
  nkey (sne-hrefl _ _ kn) = kn
  nkey (sne-tr _ _ _ key) = key

  cr3 : {p' : RTm Ξ} → SN p' → trstk? (var (vz {Ξ})) p' ≡ true →
        Σ (⊩₁ (El uI)) (λ R → R ⊩₁∋ tr (var vz) p' eI)
  cr3 snp key =
    ( R_result
    , CR3₁ R_result (sne-tr (sn-ne (sne-var vz)) snp snE key) )

  piCase : {F : RTy Ξ} {G : RTy (Ξ ∙)} {t₁ u₁ : RTm Ξ}
           (q : Hom U tI uI ⟶ᵀ* Π F G)
           (⊩F : ⊩₁ F)
           (⊩G : (v : RTm Ξ) → ⊩F ⊩₁∋ v → ⊩₁ (subTy (single v) G)) →
           tI ⟶* t₁ → uI ⟶* u₁ →
           El t₁ ⟶ᵀ* F → El (renTm vs u₁) ⟶ᵀ* G →
           {p' : RTm Ξ} → SN p' → (⊩₁Π q ⊩F ⊩G) ⊩₁∋ p' →
           Σ (⊩₁ (El uI)) (λ R → R ⊩₁∋ tr (var vz) p' eI)
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-exp r snp') hp' =
    ( dfst z , exp₁ (dfst z) (snr-trᵖ r) (dsnd z) )
    where z = piCase q ⊩F ⊩G rt ru rEt rEu snp'
                     (mem-whred₁ (⊩₁Π q ⊩F ⊩G) r hp')
  piCase {u₁ = u₁} q ⊩F ⊩G rt ru rEt rEu {lam f} (sn-lam snf) hp' =
    ( R_result , exp₁ R_result snr-taut m-res )
    where
    he-F = projl (irrel₁ (red→≅ᵀ (⟶ᵀ*-trans (⟶ᵀ*-El rt) rEt)) R_e ⊩F)
                 eI he
    cG : El uI ≅ᵀ subTy (single eI) _
    cG = red→≅ᵀ
           (⟶ᵀ*-trans (⟶ᵀ*-El ru)
             (subst (λ z → El z ⟶ᵀ* _) (wk-cancel-tm eI u₁)
                    (⟶ᵀ*-sub (single eI) rEu)))
    m-res = projl (irrel₁ (csymᵀ cG) (⊩G eI he-F) R_result)
                  (app (lam f) eI) (projr hp' eI he-F)
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-ne n) hp'      = cr3 (sn-ne n) (nkey n)
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-pair sa sb) hp' = cr3 (sn-pair sa sb) refl
  piCase q ⊩F ⊩G rt ru rEt rEu sn-cb hp'           = cr3 sn-cb refl
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-cΠ h₁ h₂) hp'   = cr3 (sn-cΠ h₁ h₂) refl
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-cΣ h₁ h₂) hp'   = cr3 (sn-cΣ h₁ h₂) refl
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-cH h₁ h₂ h₃) hp' = cr3 (sn-cH h₁ h₂ h₃) refl

  main : (R : ⊩₁ (Hom U tI uI)) → R ⊩₁∋ pI →
         Σ (⊩₁ (El uI)) (λ R' → R' ⊩₁∋ tr (var vz) pI eI)
  main (⊩₁base q) hp with hom-shape q
  ... | ()
  main (⊩₁U q) hp with hom-shape q
  ... | ()
  main (⊩₁ne q n) hp with hom-shape q
  ... | ()
  main (⊩₁Σ q ⊩F ⊩G) hp with hom-shape q
  ... | ()
  main (⊩₁Hom q sh) hp with Hom-to-Hom q
  ... | mkHomRed rA rt ru with U-reduct rA
  ...   | refl with sh
  ...     | ()
  main (⊩₁Π q ⊩F ⊩G) hp with hom-to-Π q
  ... | via-Π rA with U-reduct rA
  ...   | ()
  main (⊩₁Π q ⊩F ⊩G) hp | via-U rA rt ru rEt rEu =
    piCase q ⊩F ⊩G rt ru rEt rEu (projl hp) hp

-- ★★ W2 stage 2 — `⊢tr` AT THE COMPOSITION MOTIVE: the semantic
-- validation the variance floor promised.  The motive's vz-freeness
-- (the inlined `posc-Hom` premises) makes every component
-- ENDPOINT-BLIND (`subTm-occ`), so the source- and target-types differ
-- only in the transported endpoint; the path analysis runs by induction
-- on the path's `SN` derivation — head steps expand
-- (`exp₁` ∘ `mem-whred₁`, the deterministic-strategy transfer), the
-- permanently stuck shapes are neutral (`sne-tr` + the classifier
-- extractors), and the J-branches hand the payload across the endpoint
-- switch with `homSem₀-mem-endpoints`.
fund {Ξ = Ξ} {σ = σ}
  (⊢tr {A = A} {c = c₀} {a = a₀} {p = p₀} {e = e₀} {t = t₀} {u = u₀}
       dc' da' dv hc ha dt du dp de) x₀ ρ =
  relTy (cong El (sym (sub-comm σ (⌜Hom⌝ c₀ a₀ (var vz)) u₀)))
        (go (CR1₁ (dfst (fund dp x₀ ρ)) (dsnd (fund dp x₀ ρ)))
            (dsnd (fund dp x₀ ρ)))
  where
  dI : RTm (Ξ ∙)
  dI = subTm (extS σ) (⌜Hom⌝ c₀ a₀ (var vz))
  tI uI pI eI : RTm Ξ
  tI = subTm σ t₀
  uI = subTm σ u₀
  pI = subTm σ p₀
  eI = subTm σ e₀

  Rt   = fund dt x₀ ρ
  R_A  = dfst Rt
  ht   = dsnd Rt
  hu   = projl (irrel₁ crflᵀ (dfst (fund du x₀ ρ)) R_A) uI
               (dsnd (fund du x₀ ρ))
  R_H  = dfst (fund dp x₀ ρ)
  Re'  = relTy (cong El (sub-comm σ (⌜Hom⌝ c₀ a₀ (var vz)) t₀))
               (fund de x₀ ρ)
  R_e  = dfst Re'
  he   = dsnd Re'
  snE  = CR1₁ R_e he

  -- `SN` of the substituted motive, componentwise via instantiation at
  -- a fresh variable (the `sem-⌜Π⌝` pattern)
  r₀    = CR3₁ R_A (sne-var x₀)
  bodyC = fund dc' x₀ (⊩ˢ-ext ρ R_A (var x₀) r₀)
  bodyA = fund da' x₀ (⊩ˢ-ext ρ R_A (var x₀) r₀)
  snD : SN dI
  snD = sn-cH
          (sn-body x₀ (subst SN (sym (sub-single-Tm σ (var x₀) c₀))
                             (CR1₁ (dfst bodyC) (dsnd bodyC))))
          (sn-body x₀ (subst SN (sym (sub-single-Tm σ (var x₀) a₀))
                             (CR1₁ (dfst bodyA) (dsnd bodyA))))
          (sn-ne (sne-var vz))

  -- the motive's components at the t-endpoint environment
  envT = ⊩ˢ-ext ρ R_A tI ht
  envU = ⊩ˢ-ext ρ R_A uI hu

  cT aT : RTm Ξ
  cT = subTm (σ ,ₛ tI) c₀
  aT = subTm (σ ,ₛ tI) a₀

  hcT = projl (irrel₁ crflᵀ (dfst (fund dc' x₀ envT)) (⊩₁U doneᵀ))
              cT (dsnd (fund dc' x₀ envT))
  Rc : ⊩₀ (El cT)
  Rc = sem-El doneᵀ hcT

  haT : Rc ⊩₀∋ aT
  haT = projr (emb-coh Rc) aT
              (projl (irrel₁ crflᵀ (dfst (fund da' x₀ envT)) (emb Rc))
                     aT (dsnd (fund da' x₀ envT)))

  htT : Rc ⊩₀∋ tI
  htT = projr (emb-coh Rc) tI
              (projl (irrel₁ crflᵀ (dfst (fund dv x₀ envT)) (emb Rc))
                     tI (dsnd (fund dv x₀ envT)))

  -- endpoint-blindness of the components (`subTm-occ` on the premises)
  agree-c : (x : Var (_ ∙)) → occTm x c₀ ≡ true → (σ ,ₛ uI) x ≡ (σ ,ₛ tI) x
  agree-c vz o with trans (sym o) hc
  ... | ()
  agree-c (vs y) o = refl

  agree-a : (x : Var (_ ∙)) → occTm x a₀ ≡ true → (σ ,ₛ uI) x ≡ (σ ,ₛ tI) x
  agree-a vz o with trans (sym o) ha
  ... | ()
  agree-a (vs y) o = refl

  eqc : subTm (σ ,ₛ uI) c₀ ≡ cT
  eqc = subTm-occ c₀ agree-c
  eqa : subTm (σ ,ₛ uI) a₀ ≡ aT
  eqa = subTm-occ a₀ agree-a

  huT : Rc ⊩₀∋ uI
  huT = projr (emb-coh Rc) uI
              (projl (irrel₁ crflᵀ
                        (dfst (relTy (cong El eqc) (fund dv x₀ envU)))
                        (emb Rc))
                     uI (dsnd (relTy (cong El eqc) (fund dv x₀ envU))))

  -- source and target decoded interps, and the payload's transfer
  eq-ct : subTm (single tI) (subTm (extS σ) c₀) ≡ cT
  eq-ct = sub-single-Tm σ tI c₀
  eq-at : subTm (single tI) (subTm (extS σ) a₀) ≡ aT
  eq-at = sub-single-Tm σ tI a₀
  eq-cu : subTm (single uI) (subTm (extS σ) c₀) ≡ cT
  eq-cu = trans (sub-single-Tm σ uI c₀) eqc
  eq-au : subTm (single uI) (subTm (extS σ) a₀) ≡ aT
  eq-au = trans (sub-single-Tm σ uI a₀) eqa

  eqSrc : El (⌜Hom⌝ cT aT tI) ≡ El (subTm (single tI) dI)
  eqSrc = cong El (sym (⌜Hom⌝-cong₃ eq-ct eq-at refl))
  eqTgt : El (⌜Hom⌝ cT aT uI) ≡ El (subTm (single uI) dI)
  eqTgt = cong El (sym (⌜Hom⌝-cong₃ eq-cu eq-au refl))

  srcBase = bwd₀ (stepᵀ (El-⌜Hom⌝ cT aT tI) doneᵀ) (homSem₀ Rc haT htT)
  tgtBase = bwd₀ (stepᵀ (El-⌜Hom⌝ cT aT uI) doneᵀ) (homSem₀ Rc haT huT)

  R₀t : ⊩₀ (El (subTm (single tI) dI))
  R₀t = ⊩₀cast eqSrc srcBase
  R₀u : ⊩₀ (El (subTm (single uI) dI))
  R₀u = ⊩₀cast eqTgt tgtBase

  R_result : ⊩₁ (El (subTm (single uI) dI))
  R_result = emb R₀u

  mem₀-castF : {X Y : RTy Ξ} (eq : X ≡ Y) (R : ⊩₀ X) {w : RTm Ξ} →
               R ⊩₀∋ w → (⊩₀cast eq R) ⊩₀∋ w
  mem₀-castF refl R h = h

  mem₀-castF⁻ : {X Y : RTy Ξ} (eq : X ≡ Y) (R : ⊩₀ X) {w : RTm Ξ} →
                (⊩₀cast eq R) ⊩₀∋ w → R ⊩₀∋ w
  mem₀-castF⁻ refl R h = h

  mem-bwd₀ : {X Y : RTy Ξ} (q : X ⟶ᵀ* Y) (R : ⊩₀ Y) {w : RTm Ξ} →
             R ⊩₀∋ w → (bwd₀ q R) ⊩₀∋ w
  mem-bwd₀ q (⊩₀base _)  h = h
  mem-bwd₀ q (⊩₀ne _ _)  h = h
  mem-bwd₀ q (⊩₀Π _ _ _) h = h
  mem-bwd₀ q (⊩₀Σ _ _ _) h = h
  mem-bwd₀ q (⊩₀Hom _ _) h = h

  mem-bwd₀⁻ : {X Y : RTy Ξ} (q : X ⟶ᵀ* Y) (R : ⊩₀ Y) {w : RTm Ξ} →
              (bwd₀ q R) ⊩₀∋ w → R ⊩₀∋ w
  mem-bwd₀⁻ q (⊩₀base _)  h = h
  mem-bwd₀⁻ q (⊩₀ne _ _)  h = h
  mem-bwd₀⁻ q (⊩₀Π _ _ _) h = h
  mem-bwd₀⁻ q (⊩₀Σ _ _ _) h = h
  mem-bwd₀⁻ q (⊩₀Hom _ _) h = h

  heTgt : R_result ⊩₁∋ eI
  heTgt =
    projl (emb-coh R₀u) eI
      (mem₀-castF eqTgt tgtBase
        (mem-bwd₀ (stepᵀ (El-⌜Hom⌝ cT aT uI) doneᵀ) (homSem₀ Rc haT huT)
          (homSem₀-mem-endpoints Rc haT htT haT huT
            (mem-bwd₀⁻ (stepᵀ (El-⌜Hom⌝ cT aT tI) doneᵀ) (homSem₀ Rc haT htT)
              (mem₀-castF⁻ eqSrc srcBase
                (projr (emb-coh R₀t) eI
                  (projl (irrel₁ crflᵀ R_e (emb R₀t)) eI he)))))))

  -- ★ the path analysis.
  cr3 : {p' : RTm Ξ} → SN p' → trstk? dI p' ≡ true →
        Σ (⊩₁ (El (subTm (single uI) dI)))
          (λ R → R ⊩₁∋ tr dI p' eI)
  cr3 snp key = ( R_result , CR3₁ R_result (sne-tr snD snp snE key) )

  go  : {p' : RTm Ξ} → SN p' → R_H ⊩₁∋ p' →
        Σ (⊩₁ (El (subTm (single uI) dI)))
          (λ R → R ⊩₁∋ tr dI p' eI)
  goh : {c' s' : RTm Ξ} → SN c' → SN s' → nopw? c' ≡ true →
        R_H ⊩₁∋ hrefl c' s' →
        Σ (⊩₁ (El (subTm (single uI) dI)))
          (λ R → R ⊩₁∋ tr dI (hrefl c' s') eI)

  go (sn-exp r snp') hp' =
    ( dfst z , exp₁ (dfst z) (snr-trᵖ r) (dsnd z) )
    where z = go snp' (mem-whred₁ R_H r hp')
  go (sn-ne (sne-var x)) hp'         = cr3 (sn-ne (sne-var x)) refl
  go (sn-ne (sne-app n s)) hp'       = cr3 (sn-ne (sne-app n s)) (sne→spine n)
  go (sn-ne (sne-fst n)) hp'         = cr3 (sn-ne (sne-fst n)) (sne→spine n)
  go (sn-ne (sne-snd n)) hp'         = cr3 (sn-ne (sne-snd n)) (sne→spine n)
  go (sn-ne (sne-hrefl snc sns kn)) hp' = goh snc sns kn hp'
  go (sn-ne (sne-tr h₁ h₂ h₃ key)) hp' =
    cr3 (sn-ne (sne-tr h₁ h₂ h₃ key)) key
  go (sn-lam snf) hp'      = cr3 (sn-lam snf) refl
  go (sn-pair sa sb) hp'   = cr3 (sn-pair sa sb) refl
  go sn-cb hp'             = cr3 sn-cb refl
  go (sn-cΠ h₁ h₂) hp'     = cr3 (sn-cΠ h₁ h₂) refl
  go (sn-cΣ h₁ h₂) hp'     = cr3 (sn-cΣ h₁ h₂) refl
  go (sn-cH h₁ h₂ h₃) hp'  = cr3 (sn-cH h₁ h₂ h₃) refl

  -- the path's own head star, wrapped into the tr.
  trP-star : {p₁ p₂ : RTm Ξ} → p₁ ⟶snr* p₂ →
             tr dI p₁ eI ⟶snr* tr dI p₂ eI
  trP-star snr-done       = snr-done
  trP-star (snr-step r q) = snr-step (snr-trᵖ r) (trP-star q)

  goh sn-cb sns kn hp' =
    ( R_result , exp₁ R_result (snr-J-base snD sns) heTgt )
  goh (sn-cΣ h₁ h₂) sns kn hp' =
    ( R_result , exp₁ R_result (snr-J-Σ snD h₁ h₂ sns) heTgt )
  goh (sn-exp rc snc') sns kn hp' =
    ( dfst z , exp₁ (dfst z) (snr-trᵖ (snr-hreflᶜ (csr-here rc))) (dsnd z) )
    where z = goh snc' sns (nopw?-red (snr→⟶ rc) kn)
                  (mem-whred₁ R_H (snr-hreflᶜ (csr-here rc)) hp')
  goh (sn-ne nc) sns kn hp' =
    cr3 (sn-ne (sne-hrefl (sn-ne nc) sns (sne→nopw nc))) (sne→stablecd nc)
  goh (sn-lam snb) sns kn hp' =
    cr3 (sn-ne (sne-hrefl (sn-lam snb) sns refl)) refl
  goh (sn-pair sa sb) sns kn hp' =
    cr3 (sn-ne (sne-hrefl (sn-pair sa sb) sns refl)) refl
  goh (sn-cΠ h₁ h₂) sns () hp'
  -- ★ W2b: a ⌜Hom⌝-CODE path — normalize its spine (codeNorm); the
  -- J-able leaf fires tr-J-Hom (endpoint transfer = the SAME heTgt as
  -- J-base), the dead leaf is CR3; both memberships travel back along
  -- the head star.
  goh (sn-cH {c = C₂} {a = a₂} {b = b₂} h₁ h₂ h₃) sns kn hp'
    with codeNorm h₁ kn
  ... | C* , (csr , cf-stk k) =
        ( R_result
        , expStar₁ R_result
            (trP-star (snrs-hreflᶜ (csrs-hom csr)))
            (exp₁ R_result
              (snr-J-Hom snD (sn-csrs h₁ csr) h₂ h₃ sns k) heTgt) )
  ... | C* , (csr , cf-dead k) =
        ( R_result
        , expStar₁ R_result
            (trP-star (snrs-hreflᶜ (csrs-hom csr)))
            (CR3₁ R_result
              (sne-tr snD
                (sn-ne (sne-hrefl (sn-cH (sn-csrs h₁ csr) h₂ h₃) sns
                                  (nopw?-csrs csr kn)))
                snE k)) )

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
