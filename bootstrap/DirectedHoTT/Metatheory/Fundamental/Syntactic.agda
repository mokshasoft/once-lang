------------------------------------------------------------------------
-- OCP-0009 · W1h — `fund`, PART 1: THE SYNTACTIC PLUMBING.
--
-- Split out of NbEPDirDBFund for COMPILE TIME, not for meaning: this
-- part is the substitution calculus and the SN/SNRed/CSR
-- anti-renaming + renaming stability lemmas.  It mentions no logical
-- relation at all, and it changes about once a stage — so editing
-- `fund` should not re-check it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Fundamental.Syntactic where
open import DirectedHoTT.Metatheory.RedCong
  using ( ren-comm2; ren-comm; ren-comm-ext; pwShift-ren )
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_; ⊥; ⊥-elim )

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom; Id; Hom-cong₃
        ; Id-cong₃; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃; ⌜Id⌝-cong₃; jsub-cong₃
        ; RTm; var; lam; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; ⌜Hom⌝; hrefl; tr; ap; ⌜Id⌝; idrefl; jsub; Unit; Nat; unit; nzero
        ; nsuc; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝; ordtr-cong₅; Ren; extR
        ; renTy; renTm; Sub; subTy; subTm; extS; idₛ; _∘ᵣ_; subTy-cong
        ; subTm-cong; subTy-renTy; subTm-renTm; renTy-subTy; renTm-subTm
        ; subTy-subTy; subTm-subTm; subTy-id; subTm-id; renTm-renTm
        ; renTm-cong; Desc; con; IMu; ielim; ⌜IMu⌝; εwkTm; cong₃; DIh; Fin
        ; ⌜Fin⌝; dι; dσ; dρ; dpay; dih; fzero; fsuc; fcase; fcase0; psplit
        ; cong₄ )
open import DirectedHoTT.Spec.Typing
  using ( single; nrs; _⟶_; _⟶*_; done; step; β; βfst; βsnd; ξ-lam; ξ-appˡ
        ; ξ-appʳ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ordtr-z; ordtr-szz
        ; ordtr-ssz; ordtr-szs; ordtr-sss; ξ-ordtrᵃ; ξ-ordtrᵗ; ξ-ordtrᵘ
        ; ξ-ordtrᵖ; ξ-ordtrq; ξ-fst; ξ-snd; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; hrefl-pw
        ; tr-J-base; tr-J-Σ; tr-J-Hom; tr-taut; tr-pw; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ
        ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ; ξ-Σˡ; ξ-Σʳ; _≅_; _≅ᵀ_; crflᵀ; csymᵀ
        ; ctrnᵀ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_; here; there; _⊢_∷_; ⊢var; ⊢lam; ⊢app
        ; ⊢pair; ⊢fst; ⊢snd; ⊢absurd; El-⌜Hom⌝; ξ-El; El-⌜Π⌝; _⟶ᵀ_; El-⌜base⌝
        ; El-⌜Σ⌝; El-⌜Id⌝; El-⌜Nat⌝; El-⌜Unit⌝; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ; Hom-U
        ; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢trU; ⊢ap; ⊢conv; ⊢⌜Nat⌝
        ; ⊢⌜Unit⌝; ⊢⌜Id⌝; ⊢idrefl; ⊢jsub; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ
        ; ty-El; ty-Hom; ty-Id; ty-Unit; ty-Nat; ⊢unit; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢ctx_; c-◇; c-▹; ⊢id; ⊢appex; single2 )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; occTm; subTm-occ; pw?; stkC?; stkA?; pwBody; pwDom
        ; pwShift; pw?-ren; stkC?-ren; stkA?-ren; pwBody-ren; wk-ren-tm
        ; pw?-sub; stkC?→stkA?; wk-sub-tm; stk⊥pw; pw⊥stk; flat?; flat→stk
        ; flat?-sub; eqv; occ-sub; occ-ren-tm; avoids-wk; ren-as-sub )
open import DirectedHoTT.Metatheory.SubjectReductionBase
  using ( ≅ᵀ-sub; sub-comm; wk-sub )
open import DirectedHoTT.Metatheory.Confluence
  using ( )
open import DirectedHoTT.Algorithm.DecideConversion
  using ( dec-conv )
open import DirectedHoTT.Metatheory.Injectivity
  using ( confluentᵀ; church-rosserᵀ; Π-inj; Π-reduct; Σ-reduct; mkΠRed
        ; mkΣRed; Id-reduct )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( HomΠShape; hsΠ; hsH; hom-shape; hom-shapeN; nn-U; NoNat
        ; pw-El-decode; HomRed; mkHomRed; Hom-to-Hom; homAmb→; HomToΠ; via-U
        ; via-Π; hom-to-Π; U-reduct; ≅ᵀ-Homᵀ; gen-var )
open import DirectedHoTT.Metatheory.LogicalRelation
  using ( SNe; sne-var; sne-app; sne-absurd; sne-fst; sne-snd; sne-hrefl
        ; sne-tr; sne-ap; sne-jsub; Ne; ne-var; ne-app; ne-absurd; ne-fst
        ; ne-snd; ne-hrefl; ne-tr; ne-ap; ne-jsub; homSem₁; SN; sn-ne; sn-lam
        ; sn-pair; sn-cb; sn-cΠ; sn-cΣ; sn-cH; sn-cId; sn-idrefl; sn-exp
        ; sn-cNat; sn-cUnit; sn-cIMu; snr-J-IMu; sne-ielim; snr-ielimᵗ; SNRed
        ; snr-β; snr-βfst; snr-βsnd; snr-app; snr-fst; snr-snd; snr-hreflᶜ
        ; snr-J-base; snr-J-Σ; snr-J-Id; snr-J-Unit; snr-taut; snr-trᵖ
        ; snr-ap-J; snr-apᵖ; snr-jsub-refl; snr-jsubᵖ; snr-natrec-zero
        ; snr-natrec-suc; snr-natrecⁿ; sne-natrec; ne-natrec; sn-unit
        ; sn-nzero; sn-nsuc; sne-ordtr; ne-ordtr; ordstk?; ordstk?-ren
        ; ordstk?-redᵃ; ordstk?-redᵗ; ordstk?-redᵘ; snr-ordtr-z; snr-ordtr-szz
        ; snr-ordtr-ssz; snr-ordtr-szs; snr-ordtr-sss; snr-ordtrᵃ; snr-ordtrᵗ
        ; snr-ordtrᵘᶻ; snr-ordtrᵘˢ; NatMem; nm-ne; nm-zero; nm-suc; nm-exp
        ; natmem-whred; ⊩₁Unit; ⊩₁Nat; natstk?-ren; natstk?-red; sne→natstk
        ; sn-whred; homNatSem; homNatSem₀; hns₀-in; bwd₀-mem⁻; StkHd; sh-Hom
        ; sh-NatH; homnat?; trstk?-ren; apstk?-ren; idstk?-ren; nopw?-ren
        ; trlam?-ren; idstk?-red; ⊩₀Id; ⊩₁Id; IdPay; idpay-transfer
        ; idpay-peel; sne-nopay; nopw⊥pw; stk⊥dead; pw⊥dead; dead→nopw
        ; snr-nonpw; snr-hrefl-pw; snr-J-Hom; snr-tr-pw; snr-tr-mot
        ; deadmot?-red; deadmot?-ren; deadmot→nopw; stk→deadmot; nopw?-red
        ; nopw?-red*; CSR; csr-here; csr-hom; csr→⟶; csr-nonpw; csr-stk⊥
        ; sn-csr; csr-det; _⟶csr*_; csr-done; csr-step; csrs-hom; PayT
        ; payChain; payT-exp; payT-whred; payT-irrel; payT-cast; payT-code
        ; payHomT; _⟶snr*_; snr-done; snr-step; ⊩₀_; ⊩₀base; ⊩₀ne; ⊩₀Π; ⊩₀Σ
        ; ⊩₀Hom; _⊩₀∋_; bwd₀; exp₁; ⊩₀Unit; ⊩₀Nat; base-nf; Unit-nf; Nat-nf
        ; El-ne-reduct; mkElNe; Hom-stk-reduct; mkHomStk; trlam?; sne→spine
        ; snr→⟶; exp₀; f≢t; mem-whred₁; homSem₀; homSem₀-mem-endpoints
        ; sne→stablecd; sne→stableA; trstk?; ⊩₁_; ⊩₁base; ⊩₁U; ⊩₁ne; ⊩₁Π; ⊩₁Σ
        ; ⊩₁Hom; _⊩₁∋_; bwd₁; irrel₁; conv₁; CR1₀; CR1₁; CR3₀; CR3₁; emb
        ; emb-coh; sem-conv; sem-lam; sem-app; sem-fst; sem-snd; sem-pair
        ; sem-El; sem-⌜base⌝; sem-⌜Π⌝; sem-⌜Σ⌝; sem-⌜Hom⌝; sem-hrefl; ⟶ᵀ*-sub
        ; IsNormal; WN; mkWN; wn; projl; projr; dfst; dsnd; sn-con; snr-ι
        ; mustk?; mustk?-ren; dstk?-ren; sne-fcase; snr-dpay-ρ; snr-psplit-β
        ; snr-dpay-σ; snr-fcase-s; sne-dih; finstk?-ren; sne-dpay; sn-cFin
        ; sn-dι; sn-dρ; sn-dσ; sn-fsuc; sn-fzero; sne-fcase0; sne-psplit
        ; snr-J-Fin; snr-dih-ι; snr-dih-ρ; snr-dih-σ; snr-dihᶜ; snr-dpay-ι
        ; snr-dpayᶜ; snr-fcase-z; snr-fcaseᵗ; snr-psplitᵍ )


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

exts2-var : (ρ : Ren Θ Ξ) (x : Var ((Θ ∙) ∙)) →
            extS (extS ⟨ ρ ⟩ᵣ) x ≡ ⟨ extR (extR ρ) ⟩ᵣ x
exts2-var ρ vz          = refl
exts2-var ρ (vs vz)     = refl
exts2-var ρ (vs (vs x)) = refl

-- (1a) substituting a renaming IS renaming.
subTy-var : (ρ : Ren Θ Ξ) (A : RTy Θ) → subTy ⟨ ρ ⟩ᵣ A ≡ renTy ρ A
subTm-var : (ρ : Ren Θ Ξ) (t : RTm Θ) → subTm ⟨ ρ ⟩ᵣ t ≡ renTm ρ t
subTy-var ρ base     = refl
subTy-var ρ Unit     = refl
subTy-var ρ Nat      = refl
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
subTy-var ρ (IMu I D i) = cong₃ IMu (subTm-var ρ I) (subTm-var ρ D) (subTm-var ρ i)
subTy-var ρ (Desc I) = cong Desc (subTm-var ρ I)
subTy-var ρ (DIh D M C p) =
  cong₄ DIh (subTm-var ρ D)
            (trans (subTy-cong (exts2-var ρ) M) (subTy-var (extR (extR ρ)) M))
            (subTm-var ρ C) (subTm-var ρ p)
subTy-var ρ (Fin n) = refl
subTy-var ρ (Id A t u) =
  Id-cong₃ (subTy-var ρ A) (subTm-var ρ t) (subTm-var ρ u)
-- ★ the TERM half is `Spec/Variance`'s generated `ren-as-sub` (⟨ ρ ⟩ᵣ is
--   `var ∘ ρ` on the nose) — one statement, not a second enumeration.
subTm-var ρ t = sym (ren-as-sub ρ t)

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

-- ★ WF stage A.  Instantiating the recursor's STEP motive at the number
-- then at the IH is the motive at the SUCCESSOR — the semantic twin of
-- `natrec-step-ty`, phrased on the cons-substitutions `fund` builds.
nrs-cons-Ty : (σ : Sub Θ Ξ) (m r : RTm Ξ) (M : RTy (Θ ∙)) →
              subTy ((σ ,ₛ m) ,ₛ r) (subTy nrs M) ≡ subTy (σ ,ₛ nsuc m) M
nrs-cons-Ty {Θ} σ m r M = trans (subTy-subTy M) (subTy-cong bridge M)
  where
  bridge : (x : Var (Θ ∙)) →
           subTm ((σ ,ₛ m) ,ₛ r) (nrs x) ≡ (σ ,ₛ nsuc m) x
  bridge vz     = refl
  bridge (vs y) = refl

-- …and the same on the step TERM: the two nested single-substitutions
-- the reduction performs ARE the cons-substitution `fund` recurses with.
nrs-cons-Tm : (σ : Sub Θ Ξ) (m r : RTm Ξ) (w : RTm ((Θ ∙) ∙)) →
              subTm (single r) (subTm (extS (single m)) (subTm (extS (extS σ)) w))
              ≡ subTm ((σ ,ₛ m) ,ₛ r) w
nrs-cons-Tm {Θ} σ m r w =
  trans (cong (subTm (single r)) inner)
        (sub-single-Tm (σ ,ₛ m) r w)
  where
  inner : subTm (extS (single m)) (subTm (extS (extS σ)) w)
          ≡ subTm (extS (σ ,ₛ m)) w
  inner = trans (subTm-subTm w) (subTm-cong bridge w)
    where
    bridge : (x : Var ((Θ ∙) ∙)) →
             subTm (extS (single m)) (extS (extS σ) x) ≡ extS (σ ,ₛ m) x
    bridge vz     = refl
    bridge (vs y) =
      trans (wk-sub (single m) (extS σ y))
            (cong (renTm vs) (single-exts σ m y))
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
sne-anti {ρ = ρ} {t = natrec z w n} (sne-natrec hz hw hn key) =
  sne-natrec (sn-anti hz) (sn-anti hw) (sn-anti hn)
             (trans (sym (natstk?-ren ρ n)) key)
-- ★ INDUCTIVE TYPES: one classifier, so the key transports through
-- `mustk?-ren` — `sne-natrec`'s shape exactly.
-- ⚠ the INDEXED twin takes ONE MORE `SN`: `ielim` carries the index and
--   `ξ-ielimⁱ` steps it, so `sne-ielim` has a fourth premise.  The key is
--   still about the SCRUTINEE alone, so it rides the same `mustk?-ren`.
sne-anti {t = app t u}  (sne-app n s) = sne-app (sne-anti n) (sn-anti s)
sne-anti {t = absurd c e} (sne-absurd sc sn₀) = sne-absurd (sn-anti sc) (sn-anti sn₀)
-- ★★ WF stage E: three bounds, so the key transports through
-- `ordstk?-ren` rather than a single classifier.
sne-anti {ρ = ρ} {t = ordtr a t u p q} (sne-ordtr ha ht hu hp hq key) =
  sne-ordtr (sn-anti ha) (sn-anti ht) (sn-anti hu) (sn-anti hp) (sn-anti hq)
            (trans (sym (ordstk?-ren ρ a t u)) key)
sne-anti {t = fst p}    (sne-fst n)   = sne-fst (sne-anti n)
sne-anti {t = snd p}    (sne-snd n)   = sne-snd (sne-anti n)
sne-anti {ρ = ρ} {t = hrefl c t} (sne-hrefl hc ht kn) =
  sne-hrefl (sn-anti hc) (sn-anti ht) (trans (sym (nopw?-ren ρ c)) kn)
sne-anti {ρ = ρ} {t = tr d p e} (sne-tr hd hp he key) =
  sne-tr (sn-anti hd) (sn-anti hp) (sn-anti he)
         (trans (sym (trstk?-ren ρ d p)) key)
sne-anti {ρ = ρ} {t = ap c b p} (sne-ap hc hb hp key) =
  sne-ap (sn-anti hc) (sn-anti hb) (sn-anti hp)
         (trans (sym (apstk?-ren ρ p)) key)
sne-anti {ρ = ρ} {t = jsub d p e} (sne-jsub hd hp he key) =
  sne-jsub (sn-anti hd) (sn-anti hp) (sn-anti he)
           (trans (sym (idstk?-ren ρ p)) key)
-- ★★ LEVITATED FAMILIES: each key transports through its classifier's
--   `-ren`, `sne-natrec`'s shape; `psplit`'s neutral pair recurses.
sne-anti {ρ = ρ} {t = ielim D i e t₀} (sne-ielim hD hi he ht key) =
  sne-ielim (sn-anti hD) (sn-anti hi) (sn-anti he) (sn-anti ht)
            (trans (sym (mustk?-ren ρ t₀)) key)
sne-anti {ρ = ρ} {t = dpay I D C} (sne-dpay hI hD hC key) =
  sne-dpay (sn-anti hI) (sn-anti hD) (sn-anti hC)
           (trans (sym (dstk?-ren ρ C)) key)
sne-anti {ρ = ρ} {t = dih D e C p} (sne-dih hD he hC hp key) =
  sne-dih (sn-anti hD) (sn-anti he) (sn-anti hC) (sn-anti hp)
          (trans (sym (dstk?-ren ρ C)) key)
sne-anti {ρ = ρ} {t = fcase t₀ a b} (sne-fcase ht ha hb key) =
  sne-fcase (sn-anti ht) (sn-anti ha) (sn-anti hb)
            (trans (sym (finstk?-ren ρ t₀)) key)
sne-anti {t = fcase0 t₀} (sne-fcase0 ht) = sne-fcase0 (sn-anti ht)
sne-anti {t = psplit b q} (sne-psplit hb n) = sne-psplit (sn-anti hb) (sne-anti n)

sn-anti {t = var x}    _              = sn-ne (sne-var x)
sn-anti {t = unit}     _              = sn-unit
sn-anti {t = nzero}    _              = sn-nzero
sn-anti {t = nsuc n}   (sn-nsuc h)    = sn-nsuc (sn-anti h)
sn-anti {t = natrec z w n} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = natrec z w n} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = ielim D i ms t₀} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = ielim D i ms t₀} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = lam s}    (sn-lam h)     = sn-lam (sn-anti h)
sn-anti {t = pair a b} (sn-pair ha hb) = sn-pair (sn-anti ha) (sn-anti hb)
sn-anti {t = ⌜base⌝}   _              = sn-cb
sn-anti {t = ⌜Nat⌝}    _              = sn-cNat
sn-anti {t = ⌜Unit⌝}   _              = sn-cUnit
-- ⚠ NOT nullary like `⌜Mu⌝`: `⌜IMu⌝` carries the index, so its `SN` has a
--   premise and anti-renaming has to recurse into it.
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
sn-anti {t = ap c b p}  (sn-ne n)     = sn-ne (sne-anti n)
sn-anti {t = ap c b p}  (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = ⌜Id⌝ c a b} (sn-cId hc ha hb) =
  sn-cId (sn-anti hc) (sn-anti ha) (sn-anti hb)
sn-anti {t = idrefl c t} (sn-idrefl hc ht) =
  sn-idrefl (sn-anti hc) (sn-anti ht)
sn-anti {t = jsub d p e}  (sn-ne n)     = sn-ne (sne-anti n)
sn-anti {t = jsub d p e}  (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = app t u}  (sn-ne n)      = sn-ne (sne-anti n)
sn-anti {t = absurd c e} (sn-ne n)     = sn-ne (sne-anti n)
sn-anti {t = ordtr a t u p q} (sn-ne n) = sn-ne (sne-anti n)
sn-anti {t = ordtr a t u p q} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = fst p}    (sn-ne n)      = sn-ne (sne-anti n)
sn-anti {t = snd p}    (sn-ne n)      = sn-ne (sne-anti n)
sn-anti {t = app t u}  (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
-- ★ ex falso never head-reduces — it is a permanent neutral — so the
-- head-expansion case is vacuous.
sn-anti {t = absurd c e} (sn-exp () h)
sn-anti {t = fst p}    (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = snd p}    (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
-- ★★ LEVITATED FAMILIES: the constructors and codes recurse into their
--   parts; the eliminators are `natrec`'s two rows (neutral / expansion),
--   except `fcase0`, which never steps (`absurd`'s shape).
sn-anti {t = ⌜IMu⌝ I D i} (sn-cIMu hI hD hi) = sn-cIMu (sn-anti hI) (sn-anti hD) (sn-anti hi)
sn-anti {t = ⌜Fin⌝ n}  _               = sn-cFin
sn-anti {t = con q}    (sn-con h)      = sn-con (sn-anti h)
sn-anti {t = dι}       _               = sn-dι
sn-anti {t = dσ S f}   (sn-dσ h₁ h₂)   = sn-dσ (sn-anti h₁) (sn-anti h₂)
sn-anti {t = dρ j C}   (sn-dρ h₁ h₂)   = sn-dρ (sn-anti h₁) (sn-anti h₂)
sn-anti {t = fzero}    _               = sn-fzero
sn-anti {t = fsuc t₀}  (sn-fsuc h)     = sn-fsuc (sn-anti h)
sn-anti {t = dpay I D C} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = dpay I D C} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = dih D e C p} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = dih D e C p} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = fcase t₀ a b} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = fcase t₀ a b} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = fcase0 t₀} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = fcase0 t₀} (sn-exp () h)
sn-anti {t = psplit b q} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = psplit b q} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)

snr-anti {t = natrec z w nzero} (snr-natrec-zero hw) =
  z , (snr-natrec-zero (sn-anti hw) , refl)
snr-anti {ρ = ρ} {t = natrec z w (nsuc m)} (snr-natrec-suc hz hw hn) =
  subTm (single (natrec z w m)) (subTm (extS (single m)) w)
  , ( snr-natrec-suc (sn-anti hz) (sn-anti hw) (sn-anti hn)
    , sym (trans (ren-comm ρ (subTm (extS (single m)) w) (natrec z w m))
                 (cong (λ q → subTm (single (natrec (renTm ρ z)
                                                    (renTm (extR (extR ρ)) w)
                                                    (renTm ρ m))) q)
                       (ren-comm-ext ρ w m))) )
snr-anti {t = natrec z w n} (snr-natrecⁿ r) with snr-anti r
... | n' , (r' , refl) = natrec z w n' , (snr-natrecⁿ r' , refl)
-- ★ INDUCTIVE TYPES: the scrutinee is matched SHAPED (`con k q`) for the
-- reason the comment below gives — otherwise `renTm ρ (con k q)` does not
-- reduce and the index unification sticks.  The equation is `ren-fields`
-- composed with `ren-sel`, the same pair `⟶-ren` needed.
-- ★ the INDEXED ι.  Same shape, one extra `SN` premise, and the equation
--   is `ren-ifieldsⁱ` — the specialised form that already folds in
--   `isingle-ren`, so the environment lands as `isingle (renTm ρ i)`.
snr-anti {t = ielim D i ms t₀} (snr-ielimᵗ r) with snr-anti r
... | t' , (r' , refl) = ielim D i ms t' , (snr-ielimᵗ r' , refl)
-- ★★ WF stage E: the bounds must be matched SHAPED, or `renTm ρ a` does
-- not reduce and the index unification gets stuck (the `snr-βfst`
-- SplitError is the same disease).  The serialized xi's each carry the
-- shape their premise already fixed.
snr-anti {t = ordtr nzero t u p q} (snr-ordtr-z ht hu hp hq) =
  unit , (snr-ordtr-z (sn-anti ht) (sn-anti hu) (sn-anti hp) (sn-anti hq) , refl)
snr-anti {t = ordtr (nsuc a) nzero nzero p q} (snr-ordtr-szz ha hq) =
  p , (snr-ordtr-szz (sn-anti ha) (sn-anti hq) , refl)
snr-anti {t = ordtr (nsuc a) (nsuc t) nzero p q} (snr-ordtr-ssz ha ht hp) =
  q , (snr-ordtr-ssz (sn-anti ha) (sn-anti ht) (sn-anti hp) , refl)
snr-anti {t = ordtr (nsuc a) nzero (nsuc u) p q} (snr-ordtr-szs hq) =
  absurd (⌜Hom⌝ ⌜Nat⌝ a u) p , (snr-ordtr-szs (sn-anti hq) , refl)
snr-anti {t = ordtr (nsuc a) (nsuc t) (nsuc u) p q} snr-ordtr-sss =
  ordtr a t u p q , (snr-ordtr-sss , refl)
snr-anti {t = ordtr a t u p q} (snr-ordtrᵃ r) with snr-anti r
... | a' , (r' , refl) = ordtr a' t u p q , (snr-ordtrᵃ r' , refl)
snr-anti {t = ordtr (nsuc a) t u p q} (snr-ordtrᵗ r) with snr-anti r
... | t' , (r' , refl) = ordtr (nsuc a) t' u p q , (snr-ordtrᵗ r' , refl)
snr-anti {t = ordtr (nsuc a) nzero u p q} (snr-ordtrᵘᶻ r) with snr-anti r
... | u' , (r' , refl) = ordtr (nsuc a) nzero u' p q , (snr-ordtrᵘᶻ r' , refl)
snr-anti {t = ordtr (nsuc a) (nsuc t) u p q} (snr-ordtrᵘˢ r) with snr-anti r
... | u' , (r' , refl) = ordtr (nsuc a) (nsuc t) u' p q , (snr-ordtrᵘˢ r' , refl)
snr-anti {ρ = ρ} {t = app (lam s) u} (snr-β h) =
  subTm (single u) s , (snr-β (sn-anti h) , ren-single ρ u s)
snr-anti {t = app (app a b) u}  (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (fst p) u}    (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (snd p) u}    (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app unit u}       (snr-app ())
snr-anti {t = app nzero u}      (snr-app ())
snr-anti {t = app (nsuc k) u}   (snr-app ())
snr-anti {t = app (con _) u}   (snr-app ())
snr-anti {t = app dι u}   (snr-app ())
snr-anti {t = app (dσ _ _) u}   (snr-app ())
snr-anti {t = app (dρ _ _) u}   (snr-app ())
snr-anti {t = app fzero u}   (snr-app ())
snr-anti {t = app (fsuc _) u}   (snr-app ())
snr-anti {t = app (fcase0 _) u}   (snr-app ())
snr-anti {t = app (⌜Fin⌝ _) u}   (snr-app ())
snr-anti {t = app (natrec z w n) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (dpay _ _ _) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (dih _ _ _ _) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (fcase _ _ _) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (psplit _ _) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
-- ★ INDUCTIVE TYPES: in a SPINE position a `con` head is inert (no SNRed
-- rule steps it) and an `elim` head recurses — `nsuc`/`natrec` exactly.
snr-anti {t = app (ielim D i ms t₀) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = absurd c e} ()
-- ex falso is a permanent neutral, so as a SCRUTINEE it never lets an
-- eliminator fire — every one of these is `()` on the inner step.
snr-anti {t = fst (absurd c e)}     (snr-fst ())
snr-anti {t = snd (absurd c e)}     (snr-snd ())
snr-anti {t = app (absurd c e) u}   (snr-app ())
-- ⚠ NOT the `absurd` shape: ex falso never steps, so its rows are `()`,
-- whereas an `ordtr` SCRUTINEE does step and each row must recurse —
-- the `natrec` shape.
snr-anti {t = fst (ordtr a t u p q)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = snd (ordtr a t u p q)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = app (ordtr a t u p q) w} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' w , (snr-app r' , refl)
snr-anti {t = fst unit}         (snr-fst ())
snr-anti {t = fst nzero}        (snr-fst ())
snr-anti {t = fst (nsuc k)}     (snr-fst ())
snr-anti {t = fst (con _)}     (snr-fst ())
snr-anti {t = fst dι}     (snr-fst ())
snr-anti {t = fst (dσ _ _)}     (snr-fst ())
snr-anti {t = fst (dρ _ _)}     (snr-fst ())
snr-anti {t = fst fzero}     (snr-fst ())
snr-anti {t = fst (fsuc _)}     (snr-fst ())
snr-anti {t = fst (fcase0 _)}     (snr-fst ())
snr-anti {t = fst (⌜Fin⌝ _)}     (snr-fst ())
snr-anti {t = fst (natrec z w n)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = fst (dpay _ _ _)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = fst (dih _ _ _ _)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = fst (fcase _ _ _)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = fst (psplit _ _)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = snd unit}         (snr-snd ())
snr-anti {t = snd nzero}        (snr-snd ())
snr-anti {t = snd (nsuc k)}     (snr-snd ())
snr-anti {t = snd (con _)}     (snr-snd ())
snr-anti {t = snd dι}     (snr-snd ())
snr-anti {t = snd (dσ _ _)}     (snr-snd ())
snr-anti {t = snd (dρ _ _)}     (snr-snd ())
snr-anti {t = snd fzero}     (snr-snd ())
snr-anti {t = snd (fsuc _)}     (snr-snd ())
snr-anti {t = snd (fcase0 _)}     (snr-snd ())
snr-anti {t = snd (⌜Fin⌝ _)}     (snr-snd ())
snr-anti {t = snd (natrec z w n)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (dpay _ _ _)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (dih _ _ _ _)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (fcase _ _ _)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (psplit _ _)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (ielim D i ms t₀)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = fst (ielim D i ms t₀)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
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
snr-anti {t = tr (⌜Hom⌝ c a m) (hrefl ⌜Unit⌝ s) e} (snr-J-Unit hd hs) =
  e , (snr-J-Unit (sn-anti hd) (sn-anti hs) , refl)
snr-anti {t = tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ Dⁱ Iⁱ iˣ) s) e} (snr-J-IMu hd hs) =
  e , (snr-J-IMu (sn-anti hd) (sn-anti hs) , refl)
snr-anti {t = tr d (hrefl ⌜Unit⌝ s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl ⌜Unit⌝ s) e} (snr-trᵖ (snr-hrefl-pw ()))
-- ⌜Nat⌝ has NO J root — a `hrefl ⌜Nat⌝` path is neutral — so the only
-- shapes here are the (absurd) code reductions.
-- an `absurd` path CODE is neither `pw?` nor `stkC?`, and it has no
-- spine step of its own.
snr-anti {t = tr d (hrefl (absurd c₉ e₉) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (absurd c₉ e₉) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl ⌜Nat⌝ s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl ⌜Nat⌝ s) e} (snr-trᵖ (snr-hrefl-pw ()))
-- a bare datatype CODE as a path is permanently stuck: no root fires.
snr-anti {t = tr (⌜Hom⌝ c a m) (absurd c₉ e₉) e} (snr-trᵖ ())
snr-anti {t = tr (⌜Hom⌝ c a m) ⌜Nat⌝ e} (snr-trᵖ ())
snr-anti {t = tr (⌜Hom⌝ c a m) ⌜Unit⌝ e} (snr-trᵖ ())
snr-anti {t = tr (⌜Hom⌝ c a m) (hrefl (⌜Σ⌝ c₁ c₂) s) e} (snr-J-Σ hd h₁ h₂ hs) =
  e , (snr-J-Σ (sn-anti hd) (sn-anti h₁) (sn-anti h₂) (sn-anti hs) , refl)
snr-anti {t = tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (⌜Σ⌝ c₁ c₂) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr (var vz) (lam f) e} snr-taut =
  app (lam f) e , (snr-taut , refl)
snr-anti {ρ = ρ} {t = tr (⌜Hom⌝ c a m) (hrefl (⌜Hom⌝ c₁ a₁ b₁) s) e}
         (snr-J-Hom hd h₁ h₂ h₃ hs kh) =
  e , ( snr-J-Hom (sn-anti hd) (sn-anti h₁) (sn-anti h₂) (sn-anti h₃)
                  (sn-anti hs) (trans (sym (stkA?-ren ρ c₁)) kh)
      , refl )
snr-anti {ρ = ρ} {t = tr (⌜Hom⌝ c a (var vz)) (lam f) e}
         (snr-tr-mot σ) with csr-anti σ
... | c' , (σ' , refl) =
      tr (⌜Hom⌝ c' a (var vz)) (lam f) e , (snr-tr-mot σ' , refl)
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
snr-anti {t = tr d (hrefl (ap g w v) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (ordtr a₉ t₉ u₉ p₉ q₉) s) e} (snr-trᵖ r) with snr-anti r
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
snr-anti {t = tr d (ap g w v) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d ⌜base⌝ e} (snr-trᵖ ())
snr-anti {t = tr d (⌜Π⌝ g w) e} (snr-trᵖ ())
snr-anti {t = tr d (⌜Σ⌝ g w) e} (snr-trᵖ ())
snr-anti {t = tr d (⌜Hom⌝ g w v) e} (snr-trᵖ ())
snr-anti {t = tr d (tr g w v) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
-- an `ordtr` PATH steps, so the row recurses (the `app`/`fst` shape),
-- not `()` (the `pair`/`lam` shape).
snr-anti {t = tr d (ordtr a₉ t₉ u₉ p₉ q₉) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)

-- the heads that reduce to nothing: a renaming cannot turn them into redexes.
snr-anti {t = app (var x) u}    (snr-app ())
snr-anti {t = app (pair a b) u} (snr-app ())
snr-anti {t = app ⌜base⌝ u}     (snr-app ())
snr-anti {t = app ⌜Nat⌝ u}      (snr-app ())
snr-anti {t = app ⌜Unit⌝ u}     (snr-app ())
snr-anti {t = app (⌜Π⌝ c d) u}  (snr-app ())
snr-anti {t = app (⌜Σ⌝ c d) u}  (snr-app ())
snr-anti {t = app (⌜IMu⌝ Dⁱ Iⁱ i₉) u} (snr-app ())
snr-anti {t = fst (var x)}      (snr-fst ())
snr-anti {t = fst (lam s)}      (snr-fst ())
snr-anti {t = fst ⌜base⌝}       (snr-fst ())
snr-anti {t = fst ⌜Nat⌝}        (snr-fst ())
snr-anti {t = fst ⌜Unit⌝}       (snr-fst ())
snr-anti {t = fst (⌜IMu⌝ Dⁱ Iⁱ i₉)} (snr-fst ())
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
snr-anti {t = snd ⌜Nat⌝}        (snr-snd ())
snr-anti {t = snd ⌜Unit⌝}       (snr-snd ())
snr-anti {t = snd (⌜IMu⌝ Dⁱ Iⁱ i₉)} (snr-snd ())
snr-anti {t = snd (⌜Π⌝ c d)}    (snr-snd ())
snr-anti {t = snd (⌜Σ⌝ c d)}    (snr-snd ())
snr-anti {t = app (ap c b p) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = fst (ap c b p)}   (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = snd (ap c b p)}   (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = app (⌜Id⌝ c a b) u} (snr-app ())
snr-anti {t = app (idrefl c t) u} (snr-app ())
snr-anti {t = app (jsub d p e) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = fst (⌜Id⌝ c a b)} (snr-fst ())
snr-anti {t = fst (idrefl c t)} (snr-fst ())
snr-anti {t = fst (jsub d p e)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = snd (⌜Id⌝ c a b)} (snr-snd ())
snr-anti {t = snd (idrefl c t)} (snr-snd ())
snr-anti {t = snd (jsub d p e)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
-- the two-former kernel: jsub root steps + the tr-with-Id-family paths
snr-anti {ρ = ρ} {t = jsub d (idrefl c s) e} (snr-jsub-refl hd hc hs) =
  e , (snr-jsub-refl (sn-anti hd) (sn-anti hc) (sn-anti hs) , refl)
snr-anti {t = jsub d p e} (snr-jsubᵖ r) with snr-anti r
... | p' , (r' , refl) = jsub d p' e , (snr-jsubᵖ r' , refl)
snr-anti {ρ = ρ} {t = tr (⌜Hom⌝ c a m) (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e}
         (snr-J-Id hd h₁ h₂ h₃ hs) =
  e , ( snr-J-Id (sn-anti hd) (sn-anti h₁) (sn-anti h₂) (sn-anti h₃)
                 (sn-anti hs)
      , refl )
snr-anti {t = tr d (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (⌜Id⌝ c₁ a₁ b₁) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (idrefl c₁ s₁) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (idrefl c₁ s₁) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (jsub d₁ p₁ e₁) s) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (⌜Id⌝ c a b) e} (snr-trᵖ ())
snr-anti {t = tr d (idrefl c s) e} (snr-trᵖ ())
snr-anti {t = tr d (hrefl unit s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl unit s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl nzero s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl nzero s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (nsuc k) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (con _) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl dι s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (dσ _ _) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (dρ _ _) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl fzero s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (fsuc _) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (fcase0 _) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (⌜Fin⌝ _) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (nsuc k) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (con _) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl dι s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (dσ _ _) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (dρ _ _) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl fzero s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (fsuc _) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (fcase0 _) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (⌜Fin⌝ _) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (natrec z w n) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (dpay _ _ _) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (dih _ _ _ _) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (fcase _ _ _) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (psplit _ _) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
-- ★ INDUCTIVE TYPES: the MOTIVE stays a variable here, as in the `natrec`
-- rows above — `trstk?` falls to `pathstk?` on a `con`/`elim` path, so it
-- does not look at the motive at all.
-- ⚠ the INDEXED code has NO J root (unlike `⌜Mu⌝`): `pathstk? (⌜IMu⌝ …)`
--   is `true`, so a `hrefl ⌜IMu⌝` path is permanently STUCK — the `⌜Nat⌝`
--   rows' shape, not `⌜Mu⌝`'s.
snr-anti {t = tr d (hrefl (ielim D₁ i₁ ms₁ t₁) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (⌜IMu⌝ Dⁱ Iⁱ i₉) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (⌜IMu⌝ Dⁱ Iⁱ i₉) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d unit e} (snr-trᵖ ())
snr-anti {t = tr d nzero e} (snr-trᵖ ())
snr-anti {t = tr d (nsuc k) e} (snr-trᵖ ())
snr-anti {t = tr d (con _) e} (snr-trᵖ ())
snr-anti {t = tr d dι e} (snr-trᵖ ())
snr-anti {t = tr d (dσ _ _) e} (snr-trᵖ ())
snr-anti {t = tr d (dρ _ _) e} (snr-trᵖ ())
snr-anti {t = tr d fzero e} (snr-trᵖ ())
snr-anti {t = tr d (fsuc _) e} (snr-trᵖ ())
snr-anti {t = tr d (fcase0 _) e} (snr-trᵖ ())
snr-anti {t = tr d (⌜Fin⌝ _) e} (snr-trᵖ ())
snr-anti {t = tr d (natrec z w n) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (dpay _ _ _) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (dih _ _ _ _) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (fcase _ _ _) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (psplit _ _) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (⌜IMu⌝ Dⁱ Iⁱ i₉) e} (snr-trᵖ ())
snr-anti {t = tr d (ielim D₁ i₁ ms₁ t₁) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (jsub d₁ p₁ e₁) e} (snr-trᵖ r) with snr-anti r
... | p' , (r' , refl) = tr d p' e , (snr-trᵖ r' , refl)
snr-anti {ρ = ρ} {t = ap c b (hrefl c₁ s)} (snr-ap-J h₁ kh) =
  hrefl c (subTm (single s) b)
  , ( snr-ap-J (sn-anti h₁) (trans (sym (stkC?-ren ρ c₁)) kh)
    , cong (hrefl (renTm ρ c)) (ren-single ρ s b) )
snr-anti {t = ap c b p} (snr-apᵖ r) with snr-anti r
... | p' , (r' , refl) = ap c b p' , (snr-apᵖ r' , refl)
-- ★★ LEVITATED FAMILIES: the root rules (the scrutinee matched SHAPED, so
--   `renTm ρ` reduces), then each scrutinee ξ.  A reduct built under a
--   binder is related by `wk-ren-tm`; `fcase-s`/`psplit-β` by the
--   single/double substitution commutations.
snr-anti {t = ielim D i e (con q)} (snr-ι hD hi he hq) =
  app (app (app e i) q) (dih D e (app D i) q)
  , (snr-ι (sn-anti hD) (sn-anti hi) (sn-anti he) (sn-anti hq) , refl)
snr-anti {t = dpay I D dι} (snr-dpay-ι hI hD) =
  ⌜Unit⌝ , (snr-dpay-ι (sn-anti hI) (sn-anti hD) , refl)
snr-anti {ρ = ρ} {t = dpay I D (dσ S f)} snr-dpay-σ =
  ⌜Σ⌝ S (dpay (renTm vs I) (renTm vs D) (app (renTm vs f) (var vz)))
  , ( snr-dpay-σ
    , cong (⌜Σ⌝ (renTm ρ S))
           (cong₃ dpay (sym (wk-ren-tm ρ I)) (sym (wk-ren-tm ρ D))
                       (cong (λ z → app z (var vz)) (sym (wk-ren-tm ρ f)))) )
snr-anti {ρ = ρ} {t = dpay I D (dρ j C)} snr-dpay-ρ =
  ⌜Σ⌝ (⌜IMu⌝ I D j) (dpay (renTm vs I) (renTm vs D) (renTm vs C))
  , ( snr-dpay-ρ
    , cong (⌜Σ⌝ (⌜IMu⌝ (renTm ρ I) (renTm ρ D) (renTm ρ j)))
           (cong₃ dpay (sym (wk-ren-tm ρ I)) (sym (wk-ren-tm ρ D))
                       (sym (wk-ren-tm ρ C))) )
snr-anti {t = dpay I D C} (snr-dpayᶜ r) with snr-anti r
... | C' , (r' , refl) = dpay I D C' , (snr-dpayᶜ r' , refl)
snr-anti {t = dih D e dι p} (snr-dih-ι hD he hp) =
  unit , (snr-dih-ι (sn-anti hD) (sn-anti he) (sn-anti hp) , refl)
snr-anti {t = dih D e (dσ S f) p} (snr-dih-σ hS) =
  dih D e (app f (fst p)) (snd p) , (snr-dih-σ (sn-anti hS) , refl)
snr-anti {t = dih D e (dρ j C) p} snr-dih-ρ =
  pair (ielim D j e (fst p)) (dih D e C (snd p)) , (snr-dih-ρ , refl)
snr-anti {t = dih D e C p} (snr-dihᶜ r) with snr-anti r
... | C' , (r' , refl) = dih D e C' p , (snr-dihᶜ r' , refl)
snr-anti {t = fcase fzero a b} (snr-fcase-z hb) =
  a , (snr-fcase-z (sn-anti hb) , refl)
snr-anti {ρ = ρ} {t = fcase (fsuc t₀) a b} (snr-fcase-s ht ha) =
  subTm (single t₀) b , (snr-fcase-s (sn-anti ht) (sn-anti ha) , ren-single ρ t₀ b)
snr-anti {t = fcase t₀ a b} (snr-fcaseᵗ r) with snr-anti r
... | t' , (r' , refl) = fcase t' a b , (snr-fcaseᵗ r' , refl)
snr-anti {ρ = ρ} {t = psplit b (pair x y)} (snr-psplit-β hx hy) =
  subTm (single2 x y) b
  , (snr-psplit-β (sn-anti hx) (sn-anti hy) , sym (ren-comm2 ρ b x y))
snr-anti {t = psplit b q} (snr-psplitᵍ r) with snr-anti r
... | q' , (r' , refl) = psplit b q' , (snr-psplitᵍ r' , refl)
snr-anti {t = tr (⌜Hom⌝ c a m) (hrefl (⌜Fin⌝ n) s) e} (snr-J-Fin hd hs) =
  e , (snr-J-Fin (sn-anti hd) (sn-anti hs) , refl)
snr-anti {t = tr d (hrefl (⌜Fin⌝ n) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (⌜Fin⌝ n) s) e} (snr-trᵖ (snr-hrefl-pw ()))

csr-anti {t = var x} (csr-here ())
csr-anti {t = unit} (csr-here ())
csr-anti {t = nzero} (csr-here ())
csr-anti {t = nsuc _} (csr-here ())
csr-anti {t = con _} (csr-here ())
csr-anti {t = dι} (csr-here ())
csr-anti {t = dσ _ _} (csr-here ())
csr-anti {t = dρ _ _} (csr-here ())
csr-anti {t = fzero} (csr-here ())
csr-anti {t = fsuc _} (csr-here ())
csr-anti {t = fcase0 _} (csr-here ())
csr-anti {t = ⌜Fin⌝ _} (csr-here ())
csr-anti {t = natrec z w n} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = dpay _ _ _} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = dih _ _ _ _} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = fcase _ _ _} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = psplit _ _} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = ielim D i ms t₀} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = ordtr a t u p q} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = lam _} (csr-here ())
csr-anti {t = pair _ _} (csr-here ())
csr-anti {t = ⌜base⌝} (csr-here ())
csr-anti {t = absurd c e} (csr-here ())
csr-anti {t = ⌜Nat⌝ } (csr-here ())
csr-anti {t = ⌜Unit⌝ } (csr-here ())
csr-anti {t = ⌜IMu⌝ Dⁱ Iⁱ i } (csr-here ())
csr-anti {t = ⌜Π⌝ _ _} (csr-here ())
csr-anti {t = ⌜Σ⌝ _ _} (csr-here ())
csr-anti {t = app f u} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = fst q} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = snd q} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = ap c b p} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = ⌜Id⌝ c a b} (csr-here ())
csr-anti {t = idrefl c t} (csr-here ())
csr-anti {t = jsub d p e} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = hrefl _ _} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = tr _ _ _} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = ⌜Hom⌝ c a b} (csr-here ())
csr-anti {t = ⌜Hom⌝ c a b} (csr-hom σ) with csr-anti σ
... | c' , (σ' , refl) = ⌜Hom⌝ c' a b , (csr-hom σ' , refl)

------------------------------------------------------------------------
-- ★ W2b final frontier — FORWARD renaming for the SN family (the
-- mirror of the anti-family above; the one renaming action never
-- needed until `semTrPw` had to push a payload's spine-chains from
-- the instance level onto the binder-form motive).
------------------------------------------------------------------------

sne-ren : {ρ : Ren Θ Ξ} {t : RTm Θ} → SNe t → SNe (renTm ρ t)
sn-ren  : {ρ : Ren Θ Ξ} {t : RTm Θ} → SN t → SN (renTm ρ t)
snr-ren : {ρ : Ren Θ Ξ} {t t' : RTm Θ} → SNRed t t' →
          SNRed (renTm ρ t) (renTm ρ t')
csr-ren : {ρ : Ren Θ Ξ} {t t' : RTm Θ} → CSR t t' →
          CSR (renTm ρ t) (renTm ρ t')

sne-ren {ρ = ρ} (sne-var x)   = sne-var (ρ x)
sne-ren {ρ = ρ} (sne-natrec {n = n} hz hw hn key) =
  sne-natrec (sn-ren hz) (sn-ren hw) (sn-ren hn)
             (trans (natstk?-ren ρ n) key)
-- ★ INDUCTIVE TYPES: the key transports FORWARD through `mustk?-ren`.
sne-ren (sne-app n s)         = sne-app (sne-ren n) (sn-ren s)
sne-ren (sne-absurd sc sn₀)   = sne-absurd (sn-ren sc) (sn-ren sn₀)
sne-ren (sne-fst n)           = sne-fst (sne-ren n)
sne-ren (sne-snd n)           = sne-snd (sne-ren n)
sne-ren {ρ = ρ} (sne-hrefl {c = c} hc ht kn) =
  sne-hrefl (sn-ren hc) (sn-ren ht) (trans (nopw?-ren ρ c) kn)
sne-ren {ρ = ρ} (sne-tr {d = d} {p = p} hd hp he key) =
  sne-tr (sn-ren hd) (sn-ren hp) (sn-ren he)
         (trans (trstk?-ren ρ d p) key)
sne-ren {ρ = ρ} (sne-ap {p = p} hc hb hp key) =
  sne-ap (sn-ren hc) (sn-ren hb) (sn-ren hp)
         (trans (apstk?-ren ρ p) key)
sne-ren {ρ = ρ} (sne-jsub {p = p} hd hp he key) =
  sne-jsub (sn-ren hd) (sn-ren hp) (sn-ren he)
           (trans (idstk?-ren ρ p) key)
sne-ren {ρ = ρ} (sne-ordtr {a = a} {t = t} {u = u} ha ht hu hp hq key) =
  sne-ordtr (sn-ren ha) (sn-ren ht) (sn-ren hu) (sn-ren hp) (sn-ren hq)
            (trans (ordstk?-ren ρ a t u) key)
sne-ren {ρ = ρ} (sne-ielim {t = t₀} hD hi he ht key) =
  sne-ielim (sn-ren hD) (sn-ren hi) (sn-ren he) (sn-ren ht) (trans (mustk?-ren ρ t₀) key)
sne-ren {ρ = ρ} (sne-dpay {C = C} hI hD hC key) =
  sne-dpay (sn-ren hI) (sn-ren hD) (sn-ren hC) (trans (dstk?-ren ρ C) key)
sne-ren {ρ = ρ} (sne-dih {C = C} hD he hC hp key) =
  sne-dih (sn-ren hD) (sn-ren he) (sn-ren hC) (sn-ren hp) (trans (dstk?-ren ρ C) key)
sne-ren {ρ = ρ} (sne-fcase {t = t₀} ht ha hb key) =
  sne-fcase (sn-ren ht) (sn-ren ha) (sn-ren hb) (trans (finstk?-ren ρ t₀) key)
sne-ren (sne-fcase0 ht) = sne-fcase0 (sn-ren ht)
sne-ren (sne-psplit hb n) = sne-psplit (sn-ren hb) (sne-ren n)

sn-ren (sn-ne n)        = sn-ne (sne-ren n)
sn-ren (sn-lam h)       = sn-lam (sn-ren h)
sn-ren (sn-pair ha hb)  = sn-pair (sn-ren ha) (sn-ren hb)
sn-ren sn-cb            = sn-cb
sn-ren sn-cNat          = sn-cNat
sn-ren sn-cUnit         = sn-cUnit
sn-ren (sn-cΠ h₁ h₂)    = sn-cΠ (sn-ren h₁) (sn-ren h₂)
sn-ren (sn-cΣ h₁ h₂)    = sn-cΣ (sn-ren h₁) (sn-ren h₂)
sn-ren (sn-cH h₁ h₂ h₃) = sn-cH (sn-ren h₁) (sn-ren h₂) (sn-ren h₃)
sn-ren (sn-cId h₁ h₂ h₃) = sn-cId (sn-ren h₁) (sn-ren h₂) (sn-ren h₃)
sn-ren (sn-idrefl h₁ h₂) = sn-idrefl (sn-ren h₁) (sn-ren h₂)
sn-ren sn-unit          = sn-unit
sn-ren sn-nzero         = sn-nzero
sn-ren (sn-nsuc h)      = sn-nsuc (sn-ren h)
sn-ren (sn-con h)       = sn-con (sn-ren h)
sn-ren (sn-exp r h)     = sn-exp (snr-ren r) (sn-ren h)
sn-ren (sn-cIMu h₁ h₂ h₃) = sn-cIMu (sn-ren h₁) (sn-ren h₂) (sn-ren h₃)
sn-ren sn-cFin          = sn-cFin
sn-ren (sn-con h)       = sn-con (sn-ren h)
sn-ren sn-dι            = sn-dι
sn-ren (sn-dσ h₁ h₂)    = sn-dσ (sn-ren h₁) (sn-ren h₂)
sn-ren (sn-dρ h₁ h₂)    = sn-dρ (sn-ren h₁) (sn-ren h₂)
sn-ren sn-fzero         = sn-fzero
sn-ren (sn-fsuc h)      = sn-fsuc (sn-ren h)

snr-ren {ρ = ρ} (snr-β {s = s} {u = u} hu) =
  subst (λ z → SNRed (app (lam (renTm (extR ρ) s)) (renTm ρ u)) z)
        (ren-single ρ u s)
        (snr-β (sn-ren hu))
snr-ren (snr-natrec-zero hw) = snr-natrec-zero (sn-ren hw)
snr-ren {ρ = ρ} (snr-natrec-suc {z = z} {w = w} {n = m} hz hw hn) =
  subst (λ q → SNRed (natrec (renTm ρ z) (renTm (extR (extR ρ)) w)
                             (nsuc (renTm ρ m))) q)
        (sym (trans (ren-comm ρ (subTm (extS (single m)) w) (natrec z w m))
                    (cong (λ q → subTm (single (natrec (renTm ρ z)
                                                       (renTm (extR (extR ρ)) w)
                                                       (renTm ρ m))) q)
                          (ren-comm-ext ρ w m))))
        (snr-natrec-suc (sn-ren hz) (sn-ren hw) (sn-ren hn))
snr-ren (snr-natrecⁿ r) = snr-natrecⁿ (snr-ren r)
-- ★ INDUCTIVE TYPES: ι's equation, forward — `ren-fields` after `ren-sel`.
-- ★ the INDEXED ι, forward.  `ren-ifieldsⁱ` after `ren-sel`.
snr-ren (snr-ielimᵗ r)  = snr-ielimᵗ (snr-ren r)
snr-ren (snr-ordtr-z ht hu hp hq) =
  snr-ordtr-z (sn-ren ht) (sn-ren hu) (sn-ren hp) (sn-ren hq)
snr-ren (snr-ordtr-szz ha hq)    = snr-ordtr-szz (sn-ren ha) (sn-ren hq)
snr-ren (snr-ordtr-ssz ha ht hp) = snr-ordtr-ssz (sn-ren ha) (sn-ren ht) (sn-ren hp)
snr-ren (snr-ordtr-szs hq)       = snr-ordtr-szs (sn-ren hq)
snr-ren snr-ordtr-sss            = snr-ordtr-sss
snr-ren (snr-ordtrᵃ r)  = snr-ordtrᵃ (snr-ren r)
snr-ren (snr-ordtrᵗ r)  = snr-ordtrᵗ (snr-ren r)
snr-ren (snr-ordtrᵘᶻ r) = snr-ordtrᵘᶻ (snr-ren r)
snr-ren (snr-ordtrᵘˢ r) = snr-ordtrᵘˢ (snr-ren r)
snr-ren (snr-βfst hb) = snr-βfst (sn-ren hb)
snr-ren (snr-βsnd ha) = snr-βsnd (sn-ren ha)
snr-ren (snr-app r)   = snr-app (snr-ren r)
snr-ren (snr-fst r)   = snr-fst (snr-ren r)
snr-ren (snr-snd r)   = snr-snd (snr-ren r)
snr-ren (snr-hreflᶜ σ) = snr-hreflᶜ (csr-ren σ)
snr-ren {ρ = ρ} (snr-hrefl-pw {C = C} {t = t} kp) =
  subst (λ z → SNRed (hrefl (renTm ρ C) (renTm ρ t)) z)
        (cong₂ (λ x y → lam (hrefl x (app y (var vz))))
               (pwBody-ren ρ C kp)
               (sym (wk-ren-tm ρ t)))
        (snr-hrefl-pw (trans (pw?-ren ρ C) kp))
snr-ren (snr-J-base hd hs) = snr-J-base (sn-ren hd) (sn-ren hs)
snr-ren (snr-J-Unit hd hs) = snr-J-Unit (sn-ren hd) (sn-ren hs)
snr-ren (snr-J-IMu hd hs)  = snr-J-IMu (sn-ren hd) (sn-ren hs)
snr-ren (snr-J-Σ hd h₁ h₂ hs) =
  snr-J-Σ (sn-ren hd) (sn-ren h₁) (sn-ren h₂) (sn-ren hs)
snr-ren {ρ = ρ} (snr-J-Hom {c₁ = c₁} hd h₁ h₂ h₃ hs ks) =
  snr-J-Hom (sn-ren hd) (sn-ren h₁) (sn-ren h₂) (sn-ren h₃) (sn-ren hs)
            (trans (stkA?-ren ρ c₁) ks)
snr-ren {ρ = ρ} (snr-ap-J {cB = cB} {b = b} {c₁ = c₁} {s = t} h₁ ks) =
  subst (λ z → SNRed (ap (renTm ρ cB) (renTm (extR ρ) b)
                         (hrefl (renTm ρ c₁) (renTm ρ t))) z)
        (cong (hrefl (renTm ρ cB)) (ren-single ρ t b))
        (snr-ap-J (sn-ren h₁) (trans (stkC?-ren ρ c₁) ks))
snr-ren (snr-apᵖ r) = snr-apᵖ (snr-ren r)
snr-ren (snr-jsub-refl hd hc hs) =
  snr-jsub-refl (sn-ren hd) (sn-ren hc) (sn-ren hs)
snr-ren (snr-jsubᵖ r) = snr-jsubᵖ (snr-ren r)
snr-ren (snr-J-Id hd h₁ h₂ h₃ hs) =
  snr-J-Id (sn-ren hd) (sn-ren h₁) (sn-ren h₂) (sn-ren h₃) (sn-ren hs)
snr-ren snr-taut = snr-taut
snr-ren {ρ = ρ} (snr-trᵖ r) = snr-trᵖ (snr-ren r)
snr-ren {ρ = ρ} (snr-tr-mot σ) = snr-tr-mot (csr-ren σ)
snr-ren {ρ = ρ} (snr-tr-pw {c = c} {a = a} {f = f} {e = e} hc ha kp) =
  subst (λ z → SNRed (tr (⌜Hom⌝ (renTm (extR ρ) c) (renTm (extR ρ) a)
                                (var vz))
                         (lam (renTm (extR ρ) f)) (renTm ρ e)) z)
        (cong lam
          (tr-cong₃
            (⌜Hom⌝-cong₃
              (trans (cong (renTm pwShift) (pwBody-ren (extR ρ) c kp))
                     (sym (pwShift-ren ρ (pwBody c))))
              (cong (λ z → app z (var (vs vz)))
                    (sym (wk-ren-tm (extR ρ) a)))
              refl)
            refl
            (cong (λ z → app z (var vz)) (sym (wk-ren-tm ρ e)))))
        (snr-tr-pw (sn-ren hc) (sn-ren ha) (trans (pw?-ren (extR ρ) c) kp))
snr-ren (snr-ι hD hi he hq) = snr-ι (sn-ren hD) (sn-ren hi) (sn-ren he) (sn-ren hq)
snr-ren (snr-dpay-ι hI hD) = snr-dpay-ι (sn-ren hI) (sn-ren hD)
snr-ren {ρ = ρ} (snr-dpay-σ {I = I} {D = D} {S = S} {f = f}) =
  subst (SNRed (dpay (renTm ρ I) (renTm ρ D) (dσ (renTm ρ S) (renTm ρ f))))
        (cong (⌜Σ⌝ (renTm ρ S))
              (cong₃ dpay (sym (wk-ren-tm ρ I)) (sym (wk-ren-tm ρ D))
                          (cong (λ z → app z (var vz)) (sym (wk-ren-tm ρ f)))))
        snr-dpay-σ
snr-ren {ρ = ρ} (snr-dpay-ρ {I = I} {D = D} {j = j} {C = C}) =
  subst (SNRed (dpay (renTm ρ I) (renTm ρ D) (dρ (renTm ρ j) (renTm ρ C))))
        (cong (⌜Σ⌝ (⌜IMu⌝ (renTm ρ I) (renTm ρ D) (renTm ρ j)))
              (cong₃ dpay (sym (wk-ren-tm ρ I)) (sym (wk-ren-tm ρ D))
                          (sym (wk-ren-tm ρ C))))
        snr-dpay-ρ
snr-ren (snr-dpayᶜ r) = snr-dpayᶜ (snr-ren r)
snr-ren (snr-dih-ι hD he hp) = snr-dih-ι (sn-ren hD) (sn-ren he) (sn-ren hp)
snr-ren (snr-dih-σ hS) = snr-dih-σ (sn-ren hS)
snr-ren snr-dih-ρ = snr-dih-ρ
snr-ren (snr-dihᶜ r) = snr-dihᶜ (snr-ren r)
snr-ren (snr-fcase-z hb) = snr-fcase-z (sn-ren hb)
snr-ren {ρ = ρ} (snr-fcase-s {t = t₀} {a = a} {b = b} ht ha) =
  subst (SNRed (fcase (fsuc (renTm ρ t₀)) (renTm ρ a) (renTm (extR ρ) b)))
        (ren-single ρ t₀ b)
        (snr-fcase-s (sn-ren ht) (sn-ren ha))
snr-ren (snr-fcaseᵗ r) = snr-fcaseᵗ (snr-ren r)
snr-ren {ρ = ρ} (snr-psplit-β {b = b} {x = x} {y = y} hx hy) =
  subst (SNRed (psplit (renTm (extR (extR ρ)) b) (pair (renTm ρ x) (renTm ρ y))))
        (sym (ren-comm2 ρ b x y))
        (snr-psplit-β (sn-ren hx) (sn-ren hy))
snr-ren (snr-psplitᵍ r) = snr-psplitᵍ (snr-ren r)
snr-ren (snr-J-Fin hd hs) = snr-J-Fin (sn-ren hd) (sn-ren hs)

csr-ren (csr-here r) = csr-here (snr-ren r)
csr-ren (csr-hom σ)  = csr-hom (csr-ren σ)


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

-- ★ WF stage A: the same trick one binder deeper — the recursor's step
-- body lives under TWO binders, so its SN premise peels two variable
-- instantiations (both are renaming-substitutions, so `sn-anti` twice).
sn-body₂ : (x₀ : Var Ξ) {w : RTm ((Ξ ∙) ∙)} →
           SN (subTm (single (var x₀)) (subTm (extS (single (var x₀))) w)) →
           SN w
sn-body₂ {Ξ = Ξ} x₀ {w} h = sn-anti (subst SN eq (sn-body x₀ h))
  where
    ρ₁ : Ren ((Ξ ∙) ∙) (Ξ ∙)
    ρ₁ vz          = vz
    ρ₁ (vs vz)     = vs x₀
    ρ₁ (vs (vs y)) = vs y

    pw : (x : Var ((Ξ ∙) ∙)) → extS (single (var x₀)) x ≡ ⟨ ρ₁ ⟩ᵣ x
    pw vz          = refl
    pw (vs vz)     = refl
    pw (vs (vs y)) = refl

    eq : subTm (extS (single (var x₀))) w ≡ renTm ρ₁ w
    eq = trans (subTm-cong pw w) (subTm-var ρ₁ w)

------------------------------------------------------------------------
-- 3. THE EXISTENTIAL PAYLOAD, and its two casts.
--
-- `fund` returns a PAIR — some semantic type at `A`, and a membership at `t`.
-- Casting is by `≡` on both indices AT ONCE: doing it in two steps would leave
-- the membership pointing at a different (though equal) first component.
------------------------------------------------------------------------
