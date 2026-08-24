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
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_; ⊥; ⊥-elim )

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom; Id; Hom-cong₃; Id-cong₃; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃; ⌜Id⌝-cong₃; jsub-cong₃
        ; RTm; var; lam; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap
        ; ⌜Id⌝; idrefl; jsub
        ; Unit; Nat; unit; nzero; nsuc; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝; ⌜Mu⌝
        ; ordtr-cong₅
        ; Ren; extR; renTy; renTm
        ; Sub; subTy; subTm; extS; idₛ
        ; _∘ᵣ_
        ; subTy-cong; subTm-cong
        ; subTy-renTy; subTm-renTm
        ; renTy-subTy; renTm-subTm
        ; subTy-subTy; subTm-subTm
        ; subTy-id; subTm-id; renTm-renTm; renTm-cong
        ; Desc; Mu; con; elim; lookupD; sel; fields; ren-fields; ren-sel
        ; isingle; ren-ifieldsⁱ
        ; IMu; icon; ielim; ⌜IMu⌝; ICon; IDesc; iι; iρ; iκ; inil; _◂_; ipayTy; ilookupD; _∈ID_; hereID; thereID; iihs; ifields; εwkTm )
open import DirectedHoTT.Spec.Typing
  using ( single; nrs
        ; _⟶_; _⟶*_; done; step
        ; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ordtr-z; ordtr-szz; ordtr-ssz; ordtr-szs; ordtr-sss
        ; ξ-ordtrᵃ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ; ξ-ordtrq; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ
        ; ξ-hreflᶜ; ξ-hreflᵃ; hrefl-pw; tr-J-base; tr-J-Σ; tr-J-Hom; tr-taut
        ; tr-pw; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ
        ; ξ-Σˡ; ξ-Σʳ
        ; _≅_
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋
        ; _∋_∷_; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢absurd
        ; El-⌜Hom⌝; ξ-El; El-⌜Π⌝; _⟶ᵀ_; El-⌜base⌝; El-⌜Σ⌝; El-⌜Id⌝
        ; El-⌜Nat⌝; El-⌜Unit⌝
        ; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢trU; ⊢ap; ⊢conv
        ; ⊢⌜Nat⌝; ⊢⌜Unit⌝
        ; ⊢⌜Id⌝; ⊢idrefl; ⊢jsub
        ; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom; ty-Id; ty-Unit; ty-Nat
        ; ⊢unit; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢ctx_; c-◇; c-▹
        ; ⊢id; ⊢appex )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; occTm; subTm-occ
        ; pw?; stkC?; stkA?; pwBody; pwDom; pwShift
        ; pw?-ren; stkC?-ren; stkA?-ren; pwBody-ren; wk-ren-tm; pw?-sub
        ; stkC?→stkA?
        ; wk-sub-tm; stk⊥pw; pw⊥stk; flat?; flat→stk; flat?-sub
        ; eqv; occ-sub; occ-ren-tm; avoids-wk )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( ≅ᵀ-sub; sub-comm; wk-sub )
open import DirectedHoTT.Metatheory.Confluence using ( pwShift-ren; stkC?-red; stkA?-red; subTm-monoˢ; single-mono; ⟶*-trans; ren-comm; ren-comm-ext )
open import DirectedHoTT.Algorithm.DecideConversion using ( Dec; dec-conv )
open import DirectedHoTT.Metatheory.Injectivity
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; confluentᵀ; church-rosserᵀ; Π-inj
        ; red→≅ᵀ; Π-reduct; Σ-reduct; mkΠRed; mkΣRed
        ; Id-reduct; ⟶ᵀ*-Homᵀ )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( HomΠShape; hsΠ; hsH; hom-shape; hom-shapeN; nn-U; NoNat; pw-El-decode
        ; HomRed; mkHomRed; Hom-to-Hom; homAmb→
        ; HomToΠ; via-U; via-Π; hom-to-Π
        ; U-reduct; wk-cancel-tm; ≅ᵀ-Homᵀ; gen-var; subTy-comm; subTy-monoˢ )
open import DirectedHoTT.Metatheory.LogicalRelation
  using ( SNe; sne-var; sne-app; sne-absurd; sne-fst; sne-snd; sne-hrefl; sne-tr; sne-ap; sne-jsub
        ; Ne; ne-var; ne-app; ne-absurd; ne-fst; ne-snd; ne-hrefl; ne-tr; ne-ap; ne-jsub; homSem₁
        ; SN; sn-ne; sn-lam; sn-pair; sn-cb; sn-cΠ; sn-cΣ; sn-cH; sn-cId; sn-idrefl; sn-exp
        ; sn-cNat; sn-cUnit; sn-cMu; sn-cIMu; sn-icon; snr-J-IMu
        ; sne-ielim; snr-ιi; snr-ielimᵗ
        ; SNRed; snr-β; snr-βfst; snr-βsnd; snr-app; snr-fst; snr-snd
        ; snr-hreflᶜ; snr-J-base; snr-J-Σ; snr-J-Id; snr-J-Unit; snr-J-Mu; snr-taut; snr-trᵖ; snr-ap-J; snr-apᵖ
        ; snr-jsub-refl; snr-jsubᵖ
        ; snr-natrec-zero; snr-natrec-suc; snr-natrecⁿ
        ; sne-natrec; ne-natrec; sn-unit; sn-nzero; sn-nsuc
        ; sne-ordtr; ne-ordtr; ordstk?; ordstk?-ren
        ; ordstk?-redᵃ; ordstk?-redᵗ; ordstk?-redᵘ
        ; snr-ordtr-z; snr-ordtr-szz; snr-ordtr-ssz; snr-ordtr-szs; snr-ordtr-sss
        ; snr-ordtrᵃ; snr-ordtrᵗ; snr-ordtrᵘᶻ; snr-ordtrᵘˢ
        ; NatMem; nm-ne; nm-zero; nm-suc; nm-exp; natmem-whred
        ; ⊩₁Unit; ⊩₁Nat; natstk?; natstk?-ren; natstk?-red; sne→natstk; sn-whred
        ; homNatSem; homNatSem₀; hns₀-in; bwd₀-mem⁻
        ; StkHd; sh-Hom; sh-NatH; homnat?
        ; trstk?-ren; apstk?-ren; idstk?-ren; nopw?-ren; trlam?-ren
        ; idstk?-red; ⊩₀Id; ⊩₁Id; IdPay; idpay-transfer; idpay-peel; sne-nopay
        ; nopw⊥pw; stk⊥dead; pw⊥dead; dead→nopw; snr-nonpw
        ; snr-hrefl-pw; snr-J-Hom; snr-tr-pw; snr-tr-mot
        ; deadmot?; deadmot?-red; deadmot?-ren; deadmot→nopw; stk→deadmot
        ; nopw?-red; nopw?-red*
        ; CSR; csr-here; csr-hom; csr→⟶; csr-nonpw; csr-stk⊥; sn-csr
        ; csr-det
        ; _⟶csr*_; csr-done; csr-step; csrs-hom
        ; PayT; payChain; payT-exp; payT-whred; payT-irrel
        ; payT-cast; payT-code; payHomT; _⟶snr*_; snr-done; snr-step
        ; ⊩₀_; ⊩₀base; ⊩₀ne; ⊩₀Π; ⊩₀Σ; ⊩₀Hom; _⊩₀∋_; bwd₀; exp₁
        ; ⊩₀Unit; ⊩₀Nat
        ; base-nf; Unit-nf; Nat-nf; El-ne-reduct; mkElNe; Hom-stk-reduct; mkHomStk
        ; nopw?; trlam?; stablecd?; stableA?; idstk?; sne→spine; wk-single; snr→⟶
        ; exp₀; f≢t
        ; mem-whred₁; homSem₀; homSem₀-mem-endpoints
        ; sne→stablecd; sne→stableA; trstk?
        ; ⊩₁_; ⊩₁base; ⊩₁U; ⊩₁ne; ⊩₁Π; ⊩₁Σ; ⊩₁Hom; _⊩₁∋_
        ; bwd₁; irrel₁; conv₁; CR1₀; CR1₁; CR3₀; CR3₁
        ; emb; emb-coh
        ; sem-conv; sem-lam; sem-app; sem-fst; sem-snd; sem-pair
        ; sem-El; sem-⌜base⌝; sem-⌜Π⌝; sem-⌜Σ⌝; sem-⌜Hom⌝; sem-hrefl
        ; ⟶ᵀ*-sub
        ; IsNormal; WN; mkWN; wn
        ; projl; projr; dfst; dsnd
        ; sne-elim; sn-con; snr-ι; snr-elimᵗ; mustk?; mustk?-ren )


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
subTy-var ρ (Mu D)   = refl
subTy-var ρ (IMu Dⁱ Iⁱ i) = cong (IMu Dⁱ Iⁱ) (subTm-var ρ i)
subTy-var ρ (Id A t u) =
  Id-cong₃ (subTy-var ρ A) (subTm-var ρ t) (subTm-var ρ u)
subTm-var ρ (var x)   = refl
subTm-var ρ (lam t)   =
  cong lam (trans (subTm-cong (exts-var ρ) t) (subTm-var (extR ρ) t))
subTm-var ρ (app t u)  = cong₂ app (subTm-var ρ t) (subTm-var ρ u)
subTm-var ρ (pair a b) = cong₂ pair (subTm-var ρ a) (subTm-var ρ b)
subTm-var ρ (absurd c e) = cong₂ absurd (subTm-var ρ c) (subTm-var ρ e)
subTm-var ρ (ordtr a t u p q) =
  ordtr-cong₅ (subTm-var ρ a) (subTm-var ρ t) (subTm-var ρ u)
              (subTm-var ρ p) (subTm-var ρ q)
subTm-var ρ (fst p)    = cong fst (subTm-var ρ p)
subTm-var ρ (snd p)    = cong snd (subTm-var ρ p)
subTm-var ρ ⌜base⌝     = refl
subTm-var ρ ⌜Nat⌝      = refl
subTm-var ρ ⌜Unit⌝     = refl
subTm-var ρ (⌜Mu⌝ Dᵐ)  = refl
subTm-var ρ (⌜IMu⌝ Dⁱ Iⁱ i) = cong (⌜IMu⌝ Dⁱ Iⁱ) (subTm-var ρ i)
subTm-var ρ unit       = refl
subTm-var ρ nzero      = refl
subTm-var ρ (nsuc n)   = cong nsuc (subTm-var ρ n)
subTm-var ρ (con k q)  = cong (con k) (subTm-var ρ q)
subTm-var ρ (elim D ms t) = cong₂ (elim D) (subTm-var ρ ms) (subTm-var ρ t)
subTm-var ρ (icon k q) = cong (icon k) (subTm-var ρ q)
subTm-var ρ (ielim D i ms t) =
  trans (cong (λ z → ielim D z (subTm ⟨ ρ ⟩ᵣ ms) (subTm ⟨ ρ ⟩ᵣ t))
              (subTm-var ρ i))
        (cong₂ (ielim D (renTm ρ i)) (subTm-var ρ ms) (subTm-var ρ t))
subTm-var ρ (natrec z w n) =
  natrec-cong₃ (subTm-var ρ z)
    (trans (subTm-cong (exts2-var ρ) w) (subTm-var (extR (extR ρ)) w))
    (subTm-var ρ n)
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
subTm-var ρ (ap c b p)  =
  ap-cong₃ (subTm-var ρ c)
           (trans (subTm-cong (exts-var ρ) b) (subTm-var (extR ρ) b))
           (subTm-var ρ p)
subTm-var ρ (⌜Id⌝ c a b) =
  ⌜Id⌝-cong₃ (subTm-var ρ c) (subTm-var ρ a) (subTm-var ρ b)
subTm-var ρ (idrefl c t) = cong₂ idrefl (subTm-var ρ c) (subTm-var ρ t)
subTm-var ρ (jsub d p e) =
  jsub-cong₃ (trans (subTm-cong (exts-var ρ) d) (subTm-var (extR ρ) d))
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
sne-anti {ρ = ρ} {t = elim D ms t₀} (sne-elim hm ht key) =
  sne-elim (sn-anti hm) (sn-anti ht)
           (trans (sym (mustk?-ren ρ t₀)) key)
-- ⚠ the INDEXED twin takes ONE MORE `SN`: `ielim` carries the index and
--   `ξ-ielimⁱ` steps it, so `sne-ielim` has a fourth premise.  The key is
--   still about the SCRUTINEE alone, so it rides the same `mustk?-ren`.
sne-anti {ρ = ρ} {t = ielim D i ms t₀} (sne-ielim hi hm ht key) =
  sne-ielim (sn-anti hi) (sn-anti hm) (sn-anti ht)
            (trans (sym (mustk?-ren ρ t₀)) key)
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

sn-anti {t = var x}    _              = sn-ne (sne-var x)
sn-anti {t = unit}     _              = sn-unit
sn-anti {t = nzero}    _              = sn-nzero
sn-anti {t = nsuc n}   (sn-nsuc h)    = sn-nsuc (sn-anti h)
sn-anti {t = natrec z w n} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = natrec z w n} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = con k q}  (sn-con h)     = sn-con (sn-anti h)
sn-anti {t = elim D ms t₀} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = elim D ms t₀} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = icon k q} (sn-icon h)    = sn-icon (sn-anti h)
sn-anti {t = ielim D i ms t₀} (sn-ne nt) = sn-ne (sne-anti nt)
sn-anti {t = ielim D i ms t₀} (sn-exp r h) with snr-anti r
... | t' , (r' , refl) = sn-exp r' (sn-anti h)
sn-anti {t = lam s}    (sn-lam h)     = sn-lam (sn-anti h)
sn-anti {t = pair a b} (sn-pair ha hb) = sn-pair (sn-anti ha) (sn-anti hb)
sn-anti {t = ⌜base⌝}   _              = sn-cb
sn-anti {t = ⌜Nat⌝}    _              = sn-cNat
sn-anti {t = ⌜Unit⌝}   _              = sn-cUnit
sn-anti {t = ⌜Mu⌝ Dᵐ}  _              = sn-cMu
-- ⚠ NOT nullary like `⌜Mu⌝`: `⌜IMu⌝` carries the index, so its `SN` has a
--   premise and anti-renaming has to recurse into it.
sn-anti {t = ⌜IMu⌝ Dⁱ Iⁱ i} (sn-cIMu h) = sn-cIMu (sn-anti h)
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
snr-anti {ρ = ρ} {t = elim D ms (con k q)} (snr-ι hm hq) =
  fields D ms (lookupD D k) (sel k ms) q
  , ( snr-ι (sn-anti hm) (sn-anti hq)
    , sym (trans (ren-fields ρ D ms (lookupD D k) (sel k ms) q)
                 (cong (λ w → fields D (renTm ρ ms) (lookupD D k) w (renTm ρ q))
                       (ren-sel ρ k ms))) )
snr-anti {t = elim D ms t₀} (snr-elimᵗ r) with snr-anti r
... | t' , (r' , refl) = elim D ms t' , (snr-elimᵗ r' , refl)
-- ★ the INDEXED ι.  Same shape, one extra `SN` premise, and the equation
--   is `ren-ifieldsⁱ` — the specialised form that already folds in
--   `isingle-ren`, so the environment lands as `isingle (renTm ρ i)`.
snr-anti {ρ = ρ} {t = ielim D i ms (icon k q)} (snr-ιi hi hm hq) =
  ifields D i ms (isingle i) (ilookupD D k) (sel k ms) q
  , ( snr-ιi (sn-anti hi) (sn-anti hm) (sn-anti hq)
    , sym (trans (ren-ifieldsⁱ ρ D i ms (ilookupD D k) (sel k ms) q)
                 (cong (λ w → ifields D (renTm ρ i) (renTm ρ ms)
                                      (isingle (renTm ρ i))
                                      (ilookupD D k) w (renTm ρ q))
                       (ren-sel ρ k ms))) )
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
snr-anti {t = app (natrec z w n) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
-- ★ INDUCTIVE TYPES: in a SPINE position a `con` head is inert (no SNRed
-- rule steps it) and an `elim` head recurses — `nsuc`/`natrec` exactly.
snr-anti {t = app (con k q) u}  (snr-app ())
snr-anti {t = app (elim D ms t₀) u} (snr-app r) with snr-anti r
... | t' , (r' , refl) = app t' u , (snr-app r' , refl)
snr-anti {t = app (icon k q) u}  (snr-app ())
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
snr-anti {t = fst (natrec z w n)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = snd unit}         (snr-snd ())
snr-anti {t = snd nzero}        (snr-snd ())
snr-anti {t = snd (nsuc k)}     (snr-snd ())
snr-anti {t = snd (natrec z w n)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = snd (con k q)}    (snr-snd ())
snr-anti {t = snd (elim D ms t₀)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = fst (con k q)}    (snr-fst ())
snr-anti {t = fst (elim D ms t₀)} (snr-fst r) with snr-anti r
... | t' , (r' , refl) = fst t' , (snr-fst r' , refl)
snr-anti {t = snd (icon k q)}    (snr-snd ())
snr-anti {t = snd (ielim D i ms t₀)} (snr-snd r) with snr-anti r
... | t' , (r' , refl) = snd t' , (snr-snd r' , refl)
snr-anti {t = fst (icon k q)}    (snr-fst ())
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
snr-anti {t = tr (⌜Hom⌝ c a m) (hrefl (⌜Mu⌝ Dᵐ) s) e} (snr-J-Mu hd hs) =
  e , (snr-J-Mu (sn-anti hd) (sn-anti hs) , refl)
snr-anti {t = tr (⌜Hom⌝ c a m) (hrefl (⌜IMu⌝ Dⁱ Iⁱ iˣ) s) e} (snr-J-IMu hd hs) =
  e , (snr-J-IMu (sn-anti hd) (sn-anti hs) , refl)
snr-anti {t = tr d (hrefl ⌜Unit⌝ s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (⌜Mu⌝ Dᵐ) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl ⌜Unit⌝ s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (⌜Mu⌝ Dᵐ) s) e} (snr-trᵖ (snr-hrefl-pw ()))
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
snr-anti {t = tr (⌜Hom⌝ c a m) (⌜Mu⌝ Dᵐ) e} (snr-trᵖ ())
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
snr-anti {t = app (⌜Mu⌝ Dᵐ) u}     (snr-app ())
snr-anti {t = app (⌜Π⌝ c d) u}  (snr-app ())
snr-anti {t = app (⌜Σ⌝ c d) u}  (snr-app ())
snr-anti {t = app (⌜IMu⌝ Dⁱ Iⁱ i₉) u} (snr-app ())
snr-anti {t = fst (var x)}      (snr-fst ())
snr-anti {t = fst (lam s)}      (snr-fst ())
snr-anti {t = fst ⌜base⌝}       (snr-fst ())
snr-anti {t = fst ⌜Nat⌝}        (snr-fst ())
snr-anti {t = fst ⌜Unit⌝}       (snr-fst ())
snr-anti {t = fst (⌜Mu⌝ Dᵐ)}    (snr-fst ())
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
snr-anti {t = snd (⌜Mu⌝ Dᵐ)}    (snr-snd ())
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
snr-anti {t = tr d (hrefl (nsuc k) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d (hrefl (natrec z w n) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
-- ★ INDUCTIVE TYPES: the MOTIVE stays a variable here, as in the `natrec`
-- rows above — `trstk?` falls to `pathstk?` on a `con`/`elim` path, so it
-- does not look at the motive at all.
snr-anti {t = tr d (hrefl (con k q) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (elim D₁ ms₁ t₁) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
-- ⚠ the INDEXED code has NO J root (unlike `⌜Mu⌝`): `pathstk? (⌜IMu⌝ …)`
--   is `true`, so a `hrefl ⌜IMu⌝` path is permanently STUCK — the `⌜Nat⌝`
--   rows' shape, not `⌜Mu⌝`'s.
snr-anti {t = tr d (hrefl (icon k q) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (ielim D₁ i₁ ms₁ t₁) s) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (hrefl (⌜IMu⌝ Dⁱ Iⁱ i₉) s) e} (snr-trᵖ (snr-hreflᶜ (csr-here ())))
snr-anti {t = tr d (hrefl (⌜IMu⌝ Dⁱ Iⁱ i₉) s) e} (snr-trᵖ (snr-hrefl-pw ()))
snr-anti {t = tr d unit e} (snr-trᵖ ())
snr-anti {t = tr d nzero e} (snr-trᵖ ())
snr-anti {t = tr d (nsuc k) e} (snr-trᵖ ())
snr-anti {t = tr d (natrec z w n) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (con k q) e} (snr-trᵖ ())
snr-anti {t = tr d (elim D₁ ms₁ t₁) e} (snr-trᵖ r) with snr-anti r
... | t' , (r' , refl) = tr d t' e , (snr-trᵖ r' , refl)
snr-anti {t = tr d (icon k q) e} (snr-trᵖ ())
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

csr-anti {t = var x} (csr-here ())
csr-anti {t = unit} (csr-here ())
csr-anti {t = nzero} (csr-here ())
csr-anti {t = nsuc _} (csr-here ())
csr-anti {t = natrec z w n} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = con _ _} (csr-here ())
csr-anti {t = elim D ms t₀} (csr-here r) with snr-anti r
... | t' , (r' , refl) = t' , (csr-here r' , refl)
csr-anti {t = icon _ _} (csr-here ())
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
csr-anti {t = (⌜Mu⌝ Dᵐ) } (csr-here ())
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
sne-ren {ρ = ρ} (sne-elim {t = t₀} hm ht key) =
  sne-elim (sn-ren hm) (sn-ren ht) (trans (mustk?-ren ρ t₀) key)
sne-ren {ρ = ρ} (sne-ielim {t = t₀} hi hm ht key) =
  sne-ielim (sn-ren hi) (sn-ren hm) (sn-ren ht)
            (trans (mustk?-ren ρ t₀) key)
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

sn-ren (sn-ne n)        = sn-ne (sne-ren n)
sn-ren (sn-lam h)       = sn-lam (sn-ren h)
sn-ren (sn-pair ha hb)  = sn-pair (sn-ren ha) (sn-ren hb)
sn-ren sn-cb            = sn-cb
sn-ren sn-cNat          = sn-cNat
sn-ren sn-cUnit         = sn-cUnit
sn-ren sn-cMu           = sn-cMu
sn-ren (sn-cΠ h₁ h₂)    = sn-cΠ (sn-ren h₁) (sn-ren h₂)
sn-ren (sn-cΣ h₁ h₂)    = sn-cΣ (sn-ren h₁) (sn-ren h₂)
sn-ren (sn-cH h₁ h₂ h₃) = sn-cH (sn-ren h₁) (sn-ren h₂) (sn-ren h₃)
sn-ren (sn-cId h₁ h₂ h₃) = sn-cId (sn-ren h₁) (sn-ren h₂) (sn-ren h₃)
sn-ren (sn-idrefl h₁ h₂) = sn-idrefl (sn-ren h₁) (sn-ren h₂)
sn-ren sn-unit          = sn-unit
sn-ren sn-nzero         = sn-nzero
sn-ren (sn-nsuc h)      = sn-nsuc (sn-ren h)
sn-ren (sn-con h)       = sn-con (sn-ren h)
sn-ren (sn-icon h)      = sn-icon (sn-ren h)
sn-ren (sn-cIMu h)      = sn-cIMu (sn-ren h)
sn-ren (sn-exp r h)     = sn-exp (snr-ren r) (sn-ren h)

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
snr-ren {ρ = ρ} (snr-ι {D = D} {ms = ms} {k = k} {p = q} hm hq) =
  subst (SNRed (elim D (renTm ρ ms) (con k (renTm ρ q))))
        (sym (trans (ren-fields ρ D ms (lookupD D k) (sel k ms) q)
                    (cong (λ w → fields D (renTm ρ ms) (lookupD D k) w (renTm ρ q))
                          (ren-sel ρ k ms))))
        (snr-ι (sn-ren hm) (sn-ren hq))
snr-ren (snr-elimᵗ r)   = snr-elimᵗ (snr-ren r)
-- ★ the INDEXED ι, forward.  `ren-ifieldsⁱ` after `ren-sel`.
snr-ren {ρ = ρ} (snr-ιi {D = D} {i = i} {ms = ms} {k = k} {p = q} hi hm hq) =
  subst (SNRed (ielim D (renTm ρ i) (renTm ρ ms) (icon k (renTm ρ q))))
        (sym (trans (ren-ifieldsⁱ ρ D i ms (ilookupD D k) (sel k ms) q)
                    (cong (λ w → ifields D (renTm ρ i) (renTm ρ ms)
                                         (isingle (renTm ρ i))
                                         (ilookupD D k) w (renTm ρ q))
                          (ren-sel ρ k ms))))
        (snr-ιi (sn-ren hi) (sn-ren hm) (sn-ren hq))
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
snr-ren (snr-J-Mu hd hs)   = snr-J-Mu (sn-ren hd) (sn-ren hs)
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
