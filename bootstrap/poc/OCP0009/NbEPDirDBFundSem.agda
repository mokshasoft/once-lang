------------------------------------------------------------------------
-- OCP-0009 · W1h — `fund`, PART 2: THE SEMANTIC COMBINATORS.
--
-- Split out of NbEPDirDBFund for COMPILE TIME.  Everything `fund`
-- dispatches TO but is not itself: the `Rel` package, the ⊩-eliminator
-- combinators, the `Spine`/`snHH` machinery,
-- `semHreflPay`/`semTr`/`snTrGo`, and the code-fate analysis
-- `codeNorm`/`codeNormA`/`motFate`.
--
-- ⚠ `fund-ty` does NOT live here: its clauses sit after `fund`'s
-- signature, so the two are one MUTUAL block and cannot be separated.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBFundSem where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_; ⊥; ⊥-elim )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom; Id; Hom-cong₃; Id-cong₃; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃; ⌜Id⌝-cong₃; jsub-cong₃
        ; RTm; var; lam; app; pair; fst; snd; absurd; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap
        ; ⌜Id⌝; idrefl; jsub
        ; Unit; Nat; unit; nzero; nsuc; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝
        ; Ren; extR; renTy; renTm
        ; Sub; subTy; subTm; extS; idₛ
        ; _∘ᵣ_
        ; subTy-cong; subTm-cong
        ; subTy-renTy; subTm-renTm
        ; renTy-subTy; renTm-subTm
        ; subTy-subTy; subTm-subTm
        ; subTy-id; subTm-id; renTm-renTm; renTm-cong )
open import poc.OCP0009.NbEPDirDBType
  using ( single; nrs
        ; _⟶_; _⟶*_; done; step
        ; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ξ-fst; ξ-snd
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
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; false; occTm; subTm-occ
        ; pw?; stkC?; stkA?; pwBody; pwDom; pwShift
        ; pw?-ren; stkC?-ren; stkA?-ren; pwBody-ren; wk-ren-tm; pw?-sub
        ; stkC?→stkA?
        ; wk-sub-tm; stk⊥pw; pw⊥stk; flat?; flat→stk; flat?-sub
        ; eqv; occ-sub; occ-ren-tm; avoids-wk )
open import poc.OCP0009.NbEPDirDBSR using ( ≅ᵀ-sub; sub-comm; wk-sub )
open import poc.OCP0009.NbEPDirDBConf using ( pwShift-ren; stkC?-red; stkA?-red; subTm-monoˢ; single-mono; ⟶*-trans; ren-comm; ren-comm-ext )
open import poc.OCP0009.NbEPDirDBDec using ( Dec; dec-conv )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; confluentᵀ; church-rosserᵀ; Π-inj
        ; red→≅ᵀ; Π-reduct; Σ-reduct; mkΠRed; mkΣRed
        ; Id-reduct; ⟶ᵀ*-Homᵀ )
open import poc.OCP0009.NbEPDirDBSubj
  using ( HomΠShape; hsΠ; hsH; hom-shape; hom-shapeN; nn-U; NoNat; pw-El-decode
        ; HomRed; mkHomRed; Hom-to-Hom; homAmb→
        ; HomToΠ; via-U; via-Π; hom-to-Π
        ; U-reduct; wk-cancel-tm; ≅ᵀ-Homᵀ; gen-var; subTy-comm; subTy-monoˢ )
open import poc.OCP0009.NbEPDirDBLR
  using ( SNe; sne-var; sne-app; sne-absurd; sne-fst; sne-snd; sne-hrefl; sne-tr; sne-ap; sne-jsub
        ; Ne; ne-var; ne-app; ne-absurd; ne-fst; ne-snd; ne-hrefl; ne-tr; ne-ap; ne-jsub; homSem₁
        ; SN; sn-ne; sn-lam; sn-pair; sn-cb; sn-cΠ; sn-cΣ; sn-cH; sn-cId; sn-idrefl; sn-exp
        ; sn-cNat; sn-cUnit
        ; SNRed; snr-β; snr-βfst; snr-βsnd; snr-app; snr-fst; snr-snd
        ; snr-hreflᶜ; snr-J-base; snr-J-Σ; snr-J-Id; snr-J-Unit; snr-taut; snr-trᵖ; snr-ap-J; snr-apᵖ
        ; snr-jsub-refl; snr-jsubᵖ
        ; snr-natrec-zero; snr-natrec-suc; snr-natrecⁿ
        ; sne-natrec; ne-natrec; sn-unit; sn-nzero; sn-nsuc
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
        ; homSem₁
        ; ⟶ᵀ*-sub
        ; IsNormal; WN; mkWN; wn
        ; projl; projr; dfst; dsnd )

open import poc.OCP0009.NbEPDirDBFundSN

private
  variable
    Θ Ξ : Cx
    Γ Δ : Ctx
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
⊩₁-app (⊩₁Unit p) S h k with Π-reduct p
... | mkΠRed _ _ () _ _
⊩₁-app (⊩₁Nat p) S h k with Π-reduct p
... | mkΠRed _ _ () _ _
⊩₁-app (⊩₁Id p) S h k with Π-reduct p
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
⊩₁-fstm (⊩₁Unit p) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-fstm (⊩₁Nat p) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-fstm (⊩₁Id p) h with Σ-reduct p
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
⊩₁-sndm (⊩₁Unit p) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-sndm (⊩₁Nat p) h with Σ-reduct p
... | mkΣRed _ _ () _ _
⊩₁-sndm (⊩₁Id p) h with Σ-reduct p
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
sne→nopw (sne-absurd _ _)   = refl
sne→nopw (sne-fst n)        = sne→spine n
sne→nopw (sne-snd n)        = sne→spine n
sne→nopw (sne-hrefl _ _ _)  = refl
sne→nopw (sne-tr _ _ _ key) = key
sne→nopw (sne-ap _ _ _ key) = refl
sne→nopw (sne-jsub _ _ _ key) = key
sne→nopw (sne-natrec _ _ _ key) = key

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
snHH sp sn-cNat snt noPiT =
  sn-ne (sne-hrefl (snPlug sp sn-cNat) snt (nopw-plug sp refl))
snHH sp sn-cUnit snt noPiT =
  sn-ne (sne-hrefl (snPlug sp sn-cUnit) snt (nopw-plug sp refl))
snHH sp (sn-cΣ h₁ h₂) snt noPiT =
  sn-ne (sne-hrefl (snPlug sp (sn-cΣ h₁ h₂)) snt (nopw-plug sp refl))
snHH sp (sn-cId h₁ h₂ h₃) snt noPiT =
  sn-ne (sne-hrefl (snPlug sp (sn-cId h₁ h₂ h₃)) snt (nopw-plug sp refl))
snHH sp (sn-idrefl h₁ h₂) snt noPiT =
  sn-ne (sne-hrefl (snPlug sp (sn-idrefl h₁ h₂)) snt (nopw-plug sp refl))
snHH sp sn-unit snt noPiT =
  sn-ne (sne-hrefl (snPlug sp sn-unit) snt (nopw-plug sp refl))
snHH sp sn-nzero snt noPiT =
  sn-ne (sne-hrefl (snPlug sp sn-nzero) snt (nopw-plug sp refl))
snHH sp (sn-nsuc h) snt noPiT =
  sn-ne (sne-hrefl (snPlug sp (sn-nsuc h)) snt (nopw-plug sp refl))
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

-- ★★ WF stage C: at a `Nat` ambient the hom interp is `homNatSem`, the
-- double meta-induction — NOT a stuck `⊩₁Hom`.  But EVERY one of its
-- leaves is SN-only membership: the stuck order-hom (`⊩₁Hom`), the
-- holding inequality (`⊩₁Unit`), and the failing one (`⊩₁base`) all
-- read `SN t`, and `bwd₁` is constructor-preserving.  So SN-ness alone
-- discharges the whole tree, whatever the endpoints do.
--
-- ⚠ the `sa`/`sb` arguments must be handed on EXACTLY as `homNatSem`
-- does them (`sn-whred`, and the `sn-nsuc` match standing in for its
-- local `snsuc-inv`) or the two indices stop being definitionally
-- equal and the recursion no longer typechecks.
-- `bwd₁` only ever retargets the reduction chain, never the shape, so
-- membership is carried across unchanged — but the equation is stuck
-- until the interp's constructor is known, hence this dispatch.
mem-bwd₁ : {Γ : Cx} {X Y : RTy Γ} (q : X ⟶ᵀ* Y) (R : ⊩₁ Y) {w : RTm Γ} →
           R ⊩₁∋ w → (bwd₁ q R) ⊩₁∋ w
mem-bwd₁ q (⊩₁base _)  h = h
mem-bwd₁ q (⊩₁U _)     h = h
mem-bwd₁ q (⊩₁ne _ _)  h = h
mem-bwd₁ q (⊩₁Π _ _ _) h = h
mem-bwd₁ q (⊩₁Σ _ _ _) h = h
mem-bwd₁ q (⊩₁Hom _ _) h = h
mem-bwd₁ q (⊩₁Unit _)  h = h
mem-bwd₁ q (⊩₁Nat _)   h = h
mem-bwd₁ q (⊩₁Id _)    h = h

natHreflMem : {Γ : Cx} (a b : RTm Γ) (sa : SN a) (ma : NatMem a)
              (sb : SN b) (mb : NatMem b) {w : RTm Γ} → SN w →
              (homNatSem a b sa ma sb mb) ⊩₁∋ w
natHreflMem a b sa (nm-ne nt) sb mb h = h
natHreflMem a b sa (nm-exp {t' = a'} r ma) sb mb h =
  mem-bwd₁ (stepᵀ (ξ-Homˡ (snr→⟶ r)) doneᵀ)
           (homNatSem a' b (sn-whred sa r) ma sb mb)
           (natHreflMem a' b (sn-whred sa r) ma sb mb h)
natHreflMem .nzero b sa nm-zero sb mb h =
  mem-bwd₁ (stepᵀ (Hom-Nat-z b) doneᵀ) (⊩₁Unit doneᵀ) h
natHreflMem .(nsuc _) b sa (nm-suc ma) sb (nm-ne nt) h = h
natHreflMem .(nsuc _) b sa (nm-suc {n = m} ma) sb (nm-exp {t' = b'} r mb) h =
  mem-bwd₁ (stepᵀ (ξ-Homʳ (snr→⟶ r)) doneᵀ)
           (homNatSem (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb)
           (natHreflMem (nsuc m) b' sa (nm-suc ma) (sn-whred sb r) mb h)
natHreflMem .(nsuc _) .nzero sa (nm-suc {n = m} ma) sb nm-zero h =
  mem-bwd₁ (stepᵀ (Hom-Nat-sz m) doneᵀ) (⊩₁base doneᵀ) h
natHreflMem .(nsuc _) .(nsuc _) (sn-nsuc sa) (nm-suc {n = m} ma)
                                (sn-nsuc sb) (nm-suc {n = n} mb) h =
  mem-bwd₁ (stepᵀ (Hom-Nat-ss m n) doneᵀ)
           (homNatSem m n sa ma sb mb)
           (natHreflMem m n sa ma sb mb h)

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
-- ★ WF stage C: `Unit`/`Nat` are INERT types, so the "the decode never
-- unfolds to Π" obligation is discharged by their own normal forms —
-- the same two-liner as ⌜base⌝.
semHreflPay x₀ (⊩₀Unit p) lk snc pay snt ht =
  snHH sp-nil snc snt noPiT
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (uE , πE) with Unit-nf uE
  ...   | refl with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semHreflPay x₀ {t = t} (⊩₀Nat p) lk snc pay snt ht =
  mem-bwd₁ (⟶ᵀ*-Homᵀ p)
           (homNatSem t t (projl ht) (projr ht) (projl ht) (projr ht))
           (natHreflMem t t (projl ht) (projr ht) (projl ht) (projr ht)
                        (snHH sp-nil snc snt noPiT))
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (nE , πE) with Nat-nf nE
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
semHreflPay x₀ (⊩₀Id p) lk snc pay snt ht =
  snHH sp-nil snc snt noPiT
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (iE , πE) with Π-reduct πE
  ...   | mkΠRed _ _ refl _ _ with Id-reduct iE
  ...     | _ , (_ , (_ , ((), _)))
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
      (sym (Hom-cong₃; ordtr-cong₅ refl
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


-- ★★ SpikeNatJ: the WRAPPED fate.  `codeNorm`'s ⌜Hom⌝ case builds the
-- verdict for `⌜Hom⌝ C* a b`, whose keys are `stkA? C*` / `stableA? C*`
-- — NOT `stkC? C*` / `stablecd? C*`.  The two differ at exactly one
-- code: ⌜Nat⌝ is DEAD bare (nothing fires on a `hrefl ⌜Nat⌝ s` path)
-- and ALIVE wrapped (`⌜Hom⌝ ⌜Nat⌝ a b` IS J-able).  That one row is the
-- whole reason this second fate exists.
data CodeFateA {Ξ : Cx} (c* : RTm Ξ) : Set where
  cfa-stk  : stkA? c* ≡ true → CodeFateA c*
  cfa-dead : stableA? c* ≡ true → CodeFateA c*

codeNormA : {c' : RTm Ξ} → SN c' → nopw? c' ≡ true →
            Σ (RTm Ξ) (λ c* → (c' ⟶csr* c*) × CodeFateA c*)
codeNormA (sn-exp r h) kn with codeNormA h (nopw?-red (snr→⟶ r) kn)
... | c* , (csr , fate) = c* , (csr-step (csr-here r) csr , fate)
codeNormA (sn-ne n) kn = _ , (csr-done , cfa-dead (sne→stableA n))
codeNormA (sn-lam h) kn = _ , (csr-done , cfa-dead refl)
codeNormA (sn-pair ha hb) kn = _ , (csr-done , cfa-dead refl)
codeNormA sn-cb kn = _ , (csr-done , cfa-stk refl)
codeNormA sn-cUnit kn = _ , (csr-done , cfa-stk refl)
-- ★ THE row.  `codeNorm` sends this one to `cf-dead`.
codeNormA sn-cNat kn = _ , (csr-done , cfa-stk refl)
codeNormA (sn-cΣ h₁ h₂) kn = _ , (csr-done , cfa-stk refl)
codeNormA (sn-cId h₁ h₂ h₃) kn = _ , (csr-done , cfa-stk refl)
codeNormA (sn-idrefl h₁ h₂) kn = _ , (csr-done , cfa-dead refl)
codeNormA sn-unit kn      = _ , (csr-done , cfa-dead refl)
codeNormA sn-nzero kn     = _ , (csr-done , cfa-dead refl)
codeNormA (sn-nsuc h) kn  = _ , (csr-done , cfa-dead refl)
codeNormA (sn-cΠ h₁ h₂) ()
codeNormA (sn-cH {a = a₂} {b = b₂} hC ha hb) kn with codeNormA hC kn
... | C* , (csr , cfa-stk k)  =
      ⌜Hom⌝ C* a₂ b₂ , (csrs-homA csr , cfa-stk k)
  where
  csrs-homA : {x y : RTm _} → x ⟶csr* y →
              ⌜Hom⌝ x a₂ b₂ ⟶csr* ⌜Hom⌝ y a₂ b₂
  csrs-homA csr-done       = csr-done
  csrs-homA (csr-step σ q) = csr-step (csr-hom σ) (csrs-homA q)
... | C* , (csr , cfa-dead k) =
      ⌜Hom⌝ C* a₂ b₂ , (csrs-homA csr , cfa-dead k)
  where
  csrs-homA : {x y : RTm _} → x ⟶csr* y →
              ⌜Hom⌝ x a₂ b₂ ⟶csr* ⌜Hom⌝ y a₂ b₂
  csrs-homA csr-done       = csr-done
  csrs-homA (csr-step σ q) = csr-step (csr-hom σ) (csrs-homA q)

codeNorm : {c' : RTm Ξ} → SN c' → nopw? c' ≡ true →
           Σ (RTm Ξ) (λ c* → (c' ⟶csr* c*) × CodeFate c*)
codeNorm (sn-exp r h) kn with codeNorm h (nopw?-red (snr→⟶ r) kn)
... | c* , (csr , fate) = c* , (csr-step (csr-here r) csr , fate)
codeNorm (sn-ne n) kn = _ , (csr-done , cf-dead (sne→stablecd n))
codeNorm (sn-lam h) kn = _ , (csr-done , cf-dead refl)
codeNorm (sn-pair ha hb) kn = _ , (csr-done , cf-dead refl)
codeNorm sn-cb kn = _ , (csr-done , cf-stk refl)
codeNorm sn-cUnit kn = _ , (csr-done , cf-stk refl)
-- ★★ the THIRD code kind: ⌜Nat⌝ is neither `pw?` nor `stkC?`.  It is
-- however DEAD (nothing fires on a `hrefl ⌜Nat⌝` path since the
-- retraction), so it lands in `cf-dead` and `CodeFate` stays two-way.
codeNorm sn-cNat kn = _ , (csr-done , cf-dead refl)
codeNorm (sn-cΣ h₁ h₂) kn = _ , (csr-done , cf-stk refl)
codeNorm (sn-cId h₁ h₂ h₃) kn = _ , (csr-done , cf-stk refl)
codeNorm (sn-idrefl h₁ h₂) kn = _ , (csr-done , cf-dead refl)
codeNorm sn-unit kn      = _ , (csr-done , cf-dead refl)
codeNorm sn-nzero kn     = _ , (csr-done , cf-dead refl)
codeNorm (sn-nsuc h) kn  = _ , (csr-done , cf-dead refl)
codeNorm (sn-cΠ h₁ h₂) ()
codeNorm (sn-cH {a = a₂} {b = b₂} hC ha hb) kn with codeNormA hC kn
... | C* , (csr , cfa-stk k)  =
      ⌜Hom⌝ C* a₂ b₂ , (csrs-hom' csr , cf-stk k)
  where
  csrs-hom' : {x y : RTm _} → x ⟶csr* y →
              ⌜Hom⌝ x a₂ b₂ ⟶csr* ⌜Hom⌝ y a₂ b₂
  csrs-hom' csr-done       = csr-done
  csrs-hom' (csr-step σ q) = csr-step (csr-hom σ) (csrs-hom' q)
... | C* , (csr , cfa-dead k) =
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


------------------------------------------------------------------------
-- ★★ W2b, THE LAST HOLE — `semTr`: the pointwise-transport membership,
-- a go-REPLICA at level 0, parameterized by layer.  The strengthening
-- collapse (the motive's binder form is `renTm vs` of the strengthened
-- code) and the pwShift collapse (pwShift ∘ extR vs ≡ vs) make each
-- layer's recursion invariant DEFINITIONAL; the payload node supplies
-- the spine-normalization, the pw-key, and the body data; the path's
-- own Π-closure supplies the instantiated inner paths.
------------------------------------------------------------------------

csrs-det : {c x y : RTm Ξ} → c ⟶csr* x → pw? x ≡ true →
           c ⟶csr* y → pw? y ≡ true → x ≡ y
csrs-det csr-done kx csr-done ky = refl
csrs-det csr-done kx (csr-step σ q) ky =
  ⊥-elim (f≢t (trans (sym (csr-nonpw σ)) kx))
csrs-det (csr-step σ q) kx csr-done ky =
  ⊥-elim (f≢t (trans (sym (csr-nonpw σ)) ky))
csrs-det (csr-step σ q) kx (csr-step σ' q') ky with csr-det σ σ'
... | refl = csrs-det q kx q' ky

csrs-ren : {ρ : Ren Θ Ξ} {x y : RTm Θ} → x ⟶csr* y →
           renTm ρ x ⟶csr* renTm ρ y
csrs-ren csr-done       = csr-done
csrs-ren (csr-step σ q) = csr-step (csr-ren σ) (csrs-ren q)

mem₀cast : {A B : RTy Ξ} (eq : A ≡ B) (R : ⊩₀ A) {w : RTm Ξ} →
           R ⊩₀∋ w → (subst ⊩₀_ eq R) ⊩₀∋ w
mem₀cast refl R h = h

mem₀cast⁻ : {A B : RTy Ξ} (eq : A ≡ B) (R : ⊩₀ A) {w : RTm Ξ} →
            (subst ⊩₀_ eq R) ⊩₀∋ w → R ⊩₀∋ w
mem₀cast⁻ refl R h = h

mem₁cast⁻ : {A B : RTy Ξ} (eq : A ≡ B) (R : ⊩₁ A) {w : RTm Ξ} →
            (subst ⊩₁_ eq R) ⊩₁∋ w → R ⊩₁∋ w
mem₁cast⁻ refl R h = h

memTm : {A : RTy Ξ} (R : ⊩₀ A) {w w' : RTm Ξ} → w ≡ w' →
        R ⊩₀∋ w → R ⊩₀∋ w'
memTm R refl h = h

expStar₀ : {A : RTy Ξ} (R : ⊩₀ A) {t t' : RTm Ξ} →
           t ⟶snr* t' → R ⊩₀∋ t' → R ⊩₀∋ t
expStar₀ R snr-done       h = h
expStar₀ R (snr-step r q) h = exp₀ R r (expStar₀ R q h)

-- the pwShift collapse: after strengthening, the junk slot vanishes.
pwvs : {X : RTm (Θ ∙)} → renTm pwShift (renTm (extR vs) X) ≡ renTm vs X
pwvs {X = X} = trans (renTm-renTm X) (renTm-cong ptw X)
  where
  ptw : ∀ x → _
  ptw vz     = refl
  ptw (vs i) = refl

semTr :
  (x₀ : Var Ξ) {X : RTy Ξ} (R : ⊩₀ X) {CT : RTm Ξ}
  (lk : X ≅ᵀ El CT) (snCT : SN CT) (payR : PayT R CT)
  {aP tP uP : RTm Ξ}
  (hA : R ⊩₀∋ aP) (hT : R ⊩₀∋ tP) (hU : R ⊩₀∋ uP)
  {p' : RTm Ξ} (snp : SN p')
  (hTe : (emb R) ⊩₁∋ tP) (hUe : (emb R) ⊩₁∋ uP)
  (hp : (homSem₁ (emb R) hTe hUe) ⊩₁∋ p')
  {eP : RTm Ξ} (hE : (homSem₀ R hA hT) ⊩₀∋ eP) →
  (homSem₀ R hA hU) ⊩₀∋
    tr (⌜Hom⌝ (renTm vs CT) (renTm vs aP) (var vz)) p' eP

snrs-trans : {t u v : RTm Ξ} → t ⟶snr* u → u ⟶snr* v → t ⟶snr* v
snrs-trans snr-done       q = q
snrs-trans (snr-step r p) q = snr-step r (snrs-trans p q)

csrs-app : {t u v : RTm Ξ} → t ⟶csr* u → u ⟶csr* v → t ⟶csr* v
csrs-app csr-done       q = q
csrs-app (csr-step σ p) q = csr-step σ (csrs-app p q)

-- the MOTIVE-code fate: fully normalize down CSR (recursing into
-- hrefl-codes' own codes — a live inner code either unfolds the hrefl
-- to a lam, dead, or the whole hrefl is dead with it).
data MFate {Ξ : Cx} (c* : RTm Ξ) : Set where
  mf-pw   : pw? c* ≡ true → MFate c*
  mf-dead : deadmot? c* ≡ true → MFate c*

motFate : {c' : RTm Ξ} → SN c' →
          Σ (RTm Ξ) (λ c* → (c' ⟶csr* c*) × MFate c*)
motFate (sn-exp r h) with motFate h
... | c* , (csr , fate) = c* , (csr-step (csr-here r) csr , fate)
motFate (sn-ne (sne-var x)) = _ , (csr-done , mf-dead refl)
motFate (sn-ne (sne-app n s)) = _ , (csr-done , mf-dead (sne→spine n))
motFate (sn-ne (sne-absurd _ _)) = _ , (csr-done , mf-dead refl)
motFate (sn-ne (sne-fst n)) = _ , (csr-done , mf-dead (sne→spine n))
motFate (sn-ne (sne-snd n)) = _ , (csr-done , mf-dead (sne→spine n))
motFate (sn-ne (sne-hrefl {c = c₂} {t = t₂} snc snt kn)) with motFate snc
... | C₃ , (csr₃ , mf-pw k) =
      lam (hrefl (pwBody C₃) (app (renTm vs t₂) (var vz)))
      , ( csrs-app (hrmap csr₃)
                   (csr-step (csr-here (snr-hrefl-pw k)) csr-done)
        , mf-dead refl )
  where
  hrmap : {x y : RTm _} → x ⟶csr* y → hrefl x t₂ ⟶csr* hrefl y t₂
  hrmap csr-done       = csr-done
  hrmap (csr-step σ w) = csr-step (csr-here (snr-hreflᶜ σ)) (hrmap w)
... | C₃ , (csr₃ , mf-dead k) =
      hrefl C₃ t₂ , (hrmap csr₃ , mf-dead k)
  where
  hrmap : {x y : RTm _} → x ⟶csr* y → hrefl x t₂ ⟶csr* hrefl y t₂
  hrmap csr-done       = csr-done
  hrmap (csr-step σ w) = csr-step (csr-here (snr-hreflᶜ σ)) (hrmap w)
motFate (sn-ne (sne-tr h₁ h₂ h₃ key)) = _ , (csr-done , mf-dead key)
motFate (sn-ne (sne-ap h₁ h₂ h₃ key)) = _ , (csr-done , mf-dead key)
motFate (sn-ne (sne-jsub h₁ h₂ h₃ key)) = _ , (csr-done , mf-dead key)
motFate (sn-ne (sne-natrec h₁ h₂ h₃ key)) = _ , (csr-done , mf-dead key)
motFate (sn-lam h) = _ , (csr-done , mf-dead refl)
motFate (sn-pair a b) = _ , (csr-done , mf-dead refl)
motFate sn-cb = _ , (csr-done , mf-dead refl)
motFate sn-cNat = _ , (csr-done , mf-dead refl)
motFate sn-cUnit = _ , (csr-done , mf-dead refl)
motFate (sn-cΠ h₁ h₂) = _ , (csr-done , mf-pw refl)
motFate (sn-cΣ h₁ h₂) = _ , (csr-done , mf-dead refl)
motFate (sn-cId h₁ h₂ h₃) = _ , (csr-done , mf-dead refl)
motFate (sn-idrefl h₁ h₂) = _ , (csr-done , mf-dead refl)
motFate sn-unit     = _ , (csr-done , mf-dead refl)
motFate sn-nzero    = _ , (csr-done , mf-dead refl)
motFate (sn-nsuc h) = _ , (csr-done , mf-dead refl)
motFate (sn-cH {c = C₂} {a = a₂} {b = b₂} hC ha hb) with motFate hC
... | C* , (csr , mf-pw k)   = ⌜Hom⌝ C* a₂ b₂ , (csrs-hom csr , mf-pw k)
... | C* , (csr , mf-dead k) = ⌜Hom⌝ C* a₂ b₂ , (csrs-hom csr , mf-dead k)

-- the SN-only worker (the non-Π interps' membership IS this SN).
snTrGo :
  {CT aP eP : RTm Ξ} →
  (∀ {P : RTy Ξ} {Q : RTy (Ξ ∙)} → El CT ⟶ᵀ* Π P Q → ⊥) →
  SN CT → SN aP → SN eP →
  {p' : RTm Ξ} → SN p' →
  SN (tr (⌜Hom⌝ (renTm vs CT) (renTm vs aP) (var vz)) p' eP)
snTrGo {Ξ = Ξ} {CT = CT} {aP} {eP} noPiT snCT snA snE = go'
  where
  M : RTm (Ξ ∙)
  M = ⌜Hom⌝ (renTm vs CT) (renTm vs aP) (var vz)
  snM : SN M
  snM = sn-cH (sn-ren snCT) (sn-ren snA) (sn-ne (sne-var vz))

  tstar : {p₁ p₂ : RTm Ξ} → p₁ ⟶snr* p₂ → tr M p₁ eP ⟶snr* tr M p₂ eP
  tstar snr-done       = snr-done
  tstar (snr-step r q) = snr-step (snr-trᵖ r) (tstar q)

  mstar : {x y : RTm Ξ} → x ⟶csr* y → {f : RTm (Ξ ∙)} →
          tr (⌜Hom⌝ (renTm vs x) (renTm vs aP) (var vz)) (lam f) eP ⟶snr*
          tr (⌜Hom⌝ (renTm vs y) (renTm vs aP) (var vz)) (lam f) eP
  mstar csr-done       = snr-done
  mstar (csr-step σ w) = snr-step (snr-tr-mot (csr-ren σ)) (mstar w)

  go' : {p' : RTm Ξ} → SN p' → SN (tr M p' eP)
  goH : {c' s' : RTm Ξ} → SN c' → SN s' → nopw? c' ≡ true →
        SN (tr M (hrefl c' s') eP)

  go' (sn-exp r h) = sn-exp (snr-trᵖ r) (go' h)
  go' (sn-ne (sne-var x)) =
    sn-ne (sne-tr snM (sn-ne (sne-var x)) snE refl)
  go' (sn-ne (sne-app n s)) =
    sn-ne (sne-tr snM (sn-ne (sne-app n s)) snE (sne→spine n))
  go' (sn-ne w@(sne-absurd _ _)) =
    sn-ne (sne-tr snM (sn-ne w) snE refl)
  go' (sn-ne (sne-fst n)) =
    sn-ne (sne-tr snM (sn-ne (sne-fst n)) snE (sne→spine n))
  go' (sn-ne (sne-snd n)) =
    sn-ne (sne-tr snM (sn-ne (sne-snd n)) snE (sne→spine n))
  go' (sn-ne (sne-hrefl snc sns kn)) = goH snc sns kn
  go' (sn-ne (sne-tr h₁ h₂ h₃ key)) =
    sn-ne (sne-tr snM (sn-ne (sne-tr h₁ h₂ h₃ key)) snE key)
  go' (sn-ne (sne-ap h₁ h₂ h₃ key)) =
    sn-ne (sne-tr snM (sn-ne (sne-ap h₁ h₂ h₃ key)) snE key)
  go' (sn-ne (sne-jsub h₁ h₂ h₃ key)) =
    sn-ne (sne-tr snM (sn-ne (sne-jsub h₁ h₂ h₃ key)) snE key)
  go' (sn-ne (sne-natrec h₁ h₂ h₃ key)) =
    sn-ne (sne-tr snM (sn-ne (sne-natrec h₁ h₂ h₃ key)) snE key)
  go' (sn-lam snf) with motFate snCT
  ... | CT* , (csr , mf-pw k) =
        ⊥-elim (noPiT (⟶ᵀ*-trans (⟶ᵀ*-El (csrs→⟶* csr))
                        (Σ.fst (Σ.snd (pw-El-decode CT* k)))))
  ... | CT* , (csr , mf-dead k) =
        snExpStar (mstar csr)
          (sn-ne (sne-tr (sn-cH (sn-ren (sn-csrs snCT csr)) (sn-ren snA)
                                (sn-ne (sne-var vz)))
                         (sn-lam snf) snE
                         (trans (deadmot?-ren vs CT*) k)))
  go' (sn-pair a b)    = sn-ne (sne-tr snM (sn-pair a b) snE refl)
  go' sn-cb            = sn-ne (sne-tr snM sn-cb snE refl)
  go' sn-cNat            = sn-ne (sne-tr snM sn-cNat snE refl)
  go' sn-cUnit            = sn-ne (sne-tr snM sn-cUnit snE refl)
  go' (sn-cΠ h₁ h₂)    = sn-ne (sne-tr snM (sn-cΠ h₁ h₂) snE refl)
  go' (sn-cΣ h₁ h₂)    = sn-ne (sne-tr snM (sn-cΣ h₁ h₂) snE refl)
  go' (sn-cH h₁ h₂ h₃) = sn-ne (sne-tr snM (sn-cH h₁ h₂ h₃) snE refl)
  go' (sn-cId h₁ h₂ h₃) = sn-ne (sne-tr snM (sn-cId h₁ h₂ h₃) snE refl)
  go' (sn-idrefl h₁ h₂) = sn-ne (sne-tr snM (sn-idrefl h₁ h₂) snE refl)
  go' sn-unit           = sn-ne (sne-tr snM sn-unit snE refl)
  go' sn-nzero          = sn-ne (sne-tr snM sn-nzero snE refl)
  go' (sn-nsuc h)       = sn-ne (sne-tr snM (sn-nsuc h) snE refl)

  goH sn-cb sns kn = sn-exp (snr-J-base snM sns) snE
  goH sn-cUnit sns kn = sn-exp (snr-J-Unit snM sns) snE
  -- ★★ J is OFF at ⌜Nat⌝, so this configuration is permanently stuck —
  -- i.e. NEUTRAL.  `stablecd? ⌜Nat⌝ = true` is exactly the key that
  -- lets `sne-tr` accept it.
  goH sn-cNat sns kn =
    sn-ne (sne-tr snM (sn-ne (sne-hrefl sn-cNat sns refl)) snE refl)
  goH (sn-cΣ h₁ h₂) sns kn = sn-exp (snr-J-Σ snM h₁ h₂ sns) snE
  goH (sn-cId h₁ h₂ h₃) sns kn = sn-exp (snr-J-Id snM h₁ h₂ h₃ sns) snE
  goH (sn-idrefl h₁ h₂) sns kn =
    sn-ne (sne-tr snM (sn-ne (sne-hrefl (sn-idrefl h₁ h₂) sns refl)) snE refl)
  goH (sn-exp rc snc') sns kn =
    sn-exp (snr-trᵖ (snr-hreflᶜ (csr-here rc)))
           (goH snc' sns (nopw?-red (snr→⟶ rc) kn))
  goH (sn-ne nc) sns kn =
    sn-ne (sne-tr snM (sn-ne (sne-hrefl (sn-ne nc) sns (sne→nopw nc)))
                  snE (sne→stablecd nc))
  goH (sn-lam h) sns kn =
    sn-ne (sne-tr snM (sn-ne (sne-hrefl (sn-lam h) sns refl)) snE refl)
  goH (sn-pair a b) sns kn =
    sn-ne (sne-tr snM (sn-ne (sne-hrefl (sn-pair a b) sns refl)) snE refl)
  goH sn-unit sns kn =
    sn-ne (sne-tr snM (sn-ne (sne-hrefl sn-unit sns refl)) snE refl)
  goH sn-nzero sns kn =
    sn-ne (sne-tr snM (sn-ne (sne-hrefl sn-nzero sns refl)) snE refl)
  goH (sn-nsuc h) sns kn =
    sn-ne (sne-tr snM (sn-ne (sne-hrefl (sn-nsuc h) sns refl)) snE refl)
  goH (sn-cΠ h₁ h₂) sns ()
  goH (sn-cH hC h₂ h₃) sns kn with codeNormA hC kn
  ... | C*c , (csr , cfa-stk k) =
        snExpStar (tstar (snrs-hreflᶜ (csrs-hom csr)))
          (sn-exp (snr-J-Hom snM (sn-csrs hC csr) h₂ h₃ sns k) snE)
  ... | C*c , (csr , cfa-dead k) =
        snExpStar (tstar (snrs-hreflᶜ (csrs-hom csr)))
          (sn-ne (sne-tr snM
                   (sn-ne (sne-hrefl (sn-cH (sn-csrs hC csr) h₂ h₃) sns
                                     (nopw?-csrs csr kn)))
                   snE k))

semTr x₀ (⊩₀base p) lk snCT payR hA hT hU snp hTe hUe hp hE =
  snTrGo noPiT snCT (CR1₀ (⊩₀base p) hA)
         (CR1₀ (homSem₀ (⊩₀base p) hA hT) hE) snp
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (bE , πE) with base-nf bE
  ...   | refl with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semTr x₀ (⊩₀Unit p) lk snCT payR hA hT hU snp hTe hUe hp hE =
  snTrGo noPiT snCT (CR1₀ (⊩₀Unit p) hA)
         (CR1₀ (homSem₀ (⊩₀Unit p) hA hT) hE) snp
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (uE , πE) with Unit-nf uE
  ...   | refl with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
-- ★★ at a `Nat` ambient `homSem₀` is `homNatSem₀`, whose membership is
-- ENDPOINT-BLIND (`hns₀-in`) — SN-ness is the whole obligation, so the
-- generic `snTrGo` still does all the work; it just has to be threaded
-- through the order-hom wrapper instead of landing on a `⊩₀Hom`.
semTr x₀ (⊩₀Nat p) lk snCT payR {aP} {tP} {uP} hA hT hU snp hTe hUe hp hE =
  bwd₀-mem⁻ (⟶ᵀ*-Homᵀ p)
    (homNatSem₀ aP uP (projl hA) (projr hA) (projl hU) (projr hU))
    (hns₀-in aP uP (projl hA) (projr hA) (projl hU) (projr hU)
       (snTrGo noPiT snCT (CR1₀ (⊩₀Nat p) hA)
               (CR1₀ (homSem₀ (⊩₀Nat p) hA hT) hE) snp))
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (nE , πE) with Nat-nf nE
  ...   | refl with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semTr x₀ (⊩₀ne p n) lk snCT payR hA hT hU snp hTe hUe hp hE =
  snTrGo noPiT snCT (CR1₀ (⊩₀ne p n) hA)
         (CR1₀ (homSem₀ (⊩₀ne p n) hA hT) hE) snp
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (nE , πE) with El-ne-reduct n nE
  ...   | mkElNe _ _ refl with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semTr x₀ (⊩₀Σ p ⊩F ⊩G) lk snCT payR hA hT hU snp hTe hUe hp hE =
  snTrGo noPiT snCT (CR1₀ (⊩₀Σ p ⊩F ⊩G) hA)
         (CR1₀ (homSem₀ (⊩₀Σ p ⊩F ⊩G) hA hT) hE) snp
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (σE , πE) with Σ-reduct σE
  ...   | mkΣRed _ _ refl _ _ with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semTr x₀ (⊩₀Hom p sh) lk snCT payR hA hT hU snp hTe hUe hp hE =
  snTrGo noPiT snCT (CR1₀ (⊩₀Hom p sh) hA)
         (CR1₀ (homSem₀ (⊩₀Hom p sh) hA hT) hE) snp
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (hE₂ , πE) with Hom-stk-reduct sh hE₂
  ...   | mkHomStk _ _ _ _ refl with Π-reduct πE
  ...     | mkΠRed _ _ () _ _
semTr x₀ (⊩₀Id p) lk snCT payR hA hT hU snp hTe hUe hp hE =
  snTrGo noPiT snCT (CR1₀ (⊩₀Id p) hA)
         (CR1₀ (homSem₀ (⊩₀Id p) hA hT) hE) snp
  where
  noPiT : ∀ {P Q} → El _ ⟶ᵀ* Π P Q → ⊥
  noPiT ch with church-rosserᵀ
                 (ctrnᵀ (csymᵀ (red→≅ᵀ p)) (ctrnᵀ lk (red→≅ᵀ ch)))
  ... | E , (iE₂ , πE) with Π-reduct πE
  ...   | mkΠRed _ _ refl _ _ with Id-reduct iE₂
  ...     | _ , (_ , (_ , ((), _)))
semTr x₀ {X = X} (⊩₀Π {F = F} {G = G} q Fc Gc) {CT = CT} lk snCT payR
      {aP} {tP} {uP} hA hT hU {p'} snp hTe hUe hp {eP} hE = go₀ snp hp
  where
  RcΠ = ⊩₀Π {A = X} q Fc Gc
  M : RTm (_ ∙)
  M = ⌜Hom⌝ (renTm vs CT) (renTm vs aP) (var vz)
  snA  = CR1₀ RcΠ hA
  snE' = CR1₀ (homSem₀ RcΠ hA hT) hE
  RH0  = homSem₀ RcΠ hA hU
  snM : SN M
  snM = sn-cH (sn-ren snCT) (sn-ren snA) (sn-ne (sne-var vz))

  heU : RH0 ⊩₀∋ eP
  heU = homSem₀-mem-endpoints RcΠ hA hT hA hU hE

  tstar : {p₁ p₂ : RTm _} → p₁ ⟶snr* p₂ → tr M p₁ eP ⟶snr* tr M p₂ eP
  tstar snr-done       = snr-done
  tstar (snr-step r w) = snr-step (snr-trᵖ r) (tstar w)

  -- the x₀-node pins the (unique) spine-normalization of CT.
  r₀ = CR3₀ Fc (sne-var x₀)
  n₀ = payR (var x₀) r₀
  cT*  = Σ.fst n₀
  csr₀ = Σ.fst (Σ.snd n₀)
  key₀ = Σ.fst (Σ.snd (Σ.snd n₀))

  go₀  : {pʹ : RTm _} → SN pʹ →
         (homSem₁ (emb RcΠ) hTe hUe) ⊩₁∋ pʹ → RH0 ⊩₀∋ tr M pʹ eP
  goH₀ : {c' s' : RTm _} → SN c' → SN s' → nopw? c' ≡ true →
         RH0 ⊩₀∋ tr M (hrefl c' s') eP
  pwC  : {f : RTm (_ ∙)} → SN f →
         (homSem₁ (emb RcΠ) hTe hUe) ⊩₁∋ lam f → RH0 ⊩₀∋ tr M (lam f) eP

  go₀ (sn-exp r h) hpʹ =
    exp₀ RH0 (snr-trᵖ r) (go₀ h (mem-whred₁ (homSem₁ (emb RcΠ) hTe hUe) r hpʹ))
  go₀ (sn-ne (sne-var x)) hpʹ =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-var x)) snE' refl)
  go₀ (sn-ne (sne-app n s)) hpʹ =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-app n s)) snE' (sne→spine n))
  go₀ (sn-ne w@(sne-absurd _ _)) hpʹ =
    CR3₀ RH0 (sne-tr snM (sn-ne w) snE' refl)
  go₀ (sn-ne (sne-fst n)) hpʹ =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-fst n)) snE' (sne→spine n))
  go₀ (sn-ne (sne-snd n)) hpʹ =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-snd n)) snE' (sne→spine n))
  go₀ (sn-ne (sne-hrefl snc sns kn)) hpʹ = goH₀ snc sns kn
  go₀ (sn-ne (sne-tr h₁ h₂ h₃ key)) hpʹ =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-tr h₁ h₂ h₃ key)) snE' key)
  go₀ (sn-ne (sne-ap h₁ h₂ h₃ key)) hpʹ =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-ap h₁ h₂ h₃ key)) snE' key)
  go₀ (sn-ne (sne-jsub h₁ h₂ h₃ key)) hpʹ =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-jsub h₁ h₂ h₃ key)) snE' key)
  go₀ (sn-ne (sne-natrec h₁ h₂ h₃ key)) hpʹ =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-natrec h₁ h₂ h₃ key)) snE' key)
  go₀ (sn-lam snf) hpʹ = pwC snf hpʹ
  go₀ (sn-pair a b) hpʹ    = CR3₀ RH0 (sne-tr snM (sn-pair a b) snE' refl)
  go₀ sn-cb hpʹ            = CR3₀ RH0 (sne-tr snM sn-cb snE' refl)
  go₀ sn-cNat hpʹ            = CR3₀ RH0 (sne-tr snM sn-cNat snE' refl)
  go₀ sn-cUnit hpʹ            = CR3₀ RH0 (sne-tr snM sn-cUnit snE' refl)
  go₀ (sn-cΠ h₁ h₂) hpʹ    = CR3₀ RH0 (sne-tr snM (sn-cΠ h₁ h₂) snE' refl)
  go₀ (sn-cΣ h₁ h₂) hpʹ    = CR3₀ RH0 (sne-tr snM (sn-cΣ h₁ h₂) snE' refl)
  go₀ (sn-cH h₁ h₂ h₃) hpʹ = CR3₀ RH0 (sne-tr snM (sn-cH h₁ h₂ h₃) snE' refl)
  go₀ (sn-cId h₁ h₂ h₃) hpʹ = CR3₀ RH0 (sne-tr snM (sn-cId h₁ h₂ h₃) snE' refl)
  go₀ (sn-idrefl h₁ h₂) hpʹ = CR3₀ RH0 (sne-tr snM (sn-idrefl h₁ h₂) snE' refl)
  go₀ sn-unit hpʹ      = CR3₀ RH0 (sne-tr snM sn-unit snE' refl)
  go₀ sn-nzero hpʹ     = CR3₀ RH0 (sne-tr snM sn-nzero snE' refl)
  go₀ (sn-nsuc h) hpʹ  = CR3₀ RH0 (sne-tr snM (sn-nsuc h) snE' refl)

  goH₀ sn-cb sns kn = exp₀ RH0 (snr-J-base snM sns) heU
  goH₀ sn-cUnit sns kn = exp₀ RH0 (snr-J-Unit snM sns) heU
  goH₀ sn-cNat sns kn =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-hrefl sn-cNat sns refl)) snE' refl)
  goH₀ (sn-cΣ h₁ h₂) sns kn = exp₀ RH0 (snr-J-Σ snM h₁ h₂ sns) heU
  goH₀ (sn-cId h₁ h₂ h₃) sns kn = exp₀ RH0 (snr-J-Id snM h₁ h₂ h₃ sns) heU
  goH₀ (sn-idrefl h₁ h₂) sns kn =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-hrefl (sn-idrefl h₁ h₂) sns refl)) snE' refl)
  goH₀ (sn-exp rc snc') sns kn =
    exp₀ RH0 (snr-trᵖ (snr-hreflᶜ (csr-here rc)))
         (goH₀ snc' sns (nopw?-red (snr→⟶ rc) kn))
  goH₀ (sn-ne nc) sns kn =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-hrefl (sn-ne nc) sns (sne→nopw nc)))
                     snE' (sne→stablecd nc))
  goH₀ (sn-lam h) sns kn =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-hrefl (sn-lam h) sns refl)) snE' refl)
  goH₀ (sn-pair a b) sns kn =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-hrefl (sn-pair a b) sns refl)) snE' refl)
  goH₀ sn-unit sns kn =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-hrefl sn-unit sns refl)) snE' refl)
  goH₀ sn-nzero sns kn =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-hrefl sn-nzero sns refl)) snE' refl)
  goH₀ (sn-nsuc h) sns kn =
    CR3₀ RH0 (sne-tr snM (sn-ne (sne-hrefl (sn-nsuc h) sns refl)) snE' refl)
  goH₀ (sn-cΠ h₁ h₂) sns ()
  goH₀ (sn-cH hC h₂ h₃) sns kn with codeNormA hC kn
  ... | C*c , (csr , cfa-stk k) =
        expStar₀ RH0 (tstar (snrs-hreflᶜ (csrs-hom csr)))
          (exp₀ RH0 (snr-J-Hom snM (sn-csrs hC csr) h₂ h₃ sns k) heU)
  ... | C*c , (csr , cfa-dead k) =
        expStar₀ RH0 (tstar (snrs-hreflᶜ (csrs-hom csr)))
          (CR3₀ RH0 (sne-tr snM
                      (sn-ne (sne-hrefl (sn-cH (sn-csrs hC csr) h₂ h₃) sns
                                        (nopw?-csrs csr kn)))
                      snE' k))

  -- ★ the pointwise case: the payload node fires the strategy, the
  -- collapse equalities make the β-instances line up definitionally,
  -- and the recursion descends one interp layer per Π.
  pwC {f = f} snf hpf = expStar₀ RH0 chainAll memLam
    where
    cS* = renTm vs cT*
    BODYt : RTm (_ ∙)
    BODYt = tr (⌜Hom⌝ (renTm pwShift (pwBody cS*))
                      (app (renTm vs (renTm vs aP)) (var (vs vz)))
                      (var vz))
               f (app (renTm vs eP) (var vz))
    LAMt = lam BODYt

    mstar : {x y : RTm _} → x ⟶csr* y →
            tr (⌜Hom⌝ (renTm vs x) (renTm vs aP) (var vz)) (lam f) eP
              ⟶snr*
            tr (⌜Hom⌝ (renTm vs y) (renTm vs aP) (var vz)) (lam f) eP
    mstar csr-done       = snr-done
    mstar (csr-step σ w) = snr-step (snr-tr-mot (csr-ren σ)) (mstar w)

    chainAll : tr M (lam f) eP ⟶snr* LAMt
    chainAll =
      snrs-trans (mstar csr₀)
        (snr-step (snr-tr-pw (sn-ren (sn-csrs snCT csr₀)) (sn-ren snA)
                             (trans (pw?-ren vs cT*) key₀))
                  snr-done)

    bodyEq : (v : RTm _) →
      subTm (single v) BODYt
      ≡ tr (⌜Hom⌝ (renTm vs (subTm (single v) (pwBody cT*)))
                  (renTm vs (app aP v)) (var vz))
           (subTm (single v) f) (app eP v)
    bodyEq v =
      tr-cong₃
        (⌜Hom⌝-cong₃
          (trans (cong (subTm (extS (single v)))
                       (trans (cong (renTm pwShift) (pwBody-ren vs cT* key₀))
                              pwvs))
                 (wk-sub-tm (single v) (pwBody cT*)))
          (cong₂ app (trans (wk-sub-tm (single v) (renTm vs aP))
                            (cong (renTm vs) (wk-cancel-tm v aP)))
                     refl)
          refl)
        refl
        (cong₂ app (wk-cancel-tm v eP) refl)

    bodyLk : (v : RTm _) →
             subTy (single v) G ≅ᵀ El (subTm (single v) (pwBody cT*))
    bodyLk v =
      ctrnᵀ (≅ᵀ-sub (single v)
              (Σ.snd (Π-inj
                (ctrnᵀ (csymᵀ (red→≅ᵀ q))
                  (ctrnᵀ lk
                    (red→≅ᵀ
                      (⟶ᵀ*-trans (⟶ᵀ*-El (csrs→⟶* csr₀))
                        (Σ.fst (Σ.snd (pw-El-decode cT* key₀))))))))))
            (csymᵀ (≅ᵀ-sub (single v)
              (red→≅ᵀ (Σ.snd (Σ.snd (pw-El-decode cT* key₀))))))

    inner : (v : RTm _) (r : Fc ⊩₀∋ v) →
            (homSem₀ (Gc v r) (projr hA v r) (projr hU v r)) ⊩₀∋
              tr (⌜Hom⌝ (renTm vs (subTm (single v) (pwBody cT*)))
                        (renTm vs (app aP v)) (var vz))
                 (subTm (single v) f) (app eP v)
    inner v r =
      semTr x₀ (Gc v r) (bodyLk v) snb' pay'
            (projr hA v r) (projr hT v r) (projr hU v r)
            (CR1₁ _ fv) hTe' hUe'
            (projl (irrel₁ crflᵀ _ (homSem₁ (emb (Gc v r)) hTe' hUe'))
                   (subTm (single v) f) fv)
            (mem₀cast⁻ (sym (Hom-cong₃ refl
                              (cong₂ app (wk-single aP) refl)
                              (cong₂ app (wk-single tP) refl)))
                       (homSem₀ (Gc v r) (projr hA v r) (projr hT v r))
                       (projr hE v r))
      where
      nv = payR v r
      ceq : Σ.fst nv ≡ cT*
      ceq = csrs-det (Σ.fst (Σ.snd nv)) (Σ.fst (Σ.snd (Σ.snd nv))) csr₀ key₀
      snb' : SN (subTm (single v) (pwBody cT*))
      snb' = subst (λ z → SN (subTm (single v) (pwBody z))) ceq
                   (Σ.fst (Σ.snd (Σ.snd (Σ.snd nv))))
      pay' : PayT (Gc v r) (subTm (single v) (pwBody cT*))
      pay' = payT-code (Gc v r)
                       (cong (λ z → subTm (single v) (pwBody z)) ceq)
                       (Σ.snd (Σ.snd (Σ.snd (Σ.snd nv))))
      hTe' = projl (emb-coh (Gc v r)) (app tP v) (projr hT v r)
      hUe' = projl (emb-coh (Gc v r)) (app uP v) (projr hU v r)
      re = projl (emb-coh Fc) v r
      fv = mem-whred₁ _ (snr-β (CR1₁ (emb Fc) re))
             (mem₁cast⁻ (sym (Hom-cong₃ refl
                               (cong₂ app (wk-single tP) refl)
                               (cong₂ app (wk-single uP) refl)))
                        _ (projr hpf v re))

    memLam : RH0 ⊩₀∋ LAMt
    memLam =
      ( sn-lam (sn-body x₀
          (subst SN (sym (bodyEq (var x₀)))
            (CR1₀ (homSem₀ (Gc (var x₀) r₀) (projr hA (var x₀) r₀)
                           (projr hU (var x₀) r₀))
                  (inner (var x₀) r₀))))
      , (λ v r →
           mem₀cast (sym (Hom-cong₃ refl
                           (cong₂ app (wk-single aP) refl)
                           (cong₂ app (wk-single uP) refl)))
                    (homSem₀ (Gc v r) (projr hA v r) (projr hU v r))
             (exp₀ _ (snr-β (CR1₀ Fc r))
               (memTm _ (sym (bodyEq v)) (inner v r)))) )

------------------------------------------------------------------------
-- ★★ THE FLAT-AMBIENT SUB-THEORY (lifted out of `fund`'s ⊢ap clause).
--
-- PERFORMANCE, measured: inside that `where` block these were
-- re-elaborated against the clause's ~22-binder telescope, and
-- `--profile=definitions` put `flatred` at 19.3s, `ett-red` at 4.6s and
-- `stkel-red` at 3.7s — 74% of ALL attributed definition time in
-- NbEPDirDBFund, for lemmas that mention nothing from the clause.
--
-- `StkEl` is the local mirror of Subj's `StkAmb` ("never Π/U", NOT
-- "stuck" — LR's `StkHd` is that one), so its key is `stkA?` and the
-- order rules are absorbed rather than refuted.  `ElStkT` is the
-- reachability invariant for `El`-of-FLAT codes: `base`, a stuck `Hom`,
-- or `Unit` (an order-hom LEAVES for `Unit` when the inequality holds).
-- `Nat` is deliberately absent — a `flat?` code decodes to `base` or a
-- `Hom`, neither of which ever becomes `Nat`, which is what keeps
-- `flatMem`'s ⊩₁Nat row absurd.
------------------------------------------------------------------------

flatred : {c c' : RTm Ξ} → c ⟶ c' → flat? c ≡ true → flat? c' ≡ true
flatred (β _ _) ()
flatred (βfst _ _) ()
flatred (βsnd _ _) ()
flatred (ξ-lam _) ()
flatred (ξ-appˡ _) ()
flatred (ξ-appʳ _) ()
flatred (ξ-pairˡ _) ()
flatred (ξ-pairʳ _) ()
flatred (ξ-fst _) ()
flatred (ξ-snd _) ()
flatred (ξ-⌜Π⌝ˡ _) ()
flatred (ξ-⌜Π⌝ʳ _) ()
flatred (ξ-⌜Σ⌝ˡ _) ()
flatred (ξ-⌜Σ⌝ʳ _) ()
flatred (ξ-⌜Hom⌝ᶜ r) k = stkC?-red r k
flatred (ξ-⌜Hom⌝ˡ r) k = k
flatred (ξ-⌜Hom⌝ʳ r) k = k
flatred (ξ-hreflᶜ _) ()
flatred (ξ-hreflᵃ _) ()
flatred (hrefl-pw _ _ _) ()
flatred (tr-J-base _ _ _ _ _) ()
flatred (tr-J-Σ _ _ _ _ _ _ _) ()
flatred (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
flatred (tr-taut _ _) ()
flatred (tr-pw _ _ _ _ _) ()
flatred (ξ-trᵈ _) ()
flatred (ξ-trᵖ _) ()
flatred (ξ-trᵉ _) ()
flatred (ap-J _ _ _ _ _) ()
flatred (ξ-apᶜ _) ()
flatred (ξ-apᵇ _) ()
flatred (ξ-apᵖ _) ()

-- the INNER invariant: reducts of `El`-of-STABLE codes never reach
-- `U` nor a literal `Π` (so nested `Hom`s never unfold).
data StkEl {Ξ : Cx} : RTy Ξ → Set where
  se-el   : {c : RTm Ξ} → stkA? c ≡ true → StkEl (El c)
  se-base : StkEl base
  se-Σ    : {A : RTy Ξ} {B : RTy (Ξ ∙)} → StkEl (Σ' A B)
  se-hom  : {H : RTy Ξ} {a b₂ : RTm Ξ} → StkEl H → StkEl (Hom H a b₂)
  se-Id   : {A₂ : RTy Ξ} {t₂ u₂ : RTm Ξ} → StkEl (Id A₂ t₂ u₂)
  -- ★ WF stage C: ⌜Unit⌝ is stable, so its decode joins.
  se-Unit : StkEl (Unit {Ξ})
  -- ★★ SpikeNatJ: and so does `Nat` — `StkEl` is the local mirror of
  -- Subj's `StkAmb` ("never Π/U"), so its key is `stkA?` and the
  -- order rules are ABSORBED below, not refuted.
  se-Nat  : StkEl (Nat {Ξ})

stkel-red : {A A' : RTy Ξ} → StkEl A → A ⟶ᵀ A' → StkEl A'
stkel-red (se-el {c = ⌜base⌝} k) El-⌜base⌝ = se-base
stkel-red (se-el {c = ⌜Σ⌝ _ _} k) (El-⌜Σ⌝ _ _) = se-Σ
stkel-red (se-el {c = ⌜Hom⌝ c' a' b'} k) (El-⌜Hom⌝ _ _ _) =
  se-hom (se-el k)
stkel-red (se-el {c = ⌜Π⌝ _ _} ()) (El-⌜Π⌝ _ _)
stkel-red (se-el {c = ⌜Id⌝ c' a' b'} k) (El-⌜Id⌝ _ _ _) = se-Id
stkel-red (se-el {c = ⌜Unit⌝} k) El-⌜Unit⌝ = se-Unit
stkel-red (se-el {c = ⌜Nat⌝} k) El-⌜Nat⌝ = se-Nat
stkel-red se-Unit ()
stkel-red se-Nat ()
stkel-red se-Id (ξ-Idᵀ r) = se-Id
stkel-red se-Id (ξ-Idˡ r) = se-Id
stkel-red se-Id (ξ-Idʳ r) = se-Id
stkel-red (se-el k) (ξ-El r) = se-el (stkA?-red r k)
stkel-red se-Σ (ξ-Σˡ r) = se-Σ
stkel-red se-Σ (ξ-Σʳ r) = se-Σ
stkel-red (se-hom ()) (Hom-U _ _)
stkel-red (se-hom ()) (Hom-Π _ _ _ _)
stkel-red (se-hom h) (ξ-Homᵀ r) = se-hom (stkel-red h r)
stkel-red (se-hom h) (ξ-Homˡ r) = se-hom h
stkel-red (se-hom h) (ξ-Homʳ r) = se-hom h
stkel-red (se-hom se-Nat) (Hom-Nat-z _)    = se-Unit
stkel-red (se-hom se-Nat) (Hom-Nat-sz _)   = se-base
stkel-red (se-hom se-Nat) (Hom-Nat-ss _ _) = se-hom se-Nat

-- the TOP invariant: reducts of `El`-of-FLAT codes are flat decodes,
-- `base`, or stuck `Hom`s — never `U`/`Π`/`Σ'`/neutral `El`.
data ElStkT {Ξ : Cx} : RTy Ξ → Set where
  et-el   : {c : RTm Ξ} → flat? c ≡ true → ElStkT (El c)
  et-base : ElStkT base
  et-hom  : {H : RTy Ξ} {a b₂ : RTm Ξ} → StkEl H → ElStkT (Hom H a b₂)
  -- ★★ SpikeNatJ: an order-hom LEAVES for `Unit` when the inequality
  -- holds, so `Unit` joins.  `Nat` deliberately does NOT — a `flat?`
  -- code decodes to `base` or a `Hom`, and neither ever becomes `Nat`,
  -- which is what keeps `flatMem`'s ⊩₁Nat row absurd.
  et-Unit : ElStkT (Unit {Ξ})

ett-red : {A A' : RTy Ξ} → ElStkT A → A ⟶ᵀ A' → ElStkT A'
ett-red (et-el {c = ⌜base⌝} k) El-⌜base⌝ = et-base
ett-red (et-el {c = ⌜Hom⌝ c' a' b'} k) (El-⌜Hom⌝ _ _ _) =
  et-hom (se-el (stkC?→stkA? c' k))
ett-red (et-el {c = ⌜Π⌝ _ _} ()) (El-⌜Π⌝ _ _)
ett-red (et-el {c = ⌜Σ⌝ _ _} ()) (El-⌜Σ⌝ _ _)
ett-red (et-el k) (ξ-El r) = et-el (flatred r k)
ett-red (et-hom ()) (Hom-U _ _)
ett-red (et-hom ()) (Hom-Π _ _ _ _)
ett-red (et-hom h) (ξ-Homᵀ r) = et-hom (stkel-red h r)
ett-red (et-hom h) (ξ-Homˡ r) = et-hom h
ett-red (et-hom h) (ξ-Homʳ r) = et-hom h
ett-red (et-hom se-Nat) (Hom-Nat-z _)    = et-Unit
ett-red (et-hom se-Nat) (Hom-Nat-sz _)   = et-base
ett-red (et-hom se-Nat) (Hom-Nat-ss _ _) = et-hom se-Nat
ett-red et-Unit ()

ett-star : {A A' : RTy Ξ} → ElStkT A → A ⟶ᵀ* A' → ElStkT A'
ett-star h doneᵀ       = h
ett-star h (stepᵀ r q) = ett-star (ett-red h r) q

ne-nostk : {n : RTm Ξ} → Ne n → stkC? n ≡ false
ne-nostk (ne-var _)   = refl
ne-nostk (ne-app _)   = refl
ne-nostk ne-absurd = refl
ne-nostk (ne-fst _)   = refl
ne-nostk (ne-snd _)   = refl
ne-nostk (ne-hrefl _) = refl
ne-nostk (ne-tr _)    = refl
ne-nostk (ne-ap _)    = refl
ne-nostk (ne-jsub _)  = refl
ne-nostk (ne-natrec _) = refl
