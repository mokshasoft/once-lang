------------------------------------------------------------------------
-- DirectedHoTT · METATHEORY — ★★★ THE **CONGRUENCES** OF `⟶*`, SPLIT OUT
-- OF `Confluence` — AND THE REASON IS MEASURED.
--
-- ⚠⚠ `Metatheory/Confluence.agdai` IS **8.7 MB**, the largest interface
--   in the development, and 11 `Lib` modules pull it in — so effectively
--   every module of the knot loads it.  What they USE from it is these
--   ~15 structural congruences; the other 4000 lines are the confluence
--   proof itself (`⟹-⁺`), which the knot never mentions.
--
-- ★★★ AND THE COST IS NOT TYPE-CHECKING.  `--profile=all` on four knot
--   modules, warm:
--
--       Knot/Census   total 5,811ms   deserialization 3,948ms   TYPING 2ms
--       Knot/IPayTy   total 3,622ms   deserialization 2,655ms   typing ~0
--       Knot/SubApp   total 3,383ms   deserialization 2,510ms   typing ~0
--       Knot/PayTy    total 3,508ms   deserialization 2,599ms   typing ~0
--
--   ⇒ ~70% of a sweep is READING INTERFACES.  Shrinking what the knot
--     must read is therefore the only lever that touches the dominant
--     cost — and Def-lifting is not it (measured: 48.3s/4.56 GB against
--     48.3s/4.53 GB, no effect).
--
-- ★ THIS BLOCK IS SELF-CONTAINED: lines 84–318 of `Confluence` mention
--   `⟹` ZERO times.  It needs `Spec/Syntax` and `Spec/Typing` and
--   nothing else.
--
-- ⚠ `Confluence` re-exports it `public`, so every existing importer keeps
--   working unchanged; a module that wants only the congruences imports
--   THIS one and skips 8.7 MB.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.RedCong where
open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; cong₂; Σ; _,_; _×_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs; RTm; var; lam; app; pair; fst; snd; absurd
        ; ordtr; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap; ⌜Id⌝; idrefl; jsub
        ; unit; nzero; nsuc; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝; subTm-subTm
        ; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃; ⌜Id⌝-cong₃; jsub-cong₃; Ren; extR
        ; renTm; renTm-renTm; renTm-cong; Sub; extS; subTm; renTm-subTm
        ; subTm-renTm; subTm-cong; _ᵣ∘ₛ_; _ₛ∘ᵣ_; _∘ᵣ_; Desc; dι; dρ; con; IMu
        ; ielim; ⌜IMu⌝; εwkTm; RTy; El; Π; Σ'; Hom; Id; DIh; ⌜Fin⌝; dσ; dpay
        ; dih; fzero; fsuc; fcase; fcase0; psplit; cong₄ )
open import DirectedHoTT.Spec.Variance
  using ( 𝔹; true; false; pw?; stkC?; stkA?; pwBody; pwShift; pw?-ren
        ; stkC?-ren; stkA?-ren; pwBody-ren; pw?-sub; stkC?-sub; stkA?-sub
        ; pwBody-sub; pw⊥stk; pw⊥stkA; stkC?→stkA? )
open import DirectedHoTT.Spec.Typing
  using ( single; swp; _⟶_; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ
        ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ordtr-z; ordtr-szz; ordtr-ssz
        ; ordtr-szs; ordtr-sss; ξ-ordtrᵃ; ξ-ordtrᵗ; ξ-ordtrᵘ; ξ-ordtrᵖ
        ; ξ-ordtrq; ξ-fst; ξ-snd; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; tr-J-base
        ; tr-J-Σ; tr-J-Id; tr-taut; hrefl-pw; tr-J-Hom; tr-pw; ξ-⌜Hom⌝ᶜ
        ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ; ap-J
        ; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ; jsub-refl; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-idreflᶜ
        ; ξ-idreflᵃ; ξ-jsubᵈ; ξ-jsubᵖ; ξ-jsubᵉ; natrec-zero; natrec-suc
        ; ξ-nsuc; ξ-natrecᶻ; ξ-natrecˢ; ξ-natrecⁿ; tr-J-Unit; tr-J-IMu
        ; El-⌜Nat⌝; El-⌜Unit⌝; _⟶*_; done; step; _≅_; cred; crfl; csym; ctrn
        ; ξ-con; ξ-ielimⁱ; ξ-ielimᵗ; El-⌜IMu⌝; _⟶ᵀ_; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ
        ; ξ-Σʳ; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ; _≅ᵀ_; crflᵀ
        ; ctrnᵀ; credᵀ; ι; dpay-ι; dpay-σ; dpay-ρ; dih-ι; dih-σ; dih-ρ
        ; fcase-z; fcase-s; psplit-β; tr-J-Fin; single2; ξ-⌜IMu⌝ᴵ; ξ-⌜IMu⌝ᴰ
        ; ξ-⌜IMu⌝ⁱ; ξ-ielimᴰ; ξ-ielimᵉ; ξ-dι; ξ-dσˢ; ξ-dσᶠ; ξ-dρʲ; ξ-dρᶜ
        ; ξ-dpayᴵ; ξ-dpayᴰ; ξ-dpayᶜ; ξ-dpayⁱ; ξ-dihᴰ; ξ-dihᵉ; ξ-dihᶜ; ξ-dihᵖ
        ; ξ-fsuc; ξ-fcaseᵗ; ξ-fcaseᵃ; ξ-fcaseᵇ; ξ-fcase0; ξ-psplitᵇ; ξ-psplitᵍ
        ; ξ-IMuᴵ; ξ-IMuᴰ; ξ-IMuⁱ; ξ-Desc; ξ-DIhᴰ; ξ-DIhᴹ; ξ-DIhᶜ; ξ-DIhᵖ )
open import DirectedHoTT.Metatheory.SubjectReductionBase
  using ( sub-comm; sub-comm-ext; ⟶-sub; wk-sub; wk₁-sub; swp-sub; pwShift-sub )

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- Multi-step reduction: transitivity + congruences.
------------------------------------------------------------------------

⟶*-trans : {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
⟶*-trans done       q = q
⟶*-trans (step r p) q = step r (⟶*-trans p q)

⟶*-lam : {t t' : RTm (Γ ∙)} → t ⟶* t' → lam t ⟶* lam t'
⟶*-lam done       = done
⟶*-lam (step r p) = step (ξ-lam r) (⟶*-lam p)

⟶*-appˡ : {t t' u : RTm Γ} → t ⟶* t' → app t u ⟶* app t' u
⟶*-appˡ done       = done
⟶*-appˡ (step r p) = step (ξ-appˡ r) (⟶*-appˡ p)

⟶*-appʳ : {t u u' : RTm Γ} → u ⟶* u' → app t u ⟶* app t u'
⟶*-appʳ done       = done
⟶*-appʳ (step r p) = step (ξ-appʳ r) (⟶*-appʳ p)

⟶*-pairˡ : {a a' b : RTm Γ} → a ⟶* a' → pair a b ⟶* pair a' b
⟶*-pairˡ done       = done
⟶*-pairˡ (step r p) = step (ξ-pairˡ r) (⟶*-pairˡ p)

⟶*-pairʳ : {a b b' : RTm Γ} → b ⟶* b' → pair a b ⟶* pair a b'
⟶*-pairʳ done       = done
⟶*-pairʳ (step r p) = step (ξ-pairʳ r) (⟶*-pairʳ p)

⟶*-ordtrᵃ : {a a' t u p q : RTm Γ} → a ⟶* a' → ordtr a t u p q ⟶* ordtr a' t u p q
⟶*-ordtrᵃ done       = done
⟶*-ordtrᵃ (step r q) = step (ξ-ordtrᵃ r) (⟶*-ordtrᵃ q)
⟶*-ordtrᵗ : {a t t' u p q : RTm Γ} → t ⟶* t' → ordtr a t u p q ⟶* ordtr a t' u p q
⟶*-ordtrᵗ done       = done
⟶*-ordtrᵗ (step r q) = step (ξ-ordtrᵗ r) (⟶*-ordtrᵗ q)
⟶*-ordtrᵘ : {a t u u' p q : RTm Γ} → u ⟶* u' → ordtr a t u p q ⟶* ordtr a t u' p q
⟶*-ordtrᵘ done       = done
⟶*-ordtrᵘ (step r q) = step (ξ-ordtrᵘ r) (⟶*-ordtrᵘ q)
⟶*-ordtrᵖ : {a t u p p' q : RTm Γ} → p ⟶* p' → ordtr a t u p q ⟶* ordtr a t u p' q
⟶*-ordtrᵖ done       = done
⟶*-ordtrᵖ (step r q) = step (ξ-ordtrᵖ r) (⟶*-ordtrᵖ q)
⟶*-ordtrq : {a t u p q q' : RTm Γ} → q ⟶* q' → ordtr a t u p q ⟶* ordtr a t u p q'
⟶*-ordtrq done       = done
⟶*-ordtrq (step r w) = step (ξ-ordtrq r) (⟶*-ordtrq w)

⟶*-absurdᶜ : {c c' e : RTm Γ} → c ⟶* c' → absurd c e ⟶* absurd c' e
⟶*-absurdᶜ done       = done
⟶*-absurdᶜ (step r q) = step (ξ-absurdᶜ r) (⟶*-absurdᶜ q)

⟶*-absurdᵉ : {c e e' : RTm Γ} → e ⟶* e' → absurd c e ⟶* absurd c e'
⟶*-absurdᵉ done       = done
⟶*-absurdᵉ (step r q) = step (ξ-absurdᵉ r) (⟶*-absurdᵉ q)

⟶*-fst : {p p' : RTm Γ} → p ⟶* p' → fst p ⟶* fst p'
⟶*-fst done       = done
⟶*-fst (step r q) = step (ξ-fst r) (⟶*-fst q)

⟶*-snd : {p p' : RTm Γ} → p ⟶* p' → snd p ⟶* snd p'
⟶*-snd done       = done
⟶*-snd (step r q) = step (ξ-snd r) (⟶*-snd q)

⟶*-⌜Π⌝ˡ : {c c' : RTm Γ} {d : RTm (Γ ∙)} → c ⟶* c' → ⌜Π⌝ c d ⟶* ⌜Π⌝ c' d
⟶*-⌜Π⌝ˡ done       = done
⟶*-⌜Π⌝ˡ (step r p) = step (ξ-⌜Π⌝ˡ r) (⟶*-⌜Π⌝ˡ p)

⟶*-⌜Π⌝ʳ : {c : RTm Γ} {d d' : RTm (Γ ∙)} → d ⟶* d' → ⌜Π⌝ c d ⟶* ⌜Π⌝ c d'
⟶*-⌜Π⌝ʳ done       = done
⟶*-⌜Π⌝ʳ (step r p) = step (ξ-⌜Π⌝ʳ r) (⟶*-⌜Π⌝ʳ p)

⟶*-⌜Σ⌝ˡ : {c c' : RTm Γ} {d : RTm (Γ ∙)} → c ⟶* c' → ⌜Σ⌝ c d ⟶* ⌜Σ⌝ c' d
⟶*-⌜Σ⌝ˡ done       = done
⟶*-⌜Σ⌝ˡ (step r p) = step (ξ-⌜Σ⌝ˡ r) (⟶*-⌜Σ⌝ˡ p)

⟶*-⌜Σ⌝ʳ : {c : RTm Γ} {d d' : RTm (Γ ∙)} → d ⟶* d' → ⌜Σ⌝ c d ⟶* ⌜Σ⌝ c d'
⟶*-⌜Σ⌝ʳ done       = done
⟶*-⌜Σ⌝ʳ (step r p) = step (ξ-⌜Σ⌝ʳ r) (⟶*-⌜Σ⌝ʳ p)

⟶*-⌜Hom⌝ᶜ : {c c' a b : RTm Γ} → c ⟶* c' → ⌜Hom⌝ c a b ⟶* ⌜Hom⌝ c' a b
⟶*-⌜Hom⌝ᶜ done       = done
⟶*-⌜Hom⌝ᶜ (step r p) = step (ξ-⌜Hom⌝ᶜ r) (⟶*-⌜Hom⌝ᶜ p)

⟶*-⌜Hom⌝ˡ : {c a a' b : RTm Γ} → a ⟶* a' → ⌜Hom⌝ c a b ⟶* ⌜Hom⌝ c a' b
⟶*-⌜Hom⌝ˡ done       = done
⟶*-⌜Hom⌝ˡ (step r p) = step (ξ-⌜Hom⌝ˡ r) (⟶*-⌜Hom⌝ˡ p)

⟶*-⌜Hom⌝ʳ : {c a b b' : RTm Γ} → b ⟶* b' → ⌜Hom⌝ c a b ⟶* ⌜Hom⌝ c a b'
⟶*-⌜Hom⌝ʳ done       = done
⟶*-⌜Hom⌝ʳ (step r p) = step (ξ-⌜Hom⌝ʳ r) (⟶*-⌜Hom⌝ʳ p)

⟶*-hreflᶜ : {c c' t : RTm Γ} → c ⟶* c' → hrefl c t ⟶* hrefl c' t
⟶*-hreflᶜ done       = done
⟶*-hreflᶜ (step r p) = step (ξ-hreflᶜ r) (⟶*-hreflᶜ p)

⟶*-hreflᵃ : {c t t' : RTm Γ} → t ⟶* t' → hrefl c t ⟶* hrefl c t'
⟶*-hreflᵃ done       = done
⟶*-hreflᵃ (step r p) = step (ξ-hreflᵃ r) (⟶*-hreflᵃ p)

⟶*-trᵈ : {d d' : RTm (Γ ∙)} {p e : RTm Γ} → d ⟶* d' → tr d p e ⟶* tr d' p e
⟶*-trᵈ done       = done
⟶*-trᵈ (step r q) = step (ξ-trᵈ r) (⟶*-trᵈ q)

⟶*-trᵖ : {d : RTm (Γ ∙)} {p p' e : RTm Γ} → p ⟶* p' → tr d p e ⟶* tr d p' e
⟶*-trᵖ done       = done
⟶*-trᵖ (step r q) = step (ξ-trᵖ r) (⟶*-trᵖ q)

⟶*-trᵉ : {d : RTm (Γ ∙)} {p e e' : RTm Γ} → e ⟶* e' → tr d p e ⟶* tr d p e'
⟶*-trᵉ done       = done
⟶*-trᵉ (step r q) = step (ξ-trᵉ r) (⟶*-trᵉ q)

⟶*-apᶜ : {c c' : RTm Γ} {b : RTm (Γ ∙)} {p : RTm Γ} → c ⟶* c' → ap c b p ⟶* ap c' b p
⟶*-apᶜ done       = done
⟶*-apᶜ (step r q) = step (ξ-apᶜ r) (⟶*-apᶜ q)

⟶*-apᵇ : {c : RTm Γ} {b b' : RTm (Γ ∙)} {p : RTm Γ} → b ⟶* b' → ap c b p ⟶* ap c b' p
⟶*-apᵇ done       = done
⟶*-apᵇ (step r q) = step (ξ-apᵇ r) (⟶*-apᵇ q)

⟶*-apᵖ : {c : RTm Γ} {b : RTm (Γ ∙)} {p p' : RTm Γ} → p ⟶* p' → ap c b p ⟶* ap c b p'
⟶*-apᵖ done       = done
⟶*-apᵖ (step r q) = step (ξ-apᵖ r) (⟶*-apᵖ q)

⟶*-⌜Id⌝ᶜ : {c c' a b : RTm Γ} → c ⟶* c' → ⌜Id⌝ c a b ⟶* ⌜Id⌝ c' a b
⟶*-⌜Id⌝ᶜ done       = done
⟶*-⌜Id⌝ᶜ (step r q) = step (ξ-⌜Id⌝ᶜ r) (⟶*-⌜Id⌝ᶜ q)

⟶*-⌜Id⌝ˡ : {c a a' b : RTm Γ} → a ⟶* a' → ⌜Id⌝ c a b ⟶* ⌜Id⌝ c a' b
⟶*-⌜Id⌝ˡ done       = done
⟶*-⌜Id⌝ˡ (step r q) = step (ξ-⌜Id⌝ˡ r) (⟶*-⌜Id⌝ˡ q)

⟶*-⌜Id⌝ʳ : {c a b b' : RTm Γ} → b ⟶* b' → ⌜Id⌝ c a b ⟶* ⌜Id⌝ c a b'
⟶*-⌜Id⌝ʳ done       = done
⟶*-⌜Id⌝ʳ (step r q) = step (ξ-⌜Id⌝ʳ r) (⟶*-⌜Id⌝ʳ q)

⟶*-idreflᶜ : {c c' t : RTm Γ} → c ⟶* c' → idrefl c t ⟶* idrefl c' t
⟶*-idreflᶜ done       = done
⟶*-idreflᶜ (step r q) = step (ξ-idreflᶜ r) (⟶*-idreflᶜ q)

⟶*-idreflᵃ : {c t t' : RTm Γ} → t ⟶* t' → idrefl c t ⟶* idrefl c t'
⟶*-idreflᵃ done       = done
⟶*-idreflᵃ (step r q) = step (ξ-idreflᵃ r) (⟶*-idreflᵃ q)

⟶*-jsubᵈ : {d d' : RTm (Γ ∙)} {p e : RTm Γ} → d ⟶* d' → jsub d p e ⟶* jsub d' p e
⟶*-jsubᵈ done       = done
⟶*-jsubᵈ (step r q) = step (ξ-jsubᵈ r) (⟶*-jsubᵈ q)

⟶*-jsubᵖ : {d : RTm (Γ ∙)} {p p' e : RTm Γ} → p ⟶* p' → jsub d p e ⟶* jsub d p' e
⟶*-jsubᵖ done       = done
⟶*-jsubᵖ (step r q) = step (ξ-jsubᵖ r) (⟶*-jsubᵖ q)

⟶*-jsubᵉ : {d : RTm (Γ ∙)} {p e e' : RTm Γ} → e ⟶* e' → jsub d p e ⟶* jsub d p e'
⟶*-jsubᵉ done       = done
⟶*-jsubᵉ (step r q) = step (ξ-jsubᵉ r) (⟶*-jsubᵉ q)

⟶*-nsuc : {n n' : RTm Γ} → n ⟶* n' → nsuc n ⟶* nsuc n'
⟶*-nsuc done       = done
⟶*-nsuc (step r q) = step (ξ-nsuc r) (⟶*-nsuc q)

⟶*-natrecᶻ : {z z' : RTm Γ} {s : RTm ((Γ ∙) ∙)} {n : RTm Γ} →
             z ⟶* z' → natrec z s n ⟶* natrec z' s n
⟶*-natrecᶻ done       = done
⟶*-natrecᶻ (step r q) = step (ξ-natrecᶻ r) (⟶*-natrecᶻ q)

⟶*-natrecˢ : {z : RTm Γ} {s s' : RTm ((Γ ∙) ∙)} {n : RTm Γ} →
             s ⟶* s' → natrec z s n ⟶* natrec z s' n
⟶*-natrecˢ done       = done
⟶*-natrecˢ (step r q) = step (ξ-natrecˢ r) (⟶*-natrecˢ q)

⟶*-natrecⁿ : {z : RTm Γ} {s : RTm ((Γ ∙) ∙)} {n n' : RTm Γ} →
             n ⟶* n' → natrec z s n ⟶* natrec z s n'
⟶*-natrecⁿ done       = done
⟶*-natrecⁿ (step r q) = step (ξ-natrecⁿ r) (⟶*-natrecⁿ q)

-- ★ LEVITATION: the congruence closures of the levitated formers.
⟶*-⌜IMu⌝ᴵ : {D : RTm Γ} {i : RTm Γ} {I I' : RTm Γ} → I ⟶* I' → ⌜IMu⌝ I D i ⟶* ⌜IMu⌝ I' D i
⟶*-⌜IMu⌝ᴵ done       = done
⟶*-⌜IMu⌝ᴵ (step r q) = step (ξ-⌜IMu⌝ᴵ r) (⟶*-⌜IMu⌝ᴵ q)

⟶*-⌜IMu⌝ᴰ : {I : RTm Γ} {i : RTm Γ} {D D' : RTm Γ} → D ⟶* D' → ⌜IMu⌝ I D i ⟶* ⌜IMu⌝ I D' i
⟶*-⌜IMu⌝ᴰ done       = done
⟶*-⌜IMu⌝ᴰ (step r q) = step (ξ-⌜IMu⌝ᴰ r) (⟶*-⌜IMu⌝ᴰ q)

⟶*-⌜IMu⌝ⁱ : {I : RTm Γ} {D : RTm Γ} {i i' : RTm Γ} → i ⟶* i' → ⌜IMu⌝ I D i ⟶* ⌜IMu⌝ I D i'
⟶*-⌜IMu⌝ⁱ done       = done
⟶*-⌜IMu⌝ⁱ (step r q) = step (ξ-⌜IMu⌝ⁱ r) (⟶*-⌜IMu⌝ⁱ q)

⟶*-con :  {p p' : RTm Γ} → p ⟶* p' → con p ⟶* con p'
⟶*-con done       = done
⟶*-con (step r q) = step (ξ-con r) (⟶*-con q)

⟶*-ielimᴰ : {i : RTm Γ} {e : RTm Γ} {t : RTm Γ} {D D' : RTm Γ} → D ⟶* D' → ielim D i e t ⟶* ielim D' i e t
⟶*-ielimᴰ done       = done
⟶*-ielimᴰ (step r q) = step (ξ-ielimᴰ r) (⟶*-ielimᴰ q)

⟶*-ielimⁱ : {D : RTm Γ} {e : RTm Γ} {t : RTm Γ} {i i' : RTm Γ} → i ⟶* i' → ielim D i e t ⟶* ielim D i' e t
⟶*-ielimⁱ done       = done
⟶*-ielimⁱ (step r q) = step (ξ-ielimⁱ r) (⟶*-ielimⁱ q)

⟶*-ielimᵉ : {D : RTm Γ} {i : RTm Γ} {t : RTm Γ} {e e' : RTm Γ} → e ⟶* e' → ielim D i e t ⟶* ielim D i e' t
⟶*-ielimᵉ done       = done
⟶*-ielimᵉ (step r q) = step (ξ-ielimᵉ r) (⟶*-ielimᵉ q)

⟶*-ielimᵗ : {D : RTm Γ} {i : RTm Γ} {e : RTm Γ} {t t' : RTm Γ} → t ⟶* t' → ielim D i e t ⟶* ielim D i e t'
⟶*-ielimᵗ done       = done
⟶*-ielimᵗ (step r q) = step (ξ-ielimᵗ r) (⟶*-ielimᵗ q)

⟶*-dι :  {j j' : RTm Γ} → j ⟶* j' → dι j ⟶* dι j'
⟶*-dι done       = done
⟶*-dι (step r q) = step (ξ-dι r) (⟶*-dι q)

⟶*-dσˢ : {f : RTm Γ} {S S' : RTm Γ} → S ⟶* S' → dσ S f ⟶* dσ S' f
⟶*-dσˢ done       = done
⟶*-dσˢ (step r q) = step (ξ-dσˢ r) (⟶*-dσˢ q)

⟶*-dσᶠ : {S : RTm Γ} {f f' : RTm Γ} → f ⟶* f' → dσ S f ⟶* dσ S f'
⟶*-dσᶠ done       = done
⟶*-dσᶠ (step r q) = step (ξ-dσᶠ r) (⟶*-dσᶠ q)

⟶*-dρʲ : {C : RTm Γ} {j j' : RTm Γ} → j ⟶* j' → dρ j C ⟶* dρ j' C
⟶*-dρʲ done       = done
⟶*-dρʲ (step r q) = step (ξ-dρʲ r) (⟶*-dρʲ q)

⟶*-dρᶜ : {j : RTm Γ} {C C' : RTm Γ} → C ⟶* C' → dρ j C ⟶* dρ j C'
⟶*-dρᶜ done       = done
⟶*-dρᶜ (step r q) = step (ξ-dρᶜ r) (⟶*-dρᶜ q)

⟶*-dpayᴵ : {D : RTm Γ} {C : RTm Γ} {i : RTm Γ} {I I' : RTm Γ} → I ⟶* I' → dpay I D C i ⟶* dpay I' D C i
⟶*-dpayᴵ done       = done
⟶*-dpayᴵ (step r q) = step (ξ-dpayᴵ r) (⟶*-dpayᴵ q)

⟶*-dpayᴰ : {I : RTm Γ} {C : RTm Γ} {i : RTm Γ} {D D' : RTm Γ} → D ⟶* D' → dpay I D C i ⟶* dpay I D' C i
⟶*-dpayᴰ done       = done
⟶*-dpayᴰ (step r q) = step (ξ-dpayᴰ r) (⟶*-dpayᴰ q)

⟶*-dpayᶜ : {I : RTm Γ} {D : RTm Γ} {i : RTm Γ} {C C' : RTm Γ} → C ⟶* C' → dpay I D C i ⟶* dpay I D C' i
⟶*-dpayᶜ done       = done
⟶*-dpayᶜ (step r q) = step (ξ-dpayᶜ r) (⟶*-dpayᶜ q)

⟶*-dpayⁱ : {I : RTm Γ} {D : RTm Γ} {C : RTm Γ} {i i' : RTm Γ} → i ⟶* i' → dpay I D C i ⟶* dpay I D C i'
⟶*-dpayⁱ done       = done
⟶*-dpayⁱ (step r q) = step (ξ-dpayⁱ r) (⟶*-dpayⁱ q)

⟶*-dihᴰ : {e : RTm Γ} {C : RTm Γ} {p : RTm Γ} {D D' : RTm Γ} → D ⟶* D' → dih D e C p ⟶* dih D' e C p
⟶*-dihᴰ done       = done
⟶*-dihᴰ (step r q) = step (ξ-dihᴰ r) (⟶*-dihᴰ q)

⟶*-dihᵉ : {D : RTm Γ} {C : RTm Γ} {p : RTm Γ} {e e' : RTm Γ} → e ⟶* e' → dih D e C p ⟶* dih D e' C p
⟶*-dihᵉ done       = done
⟶*-dihᵉ (step r q) = step (ξ-dihᵉ r) (⟶*-dihᵉ q)

⟶*-dihᶜ : {D : RTm Γ} {e : RTm Γ} {p : RTm Γ} {C C' : RTm Γ} → C ⟶* C' → dih D e C p ⟶* dih D e C' p
⟶*-dihᶜ done       = done
⟶*-dihᶜ (step r q) = step (ξ-dihᶜ r) (⟶*-dihᶜ q)

⟶*-dihᵖ : {D : RTm Γ} {e : RTm Γ} {C : RTm Γ} {p p' : RTm Γ} → p ⟶* p' → dih D e C p ⟶* dih D e C p'
⟶*-dihᵖ done       = done
⟶*-dihᵖ (step r q) = step (ξ-dihᵖ r) (⟶*-dihᵖ q)

⟶*-fsuc :  {t t' : RTm Γ} → t ⟶* t' → fsuc t ⟶* fsuc t'
⟶*-fsuc done       = done
⟶*-fsuc (step r q) = step (ξ-fsuc r) (⟶*-fsuc q)

⟶*-fcaseᵗ : {a : RTm Γ} {b : RTm (Γ ∙)} {t t' : RTm Γ} → t ⟶* t' → fcase t a b ⟶* fcase t' a b
⟶*-fcaseᵗ done       = done
⟶*-fcaseᵗ (step r q) = step (ξ-fcaseᵗ r) (⟶*-fcaseᵗ q)

⟶*-fcaseᵃ : {t : RTm Γ} {b : RTm (Γ ∙)} {a a' : RTm Γ} → a ⟶* a' → fcase t a b ⟶* fcase t a' b
⟶*-fcaseᵃ done       = done
⟶*-fcaseᵃ (step r q) = step (ξ-fcaseᵃ r) (⟶*-fcaseᵃ q)

⟶*-fcaseᵇ : {t : RTm Γ} {a : RTm Γ} {b b' : RTm (Γ ∙)} → b ⟶* b' → fcase t a b ⟶* fcase t a b'
⟶*-fcaseᵇ done       = done
⟶*-fcaseᵇ (step r q) = step (ξ-fcaseᵇ r) (⟶*-fcaseᵇ q)

⟶*-fcase0 :  {t t' : RTm Γ} → t ⟶* t' → fcase0 t ⟶* fcase0 t'
⟶*-fcase0 done       = done
⟶*-fcase0 (step r q) = step (ξ-fcase0 r) (⟶*-fcase0 q)

⟶*-psplitᵇ : {q : RTm Γ} {b b' : RTm ((Γ ∙) ∙)} → b ⟶* b' → psplit b q ⟶* psplit b' q
⟶*-psplitᵇ done       = done
⟶*-psplitᵇ (step r q) = step (ξ-psplitᵇ r) (⟶*-psplitᵇ q)

⟶*-psplitᵍ : {b : RTm ((Γ ∙) ∙)} {q q' : RTm Γ} → q ⟶* q' → psplit b q ⟶* psplit b q'
⟶*-psplitᵍ done       = done
⟶*-psplitᵍ (step r q) = step (ξ-psplitᵍ r) (⟶*-psplitᵍ q)

⟶*-sub : (σ : Sub Γ Δ) {t u : RTm Γ} → t ⟶* u → subTm σ t ⟶* subTm σ u
⟶*-sub σ done       = done
⟶*-sub σ (step r p) = step (⟶-sub σ r) (⟶*-sub σ p)

------------------------------------------------------------------------
-- ★★★ AND THE **RENAMING** CONGRUENCES COME WITH IT — because 10 more
--   modules (`Gcd/Step*`, `Lib/Max`, `Lib/DvdArith`, …) were blocked on
--   `⟶*-ren` ALONE.  Bringing `ren-comm`/`⟶-ren` across turns 25 movable
--   importers into 35.
--
-- ⚠ Still `⟹`-free: the parallel-reduction relation is not mentioned
--   anywhere below.  The block is closed under its own dependencies —
--   `pwBody-ren`, `pw?-ren`, `stkA?-ren`, `wk-ren`, `pwShift-ren` all
--   come from `Spec`, not from `Confluence`.
------------------------------------------------------------------------

ren-comm : (ρ : Ren Γ Δ) (t : RTm (Γ ∙)) (u : RTm Γ) →
           renTm ρ (subTm (single u) t) ≡
           subTm (single (renTm ρ u)) (renTm (extR ρ) t)
ren-comm {Γ} ρ t u =
  trans (renTm-subTm t) (trans (subTm-cong bridge t) (sym (subTm-renTm t)))
  where
  bridge : ∀ (x : Var (Γ ∙)) →
           (ρ ᵣ∘ₛ single u) x ≡ (single (renTm ρ u) ₛ∘ᵣ extR ρ) x
  bridge vz     = refl
  bridge (vs x) = refl

-- The pure-renaming commutation bridges (all pointwise-definitional):
-- weakening, weakening-under-a-binder, and the top-two-variable swap
-- each commute with an arbitrary lifted renaming.
wk-ren : (ρ : Ren Γ Δ) (t : RTm Γ) →
         renTm (extR ρ) (renTm vs t) ≡ renTm vs (renTm ρ t)
wk-ren ρ t =
  trans (renTm-renTm t) (trans (renTm-cong (λ _ → refl) t) (sym (renTm-renTm t)))

-- ★ WF stage A: `ren-comm` one binder down (the renaming analog of
-- `sub-comm-ext`) — for the recursor's step substitution.
ren-comm-ext : (ρ : Ren Γ Δ) (s : RTm ((Γ ∙) ∙)) (n : RTm Γ) →
               renTm (extR ρ) (subTm (extS (single n)) s) ≡
               subTm (extS (single (renTm ρ n))) (renTm (extR (extR ρ)) s)
ren-comm-ext {Γ} ρ s n =
  trans (renTm-subTm s) (trans (subTm-cong bridge s) (sym (subTm-renTm s)))
  where
  bridge : ∀ (x : Var ((Γ ∙) ∙)) →
           renTm (extR ρ) (extS (single n) x) ≡
           extS (single (renTm ρ n)) (extR (extR ρ) x)
  bridge vz          = refl
  bridge (vs vz)     = wk-ren ρ n
  bridge (vs (vs x)) = refl

wk₁-ren : (ρ : Ren Γ Δ) (t : RTm (Γ ∙)) →
          renTm (extR (extR ρ)) (renTm (extR vs) t) ≡
          renTm (extR vs) (renTm (extR ρ) t)
wk₁-ren ρ t =
  trans (renTm-renTm t) (trans (renTm-cong ptw t) (sym (renTm-renTm t)))
  where
  ptw : ∀ x → (extR (extR ρ) ∘ᵣ extR vs) x ≡ (extR vs ∘ᵣ extR ρ) x
  ptw vz     = refl
  ptw (vs z) = refl

swp-ren : (ρ : Ren Γ Δ) (t : RTm ((Γ ∙) ∙)) →
          renTm (extR (extR ρ)) (renTm swp t) ≡
          renTm swp (renTm (extR (extR ρ)) t)
swp-ren ρ t =
  trans (renTm-renTm t) (trans (renTm-cong ptw t) (sym (renTm-renTm t)))
  where
  ptw : ∀ x → (extR (extR ρ) ∘ᵣ swp) x ≡ (swp ∘ᵣ extR (extR ρ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs z)) = refl

-- ...and the same against `pwShift` (W2b).
pwShift-ren : (ρ : Ren Γ Δ) (t : RTm ((Γ ∙) ∙)) →
              renTm (extR (extR ρ)) (renTm pwShift t) ≡
              renTm pwShift (renTm (extR (extR ρ)) t)
pwShift-ren ρ t =
  trans (renTm-renTm t) (trans (renTm-cong ptw t) (sym (renTm-renTm t)))
  where
  ptw : ∀ x → (extR (extR ρ) ∘ᵣ pwShift) x ≡ (pwShift ∘ᵣ extR (extR ρ)) x
  ptw vz          = refl
  ptw (vs vz)     = refl
  ptw (vs (vs z)) = refl

-- `psplit-β`'s two-binder instantiation commutes with renaming
ren-comm2 : (ρ : Ren Γ Δ) (b : RTm ((Γ ∙) ∙)) (x y : RTm Γ) →
            renTm ρ (subTm (single2 x y) b) ≡
            subTm (single2 (renTm ρ x) (renTm ρ y)) (renTm (extR (extR ρ)) b)
ren-comm2 {Γ} ρ b x y =
  trans (renTm-subTm b) (trans (subTm-cong bridge b) (sym (subTm-renTm b)))
  where
  bridge : ∀ (z : Var ((Γ ∙) ∙)) →
           (ρ ᵣ∘ₛ single2 x y) z ≡ (single2 (renTm ρ x) (renTm ρ y) ₛ∘ᵣ extR (extR ρ)) z
  bridge vz          = refl
  bridge (vs vz)     = refl
  bridge (vs (vs z)) = refl

⟶-ren : (ρ : Ren Γ Δ) {t u : RTm Γ} → t ⟶ u → renTm ρ t ⟶ renTm ρ u
⟶-ren ρ (β t u)    =
  subst (λ z → renTm ρ (app (lam t) u) ⟶ z)
        (sym (ren-comm ρ t u))
        (β (renTm (extR ρ) t) (renTm ρ u))
⟶-ren ρ (βfst a b)  = βfst (renTm ρ a) (renTm ρ b)
⟶-ren ρ (βsnd a b)  = βsnd (renTm ρ a) (renTm ρ b)
⟶-ren ρ (ξ-lam r)   = ξ-lam (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-appˡ r)  = ξ-appˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-appʳ r)  = ξ-appʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-pairˡ r) = ξ-pairˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-pairʳ r) = ξ-pairʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-absurdᶜ r)   = ξ-absurdᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-absurdᵉ r)   = ξ-absurdᵉ (⟶-ren ρ r)
⟶-ren ρ (ordtr-z t u p q) = ordtr-z _ _ _ _
⟶-ren ρ (ordtr-szz a p q) = ordtr-szz _ _ _
⟶-ren ρ (ordtr-ssz a t p q) = ordtr-ssz _ _ _ _
⟶-ren ρ (ordtr-szs a u p q) = ordtr-szs _ _ _ _
⟶-ren ρ (ordtr-sss a t u p q) = ordtr-sss _ _ _ _ _
⟶-ren ρ (ξ-ordtrᵃ r) = ξ-ordtrᵃ (⟶-ren ρ r)
⟶-ren ρ (ξ-ordtrᵗ r) = ξ-ordtrᵗ (⟶-ren ρ r)
⟶-ren ρ (ξ-ordtrᵘ r) = ξ-ordtrᵘ (⟶-ren ρ r)
⟶-ren ρ (ξ-ordtrᵖ r) = ξ-ordtrᵖ (⟶-ren ρ r)
⟶-ren ρ (ξ-ordtrq r) = ξ-ordtrq (⟶-ren ρ r)
⟶-ren ρ (ξ-fst r)   = ξ-fst (⟶-ren ρ r)
⟶-ren ρ (ξ-snd r)   = ξ-snd (⟶-ren ρ r)
⟶-ren ρ (natrec-zero z s) =
  natrec-zero (renTm ρ z) (renTm (extR (extR ρ)) s)
⟶-ren ρ (natrec-suc z s n) =
  subst (λ w → natrec (renTm ρ z) (renTm (extR (extR ρ)) s)
                      (nsuc (renTm ρ n)) ⟶ w)
        (sym (trans (ren-comm ρ (subTm (extS (single n)) s) (natrec z s n))
                    (cong (subTm (single (natrec (renTm ρ z)
                                                 (renTm (extR (extR ρ)) s)
                                                 (renTm ρ n))))
                          (ren-comm-ext ρ s n))))
        (natrec-suc (renTm ρ z) (renTm (extR (extR ρ)) s) (renTm ρ n))
-- ★ LEVITATION
⟶-ren ρ (ι D i e p) = ι _ _ _ _
⟶-ren ρ (dpay-ι I D j i) = dpay-ι _ _ _ _
⟶-ren ρ (dpay-σ I D S f i) =
  subst (λ z → dpay (renTm ρ I) (renTm ρ D) (dσ (renTm ρ S) (renTm ρ f)) (renTm ρ i) ⟶ z)
        (sym (cong₄ (λ a b c d → ⌜Σ⌝ (renTm ρ S) (dpay a b (app c (var vz)) d))
                    (wk-ren ρ I) (wk-ren ρ D) (wk-ren ρ f) (wk-ren ρ i)))
        (dpay-σ _ _ _ _ _)
⟶-ren ρ (dpay-ρ I D j C i) =
  subst (λ z → dpay (renTm ρ I) (renTm ρ D) (dρ (renTm ρ j) (renTm ρ C)) (renTm ρ i) ⟶ z)
        (sym (cong₄ (λ a b c d → ⌜Σ⌝ (⌜IMu⌝ (renTm ρ I) (renTm ρ D) (renTm ρ j)) (dpay a b c d))
                    (wk-ren ρ I) (wk-ren ρ D) (wk-ren ρ C) (wk-ren ρ i)))
        (dpay-ρ _ _ _ _ _)
⟶-ren ρ (dih-ι D e j p) = dih-ι _ _ _ _
⟶-ren ρ (dih-σ D e S f p) = dih-σ _ _ _ _ _
⟶-ren ρ (dih-ρ D e j C p) = dih-ρ _ _ _ _ _
⟶-ren ρ (fcase-z a b) = fcase-z _ _
⟶-ren ρ (fcase-s t a b) =
  subst (λ z → fcase (fsuc (renTm ρ t)) (renTm ρ a) (renTm (extR ρ) b) ⟶ z)
        (sym (ren-comm ρ b t))
        (fcase-s _ _ _)
⟶-ren ρ (psplit-β b x y) =
  subst (λ z → psplit (renTm (extR (extR ρ)) b) (pair (renTm ρ x) (renTm ρ y)) ⟶ z)
        (sym (ren-comm2 ρ b x y))
        (psplit-β _ _ _)
⟶-ren ρ (tr-J-Fin c a m s e) =
  tr-J-Fin (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m) (renTm ρ s) (renTm ρ e)
⟶-ren ρ (ξ-⌜IMu⌝ᴵ r) = ξ-⌜IMu⌝ᴵ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜IMu⌝ᴰ r) = ξ-⌜IMu⌝ᴰ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜IMu⌝ⁱ r) = ξ-⌜IMu⌝ⁱ (⟶-ren ρ r)
⟶-ren ρ (ξ-con r) = ξ-con (⟶-ren ρ r)
⟶-ren ρ (ξ-ielimᴰ r) = ξ-ielimᴰ (⟶-ren ρ r)
⟶-ren ρ (ξ-ielimⁱ r) = ξ-ielimⁱ (⟶-ren ρ r)
⟶-ren ρ (ξ-ielimᵉ r) = ξ-ielimᵉ (⟶-ren ρ r)
⟶-ren ρ (ξ-ielimᵗ r) = ξ-ielimᵗ (⟶-ren ρ r)
⟶-ren ρ (ξ-dι r) = ξ-dι (⟶-ren ρ r)
⟶-ren ρ (ξ-dσˢ r) = ξ-dσˢ (⟶-ren ρ r)
⟶-ren ρ (ξ-dσᶠ r) = ξ-dσᶠ (⟶-ren ρ r)
⟶-ren ρ (ξ-dρʲ r) = ξ-dρʲ (⟶-ren ρ r)
⟶-ren ρ (ξ-dρᶜ r) = ξ-dρᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-dpayᴵ r) = ξ-dpayᴵ (⟶-ren ρ r)
⟶-ren ρ (ξ-dpayᴰ r) = ξ-dpayᴰ (⟶-ren ρ r)
⟶-ren ρ (ξ-dpayᶜ r) = ξ-dpayᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-dpayⁱ r) = ξ-dpayⁱ (⟶-ren ρ r)
⟶-ren ρ (ξ-dihᴰ r) = ξ-dihᴰ (⟶-ren ρ r)
⟶-ren ρ (ξ-dihᵉ r) = ξ-dihᵉ (⟶-ren ρ r)
⟶-ren ρ (ξ-dihᶜ r) = ξ-dihᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-dihᵖ r) = ξ-dihᵖ (⟶-ren ρ r)
⟶-ren ρ (ξ-fsuc r) = ξ-fsuc (⟶-ren ρ r)
⟶-ren ρ (ξ-fcaseᵗ r) = ξ-fcaseᵗ (⟶-ren ρ r)
⟶-ren ρ (ξ-fcaseᵃ r) = ξ-fcaseᵃ (⟶-ren ρ r)
⟶-ren ρ (ξ-fcaseᵇ r) = ξ-fcaseᵇ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-fcase0 r) = ξ-fcase0 (⟶-ren ρ r)
⟶-ren ρ (ξ-psplitᵇ r) = ξ-psplitᵇ (⟶-ren (extR (extR ρ)) r)
⟶-ren ρ (ξ-psplitᵍ r) = ξ-psplitᵍ (⟶-ren ρ r)
⟶-ren ρ (ξ-nsuc r)    = ξ-nsuc (⟶-ren ρ r)
⟶-ren ρ (ξ-natrecᶻ r) = ξ-natrecᶻ (⟶-ren ρ r)
⟶-ren ρ (ξ-natrecˢ r) = ξ-natrecˢ (⟶-ren (extR (extR ρ)) r)
⟶-ren ρ (ξ-natrecⁿ r) = ξ-natrecⁿ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Π⌝ˡ r) = ξ-⌜Π⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Π⌝ʳ r) = ξ-⌜Π⌝ʳ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-⌜Σ⌝ˡ r) = ξ-⌜Σ⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Σ⌝ʳ r) = ξ-⌜Σ⌝ʳ (⟶-ren (extR ρ) r)
⟶-ren ρ (tr-J-Unit c a m s e) =
  tr-J-Unit (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
            (renTm ρ s) (renTm ρ e)
⟶-ren ρ (tr-J-IMu c a m s e) =
  tr-J-IMu (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
           (renTm ρ s) (renTm ρ e)
⟶-ren ρ (tr-J-base c a m s e) =
  tr-J-base (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
            (renTm ρ s) (renTm ρ e)
⟶-ren ρ (tr-J-Σ c a m c₁ c₂ s e) =
  tr-J-Σ (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
         (renTm ρ c₁) (renTm (extR ρ) c₂)
         (renTm ρ s) (renTm ρ e)
⟶-ren ρ (tr-taut f e) = tr-taut (renTm (extR ρ) f) (renTm ρ e)
⟶-ren ρ (hrefl-pw C t key) =
  subst (λ z → hrefl (renTm ρ C) (renTm ρ t) ⟶ z)
        (cong₂ (λ x y → lam (hrefl x (app y (var vz))))
               (pwBody-ren ρ C key) (sym (wk-ren ρ t)))
        (hrefl-pw (renTm ρ C) (renTm ρ t)
                  (trans (pw?-ren ρ C) key))
⟶-ren ρ (tr-J-Hom c a m c₁ a₁ b₁ t e key) =
  tr-J-Hom (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
           (renTm ρ c₁) (renTm ρ a₁) (renTm ρ b₁)
           (renTm ρ t) (renTm ρ e) (trans (stkA?-ren ρ c₁) key)
⟶-ren ρ (tr-pw c a f e key) =
  subst (λ z → tr (⌜Hom⌝ (renTm (extR ρ) c) (renTm (extR ρ) a) (var vz))
                  (lam (renTm (extR ρ) f)) (renTm ρ e) ⟶ z)
        (cong lam
          (tr-cong₃
            (⌜Hom⌝-cong₃
              (trans (cong (renTm pwShift) (pwBody-ren (extR ρ) c key))
                     (sym (pwShift-ren ρ (pwBody c))))
              (cong (λ z → app z (var (vs vz))) (sym (wk-ren (extR ρ) a)))
              refl)
            refl
            (cong (λ z → app z (var vz)) (sym (wk-ren ρ e)))))
        (tr-pw (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) f)
               (renTm ρ e) (trans (pw?-ren (extR ρ) c) key))
⟶-ren ρ (ξ-⌜Hom⌝ᶜ r) = ξ-⌜Hom⌝ᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Hom⌝ˡ r) = ξ-⌜Hom⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Hom⌝ʳ r) = ξ-⌜Hom⌝ʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-hreflᶜ r) = ξ-hreflᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-hreflᵃ r) = ξ-hreflᵃ (⟶-ren ρ r)
⟶-ren ρ (ξ-trᵈ r)    = ξ-trᵈ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-trᵖ r)    = ξ-trᵖ (⟶-ren ρ r)
⟶-ren ρ (ξ-trᵉ r)    = ξ-trᵉ (⟶-ren ρ r)
⟶-ren ρ (ap-J cB b c₁ s key) =
  subst (λ z → ap (renTm ρ cB) (renTm (extR ρ) b)
                  (hrefl (renTm ρ c₁) (renTm ρ s))
               ⟶ hrefl (renTm ρ cB) z)
        (sym (ren-comm ρ b s))
        (ap-J (renTm ρ cB) (renTm (extR ρ) b) (renTm ρ c₁) (renTm ρ s)
              (trans (stkC?-ren ρ c₁) key))
⟶-ren ρ (ξ-apᶜ r) = ξ-apᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-apᵇ r) = ξ-apᵇ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-apᵖ r) = ξ-apᵖ (⟶-ren ρ r)
⟶-ren ρ (tr-J-Id c a m c₁ a₁ b₁ s e) =
  tr-J-Id (renTm (extR ρ) c) (renTm (extR ρ) a) (renTm (extR ρ) m)
          (renTm ρ c₁) (renTm ρ a₁) (renTm ρ b₁) (renTm ρ s) (renTm ρ e)
⟶-ren ρ (jsub-refl d c s e) =
  jsub-refl (renTm (extR ρ) d) (renTm ρ c) (renTm ρ s) (renTm ρ e)
⟶-ren ρ (ξ-⌜Id⌝ᶜ r) = ξ-⌜Id⌝ᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Id⌝ˡ r) = ξ-⌜Id⌝ˡ (⟶-ren ρ r)
⟶-ren ρ (ξ-⌜Id⌝ʳ r) = ξ-⌜Id⌝ʳ (⟶-ren ρ r)
⟶-ren ρ (ξ-idreflᶜ r) = ξ-idreflᶜ (⟶-ren ρ r)
⟶-ren ρ (ξ-idreflᵃ r) = ξ-idreflᵃ (⟶-ren ρ r)
⟶-ren ρ (ξ-jsubᵈ r) = ξ-jsubᵈ (⟶-ren (extR ρ) r)
⟶-ren ρ (ξ-jsubᵖ r) = ξ-jsubᵖ (⟶-ren ρ r)
⟶-ren ρ (ξ-jsubᵉ r) = ξ-jsubᵉ (⟶-ren ρ r)

⟶*-ren : (ρ : Ren Γ Δ) {t u : RTm Γ} → t ⟶* u → renTm ρ t ⟶* renTm ρ u
⟶*-ren ρ done       = done
⟶*-ren ρ (step r p) = step (⟶-ren ρ r) (⟶*-ren ρ p)

------------------------------------------------------------------------
-- ★★★ AND THE **SUBSTITUTION-MONOTONICITY** BLOCK COMES TOO — `stkA?-red`,
--   `stkC?-red`, `extS-mono`, `subTm-monoˢ`, `single-mono`.
--
-- ⚠⚠ THIS IS THE ONE THAT MATTERS.  These five are ALL that
--   `Metatheory/SubjectReduction` needed from `Confluence` besides
--   `church-rosser` — and `SubjectReduction` is imported by ~90 knot
--   modules, MOST OF WHICH USE EXACTLY ONE NAME FROM IT (`⊢wk`).  So
--   every knot leaf was paying 8.9 MB of confluence proof to weaken a
--   derivation.  Moving these lets the typing-side structural lemmas be
--   split off `SubjectReduction` with NO `Confluence` dependency at all.
--
-- ★ The cut is exact: everything above the original line 358 is `⟹`-free;
--   `infix 3 _⟹_` is the first line that is not.  What stays behind in
--   `Confluence` is the parallel-reduction proof and nothing else.
------------------------------------------------------------------------


-- W2b: the classifier keys are closed under reduction, and the body
-- function maps a code's step to steps of the body — the content of
-- the hrefl-pw/ξ-hreflᶜ and tr-pw/ξ-trᵈ critical-pair joins.
pw?-red : {C C' : RTm Γ} → C ⟶ C' → pw? C ≡ true → pw? C' ≡ true
pw?-red (β _ _) ()
pw?-red (βfst _ _) ()
pw?-red (βsnd _ _) ()
pw?-red (ξ-lam _) ()
pw?-red (ξ-appˡ _) ()
pw?-red (ξ-appʳ _) ()
pw?-red (ξ-pairˡ _) ()
pw?-red (ξ-pairʳ _) ()
pw?-red (ξ-fst _) ()
pw?-red (ξ-snd _) ()
pw?-red (ξ-⌜Π⌝ˡ r) h = refl
pw?-red (ξ-⌜Π⌝ʳ r) h = refl
pw?-red (ξ-⌜Σ⌝ˡ _) ()
pw?-red (ξ-⌜Σ⌝ʳ _) ()
pw?-red (ξ-⌜Hom⌝ᶜ r) h = pw?-red r h
pw?-red (ξ-⌜Hom⌝ˡ r) h = h
pw?-red (ξ-⌜Hom⌝ʳ r) h = h
pw?-red (ξ-hreflᶜ _) ()
pw?-red (ξ-hreflᵃ _) ()
pw?-red (hrefl-pw _ _ _) ()
pw?-red (tr-J-base _ _ _ _ _) ()
pw?-red (tr-J-Σ _ _ _ _ _ _ _) ()
pw?-red (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
pw?-red (tr-taut _ _) ()
pw?-red (tr-pw _ _ _ _ _) ()
pw?-red (ξ-trᵈ _) ()
pw?-red (ξ-trᵖ _) ()
pw?-red (ξ-trᵉ _) ()

-- ★ the `stkA?` peer (SpikeNatJ split).  Same shape: no stable code
-- is a redex, so every arm is absurd or a component congruence.
stkA?-red : {C C' : RTm Γ} → C ⟶ C' → stkA? C ≡ true → stkA? C' ≡ true
stkA?-red (β _ _) ()
stkA?-red (βfst _ _) ()
stkA?-red (βsnd _ _) ()
stkA?-red (ξ-lam _) ()
stkA?-red (ξ-appˡ _) ()
stkA?-red (ξ-appʳ _) ()
stkA?-red (ξ-pairˡ _) ()
stkA?-red (ξ-pairʳ _) ()
stkA?-red (ξ-fst _) ()
stkA?-red (ξ-snd _) ()
stkA?-red (ξ-⌜Π⌝ˡ _) ()
stkA?-red (ξ-⌜Π⌝ʳ _) ()
-- ⚠ §10.4: `stkA? (⌜IMu⌝ …)` is `true` and the INDEX steps, so this is
--   a real preservation row, not an absurdity.
stkA?-red (ξ-⌜IMu⌝ᴵ r) h = refl
stkA?-red (ξ-⌜IMu⌝ᴰ r) h = refl
stkA?-red (ξ-⌜IMu⌝ⁱ r) h = refl
stkA?-red (ξ-⌜Σ⌝ˡ r) h = refl
stkA?-red (ξ-⌜Σ⌝ʳ r) h = refl
stkA?-red (ξ-⌜Hom⌝ᶜ r) h = stkA?-red r h
stkA?-red (ξ-⌜Id⌝ᶜ r) h = refl
stkA?-red (ξ-⌜Id⌝ˡ r) h = refl
stkA?-red (ξ-⌜Id⌝ʳ r) h = refl
stkA?-red (ξ-⌜Hom⌝ˡ r) h = h
stkA?-red (ξ-⌜Hom⌝ʳ r) h = h
stkA?-red (ξ-hreflᶜ _) ()
stkA?-red (ξ-hreflᵃ _) ()
stkA?-red (hrefl-pw _ _ _) ()
stkA?-red (tr-J-base _ _ _ _ _) ()
stkA?-red (tr-J-Σ _ _ _ _ _ _ _) ()
stkA?-red (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
stkA?-red (tr-taut _ _) ()
stkA?-red (tr-pw _ _ _ _ _) ()
stkA?-red (ξ-trᵈ _) ()
stkA?-red (ξ-trᵖ _) ()
stkA?-red (ξ-trᵉ _) ()

stkC?-red : {C C' : RTm Γ} → C ⟶ C' → stkC? C ≡ true → stkC? C' ≡ true
stkC?-red (β _ _) ()
stkC?-red (βfst _ _) ()
stkC?-red (βsnd _ _) ()
stkC?-red (ξ-lam _) ()
stkC?-red (ξ-appˡ _) ()
stkC?-red (ξ-appʳ _) ()
stkC?-red (ξ-pairˡ _) ()
stkC?-red (ξ-pairʳ _) ()
stkC?-red (ξ-fst _) ()
stkC?-red (ξ-snd _) ()
stkC?-red (ξ-⌜Π⌝ˡ _) ()
stkC?-red (ξ-⌜Π⌝ʳ _) ()
stkC?-red (ξ-⌜IMu⌝ᴵ r) h = refl
stkC?-red (ξ-⌜IMu⌝ᴰ r) h = refl
stkC?-red (ξ-⌜IMu⌝ⁱ r) h = refl
stkC?-red (ξ-⌜Σ⌝ˡ r) h = refl
stkC?-red (ξ-⌜Σ⌝ʳ r) h = refl
stkC?-red (ξ-⌜Hom⌝ᶜ r) h = stkA?-red r h
stkC?-red (ξ-⌜Id⌝ᶜ r) h = refl
stkC?-red (ξ-⌜Id⌝ˡ r) h = refl
stkC?-red (ξ-⌜Id⌝ʳ r) h = refl
stkC?-red (ξ-⌜Hom⌝ˡ r) h = h
stkC?-red (ξ-⌜Hom⌝ʳ r) h = h
stkC?-red (ξ-hreflᶜ _) ()
stkC?-red (ξ-hreflᵃ _) ()
stkC?-red (hrefl-pw _ _ _) ()
stkC?-red (tr-J-base _ _ _ _ _) ()
stkC?-red (tr-J-Σ _ _ _ _ _ _ _) ()
stkC?-red (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
stkC?-red (tr-taut _ _) ()
stkC?-red (tr-pw _ _ _ _ _) ()
stkC?-red (ξ-trᵈ _) ()
stkC?-red (ξ-trᵖ _) ()
stkC?-red (ξ-trᵉ _) ()

pwBody-red : {C C' : RTm Γ} → C ⟶ C' → pw? C ≡ true →
             pwBody C ⟶* pwBody C'
pwBody-red (β _ _) ()
pwBody-red (βfst _ _) ()
pwBody-red (βsnd _ _) ()
pwBody-red (ξ-lam _) ()
pwBody-red (ξ-appˡ _) ()
pwBody-red (ξ-appʳ _) ()
pwBody-red (ξ-pairˡ _) ()
pwBody-red (ξ-pairʳ _) ()
pwBody-red (ξ-fst _) ()
pwBody-red (ξ-snd _) ()
pwBody-red (ξ-⌜Π⌝ˡ r) h = done
pwBody-red (ξ-⌜Π⌝ʳ r) h = step r done
pwBody-red (ξ-⌜Σ⌝ˡ _) ()
pwBody-red (ξ-⌜Σ⌝ʳ _) ()
pwBody-red (ξ-⌜Hom⌝ᶜ r) h = ⟶*-⌜Hom⌝ᶜ (pwBody-red r h)
pwBody-red (ξ-⌜Hom⌝ˡ r) h = step (ξ-⌜Hom⌝ˡ (ξ-appˡ (⟶-ren vs r))) done
pwBody-red (ξ-⌜Hom⌝ʳ r) h = step (ξ-⌜Hom⌝ʳ (ξ-appˡ (⟶-ren vs r))) done
pwBody-red (ξ-hreflᶜ _) ()
pwBody-red (ξ-hreflᵃ _) ()
pwBody-red (hrefl-pw _ _ _) ()
pwBody-red (tr-J-base _ _ _ _ _) ()
pwBody-red (tr-J-Σ _ _ _ _ _ _ _) ()
pwBody-red (tr-J-Hom _ _ _ _ _ _ _ _ _) ()
pwBody-red (tr-taut _ _) ()
pwBody-red (tr-pw _ _ _ _ _) ()
pwBody-red (ξ-trᵈ _) ()
pwBody-red (ξ-trᵖ _) ()
pwBody-red (ξ-trᵉ _) ()

pwBody-red* : {C C' : RTm Γ} → pw? C ≡ true → C ⟶* C' →
              pwBody C ⟶* pwBody C'
pwBody-red* h done       = done
pwBody-red* h (step r p) =
  ⟶*-trans (pwBody-red r h) (pwBody-red* (pw?-red r h) p)


------------------------------------------------------------------------
-- Substitution is monotone in the substitution (pointwise `⟶*`).
------------------------------------------------------------------------

extS-mono : {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟶* σ' x) →
            ∀ (x : Var (Γ ∙)) → extS σ x ⟶* extS σ' x
extS-mono h vz     = done
extS-mono h (vs x) = ⟶*-ren vs (h x)

subTm-monoˢ : {σ σ' : Sub Γ Δ} → (∀ x → σ x ⟶* σ' x) →
              (t : RTm Γ) → subTm σ t ⟶* subTm σ' t
subTm-monoˢ h (var x)   = h x
subTm-monoˢ h (lam t)   = ⟶*-lam (subTm-monoˢ (extS-mono h) t)
subTm-monoˢ h (app t u) =
  ⟶*-trans (⟶*-appˡ (subTm-monoˢ h t)) (⟶*-appʳ (subTm-monoˢ h u))
subTm-monoˢ h (pair a b) =
  ⟶*-trans (⟶*-pairˡ (subTm-monoˢ h a)) (⟶*-pairʳ (subTm-monoˢ h b))
subTm-monoˢ h (ordtr a t u p q) =
  ⟶*-trans (⟶*-ordtrᵃ (subTm-monoˢ h a))
   (⟶*-trans (⟶*-ordtrᵗ (subTm-monoˢ h t))
    (⟶*-trans (⟶*-ordtrᵘ (subTm-monoˢ h u))
     (⟶*-trans (⟶*-ordtrᵖ (subTm-monoˢ h p)) (⟶*-ordtrq (subTm-monoˢ h q)))))
subTm-monoˢ h (absurd c₁ p) =
  ⟶*-trans (⟶*-absurdᶜ (subTm-monoˢ h c₁)) (⟶*-absurdᵉ (subTm-monoˢ h p))
subTm-monoˢ h (fst p) = ⟶*-fst (subTm-monoˢ h p)
subTm-monoˢ h (snd p) = ⟶*-snd (subTm-monoˢ h p)
subTm-monoˢ h ⌜base⌝  = done
subTm-monoˢ h (⌜Π⌝ c d) =
  ⟶*-trans (⟶*-⌜Π⌝ˡ (subTm-monoˢ h c)) (⟶*-⌜Π⌝ʳ (subTm-monoˢ (extS-mono h) d))
subTm-monoˢ h (⌜Σ⌝ c d) =
  ⟶*-trans (⟶*-⌜Σ⌝ˡ (subTm-monoˢ h c)) (⟶*-⌜Σ⌝ʳ (subTm-monoˢ (extS-mono h) d))
subTm-monoˢ h (⌜Hom⌝ c a b) =
  ⟶*-trans (⟶*-⌜Hom⌝ᶜ (subTm-monoˢ h c))
           (⟶*-trans (⟶*-⌜Hom⌝ˡ (subTm-monoˢ h a))
                     (⟶*-⌜Hom⌝ʳ (subTm-monoˢ h b)))
subTm-monoˢ h (hrefl c t) =
  ⟶*-trans (⟶*-hreflᶜ (subTm-monoˢ h c)) (⟶*-hreflᵃ (subTm-monoˢ h t))
subTm-monoˢ h (tr d p e) =
  ⟶*-trans (⟶*-trᵈ (subTm-monoˢ (extS-mono h) d))
           (⟶*-trans (⟶*-trᵖ (subTm-monoˢ h p)) (⟶*-trᵉ (subTm-monoˢ h e)))
subTm-monoˢ h (ap c b p) =
  ⟶*-trans (⟶*-apᶜ (subTm-monoˢ h c))
           (⟶*-trans (⟶*-apᵇ (subTm-monoˢ (extS-mono h) b))
                     (⟶*-apᵖ (subTm-monoˢ h p)))
subTm-monoˢ h (⌜Id⌝ c a b) =
  ⟶*-trans (⟶*-⌜Id⌝ᶜ (subTm-monoˢ h c))
           (⟶*-trans (⟶*-⌜Id⌝ˡ (subTm-monoˢ h a))
                     (⟶*-⌜Id⌝ʳ (subTm-monoˢ h b)))
subTm-monoˢ h (idrefl c t) =
  ⟶*-trans (⟶*-idreflᶜ (subTm-monoˢ h c)) (⟶*-idreflᵃ (subTm-monoˢ h t))
subTm-monoˢ h ⌜Nat⌝    = done
subTm-monoˢ h ⌜Unit⌝   = done
subTm-monoˢ h unit     = done
subTm-monoˢ h nzero    = done
subTm-monoˢ h (nsuc n) = ⟶*-nsuc (subTm-monoˢ h n)
subTm-monoˢ h (⌜Fin⌝ n) = done
subTm-monoˢ h fzero = done
subTm-monoˢ h (⌜IMu⌝ I D i) =
  ⟶*-trans (⟶*-⌜IMu⌝ᴵ (subTm-monoˢ h I)) (⟶*-trans (⟶*-⌜IMu⌝ᴰ (subTm-monoˢ h D)) (⟶*-⌜IMu⌝ⁱ (subTm-monoˢ h i)))
subTm-monoˢ h (con p) =
  ⟶*-con (subTm-monoˢ h p)
subTm-monoˢ h (ielim D i e t) =
  ⟶*-trans (⟶*-ielimᴰ (subTm-monoˢ h D)) (⟶*-trans (⟶*-ielimⁱ (subTm-monoˢ h i)) (⟶*-trans (⟶*-ielimᵉ (subTm-monoˢ h e)) (⟶*-ielimᵗ (subTm-monoˢ h t))))
subTm-monoˢ h (dι j) =
  ⟶*-dι (subTm-monoˢ h j)
subTm-monoˢ h (dσ S f) =
  ⟶*-trans (⟶*-dσˢ (subTm-monoˢ h S)) (⟶*-dσᶠ (subTm-monoˢ h f))
subTm-monoˢ h (dρ j C) =
  ⟶*-trans (⟶*-dρʲ (subTm-monoˢ h j)) (⟶*-dρᶜ (subTm-monoˢ h C))
subTm-monoˢ h (dpay I D C i) =
  ⟶*-trans (⟶*-dpayᴵ (subTm-monoˢ h I)) (⟶*-trans (⟶*-dpayᴰ (subTm-monoˢ h D)) (⟶*-trans (⟶*-dpayᶜ (subTm-monoˢ h C)) (⟶*-dpayⁱ (subTm-monoˢ h i))))
subTm-monoˢ h (dih D e C p) =
  ⟶*-trans (⟶*-dihᴰ (subTm-monoˢ h D)) (⟶*-trans (⟶*-dihᵉ (subTm-monoˢ h e)) (⟶*-trans (⟶*-dihᶜ (subTm-monoˢ h C)) (⟶*-dihᵖ (subTm-monoˢ h p))))
subTm-monoˢ h (fsuc t) =
  ⟶*-fsuc (subTm-monoˢ h t)
subTm-monoˢ h (fcase t a b) =
  ⟶*-trans (⟶*-fcaseᵗ (subTm-monoˢ h t)) (⟶*-trans (⟶*-fcaseᵃ (subTm-monoˢ h a)) (⟶*-fcaseᵇ (subTm-monoˢ (extS-mono h) b)))
subTm-monoˢ h (fcase0 t) =
  ⟶*-fcase0 (subTm-monoˢ h t)
subTm-monoˢ h (psplit b q) =
  ⟶*-trans (⟶*-psplitᵇ (subTm-monoˢ (extS-mono (extS-mono h)) b)) (⟶*-psplitᵍ (subTm-monoˢ h q))
subTm-monoˢ h (natrec z s n) =
  ⟶*-trans (⟶*-natrecᶻ (subTm-monoˢ h z))
           (⟶*-trans (⟶*-natrecˢ (subTm-monoˢ (extS-mono (extS-mono h)) s))
                     (⟶*-natrecⁿ (subTm-monoˢ h n)))
subTm-monoˢ h (jsub d p e) =
  ⟶*-trans (⟶*-jsubᵈ (subTm-monoˢ (extS-mono h) d))
           (⟶*-trans (⟶*-jsubᵖ (subTm-monoˢ h p))
                     (⟶*-jsubᵉ (subTm-monoˢ h e)))


single-mono : {u u' : RTm Γ} → u ⟶* u' →
              ∀ (x : Var (Γ ∙)) → single u x ⟶* single u' x
single-mono p vz     = p
single-mono p (vs x) = done

------------------------------------------------------------------------
-- Parallel reduction, reflexivity, and the two inclusions.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- ★★★ AND THE **TYPE-LEVEL** MULTI-STEP RELATION `_⟶ᵀ*_` WITH ITS
--   CONGRUENCES — lifted out of `Metatheory/Injectivity` for the SAME
--   reason, and it is the piece that makes the `SubjectReduction` split
--   possible at all.
--
-- ⚠ `Metatheory/TySub` needs `_⟶ᵀ*_`, its congruences and `red→≅ᵀ`, and
--   NOTHING else from `Injectivity`.  The genuine injectivity results —
--   `Π-inj`, `Π-reduct`, `Id-reduct`, `church-rosserᵀ`, the `⟹ᵀ` layer —
--   are only ever used by `sr`'s reduct analyses, which stay behind.
--   Leaving these fifteen definitions in `Injectivity` would have forced
--   every knot module to load the 5.4 MB injectivity proof to weaken a
--   derivation.
--
-- ★ THEY ARE ALL FOLDS.  Not one mentions `⟹` or confluence; each is
--   three lines over `doneᵀ`/`stepᵀ`.  `Injectivity` re-exports them
--   `public`, so its own callers are unaffected.
------------------------------------------------------------------------

infix 3 _⟶ᵀ*_
data _⟶ᵀ*_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  doneᵀ : {A : RTy Γ} → A ⟶ᵀ* A
  stepᵀ : {A B C : RTy Γ} → A ⟶ᵀ B → B ⟶ᵀ* C → A ⟶ᵀ* C

⟶ᵀ*-trans : {A B C : RTy Γ} → A ⟶ᵀ* B → B ⟶ᵀ* C → A ⟶ᵀ* C
⟶ᵀ*-trans doneᵀ       q = q
⟶ᵀ*-trans (stepᵀ r p) q = stepᵀ r (⟶ᵀ*-trans p q)

⟶ᵀ*-El : {t t' : RTm Γ} → t ⟶* t' → El t ⟶ᵀ* El t'
⟶ᵀ*-El done       = doneᵀ
⟶ᵀ*-El (step r p) = stepᵀ (ξ-El r) (⟶ᵀ*-El p)

⟶ᵀ*-Πˡ : {A A' : RTy Γ} {B : RTy (Γ ∙)} → A ⟶ᵀ* A' → Π A B ⟶ᵀ* Π A' B
⟶ᵀ*-Πˡ doneᵀ       = doneᵀ
⟶ᵀ*-Πˡ (stepᵀ r p) = stepᵀ (ξ-Πˡ r) (⟶ᵀ*-Πˡ p)

⟶ᵀ*-Πʳ : {A : RTy Γ} {B B' : RTy (Γ ∙)} → B ⟶ᵀ* B' → Π A B ⟶ᵀ* Π A B'
⟶ᵀ*-Πʳ doneᵀ       = doneᵀ
⟶ᵀ*-Πʳ (stepᵀ r p) = stepᵀ (ξ-Πʳ r) (⟶ᵀ*-Πʳ p)

⟶ᵀ*-Σˡ : {A A' : RTy Γ} {B : RTy (Γ ∙)} → A ⟶ᵀ* A' → Σ' A B ⟶ᵀ* Σ' A' B
⟶ᵀ*-Σˡ doneᵀ       = doneᵀ
⟶ᵀ*-Σˡ (stepᵀ r p) = stepᵀ (ξ-Σˡ r) (⟶ᵀ*-Σˡ p)

⟶ᵀ*-Σʳ : {A : RTy Γ} {B B' : RTy (Γ ∙)} → B ⟶ᵀ* B' → Σ' A B ⟶ᵀ* Σ' A B'
⟶ᵀ*-Σʳ doneᵀ       = doneᵀ
⟶ᵀ*-Σʳ (stepᵀ r p) = stepᵀ (ξ-Σʳ r) (⟶ᵀ*-Σʳ p)

⟶ᵀ*-Homᵀ : {A A' : RTy Γ} {t u : RTm Γ} → A ⟶ᵀ* A' → Hom A t u ⟶ᵀ* Hom A' t u
⟶ᵀ*-Homᵀ doneᵀ       = doneᵀ
⟶ᵀ*-Homᵀ (stepᵀ r p) = stepᵀ (ξ-Homᵀ r) (⟶ᵀ*-Homᵀ p)

⟶ᵀ*-Homˡ : {A : RTy Γ} {t t' u : RTm Γ} → t ⟶* t' → Hom A t u ⟶ᵀ* Hom A t' u
⟶ᵀ*-Homˡ done       = doneᵀ
⟶ᵀ*-Homˡ (step r p) = stepᵀ (ξ-Homˡ r) (⟶ᵀ*-Homˡ p)

⟶ᵀ*-Homʳ : {A : RTy Γ} {t u u' : RTm Γ} → u ⟶* u' → Hom A t u ⟶ᵀ* Hom A t u'
⟶ᵀ*-Homʳ done       = doneᵀ
⟶ᵀ*-Homʳ (step r p) = stepᵀ (ξ-Homʳ r) (⟶ᵀ*-Homʳ p)

-- the levitated types' congruences, closed under ⟶ᵀ*
⟶ᵀ*-IMuᴵ : {I I' D i : RTm Γ} → I ⟶* I' → IMu I D i ⟶ᵀ* IMu I' D i
⟶ᵀ*-IMuᴵ done       = doneᵀ
⟶ᵀ*-IMuᴵ (step r p) = stepᵀ (ξ-IMuᴵ r) (⟶ᵀ*-IMuᴵ p)

⟶ᵀ*-IMuᴰ : {I D D' i : RTm Γ} → D ⟶* D' → IMu I D i ⟶ᵀ* IMu I D' i
⟶ᵀ*-IMuᴰ done       = doneᵀ
⟶ᵀ*-IMuᴰ (step r p) = stepᵀ (ξ-IMuᴰ r) (⟶ᵀ*-IMuᴰ p)

-- the INDEX congruence keeps its old name (`IMu`'s analogue of `⟶ᵀ*-Idˡ`)
⟶ᵀ*-IMu : {I D i i' : RTm Γ} → i ⟶* i' → IMu I D i ⟶ᵀ* IMu I D i'
⟶ᵀ*-IMu done       = doneᵀ
⟶ᵀ*-IMu (step r p) = stepᵀ (ξ-IMuⁱ r) (⟶ᵀ*-IMu p)

⟶ᵀ*-Desc : {I I' : RTm Γ} → I ⟶* I' → Desc I ⟶ᵀ* Desc I'
⟶ᵀ*-Desc done       = doneᵀ
⟶ᵀ*-Desc (step r p) = stepᵀ (ξ-Desc r) (⟶ᵀ*-Desc p)

⟶ᵀ*-DIhᴰ : {D D' C p : RTm Γ} {M : RTy ((Γ ∙) ∙)} → D ⟶* D' → DIh D M C p ⟶ᵀ* DIh D' M C p
⟶ᵀ*-DIhᴰ done       = doneᵀ
⟶ᵀ*-DIhᴰ (step r q) = stepᵀ (ξ-DIhᴰ r) (⟶ᵀ*-DIhᴰ q)

⟶ᵀ*-DIhᴹ : {D C p : RTm Γ} {M M' : RTy ((Γ ∙) ∙)} → M ⟶ᵀ* M' → DIh D M C p ⟶ᵀ* DIh D M' C p
⟶ᵀ*-DIhᴹ doneᵀ       = doneᵀ
⟶ᵀ*-DIhᴹ (stepᵀ r q) = stepᵀ (ξ-DIhᴹ r) (⟶ᵀ*-DIhᴹ q)

⟶ᵀ*-DIhᶜ : {D C C' p : RTm Γ} {M : RTy ((Γ ∙) ∙)} → C ⟶* C' → DIh D M C p ⟶ᵀ* DIh D M C' p
⟶ᵀ*-DIhᶜ done       = doneᵀ
⟶ᵀ*-DIhᶜ (step r q) = stepᵀ (ξ-DIhᶜ r) (⟶ᵀ*-DIhᶜ q)

⟶ᵀ*-DIhᵖ : {D C p p' : RTm Γ} {M : RTy ((Γ ∙) ∙)} → p ⟶* p' → DIh D M C p ⟶ᵀ* DIh D M C p'
⟶ᵀ*-DIhᵖ done       = doneᵀ
⟶ᵀ*-DIhᵖ (step r q) = stepᵀ (ξ-DIhᵖ r) (⟶ᵀ*-DIhᵖ q)

⟶ᵀ*-Idᵀ : {A A' : RTy Γ} {t u : RTm Γ} → A ⟶ᵀ* A' → Id A t u ⟶ᵀ* Id A' t u
⟶ᵀ*-Idᵀ doneᵀ       = doneᵀ
⟶ᵀ*-Idᵀ (stepᵀ r p) = stepᵀ (ξ-Idᵀ r) (⟶ᵀ*-Idᵀ p)

⟶ᵀ*-Idˡ : {A : RTy Γ} {t t' u : RTm Γ} → t ⟶* t' → Id A t u ⟶ᵀ* Id A t' u
⟶ᵀ*-Idˡ done       = doneᵀ
⟶ᵀ*-Idˡ (step r p) = stepᵀ (ξ-Idˡ r) (⟶ᵀ*-Idˡ p)

⟶ᵀ*-Idʳ : {A : RTy Γ} {t u u' : RTm Γ} → u ⟶* u' → Id A t u ⟶ᵀ* Id A t u'
⟶ᵀ*-Idʳ done       = doneᵀ
⟶ᵀ*-Idʳ (step r p) = stepᵀ (ξ-Idʳ r) (⟶ᵀ*-Idʳ p)

-- reductions ⊆ conversion.
red→≅ᵀ : {A B : RTy Γ} → A ⟶ᵀ* B → A ≅ᵀ B
red→≅ᵀ doneᵀ       = crflᵀ
red→≅ᵀ (stepᵀ r p) = ctrnᵀ (credᵀ r) (red→≅ᵀ p)
