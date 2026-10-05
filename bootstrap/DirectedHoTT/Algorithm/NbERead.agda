-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ READING a value as a term (PLAN-EVAL E3, §2c).
--
-- The soundness of the environment evaluator (`Algorithm/NbE`) is proved
-- by reading every value back as a — not necessarily normal — TERM and
-- showing each evaluation step is a conversion between readings.  This
-- module is the reading and its algebra; no reduction yet.
--
-- ★ LEVELS are read through a total map `L : ℕ → RTm Δ` (what each level
--   stands for), so reading needs no scope argument; the readback's own
--   map is `lvl Δ`.  Under a binder the map is weakened (`wkL`).
--
-- ★ A DEFUNCTIONALISED closure reads as its rule's right-hand-side body;
--   `cloTrPw` is the exception (its rule's side condition is syntactic):
--   `vlam (cloTrPw d f e)` reads as the REDEX `tr ⌊d⌋ (lam ⌊f⌋) ⌊e⌋`.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.NbERead where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; _×_; _,_; ⊤; tt )
open import Agda.Builtin.Nat using ( zero; suc; _<_; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Variance using ( pwBody )
open import DirectedHoTT.Algorithm.NbE

private
  variable
    Γ Δ Θ : Cx

-- what the levels stand for
Lv : Cx → Set
Lv Δ = ℕ → RTm Δ

wkL : Lv Δ → Lv (Δ ∙)
wkL L l = renTm vs (L l)

wk : RTm Δ → RTm (Δ ∙)
wk = renTm vs

⌊_⌋  : Val → Lv Δ → RTm Δ
⌊_⌋ᶜ : Clo → Lv Δ → RTm (Δ ∙)
⌊_⌋² : Clo₂ → Lv Δ → RTm ((Δ ∙) ∙)
⌊_⌋ᵉ : Env Γ → Lv Δ → Sub Γ Δ

⌊ [] ⌋ᵉ     L ()
⌊ ρ , v ⌋ᵉ  L vz     = ⌊ v ⌋ L
⌊ ρ , v ⌋ᵉ  L (vs x) = ⌊ ρ ⌋ᵉ L x

⌊ clo ρ t ⌋ᶜ        L = subTm (extS (⌊ ρ ⌋ᵉ L)) t
⌊ cloK v ⌋ᶜ         L = wk (⌊ v ⌋ L)
⌊ cloHrefl C s ⌋ᶜ   L = hrefl (pwBody (⌊ C ⌋ L)) (app (wk (⌊ s ⌋ L)) (var vz))
⌊ cloDpay I D f ⌋ᶜ  L = dpay (wk (⌊ I ⌋ L)) (wk (⌊ D ⌋ L)) (app (wk (⌊ f ⌋ L)) (var vz))
⌊ cloHomTo C A ⌋ᶜ   L = ⌜Hom⌝ (wk (⌊ C ⌋ L)) (wk (⌊ A ⌋ L)) (var vz)
-- never read under a binder: `cloTrPw` only ever occurs as `vlam (cloTrPw …)`,
-- which `⌊_⌋` reads as its redex.  (Any term would do; this one is honest.)
⌊ cloTrPw d f e ⌋ᶜ  L = app (wk (tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L))) (var vz)

⌊ clo₂ ρ t ⌋² L = subTm (extS (extS (⌊ ρ ⌋ᵉ L))) t

⌊ vvar l ⌋           L = L l
⌊ vlam (cloTrPw d f e) ⌋ L = tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L)
⌊ vlam c ⌋           L = lam (⌊ c ⌋ᶜ L)
⌊ vapp f a ⌋         L = app (⌊ f ⌋ L) (⌊ a ⌋ L)
⌊ vpair a b ⌋        L = pair (⌊ a ⌋ L) (⌊ b ⌋ L)
⌊ vabsurd c e ⌋      L = absurd (⌊ c ⌋ L) (⌊ e ⌋ L)
⌊ vordtr a t u p q ⌋ L = ordtr (⌊ a ⌋ L) (⌊ t ⌋ L) (⌊ u ⌋ L) (⌊ p ⌋ L) (⌊ q ⌋ L)
⌊ vfst p ⌋           L = fst (⌊ p ⌋ L)
⌊ vsnd p ⌋           L = snd (⌊ p ⌋ L)
⌊ v⌜base⌝ ⌋          L = ⌜base⌝
⌊ v⌜Π⌝ c d ⌋         L = ⌜Π⌝ (⌊ c ⌋ L) (⌊ d ⌋ᶜ L)
⌊ v⌜Σ⌝ c d ⌋         L = ⌜Σ⌝ (⌊ c ⌋ L) (⌊ d ⌋ᶜ L)
⌊ v⌜Hom⌝ c a b ⌋     L = ⌜Hom⌝ (⌊ c ⌋ L) (⌊ a ⌋ L) (⌊ b ⌋ L)
⌊ vhrefl c t ⌋       L = hrefl (⌊ c ⌋ L) (⌊ t ⌋ L)
⌊ vtr d p e ⌋        L = tr (⌊ d ⌋ᶜ L) (⌊ p ⌋ L) (⌊ e ⌋ L)
⌊ vap c b p ⌋        L = ap (⌊ c ⌋ L) (⌊ b ⌋ᶜ L) (⌊ p ⌋ L)
⌊ v⌜Id⌝ c a b ⌋      L = ⌜Id⌝ (⌊ c ⌋ L) (⌊ a ⌋ L) (⌊ b ⌋ L)
⌊ vidrefl c t ⌋      L = idrefl (⌊ c ⌋ L) (⌊ t ⌋ L)
⌊ vjsub d p e ⌋      L = jsub (⌊ d ⌋ᶜ L) (⌊ p ⌋ L) (⌊ e ⌋ L)
⌊ vunit ⌋            L = unit
⌊ vnzero ⌋           L = nzero
⌊ vnsuc t ⌋          L = nsuc (⌊ t ⌋ L)
⌊ vnatrec z s t ⌋    L = natrec (⌊ z ⌋ L) (⌊ s ⌋² L) (⌊ t ⌋ L)
⌊ vcon p ⌋           L = con (⌊ p ⌋ L)
⌊ vielim D i e t ⌋   L = ielim (⌊ D ⌋ L) (⌊ i ⌋ L) (⌊ e ⌋ L) (⌊ t ⌋ L)
⌊ vdι ⌋              L = dι
⌊ vdσ S f ⌋          L = dσ (⌊ S ⌋ L) (⌊ f ⌋ L)
⌊ vdρ j C ⌋          L = dρ (⌊ j ⌋ L) (⌊ C ⌋ L)
⌊ vdpay I D C ⌋      L = dpay (⌊ I ⌋ L) (⌊ D ⌋ L) (⌊ C ⌋ L)
⌊ vdih D e C p ⌋     L = dih (⌊ D ⌋ L) (⌊ e ⌋ L) (⌊ C ⌋ L) (⌊ p ⌋ L)
⌊ vfzero ⌋           L = fzero
⌊ vfsuc t ⌋          L = fsuc (⌊ t ⌋ L)
⌊ vfcase t a b ⌋     L = fcase (⌊ t ⌋ L) (⌊ a ⌋ L) (⌊ b ⌋ᶜ L)
⌊ vfcase0 t ⌋        L = fcase0 (⌊ t ⌋ L)
⌊ vpsplit b p ⌋      L = psplit (⌊ b ⌋² L) (⌊ p ⌋ L)
⌊ v⌜Nat⌝ ⌋           L = ⌜Nat⌝
⌊ v⌜Unit⌝ ⌋          L = ⌜Unit⌝
⌊ v⌜IMu⌝ I D i ⌋     L = ⌜IMu⌝ (⌊ I ⌋ L) (⌊ D ⌋ L) (⌊ i ⌋ L)
⌊ v⌜Fin⌝ t ⌋         L = ⌜Fin⌝ (⌊ t ⌋ L)
⌊ vref d b ⌋         L = ref d b

------------------------------------------------------------------------
-- RENAMING commutes with reading (no scope argument: the level map is
-- renamed instead).
------------------------------------------------------------------------

wk-ren : (r : Ren Δ Θ) (t : RTm Δ) → renTm (extR r) (wk t) ≡ wk (renTm r t)
wk-ren r t = trans (renTm-renTm t) (sym (renTm-renTm t))

-- `pwBody` commutes with renaming at EVERY code (Variance's `pwBody-ren`
-- asks `pw? C`; a reading may be any term)
pwBody-ren : (r : Ren Δ Θ) (t : RTm Δ) → renTm (extR r) (pwBody t) ≡ pwBody (renTm r t)
pwBody-ren r (⌜Π⌝ γ δ) = refl
pwBody-ren r (⌜Hom⌝ C a b) =
  cong₃ ⌜Hom⌝ (pwBody-ren r C) (cong (λ z → app z (var vz)) (wk-ren r a))
                               (cong (λ z → app z (var vz)) (wk-ren r b))
pwBody-ren r t@(var _) = wk-ren r t
pwBody-ren r t@(lam _) = wk-ren r t
pwBody-ren r t@(app _ _) = wk-ren r t
pwBody-ren r t@(pair _ _) = wk-ren r t
pwBody-ren r t@(absurd _ _) = wk-ren r t
pwBody-ren r t@(ordtr _ _ _ _ _) = wk-ren r t
pwBody-ren r t@(fst _) = wk-ren r t
pwBody-ren r t@(snd _) = wk-ren r t
pwBody-ren r t@⌜base⌝ = wk-ren r t
pwBody-ren r t@(⌜Σ⌝ _ _) = wk-ren r t
pwBody-ren r t@(hrefl _ _) = wk-ren r t
pwBody-ren r t@(tr _ _ _) = wk-ren r t
pwBody-ren r t@(ap _ _ _) = wk-ren r t
pwBody-ren r t@(⌜Id⌝ _ _ _) = wk-ren r t
pwBody-ren r t@(idrefl _ _) = wk-ren r t
pwBody-ren r t@(jsub _ _ _) = wk-ren r t
pwBody-ren r t@unit = wk-ren r t
pwBody-ren r t@nzero = wk-ren r t
pwBody-ren r t@(nsuc _) = wk-ren r t
pwBody-ren r t@(natrec _ _ _) = wk-ren r t
pwBody-ren r t@(con _) = wk-ren r t
pwBody-ren r t@(ielim _ _ _ _) = wk-ren r t
pwBody-ren r t@dι = wk-ren r t
pwBody-ren r t@(dσ _ _) = wk-ren r t
pwBody-ren r t@(dρ _ _) = wk-ren r t
pwBody-ren r t@(dpay _ _ _) = wk-ren r t
pwBody-ren r t@(dih _ _ _ _) = wk-ren r t
pwBody-ren r t@fzero = wk-ren r t
pwBody-ren r t@(fsuc _) = wk-ren r t
pwBody-ren r t@(fcase _ _ _) = wk-ren r t
pwBody-ren r t@(fcase0 _) = wk-ren r t
pwBody-ren r t@(psplit _ _) = wk-ren r t
pwBody-ren r t@⌜Nat⌝ = wk-ren r t
pwBody-ren r t@(⌜IMu⌝ _ _ _) = wk-ren r t
pwBody-ren r t@(⌜Fin⌝ _) = wk-ren r t
pwBody-ren r t@⌜Unit⌝ = wk-ren r t
pwBody-ren r t@(ref _ _) = wk-ren r t

_ᴸ_ : Ren Δ Θ → Lv Δ → Lv Θ
(r ᴸ L) l = renTm r (L l)

cong₅ : {A B C D E F : Set} (f : A → B → C → D → E → F) {a a' : A} {b b' : B} {c c' : C} {d d' : D} {e e' : E} →
        a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → e ≡ e' → f a b c d e ≡ f a' b' c' d' e'
cong₅ f refl refl refl refl refl = refl

ren⌊⌋  : (r : Ren Δ Θ) (v : Val) (L : Lv Δ) → renTm r (⌊ v ⌋ L) ≡ ⌊ v ⌋ (r ᴸ L)
renᶜ   : (r : Ren Δ Θ) (c : Clo) (L : Lv Δ) → renTm (extR r) (⌊ c ⌋ᶜ L) ≡ ⌊ c ⌋ᶜ (r ᴸ L)
ren²   : (r : Ren Δ Θ) (c : Clo₂) (L : Lv Δ) → renTm (extR (extR r)) (⌊ c ⌋² L) ≡ ⌊ c ⌋² (r ᴸ L)
renᵉ   : (r : Ren Δ Θ) (ρ : Env Γ) (L : Lv Δ) (x : Var Γ) → (r ᵣ∘ₛ ⌊ ρ ⌋ᵉ L) x ≡ ⌊ ρ ⌋ᵉ (r ᴸ L) x

renᵉ r (ρ , v) L vz     = ren⌊⌋ r v L
renᵉ r (ρ , v) L (vs x) = renᵉ r ρ L x

renᶜ r (clo ρ t) L =
  trans (renTm-subTm t)
  (trans (subTm-cong (extr-exts r (⌊ ρ ⌋ᵉ L)) t)
         (subTm-cong (extS-cong (renᵉ r ρ L)) t))
renᶜ r (cloK v) L = trans (wk-ren r (⌊ v ⌋ L)) (cong wk (ren⌊⌋ r v L))
renᶜ r (cloHrefl C s) L =
  cong₂ hrefl (trans (pwBody-ren r (⌊ C ⌋ L)) (cong pwBody (ren⌊⌋ r C L)))
              (cong (λ z → app z (var vz)) (trans (wk-ren r (⌊ s ⌋ L)) (cong wk (ren⌊⌋ r s L))))
renᶜ r (cloDpay I D f) L =
  cong₃ dpay (trans (wk-ren r (⌊ I ⌋ L)) (cong wk (ren⌊⌋ r I L)))
             (trans (wk-ren r (⌊ D ⌋ L)) (cong wk (ren⌊⌋ r D L)))
             (cong (λ z → app z (var vz)) (trans (wk-ren r (⌊ f ⌋ L)) (cong wk (ren⌊⌋ r f L))))
renᶜ r (cloHomTo C A) L =
  cong₃ ⌜Hom⌝ (trans (wk-ren r (⌊ C ⌋ L)) (cong wk (ren⌊⌋ r C L)))
              (trans (wk-ren r (⌊ A ⌋ L)) (cong wk (ren⌊⌋ r A L))) refl
renᶜ r (cloTrPw d f e) L =
  cong (λ z → app z (var vz))
       (trans (wk-ren r (tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L)))
              (cong wk (cong₃ tr (renᶜ r d L) (cong lam (renᶜ r f L)) (ren⌊⌋ r e L))))

ren² r (clo₂ ρ t) L =
  trans (renTm-subTm t)
  (trans (subTm-cong (extr-exts (extR r) (extS (⌊ ρ ⌋ᵉ L))) t)
  (trans (subTm-cong (extS-cong (extr-exts r (⌊ ρ ⌋ᵉ L))) t)
         (subTm-cong (extS-cong (extS-cong (renᵉ r ρ L))) t)))

ren⌊⌋ r (vvar l) L = refl
ren⌊⌋ r (vlam (cloTrPw d f e)) L = cong₃ tr (renᶜ r d L) (cong lam (renᶜ r f L)) (ren⌊⌋ r e L)
ren⌊⌋ r (vlam c@(clo _ _)) L      = cong lam (renᶜ r c L)
ren⌊⌋ r (vlam c@(cloK _)) L       = cong lam (renᶜ r c L)
ren⌊⌋ r (vlam c@(cloHrefl _ _)) L = cong lam (renᶜ r c L)
ren⌊⌋ r (vlam c@(cloDpay _ _ _)) L = cong lam (renᶜ r c L)
ren⌊⌋ r (vlam c@(cloHomTo _ _)) L = cong lam (renᶜ r c L)
ren⌊⌋ r (vapp f a) L = cong₂ app (ren⌊⌋ r f L) (ren⌊⌋ r a L)
ren⌊⌋ r (vpair a b) L = cong₂ pair (ren⌊⌋ r a L) (ren⌊⌋ r b L)
ren⌊⌋ r (vabsurd c e) L = cong₂ absurd (ren⌊⌋ r c L) (ren⌊⌋ r e L)
ren⌊⌋ r (vordtr a t u p q) L = cong₅ ordtr (ren⌊⌋ r a L) (ren⌊⌋ r t L) (ren⌊⌋ r u L) (ren⌊⌋ r p L) (ren⌊⌋ r q L)
ren⌊⌋ r (vfst p) L = cong fst (ren⌊⌋ r p L)
ren⌊⌋ r (vsnd p) L = cong snd (ren⌊⌋ r p L)
ren⌊⌋ r v⌜base⌝ L = refl
ren⌊⌋ r (v⌜Π⌝ c d) L = cong₂ ⌜Π⌝ (ren⌊⌋ r c L) (renᶜ r d L)
ren⌊⌋ r (v⌜Σ⌝ c d) L = cong₂ ⌜Σ⌝ (ren⌊⌋ r c L) (renᶜ r d L)
ren⌊⌋ r (v⌜Hom⌝ c a b) L = cong₃ ⌜Hom⌝ (ren⌊⌋ r c L) (ren⌊⌋ r a L) (ren⌊⌋ r b L)
ren⌊⌋ r (vhrefl c t) L = cong₂ hrefl (ren⌊⌋ r c L) (ren⌊⌋ r t L)
ren⌊⌋ r (vtr d p e) L = cong₃ tr (renᶜ r d L) (ren⌊⌋ r p L) (ren⌊⌋ r e L)
ren⌊⌋ r (vap c b p) L = cong₃ ap (ren⌊⌋ r c L) (renᶜ r b L) (ren⌊⌋ r p L)
ren⌊⌋ r (v⌜Id⌝ c a b) L = cong₃ ⌜Id⌝ (ren⌊⌋ r c L) (ren⌊⌋ r a L) (ren⌊⌋ r b L)
ren⌊⌋ r (vidrefl c t) L = cong₂ idrefl (ren⌊⌋ r c L) (ren⌊⌋ r t L)
ren⌊⌋ r (vjsub d p e) L = cong₃ jsub (renᶜ r d L) (ren⌊⌋ r p L) (ren⌊⌋ r e L)
ren⌊⌋ r vunit L = refl
ren⌊⌋ r vnzero L = refl
ren⌊⌋ r (vnsuc t) L = cong nsuc (ren⌊⌋ r t L)
ren⌊⌋ r (vnatrec z s t) L = cong₃ natrec (ren⌊⌋ r z L) (ren² r s L) (ren⌊⌋ r t L)
ren⌊⌋ r (vcon p) L = cong con (ren⌊⌋ r p L)
ren⌊⌋ r (vielim D i e t) L = cong₄ ielim (ren⌊⌋ r D L) (ren⌊⌋ r i L) (ren⌊⌋ r e L) (ren⌊⌋ r t L)
ren⌊⌋ r vdι L = refl
ren⌊⌋ r (vdσ S f) L = cong₂ dσ (ren⌊⌋ r S L) (ren⌊⌋ r f L)
ren⌊⌋ r (vdρ j C) L = cong₂ dρ (ren⌊⌋ r j L) (ren⌊⌋ r C L)
ren⌊⌋ r (vdpay I D C) L = cong₃ dpay (ren⌊⌋ r I L) (ren⌊⌋ r D L) (ren⌊⌋ r C L)
ren⌊⌋ r (vdih D e C p) L = cong₄ dih (ren⌊⌋ r D L) (ren⌊⌋ r e L) (ren⌊⌋ r C L) (ren⌊⌋ r p L)
ren⌊⌋ r vfzero L = refl
ren⌊⌋ r (vfsuc t) L = cong fsuc (ren⌊⌋ r t L)
ren⌊⌋ r (vfcase t a b) L = cong₃ fcase (ren⌊⌋ r t L) (ren⌊⌋ r a L) (renᶜ r b L)
ren⌊⌋ r (vfcase0 t) L = cong fcase0 (ren⌊⌋ r t L)
ren⌊⌋ r (vpsplit b p) L = cong₂ psplit (ren² r b L) (ren⌊⌋ r p L)
ren⌊⌋ r v⌜Nat⌝ L = refl
ren⌊⌋ r v⌜Unit⌝ L = refl
ren⌊⌋ r (v⌜IMu⌝ I D i) L = cong₃ ⌜IMu⌝ (ren⌊⌋ r I L) (ren⌊⌋ r D L) (ren⌊⌋ r i L)
ren⌊⌋ r (v⌜Fin⌝ t) L = cong ⌜Fin⌝ (ren⌊⌋ r t L)
ren⌊⌋ r (vref d b) L = refl

------------------------------------------------------------------------
-- SCOPE: a value built at depth `n` mentions only the levels below `n`.
-- Reading a scoped value depends only on what the levels below `n` stand
-- for (`agree`) — which is what lets readback extend the level map with
-- the fresh level `n` under a binder.
------------------------------------------------------------------------

Sc  : ℕ → Val → Set
Scᶜ : ℕ → Clo → Set
Sc² : ℕ → Clo₂ → Set
Scᵉ : ℕ → Env Γ → Set

Scᵉ n []      = ⊤
Scᵉ n (ρ , v) = Scᵉ n ρ × Sc n v

Scᶜ n (clo ρ t)       = Scᵉ n ρ
Scᶜ n (cloK v)        = Sc n v
Scᶜ n (cloHrefl C s)  = Sc n C × Sc n s
Scᶜ n (cloDpay I D f) = Sc n I × (Sc n D × Sc n f)
Scᶜ n (cloHomTo C A)  = Sc n C × Sc n A
Scᶜ n (cloTrPw d f e) = Scᶜ n d × (Scᶜ n f × Sc n e)

Sc² n (clo₂ ρ t) = Scᵉ n ρ

Sc n (vvar l)           = (l < n) ≡ true
Sc n (vlam c)           = Scᶜ n c
Sc n (vapp f a)         = Sc n f × Sc n a
Sc n (vpair a b)        = Sc n a × Sc n b
Sc n (vabsurd c e)      = Sc n c × Sc n e
Sc n (vordtr a t u p q) = Sc n a × (Sc n t × (Sc n u × (Sc n p × Sc n q)))
Sc n (vfst p)           = Sc n p
Sc n (vsnd p)           = Sc n p
Sc n v⌜base⌝            = ⊤
Sc n (v⌜Π⌝ c d)         = Sc n c × Scᶜ n d
Sc n (v⌜Σ⌝ c d)         = Sc n c × Scᶜ n d
Sc n (v⌜Hom⌝ c a b)     = Sc n c × (Sc n a × Sc n b)
Sc n (vhrefl c t)       = Sc n c × Sc n t
Sc n (vtr d p e)        = Scᶜ n d × (Sc n p × Sc n e)
Sc n (vap c b p)        = Sc n c × (Scᶜ n b × Sc n p)
Sc n (v⌜Id⌝ c a b)      = Sc n c × (Sc n a × Sc n b)
Sc n (vidrefl c t)      = Sc n c × Sc n t
Sc n (vjsub d p e)      = Scᶜ n d × (Sc n p × Sc n e)
Sc n vunit              = ⊤
Sc n vnzero             = ⊤
Sc n (vnsuc t)          = Sc n t
Sc n (vnatrec z s t)    = Sc n z × (Sc² n s × Sc n t)
Sc n (vcon p)           = Sc n p
Sc n (vielim D i e t)   = Sc n D × (Sc n i × (Sc n e × Sc n t))
Sc n vdι                = ⊤
Sc n (vdσ S f)          = Sc n S × Sc n f
Sc n (vdρ j C)          = Sc n j × Sc n C
Sc n (vdpay I D C)      = Sc n I × (Sc n D × Sc n C)
Sc n (vdih D e C p)     = Sc n D × (Sc n e × (Sc n C × Sc n p))
Sc n vfzero             = ⊤
Sc n (vfsuc t)          = Sc n t
Sc n (vfcase t a b)     = Sc n t × (Sc n a × Scᶜ n b)
Sc n (vfcase0 t)        = Sc n t
Sc n (vpsplit b p)      = Sc² n b × Sc n p
Sc n v⌜Nat⌝             = ⊤
Sc n v⌜Unit⌝            = ⊤
Sc n (v⌜IMu⌝ I D i)     = Sc n I × (Sc n D × Sc n i)
Sc n (v⌜Fin⌝ t)         = Sc n t
Sc n (vref d b)         = ⊤

-- levels below n
Below : ℕ → Lv Δ → Lv Δ → Set
Below n L L' = (l : ℕ) → (l < n) ≡ true → L l ≡ L' l

agree  : (n : ℕ) (v : Val) {L L' : Lv Δ} → Below n L L' → Sc n v → ⌊ v ⌋ L ≡ ⌊ v ⌋ L'
agreeᶜ : (n : ℕ) (c : Clo) {L L' : Lv Δ} → Below n L L' → Scᶜ n c → ⌊ c ⌋ᶜ L ≡ ⌊ c ⌋ᶜ L'
agree² : (n : ℕ) (c : Clo₂) {L L' : Lv Δ} → Below n L L' → Sc² n c → ⌊ c ⌋² L ≡ ⌊ c ⌋² L'
agreeᵉ : (n : ℕ) (ρ : Env Γ) {L L' : Lv Δ} → Below n L L' → Scᵉ n ρ → (x : Var Γ) → ⌊ ρ ⌋ᵉ L x ≡ ⌊ ρ ⌋ᵉ L' x

agreeᵉ n (ρ , v) h (sρ , sv) vz     = agree n v h sv
agreeᵉ n (ρ , v) h (sρ , sv) (vs x) = agreeᵉ n ρ h sρ x

agreeᶜ n (clo ρ t) h s = subTm-cong (extS-cong (agreeᵉ n ρ h s)) t
agreeᶜ n (cloK v) h s = cong wk (agree n v h s)
agreeᶜ n (cloHrefl C t) h (sC , st) =
  cong₂ hrefl (cong pwBody (agree n C h sC)) (cong (λ z → app (wk z) (var vz)) (agree n t h st))
agreeᶜ n (cloDpay I D f) h (sI , (sD , sf)) =
  cong₃ dpay (cong wk (agree n I h sI)) (cong wk (agree n D h sD)) (cong (λ z → app (wk z) (var vz)) (agree n f h sf))
agreeᶜ n (cloHomTo C A) h (sC , sA) = cong₃ ⌜Hom⌝ (cong wk (agree n C h sC)) (cong wk (agree n A h sA)) refl
agreeᶜ n (cloTrPw d f e) h (sd , (sf , se)) =
  cong (λ z → app (wk z) (var vz)) (cong₃ tr (agreeᶜ n d h sd) (cong lam (agreeᶜ n f h sf)) (agree n e h se))

agree² n (clo₂ ρ t) h s = subTm-cong (extS-cong (extS-cong (agreeᵉ n ρ h s))) t

agree n (vvar l) h s = h l s
agree n (vlam (cloTrPw d f e)) h (sd , (sf , se)) =
  cong₃ tr (agreeᶜ n d h sd) (cong lam (agreeᶜ n f h sf)) (agree n e h se)
agree n (vlam c@(clo _ _)) h s       = cong lam (agreeᶜ n c h s)
agree n (vlam c@(cloK _)) h s        = cong lam (agreeᶜ n c h s)
agree n (vlam c@(cloHrefl _ _)) h s  = cong lam (agreeᶜ n c h s)
agree n (vlam c@(cloDpay _ _ _)) h s = cong lam (agreeᶜ n c h s)
agree n (vlam c@(cloHomTo _ _)) h s  = cong lam (agreeᶜ n c h s)
agree n (vapp f a) h (s₁ , s₂) = cong₂ app (agree n f h s₁) (agree n a h s₂)
agree n (vpair a b) h (s₁ , s₂) = cong₂ pair (agree n a h s₁) (agree n b h s₂)
agree n (vabsurd c e) h (s₁ , s₂) = cong₂ absurd (agree n c h s₁) (agree n e h s₂)
agree n (vordtr a t u p q) h (s₁ , (s₂ , (s₃ , (s₄ , s₅)))) =
  cong₅ ordtr (agree n a h s₁) (agree n t h s₂) (agree n u h s₃) (agree n p h s₄) (agree n q h s₅)
agree n (vfst p) h s = cong fst (agree n p h s)
agree n (vsnd p) h s = cong snd (agree n p h s)
agree n v⌜base⌝ h s = refl
agree n (v⌜Π⌝ c d) h (s₁ , s₂) = cong₂ ⌜Π⌝ (agree n c h s₁) (agreeᶜ n d h s₂)
agree n (v⌜Σ⌝ c d) h (s₁ , s₂) = cong₂ ⌜Σ⌝ (agree n c h s₁) (agreeᶜ n d h s₂)
agree n (v⌜Hom⌝ c a b) h (s₁ , (s₂ , s₃)) = cong₃ ⌜Hom⌝ (agree n c h s₁) (agree n a h s₂) (agree n b h s₃)
agree n (vhrefl c t) h (s₁ , s₂) = cong₂ hrefl (agree n c h s₁) (agree n t h s₂)
agree n (vtr d p e) h (s₁ , (s₂ , s₃)) = cong₃ tr (agreeᶜ n d h s₁) (agree n p h s₂) (agree n e h s₃)
agree n (vap c b p) h (s₁ , (s₂ , s₃)) = cong₃ ap (agree n c h s₁) (agreeᶜ n b h s₂) (agree n p h s₃)
agree n (v⌜Id⌝ c a b) h (s₁ , (s₂ , s₃)) = cong₃ ⌜Id⌝ (agree n c h s₁) (agree n a h s₂) (agree n b h s₃)
agree n (vidrefl c t) h (s₁ , s₂) = cong₂ idrefl (agree n c h s₁) (agree n t h s₂)
agree n (vjsub d p e) h (s₁ , (s₂ , s₃)) = cong₃ jsub (agreeᶜ n d h s₁) (agree n p h s₂) (agree n e h s₃)
agree n vunit h s = refl
agree n vnzero h s = refl
agree n (vnsuc t) h s = cong nsuc (agree n t h s)
agree n (vnatrec z c t) h (s₁ , (s₂ , s₃)) = cong₃ natrec (agree n z h s₁) (agree² n c h s₂) (agree n t h s₃)
agree n (vcon p) h s = cong con (agree n p h s)
agree n (vielim D i e t) h (s₁ , (s₂ , (s₃ , s₄))) =
  cong₄ ielim (agree n D h s₁) (agree n i h s₂) (agree n e h s₃) (agree n t h s₄)
agree n vdι h s = refl
agree n (vdσ S f) h (s₁ , s₂) = cong₂ dσ (agree n S h s₁) (agree n f h s₂)
agree n (vdρ j C) h (s₁ , s₂) = cong₂ dρ (agree n j h s₁) (agree n C h s₂)
agree n (vdpay I D C) h (s₁ , (s₂ , s₃)) = cong₃ dpay (agree n I h s₁) (agree n D h s₂) (agree n C h s₃)
agree n (vdih D e C p) h (s₁ , (s₂ , (s₃ , s₄))) =
  cong₄ dih (agree n D h s₁) (agree n e h s₂) (agree n C h s₃) (agree n p h s₄)
agree n vfzero h s = refl
agree n (vfsuc t) h s = cong fsuc (agree n t h s)
agree n (vfcase t a b) h (s₁ , (s₂ , s₃)) = cong₃ fcase (agree n t h s₁) (agree n a h s₂) (agreeᶜ n b h s₃)
agree n (vfcase0 t) h s = cong fcase0 (agree n t h s)
agree n (vpsplit b p) h (s₁ , s₂) = cong₂ psplit (agree² n b h s₁) (agree n p h s₂)
agree n v⌜Nat⌝ h s = refl
agree n v⌜Unit⌝ h s = refl
agree n (v⌜IMu⌝ I D i) h (s₁ , (s₂ , s₃)) = cong₃ ⌜IMu⌝ (agree n I h s₁) (agree n D h s₂) (agree n i h s₃)
agree n (v⌜Fin⌝ t) h s = cong ⌜Fin⌝ (agree n t h s)
agree n (vref d b) h s = refl

-- scope is monotone in the depth
Up : ℕ → ℕ → Set
Up n m = (l : ℕ) → (l < n) ≡ true → (l < m) ≡ true

mono  : {n m : ℕ} (v : Val) → Up n m → Sc n v → Sc m v
monoᶜ : {n m : ℕ} (c : Clo) → Up n m → Scᶜ n c → Scᶜ m c
mono² : {n m : ℕ} (c : Clo₂) → Up n m → Sc² n c → Sc² m c
monoᵉ : {n m : ℕ} (ρ : Env Γ) → Up n m → Scᵉ n ρ → Scᵉ m ρ

monoᵉ [] h s1 = tt
monoᵉ (ρ , v) h (s1 , s2) = (monoᵉ ρ h s1 , mono v h s2)
monoᶜ (clo ρ t) h s1 = monoᵉ ρ h s1
monoᶜ (cloK v) h s1 = mono v h s1
monoᶜ (cloHrefl C s) h (s1 , s2) = (mono C h s1 , mono s h s2)
monoᶜ (cloDpay I D f) h (s1 , (s2 , s3)) = (mono I h s1 , (mono D h s2 , mono f h s3))
monoᶜ (cloHomTo C A) h (s1 , s2) = (mono C h s1 , mono A h s2)
monoᶜ (cloTrPw d f e) h (s1 , (s2 , s3)) = (monoᶜ d h s1 , (monoᶜ f h s2 , mono e h s3))
mono² (clo₂ ρ t) h s1 = monoᵉ ρ h s1
mono (vvar l) h s1 = h l s1
mono (vlam c) h s1 = monoᶜ c h s1
mono (vapp f a) h (s1 , s2) = (mono f h s1 , mono a h s2)
mono (vpair a b) h (s1 , s2) = (mono a h s1 , mono b h s2)
mono (vabsurd c e) h (s1 , s2) = (mono c h s1 , mono e h s2)
mono (vordtr a t u p q) h (s1 , (s2 , (s3 , (s4 , s5)))) = (mono a h s1 , (mono t h s2 , (mono u h s3 , (mono p h s4 , mono q h s5))))
mono (vfst p) h s1 = mono p h s1
mono (vsnd p) h s1 = mono p h s1
mono v⌜base⌝ h s1 = tt
mono (v⌜Π⌝ c d) h (s1 , s2) = (mono c h s1 , monoᶜ d h s2)
mono (v⌜Σ⌝ c d) h (s1 , s2) = (mono c h s1 , monoᶜ d h s2)
mono (v⌜Hom⌝ c a b) h (s1 , (s2 , s3)) = (mono c h s1 , (mono a h s2 , mono b h s3))
mono (vhrefl c t) h (s1 , s2) = (mono c h s1 , mono t h s2)
mono (vtr d p e) h (s1 , (s2 , s3)) = (monoᶜ d h s1 , (mono p h s2 , mono e h s3))
mono (vap c b p) h (s1 , (s2 , s3)) = (mono c h s1 , (monoᶜ b h s2 , mono p h s3))
mono (v⌜Id⌝ c a b) h (s1 , (s2 , s3)) = (mono c h s1 , (mono a h s2 , mono b h s3))
mono (vidrefl c t) h (s1 , s2) = (mono c h s1 , mono t h s2)
mono (vjsub d p e) h (s1 , (s2 , s3)) = (monoᶜ d h s1 , (mono p h s2 , mono e h s3))
mono vunit h s1 = tt
mono vnzero h s1 = tt
mono (vnsuc t) h s1 = mono t h s1
mono (vnatrec z s t) h (s1 , (s2 , s3)) = (mono z h s1 , (mono² s h s2 , mono t h s3))
mono (vcon p) h s1 = mono p h s1
mono (vielim D i e t) h (s1 , (s2 , (s3 , s4))) = (mono D h s1 , (mono i h s2 , (mono e h s3 , mono t h s4)))
mono vdι h s1 = tt
mono (vdσ S f) h (s1 , s2) = (mono S h s1 , mono f h s2)
mono (vdρ j C) h (s1 , s2) = (mono j h s1 , mono C h s2)
mono (vdpay I D C) h (s1 , (s2 , s3)) = (mono I h s1 , (mono D h s2 , mono C h s3))
mono (vdih D e C p) h (s1 , (s2 , (s3 , s4))) = (mono D h s1 , (mono e h s2 , (mono C h s3 , mono p h s4)))
mono vfzero h s1 = tt
mono (vfsuc t) h s1 = mono t h s1
mono (vfcase t a b) h (s1 , (s2 , s3)) = (mono t h s1 , (mono a h s2 , monoᶜ b h s3))
mono (vfcase0 t) h s1 = mono t h s1
mono (vpsplit b p) h (s1 , s2) = (mono² b h s1 , mono p h s2)
mono v⌜Nat⌝ h s1 = tt
mono v⌜Unit⌝ h s1 = tt
mono (v⌜IMu⌝ I D i) h (s1 , (s2 , s3)) = (mono I h s1 , (mono D h s2 , mono i h s3))
mono (v⌜Fin⌝ t) h s1 = mono t h s1
mono (vref d b) h s1 = tt

lt-suc : (l n : ℕ) → (l < n) ≡ true → (l < suc n) ≡ true
lt-suc zero    n       h = refl
lt-suc (suc l) zero    ()
lt-suc (suc l) (suc n) h = lt-suc l n h

up-suc : (n : ℕ) → Up n (suc n)
up-suc n l = lt-suc l n

up-zero : (n : ℕ) → Up 0 n
up-zero n l ()
