-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE ENVIRONMENT EVALUATOR IS SOUND (PLAN-EVAL E3).
--
--     nbe-sound : t ≅ nbe k t
--
-- up to CONVERSION (`Spec/Typing._≅_`, the untyped equivalence closure of
-- `_⟶_`): all the checker needs (a "yes" is two conversions meeting; a "no"
-- is two distinct normal forms, Church–Rosser).  Up to `≅`, two
-- computations of one value at different fuel are interchangeable, so no
-- lemma matches the evaluator's fuel.
--
-- ★ THE METHOD: read every value as a term (`Algorithm/NbE.⌊_⌋`); each
--   evaluator function gets a lemma "the kernel term it stands for converts
--   to the reading of its result", by the SAME views and the same fuel
--   recursion.  A rule's case is: force/instantiate soundness, congruence,
--   ONE kernel step, a fusion equation.  The pointwise rules land EXACTLY
--   on their closures' readings (their right-hand sides, over the forced
--   pw-spine — PLAN-EVAL §2d).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.NbESound where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _×_; _,_; ⊤; tt )
open import Agda.Builtin.Nat using ( zero; suc; _<_; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_; ⌊_⌋ )
open import DirectedHoTT.Spec.Variance using ( pw?; stkA?; stkC?; pwBody; pwShift; 𝔹; true; false )
open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( wk-sub; ⟶-sub )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶-ren; ⟶*-trans )
open import DirectedHoTT.Metatheory.Confluence using ( church-rosser; ⟹-sub; ⟹-refl; ⟹→⟶*; ⟶→⟹; single-⟹; single2-⟹; pwBody-⟹; pw?-⟹ )
open import DirectedHoTT.Spec.Variance using ( pw?-sub; pwBody-sub )
open import DirectedHoTT.Algorithm.ConvLazy using ( cong≅; red→≅ )
open import DirectedHoTT.Algorithm.ConvCong
open import DirectedHoTT.Algorithm.NbE
open import DirectedHoTT.Algorithm.NbERead
open import DirectedHoTT.Algorithm.NbEScope

private
  variable
    Γ Δ : Cx

------------------------------------------------------------------------
-- 1. Small facts.
------------------------------------------------------------------------

≡→≅ : {t u : RTm Δ} → t ≡ u → t ≅ u

≡→≅ refl = crfl

infixr 4 _⨾_

_⨾_ : {t u v : RTm Δ} → t ≅ u → u ≅ v → t ≅ v

_⨾_ = ctrn

-- one kernel step, as a conversion
⟶≅ : {t u : RTm Δ} → t ⟶ u → t ≅ u

⟶≅ = cred

-- reading a looked-up variable is reading the environment
read-lookup : (ρ : Env Γ) (x : Var Γ) (L : Lv Δ) → ⌊ ρ ⌋ᵉ L x ≡ ⌊ lookup ρ x ⌋ L

read-lookup (ρ , v) vz     L = refl

read-lookup (ρ , v) (vs x) L = read-lookup ρ x L

-- ★ instantiating a syntactic closure is ONE substitution
sub-single-ext : (σ : Sub Γ Δ) (X : RTm Δ) (t : RTm (Γ ∙)) (τ : Sub (Γ ∙) Δ) →
                 τ vz ≡ X → (∀ x → τ (vs x) ≡ σ x) →
                 subTm (single X) (subTm (extS σ) t) ≡ subTm τ t

sub-single-ext σ X t τ hz hs =
  trans (subTm-subTm t) (subTm-cong pt t)
  where
  pt : ∀ x → (single X ∘ₛ extS σ) x ≡ τ x
  pt vz     = sym hz
  pt (vs x) = trans (wk-cancel-tm X (σ x)) (sym (hs x))

-- …and under two binders
sub-single2-ext : (σ : Sub Γ Δ) (X Y : RTm Δ) (t : RTm ((Γ ∙) ∙)) (τ : Sub ((Γ ∙) ∙) Δ) →
                  τ vz ≡ Y → τ (vs vz) ≡ X → (∀ x → τ (vs (vs x)) ≡ σ x) →
                  subTm (single2 X Y) (subTm (extS (extS σ)) t) ≡ subTm τ t

sub-single2-ext σ X Y t τ hz h1 hs =
  trans (subTm-subTm t) (subTm-cong pt t)
  where
  pt : ∀ x → (single2 X Y ∘ₛ extS (extS σ)) x ≡ τ x
  pt vz          = sym hz
  pt (vs vz)     = sym h1
  pt (vs (vs x)) = trans (sub2-wk2 X Y (σ x)) (sym (hs x))
    where
    -- two weakenings cancelled by the two-point substitution
    sub2-wk2 : (X Y t : RTm Δ) → subTm (single2 X Y) (renTm vs (renTm vs t)) ≡ t
    sub2-wk2 X Y t = trans (subTm-renTm (renTm vs t)) (trans (subTm-renTm t) (trans (subTm-cong (λ _ → refl) t) (subTm-id t)))

-- natrec-suc's two substitutions are the two-point one
natrec-sub : (N R : RTm Δ) (S : RTm ((Δ ∙) ∙)) →
             subTm (single R) (subTm (extS (single N)) S) ≡ subTm (single2 N R) S

natrec-sub N R S = trans (subTm-subTm S) (subTm-cong pt S)
  where
  pt : ∀ x → (single R ∘ₛ extS (single N)) x ≡ single2 N R x
  pt vz          = refl
  pt (vs vz)     = wk-cancel-tm R N
  pt (vs (vs x)) = wk-cancel-tm R (var x)

-- a weakening cancelled by a single substitution
wkc : (X t : RTm Δ) → subTm (single X) (wk t) ≡ t

wkc X t = wk-cancel-tm X t

------------------------------------------------------------------------
-- 3. Conversion facts from Church–Rosser and the parallel reduction.
------------------------------------------------------------------------

-- substitution and renaming respect conversion
≅-sub : (σ : Sub Γ Δ) {t u : RTm Γ} → t ≅ u → subTm σ t ≅ subTm σ u

≅-sub σ (cred r)   = cred (⟶-sub σ r)

≅-sub σ crfl       = crfl

≅-sub σ (csym c)   = csym (≅-sub σ c)

≅-sub σ (ctrn c d) = ctrn (≅-sub σ c) (≅-sub σ d)

≅-ren : (ρ : Ren Γ Δ) {t u : RTm Γ} → t ≅ u → renTm ρ t ≅ renTm ρ u

≅-ren ρ (cred r)   = cred (⟶-ren ρ r)

≅-ren ρ crfl       = crfl

≅-ren ρ (csym c)   = csym (≅-ren ρ c)

≅-ren ρ (ctrn c d) = ctrn (≅-ren ρ c) (≅-ren ρ d)

-- substituting convertible terms (one point; the second of two points)
sub1≅ : (t : RTm (Δ ∙)) {X X' : RTm Δ} → X ≅ X' → subTm (single X) t ≅ subTm (single X') t

sub1≅ t (cred r)   = red→≅ (⟹→⟶* (⟹-sub (single-⟹ (⟶→⟹ r)) (⟹-refl t)))

sub1≅ t crfl       = crfl

sub1≅ t (csym c)   = csym (sub1≅ t c)

sub1≅ t (ctrn c d) = ctrn (sub1≅ t c) (sub1≅ t d)

sub-cong≅ : {X : RTm Δ} (t : RTm ((Δ ∙) ∙)) {R R' : RTm Δ} → R ≅ R' → subTm (single2 X R) t ≅ subTm (single2 X R') t

sub-cong≅ {X = X} t (cred r) = red→≅ (⟹→⟶* (⟹-sub (single2-⟹ (⟹-refl X) (⟶→⟹ r)) (⟹-refl t)))

sub-cong≅ t crfl       = crfl

sub-cong≅ t (csym c)   = csym (sub-cong≅ t c)

sub-cong≅ t (ctrn c d) = ctrn (sub-cong≅ t c) (sub-cong≅ t d)

-- ★ a ⌜Hom⌝ code only reduces in its fields, so convertible ⌜Hom⌝s have
--   convertible fields (Church–Rosser)
private
  hom* : {a b c r : RTm Δ} → ⌜Hom⌝ a b c ⟶* r →
         Σ (RTm Δ) λ a' → Σ (RTm Δ) λ b' → Σ (RTm Δ) λ c' →
           (r ≡ ⌜Hom⌝ a' b' c') × ((a ⟶* a') × ((b ⟶* b') × (c ⟶* c')))
  hom* done = _ , (_ , (_ , (refl , (done , (done , done)))))
  hom* (step (ξ-⌜Hom⌝ᶜ r) p) with hom* p
  ... | a' , (b' , (c' , (e , (pa , (pb , pc))))) = a' , (b' , (c' , (e , (step r pa , (pb , pc)))))
  hom* (step (ξ-⌜Hom⌝ˡ r) p) with hom* p
  ... | a' , (b' , (c' , (e , (pa , (pb , pc))))) = a' , (b' , (c' , (e , (pa , (step r pb , pc)))))
  hom* (step (ξ-⌜Hom⌝ʳ r) p) with hom* p
  ... | a' , (b' , (c' , (e , (pa , (pb , pc))))) = a' , (b' , (c' , (e , (pa , (pb , step r pc)))))

Hom-inj : {a b c a₁ b₁ c₁ : RTm Δ} → ⌜Hom⌝ a b c ≅ ⌜Hom⌝ a₁ b₁ c₁ → (a ≅ a₁) × ((b ≅ b₁) × (c ≅ c₁))

Hom-inj h with church-rosser h
... | r , (p , q) with hom* p | hom* q
...   | a' , (b' , (c' , (refl , (pa , (pb , pc))))) | a'' , (b'' , (c'' , (e , (qa , (qb , qc))))) with e
...     | refl = (red→≅ pa ⨾ csym (red→≅ qa)) , ((red→≅ pb ⨾ csym (red→≅ qb)) , (red→≅ pc ⨾ csym (red→≅ qc)))

-- ★ `pwBody` respects conversion between pw-shaped codes
private
  pwBody* : {p r : RTm Δ} → p ⟶* r → pw? p ≡ true → (pwBody p ⟶* pwBody r) × (pw? r ≡ true)
  pwBody* done h = done , h
  pwBody* (step s p) h with pwBody* p (pw?-⟹ (⟶→⟹ s) h)
  ... | q , h' = ⟶*-trans (⟹→⟶* (pwBody-⟹ (⟶→⟹ s) h)) q , h'

pwBody≅ : {p q : RTm Δ} → p ≅ q → pw? p ≡ true → pw? q ≡ true → pwBody p ≅ pwBody q

pwBody≅ c hp hq with church-rosser c
... | r , (pr , qr) = red→≅ (fst′ (pwBody* pr hp)) ⨾ csym (red→≅ (fst′ (pwBody* qr hq)))
  where
  fst′ : {A B : Set} → A × B → A
  fst′ (a , b) = a

------------------------------------------------------------------------
-- 4. The remaining rules.
------------------------------------------------------------------------

-- a closure that is not tr-pw's reads as the λ of its body
readLam-plain : (f : Clo) (L : Lv Δ) → isTrPw f ≡ false → readLam f L ≡ lam (⌊ f ⌋ᶜ L)

readLam-plain (clo _ _)        L h = refl

readLam-plain (cloK _)         L h = refl

readLam-plain (cloHrefl _ _ _) L h = refl

readLam-plain (cloDpay _ _ _)  L h = refl

readLam-plain (cloHomTo _ _)   L h = refl

readLam-plain (cloTrPw _ _ _)  L ()

-- a pw-spine's reading is pw-shaped: the side condition of hrefl-pw / tr-pw
pw-read : {C : Val} (sp : PwSpine C) (L : Lv Δ) → pw? (⌊ C ⌋ L) ≡ true

pw-read (spΠ c d)      L = refl

pw-read (spHom sp a b) L = pw-read sp L

-- what tr-pw's inspection tells about the motive (when its guard holds)
VS : ℕ → Clo → Lv Δ → Maybe TrPwV → Set

VS m d L (just (trpw c sp a)) = ⌊ d ⌋ᶜ L ≅ ⌜Hom⌝ (⌊ c ⌋ (bindL m L)) (⌊ a ⌋ (bindL m L)) (var vz)

VS m d L nothing              = ⊤

private
  ==-refl : (n : ℕ) → (n == n) ≡ true
  ==-refl zero    = refl
  ==-refl (suc n) = ==-refl n

  ==→≡ : (l n : ℕ) → (l == n) ≡ true → l ≡ n
  ==→≡ zero    zero    e = refl
  ==→≡ zero    (suc n) ()
  ==→≡ (suc l) zero    ()
  ==→≡ (suc l) (suc n) e = cong suc (==→≡ l n e)

  <→≠′ : (d n : ℕ) → (d < n) ≡ true → (d == n) ≡ false
  <→≠′ zero    zero    ()
  <→≠′ zero    (suc n) e = refl
  <→≠′ (suc d) zero    ()
  <→≠′ (suc d) (suc n) e = <→≠′ d n e

-- the bound level reads as the binder
bind-here : (m : ℕ) (L : Lv Δ) → bindL m L m ≡ var vz

bind-here m L = subst (λ b → pickTm b (var vz) (wk (L m)) ≡ var vz) (sym (==-refl m)) refl

-- under the binder, a value scoped below m reads as its weakening
bind-wk : (m : ℕ) (L : Lv Δ) → Below m (bindL m L) (vs ᴸ L)

bind-wk m L l p = subst (λ b → pickTm b (var vz) (wk (L l)) ≡ wk (L l)) (sym (<→≠′ l m p)) refl

-- substituting the binder for itself undoes a weakening under it
sub-vz-wk : (X : RTm (Δ ∙)) → subTm (single (var vz)) (renTm (extR vs) X) ≡ X

sub-vz-wk X = trans (subTm-renTm X) (trans (subTm-cong pt X) (subTm-id X))
  where
  pt : ∀ x → (single (var vz) ₛ∘ᵣ extR vs) x ≡ idₛ x
  pt vz     = refl
  pt (vs x) = refl

-- …and under two binders (readback of natrec's step, psplit's body)
private
  lt-two : (n : ℕ) → (n < suc (suc n)) ≡ true
  lt-two zero    = refl
  lt-two (suc n) = lt-two n

  up2 : (n : ℕ) → Up n (suc (suc n))
  up2 n l p = lt-suc l (suc n) (lt-suc l n p)

  ≠suc : (n : ℕ) → (n == suc n) ≡ false
  ≠suc zero    = refl
  ≠suc (suc n) = ≠suc n

  bind2-wk : (m : ℕ) (L : Lv Δ) → Below m (bindL (suc m) (bindL m L)) (vs ᴸ (vs ᴸ L))
  bind2-wk m L l p =
    trans (subst (λ b → pickTm b (var vz) (wk (bindL m L l)) ≡ wk (bindL m L l)) (sym (<→≠′ l (suc m) (lt-suc l m p))) refl)
          (cong wk (bind-wk m L l p))

  sub2-wk2 : (X : RTm ((Δ ∙) ∙)) →
             subTm (single2 (var (vs vz)) (var vz)) (renTm (extR (extR vs)) (renTm (extR (extR vs)) X)) ≡ X
  sub2-wk2 X = trans (cong (subTm _) (renTm-renTm X)) (trans (subTm-renTm X) (trans (subTm-cong pt X) (subTm-id X)))
    where
    pt : ∀ x → (single2 (var (vs vz)) (var vz) ₛ∘ᵣ (extR (extR vs) ∘ᵣ extR (extR vs))) x ≡ idₛ x
    pt vz          = refl
    pt (vs vz)     = refl
    pt (vs (vs x)) = refl

-- the stability guards, read: a code that passes `stkV` converts to one
-- whose head the kernel's guard accepts
StkX : Bool → RTm Δ → 𝔹

StkX true  C = stkA? C

StkX false C = stkC? C

------------------------------------------------------------------------
-- 5. ★ Instantiation.
------------------------------------------------------------------------

-- substituting y for BOTH of pwShift's collapsed variables, under a binder
pwShift-sub : (Y : RTm Δ) (t : RTm ((Δ ∙) ∙)) →
              subTm (extS (single Y)) (renTm pwShift t) ≡ wk (subTm (single2 Y Y) t)

pwShift-sub Y t = trans (subTm-renTm t) (trans (subTm-cong pt t) (sym (renTm-subTm t)))
  where
  pt : ∀ x → (extS (single Y) ₛ∘ᵣ pwShift) x ≡ (vs ᵣ∘ₛ single2 Y Y) x
  pt vz          = refl
  pt (vs vz)     = refl
  pt (vs (vs x)) = refl

-- the two-point substitution at one point, through pwBody
two-at-one : (Y : RTm Δ) (P : RTm (Δ ∙)) → pw? P ≡ true →
             subTm (single2 Y Y) (pwBody P) ≡ subTm (single Y) (pwBody (subTm (single Y) P))

two-at-one Y P h = trans (subTm-cong pt (pwBody P))
                     (trans (sym (subTm-subTm (pwBody P))) (cong (subTm (single Y)) (sym (pwBody-sub (single Y) P h))))
  where
  pt : ∀ x → single2 Y Y x ≡ (single Y ∘ₛ extS (single Y)) x
  pt vz          = refl
  pt (vs vz)     = sym (wk-cancel-tm Y Y)
  pt (vs (vs x)) = sym (wk-cancel-tm Y (var x))

------------------------------------------------------------------------
-- ★ THE LEMMAS (one mutual group, the evaluator's fuel recursion).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 2. ★ THE LEMMAS, one per evaluator function (one mutual block, the
--    evaluator's fuel recursion).
------------------------------------------------------------------------

S-appLam : (k n : ℕ) (c : Clo) (u : Val) (L : Lv Δ) → Scᶜ n c → Sc n u →
           app (readLam c L) (⌊ u ⌋ L) ≅ ⌊ inst k n c u ⌋ L

S-trPwApp : (k n : ℕ) (d f : Clo) (e y : Val) (L : Lv Δ) → Scᶜ n (cloTrPw d f e) → Sc n y →
            app (tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L)) (⌊ y ⌋ L) ≅ ⌊ trPwN k n (cloTrPw d f e) d f e y (trPwView k n d) ⌋ L

S-eval  : (k n : ℕ) (ρ : Env Γ) (t : RTm Γ) (L : Lv Δ) → Scᵉ n ρ → subTm (⌊ ρ ⌋ᵉ L) t ≅ ⌊ eval k n ρ t ⌋ L

S-force : (k : ℕ) (v : Val) (L : Lv Δ) → ⌊ v ⌋ L ≅ ⌊ force k v ⌋ L

S-forceR : (k : ℕ) {v : Val} (w : RefV v) (L : Lv Δ) → ⌊ v ⌋ L ≅ ⌊ forceR k w ⌋ L

S-inst  : (k n : ℕ) (c : Clo) (v : Val) (L : Lv Δ) → Scᶜ n c → Sc n v →
          subTm (single (⌊ v ⌋ L)) (⌊ c ⌋ᶜ L) ≅ ⌊ inst k n c v ⌋ L

S-inst₂ : (k n : ℕ) (c : Clo₂) (x y : Val) (L : Lv Δ) → Sc² n c → Sc n x → Sc n y →
          subTm (single2 (⌊ x ⌋ L) (⌊ y ⌋ L)) (⌊ c ⌋² L) ≅ ⌊ inst₂ k n c x y ⌋ L

S-vApp  : (k n : ℕ) (f u : Val) (L : Lv Δ) → Sc n f → Sc n u → app (⌊ f ⌋ L) (⌊ u ⌋ L) ≅ ⌊ vApp k n f u ⌋ L

S-appF  : (k n : ℕ) {f : Val} (w : LamV f) (u : Val) (L : Lv Δ) → Sc n f → Sc n u → app (⌊ f ⌋ L) (⌊ u ⌋ L) ≅ ⌊ appF k n w u ⌋ L

S-fstF  : {p : Val} (w : PairV p) (L : Lv Δ) → fst (⌊ p ⌋ L) ≅ ⌊ fstF w ⌋ L

S-sndF  : {p : Val} (w : PairV p) (L : Lv Δ) → snd (⌊ p ⌋ L) ≅ ⌊ sndF w ⌋ L

S-vPsplit : (k n : ℕ) (b : Clo₂) (p : Val) (L : Lv Δ) → Sc² n b → Sc n p → psplit (⌊ b ⌋² L) (⌊ p ⌋ L) ≅ ⌊ vPsplit k n b p ⌋ L

S-psplitF : (k n : ℕ) (b : Clo₂) {p : Val} (w : PairV p) (L : Lv Δ) → Sc² n b → Sc n p → psplit (⌊ b ⌋² L) (⌊ p ⌋ L) ≅ ⌊ psplitF k n b w ⌋ L

S-vNatrec : (k n : ℕ) (z : Val) (s : Clo₂) (t : Val) (L : Lv Δ) → Sc n z → Sc² n s → Sc n t →
            natrec (⌊ z ⌋ L) (⌊ s ⌋² L) (⌊ t ⌋ L) ≅ ⌊ vNatrec k n z s t ⌋ L

S-natrecF : (k n : ℕ) (z : Val) (s : Clo₂) {t : Val} (w : NatV t) (L : Lv Δ) → Sc n z → Sc² n s → Sc n t →
            natrec (⌊ z ⌋ L) (⌊ s ⌋² L) (⌊ t ⌋ L) ≅ ⌊ natrecF k n z s w ⌋ L

S-vFcase : (k n : ℕ) (t a : Val) (b : Clo) (L : Lv Δ) → Sc n t → Sc n a → Scᶜ n b →
           fcase (⌊ t ⌋ L) (⌊ a ⌋ L) (⌊ b ⌋ᶜ L) ≅ ⌊ vFcase k n t a b ⌋ L

S-fcaseF : (k n : ℕ) {t : Val} (w : FinV t) (a : Val) (b : Clo) (L : Lv Δ) → Sc n t → Sc n a → Scᶜ n b →
           fcase (⌊ t ⌋ L) (⌊ a ⌋ L) (⌊ b ⌋ᶜ L) ≅ ⌊ fcaseF k n w a b ⌋ L

S-vOrdtr : (k n : ℕ) (a t u p q : Val) (L : Lv Δ) →
           ordtr (⌊ a ⌋ L) (⌊ t ⌋ L) (⌊ u ⌋ L) (⌊ p ⌋ L) (⌊ q ⌋ L) ≅ ⌊ vOrdtr k n a t u p q ⌋ L

S-ordA  : (k n : ℕ) {a : Val} (w : NatV a) (t u p q : Val) (L : Lv Δ) →
          ordtr (⌊ a ⌋ L) (⌊ t ⌋ L) (⌊ u ⌋ L) (⌊ p ⌋ L) (⌊ q ⌋ L) ≅ ⌊ ordA k n w t u p q ⌋ L

S-ordB  : (k n : ℕ) (a : Val) {t u : Val} (wt : NatV t) (wu : NatV u) (p q : Val) (L : Lv Δ) →
          ordtr (nsuc (⌊ a ⌋ L)) (⌊ t ⌋ L) (⌊ u ⌋ L) (⌊ p ⌋ L) (⌊ q ⌋ L) ≅ ⌊ ordB k n a wt wu p q ⌋ L

S-vJsub : (k : ℕ) (d : Clo) (p e : Val) (L : Lv Δ) → jsub (⌊ d ⌋ᶜ L) (⌊ p ⌋ L) (⌊ e ⌋ L) ≅ ⌊ vJsub k d p e ⌋ L

S-jsubF : (d : Clo) {p : Val} (w : IdreflV p) (e : Val) (L : Lv Δ) → jsub (⌊ d ⌋ᶜ L) (⌊ p ⌋ L) (⌊ e ⌋ L) ≅ ⌊ jsubF d w e ⌋ L

S-vFst  : (k : ℕ) (p : Val) (L : Lv Δ) → fst (⌊ p ⌋ L) ≅ ⌊ vFst k p ⌋ L

S-vSnd  : (k : ℕ) (p : Val) (L : Lv Δ) → snd (⌊ p ⌋ L) ≅ ⌊ vSnd k p ⌋ L

-- ★ the motive at the fresh level n is its body
S-fresh : (k m : ℕ) (d : Clo) (L : Lv Δ) → Scᶜ m d → ⌊ d ⌋ᶜ L ≅ ⌊ inst k (suc m) d (vvar m) ⌋ (bindL m L)

S-fresh2 : (k m : ℕ) (c : Clo₂) (L : Lv Δ) → Sc² m c →
           ⌊ c ⌋² L ≅ ⌊ inst₂ k (suc (suc m)) c (vvar m) (vvar (suc m)) ⌋ (bindL (suc m) (bindL m L))

-- what the inspection shows (the evaluator's guard), by its own computation
S-view : (k m : ℕ) (d : Clo) (L : Lv Δ) → Scᶜ m d → VS m d L (trPwView k m d)

-- forcing a pw-spine
S-pwForce  : (k : ℕ) (C : Val) (L : Lv Δ) → ⌊ C ⌋ L ≅ ⌊ pwForce k C ⌋ L

S-pwForceH : (k : ℕ) {C : Val} (w : HomV C) (L : Lv Δ) → ⌊ C ⌋ L ≅ ⌊ pwForceH k w ⌋ L

-- ★ hrefl: a pw-able code (its spine forced) steps to its pointwise RHS —
--   EXACTLY the reading of `cloHrefl`; else the order's reflexivity at ⌜Nat⌝
S-vHrefl : (k n : ℕ) (C s : Val) (L : Lv Δ) → Sc n C → Sc n s → hrefl (⌊ C ⌋ L) (⌊ s ⌋ L) ≅ ⌊ vHrefl k n C s ⌋ L

S-hreflS : (k n : ℕ) (C : Val) (w : Maybe (PwSpine C)) (s : Val) (L : Lv Δ) → hrefl (⌊ C ⌋ L) (⌊ s ⌋ L) ≅ ⌊ hreflS k n C w s ⌋ L

S-hreflC : (k n : ℕ) {C : Val} (w : CodeV C) (s : Val) (L : Lv Δ) → hrefl (⌊ C ⌋ L) (⌊ s ⌋ L) ≅ ⌊ hreflC k n w s ⌋ L

S-hreflNat : (k n : ℕ) (s : Val) (L : Lv Δ) → hrefl ⌜Nat⌝ (⌊ s ⌋ L) ≅ ⌊ hreflNat k n s ⌋ L

S-hreflN : (k n : ℕ) {s : Val} (w : NatV s) (L : Lv Δ) → hrefl ⌜Nat⌝ (⌊ s ⌋ L) ≅ ⌊ hreflN k n w ⌋ L

-- ★ pwBody along a spine, instantiated
S-pwAtS : (k n : ℕ) {C : Val} (sp : PwSpine C) (x : Val) (L : Lv Δ) → Sc n C → Sc n x →
          subTm (single (⌊ x ⌋ L)) (pwBody (⌊ C ⌋ L)) ≅ ⌊ pwAtS k n sp x ⌋ L

S-stk  : (nat : Bool) (k : ℕ) (C : Val) (L : Lv Δ) → stkV nat k C ≡ true →
         Σ (RTm Δ) λ C' → (⌊ C ⌋ L ≅ C') × (StkX nat C' ≡ true)

S-stkF : (nat : Bool) (k : ℕ) {C : Val} (w : CodeV C) (L : Lv Δ) → stkF nat k w ≡ true →
         Σ (RTm Δ) λ C' → (⌊ C ⌋ L ≅ C') × (StkX nat C' ≡ true)

-- ★ tr-J: a J-able path code
S-trJ : (k : ℕ) {C : Val} (w : CodeV C) (L : Lv Δ) → trJ k w ≡ true →
        (cm am mm : RTm (Δ ∙)) (S E : RTm Δ) → tr (⌜Hom⌝ cm am mm) (hrefl (⌊ C ⌋ L) S) E ≅ E

-- ★ transport: the motive is inspected at the fresh level n
S-vTr : (k n : ℕ) (d : Clo) (p e : Val) (L : Lv Δ) → Scᶜ n d → Sc n p → Sc n e →
        tr (⌊ d ⌋ᶜ L) (⌊ p ⌋ L) (⌊ e ⌋ L) ≅ ⌊ vTr k n d p e ⌋ L

S-trF : (k n : ℕ) (d : Clo) {h : Val} (c : HomV h) {p : Val} (w : HreflV p) (lw : LamV p) (vw : VarV h) (e : Val) (L : Lv Δ) →
        Scᶜ n d → Sc n p → Sc n e → ⌊ d ⌋ᶜ L ≅ ⌊ h ⌋ (bindL n L) →
        tr (⌊ d ⌋ᶜ L) (⌊ p ⌋ L) (⌊ e ⌋ L) ≅ ⌊ trF k n d c w lw vw e ⌋ L

-- ★ tr-pw at creation: the kernel's step lands on the closure's reading
S-trPwC : (k n : ℕ) (d f : Clo) (e : Val) (L : Lv Δ) → Scᶜ n d → Scᶜ n f → Sc n e → isTrPw f ≡ false →
          tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L) ≅ ⌊ trPwC k n d f e (trPwView k n d) ⌋ L

S-trTautB : (k n : ℕ) (b : Bool) (d f : Clo) (e : Val) (L : Lv Δ) → ⊤

-- ★ ap-J
S-vAp : (k n : ℕ) (cB : Val) (b : Clo) (p : Val) (L : Lv Δ) → Sc n cB → Scᶜ n b → Sc n p →
        ap (⌊ cB ⌋ L) (⌊ b ⌋ᶜ L) (⌊ p ⌋ L) ≅ ⌊ vAp k n cB b p ⌋ L

S-apF : (k n : ℕ) (cB : Val) (b : Clo) {p : Val} (w : HreflV p) (L : Lv Δ) → Sc n cB → Scᶜ n b → Sc n p →
        ap (⌊ cB ⌋ L) (⌊ b ⌋ᶜ L) (⌊ p ⌋ L) ≅ ⌊ apF k n cB b w ⌋ L

-- ★ ι, and the hypotheses' fold
S-vIelim : (k n : ℕ) (D i e t : Val) (L : Lv Δ) → Sc n D → Sc n i → Sc n e → Sc n t →
           ielim (⌊ D ⌋ L) (⌊ i ⌋ L) (⌊ e ⌋ L) (⌊ t ⌋ L) ≅ ⌊ vIelim k n D i e t ⌋ L

S-ielimF : (k n : ℕ) (D i e : Val) {t : Val} (w : ConV t) (L : Lv Δ) → Sc n D → Sc n i → Sc n e → Sc n t →
           ielim (⌊ D ⌋ L) (⌊ i ⌋ L) (⌊ e ⌋ L) (⌊ t ⌋ L) ≅ ⌊ ielimF k n D i e w ⌋ L

S-vDpay : (k n : ℕ) (I D C : Val) (L : Lv Δ) →
          dpay (⌊ I ⌋ L) (⌊ D ⌋ L) (⌊ C ⌋ L) ≅ ⌊ vDpay k I D C ⌋ L

S-dpayF : (k : ℕ) (I D : Val) {C : Val} (w : DescV C) (L : Lv Δ) →
          dpay (⌊ I ⌋ L) (⌊ D ⌋ L) (⌊ C ⌋ L) ≅ ⌊ dpayF k I D w ⌋ L

S-vDih : (k n : ℕ) (D e C p : Val) (L : Lv Δ) → Sc n D → Sc n e → Sc n C → Sc n p →
         dih (⌊ D ⌋ L) (⌊ e ⌋ L) (⌊ C ⌋ L) (⌊ p ⌋ L) ≅ ⌊ vDih k n D e C p ⌋ L

S-dihF : (k n : ℕ) (D e : Val) {C : Val} (w : DescV C) (p : Val) (L : Lv Δ) → Sc n D → Sc n e → Sc n C → Sc n p →
         dih (⌊ D ⌋ L) (⌊ e ⌋ L) (⌊ C ⌋ L) (⌊ p ⌋ L) ≅ ⌊ dihF k n D e w p ⌋ L

S-eval k n ρ (var x)           L s = ≡→≅ (read-lookup ρ x L)

S-eval k n ρ (lam t)           L s = crfl

S-eval k n ρ (app f u)         L s = ≅app (S-eval k n ρ f L s) (S-eval k n ρ u L s) ⨾ S-vApp k n _ _ L (sc-eval k n ρ f s) (sc-eval k n ρ u s)

S-eval k n ρ (pair a b)        L s = ≅pair (S-eval k n ρ a L s) (S-eval k n ρ b L s)

S-eval k n ρ (absurd c e)      L s = ≅absurd (S-eval k n ρ c L s) (S-eval k n ρ e L s)

S-eval k n ρ (ordtr a t u p q) L s =
  ≅ordtr (S-eval k n ρ a L s) (S-eval k n ρ t L s) (S-eval k n ρ u L s) (S-eval k n ρ p L s) (S-eval k n ρ q L s)
  ⨾ S-vOrdtr k n _ _ _ _ _ L

S-eval k n ρ (fst p)           L s = ≅fst (S-eval k n ρ p L s) ⨾ (≅fst (S-force k _ L) ⨾ S-fstF (pairV (force k (eval k n ρ p))) L)

S-eval k n ρ (snd p)           L s = ≅snd (S-eval k n ρ p L s) ⨾ (≅snd (S-force k _ L) ⨾ S-sndF (pairV (force k (eval k n ρ p))) L)

S-eval k n ρ ⌜base⌝            L s = crfl

S-eval k n ρ (⌜Π⌝ c d)         L s = ≅⌜Π⌝ (S-eval k n ρ c L s) crfl

S-eval k n ρ (⌜Σ⌝ c d)         L s = ≅⌜Σ⌝ (S-eval k n ρ c L s) crfl

S-eval k n ρ (⌜Hom⌝ c a b)     L s = ≅⌜Hom⌝ (S-eval k n ρ c L s) (S-eval k n ρ a L s) (S-eval k n ρ b L s)

S-eval k n ρ (hrefl c t)       L s = ≅hrefl (S-eval k n ρ c L s) (S-eval k n ρ t L s) ⨾ S-vHrefl k n _ _ L (sc-eval k n ρ c s) (sc-eval k n ρ t s)

S-eval k n ρ (tr d p e)        L s = ≅tr crfl (S-eval k n ρ p L s) (S-eval k n ρ e L s) ⨾ S-vTr k n (clo ρ d) _ _ L s (sc-eval k n ρ p s) (sc-eval k n ρ e s)

S-eval k n ρ (ap c b p)        L s = ≅ap (S-eval k n ρ c L s) crfl (S-eval k n ρ p L s) ⨾ S-vAp k n _ (clo ρ b) _ L (sc-eval k n ρ c s) s (sc-eval k n ρ p s)

S-eval k n ρ (⌜Id⌝ c a b)      L s = ≅⌜Id⌝ (S-eval k n ρ c L s) (S-eval k n ρ a L s) (S-eval k n ρ b L s)

S-eval k n ρ (idrefl c t)      L s = ≅idrefl (S-eval k n ρ c L s) (S-eval k n ρ t L s)

S-eval k n ρ (jsub d p e)      L s = ≅jsub crfl (S-eval k n ρ p L s) (S-eval k n ρ e L s) ⨾ S-vJsub k (clo ρ d) _ _ L

S-eval k n ρ unit              L s = crfl

S-eval k n ρ nzero             L s = crfl

S-eval k n ρ (nsuc t)          L s = ≅nsuc (S-eval k n ρ t L s)

S-eval k n ρ (natrec z c t)    L s = ≅natrec (S-eval k n ρ z L s) crfl (S-eval k n ρ t L s) ⨾ S-vNatrec k n _ (clo₂ ρ c) _ L (sc-eval k n ρ z s) s (sc-eval k n ρ t s)

S-eval k n ρ (con p)           L s = ≅con (S-eval k n ρ p L s)

S-eval k n ρ (ielim D i e t)   L s =
  ≅ielim (S-eval k n ρ D L s) (S-eval k n ρ i L s) (S-eval k n ρ e L s) (S-eval k n ρ t L s)
  ⨾ S-vIelim k n _ _ _ _ L (sc-eval k n ρ D s) (sc-eval k n ρ i s) (sc-eval k n ρ e s) (sc-eval k n ρ t s)

S-eval k n ρ dι                L s = crfl

S-eval k n ρ (dσ S f)          L s = ≅dσ (S-eval k n ρ S L s) (S-eval k n ρ f L s)

S-eval k n ρ (dρ j C)          L s = ≅dρ (S-eval k n ρ j L s) (S-eval k n ρ C L s)

S-eval k n ρ (dpay I D C)      L s = ≅dpay (S-eval k n ρ I L s) (S-eval k n ρ D L s) (S-eval k n ρ C L s) ⨾ S-vDpay k n _ _ _ L

S-eval k n ρ (dih D e C p)     L s =
  ≅dih (S-eval k n ρ D L s) (S-eval k n ρ e L s) (S-eval k n ρ C L s) (S-eval k n ρ p L s)
  ⨾ S-vDih k n _ _ _ _ L (sc-eval k n ρ D s) (sc-eval k n ρ e s) (sc-eval k n ρ C s) (sc-eval k n ρ p s)

S-eval k n ρ fzero             L s = crfl

S-eval k n ρ (fsuc t)          L s = ≅fsuc (S-eval k n ρ t L s)

S-eval k n ρ (fcase t a b)     L s = ≅fcase (S-eval k n ρ t L s) (S-eval k n ρ a L s) crfl ⨾ S-vFcase k n _ _ (clo ρ b) L (sc-eval k n ρ t s) (sc-eval k n ρ a s) s

S-eval k n ρ (fcase0 t)        L s = ≅fcase0 (S-eval k n ρ t L s)

S-eval k n ρ (psplit b p)      L s = ≅psplit crfl (S-eval k n ρ p L s) ⨾ S-vPsplit k n (clo₂ ρ b) _ L s (sc-eval k n ρ p s)

S-eval k n ρ ⌜Nat⌝             L s = crfl

S-eval k n ρ (⌜IMu⌝ I D i)     L s = ≅⌜IMu⌝ (S-eval k n ρ I L s) (S-eval k n ρ D L s) (S-eval k n ρ i L s)

S-eval k n ρ (⌜Fin⌝ t)         L s = ≅⌜Fin⌝ (S-eval k n ρ t L s)

S-eval k n ρ ⌜Unit⌝            L s = crfl

S-eval k n ρ (ref d b)         L s = crfl

-- ★ δ: a reference unfolds to its (closed) body, evaluated at depth 0
S-force zero    v L = crfl

S-force (suc k) v L = S-forceR k (refV v) L

S-forceR k (isRef d b) L =
  ⟶≅ (δref d b) ⨾ (≡→≅ (subTm-cong (λ ()) b) ⨾ (S-eval k 0 [] b L tt ⨾ S-force k _ L))

S-forceR k (notRef v)  L = crfl

S-vApp k n f u L sf su = ≅app (S-force k f L) crfl ⨾ S-appF k n (lamV (force k f)) u L (sc-force k n f sf) su

S-appF zero    n (isLam c)  u L sf su = crfl

S-appF zero    n (notLam f) u L sf su = crfl

S-appF (suc k) n (isLam c)  u L sf su = S-appLam k n c u L sf su

S-appF (suc k) n (notLam f) u L sf su = crfl

S-fstF (isPair a b) L = ⟶≅ (βfst _ _)

S-fstF (notPair p)  L = crfl

S-sndF (isPair a b) L = ⟶≅ (βsnd _ _)

S-sndF (notPair p)  L = crfl

S-vPsplit k n b p L sb sp = ≅psplit crfl (S-force k p L) ⨾ S-psplitF k n b (pairV (force k p)) L sb (sc-force k n p sp)

S-psplitF zero    n b (isPair x y) L sb sp = crfl

S-psplitF zero    n b (notPair p)  L sb sp = crfl

S-psplitF (suc k) n b (isPair x y) L sb (sx , sy) = ⟶≅ (psplit-β _ _ _) ⨾ S-inst₂ k n b x y L sb sx sy

S-psplitF (suc k) n b (notPair p)  L sb sp = crfl

S-vNatrec k n z s t L sz ss st =
  ≅natrec crfl crfl (S-force k t L) ⨾ S-natrecF k n z s (natV (force k t)) L sz ss (sc-force k n t st)

S-natrecF k       n z s isZero     L sz ss st = ⟶≅ (natrec-zero _ _)

S-natrecF zero    n z s (isSuc t)  L sz ss st = crfl

S-natrecF (suc k) n z s (isSuc t)  L sz ss st =
  ⟶≅ (natrec-suc _ _ _) ⨾ (≡→≅ (natrec-sub (⌊ t ⌋ L) (natrec (⌊ z ⌋ L) (⌊ s ⌋² L) (⌊ t ⌋ L)) (⌊ s ⌋² L))
  ⨾ (sub-cong≅ (⌊ s ⌋² L) (S-vNatrec k n z s t L sz ss st) ⨾ S-inst₂ k n s t _ L ss st (sc-vNatrec k n z s t sz ss st)))

S-natrecF k       n z s (notNat t) L sz ss st = crfl

S-vFcase k n t a b L st sa sb = ≅fcase (S-force k t L) crfl crfl ⨾ S-fcaseF k n (finV (force k t)) a b L (sc-force k n t st) sa sb

S-fcaseF k       n isFz       a b L st sa sb = ⟶≅ (fcase-z _ _)

S-fcaseF zero    n (isFs t)   a b L st sa sb = crfl

S-fcaseF (suc k) n (isFs t)   a b L st sa sb = ⟶≅ (fcase-s _ _ _) ⨾ S-inst k n b t L sb st

S-fcaseF k       n (notFin t) a b L st sa sb = crfl

S-vOrdtr k n a t u p q L =
  ≅ordtr (S-force k a L) (S-force k t L) (S-force k u L) crfl crfl ⨾ S-ordA k n (natV (force k a)) _ _ p q L

S-ordA k n isZero     t u p q L = ⟶≅ (ordtr-z _ _ _ _)

S-ordA k n (isSuc a)  t u p q L = S-ordB k n a (natV t) (natV u) p q L

S-ordA k n (notNat a) t u p q L = crfl

S-ordB k       n a isZero     isZero     p q L = ⟶≅ (ordtr-szz _ _ _)

S-ordB k       n a (isSuc t)  isZero     p q L = ⟶≅ (ordtr-ssz _ _ _ _)

S-ordB k       n a isZero     (isSuc u)  p q L = ⟶≅ (ordtr-szs _ _ _ _)

S-ordB zero    n a (isSuc t)  (isSuc u)  p q L = crfl

S-ordB (suc k) n a (isSuc t)  (isSuc u)  p q L = ⟶≅ (ordtr-sss _ _ _ _ _) ⨾ S-vOrdtr k n a t u p q L

S-ordB k       n a (notNat t) isZero     p q L = crfl

S-ordB k       n a (notNat t) (isSuc u)  p q L = crfl

S-ordB k       n a (notNat t) (notNat u) p q L = crfl

S-ordB k       n a isZero     (notNat u) p q L = crfl

S-ordB k       n a (isSuc t)  (notNat u) p q L = crfl

S-vJsub k d p e L = ≅jsub crfl (S-force k p L) crfl ⨾ S-jsubF d (idreflV (force k p)) e L

S-jsubF d (isIdrefl c s) e L = ⟶≅ (jsub-refl _ _ _ _)

S-jsubF d (notIdrefl p)  e L = crfl

S-vFst k p L = ≅fst (S-force k p L) ⨾ S-fstF (pairV (force k p)) L

S-vSnd k p L = ≅snd (S-force k p L) ⨾ S-sndF (pairV (force k p)) L

S-fresh k m d L sd =
  ≡→≅ (sym eq) ⨾ S-inst k (suc m) d (vvar m) (bindL m L) (monoᶜ d (up-suc m) sd) (lt-self m)
  where
  eq : subTm (single (⌊ vvar m ⌋ (bindL m L))) (⌊ d ⌋ᶜ (bindL m L)) ≡ ⌊ d ⌋ᶜ L
  eq = trans (cong₂ (λ X Y → subTm (single X) Y) (bind-here m L)
                    (trans (agreeᶜ m d (bind-wk m L) sd) (sym (renᶜ vs d L))))
             (sub-vz-wk (⌊ d ⌋ᶜ L))

S-fresh2 k m c L sc =
  ≡→≅ (sym eq)
  ⨾ S-inst₂ k (suc (suc m)) c (vvar m) (vvar (suc m)) L″ (mono² c (up2 m) sc) (lt-two m) (lt-self (suc m))
  where
  L″ = bindL (suc m) (bindL m L)
  e₀ : ⌊ vvar m ⌋ L″ ≡ var (vs vz)
  e₀ = trans (subst (λ b → pickTm b (var vz) (wk (bindL m L m)) ≡ wk (bindL m L m)) (sym (≠suc m)) refl)
             (cong wk (bind-here m L))
  eq : subTm (single2 (⌊ vvar m ⌋ L″) (⌊ vvar (suc m) ⌋ L″)) (⌊ c ⌋² L″) ≡ ⌊ c ⌋² L
  eq = trans (cong₂ (λ X Y → subTm (single2 X Y) (⌊ c ⌋² L″)) e₀ (bind-here (suc m) (bindL m L)))
       (trans (cong (subTm (single2 (var (vs vz)) (var vz)))
                    (trans (agree² m c (bind2-wk m L) sc)
                           (trans (sym (ren² vs c (vs ᴸ L))) (cong (renTm (extR (extR vs))) (sym (ren² vs c L))))))
              (sub2-wk2 (⌊ c ⌋² L)))

S-view k m d L sd =
  tpvH-sound (homV (force k (inst k (suc m) d (vvar m))))
             (S-fresh k m d L sd ⨾ S-force k _ (bindL m L))
  where
  tpvH-sound : {h : Val} (w : HomV h) → ⌊ d ⌋ᶜ L ≅ ⌊ h ⌋ (bindL m L) → VS m d L (tpvH k m w)
  tpvH-sound (isHom c a mm) cv = tpvL-sound (varV mm)
    where
    tpvS-sound : (c' : Val) (w : Maybe (PwSpine c')) → ⌊ c ⌋ (bindL m L) ≅ ⌊ c' ⌋ (bindL m L) →
                 ⌊ mm ⌋ (bindL m L) ≡ var vz → VS m d L (tpvS a c' w)
    tpvS-sound c' (just sp) cc em = cv ⨾ ≅⌜Hom⌝ cc crfl (≡→≅ em)
    tpvS-sound c' nothing   cc em = tt
    tpvL-sound : (vw : VarV mm) → VS m d L (tpvL k c a (isLvl m vw))
    tpvL-sound (isVar l) = byB (l == m) refl
      where
      byB : (b : Bool) → (l == m) ≡ b → VS m d L (tpvL k c a b)
      byB true  e = tpvS-sound (pwForce k c) (pwSpine? (pwForce k c)) (S-pwForce k c (bindL m L))
                      (subst (λ x → bindL m L x ≡ var vz) (sym (==→≡ l m e)) (bind-here m L))
      byB false e = tt
    tpvL-sound (notVar v) = tt
  tpvH-sound (notHom _) cv = tt

S-pwForce zero    C L = crfl

S-pwForce (suc k) C L = S-force k C L ⨾ S-pwForceH k (homV (force k C)) L

S-pwForceH k (isHom C a b) L = ≅⌜Hom⌝ (S-pwForce k C L) crfl crfl

S-pwForceH k (notHom v)    L = crfl

S-vHrefl k n C s L sC ss = ≅hrefl (S-pwForce k C L) crfl ⨾ S-hreflS k n (pwForce k C) (pwSpine? (pwForce k C)) s L

S-hreflS k n C (just sp) s L = ⟶≅ (hrefl-pw (⌊ C ⌋ L) (⌊ s ⌋ L) (pw-read sp L))

S-hreflS k n C nothing   s L = S-hreflC k n (codeV C) s L

S-hreflC k n cNat         s L = S-hreflNat k n s L

S-hreflC k n cbase        s L = crfl

S-hreflC k n (cΠ c d)     s L = crfl

S-hreflC k n (cΣ c d)     s L = crfl

S-hreflC k n (cHom c a b) s L = crfl

S-hreflC k n (cId c a b)  s L = crfl

S-hreflC k n cUnit        s L = crfl

S-hreflC k n (cIMu I D i) s L = crfl

S-hreflC k n (cFin t)     s L = crfl

S-hreflC k n (cOther C)   s L = crfl

S-hreflNat zero    n s L = crfl

S-hreflNat (suc k) n s L = ≅hrefl crfl (S-force k s L) ⨾ S-hreflN k n (natV (force k s)) L

S-hreflN k n isZero     L = ⟶≅ hrefl-Nat-z

S-hreflN k n (isSuc m)  L = ⟶≅ (hrefl-Nat-s _) ⨾ S-hreflNat k n m L

S-hreflN k n (notNat s) L = crfl

S-pwAtS k n (spΠ c d)      x L (sc , sd) sx = S-inst k n d x L sd sx

S-pwAtS k n (spHom sp a b) x L (sC , (sa , sb)) sx =
  ≅⌜Hom⌝ (S-pwAtS k n sp x L sC sx)
         (≅app (≡→≅ (wkc _ (⌊ a ⌋ L))) crfl ⨾ S-vApp k n a x L sa sx)
         (≅app (≡→≅ (wkc _ (⌊ b ⌋ L))) crfl ⨾ S-vApp k n b x L sb sx)

S-stk nat k C L h with S-stkF nat k (codeV (force k C)) L h
... | C' , (c , e) = C' , ((S-force k C L ⨾ c) , e)

S-stkF true  k cbase L h = _ , (crfl , refl)

S-stkF false k cbase L h = _ , (crfl , refl)

S-stkF true  k (cΣ _ _) L h = _ , (crfl , refl)

S-stkF false k (cΣ _ _) L h = _ , (crfl , refl)

S-stkF true  k (cId _ _ _) L h = _ , (crfl , refl)

S-stkF false k (cId _ _ _) L h = _ , (crfl , refl)

S-stkF true  k cUnit L h = _ , (crfl , refl)

S-stkF false k cUnit L h = _ , (crfl , refl)

S-stkF true  k (cFin _) L h = _ , (crfl , refl)

S-stkF false k (cFin _) L h = _ , (crfl , refl)

S-stkF true  k cNat L h = _ , (crfl , refl)

S-stkF false k cNat L ()

S-stkF true  k (cIMu _ _ _) L h = _ , (crfl , refl)

S-stkF false k (cIMu _ _ _) L h = _ , (crfl , refl)

S-stkF nat zero    (cHom C a b) L ()

S-stkF nat (suc k) (cHom C a b) L h with S-stk true k C L h

S-stkF true  (suc k) (cHom C a b) L h | C' , (c , e) = ⌜Hom⌝ C' (⌊ a ⌋ L) (⌊ b ⌋ L) , (≅⌜Hom⌝ c crfl crfl , e)

S-stkF false (suc k) (cHom C a b) L h | C' , (c , e) = ⌜Hom⌝ C' (⌊ a ⌋ L) (⌊ b ⌋ L) , (≅⌜Hom⌝ c crfl crfl , e)

S-stkF nat k (cΠ _ _) L ()

S-stkF nat k (cOther _) L ()

S-trJ k cbase          L h cm am mm S E = ⟶≅ (tr-J-base cm am mm S E)

S-trJ k (cΣ c d)       L h cm am mm S E = ⟶≅ (tr-J-Σ cm am mm _ _ S E)

S-trJ k cUnit          L h cm am mm S E = ⟶≅ (tr-J-Unit cm am mm S E)

S-trJ k (cId c a b)    L h cm am mm S E = ⟶≅ (tr-J-Id cm am mm _ _ _ S E)

S-trJ k (cIMu I D i)   L h cm am mm S E = ⟶≅ (tr-J-IMu cm am mm S E)

S-trJ k (cFin t)       L h cm am mm S E = ⟶≅ (tr-J-Fin cm am mm S E)

S-trJ k (cHom c₁ a₁ b₁) L h cm am mm S E with S-stk true k c₁ L h
... | C' , (c , key) = ≅tr crfl (≅hrefl (≅⌜Hom⌝ c crfl crfl) crfl) crfl ⨾ ⟶≅ (tr-J-Hom cm am mm C' _ _ S E key)

S-trJ k (cΠ _ _)    L () cm am mm S E

S-trJ k cNat        L () cm am mm S E

S-trJ k (cOther _)  L () cm am mm S E

S-vTr zero    n d p e L sd sp se = crfl

S-vTr (suc k) n d p e L sd sp se =
  ≅tr crfl (S-force k p L) crfl
  ⨾ S-trF k n d (homV h) (hreflV (force k p)) (lamV (force k p)) (varV h) e L sd (sc-force k n p sp) se
          (S-fresh k n d L sd ⨾ S-force k _ (bindL n L))
  where h = force k (inst k (suc n) d (vvar n))

-- tr-J (the path is a reflexivity at a J-able code)
S-trF k n d (isHom c a m) (isHrefl C s) w v e L sd sp se mot = byJ (trJ k (codeV (force k C))) refl
  where
  byJ : (b : Bool) → trJ k (codeV (force k C)) ≡ b → tr (⌊ d ⌋ᶜ L) (hrefl (⌊ C ⌋ L) (⌊ s ⌋ L)) (⌊ e ⌋ L) ≅ ⌊ trJB b d (vhrefl C s) e ⌋ L
  byJ true  h = ≅tr mot (≅hrefl (S-force k C L) crfl) crfl
                ⨾ S-trJ k (codeV (force k C)) L h (⌊ c ⌋ (bindL n L)) (⌊ a ⌋ (bindL n L)) (⌊ m ⌋ (bindL n L)) (⌊ s ⌋ L) (⌊ e ⌋ L)
  byJ false h = crfl

-- tr-pw (the path is a λ, the motive pw-able at its own endpoint)
S-trF k n d (isHom c a m) (notHrefl _) (isLam f) v e L sd sp se mot = byP (isTrPw f) refl
  where
  byP : (b : Bool) → isTrPw f ≡ b → tr (⌊ d ⌋ᶜ L) (readLam f L) (⌊ e ⌋ L) ≅ ⌊ trPwP k n d f e b ⌋ L
  byP true  h = crfl
  byP false h = ≡→≅ (cong (λ z → tr (⌊ d ⌋ᶜ L) z (⌊ e ⌋ L)) (readLam-plain f L h)) ⨾ S-trPwC k n d f e L sd sp se h

S-trF k n d (isHom c a m) (notHrefl _) (notLam p) v e L sd sp se mot = crfl

-- tr-taut (the motive is the endpoint itself)
S-trF k n d (notHom _) w (isLam f) (isVar l) e L sd sp se mot = byP (isTrPw f) refl
  where
  byP : (b : Bool) → isTrPw f ≡ b → tr (⌊ d ⌋ᶜ L) (readLam f L) (⌊ e ⌋ L) ≅ ⌊ trTautP k n l d f e b ⌋ L
  byP true  h = crfl
  byP false h = byT (l == n) refl
    where
    byT : (b : Bool) → (l == n) ≡ b → tr (⌊ d ⌋ᶜ L) (readLam f L) (⌊ e ⌋ L) ≅ ⌊ trTautB k n b d f e ⌋ L
    byT true  h′ = ≅tr (mot ⨾ ≡→≅ (subst (λ x → bindL n L x ≡ var vz) (sym (==→≡ l n h′)) (bind-here n L)))
                       (≡→≅ (readLam-plain f L h)) crfl
                   ⨾ (⟶≅ (tr-taut _ _) ⨾ (⟶≅ (β _ _) ⨾ S-inst k n f e L sp se))
    byT false h′ = crfl

S-trF k n d (notHom _) w (isLam f) (notVar _) e L sd sp se mot = crfl

S-trF k n d (notHom _) w (notLam p) v e L sd sp se mot = crfl

S-trPwC k n d f e L sd sf se pl = go (trPwView k n d)
  where
  go : (w : Maybe TrPwV) → tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L) ≅ ⌊ trPwC k n d f e w ⌋ L
  go (just _) = crfl
  go nothing  = ≡→≅ (cong (λ z → tr (⌊ d ⌋ᶜ L) z (⌊ e ⌋ L)) (sym (readLam-plain f L pl)))

S-trTautB k n b d f e L = tt

S-vAp k n cB b p L scB sb sp = ≅ap crfl crfl (S-force k p L) ⨾ S-apF k n cB b (hreflV (force k p)) L scB sb (sc-force k n p sp)

S-apF zero    n cB b (isHrefl c₁ s) L scB sb sp = crfl

S-apF zero    n cB b (notHrefl p)   L scB sb sp = crfl

S-apF (suc k) n cB b (isHrefl c₁ s) L scB sb (sc₁ , ss) = byS (stkV false k c₁) refl
  where
  byS : (t : Bool) → stkV false k c₁ ≡ t → ap (⌊ cB ⌋ L) (⌊ b ⌋ᶜ L) (hrefl (⌊ c₁ ⌋ L) (⌊ s ⌋ L)) ≅ ⌊ apB k n t cB b c₁ s ⌋ L
  byS true h with S-stk false k c₁ L h
  ... | C' , (c , key) =
    ≅ap crfl crfl (≅hrefl c crfl) ⨾ (⟶≅ (ap-J _ _ C' _ key)
    ⨾ (≅hrefl crfl (S-inst k n b s L sb ss) ⨾ S-vHrefl k n cB _ L scB (sc-inst k n b s sb ss)))
  byS false h = crfl

S-apF (suc k) n cB b (notHrefl p) L scB sb sp = crfl

S-vIelim k n D i e t L sD si se st =
  ≅ielim crfl crfl crfl (S-force k t L) ⨾ S-ielimF k n D i e (conV (force k t)) L sD si se (sc-force k n t st)

S-ielimF zero    n D i e (isCon p)  L sD si se st = crfl

S-ielimF zero    n D i e (notCon t) L sD si se st = crfl

S-ielimF (suc k) n D i e (isCon p)  L sD si se sp =
  ⟶≅ (ι _ _ _ _)
  ⨾ (≅app (≅app (S-vApp k n e i L se si) crfl ⨾ S-vApp k n _ p L (sc-vApp k n e i se si) sp)
          (≅dih crfl crfl (S-vApp k n D i L sD si) crfl ⨾ S-vDih k n D e _ p L sD se (sc-vApp k n D i sD si) sp)
  ⨾ S-vApp k n _ _ L (sc-vApp k n _ p (sc-vApp k n e i se si) sp) (sc-vDih k n D e _ p sD se (sc-vApp k n D i sD si) sp))

S-ielimF (suc k) n D i e (notCon t) L sD si se st = crfl

S-vDpay k n I D C L = ≅dpay crfl crfl (S-force k C L) ⨾ S-dpayF k I D (descV (force k C)) L

S-dpayF k       I D isDι       L = ⟶≅ (dpay-ι _ _)

S-dpayF k       I D (isDσ S f) L = ⟶≅ (dpay-σ _ _ _ _)

S-dpayF zero    I D (isDρ j C) L = crfl

S-dpayF (suc k) I D (isDρ j C) L =
  ⟶≅ (dpay-ρ _ _ _ _) ⨾ ≅⌜Σ⌝ crfl (≅-ren vs (S-vDpay k 0 I D C L))

S-dpayF k       I D (notDesc C) L = crfl

S-vDih k n D e C p L sD se sC sp =
  ≅dih crfl crfl (S-force k C L) crfl ⨾ S-dihF k n D e (descV (force k C)) p L sD se (sc-force k n C sC) sp

S-dihF k       n D e isDι       p L sD se sC sp = ⟶≅ (dih-ι _ _ _)

S-dihF zero    n D e (isDσ S f) p L sD se sC sp = crfl

S-dihF (suc k) n D e (isDσ S f) p L sD se (sS , sf) sp =
  ⟶≅ (dih-σ _ _ _ _ _)
  ⨾ (≅dih crfl crfl (≅app crfl (S-vFst k p L) ⨾ S-vApp k n f _ L sf (sc-vFst k n p sp)) (S-vSnd k p L)
  ⨾ S-vDih k n D e _ _ L sD se (sc-vApp k n f _ sf (sc-vFst k n p sp)) (sc-vSnd k n p sp))

S-dihF zero    n D e (isDρ j C) p L sD se sC sp = crfl

S-dihF (suc k) n D e (isDρ j C) p L sD se (sj , sC) sp =
  ⟶≅ (dih-ρ _ _ _ _ _)
  ⨾ ≅pair (≅ielim crfl crfl crfl (S-vFst k p L) ⨾ S-vIelim k n D j e _ L sD sj se (sc-vFst k n p sp))
          (≅dih crfl crfl crfl (S-vSnd k p L) ⨾ S-vDih k n D e C _ L sD se sC (sc-vSnd k n p sp))

S-dihF k n D e (notDesc C) p L sD se sC sp = crfl

S-inst zero    n c@(clo _ _)        v L sc sv = csym (⟶≅ (β _ _))

S-inst zero    n c@(cloK _)         v L sc sv = csym (⟶≅ (β _ _))

S-inst zero    n c@(cloHrefl _ _ _) v L sc sv = csym (⟶≅ (β _ _))

S-inst zero    n c@(cloDpay _ _ _)  v L sc sv = csym (⟶≅ (β _ _))

S-inst zero    n c@(cloHomTo _ _)   v L sc sv = csym (⟶≅ (β _ _))

S-inst zero    n (cloTrPw d f e)    v L sc sv = ≡→≅ (cong (λ z → app z (⌊ v ⌋ L)) (wkc _ _))

S-inst (suc k) n (clo ρ t)        v L sρ sv =
  ≡→≅ (sub-single-ext (⌊ ρ ⌋ᵉ L) (⌊ v ⌋ L) t (⌊ ρ , v ⌋ᵉ L) refl (λ x → refl)) ⨾ S-eval k n (ρ , v) t L (sρ , sv)

S-inst (suc k) n (cloK w)         v L sw sv = ≡→≅ (wkc _ (⌊ w ⌋ L))

S-inst (suc k) n (cloHrefl C sp s) v L (sC , ss) sv =
  ≅hrefl (S-pwAtS k n sp v L sC sv) (≅app (≡→≅ (wkc _ (⌊ s ⌋ L))) crfl ⨾ S-vApp k n s v L ss sv)
  ⨾ S-vHrefl k n _ _ L (sc-pwAtS k n sp v sC sv) (sc-vApp k n s v ss sv)

S-inst (suc k) n (cloDpay I D f)  v L (sI , (sD , sf)) sv =
  ≅dpay (≡→≅ (wkc _ (⌊ I ⌋ L))) (≡→≅ (wkc _ (⌊ D ⌋ L))) (≅app (≡→≅ (wkc _ (⌊ f ⌋ L))) crfl ⨾ S-vApp k n f v L sf sv)
  ⨾ S-vDpay k n I D _ L

S-inst (suc k) n (cloHomTo C A)   v L sCA sv = ≅⌜Hom⌝ (≡→≅ (wkc _ (⌊ C ⌋ L))) (≡→≅ (wkc _ (⌊ A ⌋ L))) crfl

S-inst (suc k) n self@(cloTrPw d f e) y L ss sy =
  ≡→≅ (cong (λ z → app z (⌊ y ⌋ L)) (wkc _ _)) ⨾ S-trPwApp k n d f e y L ss sy

-- applying a λ-value: β — except tr-pw's, whose redex steps only under its guard
S-appLam k n c@(clo _ _)        u L sc su = ⟶≅ (β _ _) ⨾ S-inst k n c u L sc su

S-appLam k n c@(cloK _)         u L sc su = ⟶≅ (β _ _) ⨾ S-inst k n c u L sc su

S-appLam k n c@(cloHrefl _ _ _) u L sc su = ⟶≅ (β _ _) ⨾ S-inst k n c u L sc su

S-appLam k n c@(cloDpay _ _ _)  u L sc su = ⟶≅ (β _ _) ⨾ S-inst k n c u L sc su

S-appLam k n c@(cloHomTo _ _)   u L sc su = ⟶≅ (β _ _) ⨾ S-inst k n c u L sc su

S-appLam zero    n (cloTrPw d f e) u L sc su = crfl

S-appLam (suc k) n (cloTrPw d f e) u L sc su = S-trPwApp k n d f e u L sc su

-- ★ tr-pw, applied: the guard re-checked at THIS fuel; when it holds the
--   kernel's step takes the redex to the rule's right-hand side, whose
--   instance at y is met by the evaluator's re-inspection at y (⌜Hom⌝
--   injectivity, pwBody between convertible pw-shaped codes)
S-trPwApp k n d f e y L ss@(sd , (sf , se)) sy = go (trPwView k n d) (S-view k n d L sd)
  where
  self = cloTrPw d f e
  Y = ⌊ y ⌋ L
  R = tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L)
  go : (w : Maybe TrPwV) → VS n d L w → app R Y ≅ ⌊ trPwN k n self d f e y w ⌋ L
  go nothing             vs′ = crfl
  go (just (trpw c sp a)) vs′ = insp (homV (force k (inst k n d y))) atY (sc-force k n _ (sc-inst k n d y sd sy))
    where
    P = ⌊ c ⌋ (bindL n L)
    A = ⌊ a ⌋ (bindL n L)
    -- the redex steps (tr-pw, then β) to the right-hand side at y
    toB : app R Y ≅ subTm (single Y) (tr (⌜Hom⌝ (renTm pwShift (pwBody P)) (app (renTm vs A) (var (vs vz))) (var vz))
                                         (⌊ f ⌋ᶜ L) (app (renTm vs (⌊ e ⌋ L)) (var vz)))
    toB = ≅app (≅tr vs′ crfl crfl ⨾ ⟶≅ (tr-pw P A (⌊ f ⌋ᶜ L) (⌊ e ⌋ L) (pw-read sp (bindL n L)))) crfl ⨾ ⟶≅ (β _ _)
    atY : ⌜Hom⌝ (subTm (single Y) P) (subTm (single Y) A) Y ≅ ⌊ force k (inst k n d y) ⌋ L
    atY = csym (≅-sub (single Y) vs′) ⨾ (S-inst k n d y L sd sy ⨾ S-force k _ L)
    insp : {h : Val} (w′ : HomV h) → ⌜Hom⌝ (subTm (single Y) P) (subTm (single Y) A) Y ≅ ⌊ h ⌋ L → Sc n h →
           app R Y ≅ ⌊ trPwI k n self d f e y w′ ⌋ L
    insp (notHom _) h≅ sh = crfl
    insp (isHom c′ a′ _) h≅ (sc′ , (sa′ , _)) = spine (pwSpine? (pwForce k c′))
      where
      fields = Hom-inj h≅
      cc : subTm (single Y) P ≅ ⌊ c′ ⌋ L
      cc = Σ.fst fields
      aa : subTm (single Y) A ≅ ⌊ a′ ⌋ L
      aa = Σ.fst (Σ.snd fields)
      spine : (w″ : Maybe (PwSpine (pwForce k c′))) → app R Y ≅ ⌊ trPwS k n self f e y a′ w″ ⌋ L
      spine nothing    = crfl
      spine (just sp′) =
        toB
        ⨾ (≅tr (≅⌜Hom⌝ mot₁ mot₂ crfl) (S-inst k n f y L sf sy) (≅app (≡→≅ (wkc Y (⌊ e ⌋ L))) crfl ⨾ S-vApp k n e y L se sy)
        ⨾ S-vTr k n _ _ _ L (sc-pwAtS k n sp′ y (sc-pwForce k n c′ sc′) sy , sc-vApp k n a′ y sa′ sy)
                (sc-inst k n f y sf sy) (sc-vApp k n e y se sy))
        where
        mot₁ : subTm (extS (single Y)) (renTm pwShift (pwBody P)) ≅ wk (⌊ pwAtS k n sp′ y ⌋ L)
        mot₁ = ≡→≅ (trans (pwShift-sub Y (pwBody P)) (cong wk (two-at-one Y P (pw-read sp (bindL n L)))))
               ⨾ ≅-ren vs (≅-sub (single Y) (pwBody≅ (cc ⨾ S-pwForce k c′ L) (pw?-sub (single Y) P (pw-read sp (bindL n L))) (pw-read sp′ L))
                           ⨾ S-pwAtS k n sp′ y L (sc-pwForce k n c′ sc′) sy)
        mot₂ : app (subTm (extS (single Y)) (renTm vs A)) (renTm vs Y) ≅ wk (⌊ vApp k n a′ y ⌋ L)
        mot₂ = ≡→≅ (cong (λ z → app z (renTm vs Y)) (wk-sub (single Y) A))
               ⨾ ≅-ren vs (≅app aa crfl ⨾ S-vApp k n a′ y L sa′ sy)

S-inst₂ zero    n (clo₂ ρ t) x y L sρ sx sy = csym (⟶≅ (psplit-β _ _ _))

S-inst₂ (suc k) n (clo₂ ρ t) x y L sρ sx sy =
  ≡→≅ (sub-single2-ext (⌊ ρ ⌋ᵉ L) (⌊ x ⌋ L) (⌊ y ⌋ L) t (⌊ (ρ , x) , y ⌋ᵉ L) refl refl (λ _ → refl))
  ⨾ S-eval k n ((ρ , x) , y) t L ((sρ , sx) , sy)

------------------------------------------------------------------------
-- 6. ★ Readback, and the theorem.
------------------------------------------------------------------------

-- the readback's level map under a binder IS binding the fresh level
lvl-bind : (Γ : Cx) (l : ℕ) → lvl (Γ ∙) l ≡ bindL (len Γ) (lvl Γ) l

lvl-bind Γ l = refl

S-rb  : (u : Bool) (k : ℕ) (Γ : Cx) (v : Val) → Sc (len Γ) v → ⌊ v ⌋ (lvl Γ) ≅ rb u k Γ v

S-rbᶜ : (u : Bool) (k : ℕ) (Γ : Cx) (c : Clo) → Scᶜ (len Γ) c → ⌊ c ⌋ᶜ (lvl Γ) ≅ rbᶜ u k Γ c

S-rb₂ : (u : Bool) (k : ℕ) (Γ : Cx) (c : Clo₂) → Sc² (len Γ) c → ⌊ c ⌋² (lvl Γ) ≅ rb₂ u k Γ c

S-rbL : (u : Bool) (k : ℕ) (Γ : Cx) (c : Clo) → Scᶜ (len Γ) c → readLam c (lvl Γ) ≅ rbLam u k Γ c

-- a λ-value read back: λ of its body — tr-pw's, by its guard at THIS fuel
S-rbL u k Γ c@(clo _ _)        s = ≅lam (S-rbᶜ u k Γ c s)

S-rbL u k Γ c@(cloK _)         s = ≅lam (S-rbᶜ u k Γ c s)

S-rbL u k Γ c@(cloHrefl _ _ _) s = ≅lam (S-rbᶜ u k Γ c s)

S-rbL u k Γ c@(cloDpay _ _ _)  s = ≅lam (S-rbᶜ u k Γ c s)

S-rbL u k Γ c@(cloHomTo _ _)   s = ≅lam (S-rbᶜ u k Γ c s)

S-rbL u k Γ c@(cloTrPw d f e)  s@(sd , (sf , se)) = go (trPwView k (len Γ) d) (S-view k (len Γ) d (lvl Γ) sd)
  where
  L = lvl Γ
  R = tr (⌊ d ⌋ᶜ L) (lam (⌊ f ⌋ᶜ L)) (⌊ e ⌋ L)
  go : (w : Maybe TrPwV) → VS (len Γ) d L w → R ≅ rbTrPw u k Γ c d f e w
  go nothing             vs′ = ≅tr (S-rbᶜ u k Γ d sd) (≅lam (S-rbᶜ u k Γ f sf)) (S-rb u k Γ e se)
  go (just (trpw c′ sp a)) vs′ = Rλ ⨾ ≅lam (csym back ⨾ S-rbᶜ u k Γ c s)
    where
    B = tr (⌜Hom⌝ (renTm pwShift (pwBody (⌊ c′ ⌋ (bindL (len Γ) L)))) (app (renTm vs (⌊ a ⌋ (bindL (len Γ) L))) (var (vs vz))) (var vz))
           (⌊ f ⌋ᶜ L) (app (renTm vs (⌊ e ⌋ L)) (var vz))
    Rλ : R ≅ lam B
    Rλ = ≅tr vs′ crfl crfl ⨾ ⟶≅ (tr-pw _ _ (⌊ f ⌋ᶜ L) (⌊ e ⌋ L) (pw-read sp (bindL (len Γ) L)))
    -- the closure's reading under the binder is the redex applied: B again
    back : ⌊ c ⌋ᶜ L ≅ B
    back = ≅app (≅-ren vs Rλ) crfl ⨾ (⟶≅ (β _ _) ⨾ ≡→≅ (sub-vz-wk B))

S-rbᶜ u zero    Γ c s = crfl

S-rbᶜ u (suc k) Γ c s =
  S-fresh k (len Γ) c (lvl Γ) s
  ⨾ S-rb u k (Γ ∙) (inst k (suc (len Γ)) c (vvar (len Γ)))
         (sc-inst k (suc (len Γ)) c (vvar (len Γ)) (monoᶜ c (up-suc (len Γ)) s) (lt-self (len Γ)))

S-rb₂ u zero    Γ c s = crfl

S-rb₂ u (suc k) Γ c s =
  S-fresh2 k (len Γ) c (lvl Γ) s
  ⨾ S-rb u k ((Γ ∙) ∙) (inst₂ k (suc (suc (len Γ))) c (vvar (len Γ)) (vvar (suc (len Γ))))
         (sc-inst₂ k (suc (suc (len Γ))) c (vvar (len Γ)) (vvar (suc (len Γ)))
                   (mono² c (up2 (len Γ)) s) (lt-two (len Γ)) (lt-self (suc (len Γ))))

S-rb u k Γ (vvar l) s = crfl

S-rb false k       Γ (vref d b) s = crfl

S-rb true  zero    Γ (vref d b) s = crfl

S-rb true  (suc k) Γ (vref d b) s =
  ⟶≅ (δref d b) ⨾ (≡→≅ (subTm-cong (λ ()) b) ⨾ (S-eval k 0 [] b (lvl Γ) tt
  ⨾ S-rb true k Γ (eval k 0 [] b) (mono (eval k 0 [] b) (up-zero (len Γ)) (sc-eval k 0 [] b tt))))

S-rb u k Γ (vlam c) s0 = S-rbL u k Γ c s0

S-rb u k Γ (vapp f a) (s0 , s1) = ≅app (S-rb u k Γ f s0) (S-rb u k Γ a s1)

S-rb u k Γ (vpair a b) (s0 , s1) = ≅pair (S-rb u k Γ a s0) (S-rb u k Γ b s1)

S-rb u k Γ (vabsurd c e) (s0 , s1) = ≅absurd (S-rb u k Γ c s0) (S-rb u k Γ e s1)

S-rb u k Γ (vordtr a t v p q) (s0 , (s1 , (s2 , (s3 , s4)))) = ≅ordtr (S-rb u k Γ a s0) (S-rb u k Γ t s1) (S-rb u k Γ v s2) (S-rb u k Γ p s3) (S-rb u k Γ q s4)

S-rb u k Γ (vfst p) s0 = ≅fst (S-rb u k Γ p s0)

S-rb u k Γ (vsnd p) s0 = ≅snd (S-rb u k Γ p s0)

S-rb u k Γ v⌜base⌝ s = crfl

S-rb u k Γ (v⌜Π⌝ c d) (s0 , s1) = ≅⌜Π⌝ (S-rb u k Γ c s0) (S-rbᶜ u k Γ d s1)

S-rb u k Γ (v⌜Σ⌝ c d) (s0 , s1) = ≅⌜Σ⌝ (S-rb u k Γ c s0) (S-rbᶜ u k Γ d s1)

S-rb u k Γ (v⌜Hom⌝ c a b) (s0 , (s1 , s2)) = ≅⌜Hom⌝ (S-rb u k Γ c s0) (S-rb u k Γ a s1) (S-rb u k Γ b s2)

S-rb u k Γ (vhrefl c t) (s0 , s1) = ≅hrefl (S-rb u k Γ c s0) (S-rb u k Γ t s1)

S-rb u k Γ (vtr d p e) (s0 , (s1 , s2)) = ≅tr (S-rbᶜ u k Γ d s0) (S-rb u k Γ p s1) (S-rb u k Γ e s2)

S-rb u k Γ (vap c b p) (s0 , (s1 , s2)) = ≅ap (S-rb u k Γ c s0) (S-rbᶜ u k Γ b s1) (S-rb u k Γ p s2)

S-rb u k Γ (v⌜Id⌝ c a b) (s0 , (s1 , s2)) = ≅⌜Id⌝ (S-rb u k Γ c s0) (S-rb u k Γ a s1) (S-rb u k Γ b s2)

S-rb u k Γ (vidrefl c t) (s0 , s1) = ≅idrefl (S-rb u k Γ c s0) (S-rb u k Γ t s1)

S-rb u k Γ (vjsub d p e) (s0 , (s1 , s2)) = ≅jsub (S-rbᶜ u k Γ d s0) (S-rb u k Γ p s1) (S-rb u k Γ e s2)

S-rb u k Γ vunit s = crfl

S-rb u k Γ vnzero s = crfl

S-rb u k Γ (vnsuc t) s0 = ≅nsuc (S-rb u k Γ t s0)

S-rb u k Γ (vnatrec z s t) (s0 , (s1 , s2)) = ≅natrec (S-rb u k Γ z s0) (S-rb₂ u k Γ s s1) (S-rb u k Γ t s2)

S-rb u k Γ (vcon p) s0 = ≅con (S-rb u k Γ p s0)

S-rb u k Γ (vielim D i e t) (s0 , (s1 , (s2 , s3))) = ≅ielim (S-rb u k Γ D s0) (S-rb u k Γ i s1) (S-rb u k Γ e s2) (S-rb u k Γ t s3)

S-rb u k Γ vdι s = crfl

S-rb u k Γ (vdσ S f) (s0 , s1) = ≅dσ (S-rb u k Γ S s0) (S-rb u k Γ f s1)

S-rb u k Γ (vdρ j C) (s0 , s1) = ≅dρ (S-rb u k Γ j s0) (S-rb u k Γ C s1)

S-rb u k Γ (vdpay I D C) (s0 , (s1 , s2)) = ≅dpay (S-rb u k Γ I s0) (S-rb u k Γ D s1) (S-rb u k Γ C s2)

S-rb u k Γ (vdih D e C p) (s0 , (s1 , (s2 , s3))) = ≅dih (S-rb u k Γ D s0) (S-rb u k Γ e s1) (S-rb u k Γ C s2) (S-rb u k Γ p s3)

S-rb u k Γ vfzero s = crfl

S-rb u k Γ (vfsuc t) s0 = ≅fsuc (S-rb u k Γ t s0)

S-rb u k Γ (vfcase t a b) (s0 , (s1 , s2)) = ≅fcase (S-rb u k Γ t s0) (S-rb u k Γ a s1) (S-rbᶜ u k Γ b s2)

S-rb u k Γ (vfcase0 t) s0 = ≅fcase0 (S-rb u k Γ t s0)

S-rb u k Γ (vpsplit b p) (s0 , s1) = ≅psplit (S-rb₂ u k Γ b s0) (S-rb u k Γ p s1)

S-rb u k Γ v⌜Nat⌝ s = crfl

S-rb u k Γ v⌜Unit⌝ s = crfl

S-rb u k Γ (v⌜IMu⌝ I D i) (s0 , (s1 , s2)) = ≅⌜IMu⌝ (S-rb u k Γ I s0) (S-rb u k Γ D s1) (S-rb u k Γ i s2)

S-rb u k Γ (v⌜Fin⌝ t) s0 = ≅⌜Fin⌝ (S-rb u k Γ t s0)

-- ★ the identity environment reads as the identity substitution
sc-idEnv : (Γ : Cx) → Scᵉ (len Γ) (idEnv Γ)

sc-idEnv ε     = tt

sc-idEnv (Γ ∙) = monoᵉ (idEnv Γ) (up-suc (len Γ)) (sc-idEnv Γ) , lt-self (len Γ)

idEnv-read : (Γ : Cx) (x : Var Γ) → ⌊ idEnv Γ ⌋ᵉ (lvl Γ) x ≡ var x

idEnv-read (Γ ∙) vz     = bind-here (len Γ) (lvl Γ)

idEnv-read (Γ ∙) (vs x) =
  trans (agreeᵉ (len Γ) (idEnv Γ) (bind-wk (len Γ) (lvl Γ)) (sc-idEnv Γ) x)
        (trans (sym (renᵉ vs (idEnv Γ) (lvl Γ) x)) (cong (renTm vs) (idEnv-read Γ x)))

------------------------------------------------------------------------
-- ★★ THE THEOREM: the environment evaluator's normal form is convertible
--     with its input — at every fuel.
------------------------------------------------------------------------

nbe-sound : (k : ℕ) (t : RTm Γ) → t ≅ nbe k t

nbe-sound {Γ} k t =
  ≡→≅ (trans (sym (subTm-id t)) (subTm-cong (λ x → sym (idEnv-read Γ x)) t))
  ⨾ (S-eval k (len Γ) (idEnv Γ) t (lvl Γ) (sc-idEnv Γ)
  ⨾ S-rb true k Γ (eval k (len Γ) (idEnv Γ) t) (sc-eval k (len Γ) (idEnv Γ) t (sc-idEnv Γ)))
