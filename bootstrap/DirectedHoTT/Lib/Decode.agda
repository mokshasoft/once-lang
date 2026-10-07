-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — ★ CLOSED-NORMAL INVERSION (PLAN-FAITHFUL F6.0).
--
-- Decoding reads a CLOSED NORMAL inhabitant back, one introduction form
-- at a time.  Each lemma takes the typing at the type the decoder KNOWS
-- (not the one generation happens to return) and gives the pieces typed
-- at that type's own components, and normal:
--
--     con-dec   at `IMu I D i`         a `con p`,   p at `El (dpay I D (app D i))`
--     pay-ι     at `dpay I D C`, C ⟶* dι        `unit` (`Canonicity.canUnit`:
--                                                `Unit` is canonical)
--     pay-σ     …, C ⟶* dσ S f                  `pair a b`, a at `El S`,
--                                                b at `El (dpay I D (app f a))`
--     pay-ρ     …, C ⟶* dρ j C'                 `pair r b`, r at `IMu I D j`,
--                                                b at `El (dpay I D C')`
--     tag-dec   at `Fin n`             `tag k` with `k < n`
--     idrefl-dec at `Id A a b`         an `idrefl`, and `a ≅ b`
--     tel-dec   at `dpay I D (subTm σ ⌜ T ⌝ᵗ)`  the payload along the
--               `Tel` view, field by field (`TDec`) — the converse of
--               `Tel.payN-red`
--
-- The route is always: progress at a normal term is a canonical form
-- (`Canonicity.progress`), the inert head picks the introduction form
-- (`canAt`), generation types its pieces up to conversion, and the
-- head's injectivity puts the conversion back on the components.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_; _<ˢ?_ )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Lib.Decode (𝒮 : KSig) (wf : WfK 𝒮) where

-- ★ PLAN-REF: at a well-formed signature, all its names
private
  n = KSig.size 𝒮
  ok = Entries.sigOK 𝒮 n wf
  refs = Entries.refsOK 𝒮 n (λ p → p) wf


open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_; _×_; ⊥; ⊥-elim )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Syntax using ( Fin )
open import DirectedHoTT.Lib.NatNum 𝒮 n using ( num )
open import DirectedHoTT.Spec.Typing 𝒮 n hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong 𝒮
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; red→≅ᵀ; ⟶*-trans
        ; ⟶*-appˡ; ⟶*-appʳ; ⟶*-dpayᴵ; ⟶*-dpayᴰ; ⟶*-dpayᶜ )
open import DirectedHoTT.Metatheory.Confluence 𝒮 using ( church-rosser )
open import DirectedHoTT.Metatheory.Injectivity 𝒮
  using ( church-rosserᵀ; IMu-inj; Σ-inj; Fin-inj; Id-reduct; nzero≇nsuc; nsuc-inj≅; Fin-cong≅ )
open import DirectedHoTT.Metatheory.TySub 𝒮 n using ( wk-cancel-tm; ⊢-cast )
open import DirectedHoTT.Metatheory.SubjectReductionBase 𝒮 using ( ≅ᵀ-sub )
open import DirectedHoTT.Metatheory.SubjectReduction 𝒮 n ok
  using ( gen-con; gen-pair; gen-fsuc; gen-idrefl )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( IsNormal )
open import DirectedHoTT.Metatheory.Canonicity 𝒮 wf
  using ( Canon; Prog; prog-can; prog-step; progress; canAt; CanOf
        ; Inert; in-IMu; in-Σ; in-Unit; in-Fin; in-Id
        ; co-con; co-pair; co-unit; co-fzero; co-fsuc; co-idrefl
        ; gen-fzero; canUnit )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic 𝒮 using ( _,ₛ_ )
open import DirectedHoTT.Lib.Sugar 𝒮 n ok using ( tag; conₗ; Lt; lt-z; lt-s; Cons; []; _∷_; Nth; nth-z; nth-s; selF; selF-β )
open import DirectedHoTT.Lib.Tel 𝒮 n ok using ( Tel; tι; tσ; tρ; ⌜_⌝ᵗ; sub-snoc )

------------------------------------------------------------------------
-- 1. Normal forms, and their subterms.
------------------------------------------------------------------------

-- ★ a closed normal typed term is canonical
canon : {t : RTm ε} {T : RTy ε} → ◇ ⊢ t ∷ T → IsNormal t → Canon t
canon d nrm with progress d
... | prog-can cn = cn
... | prog-step r = ⊥-elim (nrm r)

nrm-con : {p : RTm ε} → IsNormal (con p) → IsNormal p
nrm-con nrm r = nrm (ξ-con r)

nrm-pairˡ : {a b : RTm ε} → IsNormal (pair a b) → IsNormal a
nrm-pairˡ nrm r = nrm (ξ-pairˡ r)

nrm-pairʳ : {a b : RTm ε} → IsNormal (pair a b) → IsNormal b
nrm-pairʳ nrm r = nrm (ξ-pairʳ r)

nrm-fsuc : {t : RTm ε} → IsNormal (fsuc t) → IsNormal t
nrm-fsuc nrm r = nrm (ξ-fsuc r)

------------------------------------------------------------------------
-- 2. Conversions from common reducts.
------------------------------------------------------------------------

joinᵀ : {Γ : Cx} {A B C : RTy Γ} → A ⟶ᵀ* C → B ⟶ᵀ* C → A ≅ᵀ B
joinᵀ ra rb = ctrnᵀ (red→≅ᵀ ra) (csymᵀ (red→≅ᵀ rb))

-- the payload type of a constructor, reduced along its three components
payRed : {Γ : Cx} {I I' D D' i i' : RTm Γ} → I ⟶* I' → D ⟶* D' → i ⟶* i' →
         El (dpay I D (app D i)) ⟶ᵀ* El (dpay I' D' (app D' i'))
payRed rI rD ri =
  ⟶ᵀ*-El (⟶*-trans (⟶*-dpayᴵ rI) (⟶*-trans (⟶*-dpayᴰ rD)
           (⟶*-dpayᶜ (⟶*-trans (⟶*-appˡ rD) (⟶*-appʳ ri)))))

-- ★ the payload type respects conversion of the family's components
payConv : {Γ : Cx} {I I' D D' i i' : RTm Γ} → I ≅ I' → D ≅ D' → i ≅ i' →
          El (dpay I D (app D i)) ≅ᵀ El (dpay I' D' (app D' i'))
payConv cI cD ci with church-rosser cI | church-rosser cD | church-rosser ci
... | _ , (rI , rI') | _ , (rD , rD') | _ , (ri , ri') = joinᵀ (payRed rI rD ri) (payRed rI' rD' ri')

------------------------------------------------------------------------
-- 3. ★ The family: a closed normal inhabitant is a constructor.
------------------------------------------------------------------------

con-dec : {t : RTm ε} {I D i : RTm ε} → ◇ ⊢ t ∷ IMu I D i → IsNormal t →
          Σ (RTm ε) (λ p → (t ≡ con p) × ((◇ ⊢ p ∷ El (dpay I D (app D i))) × IsNormal p))
con-dec d nrm with canAt d crflᵀ in-IMu (λ ()) (canon d nrm)
... | co-con p with gen-con d
...   | I' , (D' , (i' , (_ , (_ , (_ , (dp , cv)))))) with IMu-inj cv
...     | cI , (cD , ci) = p , (refl , (⊢conv dp (csymᵀ (payConv cI cD ci)) , nrm-con nrm))

------------------------------------------------------------------------
-- 4. ★ Payloads, one telescope entry at a time.
------------------------------------------------------------------------

private
  -- a closed normal pair at a type reducing to a Σ: its halves, typed at
  --   the Σ's own components
  pair-dec : {p : RTm ε} {T : RTy ε} {A : RTy ε} {B : RTy (ε ∙)} →
             ◇ ⊢ p ∷ T → T ⟶ᵀ* Σ' A B → IsNormal p →
             Σ (RTm ε) (λ a → Σ (RTm ε) (λ b → (p ≡ pair a b) ×
               (((◇ ⊢ a ∷ A) × (◇ ⊢ b ∷ subTy (single a) B)) × (IsNormal a × IsNormal b))))
  pair-dec d r nrm with canAt d (red→≅ᵀ r) in-Σ (λ ()) (canon d nrm)
  ... | co-pair a b with gen-pair d
  ...   | A' , (B' , (cv , (_ , (da , db)))) with Σ-inj (ctrnᵀ (csymᵀ cv) (red→≅ᵀ r))
  ...     | cA , cB =
            a , (b , (refl , ((⊢conv da cA , ⊢conv db (≅ᵀ-sub (single a) cB))
                     , (nrm-pairˡ nrm , nrm-pairʳ nrm))))

pay-ι : {p I D C : RTm ε} → ◇ ⊢ p ∷ El (dpay I D C) → C ⟶* dι → IsNormal p → p ≡ unit
pay-ι d r nrm =
  canUnit (⊢conv d (red→≅ᵀ (⟶ᵀ*-trans (⟶ᵀ*-El (⟶*-dpayᶜ r)) (stepᵀ (ξ-El (dpay-ι _ _)) (stepᵀ El-⌜Unit⌝ doneᵀ))))) nrm

-- what the payload decoders return (named: a caller's helper states them)
PayΣ : (I D S f p : RTm ε) → Set
PayΣ I D S f p = Σ (RTm ε) (λ a → Σ (RTm ε) (λ b → (p ≡ pair a b) ×
                   (((◇ ⊢ a ∷ El S) × (◇ ⊢ b ∷ El (dpay I D (app f a)))) × (IsNormal a × IsNormal b))))

PayΡ : (I D j C' p : RTm ε) → Set
PayΡ I D j C' p = Σ (RTm ε) (λ r → Σ (RTm ε) (λ b → (p ≡ pair r b) ×
                    (((◇ ⊢ r ∷ IMu I D j) × (◇ ⊢ b ∷ El (dpay I D C'))) × (IsNormal r × IsNormal b))))

pay-σ : {p I D C S f : RTm ε} → ◇ ⊢ p ∷ El (dpay I D C) → C ⟶* dσ S f → IsNormal p → PayΣ I D S f p
pay-σ {I = I} {D} {S = S} {f} d r nrm
  with pair-dec d (⟶ᵀ*-trans (⟶ᵀ*-El (⟶*-dpayᶜ r))
                    (stepᵀ (ξ-El (dpay-σ I D S f)) (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ))) nrm
... | a , (b , (eq , ((da , db) , nn))) =
      a , (b , (eq , ((da , ⊢-cast (cong El (cong₃' (wk-cancel-tm a I) (wk-cancel-tm a D) (cong (λ g → app g a) (wk-cancel-tm a f)))) db) , nn)))
  where
    cong₃' : {I₁ I₂ D₁ D₂ C₁ C₂ : RTm ε} → I₁ ≡ I₂ → D₁ ≡ D₂ → C₁ ≡ C₂ → dpay I₁ D₁ C₁ ≡ dpay I₂ D₂ C₂
    cong₃' refl refl refl = refl

pay-ρ : {p I D C j C' : RTm ε} → ◇ ⊢ p ∷ El (dpay I D C) → C ⟶* dρ j C' → IsNormal p → PayΡ I D j C' p
pay-ρ {I = I} {D} {j = j} {C'} d r nrm
  with pair-dec d (⟶ᵀ*-trans (⟶ᵀ*-El (⟶*-dpayᶜ r))
                    (stepᵀ (ξ-El (dpay-ρ I D j C')) (stepᵀ (El-⌜Σ⌝ _ _) doneᵀ))) nrm
... | a , (b , (eq , ((da , db) , nn))) =
      a , (b , (eq , ((⊢conv da (credᵀ El-⌜IMu⌝)
                     , ⊢-cast (cong El (cong₃' (wk-cancel-tm a I) (wk-cancel-tm a D) (wk-cancel-tm a C'))) db) , nn)))
  where
    cong₃' : {I₁ I₂ D₁ D₂ C₁ C₂ : RTm ε} → I₁ ≡ I₂ → D₁ ≡ D₂ → C₁ ≡ C₂ → dpay I₁ D₁ C₁ ≡ dpay I₂ D₂ C₂
    cong₃' refl refl refl = refl

------------------------------------------------------------------------
-- 5. Tags and identity proofs.
------------------------------------------------------------------------

-- ★ a closed normal tag is a numeral below its bound — the bound only up
--   to conversion (`Fin` is indexed by a Nat TERM)
tag-dec : {t : RTm ε} {n : ℕ} → ◇ ⊢ t ∷ Fin (num n) → IsNormal t →
          Σ ℕ (λ k → Lt k n × (t ≡ tag k))
tag-dec d nrm with canAt d crflᵀ in-Fin (λ ()) (canon d nrm)
tag-dec {n = zero} d nrm | co-fzero with gen-fzero d
... | m , cv = ⊥-elim (nzero≇nsuc (Fin-inj cv))
tag-dec {n = suc n} d nrm | co-fzero = zero , (lt-z , refl)
tag-dec {t = fsuc t'} {n = zero} d nrm | co-fsuc .t' with gen-fsuc d
... | m , (dt , cv) = ⊥-elim (nzero≇nsuc (Fin-inj cv))
tag-dec {t = fsuc t'} {n = suc n} d nrm | co-fsuc .t' with gen-fsuc d
... | m , (dt , cv) with tag-dec (⊢conv dt (Fin-cong≅ (csym (nsuc-inj≅ (Fin-inj cv))))) (nrm-fsuc nrm)
...   | k , (lt , eq) = suc k , (lt-s lt , cong fsuc eq)

-- at a CODE of tags
tag-decᶜ : {t : RTm ε} {n : ℕ} → ◇ ⊢ t ∷ El (⌜Fin⌝ (num n)) → IsNormal t →
           Σ ℕ (λ k → Lt k n × (t ≡ tag k))
tag-decᶜ d = tag-dec (⊢conv d (credᵀ El-⌜Fin⌝))

private
  Id-inj : {A A' : RTy ε} {a a' b b' : RTm ε} → Id A a b ≅ᵀ Id A' a' b' → (a ≅ a') × (b ≅ b')
  Id-inj c with church-rosserᵀ c
  ... | C , (r₁ , r₂) with Id-reduct r₁ | Id-reduct r₂
  ...   | _ , (_ , (_ , (refl , (_ , (ra , rb))))) | _ , (_ , (_ , (refl , (_ , (ra' , rb'))))) =
          ctrn (red→≅ ra) (csym (red→≅ ra')) , ctrn (red→≅ rb) (csym (red→≅ rb'))
    where
      red→≅ : {t u : RTm ε} → t ⟶* u → t ≅ u
      red→≅ done       = crfl
      red→≅ (step r p) = ctrn (cred r) (red→≅ p)

-- ★ a closed normal identity proof makes its endpoints convertible
idrefl-dec : {t : RTm ε} {A : RTy ε} {a b : RTm ε} → ◇ ⊢ t ∷ Id A a b → IsNormal t → a ≅ b
idrefl-dec d nrm with canAt d crflᵀ in-Id (λ ()) (canon d nrm)
... | co-idrefl c s with gen-idrefl d
...   | (_ , (_ , cv)) with Id-inj (csymᵀ cv)
...     | ca , cb = ctrn (csym ca) cb

idrefl-decᶜ : {t c a b : RTm ε} → ◇ ⊢ t ∷ El (⌜Id⌝ c a b) → IsNormal t → a ≅ b
idrefl-decᶜ d = idrefl-dec (⊢conv d (credᵀ (El-⌜Id⌝ _ _ _)))

------------------------------------------------------------------------
-- 6. ★ A payload along the `Tel` view, under a pending substitution
--    (the `PayN` discipline: a `tσ` field extends `σ` by its value).
------------------------------------------------------------------------

data TDec (I D : RTm ε) : {Δ : Cx} → Sub Δ ε → Tel Δ → RTm ε → Set where
  td-ι : {Δ : Cx} {σ : Sub Δ ε} → TDec I D σ tι unit
  td-σ : {Δ : Cx} {σ : Sub Δ ε} {S : RTm Δ} {T : Tel (Δ ∙)} {a b : RTm ε} →
         ◇ ⊢ a ∷ El (subTm σ S) → IsNormal a → TDec I D (σ ,ₛ a) T b → TDec I D σ (tσ S T) (pair a b)
  td-ρ : {Δ : Cx} {σ : Sub Δ ε} {j : RTm Δ} {T : Tel Δ} {r b : RTm ε} →
         ◇ ⊢ r ∷ IMu I D (subTm σ j) → IsNormal r → TDec I D σ T b → TDec I D σ (tρ j T) (pair r b)

tel-dec : {Δ : Cx} {I D p : RTm ε} (σ : Sub Δ ε) (T : Tel Δ) →
          ◇ ⊢ p ∷ El (dpay I D (subTm σ ⌜ T ⌝ᵗ)) → IsNormal p → TDec I D σ T p
tel-dec σ tι dp nrm with pay-ι dp done nrm
... | refl = td-ι
tel-dec {I = I} {D} σ (tσ S T) dp nrm with pay-σ dp done nrm
... | a , (b , (refl , ((da , db) , (na , nb)))) =
      td-σ da na (tel-dec (σ ,ₛ a) T
        (⊢-cast (cong (λ X → El (dpay I D X)) (sub-snoc σ a ⌜ T ⌝ᵗ))
                (⊢conv db (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (step (β _ a) done)))))) nb)
tel-dec σ (tρ j T) dp nrm with pay-ρ dp done nrm
... | r , (b , (refl , ((dr , db) , (nr , nb)))) = td-ρ dr nr (tel-dec σ T db nb)

------------------------------------------------------------------------
-- 7. ★ Normal forms are unique up to conversion.
------------------------------------------------------------------------

⟶*→≅ : {Γ : Cx} {a b : RTm Γ} → a ⟶* b → a ≅ b
⟶*→≅ done       = crfl
⟶*→≅ (step r p) = ctrn (cred r) (⟶*→≅ p)

nf-red : {a b : RTm ε} → IsNormal a → a ⟶* b → a ≡ b
nf-red nrm done       = refl
nf-red nrm (step r _) = ⊥-elim (nrm r)

nf-≅ : {a b : RTm ε} → IsNormal a → IsNormal b → a ≅ b → a ≡ b
nf-≅ na nb c with church-rosser c
... | w , (ra , rb) = trans (nf-red na ra) (sym (nf-red nb rb))

------------------------------------------------------------------------
-- 8. ★ A FIBRE OF RULES: `dσ (⌜Fin⌝ m) (selF Cs)` — a closed normal
--    inhabitant is one rule `k`, with its payload at that rule's
--    telescope.  With no rules (`m = 0`) there is none.
------------------------------------------------------------------------

nthC : {Δ : Cx} {m k : ℕ} (Cs : Cons Δ m) → Lt k m → Σ (RTm Δ) (Nth Cs k)
nthC (C ∷ Cs) lt-z     = C , nth-z
nthC (C ∷ Cs) (lt-s l) with nthC Cs l
... | C' , nt = C' , nth-s nt

RowsDec : (I D : RTm ε) {m : ℕ} → Cons ε m → RTm ε → Set
RowsDec I D Cs x = Σ ℕ (λ k → Σ (RTm ε) (λ C → Σ (RTm ε) (λ q →
                     Nth Cs k C × ((x ≡ conₗ k q) × ((◇ ⊢ q ∷ El (dpay I D C)) × IsNormal q)))))

rows-dec : {I D i x : RTm ε} {m : ℕ} {Cs : Cons ε m} → app D i ⟶* dσ (⌜Fin⌝ (num m)) (selF Cs) →
           ◇ ⊢ x ∷ IMu I D i → IsNormal x → RowsDec I D Cs x
rows-dec {I = I} {D} {Cs = Cs} r dx nrm with con-dec dx nrm
... | q₀ , (refl , (dq₀ , nq₀)) with pay-σ dq₀ r nq₀
...   | t , (q , (refl , ((dt , dq) , (nt , nq)))) with tag-decᶜ dt nt
...     | k , (lt , refl) with nthC Cs lt
...       | C , nth = k , (C , (q , (nth , (refl ,
                        (⊢conv dq (red→≅ᵀ (⟶ᵀ*-El (⟶*-dpayᶜ (selF-β nth)))) , nq)))))

-- a fibre with no rule is empty
rows-none : {I D i x : RTm ε} → app D i ⟶* dσ (⌜Fin⌝ (num 0)) (selF ([] {ε})) → ◇ ⊢ x ∷ IMu I D i → IsNormal x → ⊥
rows-none r dx nrm with rows-dec r dx nrm
... | _ , (_ , (_ , (() , _)))

------------------------------------------------------------------------
-- 9. Chaining decoders without `with` (with-over-knot-contexts-ooms):
--    `step ▷ λ { pattern → next }`, each step typed by the one before.
------------------------------------------------------------------------

infixl 1 _▷_
_▷_ : {A B : Set} → A → (A → B) → B
x ▷ f = f x

-- a payload at an EMPTY rule list (`dσ (⌜Fin⌝ 0) …`) has no inhabitant
pay-none : {p I D C f : RTm ε} → ◇ ⊢ p ∷ El (dpay I D C) → C ⟶* dσ (⌜Fin⌝ (num 0)) f → IsNormal p → ⊥
pay-none dp r np with pay-σ dp r np
... | t , (_ , (_ , ((dt , _) , (nt , _)))) with tag-decᶜ dt nt
...   | _ , (() , _)
