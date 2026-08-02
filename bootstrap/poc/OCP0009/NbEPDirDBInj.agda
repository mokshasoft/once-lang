------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 26 — (B2, part 1) Π-INJECTIVITY of conversion
--                            (type-level confluence)
--
-- `NbEPDirDBSR` (dHoTT-24) scoped general subject reduction on exactly one
-- obstruction: inverting `⊢ lam t ∷ Π A B` through `⊢conv` needs Π-injectivity
-- of conversion, `Π A B ≅ᵀ Π A' B' → A ≅ᵀ A' × B ≅ᵀ B'`, which follows from
-- confluence. Confluence of terms is now proven (`NbEPDirDBConf`, dHoTT-25);
-- this module lifts it to TYPES and derives Π-injectivity — removing the
-- ceiling.
--
-- Type reduction has no top-level redex (β lives only at terms, reached via
-- `El`), so type confluence is the structural companion of term confluence:
-- parallel type reduction `_⟹ᵀ_` reuses the TERM triangle (`⟹-⁺`) at `El`
-- leaves. Then:
--   * `confluentᵀ` / `church-rosserᵀ` — confluence and joinability for types.
--   * `Π-reduct` — a reduct of `Π A B` is `Π A'' B''` with `A ⟶ᵀ* A''`,
--     `B ⟶ᵀ* B''` (Π-shape is preserved: only `ξ-Πˡ`/`ξ-Πʳ` apply).
--   * `Π-inj` — Π-INJECTIVITY OF CONVERSION. The dHoTT-24 ceiling, discharged.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBInj where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; base; U; Π; Σ'; El; Hom; RTm; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝
        ; ⌜Hom⌝; hrefl; tr
        ; var; lam; app; pair; fst; snd; vz; vs; renTm )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶ᵀ_; El-⌜base⌝; El-⌜Π⌝; El-⌜Σ⌝; El-⌜Hom⌝
        ; ξ-El; ξ-Πˡ; ξ-Πʳ; ξ-Σˡ; ξ-Σʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; _⟶*_; done; step
        ; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ )
open import poc.OCP0009.NbEPDirDBConf
  using ( _⟹_; pvar; plam; papp; pβ; ppair; pfst; psnd; pβfst; pβsnd
        ; p⌜base⌝; p⌜Π⌝; p⌜Σ⌝; p⌜Hom⌝; phrefl
        ; ptr; ptr-J-base; ptr-J-Σ; ptr-taut
        ; _⁺; ⟹-refl; ⟹-⁺; ⟶→⟹; ⟹→⟶*; ⟶*-trans
        ; ⟹-ren; ⟶*-ren; ⟶*-appˡ )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- Type multi-step reduction and its congruences.
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

------------------------------------------------------------------------
-- Parallel type reduction; reuses the TERM triangle at `El` leaves.
------------------------------------------------------------------------

infix 3 _⟹ᵀ_
data _⟹ᵀ_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  pbase : base {Γ} ⟹ᵀ base
  pU    : U {Γ} ⟹ᵀ U
  pEl   : {t t' : RTm Γ} → t ⟹ t' → El t ⟹ᵀ El t'
  pΠ    : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → A ⟹ᵀ A' → B ⟹ᵀ B' → Π A B ⟹ᵀ Π A' B'
  pΣ    : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → A ⟹ᵀ A' → B ⟹ᵀ B' → Σ' A B ⟹ᵀ Σ' A' B'
  pEl-⌜base⌝ : El (⌜base⌝ {Γ}) ⟹ᵀ base
  pEl-⌜Π⌝ : {c c' : RTm Γ} {d d' : RTm (Γ ∙)} →
            c ⟹ c' → d ⟹ d' → El (⌜Π⌝ c d) ⟹ᵀ Π (El c') (El d')
  pEl-⌜Σ⌝ : {c c' : RTm Γ} {d d' : RTm (Γ ∙)} →
            c ⟹ c' → d ⟹ d' → El (⌜Σ⌝ c d) ⟹ᵀ Σ' (El c') (El d')
  pEl-⌜Hom⌝ : {c c' a a' b b' : RTm Γ} →
              c ⟹ c' → a ⟹ a' → b ⟹ b' →
              El (⌜Hom⌝ c a b) ⟹ᵀ Hom (El c') a' b'
  -- W2: `Hom` congruence, and its two unfoldings (`SpikeHomTy` promoted).
  pHom : {A A' : RTy Γ} {t t' u u' : RTm Γ} →
         A ⟹ᵀ A' → t ⟹ t' → u ⟹ u' → Hom A t u ⟹ᵀ Hom A' t' u'
  pHom-U : {c c' d d' : RTm Γ} →
           c ⟹ c' → d ⟹ d' → Hom U c d ⟹ᵀ Π (El c') (El (renTm vs d'))
  pHom-Π : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} {f f' g g' : RTm Γ} →
           A ⟹ᵀ A' → B ⟹ᵀ B' → f ⟹ f' → g ⟹ g' →
           Hom (Π A B) f g ⟹ᵀ
           Π A' (Hom B' (app (renTm vs f') (var vz)) (app (renTm vs g') (var vz)))

⟹ᵀ-refl : (A : RTy Γ) → A ⟹ᵀ A
⟹ᵀ-refl base     = pbase
⟹ᵀ-refl (El t)   = pEl (⟹-refl t)
⟹ᵀ-refl U        = pU
⟹ᵀ-refl (Π A B)  = pΠ (⟹ᵀ-refl A) (⟹ᵀ-refl B)
⟹ᵀ-refl (Σ' A B) = pΣ (⟹ᵀ-refl A) (⟹ᵀ-refl B)
⟹ᵀ-refl (Hom A t u) = pHom (⟹ᵀ-refl A) (⟹-refl t) (⟹-refl u)

⟶ᵀ→⟹ᵀ : {A B : RTy Γ} → A ⟶ᵀ B → A ⟹ᵀ B
⟶ᵀ→⟹ᵀ El-⌜base⌝    = pEl-⌜base⌝
⟶ᵀ→⟹ᵀ (El-⌜Π⌝ c d) = pEl-⌜Π⌝ (⟹-refl c) (⟹-refl d)
⟶ᵀ→⟹ᵀ (El-⌜Σ⌝ c d) = pEl-⌜Σ⌝ (⟹-refl c) (⟹-refl d)
⟶ᵀ→⟹ᵀ (El-⌜Hom⌝ c a b) = pEl-⌜Hom⌝ (⟹-refl c) (⟹-refl a) (⟹-refl b)
⟶ᵀ→⟹ᵀ (ξ-El r) = pEl (⟶→⟹ r)
⟶ᵀ→⟹ᵀ (ξ-Πˡ r) = pΠ (⟶ᵀ→⟹ᵀ r) (⟹ᵀ-refl _)
⟶ᵀ→⟹ᵀ (ξ-Πʳ r) = pΠ (⟹ᵀ-refl _) (⟶ᵀ→⟹ᵀ r)
⟶ᵀ→⟹ᵀ (ξ-Σˡ r) = pΣ (⟶ᵀ→⟹ᵀ r) (⟹ᵀ-refl _)
⟶ᵀ→⟹ᵀ (ξ-Σʳ r) = pΣ (⟹ᵀ-refl _) (⟶ᵀ→⟹ᵀ r)
⟶ᵀ→⟹ᵀ (Hom-U c d)     = pHom-U (⟹-refl c) (⟹-refl d)
⟶ᵀ→⟹ᵀ (Hom-Π A B f g) =
  pHom-Π (⟹ᵀ-refl A) (⟹ᵀ-refl B) (⟹-refl f) (⟹-refl g)
⟶ᵀ→⟹ᵀ (ξ-Homᵀ r) = pHom (⟶ᵀ→⟹ᵀ r) (⟹-refl _) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-Homˡ r) = pHom (⟹ᵀ-refl _) (⟶→⟹ r) (⟹-refl _)
⟶ᵀ→⟹ᵀ (ξ-Homʳ r) = pHom (⟹ᵀ-refl _) (⟹-refl _) (⟶→⟹ r)

⟹ᵀ→⟶ᵀ* : {A B : RTy Γ} → A ⟹ᵀ B → A ⟶ᵀ* B
⟹ᵀ→⟶ᵀ* pbase    = doneᵀ
⟹ᵀ→⟶ᵀ* pU       = doneᵀ
⟹ᵀ→⟶ᵀ* (pEl p)  = ⟶ᵀ*-El (⟹→⟶* p)
⟹ᵀ→⟶ᵀ* (pΠ p q) = ⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟹ᵀ→⟶ᵀ* p)) (⟶ᵀ*-Πʳ (⟹ᵀ→⟶ᵀ* q))
⟹ᵀ→⟶ᵀ* (pΣ p q) = ⟶ᵀ*-trans (⟶ᵀ*-Σˡ (⟹ᵀ→⟶ᵀ* p)) (⟶ᵀ*-Σʳ (⟹ᵀ→⟶ᵀ* q))
⟹ᵀ→⟶ᵀ* pEl-⌜base⌝ = stepᵀ El-⌜base⌝ doneᵀ
⟹ᵀ→⟶ᵀ* (pEl-⌜Π⌝ {c = c} {d = d} p q) =
  stepᵀ (El-⌜Π⌝ c d)
    (⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟶ᵀ*-El (⟹→⟶* p))) (⟶ᵀ*-Πʳ (⟶ᵀ*-El (⟹→⟶* q))))
⟹ᵀ→⟶ᵀ* (pEl-⌜Σ⌝ {c = c} {d = d} p q) =
  stepᵀ (El-⌜Σ⌝ c d)
    (⟶ᵀ*-trans (⟶ᵀ*-Σˡ (⟶ᵀ*-El (⟹→⟶* p))) (⟶ᵀ*-Σʳ (⟶ᵀ*-El (⟹→⟶* q))))
⟹ᵀ→⟶ᵀ* (pEl-⌜Hom⌝ {c = c} {c'} {a} {a'} {b} {b'} p q r) =
  stepᵀ (El-⌜Hom⌝ c a b)
    (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ (⟶ᵀ*-El (⟹→⟶* p)))
               (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (⟹→⟶* q)) (⟶ᵀ*-Homʳ (⟹→⟶* r))))
⟹ᵀ→⟶ᵀ* (pHom p q r) =
  ⟶ᵀ*-trans (⟶ᵀ*-Homᵀ (⟹ᵀ→⟶ᵀ* p))
    (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (⟹→⟶* q)) (⟶ᵀ*-Homʳ (⟹→⟶* r)))
⟹ᵀ→⟶ᵀ* (pHom-U {c = c} {d = d} p q) =
  stepᵀ (Hom-U c d)
    (⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟶ᵀ*-El (⟹→⟶* p)))
               (⟶ᵀ*-Πʳ (⟶ᵀ*-El (⟶*-ren vs (⟹→⟶* q)))))
⟹ᵀ→⟶ᵀ* (pHom-Π {A = A} {B = B} {f = f} {g = g} pA pB pf pg) =
  stepᵀ (Hom-Π A B f g)
    (⟶ᵀ*-trans (⟶ᵀ*-Πˡ (⟹ᵀ→⟶ᵀ* pA))
      (⟶ᵀ*-Πʳ (⟶ᵀ*-trans (⟶ᵀ*-Homᵀ (⟹ᵀ→⟶ᵀ* pB))
        (⟶ᵀ*-trans (⟶ᵀ*-Homˡ (⟶*-appˡ (⟶*-ren vs (⟹→⟶* pf))))
                   (⟶ᵀ*-Homʳ (⟶*-appˡ (⟶*-ren vs (⟹→⟶* pg))))))))

------------------------------------------------------------------------
-- Complete development + triangle for types.
------------------------------------------------------------------------

_⁺ᵀ : RTy Γ → RTy Γ
base ⁺ᵀ         = base
U ⁺ᵀ            = U
El (var x) ⁺ᵀ   = El (var x ⁺)
El (lam t) ⁺ᵀ   = El (lam t ⁺)
El (app f a) ⁺ᵀ = El (app f a ⁺)
El (pair a b) ⁺ᵀ = El (pair a b ⁺)
El (fst p) ⁺ᵀ   = El (fst p ⁺)
El (snd p) ⁺ᵀ   = El (snd p ⁺)
El ⌜base⌝ ⁺ᵀ    = base
El (⌜Π⌝ c d) ⁺ᵀ = Π (El (c ⁺)) (El (d ⁺))
El (⌜Σ⌝ c d) ⁺ᵀ = Σ' (El (c ⁺)) (El (d ⁺))
El (⌜Hom⌝ c a b) ⁺ᵀ = Hom (El (c ⁺)) (a ⁺) (b ⁺)
El (hrefl c t) ⁺ᵀ   = El (hrefl c t ⁺)
El (tr d p e) ⁺ᵀ    = El (tr d p e ⁺)
Π A B ⁺ᵀ        = Π (A ⁺ᵀ) (B ⁺ᵀ)
Σ' A B ⁺ᵀ       = Σ' (A ⁺ᵀ) (B ⁺ᵀ)
-- W2: `Hom` develops by the head of its TYPE argument.  Where the head is
-- already `U`/`Π` the unfolding fires (with components developed); where it
-- is an `El` code the development DECODES ONLY — one parallel step cannot
-- both decode and unfold, the same one-step-behind pattern `El` itself uses.
Hom base t u ⁺ᵀ        = Hom base (t ⁺) (u ⁺)
Hom U c d ⁺ᵀ           = Π (El (c ⁺)) (El (renTm vs (d ⁺)))
Hom (Π A B) f g ⁺ᵀ     =
  Π (A ⁺ᵀ) (Hom (B ⁺ᵀ) (app (renTm vs (f ⁺)) (var vz))
                       (app (renTm vs (g ⁺)) (var vz)))
Hom (Σ' A B) t u ⁺ᵀ    = Hom (Σ' (A ⁺ᵀ) (B ⁺ᵀ)) (t ⁺) (u ⁺)
Hom (El e) t u ⁺ᵀ      = Hom ((El e) ⁺ᵀ) (t ⁺) (u ⁺)
Hom (Hom A a b) t u ⁺ᵀ = Hom ((Hom A a b) ⁺ᵀ) (t ⁺) (u ⁺)

⟹ᵀ-⁺ : {A B : RTy Γ} → A ⟹ᵀ B → B ⟹ᵀ A ⁺ᵀ
⟹ᵀ-⁺ pbase          = pbase
⟹ᵀ-⁺ pU             = pU
⟹ᵀ-⁺ (pEl (pvar x)) = pEl (⟹-⁺ (pvar x))
⟹ᵀ-⁺ (pEl (plam p)) = pEl (⟹-⁺ (plam p))
⟹ᵀ-⁺ (pEl (papp p q)) = pEl (⟹-⁺ (papp p q))
⟹ᵀ-⁺ (pEl (pβ p q))  = pEl (⟹-⁺ (pβ p q))
⟹ᵀ-⁺ (pEl (ppair p q)) = pEl (⟹-⁺ (ppair p q))
⟹ᵀ-⁺ (pEl (pfst p))  = pEl (⟹-⁺ (pfst p))
⟹ᵀ-⁺ (pEl (psnd p))  = pEl (⟹-⁺ (psnd p))
⟹ᵀ-⁺ (pEl (pβfst p q)) = pEl (⟹-⁺ (pβfst p q))
⟹ᵀ-⁺ (pEl (pβsnd p q)) = pEl (⟹-⁺ (pβsnd p q))
⟹ᵀ-⁺ (pEl p⌜base⌝)   = pEl-⌜base⌝
⟹ᵀ-⁺ (pEl (p⌜Π⌝ p q)) = pEl-⌜Π⌝ (⟹-⁺ p) (⟹-⁺ q)
⟹ᵀ-⁺ (pEl (p⌜Σ⌝ p q)) = pEl-⌜Σ⌝ (⟹-⁺ p) (⟹-⁺ q)
⟹ᵀ-⁺ (pEl (p⌜Hom⌝ p q r)) = pEl-⌜Hom⌝ (⟹-⁺ p) (⟹-⁺ q) (⟹-⁺ r)
⟹ᵀ-⁺ (pEl w@(phrefl _ _))      = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr _ _ _))       = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-J-base _))    = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-J-Σ _))       = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pEl w@(ptr-taut _ _))    = pEl (⟹-⁺ w)
⟹ᵀ-⁺ (pΠ p q)       = pΠ (⟹ᵀ-⁺ p) (⟹ᵀ-⁺ q)
⟹ᵀ-⁺ (pΣ p q)       = pΣ (⟹ᵀ-⁺ p) (⟹ᵀ-⁺ q)
⟹ᵀ-⁺ pEl-⌜base⌝     = pbase
⟹ᵀ-⁺ (pEl-⌜Π⌝ p q)  = pΠ (pEl (⟹-⁺ p)) (pEl (⟹-⁺ q))
⟹ᵀ-⁺ (pEl-⌜Σ⌝ p q)  = pΣ (pEl (⟹-⁺ p)) (pEl (⟹-⁺ q))
-- W2: the `Hom` triangle, dispatching on the type argument's evidence.
-- Only two cases are non-uniform — the heads whose development UNFOLDS.
⟹ᵀ-⁺ (pHom pU pt pu)         = pHom-U (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pΠ pA pB) pt pu) =
  pHom-Π (⟹ᵀ-⁺ pA) (⟹ᵀ-⁺ pB) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pbase pt pu)      = pHom pbase (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pΣ pA pB) pt pu) =
  pHom (pΣ (⟹ᵀ-⁺ pA) (⟹ᵀ-⁺ pB)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pEl pe) pt pu)   =
  pHom (⟹ᵀ-⁺ (pEl pe)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom pEl-⌜base⌝ pt pu) =
  pHom (⟹ᵀ-⁺ pEl-⌜base⌝) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pEl-⌜Π⌝ p q) pt pu) =
  pHom (⟹ᵀ-⁺ (pEl-⌜Π⌝ p q)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pEl-⌜Σ⌝ p q) pt pu) =
  pHom (⟹ᵀ-⁺ (pEl-⌜Σ⌝ p q)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pEl-⌜Hom⌝ p q r) pt pu) =
  pHom (⟹ᵀ-⁺ (pEl-⌜Hom⌝ p q r)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pHom pA pa pb) pt pu) =
  pHom (⟹ᵀ-⁺ (pHom pA pa pb)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pHom-U p q) pt pu) =
  pHom (⟹ᵀ-⁺ (pHom-U p q)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pHom (pHom-Π pA pB pf pg) pt pu) =
  pHom (⟹ᵀ-⁺ (pHom-Π pA pB pf pg)) (⟹-⁺ pt) (⟹-⁺ pu)
⟹ᵀ-⁺ (pEl-⌜Hom⌝ p q r) = pHom (pEl (⟹-⁺ p)) (⟹-⁺ q) (⟹-⁺ r)
⟹ᵀ-⁺ (pHom-U p q) = pΠ (pEl (⟹-⁺ p)) (pEl (⟹-ren vs (⟹-⁺ q)))
⟹ᵀ-⁺ (pHom-Π pA pB pf pg) =
  pΠ (⟹ᵀ-⁺ pA)
     (pHom (⟹ᵀ-⁺ pB) (papp (⟹-ren vs (⟹-⁺ pf)) (pvar vz))
                     (papp (⟹-ren vs (⟹-⁺ pg)) (pvar vz)))

------------------------------------------------------------------------
-- Diamond → confluence → Church–Rosser, for types.
------------------------------------------------------------------------

diamondᵀ : {A B C : RTy Γ} → A ⟹ᵀ B → A ⟹ᵀ C →
           Σ (RTy _) (λ D → (B ⟹ᵀ D) × (C ⟹ᵀ D))
diamondᵀ {A = A} pu pv = (A ⁺ᵀ) , (⟹ᵀ-⁺ pu , ⟹ᵀ-⁺ pv)

infix 3 _⟹ᵀ*_
data _⟹ᵀ*_ : {Γ : Cx} → RTy Γ → RTy Γ → Set where
  pdoneᵀ : {A : RTy Γ} → A ⟹ᵀ* A
  pstepᵀ : {A B C : RTy Γ} → A ⟹ᵀ B → B ⟹ᵀ* C → A ⟹ᵀ* C

stripᵀ : {A B C : RTy Γ} → A ⟹ᵀ B → A ⟹ᵀ* C →
         Σ (RTy _) (λ D → (B ⟹ᵀ* D) × (C ⟹ᵀ D))
stripᵀ pu pdoneᵀ = _ , (pdoneᵀ , pu)
stripᵀ pu (pstepᵀ pv pv*) with diamondᵀ pu pv
... | w₁ , (u⟹w₁ , v₁⟹w₁) with stripᵀ v₁⟹w₁ pv*
...   | w , (w₁⟹*w , v⟹w) = w , (pstepᵀ u⟹w₁ w₁⟹*w , v⟹w)

confluent⟹ᵀ : {A B C : RTy Γ} → A ⟹ᵀ* B → A ⟹ᵀ* C →
              Σ (RTy _) (λ D → (B ⟹ᵀ* D) × (C ⟹ᵀ* D))
confluent⟹ᵀ pdoneᵀ pv = _ , (pv , pdoneᵀ)
confluent⟹ᵀ (pstepᵀ pu pu*) pv with stripᵀ pu pv
... | w₁ , (u₁⟹*w₁ , v⟹w₁) with confluent⟹ᵀ pu* u₁⟹*w₁
...   | w , (u⟹*w , w₁⟹*w) = w , (u⟹*w , pstepᵀ v⟹w₁ w₁⟹*w)

⟶ᵀ*→⟹ᵀ* : {A B : RTy Γ} → A ⟶ᵀ* B → A ⟹ᵀ* B
⟶ᵀ*→⟹ᵀ* doneᵀ       = pdoneᵀ
⟶ᵀ*→⟹ᵀ* (stepᵀ r p) = pstepᵀ (⟶ᵀ→⟹ᵀ r) (⟶ᵀ*→⟹ᵀ* p)

⟹ᵀ*→⟶ᵀ* : {A B : RTy Γ} → A ⟹ᵀ* B → A ⟶ᵀ* B
⟹ᵀ*→⟶ᵀ* pdoneᵀ        = doneᵀ
⟹ᵀ*→⟶ᵀ* (pstepᵀ p ps) = ⟶ᵀ*-trans (⟹ᵀ→⟶ᵀ* p) (⟹ᵀ*→⟶ᵀ* ps)

confluentᵀ : {A B C : RTy Γ} → A ⟶ᵀ* B → A ⟶ᵀ* C →
             Σ (RTy _) (λ D → (B ⟶ᵀ* D) × (C ⟶ᵀ* D))
confluentᵀ p q with confluent⟹ᵀ (⟶ᵀ*→⟹ᵀ* p) (⟶ᵀ*→⟹ᵀ* q)
... | w , (uw , vw) = w , (⟹ᵀ*→⟶ᵀ* uw , ⟹ᵀ*→⟶ᵀ* vw)

church-rosserᵀ : {A B : RTy Γ} → A ≅ᵀ B → Σ (RTy _) (λ C → (A ⟶ᵀ* C) × (B ⟶ᵀ* C))
church-rosserᵀ (credᵀ r)   = _ , (stepᵀ r doneᵀ , doneᵀ)
church-rosserᵀ crflᵀ       = _ , (doneᵀ , doneᵀ)
church-rosserᵀ (csymᵀ c) with church-rosserᵀ c
... | w , (aw , bw) = w , (bw , aw)
church-rosserᵀ (ctrnᵀ c d) with church-rosserᵀ c | church-rosserᵀ d
... | w₁ , (aw₁ , mw₁) | w₂ , (mw₂ , bw₂) with confluentᵀ mw₁ mw₂
...   | w , (w₁w , w₂w) = w , (⟶ᵀ*-trans aw₁ w₁w , ⟶ᵀ*-trans bw₂ w₂w)

------------------------------------------------------------------------
-- Π-shape is preserved by reduction, and Π-INJECTIVITY of conversion.
------------------------------------------------------------------------

record ΠRed {Γ} (A : RTy Γ) (B : RTy (Γ ∙)) (C : RTy Γ) : Set where
  constructor mkΠRed
  field
    A'' : RTy Γ
    B'' : RTy (Γ ∙)
    eqC : C ≡ Π A'' B''
    rA  : A ⟶ᵀ* A''
    rB  : B ⟶ᵀ* B''

Π-reduct : {A : RTy Γ} {B : RTy (Γ ∙)} {C : RTy Γ} → Π A B ⟶ᵀ* C → ΠRed A B C
Π-reduct {A = A} {B} doneᵀ = mkΠRed A B refl doneᵀ doneᵀ
Π-reduct (stepᵀ (ξ-Πˡ r) rest) with Π-reduct rest
... | mkΠRed A'' B'' eqC rA rB = mkΠRed A'' B'' eqC (stepᵀ r rA) rB
Π-reduct (stepᵀ (ξ-Πʳ r) rest) with Π-reduct rest
... | mkΠRed A'' B'' eqC rA rB = mkΠRed A'' B'' eqC rA (stepᵀ r rB)

-- reductions ⊆ conversion.
red→≅ᵀ : {A B : RTy Γ} → A ⟶ᵀ* B → A ≅ᵀ B
red→≅ᵀ doneᵀ       = crflᵀ
red→≅ᵀ (stepᵀ r p) = ctrnᵀ (credᵀ r) (red→≅ᵀ p)

-- Π constructor is injective for `≡`.
Πinj≡ : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → Π A B ≡ Π A' B' → (A ≡ A') × (B ≡ B')
Πinj≡ refl = refl , refl

-- ★ Π-INJECTIVITY OF CONVERSION — dHoTT-24's scoped ceiling, discharged.
Π-inj : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} →
        Π A B ≅ᵀ Π A' B' → (A ≅ᵀ A') × (B ≅ᵀ B')
Π-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) with Π-reduct r₁ | Π-reduct r₂
...   | mkΠRed A₁ B₁ eq₁ rA₁ rB₁ | mkΠRed A₂ B₂ eq₂ rA₂ rB₂
        with Πinj≡ (trans (sym eq₁) eq₂)
...       | (eqA , eqB) =
            ctrnᵀ (red→≅ᵀ rA₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqA) rA₂)))
          , ctrnᵀ (red→≅ᵀ rB₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqB) rB₂)))

------------------------------------------------------------------------
-- Σ-injectivity (mirrors Π-injectivity) — for `⊢fst`/`⊢snd` inversion (A1).
------------------------------------------------------------------------

record ΣRed {Γ} (A : RTy Γ) (B : RTy (Γ ∙)) (C : RTy Γ) : Set where
  constructor mkΣRed
  field
    A'' : RTy Γ
    B'' : RTy (Γ ∙)
    eqC : C ≡ Σ' A'' B''
    rA  : A ⟶ᵀ* A''
    rB  : B ⟶ᵀ* B''

Σ-reduct : {A : RTy Γ} {B : RTy (Γ ∙)} {C : RTy Γ} → Σ' A B ⟶ᵀ* C → ΣRed A B C
Σ-reduct {A = A} {B} doneᵀ = mkΣRed A B refl doneᵀ doneᵀ
Σ-reduct (stepᵀ (ξ-Σˡ r) rest) with Σ-reduct rest
... | mkΣRed A'' B'' eqC rA rB = mkΣRed A'' B'' eqC (stepᵀ r rA) rB
Σ-reduct (stepᵀ (ξ-Σʳ r) rest) with Σ-reduct rest
... | mkΣRed A'' B'' eqC rA rB = mkΣRed A'' B'' eqC rA (stepᵀ r rB)

Σinj≡ : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} → Σ' A B ≡ Σ' A' B' → (A ≡ A') × (B ≡ B')
Σinj≡ refl = refl , refl

Σ-inj : {A A' : RTy Γ} {B B' : RTy (Γ ∙)} →
        Σ' A B ≅ᵀ Σ' A' B' → (A ≅ᵀ A') × (B ≅ᵀ B')
Σ-inj c with church-rosserᵀ c
... | C , (r₁ , r₂) with Σ-reduct r₁ | Σ-reduct r₂
...   | mkΣRed A₁ B₁ eq₁ rA₁ rB₁ | mkΣRed A₂ B₂ eq₂ rA₂ rB₂
        with Σinj≡ (trans (sym eq₁) eq₂)
...       | (eqA , eqB) =
            ctrnᵀ (red→≅ᵀ rA₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqA) rA₂)))
          , ctrnᵀ (red→≅ᵀ rB₁) (csymᵀ (red→≅ᵀ (subst (_ ⟶ᵀ*_) (sym eqB) rB₂)))
