------------------------------------------------------------------------
-- OCP-0009 · W2 eliminator, STAGE 1 — `⊢tr` as a STAGED judgment, with
--                                     subject reduction.
--
-- The consolidation (2026-08-01/02) landed the three W2 term formers
-- (`⌜Hom⌝`/`hrefl`/`tr`) in the kernel syntax with SpikeTr's path-keyed
-- reduction rules, and re-proved the raw metatheory over them
-- (substitution calculus, confluence, type confluence + injectivity).
-- `⊢⌜Hom⌝`/`⊢hrefl` joined the base judgment with `sr` and `fund`.
--
-- `⊢tr` is STAGED here instead, because its `fund` case REOPENS the
-- `SpikeHomLR` gate at exactly the spot the handoff told W2 to watch:
-- an ELIMINATOR's semantic case needs its computation packaged in the
-- scrutinee-type's membership clause (the way `⊩Π`'s membership carries
-- `app` and `⊩Σ`'s carries `fst`/`snd`).  `tr`'s case therefore needs
-- the `Hom`-membership to carry a TRANSPORT CLOSURE — a change to the
-- relation's clause shape, which per the gate's own instruction must be
-- SPIKED before touching the relation (`SpikeTrLR`, next session).
--
-- WHAT THIS MODULE PROVES, on the revised SpikeTr §0 spec:
--   * `_⊢ᵗ_∷_` — the base judgment plus `⊢tr` (premises in the BASE
--     judgment: stage 1 does not nest `tr` inside its own motive/path —
--     an honest, documented restriction, irrelevant to the done-when);
--   * `srᵗ` — SUBJECT REDUCTION for the extended judgment.  The J cases
--     extract the endpoint conversion a canonical identity path
--     witnesses via confluence (stuck-ambient `Hom`s never unfold, so
--     reducts decompose componentwise); the taut case re-types the redex
--     as the application it becomes (`Hom-U` was the only possible
--     unfold, refuting the `Hom-Π` branch against the tautological
--     motive's typing); the `ξ-trᵈ` case carries `PosC` across the
--     motive's step (`posc-red` — reduction cannot introduce the
--     transported variable).
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBTr where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; subst; cong; Σ; _,_; _×_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTy; base; U; Π; Σ'; El; Hom
        ; RTm; var; lam; app; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr
        ; Sub; subTm; subTy; renTm; renTy )
open import poc.OCP0009.NbEPDirDBVar
  using ( PosC; posc-var; posc-Hom; sym-code; sym-code-not-posc )
open import poc.OCP0009.NbEPDirDBType
  using ( single; _⟶_; _⟶*_; done; step; β
        ; tr-J-base; tr-J-Σ; tr-taut; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ; ξ-El
        ; El-⌜base⌝; El-⌜Hom⌝; Hom-U
        ; _⟶ᵀ_; _≅ᵀ_; credᵀ; crflᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢conv
        ; ⊢⌜base⌝; ⊢⌜Hom⌝; ⊢hrefl; _⊢ty_; ty-El )
open import poc.OCP0009.NbEPDirDBSR using ( ≅ᵀ-sub; ⟶-sub )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-ren )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; red→≅ᵀ
        ; church-rosserᵀ; Π-reduct; ΠRed; mkΠRed )
open import poc.OCP0009.NbEPDirDBSubj
  using ( sr; ⊢-cast; gen-lam; gen-var; gen-hrefl
        ; homred-inv; BaseAmb; ba-el; ba-base; baseamb-red
        ; ΣAmb; sa-el; sa-Σ; σamb-red
        ; HomRed; mkHomRed; Hom-to-Hom
        ; HomToΠ; via-U; via-Π; hom-to-Π
        ; U-reduct; mono-El[]; wk-cancel-tm; ⟶ᵀ*-ren; posc-red )

------------------------------------------------------------------------
-- The staged judgment: base typing, `⊢tr` (SpikeTr §0 spec), conversion.
------------------------------------------------------------------------

infix 3 _⊢ᵗ_∷_
data _⊢ᵗ_∷_ : (Γ : Ctx) → RTm ⌊ Γ ⌋ → RTy ⌊ Γ ⌋ → Set where
  ⊢lift  : ∀ {Γ t A} → Γ ⊢ t ∷ A → Γ ⊢ᵗ t ∷ A
  ⊢tr    : ∀ {Γ A d p e t u} →
           (Γ ▹ A) ⊢ d ∷ U → PosC vz d →
           Γ ⊢ p ∷ Hom A t u → Γ ⊢ e ∷ El (subTm (single t) d) →
           Γ ⊢ᵗ tr d p e ∷ El (subTm (single u) d)
  ⊢convᵗ : ∀ {Γ t A B} → Γ ⊢ᵗ t ∷ A → A ≅ᵀ B → Γ ⊢ᵗ t ∷ B

------------------------------------------------------------------------
-- ★ SUBJECT REDUCTION for the staged judgment.
------------------------------------------------------------------------

srᵗ : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
      Γ ⊢ᵗ t ∷ A → t ⟶ u → Γ ⊢ᵗ u ∷ A
srᵗ (⊢lift d)     r = ⊢lift (sr d r)
srᵗ (⊢convᵗ d c)  r = ⊢convᵗ (srᵗ d r) c
-- the J-equation at `⌜base⌝`: the canonical path pins both endpoints to
-- a common reduct, so the payload's type converts across.
srᵗ (⊢tr {A = A} {d = d₂} {t = t} {u = u} dd pc dp de) (tr-J-base _ s e₀)
  with gen-hrefl dp
... | (dc , (ds , cH)) with church-rosserᵀ cH
...   | W , (rL , rR) with homred-inv baseamb-red (λ ()) (λ ()) ba-el rR
...     | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
          with Hom-to-Hom (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...       | mkHomRed rA rt ru =
            ⊢lift (⊢conv de
              (ctrnᵀ (mono-El[] d₂ rt)
                (ctrnᵀ (csymᵀ (mono-El[] d₂ rs₁))
                  (ctrnᵀ (mono-El[] d₂ rs₂)
                    (csymᵀ (mono-El[] d₂ ru))))))
srᵗ (⊢tr {A = A} {d = d₂} {t = t} {u = u} dd pc dp de) (tr-J-Σ _ c₁ c₂ s e₀)
  with gen-hrefl dp
... | (dc , (ds , cH)) with church-rosserᵀ cH
...   | W , (rL , rR) with homred-inv σamb-red (λ ()) (λ ()) sa-el rR
...     | A₂ , (s₁ , (s₂ , (eqW , (rs₁ , rs₂))))
          with Hom-to-Hom (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...       | mkHomRed rA rt ru =
            ⊢lift (⊢conv de
              (ctrnᵀ (mono-El[] d₂ rt)
                (ctrnᵀ (csymᵀ (mono-El[] d₂ rs₁))
                  (ctrnᵀ (mono-El[] d₂ rs₂)
                    (csymᵀ (mono-El[] d₂ ru))))))
-- directed univalence computing: the path's `Hom` is convertible to a
-- `Π`; the tautological motive's typing refutes the `Hom-Π` unfold, so
-- it was `Hom-U`, giving exactly the conversions the application needs.
srᵗ (⊢tr {A = A} {t = t} {u = u} dd pc dp de) (tr-taut f e₀)
  with gen-lam dp
... | A₁ , (B₁ , (cΠ , (tyA₁ , d-f))) with church-rosserᵀ cΠ
...   | W , (rL , rR) with Π-reduct rR
...     | mkΠRed P₂ Q₂ eqW rP rQ
          with hom-to-Π (subst (Hom A t u ⟶ᵀ*_) eqW rL)
...       | via-Π rA with gen-var dd
...         | _ , (here , cU)
              with church-rosserᵀ (ctrnᵀ cU (red→≅ᵀ (⟶ᵀ*-ren vs rA)))
...           | W' , (rU , rΠ') with U-reduct rU
...             | refl with Π-reduct rΠ'
...               | mkΠRed _ _ () _ _
srᵗ (⊢tr {A = A} {t = t} {u = u} dd pc dp de) (tr-taut f e₀)
    | A₁ , (B₁ , (cΠ , (tyA₁ , d-f))) | W , (rL , rR)
    | mkΠRed P₂ Q₂ eqW rP rQ
    | via-U rA rt ru rEt rEu =
      ⊢lift
        (⊢-cast (cong El (wk-cancel-tm e₀ u))
          (⊢conv
            (⊢app (⊢lam tyA₁ d-f)
              (⊢conv de
                (ctrnᵀ (red→≅ᵀ (⟶ᵀ*-trans (⟶ᵀ*-El rt) rEt))
                       (csymᵀ (red→≅ᵀ rP)))))
            (≅ᵀ-sub (single e₀)
              (ctrnᵀ (red→≅ᵀ rQ)
                     (csymᵀ (red→≅ᵀ (⟶ᵀ*-trans (⟶ᵀ*-El (⟶*-ren vs ru)) rEu)))))))
-- congruences: `PosC` survives the motive's step; the payload's type
-- converts along the substituted step.
srᵗ (⊢tr {d = d₂} {t = t} {u = u} dd pc dp de) (ξ-trᵈ r) =
  ⊢convᵗ (⊢tr (sr dd r) (posc-red pc r) dp
              (⊢conv de (credᵀ (ξ-El (⟶-sub (single t) r)))))
         (csymᵀ (credᵀ (ξ-El (⟶-sub (single u) r))))
srᵗ (⊢tr dd pc dp de) (ξ-trᵖ r) = ⊢tr dd pc (sr dp r) de
srᵗ (⊢tr dd pc dp de) (ξ-trᵉ r) = ⊢tr dd pc dp (sr de r)

-- multi-step corollary.
srᵗ* : {Γ : Ctx} {t u : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
       Γ ⊢ᵗ t ∷ A → t ⟶* u → Γ ⊢ᵗ u ∷ A
srᵗ* d done       = d
srᵗ* d (step r p) = srᵗ* (srᵗ d r) p

------------------------------------------------------------------------
-- ★ DONE-WHEN DEMOS (HANDOFF §4.3 item 4b).
------------------------------------------------------------------------

private
  Γ₁ : Ctx
  Γ₁ = ◇ ▹ El ⌜base⌝

  x₁ : RTm (ε ∙)
  x₁ = var vz

  ⊢x₁ : Γ₁ ⊢ x₁ ∷ El ⌜base⌝
  ⊢x₁ = ⊢var here

  ⊢idpath : Γ₁ ⊢ hrefl ⌜base⌝ x₁ ∷ Hom (El ⌜base⌝) x₁ x₁
  ⊢idpath = ⊢hrefl ⊢⌜base⌝ ⊢x₁

  -- the composition motive: paths-from-`x₁`, `⌜Hom⌝ ⌜base⌝ (x₁ ↑) (var vz)`
  compM : RTm ((ε ∙) ∙)
  compM = ⌜Hom⌝ ⌜base⌝ (var (vs vz)) (var vz)

  ⊢compM : (Γ₁ ▹ El ⌜base⌝) ⊢ compM ∷ U
  ⊢compM = ⊢⌜Hom⌝ ⊢⌜base⌝ (⊢var (there here)) (⊢var here)

-- ★ `trans`, INTERNALLY: a path transported along a path, at the `⌜Hom⌝`
-- composition motive, with the `PosC` premise discharged by computation.
trans-tr : RTm (ε ∙)
trans-tr = tr compM (hrefl ⌜base⌝ x₁) (hrefl ⌜base⌝ x₁)

⊢trans-tr : Γ₁ ⊢ᵗ trans-tr ∷ El (subTm (single x₁) compM)
⊢trans-tr =
  ⊢tr ⊢compM (posc-Hom refl refl) ⊢idpath
      (⊢conv (⊢hrefl ⊢⌜base⌝ ⊢x₁)
             (csymᵀ (credᵀ (El-⌜Hom⌝ ⌜base⌝ x₁ x₁))))

-- ★ …and the J-EQUATION computes the composite along an identity path
-- back to the original path — with typing preserved (`srᵗ`).
trans-tr-J : trans-tr ⟶ hrefl ⌜base⌝ x₁
trans-tr-J = tr-J-base compM x₁ (hrefl ⌜base⌝ x₁)

⊢trans-tr-red : Γ₁ ⊢ᵗ hrefl ⌜base⌝ x₁ ∷ El (subTm (single x₁) compM)
⊢trans-tr-red = srᵗ ⊢trans-tr trans-tr-J

-- ★ DIRECTED UNIVALENCE COMPUTES A THIRD TIME: transport at the
-- tautological motive along a universe path is application — the taut
-- rule then β, two steps to the payload.
univ-tr : RTm (ε ∙)
univ-tr = tr (var vz) (lam (var vz)) (var vz)

⊢univ-tr : (◇ ▹ base) ⊢ᵗ univ-tr ∷ El (subTm (single ⌜base⌝) (var vz))
⊢univ-tr =
  ⊢tr (⊢var here) posc-var
      (⊢conv (⊢lam (ty-El ⊢⌜base⌝) (⊢var here))
             (csymᵀ (credᵀ (Hom-U ⌜base⌝ ⌜base⌝))))
      (⊢conv (⊢var here) (csymᵀ (credᵀ El-⌜base⌝)))

univ-tr-taut : univ-tr ⟶ app (lam (var vz)) (var (vz {ε}))
univ-tr-taut = tr-taut (var vz) (var vz)

univ-tr-β : app (lam (var vz)) (var (vz {ε})) ⟶ var vz
univ-tr-β = β (var vz) (var vz)

-- ★ the internal `no-sym` regression, syntactic half: `sym`'s motive
-- CODE fails the `PosC` premise, so no `⊢tr` can even be STATED at it
-- (`SpikeNoSym` holds the semantic half: `sym` is FALSE at `U`).
no-sym-tr : PosC vz sym-code → (∀ {P : Set} → P)
no-sym-tr = sym-code-not-posc
