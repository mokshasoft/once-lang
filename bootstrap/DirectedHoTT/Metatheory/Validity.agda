------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ SUBJECT REDUCTION FOR TYPES, and VALIDITY.
--                      (PLAN-BIDI, route C to S4 — step 1)
--
-- ★ WHY.  Route C normalises TYPES because they are well-formed, and the
--   bidirectional checker needs the same facts: `infer` must return a
--   well-formed type (slice 1 re-checked every inferred domain because
--   this lemma did not exist), and completeness needs inversion.
--
-- ⚠⚠ VALIDITY IS "UP TO CONVERSION", AND THAT IS NOT A WEAKENING OF CHOICE.
--   `⊢conv : Γ ⊢ t ∷ A → A ≅ᵀ B → Γ ⊢ t ∷ B` has NO `Γ ⊢ty B` premise (the
--   logical relation is closed under conversion, so the kernel never needed
--   one — `Fundamental`, the `⊢conv` case).  Conversion runs BOTH ways, so a
--   term of type `base` also has type `El (fst (pair ⌜base⌝ junk))` for an
--   ill-typed `junk`: the plain statement "every derived type is
--   well-formed" is FALSE here.  What IS true, and all any consumer needs:
--       validity : ⊢ctx Γ → Γ ⊢ t ∷ A → A is CONVERTIBLE to a well-formed type
--   Adding the premise to `⊢conv` (the Abel–Öhman–Vezzosi presentation)
--   would buy the strong form at the cost of every `⊢conv` in Lib and the
--   Knot — a separate kernel decision, not taken here.
--
-- ★ `srᵀ` needs nothing new: term SR (`sr`) at `El`/`Hom`/`Id`/`IMu`
--   leaves, the code inversions (`gen-⌜Π⌝` …) at decode steps, and
--   weakening at `Hom-U`/`Hom-Π`.  Type formation has no conversion rule,
--   so inverting `⊢ty` is plain pattern matching.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Validity where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst; Σ; _,_; _×_ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( sr; gen-⌜Π⌝; gen-⌜Σ⌝; gen-⌜Hom⌝; gen-⌜Id⌝; gen-⌜IMu⌝; gen-nsuc
        ; ren-ty; sub-ty; sub-lemma; ⊢wk; ⊢single; ⊢[]; ⊢-cast; Sub⊢
        ; wk-cancel; wk-cancel-tm; ⟶ᵀ*-sub'; iinst-wf; conv-ctxᵀ
        ; dσ-step; dρ-step )
open import DirectedHoTT.Metatheory.SubjectReductionBase using ( ≅ᵀ-sub )
open import DirectedHoTT.Metatheory.TySub using ( ≅ᵀ-ren )
open import DirectedHoTT.Metatheory.RedCong
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; red→≅ᵀ; ⟶-ren )
open import DirectedHoTT.Metatheory.Injectivity
  using ( church-rosserᵀ; Π-reduct; Σ-reduct; ΠRed; ΣRed; mkΠRed; mkΣRed )

private
  variable
    Γ : Ctx

------------------------------------------------------------------------
-- 0. Small pieces.
------------------------------------------------------------------------

-- (`conv-ctxᵀ`, the `⊢ty` twin of `conv-ctx`, lives in `TySub`.)

-- applying a weakened term to the fresh variable undoes the weakening in
-- the codomain: `B[vz/vz]` after `extR vs`.
wk-app-vz : {Γ : Cx} (B : RTy (Γ ∙)) → subTy (single (var vz)) (renTy (extR vs) B) ≡ B
wk-app-vz B = trans (subTy-renTy B) (trans (subTy-cong h B) (subTy-id B))
  where
  h : ∀ x → single (var vz) (extR vs x) ≡ idₛ x
  h vz     = refl
  h (vs x) = refl

------------------------------------------------------------------------
-- 1. ★ SUBJECT REDUCTION FOR TYPES.
------------------------------------------------------------------------

srᵀ : {A B : RTy ⌊ Γ ⌋} → Γ ⊢ty A → A ⟶ᵀ B → Γ ⊢ty B
-- decode steps: invert the code
srᵀ (ty-El dc) El-⌜base⌝ = ty-base
srᵀ (ty-El dc) (El-⌜Π⌝ c d) with gen-⌜Π⌝ dc
... | dc' , (dd' , _) = ty-Π (ty-El dc') (ty-El dd')
srᵀ (ty-El dc) (El-⌜Σ⌝ c d) with gen-⌜Σ⌝ dc
... | dc' , (dd' , _) = ty-Σ (ty-El dc') (ty-El dd')
srᵀ (ty-El dc) (El-⌜Hom⌝ c a b) with gen-⌜Hom⌝ dc
... | dc' , (da , (db , _)) = ty-Hom (ty-El dc') da db
srᵀ (ty-El dc) (El-⌜Id⌝ c a b) with gen-⌜Id⌝ dc
... | dc' , (da , (db , _)) = ty-Id (ty-El dc') da db
srᵀ (ty-El dc) El-⌜Nat⌝  = ty-Nat
srᵀ (ty-El dc) El-⌜Unit⌝ = ty-Unit
srᵀ (ty-El dc) El-⌜IMu⌝ with gen-⌜IMu⌝ dc
... | dI , (dD , (di , _)) = ty-IMu dI dD di
srᵀ (ty-El dc) El-⌜Fin⌝ = ty-Fin
srᵀ (ty-El dc) (ξ-El r) = ty-El (sr dc r)
-- congruences
srᵀ (ty-Π dA dB) (ξ-Πˡ r) = ty-Π (srᵀ dA r) (conv-ctxᵀ (credᵀ r) dB)
srᵀ (ty-Π dA dB) (ξ-Πʳ r) = ty-Π dA (srᵀ dB r)
srᵀ (ty-Σ dA dB) (ξ-Σˡ r) = ty-Σ (srᵀ dA r) (conv-ctxᵀ (credᵀ r) dB)
srᵀ (ty-Σ dA dB) (ξ-Σʳ r) = ty-Σ dA (srᵀ dB r)
-- the computing order at `Nat`
srᵀ (ty-Hom dA dt du) (Hom-Nat-z n)  = ty-Unit
srᵀ (ty-Hom dA dt du) (Hom-Nat-sz m) = ty-base
srᵀ (ty-Hom dA dt du) (Hom-Nat-ss m n) with gen-nsuc dt | gen-nsuc du
... | dm , _ | dn , _ = ty-Hom ty-Nat dm dn
-- directed univalence at `U`
srᵀ (ty-Hom dA dt du) (Hom-U c d) = ty-Π (ty-El dt) (ty-El (⊢wk du))
-- ★ the pointwise family at `Π` — the one rule that CREATES terms
srᵀ (ty-Hom (ty-Π dA dB) df dg) (Hom-Π A B f g) =
  ty-Π dA (ty-Hom dB (appvz df) (appvz dg))
  where
  appvz : {h : RTm ⌊ _ ⌋} → _ ⊢ h ∷ Π A B → (_ ▹ A) ⊢ app (renTm vs h) (var vz) ∷ B
  appvz dh = ⊢-cast (wk-app-vz B) (⊢app (⊢wk dh) (⊢var here))
srᵀ (ty-Hom dA dt du) (ξ-Homᵀ r) =
  ty-Hom (srᵀ dA r) (⊢conv dt (credᵀ r)) (⊢conv du (credᵀ r))
srᵀ (ty-Hom dA dt du) (ξ-Homˡ r) = ty-Hom dA (sr dt r) du
srᵀ (ty-Hom dA dt du) (ξ-Homʳ r) = ty-Hom dA dt (sr du r)
srᵀ (ty-Id dA dt du) (ξ-Idᵀ r) =
  ty-Id (srᵀ dA r) (⊢conv dt (credᵀ r)) (⊢conv du (credᵀ r))
srᵀ (ty-Id dA dt du) (ξ-Idˡ r) = ty-Id dA (sr dt r) du
srᵀ (ty-Id dA dt du) (ξ-Idʳ r) = ty-Id dA dt (sr du r)
-- ★★ the levitated families: the hypotheses' type computes on the
--   telescope (the payload steps are `sr`'s), the slots step under
--   conversion.
srᵀ (ty-DIh dI dD dM dC di dp) (DIh-ι D M j p) = ty-Unit
srᵀ (ty-DIh dI dD dM dC di dp) (DIh-σ D M S f p) with dσ-step dC dp
... | dC' , dsnd = ty-DIh dI dD dM dC' di dsnd
srᵀ (ty-DIh dI dD dM dC di dp) (DIh-ρ D M j C p) with dρ-step dC dp
... | dj , (dC' , (dfst , dsnd)) =
      ty-Σ (iinst-wf M j (fst p) dj dfst dM) (ren-ty (ty-DIh dI dD dM dC' di dsnd) there)
srᵀ (ty-IMu dI dD di) (ξ-IMuᴵ r) =
  ty-IMu (sr dI r) (⊢conv dD (credᵀ (ξ-Desc r))) (⊢conv di (credᵀ (ξ-El r)))
srᵀ (ty-IMu dI dD di) (ξ-IMuᴰ r) = ty-IMu dI (sr dD r) di
srᵀ (ty-IMu dI dD di) (ξ-IMuⁱ r) = ty-IMu dI dD (sr di r)
srᵀ (ty-Desc dI) (ξ-Desc r) = ty-Desc (sr dI r)
srᵀ (ty-DIh dI dD dM dC di dp) (ξ-DIhᴰ r) =
  ty-DIh dI (sr dD r) (conv-ctxᵀ (credᵀ (ξ-IMuᴰ (⟶-ren vs r))) dM) dC di
         (⊢conv dp (credᵀ (ξ-El (ξ-dpayᴰ r))))
srᵀ (ty-DIh dI dD dM dC di dp) (ξ-DIhᴹ r) = ty-DIh dI dD (srᵀ dM r) dC di dp
srᵀ (ty-DIh dI dD dM dC di dp) (ξ-DIhᶜ r) =
  ty-DIh dI dD dM (sr dC r) di (⊢conv dp (credᵀ (ξ-El (ξ-dpayᶜ r))))
srᵀ (ty-DIh dI dD dM dC di dp) (ξ-DIhᵖ r) = ty-DIh dI dD dM dC di (sr dp r)

srᵀ* : {A B : RTy ⌊ Γ ⌋} → Γ ⊢ty A → A ⟶ᵀ* B → Γ ⊢ty B
srᵀ* d doneᵀ       = d
srᵀ* d (stepᵀ r p) = srᵀ* (srᵀ d r) p

------------------------------------------------------------------------
-- 2. ★ VALIDITY, up to conversion.
------------------------------------------------------------------------

-- "`A` is convertible to a well-formed type"
record WfUpTo (Γ : Ctx) (A : RTy ⌊ Γ ⌋) : Set where
  constructor wf
  field
    ty  : RTy ⌊ Γ ⌋
    cnv : A ≅ᵀ ty
    wft : Γ ⊢ty ty

exact : {A : RTy ⌊ Γ ⌋} → Γ ⊢ty A → WfUpTo Γ A
exact d = wf _ crflᵀ d

-- a variable's type is well-formed on the nose, in a well-formed context
lookup-wf : {x : Var ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → ⊢ctx Γ → Γ ∋ x ∷ A → Γ ⊢ty A
lookup-wf (c-▹ wΓ dA) here     = ren-ty dA there
lookup-wf (c-▹ wΓ dB) (there v) = ren-ty (lookup-wf wΓ v) there

-- ★ a type convertible to a well-formed type that is a Π: recover a
--   well-formed Π it REDUCES to, and the conversions of the pieces.
record ΠWf (Γ : Ctx) (A : RTy ⌊ Γ ⌋) (B : RTy (⌊ Γ ⌋ ∙)) : Set where
  constructor πwf
  field
    A'' : RTy ⌊ Γ ⌋
    B'' : RTy (⌊ Γ ⌋ ∙)
    rA  : A ⟶ᵀ* A''
    rB  : B ⟶ᵀ* B''
    dA  : Γ ⊢ty A''
    dB  : (Γ ▹ A'') ⊢ty B''

toΠWf : {A : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} → WfUpTo Γ (Π A B) → ΠWf Γ A B
toΠWf (wf T c dT) with church-rosserᵀ c
... | W , (ΠW , TW) with Π-reduct ΠW | srᵀ* dT TW
...   | mkΠRed A'' B'' refl rA rB | ty-Π dA dB = πwf A'' B'' rA rB dA dB

record ΣWf (Γ : Ctx) (A : RTy ⌊ Γ ⌋) (B : RTy (⌊ Γ ⌋ ∙)) : Set where
  constructor σwf
  field
    A'' : RTy ⌊ Γ ⌋
    B'' : RTy (⌊ Γ ⌋ ∙)
    rA  : A ⟶ᵀ* A''
    rB  : B ⟶ᵀ* B''
    dA  : Γ ⊢ty A''
    dB  : (Γ ▹ A'') ⊢ty B''

toΣWf : {A : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} → WfUpTo Γ (Σ' A B) → ΣWf Γ A B
toΣWf (wf T c dT) with church-rosserᵀ c
... | W , (ΣW , TW) with Σ-reduct ΣW | srᵀ* dT TW
...   | mkΣRed A'' B'' refl rA rB | ty-Σ dA dB = σwf A'' B'' rA rB dA dB

-- conversion is a congruence under `Π`/`Σ` in each argument
≅ᵀ-Πʳ : {A : RTy ⌊ Γ ⌋} {B B' : RTy (⌊ Γ ⌋ ∙)} → B ≅ᵀ B' → Π A B ≅ᵀ Π A B'
≅ᵀ-Πʳ (credᵀ r)   = credᵀ (ξ-Πʳ r)
≅ᵀ-Πʳ crflᵀ       = crflᵀ
≅ᵀ-Πʳ (csymᵀ c)   = csymᵀ (≅ᵀ-Πʳ c)
≅ᵀ-Πʳ (ctrnᵀ c d) = ctrnᵀ (≅ᵀ-Πʳ c) (≅ᵀ-Πʳ d)

≅ᵀ-Σˡ : {A A' : RTy ⌊ Γ ⌋} {B : RTy (⌊ Γ ⌋ ∙)} → A ≅ᵀ A' → Σ' A B ≅ᵀ Σ' A' B
≅ᵀ-Σˡ (credᵀ r)   = credᵀ (ξ-Σˡ r)
≅ᵀ-Σˡ crflᵀ       = crflᵀ
≅ᵀ-Σˡ (csymᵀ c)   = csymᵀ (≅ᵀ-Σˡ c)
≅ᵀ-Σˡ (ctrnᵀ c d) = ctrnᵀ (≅ᵀ-Σˡ c) (≅ᵀ-Σˡ d)

validity : {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → ⊢ctx Γ → Γ ⊢ t ∷ A → WfUpTo Γ A
validity wΓ (⊢var v) = exact (lookup-wf wΓ v)
validity wΓ (⊢lam dA d) with validity (c-▹ wΓ dA) d
... | wf B' c dB' = wf (Π _ B') (≅ᵀ-Πʳ c) (ty-Π dA dB')
validity wΓ (⊢app {u = u} d₁ d₂) with toΠWf (validity wΓ d₁)
... | πwf A'' B'' rA rB dA dB =
      wf (subTy (single u) B'') (red→≅ᵀ (⟶ᵀ*-sub' (single u) rB))
         (sub-ty dB (⊢single (⊢conv d₂ (red→≅ᵀ rA))))
validity wΓ (⊢pair dB da db) with validity wΓ da
... | wf A' c dA' = wf (Σ' A' _) (≅ᵀ-Σˡ c) (ty-Σ dA' (conv-ctxᵀ c dB))
validity wΓ (⊢absurd dc de) = exact (ty-El dc)
validity wΓ (⊢ordtr da dt du dp dq) = exact (ty-Hom ty-Nat da du)
validity wΓ (⊢fst d) with toΣWf (validity wΓ d)
... | σwf A'' B'' rA rB dA dB = wf A'' (red→≅ᵀ rA) dA
validity wΓ (⊢snd {p = p} d) with toΣWf (validity wΓ d)
... | σwf A'' B'' rA rB dA dB =
      wf (subTy (single (fst p)) B'') (red→≅ᵀ (⟶ᵀ*-sub' (single (fst p)) rB))
         (sub-ty dB (⊢single (⊢conv (⊢fst d) (red→≅ᵀ rA))))
validity wΓ ⊢⌜base⌝ = exact ty-U
validity wΓ (⊢⌜Π⌝ dc dd) = exact ty-U
validity wΓ (⊢⌜Σ⌝ dc dd) = exact ty-U
validity wΓ (⊢⌜Hom⌝ dc da db) = exact ty-U
validity wΓ (⊢hrefl dc dt) = exact (ty-Hom (ty-El dc) dt dt)
validity wΓ (⊢trU dt du dp de) = exact (ty-El du)
validity wΓ (⊢tr dc da dvz nn o₁ o₂ dt du dp de) =
  exact (ty-El (sub-lemma (⊢⌜Hom⌝ dc da dvz) (⊢single du)))
validity wΓ (⊢ap {cB = cB} {b = b} {t = t} {u = u} dcA fl dcB db dt du dp) =
  exact (ty-Hom (ty-El dcB) (at dt) (at du))
  where
  at : {s : RTm ⌊ _ ⌋} → _ ⊢ s ∷ El _ → _ ⊢ subTm (single s) b ∷ El cB
  at {s} ds = ⊢-cast (cong El (wk-cancel-tm s cB)) (⊢[] db ds)
validity wΓ (⊢⌜Id⌝ dc da db) = exact ty-U
validity wΓ ⊢⌜Nat⌝ = exact ty-U
validity wΓ (⊢⌜IMu⌝ dI dD di) = exact ty-U
validity wΓ ⊢⌜Fin⌝ = exact ty-U
validity wΓ ⊢⌜Unit⌝ = exact ty-U
validity wΓ (⊢idrefl dc dt) = exact (ty-Id (ty-El dc) dt dt)
validity wΓ (⊢jsub dd dt du dp de) = exact (ty-El (⊢[] dd du))
validity wΓ ⊢unit = exact ty-Unit
validity wΓ ⊢nzero = exact ty-Nat
validity wΓ (⊢nsuc dn) = exact ty-Nat
validity wΓ (⊢natrec dM dz ds dn) = exact (sub-ty dM (⊢single dn))
-- ★★ the levitated families: every telescope former types its index code
validity wΓ (⊢dι dI dj) = exact (ty-Desc dI)
validity wΓ (⊢dσ dI dS df) = exact (ty-Desc dI)
validity wΓ (⊢dρ dI dj dC) = exact (ty-Desc dI)
validity wΓ (⊢dpay dI dD dC di) = exact ty-U
validity wΓ (⊢con dI dD di dp) = exact (ty-IMu dI dD di)
validity wΓ (⊢dih dI dD dM de dC di dp) = exact (ty-DIh dI dD dM dC di dp)
validity wΓ (⊢ielim {M = M} {i = i} {t = t} dI dD dM de di dt) = exact (iinst-wf M i t di dt dM)
validity wΓ ⊢fzero = exact ty-Fin
validity wΓ (⊢fsuc dt) = exact ty-Fin
validity wΓ (⊢fcase dP dt da db) = exact (sub-ty dP (⊢single dt))
validity wΓ (⊢fcase0 dP dt) = exact (sub-ty dP (⊢single dt))
validity wΓ (⊢psplit dA dB dP dq db) = exact (sub-ty dP (⊢single dq))
validity wΓ (⊢conv d c) with validity wΓ d
... | wf A' c' dA' = wf A' (ctrnᵀ (csymᵀ c) c') dA'
