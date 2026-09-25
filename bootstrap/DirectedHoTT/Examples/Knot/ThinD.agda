------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★ `Thin`, OBJECT-LEVEL: the thinning as DATA.
--
-- ★ WHY IT EXISTS.  A-math's `IConWf I Θ ρ x C` carries a thinning
--   `ρ : Thin Δ ⌊ Θ ⌋` — the constructor's own scope embedded into its
--   telescope, skipping the abstract family.  The Knot reifies `IConWf`
--   1:1, so `ρ` needs an object-level representation, and a thinning is
--   FIRST-ORDER: `done`, `keep`, `drop`.  (A `SubTy` λ-term could not be
--   a κ field at all — `ICodeWf` admits no `⌜Π⌝` code.)
--
-- ★ A STRATUM, LIKE `CtxD`.  `Thin` depends on scopes only — no syntax —
--   so it is its own family and not a knot sort.  Its index is the PAIR
--   (source depth , target depth), and every row Fords both components:
--
--       done :                    Thin (0 , 0)
--       keep : Thin (m , n)  →    Thin (suc m , suc n)
--       drop : Thin (m , n)  →    Thin (m , suc n)
--
-- ★ AND ITS ACTION IS THE KNOT'S EXISTING RENAMING.  `thinRenK` (in
--   `Knot/ThinRen`) folds a thinning to a `RenTy`, and `renTmAtK` applies
--   it — the kernel's `renTm (thinR θ)`, one to one.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.ThinD where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Lib.Lkp using ( ∋lkp; vsⁿ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; Nat; IMu
        ; var; pair; fst; snd; unit; nzero; nsuc; ⌜Nat⌝; ⌜Id⌝; idrefl; icon
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_; hereID; thereID; isingle; iext
        ; Thin; done; keep; drop )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_
        ; ⊢var; here; there; ⊢fst; ⊢snd; ⊢nzero; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢icon; ⊢unit
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ; icw-clo; icw-ford
        ; IDescWf; idwf-nil; idwf-cons; _,,_; Θ₀; ρ₀; x₀ )
open import DirectedHoTT.Metatheory.TySub using ( xenv₀; xenv-κ; xenv-ρ )
open import DirectedHoTT.Lib.IPay using ( ⊢payκ; ⊢payρ; icwTailκ; icwTailρ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; toI; fromI; ⊢ixP; num; ⊢num )
open import DirectedHoTT.Examples.Knot.Terms using ( fordFst; fordSnd )

------------------------------------------------------------------------
-- 1. THE DESCRIPTION.
------------------------------------------------------------------------

-- done : both components are zero
cThin-done : ICon (ε ∙)
cThin-done =
  iκ (⌜Id⌝ ⌜Nat⌝ (fst (var vz)) nzero)
   (iκ (⌜Id⌝ ⌜Nat⌝ (snd (var (vs vz))) nzero)
    iι)

-- keep : m n , a thinning at (m , n) , fst ≡ suc m , snd ≡ suc n
cThin-keep : ICon (ε ∙)
cThin-keep =
  iκ ⌜Nat⌝
   (iκ ⌜Nat⌝
    (iρ (pair (var (vs vz)) (var vz))
     (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs (vs vz))))) (nsuc (var (vs (vs vz)))))
      (iκ (⌜Id⌝ ⌜Nat⌝ (snd (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs vz)))))
       iι))))

-- drop : m n , a thinning at (m , n) , fst ≡ m , snd ≡ suc n
cThin-drop : ICon (ε ∙)
cThin-drop =
  iκ ⌜Nat⌝
   (iκ ⌜Nat⌝
    (iρ (pair (var (vs vz)) (var vz))
     (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs (vs vz))))) (var (vs (vs vz))))
      (iκ (⌜Id⌝ ⌜Nat⌝ (snd (var (vs (vs (vs (vs vz)))))) (nsuc (var (vs (vs vz)))))
       iι))))

ThinD : IDesc
ThinD = cThin-done ◂ (cThin-keep ◂ (cThin-drop ◂ inil))

ThinK : {Γ : Cx} → RTm Γ → RTy Γ
ThinK i = IMu ThinD IPair i

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS (A-math: the root telescope binds the family, then
--    the index; nothing here reads a recursive field, so the family's
--    abstractness costs nothing).
------------------------------------------------------------------------

cThin-doneWf : IConWf IPair (Θ₀ IPair) ρ₀ x₀ cThin-done
cThin-doneWf =
  iwf-κ (⌜Id⌝ ⌜Nat⌝ (fst (var vz)) nzero) (icw-ford _ _ _)
        (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var here))) (toI ⊢nzero))
   (iwf-κ (⌜Id⌝ ⌜Nat⌝ (snd (var (vs vz))) nzero) (icw-ford _ _ _)
          (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢snd (⊢var (there here)))) (toI ⊢nzero))
    iwf-ι)

-- ⚠ keep and drop differ ONLY in the first Ford's right-hand side.
cThin-keepWf : IConWf IPair (Θ₀ IPair) ρ₀ x₀ cThin-keep
cThin-keepWf =
  iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
   (iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
    (iwf-ρ (pair (var (vs vz)) (var vz))
           (⊢ixP (fromI (⊢var (there here))) (fromI (⊢var here)))
     (iwf-κ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs (vs vz))))) (nsuc (var (vs (vs vz))))) (icw-ford _ _ _)
            (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 3 vz))))) (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 2 vz)))))))
      (iwf-κ (⌜Id⌝ ⌜Nat⌝ (snd (var (vs (vs (vs (vs vz))))))
                         (nsuc (var (vs (vs vz)))))
             (icw-ford _ _ _)
             (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢snd (⊢var (∋lkp _ (vsⁿ 4 vz)))))
                           (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 2 vz)))))))
       iwf-ι))))

cThin-dropWf : IConWf IPair (Θ₀ IPair) ρ₀ x₀ cThin-drop
cThin-dropWf =
  iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
   (iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
    (iwf-ρ (pair (var (vs vz)) (var vz))
           (⊢ixP (fromI (⊢var (there here))) (fromI (⊢var here)))
     (iwf-κ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs (vs vz))))) (var (vs (vs vz)))) (icw-ford _ _ _)
            (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 3 vz))))) (⊢var (∋lkp _ (vsⁿ 2 vz))))
      (iwf-κ (⌜Id⌝ ⌜Nat⌝ (snd (var (vs (vs (vs (vs vz))))))
                         (nsuc (var (vs (vs vz)))))
             (icw-ford _ _ _)
             (⊢⌜Id⌝ ⊢⌜Nat⌝ (toI (⊢snd (⊢var (∋lkp _ (vsⁿ 4 vz)))))
                           (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 2 vz)))))))
       iwf-ι))))

ThinWf : IDescWf IPair ThinD
ThinWf = ⊢IPair ,, idwf-cons cThin-doneWf (idwf-cons cThin-keepWf (idwf-cons cThin-dropWf idwf-nil))

------------------------------------------------------------------------
-- 3. SMART CONSTRUCTORS — each payload is a chain of `⊢payκ`/`⊢payρ`,
--    so no field needs a substitution lemma: the Fords compute to
--    `⌜Id⌝ ⌜Nat⌝ (fst (pair …)) …` and `fordFst`/`fordSnd` take the one
--    `βfst`/`βsnd` step.
------------------------------------------------------------------------

Thin-doneK : {Γ : Cx} → RTm Γ
Thin-doneK = icon zero (pair (idrefl ⌜Nat⌝ nzero) (pair (idrefl ⌜Nat⌝ nzero) unit))

⊢Thin-doneK : {Γ : Ctx} → Γ ⊢ Thin-doneK ∷ ThinK (pair nzero nzero)
⊢Thin-doneK =
  ⊢icon ThinWf hereID ip
    (⊢payκ ThinD IPair (isingle (pair nzero nzero)) _ _ ThinWf cThin-doneWf e₀
           (fordFst ⊢nzero)
      (⊢payκ ThinD IPair _ _ _ ThinWf (icwTailκ cThin-doneWf)
             (xenv-κ e₀ _ (fordFst ⊢nzero))
             (fordSnd ⊢nzero)
        ⊢unit))
  where
    ip = ⊢ixP ⊢nzero ⊢nzero
    e₀ = xenv₀ ThinWf ip

Thin-keepK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
Thin-keepK m n θ =
  icon (suc zero)
    (pair m (pair n (pair θ (pair (idrefl ⌜Nat⌝ (nsuc m))
                                  (pair (idrefl ⌜Nat⌝ (nsuc n)) unit)))))

⊢Thin-keepK : {Γ : Ctx} {m n θ : RTm ⌊ Γ ⌋} →
              Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ θ ∷ ThinK (pair m n) →
              Γ ⊢ Thin-keepK m n θ ∷ ThinK (pair (nsuc m) (nsuc n))
⊢Thin-keepK {m = m} {n = n} dm dn dθ =
  ⊢icon ThinWf (thereID hereID) ip
    (⊢payκ ThinD IPair _ _ _ ThinWf cThin-keepWf e₀ (toI dm)
     (⊢payκ ThinD IPair _ _ _ ThinWf w₁ e₁ (toI dn)
      (⊢payρ ThinD IPair _ _ _ ThinWf w₂ e₂ dθ
       (⊢payκ ThinD IPair _ _ _ ThinWf w₃ e₃ (fordFst (⊢nsuc dm))
        (⊢payκ ThinD IPair _ _ _ ThinWf w₄ e₄ (fordSnd (⊢nsuc dn))
         ⊢unit)))))
  where
    ip = ⊢ixP (⊢nsuc dm) (⊢nsuc dn)
    e₀ = xenv₀ ThinWf ip
    w₁ = icwTailκ cThin-keepWf
    w₂ = icwTailκ w₁
    w₃ = icwTailρ w₂
    w₄ = icwTailκ w₃
    e₁ = xenv-κ e₀ ⌜Nat⌝ (toI dm)
    e₂ = xenv-κ e₁ ⌜Nat⌝ (toI dn)
    e₃ = xenv-ρ e₂ (pair (var (vs vz)) (var vz)) dθ
    e₄ = xenv-κ e₃ _ (fordFst (⊢nsuc dm))

Thin-dropK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
Thin-dropK m n θ =
  icon (suc (suc zero))
    (pair m (pair n (pair θ (pair (idrefl ⌜Nat⌝ m)
                                  (pair (idrefl ⌜Nat⌝ (nsuc n)) unit)))))

⊢Thin-dropK : {Γ : Ctx} {m n θ : RTm ⌊ Γ ⌋} →
              Γ ⊢ m ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ θ ∷ ThinK (pair m n) →
              Γ ⊢ Thin-dropK m n θ ∷ ThinK (pair m (nsuc n))
⊢Thin-dropK {m = m} {n = n} dm dn dθ =
  ⊢icon ThinWf (thereID (thereID hereID)) ip
    (⊢payκ ThinD IPair _ _ _ ThinWf cThin-dropWf e₀ (toI dm)
     (⊢payκ ThinD IPair _ _ _ ThinWf w₁ e₁ (toI dn)
      (⊢payρ ThinD IPair _ _ _ ThinWf w₂ e₂ dθ
       (⊢payκ ThinD IPair _ _ _ ThinWf w₃ e₃ (fordFst dm)
        (⊢payκ ThinD IPair _ _ _ ThinWf w₄ e₄ (fordSnd (⊢nsuc dn))
         ⊢unit)))))
  where
    ip = ⊢ixP dm (⊢nsuc dn)
    e₀ = xenv₀ ThinWf ip
    w₁ = icwTailκ cThin-dropWf
    w₂ = icwTailκ w₁
    w₃ = icwTailρ w₂
    w₄ = icwTailκ w₃
    e₁ = xenv-κ e₀ ⌜Nat⌝ (toI dm)
    e₂ = xenv-κ e₁ ⌜Nat⌝ (toI dn)
    e₃ = xenv-ρ e₂ (pair (var (vs vz)) (var vz)) dθ
    e₄ = xenv-κ e₃ _ (fordFst dm)
