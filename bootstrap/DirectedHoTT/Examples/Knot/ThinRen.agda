------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★ A THINNING'S ACTION: `thinR`, OBJECT-LEVEL.
--
-- The kernel reads a thinning through `thinR : Thin Γ Δ → Ren Γ Δ` and
-- applies it with `renTm`.  The object level already HAS renamings as
-- values (`Knot/RenMot.RenTy`, applied by `Knot/RenTm.renTmAtK`), so the
-- one missing piece is this fold, clause for clause the kernel's:
--
--     thinR (keep θ) = extR (thinR θ)        ↦  `extRNK m n (thinRenK θ)`
--     thinR (drop θ) = vs ∘ thinR θ          ↦  `Var-vsK n (app (…) v)`
--     done           = the empty renaming    ↦  the variable, transported
--
-- ⚠ EVERY METHOD TRANSPORTS ALONG ITS FORDS.  The index is a PAIR and a
--   row's target is only PROPOSITIONALLY `(suc m , suc n)`, so the answer
--   built at `(suc m , suc n)` is moved to `(fst i , snd i)` by `kTr` —
--   `Knot/ConS`'s `jsub` idiom, named once.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.ThinRen where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Lib.Lkp using ( ∋lkp; vsⁿ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; Nat; IMu; Π; Σ'
        ; var; lam; app; pair; fst; snd; unit; nzero; nsuc; ⌜IMu⌝; jsub; ielim
        ; iι; iρ; iκ; inil; _◂_; renTm; subTm; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; single
        ; ⊢var; here; there; ⊢lam; ⊢app; ⊢fst; ⊢snd; ⊢nzero; ⊢nsuc; ⊢unit
        ; ⊢jsub; ⊢⌜IMu⌝; ⊢ielim; ⊢conv; βfst; βsnd; done; step; wk-single
        ; idwf-nil; idwf-cons; ty-IMu; imethTy; imethsTy )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; ⊢wk )
open import DirectedHoTT.Metatheory.RedCong
  using ( red→≅ᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-Πˡ; ⟶ᵀ*-Πʳ; ⟶ᵀ*-IMu; ⟶*-pairʳ )
open import DirectedHoTT.Lib.Wk using ( w; sub-w-single )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢methsCons; spl-nil; spl-cons )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair; sVar; ⊢sVar; sTm; ⊢sTm; ⊢ixP )
open import DirectedHoTT.Examples.Knot.RenTm using ( renTmAtK; ⊢renTmAtK )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vsK; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.RenMot using ( RenTy; ty-RenTy; extRNK; ⊢extRNK )
open import DirectedHoTT.Examples.Knot.ThinD
  using ( ThinD; ThinK; ThinWf; cThin-done; cThin-keep; cThin-drop
        ; cThin-doneWf; cThin-keepWf; cThin-dropWf )

------------------------------------------------------------------------
-- 1. A VARIABLE, MOVED ALONG A DEPTH EQUATION.
------------------------------------------------------------------------

kTr : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
kTr p v = jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz))) p v

⊢kTr : {Γ : Ctx} {a b p v : RTm ⌊ Γ ⌋} →
       Γ ⊢ a ∷ Nat → Γ ⊢ b ∷ Nat → Γ ⊢ p ∷ IdN a b →
       Γ ⊢ v ∷ K (pair sVar a) → Γ ⊢ kTr p v ∷ K (pair sVar b)
⊢kTr da db dp dv =
  fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                (natAsEl da) (natAsEl db) dp (toMu dv))

-- a renaming typed at a `pair`'s projections, at the pair's components
renTyβ : {Γ : Ctx} {a b r : RTm ⌊ Γ ⌋} →
         Γ ⊢ r ∷ RenTy (fst (pair a b)) (snd (pair a b)) → Γ ⊢ r ∷ RenTy a b
renTyβ {a = a} {b = b} d =
  ⊢conv d (red→≅ᵀ (⟶ᵀ*-trans
    (⟶ᵀ*-Πˡ (⟶ᵀ*-IMu (⟶*-pairʳ (step (βfst a b) done))))
    (⟶ᵀ*-Πʳ (⟶ᵀ*-IMu (⟶*-pairʳ (step (βsnd (renTm vs a) (renTm vs b)) done))))))

------------------------------------------------------------------------
-- 2. THE MOTIVE AND THE THREE METHODS.
--
-- In a method body (`⊢methLam`, then one more `lam` for the variable):
--   v = var vz · ih = var (vs vz) · p = var (vs² vz) · i = var (vs³ vz)
------------------------------------------------------------------------

thinMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
thinMotK = RenTy (fst (var (vs vz))) (snd (var (vs vz)))

⊢thinMotK : {Γ : Ctx} →
            ((Γ ▹ εwkTy IPair) ▹ IMu ThinD IPair (var vz)) ⊢ty thinMotK
⊢thinMotK = ty-RenTy (⊢fst (⊢var (there here))) (⊢snd (⊢var (there here)))

private
  -- the four names every body uses
  I₄ P₄ H₄ : {Γ : Cx} → RTm ((((Γ ∙) ∙) ∙) ∙)
  I₄ = var (vs (vs (vs vz)))
  P₄ = var (vs (vs vz))
  H₄ = var (vs vz)

thinDone : {Γ : Cx} → RTm Γ
thinDone = lam (lam (lam (lam
  (kTr (symN (snd I₄) (fst (snd P₄))) (kTr (fst P₄) (var vz))))))

⊢thinDone : {Γ : Ctx} → Γ ⊢ thinDone ∷ imethTy ThinD IPair zero cThin-done thinMotK
⊢thinDone =
  ⊢methLam ThinD IPair zero cThin-done ThinWf cThin-doneWf ⊢IPair ⊢thinMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢fst (⊢var (∋lkp _ (vsⁿ 2 vz))))))
      (⊢kTr ⊢nzero dsi (⊢symN dsi ⊢nzero (fordAs (⊢fst (⊢snd dp))))
            (⊢kTr dfi ⊢nzero (fordAs (⊢fst dp)) (⊢var here))))
  where
    di  = ⊢var (∋lkp _ (vsⁿ 3 vz))
    dp  = ⊢var (∋lkp _ (vsⁿ 2 vz))
    dfi = ⊢fst di
    dsi = ⊢snd di

thinKeep : {Γ : Cx} → RTm Γ
thinKeep = lam (lam (lam (lam
  (kTr (symN (snd I₄) (fst (snd (snd (snd (snd P₄))))))
       (app (extRNK (fst P₄) (fst (snd P₄)) (fst H₄))
            (kTr (fst (snd (snd (snd P₄)))) (var vz)))))))

⊢thinKeep : {Γ : Ctx} → Γ ⊢ thinKeep ∷ imethTy ThinD IPair (suc zero) cThin-keep thinMotK
⊢thinKeep =
  ⊢methLam ThinD IPair (suc zero) cThin-keep ThinWf cThin-keepWf ⊢IPair ⊢thinMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢fst (⊢var (∋lkp _ (vsⁿ 2 vz))))))
      (⊢kTr (⊢nsuc dn) dsi (⊢symN dsi (⊢nsuc dn) df2)
        (⊢-cast (cong (λ z → K (pair sVar z)) (wk-single {v = x₁} (nsuc n₁)))
          (⊢app (⊢extRNK dm dn (renTyβ (⊢fst dh)))
                (⊢kTr dfi (⊢nsuc dm) df1 (⊢var here))))))
  where
    di  = ⊢var (∋lkp _ (vsⁿ 3 vz))
    dp  = ⊢var (∋lkp _ (vsⁿ 2 vz))
    dh  = ⊢var (∋lkp _ (vsⁿ 1 vz))
    dfi = ⊢fst di
    dsi = ⊢snd di
    dm  = elAsNat (⊢fst dp)
    dn  = elAsNat (⊢fst (⊢snd dp))
    df1 = fordAs (⊢fst (⊢snd (⊢snd (⊢snd dp))))
    df2 = fordAs (⊢fst (⊢snd (⊢snd (⊢snd (⊢snd dp)))))
    n₁ : RTm _
    n₁ = fst (snd P₄)
    x₁ : RTm _
    x₁ = kTr (fst (snd (snd (snd P₄)))) (var vz)

thinDrop : {Γ : Cx} → RTm Γ
thinDrop = lam (lam (lam (lam
  (kTr (symN (snd I₄) (fst (snd (snd (snd (snd P₄))))))
       (Var-vsK (fst (snd P₄))
                (app (fst H₄) (kTr (fst (snd (snd (snd P₄)))) (var vz))))))))

⊢thinDrop : {Γ : Ctx} → Γ ⊢ thinDrop ∷ imethTy ThinD IPair (suc (suc zero)) cThin-drop thinMotK
⊢thinDrop =
  ⊢methLam ThinD IPair (suc (suc zero)) cThin-drop ThinWf cThin-dropWf ⊢IPair ⊢thinMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢fst (⊢var (∋lkp _ (vsⁿ 2 vz))))))
      (⊢kTr (⊢nsuc dn) dsi (⊢symN dsi (⊢nsuc dn) df2)
        (⊢Var-vsKt dn
          (⊢-cast (cong (λ z → K (pair sVar z)) (wk-single {v = x₁} n₁))
            (⊢app (renTyβ (⊢fst dh)) (⊢kTr dfi dm df1 (⊢var here)))))))
  where
    di  = ⊢var (∋lkp _ (vsⁿ 3 vz))
    dp  = ⊢var (∋lkp _ (vsⁿ 2 vz))
    dh  = ⊢var (∋lkp _ (vsⁿ 1 vz))
    dfi = ⊢fst di
    dsi = ⊢snd di
    dm  = elAsNat (⊢fst dp)
    dn  = elAsNat (⊢fst (⊢snd dp))
    df1 = fordAs (⊢fst (⊢snd (⊢snd (⊢snd dp))))
    df2 = fordAs (⊢fst (⊢snd (⊢snd (⊢snd (⊢snd dp)))))
    n₁ : RTm _
    n₁ = fst (snd P₄)
    x₁ : RTm _
    x₁ = kTr (fst (snd (snd (snd P₄)))) (var vz)

------------------------------------------------------------------------
-- 3. THE TUPLE, AND THE FOLD.
------------------------------------------------------------------------

thinMethsK : {Γ : Cx} → RTm Γ
thinMethsK = pair thinDone (pair thinKeep (pair thinDrop unit))

⊢thinMethsK : {Γ : Ctx} → Γ ⊢ thinMethsK ∷ imethsTy ThinD IPair thinMotK ThinD
⊢thinMethsK =
  ⊢methsCons ThinD IPair zero {C = cThin-done} (cThin-keep ◂ (cThin-drop ◂ inil)) ThinWf
    (idwf-cons cThin-keepWf (idwf-cons cThin-dropWf idwf-nil))
    (spl-cons spl-nil) ⊢IPair ⊢thinMotK ⊢thinDone
  (⊢methsCons ThinD IPair (suc zero) {C = cThin-keep} (cThin-drop ◂ inil) ThinWf
    (idwf-cons cThin-dropWf idwf-nil)
    (spl-cons (spl-cons spl-nil)) ⊢IPair ⊢thinMotK ⊢thinKeep
  (⊢methsCons ThinD IPair (suc (suc zero)) {C = cThin-drop} inil ThinWf idwf-nil
    (spl-cons (spl-cons (spl-cons spl-nil))) ⊢IPair ⊢thinMotK ⊢thinDrop
    ⊢unit))

-- ★ the object-level `thinR`: a thinning at `(d , n)` to a `RenTy d n`.
thinRenK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
thinRenK d n θ = ielim ThinD (pair d n) thinMethsK θ

⊢thinRenK : {Γ : Ctx} {d n θ : RTm ⌊ Γ ⌋} →
            Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ θ ∷ ThinK (pair d n) →
            Γ ⊢ thinRenK d n θ ∷ RenTy d n
⊢thinRenK {d = d} {n = n} {θ = θ} dd dn dθ =
  renTyβ (⊢-cast (cong₂ (λ a b → Π (K (pair sVar (fst a))) (K (pair sVar (snd b))))
                        (wk-single {v = θ} (pair d n))
                        (sub-w-single {v = θ} (pair d n)))
                 (⊢ielim ThinWf ⊢thinMotK (⊢ixP dd dn) ⊢thinMethsK dθ))

------------------------------------------------------------------------
-- 4. ★ THE KERNEL'S `renTm (thinR θ) t`, AS ONE PROGRAM — what an
--    A-math `IConWf` premise names, so the judgement rows cite it whole.
------------------------------------------------------------------------

thinTmK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
thinTmK d n θ t = renTmAtK sTm d n (thinRenK d n θ) t

⊢thinTmK : {Γ : Ctx} {d n θ t : RTm ⌊ Γ ⌋} →
           Γ ⊢ d ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ θ ∷ ThinK (pair d n) →
           Γ ⊢ t ∷ K (pair sTm d) → Γ ⊢ thinTmK d n θ t ∷ K (pair sTm n)
⊢thinTmK dd dn dθ dt = ⊢renTmAtK ⊢sTm dd dn (⊢thinRenK dd dn dθ) dt
