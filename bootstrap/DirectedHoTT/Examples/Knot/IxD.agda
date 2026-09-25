------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE MERGED JUDGEMENT'S **PER-TAG PAYLOAD**.
--
-- `JUDGEMENT-ATTEMPTS` §10.5: the merged index is split by WHO READS IT.
-- The five slots consumers PROJECT stay flat and projectable; the
-- merge-only subjects go behind ONE payload, here.
--
--     IJudge = Σ' Nat (Σ' Ctx (Σ' Tm (Σ' Ty (Σ' Nat (IMu IxD INat ⟨d⟩)))))
--              └───────────── projected by consumers ─────────┘ └ this ┘
--
-- ⇒ width 5 → 6 rather than 5 → 11, and the 43 typing rows carry ONE
--   dummy (`IxNoneK`) instead of six at six different sorts.
--
-- ★★★ INDEXED BY THE **DEPTH**, NOT BY THE TAG — counted, in §11.2.
--   Across all seven merged judgements the payload carries at most FIVE
--   fields (`IConWf`'s, under A-math: `I`, the constructor scope's depth
--   `dΔ`, the thinning `ρ`, the family variable `x` and `C : ICon Δ`), and
--   `ρ`/`x` are the ones that read the depth.  A `(tag , depth)` pair index is NOT needed: each
--   judgement ROW Fords its payload slot to a specific `icon k …`, so
--   the tag is already pinned where it matters.
--
-- ★★★ AND THE CLOSED SUBJECTS SIT AT ABSOLUTE DEPTH **0**, WHICH IS A
--   DECISION, NOT A DEFAULT.  `KNOT` carries `Desc`/`DCon`/`IDesc`
--   fields at the AMBIENT depth (`rec("sDesc", D)`) and `RTy ε` at
--   `lit 0`.  Both conventions are available here and they are NOT
--   symmetric:
--
--     AMBIENT  `⊢icon`/`⊢elim` agree with the knot's own fields, but
--              `idwf-cons` read `D` at its premise's depth AND at the
--              row's variable `n` (before A-math removed `D` from it).  Relating those needs `n → 1`, a
--              STRENGTHENING.  Nothing provides one.
--     CLOSED   `idwf-cons` reads one field, at 0, in both places; and
--              `⊢icon` recovers the knot's ambient copy with
--              `εwkK sIDesc n` — `0 → n`, which is exactly what
--              `Knot/EWk` is.
--
--   ⇒ CLOSED, because the reindexing it needs EXISTS and the other's
--     does not.  ⚠ That asymmetry is the whole argument; "closed things
--     belong at 0" on its own would have been a preference.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IxD where
open import DirectedHoTT.Lib.Lkp using ( ∋lkp; vsⁿ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTy; RTm; var; vz; vs; pair; unit; nzero; icon; IMu
        ; ⌜IMu⌝; ⌜Nat⌝; Nat; ICon; IDesc; iι; iκ; inil; _◂_; εwkTy
        ; _∈ID_; hereID; thereID; subTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; ⊢unit; ⊢icon; ⊢pair; ⊢nzero; ⊢⌜IMu⌝; ⊢⌜Nat⌝
        ; ty-Unit; ty-Σ; ty-El; ⊢var; here; there; single; wk-single
        ; IConWf; iwf-ι; iwf-κ; ICodeWf; icw-imu; icw-clo
        ; IDescWf; idwf-nil; idwf-cons; _,,_; Θ₀; ρ₀; x₀ )
open import DirectedHoTT.Metatheory.TySub using ( xenv₀; xenv-κ )
open import DirectedHoTT.Lib.IPay using ( ⊢payκ; icwTailκ )
open import DirectedHoTT.Lib.ICast using ( toMu )
open import DirectedHoTT.Examples.Knot.ThinD using ( ThinD; ThinK; ThinWf )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sDesc; sDCon; sIDesc; sICon; sVar
        ; ⊢sTy; ⊢sDesc; ⊢sDCon; ⊢sIDesc; ⊢sICon; ⊢sVar; toI; fromI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.CtxD using ( INat; toKn )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Wk using ( sub-w-single )
open import DirectedHoTT.Examples.Knot.Build using ( tmCast; kCast )
open import normalizer.Syntax.Types using ( sym; trans; cong )

------------------------------------------------------------------------
-- 1. THE FIVE CONSTRUCTORS.  ⚠ `iι` targets the AMBIENT index, so none
--    of these Fords the depth — a payload is available at every depth,
--    and the JUDGEMENT row is what pins which one it is.
------------------------------------------------------------------------

-- ⊢ty / ⊢_∷_ / ICodeWf — no merge-only subject at all
cIxNone : ICon (ε ∙)
cIxNone = iι

-- DConWf C
cIxDCon : ICon (ε ∙)
cIxDCon = iκ (⌜IMu⌝ KnotD IPair (pair sDCon nzero)) iι

-- DescWf D
cIxDesc : ICon (ε ∙)
cIxDesc = iκ (⌜IMu⌝ KnotD IPair (pair sDesc nzero)) iι

-- ★ IConWf I {Δ} Θ ρ x C — A-MATH.  `I` closed; `dΔ` the constructor
--   scope's depth; the thinning `ρ : Thin (dΔ , n)`; the family variable
--   `x : Var n`; and `C : ICon (dΔ)` — at the SCOPE's depth, not Θ's.
cIxICon : ICon (ε ∙)
cIxICon =
  iκ (⌜IMu⌝ KnotD IPair (pair sTy nzero))
   (iκ ⌜Nat⌝
    (iκ (⌜IMu⌝ ThinD IPair (pair (var vz) (var (vs (vs vz)))))
     (iκ (⌜IMu⌝ KnotD IPair (pair sVar (var (vs (vs (vs vz))))))
      (iκ (⌜IMu⌝ KnotD IPair (pair sICon (var (vs (vs vz)))))
       iι))))

-- IDescWfFrom I E — both CLOSED (A-math: no description in the judgment)
cIxIDesc : ICon (ε ∙)
cIxIDesc =
  iκ (⌜IMu⌝ KnotD IPair (pair sTy nzero))
   (iκ (⌜IMu⌝ KnotD IPair (pair sIDesc nzero))
    iι)

IxD : IDesc
IxD = cIxNone ◂ (cIxDCon ◂ (cIxDesc ◂ (cIxICon ◂ (cIxIDesc ◂ inil))))

------------------------------------------------------------------------
-- 2. WELL-FORMEDNESS.
------------------------------------------------------------------------

cIxNoneWf : IConWf INat (Θ₀ INat) ρ₀ x₀ cIxNone
cIxNoneWf = iwf-ι

cIxDConWf : IConWf INat (Θ₀ INat) ρ₀ x₀ cIxDCon
cIxDConWf =
  iwf-κ (⌜IMu⌝ KnotD IPair (pair sDCon nzero))
        (icw-imu (pair sDCon nzero) KnotWf)
        (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sDCon ⊢nzero))
        iwf-ι

cIxDescWf : IConWf INat (Θ₀ INat) ρ₀ x₀ cIxDesc
cIxDescWf =
  iwf-κ (⌜IMu⌝ KnotD IPair (pair sDesc nzero))
        (icw-imu (pair sDesc nzero) KnotWf)
        (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sDesc ⊢nzero))
        iwf-ι

cIxIConWf : IConWf INat (Θ₀ INat) ρ₀ x₀ cIxICon
cIxIConWf =
  iwf-κ (⌜IMu⌝ KnotD IPair (pair sTy nzero))
        (icw-imu (pair sTy nzero) KnotWf)
        (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy ⊢nzero))
   (iwf-κ ⌜Nat⌝ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝
    (iwf-κ (⌜IMu⌝ ThinD IPair (pair (var vz) (var (vs (vs vz)))))
           (icw-imu (pair (var vz) (var (vs (vs vz)))) ThinWf)
           (⊢⌜IMu⌝ ThinWf (⊢ixP (fromI (⊢var here))
                                (fromI (⊢var (∋lkp _ (vsⁿ 2 vz))))))
     (iwf-κ (⌜IMu⌝ KnotD IPair (pair sVar (var (vs (vs (vs vz))))))
            (icw-imu (pair sVar (var (vs (vs (vs vz))))) KnotWf)
            (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (fromI (⊢var (∋lkp _ (vsⁿ 3 vz))))))
      (iwf-κ (⌜IMu⌝ KnotD IPair (pair sICon (var (vs (vs vz)))))
             (icw-imu (pair sICon (var (vs (vs vz)))) KnotWf)
             (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sICon (fromI (⊢var (∋lkp _ (vsⁿ 2 vz))))))
       iwf-ι))))

cIxIDescWf : IConWf INat (Θ₀ INat) ρ₀ x₀ cIxIDesc
cIxIDescWf =
  iwf-κ (⌜IMu⌝ KnotD IPair (pair sTy nzero))
        (icw-imu (pair sTy nzero) KnotWf)
        (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy ⊢nzero))
   (iwf-κ (⌜IMu⌝ KnotD IPair (pair sIDesc nzero))
          (icw-imu (pair sIDesc nzero) KnotWf)
          (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sIDesc ⊢nzero))
    iwf-ι)

IxWf : IDescWf INat IxD
IxWf =
  ty-El ⊢⌜Nat⌝ ,,
  idwf-cons cIxNoneWf
   (idwf-cons cIxDConWf
    (idwf-cons cIxDescWf
     (idwf-cons cIxIConWf
      (idwf-cons cIxIDescWf idwf-nil))))

IxNoneK : {Γ : Cx} → RTm Γ → RTm Γ
IxNoneK _ = icon zero unit

⊢IxNoneK : {Δ : Ctx} {n : RTm ⌊ Δ ⌋} →
           Δ ⊢ n ∷ Nat → Δ ⊢ IxNoneK n ∷ IMu IxD INat n
⊢IxNoneK dn = ⊢icon IxWf hereID (toI dn) ⊢unit

IxDConK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
IxDConK _ c = icon (suc zero) (pair c unit)

⊢IxDConK : {Δ : Ctx} {n c : RTm ⌊ Δ ⌋} →
           Δ ⊢ n ∷ Nat → Δ ⊢ c ∷ K (pair sDCon nzero) →
           Δ ⊢ IxDConK n c ∷ IMu IxD INat n
⊢IxDConK dn dc =
  ⊢icon IxWf (thereID hereID) (toI dn)
    (⊢pair ty-Unit (toKn dc) ⊢unit)

IxDescK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
IxDescK _ d = icon (suc (suc zero)) (pair d unit)

⊢IxDescK : {Δ : Ctx} {n d : RTm ⌊ Δ ⌋} →
           Δ ⊢ n ∷ Nat → Δ ⊢ d ∷ K (pair sDesc nzero) →
           Δ ⊢ IxDescK n d ∷ IMu IxD INat n
⊢IxDescK dn dd =
  ⊢icon IxWf (thereID (thereID hereID)) (toI dn)
    (⊢pair ty-Unit (toKn dd) ⊢unit)

-- ★ the ONE constructor whose last field reads the index
-- ★ A-MATH: `IConWf I {Δ} Θ ρ x C`'s payload, one field at a time.
IxIConK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
IxIConK _ i d r x c =
  icon (suc (suc (suc zero))) (pair i (pair d (pair r (pair x (pair c unit)))))

⊢IxIConK : {Δ : Ctx} {n i d r x c : RTm ⌊ Δ ⌋} →
           Δ ⊢ n ∷ Nat →
           Δ ⊢ i ∷ K (pair sTy nzero) →
           Δ ⊢ d ∷ Nat →
           Δ ⊢ r ∷ ThinK (pair d n) →
           Δ ⊢ x ∷ K (pair sVar n) →
           Δ ⊢ c ∷ K (pair sICon d) →
           Δ ⊢ IxIConK n i d r x c ∷ IMu IxD INat n
⊢IxIConK dn di dd dr dx dc =
  ⊢icon IxWf (thereID (thereID (thereID hereID))) (toI dn)
    (⊢payκ IxD INat _ _ _ IxWf cIxIConWf e₀ (toKn di)
     (⊢payκ IxD INat _ _ _ IxWf w₁ e₁ (toI dd)
      (⊢payκ IxD INat _ _ _ IxWf w₂ e₂ (toMu dr)
       (⊢payκ IxD INat _ _ _ IxWf w₃ e₃ (toKn dx)
        (⊢payκ IxD INat _ _ _ IxWf w₄ e₄ (toKn dc)
         ⊢unit)))))
  where
    e₀ = xenv₀ IxWf (toI dn)
    w₁ = icwTailκ cIxIConWf
    w₂ = icwTailκ w₁
    w₃ = icwTailκ w₂
    w₄ = icwTailκ w₃
    e₁ = xenv-κ e₀ _ (toKn di)
    e₂ = xenv-κ e₁ ⌜Nat⌝ (toI dd)
    e₃ = xenv-κ e₂ _ (toMu dr)
    e₄ = xenv-κ e₃ _ (toKn dx)

IxIDescK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
IxIDescK _ i e = icon (suc (suc (suc (suc zero)))) (pair i (pair e unit))

⊢IxIDescK : {Δ : Ctx} {n i e : RTm ⌊ Δ ⌋} →
            Δ ⊢ n ∷ Nat →
            Δ ⊢ i ∷ K (pair sTy nzero) →
            Δ ⊢ e ∷ K (pair sIDesc nzero) →
            Δ ⊢ IxIDescK n i e ∷ IMu IxD INat n
⊢IxIDescK dn di de =
  ⊢icon IxWf (thereID (thereID (thereID (thereID hereID)))) (toI dn)
    (⊢payκ IxD INat _ _ _ IxWf cIxIDescWf e₀ (toKn di)
     (⊢payκ IxD INat _ _ _ IxWf (icwTailκ cIxIDescWf) (xenv-κ e₀ _ (toKn di)) (toKn de)
      ⊢unit))
  where
    e₀ = xenv₀ IxWf (toI dn)

