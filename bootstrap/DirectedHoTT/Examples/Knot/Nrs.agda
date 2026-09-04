------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `nrs`, OBJECT-LEVEL.
--
--     nrs : Sub (Γ ∙) ((Γ ∙) ∙)
--     nrs vz     = nsuc (var (vs vz))
--     nrs (vs x) = var (vs (vs x))
--
-- ⚠ `⊢natrec`'s successor premise reads `((Γ ▹ Nat) ▹ M) ⊢ s ∷ subTy nrs M`
--   — the ONE rule left whose every depth question is already resolved
--   and which needs only this function.
--
-- ★★★ IT IS THE FIRST **RAISING** SUBSTITUTION.  `single` and `extS`
--   lower or preserve; `nrs` sends a variable at `n` to a term at
--   `nsuc n`, which is why `_argshift` had to learn to dispatch on the
--   substitution rather than on `subTy`.
--
-- ★ SHAPE: `Knot/Single`'s.  Two `Var` methods do the work, the other 51
--   rows are junk that no well-typed call can reach — the eliminator
--   runs over every row, so they must be SOMETHING, and `nzero` is a
--   term at every depth.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Nrs where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; fst; snd; pair; nsuc
        ; ICon; IDesc; εwkTy; IMu; unit; ielim; Σ'; Nat; _◂_; renTm )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢nsuc; ty-IMu; IConWf; imethTy; imethsTy; imethsTyFrom
        ; ⊢unit; ⊢ielim; IDescWfFrom; ⊢lam; βsnd; ξ-nsuc; ξ-pairʳ )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢methsFrom; ⊢methsCons; imethsTyFrom-wf; idwfDrop
        ; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-nzeroK; Tm-varK; Tm-nsucK )
open import DirectedHoTT.Examples.Knot.CtorsV
  using ( ⊢Tm-nzeroKv; ⊢Tm-varKv; ⊢Tm-nsucKv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; Var-vsK; ⊢Var-vzKt; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.Desc using ( cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Wf using ( cVar-vzWf; cVar-vsWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz; tagVar-vs )
open import DirectedHoTT.Lib.ICast using ( toMu; fromMu; fordAs; muFwd )
open import DirectedHoTT.Lib.ArithComm using ( symN; ⊢symN )
open import DirectedHoTT.Lib.IdSuc using ( predN; ⊢fordPredN )
open import DirectedHoTT.Lib.Strong using ( elAsNat; natAsEl )
open import DirectedHoTT.Lib.Monus using ( predTm; ⊢pred )
open import DirectedHoTT.Spec.Syntax using ( ⌜IMu⌝; jsub )
open import DirectedHoTT.Spec.Typing using ( ⊢jsub; ⊢⌜IMu⌝; ⊢fst )
open import DirectedHoTT.Examples.Knot.Sorts using ( sVar; ⊢sVar )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Spec.Typing using ( wk-single )
open import normalizer.Syntax.Types using ( cong )

------------------------------------------------------------------------
-- ★ THE MOTIVE.  At index `i` the answer is a term one binder DEEPER:
--   `nrs` is what `natrec`'s successor branch substitutes, and that
--   branch lives under two binders where the motive lived under one.
------------------------------------------------------------------------

nrsMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
nrsMotK = IMu KnotD IPair (pair sTm (nsuc (snd (var (vs vz)))))

⊢nrsMotK : {Γ : Ctx} →
           ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty nrsMotK
⊢nrsMotK = ty-IMu KnotWf (⊢ixP ⊢sTm (⊢nsuc (⊢snd (⊢var (there here)))))

------------------------------------------------------------------------
-- ★ THE 51 UNREACHABLE ROWS.  ⚠ They are not dead code: `ielim` demands
--   a method per row whether or not a well-typed caller can select it.
------------------------------------------------------------------------

nrsJunk : {Γ : Cx} → RTm Γ
nrsJunk = lam (lam (lam Tm-nzeroK))

⊢nrsJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
           IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
           Γ ⊢ nrsJunk ∷ imethTy KnotD IPair k C nrsMotK
⊢nrsJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢nrsMotK
    (⊢Tm-nzeroKv _ (⊢nsuc (⊢snd (⊢var (there (there here))))))

------------------------------------------------------------------------
-- ★★★ `vz ↦ nsuc (var (vs vz))`.
--
-- The row Fords its depth: `cVar-vz` exists only at a SUCCESSOR, so the
-- ambient `snd ⟨i⟩` is `nsuc` of the row's own `m`.  The answer wants a
-- `Var` at `nsuc (snd ⟨i⟩)` = `nsuc (nsuc m)`, i.e. `vs vz` there —
-- `Var-vsK (nsuc m)` applied to `Var-vzK m`.
--
-- ⚠ SAME FORD TRANSPORT AS `Knot/Single`'s `vs` ROW, for the same
--   reason: the row's `m` and the ambient `pred (snd ⟨i⟩)` agree only
--   through the row's depth ford, inverted and stepped down.
------------------------------------------------------------------------

-- ★ payload = (m , (sort-ford , (depth-ford , unit))), and the DEPTH
--   ford says `snd ⟨i⟩ ≡ nsuc m` — the transport this row needs, in the
--   direction it needs it.  ⚠ Simpler than `Knot/Single`'s `vs` row,
--   whose motive read `predTm (snd ⟨i⟩)` and so had to step the ford
--   down with `⊢fordPredN` first.

nrsVz : {Γ : Cx} → RTm Γ
nrsVz = lam (lam (lam
  (Tm-nsucK (Tm-varK
    (Var-vsK (snd (var (vs (vs vz))))
             (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                   -- ⚠ BODY-LEVEL indices: only `jsub`'s MOTIVE binds a
                   --   variable, its path and term do not.  And this
                   --   method has THREE `lam`s, not `Knot/Single`'s four
                   --   — that motive was a `Π`, this one is not.
                   (symN (snd (var (vs (vs vz))))
                         (fst (snd (snd (var (vs vz))))))
                   (Var-vzK (fst (var (vs vz))))))))))

⊢nrsVz : {Γ : Ctx} →
         Γ ⊢ nrsVz ∷ imethTy KnotD IPair tagVar-vz cVar-vz nrsMotK
⊢nrsVz =
  ⊢methLam KnotD IPair tagVar-vz cVar-vz KnotWf cVar-vzWf ⊢IPair ⊢nrsMotK
    (⊢Tm-nsucKv _ (⊢nsuc dsi)
      (⊢Tm-varKv _ (⊢nsuc dsi) (⊢Var-vsKt dsi tx)))
  where
    dp   = ⊢var (there here)
    dsi  = ⊢snd (⊢var (there (there here)))
    dm   = elAsNat (⊢fst dp)
    deq  = ⊢symN dsi (⊢nsuc dm) (fordAs (⊢fst (⊢snd (⊢snd dp))))
    tx   = fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                         (natAsEl (⊢nsuc dm)) (natAsEl dsi) deq
                         (toMu (⊢Var-vzKt dm)))

------------------------------------------------------------------------
-- ★★★ `vs x ↦ var (vs (vs x))` — the variable weakened TWICE.
--
-- ⚠ `x` COMES FROM THE PAYLOAD, NOT THE IH.  `nrs` is not recursive:
--   it rebuilds the variable rather than mapping under it, so the IH
--   tuple is present and unused.
------------------------------------------------------------------------

nrsVs : {Γ : Cx} → RTm Γ
nrsVs = lam (lam (lam
  (Tm-varK
    (Var-vsK (snd (var (vs (vs vz))))
             (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                   (symN (snd (var (vs (vs vz))))
                         (fst (snd (snd (snd (var (vs vz)))))))
                   (Var-vsK (fst (var (vs vz))) (fst (snd (var (vs vz))))))))))

⊢nrsVs : {Γ : Ctx} →
         Γ ⊢ nrsVs ∷ imethTy KnotD IPair tagVar-vs cVar-vs nrsMotK
⊢nrsVs =
  ⊢methLam KnotD IPair tagVar-vs cVar-vs KnotWf cVar-vsWf ⊢IPair ⊢nrsMotK
    (⊢Tm-varKv _ (⊢nsuc dsi) (⊢Var-vsKt dsi tx))
  where
    dp   = ⊢var (there here)
    dsi  = ⊢snd (⊢var (there (there here)))
    dm   = elAsNat (⊢fst dp)
    -- ⚠ `x` IS AN `iρ` FIELD, so the payload already holds an `IMu` —
    --   `fromMu` (El → IMu) is the wrong direction here.
    dx   = ⊢fst (⊢snd dp)
    deq  = ⊢symN dsi (⊢nsuc dm) (fordAs (⊢fst (⊢snd (⊢snd (⊢snd dp)))))
    tx   = fromMu (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (elAsNat (⊢var here))))
                         (natAsEl (⊢nsuc dm)) (natAsEl dsi) deq
                         (toMu (⊢Var-vsKt dm dx)))

------------------------------------------------------------------------
-- ★★★ THE TUPLE AND THE ELIMINATOR — `Knot/Single`'s assembly exactly:
--   51 junk rows, then the two `Var` rows that do the work.
------------------------------------------------------------------------

nrsTail : {Γ : Cx} → RTm Γ
nrsTail = pair nrsVz (pair nrsVs unit)

D51 : IDesc
D51 = cdRest (cdTake 51 KnotD)

sp51 : Split KnotD 51 D51
sp51 = splTake spl-nil (cdTake 51 KnotD)

⊢nrsTail : {Γ : Ctx} →
           Γ ⊢ nrsTail ∷ imethsTyFrom KnotD IPair nrsMotK 51 D51
⊢nrsTail =
  ⊢methsCons KnotD IPair 51 {C = cVar-vz} _ KnotWf
             (idwfDrop (spl-step sp51) KnotWf) (spl-step sp51)
             ⊢IPair ⊢nrsMotK ⊢nrsVz
    (⊢methsCons KnotD IPair 52 {C = cVar-vs} _ KnotWf
                (idwfDrop (spl-step (spl-step sp51)) KnotWf)
                (spl-step (spl-step sp51))
                ⊢IPair ⊢nrsMotK ⊢nrsVs ⊢unit)

nrsMeths : {Γ : Cx} → RTm Γ
nrsMeths = methsFrom (cdTake 51 KnotD) nrsJunk nrsTail

⊢nrsMeths : {Γ : Ctx} → Γ ⊢ nrsMeths ∷ imethsTy KnotD IPair nrsMotK KnotD
⊢nrsMeths =
  ⊢methsFrom KnotD IPair 0 (cdTake 51 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢nrsMotK (λ {k} {C} wC _ _ → ⊢nrsJunk k C wC)
             nrsTail ⊢nrsTail

-- ★ NO CAST: the motive mentions only `snd ⟨i⟩`, so `iinst i x nrsMotK`
--   is already `K (pair sTm (nsuc (snd i)))`.
nrsK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
nrsK i x = ielim KnotD i nrsMeths x

------------------------------------------------------------------------
-- ★★★ `nrs` AS A **SUBSTITUTION**, which is how the rule names it.
--
-- ⚠ `subTy nrs M` wants a `SubTy` — a `Π (Var d) (Tm n)`, i.e. a LAMBDA.
--   Mapping `nrs` to the bare eliminator emits `nrsK ⟨i⟩` with its
--   scrutinee missing, which is not a term at all; the Wf emitter said
--   so (`no Wf rule for head 'nrsK'`) before anything type-checked.
--
-- ★ AND IT RAISES: `SubTy d (nsuc d)`.  `single` and `extS` do not, which
--   is exactly the distinction `_argshift` was rebuilt around.
------------------------------------------------------------------------

nrsSubK : {Γ : Cx} → RTm Γ → RTm Γ
nrsSubK d = lam (nrsK (pair sVar (renTm vs d)) (var vz))

⊢nrsSubK : {Γ : Ctx} {d : RTm ⌊ Γ ⌋} →
           Γ ⊢ d ∷ Nat → Γ ⊢ nrsSubK d ∷ SubTy d (nsuc d)
⊢nrsSubK dd =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar dd))
       -- ⚠ TWO STEPS, DIFFERENT CURRENCIES.  `iinst` leaves the index
       --   as `subTm (single x) (w i)` — an `≡`, so `⊢-cast`; then
       --   `snd (pair sVar …)` is a REDUCTION, so `muFwd`.  The same
       --   pair `⊢singleSK` and `⊢extSK` pay.
       (muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
         (⊢-cast (cong (λ z → IMu KnotD IPair (pair sTm (nsuc (snd z))))
                       (wk-single {v = var vz} (pair sVar (renTm vs _))))
                 (⊢ielim KnotWf ⊢nrsMotK (⊢ixP ⊢sVar (⊢wk dd)) ⊢nrsMeths
                         (⊢var here))))
