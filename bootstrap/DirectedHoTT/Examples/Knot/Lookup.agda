------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `_∋_∷_`, THE FIRST REAL JUDGEMENT.
--
--     here  : (Γ ▹ A) ∋ vz   ∷ renTy vs A
--     there : Γ ∋ x ∷ A → (Γ ▹ B) ∋ vs x ∷ renTy vs A
--
-- `PLAN-JUDGEMENT` step 1.  A RELATION over encoded syntax, and the
-- smallest complete one: two constructors, mentioning only `Ctx`, `Var`,
-- `RTy` and `renTy vs` — all four of which now exist object-level.
--
-- ★★ THE INDEX IS A FOUR-COMPONENT DEPENDENT TELESCOPE, and it spans
--   TWO DIFFERENT `IMu`s:
--
--     Σ' Nat (Σ' (CtxK ⟨d⟩) (Σ' (Var@⟨d⟩) (RTy@⟨d⟩)))
--
--   `Examples/DepIx` tested TWO components over one family.  ⚠ This is
--   where the plan said to look first if a telescope misbehaves, so it
--   is built and checked before either row is written.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Lookup where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; RTy; RTm; Nat; Σ'; El; IMu; pair
        ; fst; snd; nsuc; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; jsub
        ; ICon; IDesc; iι; iκ; inil; _◂_ )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ty-Nat; ty-Σ; ty-IMu )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sVar; ⊢sTy; ⊢sVar; toI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Lib.ArithComm using ( symN )
open import DirectedHoTT.Examples.Knot.CtxD
  using ( CtxD; CtxK; CtxWf; INat; Ctx-extK )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK )

------------------------------------------------------------------------
-- 1. THE INDEX.
--
-- ⚠ `Σ'` BINDS, so each component may mention the earlier ones while the
--   WHOLE thing mentions no ambient variable — which is what keeps it a
--   CLOSED `RTy ε`, the only kind `IMu` accepts.  That is `DepIx`'s
--   result, here at four components instead of two.
------------------------------------------------------------------------

ILk : RTy ε
ILk =
  Σ' Nat
    (Σ' (CtxK (var vz))
      (Σ' (K (pair sVar (var (vs vz))))
          (K (pair sTy (var (vs (vs vz)))))))

-- ⚠ THE ⊢ty RESTATES THE TYPE rather than naming `ILk`, exactly as
--   `Knot/Sorts.⊢IPair` does: `ILk` is fixed at `RTy ε` because that is
--   what `IMu` takes, while a `⊢ty` is needed at an ARBITRARY `Γ`.  The
--   body is closed, so it inhabits `RTy ⌊ Γ ⌋` for every `Γ`.
⊢ILk : {Γ : Ctx} → Γ ⊢ty
       Σ' Nat
         (Σ' (CtxK (var vz))
           (Σ' (K (pair sVar (var (vs vz))))
               (K (pair sTy (var (vs (vs vz)))))))
⊢ILk =
  ty-Σ ty-Nat
    (ty-Σ (ty-IMu CtxWf (toI (⊢var here)))
      (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here))))
            (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (there (there here)))))))

------------------------------------------------------------------------
-- 2. ★★ `here`, AND THE PRICE FORDING CHARGES HERE.
--
--     here : (Γ ▹ A) ∋ vz ∷ renTy vs A
--
-- It binds `m`, `Γ : Ctx m` and `A : RTy m`, and targets the index
-- `(suc m, Γ ▹ A, vz, wk A)` — so it FORDS all four components.
--
-- ⚠⚠ AND THE LAST THREE FORDS CANNOT BE WRITTEN NAIVELY.  `iwf-κ` wants
--   the ford's code TYPED, and a ford's two sides must sit at the SAME
--   code.  The ambient's `Ctx` component lives at depth `fst ⟨i⟩`, while
--   `Ctx-extK m Γ A` lives at `nsuc m` — and those agree only by the
--   DEPTH FORD, which is PROPOSITIONAL.
--
-- ⇒ each of the three later fords transports its right-hand side along
--   the depth ford, `jsub (⌜IMu⌝ … ⟨-⟩) (symN … p) e` — `Examples/WkFin`'s
--   idiom, three times in one row.  ★ This is `PLAN-JUDGEMENT` §1's
--   "Fording costs a transport in the DERIVATION and nothing at runtime"
--   made concrete, and it is the first row where the transport is paid
--   for a FOREIGN family rather than for the row's own index.
------------------------------------------------------------------------

lkHere : ICon (ε ∙)
lkHere =
  iκ ⌜Nat⌝                                                    -- 0: m
   (iκ (⌜IMu⌝ CtxD INat (var vz))                             -- 1: Γ : Ctx m
    (iκ (⌜IMu⌝ KnotD IPair (pair sTy (var (vs vz))))          -- 2: A : RTy m
     -- 3: the DEPTH ford, `fst ⟨i⟩ ≡ suc m`
     (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs (vs vz)))))
                     (nsuc (var (vs (vs vz)))))
      -- 4: the CONTEXT ford, transported along 3
      (iκ (⌜Id⌝ (⌜IMu⌝ CtxD INat (fst (var (vs (vs (vs (vs vz)))))))
                (fst (snd (var (vs (vs (vs (vs vz)))))))
                (jsub (⌜IMu⌝ CtxD INat (var vz))
                      (symN (fst (var (vs (vs (vs (vs vz))))) ) (var vz))
                      (Ctx-extK (var (vs (vs (vs vz))))
                                (var (vs (vs vz)))
                                (var (vs vz)))))
      -- 5: the VARIABLE ford, transported along 3
      (iκ (⌜Id⌝ (⌜IMu⌝ KnotD IPair (pair sVar (fst (var (vs (vs (vs (vs (vs vz)))))))))
                (fst (snd (snd (var (vs (vs (vs (vs (vs vz)))))))))
                (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                      (symN (fst (var (vs (vs (vs (vs (vs vz))))))) (var (vs vz)))
                      (Var-vzK (var (vs (vs (vs (vs vz))))))))
       -- 6: the TYPE ford — ★ and its right-hand side is `wkK`, which is
       --    why step 2 had to land before step 1 could be written.
       (iκ (⌜Id⌝ (⌜IMu⌝ KnotD IPair (pair sTy (fst (var (vs (vs (vs (vs (vs (vs vz))))))))))
                 (snd (snd (snd (var (vs (vs (vs (vs (vs (vs vz))))))))))
                 (jsub (⌜IMu⌝ KnotD IPair (pair sTy (var vz)))
                       (symN (fst (var (vs (vs (vs (vs (vs (vs vz))))))))
                             (var (vs (vs vz))))
                       (wkK (pair sTy (var (vs (vs (vs (vs (vs vz)))))))
                            (var (vs (vs (vs vz)))))))
        iι))))))
