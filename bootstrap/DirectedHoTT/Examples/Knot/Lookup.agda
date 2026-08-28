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
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢conv
        ; ⊢fst; ⊢snd; ⊢nsuc; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢jsub
        ; ty-Nat; ty-Σ; ty-IMu
        ; IConWf; iwf-ι; iwf-κ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; _≅ᵀ_; csymᵀ; credᵀ; El-⌜IMu⌝; ξ-IMu
        ; _⟶_; βfst; βsnd; ξ-pairˡ; ξ-pairʳ; ξ-nsuc )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sVar; ⊢sTy; ⊢sVar; toI; fromI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN; elIdN )
open import DirectedHoTT.Examples.Knot.CtxD
  using ( CtxD; CtxK; CtxWf; INat; Ctx-extK; ⊢Ctx-extKv; toKn )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK; ⊢Var-vzKv )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkK )

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
-- 2. ★★ `here` — ONE `Def` PER FIELD, AND THAT IS FORCED.
--
--     here : (Γ ▹ A) ∋ vz ∷ renTy vs A
--
-- It binds `m`, `Γ : Ctx m` and `A : RTy m` and targets
-- `(suc m, Γ ▹ A, vz, wk A)`, so it FORDS all four components.
--
-- ⚠⚠ WRITTEN AS ONE NESTED TERM THIS ROW DOES NOT FIT — `-A64m` and
--   `-A64m -c` both OOM (143), on a box with 4.2 GB free against a 5.5 GB
--   cap.  ⚠ Diagnosed rather than guessed: no concurrent `agda`
--   (`never-run-two-agda-checks-at-once` ruled out), `-c` tried FIRST
--   (`agda-oom-is-a-gc-choice`) and did not help alone.  It is
--   `agda-cost-is-elaborated-term-size`, and the remedy is that rule's
--   own: every code, telescope and field-proof gets a NAME, so the bodies
--   are elaborated behind a `Def` and the traversal phases walk small
--   terms.  Split, the module is 238 MB peak and 5.4s — of which its own
--   `Typing` is 26ms and the rest is deserialising the import closure.
--
-- ★★★ AND THE THREE LATER FORDS ARE TRANSPORTED.  `iwf-κ` wants each
--   ford's code TYPED, and a ford's two sides must sit at the SAME code —
--   but the ambient's `Ctx` component lives at depth `fst ⟨i⟩` while
--   `Ctx-extK m Γ A` lives at `nsuc m`, and those agree only by the DEPTH
--   ford, which is PROPOSITIONAL.  So each right-hand side moves along it
--   by `jsub (⌜IMu⌝ … ⟨-⟩) (symN … p) e` — `Examples/WkFin`'s idiom, three
--   times in one row, and the first time it is paid for a FOREIGN family
--   rather than for the row's own index.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- THE CONVERSIONS EVERY FOREIGN-`IMu` FORD CROSSES.
--
-- ⚠ A ford's code is `⌜IMu⌝ …`, so its two sides are typed at
--   `El (⌜IMu⌝ …)`, while the things inhabiting them are typed at
--   `IMu …`.  One `El-⌜IMu⌝` each way — and `CtxD` needs its own pair,
--   because `toKn` is `KnotD`'s.
------------------------------------------------------------------------

toCn : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
       Γ ⊢ t ∷ CtxK i → Γ ⊢ t ∷ El (⌜IMu⌝ CtxD INat i)
toCn d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

fromCn : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ El (⌜IMu⌝ CtxD INat i) → Γ ⊢ t ∷ CtxK i
fromCn d = ⊢conv d (credᵀ El-⌜IMu⌝)

fromKn : {Γ : Ctx} {i t : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ El (⌜IMu⌝ KnotD IPair i) → Γ ⊢ t ∷ K i
fromKn d = ⊢conv d (credᵀ El-⌜IMu⌝)

fordAs : {Γ : Ctx} {a b t : RTm ⌊ Γ ⌋} →
         Γ ⊢ t ∷ El (⌜Id⌝ ⌜Nat⌝ a b) → Γ ⊢ t ∷ IdN a b
fordAs {a = a} {b = b} d = ⊢conv d (elIdN a b)

-- ★ `wkK`'s result index is `sh (pair sTy m)`; the ford wants
--   `pair sTy (nsuc m)`.  Two β-steps, the same two every time.
kFwd : {Γ : Ctx} {i i' t : RTm ⌊ Γ ⌋} → i ⟶ i' → Γ ⊢ t ∷ K i → Γ ⊢ t ∷ K i'
kFwd r d = ⊢conv d (credᵀ (ξ-IMu r))

-- ⚠ THE TELESCOPES AND THE CODES INTERLEAVE, and they must: `κₖ` lives in
--   `⌊ Θₖ ⌋` and `Θₖ₊₁` is `Θₖ ▹ El κₖ`.  A context-POLYMORPHIC `κ` cannot
--   work — `var (vs (vs (vs vz)))` needs a `Cx` at least four deep, so the
--   context has to be concrete at each step.

Θ0 : Ctx
Θ0 = ◇ ▹ ILk

κ₀ : RTm ⌊ Θ0 ⌋
κ₀ = ⌜Nat⌝                                          -- m : Nat

Θ1 : Ctx
Θ1 = Θ0 ▹ El κ₀

κ₁ : RTm ⌊ Θ1 ⌋
κ₁ = ⌜IMu⌝ CtxD INat (var vz)                       -- Γ : Ctx m

Θ2 : Ctx
Θ2 = Θ1 ▹ El κ₁

κ₂ : RTm ⌊ Θ2 ⌋
κ₂ = ⌜IMu⌝ KnotD IPair (pair sTy (var (vs vz)))     -- A : RTy m

Θ3 : Ctx
Θ3 = Θ2 ▹ El κ₂

-- the DEPTH ford, `fst ⟨i⟩ ≡ suc m`
κ₃ : RTm ⌊ Θ3 ⌋
κ₃ = ⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs (vs vz))))) (nsuc (var (vs (vs vz))))

Θ4 : Ctx
Θ4 = Θ3 ▹ El κ₃

-- the CONTEXT ford, right-hand side TRANSPORTED along κ₃
κ₄ : RTm ⌊ Θ4 ⌋
κ₄ = ⌜Id⌝ (⌜IMu⌝ CtxD INat (fst (var (vs (vs (vs (vs vz)))))))
          (fst (snd (var (vs (vs (vs (vs vz))))))) 
          (jsub (⌜IMu⌝ CtxD INat (var vz))
                (symN (fst (var (vs (vs (vs (vs vz))))))  (var vz))
                (Ctx-extK (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var (vs vz))))

Θ5 : Ctx
Θ5 = Θ4 ▹ El κ₄

-- the VARIABLE ford
κ₅ : RTm ⌊ Θ5 ⌋
κ₅ = ⌜Id⌝ (⌜IMu⌝ KnotD IPair (pair sVar (fst (var (vs (vs (vs (vs (vs vz)))))))))
          (fst (snd (snd (var (vs (vs (vs (vs (vs vz))))))))) 
          (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                (symN (fst (var (vs (vs (vs (vs (vs vz)))))))  (var (vs vz)))
                (Var-vzK (var (vs (vs (vs (vs vz)))))))

Θ6 : Ctx
Θ6 = Θ5 ▹ El κ₅

-- ★ the TYPE ford — its right-hand side is `wkK`, which is why step 2 had
--   to land before step 1 could be written at all.
κ₆ : RTm ⌊ Θ6 ⌋
κ₆ = ⌜Id⌝ (⌜IMu⌝ KnotD IPair (pair sTy (fst (var (vs (vs (vs (vs (vs (vs vz)))))))))) 
          (snd (snd (snd (var (vs (vs (vs (vs (vs (vs vz)))))))))) 
          (jsub (⌜IMu⌝ KnotD IPair (pair sTy (var vz)))
                (symN (fst (var (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs vz))))
                (wkK (pair sTy (var (vs (vs (vs (vs (vs vz)))))))
                     (var (vs (vs (vs vz))))))

C₆ : ICon ⌊ Θ6 ⌋
C₆ = iκ κ₆ iι
C₅ : ICon ⌊ Θ5 ⌋
C₅ = iκ κ₅ C₆
C₄ : ICon ⌊ Θ4 ⌋
C₄ = iκ κ₄ C₅
C₃ : ICon ⌊ Θ3 ⌋
C₃ = iκ κ₃ C₄
C₂ : ICon ⌊ Θ2 ⌋
C₂ = iκ κ₂ C₃
C₁ : ICon ⌊ Θ1 ⌋
C₁ = iκ κ₁ C₂

lkHere : ICon (ε ∙)
lkHere = iκ κ₀ C₁

------------------------------------------------------------------------
-- 3. ★ ONE WELL-FORMEDNESS LEMMA PER FIELD, innermost first.
--
-- `D` is a PARAMETER: `IConWf` uses it only at `iwf-ρ`, and `here` has no
-- recursive field, so none of these needs redoing when `there` joins the
-- description.
------------------------------------------------------------------------

W₆ : (D : IDesc) → IConWf D ILk Θ6 C₆
W₆ D =
  iwf-κ κ₆ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ KnotWf
              (⊢ixP ⊢sTy (⊢fst (⊢var (there (there (there (there (there (there here))))))))))
           (toKn (⊢snd (⊢snd (⊢snd
              (⊢var (there (there (there (there (there (there here)))))))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (there (there (there (there (there here)))))))))
                  (toI (⊢fst (⊢var (there (there (there (there (there (there here)))))))))
                  (⊢symN (⊢fst (⊢var (there (there (there (there (there (there here))))))))
                         (⊢nsuc (fromI (⊢var (there (there (there (there (there here))))))))
                         (fordAs (⊢var (there (there here)))))
                  (toKn (kFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
                          (kFwd (ξ-pairˡ (βfst _ _))
                            (⊢wkK (⊢ixP ⊢sTy
                                     (fromI (⊢var (there (there (there (there (there here))))))))
                                  (fromKn (⊢var (there (there (there here)))))))))))
    iwf-ι

W₅ : (D : IDesc) → IConWf D ILk Θ5 C₅
W₅ D =
  iwf-κ κ₅ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ KnotWf
              (⊢ixP ⊢sVar (⊢fst (⊢var (there (there (there (there (there here)))))))))
           (toKn (⊢fst (⊢snd (⊢snd
              (⊢var (there (there (there (there (there here))))))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (there (there (there (there here))))))))
                  (toI (⊢fst (⊢var (there (there (there (there (there here))))))))
                  (⊢symN (⊢fst (⊢var (there (there (there (there (there here)))))))
                         (⊢nsuc (fromI (⊢var (there (there (there (there here)))))))
                         (fordAs (⊢var (there here))))
                  (toKn (⊢Var-vzKv
                           (fromI (⊢var (there (there (there (there here))))))))))
    (W₆ D)

W₄ : (D : IDesc) → IConWf D ILk Θ4 C₄
W₄ D =
  iwf-κ κ₄ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ CtxWf
              (toI (⊢fst (⊢var (there (there (there (there here))))))))
           (toCn (⊢fst (⊢snd (⊢var (there (there (there (there here))))))))
           (⊢jsub (⊢⌜IMu⌝ CtxWf (⊢var here))
                  (toI (⊢nsuc (fromI (⊢var (there (there (there here)))))))
                  (toI (⊢fst (⊢var (there (there (there (there here)))))))
                  (⊢symN (⊢fst (⊢var (there (there (there (there here))))))
                         (⊢nsuc (fromI (⊢var (there (there (there here))))))
                         (fordAs (⊢var here)))
                  (toCn (⊢Ctx-extKv
                           (fromI (⊢var (there (there (there here)))))
                           (fromCn (⊢var (there (there here))))
                           (fromKn (⊢var (there here)))))))
    (W₅ D)

W₃ : (D : IDesc) → IConWf D ILk Θ3 C₃
W₃ D =
  iwf-κ κ₃ (icw-ford _ _ _)
    (⊢⌜Id⌝ ⊢⌜Nat⌝
      (toI (⊢fst (⊢var (there (there (there here))))))
      (toI (⊢nsuc (fromI (⊢var (there (there here)))))))
    (W₄ D)

W₂ : (D : IDesc) → IConWf D ILk Θ2 C₂
W₂ D =
  iwf-κ κ₂ (icw-imu (pair sTy (var (vs vz))) KnotWf)
    (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (there here)))))
    (W₃ D)

W₁ : (D : IDesc) → IConWf D ILk Θ1 C₁
W₁ D =
  iwf-κ κ₁ (icw-imu (var vz) CtxWf) (⊢⌜IMu⌝ CtxWf (⊢var here)) (W₂ D)

-- ★★★ `here` IS WELL FORMED.
lkHereWf : (D : IDesc) → IConWf D ILk Θ0 lkHere
lkHereWf D = iwf-κ κ₀ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝ (W₁ D)
