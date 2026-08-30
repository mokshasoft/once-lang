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
open import normalizer.Syntax.Types using ( _≡_; refl; sym )
open import Agda.Builtin.Nat using ( zero; suc )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; RTy; RTm; Nat; Σ'; El; U; IMu; pair
        ; fst; snd; nsuc; nzero; unit; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; jsub; icon; idrefl
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_; _∈ID_; hereID
        ; isingle; iext; extS; subTm; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢conv; ⊢fst; ⊢snd; ⊢nsuc; ⊢pair; ⊢unit; ⊢icon; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢jsub
        ; ty-Nat; ty-Unit; ty-Σ; ty-IMu; ⊢nzero
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; IDescWf; idwf-nil; idwf-cons
        ; _≅ᵀ_; csymᵀ; credᵀ; El-⌜IMu⌝; ξ-IMu; ξ-El
        ; _⟶_; _⟶*_; done; step; βfst; βsnd; ξ-fst; ξ-snd
        ; ξ-pairˡ; ξ-pairʳ; ξ-nsuc
        ; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-⌜IMu⌝; El-⌜Id⌝; ⊢idrefl )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sVar; ⊢sTy; ⊢sVar; toI; fromI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN; elIdN )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( ⊢wk; ⊢-cast; Sub⊢; Sub⊢-ext; isingle-Sub⊢; iext-Sub⊢ )
open import DirectedHoTT.Lib.IPay using ( ipayTy-wf )
open import DirectedHoTT.Lib.IWk using ( payStep )
open import DirectedHoTT.Examples.WkFin using ( transport-fires )
open import DirectedHoTT.Examples.Knot.CtxD
  using ( CtxD; CtxK; CtxWf; INat; Ctx-extK; ⊢Ctx-extKv
        ; Ctx-empK; ⊢Ctx-empK; ⊢Ctx-extK )
open import DirectedHoTT.Examples.Knot.Build
  using ( Var-vzK; ⊢Var-vzK; ⊢Var-vzKv; Var-vsK; ⊢Var-vsKv )
open import DirectedHoTT.Examples.Knot.Wk using ( wkK; ⊢wkK )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-NatK; ⊢Ty-NatK )

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
--   `IMu …`.  One `El-⌜IMu⌝` each way.
------------------------------------------------------------------------

-- ★ ALL FOUR NOW LIVE IN `Lib/ICast`, stated in terms of
--   the CODE alone, with the description and its index type IMPLICIT.
--   ⚠ `toCn`/`toKn` were the SAME function, as were `fromCn`/`fromKn` —
--   `El-⌜IMu⌝` does not care which description it unfolds.
open import DirectedHoTT.Lib.ICast public
  using ( toMu; fromMu; fordAs; muFwd )

-- ⚠ THE TELESCOPES AND THE CODES INTERLEAVE, and they must: `κₖ` lives in
--   `⌊ Θₖ ⌋` and `Θₖ₊₁` is `Θₖ ▹ El κₖ`.  A context-POLYMORPHIC `κ` cannot
--   work — `var (vs (vs (vs vz)))` needs a `Cx` at least four deep, so the
--   context has to be concrete at each step.

-- ⚠ `εwkTy ILk`, NOT `ILk`, even though they are definitionally equal.
--   `isingle-Sub⊢`'s conclusion is at `◇ ▹ εwkTy I`, and solving `I` from
--   `εwkTy I ≟ ILk` asks Agda to invert a DEFINED function — it will not
--   (`pin-implicits-on-defined-set-types`).  Writing the telescope in the
--   form the lemma states it in is what makes `I` solvable.
Θ0 : Ctx
Θ0 = ◇ ▹ εwkTy ILk

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
           (toMu (⊢snd (⊢snd (⊢snd
              (⊢var (there (there (there (there (there (there here)))))))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (there (there (there (there (there here)))))))))
                  (toI (⊢fst (⊢var (there (there (there (there (there (there here)))))))))
                  (⊢symN (⊢fst (⊢var (there (there (there (there (there (there here))))))))
                         (⊢nsuc (fromI (⊢var (there (there (there (there (there here))))))))
                         (fordAs (⊢var (there (there here)))))
                  (toMu (muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
                          (muFwd (ξ-pairˡ (βfst _ _))
                            (⊢wkK (⊢ixP ⊢sTy
                                     (fromI (⊢var (there (there (there (there (there here))))))))
                                  (fromMu (⊢var (there (there (there here)))))))))))
    iwf-ι

W₅ : (D : IDesc) → IConWf D ILk Θ5 C₅
W₅ D =
  iwf-κ κ₅ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ KnotWf
              (⊢ixP ⊢sVar (⊢fst (⊢var (there (there (there (there (there here)))))))))
           (toMu (⊢fst (⊢snd (⊢snd
              (⊢var (there (there (there (there (there here))))))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (there (there (there (there here))))))))
                  (toI (⊢fst (⊢var (there (there (there (there (there here))))))))
                  (⊢symN (⊢fst (⊢var (there (there (there (there (there here)))))))
                         (⊢nsuc (fromI (⊢var (there (there (there (there here)))))))
                         (fordAs (⊢var (there here))))
                  (toMu (⊢Var-vzKv
                           (fromI (⊢var (there (there (there (there here))))))))))
    (W₆ D)

W₄ : (D : IDesc) → IConWf D ILk Θ4 C₄
W₄ D =
  iwf-κ κ₄ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ CtxWf
              (toI (⊢fst (⊢var (there (there (there (there here))))))))
           (toMu (⊢fst (⊢snd (⊢var (there (there (there (there here))))))))
           (⊢jsub (⊢⌜IMu⌝ CtxWf (⊢var here))
                  (toI (⊢nsuc (fromI (⊢var (there (there (there here)))))))
                  (toI (⊢fst (⊢var (there (there (there (there here)))))))
                  (⊢symN (⊢fst (⊢var (there (there (there (there here))))))
                         (⊢nsuc (fromI (⊢var (there (there (there here))))))
                         (fordAs (⊢var here)))
                  (toMu (⊢Ctx-extKv
                           (fromI (⊢var (there (there (there here)))))
                           (fromMu (⊢var (there (there here))))
                           (fromMu (⊢var (there here)))))))
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

------------------------------------------------------------------------
-- 4. `there` — the same shape plus ONE RECURSIVE FIELD.
--
--     there : Γ ∋ x ∷ A → (Γ ▹ B) ∷ vs x ∷ renTy vs A
--
-- ⚠ Ten fields: five bound values, the recursive premise, and the same
--   four fords `here` has — with the same three transports.  ★ The
--   recursive field is the only genuinely new thing, and its index is the
--   FOUR-TUPLE `(m, Γ, x, A)`, i.e. the telescope §1 built.
------------------------------------------------------------------------

Ξ0 : Ctx
Ξ0 = ◇ ▹ εwkTy ILk

λ₀ : RTm ⌊ Ξ0 ⌋
λ₀ = ⌜Nat⌝                                          -- m

Ξ1 : Ctx
Ξ1 = Ξ0 ▹ El λ₀

λ₁ : RTm ⌊ Ξ1 ⌋
λ₁ = ⌜IMu⌝ CtxD INat (var vz)                       -- Γ : Ctx m

Ξ2 : Ctx
Ξ2 = Ξ1 ▹ El λ₁

λ₂ : RTm ⌊ Ξ2 ⌋
λ₂ = ⌜IMu⌝ KnotD IPair (pair sVar (var (vs vz)))    -- x : Var m

Ξ3 : Ctx
Ξ3 = Ξ2 ▹ El λ₂

λ₃ : RTm ⌊ Ξ3 ⌋
λ₃ = ⌜IMu⌝ KnotD IPair (pair sTy (var (vs (vs vz))))   -- A : RTy m

Ξ4 : Ctx
Ξ4 = Ξ3 ▹ El λ₃

λ₄ : RTm ⌊ Ξ4 ⌋
λ₄ = ⌜IMu⌝ KnotD IPair (pair sTy (var (vs (vs (vs vz)))))  -- B : RTy m

Ξ5 : Ctx
Ξ5 = Ξ4 ▹ El λ₄

-- ★ THE RECURSIVE PREMISE, at the four-component index `(m, Γ, x, A)`.
ρ₅ : RTm ⌊ Ξ5 ⌋
ρ₅ = pair (var (vs (vs (vs (vs vz)))))
          (pair (var (vs (vs (vs vz))))
            (pair (var (vs (vs vz))) (var (vs vz))))

-- ⚠ FROM HERE THE CONTEXTS ARE `Cx`, NOT `Ctx`, and that is forced: the
--   recursive field extends the telescope by `IMu LkD ILk ρ₅`, which
--   mentions the description being DEFINED.  ⌊_⌋ only COUNTS, so the
--   codes after it can be typed at a plain `Cx` and the row stays
--   definable before `LkD` exists.  The `Ctx`-level telescopes come back
--   in §5, where `LkD` is available.
X6 X7 X8 X9 : Cx
X6 = ⌊ Ξ5 ⌋ ∙
X7 = X6 ∙
X8 = X7 ∙
X9 = X8 ∙

-- the DEPTH ford, `fst ⟨i⟩ ≡ suc m`
λ₆ : RTm X6
λ₆ = ⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs (vs (vs (vs (vs vz))))))))
                (nsuc (var (vs (vs (vs (vs (vs vz)))))))

-- the CONTEXT ford — target `Γ ▹ B`, transported along λ₆
λ₇ : RTm X7
λ₇ = ⌜Id⌝ (⌜IMu⌝ CtxD INat (fst (var (vs (vs (vs (vs (vs (vs (vs vz))))))))))
          (fst (snd (var (vs (vs (vs (vs (vs (vs (vs vz)))))))))) 
          (jsub (⌜IMu⌝ CtxD INat (var vz))
                (symN (fst (var (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var vz))
                (Ctx-extK (var (vs (vs (vs (vs (vs (vs vz)))))))
                          (var (vs (vs (vs (vs (vs vz))))))
                          (var (vs (vs vz)))))

-- the VARIABLE ford — target `vs x`
λ₈ : RTm X8
λ₈ = ⌜Id⌝ (⌜IMu⌝ KnotD IPair
             (pair sVar (fst (var (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))) 
          (fst (snd (snd (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))
          (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                (symN (fst (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))
                      (var (vs vz)))
                (Var-vsK (var (vs (vs (vs (vs (vs (vs (vs vz))))))))
                         (var (vs (vs (vs (vs (vs vz))))))))

-- the TYPE ford — target `wk A`
λ₉ : RTm X9
λ₉ = ⌜Id⌝ (⌜IMu⌝ KnotD IPair
             (pair sTy (fst (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))))) 
          (snd (snd (snd (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))))
          (jsub (⌜IMu⌝ KnotD IPair (pair sTy (var vz)))
                (symN (fst (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))))
                      (var (vs (vs vz))))
                (wkK (pair sTy (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))
                     (var (vs (vs (vs (vs (vs vz))))))))

lkThere : ICon (ε ∙)
lkThere =
  iκ λ₀ (iκ λ₁ (iκ λ₂ (iκ λ₃ (iκ λ₄
    (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι)))))))))

-- ★★★ THE DESCRIPTION.
LkD : IDesc
LkD = lkHere ◂ (lkThere ◂ inil)

Lk : {Γ : Cx} → RTm Γ → RTy Γ
Lk i = IMu LkD ILk i

------------------------------------------------------------------------
-- 5. `there`'s WELL-FORMEDNESS, one lemma per field.
--
-- ⚠ THE TELESCOPES ARE `Ctx` AGAIN HERE, because `LkD` now exists — and
--   Ξ6 is where the recursive premise enters, extending by
--   `IMu LkD ILk ρ₅` rather than by an `El`.
------------------------------------------------------------------------

Ξ6 Ξ7 Ξ8 Ξ9 : Ctx
Ξ6 = Ξ5 ▹ IMu LkD ILk ρ₅
Ξ7 = Ξ6 ▹ El λ₆
Ξ8 = Ξ7 ▹ El λ₇
Ξ9 = Ξ8 ▹ El λ₈

V₉ : IConWf LkD ILk Ξ9 (iκ λ₉ iι)
V₉ =
  iwf-κ λ₉ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ KnotWf
              (⊢ixP ⊢sTy (⊢fst (⊢var (there (there (there (there (there (there (there (there (there here)))))))))))))
           (toMu (⊢snd (⊢snd (⊢snd
              (⊢var (there (there (there (there (there (there (there (there (there here))))))))))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (there (there (there (there (there (there (there (there here)))))))))))) 
                  (toI (⊢fst (⊢var (there (there (there (there (there (there (there (there (there here))))))))))))
                  (⊢symN (⊢fst (⊢var (there (there (there (there (there (there (there (there (there here)))))))))))
                         (⊢nsuc (fromI (⊢var (there (there (there (there (there (there (there (there here))))))))))) 
                         (fordAs (⊢var (there (there here)))))
                  (toMu (muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
                          (muFwd (ξ-pairˡ (βfst _ _))
                            (⊢wkK (⊢ixP ⊢sTy
                                     (fromI (⊢var (there (there (there (there (there (there (there (there here)))))))))))
                                  (fromMu (⊢var (there (there (there (there (there here)))))))))))))
    iwf-ι

V₈ : IConWf LkD ILk Ξ8 (iκ λ₈ (iκ λ₉ iι))
V₈ =
  iwf-κ λ₈ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ KnotWf
              (⊢ixP ⊢sVar (⊢fst (⊢var (there (there (there (there (there (there (there (there here))))))))))))
           (toMu (⊢fst (⊢snd (⊢snd
              (⊢var (there (there (there (there (there (there (there (there here)))))))))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (there (there (there (there (there (there (there here))))))))))) 
                  (toI (⊢fst (⊢var (there (there (there (there (there (there (there (there here)))))))))))
                  (⊢symN (⊢fst (⊢var (there (there (there (there (there (there (there (there here))))))))))
                         (⊢nsuc (fromI (⊢var (there (there (there (there (there (there (there here)))))))))) 
                         (fordAs (⊢var (there here))))
                  (toMu (⊢Var-vsKv
                           (fromI (⊢var (there (there (there (there (there (there (there here)))))))))
                           (fromMu (⊢var (there (there (there (there (there here)))))))))))
    V₉

V₇ : IConWf LkD ILk Ξ7 (iκ λ₇ (iκ λ₈ (iκ λ₉ iι)))
V₇ =
  iwf-κ λ₇ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ CtxWf
              (toI (⊢fst (⊢var (there (there (there (there (there (there (there here)))))))))))
           (toMu (⊢fst (⊢snd (⊢var (there (there (there (there (there (there (there here))))))))))) 
           (⊢jsub (⊢⌜IMu⌝ CtxWf (⊢var here))
                  (toI (⊢nsuc (fromI (⊢var (there (there (there (there (there (there here)))))))))) 
                  (toI (⊢fst (⊢var (there (there (there (there (there (there (there here))))))))))
                  (⊢symN (⊢fst (⊢var (there (there (there (there (there (there (there here)))))))))
                         (⊢nsuc (fromI (⊢var (there (there (there (there (there (there here))))))))) 
                         (fordAs (⊢var here)))
                  (toMu (⊢Ctx-extKv
                           (fromI (⊢var (there (there (there (there (there (there here))))))))
                           (fromMu (⊢var (there (there (there (there (there here)))))))
                           (fromMu (⊢var (there (there here))))))))
    V₈

V₆ : IConWf LkD ILk Ξ6 (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι))))
V₆ =
  iwf-κ λ₆ (icw-ford _ _ _)
    (⊢⌜Id⌝ ⊢⌜Nat⌝
      (toI (⊢fst (⊢var (there (there (there (there (there (there here)))))))))
      (toI (⊢nsuc (fromI (⊢var (there (there (there (there (there here)))))))))) 
    V₇

-- ★ THE RECURSIVE PREMISE.  Its index is the four-tuple `(m, Γ, x, A)`.
-- ★ THE RECURSIVE PREMISE.  Its index is the four-tuple `(m, Γ, x, A)` —
--   the telescope §1 built, now carrying actual field values.
--
-- ⚠ `⊢pair`'s FIRST argument is the ⊢ty of the TAIL, not of the head.
V₅ : IConWf LkD ILk Ξ5 (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι)))))
V₅ =
  iwf-ρ ρ₅
    (⊢pair (ty-Σ (ty-IMu CtxWf (toI (⊢var here)))
             (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here))))
                   (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (there (there here)))))))
           (fromI (⊢var (there (there (there (there here))))))
      (⊢pair (ty-Σ (ty-IMu KnotWf
                     (⊢ixP ⊢sVar (⊢wk (fromI (⊢var (there (there (there (there here)))))))))
                   (ty-IMu KnotWf
                     (⊢ixP ⊢sTy (⊢wk (⊢wk (fromI (⊢var (there (there (there (there here))))))))))) 
             (fromMu (⊢var (there (there (there here)))))
        (⊢pair (ty-IMu KnotWf
                 (⊢ixP ⊢sTy (⊢wk (fromI (⊢var (there (there (there (there here)))))))))
               (fromMu (⊢var (there (there here))))
               (fromMu (⊢var (there here))))))
    V₆

V₄ : IConWf LkD ILk Ξ4 (iκ λ₄ (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι))))))
V₄ =
  iwf-κ λ₄ (icw-imu (pair sTy (var (vs (vs (vs vz))))) KnotWf)
    (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (there (there (there here)))))))
    V₅

V₃ : IConWf LkD ILk Ξ3 (iκ λ₃ (iκ λ₄ (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι)))))))
V₃ =
  iwf-κ λ₃ (icw-imu (pair sTy (var (vs (vs vz)))) KnotWf)
    (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (there (there here))))))
    V₄

V₂ : IConWf LkD ILk Ξ2
       (iκ λ₂ (iκ λ₃ (iκ λ₄ (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι))))))))
V₂ =
  iwf-κ λ₂ (icw-imu (pair sVar (var (vs vz))) KnotWf)
    (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (fromI (⊢var (there here)))))
    V₃

V₁ : IConWf LkD ILk Ξ1
       (iκ λ₁ (iκ λ₂ (iκ λ₃ (iκ λ₄ (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι)))))))))
V₁ =
  iwf-κ λ₁ (icw-imu (var vz) CtxWf) (⊢⌜IMu⌝ CtxWf (⊢var here)) V₂

-- ★★★ `there` IS WELL FORMED.
lkThereWf : IConWf LkD ILk Ξ0 lkThere
lkThereWf = iwf-κ λ₀ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝ V₁

------------------------------------------------------------------------
-- 6. ★★★ THE JUDGEMENT IS A WELL-FORMED INDEXED DESCRIPTION.
--
--     `_∋_∷_` — two constructors, a four-component dependent index over
--     TWO different `IMu`s, and six Fording transports between them.
--
-- `PLAN-JUDGEMENT` step 1, and the first RELATION over encoded syntax.
------------------------------------------------------------------------

LkWf : IDescWf ILk LkD
LkWf = idwf-cons (lkHereWf LkD) (idwf-cons lkThereWf idwf-nil)

------------------------------------------------------------------------
-- 7. ⚠⚠ AND IT IS INHABITED — without this, §6 is
--    `verification-that-covers-less-than-it-claims`.
--
-- A description can be well formed and have NO closed inhabitant at any
-- index — `Examples/Vec.no-cons-at-zero` is that hazard proved on
-- purpose, and `Knot/Terms` exists for exactly this reason on the syntax
-- side.  Six Fording constraints is plenty of rope.
--
-- ★ THE WITNESS: `(◇ ▹ Nat) ∋ vz ∷ renTy vs Nat`, encoded — the smallest
--   `here`.  At a CONCRETE index every ford witness is an `idrefl`, and
--   ★★ the three TRANSPORTS EVAPORATE: `jsub d (symN a (idrefl …)) e ⟶* e`
--   in two steps (`Examples/WkFin.transport-fires`).  ⇒ the transports
--   that §2 pays in the DERIVATION cost nothing at runtime, which is
--   `PLAN-JUDGEMENT` §1's claim, now exercised at a judgement.
------------------------------------------------------------------------

-- one conversion step on each part of a Fording constraint
idCᶜ : {Γ : Ctx} {c c' a b t : RTm ⌊ Γ ⌋} → c ⟶ c' →
       Γ ⊢ t ∷ El (⌜Id⌝ c' a b) → Γ ⊢ t ∷ El (⌜Id⌝ c a b)
idCᶜ r d = ⊢conv d (csymᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ᶜ r))))

idCˡ : {Γ : Ctx} {c a a' b t : RTm ⌊ Γ ⌋} → a ⟶ a' →
       Γ ⊢ t ∷ El (⌜Id⌝ c a' b) → Γ ⊢ t ∷ El (⌜Id⌝ c a b)
idCˡ r d = ⊢conv d (csymᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ˡ r))))

idCʳ : {Γ : Ctx} {c a b b' t : RTm ⌊ Γ ⌋} → b ⟶ b' →
       Γ ⊢ t ∷ El (⌜Id⌝ c a b') → Γ ⊢ t ∷ El (⌜Id⌝ c a b)
idCʳ r d = ⊢conv d (csymᵀ (credᵀ (ξ-El (ξ-⌜Id⌝ʳ r))))

-- ★ …and their MULTI-STEP versions, so `WkFin.transport-fires` (a `⟶*`)
--   can be used as it stands.
idCᶜ* : {Γ : Ctx} {c c' a b t : RTm ⌊ Γ ⌋} → c ⟶* c' →
        Γ ⊢ t ∷ El (⌜Id⌝ c' a b) → Γ ⊢ t ∷ El (⌜Id⌝ c a b)
idCᶜ* done        d = d
idCᶜ* (step r rs) d = idCᶜ r (idCᶜ* rs d)

idCˡ* : {Γ : Ctx} {c a a' b t : RTm ⌊ Γ ⌋} → a ⟶* a' →
        Γ ⊢ t ∷ El (⌜Id⌝ c a' b) → Γ ⊢ t ∷ El (⌜Id⌝ c a b)
idCˡ* done        d = d
idCˡ* (step r rs) d = idCˡ r (idCˡ* rs d)

idCʳ* : {Γ : Ctx} {c a b b' t : RTm ⌊ Γ ⌋} → b ⟶* b' →
        Γ ⊢ t ∷ El (⌜Id⌝ c a b') → Γ ⊢ t ∷ El (⌜Id⌝ c a b)
idCʳ* done        d = d
idCʳ* (step r rs) d = idCʳ r (idCʳ* rs d)

-- `idrefl c v` at the constraint both of whose sides reduce to `v`
reflAt : {Γ : Ctx} {c v : RTm ⌊ Γ ⌋} →
         Γ ⊢ c ∷ U → Γ ⊢ v ∷ El c →
         Γ ⊢ idrefl c v ∷ El (⌜Id⌝ c v v)
reflAt {c = c} {v = v} dc dv =
  ⊢conv (⊢idrefl dc dv) (csymᵀ (credᵀ (El-⌜Id⌝ c v v)))

-- the index: `(1, ◇ ▹ Nat, vz, wk Nat)`
i₀ : {Γ : Cx} → RTm Γ
i₀ = pair (nsuc nzero)
       (pair (Ctx-extK nzero Ctx-empK Ty-NatK)
         (pair (Var-vzK nzero) (wkK (pair sTy nzero) Ty-NatK)))

-- ⚠ RESTATED, not `∷ ILk`: `ILk` is pinned at `RTy ε` because that is
--   what `IMu` takes, and a derivation needs it at an arbitrary `Δ`.
--   Same move as `⊢ILk`.
⊢i₀ : {Δ : Ctx} → Δ ⊢ i₀ ∷
      Σ' Nat
        (Σ' (CtxK (var vz))
          (Σ' (K (pair sVar (var (vs vz))))
              (K (pair sTy (var (vs (vs vz)))))))
⊢i₀ =
  ⊢pair (ty-Σ (ty-IMu CtxWf (toI (⊢var here)))
          (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here))))
                (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (there (there here)))))))
        (⊢nsuc ⊢nzero)
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢nsuc ⊢nzero)))
                 (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢nsuc ⊢nzero))))
           (⊢Ctx-extK 0 ⊢Ctx-empK (⊢Ty-NatK 0))
      (⊢pair (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢nsuc ⊢nzero)))
             (⊢Var-vzK 0)
             (muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
               (muFwd (ξ-pairˡ (βfst _ _))
                 (⊢wkK (⊢ixP ⊢sTy ⊢nzero) (⊢Ty-NatK 0))))))


lkVz : {Γ : Cx} → RTm Γ
lkVz = icon zero
  (pair nzero
    (pair Ctx-empK
      (pair Ty-NatK
        (pair (idrefl ⌜Nat⌝ (nsuc nzero))
          (pair (idrefl (⌜IMu⌝ CtxD INat (nsuc nzero))
                        (Ctx-extK nzero Ctx-empK Ty-NatK))
            (pair (idrefl (⌜IMu⌝ KnotD IPair (pair sVar (nsuc nzero)))
                          (Var-vzK nzero))
              (pair (idrefl (⌜IMu⌝ KnotD IPair (pair sTy (nsuc nzero)))
                            (wkK (pair sTy nzero) Ty-NatK))
                    unit)))))))

-- ⚠ AND `ipayTy-wf`'s `Θ` IS PINNED.  It is a `Ctx` reached only through
--   `⌊ Θ ⌋` in the explicit arguments, and `⌊_⌋` is not injective — the
--   hazard `Lib/IFold` records from the other side.  Left implicit the
--   constraint comes back "blocked on _i".
--
-- ⚠ THE ENVIRONMENTS ARE NAMED, not `_`.  `ipayTy-wf` and `payStep` both
--   take the substitution explicitly, and it is not inferable from the
--   result — `subTm σ` is a defined function, so the constraint comes
--   back "blocked on _σ" (`pin-implicits-on-defined-set-types` again).
⊢lkVz : {Δ : Ctx} → Δ ⊢ lkVz ∷ Lk i₀
⊢lkVz {Δ = Δ} =
  ⊢icon LkWf hereID ⊢i₀
    (⊢pair (ipayTy-wf {Θ = Θ1} LkD ILk (extS σ₀) C₁ LkWf (W₁ LkD) (Sub⊢-ext h0))
           (toI ⊢nzero)
      (⊢-cast (sym (payStep LkD ILk σ₀ nzero C₁))
        (⊢pair (ipayTy-wf {Θ = Θ2} LkD ILk (extS σ₁) C₂ LkWf (W₂ LkD) (Sub⊢-ext h1))
               (toMu ⊢Ctx-empK)
          (⊢-cast (sym (payStep LkD ILk σ₁ Ctx-empK C₂))
            (⊢pair (ipayTy-wf {Θ = Θ3} LkD ILk (extS σ₂) C₃ LkWf (W₃ LkD) (Sub⊢-ext h2))
                   (toMu (⊢Ty-NatK 0))
              (⊢-cast (sym (payStep LkD ILk σ₂ Ty-NatK C₃))
                (⊢pair (ipayTy-wf {Θ = Θ4} LkD ILk (extS σ₃) C₄ LkWf (W₄ LkD) (Sub⊢-ext h3))
                       f₃
                  (⊢-cast (sym (payStep LkD ILk σ₃ v₃ C₄))
                    (⊢pair (ipayTy-wf {Θ = Θ5} LkD ILk (extS σ₄) C₅ LkWf (W₅ LkD) (Sub⊢-ext h4))
                           f₄
                      (⊢-cast (sym (payStep LkD ILk σ₄ v₄ C₅))
                        (⊢pair (ipayTy-wf {Θ = Θ6} LkD ILk (extS σ₅) C₆ LkWf (W₆ LkD) (Sub⊢-ext h5))
                               f₅
                          (⊢-cast (sym (payStep LkD ILk σ₅ v₅ C₆))
                            (⊢pair ty-Unit f₆ ⊢unit)))))))))))))
  where
    v₃ = idrefl ⌜Nat⌝ (nsuc nzero)
    v₄ = idrefl (⌜IMu⌝ CtxD INat (nsuc nzero)) (Ctx-extK nzero Ctx-empK Ty-NatK)
    v₅ = idrefl (⌜IMu⌝ KnotD IPair (pair sVar (nsuc nzero))) (Var-vzK nzero)
    σ₀ = isingle i₀
    σ₁ = iext σ₀ nzero
    σ₂ = iext σ₁ Ctx-empK
    σ₃ = iext σ₂ Ty-NatK
    σ₄ = iext σ₃ v₃
    σ₅ = iext σ₄ v₄
    σ₆ = iext σ₅ v₅
    v₆ = idrefl (⌜IMu⌝ KnotD IPair (pair sTy (nsuc nzero)))
                (wkK (pair sTy nzero) Ty-NatK)
    -- ⚠ `{I = ILk}` PINNED: `isingle-Sub⊢`'s conclusion mentions `I` only
    --   under `εwkTy`, a DEFINED function, so it never solves on its own.
    h0 : Sub⊢ Θ0 Δ σ₀
    h0 = isingle-Sub⊢ {I = ILk} ⊢i₀
    h1 = iext-Sub⊢ h0 (toI ⊢nzero)
    h2 = iext-Sub⊢ h1 (toMu ⊢Ctx-empK)
    h3 = iext-Sub⊢ h2 (toMu (⊢Ty-NatK 0))
    -- the DEPTH ford: both sides reduce to `suc 0`
    f₃ : Δ ⊢ v₃ ∷ El (subTm σ₃ κ₃)
    f₃ = idCˡ (βfst _ _) (reflAt ⊢⌜Nat⌝ (toI (⊢nsuc ⊢nzero)))
    h4 = iext-Sub⊢ h3 f₃
    -- ★ the CONTEXT ford, and ★★ THE TRANSPORT EVAPORATES: at a concrete
    --   index the ford witness IS an `idrefl`, so `transport-fires`
    --   collapses the `jsub` in two steps.
    f₄ : Δ ⊢ v₄ ∷ El (subTm σ₄ κ₄)
    f₄ = idCᶜ (ξ-⌜IMu⌝ (βfst _ _))
          (idCˡ* (step (ξ-fst (βsnd _ _)) (step (βfst _ _) done))
            (idCʳ* (transport-fires _ _ _ _)
              (reflAt (⊢⌜IMu⌝ CtxWf (toI (⊢nsuc ⊢nzero)))
                      (toMu (⊢Ctx-extK 0 ⊢Ctx-empK (⊢Ty-NatK 0))))))
    h5 = iext-Sub⊢ h4 f₄
    f₅ : Δ ⊢ v₅ ∷ El (subTm σ₅ κ₅)
    f₅ = idCᶜ (ξ-⌜IMu⌝ (ξ-pairʳ (βfst _ _)))
          (idCˡ* (step (ξ-fst (ξ-snd (βsnd _ _)))
                   (step (ξ-fst (βsnd _ _)) (step (βfst _ _) done)))
            (idCʳ* (transport-fires _ _ _ _)
              (reflAt (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (⊢nsuc ⊢nzero)))
                      (toMu (⊢Var-vzK 0)))))
    f₆ : Δ ⊢ v₆ ∷ El (subTm σ₆ κ₆)
    f₆ = idCᶜ (ξ-⌜IMu⌝ (ξ-pairʳ (βfst _ _)))
          (idCˡ* (step (ξ-snd (ξ-snd (βsnd _ _)))
                   (step (ξ-snd (βsnd _ _)) (step (βsnd _ _) done)))
            (idCʳ* (transport-fires _ _ _ _)
              (reflAt (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (⊢nsuc ⊢nzero)))
                      (toMu (muFwd (ξ-pairʳ (ξ-nsuc (βsnd _ _)))
                              (muFwd (ξ-pairˡ (βfst _ _))
                                (⊢wkK (⊢ixP ⊢sTy ⊢nzero) (⊢Ty-NatK 0))))))))
