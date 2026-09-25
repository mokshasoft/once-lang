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
open import DirectedHoTT.Lib.Lkp using ( ∋lkp; vsⁿ )
open import normalizer.Syntax.Types using ( _≡_; refl; sym )
open import Agda.Builtin.Nat using ( zero; suc )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; RTy; RTm; Nat; Σ'; El; U; IMu; pair
        ; fst; snd; nsuc; nzero; unit; ⌜Nat⌝; ⌜Id⌝; ⌜IMu⌝; jsub; icon; idrefl
        ; ICon; IDesc; iι; iρ; iκ; inil; _◂_; _∈ID_; hereID
        ; isingle; iext; extS; subTm; εwkTy; app; renTm; thinR; keep )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢conv; ⊢fst; ⊢snd; ⊢nsuc; ⊢pair; ⊢unit; ⊢icon; ⊢⌜Nat⌝; ⊢⌜Id⌝; ⊢⌜IMu⌝; ⊢jsub
        ; ty-Nat; ty-Unit; ty-Σ; ty-IMu; ⊢nzero
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ; ICodeWf; icw-clo; icw-ford; icw-imu
        ; IDescWf; idwf-nil; idwf-cons; _,,_; Θ₀; ρ₀; x₀
        ; _≅ᵀ_; csymᵀ; credᵀ; El-⌜IMu⌝; ξ-IMu; ξ-El
        ; _⟶_; _⟶*_; done; step; βfst; βsnd; ξ-fst; ξ-snd
        ; ξ-pairˡ; ξ-pairʳ; ξ-nsuc
        ; ξ-⌜Id⌝ᶜ; ξ-⌜Id⌝ˡ; ξ-⌜Id⌝ʳ; ξ-⌜IMu⌝; El-⌜Id⌝; ⊢idrefl )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sVar; ⊢sTy; ⊢sVar; toI; fromI; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Lib.ArithComm using ( IdN; symN; ⊢symN; elIdN )
open import DirectedHoTT.Metatheory.TySub
  using ( ⊢wk; ⊢-cast; xenv₀; xenv-κ )
open import DirectedHoTT.Lib.IPay using ( ⊢payκ )
open import DirectedHoTT.Examples.WkFin using ( transport-fires )
open import DirectedHoTT.Examples.Knot.CtxD
  using ( CtxD; CtxK; CtxWf; INat; Ctx-extK; ⊢Ctx-extKv
        ; Ctx-empK; ⊢Ctx-empK; ⊢Ctx-extK )
open import DirectedHoTT.Examples.Knot.Build
  using ( Var-vzK; ⊢Var-vzK; ⊢Var-vzKv; Var-vsK; ⊢Var-vsKv )
-- ⚠⚠ `wkTyK`, NOT `wkK`, FOR THE ROW'S `renTy vs A`.  `A` is a bound
--   FIELD standing for an arbitrary type, hence OPEN, and the two
--   weakenings differ on exactly those (`PLAN-RENAMING.md` §0).  The
--   ★ AND THE EXAMPLE INSTANTIATION FORCED THE ISSUE: the row and its
--   consumer must name the SAME weakening, so converting the row made
--   the example fail until it was converted too.  Libraries exercised by
--   examples, paying again.
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK; ⊢wkTyK )
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
            (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (∋lkp _ (vsⁿ 2 vz)))))))

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
                (wkTyK (var (vs (vs (vs (vs (vs vz))))))
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

-- ★ A-MATH: the TELESCOPE `here` is typed in — the abstract family, the
--   index, then each code read through the thinning that skips the family.
TΘ0 TΘ1 TΘ2 TΘ3 TΘ4 TΘ5 TΘ6 : Ctx
TΘ0 = Θ₀ ILk
TΘ1 = TΘ0 ▹ El (renTm (thinR (ρ₀)) κ₀)
TΘ2 = TΘ1 ▹ El (renTm (thinR (keep ρ₀)) κ₁)
TΘ3 = TΘ2 ▹ El (renTm (thinR (keep (keep ρ₀))) κ₂)
TΘ4 = TΘ3 ▹ El (renTm (thinR (keep (keep (keep ρ₀)))) κ₃)
TΘ5 = TΘ4 ▹ El (renTm (thinR (keep (keep (keep (keep ρ₀))))) κ₄)
TΘ6 = TΘ5 ▹ El (renTm (thinR (keep (keep (keep (keep (keep ρ₀)))))) κ₅)

------------------------------------------------------------------------
-- 3. ★ ONE WELL-FORMEDNESS LEMMA PER FIELD, innermost first.
--
-- ★ A-MATH: `IConWf` names no description at all, so neither `here` nor
--   `there` needs one — each lemma is proved once, at its telescope.
------------------------------------------------------------------------

W₆ : IConWf ILk TΘ6 (keep (keep (keep (keep (keep (keep ρ₀)))))) (vs (vs (vs (vs (vs (vs x₀)))))) C₆
W₆ =
  iwf-κ κ₆ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ KnotWf
              (⊢ixP ⊢sTy (⊢fst (⊢var (∋lkp _ (vsⁿ 6 vz))))))
           (toMu (⊢snd (⊢snd (⊢snd
              (⊢var (∋lkp _ (vsⁿ 6 vz)))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 5 vz))))))
                  (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 6 vz)))))
                  (⊢symN (⊢fst (⊢var (∋lkp _ (vsⁿ 6 vz))))
                         (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 5 vz)))))
                         (fordAs (⊢var (∋lkp _ (vsⁿ 2 vz)))))
                  (toMu (⊢wkTyK (fromI (⊢var (∋lkp _ (vsⁿ 5 vz))))
                                (fromMu (⊢var (∋lkp _ (vsⁿ 3 vz))))))))
    iwf-ι

W₅ : IConWf ILk TΘ5 (keep (keep (keep (keep (keep ρ₀))))) (vs (vs (vs (vs (vs x₀))))) C₅
W₅ =
  iwf-κ κ₅ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ KnotWf
              (⊢ixP ⊢sVar (⊢fst (⊢var (∋lkp _ (vsⁿ 5 vz))))))
           (toMu (⊢fst (⊢snd (⊢snd
              (⊢var (∋lkp _ (vsⁿ 5 vz)))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 4 vz))))))
                  (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 5 vz)))))
                  (⊢symN (⊢fst (⊢var (∋lkp _ (vsⁿ 5 vz))))
                         (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 4 vz)))))
                         (fordAs (⊢var (there here))))
                  (toMu (⊢Var-vzKv
                           (fromI (⊢var (∋lkp _ (vsⁿ 4 vz))))))))
    W₆

W₄ : IConWf ILk TΘ4 (keep (keep (keep (keep ρ₀)))) (vs (vs (vs (vs x₀)))) C₄
W₄ =
  iwf-κ κ₄ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ CtxWf
              (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 4 vz))))))
           (toMu (⊢fst (⊢snd (⊢var (∋lkp _ (vsⁿ 4 vz))))))
           (⊢jsub (⊢⌜IMu⌝ CtxWf (⊢var here))
                  (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 3 vz))))))
                  (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 4 vz)))))
                  (⊢symN (⊢fst (⊢var (∋lkp _ (vsⁿ 4 vz))))
                         (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 3 vz)))))
                         (fordAs (⊢var here)))
                  (toMu (⊢Ctx-extKv
                           (fromI (⊢var (∋lkp _ (vsⁿ 3 vz))))
                           (fromMu (⊢var (∋lkp _ (vsⁿ 2 vz))))
                           (fromMu (⊢var (there here)))))))
    W₅

W₃ : IConWf ILk TΘ3 (keep (keep (keep ρ₀))) (vs (vs (vs x₀))) C₃
W₃ =
  iwf-κ κ₃ (icw-ford _ _ _)
    (⊢⌜Id⌝ ⊢⌜Nat⌝
      (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 3 vz)))))
      (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 2 vz)))))))
    W₄

W₂ : IConWf ILk TΘ2 (keep (keep ρ₀)) (vs (vs x₀)) C₂
W₂ =
  iwf-κ κ₂ (icw-imu (pair sTy (var (vs vz))) KnotWf)
    (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (there here)))))
    W₃

W₁ : IConWf ILk TΘ1 (keep ρ₀) (vs x₀) C₁
W₁ =
  iwf-κ κ₁ (icw-imu (var vz) CtxWf) (⊢⌜IMu⌝ CtxWf (⊢var here)) W₂

-- ★★★ `here` IS WELL FORMED.
lkHereWf : IConWf ILk (Θ₀ ILk) ρ₀ x₀ lkHere
lkHereWf = iwf-κ κ₀ (icw-clo ⌜Nat⌝ ⊢⌜Nat⌝) ⊢⌜Nat⌝ W₁

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
                (wkTyK (var (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))
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
-- ★ A-MATH: the telescope `TΞ` is the family, the index, and each code
--   read through the family-skipping thinning; the recursive premise
--   enters as the FAMILY at its index, `El (app (var x) …)` — so it no
--   longer mentions `LkD`, and could be stated before it.
------------------------------------------------------------------------

TΞ0 TΞ1 TΞ2 TΞ3 TΞ4 TΞ5 TΞ6 TΞ7 TΞ8 TΞ9 : Ctx
TΞ0 = Θ₀ ILk
TΞ1 = TΞ0 ▹ El (renTm (thinR (ρ₀)) λ₀)
TΞ2 = TΞ1 ▹ El (renTm (thinR (keep ρ₀)) λ₁)
TΞ3 = TΞ2 ▹ El (renTm (thinR (keep (keep ρ₀))) λ₂)
TΞ4 = TΞ3 ▹ El (renTm (thinR (keep (keep (keep ρ₀)))) λ₃)
TΞ5 = TΞ4 ▹ El (renTm (thinR (keep (keep (keep (keep ρ₀))))) λ₄)
TΞ6 = TΞ5 ▹ El (app (var (vs (vs (vs (vs (vs x₀)))))) (renTm (thinR (keep (keep (keep (keep (keep ρ₀)))))) ρ₅))
TΞ7 = TΞ6 ▹ El (renTm (thinR (keep (keep (keep (keep (keep (keep ρ₀))))))) λ₆)
TΞ8 = TΞ7 ▹ El (renTm (thinR (keep (keep (keep (keep (keep (keep (keep ρ₀)))))))) λ₇)
TΞ9 = TΞ8 ▹ El (renTm (thinR (keep (keep (keep (keep (keep (keep (keep (keep ρ₀))))))))) λ₈)

V₉ : IConWf ILk TΞ9 (keep (keep (keep (keep (keep (keep (keep (keep (keep ρ₀))))))))) (vs (vs (vs (vs (vs (vs (vs (vs (vs x₀))))))))) (iκ λ₉ iι)
V₉ =
  iwf-κ λ₉ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ KnotWf
              (⊢ixP ⊢sTy (⊢fst (⊢var (∋lkp _ (vsⁿ 9 vz))))))
           (toMu (⊢snd (⊢snd (⊢snd
              (⊢var (∋lkp _ (vsⁿ 9 vz)))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 8 vz)))))) 
                  (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 9 vz)))))
                  (⊢symN (⊢fst (⊢var (∋lkp _ (vsⁿ 9 vz))))
                         (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 8 vz))))) 
                         (fordAs (⊢var (∋lkp _ (vsⁿ 2 vz)))))
                  (toMu (⊢wkTyK (fromI (⊢var (∋lkp _ (vsⁿ 8 vz))))
                                (fromMu (⊢var (∋lkp _ (vsⁿ 5 vz))))))))
    iwf-ι

V₈ : IConWf ILk TΞ8 (keep (keep (keep (keep (keep (keep (keep (keep ρ₀)))))))) (vs (vs (vs (vs (vs (vs (vs (vs x₀)))))))) (iκ λ₈ (iκ λ₉ iι))
V₈ =
  iwf-κ λ₈ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ KnotWf
              (⊢ixP ⊢sVar (⊢fst (⊢var (∋lkp _ (vsⁿ 8 vz))))))
           (toMu (⊢fst (⊢snd (⊢snd
              (⊢var (∋lkp _ (vsⁿ 8 vz)))))))
           (⊢jsub (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (fromI (⊢var here))))
                  (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 7 vz)))))) 
                  (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 8 vz)))))
                  (⊢symN (⊢fst (⊢var (∋lkp _ (vsⁿ 8 vz))))
                         (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 7 vz))))) 
                         (fordAs (⊢var (there here))))
                  (toMu (⊢Var-vsKv
                           (fromI (⊢var (∋lkp _ (vsⁿ 7 vz))))
                           (fromMu (⊢var (∋lkp _ (vsⁿ 5 vz))))))))
    V₉

V₇ : IConWf ILk TΞ7 (keep (keep (keep (keep (keep (keep (keep ρ₀))))))) (vs (vs (vs (vs (vs (vs (vs x₀))))))) (iκ λ₇ (iκ λ₈ (iκ λ₉ iι)))
V₇ =
  iwf-κ λ₇ (icw-ford _ _ _)
    (⊢⌜Id⌝ (⊢⌜IMu⌝ CtxWf
              (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 7 vz))))))
           (toMu (⊢fst (⊢snd (⊢var (∋lkp _ (vsⁿ 7 vz)))))) 
           (⊢jsub (⊢⌜IMu⌝ CtxWf (⊢var here))
                  (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 6 vz)))))) 
                  (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 7 vz)))))
                  (⊢symN (⊢fst (⊢var (∋lkp _ (vsⁿ 7 vz))))
                         (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 6 vz))))) 
                         (fordAs (⊢var here)))
                  (toMu (⊢Ctx-extKv
                           (fromI (⊢var (∋lkp _ (vsⁿ 6 vz))))
                           (fromMu (⊢var (∋lkp _ (vsⁿ 5 vz))))
                           (fromMu (⊢var (∋lkp _ (vsⁿ 2 vz))))))))
    V₈

V₆ : IConWf ILk TΞ6 (keep (keep (keep (keep (keep (keep ρ₀)))))) (vs (vs (vs (vs (vs (vs x₀)))))) (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι))))
V₆ =
  iwf-κ λ₆ (icw-ford _ _ _)
    (⊢⌜Id⌝ ⊢⌜Nat⌝
      (toI (⊢fst (⊢var (∋lkp _ (vsⁿ 6 vz)))))
      (toI (⊢nsuc (fromI (⊢var (∋lkp _ (vsⁿ 5 vz))))))) 
    V₇

-- ★ THE RECURSIVE PREMISE.  Its index is the four-tuple `(m, Γ, x, A)`.
-- ★ THE RECURSIVE PREMISE.  Its index is the four-tuple `(m, Γ, x, A)` —
--   the telescope §1 built, now carrying actual field values.
--
-- ⚠ `⊢pair`'s FIRST argument is the ⊢ty of the TAIL, not of the head.
V₅ : IConWf ILk TΞ5 (keep (keep (keep (keep (keep ρ₀))))) (vs (vs (vs (vs (vs x₀))))) (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι)))))
V₅ =
  iwf-ρ ρ₅
    (⊢pair (ty-Σ (ty-IMu CtxWf (toI (⊢var here)))
             (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here))))
                   (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (∋lkp _ (vsⁿ 2 vz)))))))
           (fromI (⊢var (∋lkp _ (vsⁿ 4 vz))))
      (⊢pair (ty-Σ (ty-IMu KnotWf
                     (⊢ixP ⊢sVar (⊢wk (fromI (⊢var (∋lkp _ (vsⁿ 4 vz)))))))
                   (ty-IMu KnotWf
                     (⊢ixP ⊢sTy (⊢wk (⊢wk (fromI (⊢var (∋lkp _ (vsⁿ 4 vz))))))))) 
             (fromMu (⊢var (∋lkp _ (vsⁿ 3 vz))))
        (⊢pair (ty-IMu KnotWf
                 (⊢ixP ⊢sTy (⊢wk (fromI (⊢var (∋lkp _ (vsⁿ 4 vz)))))))
               (fromMu (⊢var (∋lkp _ (vsⁿ 2 vz))))
               (fromMu (⊢var (there here))))))
    V₆

V₄ : IConWf ILk TΞ4 (keep (keep (keep (keep ρ₀)))) (vs (vs (vs (vs x₀)))) (iκ λ₄ (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι))))))
V₄ =
  iwf-κ λ₄ (icw-imu (pair sTy (var (vs (vs (vs vz))))) KnotWf)
    (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (∋lkp _ (vsⁿ 3 vz))))))
    V₅

V₃ : IConWf ILk TΞ3 (keep (keep (keep ρ₀))) (vs (vs (vs x₀))) (iκ λ₃ (iκ λ₄ (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι)))))))
V₃ =
  iwf-κ λ₃ (icw-imu (pair sTy (var (vs (vs vz)))) KnotWf)
    (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (fromI (⊢var (∋lkp _ (vsⁿ 2 vz))))))
    V₄

V₂ : IConWf ILk TΞ2 (keep (keep ρ₀)) (vs (vs x₀))
       (iκ λ₂ (iκ λ₃ (iκ λ₄ (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι))))))))
V₂ =
  iwf-κ λ₂ (icw-imu (pair sVar (var (vs vz))) KnotWf)
    (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (fromI (⊢var (there here)))))
    V₃

V₁ : IConWf ILk TΞ1 (keep ρ₀) (vs x₀)
       (iκ λ₁ (iκ λ₂ (iκ λ₃ (iκ λ₄ (iρ ρ₅ (iκ λ₆ (iκ λ₇ (iκ λ₈ (iκ λ₉ iι)))))))))
V₁ =
  iwf-κ λ₁ (icw-imu (var vz) CtxWf) (⊢⌜IMu⌝ CtxWf (⊢var here)) V₂

-- ★★★ `there` IS WELL FORMED.
lkThereWf : IConWf ILk (Θ₀ ILk) ρ₀ x₀ lkThere
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
LkWf =
  -- ★ the index type IS a type — `IDescWf` carries it (A-math)
  ty-Σ ty-Nat (ty-Σ (ty-IMu CtxWf (toI (⊢var here)))
                (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢var (there here))))
                      (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (∋lkp _ (vsⁿ 2 vz))))))) ,,
  idwf-cons lkHereWf (idwf-cons lkThereWf idwf-nil)

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
         (pair (Var-vzK nzero) (wkTyK nzero Ty-NatK)))

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
                (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢var (∋lkp _ (vsⁿ 2 vz)))))))
        (⊢nsuc ⊢nzero)
    (⊢pair (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sVar (⊢nsuc ⊢nzero)))
                 (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢nsuc ⊢nzero))))
           (⊢Ctx-extK 0 ⊢Ctx-empK (⊢Ty-NatK 0))
      (⊢pair (ty-IMu KnotWf (⊢ixP ⊢sTy (⊢nsuc ⊢nzero)))
             (⊢Var-vzK 0)
             (⊢wkTyK ⊢nzero (⊢Ty-NatK 0))))


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
                            (wkTyK nzero Ty-NatK))
                    unit)))))))

-- (HISTORY, pre-A-math) ⚠ `ipayTy-wf`'s `Θ` WAS PINNED.  It is a `Ctx` reached only through
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
    -- ★ A-MATH: the payload one field at a time (`Lib/IPay.⊢payκ`), each
    --   against its telescope's `XEnv` — no `Sub⊢` bookkeeping, no casts.
    (⊢payκ LkD ILk σ₀ κ₀ C₁ LkWf lkHereWf e₀ (toI ⊢nzero)
     (⊢payκ LkD ILk σ₁ κ₁ C₂ LkWf W₁ e₁ (toMu ⊢Ctx-empK)
      (⊢payκ LkD ILk σ₂ κ₂ C₃ LkWf W₂ e₂ (toMu (⊢Ty-NatK 0))
       (⊢payκ LkD ILk σ₃ κ₃ C₄ LkWf W₃ e₃ f₃
        (⊢payκ LkD ILk σ₄ κ₄ C₅ LkWf W₄ e₄ f₄
         (⊢payκ LkD ILk σ₅ κ₅ C₆ LkWf W₅ e₅ f₅
          (⊢payκ LkD ILk σ₆ κ₆ iι LkWf W₆ e₆ f₆ ⊢unit)))))))
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
                (wkTyK nzero Ty-NatK)
    e₀ = xenv₀ {D = LkD} {I = ILk} LkWf ⊢i₀
    e₁ = xenv-κ e₀ κ₀ (toI ⊢nzero)
    e₂ = xenv-κ e₁ κ₁ (toMu ⊢Ctx-empK)
    e₃ = xenv-κ e₂ κ₂ (toMu (⊢Ty-NatK 0))
    -- the DEPTH ford: both sides reduce to `suc 0`
    f₃ : Δ ⊢ v₃ ∷ El (subTm σ₃ κ₃)
    f₃ = idCˡ (βfst _ _) (reflAt ⊢⌜Nat⌝ (toI (⊢nsuc ⊢nzero)))
    e₄ = xenv-κ e₃ κ₃ f₃
    -- ★ the CONTEXT ford, and ★★ THE TRANSPORT EVAPORATES: at a concrete
    --   index the ford witness IS an `idrefl`, so `transport-fires`
    --   collapses the `jsub` in two steps.
    f₄ : Δ ⊢ v₄ ∷ El (subTm σ₄ κ₄)
    f₄ = idCᶜ (ξ-⌜IMu⌝ (βfst _ _))
          (idCˡ* (step (ξ-fst (βsnd _ _)) (step (βfst _ _) done))
            (idCʳ* (transport-fires _ _ _ _)
              (reflAt (⊢⌜IMu⌝ CtxWf (toI (⊢nsuc ⊢nzero)))
                      (toMu (⊢Ctx-extK 0 ⊢Ctx-empK (⊢Ty-NatK 0))))))
    e₅ = xenv-κ e₄ κ₄ f₄
    f₅ : Δ ⊢ v₅ ∷ El (subTm σ₅ κ₅)
    f₅ = idCᶜ (ξ-⌜IMu⌝ (ξ-pairʳ (βfst _ _)))
          (idCˡ* (step (ξ-fst (ξ-snd (βsnd _ _)))
                   (step (ξ-fst (βsnd _ _)) (step (βfst _ _) done)))
            (idCʳ* (transport-fires _ _ _ _)
              (reflAt (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sVar (⊢nsuc ⊢nzero)))
                      (toMu (⊢Var-vzK 0)))))
    e₆ = xenv-κ e₅ κ₅ f₅
    f₆ : Δ ⊢ v₆ ∷ El (subTm σ₆ κ₆)
    f₆ = idCᶜ (ξ-⌜IMu⌝ (ξ-pairʳ (βfst _ _)))
          (idCˡ* (step (ξ-snd (ξ-snd (βsnd _ _)))
                   (step (ξ-snd (βsnd _ _)) (step (βsnd _ _) done)))
            (idCʳ* (transport-fires _ _ _ _)
              (reflAt (⊢⌜IMu⌝ KnotWf (⊢ixP ⊢sTy (⊢nsuc ⊢nzero)))
                      (toMu (⊢wkTyK ⊢nzero (⊢Ty-NatK 0))))))
