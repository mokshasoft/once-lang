------------------------------------------------------------------------
-- OCP-0009 — SPIKE: THE ⌜Hom⌝-OVER-⌜Nat⌝ STUCK TRANSPORT.
--
-- ★★ A COUNTEREXAMPLE PROBE, not a feature.  It exhibits a CLOSED,
-- WELL-TYPED `tr` that is NORMAL — which refutes `trProgress` (Canon's
-- G2 "closed well-typed `tr`s always step") as the kernel stands after
-- WF stage C step 2.
--
-- The mechanism.  Step 0 set `stkC? ⌜Nat⌝ = false` — correctly: J at an
-- ORDERED type is unsound, because `Hom Nat nzero n ⟶ᵀ Unit` discards
-- `n`, so a `hrefl ⌜Nat⌝ s` does not pin its endpoints.  But `stkC?`
-- RECURSES through ⌜Hom⌝ (`stkC? (⌜Hom⌝ C a b) = stkC? C`), so the
-- `false` propagates OUT to every code built over ⌜Nat⌝ — including
-- `⌜Hom⌝ ⌜Nat⌝ a b`, whose decode is `Hom Nat a b`, a type that is
-- *not itself ordered*.  For such a code J is perfectly sound: the
-- ambient of `hrefl (⌜Hom⌝ ⌜Nat⌝ a b) s` is a `Hom`, which can only
-- become `Unit`/`base`/`Hom Nat _ _` — never `Nat`, so no order rule
-- can fire at that level and the endpoints ARE pinned.
--
-- Consequence: `tr` at such a path has nothing to fire and no premise
-- excludes it, so it is stuck.  The propagation is the bug; the
-- retraction is not.
--
--   ★ `p-nat`     — the path, well-typed and NORMAL
--   ★ `⊢stuck`    — the whole `tr`, closed and well-typed
--   ★ `stuck-nf`  — …and it does not reduce.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeNatJ where

open import normalizer.Syntax.Types using ( _≡_; refl; ⊥; Σ; _,_ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; El; Hom; Unit; Nat
        ; RTm; var; ⌜Hom⌝; ⌜Nat⌝; ⌜Unit⌝; hrefl; tr
        ; unit; nzero; nsuc )
open import poc.OCP0009.NbEPDirDBVar using ( NoNatC; nnc-Unit )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶_; _⟶ᵀ_
        ; El-⌜Nat⌝; El-⌜Unit⌝; El-⌜Hom⌝; ξ-Homᵀ
        ; Hom-Nat-z; Hom-Nat-ss
        ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ; ξ-hreflᶜ; ξ-hreflᵃ
        ; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ; ξ-nsuc
        ; _≅ᵀ_; credᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋; _∋_∷_; here
        ; _⊢_∷_; ⊢var; ⊢conv; ⊢unit; ⊢nzero; ⊢nsuc
        ; ⊢⌜Nat⌝; ⊢⌜Unit⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; red→≅ᵀ; ⟶ᵀ*-Homᵀ )

n1 n2 : {Γ : Cx} → RTm Γ
n1 = nsuc nzero
n2 = nsuc (nsuc nzero)

------------------------------------------------------------------------
-- 1. The ORDER CODE `⌜Hom⌝ ⌜Nat⌝ 1 2`, and the fact that its decode is
--    `Unit` — the inequality holds, so the order type is inhabited by
--    `unit` (stage B's payoff), and `⌜Hom⌝ ⌜Nat⌝ 1 2` is a code at `U`.
------------------------------------------------------------------------

cNat12 : {Γ : Cx} → RTm Γ
cNat12 = ⌜Hom⌝ ⌜Nat⌝ n1 n2

el-cNat12 : {Γ : Cx} → El (cNat12 {Γ}) ⟶ᵀ* Unit
el-cNat12 =
  stepᵀ (El-⌜Hom⌝ _ _ _)
    (stepᵀ (ξ-Homᵀ El-⌜Nat⌝)
      (stepᵀ (Hom-Nat-ss _ _)
        (stepᵀ (Hom-Nat-z _) doneᵀ)))

⊢n1 : {Γ : Ctx} → Γ ⊢ n1 ∷ El ⌜Nat⌝
⊢n1 = ⊢conv (⊢nsuc ⊢nzero) (csymᵀ (credᵀ El-⌜Nat⌝))

⊢n2 : {Γ : Ctx} → Γ ⊢ n2 ∷ El ⌜Nat⌝
⊢n2 = ⊢conv (⊢nsuc (⊢nsuc ⊢nzero)) (csymᵀ (credᵀ El-⌜Nat⌝))

⊢cNat12 : {Γ : Ctx} → Γ ⊢ cNat12 ∷ U
⊢cNat12 = ⊢⌜Hom⌝ ⊢⌜Nat⌝ ⊢n1 ⊢n2

⊢unit-at-cNat12 : {Γ : Ctx} → Γ ⊢ unit ∷ El cNat12
⊢unit-at-cNat12 = ⊢conv ⊢unit (csymᵀ (red→≅ᵀ el-cNat12))

------------------------------------------------------------------------
-- 2. ★ THE PATH.  `hrefl` at the ORDER code — reflexivity of the
--    proof-space of `1 ≤ 2`, a hom over `Hom Nat 1 2`, NOT over `Nat`.
--    Its type is convertible to `Hom (El ⌜Unit⌝) unit unit`, because
--    both ambients decode to `Unit`.
------------------------------------------------------------------------

p-nat : {Γ : Cx} → RTm Γ
p-nat = hrefl cNat12 unit

⊢p-nat : {Γ : Ctx} → Γ ⊢ p-nat ∷ Hom (El cNat12) unit unit
⊢p-nat = ⊢hrefl ⊢cNat12 ⊢unit-at-cNat12

-- both ambients reach `Unit`, so the two hom types are convertible.
amb-conv : {Γ : Cx} → Hom (El (cNat12 {Γ})) unit unit ≅ᵀ Hom (El ⌜Unit⌝) unit unit
amb-conv =
  ctrnᵀ (red→≅ᵀ (⟶ᵀ*-Homᵀ el-cNat12))
        (csymᵀ (red→≅ᵀ (⟶ᵀ*-Homᵀ (stepᵀ El-⌜Unit⌝ doneᵀ))))

⊢p-at-Unit : {Γ : Ctx} → Γ ⊢ p-nat ∷ Hom (El ⌜Unit⌝) unit unit
⊢p-at-Unit = ⊢conv ⊢p-nat amb-conv

------------------------------------------------------------------------
-- 3. ★★ THE STUCK TRANSPORT.  Ambient `El ⌜Unit⌝`, motive code
--    ⌜Unit⌝ — so `⊢tr`'s stage-C premise `NoNatC c` is DISCHARGED
--    (`nnc-Unit`); the ⌜Nat⌝ is hidden inside the PATH's code, which
--    the rule does not see.
------------------------------------------------------------------------

stuck : {Γ : Cx} → RTm Γ
stuck = tr (⌜Hom⌝ ⌜Unit⌝ unit (var vz)) p-nat (hrefl ⌜Unit⌝ unit)

⊢unit-at-Unit : {Γ : Ctx} → Γ ⊢ unit ∷ El ⌜Unit⌝
⊢unit-at-Unit = ⊢conv ⊢unit (csymᵀ (credᵀ El-⌜Unit⌝))

⊢e : {Γ : Ctx} → Γ ⊢ hrefl ⌜Unit⌝ unit ∷ El (⌜Hom⌝ ⌜Unit⌝ unit unit)
⊢e = ⊢conv (⊢hrefl ⊢⌜Unit⌝ ⊢unit-at-Unit)
           (csymᵀ (credᵀ (El-⌜Hom⌝ _ _ _)))

⊢stuck : ◇ ⊢ stuck ∷ El (⌜Hom⌝ ⌜Unit⌝ unit unit)
⊢stuck =
  ⊢tr {A = El ⌜Unit⌝}
      ⊢⌜Unit⌝ ⊢unit-at-Unit (⊢var here) nnc-Unit refl refl
      ⊢unit-at-Unit ⊢unit-at-Unit
      ⊢p-at-Unit
      ⊢e

------------------------------------------------------------------------
-- 4. ★★★ …AND IT DOES NOT STEP.  Every root rule is keyed off the
--    path's code head: `tr-J-base`/`-Σ`/`-Unit`/`-Id` want a different
--    constructor, `tr-J-Hom` wants `stkC? (⌜Hom⌝ ⌜Nat⌝ 1 2) ≡ true` —
--    which is `stkC? ⌜Nat⌝`, i.e. `false` — and `tr-taut`/`tr-pw` want
--    a `lam` path.  The congruences all hit normal subterms.
------------------------------------------------------------------------

stuck-nf : {Γ : Cx} {u : RTm Γ} → stuck ⟶ u → ⊥
-- the J family: only the ⌜Hom⌝ arm matches the shape, and its key is
-- `stkC? ⌜Nat⌝ ≡ true`.
stuck-nf (ξ-trᵈ (ξ-⌜Hom⌝ᶜ ()))
stuck-nf (ξ-trᵈ (ξ-⌜Hom⌝ˡ ()))
stuck-nf (ξ-trᵈ (ξ-⌜Hom⌝ʳ ()))
stuck-nf (ξ-trᵖ (ξ-hreflᶜ (ξ-⌜Hom⌝ᶜ ())))
stuck-nf (ξ-trᵖ (ξ-hreflᶜ (ξ-⌜Hom⌝ˡ (ξ-nsuc ()))))
stuck-nf (ξ-trᵖ (ξ-hreflᶜ (ξ-⌜Hom⌝ʳ (ξ-nsuc (ξ-nsuc ())))))
stuck-nf (ξ-trᵖ (ξ-hreflᵃ ()))
stuck-nf (ξ-trᵉ (ξ-hreflᶜ ()))
stuck-nf (ξ-trᵉ (ξ-hreflᵃ ()))

------------------------------------------------------------------------
-- 5. ★★★★ THE REFUTATION, stated against the THEOREM STATEMENTS rather
--    than against `NbEPDirDBCanon` itself — so it is checkable NOW,
--    with no dependency on that module compiling.  Feed either theorem
--    its own statement and you get `⊥`.
--
--    `Canon`'s `trProgress` is verbatim:
--        {dM : RTm (ε ∙)} {p e : RTm ε} {T : RTy ε} →
--        ◇ ⊢ tr dM p e ∷ T → Σ (RTm ε) (λ u → tr dM p e ⟶ u)
--    and `progress` is `◇ ⊢ t ∷ T → Prog t`, where `Prog` is
--    canonical-or-steps.  `Canon` has no `tr` arm, so the `tr` case of
--    `progress` must produce a step too.
------------------------------------------------------------------------

trProgress-refuted :
  ({dM : RTm (ε ∙)} {p e : RTm ε} {T : RTy ε} →
   ◇ ⊢ tr dM p e ∷ T → Σ (RTm ε) (λ u → tr dM p e ⟶ u)) → ⊥
trProgress-refuted tp with tp ⊢stuck
... | _ , r = stuck-nf r
