------------------------------------------------------------------------
-- OCP-0009 · directed-`ap` spike — THE CANONICITY KEYSTONE, MECHANIZED.
--
-- THE GAP (NbEPDirDBExamples §6): no former acts on homs — `cong` is
-- unwritable, so hom-chains cannot be built under constructors.
--
-- THE DESIGN (this spike's paper half):
--   syntax   ap : cB (target code) → b (body, vz free) → p (path)
--   typing   ⊢ap : Γ ⊢ cA ∷ U → stkC? cA ≡ true → Γ ⊢ cB ∷ U →
--                  (Γ ▹ El cA) ⊢ b ∷ El (renTm vs cB) →
--                  Γ ⊢ p ∷ Hom (El cA) t u →
--                  Γ ⊢ ap cB b p
--                    ∷ Hom (El cB) (subTm (single t) b) (subTm (single u) b)
--   rules    ap-J   : stkC? c₁ ≡ true →
--                     ap cB b (hrefl c₁ s) ⟶ hrefl cB (subTm (single s) b)
--            ξ-apᵖ/ξ-apᵇ/ξ-apᶜ congruences.
--
--   * the TARGET is code-annotated (like `hrefl`) — that is where the
--     result reflexivity's code comes from;
--   * the SOURCE ambient is restricted to STABLE codes (`stkC?`, a
--     substitution-stable Boolean — `stkC?-sub` — so the typing rule
--     survives `⊢[]`), which makes the J-rule COMPLETE for closed
--     canonicity (theorems below);
--   * `ap` along lam-paths (pw-coded sources = higher-order cong =
--     whiskering) and dependent `apd` (needs HomOver) stay out, with
--     the same honesty as Hom-at-Hom.
--
-- ★★ MECHANIZED HERE, against the REAL kernel + G2's Canon:
--   1. `stable-path-is-hrefl` — closed normal paths at stable-coded
--      ambients are EXACTLY hrefls (the lam case is untypeable);
--   2. `normal-hrefl-code-stable` — a closed normal hrefl's own code
--      passes `stkC?` (pw would fire `hrefl-pw`, refuting normality);
--   3. `apJ-complete` — combining: on every closed normal well-typed
--      instance, ap-J's key HOLDS.  No new stuck forms: G2's progress
--      extends with one rule.
--   4. `apJ-vs-hreflpw-disjoint` — the raw overlap with `hrefl-pw` is
--      empty (`stk⊥pw`): the Takahashi rows stay premise-disjoint.
--
-- `--safe`, zero postulates, zero holes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeAp where

open import normalizer.Syntax.Types
  using ( _≡_; refl; trans; sym; Σ; _,_; ⊥; ⊥-elim; _⊎_; inj₁; inj₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; RTy; El; Hom; RTm; lam; hrefl; ⌜Nat⌝ )
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; pw?; stkC?; stk⊥pw; stkC?→hd )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶_; hrefl-pw; ξ-hreflᶜ
        ; _≅ᵀ_; csymᵀ; Ctx; ◇; ⌊_⌋; _⊢_∷_ )
open import poc.OCP0009.NbEPDirDBLR using ( IsNormal )
open import poc.OCP0009.NbEPDirDBSubj using ( gen-lam; gen-hrefl )
open import poc.OCP0009.NbEPDirDBCanon
  using ( pathCanon; codeCanon; HomStkΠ-clash; HomNatNoNat-clash )
open import poc.OCP0009.NbEPDirDBSubj using ( nn-El )

------------------------------------------------------------------------
-- 1. Closed normal paths at STABLE-coded ambients are exactly hrefls.
------------------------------------------------------------------------

stable-path-is-hrefl :
  {p : RTm ε} {c t u : RTm ε} →
  ◇ ⊢ p ∷ Hom (El c) t u → stkC? c ≡ true → IsNormal p →
  Σ (RTm ε) (λ c₁ → Σ (RTm ε) (λ s → p ≡ hrefl c₁ s))
stable-path-is-hrefl {c = c} d k nrm
  with pathCanon (nn-El (stkC?→hd c k)) d nrm
... | inj₁ hs = hs
... | inj₂ (f , refl) with gen-lam d
...   | _ , (_ , (cv , _)) = ⊥-elim (HomStkΠ-clash k cv)

------------------------------------------------------------------------
-- 2. A closed normal hrefl's code passes `stkC?` — the ap-J key.
------------------------------------------------------------------------

-- ⚠ SpikeNatJ: the conclusion is WEAKER than it was.  `hrefl ⌜Nat⌝ n`
-- is closed, normal and well-typed, and `stkC? ⌜Nat⌝ = false` — the
-- ORDERED code is the one J-less closed normal path code.  What pins it
-- down is the AMBIENT, which `apJ-complete` has and this lemma does not.
normal-hrefl-code-stable :
  {c₁ s : RTm ε} {T : RTy ε} →
  ◇ ⊢ hrefl c₁ s ∷ T → IsNormal (hrefl c₁ s) →
  (stkC? c₁ ≡ true) ⊎ (c₁ ≡ ⌜Nat⌝)
normal-hrefl-code-stable {c₁} {s} d nrm with gen-hrefl d
... | dc₁ , _ with codeCanon dc₁ (λ r → nrm (ξ-hreflᶜ r))
...   | inj₁ pw        = ⊥-elim (nrm (hrefl-pw c₁ s pw))
...   | inj₂ (inj₁ k)  = inj₁ k
...   | inj₂ (inj₂ eq) = inj₂ eq

------------------------------------------------------------------------
-- 3. ★★ THE KEYSTONE: on closed normal instances the J-rule ALWAYS has
--    its key — `ap` at stable sources introduces no stuck forms.
------------------------------------------------------------------------

apJ-complete :
  {p : RTm ε} {c t u : RTm ε} →
  ◇ ⊢ p ∷ Hom (El c) t u → stkC? c ≡ true → IsNormal p →
  Σ (RTm ε) (λ c₁ → Σ (RTm ε) (λ s →
    Σ (p ≡ hrefl c₁ s) (λ _ → stkC? c₁ ≡ true)))
-- ★ the keystone SURVIVES: the source ambient's own stability rules the
-- ORDERED code out.  `El ⌜Nat⌝ ⟶ᵀ Nat`, and a `stkC?` code's decode is
-- Nat-free — so the ⌜Nat⌝ escape hatch above is unreachable HERE.
apJ-complete {c = c} d k nrm with stable-path-is-hrefl d k nrm
... | c₁ , (s , refl) with normal-hrefl-code-stable d nrm
...   | inj₁ ks = c₁ , (s , (refl , ks))
...   | inj₂ refl with gen-hrefl d
...     | _ , (_ , cvh) =
          ⊥-elim (HomNatNoNat-clash (nn-El (stkC?→hd c k)) (csymᵀ cvh))

------------------------------------------------------------------------
-- 4. The raw critical pair with `hrefl-pw` is EMPTY: the two keys are
--    contradictory, so the confluence rows stay premise-disjoint.
------------------------------------------------------------------------

apJ-vs-hreflpw-disjoint :
  {Γ : Cx} (c₁ : RTm Γ) → stkC? c₁ ≡ true → pw? c₁ ≡ true → ⊥
apJ-vs-hreflpw-disjoint c₁ k p with trans (sym (stk⊥pw c₁ k)) p
... | ()
