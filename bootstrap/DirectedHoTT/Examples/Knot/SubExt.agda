------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ EXTENSION PRESERVES `Represents`, FOR
-- SUBSTITUTION.  The last piece `sub-agree` was waiting on.
--
--     extS-Represents : Represents σ s → Represents (extS σ) (extNK d ⌈Δ⌉ s)
--
-- ⚠ IT CANNOT LIVE BESIDE `extR-Represents` IN `Knot/SubAgree`, though
--   that is where it belongs by subject: it needs `Knot/SubSpec`, which
--   needs `Knot/RenAgreeTie`, which needs `Knot/SubAgree`.  The
--   dependency structure decides the module, not the topic.
--
-- ★★★ AND THE `vs` CASE IS WHERE SUBSTITUTION DIFFERS FROM RENAMING.
--   `extS σ (vs x) = renTm vs (σ x)` — the result is WEAKENED — and
--   `extVs`'s body is `wkTmK n (app σ …)` to match.  So this case composes
--   `Represents` with `wkTmK-agree`, i.e. with `ren-agree` itself.
--   `extR-Represents` needed nothing of the sort: `extR ρ (vs x) =
--   vs (ρ x)` never leaves the variable sort.
--   ⇒ the renaming half is not a special case of the substitution half;
--     the substitution half is BUILT ON it.
--
-- ⚠⚠ THREE ORDERING FACTS, each of which cost an iteration:
--   1. RECOGNISE THE WRAPPER FIRST.  After `extVs`'s five βs the
--      substitutions are DISTRIBUTED over `wkTmK`'s unfolding, so there is
--      no `subTm τ (wkTmK …)` to rewrite — until the five are COLLAPSED
--      into one composite (`unc`), at which point `wkTmK-sub` applies.
--      Reducing inside first destroys the shape the equality describes.
--   2. EVERY LATER SLOT IS THEN AT THE COMPOSITE `τ`, and must be bridged
--      back with `unc`.  Getting that wrong reads as a CONTEXT mismatch
--      (`Θ != ((Θ ∙) ∙)`), which does not look like a tower error at all.
--   3. `eqW`'s BODY CANNOT BE INFERRED: the cast's target is fixed by the
--      chain that follows, and that chain still has metas.  Written out.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubExt where
open import Agda.Builtin.Nat using ( zero; suc; _+_ ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans; sym )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; Var; vz; vs; Sub; subTm; extS; app; pair; icon; ielim
        ; iihs; isingle; ilookupD; idrefl; ⌜Nat⌝; unit; fst; snd; var; renTm
        ; IDesc; nsuc; sel; lam; subTm-subTm; _∘ₛ_; jsub; ⌜IMu⌝ )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; βfst; βsnd; ι-ielim; single; wk-single; jsub-refl )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd
        ; ⟶*-ielimᵗ; ⟶*-jsubᵖ )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ; ⟶*-castₗ )
open import DirectedHoTT.Lib.Wk using ( w; pw^; sub-w )
open import DirectedHoTT.Lib.IMeths using ( CDesc; cdTake; sel-here≡; sel-there≡ )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vs )
open import DirectedHoTT.Examples.Knot.Sorts using ( sVar; sTm; num; len; IPair )
open import DirectedHoTT.Lib.ArithComm using ( symN )
open import DirectedHoTT.Lib.Monus using ( predTm )
open import DirectedHoTT.Lib.IdSuc using ( predN )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vsK )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enVar )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTmK )
open import DirectedHoTT.Examples.Knot.SubAgree using ( Represents )
open import DirectedHoTT.Examples.Knot.SubMot
  using ( extNK; extSK; extMethsK; extTail; extVs )
open import DirectedHoTT.Examples.Knot.SubSpec
  using ( constMethsFrom-past; wkTmK-agree; extNK-vz; wkTmK-sub )

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

cong₃' : {Γ : Cx} {a a' b b' c c' : RTm Γ} (f : RTm Γ → RTm Γ → RTm Γ → RTm Γ) →
         a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃' f refl refl refl = refl

extSK-vs : {Γ : Cx} (i m x : RTm Γ) →
           extSK i (Var-vsK m x) ⟶*
             app (app (app extVs i)
                      (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                            (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
                 (iihs KnotD extMethsK (isingle i) (ilookupD KnotD 52)
                       (pair m (pair x (pair (idrefl ⌜Nat⌝ sVar)
                                             (pair (idrefl ⌜Nat⌝ (nsuc m)) unit)))))
extSK-vs i m x =
  step (ι-ielim KnotD i extMethsK tagVar-vs _)
       (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
         (constMethsFrom-past (cdTake 51 KnotD) (suc zero) »
          sel-there≡ 0 refl (sel-here≡ refl)))))

-- ★ PROBE — the `vs` case, with the jsub chain that already worked, and
--   `done` at the wrapper so the remaining goal is legible.
extS-Represents :
  {Γ Δ Θ : Cx} {σ : Sub Γ Δ} {s : RTm Θ} (d : RTm Θ) →
  Represents σ s → Represents (extS σ) (extNK d (num (len Δ)) s)
extS-Represents d h vz = extNK-vz d _ _ _
extS-Represents {Γ} {Δ} {Θ} {σ = σ} {s = s} d h (vs x) =
  step (β _ _)
    (⟶*-castₗ (cong₃' (λ a b c → app (app (extSK (pair sVar (nsuc a)) (enVar (vs x))) b) c)
                      (wk-single {v = enVar (vs x)} d)
                      (wk-single {v = enVar (vs x)} (num (len Δ)))
                      (wk-single {v = enVar (vs x)} s))
      (⟶*-appˡ (⟶*-appˡ (extSK-vs _ _ _)) »
       ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done)))) »
       ⟶*-appˡ (⟶*-appˡ (⟶*-appˡ (step (β _ _) done))) »
       ⟶*-appˡ (⟶*-appˡ (step (β _ _) done)) »
       ⟶*-appˡ (step (β _ _) done) »
       step (β _ _) done »
       -- ★★★ RECOGNISE THE WRAPPER FIRST.  After the five βs the
       --   substitutions are DISTRIBUTED over `wkTmK`'s unfolding, so
       --   there is no `subTm τ (wkTmK …)` left to rewrite — unless the
       --   five are COLLAPSED into one composite, at which point
       --   `wkTmK-sub` applies and the term is a wrapper again.
       --   ⚠ ORDER MATTERS: this must happen BEFORE reducing inside, or
       --     the equality no longer describes the term.
       ⟶*-castₗ (eqW Bod) (
       ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ
         (⟶*-appʳ (⟶*-jsubᵖ (⟶*-jsubᵖ (⟶*-jsubᵖ
            (sel-there≡ 2 tw (sel-there≡ 1 refl (sel-there≡ 0 refl (sel-here≡ refl)))))) »
                   ⟶*-jsubᵖ (⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done)) »
                   ⟶*-jsubᵖ (step (jsub-refl _ _ _ _) done) »
                   step (jsub-refl _ _ _ _) done »
                   sel-there≡ 0 tw (sel-here≡ refl)) »
          h x))) »
       -- ★ and the DEPTH.  `wkTmK` mentions it three times, so it moves by
       --   an EQUALITY over the whole wrapper, not by reductions.
       ⟶*-castₗ (cong (λ z → wkTmK z (enTm (σ x))) tn) (wkTmK-agree (σ x)))))
  where
    P : RTm Θ
    P = pair (num (len Γ)) (pair (enVar x) (pair (idrefl ⌜Nat⌝ sVar)
          (pair (idrefl ⌜Nat⌝ (nsuc (num (len Γ)))) unit)))
    IH : RTm Θ
    IH = iihs KnotD extMethsK (isingle (pair sVar (nsuc d))) (ilookupD KnotD 52) P
    -- ⚠ AT THE COMPOSITE `τ`, not the nested form — `eqW` collapsed the
    --   five, so every later slot equality must be stated against `τ` and
    --   bridged back with `unc`.  Getting this wrong reads as a CONTEXT
    --   mismatch (`Θ != ((Θ ∙) ∙)`), not as a tower error.
    S₁ = extS (extS (extS (extS (single (pair sVar (nsuc d))))))
    S₂ = extS (extS (extS (single P)))
    S₃ = extS (extS (single IH))
    S₄ = extS (single (num (len Δ)))
    S₅ = single s
    τ  = ((((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂) ∘ₛ S₁)

    -- ⚠ EVERY implicit pinned; a composite left as `_` blocks and nothing
    --   downstream solves (`meta-standing-for-a-computation`, third time).
    unc : (X : RTm (((((Θ ∙) ∙) ∙) ∙) ∙)) →
          subTm S₅ (subTm S₄ (subTm S₃ (subTm S₂ (subTm S₁ X)))) ≡ subTm τ X
    unc X =
      trans (subTm-subTm {τ = S₅} {σ = S₄} (subTm S₃ (subTm S₂ (subTm S₁ X))))
      (trans (subTm-subTm {τ = S₅ ∘ₛ S₄} {σ = S₃} (subTm S₂ (subTm S₁ X)))
      (trans (subTm-subTm {τ = (S₅ ∘ₛ S₄) ∘ₛ S₃} {σ = S₂} (subTm S₁ X))
             (subTm-subTm {τ = ((S₅ ∘ₛ S₄) ∘ₛ S₃) ∘ₛ S₂} {σ = S₁} X)))

    -- ⚠ PARAMETERISED OVER THE BODY.  Writing the body out invites
    --   getting it wrong (it is `app σ (jsub …)`, not a projection), and
    --   the lemma does not care what it is.
    eqW : (B : RTm (((((Θ ∙) ∙) ∙) ∙) ∙)) →
          subTm S₅ (subTm S₄ (subTm S₃ (subTm S₂ (subTm S₁ (wkTmK (var (vs vz)) B)))))
          ≡ wkTmK (subTm τ (var (vs vz))) (subTm τ B)
    eqW B = trans (unc (wkTmK (var (vs vz)) B)) (wkTmK-sub τ (var (vs vz)) B)

    -- ⚠ `extVs`'s body, written out.  `eqW`'s `B` cannot be inferred: the
    --   cast's target is fixed by the chain that FOLLOWS it, and that
    --   chain still has metas of its own.
    Bod : RTm (((((Θ ∙) ∙) ∙) ∙) ∙)
    Bod = app (var vz)
            (jsub (⌜IMu⌝ KnotD IPair (pair sVar (var vz)))
                  (symN (predTm (snd (var (vs (vs (vs (vs vz)))))))
                        (predN (snd (var (vs (vs (vs (vs vz))))))
                               (fst (snd (snd (snd (var (vs (vs (vs vz))))))))))
                  (fst (snd (var (vs (vs (vs vz)))))))

    tw : subTm τ (var (vs (vs (vs vz)))) ≡ P
    tw = trans (sym (unc (var (vs (vs (vs vz))))))
           (trans (cong (λ z → subTm S₅ (subTm S₄ z)) (pw^ {u = IH} 2 P))
           (trans (cong (subTm S₅) (pw^ {u = num (len Δ)} 1 P))
                  (pw^ {u = s} 0 P)))

    tn : subTm τ (var (vs vz)) ≡ num (len Δ)
    tn = trans (sym (unc (var (vs vz)))) (pw^ {u = s} 0 (num (len Δ)))
