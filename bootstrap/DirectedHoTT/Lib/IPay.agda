------------------------------------------------------------------------
-- OCP-0009 · LIB — ★ `⊢ty` FOR AN INDEXED PAYLOAD, GENERICALLY.
--
-- The missing twin of `Metatheory/SubjectReduction.iihTy-wf`: that one
-- says the IH TUPLE's type is well formed, this one says the PAYLOAD's
-- is.  Both are one induction over the `ICon`.
--
-- ⚠ WHY IT IS NEEDED, and it is a COST result, not a gap.  A method of
--   `imethTy` binds the payload, so writing one requires `⊢ty` of the
--   payload type.  Doing that CONCRETELY — a hand-built `ty-Σ` chain
--   that Agda must then unify against the computed `ipayTy` — is what
--   makes `Examples/Knot/Sz` blow up: measured, a 2-field row costs 1s,
--   a 3-field row 9s, and `ordtr` (SIX fields) exhausts a 7.7 GB box on
--   its own.  Handing Agda a derivation whose type is ALREADY
--   `ipayTy D I σ C` removes the unification entirely.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.IPay where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; RTy; RTm; Unit; Σ'; El; IMu; Nat; Π
        ; renTy; isingle; ipayTy-ren; ipayTy-cong
        ; ICon; IDesc; iι; iρ; iκ; ipayTy; Sub; extS; subTm; subTy
        ; εwkTy; εwk-sub; εwk-ren; _◂_; inil
        ; ilookupD; _∈ID_; icon; subTy-renTy; subTy-cong )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there
        ; _⊢ty_; ty-Unit; ty-Σ; ty-El; ty-IMu; ty-Π; ty-Nat
        ; IConWf; iwf-ι; iwf-ρ; iwf-κ
        ; IDescWf; IDescWfFrom; idwf-nil; idwf-cons
        ; imethTy; imethsTyFrom; ⊢icon; iconS; iatCon )
open import DirectedHoTT.Metatheory.SubjectReduction
  using ( Sub⊢; Sub⊢-ext; sub-lemma; sub-ty; ⊢-cast; ren-ty; ⊢wk
        ; isingle-Sub⊢; iihTy-wf )
open import DirectedHoTT.Lib.Wk using ( ren-subTy )

ipayTy-wf : {Γ Θ : Ctx} (D : IDesc) (I : RTy ε)
            (σ : Sub ⌊ Θ ⌋ ⌊ Γ ⌋) (C : ICon ⌊ Θ ⌋) →
            IDescWf I D → IConWf D I Θ C → Sub⊢ Θ Γ σ →
            Γ ⊢ty ipayTy D I σ C
ipayTy-wf D I σ iι wD wC hσ = ty-Unit
ipayTy-wf D I σ (iρ j C) wD (iwf-ρ .j dj wC) hσ =
  ty-Σ (ty-IMu wD (⊢-cast (εwk-sub σ I) (sub-lemma dj hσ)))
       (ipayTy-wf D I (extS σ) C wD wC (Sub⊢-ext hσ))
ipayTy-wf D I σ (iκ κ C) wD (iwf-κ .κ _ dcode wC) hσ =
  ty-Σ (ty-El (sub-lemma dcode hσ))
       (ipayTy-wf D I (extS σ) C wD wC (Sub⊢-ext hσ))

------------------------------------------------------------------------
-- ★★★ …AND THE SAME FOR A METHOD, AND FOR A WHOLE METHOD TUPLE.
--
-- ⚠ WHY THESE EXIST, and it is the same cost result one level up.
--   `Examples/Knot/Sz` builds the 53-method tuple's `⊢ty` by ENUMERATING
--   its rungs — 53 definitions, each `ty-Σ` whose second argument sits
--   at `Γ ▹ A`, so Agda normalises `renTy vs` through the WHOLE
--   remaining tail at every rung.  That is O(n²), and measured it is
--   most of the module's 140s.
--
--   ⚠ A BETTER RUNG DOES NOT FIX IT.  Discharging the rung by
--   `imethsTyFrom-ren` measured 350s (WORSE — at a concrete tail that
--   lemma unfolds into a chain as long as the tail), and by `ren-ty`
--   it ran out of memory.  The fix is to stop enumerating: ONE
--   induction, at an ABSTRACT tail, is O(n).
--
-- ⚠ SPECIALISED TO A CONSTANT `Nat` MOTIVE.  That is all `sz` needs, and
--   it is what makes the codomain free: `iatCon k i Nat` IS `Nat`, so
--   the third `Π`'s result needs no transport.  A motive-generic version
--   would have to carry `⊢ty M` through `renTy`/`iatCon`; write it when
--   a second customer wants one.
------------------------------------------------------------------------

imethTyNat-wf : {Γ : Ctx} (D : IDesc) (I : RTy ε) (k : ℕ) (C : ICon (ε ∙)) →
                IDescWf I D → IConWf D I (◇ ▹ εwkTy I) C →
                ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
                Γ ⊢ty imethTy D I k C Nat
-- ⚠ THE CONTEXTS ARE PINNED.  `ty-Π`'s second argument lives one binder
--   deeper, and left implicit those contexts are metas that never solve.
imethTyNat-wf {Γ = Γ} D I k C wD wC tI =
  ty-Π tI
    (ty-Π (ipayTy-wf {Γ = Γ ▹ εwkTy I} D I (isingle (var vz)) C
                     wD wC (isingle-Sub⊢ (⊢-cast (εwk-ren vs I) (⊢var here))))
      (ty-Π (iihTy-wf {Γ = (Γ ▹ εwkTy I) ▹ ipayTy D I (isingle (var vz)) C}
                      D I Nat (isingle (var (vs vz))) C (var vz) wC
                      (isingle-Sub⊢ (⊢-cast (trans (cong (renTy vs) (εwk-ren vs I))
                                                   (εwk-ren vs I))
                                            (⊢var (there here)))) ty-Nat
                      -- ⚠ the payload variable, RETYPED.  `⊢var here`
                      --   gives `renTy vs (ipayTy … (isingle (var vz)) C)`
                      --   while the IH tuple is stated at
                      --   `isingle (var (vs vz))`.  The two agree by
                      --   `ipayTy-ren` then `ipayTy-cong`, NOT definitionally.
                      (⊢-cast (trans (ipayTy-ren vs D I (isingle (var vz)) C)
                                     (ipayTy-cong D I C
                                       (λ { vz → refl ; (vs ()) })))
                              (⊢var here)))
            ty-Nat))

-- ★★★ ONE INDUCTION over the description, at an ABSTRACT tail.
imethsTyFromNat-wf : {Γ : Ctx} (D : IDesc) (I : RTy ε) (j : ℕ) (E : IDesc) →
                     IDescWf I D → IDescWfFrom D I E →
                     ({Δ : Ctx} → Δ ⊢ty εwkTy I) →
                     Γ ⊢ty imethsTyFrom D I Nat j E
imethsTyFromNat-wf D I j inil    wD idwf-nil        tI = ty-Unit
imethsTyFromNat-wf D I j (C ◂ E) wD (idwf-cons wC wE) tI =
  ty-Σ (imethTyNat-wf D I j C wD wC tI)
       (ren-ty (imethsTyFromNat-wf D I (suc j) E wD wE tI) there)

------------------------------------------------------------------------
-- ⬜ `iatCon-wf` — SPIKED 2026-08-28, 2 of its 3 cases proved.
--
-- ★ WHY IT MATTERS: it is the ONE thing keeping `imethTyNat-wf` above
--   stuck at `Nat`.  `imethTy`'s codomain is `iatCon k ⟨-⟩ M`, and
--   nobody has shown that is a TYPE at an abstract `M`; all four
--   customers of the method-tuple shape dodge it differently
--   (`Lib/IFold`: M = Nat.  `Lib/IWk`: its own `…Mot-wf`.
--   `Knot/SubMot`: a motive written to IGNORE the scrutinee so `iatCon`
--   computes).  Generalising this module is gated on it.
--
-- ★★ AND THE APPROACH IS SOUND — the statement TYPE-CHECKS:
--
--     iconS-Sub⊢ : IDescWf I D → k ∈ID D → Γ ⊢ i ∷ εwkTy I →
--                  Sub⊢ ((Γ ▹ εwkTy I) ▹ IMu D I (var vz))
--                       (Γ ▹ ipayTy D I (isingle i) (ilookupD D k))
--                       (iconS k i)
--
--   ⚠ `iinst-wf` is the precedent but does NOT generalise to it:
--     `iinst` substitutes a GIVEN term into the scrutinee slot, so its
--     `Sub⊢` is `⊢single`.  `iconS` BUILDS one — `icon k (var vz)` —
--     from the payload binder, so the payload must be in the TARGET
--     context and `⊢single` cannot serve.
--
-- ✅ CASE 1, the scrutinee slot: `⊢icon` with the index weakened
--    (`εwk-ren`) and the payload retyped (`ipayTy-ren` + `ipayTy-cong`)
--    — the same pair `Lib/IFold.⊢ifMethod` uses.
-- ✅ CASE 2, the index slot: `εwkTy I` is CLOSED so all three actions
--    fix it, ⚠ but only PROPOSITIONALLY — `εwkTy` is a defined function,
--    so none of the steps computes and the chain is
--    `εwk-ren`/`εwk-ren`/`εwk-sub` explicitly.
-- ⬜ CASE 3, everything else: needs
--    `subTy (iconS k i) (renTy vs (renTy vs A)) ≡ renTy vs A`.
--    Two `subTy-renTy` steps compose the renamings, then `subTy-cong`
--    identifies `(iconS k i ₛ∘ᵣ vs) ₛ∘ᵣ vs` with `λ x → var (vs x)`;
--    what is missing is the last hop, "substituting by a renaming IS
--    renaming".  ⇒ look for that lemma before writing one.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ `iconS` IS A WELL-TYPED SUBSTITUTION — the lemma the spike above
-- names, now that its missing hop exists.
--
-- ★ WHAT UNBLOCKED IT: `ren-subTy` — "substituting by a renaming IS
--   renaming", at the TYPE level.  It was written long ago and trapped
--   in `Lib/Wk.nrs-wTy`'s `where` block, one scope too deep to find.
--   Its TERM-level twin `ren-sub` was top level all along.
--
-- ⚠ `iinst-wf` is the precedent and does NOT generalise to this:
--   `iinst` substitutes a GIVEN term into the scrutinee slot, so its
--   `Sub⊢` is `⊢single`.  `iconS` BUILDS one — `icon k (var vz)` — from
--   the payload binder, so the payload must live in the TARGET context
--   and `⊢single` cannot serve.
--
-- The three cases are the three clauses of `iconS`:
--   `vz`        ↦ `icon k (var vz)`   — the SCRUTINEE slot
--   `vs vz`     ↦ `renTm vs i`        — the INDEX slot, closed
--   `vs (vs x)` ↦ `var (vs x)`        — everything else
------------------------------------------------------------------------

iconS-Sub⊢ : {Γ : Ctx} (D : IDesc) (I : RTy ε) (k : ℕ) {i : RTm ⌊ Γ ⌋} →
             IDescWf I D → k ∈ID D → Γ ⊢ i ∷ εwkTy I →
             Sub⊢ ((Γ ▹ εwkTy I) ▹ IMu D I (var vz))
                  (Γ ▹ ipayTy D I (isingle i) (ilookupD D k))
                  (iconS k i)
-- ★ CASE 1 — the scrutinee.  `⊢icon` at the WEAKENED index, with the
--   payload retyped: the same `ipayTy-ren`/`ipayTy-cong` pair
--   `Lib/IFold.⊢ifMethod` uses.
iconS-Sub⊢ {Γ = Γ} D I k {i = i} wD mem di here =
  ⊢icon wD mem
        (⊢-cast (εwk-ren vs I) (⊢wk di))
        (⊢-cast (trans (ipayTy-ren vs D I (isingle i) (ilookupD D k))
                       (ipayTy-cong D I (ilookupD D k)
                          (λ { vz → refl ; (vs ()) })))
                (⊢var here))
-- ★ CASE 2 — the index slot.  `εwkTy I` is CLOSED, so every action
--   fixes it — ⚠ but only PROPOSITIONALLY: `εwkTy` is a defined
--   function, so nothing computes and the chain is explicit.
iconS-Sub⊢ D I k {i = i} wD mem di (there here) =
  ⊢-cast (trans (εwk-ren vs I)
                (sym (trans (cong (subTy (iconS k i))
                                  (trans (cong (renTy vs) (εwk-ren vs I))
                                         (εwk-ren vs I)))
                            (εwk-sub (iconS k i) I))))
         (⊢wk di)
-- ★★ CASE 3 — everything else, and the one that was stuck.  Two
--   `subTy-renTy` steps compose the renamings, `subTy-cong` identifies
--   the result with `λ x → var (vs x)`, and `ren-subTy` closes it.
iconS-Sub⊢ D I k {i = i} wD mem di (there (there {A = A₀} v)) =
  ⊢-cast (sym (trans (subTy-renTy {σ = iconS k i} (renTy vs A₀))
                     (trans (subTy-renTy A₀)
                            (trans (subTy-cong (λ _ → refl) A₀)
                                   (sym (ren-subTy {ρ = vs} A₀))))))
         (⊢var (there v))

------------------------------------------------------------------------
-- ★★★ …AND THEREFORE `iatCon k ⟨-⟩ M` IS A TYPE, AT AN ABSTRACT `M`.
--
-- ⚠⚠ THIS IS THE LEMMA THAT WAS GATING `Lib/IPay` OFF `Nat`.  `imethTy`'s
--   codomain is `renTy vs (iatCon k (var vz) M)`, and until now nobody
--   had shown that is a TYPE unless `M` was concrete — so all four
--   customers of the method-tuple shape dodged it differently
--   (`Lib/IFold`: `M = Nat`; `Lib/IWk`: its own `…Mot-wf`;
--   `Knot/SubMot`: a motive written to IGNORE the scrutinee so `iatCon`
--   computes).  ⇒ every new object-level function paid a fresh COPY of
--   the method machinery for want of these four lines.
--
-- ★ And it is four lines because `iatCon k i M` IS `subTy (iconS k i) M`
--   by definition — so once `iconS` is known to be a well-typed
--   substitution, `sub-ty` is the whole proof.
------------------------------------------------------------------------

iatCon-wf : {Γ : Ctx} (D : IDesc) (I : RTy ε) (k : ℕ) {i : RTm ⌊ Γ ⌋}
            {M : RTy ((⌊ Γ ⌋ ∙) ∙)} →
            IDescWf I D → k ∈ID D → Γ ⊢ i ∷ εwkTy I →
            ((Γ ▹ εwkTy I) ▹ IMu D I (var vz)) ⊢ty M →
            (Γ ▹ ipayTy D I (isingle i) (ilookupD D k)) ⊢ty iatCon k i M
iatCon-wf D I k wD mem di wM = sub-ty wM (iconS-Sub⊢ D I k wD mem di)
