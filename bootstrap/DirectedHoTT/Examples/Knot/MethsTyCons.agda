------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ `methsTyFrom`'s `cDesc-cons` ROW.
--
--     methsTyFrom D M j (C ◃ E) = Σ' (methTy D j C M)
--                                    (renTy vs (methsTyFrom D M (suc j) E))
--
-- ⚠⚠ `cDesc-cons` HAS **TWO** `iρ` FIELDS — `rec("sDCon", D)` then
--   `rec("sDesc", D)` — so the IH tuple has two entries and the RECURSIVE
--   one is the SECOND.  `⊢ihSkipρ` steps past the `DCon` child's IH
--   (which exists, is well typed, and is useless: it is the motive at
--   index `(sDCon , n)`), and only then does `⊢ihHere` land on `E`'s.
--   ★ `Lib/IPay`'s note on `⊢ihSkipκ` warns about the dual mistake —
--     counting a NON-recursive field into the chain.  This is the other
--     half: a recursive field that is not the recursion you want.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.MethsTyCons where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IMu; app; fst; iρ; iκ; iι
        ; ⌜Id⌝; ⌜Nat⌝; isingle; iext; unit; nsuc )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; ⊢var; here; there
        ; ⊢snd; ⊢fst; ⊢lam; ⊢nsuc; ty-Nat; ty-IMu; imethTy )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTy; ⊢sTy; sDesc; ⊢sDesc; sDCon; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cDesc-cons )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cDesc-consWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDesc-cons )
open import DirectedHoTT.Examples.Knot.Ctors using ( Ty-SgK )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkTyK )
open import DirectedHoTT.Examples.Knot.MethTy using ( methTyK )
open import DirectedHoTT.Examples.Knot.MethsTyMot
  using ( methsTyMotK; ⊢methsTyMotK; ⊢methsAppK; ⊢methsRowCons )

methsTyCons : {Γ : Cx} → RTm Γ
methsTyCons =
  lam (lam (lam (lam (lam (lam
    (Ty-SgK (methTyK (snd (var (vs (vs (vs (vs (vs vz)))))))   -- n = snd ⟨i⟩
                     (var vz)                                   -- j
                     (var (vs (vs vz)))                         -- D
                     (fst (var (vs (vs (vs (vs vz)))))) -- C = fst payload
                     (var (vs vz)))                             -- M
            (wkTyK (snd (var (vs (vs (vs (vs (vs vz)))))))
                   (app (app (app (fst (snd (var (vs (vs (vs vz)))))) -- 2nd IH
                                  (var (vs (vs vz))))                 -- D
                             (var (vs vz)))                           -- M
                        (nsuc (var vz)))))))))) -- suc j

⊢methsTyCons : {Γ : Ctx} →
               Γ ⊢ methsTyCons ∷ imethTy KnotD IPair tagDesc-cons cDesc-cons
                                   methsTyMotK
⊢methsTyCons =
  ⊢methLam KnotD IPair tagDesc-cons cDesc-cons KnotWf cDesc-consWf
           ⊢IPair ⊢methsTyMotK
    (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢snd (⊢var (there (there here))))))
      (⊢lam (ty-IMu KnotWf
               (⊢ixP ⊢sTy (⊢nsuc (⊢snd (⊢var (there (there (there here))))))))
        (⊢lam ty-Nat
          (⊢methsRowCons dn dj dD dC dM
            -- ⚠ `dd`/`u` PINNED.  They appear only under `iinst`, a
            --   DEFINED function and so not injective — Agda unfolds and
            --   the metas never solve (`pin-implicits-on-defined-set-types`).
            (⊢methsAppK {dd = snd (var (vs (vs (vs (vs (vs vz)))))) }
                        {u = fst (snd (var (vs (vs (vs (vs vz)))))) }
                        dIH dD dM (⊢nsuc dj))))))
  where
    dn = ⊢snd (⊢var (there (there (there (there (there here))))))
    dD = ⊢var (there (there here))
    dM = ⊢var (there here)
    dj = ⊢var here
    dC = ⊢fst (⊢var (there (there (there (there here)))))
    -- ★ SKIP the `sDCon` child's IH, THEN take `E`'s.
    dIH = ⊢ihHere
            {D = KnotD} {I = IPair}
            {σ = iext (isingle (var (vs (vs (vs (vs (vs vz)))))))
                      (fst (var (vs (vs (vs (vs vz))))))}
            {j = pair sDesc (snd (var (vs vz)))}
            (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDesc) iι)
            {q = snd (var (vs (vs (vs (vs vz)))))} {M = methsTyMotK}
            (⊢ihSkipρ
               {D = KnotD} {I = IPair}
               {σ = isingle (var (vs (vs (vs (vs (vs vz)))))) }
               {j = pair sDCon (snd (var vz))}
               (iρ (pair sDesc (snd (var (vs vz))))
                   (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sDesc) iι))
               {q = var (vs (vs (vs (vs vz))))} {M = methsTyMotK}
               (⊢var (there (there (there here)))))
