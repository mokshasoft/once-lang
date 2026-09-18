------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ REDUCING A DEPTH THROUGH THE `methTy` STACK.
--
-- ⚠⚠ WHY THIS LAYER EXISTS.  `βsnd` is a REDUCTION in this kernel, not a
--   definitional equality, so `snd ⟨i⟩ ⟶ n` has to be pushed into EVERY
--   occurrence of the depth — and `methsTyCons` calls
--   `methTyK (snd ⟨i⟩) …`, whose `n` reaches seven sub-programs.
--   ⇒ `⟶*` reduces one redex at a time; a term mentioning the depth k
--     times costs k descents.  `conSSK`'s trap at scale.
--
-- ★ THE PATTERN IS ALWAYS THE SAME and two instances already existed:
--   `Knot/PayTyAgree.⟶*-wkTyKᵈ` (four descents) and
--   `Knot/ConSAgree.vzLvl` (two).  Everything here is built from those.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.DepthCong where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; app; lam; pair; var; vz; vs; nsuc; ielim; icon; renTm )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-appˡ; ⟶*-appʳ; ⟶*-lam; ⟶*-icon; ⟶*-pairˡ; ⟶*-pairʳ
        ; ⟶*-ielimᵗ; ⟶*-ielimⁱ; ⟶*-nsuc; ⟶*-ren )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Sorts using ( sTy; sVar; sDCon )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-varK; Ty-PiK )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vzK )
open import DirectedHoTT.Examples.Knot.RenTm using ( renTmAtK; vsRenK; renMethsK )
open import DirectedHoTT.Examples.Knot.RenMot using ( extRNK; extRK; extRMethsK )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTyAtK )
open import DirectedHoTT.Examples.Knot.ConS using ( conSK; conSSK; atConK; conSMeths )
open import DirectedHoTT.Examples.Knot.WkSub using ( wkAtK; wkTyK; wkTyUnderK )
open import DirectedHoTT.Examples.Knot.PayTy using ( payTyK )
open import DirectedHoTT.Examples.Knot.IhTy using ( ihTyK )
open import DirectedHoTT.Examples.Knot.MethTy using ( methTyK )
open import DirectedHoTT.Examples.Knot.ConSAgree using ( vzLvl; vsLvl )

-- ★ `renTmAtK s dd m rn t = app (app (renTmK (pair s dd) t) m) rn`.
⟶*-renAtᵈ : {Γ : Cx} {s dd dd' m rn t : RTm Γ} →
            dd ⟶* dd' → renTmAtK s dd m rn t ⟶* renTmAtK s dd' m rn t
⟶*-renAtᵈ h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ h)))

⟶*-renAtᵐ : {Γ : Cx} {s dd m m' rn t : RTm Γ} →
            m ⟶* m' → renTmAtK s dd m rn t ⟶* renTmAtK s dd m' rn t
⟶*-renAtᵐ h = ⟶*-appˡ (⟶*-appʳ h)

⟶*-renAtʳ : {Γ : Cx} {s dd m rn rn' t : RTm Γ} →
            rn ⟶* rn' → renTmAtK s dd m rn t ⟶* renTmAtK s dd m rn' t
⟶*-renAtʳ h = ⟶*-appʳ h

-- ★ `vsRenK n = lam (Var-vsK (w n) (var vz))` — the level occurs TWICE
--   inside `Var-vsK` (level and ford), which is `ConSAgree.vsLvl`.
⟶*-vsRenKᵈ : {Γ : Cx} {n n' : RTm Γ} → n ⟶* n' → vsRenK n ⟶* vsRenK n'
⟶*-vsRenKᵈ h = ⟶*-lam (vsLvl (⟶*-ren vs h))

-- ★ `wkAtK s n t = renTmAtK s n (nsuc n) (vsRenK n) t` — FOUR descents.
--   (`Knot/PayTyAgree.⟶*-wkTyKᵈ` is this at `sTy`; this is it generic.)
⟶*-wkAtKᵈ : {Γ : Cx} {s n n' t : RTm Γ} →
            n ⟶* n' → wkAtK s n t ⟶* wkAtK s n' t
⟶*-wkAtKᵈ h = ⟶*-renAtᵈ h » ⟶*-renAtᵐ (⟶*-nsuc h) » ⟶*-renAtʳ (⟶*-vsRenKᵈ h)

-- ★ `extRNK d n ρ = lam (app (app (extRK (pair sVar (nsuc (w d))) (var vz)) (w n)) (w ρ))`
⟶*-extRNKᵈ : {Γ : Cx} {d d' n ρ : RTm Γ} →
             d ⟶* d' → extRNK d n ρ ⟶* extRNK d' n ρ
⟶*-extRNKᵈ h =
  ⟶*-lam (⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (⟶*-ren vs h))))))

⟶*-extRNKⁿ : {Γ : Cx} {d n n' ρ : RTm Γ} →
             n ⟶* n' → extRNK d n ρ ⟶* extRNK d n' ρ
⟶*-extRNKⁿ h = ⟶*-lam (⟶*-appˡ (⟶*-appʳ (⟶*-ren vs h)))

⟶*-extRNKʳ : {Γ : Cx} {d n ρ ρ' : RTm Γ} →
             ρ ⟶* ρ' → extRNK d n ρ ⟶* extRNK d n ρ'
⟶*-extRNKʳ h = ⟶*-lam (⟶*-appʳ (⟶*-ren vs h))

-- ★ `wkTyUnderK n A = renTmAtK sTy (nsuc n) (nsuc (nsuc n))
--                                (extRNK n (nsuc n) (vsRenK n)) A` — SIX.
⟶*-wkTyUnderKᵈ : {Γ : Cx} {n n' A : RTm Γ} →
                 n ⟶* n' → wkTyUnderK n A ⟶* wkTyUnderK n' A
⟶*-wkTyUnderKᵈ h =
    ⟶*-renAtᵈ (⟶*-nsuc h)
  » ⟶*-renAtᵐ (⟶*-nsuc (⟶*-nsuc h))
  » ⟶*-renAtʳ (⟶*-extRNKᵈ h » ⟶*-extRNKⁿ (⟶*-nsuc h) » ⟶*-extRNKʳ (⟶*-vsRenKᵈ h))

-- ★ `conSK n k = lam (conSSK (pair sVar (nsuc (w n))) (var vz) (w k))`
--   and `conSSK i x k = app (ielim KnotD i conSMeths x) k`.
⟶*-conSKᵈ : {Γ : Cx} {n n' k : RTm Γ} → n ⟶* n' → conSK n k ⟶* conSK n' k
⟶*-conSKᵈ h =
  ⟶*-lam (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsuc (⟶*-ren vs h)))))

-- ★ `subTyAtK dd m σ t = app (app (subTmK (pair sTy dd) t) m) σ`.
⟶*-subAtᵈ : {Γ : Cx} {dd dd' m σ t : RTm Γ} →
            dd ⟶* dd' → subTyAtK dd m σ t ⟶* subTyAtK dd' m σ t
⟶*-subAtᵈ h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ h)))

⟶*-subAtᵐ : {Γ : Cx} {dd m m' σ t : RTm Γ} →
            m ⟶* m' → subTyAtK dd m σ t ⟶* subTyAtK dd m' σ t
⟶*-subAtᵐ h = ⟶*-appˡ (⟶*-appʳ h)

⟶*-subAtˢ : {Γ : Cx} {dd m σ σ' t : RTm Γ} →
            σ ⟶* σ' → subTyAtK dd m σ t ⟶* subTyAtK dd m σ' t
⟶*-subAtˢ h = ⟶*-appʳ h

-- ★ `atConK n k M = subTyAtK (nsuc n) (nsuc n) (conSK n k) M`.
⟶*-atConKᵈ : {Γ : Cx} {n n' k M : RTm Γ} →
             n ⟶* n' → atConK n k M ⟶* atConK n' k M
⟶*-atConKᵈ h =
  ⟶*-subAtᵈ (⟶*-nsuc h) » ⟶*-subAtᵐ (⟶*-nsuc h) » ⟶*-subAtˢ (⟶*-conSKᵈ h)

-- ★ the two eliminator wrappers — their depth occurs ONCE each.
⟶*-payTyKᵈ : {Γ : Cx} {n n' c d : RTm Γ} →
             n ⟶* n' → payTyK n c d ⟶* payTyK n' c d
⟶*-payTyKᵈ h = ⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ h))

⟶*-ihTyKᵈ : {Γ : Cx} {n n' c q M : RTm Γ} →
            n ⟶* n' → ihTyK n c q M ⟶* ihTyK n' c q M
⟶*-ihTyKᵈ h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimⁱ (⟶*-pairʳ h)))

⟶*-ihTyKᶜ' : {Γ : Cx} {n c c' q M : RTm Γ} →
             c ⟶* c' → ihTyK n c q M ⟶* ihTyK n c' q M
⟶*-ihTyKᶜ' h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ h))

⟶*-ihTyKᵠ : {Γ : Cx} {n c q q' M : RTm Γ} →
            q ⟶* q' → ihTyK n c q M ⟶* ihTyK n c q' M
⟶*-ihTyKᵠ h = ⟶*-appˡ (⟶*-appʳ h)

⟶*-ihTyKᴹ' : {Γ : Cx} {n c q M M' : RTm Γ} →
             M ⟶* M' → ihTyK n c q M ⟶* ihTyK n c q M'
⟶*-ihTyKᴹ' h = ⟶*-appʳ h

⟶*-wkTyKᵃ' : {Γ : Cx} {n A A' : RTm Γ} → A ⟶* A' → wkTyK n A ⟶* wkTyK n A'
⟶*-wkTyKᵃ' h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ h))

inVarK : {Γ : Cx} {a a' : RTm Γ} → a ⟶* a' → Tm-varK a ⟶* Tm-varK a'
inVarK r = ⟶*-icon (⟶*-pairˡ r)

inPiL' : {Γ : Cx} {a a' b : RTm Γ} → a ⟶* a' → Ty-PiK a b ⟶* Ty-PiK a' b
inPiL' r = ⟶*-icon (⟶*-pairˡ r)

inPiR' : {Γ : Cx} {a b b' : RTm Γ} → b ⟶* b' → Ty-PiK a b ⟶* Ty-PiK a b'
inPiR' r = ⟶*-icon (⟶*-pairʳ (⟶*-pairˡ r))

------------------------------------------------------------------------
-- ★★★ AND THE WHOLE STACK — SEVEN sub-programs, twenty-odd descents.
------------------------------------------------------------------------

⟶*-methTyKᵈ : {Γ : Cx} {n n' k D C M : RTm Γ} →
              n ⟶* n' → methTyK n k D C M ⟶* methTyK n' k D C M
⟶*-methTyKᵈ h =
    inPiL' (⟶*-payTyKᵈ h)
  » inPiR' (inPiL' (⟶*-ihTyKᵈ (⟶*-nsuc h)))
  » inPiR' (inPiL' (⟶*-ihTyKᶜ' (⟶*-wkAtKᵈ h)))
  » inPiR' (inPiL' (⟶*-ihTyKᵠ (inVarK (vzLvl h))))
  » inPiR' (inPiL' (⟶*-ihTyKᴹ' (⟶*-wkTyUnderKᵈ h)))
  » inPiR' (inPiR' (⟶*-wkAtKᵈ (⟶*-nsuc h)))
  » inPiR' (inPiR' (⟶*-wkTyKᵃ' (⟶*-atConKᵈ h)))
