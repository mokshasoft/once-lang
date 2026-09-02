------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `ilookupD`, OBJECT-LEVEL.
--
--     ilookupD : IDesc → ℕ → ICon (ε ∙)     `Spec/Syntax:1113`
--     ilookupD inil    _       = iι
--     ilookupD (C ◂ D) zero    = C
--     ilookupD (C ◂ D) (suc k) = ilookupD D k
--
-- ⚠ `⊢icon` names it and so does `ι-ielim`.
--
-- ★★★ THE SIBLING OF `Knot/LookupD`, AND IT IS SIMPLER FOR ONE REASON
--   WORTH NAMING: `ilookupD`'s RESULT IS AT AN ABSOLUTE DEPTH.  An
--   `ICon (ε ∙)` lives at 1 whatever the description's depth is — `KNOT`
--   says so, `rec("sICon", lit 1)` — so the motive's codomain does NOT
--   mention `⟨i⟩`:
--
--       lookupD   Π Nat (K (sDCon , snd ⟨i⟩))    ← index-dependent
--       ilookupD  Π Nat (K (sICon , nsuc nzero)) ← CONSTANT
--
--   ⇒ the `βsnd` conversion `⊢lookupCons`/`⊢lookupDK` both pay does not
--     arise here at all, and neither does the descent cast: a closed
--     index is fixed by every substitution.
--
-- ★ THAT IS THE ANSWER TO "SHOULD THE TWO STEPS BE LIFTED?" — they are
--   NOT a shared shape.  `Knot/LookupD`'s two conversions come from its
--   motive READING THE INDEX; this one's does not, so it needs neither.
--   Lifting them would have abstracted a coincidence.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.ILookupD where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; lam; snd; pair; Π; Nat
        ; ICon; IDesc; εwkTy; IMu; natrec; app; fst; iρ; iκ; iι
        ; ⌜Id⌝; ⌜Nat⌝; isingle; iext; unit; _◂_; ielim; nzero; nsuc )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ⊢lam; ty-Π; ty-Nat; ty-IMu; IConWf; imethTy
        ; ⊢natrec; ⊢app; ⊢fst; ⊢unit; ⊢nzero; ⊢nsuc
        ; imethsTy; imethsTyFrom; IDescWfFrom; ⊢ielim )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢ihHere; ⊢ihSkipρ; ⊢methsFrom; ⊢methsCons
        ; idwfDrop; splTake; Split; spl-nil; spl-step )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsFrom )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sICon; ⊢sICon; sIDesc; ⊢sIDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K; cIDesc-cons )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf; cIDesc-consWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagIDesc-cons )
open import DirectedHoTT.Examples.Knot.Ctors using ( ICon-iK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢ICon-iKv )

-- ★ THE MOTIVE — constant, per the header.
ilookupMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
ilookupMotK = Π Nat (IMu KnotD IPair (pair sICon (nsuc nzero)))

⊢ilookupMotK : {Γ : Ctx} →
               ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty ilookupMotK
⊢ilookupMotK = ty-Π ty-Nat (ty-IMu KnotWf (⊢ixP ⊢sICon (⊢nsuc ⊢nzero)))

-- ★ 52 CONSTANT ROWS — `inil`'s answer is `iι`, which IS the junk.
ilookupJunk : {Γ : Cx} → RTm Γ
ilookupJunk = lam (lam (lam (lam ICon-iK)))

⊢ilookupJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
               IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
               Γ ⊢ ilookupJunk ∷ imethTy KnotD IPair k C ilookupMotK
⊢ilookupJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢ilookupMotK
    (⊢lam ty-Nat (⊢ICon-iKv _ (⊢nsuc ⊢nzero)))

-- ★ THE ONE REAL ROW, row 47.  Same body as `lookupD`'s: the head from
--   the PAYLOAD, the tail's answer from the IH, cased by `natrec`.
ilookupCons : {Γ : Cx} → RTm Γ
ilookupCons =
  lam (lam (lam (lam
    (natrec (fst (var (vs (vs vz))))
            (app (fst (snd (var (vs (vs (vs vz)))))) (var (vs vz)))
            (var vz)))))

⊢ilookupCons : {Γ : Ctx} →
               Γ ⊢ ilookupCons
                 ∷ imethTy KnotD IPair tagIDesc-cons cIDesc-cons ilookupMotK
⊢ilookupCons =
  ⊢methLam KnotD IPair tagIDesc-cons cIDesc-cons KnotWf cIDesc-consWf
           ⊢IPair ⊢ilookupMotK
    (⊢lam ty-Nat
      (⊢natrec (ty-IMu KnotWf (⊢ixP ⊢sICon (⊢nsuc ⊢nzero)))
               (⊢fst (⊢var (there (there here))))
               (⊢app (⊢ihHere
                        {D = KnotD} {I = IPair}
                        {σ = iext (isingle (var (vs (vs (vs (vs (vs vz)))))))
                                  (fst (var (vs (vs (vs (vs vz))))))}
                        {j = pair sIDesc (snd (var (vs vz)))}
                        (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sIDesc) iι)
                        {q = snd (var (vs (vs (vs (vs vz)))))} {M = ilookupMotK}
                        (⊢ihSkipρ {D = KnotD} {I = IPair}
                           {σ = isingle (var (vs (vs (vs (vs (vs vz)))))) }
                           {j = pair sICon (nsuc nzero)}
                           (iρ (pair sIDesc (snd (var (vs vz))))
                             (iκ (⌜Id⌝ ⌜Nat⌝ (fst (var (vs (vs vz)))) sIDesc) iι))
                           {q = var (vs (vs (vs (vs vz))))} {M = ilookupMotK}
                           (⊢var (there (there (there here))))))
                     (⊢var (there here)))
               (⊢var here)))

-- ★ THE TUPLE — rows 0–46 junk · row 47 · rows 48–52 junk.
D48 : IDesc
D48 = cdRest (cdTake 48 KnotD)

D47' : IDesc
D47' = cIDesc-cons ◂ D48

spl47 : Split KnotD 47 D47'
spl47 = splTake spl-nil (cdTake 47 KnotD)

wf48 : IDescWfFrom KnotD IPair D48
wf48 = idwfDrop (spl-step spl47) KnotWf

ilookupTail : {Γ : Cx} → RTm Γ
ilookupTail = methsFrom (cdTake 5 D48) ilookupJunk unit

⊢ilookupTail : {Γ : Ctx} →
               Γ ⊢ ilookupTail ∷ imethsTyFrom KnotD IPair ilookupMotK 48 D48
⊢ilookupTail =
  ⊢methsFrom KnotD IPair 48 (cdTake 5 D48) KnotWf wf48 (spl-step spl47)
             ⊢IPair ⊢ilookupMotK (λ {k} {C} wC _ _ → ⊢ilookupJunk k C wC)
             unit ⊢unit

ilookupMid : {Γ : Cx} → RTm Γ
ilookupMid = pair ilookupCons ilookupTail

⊢ilookupMid : {Γ : Ctx} →
              Γ ⊢ ilookupMid ∷ imethsTyFrom KnotD IPair ilookupMotK 47 D47'
⊢ilookupMid =
  ⊢methsCons KnotD IPair 47 {C = cIDesc-cons} D48 KnotWf wf48
             (spl-step spl47) ⊢IPair ⊢ilookupMotK ⊢ilookupCons ⊢ilookupTail

ilookupMethsK : {Γ : Cx} → RTm Γ
ilookupMethsK = methsFrom (cdTake 47 KnotD) ilookupJunk ilookupMid

⊢ilookupMethsK : {Γ : Ctx} →
                 Γ ⊢ ilookupMethsK ∷ imethsTy KnotD IPair ilookupMotK KnotD
⊢ilookupMethsK =
  ⊢methsFrom KnotD IPair 0 (cdTake 47 KnotD) KnotWf KnotWf spl-nil
             ⊢IPair ⊢ilookupMotK (λ {k} {C} wC _ _ → ⊢ilookupJunk k C wC)
             ilookupMid ⊢ilookupMid

-- ★★ AND THE WRAPPER — ⚠ NO CAST AND NO CONVERSION, unlike
--   `⊢lookupDK`'s two.  A constant motive is fixed by every substitution
--   `iinst` applies, so `iinst i t M` IS `M`.
ilookupDK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ
ilookupDK n d k = app (ielim KnotD (pair sIDesc n) ilookupMethsK d) k

⊢ilookupDK : {Γ : Ctx} {n d k : RTm ⌊ Γ ⌋} →
             Γ ⊢ n ∷ Nat → Γ ⊢ d ∷ K (pair sIDesc n) → Γ ⊢ k ∷ Nat →
             Γ ⊢ ilookupDK n d k ∷ K (pair sICon (nsuc nzero))
⊢ilookupDK dn dd dk =
  ⊢app (⊢ielim KnotWf ⊢ilookupMotK (⊢ixP ⊢sIDesc dn) ⊢ilookupMethsK dd) dk
