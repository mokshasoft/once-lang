------------------------------------------------------------------------
-- OCP-0009 — GAP A, EQUATION 4: `gcd (suc a , suc b) = gcd (suc a , b ∸ a)`
--             PROPOSITIONALLY, AT VARIABLES.  (Route 8 for `⊢S3s`.)
--
-- ⚠ WHAT THE OTHER SEVEN SHARE.  Attempts 45-51 (see GAP-A-ATTEMPTS.md)
--   all build `⊢S3` at the LAYERED type and convert afterwards.  Seven
--   formulations, seven OOMs — including attempt 51, which transported only
--   `⊢PAIRˢ`, whose type is the CLOSED `PairT` and therefore cannot grow.
--
--   ⇒ so it is not the type.  What every failure has in common is that a
--     DERIVATION is pushed through a stack of `Sub⊢-ext`s and `sub-lemma`
--     has to be evaluated.  Route 8 drops that assumption entirely: build
--     the successor branch's derivation AT ITS FINAL CONTEXT from scratch.
--
-- ★ THIS SPIKE TESTS ONLY THE LEAVES, which is where route 8 either works
--   or dies.  Everything is ABSTRACT in `W`/`b` — route 8 never needs the
--   terms, only their derivations, and the pattern says abstract is cheap.
--
--   ⇒ if this is fast, route 8's leaves are free and the rest is `⊢lam`/
--     `⊢app` assembly plus one TERM equality (cheap peels, not a
--     derivation transport).
--   ⇒ if this OOMs, the cost is not the transport either, and the whole
--     reading in GAP-A-ATTEMPTS.md is wrong.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Gcd.LeEq where
open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂; sym; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTy; El; Hom; Nat; Id; RTm; nsuc; pair; fst; snd; ⌜Nat⌝; Ren; renTy
        ; var; vz; vs; lam; app; Sub; extS; subTm; subTy; natrec; nzero
        ; renTm; extR; subTm-renTm; subTm-cong; subTm-id )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _▹_; _⊢_∷_; ⊢pair; ⊢nsuc; ⊢conv; ty-Nat; csymᵀ; single
        ; nrs; ⊢lam; ⊢app; ⊢var; here; wk-single; ⊢natrec; _≅ᵀ_; El-⌜Nat⌝
        ; ⊢nzero; done; ty-Hom )
open import DirectedHoTT.Metatheory.Injectivity using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import DirectedHoTT.Lib.Strong
  using ( ⊢le-refl; reflTm; natAsEl; elAsNat )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Wk
  using ( w; wᶠ; ren-w; pw3; pw4; pw5; nrs-w; cong₃; sub-w; wfw-single; w²-single )
open import DirectedHoTT.Lib.Pair using ( PairT; ⊢PairT ; msrPair)
open import DirectedHoTT.Lib.Amrec
  using ( aIHTat-ren; Prv; prv; idToRed; idOfRed )
open import DirectedHoTT.Lib.Nat using ( plusTm; ⊢plus )
open import DirectedHoTT.Lib.Monus using ( monusTm; ⊢monus )
open import DirectedHoTT.Lib.ArithComm
  using ( plusMonoLTm; plusMonoLTm-sub; congAt; ⊢congAt; IdN )
open import DirectedHoTT.Lib.ArithMonus
  using ( monusLtTm; monusLtTm-sub; ⊢desc-left; monusLeTm; ⊢monusLe
        ; descLeftTm; descLeftTm-sub; ⊢monusLeAt )
open import DirectedHoTT.Examples.Gcd.Step
  using ( gcdIH; gcdG; ⊢gcdIH; KS; NS; PAIRˢ; CERTˢ; msr; ⊢msr; gcdStp
        ; gcdIH-ren )
open import DirectedHoTT.Lib.Natrec using ( ⊢natrec-var; ⊢natrec-var-at )
open import DirectedHoTT.Examples.Gcd.LeMid
  using ( gXx; R1'; W'; R2'; S3'; Z3'; D3'; ⊢W'; Ss-collapse; Zs-collapse
        ; D3-clean; ⊢M3s; ⊢Z3s; midAt; MID; RHSz; gcd-le-prefix; gcd-le-tail )

------------------------------------------------------------------------
-- ★ THE FINAL CONTEXT.  `⊢S3s` lives at `(Γ ▹ Nat) ▹ <the small motive>`,
--   and the `⊢lam` binds one more, so the leaves sit THREE deep.
--
--   That is one slot shallower than `⊢PAIRˢ`'s home (8 slots) — and being
--   deeper is exactly why attempt 51 was WORSE than attempt 50.
------------------------------------------------------------------------

------------------------------------------------------------------------
module _ {Γ : Ctx} {W b : RTm ⌊ Γ ⌋}
         (dW : Γ ⊢ W ∷ Nat) (db : Γ ⊢ b ∷ Nat) where

  -- the motive at the branch's own depth
  μS : RTm ((⌊ Γ ⌋ ∙) ∙)
  μS = plusTm (nsuc (w (w W))) (nsuc (w (w b)))

  SΓ : Ctx
  SΓ = ((Γ ▹ Nat) ▹ gcdG (plusTm (nsuc (w W)) (nsuc (w b)))) ▹ gcdIH μS

  -- ★ the two slots the substitution stack WOULD have produced, written
  --   directly.  `μs-computes` already proved the stack lands here.
  K* : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)
  K* = w (w (w W))

  N* : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)
  N* = w (w (w b))

  -- ⚠ THREE `⊢wk`s, not a `sub-lemma` — weakening a derivation at `Nat` is
  --   structural and never touches a `Sub⊢` stack.
  dK : SΓ ⊢ K* ∷ Nat
  dK = ⊢wk (⊢wk (⊢wk dW))

  dN : SΓ ⊢ N* ∷ Nat
  dN = ⊢wk (⊢wk (⊢wk db))

  ------------------------------------------------------------------------
  -- ★★ LEAF 1 — the recursive call's ARGUMENT.
  ------------------------------------------------------------------------

  PAIR* : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)
  PAIR* = pair (monusTm (nsuc K*) (nsuc N*)) (nsuc N*)

  ⊢PAIR* : SΓ ⊢ PAIR* ∷ PairT
  ⊢PAIR* = ⊢pair ty-Nat (⊢monus (⊢nsuc dK) (⊢nsuc dN)) (⊢nsuc dN)

  ------------------------------------------------------------------------
  -- ★★ LEAF 2 — the DESCENT CERTIFICATE.  `a > b`, so the FIRST component
  --   shrinks and this is `⊢desc-left`.
  ------------------------------------------------------------------------

  CERT* : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)
  CERT* = plusMonoLTm (monusTm (nsuc K*) (nsuc N*)) (nsuc K*) (nsuc N*)
                      (monusLtTm K* N*)

  ⊢CERT* : SΓ ⊢ CERT*
         ∷ Hom Nat (nsuc (plusTm (fst PAIR*) (snd PAIR*)))
                   (plusTm (nsuc K*) (nsuc N*))
  ⊢CERT* =
    ⊢conv (⊢desc-left dK dN)
          (csymᵀ (msrPair (monusTm (nsuc K*) (nsuc N*)) (nsuc N*)
                           (plusTm (nsuc K*) (nsuc N*))))

  -- ★ the measure slot as the APPLICATION leaves it, moved back by two
  --   `wfw-single`s — one per component of the measure.
  appEq : subTm (single PAIR*) (wᶠ (w μS)) ≡ plusTm (nsuc K*) (nsuc N*)
  appEq = cong₂ (λ x y → plusTm (nsuc x) (nsuc y))
                (wfw-single (w (w W))) (wfw-single (w (w b)))

  ⊢CERT*' : SΓ ⊢ CERT*
          ∷ Hom Nat (nsuc (plusTm (fst PAIR*) (snd PAIR*)))
                    (subTm (single PAIR*) (wᶠ (w μS)))
  ⊢CERT*' =
    ⊢-cast (cong (λ t → Hom Nat (nsuc (plusTm (fst PAIR*) (snd PAIR*))) t)
                 (sym appEq))
           ⊢CERT*


------------------------------------------------------------------------
-- ★★★★★ THE PEELS, GENERIC IN WHAT IS SUBSTITUTED.
--
-- ⚠ MEASURED, AND IT IS THE AbsProbe LESSON AGAIN.  Stated CONCRETELY —
--   `eqK = pw3 (W' a' b')` — this module costs 6m47s, because matching
--   `pw3`'s type forces Agda to build `w⁴ (W' a' b')`, and `W'` unfolds
--   through `R1'`'s `natrec`.
--
--   The peels never look at WHAT is substituted, only at DEPTH.  So the
--   five slots are parameters here and nothing unfolds.
--
-- ★ REUSABLE.  This is "a variable at depth d survives a five-level
--   `extS`-stack and peels to `wᵈ`" — nothing gcd-specific except which
--   two depths are named.  Library candidate once it is green.
------------------------------------------------------------------------

module Peels {Γ' : Cx} (g q p u r : RTm Γ') where

  s0 : Sub (Γ' ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙) (Γ' ∙ ∙ ∙ ∙ ∙ ∙ ∙)
  s0 = extS (extS (extS (extS (extS (extS (extS (single g)))))))
  s1 : Sub (Γ' ∙ ∙ ∙ ∙ ∙ ∙ ∙) (Γ' ∙ ∙ ∙ ∙ ∙ ∙)
  s1 = extS (extS (extS (extS (extS (extS (single q))))))
  s2 : Sub (Γ' ∙ ∙ ∙ ∙ ∙ ∙) (Γ' ∙ ∙ ∙ ∙ ∙)
  s2 = extS (extS (extS (extS (extS (single p)))))
  s3 : Sub (Γ' ∙ ∙ ∙ ∙ ∙) (Γ' ∙ ∙ ∙ ∙)
  s3 = extS (extS (extS (extS (single u))))
  s4 : Sub (Γ' ∙ ∙ ∙ ∙) (Γ' ∙ ∙ ∙)
  s4 = extS (extS (extS (single r)))

  -- `k'` sits at `vs⁴ vz`: `s0`-`s2` fix it (each lifts past its depth),
  -- `s3` is its slot, `s4` peels one.
  eqK : subTm s4 (subTm s3 (subTm s2 (subTm s1 (subTm s0 KS)))) ≡ w (w (w u))
  eqK = pw3 u

  -- `n'` sits at `vs⁶ vz`: `s0` fixes it, `s1` is its slot, then three peels.
  eqN : subTm s4 (subTm s3 (subTm s2 (subTm s1 (subTm s0 NS)))) ≡ w (w (w q))
  eqN = trans (cong (λ x → subTm s4 (subTm s3 x)) (pw5 q))
              (trans (cong (subTm s4) (pw4 q)) (pw3 q))

  -- ★★ the two leaves — `subTm` distributes definitionally over
  --   `pair`/`monusTm`/`nsuc` and over `plusMonoLTm`/`monusLtTm`.
  eqP : subTm s4 (subTm s3 (subTm s2 (subTm s1 (subTm s0 PAIRˢ))))
      ≡ pair (monusTm (nsuc (w (w (w u)))) (nsuc (w (w (w q))))) (nsuc (w (w (w q))))
  eqP = cong₂ (λ x y → pair (monusTm (nsuc x) (nsuc y)) (nsuc y)) eqK eqN

  -- ⚠ FIVE pushes, because `descLeftTm` does not distribute definitionally.
  --   Each is one `descLeftTm-sub`; the peels then land both slots at once.
  eqC : subTm s4 (subTm s3 (subTm s2 (subTm s1 (subTm s0 CERTˢ))))
      ≡ descLeftTm (w (w (w u))) (w (w (w q)))
  eqC =
    trans (trans (cong (λ t → subTm s4 (subTm s3 (subTm s2 (subTm s1 t))))
                       (descLeftTm-sub {σ = s0} KS NS))
            (trans (cong (λ t → subTm s4 (subTm s3 (subTm s2 t)))
                         (descLeftTm-sub {σ = s1} (subTm s0 KS) (subTm s0 NS)))
              (trans (cong (λ t → subTm s4 (subTm s3 t))
                           (descLeftTm-sub {σ = s2} (subTm s1 (subTm s0 KS))
                                                    (subTm s1 (subTm s0 NS))))
                (trans (cong (subTm s4)
                             (descLeftTm-sub {σ = s3}
                                (subTm s2 (subTm s1 (subTm s0 KS)))
                                (subTm s2 (subTm s1 (subTm s0 NS)))))
                       (descLeftTm-sub {σ = s4}
                          (subTm s3 (subTm s2 (subTm s1 (subTm s0 KS))))
                          (subTm s3 (subTm s2 (subTm s1 (subTm s0 NS)))))))))
          (cong₂ descLeftTm eqK eqN)

------------------------------------------------------------------------
-- ★★★★★ `⊢S3s` — THE SUCCESSOR BRANCH, BUILT AND NOT TRANSPORTED.
--
-- ⚠ THE EIGHTH ROUTE, after seven OOMs.  Attempts 45-51 all build `⊢S3` at
--   the layered type and convert afterwards; this one never forms the
--   layered type at all.  Three ingredients, none of which moves a
--   derivation through `sub-lemma`:
--
--     the LEAVES  — `⊢PAIR*`/`⊢CERT*`, built at the final context (5.7s)
--     the PEELS   — `Peels.eqP`/`eqC`, TERM equalities, generic in the
--                   five substituted slots so nothing unfolds
--     the SPINE   — `⊢lam`/`⊢app` directly, because `subTm` already
--                   distributed through `G3s`'s constructors
--
-- ⇒ `⊢natrec-var` wants the branch at `subTy nrs M`, and `Ss-collapse`
--   plus `nrs-w` bridge that to `gcdG μS` — both small types.
------------------------------------------------------------------------

module Assemble {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
                (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) where

  open Peels (gXx a' b') b' (R1' a' b') (W' a' b') (R2' a' b')
    using ( eqP; eqC )

  dW : Γ ⊢ W' a' b' ∷ Nat
  dW = ⊢W' da db

  M : RTy (⌊ Γ ⌋ ∙)
  M = gcdG (plusTm (nsuc (w (W' a' b'))) (nsuc (w b')))

  SΓ' : Ctx
  SΓ' = (Γ ▹ Nat) ▹ M

  -- ★ the spine, at the final context.  Mirrors `⊢G3s` exactly.
  ⊢body : SΓ' ⊢ lam (app (app (var vz) (PAIR* dW db)) (CERT* dW db))
              ∷ gcdG (μS dW db)
  ⊢body =
    ⊢lam (⊢gcdIH (⊢plus (⊢nsuc (⊢wk (⊢wk dW))) (⊢nsuc (⊢wk (⊢wk db)))))
         (⊢app (⊢app (⊢var here) (⊢PAIR* dW db)) (⊢CERT*' dW db))

  -- ★ `S3'` IS that `lam` — `subTm` pushed through on its own.
  S3'-computes : S3' a' b'
               ≡ lam (app (app (var vz) (PAIR* dW db)) (CERT* dW db))
  S3'-computes = cong₂ (λ p c → lam (app (app (var vz) p) c)) eqP eqC

  -- ★ and the bridge `⊢natrec-var` needs, on SMALL types only.
  nrs-eq : subTy nrs M ≡ gcdG (μS dW db)
  nrs-eq =
    trans (Ss-collapse a' b')
          (cong gcdG (cong₂ (λ x y → plusTm (nsuc x) (nsuc y))
                            (nrs-w (W' a' b')) (nrs-w b')))

  ⊢S3s : SΓ' ⊢ S3' a' b' ∷ subTy nrs M
  ⊢S3s =
    subst (λ T → SΓ' ⊢ S3' a' b' ∷ T) (sym nrs-eq)
      (subst (λ t → SΓ' ⊢ t ∷ gcdG (μS dW db)) (sym S3'-computes) ⊢body)


------------------------------------------------------------------------
-- ★★★★★ AND THE ASSEMBLY — `⊢natrec` DIRECTLY, NO SUBSTITUTION AT ALL.
--
-- ⚠ THIS IS THE STEP THAT OOMed FOUR TIMES (attempts 34-37).  Every one of
--   those routed through `⊢natrec-at`/`⊢natrec-var-push`, i.e. through a
--   `Sub⊢` stack, because the three pieces were at LAYERED types and had to
--   be pushed into agreement.
--
-- ★ With all three at `gcdG` form the PRIMITIVE rule applies as-is: its
--   premises are literally `⊢ty M`, `∷ subTy (single nzero) M` and
--   `∷ subTy nrs M`, which is exactly what the collapse produces.  The
--   only work left is the zero branch's own one-step bridge.
------------------------------------------------------------------------

module Assemble2 {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
                 (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) where

  open Assemble da db using ( M; ⊢S3s )

  -- ★ the zero branch's bridge — `Zs-collapse` then two `wk-single`s.
  z-eq : subTy (single nzero) M ≡ gcdG (plusTm (nsuc (W' a' b')) (nsuc b'))
  z-eq =
    trans (Zs-collapse a' b')
          (cong gcdG (cong₂ (λ x y → plusTm (nsuc x) (nsuc y))
                            (wk-single (W' a' b')) (wk-single b')))

  ⊢D3 : Γ ⊢ D3' a' b' ∷ Nat
  ⊢D3 = subst (λ t → Γ ⊢ t ∷ Nat) (sym (D3-clean a' b'))
              (⊢monus (⊢nsuc da) (⊢nsuc db))

  ⊢MIDnr : Γ ⊢ natrec (Z3' a' b') (S3' a' b') (D3' a' b')
             ∷ subTy (single (D3' a' b')) M
  ⊢MIDnr = ⊢natrec (⊢M3s da db) (⊢-cast (sym z-eq) (⊢Z3s da db)) ⊢S3s ⊢D3


------------------------------------------------------------------------
-- ★ PROBE: the ONE-HOLE form, via `⊢natrec-var`.  `⊢congAt` wants the
--   context typed with the descent as a HOLE, not at `D3'`.
------------------------------------------------------------------------

module Hole {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
            (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) where

  open Assemble da db using ( M; ⊢S3s )
  open Assemble2 da db using ( z-eq )

  ⊢hole : (Γ ▹ Nat) ⊢ natrec (w (Z3' a' b'))
                             (renTm (extR (extR vs)) (S3' a' b'))
                             (var vz)
                    ∷ M
  ⊢hole = ⊢natrec-var (⊢M3s da db) (⊢-cast (sym z-eq) (⊢Z3s da db)) ⊢S3s


------------------------------------------------------------------------
-- ★★★★★ THE ONE-HOLE CONTEXT, AT `El ⌜Nat⌝` — WHAT `⊢congAt` ACTUALLY WANTS.
--
-- ⚠ THE MISMATCH THAT BLOCKED THIS.  `⊢congAt`'s family is typed in
--   `Γ ▹ El ⌜Nat⌝`, not `Γ ▹ Nat`, because `⊢jsub`'s family lives over the
--   IDENTITY's type and `IdN` is `Id (El ⌜Nat⌝) _ _`.  `⊢natrec-var` bakes
--   `Nat` into its conclusion, so it could not be handed over at all.
--
-- ★ FIXED IN THE LIBRARY, not here: `⊢natrec-var-at` takes the scrutinee's
--   derivation as a parameter, which is exactly where the `El ⌜Nat⌝ → Nat`
--   conversion goes.  `nv-at`/`nv-z`/`nv-s` needed no change — they only
--   ever spoke about `renTy (extR vs)`, which does not care what was pushed.
------------------------------------------------------------------------

module HoleE {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
             (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) where

  open Assemble  da db using ( M; ⊢S3s )
  open Assemble2 da db using ( z-eq )

  ⊢holeE : (Γ ▹ El ⌜Nat⌝) ⊢ natrec (w (Z3' a' b'))
                                   (renTm (extR (extR vs)) (S3' a' b'))
                                   (var vz)
                          ∷ M
  ⊢holeE = ⊢natrec-var-at (elAsNat (⊢var here))
                          (⊢M3s da db) (⊢-cast (sym z-eq) (⊢Z3s da db)) ⊢S3s


------------------------------------------------------------------------
-- ★★ …AND THE FULL ONE-HOLE FAMILY, `∷ Nat`, WHICH IS `⊢congAt`'s PREMISE.
--
-- `midAt a' b' ih d = app (natrec …) ih`, so the family is that `app` with
-- the descent as `var vz` and everything else weakened past it.
------------------------------------------------------------------------

module HoleF {Γ : Ctx} {a' b' ih : RTm ⌊ Γ ⌋}
             (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat)
             (dih : Γ ⊢ ih ∷ gcdIH (plusTm (nsuc (W' a' b')) (nsuc b'))) where

  open HoleE da db using ( ⊢holeE )

  -- the IH, past the hole's slot
  dihw : (Γ ▹ El ⌜Nat⌝) ⊢ w ih
       ∷ gcdIH (plusTm (nsuc (w (W' a' b'))) (nsuc (w b')))
  dihw = ⊢-cast (gcdIH-ren (plusTm (nsuc (W' a' b')) (nsuc b'))) (⊢wk dih)

  ⊢F : (Γ ▹ El ⌜Nat⌝)
     ⊢ app (natrec (w (Z3' a' b'))
                   (renTm (extR (extR vs)) (S3' a' b'))
                   (var vz))
           (w ih)
     ∷ Nat
  ⊢F = elAsNat (⊢app ⊢holeE dihw)


------------------------------------------------------------------------
-- ★★★★★ THE TRANSPORT — EQUATION 4's `congAt` STEP.
--
-- ⭐ SOUND because gcd's third `natrec` has a motive CONSTANT in its own
--   scrutinee, so replacing the descent cannot change the type and a plain
--   congruence suffices where a dependent motive would need a transport.
------------------------------------------------------------------------

module Eq4 {Γ : Ctx} {a' b' ih : RTm ⌊ Γ ⌋}
           (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat)
           (dih : Γ ⊢ ih ∷ gcdIH (plusTm (nsuc (W' a' b')) (nsuc b')))
           {p : RTm ⌊ Γ ⌋} (dp : Γ ⊢ p ∷ IdN (D3' a' b') nzero) where

  open HoleF     da db dih using ( ⊢F )
  open Assemble2 da db     using ( ⊢D3 )

  F : RTm (⌊ Γ ⌋ ∙)
  F = app (natrec (w (Z3' a' b'))
                  (renTm (extR (extR vs)) (S3' a' b'))
                  (var vz))
          (w ih)

  -- ★ the family, instantiated, IS `midAt` — three weakening cancels.
  F-at : (x : RTm ⌊ Γ ⌋) → subTm (single x) F ≡ midAt a' b' ih x
  F-at x = cong₃ (λ z sb i → app (natrec z sb x) i)
                 (wk-single {v = x} (Z3' a' b'))
                 (w²-single {x = x} (S3' a' b'))
                 (wk-single {v = x} ih)

  ⊢transport : Γ ⊢ congAt F (D3' a' b') p
             ∷ IdN (subTm (single (D3' a' b')) F) (subTm (single nzero) F)
  ⊢transport = ⊢congAt F ⊢F ⊢D3 ⊢nzero dp


------------------------------------------------------------------------
-- ★★★★★ EQUATION 4, PROPOSITIONALLY — AT VARIABLES.
--
-- ⚠ WHY THE PREMISE IS AN ORDER PROOF AND NOT A REDUCTION.  `gcd-le-term`
--   demands `monus (suc a) (suc b) ⟶* nzero`; with `b` a numeral the
--   descent computes to `a`, so that forces `a ⟶* zero` — and a VARIABLE
--   never reduces.  `…GcdStep` records this: equation 4 at real variables
--   is UNREACHABLE through a reduction premise.
--
-- ★ SO THE PREMISE IS `Hom Nat (suc a) (suc b)` — the kernel's order,
--   which COMPUTES — and `⊢monusLeAt` turns it into the propositional
--   `a ∸ b ≡ 0` that `congAt` transports along.
------------------------------------------------------------------------

module Eq4! {Γ : Ctx} {a' b' ih le : RTm ⌊ Γ ⌋}
            (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat)
            (dih : Γ ⊢ ih ∷ gcdIH (plusTm (nsuc (W' a' b')) (nsuc b')))
            (dle : Γ ⊢ le ∷ Hom Nat (nsuc a') (nsuc b')) where

  -- the order premise, as the identity `congAt` needs
  dp : Γ ⊢ app (app (monusLeTm (nsuc a')) (nsuc b')) le ∷ IdN (D3' a' b') nzero
  dp = ⊢-cast (cong (λ z → IdN z nzero) (sym (D3-clean a' b')))
              (⊢monusLeAt (⊢nsuc da) (⊢nsuc db) dle)

  open Eq4 da db dih dp using ( F; F-at; ⊢transport )

  -- the transport, restated at `midAt`
  step : Prv Γ (Id (El ⌜Nat⌝) (midAt a' b' ih (D3' a' b')) (midAt a' b' ih nzero))
  step = prv _ (⊢-cast (cong₂ (λ x y → Id (El ⌜Nat⌝) x y)
                              (F-at (D3' a' b')) (F-at nzero))
                       ⊢transport)

  -- ★★★ …AND THE EQUATION.  Prefix reduces in, tail reduces out, the
  --   transport bridges the descent in the middle.
  eq4 : Prv Γ (Id (El ⌜Nat⌝)
                  (app (app gcdStp (pair (nsuc a') (nsuc b'))) ih)
                  (RHSz a' b' ih))
  eq4 = idToRed done (gcd-le-tail a' b' ih)
          (idOfRed (gcd-le-prefix a' b' ih) done step)


------------------------------------------------------------------------
-- ★★★★★ NON-VACUITY FOR EQUATION 4 — AT A VARIABLE.
--
-- ⚠ WHAT WAS STRUCTURALLY UNREACHABLE.  `…GcdStep` records that equation
--   4's REDUCTION premise `monus (suc a) (suc b) ⟶* nzero` forces BOTH `a`
--   and `b` ground — with `b` a numeral the descent computes to `a`, so it
--   demands `a ⟶* zero`, and a variable never reduces.  Hence
--   `gcd-le-at-1` is at numerals, and the file says outright that equation
--   4 at real variables is unreachable through a reduction premise.
--
-- ★ THE ORDER PREMISE IS NOT.  Take `a' := b' := d` with `d` a genuine
--   VARIABLE; `Hom Nat (suc d) (suc d)` is discharged by reflexivity.
--
-- ⚠ THE IH REMAINS A HYPOTHESIS — exactly as in equation 3's `gcd-gt-eq`,
--   where `ih` is likewise supplied.  What is discharged is the premise
--   that was structurally unsatisfiable at variables, which is the whole
--   reason for going propositional.
------------------------------------------------------------------------

eq4-at-var : {Γ : Ctx} {d ih : RTm ⌊ Γ ⌋} (dd : Γ ⊢ d ∷ Nat) →
             Γ ⊢ ih ∷ gcdIH (plusTm (nsuc (W' d d)) (nsuc d)) →
             Prv Γ (Id (El ⌜Nat⌝)
                       (app (app gcdStp (pair (nsuc d) (nsuc d))) ih)
                       (RHSz d d ih))
eq4-at-var dd dih = Eq4!.eq4 dd dd dih (⊢le-refl (⊢nsuc dd))


------------------------------------------------------------------------
-- ★★ …AND THE IH SLOT IS INHABITED, so nothing hides behind `dih`.
--
-- ⚠ WHY THIS MATTERS.  `eq4-at-var` discharges the ORDER premise but still
--   takes the IH as a hypothesis.  If `gcdIH` were empty the instance would
--   be vacuous again, one level down.  It is not: a CONSTANT function
--   inhabits it, so the whole premise set is satisfiable at a variable.
------------------------------------------------------------------------

ihTriv : {Γ : Cx} → RTm Γ
ihTriv = lam (lam nzero)

⊢ihTriv : {Γ : Ctx} {μ : RTm ⌊ Γ ⌋} → Γ ⊢ μ ∷ Nat → Γ ⊢ ihTriv ∷ gcdIH μ
⊢ihTriv dμ =
  ⊢lam ⊢PairT (⊢lam (ty-Hom ty-Nat (⊢nsuc ⊢msr) (⊢wk dμ)) (natAsEl ⊢nzero))

-- ★★★★★ EQUATION 4, WITH EVERY PREMISE DISCHARGED, at a VARIABLE `d`.
eq4-unconditional :
  {Γ : Ctx} {d : RTm ⌊ Γ ⌋} (dd : Γ ⊢ d ∷ Nat) →
  Prv Γ (Id (El ⌜Nat⌝)
            (app (app gcdStp (pair (nsuc d) (nsuc d))) ihTriv)
            (RHSz d d ihTriv))
eq4-unconditional dd =
  eq4-at-var dd (⊢ihTriv (⊢plus (⊢nsuc (⊢W' dd dd)) (⊢nsuc dd)))
