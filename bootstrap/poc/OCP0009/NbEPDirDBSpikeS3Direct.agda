------------------------------------------------------------------------
-- OCP-0009 — ROUTE 8 FOR `⊢S3s`: BUILD, DO NOT TRANSPORT.
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
module poc.OCP0009.NbEPDirDBSpikeS3Direct where

open import normalizer.Syntax.Types using ( _≡_; trans; cong; cong₂; sym; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; Hom; Nat; RTm; nsuc; pair; fst; snd
        ; var; vz; vs; lam; app; Sub; extS; subTm; subTy; natrec; nzero
        ; renTm; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ⌊_⌋; _▹_; _⊢_∷_; ⊢pair; ⊢nsuc; ⊢conv; ty-Nat; csymᵀ; single
        ; nrs; ⊢lam; ⊢app; ⊢var; here; wk-single; ⊢natrec )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; wᶠ; ren-w; pw3; pw4; pw5; nrs-w )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBExamplesDiv using ( monusTm; ⊢monus )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( plusMonoLTm; plusMonoLTm-sub )
open import poc.OCP0009.NbEPDirDBLibArithMonus using ( monusLtTm; monusLtTm-sub; ⊢desc-left )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdIH; gcdG; ⊢gcdIH; descConv; KS; NS; PAIRˢ; CERTˢ )
open import poc.OCP0009.NbEPDirDBLibNatrec using ( ⊢natrec-var )
open import poc.OCP0009.NbEPDirDBExamplesGcdLeMid
  using ( gXx; R1'; W'; R2'; S3'; Z3'; D3'; ⊢W'; Ss-collapse; Zs-collapse
        ; D3-clean; ⊢M3s; ⊢Z3s )

------------------------------------------------------------------------
-- ★ THE FINAL CONTEXT.  `⊢S3s` lives at `(Γ ▹ Nat) ▹ <the small motive>`,
--   and the `⊢lam` binds one more, so the leaves sit THREE deep.
--
--   That is one slot shallower than `⊢PAIRˢ`'s home (8 slots) — and being
--   deeper is exactly why attempt 51 was WORSE than attempt 50.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★ THE ONE CAST ROUTE 8 NEEDS, and why `⊢G3s` does not need it.
--
--   Applying the IH substitutes the argument into the codomain, so the
--   measure slot comes back as `subTm (single v) (wᶠ (w t))`.  In `⊢G3s`
--   the slots are de Bruijn VARIABLES and that reduces definitionally.
--   Route 8's slots are ABSTRACT TERMS, so it is only propositional —
--   `ren-w` to fuse the two renamings, then `wk-single` to cancel.
------------------------------------------------------------------------

wfw-single : {Γ : Cx} {v : RTm (Γ ∙)} (t : RTm Γ) →
             subTm (single v) (wᶠ (w t)) ≡ w t
wfw-single {v = v} t =
  trans (cong (subTm (single v)) (ren-w t)) (wk-single (w t))

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
          (csymᵀ (descConv (monusTm (nsuc K*) (nsuc N*)) (nsuc N*)
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
-- ★★ THE LEFT-DESCENT CERTIFICATE, NAMED — AND IT COMMUTES WITH `subTm`.
--
-- ⚠ MEASURED: `pair`/`monusTm`/`nsuc` distribute over `subTm`
--   DEFINITIONALLY (that is why `eqP` is a bare `cong₂`), but
--   `plusMonoLTm` and `monusLtTm` do NOT — which is exactly why
--   `plusMonoLTm-sub`/`monusLtTm-sub` exist.  So the certificate needs its
--   own commutation lemma, and having it once beats five inline pushes.
--
-- ★ LIBRARY CANDIDATE: this is `⊢desc-left`'s subject, so it belongs beside
--   it in `…LibArithMonus`, not here.
------------------------------------------------------------------------

descLeftTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
descLeftTm a b =
  plusMonoLTm (monusTm (nsuc a) (nsuc b)) (nsuc a) (nsuc b) (monusLtTm a b)

descLeftTm-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'} (a b : RTm Γ) →
                 subTm σ (descLeftTm a b)
               ≡ descLeftTm (subTm σ a) (subTm σ b)
descLeftTm-sub {σ = σ} a b =
  trans (plusMonoLTm-sub (monusTm (nsuc a) (nsuc b)) (nsuc a) (nsuc b)
                         (monusLtTm a b))
        (cong (plusMonoLTm (monusTm (nsuc (subTm σ a)) (nsuc (subTm σ b)))
                           (nsuc (subTm σ a)) (nsuc (subTm σ b)))
              (monusLtTm-sub a b))

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
