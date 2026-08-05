------------------------------------------------------------------------
-- OCP-0009 · W1h — `fund`: THE FUNDAMENTAL THEOREM (part 3 of 3).
--
-- Parts 1 and 2 are NbEPDirDBFundSN / NbEPDirDBFundSem; they were
-- split off purely to cut this file's re-check time.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBFund where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst; Σ; _,_; _×_; ⊥; ⊥-elim )

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; base; U; Π; Σ'; El; Hom; Id; Hom-cong₃; Id-cong₃; ⌜Hom⌝-cong₃; tr-cong₃; ap-cong₃; ⌜Id⌝-cong₃; jsub-cong₃
        ; RTm; var; lam; app; pair; fst; snd; absurd; ⌜base⌝; ⌜Π⌝; ⌜Σ⌝; ⌜Hom⌝; hrefl; tr; ap
        ; ⌜Id⌝; idrefl; jsub
        ; Unit; Nat; unit; nzero; nsuc; natrec; natrec-cong₃; ⌜Nat⌝; ⌜Unit⌝
        ; Ren; extR; renTy; renTm
        ; Sub; subTy; subTm; extS; idₛ
        ; _∘ᵣ_
        ; subTy-cong; subTm-cong
        ; subTy-renTy; subTm-renTm
        ; renTy-subTy; renTm-subTm
        ; subTy-subTy; subTm-subTm
        ; subTy-id; subTm-id; renTm-renTm; renTm-cong )
open import poc.OCP0009.NbEPDirDBType
  using ( single; nrs
        ; _⟶_; _⟶*_; done; step
        ; β; βfst; βsnd; ξ-lam; ξ-appˡ; ξ-appʳ; ξ-pairˡ; ξ-pairʳ; ξ-absurdᶜ; ξ-absurdᵉ; ξ-fst; ξ-snd
        ; ξ-⌜Π⌝ˡ; ξ-⌜Π⌝ʳ; ξ-⌜Σ⌝ˡ; ξ-⌜Σ⌝ʳ; ξ-⌜Hom⌝ᶜ; ξ-⌜Hom⌝ˡ; ξ-⌜Hom⌝ʳ
        ; ξ-hreflᶜ; ξ-hreflᵃ; hrefl-pw; tr-J-base; tr-J-Σ; tr-J-Hom; tr-taut
        ; tr-pw; ξ-trᵈ; ξ-trᵖ; ξ-trᵉ; ap-J; ξ-apᶜ; ξ-apᵇ; ξ-apᵖ
        ; ξ-Σˡ; ξ-Σʳ
        ; _≅_
        ; _≅ᵀ_; crflᵀ; csymᵀ; ctrnᵀ
        ; Ctx; ◇; _▹_; ⌊_⌋
        ; _∋_∷_; here; there
        ; _⊢_∷_; ⊢var; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢absurd
        ; El-⌜Hom⌝; ξ-El; El-⌜Π⌝; _⟶ᵀ_; El-⌜base⌝; El-⌜Σ⌝; El-⌜Id⌝
        ; El-⌜Nat⌝; El-⌜Unit⌝
        ; ξ-Idᵀ; ξ-Idˡ; ξ-Idʳ
        ; Hom-U; Hom-Π; ξ-Homᵀ; ξ-Homˡ; ξ-Homʳ
        ; Hom-Nat-z; Hom-Nat-sz; Hom-Nat-ss
        ; ⊢⌜base⌝; ⊢⌜Π⌝; ⊢⌜Σ⌝; ⊢⌜Hom⌝; ⊢hrefl; ⊢tr; ⊢trU; ⊢ap; ⊢conv
        ; ⊢⌜Nat⌝; ⊢⌜Unit⌝
        ; ⊢⌜Id⌝; ⊢idrefl; ⊢jsub
        ; _⊢ty_; ty-base; ty-U; ty-Π; ty-Σ; ty-El; ty-Hom; ty-Id; ty-Unit; ty-Nat
        ; ⊢unit; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢ctx_; c-◇; c-▹
        ; ⊢id; ⊢appex )
open import poc.OCP0009.NbEPDirDBVar
  using ( 𝔹; true; false; occTm; subTm-occ
        ; pw?; stkC?; stkA?; pwBody; pwDom; pwShift
        ; pw?-ren; stkC?-ren; stkA?-ren; pwBody-ren; wk-ren-tm; pw?-sub
        ; stkC?→stkA?
        ; wk-sub-tm; stk⊥pw; pw⊥stk; flat?; flat→stk; flat?-sub
        ; eqv; occ-sub; occ-ren-tm; avoids-wk )
open import poc.OCP0009.NbEPDirDBSR using ( ≅ᵀ-sub; sub-comm; wk-sub )
open import poc.OCP0009.NbEPDirDBConf using ( pwShift-ren; stkC?-red; stkA?-red; subTm-monoˢ; single-mono; ⟶*-trans; ren-comm; ren-comm-ext )
open import poc.OCP0009.NbEPDirDBDec using ( Dec; dec-conv )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; doneᵀ; stepᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-El; confluentᵀ; church-rosserᵀ; Π-inj
        ; red→≅ᵀ; Π-reduct; Σ-reduct; mkΠRed; mkΣRed
        ; Id-reduct; ⟶ᵀ*-Homᵀ )
open import poc.OCP0009.NbEPDirDBSubj
  using ( HomΠShape; hsΠ; hsH; hom-shape; hom-shapeN; nn-U; NoNat; pw-El-decode
        ; HomRed; mkHomRed; Hom-to-Hom; homAmb→
        ; HomToΠ; via-U; via-Π; hom-to-Π
        ; U-reduct; wk-cancel-tm; ≅ᵀ-Homᵀ; gen-var; subTy-comm; subTy-monoˢ )
open import poc.OCP0009.NbEPDirDBLR
  using ( SNe; sne-var; sne-app; sne-absurd; sne-fst; sne-snd; sne-hrefl; sne-tr; sne-ap; sne-jsub
        ; Ne; ne-var; ne-app; ne-absurd; ne-fst; ne-snd; ne-hrefl; ne-tr; ne-ap; ne-jsub; homSem₁
        ; SN; sn-ne; sn-lam; sn-pair; sn-cb; sn-cΠ; sn-cΣ; sn-cH; sn-cId; sn-idrefl; sn-exp
        ; sn-cNat; sn-cUnit
        ; SNRed; snr-β; snr-βfst; snr-βsnd; snr-app; snr-fst; snr-snd
        ; snr-hreflᶜ; snr-J-base; snr-J-Σ; snr-J-Id; snr-J-Unit; snr-taut; snr-trᵖ; snr-ap-J; snr-apᵖ
        ; snr-jsub-refl; snr-jsubᵖ
        ; snr-natrec-zero; snr-natrec-suc; snr-natrecⁿ
        ; sne-natrec; ne-natrec; sn-unit; sn-nzero; sn-nsuc
        ; NatMem; nm-ne; nm-zero; nm-suc; nm-exp; natmem-whred
        ; ⊩₁Unit; ⊩₁Nat; natstk?; natstk?-ren; natstk?-red; sne→natstk; sn-whred
        ; homNatSem; homNatSem₀; hns₀-in; bwd₀-mem⁻; bwd₀-mem
        ; StkHd; sh-Hom; sh-NatH; homnat?
        ; trstk?-ren; apstk?-ren; idstk?-ren; nopw?-ren; trlam?-ren
        ; idstk?-red; ⊩₀Id; ⊩₁Id; IdPay; idpay-transfer; idpay-peel; sne-nopay
        ; nopw⊥pw; stk⊥dead; pw⊥dead; dead→nopw; snr-nonpw
        ; snr-hrefl-pw; snr-J-Hom; snr-tr-pw; snr-tr-mot
        ; deadmot?; deadmot?-red; deadmot?-ren; deadmot→nopw; stk→deadmot
        ; nopw?-red; nopw?-red*
        ; CSR; csr-here; csr-hom; csr→⟶; csr-nonpw; csr-stk⊥; sn-csr
        ; csr-det
        ; _⟶csr*_; csr-done; csr-step; csrs-hom
        ; PayT; payChain; payT-exp; payT-whred; payT-irrel
        ; payT-cast; payT-code; payHomT; _⟶snr*_; snr-done; snr-step
        ; ⊩₀_; ⊩₀base; ⊩₀ne; ⊩₀Π; ⊩₀Σ; ⊩₀Hom; _⊩₀∋_; bwd₀; exp₁
        ; ⊩₀Unit; ⊩₀Nat
        ; base-nf; Unit-nf; Nat-nf; El-ne-reduct; mkElNe; Hom-stk-reduct; mkHomStk
        ; nopw?; trlam?; stablecd?; stableA?; idstk?; sne→spine; wk-single; snr→⟶
        ; exp₀; f≢t
        ; mem-whred₁; homSem₀; homSem₀-mem-endpoints
        ; sne→stablecd; sne→stableA; trstk?
        ; ⊩₁_; ⊩₁base; ⊩₁U; ⊩₁ne; ⊩₁Π; ⊩₁Σ; ⊩₁Hom; _⊩₁∋_
        ; bwd₁; irrel₁; conv₁; CR1₀; CR1₁; CR3₀; CR3₁
        ; emb; emb-coh
        ; sem-conv; sem-lam; sem-app; sem-fst; sem-snd; sem-pair
        ; sem-El; sem-⌜base⌝; sem-⌜Π⌝; sem-⌜Σ⌝; sem-⌜Hom⌝; sem-hrefl
        ; homSem₁
        ; ⟶ᵀ*-sub
        ; IsNormal; WN; mkWN; wn
        ; projl; projr; dfst; dsnd )

open import poc.OCP0009.NbEPDirDBFundSN
open import poc.OCP0009.NbEPDirDBFundSem

private
  variable
    Θ Ξ : Cx
    Γ Δ : Ctx
fund-ty : {σ : Sub ⌊ Γ ⌋ Ξ} {A : RTy ⌊ Γ ⌋} →
          Γ ⊢ty A → Var Ξ → Γ ⊩ˢ σ → ⊩₁ (subTy σ A)
fund : {σ : Sub ⌊ Γ ⌋ Ξ} {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} →
       Γ ⊢ t ∷ A → Var Ξ → Γ ⊩ˢ σ → Rel (subTy σ A) (subTm σ t)

-- TYPE FORMATION.  `base`/`U` are their own whnf; `Π`/`Σ'` build the family by
-- extending the substitution; `El` is the one that changes level — down to `⊩₀`
-- through `sem-El`, and back up through `emb`.
fund-ty ty-base x₀ ρ = ⊩₁base doneᵀ
fund-ty ty-U    x₀ ρ = ⊩₁U doneᵀ
fund-ty {Ξ = Ξ} {σ = σ} (ty-Π {B = B} tyA tyB) x₀ ρ = ⊩₁Π doneᵀ ⊩F ⊩G
  where
    ⊩F = fund-ty tyA x₀ ρ

    ⊩G : (u : RTm Ξ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) (subTy (extS σ) B))
    ⊩G u r = ⊩₁cast (sym (sub-single-Ty σ u B))
                    (fund-ty tyB x₀ (⊩ˢ-ext ρ ⊩F u r))
fund-ty {Ξ = Ξ} {σ = σ} (ty-Σ {B = B} tyA tyB) x₀ ρ = ⊩₁Σ doneᵀ ⊩F ⊩G
  where
    ⊩F = fund-ty tyA x₀ ρ

    ⊩G : (u : RTm Ξ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) (subTy (extS σ) B))
    ⊩G u r = ⊩₁cast (sym (sub-single-Ty σ u B))
                    (fund-ty tyB x₀ (⊩ˢ-ext ρ ⊩F u r))
fund-ty {σ = σ} (ty-El {c = c} dc) x₀ ρ = emb (sem-El doneᵀ hc)
  where
    -- `fund` hands back SOME derivation of `⊩₁ U`; move it onto `⊩₁U doneᵀ`
    -- first (both are derivations of the same type, so `irrel₁ crflᵀ` suffices)
    -- and the `U` clause's second component IS the decoding.
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
-- W2 `ty-Hom` — the semantic action `homSem₁` does all the work; the only
-- plumbing is moving each endpoint's membership onto the IH's derivation of
-- `⊩₁ A[σ]` (the `ty-El` idiom: `irrel₁` at `crflᵀ`).  `Hom` is
-- substitution-stable definitionally, so the goal needs no cast.
-- `ty-Id` — Id is INERT: the interp is immediate, no semantic action.
fund-ty (ty-Id tyA dt du) x₀ ρ = ⊩₁Id doneᵀ
-- ★ WF stage A: the datatype core's formers are substitution-stable and
-- INERT, so their interps are immediate.
fund-ty ty-Unit x₀ ρ = ⊩₁Unit doneᵀ
fund-ty ty-Nat  x₀ ρ = ⊩₁Nat  doneᵀ
fund-ty {σ = σ} (ty-Hom {t = t} {u = u} tyA dt du) x₀ ρ = homSem₁ R ht hu
  where
    R  = fund-ty tyA x₀ ρ
    ht = projl (irrel₁ crflᵀ (dfst (fund dt x₀ ρ)) R)
               (subTm σ t) (dsnd (fund dt x₀ ρ))
    hu = projl (irrel₁ crflᵀ (dfst (fund du x₀ ρ)) R)
               (subTm σ u) (dsnd (fund du x₀ ρ))

-- TERMS.
fund (⊢var d) x₀ ρ = ρ d

-- ★★ WF stage A — the recursor's SEMANTIC validation.
--
-- The scrutinee's membership at `Nat` carries `NatMem` (the
-- reaches-numeral payload), and THAT is what the worker recurses on:
-- a numeral scrutinee makes the recursor fire (backward closure moves
-- the branch's membership onto the redex), a stuck scrutinee makes it
-- neutral (CR3, with `sne→natstk` supplying the key).  The step case
-- feeds the IH into the environment as the second extension — the two
-- cons-substitutions `nrs-cons-Ty`/`nrs-cons-Tm` collapse to the
-- successor instance, which is exactly why `natrec` is type-correct.
--
-- No fuel, no accessibility argument, no measure: the induction is on
-- the semantic number itself.
fund {Ξ = Ξ} {σ = σ} (⊢natrec {M = M} {z = z} {s = w} {n = n}
                              tyM dz dw dn) x₀ ρ =
  relTy (sym (trans (subTy-comm σ M n) (sub-single-Ty σ nI M)))
        (MotC nI hnI , go nI (projl hnI) (projr hnI) hnI)
  where
    zI = subTm σ z
    wI = subTm (extS (extS σ)) w
    nI = subTm σ n

    ⊩N : ⊩₁ (Nat {Ξ})
    ⊩N = ⊩₁Nat doneᵀ

    -- the scrutinee, moved onto the canonical `Nat` interp
    hnI : ⊩N ⊩₁∋ nI
    hnI = projl (irrel₁ crflᵀ (dfst (fund dn x₀ ρ)) ⊩N)
                nI (dsnd (fund dn x₀ ρ))

    -- the motive at a semantic number, in CONS form — exactly the shape
    -- `⊩ˢ-ext` produces, so no cast travels through the recursion.
    MotC : (u : RTm Ξ) → ⊩N ⊩₁∋ u → ⊩₁ (subTy (σ ,ₛ u) M)
    MotC u r = fund-ty tyM x₀ (⊩ˢ-ext ρ ⊩N u r)

    snW : SN wI
    snW = sn-body₂ x₀
            (subst SN (sym (nrs-cons-Tm σ (var x₀) (var x₀) w))
                   (CR1₁ (dfst body₀) (dsnd body₀)))
      where
      r₀ = CR3₁ ⊩N (sne-var x₀)
      r₁ = CR3₁ (MotC (var x₀) r₀) (sne-var x₀)
      body₀ = fund dw x₀ (⊩ˢ-ext (⊩ˢ-ext ρ ⊩N (var x₀) r₀)
                                 (MotC (var x₀) r₀) (var x₀) r₁)

    hZ0 : ⊩N ⊩₁∋ nzero
    hZ0 = (sn-nzero , nm-zero)

    -- the zero branch, at the motive's zero instance
    hZ : (MotC nzero hZ0) ⊩₁∋ zI
    hZ = projl (irrel₁ crflᵀ (dfst bz) (MotC nzero hZ0)) zI (dsnd bz)
      where
      bz = relTy (trans (subTy-comm σ M nzero) (sub-single-Ty σ nzero M))
                 (fund dz x₀ ρ)

    snZ : SN zI
    snZ = CR1₁ (MotC nzero hZ0) hZ

    -- ★ the worker: meta-induction on the reaches-numeral payload.
    -- The `NatMem` argument is the ONLY decreasing one — that is the
    -- whole point of the WF axis: no fuel, no `Acc`, no measure.
    go : (u : RTm Ξ) (snu : SN u) (mm : NatMem u) (r : ⊩N ⊩₁∋ u) →
         (MotC u r) ⊩₁∋ natrec zI wI u

    go u snu (nm-ne nt) r =
      CR3₁ (MotC u r) (sne-natrec snZ snW snu (sne→natstk nt))

    go u snu (nm-exp {t' = u'} rr mm) r =
      exp₁ (MotC u r) (snr-natrecⁿ rr)
        (projl (irrel₁ (csymᵀ conv) (MotC u' r') (MotC u r))
               (natrec zI wI u') (go u' (sn-whred snu rr) mm r'))
      where
        r' : ⊩N ⊩₁∋ u'
        r' = (sn-whred snu rr , mm)

        cons-mono : (x : Var _) → (σ ,ₛ u) x ⟶* (σ ,ₛ u') x
        cons-mono vz     = step (snr→⟶ rr) done
        cons-mono (vs y) = done

        conv : subTy (σ ,ₛ u) M ≅ᵀ subTy (σ ,ₛ u') M
        conv = red→≅ᵀ (subTy-monoˢ cons-mono M)

    go .nzero snu nm-zero r =
      exp₁ (MotC nzero r) (snr-natrec-zero snW)
        (projl (irrel₁ crflᵀ (MotC nzero hZ0) (MotC nzero r)) zI hZ)

    go .(nsuc _) snu (nm-suc {n = m} mm) r =
      exp₁ (MotC (nsuc m) r) (snr-natrec-suc snZ snW snm) stepM
      where
        snm : SN m
        snm = snsuc-inv snu
          where
          snsuc-inv : SN (nsuc m) → SN m
          snsuc-inv (sn-nsuc h) = h

        rm : ⊩N ⊩₁∋ m
        rm = (snm , mm)

        recTm = natrec zI wI m

        bodyS = relTy (nrs-cons-Ty σ m recTm M)
                  (fund dw x₀ (⊩ˢ-ext (⊩ˢ-ext ρ ⊩N m rm)
                                      (MotC m rm) recTm (go m snm mm rm)))

        stepM : (MotC (nsuc m) r) ⊩₁∋
                subTm (single recTm) (subTm (extS (single m)) wI)
        stepM =
          subst (λ q → (MotC (nsuc m) r) ⊩₁∋ q)
                (sym (nrs-cons-Tm σ m recTm w))
                (projl (irrel₁ crflᵀ (dfst bodyS) (MotC (nsuc m) r))
                       (subTm ((σ ,ₛ m) ,ₛ recTm) w) (dsnd bodyS))

fund ⊢unit  x₀ ρ = ( ⊩₁Unit doneᵀ , sn-unit )
fund ⊢nzero x₀ ρ = ( ⊩₁Nat doneᵀ , (sn-nzero , nm-zero) )
fund {σ = σ} (⊢nsuc {n = n} dn) x₀ ρ =
  ( ⊩₁Nat doneᵀ , (sn-nsuc (projl hn) , nm-suc (projr hn)) )
  where
    hn = projl (irrel₁ crflᵀ (dfst (fund dn x₀ ρ)) (⊩₁Nat doneᵀ))
               (subTm σ n) (dsnd (fund dn x₀ ρ))

fund {Ξ = Ξ} {σ = σ} (⊢lam {B = B} {t = s} tyA d) x₀ ρ =
  ( ⊩₁Π doneᵀ ⊩F ⊩G , sem-lam doneᵀ ⊩F ⊩G sns f )
  where
    ⊩F = fund-ty tyA x₀ ρ

    -- ONE call, projected twice: `⊩G u r` and `f u r` must be the first and
    -- second component of the SAME cast, or the membership would be stated at
    -- a different (though equal) semantic type.
    body : (u : RTm Ξ) (r : ⊩F ⊩₁∋ u) →
           Rel (subTy (single u) (subTy (extS σ) B))
               (subTm (single u) (subTm (extS σ) s))
    body u r = relCast (sym (sub-single-Ty σ u B)) (sym (sub-single-Tm σ u s))
                       (fund d x₀ (⊩ˢ-ext ρ ⊩F u r))

    ⊩G : (u : RTm Ξ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) (subTy (extS σ) B))
    ⊩G u r = dfst (body u r)

    f : (u : RTm Ξ) (r : ⊩F ⊩₁∋ u) →
        (⊩G u r) ⊩₁∋ subTm (single u) (subTm (extS σ) s)
    f u r = dsnd (body u r)

    -- ★ the SN premise: instantiate at a variable, then anti-rename (§2).
    r₀ = CR3₁ ⊩F (sne-var x₀)

    sns : SN (subTm (extS σ) s)
    sns = sn-body x₀ (CR1₁ (⊩G (var x₀) r₀) (f (var x₀) r₀))

fund {σ = σ} (⊢app {B = B} {u = u} d₁ d₂) x₀ ρ =
  relTy (sym (sub-comm-Ty σ u B))
        (⊩₁-app (dfst (fund d₁ x₀ ρ)) (dfst (fund d₂ x₀ ρ))
                (dsnd (fund d₁ x₀ ρ)) (dsnd (fund d₂ x₀ ρ)))

fund {Ξ = Ξ} {σ = σ} (⊢pair {B = B} {a = a} {b = b} tyB d₁ d₂) x₀ ρ =
  ( ⊩₁Σ doneᵀ ⊩F ⊩G , sem-pair doneᵀ ⊩F ⊩G sna snb ra rb )
  where
    ⊩F = dfst (fund d₁ x₀ ρ)
    ra = dsnd (fund d₁ x₀ ρ)

    ⊩G : (u : RTm Ξ) → ⊩F ⊩₁∋ u → ⊩₁ (subTy (single u) (subTy (extS σ) B))
    ⊩G u r = ⊩₁cast (sym (sub-single-Ty σ u B))
                    (fund-ty tyB x₀ (⊩ˢ-ext ρ ⊩F u r))

    -- the second component arrives at `B[a][σ]`; push `σ` inside, then bridge
    -- to the family's instance by proof-irrelevance in the membership argument.
    Sb = relTy (sub-comm-Ty σ a B) (fund d₂ x₀ ρ)

    sna = CR1₁ ⊩F ra
    snb = CR1₁ (dfst Sb) (dsnd Sb)
    rb  = projl (irrel₁ crflᵀ (dfst Sb) (⊩G (subTm σ a) ra))
                (subTm σ b) (dsnd Sb)

-- ★★★ WF-axis stage D: EX FALSO'S SEMANTICS.  `absurd c e` is a
-- PERMANENT NEUTRAL — no rule fires on it, whatever the scrutinee does
-- — so CR3 puts it in the interpretation of EVERY type.  That is
-- exactly what "from falsehood, anything" means semantically, and it is
-- why no new clause is needed anywhere in the model: the neutral case
-- was always there.
fund {σ = σ} (⊢absurd {c = c} dc de) x₀ ρ =
  ( emb R₀ , CR3₁ (emb R₀) (sne-absurd snc sne₀) )
  where
    hc  = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
                (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    R₀  = sem-El doneᵀ hc
    sne₀ = CR1₁ (dfst (fund de x₀ ρ)) (dsnd (fund de x₀ ρ))

fund (⊢fst d) x₀ ρ = ⊩₁-fstm (dfst (fund d x₀ ρ)) (dsnd (fund d x₀ ρ))

fund {σ = σ} (⊢snd {B = B} {p = p} d) x₀ ρ =
  relTy (sym (sub-comm-Ty σ (fst p) B))
        (⊩₁-sndm (dfst (fund d x₀ ρ)) (dsnd (fund d x₀ ρ)))

fund ⊢⌜base⌝ x₀ ρ = ( ⊩₁U doneᵀ , sem-⌜base⌝ doneᵀ )

-- ★ WF stage C: the datatype codes are semantically as cheap as
-- ⌜base⌝ — the decode is an INERT type, so the level-0 interp is the
-- one-step decode chain and the code payload is trivial (`PayT` is ⊤
-- off ⌜Π⌝).  ⌜Nat⌝'s membership component comes with the interp, not
-- with the code.
fund ⊢⌜Nat⌝ x₀ ρ =
  ( ⊩₁U doneᵀ , (sn-cNat , (⊩₀Nat (stepᵀ El-⌜Nat⌝ doneᵀ) , _)) )
fund ⊢⌜Unit⌝ x₀ ρ =
  ( ⊩₁U doneᵀ , (sn-cUnit , (⊩₀Unit (stepᵀ El-⌜Unit⌝ doneᵀ) , _)) )

fund {Ξ = Ξ} {σ = σ} (⊢⌜Π⌝ {c = c} {d = e} dc de) x₀ ρ =
  ( ⊩₁U doneᵀ , sem-⌜Π⌝ doneᵀ snc sne ⊩c f pays )
  where
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    ⊩c  = sem-El doneᵀ hc

    -- the codomain code lives in `Γ ▹ El c`, so the extension's semantic type
    -- is `emb ⊩c` and its members come from `emb-coh`.
    body : (u : RTm Ξ) → ⊩c ⊩₀∋ u → Rel U (subTm (σ ,ₛ u) e)
    body u r = fund de x₀ (⊩ˢ-ext ρ (emb ⊩c) u (projl (emb-coh ⊩c) u r))

    memb : (u : RTm Ξ) (r : ⊩c ⊩₀∋ u) → (⊩₁U doneᵀ) ⊩₁∋ subTm (σ ,ₛ u) e
    memb u r = projl (irrel₁ crflᵀ (dfst (body u r)) (⊩₁U doneᵀ))
                     (subTm (σ ,ₛ u) e) (dsnd (body u r))

    f : (u : RTm Ξ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) (subTm (extS σ) e)))
    f u r = ⊩₀cast (cong El (sym (sub-single-Tm σ u e)))
                   (sem-El doneᵀ (memb u r))

    -- W2b: the body code's SN and payload at each argument — straight
    -- off `fund de`'s enriched U-membership (the environment case that
    -- WALLED before the payload existed is now cargo).
    pays : (u : RTm Ξ) (r : ⊩c ⊩₀∋ u) →
           SN (subTm (single u) (subTm (extS σ) e))
           × PayT (f u r) (subTm (single u) (subTm (extS σ) e))
    pays u r =
      ( subst SN (sym (sub-single-Tm σ u e)) (projl (memb u r))
      , payT-cast (cong El (sym (sub-single-Tm σ u e)))
                  (Σ.fst (projr (memb u r)))
                  (payT-code (Σ.fst (projr (memb u r)))
                             (sym (sub-single-Tm σ u e))
                             (Σ.snd (projr (memb u r)))) )

    r₀ = CR3₀ ⊩c (sne-var x₀)

    sne : SN (subTm (extS σ) e)
    sne = sn-body x₀ (subst SN (sym (sub-single-Tm σ (var x₀) e))
                            (CR1₁ (dfst (body (var x₀) r₀))
                                  (dsnd (body (var x₀) r₀))))

fund {Ξ = Ξ} {σ = σ} (⊢⌜Σ⌝ {c = c} {d = e} dc de) x₀ ρ =
  ( ⊩₁U doneᵀ , sem-⌜Σ⌝ doneᵀ snc sne ⊩c f )
  where
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    ⊩c  = sem-El doneᵀ hc

    body : (u : RTm Ξ) → ⊩c ⊩₀∋ u → Rel U (subTm (σ ,ₛ u) e)
    body u r = fund de x₀ (⊩ˢ-ext ρ (emb ⊩c) u (projl (emb-coh ⊩c) u r))

    f : (u : RTm Ξ) → ⊩c ⊩₀∋ u → ⊩₀ (El (subTm (single u) (subTm (extS σ) e)))
    f u r = ⊩₀cast (cong El (sym (sub-single-Tm σ u e)))
                   (sem-El doneᵀ
                     (projl (irrel₁ crflᵀ (dfst (body u r)) (⊩₁U doneᵀ))
                            (subTm (σ ,ₛ u) e) (dsnd (body u r))))

    r₀ = CR3₀ ⊩c (sne-var x₀)

    sne : SN (subTm (extS σ) e)
    sne = sn-body x₀ (subst SN (sym (sub-single-Tm σ (var x₀) e))
                            (CR1₁ (dfst (body (var x₀) r₀))
                                  (dsnd (body (var x₀) r₀))))

-- W2 stage 1: the `⌜Hom⌝` code is semantic via `homSem₀` (through
-- `sem-⌜Hom⌝`); its endpoints come down to level 0 through `emb-coh`.
fund {σ = σ} (⊢⌜Hom⌝ {c = c} {a = a} {b = b} dc da db) x₀ ρ =
  ( ⊩₁U doneᵀ , sem-⌜Hom⌝ doneᵀ snc sna snb ⊩c payc ha hb )
  where
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    ⊩c  = sem-El doneᵀ hc
    payc = Σ.snd (projr hc)

    ha = projr (emb-coh ⊩c) (subTm σ a)
               (projl (irrel₁ crflᵀ (dfst (fund da x₀ ρ)) (emb ⊩c))
                      (subTm σ a) (dsnd (fund da x₀ ρ)))
    hb = projr (emb-coh ⊩c) (subTm σ b)
               (projl (irrel₁ crflᵀ (dfst (fund db x₀ ρ)) (emb ⊩c))
                      (subTm σ b) (dsnd (fund db x₀ ρ)))

    sna = CR1₀ ⊩c ha
    snb = CR1₀ ⊩c hb

-- ★★ W2b: `hrefl` computes now (`hrefl-pw`), so its semantic case
-- reads the U-PAYLOAD: the membership is built by `semHreflPay` at the
-- code's decoded interp and transferred to the ambient's interp by
-- proof-irrelevance (both interpret the same `El`).
fund {σ = σ} (⊢hrefl {c = c} {t = t} dc dt) x₀ ρ =
  ( homSem₁ (dfst Rt) (dsnd Rt) (dsnd Rt)
  , projl (irrel₁ crflᵀ (homSem₁ (emb R₀) htE htE)
                        (homSem₁ (dfst Rt) (dsnd Rt) (dsnd Rt)))
          (hrefl (subTm σ c) (subTm σ t))
          (semHreflPay x₀ R₀ crflᵀ (projl hcode) (Σ.snd (projr hcode))
                       snt htE) )
  where
    Rt = fund dt x₀ ρ
    snt = CR1₁ (dfst Rt) (dsnd Rt)
    hcode = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
                  (subTm σ c) (dsnd (fund dc x₀ ρ))
    R₀ = Σ.fst (projr hcode)
    htE = projl (irrel₁ crflᵀ (dfst Rt) (emb R₀))
                (subTm σ t) (dsnd Rt)

-- ★★ W2 stage 3 — `⊢trU`, the TAUTOLOGICAL motive: transport along a
-- universe path IS application (directed univalence, semantically).
-- With J ⌜Hom⌝-MOTIVE-KEYED, a `tr` at the `var vz` motive whose path
-- is an `hrefl` is PERMANENTLY STUCK (`trstk?`'s var-motive clause), so
-- SpikeTrLR's obstruction — the J-branches' need for `t ≅ u` — has no
-- cases left.  The path's type `Hom U tI uI` can only interp as `⊩₁Π`
-- (every other clause dies on `hom-shape`, and the stuck-`Hom` clause
-- on `U-reduct` against `StkHd`); its membership is the app-closure
-- that discharges the one computing branch, taut itself.
-- ★ directed `ap` (SpikeAp): the term's action on a hom, semantically.
-- The FLAT source key pays off here: the source-decode interp has
-- SN-only memberships (`flatMem` — the ElStk invariant refutes every
-- other root), so the path's INTERNAL argument gets its membership
-- from its own SN, and `fund db` at the extended environment supplies
-- both the body instances' memberships and (at a fresh variable, the
-- `sn-body` trick) the body's own SN.  The path normalizes by its SN:
-- stuck shapes are `sne-ap` neutrals, the head star follows `snr-apᵖ`,
-- and at a canonical hrefl `codeNorm` decides J (→ `semHreflPay` at
-- the fired reflexivity, endpoint-transferred) vs dead (→ neutral).
fund {Ξ = Ξ} {σ = σ}
  (⊢ap {cA = cA} {cB = cB} {b = b} {p = p₀} {t = t₀} {u = u₀}
       dcA key dcB db dt du dp) x₀ ρ =
  relCast (Hom-cong₃ refl (sym (sub-comm σ b t₀)) (sym (sub-comm σ b u₀)))
          refl
          (emb R_H , projl (emb-coh R_H) _ (goP snpI))
  where
  cAI cBI tI uI pI : RTm Ξ
  cAI = subTm σ cA
  cBI = subTm σ cB
  tI  = subTm σ t₀
  uI  = subTm σ u₀
  pI  = subTm σ p₀
  bI : RTm (Ξ ∙)
  bI  = subTm (extS σ) b

  -- ── the source interp and the SN-only-membership extraction ──
  RA : ⊩₁ (El cAI)
  RA = dfst (fund dt x₀ ρ)

  -- flat codes reduce to flat codes (⌜base⌝ is inert; ⌜Hom⌝ heads take
  -- ξ only, with the spine key preserved).

  kflat : flat? cAI ≡ true
  kflat = flat?-sub σ cA key

  flatMem : (R : ⊩₁ (El cAI)) {s : RTm Ξ} → SN s → R ⊩₁∋ s
  flatMem (⊩₁base p)    sns = sns
  flatMem (⊩₁Hom p sh)  sns = sns
  flatMem (⊩₁U p) sns with ett-star (et-el kflat) p
  ... | ()
  flatMem (⊩₁Π p _ _) sns with ett-star (et-el kflat) p
  ... | ()
  flatMem (⊩₁Σ p _ _) sns with ett-star (et-el kflat) p
  ... | ()
  flatMem (⊩₁Id p) sns with ett-star (et-el kflat) p
  ... | ()
  -- ★ reachable now: `El (⌜Hom⌝ ⌜Nat⌝ 1 2) ⟶ᵀ* Unit`.  Membership at
  -- ⊩₁Unit is SN-only, so it is the same answer as ⊩₁base.
  flatMem (⊩₁Unit p) sns = sns
  flatMem (⊩₁Nat p) sns with ett-star (et-el kflat) p
  ... | ()
  flatMem (⊩₁ne {n = n} p ne) sns with ett-star (et-el kflat) p
  ... | et-el {c = n₂} k' =
        ⊥-elim (f≢t (trans (sym (ne-nostk ne)) (flat→stk n₂ k')))

  -- ── the target code and its payload ──
  hcB : (⊩₁U doneᵀ) ⊩₁∋ cBI
  hcB = projl (irrel₁ crflᵀ (dfst (fund dcB x₀ ρ)) (⊩₁U doneᵀ))
              cBI (dsnd (fund dcB x₀ ρ))

  snCB : SN cBI
  snCB = Σ.fst hcB

  R₀B : ⊩₀ (El cBI)
  R₀B = Σ.fst (Σ.snd hcB)

  payB : PayT R₀B cBI
  payB = Σ.snd (Σ.snd hcB)

  -- ── the body instances (the ⊢lam pattern) ──
  bodyB : (u : RTm Ξ) (r : RA ⊩₁∋ u) →
          Rel (subTy (single u) (subTy (extS σ) (El (renTm vs cB))))
              (subTm (single u) bI)
  bodyB u r = relCast (sym (sub-single-Ty σ u (El (renTm vs cB))))
                      (sym (sub-single-Tm σ u b))
                      (fund db x₀ (⊩ˢ-ext ρ RA u r))

  eqEl : (u : RTm Ξ) →
         subTy (single u) (subTy (extS σ) (El (renTm vs cB))) ≡ El cBI
  eqEl u = cong El (trans (cong (subTm (single u)) (wk-sub-tm σ cB))
                          (wk-single cBI))

  b₀m : (u : RTm Ξ) → RA ⊩₁∋ u → R₀B ⊩₀∋ subTm (single u) bI
  b₀m u r =
    projr (emb-coh R₀B) _
      (projl (irrel₁ crflᵀ (dfst z) (emb R₀B)) _ (dsnd z))
    where z = relCast (eqEl u) refl (bodyB u r)

  huA : RA ⊩₁∋ uI
  huA = projl (irrel₁ crflᵀ (dfst (fund du x₀ ρ)) RA) uI
              (dsnd (fund du x₀ ρ))

  hbt₀ : R₀B ⊩₀∋ subTm (single tI) bI
  hbt₀ = b₀m tI (dsnd (fund dt x₀ ρ))

  hbu₀ : R₀B ⊩₀∋ subTm (single uI) bI
  hbu₀ = b₀m uI huA

  R_H : ⊩₀ (Hom (El cBI) (subTm (single tI) bI) (subTm (single uI) bI))
  R_H = homSem₀ R₀B hbt₀ hbu₀

  -- ── the body's own SN (the sn-body trick) and the path's SN ──
  snBB : SN bI
  snBB = sn-body x₀
           (CR1₀ R₀B (b₀m (var x₀) (CR3₁ RA (sne-var x₀))))

  snpI : SN pI
  snpI = CR1₁ (dfst (fund dp x₀ ρ)) (dsnd (fund dp x₀ ρ))

  -- ── the J target's membership, endpoint-transferred ──
  mJ : {s' : RTm Ξ} → SN s' → R_H ⊩₀∋ hrefl cBI (subTm (single s') bI)
  mJ {s'} sns = homSem₀-mem-endpoints R₀B bs bs hbt₀ hbu₀ m₀
    where
    bs = b₀m s' (flatMem RA sns)
    hbsE = projl (emb-coh R₀B) _ bs
    m₁ = semHreflPay x₀ R₀B crflᵀ snCB payB (CR1₀ R₀B bs) hbsE
    m₀ = projr (emb-coh (homSem₀ R₀B bs bs)) _
           (projl (irrel₁ crflᵀ (homSem₁ (emb R₀B) hbsE hbsE)
                                (emb (homSem₀ R₀B bs bs))) _ m₁)

  apstar : {x y : RTm Ξ} → x ⟶snr* y → ap cBI bI x ⟶snr* ap cBI bI y
  apstar snr-done       = snr-done
  apstar (snr-step r q) = snr-step (snr-apᵖ r) (apstar q)

  -- ── the path analysis ──
  goh : {c' s' : RTm Ξ} → SN c' → SN s' → nopw? c' ≡ true →
        R_H ⊩₀∋ ap cBI bI (hrefl c' s')
  goh snc sns kn with codeNorm snc kn
  ... | c* , (csr , cf-stk k) =
        expStar₀ R_H (apstar (snrs-hreflᶜ csr))
          (exp₀ R_H (snr-ap-J (sn-csrs snc csr) k) (mJ sns))
  ... | c* , (csr , cf-dead k) =
        expStar₀ R_H (apstar (snrs-hreflᶜ csr))
          (CR3₀ R_H (sne-ap snCB snBB
                       (sn-ne (sne-hrefl (sn-csrs snc csr) sns
                                         (nopw?-csrs csr kn)))
                       k))

  goP : {p' : RTm Ξ} → SN p' → R_H ⊩₀∋ ap cBI bI p'
  goP (sn-exp r h) = exp₀ R_H (snr-apᵖ r) (goP h)
  goP (sn-ne (sne-var x)) =
    CR3₀ R_H (sne-ap snCB snBB (sn-ne (sne-var x)) refl)
  goP (sn-ne (sne-app n sarg)) =
    CR3₀ R_H (sne-ap snCB snBB (sn-ne (sne-app n sarg)) (sne→spine n))
  goP (sn-ne w@(sne-absurd _ _)) =
    CR3₀ R_H (sne-ap snCB snBB (sn-ne w) refl)
  goP (sn-ne (sne-fst n)) =
    CR3₀ R_H (sne-ap snCB snBB (sn-ne (sne-fst n)) (sne→spine n))
  goP (sn-ne (sne-snd n)) =
    CR3₀ R_H (sne-ap snCB snBB (sn-ne (sne-snd n)) (sne→spine n))
  goP (sn-ne (sne-hrefl snc sns kn)) = goh snc sns kn
  goP (sn-ne (sne-tr h₁ h₂ h₃ k)) =
    CR3₀ R_H (sne-ap snCB snBB (sn-ne (sne-tr h₁ h₂ h₃ k)) k)
  goP (sn-ne (sne-ap h₁ h₂ h₃ k)) =
    CR3₀ R_H (sne-ap snCB snBB (sn-ne (sne-ap h₁ h₂ h₃ k)) k)
  goP (sn-ne (sne-jsub h₁ h₂ h₃ k)) =
    CR3₀ R_H (sne-ap snCB snBB (sn-ne (sne-jsub h₁ h₂ h₃ k)) k)
  goP (sn-ne (sne-natrec h₁ h₂ h₃ k)) =
    CR3₀ R_H (sne-ap snCB snBB (sn-ne (sne-natrec h₁ h₂ h₃ k)) k)
  goP (sn-lam h)       = CR3₀ R_H (sne-ap snCB snBB (sn-lam h) refl)
  goP (sn-pair ha hb)  = CR3₀ R_H (sne-ap snCB snBB (sn-pair ha hb) refl)
  goP sn-cb            = CR3₀ R_H (sne-ap snCB snBB sn-cb refl)
  goP sn-cNat            = CR3₀ R_H (sne-ap snCB snBB sn-cNat refl)
  goP sn-cUnit            = CR3₀ R_H (sne-ap snCB snBB sn-cUnit refl)
  goP (sn-cΠ h₁ h₂)    = CR3₀ R_H (sne-ap snCB snBB (sn-cΠ h₁ h₂) refl)
  goP (sn-cΣ h₁ h₂)    = CR3₀ R_H (sne-ap snCB snBB (sn-cΣ h₁ h₂) refl)
  goP (sn-cH h₁ h₂ h₃) = CR3₀ R_H (sne-ap snCB snBB (sn-cH h₁ h₂ h₃) refl)
  goP (sn-cId h₁ h₂ h₃) = CR3₀ R_H (sne-ap snCB snBB (sn-cId h₁ h₂ h₃) refl)
  goP (sn-idrefl h₁ h₂) = CR3₀ R_H (sne-ap snCB snBB (sn-idrefl h₁ h₂) refl)
  goP sn-unit           = CR3₀ R_H (sne-ap snCB snBB sn-unit refl)
  goP sn-nzero          = CR3₀ R_H (sne-ap snCB snBB sn-nzero refl)
  goP (sn-nsuc h)       = CR3₀ R_H (sne-ap snCB snBB (sn-nsuc h) refl)

-- ★ the two-former kernel: the three symmetric cases.
fund {σ = σ} (⊢⌜Id⌝ {c = c} {a = a} {b = b} dc da db) x₀ ρ =
  ( ⊩₁U doneᵀ
  , ( sn-cId snc sna snb
    , ( bwd₀ (stepᵀ (El-⌜Id⌝ _ _ _) doneᵀ) (⊩₀Id doneᵀ) , _ ) ) )
  where
    hc = projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
               (subTm σ c) (dsnd (fund dc x₀ ρ))
    snc = projl hc
    ⊩c  = Σ.fst (projr hc)
    sna = CR1₁ (dfst (fund da x₀ ρ)) (dsnd (fund da x₀ ρ))
    snb = CR1₁ (dfst (fund db x₀ ρ)) (dsnd (fund db x₀ ρ))

-- `⊢idrefl` — the payload is trivial: both endpoints are the SAME
-- substituted term, so every reaching chain joins at it by `done`.
fund {σ = σ} (⊢idrefl {c = c} {t = t} dc dt) x₀ ρ =
  ( ⊩₁Id doneᵀ
  , ( sn-idrefl snc snt , (λ _ → subTm σ t , (done , done)) ) )
  where
    snc = projl (projl (irrel₁ crflᵀ (dfst (fund dc x₀ ρ)) (⊩₁U doneᵀ))
                       (subTm σ c) (dsnd (fund dc x₀ ρ)))
    snt = CR1₁ (dfst (fund dt x₀ ρ)) (dsnd (fund dt x₀ ρ))

-- ★★ `⊢jsub` — SUBST AT AN ARBITRARY FAMILY, semantically.  The path's
-- endpoint-join payload makes the `El (d[t]) → El (d[u])` transfer
-- CONVERSION-BASED (`irrel₁` over the join's `mono-El[]` chains), so
-- no motive restriction is needed anywhere — the spike's claim, cashed.
fund {Ξ = Ξ} {σ = σ}
  (⊢jsub {A = A} {d = d} {t = t₀} {u = u₀} {p = p₀} {e = e₀}
         dd dt du dp de) x₀ ρ =
  relCast (cong El (sym (sub-comm σ d u₀))) refl
          (emb R₀u , projP)
  where
  dI : RTm (Ξ ∙)
  dI = subTm (extS σ) d
  tI uI pI eI : RTm Ξ
  tI = subTm σ t₀
  uI = subTm σ u₀
  pI = subTm σ p₀
  eI = subTm σ e₀

  RA = dfst (fund dt x₀ ρ)
  ht = dsnd (fund dt x₀ ρ)
  hu = projl (irrel₁ crflᵀ (dfst (fund du x₀ ρ)) RA) uI
             (dsnd (fund du x₀ ρ))

  -- the family instances (the ⊢lam pattern)
  bodyD : (v : RTm Ξ) (r : RA ⊩₁∋ v) →
          Rel (subTy (single v) (subTy (extS σ) U)) (subTm (single v) dI)
  bodyD v r = relCast (sym (sub-single-Ty σ v U)) (sym (sub-single-Tm σ v d))
                      (fund dd x₀ (⊩ˢ-ext ρ RA v r))

  dmem : (v : RTm Ξ) (r : RA ⊩₁∋ v) → (⊩₁U doneᵀ) ⊩₁∋ subTm (single v) dI
  dmem v r = projl (irrel₁ crflᵀ (dfst (bodyD v r)) (⊩₁U doneᵀ))
                   (subTm (single v) dI) (dsnd (bodyD v r))

  R₀t : ⊩₀ (El (subTm (single tI) dI))
  R₀t = Σ.fst (projr (dmem tI ht))
  R₀u : ⊩₀ (El (subTm (single uI) dI))
  R₀u = Σ.fst (projr (dmem uI hu))

  snDI : SN dI
  snDI = sn-body x₀
           (projl (dmem (var x₀) (CR3₁ RA (sne-var x₀))))

  -- the path's SN + payload, by ROOT-analysis of its interp (only
  -- `⊩₁Id` interps an Id-form type — Id is inert, every other root's
  -- chain clashes by `Id-reduct`).
  idMemGet : (R : ⊩₁ (Id (subTy σ A) tI uI)) → R ⊩₁∋ pI →
             SN pI × IdPay tI uI pI
  idMemGet (⊩₁Id {a = a₂} {b = b₂} ch) h with Id-reduct ch
  ... | _ , (a₃ , (b₃ , (refl , (rH , (rt , ru))))) =
        ( projl h
        , (λ c₂ → let j = projr h c₂
                  in Σ.fst j
                     , ( ⟶*-trans rt (Σ.fst (Σ.snd j))
                       , ⟶*-trans ru (Σ.snd (Σ.snd j)) )) )
  idMemGet (⊩₁base ch) h with Id-reduct ch
  ... | _ , (_ , (_ , ((), _)))
  idMemGet (⊩₁U ch) h with Id-reduct ch
  ... | _ , (_ , (_ , ((), _)))
  idMemGet (⊩₁ne ch n) h with Id-reduct ch
  ... | _ , (_ , (_ , ((), _)))
  idMemGet (⊩₁Π ch _ _) h with Id-reduct ch
  ... | _ , (_ , (_ , ((), _)))
  idMemGet (⊩₁Σ ch _ _) h with Id-reduct ch
  ... | _ , (_ , (_ , ((), _)))
  idMemGet (⊩₁Hom ch _) h with Id-reduct ch
  ... | _ , (_ , (_ , ((), _)))
  idMemGet (⊩₁Unit ch) h with Id-reduct ch
  ... | _ , (_ , (_ , ((), _)))
  idMemGet (⊩₁Nat ch) h with Id-reduct ch
  ... | _ , (_ , (_ , ((), _)))

  hpP = idMemGet (dfst (fund dp x₀ ρ)) (dsnd (fund dp x₀ ρ))

  -- e's membership at the t-instance
  hEt : (emb R₀t) ⊩₁∋ eI
  hEt = projl (irrel₁ crflᵀ
                 (dfst (relCast (cong El (sub-comm σ d t₀)) refl
                                (fund de x₀ ρ)))
                 (emb R₀t))
              eI
              (dsnd (relCast (cong El (sub-comm σ d t₀)) refl
                             (fund de x₀ ρ)))

  -- the path analysis
  nkeyJ : {p' : RTm Ξ} → SNe p' → idstk? p' ≡ true
  nkeyJ (sne-var x)        = refl
  nkeyJ (sne-app n _)      = sne→spine n
  nkeyJ (sne-absurd _ _)   = refl
  nkeyJ (sne-fst n)        = sne→spine n
  nkeyJ (sne-snd n)        = sne→spine n
  nkeyJ (sne-hrefl _ _ _)  = refl
  nkeyJ (sne-tr _ _ _ key) = key
  nkeyJ (sne-ap _ _ _ key) = key
  nkeyJ (sne-jsub _ _ _ key) = key
  nkeyJ (sne-natrec _ _ _ key) = key

  goP : {p' : RTm Ξ} → SN p' → IdPay tI uI p' →
        (emb R₀u) ⊩₁∋ jsub dI p' eI
  goP (sn-exp r h) pay =
    exp₁ (emb R₀u) (snr-jsubᵖ r) (goP h (λ ch → pay (snr-step r ch)))
  goP (sn-ne n) pay =
    CR3₁ (emb R₀u) (sne-jsub snDI (sn-ne n) (CR1₁ (emb R₀t) hEt) (nkeyJ n))
  goP (sn-idrefl hc hs) pay with pay snr-done
  ... | w , (twI , uwI) =
        exp₁ (emb R₀u) (snr-jsub-refl snDI hc hs)
          (projl (irrel₁ cvj (emb R₀t) (emb R₀u)) eI hEt)
    where
    cvj : El (subTm (single tI) dI) ≅ᵀ El (subTm (single uI) dI)
    cvj = ctrnᵀ (red→≅ᵀ (⟶ᵀ*-El (subTm-monoˢ (single-mono twI) dI)))
                (csymᵀ (red→≅ᵀ (⟶ᵀ*-El (subTm-monoˢ (single-mono uwI) dI))))
  goP (sn-lam h) pay =
    CR3₁ (emb R₀u) (sne-jsub snDI (sn-lam h) (CR1₁ (emb R₀t) hEt) refl)
  goP (sn-pair a b) pay =
    CR3₁ (emb R₀u) (sne-jsub snDI (sn-pair a b) (CR1₁ (emb R₀t) hEt) refl)
  goP sn-cb pay =
    CR3₁ (emb R₀u) (sne-jsub snDI sn-cb (CR1₁ (emb R₀t) hEt) refl)
  goP sn-cNat pay =
    CR3₁ (emb R₀u) (sne-jsub snDI sn-cNat (CR1₁ (emb R₀t) hEt) refl)
  goP sn-cUnit pay =
    CR3₁ (emb R₀u) (sne-jsub snDI sn-cUnit (CR1₁ (emb R₀t) hEt) refl)
  goP (sn-cΠ h₁ h₂) pay =
    CR3₁ (emb R₀u) (sne-jsub snDI (sn-cΠ h₁ h₂) (CR1₁ (emb R₀t) hEt) refl)
  goP (sn-cΣ h₁ h₂) pay =
    CR3₁ (emb R₀u) (sne-jsub snDI (sn-cΣ h₁ h₂) (CR1₁ (emb R₀t) hEt) refl)
  goP (sn-cH h₁ h₂ h₃) pay =
    CR3₁ (emb R₀u) (sne-jsub snDI (sn-cH h₁ h₂ h₃) (CR1₁ (emb R₀t) hEt) refl)
  goP (sn-cId h₁ h₂ h₃) pay =
    CR3₁ (emb R₀u) (sne-jsub snDI (sn-cId h₁ h₂ h₃) (CR1₁ (emb R₀t) hEt) refl)
  goP sn-unit pay =
    CR3₁ (emb R₀u) (sne-jsub snDI sn-unit (CR1₁ (emb R₀t) hEt) refl)
  goP sn-nzero pay =
    CR3₁ (emb R₀u) (sne-jsub snDI sn-nzero (CR1₁ (emb R₀t) hEt) refl)
  goP (sn-nsuc h) pay =
    CR3₁ (emb R₀u) (sne-jsub snDI (sn-nsuc h) (CR1₁ (emb R₀t) hEt) refl)

  projP : (emb R₀u) ⊩₁∋ jsub dI pI eI
  projP = goP (projl hpP) (projr hpP)

fund {Ξ = Ξ} {σ = σ}
  (⊢trU {p = p₀} {e = e₀} {t = t₀} {u = u₀} dt du dp de) x₀ ρ =
  main (dfst (fund dp x₀ ρ)) (dsnd (fund dp x₀ ρ))
  where
  tI uI pI eI : RTm Ξ
  tI = subTm σ t₀
  uI = subTm σ u₀
  pI = subTm σ p₀
  eI = subTm σ e₀

  hUu : (⊩₁U doneᵀ) ⊩₁∋ uI
  hUu = projl (irrel₁ crflᵀ (dfst (fund du x₀ ρ)) (⊩₁U doneᵀ)) uI
              (dsnd (fund du x₀ ρ))

  R_result : ⊩₁ (El uI)
  R_result = emb (Σ.fst (projr hUu))

  R_e : ⊩₁ (El tI)
  R_e = dfst (fund de x₀ ρ)
  he  : R_e ⊩₁∋ eI
  he  = dsnd (fund de x₀ ρ)
  snE = CR1₁ R_e he

  -- every permanently stuck configuration, in one place: at a `var`
  -- motive, `trstk?` needs only the path to be rule-dead.
  nkey : {p' : RTm Ξ} → SNe p' → trstk? (var (vz {Ξ})) p' ≡ true
  nkey (sne-var x)        = refl
  nkey (sne-app n s)      = sne→spine n
  nkey (sne-absurd _ _)   = refl
  nkey (sne-fst n)        = sne→spine n
  nkey (sne-snd n)        = sne→spine n
  nkey (sne-hrefl _ _ kn) = kn
  nkey (sne-tr _ _ _ key) = key
  nkey (sne-ap _ _ _ key) = key
  nkey (sne-jsub _ _ _ key) = key
  nkey (sne-natrec _ _ _ key) = key

  cr3 : {p' : RTm Ξ} → SN p' → trstk? (var (vz {Ξ})) p' ≡ true →
        Σ (⊩₁ (El uI)) (λ R → R ⊩₁∋ tr (var vz) p' eI)
  cr3 snp key =
    ( R_result
    , CR3₁ R_result (sne-tr (sn-ne (sne-var vz)) snp snE key) )

  piCase : {F : RTy Ξ} {G : RTy (Ξ ∙)} {t₁ u₁ : RTm Ξ}
           (q : Hom U tI uI ⟶ᵀ* Π F G)
           (⊩F : ⊩₁ F)
           (⊩G : (v : RTm Ξ) → ⊩F ⊩₁∋ v → ⊩₁ (subTy (single v) G)) →
           tI ⟶* t₁ → uI ⟶* u₁ →
           El t₁ ⟶ᵀ* F → El (renTm vs u₁) ⟶ᵀ* G →
           {p' : RTm Ξ} → SN p' → (⊩₁Π q ⊩F ⊩G) ⊩₁∋ p' →
           Σ (⊩₁ (El uI)) (λ R → R ⊩₁∋ tr (var vz) p' eI)
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-exp r snp') hp' =
    ( dfst z , exp₁ (dfst z) (snr-trᵖ r) (dsnd z) )
    where z = piCase q ⊩F ⊩G rt ru rEt rEu snp'
                     (mem-whred₁ (⊩₁Π q ⊩F ⊩G) r hp')
  piCase {u₁ = u₁} q ⊩F ⊩G rt ru rEt rEu {lam f} (sn-lam snf) hp' =
    ( R_result , exp₁ R_result snr-taut m-res )
    where
    he-F = projl (irrel₁ (red→≅ᵀ (⟶ᵀ*-trans (⟶ᵀ*-El rt) rEt)) R_e ⊩F)
                 eI he
    cG : El uI ≅ᵀ subTy (single eI) _
    cG = red→≅ᵀ
           (⟶ᵀ*-trans (⟶ᵀ*-El ru)
             (subst (λ z → El z ⟶ᵀ* _) (wk-cancel-tm eI u₁)
                    (⟶ᵀ*-sub (single eI) rEu)))
    m-res = projl (irrel₁ (csymᵀ cG) (⊩G eI he-F) R_result)
                  (app (lam f) eI) (projr hp' eI he-F)
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-ne n) hp'      = cr3 (sn-ne n) (nkey n)
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-pair sa sb) hp' = cr3 (sn-pair sa sb) refl
  piCase q ⊩F ⊩G rt ru rEt rEu sn-cb hp'           = cr3 sn-cb refl
  piCase q ⊩F ⊩G rt ru rEt rEu sn-cNat hp'         = cr3 sn-cNat refl
  piCase q ⊩F ⊩G rt ru rEt rEu sn-cUnit hp'        = cr3 sn-cUnit refl
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-cΠ h₁ h₂) hp'   = cr3 (sn-cΠ h₁ h₂) refl
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-cΣ h₁ h₂) hp'   = cr3 (sn-cΣ h₁ h₂) refl
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-cH h₁ h₂ h₃) hp' = cr3 (sn-cH h₁ h₂ h₃) refl
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-cId h₁ h₂ h₃) hp' = cr3 (sn-cId h₁ h₂ h₃) refl
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-idrefl h₁ h₂) hp' = cr3 (sn-idrefl h₁ h₂) refl
  piCase q ⊩F ⊩G rt ru rEt rEu sn-unit hp'  = cr3 sn-unit refl
  piCase q ⊩F ⊩G rt ru rEt rEu sn-nzero hp' = cr3 sn-nzero refl
  piCase q ⊩F ⊩G rt ru rEt rEu (sn-nsuc h) hp' = cr3 (sn-nsuc h) refl

  main : (R : ⊩₁ (Hom U tI uI)) → R ⊩₁∋ pI →
         Σ (⊩₁ (El uI)) (λ R' → R' ⊩₁∋ tr (var vz) pI eI)
  main (⊩₁base q) hp with hom-shapeN nn-U q
  ... | ()
  main (⊩₁U q) hp with hom-shapeN nn-U q
  ... | ()
  main (⊩₁ne q n) hp with hom-shapeN nn-U q
  ... | ()
  main (⊩₁Σ q ⊩F ⊩G) hp with hom-shapeN nn-U q
  ... | ()
  main (⊩₁Id q) hp with hom-shapeN nn-U q
  ... | ()
  main (⊩₁Unit q) hp with hom-shapeN nn-U q
  ... | ()
  main (⊩₁Nat q) hp with hom-shapeN nn-U q
  ... | ()
  -- ★ stage C: `Hom-to-Hom` is keyed on the TARGET ambient now, so the
  -- source witness `nn-U` is pushed forward along `q` first.
  main (⊩₁Hom q sh) hp with Hom-to-Hom (homAmb→ q nn-U) q
  ... | mkHomRed rA rt ru with U-reduct rA
  ...   | refl with sh
  ...     | sh-Hom ()
  main (⊩₁Π q ⊩F ⊩G) hp with hom-to-Π nn-U q
  ... | via-Π rA with U-reduct rA
  ...   | ()
  main (⊩₁Π q ⊩F ⊩G) hp | via-U rA rt ru rEt rEu =
    piCase q ⊩F ⊩G rt ru rEt rEu (projl hp) hp

-- ★★ W2 stage 2 — `⊢tr` AT THE COMPOSITION MOTIVE: the semantic
-- validation the variance floor promised.  The motive's vz-freeness
-- (the inlined `posc-Hom` premises) makes every component
-- ENDPOINT-BLIND (`subTm-occ`), so the source- and target-types differ
-- only in the transported endpoint; the path analysis runs by induction
-- on the path's `SN` derivation — head steps expand
-- (`exp₁` ∘ `mem-whred₁`, the deterministic-strategy transfer), the
-- permanently stuck shapes are neutral (`sne-tr` + the classifier
-- extractors), and the J-branches hand the payload across the endpoint
-- switch with `homSem₀-mem-endpoints`.
fund {Ξ = Ξ} {σ = σ}
  (⊢tr {A = A} {c = c₀} {a = a₀} {p = p₀} {e = e₀} {t = t₀} {u = u₀}
       dc' da' dv nc hc ha dt du dp de) x₀ ρ =
  relTy (cong El (sym (sub-comm σ (⌜Hom⌝ c₀ a₀ (var vz)) u₀)))
        (go (CR1₁ (dfst (fund dp x₀ ρ)) (dsnd (fund dp x₀ ρ)))
            (dsnd (fund dp x₀ ρ)))
  where
  dI : RTm (Ξ ∙)
  dI = subTm (extS σ) (⌜Hom⌝ c₀ a₀ (var vz))
  tI uI pI eI : RTm Ξ
  tI = subTm σ t₀
  uI = subTm σ u₀
  pI = subTm σ p₀
  eI = subTm σ e₀

  Rt   = fund dt x₀ ρ
  R_A  = dfst Rt
  ht   = dsnd Rt
  hu   = projl (irrel₁ crflᵀ (dfst (fund du x₀ ρ)) R_A) uI
               (dsnd (fund du x₀ ρ))
  R_H  = dfst (fund dp x₀ ρ)
  Re'  = relTy (cong El (sub-comm σ (⌜Hom⌝ c₀ a₀ (var vz)) t₀))
               (fund de x₀ ρ)
  R_e  = dfst Re'
  he   = dsnd Re'
  snE  = CR1₁ R_e he

  -- `SN` of the substituted motive, componentwise via instantiation at
  -- a fresh variable (the `sem-⌜Π⌝` pattern)
  r₀    = CR3₁ R_A (sne-var x₀)
  bodyC = fund dc' x₀ (⊩ˢ-ext ρ R_A (var x₀) r₀)
  bodyA = fund da' x₀ (⊩ˢ-ext ρ R_A (var x₀) r₀)
  snD : SN dI
  snD = sn-cH
          (sn-body x₀ (subst SN (sym (sub-single-Tm σ (var x₀) c₀))
                             (CR1₁ (dfst bodyC) (dsnd bodyC))))
          (sn-body x₀ (subst SN (sym (sub-single-Tm σ (var x₀) a₀))
                             (CR1₁ (dfst bodyA) (dsnd bodyA))))
          (sn-ne (sne-var vz))

  -- the motive's components at the t-endpoint environment
  envT = ⊩ˢ-ext ρ R_A tI ht
  envU = ⊩ˢ-ext ρ R_A uI hu

  cT aT : RTm Ξ
  cT = subTm (σ ,ₛ tI) c₀
  aT = subTm (σ ,ₛ tI) a₀

  hcT = projl (irrel₁ crflᵀ (dfst (fund dc' x₀ envT)) (⊩₁U doneᵀ))
              cT (dsnd (fund dc' x₀ envT))
  Rc : ⊩₀ (El cT)
  Rc = sem-El doneᵀ hcT

  haT : Rc ⊩₀∋ aT
  haT = projr (emb-coh Rc) aT
              (projl (irrel₁ crflᵀ (dfst (fund da' x₀ envT)) (emb Rc))
                     aT (dsnd (fund da' x₀ envT)))

  htT : Rc ⊩₀∋ tI
  htT = projr (emb-coh Rc) tI
              (projl (irrel₁ crflᵀ (dfst (fund dv x₀ envT)) (emb Rc))
                     tI (dsnd (fund dv x₀ envT)))

  -- endpoint-blindness of the components (`subTm-occ` on the premises)
  agree-c : (x : Var (_ ∙)) → occTm x c₀ ≡ true → (σ ,ₛ uI) x ≡ (σ ,ₛ tI) x
  agree-c vz o with trans (sym o) hc
  ... | ()
  agree-c (vs y) o = refl

  agree-a : (x : Var (_ ∙)) → occTm x a₀ ≡ true → (σ ,ₛ uI) x ≡ (σ ,ₛ tI) x
  agree-a vz o with trans (sym o) ha
  ... | ()
  agree-a (vs y) o = refl

  eqc : subTm (σ ,ₛ uI) c₀ ≡ cT
  eqc = subTm-occ c₀ agree-c
  eqa : subTm (σ ,ₛ uI) a₀ ≡ aT
  eqa = subTm-occ a₀ agree-a

  huT : Rc ⊩₀∋ uI
  huT = projr (emb-coh Rc) uI
              (projl (irrel₁ crflᵀ
                        (dfst (relTy (cong El eqc) (fund dv x₀ envU)))
                        (emb Rc))
                     uI (dsnd (relTy (cong El eqc) (fund dv x₀ envU))))

  -- source and target decoded interps, and the payload's transfer
  eq-ct : subTm (single tI) (subTm (extS σ) c₀) ≡ cT
  eq-ct = sub-single-Tm σ tI c₀
  eq-at : subTm (single tI) (subTm (extS σ) a₀) ≡ aT
  eq-at = sub-single-Tm σ tI a₀
  eq-cu : subTm (single uI) (subTm (extS σ) c₀) ≡ cT
  eq-cu = trans (sub-single-Tm σ uI c₀) eqc
  eq-au : subTm (single uI) (subTm (extS σ) a₀) ≡ aT
  eq-au = trans (sub-single-Tm σ uI a₀) eqa

  eqSrc : El (⌜Hom⌝ cT aT tI) ≡ El (subTm (single tI) dI)
  eqSrc = cong El (sym (⌜Hom⌝-cong₃ eq-ct eq-at refl))
  eqTgt : El (⌜Hom⌝ cT aT uI) ≡ El (subTm (single uI) dI)
  eqTgt = cong El (sym (⌜Hom⌝-cong₃ eq-cu eq-au refl))

  srcBase = bwd₀ (stepᵀ (El-⌜Hom⌝ cT aT tI) doneᵀ) (homSem₀ Rc haT htT)
  tgtBase = bwd₀ (stepᵀ (El-⌜Hom⌝ cT aT uI) doneᵀ) (homSem₀ Rc haT huT)

  R₀t : ⊩₀ (El (subTm (single tI) dI))
  R₀t = ⊩₀cast eqSrc srcBase
  R₀u : ⊩₀ (El (subTm (single uI) dI))
  R₀u = ⊩₀cast eqTgt tgtBase

  R_result : ⊩₁ (El (subTm (single uI) dI))
  R_result = emb R₀u


  heTgt : R_result ⊩₁∋ eI
  heTgt =
    projl (emb-coh R₀u) eI
      (mem₀cast eqTgt tgtBase
        (bwd₀-mem⁻ (stepᵀ (El-⌜Hom⌝ cT aT uI) doneᵀ) (homSem₀ Rc haT huT)
          (homSem₀-mem-endpoints Rc haT htT haT huT
            (bwd₀-mem (stepᵀ (El-⌜Hom⌝ cT aT tI) doneᵀ) (homSem₀ Rc haT htT)
              (mem₀cast⁻ eqSrc srcBase
                (projr (emb-coh R₀t) eI
                  (projl (irrel₁ crflᵀ R_e (emb R₀t)) eI he)))))))

  -- ★ the path analysis.
  cr3 : {p' : RTm Ξ} → SN p' → trstk? dI p' ≡ true →
        Σ (⊩₁ (El (subTm (single uI) dI)))
          (λ R → R ⊩₁∋ tr dI p' eI)
  cr3 snp key = ( R_result , CR3₁ R_result (sne-tr snD snp snE key) )

  -- ★★ W2b, the LAST branch: a lam path — POINTWISE TRANSPORT,
  -- discharged by `semTr` at layer 1.  The strengthening equalities
  -- rewrite semTr's motive onto dI; the membership then rides
  -- heTgt's exact forward chain up to R_result.
  goLam : {f : RTm (Ξ ∙)} → SN f → R_H ⊩₁∋ lam f →
          Σ (⊩₁ (El (subTm (single uI) dI)))
            (λ R → R ⊩₁∋ tr dI (lam f) eI)
  goLam {f = f} snf hp' with gen-var dv
  ... | _ , (here , cv) =
    ( R_result
    , projl (emb-coh R₀u) (tr dI (lam f) eI)
        (mem₀cast eqTgt tgtBase
          (bwd₀-mem⁻ (stepᵀ (El-⌜Hom⌝ cT aT uI) doneᵀ) (homSem₀ Rc haT huT)
            (memTm (homSem₀ Rc haT huT) trEq
              (semTr x₀ Rc crflᵀ (projl hcT) (Σ.snd (projr hcT))
                     haT htT huT (sn-lam snf) hTe hUe hpX hEX)))) )
    where
    hTe = projl (emb-coh Rc) tI htT
    hUe = projl (emb-coh Rc) uI huT

    eqA : subTy (σ ,ₛ tI) (renTy vs A) ≡ subTy σ A
    eqA = trans (subTy-renTy A) (subTy-cong (λ _ → refl) A)

    cA : subTy σ A ≅ᵀ El cT
    cA = csymᵀ (subst (λ z → El cT ≅ᵀ z) eqA (≅ᵀ-sub (σ ,ₛ tI) cv))

    hpX : (homSem₁ (emb Rc) hTe hUe) ⊩₁∋ lam f
    hpX = projl (irrel₁ (≅ᵀ-Homᵀ cA) R_H (homSem₁ (emb Rc) hTe hUe))
                (lam f) hp'

    hEX : (homSem₀ Rc haT htT) ⊩₀∋ eI
    hEX = bwd₀-mem (stepᵀ (El-⌜Hom⌝ cT aT tI) doneᵀ) (homSem₀ Rc haT htT)
            (mem₀cast⁻ eqSrc srcBase
              (projr (emb-coh R₀t) eI
                (projl (irrel₁ crflᵀ R_e (emb R₀t)) eI he)))

    occCS : occTm vz (subTm (extS σ) c₀) ≡ false
    occCS = occ-sub hs c₀ hc
      where
      hs : ∀ y → eqv vz y ≡ false → occTm vz (extS σ y) ≡ false
      hs vz ()
      hs (vs y) _ = occ-ren-tm avoids-wk (σ y)

    occAS : occTm vz (subTm (extS σ) a₀) ≡ false
    occAS = occ-sub hs a₀ ha
      where
      hs : ∀ y → eqv vz y ≡ false → occTm vz (extS σ y) ≡ false
      hs vz ()
      hs (vs y) _ = occ-ren-tm avoids-wk (σ y)

    strength : (t₂ : RTm (Ξ ∙)) → occTm vz t₂ ≡ false →
               renTm vs (subTm (single tI) t₂) ≡ t₂
    strength t₂ o =
      trans (renTm-subTm t₂) (trans (subTm-occ t₂ agree) (subTm-id t₂))
      where
      agree : ∀ x → occTm x t₂ ≡ true → _
      agree vz oc with trans (sym oc) o
      ... | ()
      agree (vs i) oc = refl

    strengthC : renTm vs cT ≡ subTm (extS σ) c₀
    strengthC = trans (cong (renTm vs) (sym eq-ct))
                      (strength (subTm (extS σ) c₀) occCS)

    strengthA : renTm vs aT ≡ subTm (extS σ) a₀
    strengthA = trans (cong (renTm vs) (sym eq-at))
                      (strength (subTm (extS σ) a₀) occAS)

    trEq : tr (⌜Hom⌝ (renTm vs cT) (renTm vs aT) (var vz)) (lam f) eI
           ≡ tr dI (lam f) eI
    trEq = tr-cong₃ (⌜Hom⌝-cong₃ strengthC strengthA refl) refl refl

  go  : {p' : RTm Ξ} → SN p' → R_H ⊩₁∋ p' →
        Σ (⊩₁ (El (subTm (single uI) dI)))
          (λ R → R ⊩₁∋ tr dI p' eI)
  goh : {c' s' : RTm Ξ} → SN c' → SN s' → nopw? c' ≡ true →
        R_H ⊩₁∋ hrefl c' s' →
        Σ (⊩₁ (El (subTm (single uI) dI)))
          (λ R → R ⊩₁∋ tr dI (hrefl c' s') eI)

  go (sn-exp r snp') hp' =
    ( dfst z , exp₁ (dfst z) (snr-trᵖ r) (dsnd z) )
    where z = go snp' (mem-whred₁ R_H r hp')
  go (sn-ne (sne-var x)) hp'         = cr3 (sn-ne (sne-var x)) refl
  go (sn-ne (sne-app n s)) hp'       = cr3 (sn-ne (sne-app n s)) (sne→spine n)
  go (sn-ne w@(sne-absurd _ _)) hp'  = cr3 (sn-ne w) refl
  go (sn-ne (sne-fst n)) hp'         = cr3 (sn-ne (sne-fst n)) (sne→spine n)
  go (sn-ne (sne-snd n)) hp'         = cr3 (sn-ne (sne-snd n)) (sne→spine n)
  go (sn-ne (sne-hrefl snc sns kn)) hp' = goh snc sns kn hp'
  go (sn-ne (sne-tr h₁ h₂ h₃ key)) hp' =
    cr3 (sn-ne (sne-tr h₁ h₂ h₃ key)) key
  go (sn-ne (sne-ap h₁ h₂ h₃ key)) hp' =
    cr3 (sn-ne (sne-ap h₁ h₂ h₃ key)) key
  go (sn-ne (sne-jsub h₁ h₂ h₃ key)) hp' =
    cr3 (sn-ne (sne-jsub h₁ h₂ h₃ key)) key
  go (sn-ne (sne-natrec h₁ h₂ h₃ key)) hp' =
    cr3 (sn-ne (sne-natrec h₁ h₂ h₃ key)) key
  go (sn-lam snf) hp'      = goLam snf hp'
  go (sn-pair sa sb) hp'   = cr3 (sn-pair sa sb) refl
  go sn-cb hp'             = cr3 sn-cb refl
  go sn-cNat hp'           = cr3 sn-cNat refl
  go sn-cUnit hp'          = cr3 sn-cUnit refl
  go (sn-cΠ h₁ h₂) hp'     = cr3 (sn-cΠ h₁ h₂) refl
  go (sn-cΣ h₁ h₂) hp'     = cr3 (sn-cΣ h₁ h₂) refl
  go (sn-cH h₁ h₂ h₃) hp'  = cr3 (sn-cH h₁ h₂ h₃) refl
  go (sn-cId h₁ h₂ h₃) hp' = cr3 (sn-cId h₁ h₂ h₃) refl
  go (sn-idrefl h₁ h₂) hp' = cr3 (sn-idrefl h₁ h₂) refl
  go sn-unit hp'           = cr3 sn-unit refl
  go sn-nzero hp'          = cr3 sn-nzero refl
  go (sn-nsuc h) hp'       = cr3 (sn-nsuc h) refl

  -- the path's own head star, wrapped into the tr.
  trP-star : {p₁ p₂ : RTm Ξ} → p₁ ⟶snr* p₂ →
             tr dI p₁ eI ⟶snr* tr dI p₂ eI
  trP-star snr-done       = snr-done
  trP-star (snr-step r q) = snr-step (snr-trᵖ r) (trP-star q)

  goh sn-cb sns kn hp' =
    ( R_result , exp₁ R_result (snr-J-base snD sns) heTgt )
  -- ⌜Unit⌝ is `stkC?`, so J FIRES — same endpoint transfer as ⌜base⌝.
  goh sn-cUnit sns kn hp' =
    ( R_result , exp₁ R_result (snr-J-Unit snD sns) heTgt )
  -- ⌜Nat⌝ is not: J is off there (the step-0 retraction), so the whole
  -- `tr` is permanently NEUTRAL and CR3 carries it.
  goh sn-cNat sns kn hp' =
    cr3 (sn-ne (sne-hrefl sn-cNat sns refl)) refl
  goh (sn-cΣ h₁ h₂) sns kn hp' =
    ( R_result , exp₁ R_result (snr-J-Σ snD h₁ h₂ sns) heTgt )
  goh (sn-cId h₁ h₂ h₃) sns kn hp' =
    ( R_result , exp₁ R_result (snr-J-Id snD h₁ h₂ h₃ sns) heTgt )
  goh (sn-idrefl h₁ h₂) sns kn hp' =
    cr3 (sn-ne (sne-hrefl (sn-idrefl h₁ h₂) sns refl)) refl
  goh (sn-exp rc snc') sns kn hp' =
    ( dfst z , exp₁ (dfst z) (snr-trᵖ (snr-hreflᶜ (csr-here rc))) (dsnd z) )
    where z = goh snc' sns (nopw?-red (snr→⟶ rc) kn)
                  (mem-whred₁ R_H (snr-hreflᶜ (csr-here rc)) hp')
  goh (sn-ne nc) sns kn hp' =
    cr3 (sn-ne (sne-hrefl (sn-ne nc) sns (sne→nopw nc))) (sne→stablecd nc)
  goh (sn-lam snb) sns kn hp' =
    cr3 (sn-ne (sne-hrefl (sn-lam snb) sns refl)) refl
  goh (sn-pair sa sb) sns kn hp' =
    cr3 (sn-ne (sne-hrefl (sn-pair sa sb) sns refl)) refl
  goh sn-unit sns kn hp' =
    cr3 (sn-ne (sne-hrefl sn-unit sns refl)) refl
  goh sn-nzero sns kn hp' =
    cr3 (sn-ne (sne-hrefl sn-nzero sns refl)) refl
  goh (sn-nsuc h) sns kn hp' =
    cr3 (sn-ne (sne-hrefl (sn-nsuc h) sns refl)) refl
  goh (sn-cΠ h₁ h₂) sns () hp'
  -- ★ W2b: a ⌜Hom⌝-CODE path — normalize its spine (codeNorm); the
  -- J-able leaf fires tr-J-Hom (endpoint transfer = the SAME heTgt as
  -- J-base), the dead leaf is CR3; both memberships travel back along
  -- the head star.
  goh (sn-cH {c = C₂} {a = a₂} {b = b₂} h₁ h₂ h₃) sns kn hp'
    with codeNormA h₁ kn
  ... | C* , (csr , cfa-stk k) =
        ( R_result
        , expStar₁ R_result
            (trP-star (snrs-hreflᶜ (csrs-hom csr)))
            (exp₁ R_result
              (snr-J-Hom snD (sn-csrs h₁ csr) h₂ h₃ sns k) heTgt) )
  ... | C* , (csr , cfa-dead k) =
        ( R_result
        , expStar₁ R_result
            (trP-star (snrs-hreflᶜ (csrs-hom csr)))
            (CR3₁ R_result
              (sne-tr snD
                (sn-ne (sne-hrefl (sn-cH (sn-csrs h₁ csr) h₂ h₃) sns
                                  (nopw?-csrs csr kn)))
                snE k)) )

-- ★ `⊢conv` — no validity premise, no `⊢ty` closed under conversion.  The
-- relation is already closed under conversion; this is the whole of §4.0.
fund {σ = σ} (⊢conv d c) x₀ ρ =
  ( conv₁ (≅ᵀ-sub σ c) (dfst (fund d x₀ ρ))
  , sem-conv (≅ᵀ-sub σ c) (dfst (fund d x₀ ρ))
             (conv₁ (≅ᵀ-sub σ c) (dfst (fund d x₀ ρ))) (dsnd (fund d x₀ ρ)) )

------------------------------------------------------------------------
-- 7. STARTING THE INDUCTION, and the corollaries.
--
-- ★ EVERY RENAMING SUBSTITUTION IS REDUCIBLE.  This is the "identity
-- substitution is reducible" lemma, generalised over a renaming — and the
-- generalisation is what makes it provable WITHOUT a renaming action on `⊩₁`
-- (which does not exist, see the header).  At `c-▹` the type is built by
-- `fund-ty` AT THE RENAMED SUBSTITUTION directly, so nothing ever has to be
-- transported across scopes; the members are variables, free by `CR3₁`.
--
-- Recursion is on `⊢ctx Γ`, which is why `wnorm` needs it and `fund` does not.
------------------------------------------------------------------------

⊩ˢ-ren : ⊢ctx Γ → (ρ : Ren ⌊ Γ ⌋ Ξ) → Γ ⊩ˢ ⟨ ρ ⟩ᵣ
⊩ˢ-ren c-◇ ρ ()
⊩ˢ-ren (c-▹ {A = A} wΓ tyA) ρ here = ( R , CR3₁ R (sne-var (ρ vz)) )
  where
    eq : subTy ⟨ ρ ⟩ᵣ (renTy vs A) ≡ subTy ⟨ ρ ∘ᵣ vs ⟩ᵣ A
    eq = trans (subTy-renTy A) (subTy-cong (λ _ → refl) A)

    R = ⊩₁cast (sym eq) (fund-ty tyA (ρ vz) (⊩ˢ-ren wΓ (ρ ∘ᵣ vs)))
⊩ˢ-ren (c-▹ wΓ tyA) ρ (there {A = B} d) =
  relTy (sym eq) (⊩ˢ-ren wΓ (ρ ∘ᵣ vs) d)
  where
    eq : subTy ⟨ ρ ⟩ᵣ (renTy vs B) ≡ subTy ⟨ ρ ∘ᵣ vs ⟩ᵣ B
    eq = trans (subTy-renTy B) (subTy-cong (λ _ → refl) B)

------------------------------------------------------------------------
-- ★ THE THEOREM.  Run the induction at `vs`, which makes the target scope
-- non-empty for free, and undo that one weakening with §2.
------------------------------------------------------------------------

snorm : {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → ⊢ctx Γ → Γ ⊢ t ∷ A → SN t
snorm {t = t} wΓ d = sn-anti (subst SN (subTm-var vs t) (CR1₁ R m))
  where
    R = dfst (fund d vz (⊩ˢ-ren wΓ vs))
    m = dsnd (fund d vz (⊩ˢ-ren wΓ vs))

-- ⚠ WEAK normalization is the headline (handoff §4.1): `SN` here is the
-- INDUCTIVE Joachimski–Matthes predicate, and nothing proves it equivalent to
-- accessibility-`SN`.  `dec-conv` consumes `WN`, so nothing downstream cares.
wnorm : {t : RTm ⌊ Γ ⌋} {A : RTy ⌊ Γ ⌋} → ⊢ctx Γ → Γ ⊢ t ∷ A → WN t
wnorm wΓ d = wn (snorm wΓ d)

------------------------------------------------------------------------
-- ★ PHASE 1 CLOSED: `dec-conv` with its normalization premises DISCHARGED.
-- Deciding conversion of two well-typed terms now asks for nothing but the
-- derivations (and decidable equality of raw terms, which is structural).
------------------------------------------------------------------------

dec-conv-typed : (dec-eq : {Θ : Cx} (t u : RTm Θ) → Dec (t ≡ u)) →
                 {t u : RTm ⌊ Γ ⌋} {A B : RTy ⌊ Γ ⌋} →
                 ⊢ctx Γ → Γ ⊢ t ∷ A → Γ ⊢ u ∷ B → Dec (t ≅ u)
dec-conv-typed deq wΓ d₁ d₂ with wnorm wΓ d₁ | wnorm wΓ d₂
... | mkWN n₁ r₁ nm₁ _ | mkWN n₂ r₂ nm₂ _ = dec-conv deq r₁ nm₁ r₂ nm₂

------------------------------------------------------------------------
-- 8. NON-VACUITY — the theorem RUNS.
--
-- Type-checking these is the check that `fund` is not merely inhabited but
-- computes: each equation forces the whole induction (`⊩ˢ-ren`, the semantic
-- lemmas, `wn`) to evaluate on a closed derivation, and pins the normal form.
------------------------------------------------------------------------

-- `◇ ⊢ λx.x ∷ Π base base` — already normal, and `wnorm` says so.
id-nf : WN.nfm (wnorm c-◇ ⊢id) ≡ lam (var vz)
id-nf = refl

-- `(◇ ▹ base) ⊢ (λx.x) y ∷ base` — a real β-redex, contracted by the theorem.
appex-nf : WN.nfm (wnorm (c-▹ c-◇ ty-base) ⊢appex) ≡ var vz
appex-nf = refl
