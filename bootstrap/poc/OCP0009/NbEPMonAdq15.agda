------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A4.4 — THE FUNDAMENTAL LEMMA
--
--   fund : R A v t → R B (evalV f v) (f ∘c t)
--
-- by induction on the combinator `f`. Each case relates the model's
-- evalV computation to the syntactic action `f ∘c t` through R. The
-- transport-free split monad keeps the tree-shaped cases (⊗c, σc via
-- mapSp) clean node recursion; the bindSp/withSp/absorb cases (α, ƛ,
-- ρ, ev) consume the A2 realizations through the A3 splice structure.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq15 where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc; Λc; evc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘; cσ-nat; cα-nat
        ; cƛ-nat; cρ-nat; cƛ-iso₁; cƛ-iso₂; cρ-iso₁; cρ-iso₂
        ; β⊸ )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm; pid; _⊙P_; padˡ; padʳ; passoc; passocInv
        ; pidRInv; bswapW )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv )
open import poc.OCP0009.NbEPMonF
  using ( Sp; ret; spl; usI; Val; evalV; mapSp; bindSp; absorb; vmap
        ; withSpˡ; withSpʳ; ⊗Leaf
        ; evkα; evkαi; evkαl; evkαli; evkƛ; evkƛo; evkρ; evkρo )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; mult-inv-r )
open import poc.OCP0009.NbEPMonAdq2
  using ( ⊙P-realC; inv-natC; pid-realC; α-natˡC )
open import poc.OCP0009.NbEPMonAdq3
  using ( padˡ-real )
open import poc.OCP0009.NbEPMonAdq8
  using ( passocInv-real; pidRInv-real )
open import poc.OCP0009.NbEPMonAdq9
  using ( node-perm-real )
open import poc.OCP0009.NbEPMonAdq6
  using ( bswapW-real; pidR-real )
open import poc.OCP0009.NbEPMonAdq12
  using ( R; R⊗; RI; R-resp; R⊗-resp )
open import poc.OCP0009.NbEPMonAdq13
  using ( R-vmap )
open import poc.OCP0009.NbEPMonAdq16
  using ( RVal; R-join )
open import poc.OCP0009.NbEPMonAdq14
  using ( R-reify; R-reflectNe; R-reflectTy )
open import poc.OCP0009.NbEPMonAdq17
  using ( Tree; Tree-resp; bindSp-Tree; withSpˡ-Tree; withSpʳ-Tree )

------------------------------------------------------------------------
-- ƛl / ρl naturality (inverse unitors), for the ƛlc / ρlc cases.
------------------------------------------------------------------------

private
  -- ƛl / ρl naturality (inverse unitors), from the inverse-naturality
  -- combinator.
  ƛl-nat : ∀ {A B} {t : CTm A B} → ((idc {I} ⊗c t) ∘c ƛlc) ≈c (ƛlc ∘c t)
  ƛl-nat = inv-natC cƛ-iso₂ cƛ-iso₁ cƛ-nat

  ρl-nat : ∀ {A B} {t : CTm A B} → ((t ⊗c idc {I}) ∘c ρlc) ≈c (ρlc ∘c t)
  ρl-nat = inv-natC cρ-iso₂ cρ-iso₁ cρ-nat

------------------------------------------------------------------------
-- R⊗ / RI / RVal are `Tree`-instances; convert to/from the generic Tree
-- so the withSp/bindSp splice lemmas (Adq17) apply.
------------------------------------------------------------------------

private
  L⊗ : ∀ A B {Δ} → _ → CTm ⟪ Δ ⟫ (A ⊗ B) → Set
  L⊗ A B p s = R⊗ A B (ret p) s

  R⊗→Tree : ∀ {A B Γ} (v : Val (A ⊗ B) Γ) {t} →
            R⊗ A B v t → Tree (L⊗ A B) v t
  R⊗→Tree (ret p)     r             = r
  R⊗→Tree (spl ρ n k) (t' , (rk , e)) = t' , (R⊗→Tree k rk , e)
  R⊗→Tree (usI ρ n k) (t' , (rk , e)) = t' , (R⊗→Tree k rk , e)

  Tree→R⊗ : ∀ {A B Γ} (v : Val (A ⊗ B) Γ) {t} →
            Tree (L⊗ A B) v t → R⊗ A B v t
  Tree→R⊗ (ret p)     r             = r
  Tree→R⊗ (spl ρ n k) (t' , (rk , e)) = t' , (Tree→R⊗ k rk , e)
  Tree→R⊗ (usI ρ n k) (t' , (rk , e)) = t' , (Tree→R⊗ k rk , e)

  L⊗-resp : ∀ A B {Δ} (p : _) {s s'} → L⊗ A B {Δ} p s → s ≈c s' → L⊗ A B p s'
  L⊗-resp A B p r e = R⊗-resp {v = ret p} r e

  LI : ∀ {Δ} → Δ ≡ ε → CTm ⟪ Δ ⟫ I → Set
  LI p s = RI (ret p) s

  RI→Tree : ∀ {Γ} (v : Sp (λ Δ → Δ ≡ ε) Γ) {t} →
            RI v t → Tree LI v t
  RI→Tree (ret refl)   r             = r
  RI→Tree (spl ρ n k) (t' , (rk , e)) = t' , (RI→Tree k rk , e)
  RI→Tree (usI ρ n k) (t' , (rk , e)) = t' , (RI→Tree k rk , e)

  -- The node-permutation realized for the LEFT (αl) side — the mirror
  -- of `node-perm-real`, from passocInv-real + padˡ-real + ⊙P-realC.
  node-perm-realˡ :
    ∀ {Γ Γ₂} Δ₁ Θ₁ Θ₂ (q : Perm Γ₂ (Θ₁ ++ Θ₂)) (ρ : Perm Γ (Δ₁ ++ Γ₂)) →
    (mult (Δ₁ ++ Θ₁) Θ₂ ∘c permC ((ρ ⊙P padˡ Δ₁ q) ⊙P passocInv Δ₁ Θ₁ Θ₂)) ≈c
    ((multInv Δ₁ Θ₁ ⊗c idc {⟪ Θ₂ ⟫}) ∘c
     (αlc ∘c ((idc {⟪ Δ₁ ⟫} ⊗c (mult Θ₁ Θ₂ ∘c permC q)) ∘c
              (mult Δ₁ Γ₂ ∘c permC ρ))))
  node-perm-realˡ Δ₁ Θ₁ Θ₂ q ρ =
    ≈ctrans (∘c-congʳ (⊙P-realC (ρ ⊙P padˡ Δ₁ q) (passocInv Δ₁ Θ₁ Θ₂)))
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ (passocInv-real Δ₁ Θ₁ Θ₂))
    (≈ctrans (∘c-congʳ (⊙P-realC ρ (padˡ Δ₁ q)))
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ
               (≈ctrans (≈csym c∘-assoc)
               (≈ctrans (∘c-congˡ (padˡ-real Δ₁ q)) c∘-assoc)))))
             (∘c-congʳ (∘c-congʳ
               (≈ctrans (≈csym c∘-assoc)
                        (∘c-congˡ (≈ctrans (≈csym c⊗-∘)
                                           (⊗c-cong cid-l ≈crefl)))))))))))))

  LV : ∀ B {Δ} → Val B Δ → CTm ⟪ Δ ⟫ B → Set
  LV B x s = R B x s

  Tree→RVal : ∀ {B Γ} (v : Sp (Val B) Γ) {t} →
              Tree (LV B) v t → RVal B v t
  Tree→RVal (ret x)     r             = r
  Tree→RVal (spl ρ n k) (t' , (rk , e)) = t' , (Tree→RVal k rk , e)
  Tree→RVal (usI ρ n k) (t' , (rk , e)) = t' , (Tree→RVal k rk , e)

------------------------------------------------------------------------
-- THE FUNDAMENTAL LEMMA.
------------------------------------------------------------------------

fund : ∀ {A B} (f : CTm A B) {Γ} {v : Val A Γ} {t : CTm ⟪ Γ ⟫ A} →
       R A v t → R B (evalV f v) (f ∘c t)

fund (idc {A}) r = R-resp A r (≈csym cid-l)

fund (_∘c_ {A} {B} {D} f g) r =
  R-resp D (fund f (fund g r)) (≈csym c∘-assoc)

-- ⊗c: mapSp preserves the tree; the ret leaf applies the two IHs.
fund (_⊗c_ {A} {B} {D} {E} f g) {v = v} {t} r = ⊗h v r
  where
  ⊗h : ∀ {Γ} (w : Val (A ⊗ D) Γ) {s : CTm ⟪ Γ ⟫ (A ⊗ D)} →
       R⊗ A D w s → R⊗ B E (evalV (f ⊗c g) w) ((f ⊗c g) ∘c s)
  ⊗h (ret (Δ₁ , (Δ₂ , (ρ , (va , vb))))) (ta , (td , (ra , (rd , e)))) =
    (f ∘c ta) , ((g ∘c td) ,
      (fund f ra , (fund g rd ,
        ≈ctrans (∘c-congʳ e)
        (≈ctrans (≈csym c∘-assoc)
                 (∘c-congˡ (≈csym c⊗-∘))))))
  ⊗h (spl ρ n k) (t' , (rk , e)) = ((f ⊗c g) ∘c t') , (⊗h k rk , ≈ctrans (∘c-congʳ e) (≈csym c∘-assoc))
  ⊗h (usI ρ n k) (t' , (rk , e)) = ((f ⊗c g) ∘c t') , (⊗h k rk , ≈ctrans (∘c-congʳ e) (≈csym c∘-assoc))

-- σc: mapSp swaps the components; the ret leaf swaps the relations.
fund (σc {A} {B}) {v = v} {t} r = σh v r
  where
  σh : ∀ {Γ} (w : Val (A ⊗ B) Γ) {s : CTm ⟪ Γ ⟫ (A ⊗ B)} →
       R⊗ A B w s → R⊗ B A (evalV (σc {A} {B}) w) (σc ∘c s)
  σh (ret (Δ₁ , (Δ₂ , (ρ , (va , vb))))) (ta , (tb , (ra , (rb , e)))) =
    tb , (ta , (rb , (ra ,
      ≈ctrans (∘c-congʳ e)
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ cσ-nat)
      (≈ctrans c∘-assoc (∘c-congʳ σmult)))))))
    where
    σmult : (σc ∘c (mult Δ₁ Δ₂ ∘c permC ρ)) ≈c
            (mult Δ₂ Δ₁ ∘c permC (ρ ⊙P bswapW Δ₁ Δ₂))
    σmult =
      ≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ (≈csym (bswapW-real Δ₁ Δ₂)))
      (≈ctrans c∘-assoc
               (∘c-congʳ (≈csym (⊙P-realC ρ (bswapW Δ₁ Δ₂))))))
  σh (spl ρ n k) (t' , (rk , e)) = (σc ∘c t') , (σh k rk , ≈ctrans (∘c-congʳ e) (≈csym c∘-assoc))
  σh (usI ρ n k) (t' , (rk , e)) = (σc ∘c t') , (σh k rk , ≈ctrans (∘c-congʳ e) (≈csym c∘-assoc))

fund (αrc {A} {B} {D}) {v = v} {t} r =
  Tree→R⊗ (bindSp v evkα)
    (bindSp-Tree (L⊗ (A ⊗ B) D) (L⊗ A (B ⊗ D)) αrc evkα HKα v (R⊗→Tree v r))
  where
  HKα : ∀ {Δ} (p : ⊗Leaf (A ⊗ B) D Δ) {s} →
        L⊗ (A ⊗ B) D p s → Tree (L⊗ A (B ⊗ D)) (evkα p) (αrc ∘c s)
  HKα (Δ₁ , (Δ₂ , (ρ , (vab , vd)))) {s} (tab , (td , (rab , (rd , es)))) =
    Tree-resp (L⊗ A (B ⊗ D)) (L⊗-resp A (B ⊗ D))
      {sp = withSpˡ ρ vab (evkαi vd)}
      (withSpˡ-Tree (L⊗ A B) (L⊗ A (B ⊗ D)) (αrc ∘c (idc ⊗c td)) (evkαi vd) Hfα
                    ρ vab (R⊗→Tree vab rab))
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ (≈ctrans (≈csym c∘-assoc)
                         (≈ctrans (∘c-congˡ (≈ctrans (≈csym c⊗-∘)
                                            (⊗c-cong cid-l cid-r)))
                                  (≈csym es))))
               ≈crefl))
    where
    Hfα : ∀ {Ξ Δ'} (ρ' : Perm Δ' (Ξ ++ Δ₂)) (p' : ⊗Leaf A B Ξ)
          {sp'} → L⊗ A B p' sp' →
          Tree (L⊗ A (B ⊗ D)) (evkαi vd ρ' p')
            ((αrc ∘c (idc ⊗c td)) ∘c ((sp' ⊗c idc) ∘c (mult Ξ Δ₂ ∘c permC ρ')))
    Hfα {Ξ} ρ' (Θ₁ , (Θ₂ , (ρᵢ , (va , vb)))) {sp'}
        (taa , (tb , (rva , (rvb , esp)))) =
      taa , (((tb ⊗c td) ∘c (mult Θ₂ Δ₂ ∘c permC (pid (Θ₂ ++ Δ₂)))) ,
        (rva , ((tb , (td , (rvb , (rd , ≈crefl)))) ,
          ≈ctrans Ahalf (≈csym Bhalf))))
      where
      Q  = mult Θ₁ Θ₂ ∘c permC ρᵢ
      M' = mult Ξ Δ₂ ∘c permC ρ'
      MPinv = ≈ctrans c∘-assoc
              (≈ctrans (∘c-congʳ (∘c-congˡ (pid-realC _)))
              (≈ctrans (∘c-congʳ cid-l) (mult-inv-r Θ₂ Δ₂)))
      Xtb = ≈ctrans c∘-assoc (≈ctrans (∘c-congʳ MPinv) cid-r)
      Bsimp = ≈ctrans (≈csym c⊗-∘) (⊗c-cong cid-r Xtb)
      Bhalf = ≈ctrans (∘c-congʳ (node-perm-real Θ₁ Θ₂ Δ₂ ρᵢ ρ'))
              (≈ctrans (≈csym c∘-assoc) (∘c-congˡ Bsimp))
      Ahalf = ≈ctrans c∘-assoc
              (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ (⊗c-cong esp ≈crefl))))
              (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ
                        (≈ctrans (⊗c-cong ≈crefl (≈csym cid-l)) c⊗-∘))))
              (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
              (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
              (≈ctrans (∘c-congʳ (∘c-congˡ (≈ctrans (≈csym c⊗-∘) (⊗c-cong cid-l cid-r))))
              (≈ctrans (≈csym c∘-assoc)
              (≈ctrans (∘c-congˡ cα-nat) c∘-assoc)))))))
fund (αlc {A} {B} {D}) {v = v} {t} r =
  Tree→R⊗ (bindSp v evkαl)
    (bindSp-Tree (L⊗ A (B ⊗ D)) (L⊗ (A ⊗ B) D) αlc evkαl HKα v (R⊗→Tree v r))
  where
  HKα : ∀ {Δ} (p : ⊗Leaf A (B ⊗ D) Δ) {s} →
        L⊗ A (B ⊗ D) p s → Tree (L⊗ (A ⊗ B) D) (evkαl p) (αlc ∘c s)
  HKα (Δ₁ , (Δ₂ , (ρ , (va , vbd)))) {s} (ta , (tbd , (rva , (rbd , es)))) =
    Tree-resp (L⊗ (A ⊗ B) D) (L⊗-resp (A ⊗ B) D)
      {sp = withSpʳ ρ vbd (evkαli va)}
      (withSpʳ-Tree (L⊗ B D) (L⊗ (A ⊗ B) D) (αlc ∘c (ta ⊗c idc)) (evkαli va) Hfα
                    ρ vbd (R⊗→Tree vbd rbd))
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ (≈ctrans (≈csym c∘-assoc)
                         (≈ctrans (∘c-congˡ (≈ctrans (≈csym c⊗-∘)
                                            (⊗c-cong cid-r cid-l)))
                                  (≈csym es))))
               ≈crefl))
    where
    Hfα : ∀ {Ξ Δ'} (ρ' : Perm Δ' (Δ₁ ++ Ξ)) (p' : ⊗Leaf B D Ξ)
          {sp'} → L⊗ B D p' sp' →
          Tree (L⊗ (A ⊗ B) D) (evkαli va ρ' p')
            ((αlc ∘c (ta ⊗c idc)) ∘c ((idc ⊗c sp') ∘c (mult Δ₁ Ξ ∘c permC ρ')))
    Hfα {Ξ} ρ' (Θ₁ , (Θ₂ , (ρᵢ , (vb , vd)))) {sp'}
        (tb , (td , (rvb , (rvd , esp)))) =
      ((ta ⊗c tb) ∘c (mult Δ₁ Θ₁ ∘c permC (pid (Δ₁ ++ Θ₁)))) ,
        (td , ((ta , (tb , (rva , (rvb , ≈crefl)))) ,
          (rvd , ≈ctrans Ahalf (≈csym Bhalf))))
      where
      Q  = mult Θ₁ Θ₂ ∘c permC ρᵢ
      M' = mult Δ₁ Ξ ∘c permC ρ'
      MPinv = ≈ctrans c∘-assoc
              (≈ctrans (∘c-congʳ (∘c-congˡ (pid-realC _)))
              (≈ctrans (∘c-congʳ cid-l) (mult-inv-r Δ₁ Θ₁)))
      Xta = ≈ctrans c∘-assoc (≈ctrans (∘c-congʳ MPinv) cid-r)
      Bsimp = ≈ctrans (≈csym c⊗-∘) (⊗c-cong Xta cid-r)
      Bhalf = ≈ctrans (∘c-congʳ (node-perm-realˡ Δ₁ Θ₁ Θ₂ ρᵢ ρ'))
              (≈ctrans (≈csym c∘-assoc) (∘c-congˡ Bsimp))
      Ahalf = ≈ctrans c∘-assoc
              (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ (⊗c-cong ≈crefl esp))))
              (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ
                        (≈ctrans (⊗c-cong (≈csym cid-l) ≈crefl) c⊗-∘))))
              (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
              (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
              (≈ctrans (∘c-congʳ (∘c-congˡ (≈ctrans (≈csym c⊗-∘) (⊗c-cong cid-r cid-l))))
              (≈ctrans (≈csym c∘-assoc)
              (≈ctrans (∘c-congˡ (≈csym α-natˡC)) c∘-assoc)))))))
fund (ƛrc {A}) {v = v} {t} r =
  R-join A (bindSp v evkƛo)
    (Tree→RVal (bindSp v evkƛo)
      (bindSp-Tree (L⊗ I A) (LV A) ƛrc evkƛo HKƛ v (R⊗→Tree v r)))
  where
  HKƛ : ∀ {Δ} (p : ⊗Leaf I A Δ) {s} →
        L⊗ I A p s → Tree (LV A) (evkƛo p) (ƛrc ∘c s)
  HKƛ (Δ₁ , (Δ₂ , (ρ , (vI , va)))) {s} (tI , (ta , (rI , (ra , es)))) =
    Tree-resp (LV A) (λ x → R-resp A)
      {sp = withSpˡ ρ vI (evkƛ A va)}
      (withSpˡ-Tree LI (LV A) (ƛrc ∘c (idc ⊗c ta)) (evkƛ A va) Hfƛ
                    ρ vI (RI→Tree vI rI))
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ (≈ctrans (≈csym c∘-assoc)
                         (≈ctrans (∘c-congˡ (≈ctrans (≈csym c⊗-∘)
                                            (⊗c-cong cid-l cid-r)))
                                  (≈csym es))))
               ≈crefl))
    where
    Hfƛ : ∀ {Δ₁' Δ'} (ρ' : Perm Δ' (Δ₁' ++ Δ₂)) (p' : Δ₁' ≡ ε)
          {sp'} → LI p' sp' →
          Tree (LV A) (evkƛ A va ρ' p')
            ((ƛrc ∘c (idc ⊗c ta)) ∘c ((sp' ⊗c idc) ∘c (mult Δ₁' Δ₂ ∘c permC ρ')))
    Hfƛ ρ' refl {sp'} rsp =
      R-resp A (R-vmap A ρ' ra)
        (≈csym (≈ctrans c∘-assoc
               (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ
                          (⊗c-cong (≈csym rsp) ≈crefl))))
               (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ c⊗-id)))
               (≈ctrans (∘c-congʳ (∘c-congʳ cid-l))
               (≈ctrans (≈csym c∘-assoc)
               (≈ctrans (∘c-congˡ cƛ-nat)
               (≈ctrans c∘-assoc
               (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
               (≈ctrans (∘c-congʳ (∘c-congˡ cƛ-iso₁))
                        (∘c-congʳ cid-l)))))))))))
fund ƛlc {Γ} {v = v} {t} r =
  idc , (t , (≈crefl , (r ,
    ≈csym (≈ctrans (∘c-congʳ (∘c-congʳ (pid-realC Γ)))
           (≈ctrans (∘c-congʳ cid-r) ƛl-nat)))))
fund (ρrc {A}) {v = v} {t} r =
  R-join A (bindSp v evkρo)
    (Tree→RVal (bindSp v evkρo)
      (bindSp-Tree (L⊗ A I) (LV A) ρrc evkρo HKρ v (R⊗→Tree v r)))
  where
  HKρ : ∀ {Δ} (p : ⊗Leaf A I Δ) {s} →
        L⊗ A I p s → Tree (LV A) (evkρo p) (ρrc ∘c s)
  HKρ (Δ₁ , (Δ₂ , (ρ , (va , vI)))) {s} (ta , (tI , (ra , (rI , es)))) =
    Tree-resp (LV A) (λ x → R-resp A)
      {sp = withSpʳ ρ vI (evkρ A va)}
      (withSpʳ-Tree LI (LV A) (ρrc ∘c (ta ⊗c idc)) (evkρ A va) Hfρ
                    ρ vI (RI→Tree vI rI))
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ (≈ctrans (≈csym c∘-assoc)
                         (≈ctrans (∘c-congˡ (≈ctrans (≈csym c⊗-∘)
                                            (⊗c-cong cid-r cid-l)))
                                  (≈csym es))))
               ≈crefl))
    where
    Hfρ : ∀ {Δ₂' Δ'} (ρ' : Perm Δ' (Δ₁ ++ Δ₂')) (p' : Δ₂' ≡ ε)
          {sp'} → LI p' sp' →
          Tree (LV A) (evkρ A va ρ' p')
            ((ρrc ∘c (ta ⊗c idc)) ∘c ((idc ⊗c sp') ∘c (mult Δ₁ Δ₂' ∘c permC ρ')))
    Hfρ ρ' refl {sp'} rsp =
      R-resp A (R-vmap A (ρ' ⊙P pidRInv Δ₁) ra)
        (≈ctrans (∘c-congʳ (⊙P-realC ρ' (pidRInv Δ₁)))
        (≈ctrans (∘c-congʳ (∘c-congˡ (pidRInv-real Δ₁)))
        (≈ctrans (∘c-congʳ c∘-assoc)
        (≈ctrans (≈csym c∘-assoc)
        (≈ctrans (∘c-congˡ (≈csym cρ-nat))
                 (∘c-congʳ
                   (≈csym (≈ctrans (∘c-congˡ
                             (≈ctrans (⊗c-cong ≈crefl (≈csym rsp)) c⊗-id))
                          cid-l))))))))
fund ρlc {Γ} {v = v} {t} r =
  t , (idc , (r , (≈crefl ,
    ≈csym (≈ctrans (∘c-congʳ (pidR-real Γ)) ρl-nat))))
fund (Λc f) {Γ} {v = v} {t} r {Δ} w s rws =
  R-resp _
    (fund f {v = ret (Γ , (Δ , (pid (Γ ++ Δ) , (v , w))))}
            (t , (s , (r , (rws , ≈crefl)))))
    termEq
  where
  tEq : (evc ∘c (((Λc f ∘c t) ⊗c s) ∘c mult Γ Δ)) ≈c
        (f ∘c ((t ⊗c s) ∘c mult Γ Δ))
  tEq =
    ≈ctrans (∘c-congʳ (∘c-congˡ
              (≈csym (≈ctrans (≈csym c⊗-∘) (⊗c-cong ≈crefl cid-l)))))
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (≈csym c∘-assoc) (∘c-congˡ β⊸)))
  termEq :
    (f ∘c ((t ⊗c s) ∘c (mult Γ Δ ∘c permC (pid (Γ ++ Δ))))) ≈c
    (evc ∘c (((Λc f ∘c t) ⊗c s) ∘c mult Γ Δ))
  termEq =
    ≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (pid-realC (Γ ++ Δ)))))
    (≈ctrans (∘c-congʳ (∘c-congʳ cid-r)) (≈csym tEq))
fund (evc {A} {B}) {v = v} {t} r =
  R-join B (bindSp v K) (evc-tree v r)
  where
  K : ∀ {Δ} →
      Σ Ctx (λ Δ₁ → Σ Ctx (λ Δ₂ →
        Σ (Perm Δ (Δ₁ ++ Δ₂)) (λ _ →
          Σ (Val (A ⊸ B) Δ₁) (λ _ → Val A Δ₂)))) → Sp (Val B) Δ
  K (Δ₁ , (Δ₂ , (ρ , (vf , va)))) = ret (vmap B ρ (vf Δ₂ va))
  evc-tree : ∀ {Γ} (w : Val ((A ⊸ B) ⊗ A) Γ) {u} →
             R⊗ (A ⊸ B) A w u → RVal B (bindSp w K) (evc ∘c u)
  evc-tree (ret (Δ₁ , (Δ₂ , (ρ , (vf , va)))))
           (tf , (ta , (rf , (ra , e)))) =
    R-resp B (R-vmap B ρ (rf va ta ra))
             (≈ctrans c∘-assoc (≈ctrans (∘c-congʳ c∘-assoc)
                               (∘c-congʳ (≈csym e))))
  evc-tree (spl ρ n k) (t' , (rk , e)) = (evc ∘c t') , (evc-tree k rk , ≈ctrans (∘c-congʳ e) (≈csym c∘-assoc))
  evc-tree (usI ρ n k) (t' , (rk , e)) = (evc ∘c t') , (evc-tree k rk , ≈ctrans (∘c-congʳ e) (≈csym c∘-assoc))
