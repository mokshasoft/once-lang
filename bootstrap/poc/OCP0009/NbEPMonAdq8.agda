------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A3b.1 — THE STRUCTURAL PERMS, REALIZED
--
-- The model is now transport-free (`NbEPMonF` composes structural
-- permutations `passoc`/`passocInv`/`pidR`/`pidRInv` instead of
-- `psubst`-ing along list equalities). This module realizes them:
--
--   * `passoc-real`    : mult ∘ permC (passoc) ≈ the α-mediated
--     double-mult path (cons case lands on `α-pent2`, the 5-α lemma
--     proven by compose-and-cancel onto the mirror pentagon)
--   * `passocInv-real` : FREE from passoc-real — `passoc ⊙P passocInv`
--     is LITERALLY `pid` (a two-line ≡-induction), so the inverse
--     realization follows by right-cancellation. No mirror pentagon.
--   * `pidRInv-real`   : permC (pidRInv Δ) ≈ ρr ∘ mult Δ ε (via the
--     right-unit triangle)
--   * `cancel-rightC`  — the reusable cancel-an-iso-on-the-right
--     combinator; `K2ₗC` — Kelly's lemma for `ƛl`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq8 where

open import normalizer.Syntax.Types
  using ( _≡_; refl; cong )
open import poc.OCP0009.NbEPMonL
  using ( CTy; I; _⊗_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘
        ; cƛ-nat
        ; cα-iso₁; cα-iso₂; cƛ-iso₁; cƛ-iso₂; cρ-iso₁; cρ-iso₂ )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_
        ; Ins; here; there; Perm; pnil; pcons; pid
        ; _⊙P_; push; padʳ
        ; pidR; pidRInv; passoc; passocInv )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; cancelC; fuse⊗ˡC; fuse⊗ʳC
        ; mult-inv-l; mult-inv-r )
open import poc.OCP0009.NbEPMonAdq2
  using ( inv-natC; α-natˡC; ⊗α-cancelˡC; ⊗α-cancelˡ′C; pid-realC
        ; ⊙P-realC )
open import poc.OCP0009.NbEPMonAdq3
  using ( inv-congC; pentagonₗC )
open import poc.OCP0009.NbEPMonAdq4
  using ( K2C )
open import poc.OCP0009.NbEPMonAdq5
  using ( tri-ρC )

------------------------------------------------------------------------
-- Kit: right-cancellation of an iso, and Kelly's lemma for ƛl.
------------------------------------------------------------------------

cancel-rightC : ∀ {P Q R} {X Y : CTm Q R} {Z : CTm P Q} {Z' : CTm Q P} →
                (Z ∘c Z') ≈c idc → (X ∘c Z) ≈c (Y ∘c Z) → X ≈c Y
cancel-rightC p e =
  ≈ctrans (≈csym cid-r)
  (≈ctrans (∘c-congʳ (≈csym p))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ e)
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ p) cid-r)))))

K2ₗC : ∀ {A B} → (ƛlc {A} ⊗c idc {B}) ≈c (αlc ∘c ƛlc {A ⊗ B})
K2ₗC =
  inv-congC
    (≈ctrans fuse⊗ʳC (≈ctrans (⊗c-cong cƛ-iso₁ ≈crefl) c⊗-id))
    (≈ctrans (cancelC cƛ-iso₂) cα-iso₂)
    K2C

------------------------------------------------------------------------
-- The 5-α lemma (compose-and-cancel onto the mirror pentagon).
------------------------------------------------------------------------

α-pent2 : ∀ {A B D E} →
          (αlc {A} {B} {D ⊗ E} ∘c (idc {A} ⊗c αrc {B} {D} {E})) ≈c
          (αrc {A ⊗ B} {D} {E} ∘c
           ((αlc {A} {B} {D} ⊗c idc {E}) ∘c αlc {A} {B ⊗ D} {E}))
α-pent2 =
  cancel-rightC ⊗α-cancelˡC
    (≈ctrans (≈ctrans c∘-assoc
             (≈ctrans (∘c-congʳ ⊗α-cancelˡ′C) cid-r))
             (≈csym rhs∘))
  where
  rhs∘ : ∀ {A B D E} →
         ((αrc {A ⊗ B} {D} {E} ∘c
           ((αlc {A} {B} {D} ⊗c idc {E}) ∘c αlc {A} {B ⊗ D} {E})) ∘c
          (idc {A} ⊗c αlc {B} {D} {E}))
         ≈c αlc {A} {B} {D ⊗ E}
  rhs∘ =
    ≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ pentagonₗC)
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ cα-iso₁) cid-l))))

------------------------------------------------------------------------
-- ⊙P data laws (literal ≡): pid is a left unit; passoc's two-sided
-- inverse is passocInv, ON THE NOSE.
------------------------------------------------------------------------

⊙P-pidˡ : ∀ {xs ys} (q : Perm xs ys) → (pid xs ⊙P q) ≡ q
⊙P-pidˡ pnil        = refl
⊙P-pidˡ (pcons q i) = cong (λ z → pcons z i) (⊙P-pidˡ q)

passoc-inv : ∀ Θ₁ Θ₂ Θ₃ →
             (passoc Θ₁ Θ₂ Θ₃ ⊙P passocInv Θ₁ Θ₂ Θ₃) ≡
             pid ((Θ₁ ++ Θ₂) ++ Θ₃)
passoc-inv ε        Θ₂ Θ₃ = ⊙P-pidˡ (pid (Θ₂ ++ Θ₃))
passoc-inv (A ∷ Θ₁) Θ₂ Θ₃ =
  cong (λ z → pcons z here) (passoc-inv Θ₁ Θ₂ Θ₃)

passocInv-inv : ∀ Θ₁ Θ₂ Θ₃ →
                (passocInv Θ₁ Θ₂ Θ₃ ⊙P passoc Θ₁ Θ₂ Θ₃) ≡
                pid (Θ₁ ++ (Θ₂ ++ Θ₃))
passocInv-inv ε        Θ₂ Θ₃ = ⊙P-pidˡ (pid (Θ₂ ++ Θ₃))
passocInv-inv (A ∷ Θ₁) Θ₂ Θ₃ =
  cong (λ z → pcons z here) (passocInv-inv Θ₁ Θ₂ Θ₃)

private
  permC-≡ : ∀ {xs ys} {p q : Perm xs ys} → p ≡ q → permC p ≈c permC q
  permC-≡ refl = ≈crefl

-- permC passoc ∘ permC passocInv ≈ id, and the flip.
passoc-cancel : ∀ Θ₁ Θ₂ Θ₃ →
                (permC (passocInv Θ₁ Θ₂ Θ₃) ∘c permC (passoc Θ₁ Θ₂ Θ₃))
                ≈c idc
passoc-cancel Θ₁ Θ₂ Θ₃ =
  ≈ctrans (≈csym (⊙P-realC (passoc Θ₁ Θ₂ Θ₃) (passocInv Θ₁ Θ₂ Θ₃)))
  (≈ctrans (permC-≡ (passoc-inv Θ₁ Θ₂ Θ₃)) (pid-realC _))

passocInv-cancel : ∀ Θ₁ Θ₂ Θ₃ →
                   (permC (passoc Θ₁ Θ₂ Θ₃) ∘c permC (passocInv Θ₁ Θ₂ Θ₃))
                   ≈c idc
passocInv-cancel Θ₁ Θ₂ Θ₃ =
  ≈ctrans (≈csym (⊙P-realC (passocInv Θ₁ Θ₂ Θ₃) (passoc Θ₁ Θ₂ Θ₃)))
  (≈ctrans (permC-≡ (passocInv-inv Θ₁ Θ₂ Θ₃)) (pid-realC _))

------------------------------------------------------------------------
-- passoc, realized.
------------------------------------------------------------------------

passoc-real : ∀ Θ₁ Θ₂ Θ₃ →
  (mult Θ₁ (Θ₂ ++ Θ₃) ∘c permC (passoc Θ₁ Θ₂ Θ₃)) ≈c
  ((idc {⟪ Θ₁ ⟫} ⊗c multInv Θ₂ Θ₃) ∘c
   (αrc ∘c ((mult Θ₁ Θ₂ ⊗c idc) ∘c mult (Θ₁ ++ Θ₂) Θ₃)))
passoc-real ε Θ₂ Θ₃ =
  ≈ctrans (∘c-congʳ (pid-realC (Θ₂ ++ Θ₃)))
  (≈ctrans cid-r (≈csym rhs-red))
  where
  rhs-red :
    ((idc {I} ⊗c multInv Θ₂ Θ₃) ∘c
     (αrc ∘c ((ƛlc ⊗c idc) ∘c mult Θ₂ Θ₃))) ≈c ƛlc
  rhs-red =
    ≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ K2ₗC)))
    (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congˡ cα-iso₁))
    (≈ctrans (∘c-congʳ cid-l)
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ (inv-natC cƛ-iso₂ cƛ-iso₁ cƛ-nat))
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ (mult-inv-l Θ₂ Θ₃)) cid-r))))))))
passoc-real (A ∷ Θ₁) Θ₂ Θ₃ =
  ≈ctrans (∘c-congʳ cid-l)
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ fuse⊗ˡC)
  (≈ctrans (∘c-congʳ (⊗c-cong ≈crefl (passoc-real Θ₁ Θ₂ Θ₃)))
  (≈ctrans (∘c-congʳ (≈csym fuse⊗ˡC))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym fuse⊗ˡC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym fuse⊗ˡC))))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (≈csym α-natˡC))
  (≈ctrans (∘c-congˡ (∘c-congˡ (⊗c-cong c⊗-id ≈crefl)))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congˡ α-pent2))
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
           (≈csym rhs-shape)))))))))))))))
  where
  rhs-shape :
    ((idc {A ⊗ ⟪ Θ₁ ⟫} ⊗c multInv Θ₂ Θ₃) ∘c
     (αrc ∘c (((αlc ∘c (idc {A} ⊗c mult Θ₁ Θ₂)) ⊗c idc {⟪ Θ₃ ⟫}) ∘c
              (αlc ∘c (idc {A} ⊗c mult (Θ₁ ++ Θ₂) Θ₃)))))
    ≈c
    ((idc {A ⊗ ⟪ Θ₁ ⟫} ⊗c multInv Θ₂ Θ₃) ∘c
     (αrc ∘c ((αlc ⊗c idc {⟪ Θ₃ ⟫}) ∘c
              (αlc ∘c ((idc {A} ⊗c (mult Θ₁ Θ₂ ⊗c idc)) ∘c
                       (idc {A} ⊗c mult (Θ₁ ++ Θ₂) Θ₃))))))
  rhs-shape =
    ≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ (≈csym fuse⊗ʳC))))
    (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ α-natˡC))))
             (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc))))))

------------------------------------------------------------------------
-- passocInv, realized — free, by right-cancellation.
------------------------------------------------------------------------

passocInv-real : ∀ Θ₁ Θ₂ Θ₃ →
  (mult (Θ₁ ++ Θ₂) Θ₃ ∘c permC (passocInv Θ₁ Θ₂ Θ₃)) ≈c
  ((multInv Θ₁ Θ₂ ⊗c idc {⟪ Θ₃ ⟫}) ∘c
   (αlc ∘c ((idc ⊗c mult Θ₂ Θ₃) ∘c mult Θ₁ (Θ₂ ++ Θ₃))))
passocInv-real Θ₁ Θ₂ Θ₃ =
  cancel-rightC (passocInv-cancel Θ₁ Θ₂ Θ₃)
    (≈ctrans lhs∘ (≈csym rhs∘))
  where
  lhs∘ : ((mult (Θ₁ ++ Θ₂) Θ₃ ∘c permC (passocInv Θ₁ Θ₂ Θ₃)) ∘c
          permC (passoc Θ₁ Θ₂ Θ₃)) ≈c mult (Θ₁ ++ Θ₂) Θ₃
  lhs∘ =
    ≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ (passoc-cancel Θ₁ Θ₂ Θ₃)) cid-r)
  rhs∘ : (((multInv Θ₁ Θ₂ ⊗c idc) ∘c
           (αlc ∘c ((idc ⊗c mult Θ₂ Θ₃) ∘c mult Θ₁ (Θ₂ ++ Θ₃)))) ∘c
          permC (passoc Θ₁ Θ₂ Θ₃)) ≈c mult (Θ₁ ++ Θ₂) Θ₃
  rhs∘ =
    ≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ (≈ctrans c∘-assoc (∘c-congʳ (≈ctrans c∘-assoc
              (∘c-congʳ (passoc-real Θ₁ Θ₂ Θ₃))))))
    (≈ctrans (∘c-congʳ (∘c-congʳ (≈ctrans (≈csym c∘-assoc)
              (≈ctrans (∘c-congˡ (≈ctrans fuse⊗ˡC
                        (≈ctrans (⊗c-cong ≈crefl (mult-inv-r Θ₂ Θ₃))
                                 c⊗-id)))
                       cid-l))))
    (≈ctrans (∘c-congʳ (≈ctrans (≈csym c∘-assoc)
              (≈ctrans (∘c-congˡ cα-iso₂) cid-l)))
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ (≈ctrans fuse⊗ʳC
              (≈ctrans (⊗c-cong (mult-inv-l Θ₁ Θ₂) ≈crefl) c⊗-id)))
             cid-l)))))

------------------------------------------------------------------------
-- pidRInv, realized (via the right-unit triangle).
------------------------------------------------------------------------

private
  -- 1_A ⊗ ρr ≈ ρr ∘ αl (the right-unit triangle, solved).
  ρr-αl : ∀ {A B} → (idc {A} ⊗c ρrc {B}) ≈c (ρrc {A ⊗ B} ∘c αlc)
  ρr-αl =
    ≈csym
    (≈ctrans (∘c-congˡ tri-ρC)
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ cα-iso₁) cid-r)))

pidRInv-real : ∀ Δ → permC (pidRInv Δ) ≈c (ρrc ∘c mult Δ ε)
pidRInv-real ε =
  ≈csym (≈ctrans (∘c-congˡ (≈csym ƛρ-IC)) cƛ-iso₁)
  where open import poc.OCP0009.NbEPMonAdq5 using ( ƛρ-IC )
pidRInv-real (A ∷ Δ) =
  ≈ctrans cid-l
  (≈ctrans (⊗c-cong ≈crefl (pidRInv-real Δ))
  (≈ctrans (≈csym fuse⊗ˡC)
  (≈ctrans (∘c-congˡ ρr-αl)
           c∘-assoc)))
