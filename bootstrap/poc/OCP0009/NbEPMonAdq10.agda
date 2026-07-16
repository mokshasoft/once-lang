------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A3b.3 — withSpˡ AND appSp, SPLICED
--
-- The left-pull and the application-under-splits splice as the
-- payload does, uniformly across every pending node:
--
--   withSpˡ-splice : payload-level H ⊢
--     reifySp g (withSpˡ ρ sp f) ≈c
--     C ∘ ((reifySp h sp ⊗ 1) ∘ (mult ∘ permC ρ))
--
--   appSp-splice   : payload-level H ⊢
--     reifySp g (appSp Δ v sp) ≈c
--     C ∘ ((reifySp h sp ⊗ 1) ∘ mult)
--
-- Each spl-node case: IH (at pid, collapsed by pid-realC) →
-- node-perm-real → interchange slides the neutral past the multInv
-- dressing → n-α pulls it out of the reassociation → `mult-head²`
-- collapses the head dressing to `αr ⊗ 1` → `fuse4` reassembles the
-- node syntax INSIDE the left tensor factor. The usI cases are the
-- same skeleton landing on `mult-headI` (i.e. on K2C).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq10 where

open import normalizer.Syntax.Types
  using ( _≡_; refl; cong )
open import poc.OCP0009.NbEPMonL
  using ( CTy; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; ƛrc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘; cα-nat )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm; pnil; pcons; pid
        ; _⊙P_; padʳ; passoc )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv )
open import poc.OCP0009.NbEPMonF
  using ( Sp; ret; spl; usI; reifySp; withSpˡ; Val; appSp )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; fuse⊗ʳC )
open import poc.OCP0009.NbEPMonAdq2
  using ( interchangeC; ⊙P-realC; pid-realC )
open import poc.OCP0009.NbEPMonAdq8
  using ( ⊙P-pidˡ )
open import poc.OCP0009.NbEPMonAdq9
  using ( mult-head²; mult-headI; n-α; node-perm-real )

private
  permC-≡ : ∀ {xs ys} {p q : Perm xs ys} → p ≡ q → permC p ≈c permC q
  permC-≡ refl = ≈crefl

  -- Four left factors fuse into one.
  fuse4 : ∀ {W₀ W₁ W₂ W₃ W₄ E V}
            (a : CTm W₃ W₄) (b : CTm W₂ W₃) (c : CTm W₁ W₂)
            (d : CTm W₀ W₁) (v : CTm V (W₀ ⊗ E)) →
          ((a ⊗c idc {E}) ∘c
           ((b ⊗c idc) ∘c ((c ⊗c idc) ∘c ((d ⊗c idc) ∘c v)))) ≈c
          (((a ∘c (b ∘c (c ∘c d))) ⊗c idc) ∘c v)
  fuse4 a b c d v =
    ≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ fuse⊗ʳC)
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ fuse⊗ʳC)
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ fuse⊗ʳC)
             (∘c-congˡ (⊗c-cong
               (≈ctrans c∘-assoc c∘-assoc) ≈crefl)))))))

  -- The head-dressing collapse, with an abstract continuation Z.
  collapse² : ∀ {X Y Θ₂ Γ₂ V}
                (Z : CTm V (((X ⊗ Y) ⊗ ⟪ Θ₂ ⟫) ⊗ ⟪ Γ₂ ⟫)) →
              (mult (X ∷ (Y ∷ Θ₂)) Γ₂ ∘c
               (αrc ∘c ((idc {X ⊗ Y} ⊗c multInv Θ₂ Γ₂) ∘c
                        (αrc ∘c Z)))) ≈c
              ((αrc {X} {Y} {⟪ Θ₂ ⟫} ⊗c idc {⟪ Γ₂ ⟫}) ∘c Z)
  collapse² {X} {Y} {Θ₂} {Γ₂} Z =
    ≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (≈csym c∘-assoc)
             (∘c-congˡ (mult-head² X Y Θ₂ Γ₂))))

  collapseI : ∀ {Θ₂ Γ₂ V}
                (Z : CTm V ((I ⊗ ⟪ Θ₂ ⟫) ⊗ ⟪ Γ₂ ⟫)) →
              (mult Θ₂ Γ₂ ∘c
               (ƛrc ∘c ((idc {I} ⊗c multInv Θ₂ Γ₂) ∘c
                        (αrc ∘c Z)))) ≈c
              ((ƛrc {⟪ Θ₂ ⟫} ⊗c idc {⟪ Γ₂ ⟫}) ∘c Z)
  collapseI {Θ₂} {Γ₂} Z =
    ≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (≈csym c∘-assoc)
             (∘c-congˡ (mult-headI Θ₂ Γ₂))))

------------------------------------------------------------------------
-- withSpˡ, spliced.
------------------------------------------------------------------------

withSpˡ-splice :
  ∀ {P Q : Ctx → Set} {T S : CTy} {Γ₂}
    (g : ∀ {Δ} → Q Δ → CTm ⟪ Δ ⟫ T)
    (h : ∀ {Δ₁} → P Δ₁ → CTm ⟪ Δ₁ ⟫ S)
    (C : CTm (S ⊗ ⟪ Γ₂ ⟫) T) →
  ∀ {Γ Γ₁} (ρ : Perm Γ (Γ₁ ++ Γ₂)) (sp : Sp P Γ₁)
    (f : ∀ {Δ₁ Δ} → Perm Δ (Δ₁ ++ Γ₂) → P Δ₁ → Sp Q Δ) →
  (∀ {Δ₁ Δ} (ρ' : Perm Δ (Δ₁ ++ Γ₂)) (p : P Δ₁) →
     reifySp g (f ρ' p) ≈c
     (C ∘c ((h p ⊗c idc {⟪ Γ₂ ⟫}) ∘c (mult Δ₁ Γ₂ ∘c permC ρ')))) →
  reifySp g (withSpˡ ρ sp f) ≈c
  (C ∘c ((reifySp h sp ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ)))

withSpˡ-splice g h C ρ (ret p) f H = H ρ p

withSpˡ-splice {Γ₂ = Γ₂} g h C ρ (spl {X = X} {Y} {Θ₁} {Θ₂} ρ₁ n k) f H =
  ≈ctrans (∘c-congˡ (withSpˡ-splice g h C (pid _) k f H))
  (≈ctrans (∘c-congˡ (∘c-congʳ (∘c-congʳ
            (≈ctrans (∘c-congʳ (pid-realC _)) cid-r))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (node-perm-real Θ₁ Θ₂ Γ₂ ρ₁ ρ))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ n-α))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ (collapse² _)))
           (∘c-congʳ (fuse4 (reifySp h k) αrc (n ⊗c idc)
                            (mult Θ₁ Θ₂ ∘c permC ρ₁) _)))))))))))))

withSpˡ-splice {Γ₂ = Γ₂} g h C ρ (usI {Γ₁ = Θ₁} {Θ₂} ρ₁ n k) f H =
  ≈ctrans (∘c-congˡ (withSpˡ-splice g h C (pid _) k f H))
  (≈ctrans (∘c-congˡ (∘c-congʳ (∘c-congʳ
            (≈ctrans (∘c-congʳ (pid-realC _)) cid-r))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (node-perm-real Θ₁ Θ₂ Γ₂ ρ₁ ρ))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ n-α))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ (collapseI _)))
           (∘c-congʳ (fuse4 (reifySp h k) ƛrc (n ⊗c idc)
                            (mult Θ₁ Θ₂ ∘c permC ρ₁) _)))))))))))))

------------------------------------------------------------------------
-- appSp, spliced.
------------------------------------------------------------------------

appSp-splice :
  ∀ {A B} {T S : CTy}
    (g : ∀ {Δ'} → Val B Δ' → CTm ⟪ Δ' ⟫ T)
    (h : ∀ {Γ'} → Val (A ⊸ B) Γ' → CTm ⟪ Γ' ⟫ S)
    (Δ : Ctx) (v : Val A Δ) (C : CTm (S ⊗ ⟪ Δ ⟫) T) →
  (∀ {Γ'} (fv : Val (A ⊸ B) Γ') →
     g (fv Δ v) ≈c (C ∘c ((h fv ⊗c idc {⟪ Δ ⟫}) ∘c mult Γ' Δ))) →
  ∀ {Γ} (sp : Sp (Val (A ⊸ B)) Γ) →
  reifySp g (appSp Δ v sp) ≈c
  (C ∘c ((reifySp h sp ⊗c idc) ∘c mult Γ Δ))

appSp-splice g h Δ v C H (ret fv) = H fv

appSp-splice g h Δ v C H (spl {Γ₁ = Θ₁} {Θ₂} ρ n k) =
  ≈ctrans (∘c-congˡ (appSp-splice g h Δ v C H k))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (permC-≡ (cong (_⊙P passoc Θ₁ Θ₂ Δ)
                     (≈≡sym (⊙P-pidˡ (padʳ Δ ρ)))))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (node-perm-real Θ₁ Θ₂ Δ ρ (pid _)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (≈ctrans (∘c-congʳ (pid-realC _)) cid-r)))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ n-α))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ (collapse² _)))
           (∘c-congʳ (fuse4 (reifySp h k) αrc (n ⊗c idc)
                            (mult Θ₁ Θ₂ ∘c permC ρ) _))))))))))))))
  where
  ≈≡sym : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  ≈≡sym refl = refl

appSp-splice g h Δ v C H (usI {Γ₁ = Θ₁} {Θ₂} ρ n k) =
  ≈ctrans (∘c-congˡ (appSp-splice g h Δ v C H k))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (permC-≡ (cong (_⊙P passoc Θ₁ Θ₂ Δ)
                     (≈≡sym (⊙P-pidˡ (padʳ Δ ρ)))))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (node-perm-real Θ₁ Θ₂ Δ ρ (pid _)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (≈ctrans (∘c-congʳ (pid-realC _)) cid-r)))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ n-α))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ (collapseI _)))
           (∘c-congʳ (fuse4 (reifySp h k) ƛrc (n ⊗c idc)
                            (mult Θ₁ Θ₂ ∘c permC ρ) _))))))))))))))
  where
  ≈≡sym : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  ≈≡sym refl = refl
