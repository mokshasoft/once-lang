------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A3b.4 — withSpʳ SPLICED: A3 CLOSED
--
-- The right-pull is the deepest traversal: its nodes carry the block
-- exchange, its continuations the two-head carry. Both realize into
-- head transpositions —
--
--   * `carry²-real` : mult ∘ permC (carry²) ≈ ŝ_X ∘ (1⊗ŝ_Y) ∘ (1⊗1⊗mult)
--     (two `mult-insˡ`-at-`here` steps)
--   * `exch-real`   : mult ∘ permC (exch) ≈
--       (1 ⊗ multInv) ∘ ŝ_{block} ∘ (1 ⊗ mult) ∘ mult
--     — THE EXCHANGE REALIZES AS THE HEAD TRANSPOSITION OF BLOCKS:
--     after ⊙P-realC + passoc-real + padʳ-real + bswapW-real +
--     passocInv-real, the α∘(σ⊗1)∘α residue IS `swapHeadC`, verbatim.
--
-- and then cancel: in `withSpʳ-splice`'s spl-case, K5′C splits the
-- block transposition into per-head ones, which annihilate carry²'s
-- two swaps by `swapHeadC-invol` (the `dance` lemma). The usI-case
-- lands exactly on K4C. With this, EVERY split-monad combinator the
-- model uses has its splice law: A3 IS CLOSED.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq11 where

open import poc.OCP0009.NbEPMonL
  using ( CTy; I; _⊗_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; σc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘; cα-nat; cƛ-nat )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_
        ; Ins; here; there; Perm; pnil; pcons; pid
        ; _⊙P_; insˡ; padˡ; padʳ; bswapW
        ; passoc; passocInv; exch; carry² )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; swapHeadC; insC; permC; mult; multInv )
open import poc.OCP0009.NbEPMonF
  using ( Sp; ret; spl; usI; reifySp; withSpʳ )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; fuse⊗ˡC; fuse⊗ʳC
        ; mult-inv-l; mult-inv-r )
open import poc.OCP0009.NbEPMonAdq2
  using ( swapHeadC-nat; swapHeadC-invol; interchangeC
        ; ⊙P-realC; pid-realC )
open import poc.OCP0009.NbEPMonAdq3
  using ( padˡ-real; padʳ-real )
open import poc.OCP0009.NbEPMonAdq4
  using ( K4C; K5′C )
open import poc.OCP0009.NbEPMonAdq6
  using ( mult-insˡ; bswapW-real )
open import poc.OCP0009.NbEPMonAdq8
  using ( passoc-real; passocInv-real )

------------------------------------------------------------------------
-- carry², realized: two mult-insˡ steps.
------------------------------------------------------------------------

private
  -- mult past a single here-insertion under a prefix.
  step : ∀ Γ₁ {x xs} →
         (mult Γ₁ (x ∷ xs) ∘c insC (insˡ Γ₁ (here {x} {xs}))) ≈c
         (swapHeadC {x} {⟪ Γ₁ ⟫} {⟪ xs ⟫} ∘c (idc {x} ⊗c mult Γ₁ xs))
  step Γ₁ =
    ≈ctrans (mult-insˡ Γ₁ here)
    (≈ctrans (∘c-congˡ c⊗-id) cid-l)

carry²-real : ∀ {X Y} Γ₁ Θ₂ →
  (mult Γ₁ (X ∷ (Y ∷ Θ₂)) ∘c permC (carry² {X} {Y} Γ₁ Θ₂)) ≈c
  (swapHeadC {X} {⟪ Γ₁ ⟫} {Y ⊗ ⟪ Θ₂ ⟫} ∘c
   ((idc {X} ⊗c swapHeadC {Y} {⟪ Γ₁ ⟫} {⟪ Θ₂ ⟫}) ∘c
    (idc {X} ⊗c (idc {Y} ⊗c mult Γ₁ Θ₂))))
carry²-real {X} {Y} Γ₁ Θ₂ =
  ≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (step Γ₁))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ fuse⊗ˡC)
  (≈ctrans (∘c-congʳ (⊗c-cong ≈crefl inner))
           (∘c-congʳ (≈csym fuse⊗ˡC))))))
  where
  inner : (mult Γ₁ (Y ∷ Θ₂) ∘c
           (insC (insˡ Γ₁ (here {Y} {Θ₂})) ∘c
            (idc {Y} ⊗c permC (pid (Γ₁ ++ Θ₂))))) ≈c
          (swapHeadC {Y} {⟪ Γ₁ ⟫} {⟪ Θ₂ ⟫} ∘c (idc {Y} ⊗c mult Γ₁ Θ₂))
  inner =
    ≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ (step Γ₁))
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ fuse⊗ˡC)
             (∘c-congʳ (⊗c-cong ≈crefl
               (≈ctrans (∘c-congʳ (pid-realC (Γ₁ ++ Θ₂))) cid-r))))))

------------------------------------------------------------------------
-- exch, realized: the head transposition of blocks.
------------------------------------------------------------------------

exch-real : ∀ Γ₁ Θ₁ Θ₂ →
  (mult Θ₁ (Γ₁ ++ Θ₂) ∘c permC (exch Γ₁ Θ₁ Θ₂)) ≈c
  ((idc {⟪ Θ₁ ⟫} ⊗c multInv Γ₁ Θ₂) ∘c
   (swapHeadC {⟪ Γ₁ ⟫} {⟪ Θ₁ ⟫} {⟪ Θ₂ ⟫} ∘c
    ((idc {⟪ Γ₁ ⟫} ⊗c mult Θ₁ Θ₂) ∘c mult Γ₁ (Θ₁ ++ Θ₂))))
exch-real Γ₁ Θ₁ Θ₂ =
  ≈ctrans (∘c-congʳ (⊙P-realC
            (passocInv Γ₁ Θ₁ Θ₂ ⊙P padʳ Θ₂ (bswapW Γ₁ Θ₁))
            (passoc Θ₁ Γ₁ Θ₂)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (⊙P-realC (passocInv Γ₁ Θ₁ Θ₂)
                                (padʳ Θ₂ (bswapW Γ₁ Θ₁)))))
  (≈ctrans (≈csym c∘-assoc)
  (≈ctrans (∘c-congˡ (passoc-real Θ₁ Γ₁ Θ₂))
  (≈ctrans c∘-assoc
  (≈ctrans (∘c-congʳ c∘-assoc)
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
            (padʳ-real Θ₂ (bswapW Γ₁ Θ₁))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (passocInv-real Γ₁ Θ₁ Θ₂)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ fuse⊗ʳC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ (⊗c-cong
            (bswapW-real Γ₁ Θ₁) ≈crefl))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ fuse⊗ʳC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ (⊗c-cong σm-cancel ≈crefl))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
           (∘c-congʳ (≈csym c∘-assoc)))))))))))))))))))
  where
  σm-cancel : ((σc {⟪ Γ₁ ⟫} {⟪ Θ₁ ⟫} ∘c mult Γ₁ Θ₁) ∘c multInv Γ₁ Θ₁)
              ≈c σc
  σm-cancel =
    ≈ctrans c∘-assoc (≈ctrans (∘c-congʳ (mult-inv-r Γ₁ Θ₁)) cid-r)

------------------------------------------------------------------------
-- The transposition dance: carry²'s swaps annihilate the block swap.
------------------------------------------------------------------------

private
  hα : ∀ {X Y W W'} {h : CTm W W'} →
       ((idc {X} ⊗c (idc {Y} ⊗c h)) ∘c αrc {X} {Y} {W}) ≈c
       (αrc {X} {Y} {W'} ∘c (idc {X ⊗ Y} ⊗c h))
  hα = ≈ctrans (≈csym cα-nat) (∘c-congʳ (⊗c-cong c⊗-id ≈crefl))

  n-ŝ : ∀ {T Z G S} {n : CTm T Z} →
        ((n ⊗c idc {G ⊗ S}) ∘c swapHeadC {G} {T} {S}) ≈c
        (swapHeadC {G} {Z} {S} ∘c (idc {G} ⊗c (n ⊗c idc {S})))
  n-ŝ = ≈csym (≈ctrans swapHeadC-nat
              (∘c-congˡ (⊗c-cong ≈crefl c⊗-id)))

  dance : ∀ {X Y Γ₁ Θ₂ V}
            (Z : CTm V (⟪ Γ₁ ⟫ ⊗ ((X ⊗ Y) ⊗ ⟪ Θ₂ ⟫))) →
          ((swapHeadC {X} {⟪ Γ₁ ⟫} {Y ⊗ ⟪ Θ₂ ⟫} ∘c
            ((idc {X} ⊗c swapHeadC {Y} {⟪ Γ₁ ⟫} {⟪ Θ₂ ⟫}) ∘c
             (idc {X} ⊗c (idc {Y} ⊗c mult Γ₁ Θ₂)))) ∘c
           (αrc {X} {Y} {⟪ Γ₁ ++ Θ₂ ⟫} ∘c
            ((idc {X ⊗ Y} ⊗c multInv Γ₁ Θ₂) ∘c
             (swapHeadC {⟪ Γ₁ ⟫} {X ⊗ Y} {⟪ Θ₂ ⟫} ∘c Z)))) ≈c
          ((idc {⟪ Γ₁ ⟫} ⊗c αrc {X} {Y} {⟪ Θ₂ ⟫}) ∘c Z)
  dance {X} {Y} {Γ₁} {Θ₂} Z =
    ≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ hα)))
    (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
              (≈ctrans fuse⊗ˡC
              (≈ctrans (⊗c-cong ≈crefl (mult-inv-r Γ₁ Θ₂)) c⊗-id))))))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ cid-l)))
    (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
    (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ K5′C)))
    (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
    (≈ctrans (∘c-congʳ (∘c-congˡ (≈csym c∘-assoc)))
    (≈ctrans (∘c-congʳ (∘c-congˡ (∘c-congˡ
              (≈ctrans fuse⊗ˡC
              (≈ctrans (⊗c-cong ≈crefl swapHeadC-invol) c⊗-id)))))
    (≈ctrans (∘c-congʳ (∘c-congˡ cid-l))
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ swapHeadC-invol)
             cid-l))))))))))))))))

------------------------------------------------------------------------
-- withSpʳ, spliced. A3 closes here.
------------------------------------------------------------------------

withSpʳ-splice :
  ∀ {P Q : Ctx → Set} {T S : CTy} {Γ₁}
    (g : ∀ {Δ} → Q Δ → CTm ⟪ Δ ⟫ T)
    (h : ∀ {Δ₂} → P Δ₂ → CTm ⟪ Δ₂ ⟫ S)
    (C : CTm (⟪ Γ₁ ⟫ ⊗ S) T) →
  ∀ {Γ Γ₂} (ρ : Perm Γ (Γ₁ ++ Γ₂)) (sp : Sp P Γ₂)
    (f : ∀ {Δ₂ Δ} → Perm Δ (Γ₁ ++ Δ₂) → P Δ₂ → Sp Q Δ) →
  (∀ {Δ₂ Δ} (ρ' : Perm Δ (Γ₁ ++ Δ₂)) (p : P Δ₂) →
     reifySp g (f ρ' p) ≈c
     (C ∘c ((idc {⟪ Γ₁ ⟫} ⊗c h p) ∘c (mult Γ₁ Δ₂ ∘c permC ρ')))) →
  reifySp g (withSpʳ ρ sp f) ≈c
  (C ∘c ((idc ⊗c reifySp h sp) ∘c (mult Γ₁ Γ₂ ∘c permC ρ)))

withSpʳ-splice g h C ρ (ret p) f H = H ρ p

withSpʳ-splice {Γ₁ = Γ₁} g h C ρ (spl {X = X} {Y} {Θ₁} {Θ₂} ρ₂ n k) f H =
  ≈ctrans (∘c-congˡ (withSpʳ-splice g h C (carry² Γ₁ Θ₂) k f H))
  (≈ctrans (∘c-congˡ (∘c-congʳ (∘c-congʳ (carry²-real Γ₁ Θ₂))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (⊙P-realC ρ (padˡ Γ₁ ρ₂ ⊙P exch Γ₁ Θ₁ Θ₂))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
            (⊙P-realC (padˡ Γ₁ ρ₂) (exch Γ₁ Θ₁ Θ₂)))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
            (exch-real Γ₁ Θ₁ Θ₂)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            c∘-assoc)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (∘c-congʳ (≈csym c∘-assoc)))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (∘c-congʳ (∘c-congˡ (padˡ-real Γ₁ ρ₂))))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (∘c-congʳ c∘-assoc))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (≈csym c∘-assoc))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (∘c-congˡ fuse⊗ˡC))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ n-ŝ))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (≈csym c∘-assoc)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
            fuse⊗ˡC)))))
  finish))))))))))))))))))))))
  where
  finish =
    ≈ctrans c∘-assoc
    (∘c-congʳ
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ (dance _))
      (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
      (≈ctrans (∘c-congʳ (∘c-congˡ fuse⊗ˡC))
      (≈ctrans (≈csym c∘-assoc)
               (∘c-congˡ fuse⊗ˡC)))))))

withSpʳ-splice {Γ₁ = Γ₁} g h C ρ (usI {Γ₁ = Θ₁} {Θ₂} ρ₂ n k) f H =
  ≈ctrans (∘c-congˡ (withSpʳ-splice g h C (pid (Γ₁ ++ Θ₂)) k f H))
  (≈ctrans (∘c-congˡ (∘c-congʳ (∘c-congʳ
            (≈ctrans (∘c-congʳ (pid-realC (Γ₁ ++ Θ₂))) cid-r))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (⊙P-realC ρ (padˡ Γ₁ ρ₂ ⊙P exch Γ₁ Θ₁ Θ₂))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
            (⊙P-realC (padˡ Γ₁ ρ₂) (exch Γ₁ Θ₁ Θ₂)))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
            (exch-real Γ₁ Θ₁ Θ₂)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            c∘-assoc)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (∘c-congʳ (≈csym c∘-assoc)))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (∘c-congʳ (∘c-congˡ (padˡ-real Γ₁ ρ₂))))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (∘c-congʳ c∘-assoc))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (≈csym c∘-assoc))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (∘c-congˡ fuse⊗ˡC))))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congˡ interchangeC)))
  (≈ctrans (∘c-congʳ (∘c-congʳ c∘-assoc))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (≈csym c∘-assoc))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ n-ŝ))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ c∘-assoc)))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ
            (≈csym c∘-assoc)))))
  (≈ctrans (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congʳ (∘c-congˡ
            fuse⊗ˡC)))))
  finishI))))))))))))))))))))))
  where
  dressEq :
    (ƛrc ∘c ((idc {I} ⊗c multInv Γ₁ Θ₂) ∘c
             (swapHeadC {⟪ Γ₁ ⟫} {I} {⟪ Θ₂ ⟫} ∘c
              ((idc {⟪ Γ₁ ⟫} ⊗c ((n ⊗c idc) ∘c (mult Θ₁ Θ₂ ∘c permC ρ₂))) ∘c
               (mult Γ₁ _ ∘c permC ρ))))) ≈c
    (multInv Γ₁ Θ₂ ∘c
     ((idc {⟪ Γ₁ ⟫} ⊗c ƛrc {⟪ Θ₂ ⟫}) ∘c
      ((idc ⊗c ((n ⊗c idc) ∘c (mult Θ₁ Θ₂ ∘c permC ρ₂))) ∘c
       (mult Γ₁ _ ∘c permC ρ))))
  dressEq =
    ≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ cƛ-nat)
    (≈ctrans c∘-assoc
             (∘c-congʳ (≈ctrans (≈csym c∘-assoc) (∘c-congˡ K4C)))))

  finishI =
    ≈ctrans c∘-assoc
    (∘c-congʳ
      (≈ctrans (∘c-congʳ dressEq)
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ (≈csym c∘-assoc))
      (≈ctrans (∘c-congʳ (∘c-congˡ (mult-inv-r Γ₁ Θ₂)))
      (≈ctrans (∘c-congʳ cid-l)
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ fuse⊗ˡC)
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ fuse⊗ˡC)
               (∘c-congˡ (⊗c-cong ≈crefl c∘-assoc))))))))))))