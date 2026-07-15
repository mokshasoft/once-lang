------------------------------------------------------------------------
-- OCP-0009 · ADEQUACY stage A4.3 — REIFY REFLECTS, REFLECT RELATES
--
--   R-reify     : R A v t → reify A v ≈c t
--   R-reflectNe : R A (reflectNe A n) n
--   R-reflectTy : R A (reflectTy A) (joinTm A)
--
-- The mutual core of the fundamental lemma's boundary. The atom/unit
-- cases are clean tree inductions (hoist is the identity there); the
-- ⊗ case threads through `hoist` via the A3 splice lemmas; the ⊸
-- cases cross-reference (reify a function reflects its body at a fresh
-- reflected argument).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonAdq14 where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc; Λc; evc
        ; _≈c_; ≈crefl; ≈csym; ≈ctrans; ∘c-cong; ⊗c-cong; Λc-cong
        ; cid-l; cid-r; c∘-assoc; c⊗-id; c⊗-∘
        ; cƛ-nat; cρ-nat; ctriangle; cρ-iso₁; cρ-iso₂
        ; cα-iso₁; cƛ-iso₁; η⊸ )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; Perm; pnil; pcons; pid; pidR; _⊙P_; padʳ )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv; ctxOf; splitTm; joinTm )
open import poc.OCP0009.NbEPMonF
  using ( Sp; ret; spl; usI; AtCore; Core; Val
        ; reifySp; reify; emit; hoist; withSpˡ; withSpʳ
        ; reflectTy; reflectNe )
open import poc.OCP0009.NbEPMonAdq1
  using ( ∘c-congˡ; ∘c-congʳ; cancelC; fuse⊗ˡC; fuse⊗ʳC
        ; mult-inv-r; join-split )
open import poc.OCP0009.NbEPMonAdq2
  using ( pid-realC; interchangeC )
open import poc.OCP0009.NbEPMonAdq10
  using ( withSpˡ-splice )
open import poc.OCP0009.NbEPMonAdq11
  using ( withSpʳ-splice )
open import poc.OCP0009.NbEPMonAdq5
  using ( ƛρ-IC; tri-ρlC )
open import poc.OCP0009.NbEPMonAdq6
  using ( pidR-real )
open import poc.OCP0009.NbEPMonAdq12
  using ( R; RAt; RI; R⊗; R-resp )
open import poc.OCP0009.NbEPMonAdq13
  using ( R-vmap )

------------------------------------------------------------------------
-- Atom / unit reification: clean tree induction (hoist = id).
------------------------------------------------------------------------

private
  emitAt : ∀ {A Δ} → AtCore A Δ → CTm ⟪ Δ ⟫ A
  emitAt (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀

  -- ρl naturality, generic in the morphism.
  ρl-natG : ∀ {A B} (f : CTm A B) → ((f ⊗c idc {I}) ∘c ρlc) ≈c (ρlc ∘c f)
  ρl-natG f =
    ≈ctrans (∘c-congˡ
      (≈ctrans (≈csym cid-l)
      (≈ctrans (∘c-congˡ (≈csym cρ-iso₂))
      (≈ctrans c∘-assoc (∘c-congʳ cρ-nat)))))
    (≈ctrans c∘-assoc
    (≈ctrans (∘c-congʳ c∘-assoc)
    (≈ctrans (∘c-congʳ (∘c-congʳ cρ-iso₁))
             (∘c-congʳ cid-r))))

  -- αr ∘ ρl_{A⊗B} ≈ 1_A ⊗ ρl_B  (via the ρ-triangle tri-ρlC).
  αrc-ρlc : ∀ {A B} → (αrc {A} {B} {I} ∘c ρlc {A ⊗ B}) ≈c (idc {A} ⊗c ρlc {B})
  αrc-ρlc =
    ≈ctrans (∘c-congʳ (≈csym tri-ρlC))
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ cα-iso₁) cid-l))

  -- (ρr ⊗ 1) ∘ αl ≈ 1 ⊗ ƛr  (the triangle, rearranged).
  ρα-G : ∀ {A B} → ((ρrc {A} ⊗c idc {B}) ∘c αlc {A} {I} {B}) ≈c (idc ⊗c ƛrc {B})
  ρα-G =
    ≈ctrans (∘c-congˡ (≈csym ctriangle))
    (≈ctrans c∘-assoc (≈ctrans (∘c-congʳ cα-iso₁) cid-r))

  -- (ρr ⊗ 1) ∘ (αl ∘ (1 ⊗ ƛl)) ≈ id  (a unit round-trip).
  tailG : ∀ {A B} →
          ((ρrc {A} ⊗c idc {B}) ∘c (αlc ∘c (idc ⊗c ƛlc {B}))) ≈c idc
  tailG =
    ≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ ρα-G)
    (≈ctrans fuse⊗ˡC
    (≈ctrans (⊗c-cong ≈crefl cƛ-iso₁) c⊗-id)))


RAt-reify : ∀ {A Γ} (v : Sp (AtCore A) Γ) {t} →
            RAt v t → reifySp emitAt v ≈c t
RAt-reify (ret _) r = r
RAt-reify (spl ρ n k) (t' , (rk , e)) =
  ≈ctrans (∘c-congˡ (RAt-reify k rk)) (≈csym e)
RAt-reify (usI ρ n k) (t' , (rk , e)) =
  ≈ctrans (∘c-congˡ (RAt-reify k rk)) (≈csym e)

RI-reify : ∀ {Γ} (v : Sp (λ Δ → Δ ≡ ε) Γ) {t} →
           RI v t → reifySp (emit I) v ≈c t
RI-reify (ret refl) r = r
RI-reify (spl ρ n k) (t' , (rk , e)) =
  ≈ctrans (∘c-congˡ (RI-reify k rk)) (≈csym e)
RI-reify (usI ρ n k) (t' , (rk , e)) =
  ≈ctrans (∘c-congˡ (RI-reify k rk)) (≈csym e)

------------------------------------------------------------------------
-- The mutual boundary.
------------------------------------------------------------------------

mutual
  R-reify : ∀ A {Γ} {v : Val A Γ} {t} → R A v t → reify A v ≈c t
  R-reify ι₁      {v = v} r = RAt-reify v r
  R-reify ι₂      {v = v} r = RAt-reify v r
  R-reify I       {v = v} r = RI-reify v r
  R-reify (A ⊗ B) {v = v} r = R⊗-reify v r
  R-reify (A ⊸ B) {Γ} {v = f} {t} rf =
    r⊸ (R-reify B (rf (reflectTy A) (joinTm A) (R-reflectTy A)))
    where
    -- reify (A⊸B) f = Λc (reify B (f (ctxOf A) (reflectTy A)) ∘c
    --                     (multInv Γ (ctxOf A) ∘c (idc ⊗c splitTm A)))
    -- and R gives reify B (f _ _) ≈c evc ∘c ((t ⊗ joinTm A) ∘c mult _ _).
    r⊸ : (reify B (f (ctxOf A) (reflectTy A)) ≈c
          (evc ∘c ((t ⊗c joinTm A) ∘c mult Γ (ctxOf A)))) →
         reify (A ⊸ B) f ≈c t
    r⊸ e =
      ≈ctrans (Λc-cong (∘c-congˡ e))
      (≈ctrans (Λc-cong iSimp) η⊸)
      where
      iSimp :
        ((evc ∘c ((t ⊗c joinTm A) ∘c mult Γ (ctxOf A))) ∘c
         (multInv Γ (ctxOf A) ∘c (idc ⊗c splitTm A))) ≈c
        (evc ∘c (t ⊗c idc))
      iSimp =
        ≈ctrans c∘-assoc
        (∘c-congʳ (≈ctrans c∘-assoc
          (≈ctrans (∘c-congʳ (≈ctrans (≈csym c∘-assoc)
                    (≈ctrans (∘c-congˡ (mult-inv-r Γ (ctxOf A))) cid-l)))
                   (≈ctrans (≈csym c⊗-∘)
                            (⊗c-cong cid-r (join-split A))))))

  -- hoist threads through spl/usI DEFINITIONALLY (bindSp (spl ρ n k) K
  -- = spl ρ n (bindSp k K)), so those cases are clean recursion — only
  -- the ret leaf needs the A3 hoist-splice lemmas.
  R⊗-reify : ∀ {A B Γ} (v : Val (A ⊗ B) Γ) {t} →
             R⊗ A B v t → reify (A ⊗ B) v ≈c t
  R⊗-reify {A} {B} (ret (Δ₁ , (Δ₂ , (ρ , (va , vb)))))
           (ta , (tb , (ra , (rb , e)))) =
    ≈ctrans
      (≈ctrans
        (withSpˡ-splice (emit (A ⊗ B)) (emit A) (idc ⊗c reify B vb)
           ρ (hoist A va)
           (λ ρ' ca → withSpʳ ρ' (hoist B vb)
                        (λ ρ'' cb → ret (_ , (_ , (ρ'' , (ca , cb))))))
           Hˡ)
        (≈ctrans (≈csym c∘-assoc)
        (≈ctrans (∘c-congˡ (≈ctrans (≈csym c⊗-∘) (⊗c-cong cid-l cid-r)))
                 (∘c-congˡ (⊗c-cong (R-reify A ra) (R-reify B rb))))))
      (≈csym e)
    where
    Hʳ : ∀ {Δ₁'} (ca : Core A Δ₁') {Δ₂''} {Δ'}
           (ρ'' : Perm Δ' (Δ₁' ++ Δ₂'')) (cb : Core B Δ₂'') →
         reifySp (emit (A ⊗ B)) (ret (Δ₁' , (Δ₂'' , (ρ'' , (ca , cb)))))
         ≈c ((emit A ca ⊗c idc) ∘c
             ((idc ⊗c emit B cb) ∘c (mult Δ₁' Δ₂'' ∘c permC ρ'')))
    Hʳ ca ρ'' cb =
      ≈csym
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ (≈ctrans (≈csym c⊗-∘) (⊗c-cong cid-r cid-l)))
               (≈csym c∘-assoc)))
    Hˡ : ∀ {Δ₁'} {Δ} (ρ' : Perm Δ (Δ₁' ++ Δ₂)) (ca : Core A Δ₁') →
         reifySp (emit (A ⊗ B))
           (withSpʳ ρ' (hoist B vb)
             (λ ρ'' cb → ret (_ , (_ , (ρ'' , (ca , cb))))))
         ≈c ((idc ⊗c reify B vb) ∘c
             ((emit A ca ⊗c idc) ∘c (mult Δ₁' Δ₂ ∘c permC ρ')))
    Hˡ ρ' ca =
      ≈ctrans (withSpʳ-splice (emit (A ⊗ B)) (emit B) (emit A ca ⊗c idc)
                 ρ' (hoist B vb)
                 (λ ρ'' cb → ret (_ , (_ , (ρ'' , (ca , cb)))))
                 (Hʳ ca))
      (≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ interchangeC) c∘-assoc))
  R⊗-reify (spl ρ n k) (t' , (rk , e)) =
    ≈ctrans (∘c-congˡ (R⊗-reify k rk)) (≈csym e)
  R⊗-reify (usI ρ n k) (t' , (rk , e)) =
    ≈ctrans (∘c-congˡ (R⊗-reify k rk)) (≈csym e)

  R-reflectNe : ∀ A {Γ} (n : CTm ⟪ Γ ⟫ A) → R A (reflectNe A n) n
  R-reflectNe ι₁ {Γ} n = ≈ctrans (∘c-congʳ (pid-realC Γ)) cid-r
  R-reflectNe ι₂ {Γ} n = ≈ctrans (∘c-congʳ (pid-realC Γ)) cid-r
  R-reflectNe I  {Γ} n = idc , (≈crefl ,
    ≈csym
    (≈ctrans cid-l
    (≈ctrans (∘c-congʳ (∘c-congʳ (pidR-real Γ)))
    (≈ctrans (∘c-congʳ ρl-nat)
    (≈ctrans (≈csym c∘-assoc)
    (≈ctrans (∘c-congˡ (∘c-congˡ ƛρ-IC))
    (≈ctrans (∘c-congˡ cρ-iso₁) cid-l)))))))
    where
    ρl-nat : ((n ⊗c idc {I}) ∘c ρlc) ≈c (ρlc ∘c n)
    ρl-nat =
      ≈ctrans (∘c-congˡ
        (≈ctrans (≈csym cid-l)
        (≈ctrans (∘c-congˡ (≈csym cρ-iso₂))
        (≈ctrans c∘-assoc (∘c-congʳ cρ-nat)))))
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ c∘-assoc)
      (≈ctrans (∘c-congʳ (∘c-congʳ cρ-iso₁))
               (∘c-congʳ cid-r))))
  R-reflectNe (X ⊗ Y) {Γ} n =
    _ , ((ρrc , (ρrc ,
      (R-reflectNe X ρrc , (R-reflectNe Y ρrc , ≈crefl)))) ,
      ≈csym (≈ctrans (∘c-congˡ leftEq)
             (≈ctrans (∘c-congʳ dressEq) combine)))
    where
    ρrr-split : (ρrc {X} ⊗c ρrc {Y}) ≈c ((idc ⊗c ρrc) ∘c (ρrc ⊗c idc))
    ρrr-split = ≈csym (≈ctrans (≈csym c⊗-∘) (⊗c-cong cid-l cid-r))
    leftEq :
      ((ρrc ⊗c ρrc) ∘c
       (mult (X ∷ ε) (Y ∷ ε) ∘c permC (pid (X ∷ (Y ∷ ε))))) ≈c
      (idc {X} ⊗c ρrc {Y})
    leftEq =
      ≈ctrans (∘c-congʳ (∘c-congʳ (pid-realC (X ∷ (Y ∷ ε)))))
      (≈ctrans (∘c-congʳ cid-r)
      (≈ctrans (∘c-congˡ ρrr-split)
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ tailG) cid-r))))
    dressEq :
      (αrc ∘c ((n ⊗c idc) ∘c (mult Γ ε ∘c permC (pidR Γ)))) ≈c
      ((idc {X} ⊗c ρlc {Y}) ∘c n)
    dressEq =
      ≈ctrans (∘c-congʳ (∘c-congʳ (pidR-real Γ)))
      (≈ctrans (∘c-congʳ (ρl-natG n))
      (≈ctrans (≈csym c∘-assoc)
               (∘c-congˡ αrc-ρlc)))
    combine :
      ((idc {X} ⊗c ρrc {Y}) ∘c ((idc ⊗c ρlc) ∘c n)) ≈c n
    combine =
      ≈ctrans (≈csym c∘-assoc)
      (≈ctrans (∘c-congˡ fuse⊗ˡC)
      (≈ctrans (∘c-congˡ (⊗c-cong ≈crefl cρ-iso₁))
      (≈ctrans (∘c-congˡ c⊗-id) cid-l)))
  R-reflectNe (A ⊸ B) {Γ} n {Δ} w s rws =
    R-resp B (R-reflectNe B ((evc ∘c (n ⊗c reify A w)) ∘c mult Γ Δ))
             (≈ctrans c∘-assoc
               (∘c-congʳ (∘c-congˡ (⊗c-cong ≈crefl (R-reify A rws)))))

  R-reflectTy : ∀ A → R A (reflectTy A) (joinTm A)
  R-reflectTy ι₁ = ≈ctrans (∘c-congʳ (pid-realC (ι₁ ∷ ε))) cid-r
  R-reflectTy ι₂ = ≈ctrans (∘c-congʳ (pid-realC (ι₂ ∷ ε))) cid-r
  R-reflectTy I  = ≈crefl
  R-reflectTy (A ⊗ B) =
    joinTm A , (joinTm B , (R-reflectTy A , (R-reflectTy B ,
      ≈csym (∘c-congʳ (≈ctrans (∘c-congʳ (pid-realC _)) cid-r)))))
  R-reflectTy (A ⊸ B) {Δ} w s rws =
    R-resp B (R-reflectNe B (evc ∘c (idc ⊗c reify A w)))
             (∘c-congʳ termInner)
    where
    ρs-split : (ρrc {A ⊸ B} ⊗c s) ≈c ((idc ⊗c s) ∘c (ρrc ⊗c idc {⟪ Δ ⟫}))
    ρs-split = ≈csym (≈ctrans (≈csym c⊗-∘) (⊗c-cong cid-l cid-r))
    termInner :
      (idc ⊗c reify A w) ≈c ((ρrc ⊗c s) ∘c (αlc ∘c (idc ⊗c ƛlc)))
    termInner =
      ≈csym
      (≈ctrans (∘c-congˡ ρs-split)
      (≈ctrans c∘-assoc
      (≈ctrans (∘c-congʳ tailG)
      (≈ctrans cid-r
               (⊗c-cong ≈crefl (≈csym (R-reify A rws)))))))
