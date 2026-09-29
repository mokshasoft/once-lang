------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ THE GENERIC TRAVERSAL COMPUTES (PLAN-FAITHFUL F1).
--
--   trav s d (conₗ k p) e f  ⟶*  conₗ k (tpayT sh p e f d)      a fields row
--   trav s d (conₗ k p) e f  ⟶*  NODE e (f (fst p))              the variable row
--
-- where `tpayT` rebuilds the payload with every recursive field the CHILD'S
-- OWN TRAVERSAL (at its depth, the environment lifted under its binders).
-- Agreement over the traversal (PLAN-RENAMING §16.2's lesson: a library
-- that computes methods but ships no reduction lemmas makes every agreement
-- over it unprovable) starts here.
--
-- ★ Generic in the signature; it ASSUMES only that the kit's `LIFT` and
--   `NODE` are closed (both `refl` at a concrete signature).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.SynTravRed where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-appˡ; ⟶*-appʳ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd; ⟶*-con; ⟶*-ielimⁱ; ⟶*-dihᶜ; ⟶*-dihᵖ )
open import DirectedHoTT.Metatheory.TySub using ( wk-cancel-tm )
open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; Nth; nth-z; nth-s; tag; conₗ; selF; selF-β; nth-sub; subC )
open import DirectedHoTT.Lib.Tel using ( nth-⌜⌝; ⌜_⌝ₛ; ⌜_⌝ᵗ )
open import DirectedHoTT.Lib.TelAt using ( nth-⌜⌝ₛₛ )
open import DirectedHoTT.Lib.Sorted using ( ιₛ-red; fibₛ-β )
open import DirectedHoTT.Lib.Syn
open import DirectedHoTT.Lib.SynView using ( DihV; dihV-red )
open import DirectedHoTT.Lib.SynTrav
open import DirectedHoTT.Lib.SynTravM
open import DirectedHoTT.Lib.MethAt using ( methAt )
open import DirectedHoTT.Lib.NatFib using ( methN; methN-sub; ιN-s )
open import DirectedHoTT.Lib.FinFam using ( FinD; ffz; ffs )
open import DirectedHoTT.Lib.Wk using ( sub-w⁴; sub-w³ )
open import DirectedHoTT.Lib.MethAt using ( methAt-β; methAt-sub )
open import DirectedHoTT.Spec.Syntax using ( cong₃; cong₄ )

private
  variable
    Γ Δ Θ : Cx
    n : ℕ

------------------------------------------------------------------------
-- 0. FOUR β AT ONCE: a method's four binders instantiated.
------------------------------------------------------------------------

σ4 : RTm Γ → RTm Γ → RTm Γ → RTm Γ → Sub ((((Γ ∙) ∙) ∙) ∙) Γ
σ4 a b c d vz                   = d
σ4 a b c d (vs vz)              = c
σ4 a b c d (vs (vs vz))         = b
σ4 a b c d (vs (vs (vs vz)))    = a
σ4 a b c d (vs (vs (vs (vs x)))) = var x

private
  -- two, three binders' weakening cancelled by the instantiations
  c2 : (c d t : RTm Γ) → subTm (single d) (subTm (extS (single c)) (renTm vs (renTm vs t))) ≡ t
  c2 c d t = trans (cong (subTm (single d)) (trans (wkS (single c) (renTm vs t)) (cong (renTm vs) (wk-cancel-tm c t))))
                   (wk-cancel-tm d t)

  c3 : (b c d t : RTm Γ) →
       subTm (single d) (subTm (extS (single c)) (subTm (extS (extS (single b))) (renTm vs (renTm vs (renTm vs t))))) ≡ t
  c3 b c d t =
    trans (cong (λ z → subTm (single d) (subTm (extS (single c)) z))
                (trans (wkS (extS (single b)) (renTm vs (renTm vs t)))
                       (cong (renTm vs) (trans (wkS (single b) (renTm vs t)) (cong (renTm vs) (wk-cancel-tm b t))))))
          (c2 c d t)

  pt4 : (a b c d : RTm Γ) (x : Var ((((Γ ∙) ∙) ∙) ∙)) →
        subTm (single d) (subTm (extS (single c)) (subTm (extS (extS (single b))) (extS (extS (extS (single a))) x)))
        ≡ σ4 a b c d x
  pt4 a b c d vz                    = refl
  pt4 a b c d (vs vz)               = wk-cancel-tm d c
  pt4 a b c d (vs (vs vz))          = c2 c d b
  pt4 a b c d (vs (vs (vs vz)))     = c3 b c d a
  pt4 a b c d (vs (vs (vs (vs x)))) = refl

β4 : (X : RTm ((((Γ ∙) ∙) ∙) ∙)) (a b c d : RTm Γ) →
     app (app (app (app (lam (lam (lam (lam X)))) a) b) c) d ⟶* subTm (σ4 a b c d) X
β4 X a b c d =
  step (ξ-appˡ (ξ-appˡ (ξ-appˡ (β (lam (lam (lam X))) a))))
  (step (ξ-appˡ (ξ-appˡ (β _ b)))
  (step (ξ-appˡ (β _ c))
  (step (β _ d)
    (subst (λ z → z ⟶* subTm (σ4 a b c d) X) (sym eq) done))))
  where
    eq : subTm (single d) (subTm (extS (single c)) (subTm (extS (extS (single b))) (subTm (extS (extS (extS (single a)))) X)))
         ≡ subTm (σ4 a b c d) X
    eq = trans (cong (λ z → subTm (single d) (subTm (extS (single c)) z)) (subTm-subTm X))
         (trans (cong (subTm (single d)) (subTm-subTm X))
         (trans (subTm-subTm X) (subTm-cong (pt4 a b c d) X)))

------------------------------------------------------------------------
-- 1. THE TRAVERSAL, at a node.
------------------------------------------------------------------------

module TravRed {sg : Sig n} (ok : SigOK n sg) (κ : Kit n sg) (vok : VarsAt sg (Kit.vsort κ))
               (LIFT-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (Trav.LIFT ok κ {Δ}) ≡ Trav.LIFT ok κ)
               (NODE-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (Kit.NODE κ {Δ}) ≡ Kit.NODE κ) where
  open Kit κ using ( NODE )
  open Trav ok κ
  open TravM ok κ vok

  LIFTS-sub : (σ : Sub Δ Θ) (k : ℕ) (e d f : RTm Δ) → subTm σ (LIFTS k e d f) ≡ LIFTS k (subTm σ e) (subTm σ d) (subTm σ f)
  LIFTS-sub σ zero    e d f = refl
  LIFTS-sub σ (suc k) e d f =
    cong₄ (λ L a b c → app (app (app L a) b) c) (LIFT-sub σ) (nsucs-sub σ k e) (nsucs-sub σ k d) (LIFTS-sub σ k e d f)

  tpay-sub : (σ : Sub Δ Θ) (sh : Shape) (p h e f d : RTm Δ) →
             subTm σ (tpay sh p h e f d) ≡ tpay sh (subTm σ p) (subTm σ h) (subTm σ e) (subTm σ f) (subTm σ d)
  tpay-sub σ []ʰ             p h e f d = refl
  tpay-sub σ (rec s k ∷ʰ sh) p h e f d =
    cong₃ (λ a b c → pair (app (app (fst (subTm σ h)) a) b) c)
          (nsucs-sub σ k e) (LIFTS-sub σ k e d f) (tpay-sub σ sh (snd p) (snd h) e f d)
  tpay-sub σ (nat ∷ʰ sh)     p h e f d = cong (pair (fst (subTm σ p))) (tpay-sub σ sh (snd p) h e f d)
  tpay-sub σ vʰ              p h e f d = refl

  conₗ-sub : (σ : Sub Δ Θ) (k : ℕ) (q : RTm Δ) → subTm σ (conₗ k q) ≡ conₗ k (subTm σ q)
  conₗ-sub σ k q = cong (λ t → con (pair t (subTm σ q))) (tag-sub σ k)

  -- the lookups `ιₛ-red` needs
  nth-sortMs : {c s : ℕ} {shs : Shapes c} → NthG sg s shs → Nth (sortMs {Γ = Γ} sg) s (lam (methAt (mTs shs zero)))
  nth-sortMs = go
    where
      go : {m c s : ℕ} {sg' : Sig m} {shs : Shapes c} → NthG sg' s shs → Nth (sortMs {Γ = Γ} sg') s (lam (methAt (mTs shs zero)))
      go nthᵍ-z      = nth-z
      go (nthᵍ-s nt) = nth-s (go nt)

  nth-mTs : {c k₀ k : ℕ} {shs : Shapes c} {sh : Shape} → NthSh shs k sh → Nth (mTs {Γ = Γ} shs k₀) k (mT sh (k +' k₀))
  nth-mTs nthʰ-z      = nth-z
  nth-mTs (nthʰ-s nt) = nth-s (nth-mTs nt)

  -- ★ what one node becomes: the payload rebuilt, or the variable's value's node
  node : Shape → ℕ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  node []ʰ         k p h e f d = conₗ k (tpay []ʰ p h e f d)
  node (fl ∷ʰ sh)  k p h e f d = conₗ k (tpay (fl ∷ʰ sh) p h e f d)
  node vʰ          k p h e f d = app (app NODE e) (app f (fst p))

  private
    -- the index binder of the sort's method, cancelled
    c4 : (a b c d t : RTm Γ) → subTm (σ4 a b c d) (renTm vs (renTm vs (renTm vs (renTm vs t)))) ≡ t
    c4 a b c d t = trans (subTm-renTm (renTm vs (renTm vs (renTm vs t))))
                   (trans (subTm-renTm (renTm vs (renTm vs t)))
                   (trans (subTm-renTm (renTm vs t))
                   (trans (subTm-renTm t)
                   (trans (subTm-cong (λ x → refl) t) (subTm-id t)))))

    ext4 : RTm Γ → Sub (((((Γ ∙) ∙) ∙) ∙) ∙) ((((Γ ∙) ∙) ∙) ∙)
    ext4 d = extS (extS (extS (extS (single d))))

    -- a fields row's body, instantiated
    fieldsEq : (sh : Shape) (k : ℕ) (p h e f d : RTm Γ) →
               subTm (σ4 p h e f) (subTm (ext4 d)
                 (conₗ k (tpay sh (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var (vs vz)) (var vz) (var (vs (vs (vs (vs vz))))))))
               ≡ conₗ k (tpay sh p h e f d)
    fieldsEq sh k p h e f d =
      trans (cong (subTm (σ4 p h e f)) (trans (conₗ-sub (ext4 d) k (tpay sh v3 v2 v1 v0 v4))
                                              (cong (conₗ k) (tpay-sub (ext4 d) sh v3 v2 v1 v0 v4))))
      (trans (conₗ-sub (σ4 p h e f) k (tpay sh v3 v2 v1 v0 d4))
             (cong (conₗ k) (trans (tpay-sub (σ4 p h e f) sh v3 v2 v1 v0 d4) (cong (tpay sh p h e f) (c4 p h e f d)))))
      where
        v0 : {Δ : Cx} → RTm (Δ ∙)
        v0 = var vz
        v1 : {Δ : Cx} → RTm ((Δ ∙) ∙)
        v1 = var (vs vz)
        v2 : {Δ : Cx} → RTm (((Δ ∙) ∙) ∙)
        v2 = var (vs (vs vz))
        v3 : {Δ : Cx} → RTm ((((Δ ∙) ∙) ∙) ∙)
        v3 = var (vs (vs (vs vz)))
        v4 : {Δ : Cx} → RTm (((((Δ ∙) ∙) ∙) ∙) ∙)
        v4 = var (vs (vs (vs (vs vz))))
        d4 = renTm vs (renTm vs (renTm vs (renTm vs d)))

  -- ★★ AT A NODE: ι, the sort's and the constructor's selection, four β
  trav-node : {s c k : ℕ} {shs : Shapes c} {sh : Shape} {d p e f : RTm Γ} → NthG sg s shs → NthSh shs k sh →
              trav s d (conₗ k p) e f
                ⟶* node sh k p (dih (SD sg) TRAVM (app (SD sg) (pair (tag s) d)) (pair (tag k) p)) e f d
  trav-node {Γ = Γ} {s = s} {k = k} {shs = shs} {sh = sh} {d} {p} {e} {f} ng nh =
    ⟶*-trans (⟶*-appˡ (⟶*-appˡ (ιₛ-red {D = SD sg} {j = d} {p = p} (nth-sortMs ng) nm))) (fin sh)
    where
      h = dih (SD sg) TRAVM (app (SD sg) (pair (tag s) d)) (pair (tag k) p)
      nm : Nth (mTs {Γ = Γ} shs zero) k (mT sh k)
      nm = subst (λ m → Nth (mTs shs zero) k (mT sh m)) (+'-zero k) (nth-mTs nh)
      fin : (sh : Shape) → app (app (app (app (subTm (single d) (mT sh k)) p) h) e) f ⟶* node sh k p h e f d
      X : Shape → RTm (((((Γ ∙) ∙) ∙) ∙))
      X sh' = subTm (ext4 d) (conₗ k (tpay sh' (var (vs (vs (vs vz)))) (var (vs (vs vz))) (var (vs vz)) (var vz) (var (vs (vs (vs (vs vz)))))))
      fin []ʰ        = ⟶*-trans (β4 (X []ʰ) p h e f)
                         (subst (λ z → subTm (σ4 p h e f) (X []ʰ) ⟶* z) (fieldsEq []ʰ k p h e f d) done)
      fin (fl ∷ʰ sh) = ⟶*-trans (β4 (X (fl ∷ʰ sh)) p h e f)
                         (subst (λ z → subTm (σ4 p h e f) (X (fl ∷ʰ sh)) ⟶* z) (fieldsEq (fl ∷ʰ sh) k p h e f d) done)
      fin vʰ         = ⟶*-trans (β4 _ p h e f)
                         (subst (λ z → app (app N' e) (app f (fst p)) ⟶* app (app z e) (app f (fst p)))
                                (trans (cong (subTm (σ4 p h e f)) (NODE-sub (ext4 d))) (NODE-sub (σ4 p h e f))) done)
        where N' = subTm (σ4 p h e f) (subTm (ext4 d) (NODE {(((((Γ ∙) ∙) ∙) ∙) ∙)}))

  ----------------------------------------------------------------------
  -- 2. THE HYPOTHESES at a node are the children's traversals.
  ----------------------------------------------------------------------

  hyps-red : {s c k : ℕ} {shs : Shapes c} {sh : Shape} {d p : RTm Γ} → NthG sg s shs → NthSh shs k sh →
             dih (SD sg) TRAVM (app (SD sg) (pair (tag s) d)) (pair (tag k) p) ⟶* DihV sh (pair (tag s) d) (SD sg) TRAVM p
  hyps-red {Γ = Γ} {s = s} {c = c} {k = k} {shs = shs} {sh = sh} {d} {p} ng nh =
    ⟶*-trans (⟶*-dihᶜ (fibₛ-β d (nth-⌜⌝ₛₛ (nth-stels ng))))
    (step (dih-σ D M (⌜Fin⌝ c) (selF Cs) q)
    (⟶*-trans (⟶*-dihᶜ (⟶*-appʳ (step (βfst (tag k) p) done)))
    (⟶*-trans (⟶*-dihᵖ (step (βsnd (tag k) p) done))
    (⟶*-trans (⟶*-dihᶜ (selF-β (nth-sub (single ix) (nth-⌜⌝ (nth-tels nh)))))
              (subst (λ C → dih D M C p ⟶* DihV sh ix D M p) (sym (sub-tel (single ix) sh (var vz)))
                     (dihV-red sh ix D M p))))))
    where
      D M ix q : RTm Γ
      D = SD sg
      M = TRAVM
      ix = pair (tag s) d
      q = pair (tag k) p
      Cs = subC (single ix) ⌜ tels {Δ = Γ} shs ⌝ₛ

  -- the payload with every recursive field the child's OWN traversal
  tpayT : Shape → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  tpayT []ʰ             p e f d = unit
  tpayT (rec s k ∷ʰ sh) p e f d = pair (trav s (nsucs k d) (fst p) (nsucs k e) (LIFTS k e d f)) (tpayT sh (snd p) e f d)
  tpayT (nat ∷ʰ sh)     p e f d = pair (fst p) (tpayT sh (snd p) e f d)
  tpayT vʰ              p e f d = unit

  tpay-red : (sh : Shape) {s : ℕ} {p h e f d : RTm Γ} → h ⟶* DihV sh (pair (tag s) d) (SD sg) TRAVM p →
             tpay sh p h e f d ⟶* tpayT sh p e f d
  tpay-red []ʰ             r = done
  tpay-red (rec s' k ∷ʰ sh) {s} {p} {h} {e} {f} {d} r =
    ⟶*-trans (⟶*-pairˡ (⟶*-appˡ (⟶*-appˡ
               (⟶*-trans (⟶*-fst r)
                 (step (βfst (ielim (SD sg) (pair (tag s') (nsucs k (snd ix))) TRAVM (fst p)) (DihV sh ix (SD sg) TRAVM (snd p)))
                   (⟶*-ielimⁱ (⟶*-pairʳ (⟶*-nsucs k (step (βsnd (tag s) d) done)))))))))
             (⟶*-pairʳ (tpay-red sh {s} (⟶*-trans (⟶*-snd r)
                 (step (βsnd (ielim (SD sg) (pair (tag s') (nsucs k (snd ix))) TRAVM (fst p)) (DihV sh ix (SD sg) TRAVM (snd p))) done))))
    where ix = pair (tag s) d
  tpay-red (nat ∷ʰ sh)     r = ⟶*-pairʳ (tpay-red sh r)
  tpay-red vʰ              r = done

  ----------------------------------------------------------------------
  -- 3. ★★★ THE TRAVERSAL COMPUTES.
  ----------------------------------------------------------------------

  data Fields : Shape → Set where
    f-nil  : Fields []ʰ
    f-cons : {fl : Fld} {sh : Shape} → Fields (fl ∷ʰ sh)

  trav-con : {s c k : ℕ} {shs : Shapes c} {sh : Shape} {d p e f : RTm Γ} → NthG sg s shs → NthSh shs k sh → Fields sh →
             trav s d (conₗ k p) e f ⟶* conₗ k (tpayT sh p e f d)
  trav-con {s = s} {k = k} {sh = sh} {d} {p} {e} {f} ng nh f-nil  = ⟶*-trans (trav-node ng nh) (⟶*-con (⟶*-pairʳ (tpay-red sh {s} {p} {e = e} {f = f} {d = d} (hyps-red {s = s} {k = k} {sh = sh} {d = d} {p = p} ng nh))))
  trav-con {s = s} {k = k} {sh = sh} {d} {p} {e} {f} ng nh f-cons = ⟶*-trans (trav-node ng nh) (⟶*-con (⟶*-pairʳ (tpay-red sh {s} {p} {e = e} {f = f} {d = d} (hyps-red {s = s} {k = k} {sh = sh} {d = d} {p = p} ng nh))))

  trav-var : {s c k : ℕ} {shs : Shapes c} {d p e f : RTm Γ} → NthG sg s shs → NthSh shs k vʰ →
             trav s d (conₗ k p) e f ⟶* app (app NODE e) (app f (fst p))
  trav-var ng nh = trav-node ng nh

------------------------------------------------------------------------
-- 4. ★★ ENVIRONMENTS COMPUTE: `(f , u)` at zero is `u`, at `fsuc y` it is
--    `f y`; the LIFTED environment at zero is the fresh variable, at
--    `fsuc y` the old value weakened.  (Assumes the kit's `V0`, `WK`
--    closed; `refl` at a concrete signature.)
------------------------------------------------------------------------

FinD-sub : (σ : Sub Δ Θ) → subTm σ (FinD {Δ}) ≡ FinD
FinD-sub σ = refl

-- three β at once, and a triple weakening cancelled by them
σ3 : RTm Γ → RTm Γ → RTm Γ → Sub (((Γ ∙) ∙) ∙) Γ
σ3 a b c vz                = c
σ3 a b c (vs vz)           = b
σ3 a b c (vs (vs vz))      = a
σ3 a b c (vs (vs (vs x)))  = var x

β3 : (X : RTm (((Γ ∙) ∙) ∙)) (a b c : RTm Γ) → app (app (app (lam (lam (lam X))) a) b) c ⟶* subTm (σ3 a b c) X
β3 {Γ} X a b c =
  step (ξ-appˡ (ξ-appˡ (β (lam (lam X)) a)))
  (step (ξ-appˡ (β _ b))
  (step (β _ c)
    (subst (λ z → z ⟶* subTm (σ3 a b c) X) (sym eq) done)))
  where
    pt : (x : Var (((Γ ∙) ∙) ∙)) → subTm (single c) (subTm (extS (single b)) (extS (extS (single a)) x)) ≡ σ3 a b c x
    pt vz               = refl
    pt (vs vz)          = wk-cancel-tm c b
    pt (vs (vs vz))     = trans (cong (subTm (single c)) (trans (wkS (single b) (renTm vs a)) (cong (renTm vs) (wk-cancel-tm b a))))
                                (wk-cancel-tm c a)
      where open import DirectedHoTT.Metatheory.SubjectReductionBase using () renaming ( wk-sub to wkS )
    pt (vs (vs (vs x))) = refl
    eq : subTm (single c) (subTm (extS (single b)) (subTm (extS (extS (single a))) X)) ≡ subTm (σ3 a b c) X
    eq = trans (cong (subTm (single c)) (subTm-subTm X)) (trans (subTm-subTm X) (subTm-cong pt X))

σ3-w3 : (a b c t : RTm Γ) → subTm (σ3 a b c) (renTm vs (renTm vs (renTm vs t))) ≡ t
σ3-w3 a b c t = trans (subTm-renTm (renTm vs (renTm vs t)))
                (trans (subTm-renTm (renTm vs t))
                (trans (subTm-renTm t)
                (trans (subTm-cong (λ x → refl) t) (subTm-id t))))

module EnvRed {sg : Sig n} (ok : SigOK n sg) (κ : Kit n sg)
              (V0-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (Kit.V0 κ {Δ}) ≡ Kit.V0 κ)
              (WK-sub : {Δ Θ : Cx} (σ : Sub Δ Θ) → subTm σ (Kit.WK κ {Δ}) ≡ Kit.WK κ) where
  open Kit κ using ( V0; WK )
  open Trav ok κ

  consM-sub : (σ : Sub Δ Θ) (u : RTm Δ) → subTm σ (consM u) ≡ consM (subTm σ u)
  consM-sub σ u =
    trans (methN-sub σ (methAt []) (methAt (cz u ∷ cs ∷ [])))
      (cong₂ methN (methAt-sub σ [])
        (trans (methAt-sub (extS σ) (cz u ∷ cs ∷ []))
               (cong (λ z → methAt (lam (lam (lam z)) ∷ cs ∷ [])) (sub-w⁴ u))))

  -- CONS e d u f  =  (f , u)  at  x
  CONS· : RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
  CONS· e d u f = app (app (app (app CONS e) d) u) f

  private
    ms : RTm Γ → Cons (Γ ∙) 2
    ms u = cz u ∷ cs ∷ []

    -- CONS's five binders instantiated: the Fin case, applied to the tail
    cons-open : (e d u f x : RTm Γ) → app (CONS· e d u f) x ⟶* app (ielim FinD (nsuc d) (consM u) x) f
    cons-open {Γ} e d u f x =
      ⟶*-trans (⟶*-appˡ (β4 (lam B) e d u f))
        (step (β _ x) (subst (λ z → z ⟶* app (ielim FinD (nsuc d) (consM u) x) f) (sym eq) done))
      where
        B : RTm (((((Γ ∙) ∙) ∙) ∙) ∙)
        B = app (ielim FinD (nsuc (var (vs (vs (vs vz))))) (consM (var (vs (vs vz)))) (var vz)) (var (vs vz))
        S : RTm (((((Γ ∙) ∙) ∙) ∙) ∙) → RTm Γ
        S t = subTm (single x) (subTm (extS (σ4 e d u f)) t)
        eq : S B ≡ app (ielim FinD (nsuc d) (consM u) x) f
        eq = cong₃' (wk-cancel-tm x d)
                    (trans (cong (subTm (single x)) (consM-sub (extS (σ4 e d u f)) (var (vs (vs vz)))))
                           (trans (consM-sub (single x) (renTm vs u)) (cong consM (wk-cancel-tm x u))))
                    (wk-cancel-tm x f)
          where
            cong₃' : {a a' M M' c c' : RTm Γ} → a ≡ a' → M ≡ M' → c ≡ c' →
                     app (ielim FinD (nsuc a) M x) c ≡ app (ielim FinD (nsuc a') M' x) c'
            cong₃' refl refl refl = refl

  -- ★ (f , u) at zero is u
  cons-z : {e d u f : RTm Γ} → app (CONS· e d u f) ffz ⟶* u
  cons-z {Γ} {e} {d} {u} {f} =
    ⟶*-trans (cons-open e d u f ffz)
    (⟶*-trans (⟶*-appˡ (ιN-s {D = FinD} {E0 = methAt []} {m = d} {q = pair (tag zero) unit} {ES = methAt (ms u)}))
    (subst (λ M → app (app (app M (pair (tag zero) unit)) h) f ⟶* u) (sym (methAt-sub (single d) (ms u)))
      (⟶*-trans (⟶*-appˡ (methAt-β {m = subTm (single d) (cz u)} {p = unit} {h = h} nth-z))
        (⟶*-trans (β3 _ unit h f)
          (subst (λ z → z ⟶* u) (sym (trans (cong (subTm (σ3 unit h f)) cancel) (σ3-w3 unit h f u))) done)))))
    where
      h = dih FinD (consM u) (app FinD (nsuc d)) (pair (tag zero) unit)
      cancel : subTm (extS (extS (extS (single d)))) (renTm vs (renTm vs (renTm vs (renTm vs u))))
               ≡ renTm vs (renTm vs (renTm vs u))
      cancel = trans (sub-w³ {σ = single d} (renTm vs u)) (cong (λ z → renTm vs (renTm vs (renTm vs z))) (wk-cancel-tm d u))

  -- ★ (f , u) at a successor is f
  cons-s : {e d u f y : RTm Γ} → app (CONS· e d u f) (ffs y) ⟶* app f y
  cons-s {Γ} {e} {d} {u} {f} {y} =
    ⟶*-trans (cons-open e d u f (ffs y))
    (⟶*-trans (⟶*-appˡ (ιN-s {D = FinD} {E0 = methAt []} {m = d} {q = pair (tag (suc zero)) (pair y unit)} {ES = methAt (ms u)}))
    (subst (λ M → app (app (app M (pair (tag (suc zero)) (pair y unit))) h) f ⟶* app f y) (sym (methAt-sub (single d) (ms u)))
      (⟶*-trans (⟶*-appˡ (methAt-β {m = subTm (single d) cs} {p = pair y unit} {h = h} (nth-s nth-z)))
        (⟶*-trans (β3 _ (pair y unit) h f) (⟶*-appʳ (step (βfst y unit) done))))))
    where
      h = dih FinD (consM u) (app FinD (nsuc d)) (pair (tag (suc zero)) (pair y unit))

  -- LIFT e d f  =  (↑ f , the fresh variable)
  LIFT· : RTm Γ → RTm Γ → RTm Γ → RTm Γ
  LIFT· e d f = app (app (app LIFT e) d) f

  private
    lift-open : (e d f x : RTm Γ) →
                app (LIFT· e d f) x ⟶* app (CONS· (nsuc e) d (app V0 e) (lam (app (app WK (renTm vs e)) (app (renTm vs f) (var vz))))) x
    lift-open {Γ} e d f x = ⟶*-appˡ (⟶*-trans (β3 LB e d f) (subst (λ z → subTm (σ3 e d f) LB ⟶* z) eq done))
      where
        LB : RTm (((Γ ∙) ∙) ∙)
        LB = app (app (app (app CONS (nsuc (var (vs (vs vz))))) (var (vs vz))) (app V0 (var (vs (vs vz)))))
                 (lam (app (app WK (var (vs (vs (vs vz))))) (app (var (vs vz)) (var vz))))
        eq : subTm (σ3 e d f) LB ≡ CONS· (nsuc e) d (app V0 e) (lam (app (app WK (renTm vs e)) (app (renTm vs f) (var vz))))
        eq = cL (V0-sub (σ3 e d f)) (WK-sub (extS (σ3 e d f)))
          where
            cL : {V V' : RTm Γ} {W W' : RTm (Γ ∙)} → V ≡ V' → W ≡ W' →
                 app (app (app (app (subTm (σ3 e d f) CONS) (nsuc e)) d) (app V e))
                     (lam (app (app W (renTm vs e)) (app (renTm vs f) (var vz))))
                 ≡ CONS· (nsuc e) d (app V' e) (lam (app (app W' (renTm vs e)) (app (renTm vs f) (var vz))))
            cL refl refl = refl

  -- ★ the lifted environment at zero: the fresh variable
  lift-z : {e d f : RTm Γ} → app (LIFT· e d f) ffz ⟶* app V0 e
  lift-z {e = e} {d} {f} = ⟶*-trans (lift-open e d f ffz) cons-z

  -- ★ …at a successor: the old value, weakened
  lift-s : {e d f y : RTm Γ} → app (LIFT· e d f) (ffs y) ⟶* app (app WK e) (app f y)
  lift-s {e = e} {d} {f} {y} =
    ⟶*-trans (lift-open e d f (ffs y)) (⟶*-trans cons-s
      (step (β _ y) (subst (λ z → z ⟶* app (app WK e) (app f y)) (sym eq) done)))
    where
      eq : subTm (single y) (app (app WK (renTm vs e)) (app (renTm vs f) (var vz))) ≡ app (app WK e) (app f y)
      eq = cW (WK-sub (single y)) (wk-cancel-tm y e) (wk-cancel-tm y f)
        where
          cW : {W W' a a' b b' : RTm _} → W ≡ W' → a ≡ a' → b ≡ b' → app (app W a) (app b y) ≡ app (app W' a') (app b' y)
          cW refl refl refl = refl
