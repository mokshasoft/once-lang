{-# OPTIONS --safe #-}
-- SPIKE-LEVITATION S1b — neutral descriptions in S3's (levitation-paper)
-- form: methods are ONE Π, and ι fires at ANY description.
--
-- S1 showed that in the constructor-LIST form ι must be guarded by a
-- canonical description: at a neutral D the method TUPLE has a stuck type,
-- so it is known only SN, and `sel k ms` can be Ω.  Here the methods are a
-- Π whose domain is stuck (`pay D D i`) but whose candidate still promises
-- "applied to SN arguments, lands in the motive".  So the question is
-- whether the unguarded ι is sound at a neutral D.
--
-- SUCCESS: `ielim-ne` — at a neutral D, `ielim D M e i t` is in the motive's
--   candidate, by Girard's CR3 (it is an elimination; every reduct is in),
--   the ι reduct handled by the method's Π-candidate and `ih` stuck on D.
-- CONTROL: know the method only SN (the tuple form's stuck type), and the
--   same statement is REFUTED with an explicit Ω (below).
module tmp.LevS1b where

open import tmp.LevSyn
open import tmp.LevS3
open Syntax Op ar

data ⊥ : Set where

¬_ : Set → Set
¬ X = X → ⊥

-- stuck terms: a variable under eliminations; the description operators
-- are stuck on a stuck TELESCOPE, ielim on a stuck SCRUTINEE.
data Ne {n : Nat} : Tm n → Set where
  ne-var   : {x : Fin n} → Ne (var x)
  ne-app   : Ne t → Ne (app t u)
  ne-fst   : Ne t → Ne (fst t)
  ne-snd   : Ne t → Ne (snd t)
  ne-ielim : Ne t → Ne (ielim D M e i t)
  ne-pay   : Ne C → Ne (pay D C i)
  ne-ihTy  : Ne C → Ne (ihTy D M C p)
  ne-ih    : Ne C → Ne (ih D M e C p)

ne-pres : Ne t → t ⟶ t' → Ne t'
ne-pres ne-var (desc ())
ne-pres (ne-app ()) β
ne-pres (ne-app n) (desc ())
ne-pres (ne-app n) (under (here s))                 = ne-app (ne-pres n s)
ne-pres (ne-app n) (under (there (here s)))         = ne-app n
ne-pres (ne-app n) (under (there (there ())))
ne-pres (ne-fst ()) π₁
ne-pres (ne-fst n) (desc ())
ne-pres (ne-fst n) (under (here s))                 = ne-fst (ne-pres n s)
ne-pres (ne-fst n) (under (there ()))
ne-pres (ne-snd ()) π₂
ne-pres (ne-snd n) (desc ())
ne-pres (ne-snd n) (under (here s))                 = ne-snd (ne-pres n s)
ne-pres (ne-snd n) (under (there ()))
ne-pres (ne-ielim ()) (desc ι)
ne-pres (ne-ielim n) (under (here _))               = ne-ielim n
ne-pres (ne-ielim n) (under (there (here _)))       = ne-ielim n
ne-pres (ne-ielim n) (under (there (there (here _)))) = ne-ielim n
ne-pres (ne-ielim n) (under (there (there (there (here _))))) = ne-ielim n
ne-pres (ne-ielim n) (under (there (there (there (there (here s)))))) = ne-ielim (ne-pres n s)
ne-pres (ne-ielim n) (under (there (there (there (there (there ()))))))
ne-pres (ne-pay ()) (desc pay-ι)
ne-pres (ne-pay ()) (desc pay-σ)
ne-pres (ne-pay ()) (desc pay-ρ)
ne-pres (ne-pay n) (under (here _))                 = ne-pay n
ne-pres (ne-pay n) (under (there (here s)))         = ne-pay (ne-pres n s)
ne-pres (ne-pay n) (under (there (there (here _)))) = ne-pay n
ne-pres (ne-pay n) (under (there (there (there ()))))
ne-pres (ne-ihTy ()) (desc ihTy-ι)
ne-pres (ne-ihTy ()) (desc ihTy-σ)
ne-pres (ne-ihTy ()) (desc ihTy-ρ)
ne-pres (ne-ihTy n) (under (here _))                = ne-ihTy n
ne-pres (ne-ihTy n) (under (there (here _)))        = ne-ihTy n
ne-pres (ne-ihTy n) (under (there (there (here s)))) = ne-ihTy (ne-pres n s)
ne-pres (ne-ihTy n) (under (there (there (there (here _))))) = ne-ihTy n
ne-pres (ne-ihTy n) (under (there (there (there (there ())))))
ne-pres (ne-ih ()) (desc ih-ι)
ne-pres (ne-ih ()) (desc ih-σ)
ne-pres (ne-ih ()) (desc ih-ρ)
ne-pres (ne-ih n) (under (here _))                  = ne-ih n
ne-pres (ne-ih n) (under (there (here _)))          = ne-ih n
ne-pres (ne-ih n) (under (there (there (here _))))  = ne-ih n
ne-pres (ne-ih n) (under (there (there (there (here s))))) = ne-ih (ne-pres n s)
ne-pres (ne-ih n) (under (there (there (there (there (here _)))))) = ne-ih n
ne-pres (ne-ih n) (under (there (there (there (there (there ()))))))

data SN {n : Nat} (t : Tm n) : Set where
  sn : (∀ {t'} → t ⟶ t' → SN t') → SN t

sn-step : SN t → t ⟶ t' → SN t'
sn-step (sn h) s = h s

sn-con-inv : SN (con p) → SN p
sn-con-inv (sn h) = sn λ s → sn-con-inv (h (under (here s)))

-- `ih` over a STUCK telescope is SN from SN parts
sn-ih   : Ne C → SN D → SN M → SN e → SN C → SN p → SN (ih D M e C p)
ih-step : Ne C → SN D → SN M → SN e → SN C → SN p → ih D M e C p ⟶ t' → SN t'
sn-ih nC sD sM se sC sp = sn (ih-step nC sD sM se sC sp)
ih-step () _ _ _ _ _ (desc ih-ι)
ih-step () _ _ _ _ _ (desc ih-σ)
ih-step () _ _ _ _ _ (desc ih-ρ)
ih-step nC (sn h) sM se sC sp (under (here s)) = sn-ih nC (h s) sM se sC sp
ih-step nC sD (sn h) se sC sp (under (there (here s))) = sn-ih nC sD (h s) se sC sp
ih-step nC sD sM (sn h) sC sp (under (there (there (here s)))) = sn-ih nC sD sM (h s) sC sp
ih-step nC sD sM se (sn h) sp (under (there (there (there (here s))))) =
  sn-ih (ne-pres nC s) sD sM se (h s) sp
ih-step nC sD sM se sC (sn h) (under (there (there (there (there (here s)))))) =
  sn-ih nC sD sM se sC (h s)
ih-step nC sD sM se sC sp (under (there (there (there (there (there ()))))))

-- Girard's candidates: CR3 is for ELIMINATIONS (non-introductions)
data Elim {n : Nat} : Tm n → Set where
  el-ielim : Elim (ielim D M e i t)

record Cand (n : Nat) : Set₁ where
  field
    _∋_ : Tm n → Set
    cr1 : ∀ {t} → _∋_ t → SN t
    cr2 : ∀ {t t'} → _∋_ t → t ⟶ t' → _∋_ t'
    cr3 : ∀ {t} → Elim t → (∀ {t'} → t ⟶ t' → _∋_ t') → _∋_ t
open Cand

-- The model's data at a NEUTRAL D.  `IxC` interprets `El ix`; `Mot M i t`
-- interprets `El (app (app M i) t)` and — as every type interpretation —
-- respects reduction of what it is built from.
variable e' M' : Tm n

module Model
  {n    : Nat}
  (IxC  : Cand n)
  (Mot  : Tm n → Tm n → Tm n → Cand n)
  (mot-M  : ∀ {M M' i t x} → M ⟶ M' → Mot M' i t ∋ x → Mot M i t ∋ x)
  (mot-M' : ∀ {M M' i t x} → M ⟶ M' → Mot M i t ∋ x → Mot M' i t ∋ x)
  (mot-i  : ∀ {M i i' t x} → i ⟶ i' → Mot M i' t ∋ x → Mot M i t ∋ x)
  (mot-t  : ∀ {M i t t' x} → t ⟶ t' → Mot M i t' ∋ x → Mot M i t ∋ x)
  where

  -- the METHOD's candidate: the three-fold Π of `MethTy D M`.  At a neutral
  -- D its domains `pay D D i` and `ihTy D M D p` are stuck, so they are
  -- interpreted as SN — the Π itself is NOT stuck.
  MF : Tm n → Tm n → Set
  MF M e = ∀ {i p h} → IxC ∋ i → SN p → SN h → Mot M i (con p) ∋ app (app (app e i) p) h

  mf-e : MF M e → e ⟶ e' → MF M e'
  mf-e {M = M} f s xi sp sh =
    cr2 (Mot M _ _) (f xi sp sh) (under (here (under (here (under (here s))))))

  mf-M : MF M e → M ⟶ M' → MF M' e
  mf-M f s xi sp sh = mot-M' s (f xi sp sh)

  -- ★ `⊢ielim` at a NEUTRAL D, with the UNGUARDED ι
  ielim-ne : Ne D → SN D → SN M → SN e → MF M e → SN i → IxC ∋ i → SN t →
             Mot M i t ∋ ielim D M e i t
  ielim-ne {D = D} {M = M} {e = e} {i = i} {t = t}
           nD sD@(sn hD) sM@(sn hM) se@(sn he) mf si@(sn hi) xi st@(sn ht) =
    cr3 (Mot M i t) el-ielim λ where
      (desc ι) → mf xi (sn-con-inv st) (sn-ih nD sD sM se sD (sn-con-inv st))
      (under (here s)) →
        ielim-ne (ne-pres nD s) (hD s) sM se mf si xi st
      (under (there (here s))) →
        mot-M s (ielim-ne nD sD (hM s) se (mf-M mf s) si xi st)
      (under (there (there (here s)))) →
        ielim-ne nD sD sM (he s) (mf-e mf s) si xi st
      (under (there (there (there (here s))))) →
        mot-i s (ielim-ne nD sD sM se mf (hi s) (cr2 IxC xi s) st)
      (under (there (there (there (there (here s)))))) →
        mot-t s (ielim-ne nD sD sM se mf si xi (ht s))
      (under (there (there (there (there (there ()))))))

-- ═══ CONTROL: the method known only SN (a stuck TUPLE type) ═════════════
module Control where
  ω : Tm n
  ω = lam (app (var fz) (var fz))

  no-Ω : ¬ SN (app (ω {n}) ω)
  no-Ω (sn h) = no-Ω (h β)

  nf→sn : (∀ {t'} → ¬ (t ⟶ t')) → SN t
  nf→sn h = sn λ s → ⊥-elim' (h s)
    where ⊥-elim' : {X : Set} → ⊥ → X
          ⊥-elim' ()

  nf-lam : {b : Tm (suc n)} → (∀ {t'} → ¬ (b ⟶ t')) → ¬ (lam b ⟶ t)
  nf-lam h (desc ())
  nf-lam h (under (here s)) = h s
  nf-lam h (under (there ()))

  nf-con : (∀ {t'} → ¬ (p ⟶ t')) → ¬ (con p ⟶ t)
  nf-con h (desc ())
  nf-con h (under (here s)) = h s
  nf-con h (under (there ()))

  nf-vv : {x y : Fin n} → ¬ (app (var x) (var y) ⟶ t)
  nf-vv (desc ())
  nf-vv (under (here (desc ())))
  nf-vv (under (there (here (desc ()))))
  nf-vv (under (there (there ())))

  ω-nf : ¬ (ω {n} ⟶ t)
  ω-nf = nf-lam nf-vv

  -- the method: λ i p h. p p — normal, hence SN; applied to p = ω it is Ω
  E : Tm n
  E = lam (lam (lam (app (var (fs fz)) (var (fs fz)))))

  refuted : ¬ (∀ {n} {D M e i t : Tm n} → Ne D → SN D → SN M → SN e → SN i → SN t →
               SN (ielim D M e i t))
  refuted claim =
    no-Ω (sn-step (sn-step (sn-step (sn-step s (desc ι))
                                    (under (here (under (here β)))))
                           (under (here β)))
                  β)
    where
    s = claim {1} {var fz} {var fz} {E} {var fz} {con ω} ne-var
          (sn λ { (desc ()) }) (sn λ { (desc ()) })
          (nf→sn (nf-lam (nf-lam (nf-lam nf-vv))))
          (sn λ { (desc ()) })
          (nf→sn (nf-con ω-nf))
