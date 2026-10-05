-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE EVALUATOR PRESERVES SCOPE (PLAN-EVAL E3, §2c).
--
-- A value built at depth `n` from an environment scoped below `n` is
-- scoped below `n` (`Algorithm/NbERead.Sc`).  One lemma per evaluator
-- function, by the SAME views: a lemma about a view-taking helper takes
-- the view and the scope of the viewed value, and has one case per view
-- constructor.  `tr`'s motive inspection runs at depth `n + 1`, but only
-- its VERDICT is used, so no lemma needs its scope.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Algorithm.NbEScope where
open import normalizer.Syntax.Types using ( _≡_; refl; _×_; _,_; ⊤; tt )
open import Agda.Builtin.Nat using ( zero; suc; _<_; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import Agda.Builtin.Maybe using ( Maybe; just; nothing )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Algorithm.NbE
open import DirectedHoTT.Algorithm.NbERead

private
  variable
    Γ : Cx

lt-self : (n : ℕ) → (n < suc n) ≡ true
lt-self zero    = refl
lt-self (suc n) = lt-self n

sc-lookup : (n : ℕ) (ρ : Env Γ) (x : Var Γ) → Scᵉ n ρ → Sc n (lookup ρ x)
sc-lookup n (ρ , v) vz     (sρ , sv) = sv
sc-lookup n (ρ , v) (vs x) (sρ , sv) = sc-lookup n ρ x sρ

sc-eval   : (k n : ℕ) (ρ : Env Γ) (t : RTm Γ) → Scᵉ n ρ → Sc n (eval k n ρ t)
sc-force  : (k n : ℕ) (v : Val) → Sc n v → Sc n (force k v)
sc-forceR : (k n : ℕ) {v : Val} (w : RefV v) → Sc n v → Sc n (forceR k w)
sc-inst   : (k n : ℕ) (c : Clo) (v : Val) → Scᶜ n c → Sc n v → Sc n (inst k n c v)
sc-inst₂  : (k n : ℕ) (c : Clo₂) (x y : Val) → Sc² n c → Sc n x → Sc n y → Sc n (inst₂ k n c x y)
-- the inspection's results live below m + 1
ScV : ℕ → Maybe TrPwV → Set
ScV n (just (trpw c sp a)) = Sc n c × Sc n a
ScV n nothing              = ⊤

sc-trPwN  : (k n : ℕ) (self d f : Clo) (e y : Val) (w : Maybe TrPwV) →
            Scᶜ n self → Scᶜ n d → Scᶜ n f → Sc n e → Sc n y → Sc n (trPwN k n self d f e y w)
sc-trPwView : (k m : ℕ) (d : Clo) → Scᶜ m d → ScV (suc m) (trPwView k m d)
sc-tpvH   : (k m : ℕ) {h : Val} (w : HomV h) → Sc (suc m) h → ScV (suc m) (tpvH k m w)
sc-trPwI  : (k n : ℕ) (self d f : Clo) (e y : Val) {h : Val} (w : HomV h) →
            Scᶜ n self → Scᶜ n d → Scᶜ n f → Sc n e → Sc n y → Sc n h → Sc n (trPwI k n self d f e y w)
sc-trPwS  : (k n : ℕ) (self f : Clo) (e y a : Val) {c : Val} (w : Maybe (PwSpine c)) →
            Scᶜ n self → Scᶜ n f → Sc n e → Sc n y → Sc n a → Sc n c → Sc n (trPwS k n self f e y a w)
sc-vApp   : (k n : ℕ) (f u : Val) → Sc n f → Sc n u → Sc n (vApp k n f u)
sc-appF   : (k n : ℕ) {f : Val} (w : LamV f) (u : Val) → Sc n f → Sc n u → Sc n (appF k n w u)
sc-vFst   : (k n : ℕ) (p : Val) → Sc n p → Sc n (vFst k p)
sc-vSnd   : (k n : ℕ) (p : Val) → Sc n p → Sc n (vSnd k p)
sc-fstF   : (n : ℕ) {p : Val} (w : PairV p) → Sc n p → Sc n (fstF w)
sc-sndF   : (n : ℕ) {p : Val} (w : PairV p) → Sc n p → Sc n (sndF w)
sc-vPsplit : (k n : ℕ) (b : Clo₂) (p : Val) → Sc² n b → Sc n p → Sc n (vPsplit k n b p)
sc-psplitF : (k n : ℕ) (b : Clo₂) {p : Val} (w : PairV p) → Sc² n b → Sc n p → Sc n (psplitF k n b w)
sc-vNatrec : (k n : ℕ) (z : Val) (s : Clo₂) (t : Val) → Sc n z → Sc² n s → Sc n t → Sc n (vNatrec k n z s t)
sc-natrecF : (k n : ℕ) (z : Val) (s : Clo₂) {t : Val} (w : NatV t) → Sc n z → Sc² n s → Sc n t → Sc n (natrecF k n z s w)
sc-vFcase : (k n : ℕ) (t a : Val) (b : Clo) → Sc n t → Sc n a → Scᶜ n b → Sc n (vFcase k n t a b)
sc-fcaseF : (k n : ℕ) {t : Val} (w : FinV t) (a : Val) (b : Clo) → Sc n t → Sc n a → Scᶜ n b → Sc n (fcaseF k n w a b)
sc-vOrdtr : (k n : ℕ) (a t u p q : Val) → Sc n a → Sc n t → Sc n u → Sc n p → Sc n q → Sc n (vOrdtr k n a t u p q)
sc-ordA   : (k n : ℕ) {a : Val} (w : NatV a) (t u p q : Val) → Sc n a → Sc n t → Sc n u → Sc n p → Sc n q → Sc n (ordA k n w t u p q)
sc-ordB   : (k n : ℕ) (a : Val) {t u : Val} (wt : NatV t) (wu : NatV u) (p q : Val) →
            Sc n a → Sc n t → Sc n u → Sc n p → Sc n q → Sc n (ordB k n a wt wu p q)
sc-vHrefl : (k n : ℕ) (C s : Val) → Sc n C → Sc n s → Sc n (vHrefl k n C s)
sc-hreflS : (k n : ℕ) (C : Val) (w : Maybe (PwSpine C)) (s : Val) → Sc n C → Sc n s → Sc n (hreflS k n C w s)
sc-hreflC : (k n : ℕ) {C : Val} (w : CodeV C) (s : Val) → Sc n C → Sc n s → Sc n (hreflC k n w s)
sc-hreflNat : (k n : ℕ) (s : Val) → Sc n s → Sc n (hreflNat k n s)
sc-hreflN : (k n : ℕ) {s : Val} (w : NatV s) → Sc n s → Sc n (hreflN k n w)
sc-vTr    : (k n : ℕ) (d : Clo) (p e : Val) → Scᶜ n d → Sc n p → Sc n e → Sc n (vTr k n d p e)
sc-trF    : (k n : ℕ) (d : Clo) {h : Val} (c : HomV h) {p : Val} (w : HreflV p) (lw : LamV p) (vw : VarV h) (e : Val) →
            Scᶜ n d → Sc n p → Sc n e → Sc (suc n) h → Sc n (trF k n d c w lw vw e)
sc-trPwC  : (k n : ℕ) (d f : Clo) (e : Val) (w : Maybe TrPwV) →
            Scᶜ n d → Scᶜ n f → Sc n e → Sc n (trPwC k n d f e w)
sc-trTautB : (k n : ℕ) (b : Bool) (d f : Clo) (e : Val) → Scᶜ n d → Scᶜ n f → Sc n e → Sc n (trTautB k n b d f e)
sc-vAp    : (k n : ℕ) (cB : Val) (b : Clo) (p : Val) → Sc n cB → Scᶜ n b → Sc n p → Sc n (vAp k n cB b p)
sc-apF    : (k n : ℕ) (cB : Val) (b : Clo) {p : Val} (w : HreflV p) → Sc n cB → Scᶜ n b → Sc n p → Sc n (apF k n cB b w)
sc-apB    : (k n : ℕ) (t : Bool) (cB : Val) (b : Clo) (c₁ s : Val) → Sc n cB → Scᶜ n b → Sc n c₁ → Sc n s → Sc n (apB k n t cB b c₁ s)
sc-vIelim : (k n : ℕ) (D i e t : Val) → Sc n D → Sc n i → Sc n e → Sc n t → Sc n (vIelim k n D i e t)
sc-ielimF : (k n : ℕ) (D i e : Val) {t : Val} (w : ConV t) → Sc n D → Sc n i → Sc n e → Sc n t → Sc n (ielimF k n D i e w)
sc-vDpay  : (k n : ℕ) (I D C : Val) → Sc n I → Sc n D → Sc n C → Sc n (vDpay k I D C)
sc-dpayF  : (k n : ℕ) (I D : Val) {C : Val} (w : DescV C) → Sc n I → Sc n D → Sc n C → Sc n (dpayF k I D w)
sc-vDih   : (k n : ℕ) (D e C p : Val) → Sc n D → Sc n e → Sc n C → Sc n p → Sc n (vDih k n D e C p)
sc-dihF   : (k n : ℕ) (D e : Val) {C : Val} (w : DescV C) (p : Val) → Sc n D → Sc n e → Sc n C → Sc n p → Sc n (dihF k n D e w p)
sc-pwAtS  : (k n : ℕ) {C : Val} (sp : PwSpine C) (x : Val) → Sc n C → Sc n x → Sc n (pwAtS k n sp x)
sc-pwForce : (k n : ℕ) (C : Val) → Sc n C → Sc n (pwForce k C)
sc-pwForceH : (k n : ℕ) {C : Val} (w : HomV C) → Sc n C → Sc n (pwForceH k w)

------------------------------------------------------------------------

sc-eval k n ρ (var x)           s = sc-lookup n ρ x s
sc-eval k n ρ (lam t)           s = s
sc-eval k n ρ (app f u)         s = sc-vApp k n _ _ (sc-eval k n ρ f s) (sc-eval k n ρ u s)
sc-eval k n ρ (pair a b)        s = sc-eval k n ρ a s , sc-eval k n ρ b s
sc-eval k n ρ (absurd c e)      s = sc-eval k n ρ c s , sc-eval k n ρ e s
sc-eval k n ρ (ordtr a t u p q) s =
  sc-vOrdtr k n _ _ _ _ _ (sc-eval k n ρ a s) (sc-eval k n ρ t s) (sc-eval k n ρ u s) (sc-eval k n ρ p s) (sc-eval k n ρ q s)
sc-eval k n ρ (fst p)           s = sc-vFst k n _ (sc-eval k n ρ p s)
sc-eval k n ρ (snd p)           s = sc-vSnd k n _ (sc-eval k n ρ p s)
sc-eval k n ρ ⌜base⌝            s = tt
sc-eval k n ρ (⌜Π⌝ c d)         s = sc-eval k n ρ c s , s
sc-eval k n ρ (⌜Σ⌝ c d)         s = sc-eval k n ρ c s , s
sc-eval k n ρ (⌜Hom⌝ c a b)     s = sc-eval k n ρ c s , (sc-eval k n ρ a s , sc-eval k n ρ b s)
sc-eval k n ρ (hrefl c t)       s = sc-vHrefl k n _ _ (sc-eval k n ρ c s) (sc-eval k n ρ t s)
sc-eval k n ρ (tr d p e)        s = sc-vTr k n _ _ _ s (sc-eval k n ρ p s) (sc-eval k n ρ e s)
sc-eval k n ρ (ap c b p)        s = sc-vAp k n _ _ _ (sc-eval k n ρ c s) s (sc-eval k n ρ p s)
sc-eval k n ρ (⌜Id⌝ c a b)      s = sc-eval k n ρ c s , (sc-eval k n ρ a s , sc-eval k n ρ b s)
sc-eval k n ρ (idrefl c t)      s = sc-eval k n ρ c s , sc-eval k n ρ t s
sc-eval k n ρ (jsub d p e)      s = sc-jsub (sc-eval k n ρ p s) (sc-eval k n ρ e s)
  where
  sc-jsub : {p e : Val} → Sc n p → Sc n e → Sc n (vJsub k (clo ρ d) p e)
  sc-jsub {p} {e} sp se = go (idreflV (force k p)) (sc-force k n p sp)
    where
    go : {p' : Val} (w : IdreflV p') → Sc n p' → Sc n (jsubF (clo ρ d) w e)
    go (isIdrefl c s') _  = se
    go (notIdrefl q)   sq = s , (sq , se)
sc-eval k n ρ unit              s = tt
sc-eval k n ρ nzero             s = tt
sc-eval k n ρ (nsuc t)          s = sc-eval k n ρ t s
sc-eval k n ρ (natrec z c t)    s = sc-vNatrec k n _ _ _ (sc-eval k n ρ z s) s (sc-eval k n ρ t s)
sc-eval k n ρ (con p)           s = sc-eval k n ρ p s
sc-eval k n ρ (ielim D i e t)   s =
  sc-vIelim k n _ _ _ _ (sc-eval k n ρ D s) (sc-eval k n ρ i s) (sc-eval k n ρ e s) (sc-eval k n ρ t s)
sc-eval k n ρ dι                s = tt
sc-eval k n ρ (dσ S f)          s = sc-eval k n ρ S s , sc-eval k n ρ f s
sc-eval k n ρ (dρ j C)          s = sc-eval k n ρ j s , sc-eval k n ρ C s
sc-eval k n ρ (dpay I D C)      s = sc-vDpay k n _ _ _ (sc-eval k n ρ I s) (sc-eval k n ρ D s) (sc-eval k n ρ C s)
sc-eval k n ρ (dih D e C p)     s =
  sc-vDih k n _ _ _ _ (sc-eval k n ρ D s) (sc-eval k n ρ e s) (sc-eval k n ρ C s) (sc-eval k n ρ p s)
sc-eval k n ρ fzero             s = tt
sc-eval k n ρ (fsuc t)          s = sc-eval k n ρ t s
sc-eval k n ρ (fcase t a b)     s = sc-vFcase k n _ _ _ (sc-eval k n ρ t s) (sc-eval k n ρ a s) s
sc-eval k n ρ (fcase0 t)        s = sc-eval k n ρ t s
sc-eval k n ρ (psplit b p)      s = sc-vPsplit k n _ _ s (sc-eval k n ρ p s)
sc-eval k n ρ ⌜Nat⌝             s = tt
sc-eval k n ρ (⌜IMu⌝ I D i)     s = sc-eval k n ρ I s , (sc-eval k n ρ D s , sc-eval k n ρ i s)
sc-eval k n ρ (⌜Fin⌝ t)         s = sc-eval k n ρ t s
sc-eval k n ρ ⌜Unit⌝            s = tt
sc-eval k n ρ (ref d b)         s = tt

sc-force zero    n v s = s
sc-force (suc k) n v s = sc-forceR k n (refV v) s
-- a reference's body is closed: scoped below 0, so below any n
sc-forceR k n (isRef d b) s = mono (force k (eval k 0 [] b)) (up-zero n) (sc-force k 0 _ (sc-eval k 0 [] b tt))
sc-forceR k n (notRef v)  s = s

sc-inst zero    n c                v sc sv = sc , sv
sc-inst (suc k) n (clo ρ t)        v sc sv = sc-eval k n (ρ , v) t (sc , sv)
sc-inst (suc k) n (cloK w)         v sc sv = sc
sc-inst (suc k) n (cloHrefl C sp s) v (sC , ss) sv =
  sc-vHrefl k n _ _ (sc-pwAtS k n sp v sC sv) (sc-vApp k n s v ss sv)
sc-inst (suc k) n (cloDpay I D f)  v (sI , (sD , sf)) sv = sc-vDpay k n _ _ _ sI sD (sc-vApp k n f v sf sv)
sc-inst (suc k) n (cloHomTo C A)   v (sC , sA) sv = sC , (sA , sv)
sc-inst (suc k) n self@(cloTrPw d f e) y sself@(sd , (sf , se)) sy =
  sc-trPwN k n self d f e y (trPwView k n d) sself sd sf se sy

sc-trPwN k n self d f e y (just _) sself sd sf se sy =
  sc-trPwI k n self d f e y (homV (force k (inst k n d y))) sself sd sf se sy (sc-force k n _ (sc-inst k n d y sd sy))
sc-trPwN k n self d f e y nothing  sself sd sf se sy = sself , sy

sc-trPwView k m d sd =
  sc-tpvH k m (homV (force k (inst k (suc m) d (vvar m))))
          (sc-force k (suc m) _ (sc-inst k (suc m) d (vvar m) (monoᶜ d (up-suc m) sd) (lt-self m)))
sc-tpvH k m (isHom c a mm) (sc , (sa , _)) = tpvL-sc (isLvl m (varV mm))
  where
  tpvS-sc : (c' : Val) (w : Maybe (PwSpine c')) → Sc (suc m) c' → ScV (suc m) (tpvS a c' w)
  tpvS-sc c' (just sp) sc' = sc' , sa
  tpvS-sc c' nothing   sc' = tt
  tpvL-sc : (b : Bool) → ScV (suc m) (tpvL k c a b)
  tpvL-sc true  = tpvS-sc (pwForce k c) (pwSpine? (pwForce k c)) (sc-pwForce k (suc m) c sc)
  tpvL-sc false = tt
sc-tpvH k m (notHom _) sh = tt

sc-trPwI k n self d f e y (isHom c a _) sself sd sf se sy (sc , (sa , _)) =
  sc-trPwS k n self f e y a (pwSpine? (pwForce k c)) sself sf se sy sa (sc-pwForce k n c sc)
sc-trPwI k n self d f e y (notHom _)    sself sd sf se sy sh = sself , sy
sc-trPwS k n self f e y a (just sp) sself sf se sy sa sc =
  sc-vTr k n _ _ _ (sc-pwAtS k n sp y sc sy , sc-vApp k n a y sa sy) (sc-inst k n f y sf sy) (sc-vApp k n e y se sy)
sc-trPwS k n self f e y a nothing   sself sf se sy sa sc = sself , sy

sc-inst₂ zero    n (clo₂ ρ t) x y sρ sx sy = sρ , (sx , sy)
sc-inst₂ (suc k) n (clo₂ ρ t) x y sρ sx sy = sc-eval k n ((ρ , x) , y) t ((sρ , sx) , sy)

sc-vApp k n f u sf su = sc-appF k n (lamV (force k f)) u (sc-force k n f sf) su
sc-appF zero    n (isLam c)  u sf su = sf , su
sc-appF zero    n (notLam f) u sf su = sf , su
sc-appF (suc k) n (isLam c)  u sf su = sc-inst k n c u sf su
sc-appF (suc k) n (notLam f) u sf su = sf , su

sc-vFst k n p s = sc-fstF n (pairV (force k p)) (sc-force k n p s)
sc-vSnd k n p s = sc-sndF n (pairV (force k p)) (sc-force k n p s)
sc-fstF n (isPair a b) (sa , sb) = sa
sc-fstF n (notPair p)  s         = s
sc-sndF n (isPair a b) (sa , sb) = sb
sc-sndF n (notPair p)  s         = s

sc-vPsplit k n b p sb sp = sc-psplitF k n b (pairV (force k p)) sb (sc-force k n p sp)
sc-psplitF zero    n b (isPair x y) sb sp = sb , sp
sc-psplitF zero    n b (notPair p)  sb sp = sb , sp
sc-psplitF (suc k) n b (isPair x y) sb (sx , sy) = sc-inst₂ k n b x y sb sx sy
sc-psplitF (suc k) n b (notPair p)  sb sp = sb , sp

sc-vNatrec k n z s t sz ss st = sc-natrecF k n z s (natV (force k t)) sz ss (sc-force k n t st)
sc-natrecF k       n z s isZero     sz ss st = sz
sc-natrecF zero    n z s (isSuc t)  sz ss st = sz , (ss , st)
sc-natrecF (suc k) n z s (isSuc t)  sz ss st = sc-inst₂ k n s t _ ss st (sc-vNatrec k n z s t sz ss st)
sc-natrecF k       n z s (notNat t) sz ss st = sz , (ss , st)

sc-vFcase k n t a b st sa sb = sc-fcaseF k n (finV (force k t)) a b (sc-force k n t st) sa sb
sc-fcaseF k       n isFz       a b st sa sb = sa
sc-fcaseF zero    n (isFs t)   a b st sa sb = st , (sa , sb)
sc-fcaseF (suc k) n (isFs t)   a b st sa sb = sc-inst k n b t sb st
sc-fcaseF k       n (notFin t) a b st sa sb = st , (sa , sb)

sc-vOrdtr k n a t u p q sa st su sp sq =
  sc-ordA k n (natV (force k a)) _ _ p q (sc-force k n a sa) (sc-force k n t st) (sc-force k n u su) sp sq
sc-ordA k n isZero     t u p q sa st su sp sq = tt
sc-ordA k n (isSuc a)  t u p q sa st su sp sq = sc-ordB k n a (natV t) (natV u) p q sa st su sp sq
sc-ordA k n (notNat a) t u p q sa st su sp sq = sa , (st , (su , (sp , sq)))
sc-ordB k       n a isZero     isZero     p q sa st su sp sq = sp
sc-ordB k       n a (isSuc t)  isZero     p q sa st su sp sq = sq
sc-ordB k       n a isZero     (isSuc u)  p q sa st su sp sq = (tt , (sa , su)) , sp
sc-ordB zero    n a (isSuc t)  (isSuc u)  p q sa st su sp sq = sa , (st , (su , (sp , sq)))
sc-ordB (suc k) n a (isSuc t)  (isSuc u)  p q sa st su sp sq = sc-vOrdtr k n a t u p q sa st su sp sq
sc-ordB k       n a (notNat t) isZero     p q sa st su sp sq = sa , (st , (tt , (sp , sq)))
sc-ordB k       n a (notNat t) (isSuc u)  p q sa st su sp sq = sa , (st , (su , (sp , sq)))
sc-ordB k       n a (notNat t) (notNat u) p q sa st su sp sq = sa , (st , (su , (sp , sq)))
sc-ordB k       n a isZero     (notNat u) p q sa st su sp sq = sa , (tt , (su , (sp , sq)))
sc-ordB k       n a (isSuc t)  (notNat u) p q sa st su sp sq = sa , (st , (su , (sp , sq)))

sc-vHrefl k n C s sC ss = sc-hreflS k n (pwForce k C) (pwSpine? (pwForce k C)) s (sc-pwForce k n C sC) ss
sc-hreflS k n C (just sp) s sC ss = sC , ss
sc-hreflS k n C nothing   s sC ss = sc-hreflC k n (codeV C) s sC ss
sc-hreflC k n cNat         s sC ss = sc-hreflNat k n s ss
sc-hreflC k n cbase        s sC ss = sC , ss
sc-hreflC k n (cΠ c d)     s sC ss = sC , ss
sc-hreflC k n (cΣ c d)     s sC ss = sC , ss
sc-hreflC k n (cHom c a b) s sC ss = sC , ss
sc-hreflC k n (cId c a b)  s sC ss = sC , ss
sc-hreflC k n cUnit        s sC ss = sC , ss
sc-hreflC k n (cIMu I D i) s sC ss = sC , ss
sc-hreflC k n (cFin t)     s sC ss = sC , ss
sc-hreflC k n (cOther C)   s sC ss = sC , ss
sc-hreflNat zero    n s ss = tt , ss
sc-hreflNat (suc k) n s ss = sc-hreflN k n (natV (force k s)) (sc-force k n s ss)
sc-hreflN k n isZero     ss = tt
sc-hreflN k n (isSuc m)  ss = sc-hreflNat k n m ss
sc-hreflN k n (notNat s) ss = tt , ss

sc-vTr zero    n d p e sd sp se = sd , (sp , se)
sc-vTr (suc k) n d p e sd sp se =
  sc-trF k n d (homV h) (hreflV (force k p)) (lamV (force k p)) (varV h) e sd (sc-force k n p sp) se
         (sc-force k (suc n) _ (sc-inst k (suc n) d (vvar n) (monoᶜ d (up-suc n) sd) (lt-self n)))
  where h = force k (inst k (suc n) d (vvar n))
sc-trF k n d (isHom c a m) (isHrefl C s) w v e sd sp se sh = sc-J (trJ k (codeV (force k C)))
  where
  sc-J : (b : Bool) → Sc n (trJB b d (vhrefl C s) e)
  sc-J true  = se
  sc-J false = sd , (sp , se)
sc-trF k n d (isHom c a m) (notHrefl _) (isLam f) v e sd sp se sh = byP (isTrPw f)
  where
  byP : (b : Bool) → Sc n (trPwP k n d f e b)
  byP true  = sd , (sp , se)
  byP false = sc-trPwC k n d f e (trPwView k n d) sd sp se
sc-trF k n d (isHom c a m) (notHrefl _) (notLam p) v e sd sp se sh = sd , (sp , se)
sc-trF k n d (notHom _) w (isLam f) (isVar l) e sd sp se sh = byP (isTrPw f)
  where
  byP : (b : Bool) → Sc n (trTautP k n l d f e b)
  byP true  = sd , (sp , se)
  byP false = sc-trTautB k n (l == n) d f e sd sp se
sc-trF k n d (notHom _) w (isLam f) (notVar _) e sd sp se sh = sd , (sp , se)
sc-trF k n d (notHom _) w (notLam p) v e sd sp se sh = sd , (sp , se)
sc-trPwC k n d f e (just _) sd sf se = sd , (sf , se)
sc-trPwC k n d f e nothing  sd sf se = sd , (sf , se)

sc-trTautB k n true  d f e sd sf se = sc-inst k n f e sf se
sc-trTautB k n false d f e sd sf se = sd , (sf , se)

sc-vAp k n cB b p scB sb sp = sc-apF k n cB b (hreflV (force k p)) scB sb (sc-force k n p sp)
sc-apF zero    n cB b (isHrefl c₁ s) scB sb sp = scB , (sb , sp)
sc-apF zero    n cB b (notHrefl p)   scB sb sp = scB , (sb , sp)
sc-apF (suc k) n cB b (isHrefl c₁ s) scB sb (sc₁ , ss) = sc-apB k n (stkV false k c₁) cB b c₁ s scB sb sc₁ ss
sc-apF (suc k) n cB b (notHrefl p)   scB sb sp = scB , (sb , sp)
sc-apB k n true  cB b c₁ s scB sb sc₁ ss = sc-vHrefl k n cB _ scB (sc-inst k n b s sb ss)
sc-apB k n false cB b c₁ s scB sb sc₁ ss = scB , (sb , (sc₁ , ss))

sc-vIelim k n D i e t sD si se st = sc-ielimF k n D i e (conV (force k t)) sD si se (sc-force k n t st)
sc-ielimF zero    n D i e (isCon p)  sD si se st = sD , (si , (se , st))
sc-ielimF zero    n D i e (notCon t) sD si se st = sD , (si , (se , st))
sc-ielimF (suc k) n D i e (isCon p)  sD si se sp =
  sc-vApp k n _ _ (sc-vApp k n _ _ (sc-vApp k n e i se si) sp)
                  (sc-vDih k n D e _ p sD se (sc-vApp k n D i sD si) sp)
sc-ielimF (suc k) n D i e (notCon t) sD si se st = sD , (si , (se , st))

sc-vDpay k n I D C sI sD sC = sc-dpayF k n I D (descV (force k C)) sI sD (sc-force k n C sC)
sc-dpayF k       n I D isDι       sI sD sC = tt
sc-dpayF k       n I D (isDσ S f) sI sD (sS , sf) = sS , (sI , (sD , sf))
sc-dpayF zero    n I D (isDρ j C) sI sD sC = sI , (sD , sC)
sc-dpayF (suc k) n I D (isDρ j C) sI sD (sj , sC) = (sI , (sD , sj)) , sc-vDpay k n I D C sI sD sC
sc-dpayF k       n I D (notDesc C) sI sD sC = sI , (sD , sC)

sc-vDih k n D e C p sD se sC sp = sc-dihF k n D e (descV (force k C)) p sD se (sc-force k n C sC) sp
sc-dihF k       n D e isDι       p sD se sC sp = tt
sc-dihF zero    n D e (isDσ S f) p sD se sC sp = sD , (se , (sC , sp))
sc-dihF (suc k) n D e (isDσ S f) p sD se (sS , sf) sp =
  sc-vDih k n D e _ _ sD se (sc-vApp k n f _ sf (sc-vFst k n p sp)) (sc-vSnd k n p sp)
sc-dihF zero    n D e (isDρ j C) p sD se sC sp = sD , (se , (sC , sp))
sc-dihF (suc k) n D e (isDρ j C) p sD se (sj , sC) sp =
  sc-vIelim k n D j e _ sD sj se (sc-vFst k n p sp) , sc-vDih k n D e C _ sD se sC (sc-vSnd k n p sp)
sc-dihF k       n D e (notDesc C) p sD se sC sp = sD , (se , (sC , sp))

sc-pwAtS k n (spΠ γ δ)      x (sγ , sδ) sx = sc-inst k n δ x sδ sx
sc-pwAtS k n (spHom sp a b) x (sC , (sa , sb)) sx =
  sc-pwAtS k n sp x sC sx , (sc-vApp k n a x sa sx , sc-vApp k n b x sb sx)

sc-pwForce zero    n C sC = sC
sc-pwForce (suc k) n C sC = sc-pwForceH k n (homV (force k C)) (sc-force k n C sC)
sc-pwForceH k n (isHom C a b) (sC , (sa , sb)) = sc-pwForce k n C sC , (sa , sb)
sc-pwForceH k n (notHom v)    sv = sv
