-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ExprOps — plan 0.146 B1.7 (D445 at the bridge): the bridge's
-- program's ops are declared.
--
-- A term is `OK` when every op it runs (`lop`) satisfies `D`; then every op
-- its code names (`Keys.tmGot`'s `ps`) does (`ok-ps`), and a table's and a
-- program's universe's (`univ-ok`), as `LinkedCore` gives for the pass's.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)
open import Once.LinCore.Flat using (Base)
open import Data.Nat using (ℕ)

module Once.LinCore.ExprOps (fmt : TargetNum) (bw : Base → ℕ) where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here)

open import Once.LinCore.Core fmt
open import Once.LinCore.Keys fmt bw using (ps; tmGot; defsGot; ops; univ)

module _ (D : Sig → Set) where

  -- every op a term runs satisfies `D`
  OK : ∀ {Γ E A B} → Tm Γ E A B → Set
  OK (f ∘l g)     = OK f × OK g
  OK (f ⊗l g)     = OK f × OK g
  OK (lcase f g)  = OK f × OK g
  OK (lcata F alg) = OK alg
  OK (liter f φ)  = OK f
  OK (lend b)     = OK b
  OK (blift f)    = OK f
  OK (bfst f)     = OK f
  OK (bsnd f)     = OK f
  OK (bcaseE f g) = OK f × OK g
  OK (bout f)     = OK f
  OK (llam b γ)   = OK b
  OK (llamω b γ)  = OK b
  OK (lop s)      = D s
  {-# CATCHALL #-}
  OK _            = ⊤

  private
    either : ∀ {s : Sig} xs {ys} → s ∈ xs ++ ys → (s ∈ xs → D s) → (s ∈ ys → D s) → D s
    either xs m l r = go (∈-++⁻ xs m)
      where
        go : _ → _
        go (inj₁ a) = l a
        go (inj₂ b) = r b

  -- ★ the ops a term's code names satisfy `D`
  ok-ps : ∀ {Γ} (ds : Defs Γ) {E A B} (t : Tm Γ E A B) → OK t → ∀ {s} → s ∈ ps (tmGot ds t) → D s
  ok-ps ds (f ∘l g)      (of , og) m = either (ps (tmGot ds f)) m (ok-ps ds f of) (ok-ps ds g og)
  ok-ps ds (f ⊗l g)      (of , og) m = either (ps (tmGot ds f)) m (ok-ps ds f of) (ok-ps ds g og)
  ok-ps ds (lcase f g)   (of , og) m = either (ps (tmGot ds f)) m (ok-ps ds f of) (ok-ps ds g og)
  ok-ps ds (lcata F alg) o         m = ok-ps ds alg o m
  ok-ps ds (liter f φ)   o         m = ok-ps ds f o m
  ok-ps ds (lend b)      o         m = ok-ps ds b o m
  ok-ps ds (blift f)     o         m = ok-ps ds f o m
  ok-ps ds (bfst f)      o         m = ok-ps ds f o m
  ok-ps ds (bsnd f)      o         m = ok-ps ds f o m
  ok-ps ds (bcaseE f g)  (of , og) m = either (ps (tmGot ds f)) m (ok-ps ds f of) (ok-ps ds g og)
  ok-ps ds (bout f)      o         m = ok-ps ds f o m
  ok-ps ds (llam b γ)    o         m = ok-ps ds b o m
  ok-ps ds (llamω b γ)   o         m = ok-ps ds b o m
  ok-ps ds (lop s)       o (here refl) = o
  ok-ps ds lid       o ()
  ok-ps ds ρl        o ()
  ok-ps ds ρl⁻       o ()
  ok-ps ds lul       o ()
  ok-ps ds lul⁻      o ()
  ok-ps ds lassoc    o ()
  ok-ps ds lassoc⁻   o ()
  ok-ps ds lswap     o ()
  ok-ps ds dup       o ()
  ok-ps ds drop      o ()
  ok-ps ds linl      o ()
  ok-ps ds linr      o ()
  ok-ps ds lzero     o ()
  ok-ps ds lIn       o ()
  ok-ps ds lOutμ     o ()
  ok-ps ds (lclo F p) o ()
  ok-ps ds (lapp p)  o ()
  ok-ps ds bcopy     o ()
  ok-ps ds (bapp p)  o ()
  ok-ps ds lev       o ()
  ok-ps ds bev       o ()
  ok-ps ds lunf      o ()
  ok-ps ds lout      o ()
  ok-ps ds (lconst v) o ()

  -- a table each of whose bodies is OK
  data DefsOK : ∀ {Γ} → Defs Γ → Set where
    ε   : DefsOK ε
    _▸₁_ : ∀ {Γ g X A B} {ds : Defs Γ} {b : LTm Γ (X ⊗t A) B} {γ : Gd g b} → DefsOK ds → OK b → DefsOK (ds ▸ b1 b γ)
    _▸ω_ : ∀ {Γ g X A B} {ds : Defs Γ} {b : Tm Γ X A B} {γ : Gd g b} → DefsOK ds → OK b → DefsOK (ds ▸ bω b γ)

  defs-ok : ∀ {Γ} (ds : Defs Γ) → DefsOK ds → ∀ {s} → s ∈ ps (defsGot ds) → D s
  defs-ok ε ε ()
  defs-ok (ds ▸ b1 b γ) (od ▸₁ ob) m = either (ps (defsGot ds)) m (defs-ok ds od) (ok-ps ds b ob)
  defs-ok (ds ▸ bω b γ) (od ▸ω ob) m = either (ps (defsGot ds)) m (defs-ok ds od) (ok-ps ds b ob)

  -- ★ a program's universe's ops
  univ-ok : ∀ {Γ} (ds : Defs Γ) {E A B} (f : Tm Γ E A B) → DefsOK ds → OK f → ∀ {s} → s ∈ ops (univ ds f) → D s
  univ-ok ds f od of m = either (ps (defsGot ds)) m (defs-ok ds od) (ok-ps ds f of)

------------------------------------------------------------------------
-- 2. ★ THE BRIDGE'S OPS are its IR's SigOp leaves (and the halting
-- `unlinked`, which owes nothing): a linked expression's bridge is OK.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (subst; subst₂)
open import Once.Contract using (ISig)
open import Once.Denotation.Program using (Declared; Leaves)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open import Once.LinCore.FromIR fmt using (⟪⌊⌋⟫-flat)
import Once.IR as M
open import Once.IRTy using (IRTy)
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_; _⊑ᵘ_; _⊑∷_)
open import Once.Context using (z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
import Once.Spec.Grade as G
import Data.Fin
open import Once.LinCore.FromExpr fmt
  using (weak; split; carryL; mixL; var-at; bindL; apω; dist; cast)
open import Once.LinCore.PassTr fmt using (copyIn)

module Ops (Σι : ISig) where
  Dc : Sig → Set
  Dc s = Declared Σι (info s)

  ok-cast : ∀ {L E A A′ B B′} (p : A ≡ A′) (q : B ≡ B′) {t : Tm L E A B} → OK Dc t → OK Dc (cast p q t)
  ok-cast refl refl o = o

  ok-weak : ∀ {L E m n} {Γ : Ctx m n} {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′) → OK Dc (weak {L} {E} {Γ = Γ} p)
  ok-weak {Γ = SC.∅}       []         = tt
  ok-weak {Γ = Γ SC.▸ A} (z≤z ⊑∷ p) = ok-weak {Γ = Γ} p
  ok-weak {Γ = Γ SC.▸ A} (z≤o ⊑∷ p) = tt , (ok-weak {Γ = Γ} p , tt)
  ok-weak {Γ = Γ SC.▸ A} (z≤m ⊑∷ p) = tt , (ok-weak {Γ = Γ} p , tt)
  ok-weak {Γ = Γ SC.▸ A} (o≤o ⊑∷ p) = ok-weak {Γ = Γ} p , tt
  ok-weak {Γ = Γ SC.▸ A} (o≤m ⊑∷ p) = ok-weak {Γ = Γ} p , tt
  ok-weak {Γ = Γ SC.▸ A} (m≤m ⊑∷ p) = ok-weak {Γ = Γ} p , tt

  ok-split : ∀ {L E m n} (Γ : Ctx m n) (Ψ₁ Ψ₂ : Usage n) → OK Dc (split {L} {E} Γ Ψ₁ Ψ₂)
  ok-split SC.∅          []          []          = tt
  ok-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Zero ∷ Ψ₂) = ok-split Γ Ψ₁ Ψ₂
  ok-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.One  ∷ Ψ₂) = tt , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.Zero ∷ Ψ₁) (G.Many ∷ Ψ₂) = tt , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Zero ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Zero ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.One  ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.One  ∷ Ψ₁) (G.Many ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.One  ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)
  ok-split (Γ SC.▸ A) (G.Many ∷ Ψ₁) (G.Many ∷ Ψ₂) = _ , (ok-split Γ Ψ₁ Ψ₂ , tt)

  ok-var : ∀ {L E m n} {Γ : Ctx m n} (i : Data.Fin.Fin n) → OK Dc (var-at {L} {E} {Γ = Γ} i)
  ok-var {Γ = Γ SC.▸ A} Data.Fin.zero    = _
  ok-var {Γ = Γ SC.▸ A} (Data.Fin.suc i) = ok-var {Γ = Γ} i

  ok-bind : ∀ {L E m n} {Γ : Ctx m n} {Ψ : Usage n} {A} (q : G.Quantity) → OK Dc (bindL {L} {E} {Γ = Γ} {Ψ} {A} q)
  ok-bind G.Zero = _
  ok-bind G.One  = tt
  ok-bind G.Many = tt

  open import Once.LinCore.FromExpr fmt
    using (ty; Rs; Lq; castΦ; opL; numL; sigL; mapT; callM; refL; coeL; coeR; clo; wrap; wrap₀; layerEq)
  open import Once.Surface.Elaborate using (elaborate; numIR; sigOpIR)
  open import Once.TypeCheck.Table using (mapIR)
  open import Once.Surface.Map
    using (Map; mp-id; mp-fst; mp-snd; mp-terminal; mp-inl; mp-inr; mp-initial; mp-apply; mp-In; mp-Out; mp-toFloat)
  open import Once.Surface.CoerceIR using (coeIR)
  open import Once.Spec.Sub using (_<:_; sub-void; sub-var; sub-unit; sub-int; sub-float; sub-arr; sub-*; sub-+; sub-μ; sub-ν)
  open import Once.Spec.Type using (Ty; Type; _⇒[_]_)
  import Once.Spec.Type as ST
  import Once.Spec.Theory as Th
  open import Once.Spec.Theory using (Has; Sym)
  open import Once.Type.Concrete using (IsConcrete; con-base; con-fun)
  open import Once.Arith.SigOp.Builders using (numInfo; value-info; arrow-info)
  open import Once.Spec.Name using (CanonicalName)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Product using (Σ; proj₁)
  open import Relation.Binary.PropositionalEquality using (sym; cong)
  open import Relation.Nullary using (Dec; yes; no)
  open import Once.Surface.CoerceIR using (VoidFree; erase-eq)
  open import Once.Arith.SigOp.Builders using (i2f-info)
  open import Once.Adequacy.ElaborateLinked using (DeclIn; sigOpIR-linked)
  open import Once.Denotation.Program using (Linked)
  open import Once.IRTy using (⌊_⌋)
  import Once.IRTy as I
  open import Once.LinCore.FromIR fmt using (⟪_⟫; grade)

  ok-opL : ∀ {L E A B} (si : SigOpInfo A B) → Declared Σι si → OK Dc (opL {L} {E} si)
  ok-opL {L} {E} si d = ok-cast {L} {E} (Relation.Binary.PropositionalEquality.sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si)))
                                   (Relation.Binary.PropositionalEquality.sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si)))
                                   {t = lop (sig si)} d

  ok-apω : ∀ {L E g A B} → OK Dc (apω {L} {E} {g} {A} {B})
  ok-apω = _

  ok-dist : ∀ {L E X A B} → OK Dc (dist {L} {E} {X} {A} {B})
  ok-dist = _

  ok-callM : ∀ {L g A B} (r : Maybe (Σ ℕ λ l → L ∋[ l ] sg once g One A B)) → OK Dc (callM r)
  ok-callM (just (l , p)) = _
  ok-callM nothing        = _

  module _ {I : Set} {C : I → CanonicalName → IRTy → IRTy → Set} {i : I} where
    Lv : ∀ {A B} → M.IR A B → Set
    Lv = Leaves C i (Declared Σι)

    ok-numL : ∀ {L E m A U k} (h : Has A U) (o : Sym U k) → Lv (numIR {m} h o) → OK Dc (numL {L} {E} {m} h o)
    ok-numL {L} {E} {A = Th.int} {k = Th.unary} h o d = ok-opL {L} {E} (numInfo h o) d
    ok-numL {L} {E} {A = Th.int} {k = Th.binary} h o d = ok-opL {L} {E} (numInfo h o) d
    ok-numL {L} {E} {A = Th.int} {k = Th.compare} h o d = ok-opL {L} {E} (numInfo h o) d
    ok-numL {L} {E} {A = Th.float} {k = Th.unary} h o d = ok-opL {L} {E} (numInfo h o) d
    ok-numL {L} {E} {A = Th.float} {k = Th.binary} h o d = ok-opL {L} {E} (numInfo h o) d
    ok-numL {L} {E} {A = Th.float} {k = Th.compare} h o d = ok-opL {L} {E} (numInfo h o) d

  -- a closure runs its body's ops
  -- (stated at `OK (copyIn b)`'s normal form, so `b` is never inferred
  -- through `OK`, which is not injective)
  ok-copyIn : ∀ {P : Set} → P → P × ((⊤ × ⊤) × ⊤)
  ok-copyIn ob = ob , _

  -- a structure map runs none but `toFloat`'s
  ok-mapT : ∀ {L m} {A B : Ty m} (mp : Map A B) → Linked [] [] (mapIR mp) → OK Dc (mapT {L} mp)
  ok-mapT mp-id                         l = tt
  ok-mapT mp-fst                        l = _
  ok-mapT mp-snd                        l = _
  ok-mapT mp-terminal                   l = tt
  ok-mapT mp-inl                        l = tt
  ok-mapT mp-inr                        l = tt
  ok-mapT mp-initial                    l = tt
  ok-mapT (mp-apply A B (G.fin G.pureᶠ)) l = _
  ok-mapT (mp-apply A B (G.fin G.actᶠ))  l = ok-copyIn (_ , tt)
  ok-mapT (mp-apply A B G.eff)          l = ok-copyIn (_ , tt)
  ok-mapT {L} (mp-In F w)               l = ok-cast {L} (sym (layerEq F w (ST.μ F))) refl {t = lIn} tt
  ok-mapT {L} (mp-Out F G.pureᶠ w)      l = ok-cast {L} refl (sym (layerEq F w (ST.ν F G.pureᶠ))) {t = lout} tt
  ok-mapT {L} (mp-Out F G.actᶠ w)       l = ok-copyIn (ok-cast {L} refl (sym (layerEq F w (ST.ν F G.actᶠ))) {t = lout} tt , tt)
  ok-mapT {L} mp-toFloat                l = ok-opL {L} {One} i2f-info tt

  -- a conversion runs none
  ok-coeL : ∀ {L m} {A B : Ty m} (p : A <: B) → OK Dc (coeL {L} p)
  ok-coeL sub-void   = tt
  ok-coeL sub-unit   = tt
  ok-coeL sub-int    = tt
  ok-coeL sub-float  = tt
  ok-coeL (sub-arr {q = G.Zero} a b r) = ok-copyIn (ok-coeL b , _)
  ok-coeL (sub-arr {q = G.One}  a b r) = ok-copyIn (ok-coeL b , (_ , (tt , ok-coeL a)))
  ok-coeL (sub-arr {q = G.Many} a b r) = ok-copyIn (ok-coeL b , (_ , (tt , ok-coeL a)))
  ok-coeL (sub-* a b) = ok-coeL a , ok-coeL b
  ok-coeL (sub-+ a b) = (tt , ok-coeL a) , (tt , ok-coeL b)
  ok-coeL sub-μ      = tt
  ok-coeL (sub-ν _)  = tt
  ok-coeL sub-var    = tt

  ok-coeR : ∀ {L m Z} {A B : Ty m} (p : A <: B) (d : Dec (VoidFree p)) {t : LTm L Z (ty A)} → OK Dc t → OK Dc (coeR p d t)
  ok-coeR p (yes vf) o = ok-cast refl (cong ⟪_⟫ (erase-eq p vf)) o
  ok-coeR p (no _)   o = ok-coeL p , o

  -- a reference runs none (a miss halts by the unlinked op, which owes nothing)
  ok-refL : ∀ {L} (rs : Rs L) {m} (T : Ty m) (f : CanonicalName) → OK Dc (refL rs T f)
  ok-refL rs (A ⇒[ G.mk-kind G.Zero π ] B) f = ok-copyIn (ok-callM (rs f I.Unit ⌊ B ⌋ (grade π)) , _)
  ok-refL rs (A ⇒[ G.mk-kind G.One π ] B) f  = ok-copyIn (ok-callM (rs f ⌊ A ⌋ ⌊ B ⌋ (grade π)) , _)
  ok-refL rs (A ⇒[ G.mk-kind G.Many π ] B) f = ok-copyIn (ok-callM (rs f ⌊ A ⌋ ⌊ B ⌋ (grade π)) , _)
  ok-refL rs T@ST.Unit      f = ok-callM (rs f I.Unit ⌊ T ⌋ act) , tt
  ok-refL rs T@ST.Void      f = ok-callM (rs f I.Unit ⌊ T ⌋ act) , tt
  ok-refL rs T@(_ ST.* _)   f = ok-callM (rs f I.Unit ⌊ T ⌋ act) , tt
  ok-refL rs T@(_ ST.+ _)   f = ok-callM (rs f I.Unit ⌊ T ⌋ act) , tt
  ok-refL rs T@(ST.μ _)     f = ok-callM (rs f I.Unit ⌊ T ⌋ act) , tt
  ok-refL rs T@(ST.ν _ _)   f = ok-callM (rs f I.Unit ⌊ T ⌋ act) , tt
  ok-refL rs T@ST.Int       f = ok-callM (rs f I.Unit ⌊ T ⌋ act) , tt
  ok-refL rs T@ST.Float     f = ok-callM (rs f I.Unit ⌊ T ⌋ act) , tt
  ok-refL rs T@(ST.var _)   f = ok-callM (rs f I.Unit ⌊ T ⌋ act) , tt

  -- ★ a declared FFI reference: its op is the one `elaborate` links
  -- (`ElaborateLinked.sigOpIR-linked`)
  ok-sigL : ∀ {L} (A : ST.Type) (name : CanonicalName) (c : IsConcrete A) → DeclIn Σι name A → OK Dc (sigL {L} A name c)
  ok-sigL (Dom ⇒[ G.mk-kind G.Zero (G.fin G.pureᶠ) ] Cod) name c@(con-fun bDom cCod) d =
    ok-copyIn (ok-opL (value-info name ST.b-Unit cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL (Dom ⇒[ G.mk-kind G.Zero G.eff ] Cod) name c@(con-fun bDom cCod) d =
    ok-copyIn (ok-opL (arrow-info (G.mk-kind G.Zero G.eff) name ST.b-Unit cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL (Dom ⇒[ G.mk-kind G.Zero (G.fin G.actᶠ) ] Cod) name c@(con-fun bDom cCod) d =
    ok-copyIn (ok-opL (arrow-info (G.mk-kind G.Zero G.act) name ST.b-Unit cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL (Dom ⇒[ G.mk-kind G.One π ] Cod) name c@(con-fun bDom cCod) d =
    ok-copyIn (ok-opL (arrow-info (G.mk-kind G.One π) name bDom cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL (Dom ⇒[ G.mk-kind G.Many π ] Cod) name c@(con-fun bDom cCod) d =
    ok-copyIn (ok-opL (arrow-info (G.mk-kind G.Many π) name bDom cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL _ name (con-base (ST.b-var {i = ()} _)) d
  ok-sigL {L} _ name c@(con-base ib@ST.b-Unit) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@ST.b-Void) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@ST.b-Int) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@ST.b-Float) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@(ST.b-* a b)) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@(ST.b-+ a b)) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
