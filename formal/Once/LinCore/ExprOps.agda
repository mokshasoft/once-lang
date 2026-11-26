-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ExprOps — plan 0.146 B1.7 (D450 at the bridge): the bridge's
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
open import Once.LinCore.Flat using (Base)
open import Once.IR.Semantics.Trace using (T)
open Sig using (info)
open import Once.LinCore.Keys fmt bw using (ps; tmGot; defsGot; univ; module Univ)
open Univ using (ops)

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
  OK (llamωᶜ b₀ γ) = OK b₀
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
  ok-ps ds (llamω b γ)   o         m = either (ps (tmGot ds b)) m (ok-ps ds b o) (λ ())
  ok-ps ds (llamωᶜ b₀ γ) o         m = either (ps (tmGot ds b₀)) m (ok-ps ds b₀ o) (λ ())
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
  ok-ps ds levω      o ()
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
open import Once.Arith.SigOp.AsBlock using (as-block; Canonical; as-block-canonical)
open import Once.Arith.SigOp.AsBlockSound using (as-block-declared)
open import Once.LinCore.FromIR fmt using (⟪⌊⌋⟫-flat)
import Once.IR as M
open import Once.IRTy using (IRTy)
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_; _⊑ᵘ_; _⊑∷_)
open import Once.Context using (z≤z; z≤o; z≤m; o≤o; o≤m; m≤m)
import Once.Context
import Once.Spec.Grade as G
import Data.Fin
open import Once.LinCore.FromExpr fmt
  using (weak; split; carryL; mixL; var-at; bindL; apω; dist; cast;
         Pth; p-var; p-fst; p-snd; p-mfst; p-msnd; Rd; rd-path; rd-int; rd-float; rd-num; rd-pair; rd-coe; coeRd; rd?; rdw?; lv; Rp; Rt; lentS; scrutL; pairL; scrutA; appL; cp?; CP; cp)
open import Once.LinCore.PassTr fmt using (copyIn)

module Ops (Σι : ISig) where
  -- declared (D450), and canonical: a block named by its digest, a
  -- primitive a comparison (D464: the image's arith table)
  Dc : Sig → Set
  Dc s = Declared Σι (info s) × Canonical (info s)

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
  open import Once.LinCore.FromExpr fmt using (Co)
  import Once.Surface.Syntax as S
  open import Once.Denotation.SurfaceRefs using (Refs)
  open import Once.Surface.CoerceIR using (voidFree?)
  open import Once.Surface.Properties using (erase-arg-usage)
  open import Once.Context using (_⊔ᵘ_; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many; ⊑ᵘ-⊔ˡ; ⊑ᵘ-⊔ʳ; ⊑ᵘ-+ʳ)
  open import Once.Spec.Context using (_*ᵘ_; zeroUsage)
  open import Once.Spec.Name using (bare)
  open import Once.IRTy using (⌊wk₀⌋)

  ok-opL : ∀ {L E A B} (si : SigOpInfo A B) → Declared Σι si → OK Dc (opL {L} {E} si)
  ok-opL {L} {E} si d = ok-cast {L} {E} (Relation.Binary.PropositionalEquality.sym (⟪⌊⌋⟫-flat (SigOpInfo.baseA si)))
                                   (Relation.Binary.PropositionalEquality.sym (⟪⌊⌋⟫-flat (SigOpInfo.conB si)))
                                   {t = lop (sig (as-block si))} (as-block-declared Σι si d , as-block-canonical si)

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

  -- a closure runs its body's ops (`OK (llamωᶜ b₀ γ) = OK b₀`, D480; stated
  -- over a plain `P`, so `b₀` is never inferred through `OK`, which is not injective)
  ok-clo : ∀ {P : Set} → P → P
  ok-clo ob = ob

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
  ok-mapT (mp-apply A B (G.fin G.actᶠ))  l = ok-clo (_ , tt)
  ok-mapT (mp-apply A B G.eff)          l = ok-clo (_ , tt)
  ok-mapT {L} (mp-In F w)               l = ok-cast {L} (sym (layerEq F w (ST.μ F))) refl {t = lIn} tt
  ok-mapT {L} (mp-Out F G.pureᶠ w)      l = ok-cast {L} refl (sym (layerEq F w (ST.ν F G.pureᶠ))) {t = lout} tt
  ok-mapT {L} (mp-Out F G.actᶠ w)       l = ok-clo (ok-cast {L} refl (sym (layerEq F w (ST.ν F G.actᶠ))) {t = lout} tt , tt)
  ok-mapT {L} mp-toFloat                l = ok-opL {L} {One} i2f-info tt

  -- a conversion runs none
  ok-coeL : ∀ {L m} {A B : Ty m} (p : A <: B) → OK Dc (coeL {L} p)
  ok-coeL sub-void   = tt
  ok-coeL sub-unit   = tt
  ok-coeL sub-int    = tt
  ok-coeL sub-float  = tt
  ok-coeL (sub-arr {q = G.Zero} a b r) = ok-clo (ok-coeL b , _)
  ok-coeL (sub-arr {q = G.One}  a b r) = ok-clo (ok-coeL b , (_ , (tt , ok-coeL a)))
  ok-coeL (sub-arr {q = G.Many} a b r) = ok-clo (ok-coeL b , (_ , (tt , ok-coeL a)))
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
  ok-refL rs (A ⇒[ G.mk-kind G.Zero π ] B) f = ok-clo (ok-callM (rs f I.Unit ⌊ B ⌋ (grade π)) , _)
  ok-refL rs (A ⇒[ G.mk-kind G.One π ] B) f  = ok-clo (ok-callM (rs f ⌊ A ⌋ ⌊ B ⌋ (grade π)) , _)
  ok-refL rs (A ⇒[ G.mk-kind G.Many π ] B) f = ok-clo (ok-callM (rs f ⌊ A ⌋ ⌊ B ⌋ (grade π)) , _)
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
    ok-clo (ok-opL (value-info name ST.b-Unit cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL (Dom ⇒[ G.mk-kind G.Zero G.eff ] Cod) name c@(con-fun bDom cCod) d =
    ok-clo (ok-opL (arrow-info (G.mk-kind G.Zero G.eff) name ST.b-Unit cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL (Dom ⇒[ G.mk-kind G.Zero (G.fin G.actᶠ) ] Cod) name c@(con-fun bDom cCod) d =
    ok-clo (ok-opL (arrow-info (G.mk-kind G.Zero G.act) name ST.b-Unit cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL (Dom ⇒[ G.mk-kind G.One π ] Cod) name c@(con-fun bDom cCod) d =
    ok-clo (ok-opL (arrow-info (G.mk-kind G.One π) name bDom cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL (Dom ⇒[ G.mk-kind G.Many π ] Cod) name c@(con-fun bDom cCod) d =
    ok-clo (ok-opL (arrow-info (G.mk-kind G.Many π) name bDom cCod) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , _)
  ok-sigL _ name (con-base (ST.b-var {i = ()} _)) d
  ok-sigL {L} _ name c@(con-base ib@ST.b-Unit) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@ST.b-Void) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@ST.b-Int) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@ST.b-Float) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@(ST.b-* a b)) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt
  ok-sigL {L} _ name c@(con-base ib@(ST.b-+ a b)) d = ok-opL {L} {One} (value-info name ST.b-Unit ib) (proj₁ (sigOpIR-linked {tbl = []} {X = I.Unit} name c d)) , tt

  -- a numeric symbol is a primitive, which owes nothing (`Builders`: every
  -- numeric SigOp is internal)
  ok-numL′ : ∀ {L E m A U k} (h : Has A U) (o : Sym U k) → OK Dc (numL {L} {E} {m} h o)
  ok-numL′ {L} {E} {A = Th.int}   {k = Th.unary}   h o = ok-opL {L} {E} (numInfo h o) _
  ok-numL′ {L} {E} {A = Th.int}   {k = Th.binary}  h o = ok-opL {L} {E} (numInfo h o) _
  ok-numL′ {L} {E} {A = Th.int}   {k = Th.compare} h o = ok-opL {L} {E} (numInfo h o) _
  ok-numL′ {L} {E} {A = Th.float} {k = Th.unary}   h o = ok-opL {L} {E} (numInfo h o) _
  ok-numL′ {L} {E} {A = Th.float} {k = Th.binary}  h o = ok-opL {L} {E} (numInfo h o) _
  ok-numL′ {L} {E} {A = Th.float} {k = Th.compare} h o = ok-opL {L} {E} (numInfo h o) _

  -- ★ the bridge of an expression whose FFI references are declared runs
  -- only declared ops (calls owe nothing here: their bodies are the table's)
  module _ {L : Cx} (rs : Rs L) where
    ok-castΦ : ∀ {m n} {Γ : Ctx m n} {Φ Φ′ : Usage n} {B} (e : Φ ≡ Φ′) {t : LTm L (Co Γ Φ) B} → OK Dc t → OK Dc (castΦ rs {Γ = Γ} e t)
    ok-castΦ refl o = o

    DRefs : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} → S.Expr Γ Ψ A → Set
    DRefs = Refs (DeclIn Σι) (λ _ _ → ⊤) (λ _ _ → ⊤)

    -- ★ D477: a scrutinee read in place runs only `numL`'s ops
    ok-lv : ∀ {m n} {Γ : Ctx m n} {Φ : Usage n} {C} (i : Data.Fin.Fin n) (q : SC.singleUse i G.One ⊑ᵘ Φ) {t : Tm L _ One C}
          → OK Dc t → OK Dc (lv {L} {Γ = Γ} i q t)
    ok-lv {Γ = Γ SC.▸ A} Data.Fin.zero    (o≤o ⊑∷ q) o = o
    ok-lv {Γ = Γ SC.▸ A} Data.Fin.zero    (o≤m ⊑∷ q) o = o
    ok-lv {Γ = Γ SC.▸ A} (Data.Fin.suc i) (z≤z ⊑∷ q) o = ok-lv {Γ = Γ} i q o
    ok-lv {Γ = Γ SC.▸ A} (Data.Fin.suc i) (z≤o ⊑∷ q) o = ok-lv {Γ = Γ} i q o
    ok-lv {Γ = Γ SC.▸ A} (Data.Fin.suc i) (z≤m ⊑∷ q) o = ok-lv {Γ = Γ} i q o

    ok-Rp : ∀ {m n} {Γ : Ctx m n} {Ψ Φ : Usage n} {A : Ty m} {C} {e : S.Expr Γ Ψ A} (d : Pth e) (q : Ψ ⊑ᵘ Φ) {t : Tm L _ One C}
          → OK Dc t → OK Dc (Rp {L} d q t)
    ok-Rp {Γ = Γ} (p-var i) q o = ok-lv {Γ = Γ} i q o
    ok-Rp (p-fst d) q o = ok-Rp d q o
    ok-Rp (p-snd d) q o = ok-Rp d q o
    ok-Rp (p-mfst d) q o = ok-Rp d _ o
    ok-Rp (p-msnd d) q o = ok-Rp d _ o

    ok-Rt : ∀ {m n} {Γ : Ctx m n} {Ψ Φ : Usage n} {A : Ty m} {e : S.Expr Γ Ψ A} (d : Rd e) (q : Ψ ⊑ᵘ Φ) → OK Dc (Rt {L} {Γ = Γ} d q)
    ok-Rt (rd-path d) q = ok-Rp d q tt
    ok-Rt (rd-int z) q = tt
    ok-Rt (rd-float d) q = tt
    ok-Rt (rd-num h o d) q = ok-numL′ h o , ok-Rt d q
    ok-Rt (rd-coe c d) q = ok-coeRd c (voidFree? c) (ok-Rt d q)
      where
        ok-coeRd : ∀ {m X} {A B : Ty m} (c : A <: B) (dc : Dec (VoidFree c)) {t : Tm L X One _}
                 → OK Dc t → OK Dc (coeRd {L} c dc t)
        ok-coeRd c (yes vf) o = ok-cast refl (cong ⟪_⟫ (erase-eq c vf)) o
        ok-coeRd c (no _)   o = ok-coeL c , o
    ok-Rt (rd-pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} da db) q =
      (ok-Rt da (⊑ᵘ-trans (Once.Context.⊑ᵘ-+ˡ Ψ₁ Ψ₂) q) , ok-Rt db (⊑ᵘ-trans (⊑ᵘ-+ʳ Ψ₁ Ψ₂) q)) , tt

    ok-scrutL : ∀ {m n} {Γ : Ctx m n} {Ψs Φ : Usage n} {S : Ty m} (s : S.Expr Γ Ψs S) (d : Maybe (Rd s))
              → OK Dc (Lq rs s) → OK Dc (scrutL rs {Γ = Γ} {Φ = Φ} s d)
    ok-scrutL {Γ = Γ} {Ψs} {Φ} s nothing  o = (tt , o) , (tt , ok-split Γ Ψs Φ)
    ok-scrutL {Γ = Γ} {Ψs} {Φ} s (just d) o =
      (ok-weak {Γ = Γ} (⊑ᵘ-+ʳ Ψs Φ) , tt) , (ok-Rt d (Once.Context.⊑ᵘ-+ˡ Ψs Φ) , tt)

    ok-pairL : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (a : S.Expr Γ Ψ₁ A) (b : S.Expr Γ Ψ₂ B) (d : Maybe (Rd a))
             → OK Dc (Lq rs a) → OK Dc (Lq rs b) → OK Dc (pairL rs {Γ = Γ} a b d)
    ok-pairL {Γ = Γ} {Ψ₁} {Ψ₂} a b nothing  oa ob = (oa , ob) , ok-split Γ Ψ₁ Ψ₂
    ok-pairL {Γ = Γ} {Ψ₁} {Ψ₂} a b (just d) oa ob =
      (tt , ob) , (tt , ((ok-weak {Γ = Γ} (⊑ᵘ-+ʳ Ψ₁ Ψ₂) , tt) , (ok-Rt d (Once.Context.⊑ᵘ-+ˡ Ψ₁ Ψ₂) , tt)))

    ok-Lq : ∀ {m n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (e : S.Expr Γ Ψ A) → DRefs e → OK Dc (Lq rs e)

    -- D481 B1: an argument as a scrutinee, and an application at `Many` (a branch where `appL` makes one)
    ok-scrutA : ∀ {m n} {Γ : Ctx m n} {Φ Ψs : Usage n} {S : Ty m} (s : S.Expr Γ Ψs S) (d : Maybe (Rd s))
              → OK Dc (Lq rs s) → OK Dc (scrutA rs {Γ = Γ} {Φ = Φ} s d)
    ok-scrutA {Γ = Γ} {Φ} {Ψs} s nothing  o = (tt , (o , ok-weak {Γ = Γ} (⊑ᵘ-*Many Ψs))) , ok-split Γ Φ (G.Many *ᵘ Ψs)
    ok-scrutA {Γ = Γ} {Φ} {Ψs} s (just d) o =
      (ok-weak {Γ = Γ} (Once.Context.⊑ᵘ-+ˡ Φ (G.Many *ᵘ Ψs)) , tt) , (ok-Rt d (⊑ᵘ-trans (⊑ᵘ-*Many Ψs) (⊑ᵘ-+ʳ Φ (G.Many *ᵘ Ψs))) , tt)

    ok-appL : ∀ {m n} {Γ : Ctx m n} {Ψ₁ Ψ₂ : Usage n} {A B : Ty m} (f : S.Expr Γ Ψ₁ (A ST.⇒[ G.mk-kind G.Many G.pure ] B)) (x : S.Expr Γ Ψ₂ A)
              (d : Maybe (CP f)) → DRefs f → DRefs x → OK Dc (appL rs {Γ = Γ} f x d)
    ok-Lq {Γ = Γ} (S.var i) r = ok-var {Γ = Γ} i
    ok-Lq (S.lam {q' = G.Zero} G.Zero _ e) r = ok-clo (ok-Lq e r , _)
    ok-Lq (S.lam {q' = G.Zero} G.One  _ e) r = ok-clo (ok-Lq e r , _)
    ok-Lq (S.lam {q' = G.Zero} G.Many _ e) r = ok-clo (ok-Lq e r , _)
    ok-Lq (S.lam {q' = G.One}  G.One  _ e) r = ok-clo (ok-Lq e r)
    ok-Lq (S.lam {q' = G.One}  G.Many _ e) r = ok-clo (ok-Lq e r)
    ok-Lq (S.lam {q' = G.Many} G.Many _ e) r = ok-clo (ok-Lq e r)
    ok-Lq {Γ = Γ} (S.app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} f x) (rf , rx) =
      ok-castΦ {Γ = Γ} (sym (erase-arg-usage Ψ₁ Ψ₂)) (_ , ((ok-Lq f rf , tt) , tt))
    ok-Lq {Γ = Γ} (S.app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} f x) (rf , rx) =
      _ , ((ok-Lq f rf , (ok-Lq x rx , ok-weak {Γ = Γ} (⊑ᵘ-*One Ψ₂))) , ok-split Γ Ψ₁ (G.One *ᵘ Ψ₂))
    ok-Lq {Γ = Γ} (S.app {q = G.Many} f x) (rf , rx) = ok-appL {Γ = Γ} f x (cp? f) rf rx
    ok-Lq {Γ = Γ} (S.effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} f x) (rf , rx) =
      ok-castΦ {Γ = Γ} (sym (erase-arg-usage Ψ₁ Ψ₂)) (ok-clo ((_ , ((ok-Lq f rf , tt) , tt)) , tt))
    ok-Lq {Γ = Γ} (S.effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} f x) (rf , rx) =
      ok-clo ((_ , ((ok-Lq f rf , (ok-Lq x rx , ok-weak {Γ = Γ} (⊑ᵘ-*One Ψ₂))) , ok-split Γ Ψ₁ (G.One *ᵘ Ψ₂))) , tt)
    ok-Lq {Γ = Γ} (S.effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} f x) (rf , rx) =
      ok-clo ((_ , ((ok-Lq f rf , (ok-Lq x rx , ok-weak {Γ = Γ} (⊑ᵘ-*Many Ψ₂))) , ok-split Γ Ψ₁ (G.Many *ᵘ Ψ₂))) , tt)
    ok-Lq {Γ = Γ} (S.pair a b) (ra , rb) = ok-pairL {Γ = Γ} a b (rdw? a) (ok-Lq a ra) (ok-Lq b rb)
    ok-Lq (S.fst' p) r = _ , ok-Lq p r
    ok-Lq (S.snd' p) r = _ , ok-Lq p r
    ok-Lq (S.inl' a) r = tt , ok-Lq a r
    ok-Lq (S.inr' b) r = tt , ok-Lq b r
    ok-Lq {Γ = Γ} (S.case' {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} {qℓ = qℓ} {qr = qr} {A = A} {B = B} s l r′) (rs′ , rl , rr) =
      ((ok-Lq l rl , (ok-bind {Γ = Γ} {A = A} qℓ , (ok-weak {Γ = Γ} (⊑ᵘ-⊔ˡ Ψₗ Ψᵣ) , tt))) ,
       (ok-Lq r′ rr , (ok-bind {Γ = Γ} {A = B} qr , (ok-weak {Γ = Γ} (⊑ᵘ-⊔ʳ Ψₗ Ψᵣ) , tt)))) ,
      (_ , ok-scrutL {Γ = Γ} {Φ = Ψₗ ⊔ᵘ Ψᵣ} s (rdw? s) (ok-Lq s rs′))
    ok-Lq S.unit r = tt
    ok-Lq (S.absurd v) r = tt , ok-Lq v r
    ok-Lq {Γ = Γ} (S.let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Zero} e1 e2) (r1 , r2) =
      ok-castΦ {Γ = Γ} (sym (erase-arg-usage Ψ₂ Ψ₁)) (ok-Lq e2 r2)
    ok-Lq {Γ = Γ} (S.let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.One} {A = A} e1 e2) (r1 , r2) =
      ok-Lq e2 r2 , (tt , ((tt , (ok-Lq e1 r1 , ok-weak {Γ = Γ} (⊑ᵘ-*One Ψ₁))) , ok-split Γ Ψ₂ (G.One *ᵘ Ψ₁)))
    ok-Lq {Γ = Γ} (S.let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = G.Many} {A = A} e1 e2) (r1 , r2) =
      ok-Lq e2 r2 , (tt , ((tt , (ok-Lq e1 r1 , ok-weak {Γ = Γ} (⊑ᵘ-*Many Ψ₁))) , ok-split Γ Ψ₂ (G.Many *ᵘ Ψ₁)))
    ok-Lq (S.int n) r = tt , tt
    ok-Lq (S.float d) r = tt , tt
    ok-Lq (S.num h o e) r = ok-numL′ h o , ok-Lq e r
    ok-Lq (S.coerce p f) r = ok-coeR p (voidFree? p) (ok-Lq f r)
    ok-Lq (S.sigOp {A = A} name c) r = ok-cast refl (cong ⟪_⟫ (sym (⌊wk₀⌋ A))) {t = sigL A name c ∘l drop} (ok-sigL A name c r , tt)
    ok-Lq {A = A} (S.closure name) r = ok-refL rs A (bare name) , tt
    ok-Lq {A = A} (S.poly name _) r = ok-refL rs A (bare name) , tt
    ok-Lq (S.closed e) r = ok-Lq e r , tt
    ok-Lq (S.lift-morphism mp) r = ok-clo (ok-mapT mp r , _)
    ok-Lq {Γ = Γ} (S.morph-app {Ψ = Ψ} mp x) (rm , rx) =
      ok-mapT mp rm , (ok-Lq x rx , ok-weak {Γ = Γ} (⊑ᵘ-trans (⊑ᵘ-*Many Ψ) (⊑ᵘ-+ʳ zeroUsage (G.Many *ᵘ Ψ))))
    ok-Lq {Γ = Γ} (S.comp' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) (rf , rg) =
      _ , ((ok-Lq f rf , (ok-Lq g rg , ok-weak {Γ = Γ} (⊑ᵘ-*Many Ψ₂))) , ok-split Γ Ψ₁ (G.Many *ᵘ Ψ₂))
    ok-Lq {Γ = Γ} (S.copair' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) (rf , rg) =
      _ , ((ok-Lq f rf , ok-Lq g rg) , ok-split Γ Ψ₁ Ψ₂)
    ok-Lq {Γ = Γ} (S.fork' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) (rf , rg) =
      ok-clo ((_ , _) , (_ , (tt , tt))) , ((ok-Lq f rf , ok-Lq g rg) , ok-split Γ Ψ₁ Ψ₂)
    ok-Lq (S.curry' f) r = ok-clo (ok-clo (_ , tt)) , ok-Lq f r
    ok-Lq {Γ = Γ} (S.cata {Ψ = Ψ} {F = F} {A = A} wfF alg) r =
      ok-cast (layerEq F wfF A) refl {t = bev} tt , (ok-Lq alg r , ok-weak {Γ = Γ} (⊑ᵘ-*Many Ψ))
    ok-Lq {Γ = Γ} (S.ana {Ψ = Ψ} {F = F} {A = A} wfF coalg) r =
      ok-clo (tt , (ok-cast refl (cong (Fn many act (ty A)) (layerEq F wfF A)) {t = lid} tt , tt)) , (ok-Lq coalg r , ok-weak {Γ = Γ} (⊑ᵘ-*Many Ψ))
    ok-Lq {Γ = Γ} (S.loop {Ψ = Ψ} round) r =
      _ , (ok-Lq round r , ok-weak {Γ = Γ} (⊑ᵘ-*Many Ψ))

    ok-appL {Γ = Γ} {Ψ₁} {Ψ₂} f x nothing rf rx =
      _ , ((ok-Lq f rf , (ok-Lq x rx , ok-weak {Γ = Γ} (⊑ᵘ-*Many Ψ₂))) , ok-split Γ Ψ₁ (G.Many *ᵘ Ψ₂))
    ok-appL {Γ = Γ} (S.copair' {Ψ₁ = Ψf} {Ψ₂ = Ψg} f g) x (just (cp _ _)) (rf , rg) rx =
      ((_ , ((ok-Lq f rf , ok-weak {Γ = Γ} (Once.Context.⊑ᵘ-+ˡ Ψf Ψg)) , tt)) , (_ , ((ok-Lq g rg , ok-weak {Γ = Γ} (⊑ᵘ-+ʳ Ψf Ψg)) , tt))) ,
      (_ , ok-scrutA {Γ = Γ} {Φ = Ψf SC.+ᵘ Ψg} x (rdw? x) (ok-Lq x rx))

------------------------------------------------------------------------
-- 3. ★ THE BRIDGE'S PROGRAM (`ExprBuild`): its table and its `main` run
-- only declared ops, so its universe's ops are declared (`FlatTop.ExprTop`'s
-- `decl`), when every definition's FFI references are.
------------------------------------------------------------------------

import Once.LinCore.ExprBuild
open import Once.CompileSrc using (CompiledSrc; module CompiledSrc; Src; src; module Src)
open import Once.Compile using (EffUU)

module Table (Σι : ISig) where
  open Ops Σι
  module ET = Once.LinCore.ExprBuild fmt
  open import Once.Spec.Sub using (_<:_; sub-arr; sub-unit; sub-void)
  open import Once.Spec.Type using (Type; _⇒[_]_)
  import Once.Spec.Type as ST
  import Once.Spec.Grade as G
  open import Once.Spec.Context using (Ctx; Usage; []; _∷_)
  import Once.Spec.Context as SC
  open import Once.Spec.Name using (bare)
  open import Once.Adequacy.ElaborateLinked using (DeclIn)
  open import Once.Denotation.SurfaceRefs using (Refs)
  open import Once.LinCore.FromExpr fmt using (ty; Rs; Lq)
  open import Once.LinCore.FromIR fmt using (⟪_⟫; grade)
  open import Once.IRTy using (⌊_⌋)
  import Once.IRTy as I
  open import Relation.Binary.PropositionalEquality using (cong)

  ok-eraseL : ∀ {L E m n} (Γ : Ctx m n) (Ψ : Usage n) → OK Dc (ET.eraseL {L} {E} Γ Ψ)
  ok-eraseL SC.∅          []           = tt
  ok-eraseL (Γ SC.▸ A) (G.Zero ∷ Ψ) = ok-eraseL Γ Ψ , _
  ok-eraseL (Γ SC.▸ A) (G.One  ∷ Ψ) = ok-eraseL Γ Ψ , tt
  ok-eraseL (Γ SC.▸ A) (G.Many ∷ Ψ) = ok-eraseL Γ Ψ , tt

  ok-dc : ∀ {L} (T : Type) (v : LTm L One (ty T)) → OK Dc v → OK Dc (ET.dc T v)
  ok-dc (A ⇒[ G.mk-kind G.Zero π ] B) v o = _ , ((o , tt) , tt)
  ok-dc (A ⇒[ G.mk-kind G.One π ] B)  v o = _ , ((o , tt) , tt)
  ok-dc (A ⇒[ G.mk-kind G.Many π ] B) v o = _ , ((o , tt) , tt)
  ok-dc ST.Unit       v o = o
  ok-dc ST.Void       v o = o
  ok-dc (X ST.* Y)    v o = o
  ok-dc (X ST.+ Y)    v o = o
  ok-dc (ST.μ F)      v o = o
  ok-dc (ST.ν F f)    v o = o
  ok-dc ST.Int        v o = o
  ok-dc ST.Float      v o = o
  ok-dc (ST.var ())   v o

  ok-val : ∀ {L T} (rs : Rs L) (s : Src T) → Refs (DeclIn Σι) (λ _ _ → ⊤) (λ _ _ → ⊤) (Src.expr s) → OK Dc (ET.val rs s)
  ok-val rs (src {Γ = Γ} {Ψ = Ψ} δ₀ m opt e) r =
    ok-cast (cong ⟪_⟫ (cong ⌊_⌋ δ₀)) refl {t = Lq rs e ∘l ET.eraseL Γ Ψ} (ok-Lq rs e r , ok-eraseL Γ Ψ)

  -- ★ the table
  ok-table : ∀ cs → ET.SrcsDecl Σι cs → DefsOK Dc (ET.ETProg.defs (ET.exprTable cs))
  ok-table []       tt        = ε
  ok-table (c ∷ cs) (r , rs′) =
    ok-table cs rs′ ▸₁ (ok-dc (CompiledSrc.csType c) _ (ok-val (ET.ETProg.rs (ET.exprTable cs)) (CompiledSrc.csSrc c) r) , tt)

  -- main calls (a miss halts)
  ok-main : ∀ {L} (rs : Rs L) {T : Type} (pm : T <: EffUU) → OK Dc (ET.mainCore rs pm)
  ok-main rs (sub-arr {π = π} a sub-unit g) = ok-callM (rs (bare "main") I.Unit I.Unit (grade π))
  ok-main rs (sub-arr {π = π} a sub-void g) = tt , ok-callM (rs (bare "main") I.Unit I.Void (grade π))
  ok-main rs sub-void                      = tt , ok-callM (rs (bare "main") I.Unit I.Void act)

  -- ★★ the bridge's program's ops are declared and canonical
  decl-ok : ∀ cs → ET.SrcsDecl Σι cs → ∀ {T : Type} (pm : T <: EffUU)
          → ∀ {s} → s ∈ ops (univ (ET.ETProg.defs (ET.exprTable cs)) (ET.mainCore (ET.ETProg.rs (ET.exprTable cs)) pm)) → Dc s
  decl-ok cs ok pm = univ-ok Dc (ET.ETProg.defs (ET.exprTable cs)) (ET.mainCore (ET.ETProg.rs (ET.exprTable cs)) pm)
                             (ok-table cs ok) (ok-main (ET.ETProg.rs (ET.exprTable cs)) pm)
