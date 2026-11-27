-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.ExprTable — plan 0.146 B1.7 step 2c (D461, D462): the
-- program's table from its definitions' sources.
--
-- Each definition's body is its source's bridge (`FromExpr.Lq`) after the
-- context's unused slots are erased (`eraseL`, as `elaborateFull`'s
-- `eraseCtx`), in `Compile.directCallIR`'s shape; its label's grade is its
-- type's. This module builds the pieces and relates each to its IR.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)

module Once.LinCore.ExprTable (fmt : TargetNum) (ans : FFIAnswers) where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
import Data.Unit
import Data.Bool
open import Data.Product using (Σ)
open import Once.Compile using (directCallIR; irFunOf; tableOf-go; tableOf; CompiledFun; EffUU; mainEntry)
open import Once.Spec.Sub using (_<:_; sub-arr; sub-unit; sub-void)
open import Once.Denotation.Program using (tableEnv)
import Once.Denotation.DenotTrace as DT
open import Once.CompileSrc using (toCF)

import Once.Spec.Grade as G
open import Once.Spec.Type using (Ty; Type; _⇒[_]_)
import Once.Spec.Type as ST
import Once.Spec.Context as SC
open import Once.Spec.Context using (Ctx; Usage; []; _∷_)
open import Once.Context using (⟦_⟧ᶜ; _↾_)
open import Once.IRTy using (⌊_⌋)
import Once.IR as M
open import Once.Surface.Elaborate using (eraseCtx)
open import Once.Denotation.DenotTrace using (CallEnv)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰᴵ)

open import Once.LinCore.Core fmt
open import Once.IR.Semantics.Trace using (T; ret)
open import Once.IR.Semantics.Iterative using (T∞)
open Sg using (gr)
open import Once.LinCore.NbEPLinCore fmt ans
open Sem using (Lᶜ; Lg)
open import Once.LinCore.FromExpr fmt using (ty; Co; apω; k-apω; cast; k-cast; gdB)
open import Once.LinCore.FromIR fmt using (grade)
open import Relation.Binary.PropositionalEquality using (cong; subst)
open import Once.LinCore.FromIR fmt using (⟪_⟫)
open import Once.LinCore.Bridge fmt ans using (W)
open import Once.LinCore.Bisim fmt ans using (_≈_; _≈[_]_; ret-bind; ≈-refl; ≈-trans; ≈-sym; ret≈R; ≈-≈R; ≈R-≈; >>=-congR; >>=-cong; ≈haltR; module _≈[_]_)
open _≈[_]_ using (blockR)
open import Once.LinCore.FromExprOk fmt ans using (Pure; PureI; bind-pure; module RelM; module Main; module RelClo; module RelGen)
open import Once.LinCore.FromExpr fmt using (Rs; Lq; Lq-blk; callM; refL)
open import Once.IR.Ref using (refIR)
open import Once.Spec.Name using (bare)
open import Data.String using (String)
open import Once.CompileSrc using (CompiledSrc; module CompiledSrc)
open CompiledSrc using (csName; csType; csSrc)
open import Once.IRTy using (_≟IRTy_)
open import Once.CanonicalName using (_≟ᶜ_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Once.CompileSrc using (Src; src; srcIR; module Src)
open Src using (expr; am)
open import Once.Denotation.SurfaceRefs using (Refs)
open import Once.Adequacy.ElaborateLinked using (Refs-map; DeclIn)
open import Once.Contract using (ISig)
open import Once.Denotation.DenotTrace using (callEnv)
open import Once.Denotation.Program using (IRFun; irFun; tableCalls; tableEnv-at)
open import Once.IR.Semantics.Trace using (unlinkedT)
open import Once.IR.Semantics.Iterative using (embed)
open import Once.LinCore.Grade fmt ans using (blk-coh)
open import Once.LinCore.ExprBuild fmt
open ETProg
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_)
open import Once.Spec.Name using (CanonicalName)
open import Once.IRTy using (IRTy)

-- the erasure's value on each side
ev-er : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → ⟦ ⟪ ⌊ ⟦ Γ ⟧ᶜ ⌋ ⟫ ⟧ → ⟦ Co Γ Ψ ⟧
ev-er SC.∅          []           x       = x
ev-er (Γ SC.▸ A) (G.Zero ∷ Ψ) (x , a) = ev-er Γ Ψ x
ev-er (Γ SC.▸ A) (G.One  ∷ Ψ) (x , a) = ev-er Γ Ψ x , a
ev-er (Γ SC.▸ A) (G.Many ∷ Ψ) (x , a) = ev-er Γ Ψ x , a

rv-er : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → ⟦ ⌊ ⟦ Γ ⟧ᶜ ⌋ ⟧ᴰᴵ → ⟦ ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ ⟧ᴰᴵ
rv-er SC.∅          []           x = x
rv-er (Γ SC.▸ A) (G.Zero ∷ Ψ) x = rv-er Γ Ψ (proj₁ x)
rv-er (Γ SC.▸ A) (G.One  ∷ Ψ) x = rv-er Γ Ψ (proj₁ x) , proj₂ x
rv-er (Γ SC.▸ A) (G.Many ∷ Ψ) x = rv-er Γ Ψ (proj₁ x) , proj₂ x

er-W : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) {x x′} → W ⌊ ⟦ Γ ⟧ᶜ ⌋ x x′ → W ⌊ ⟦ Γ ↾ Ψ ⟧ᶜ ⌋ (ev-er Γ Ψ x) (rv-er Γ Ψ x′)
er-W SC.∅          []           w        = w
er-W (Γ SC.▸ A) (G.Zero ∷ Ψ) (w , _)  = er-W Γ Ψ w
er-W (Γ SC.▸ A) (G.One  ∷ Ψ) (w , wa) = er-W Γ Ψ w , wa
er-W (Γ SC.▸ A) (G.Many ∷ Ψ) (w , wa) = er-W Γ Ψ w , wa

module _ {L : Cx} (δ : Env L) where

  erase-pure : ∀ {E m n} (Γ : Ctx m n) (Ψ : Usage n) → Pure δ (eraseL {L} {E} Γ Ψ) (ev-er Γ Ψ)
  erase-pure SC.∅          []           e x       = ≈-refl
  erase-pure (Γ SC.▸ A) (G.Zero ∷ Ψ) e (x , a) =
    ≈-trans (bind-pure (bind-pure (≈-trans ret-bind ret-bind))) (erase-pure Γ Ψ e x)
  erase-pure (Γ SC.▸ A) (G.One  ∷ Ψ) e (x , a) = ≈-trans (bind-pure (erase-pure Γ Ψ e x)) ret-bind
  erase-pure (Γ SC.▸ A) (G.Many ∷ Ψ) e (x , a) = ≈-trans (bind-pure (erase-pure Γ Ψ e x)) ret-bind

module _ (ρ : CallEnv) (am : M.AllocMode) where

  eraseCtx-pure : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → PureI ρ (eraseCtx {Γ = Γ} am Ψ) (rv-er Γ Ψ)
  eraseCtx-pure SC.∅          []           x = ≈-refl
  eraseCtx-pure (Γ SC.▸ A) (G.Zero ∷ Ψ) x = ≈-trans ret-bind (eraseCtx-pure Γ Ψ (proj₁ x))
  eraseCtx-pure (Γ SC.▸ A) (G.One  ∷ Ψ) x =
    ≈-trans (bind-pure (≈-trans ret-bind (eraseCtx-pure Γ Ψ (proj₁ x)))) ret-bind
  eraseCtx-pure (Γ SC.▸ A) (G.Many ∷ Ψ) x =
    ≈-trans (bind-pure (≈-trans ret-bind (eraseCtx-pure Γ Ψ (proj₁ x)))) ret-bind

module Erase {L : Cx} (δ : Env L) (ρ : CallEnv) (am : M.AllocMode) where
  open RelM δ ρ

  -- ★ the erasure against `eraseCtx`
  rel-erase : ∀ {m n} (Γ : Ctx m n) (Ψ : Usage n) → Rel (eraseL Γ Ψ) (eraseCtx {Γ = Γ} am Ψ)
  rel-erase Γ Ψ = rel-pure {t = eraseL Γ Ψ} {t′ = eraseCtx {Γ = Γ} am Ψ}
                           (erase-pure δ {E = One} Γ Ψ) (eraseCtx-pure ρ am Γ Ψ) (er-W Γ Ψ)

module DefRel {L : Cx} (δ : Env L) (ρ : CallEnv) where
  open RelM δ ρ

  -- the closure built on `tt`, beside the argument (`⟨ ir ∘ terminal , id ⟩`)
  rel-beside : ∀ {X A : Once.IRTy.IRTy} {v : LTm L One ⟪ X ⟫} {v′ : M.IR Once.IRTy.Unit X}
             → Rel v v′ → Rel ((v ⊗l lid {A = ⟪ A ⟫}) ∘l lul⁻) M.⟨ v′ M.∘ M.terminal , M.id ⟩
  rel-beside rv = mkRel λ {a} {a′} wa →
    ≈-≈R ret-bind (≈R-≈ (>>=-congR (relOf rv tt) (λ r → ≈-≈R ret-bind (ret≈R (r , wa))))
                        (≈-sym (≈-trans (>>=-cong ret-bind (λ _ → ≈-refl)) (>>=-cong ≈-refl (λ _ → ret-bind)))))

  -- ★ a definition's body against master's direct call
  rel-dc : ∀ (T : Type) {v : LTm L One (ty T)} {v′ : M.IR ⌊ ST.Unit {0} ⌋ ⌊ T ⌋} → Rel v v′ → Rel (dc T v) (dcIR T v′)
  rel-dc (A ⇒[ G.mk-kind G.Zero π ] B) rv = rel-∘ (rel-apω {π = π}) (rel-beside rv)
  rel-dc (A ⇒[ G.mk-kind G.One π ] B)  rv = rel-∘ (rel-apω {π = π}) (rel-beside rv)
  rel-dc (A ⇒[ G.mk-kind G.Many π ] B) rv = rel-∘ (rel-apω {π = π}) (rel-beside rv)
  rel-dc ST.Unit rv = rv
  rel-dc ST.Void rv = rv
  rel-dc (X ST.* Y) rv = rv
  rel-dc (X ST.+ Y) rv = rv
  rel-dc (ST.μ F) rv = rv
  rel-dc (ST.ν F f) rv = rv
  rel-dc ST.Int rv = rv
  rel-dc ST.Float rv = rv
  rel-dc (ST.var ()) rv

module ValRel {L : Cx} (rs : Rs L) (δ : Env L) (cs : CanonicalName → (A B : IRTy) → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ) where

  -- an input moved along an equal type, on both sides
  rel-dom′ : ∀ {ρ} {X Y B : IRTy} (e : X ≡ Y) {t : LTm L ⟪ X ⟫ ⟪ B ⟫} {t′ : M.IR X B}
           → RelM.Rel δ ρ t t′ → RelM.Rel δ ρ (cast (cong ⟪_⟫ e) refl t) (subst (λ o → M.IR o B) e t′)
  rel-dom′ refl r = r

  -- ★ a source's value against its IR (unoptimized: `compile`'s path)
  rel-val : ∀ {T} (s : Src T) → Src.opt s ≡ Data.Bool.false
          → Refs (λ _ _ → Data.Unit.⊤) (Main.RefOK rs δ cs (am s)) (Main.RefOK rs δ cs (am s)) (expr s)
          → RelM.Rel δ (callEnv cs ans) (val rs s) (srcIR s)
  rel-val (src {Γ = Γ} {Ψ = Ψ} δ₀ m Data.Bool.false e) refl refs =
    rel-dom′ (cong ⌊_⌋ δ₀) (RelM.rel-∘ δ (callEnv cs ans) (Main.Lq-ok rs δ cs m e refs) (Erase.rel-erase δ (callEnv cs ans) m Γ Ψ))

------------------------------------------------------------------------
-- 5. ★ THE TABLE'S TWO MEANINGS: a resolved call is master's lookup, a key
-- missing at every grade is master's `unlinkedT`. By induction on the table,
-- each entry deciding as both lookups do (`Table.env-ok`'s shape).
------------------------------------------------------------------------

-- the entry master's table has for a source (`Compile.irFunOf` by `dc-eq`)
record TableOK (t : ETProg) (tbl : List IRFun) : Set where
  field
    hit≈  : ∀ {f A B g l} {p : L t ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫} → rs t f A B g ≡ just (l , p)
          → ∀ {a a′} → W A a a′ → up g (lookup ⟦ defs t ⟧D p tt a) ≈[ W B ] tableCalls fmt ans tbl f A B a′
    miss≡ : ∀ {f A B} → (∀ g → rs t f A B g ≡ nothing) → ∀ a′ → tableCalls fmt ans tbl f A B a′ ≡ embed unlinkedT

-- each body's references related at the table before it, unoptimized (the program's obligation)
BodiesOK : List CompiledSrc → Set
BodiesOK []       = Data.Unit.⊤
BodiesOK (c ∷ cs) = BodiesOK cs × (Src.opt (csSrc c) ≡ Data.Bool.false)
                  × Refs (λ _ _ → Data.Unit.⊤) (Main.RefOK (rs (exprTable cs)) ⟦ defs (exprTable cs) ⟧D (tableCalls fmt ans (tblOf cs)) (am (csSrc c)))
                         (Main.RefOK (rs (exprTable cs)) ⟦ defs (exprTable cs) ⟧D (tableCalls fmt ans (tblOf cs)) (am (csSrc c)))
                         (expr (csSrc c))

private
  ≟Gr-refl : ∀ g → (g ≟Gr g) ≡ yes refl
  ≟Gr-refl act = refl
  ≟Gr-refl eff = refl

  just≢nothing : ∀ {X : Set} {x : X} → just x ≡ nothing → ⊥
  just≢nothing ()

  map-nothing′ : ∀ {X Y : Set} {f : X → Y} (m : Maybe X) → Data.Maybe.map f m ≡ nothing → m ≡ nothing
  map-nothing′ nothing refl = refl

  -- a body at its grade, as its computation
  up-Lg : ∀ {L} (δ : Env L) g {X A B} (b : LTm L (X ⊗t A) B) (γ : Gd g b) x a → up g (Lg δ g b γ tt (x , a)) ≈ Lᶜ δ b tt (x , a)
  up-Lg δ act b γ x a = ≈-sym (blk-coh δ γ tt (x , a))
  up-Lg δ eff b γ x a = ≈-refl

module Entry (cs : List CompiledSrc) (ok : TableOK (exprTable cs) (tblOf cs)) (c : CompiledSrc)
             (opt≡ : Src.opt (csSrc c) ≡ Data.Bool.false)
             (refs : Refs (λ _ _ → Data.Unit.⊤) (Main.RefOK (rs (exprTable cs)) ⟦ defs (exprTable cs) ⟧D (tableCalls fmt ans (tblOf cs)) (am (csSrc c)))
                          (Main.RefOK (rs (exprTable cs)) ⟦ defs (exprTable cs) ⟧D (tableCalls fmt ans (tblOf cs)) (am (csSrc c)))
                          (expr (csSrc c))) where
  t = exprTable cs
  δ = ⟦ defs t ⟧D
  Tc = csType c
  δ′ = ⟦ defs t ▸ bodyOf (rs t) c ⟧D
  open TableOK ok

  -- ★ the entry's body against master's
  body≈ : ∀ {a a′} → W ⌊ dcDom Tc ⌋ a a′
        → up (dcGr Tc) (lookup δ′ here tt a) ≈[ W ⌊ dcCod Tc ⌋ ] Once.Denotation.DenotTrace.evalᴰ fmt (callEnv (tableCalls fmt ans (tblOf cs)) ans) (dcIR Tc (srcIR (csSrc c))) a′
  body≈ {a} w =
    ≈-≈R (≈-trans (up-Lg δ (dcGr Tc) (dc Tc (val (rs t) (csSrc c)) ∘l lul) (dcGd Tc (k-val (rs t) (csSrc c))) tt a) ret-bind)
         (RelM.relOf δ (callEnv (tableCalls fmt ans (tblOf cs)) ans) (DefRel.rel-dc δ (callEnv (tableCalls fmt ans (tblOf cs)) ans) Tc (ValRel.rel-val (rs t) δ (tableCalls fmt ans (tblOf cs)) (csSrc c) opt≡ refs)) w)

  hit-yes : ∀ {f A B g l} {p′ : (L t ▸ sgOf c) ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫} (n : csName c ≡ f) (p : ⌊ dcDom Tc ⌋ ≡ A) (q : ⌊ dcCod Tc ⌋ ≡ B) (r : dcGr Tc ≡ g)
          → extendR-at (rs t) c f A B g (yes n) (yes p) (yes q) (yes r) ≡ just (l , p′) → ∀ {a a′} → W A a a′
          → up g (lookup δ′ p′ tt a) ≈[ W B ] tableEnv-at fmt ans (irE c) (tblOf cs) f A B (yes n) (yes p) (yes q) a′
  hit-yes n refl refl refl refl w = body≈ w

  weak-hit : ∀ {f A B g l} {p′ : (L t ▸ sgOf c) ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫} (m : Maybe (Σ ℕ λ l → L t ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫))
           → rs t f A B g ≡ m → weakR m ≡ just (l , p′) → ∀ {a a′} → W A a a′
           → up g (lookup δ′ p′ tt a) ≈[ W B ] tableCalls fmt ans (tblOf cs) f A B a′
  weak-hit (just (l₀ , p₀)) e refl w = hit≈ e w

  hit-at : ∀ {f A B g l} {p′ : (L t ▸ sgOf c) ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫}
             d₁ d₂ d₃ (d₄ : Dec (dcGr Tc ≡ g))
         → extendR-at (rs t) c f A B g d₁ d₂ d₃ d₄ ≡ just (l , p′) → ∀ {a a′} → W A a a′
         → up g (lookup δ′ p′ tt a) ≈[ W B ] tableEnv-at fmt ans (irE c) (tblOf cs) f A B d₁ d₂ d₃ a′
  hit-at (yes n) (yes p) (yes q) (yes r) eq w = hit-yes n p q r eq w
  hit-at (yes n) (yes p) (yes q) (no _)  ()
  hit-at {f} {A} {B} {g} (yes _) (yes _) (no _) _ eq w = weak-hit (rs t f A B g) refl eq w
  hit-at {f} {A} {B} {g} (yes _) (no _)  _      _ eq w = weak-hit (rs t f A B g) refl eq w
  hit-at {f} {A} {B} {g} (no _)  _       _      _ eq w = weak-hit (rs t f A B g) refl eq w

  miss-at : ∀ {f A B} d₁ d₂ d₃ → (∀ g → extendR-at (rs t) c f A B g d₁ d₂ d₃ (dcGr Tc ≟Gr g) ≡ nothing)
          → ∀ a′ → tableEnv-at fmt ans (irE c) (tblOf cs) f A B d₁ d₂ d₃ a′ ≡ embed unlinkedT
  miss-at (yes n) (yes p) (yes q) h a′ =
    ⊥-elim (just≢nothing (subst (λ d → extendR-at (rs t) c _ _ _ (dcGr Tc) (yes n) (yes p) (yes q) d ≡ nothing) (≟Gr-refl (dcGr Tc)) (h (dcGr Tc))))
  miss-at {f} {A} {B} (yes _) (yes _) (no _) h a′ = miss≡ (λ g → map-nothing′ (rs t f A B g) (h g)) a′
  miss-at {f} {A} {B} (yes _) (no _)  _      h a′ = miss≡ (λ g → map-nothing′ (rs t f A B g) (h g)) a′
  miss-at {f} {A} {B} (no _)  _       _      h a′ = miss≡ (λ g → map-nothing′ (rs t f A B g) (h g)) a′

  entry-ok : TableOK (exprTable (c ∷ cs)) (tblOf (c ∷ cs))
  entry-ok = record
    { hit≈  = λ {f} {A} {B} {g} eq w → hit-at (csName c ≟ᶜ f) (⌊ dcDom Tc ⌋ ≟IRTy A) (⌊ dcCod Tc ⌋ ≟IRTy B) (dcGr Tc ≟Gr g) eq w
    ; miss≡ = λ {f} {A} {B} h a′ → miss-at (csName c ≟ᶜ f) (⌊ dcDom Tc ⌋ ≟IRTy A) (⌊ dcCod Tc ⌋ ≟IRTy B) h a′
    }

-- ★ THE TABLE: its labels against master's lookup
table-ok : ∀ (srcs : List CompiledSrc) → BodiesOK srcs → TableOK (exprTable srcs) (tblOf srcs)
table-ok []       _ = record { hit≈ = λ () ; miss≡ = λ _ _ → refl }
table-ok (c ∷ cs) (bs , opt≡ , refs) = Entry.entry-ok cs (table-ok cs bs) c opt≡ refs

------------------------------------------------------------------------
-- 6. ★ A REFERENCE, related: its key graded (any hit for its name and call
-- types at its grade, D462), against a table whose meanings are related.
------------------------------------------------------------------------

module RefRel (t : ETProg) (tbl : List IRFun) (ok : TableOK t tbl) (am₀ : M.AllocMode) where
  open TableOK ok
  δ = ⟦ defs t ⟧D
  open RelM δ (callEnv (tableCalls fmt ans tbl) ans)

  private
    clash : ∀ {f A B g g′} {h : Σ ℕ λ l → L t ∋[ l ] sg once g′ One ⟪ A ⟫ ⟪ B ⟫} → g′ ≡ g
          → rs t f A B g′ ≡ just h → rs t f A B g ≡ nothing → ⊥
    clash refl e′ e = just≢nothing (Relation.Binary.PropositionalEquality.trans (Relation.Binary.PropositionalEquality.sym e′) e)

    all-miss : ∀ {f A B g} → Graded (rs t) f A B g → rs t f A B g ≡ nothing → ∀ g′ → rs t f A B g′ ≡ nothing
    all-miss {f} {A} {B} gr e g′ = go (rs t f A B g′) refl
      where
        go : (m : Maybe (Σ ℕ λ l → L t ∋[ l ] sg once g′ One ⟪ A ⟫ ⟪ B ⟫)) → rs t f A B g′ ≡ m → rs t f A B g′ ≡ nothing
        go (just h) e′ = ⊥-elim (clash (gr g′ e′) e′ e)
        go nothing  e′ = e′

  callM-rel′ : ∀ {f A B g} (r : Maybe (Σ ℕ λ l → L t ∋[ l ] sg once g One ⟪ A ⟫ ⟪ B ⟫)) → rs t f A B g ≡ r → Graded (rs t) f A B g
             → Rel (callM r) (M.Call {A} {B} f)
  callM-rel′ (just (l , p)) e gr = mkRel λ w → ≈-≈R (bind-pure (≈-trans ret-bind (≈-trans ret-bind ret-bind))) (hit≈ e w)
  callM-rel′ {f} {A} {B} {g} nothing e gr = mkRel λ {a} {a′} w →
    subst (λ m → Lᶜ δ (callM {L t} {g} {⟪ A ⟫} {⟪ B ⟫} nothing) tt a ≈[ W B ] m) (sym (miss≡ (all-miss gr e) a′)) (unl {g} {A} {B} {a})
    where
      sym = Relation.Binary.PropositionalEquality.sym
      unl : ∀ {g} {A B : IRTy} {a} → Lᶜ δ (callM {L t} {g} {⟪ A ⟫} {⟪ B ⟫} nothing) tt a ≈[ W B ] embed unlinkedT
      blockR unl = ≈haltR

  rel-call′ : ∀ f (A B : IRTy) g → Graded (rs t) f A B g → Rel (callM (rs t f A B g)) (M.Call {A} {B} f)
  rel-call′ f A B g gr = callM-rel′ (rs t f A B g) refl gr

  -- ★ a reference, case for case `refIR`
  rel-ref′ : ∀ {m} (T : Ty m) (x : String) → GradedRef (rs t) x T → Main.RefOK (rs t) δ (tableCalls fmt ans tbl) am₀ x T
  rel-ref′ (A ⇒[ G.mk-kind G.Zero π ] B) x gr = RelClo.rel-cloG δ _ π _ (rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ B ⌋ (grade π) gr) (RelGen.rel-snd δ _ am₀))
  rel-ref′ (A ⇒[ G.mk-kind G.One π ] B) x gr  = RelClo.rel-cloG δ _ π _ (rel-∘ (rel-call′ (bare x) ⌊ A ⌋ ⌊ B ⌋ (grade π) gr) (RelGen.rel-snd δ _ am₀))
  rel-ref′ (A ⇒[ G.mk-kind G.Many π ] B) x gr = RelClo.rel-cloG δ _ π _ (rel-∘ (rel-call′ (bare x) ⌊ A ⌋ ⌊ B ⌋ (grade π) gr) (RelGen.rel-snd δ _ am₀))
  rel-ref′ T@ST.Unit x gr = rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ T ⌋ act gr) (RelGen.rel-drop δ _ am₀)
  rel-ref′ T@ST.Void x gr = rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ T ⌋ act gr) (RelGen.rel-drop δ _ am₀)
  rel-ref′ T@(X ST.* Y) x gr = rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ T ⌋ act gr) (RelGen.rel-drop δ _ am₀)
  rel-ref′ T@(X ST.+ Y) x gr = rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ T ⌋ act gr) (RelGen.rel-drop δ _ am₀)
  rel-ref′ T@(ST.μ F) x gr = rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ T ⌋ act gr) (RelGen.rel-drop δ _ am₀)
  rel-ref′ T@(ST.ν F f) x gr = rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ T ⌋ act gr) (RelGen.rel-drop δ _ am₀)
  rel-ref′ T@ST.Int x gr = rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ T ⌋ act gr) (RelGen.rel-drop δ _ am₀)
  rel-ref′ T@ST.Float x gr = rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ T ⌋ act gr) (RelGen.rel-drop δ _ am₀)
  rel-ref′ T@(ST.var _) x gr = rel-∘ (rel-call′ (bare x) Once.IRTy.Unit ⌊ T ⌋ act gr) (RelGen.rel-drop δ _ am₀)

------------------------------------------------------------------------
-- 7. ★ THE PROGRAM'S OBLIGATION: each body unoptimized, its references
-- graded at the table before it (D462); from it, `BodiesOK`.
------------------------------------------------------------------------

bodies-ok : ∀ (srcs : List CompiledSrc) → GradedBodies srcs → BodiesOK srcs
bodies-ok []       _                  = Data.Unit.tt
bodies-ok (c ∷ cs) (gs , opt≡ , refs) =
  bodies-ok cs gs , opt≡ ,
  Refs-map (λ h → h)
           (λ {A} {x} g → RefRel.rel-ref′ (exprTable cs) (tblOf cs) (table-ok cs (bodies-ok cs gs)) (am (csSrc c)) A x g)
           (λ {A} {x} g → RefRel.rel-ref′ (exprTable cs) (tblOf cs) (table-ok cs (bodies-ok cs gs)) (am (csSrc c)) A x g)
           (expr (csSrc c)) refs

------------------------------------------------------------------------
-- 9. ★ MAIN: `Compile.mainEntry`, its call at main's grade.
------------------------------------------------------------------------

-- ★★ the bridge's program against master's, from `main`
rel-main-at : ∀ (tl : List CompiledSrc) (gb : GradedBodies tl) {ty : Type} (pm : ty <: EffUU)
            → MainGraded (rs (exprTable tl)) pm
            → Lᶜ ⟦ defs (exprTable tl) ⟧D (mainCore (rs (exprTable tl)) pm) tt tt
                ≈[ W Once.IRTy.Unit ] DT.evalᴰ fmt (tableEnv fmt ans (tblOf tl)) (mainEntry pm) tt
rel-main-at tl gb (sub-arr {π = π} a sub-unit g) gm =
  RelM.relOf _ _ (RefRel.rel-call′ (exprTable tl) (tblOf tl) (table-ok tl (bodies-ok tl gb)) M.Heap (bare "main") Once.IRTy.Unit Once.IRTy.Unit (grade π) gm) tt
rel-main-at tl gb (sub-arr {π = π} a sub-void g) gm =
  RelM.relOf _ _ (RelM.rel-∘ _ _ (RelGen.rel-zero _ _ M.Heap)
            (RefRel.rel-call′ (exprTable tl) (tblOf tl) (table-ok tl (bodies-ok tl gb)) M.Heap (bare "main") Once.IRTy.Unit Once.IRTy.Void (grade π) gm)) tt
rel-main-at tl gb sub-void gm =
  RelM.relOf _ _ (RelM.rel-∘ _ _ (RelGen.rel-zero _ _ M.Heap)
            (RefRel.rel-call′ (exprTable tl) (tblOf tl) (table-ok tl (bodies-ok tl gb)) M.Heap (bare "main") Once.IRTy.Unit Once.IRTy.Void act gm)) tt

